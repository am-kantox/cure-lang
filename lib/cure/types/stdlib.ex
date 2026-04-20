defmodule Cure.Types.Stdlib do
  @moduledoc """
  Load function signatures from the bundled Cure standard library so the
  type checker can resolve qualified (`Std.List.map`) and imported
  (`use Std.List` -> `map`) calls without having to re-check every
  stdlib module on demand.

  Each stdlib `.cure` file in `lib/std/` is parsed once, its top-level
  function definitions are lifted through `Cure.Types.Type.resolve/1`,
  and the resulting signatures are memoised in `:persistent_term` keyed
  by module name. Callers consume the prebuilt map directly; there is
  no side-effect on the compile pipeline.

  The bundle returned by `all/0` has two faces:

      %{
        qualified: %{
          "Std.List.map" => {:fun, [...], ...},
          "Std.Math.abs" => {:fun, [...], ...},
          ...
        },
        short_by_module: %{
          "Std.List" => %{"map" => {:fun, [...], ...}, ...},
          ...
        }
      }

  Callers install the qualified names unconditionally and the short
  names only in response to a matching `use Std.Mod` import. When two
  imported modules expose the same short name, the later import wins,
  mirroring the precedence the codegen applies via `resolve_import/3`.
  """

  alias Cure.Compiler.{Lexer, Parser}
  alias Cure.Types.{Env, Type}

  @stdlib_dir Path.join(["lib", "std"])
  @persistent_key {__MODULE__, :signatures_v2}

  @typedoc """
  Parsed stdlib signature bundle:

    * `:qualified` -- map of fully qualified names (`"Std.List.map"`)
      to function signatures. Safe to install in every inference
      environment.
    * `:short_by_module` -- map of `"Std.Mod"` to a map of short
      names (`"map"`) to signatures. Installed selectively in response
      to `use Std.Mod` imports.
  """
  @type bundle :: %{
          qualified: %{String.t() => term()},
          short_by_module: %{String.t() => %{String.t() => term()}}
        }

  @doc """
  Return the parsed stdlib signature bundle. The result is memoised;
  call `reload/0` after editing stdlib sources to rebuild it.
  """
  @spec all() :: bundle()
  def all do
    case :persistent_term.get(@persistent_key, :undefined) do
      :undefined ->
        loaded = load_all()
        :persistent_term.put(@persistent_key, loaded)
        loaded

      loaded ->
        loaded
    end
  end

  @doc """
  Return the short-name signature map for one stdlib module, e.g.
  `"Std.List"`. Returns `%{}` when the module is unknown.
  """
  @spec short_names_for(String.t()) :: %{String.t() => term()}
  def short_names_for(module_name) when is_binary(module_name) do
    all() |> Map.fetch!(:short_by_module) |> Map.get(module_name, %{})
  end

  @doc """
  Forget the memoised result so the next `all/0` reparses every
  stdlib source file. Exposed for tests and REPL tooling.
  """
  @spec reload() :: :ok
  def reload do
    _ = :persistent_term.erase(@persistent_key)
    :ok
  end

  # ---------------------------------------------------------------------------
  # Env installation
  # ---------------------------------------------------------------------------

  @doc """
  Extend `env` with every fully qualified stdlib signature.
  After this call, lookups like `"Std.List.map"` resolve to the
  stdlib signature without requiring an explicit `use`.
  """
  @spec install_qualified(Env.t()) :: Env.t()
  def install_qualified(%Env{} = env) do
    Enum.reduce(all().qualified, env, fn {name, sig}, e ->
      Env.extend(e, name, sig)
    end)
  end

  @doc """
  Extend `env` with short-name bindings from a single stdlib module.
  Mirrors the effect of a `use Std.Mod` import at the type level.
  Returns the env unchanged when the module is not part of the stdlib.
  """
  @spec install_import(Env.t(), String.t()) :: Env.t()
  def install_import(%Env{} = env, module_name) when is_binary(module_name) do
    canonical = strip_cure_prefix(module_name)

    case Map.get(all().short_by_module, canonical) do
      nil ->
        env

      sigs ->
        Enum.reduce(sigs, env, fn {name, sig}, e -> Env.extend(e, name, sig) end)
    end
  end

  defp strip_cure_prefix("Cure." <> rest), do: rest
  defp strip_cure_prefix(other), do: other

  # ---------------------------------------------------------------------------
  # Loading
  # ---------------------------------------------------------------------------

  defp load_all do
    empty = %{qualified: %{}, short_by_module: %{}}

    case File.ls(@stdlib_dir) do
      {:ok, entries} ->
        entries
        |> Enum.filter(&String.ends_with?(&1, ".cure"))
        |> Enum.map(&Path.join(@stdlib_dir, &1))
        |> Enum.reduce(empty, &load_module/2)

      {:error, _} ->
        empty
    end
  end

  defp load_module(path, acc) do
    with {:ok, source} <- File.read(path),
         {:ok, tokens} <- Lexer.tokenize(source, file: path, emit_events: false),
         {:ok, ast} <- Parser.parse(tokens, file: path, emit_events: false),
         {:ok, module_name, stmts} <- extract_module(ast) do
      merge_module(acc, module_name, stmts)
    else
      _ -> acc
    end
  end

  defp merge_module(acc, module_name, stmts) do
    short_map = collect_signatures(stmts)

    if map_size(short_map) == 0 do
      acc
    else
      qualified_map =
        Enum.reduce(short_map, acc.qualified, fn {name, sig}, q ->
          Map.put(q, "#{module_name}.#{name}", sig)
        end)

      short_by_module = Map.put(acc.short_by_module, module_name, short_map)
      %{acc | qualified: qualified_map, short_by_module: short_by_module}
    end
  end

  defp extract_module({:container, meta, body}) when is_list(meta) do
    case Keyword.get(meta, :container_type) do
      :module -> {:ok, Keyword.get(meta, :name, "Unknown"), body}
      _ -> :error
    end
  end

  defp extract_module({:block, _, children}) do
    case Enum.find(children, fn
           {:container, m, _} when is_list(m) ->
             Keyword.get(m, :container_type) == :module

           _ ->
             false
         end) do
      {:container, _, _} = mod -> extract_module(mod)
      _ -> :error
    end
  end

  defp extract_module(_), do: :error

  defp collect_signatures(stmts) do
    Enum.reduce(stmts, %{}, fn
      {:function_def, meta, _body}, acc ->
        case signature_from_meta(meta) do
          nil -> acc
          {short_name, signature} -> Map.put(acc, short_name, signature)
        end

      _, acc ->
        acc
    end)
  end

  defp signature_from_meta(meta) do
    name = Keyword.get(meta, :name)
    visibility = Keyword.get(meta, :visibility, :public)
    params = Keyword.get(meta, :params, [])
    return_type_ast = Keyword.get(meta, :return_type)

    cond do
      not is_binary(name) -> nil
      visibility != :public -> nil
      true -> {name, build_signature(params, return_type_ast)}
    end
  end

  defp build_signature(params, return_type_ast) do
    param_types =
      Enum.map(params, fn
        {:param, pmeta, _pname} -> Type.resolve(Keyword.get(pmeta, :type))
        _ -> :any
      end)

    ret_type =
      case return_type_ast do
        nil -> :any
        ast -> Type.resolve(ast)
      end

    {:fun, param_types, ret_type}
  end
end
