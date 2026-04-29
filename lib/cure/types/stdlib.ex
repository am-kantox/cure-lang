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
  alias Cure.Stdlib.Paths
  alias Cure.Types.{Env, Refinement, Type}

  @persistent_key {__MODULE__, :signatures_v3}

  @typedoc """
  Parsed stdlib signature bundle:

    * `:qualified` -- map of fully qualified function names
      (`"Std.List.map"`) to function signatures. Safe to install in
      every inference environment.
    * `:short_by_module` -- map of `"Std.Mod"` to a map of short
      function names (`"map"`) to signatures. Installed selectively
      in response to `use Std.Mod` imports.
    * `:qualified_types` -- map of fully qualified type names
      (`"Std.Refine.Positive"`) to canonical types. Currently only
      consumed by tests / introspection; Cure surface syntax does
      not address types by qualified name yet.
    * `:types_by_module` -- map of `"Std.Mod"` to a map of short
      type names (`"Positive"`) to canonical types. Installed into
      `env.types` selectively in response to `use Std.Mod`.
  """
  @type bundle :: %{
          qualified: %{String.t() => term()},
          short_by_module: %{String.t() => %{String.t() => term()}},
          qualified_types: %{String.t() => term()},
          types_by_module: %{String.t() => %{String.t() => term()}}
        }

  @doc """
  Return the parsed stdlib signature bundle. The result is memoised;
  call `reload/0` after editing stdlib sources to rebuild it.

  An **empty** bundle is deliberately *not* memoised. Empty almost
  always means the stdlib sources were transiently unreachable
  (release unpack in progress, `:stdlib_source_dir` override pointing
  at a path that will exist shortly, Cure's `priv/` not yet symlinked
  into the host's build tree, ...). Caching that first miss would
  silently type every stdlib call as `Any` for the lifetime of the VM.
  Retrying on the next call trades a cheap re-scan for self-healing
  correctness; the cost is trivial compared to the cost of a silently
  degraded REPL.
  """
  @spec all() :: bundle()
  def all do
    case :persistent_term.get(@persistent_key, :undefined) do
      :undefined ->
        loaded = load_all()
        unless empty?(loaded), do: :persistent_term.put(@persistent_key, loaded)
        loaded

      loaded ->
        loaded
    end
  end

  @doc false
  @spec empty?(bundle()) :: boolean()
  def empty?(%{qualified: q, short_by_module: s} = bundle) do
    qt = Map.get(bundle, :qualified_types, %{})
    tbm = Map.get(bundle, :types_by_module, %{})
    map_size(q) == 0 and map_size(s) == 0 and map_size(qt) == 0 and map_size(tbm) == 0
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
  Return the short-name type map for one stdlib module. The values are
  canonical Cure types (`{:refinement, ...}`, `{:adt, ...}`, primitive
  atoms for plain aliases). Returns `%{}` when the module is unknown.
  """
  @spec short_types_for(String.t()) :: %{String.t() => term()}
  def short_types_for(module_name) when is_binary(module_name) do
    all() |> Map.get(:types_by_module, %{}) |> Map.get(module_name, %{})
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

  @doc """
  Extend `env.types` with every fully qualified stdlib type alias.
  Cure surface syntax does not currently address types by their
  qualified name, but registering them keeps the type-level namespace
  symmetrical with the value-level one and is useful for tooling.
  """
  @spec install_qualified_types(Env.t()) :: Env.t()
  def install_qualified_types(%Env{} = env) do
    Enum.reduce(all().qualified_types, env, fn {name, type}, e ->
      Env.extend_type(e, name, type)
    end)
  end

  @doc """
  Extend `env.types` with short-name type aliases from a single stdlib
  module. Mirrors `install_import/2` at the type level: a `use Std.Mod`
  in user code now also brings every public type alias from that module
  into scope, so a parameter declared as `Positive` resolves to its
  underlying refinement type rather than remaining a bare nominal
  reference.
  """
  @spec install_import_types(Env.t(), String.t()) :: Env.t()
  def install_import_types(%Env{} = env, module_name) when is_binary(module_name) do
    canonical = strip_cure_prefix(module_name)

    case Map.get(all().types_by_module, canonical) do
      nil ->
        env

      types ->
        Enum.reduce(types, env, fn {name, type}, e -> Env.extend_type(e, name, type) end)
    end
  end

  defp strip_cure_prefix("Cure." <> rest), do: rest
  defp strip_cure_prefix(other), do: other

  # ---------------------------------------------------------------------------
  # Loading
  # ---------------------------------------------------------------------------

  defp load_all do
    empty = %{qualified: %{}, short_by_module: %{}, qualified_types: %{}, types_by_module: %{}}

    # The stdlib may live under `lib/std/` (cwd-relative, when Cure
    # itself is the current Mix project), under `:code.priv_dir(:cure)/std`
    # (the bundled location used by host applications), or at an
    # explicit override set via `Application.put_env/3`. See
    # `Cure.Stdlib.Paths` for the full resolution order.
    case Paths.source_dir() do
      nil ->
        empty

      dir ->
        load_from_dir(dir, empty)
    end
  end

  defp load_from_dir(dir, empty) do
    case File.ls(dir) do
      {:ok, entries} ->
        entries
        |> Enum.filter(&String.ends_with?(&1, ".cure"))
        |> Enum.map(&Path.join(dir, &1))
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
    type_map = collect_types(stmts)

    acc =
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

    if map_size(type_map) == 0 do
      acc
    else
      qualified_types =
        Enum.reduce(type_map, acc.qualified_types, fn {name, type}, q ->
          Map.put(q, "#{module_name}.#{name}", type)
        end)

      types_by_module = Map.put(acc.types_by_module, module_name, type_map)
      %{acc | qualified_types: qualified_types, types_by_module: types_by_module}
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

  # Lift top-level type declarations:
  #
  #   * `{:type_annotation, [refinement: true, name: name, ...], children}`
  #     -- a refinement type alias built via `Refinement.from_type_annotation/2`.
  #   * `{:type_annotation, [name: name, ...], [inner_ast]}` (no
  #     `:refinement` flag) -- a plain type alias resolved through
  #     `Type.resolve/1`.
  #   * `{:container, [container_type: :enum, name: name, type_params: tp], _}`
  #     -- an ADT, registered as `{:adt, downcased_name_atom,
  #     param_type_vars}` to match the user-side enum bookkeeping.
  defp collect_types(stmts) do
    Enum.reduce(stmts, %{}, fn
      {:type_annotation, meta, children}, acc ->
        case type_alias_from_annotation(meta, children) do
          {name, type} when is_binary(name) -> Map.put(acc, name, type)
          _ -> acc
        end

      {:container, meta, _body}, acc ->
        case adt_from_container(meta) do
          {name, type} when is_binary(name) -> Map.put(acc, name, type)
          _ -> acc
        end

      _, acc ->
        acc
    end)
  end

  defp type_alias_from_annotation(meta, children) do
    name = Keyword.get(meta, :name)

    cond do
      not is_binary(name) ->
        nil

      Keyword.get(meta, :refinement) ->
        case Refinement.from_type_annotation(meta, children) do
          nil -> nil
          ref -> {name, ref}
        end

      true ->
        case children do
          [inner] -> {name, Type.resolve(inner)}
          _ -> nil
        end
    end
  end

  defp adt_from_container(meta) do
    case Keyword.get(meta, :container_type) do
      :enum ->
        name = Keyword.get(meta, :name)
        params = Keyword.get(meta, :type_params, [])

        if is_binary(name) do
          atom = String.to_atom(String.downcase(name))
          param_vars = Enum.map(params, fn p -> {:type_var, to_string(p)} end)
          {name, {:adt, atom, param_vars}}
        else
          nil
        end

      _ ->
        nil
    end
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
