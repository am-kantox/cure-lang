defmodule Cure.Stdlib.Preload do
  @moduledoc """
  Load compiled Cure stdlib (and optionally example) BEAM modules into
  the running VM *without* adding their output directory to the global
  Erlang code path.

  Historically the preload helpers in `Cure.CLI`, `Mix.Tasks.Cure.Check.Examples`
  and the regression test suite all did:

      :code.add_patha(String.to_charlist(Path.expand("_build/cure/ebin")))

  That is convenient right up until `_build/cure/ebin` contains a stale
  lowercase `<name>.beam` left over from a previous compile with the old
  naming convention (for example, an older `examples/math.cure` produced
  a top-level `math.beam`). The moment the directory is on the code path,
  that stale file takes precedence over OTP's own `:math`, `:code`, `:lists`,
  etc., and any subsequent call to e.g. `:math.pi/0` raises
  `UndefinedFunctionError` because the stale module never exported it.

  Loading the beams directly via `:code.load_binary/3` by their fully
  qualified `Cure.*` names side-steps the whole class of shadowing bugs:
  only modules whose file name starts with `Cure.` are ever considered,
  and the target directory is never added to the global code path.
  """

  @std_modules ~w(Core List Pair Math String Io System Show Option Result
                  Eq Ord Functor Map Set Test Vector Equal Refine Fsm
                  Match Proof Gen Iter Access)

  @default_stdlib_ebin "_build/cure/ebin"
  @default_examples_ebin "_build/cure/ex_ebin"

  @typedoc """
  Options for `preload/1`.

    * `:examples` -- when `true`, also loads every `Cure.*.beam` found in
      the examples output directory. Defaults to `false`.
    * `:stdlib_ebin` -- override the stdlib beam directory. Defaults to
      `"_build/cure/ebin"`.
    * `:examples_ebin` -- override the examples beam directory. Defaults
      to `"_build/cure/ex_ebin"`.
  """
  @type option ::
          {:examples, boolean()}
          | {:stdlib_ebin, String.t()}
          | {:examples_ebin, String.t()}

  @doc """
  Load compiled stdlib (and optionally example) modules.

  Always returns `:ok`, even when nothing can be loaded (the build directory
  may not exist yet during a fresh `mix deps.compile`). Modules already
  loaded into the VM are left alone.
  """
  @spec preload([option()]) :: :ok
  def preload(opts \\ []) do
    stdlib_ebin = Keyword.get(opts, :stdlib_ebin, @default_stdlib_ebin)
    examples_ebin = Keyword.get(opts, :examples_ebin, @default_examples_ebin)
    include_examples? = Keyword.get(opts, :examples, false)

    load_stdlib(stdlib_ebin)
    if include_examples?, do: load_cure_beams(examples_ebin)

    :ok
  end

  @doc """
  Return the list of stdlib module names that `preload/1` attempts to
  load. Exposed for introspection and testing.
  """
  @spec stdlib_modules() :: [module()]
  def stdlib_modules do
    Enum.map(@std_modules, &String.to_atom("Cure.Std.#{&1}"))
  end

  # -- helpers ----------------------------------------------------------------

  defp load_stdlib(ebin) do
    if File.dir?(ebin) do
      Enum.each(stdlib_modules(), fn module ->
        path = Path.join(ebin, "#{module}.beam")
        load_if_present(module, path)
      end)
    end
  end

  # Load any `Cure.*.beam` in the given directory. We restrict to the
  # `Cure.` prefix to make sure we never load a stale bare-name beam that
  # would shadow an OTP or Elixir module.
  defp load_cure_beams(ebin) do
    if File.dir?(ebin) do
      ebin
      |> Path.join("Cure.*.beam")
      |> Path.wildcard()
      |> Enum.each(fn path ->
        module =
          path
          |> Path.basename(".beam")
          |> String.to_atom()

        load_if_present(module, path)
      end)
    end
  end

  defp load_if_present(module, path) do
    with true <- File.exists?(path),
         {:ok, binary} <- File.read(path) do
      case :code.load_binary(module, String.to_charlist(path), binary) do
        {:module, ^module} -> :ok
        {:error, _reason} -> :ok
      end
    else
      _ -> :ok
    end
  end
end
