defmodule Cure.Sup.Compiler do
  @moduledoc """
  Compiles Cure `sup` containers into BEAM `Supervisor`-behaviour modules.

  The generated module exposes `start_link/1` and `init/1`. `init/1`
  returns a hand-crafted child specification list plus the strategy
  parsed from the `sup` header.

  ## Child module resolution

  Child specs emit atoms of the form `Cure.<Kind>.<Path>` so the
  declared container name matches the atoms produced by
  `Cure.Actor.Compiler` and `Cure.Sup.Compiler`. A child written as:

    Counter as counter

  compiles to `:"Cure.Actor.Counter"`; a nested supervisor written as
  `sup Workers as workers` compiles to `:"Cure.Sup.Workers"`.

  A user may opt out of the convention by writing a dotted module path
  that already contains a `.`: `App.Gateway as gateway` resolves
  literally to `:"App.Gateway"`.

  ## Return value

  Mirrors `Cure.Actor.Compiler`: the module is compiled and loaded
  eagerly; the call returns `{:ok, {:supervisor, module_atom}}`.
  """

  alias Cure.Compiler.BeamWriter
  alias Cure.Pipeline.Events

  @default_strategy :one_for_one
  @default_intensity 3
  @default_period 5
  @default_shutdown 5000

  @doc """
  Compile a `{:container, [container_type: :supervisor, ...], child_specs}`
  node. Returns `{:ok, {:supervisor, module_atom}}` on success.

  ## Options
    * `:emit_events` -- whether to emit pipeline events (default `true`).
    * `:file`        -- filename used for diagnostics (default `"nofile"`).
    * `:output_dir`  -- when set, the compiled supervisor bytecode is
      also written to `<output_dir>/<module_atom>.beam` so the
      supervisor module becomes available to subsequent cold starts
      exactly like plain Cure modules. Writing is skipped when this
      option is absent or `nil`.
  """
  @spec compile(tuple(), keyword()) :: {:ok, {:supervisor, module()}}
  def compile({:container, meta, child_specs} = _ast, opts \\ []) do
    emit? = Keyword.get(opts, :emit_events, true)
    file = Keyword.get(opts, :file, "nofile")
    output_dir = Keyword.get(opts, :output_dir)

    name = Keyword.get(meta, :name, "unnamed")
    mod_atom = sup_module_atom(name)
    line = Keyword.get(meta, :line, 1)

    strategy = extract_atom(Keyword.get(meta, :strategy)) || @default_strategy
    intensity = extract_integer(Keyword.get(meta, :intensity)) || @default_intensity
    period = extract_integer(Keyword.get(meta, :period)) || @default_period

    module_code =
      generate_module(mod_atom, strategy, intensity, period, child_specs)

    {result, _diagnostics} =
      Code.with_diagnostics([log: false], fn ->
        Code.compile_string(module_code, file)
      end)

    [{^mod_atom, bytecode}] = result
    :code.purge(mod_atom)
    {:module, ^mod_atom} = :code.load_binary(mod_atom, ~c"#{file}", bytecode)

    if is_binary(output_dir) do
      :ok = BeamWriter.write_beam(mod_atom, bytecode, output_dir, emit_events: emit?, file: file)
    end

    if emit? do
      Events.emit(:codegen, :module_assembled, mod_atom, Events.meta(file, line))
    end

    {:ok, {:supervisor, mod_atom}}
  end

  @doc false
  def sup_module_atom(name) do
    String.to_atom("Cure.Sup." <> name)
  end

  # -- Code generation ---------------------------------------------------------

  defp generate_module(mod_atom, strategy, intensity, period, child_specs) do
    child_list = render_child_specs(child_specs)

    """
    defmodule :"#{mod_atom}" do
      use Supervisor

      def start_link(init_arg \\\\ []) do
        Supervisor.start_link(__MODULE__, init_arg, name: __MODULE__)
      end

      @impl Supervisor
      def init(_init_arg) do
        children = [#{child_list}]

        Supervisor.init(children,
          strategy: #{inspect(strategy)},
          max_restarts: #{intensity},
          max_seconds: #{period}
        )
      end
    end
    """
  end

  defp render_child_specs(specs) do
    specs
    |> Enum.map(&render_child_spec/1)
    |> Enum.join(", ")
  end

  defp render_child_spec({:child_spec, meta, _}) do
    id = Keyword.get(meta, :id, "child") |> to_string()
    kind = Keyword.get(meta, :kind, :worker)
    module_path = Keyword.get(meta, :module, "Unknown")
    module_atom = resolve_child_module(kind, module_path)

    restart = extract_atom(Keyword.get(meta, :restart)) || :permanent

    shutdown =
      case Keyword.get(meta, :shutdown) do
        nil ->
          @default_shutdown

        ast ->
          case extract_atom(ast) do
            :brutal_kill -> :brutal_kill
            :infinity -> :infinity
            _ -> extract_integer(ast) || @default_shutdown
          end
      end

    """
      %{
        id: #{inspect(String.to_atom(id))},
        start: {#{inspect(module_atom)}, :start_link, []},
        restart: #{inspect(restart)},
        shutdown: #{inspect(shutdown)},
        type: #{inspect(kind)}
      }
    """
    |> String.trim()
  end

  defp resolve_child_module(kind, module_path) do
    cond do
      String.contains?(module_path, ".") ->
        String.to_atom(module_path)

      kind == :supervisor ->
        String.to_atom("Cure.Sup." <> module_path)

      true ->
        # Default to the actor naming convention.
        String.to_atom("Cure.Actor." <> module_path)
    end
  end

  # -- Literal extraction -----------------------------------------------------

  defp extract_atom(nil), do: nil
  defp extract_atom({:literal, _, atom}) when is_atom(atom), do: atom
  defp extract_atom({:variable, _, name}) when is_binary(name), do: String.to_atom(name)
  defp extract_atom(_), do: nil

  defp extract_integer(nil), do: nil
  defp extract_integer({:literal, _, n}) when is_integer(n), do: n

  defp extract_integer({:unary_op, meta, [{:literal, _, n}]}) when is_integer(n) do
    case Keyword.get(meta, :op) do
      :minus -> -n
      _ -> n
    end
  end

  defp extract_integer(_), do: nil
end
