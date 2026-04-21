defmodule Cure.App.Compiler do
  @moduledoc """
  Compiles Cure `app` containers into BEAM modules implementing the
  OTP `Application` behaviour.

  The generated module exposes `start/2`, `stop/1`, and, when the
  container declares any `on_phase :name` clauses, `start_phase/3`.
  `start/2` delegates to the user's `on_start` clauses (if any) before
  returning `{:ok, <root_sup>.start_link()}`; when the container omits
  `on_start`, the root supervisor is started directly.

  ## Module resolution

  The generated module is named `:"Cure.App.<Name>"`. The root
  supervisor is resolved by the same conventions documented in
  `docs/SUPERVISION.md`:

    * A dotted name (`App.Root`) is used verbatim as `:"App.Root"`.
    * An undotted name (`Root`) resolves to `:"Cure.Sup.Root"` when
      it starts with uppercase, or falls back to the dotted form.
    * The shorthand `sup Root` reuses the `sup Name` soft-keyword form
      parsed by the supervisor parser and resolves to
      `:"Cure.Sup.Root"`.

  ## Return value

  Mirrors `Cure.Actor.Compiler` and `Cure.Sup.Compiler`: the module is
  compiled and loaded eagerly; the call returns `{:ok, {:app, module_atom}}`.
  When `:output_dir` is given the bytecode is also persisted via
  `Cure.Compiler.BeamWriter.write_beam/4`.
  """

  alias Cure.Compiler.BeamWriter
  alias Cure.Pipeline.Events

  @doc """
  Compile an `{:container, [container_type: :app, ...], body}` node.

  Returns `{:ok, {:app, module_atom}}` on success.

  ## Options
    * `:emit_events` -- whether to emit pipeline events (default `true`).
    * `:file`        -- filename used for diagnostics (default `"nofile"`).
    * `:output_dir`  -- when set, the compiled bytecode is also written
      to `<output_dir>/<module_atom>.beam`.
  """
  @spec compile(tuple(), keyword()) :: {:ok, {:app, module()}}
  def compile({:container, meta, _body} = _ast, opts \\ []) do
    emit? = Keyword.get(opts, :emit_events, true)
    file = Keyword.get(opts, :file, "nofile")
    output_dir = Keyword.get(opts, :output_dir)

    name = Keyword.get(meta, :name, "Unnamed")
    mod_atom = app_module_atom(name)
    line = Keyword.get(meta, :line, 1)

    root_ast = Keyword.get(meta, :root)
    root_module = resolve_root_module(root_ast)

    on_start_clauses = Keyword.get(meta, :on_start, [])
    on_stop_clauses = Keyword.get(meta, :on_stop, [])

    # Collect every `on_phase :name` block (the parser emits one
    # `on_phase` keyword entry per block, not a single combined one).
    on_phase_entries =
      meta
      |> Keyword.get_values(:on_phase)
      |> List.flatten()

    module_code =
      generate_module(
        mod_atom,
        root_module,
        on_start_clauses,
        on_stop_clauses,
        on_phase_entries
      )

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

    {:ok, {:app, mod_atom}}
  end

  @doc false
  def app_module_atom(name) do
    String.to_atom("Cure.App." <> name)
  end

  @doc """
  Resolve the `root = ...` expression to an atom denoting the root
  supervisor module to start. Returns `nil` when the app declares no
  root (pure phases-only applications are valid).
  """
  @spec resolve_root_module(term()) :: atom() | nil
  def resolve_root_module(nil), do: nil

  def resolve_root_module({:literal, _, value}) when is_atom(value), do: value

  def resolve_root_module({:literal, _, value}) when is_binary(value) do
    resolve_root_module_from_string(value)
  end

  def resolve_root_module({:variable, _, name}) when is_binary(name) do
    resolve_root_module_from_string(name)
  end

  def resolve_root_module({:attribute_access, _, _} = ast) do
    case attribute_access_to_dotted(ast) do
      nil -> nil
      name -> String.to_atom(name)
    end
  end

  def resolve_root_module({:function_call, meta, _}) do
    case Keyword.get(meta, :name) do
      nil -> nil
      name -> resolve_root_module_from_string(to_string(name))
    end
  end

  def resolve_root_module({:container, meta, _}) do
    case Keyword.get(meta, :container_type) do
      :supervisor ->
        name = Keyword.get(meta, :name, "")
        if name == "", do: nil, else: String.to_atom("Cure.Sup." <> name)

      _ ->
        nil
    end
  end

  def resolve_root_module(_), do: nil

  defp resolve_root_module_from_string(""), do: nil

  defp resolve_root_module_from_string(name) do
    if String.contains?(name, ".") do
      String.to_atom(name)
    else
      case String.first(name) do
        <<c::utf8>> when c in ?A..?Z ->
          String.to_atom("Cure.Sup." <> name)

        _ ->
          String.to_atom(name)
      end
    end
  end

  defp attribute_access_to_dotted({:attribute_access, meta, [parent]}) do
    attr = Keyword.get(meta, :attribute)

    case attribute_access_to_dotted(parent) do
      nil -> nil
      path -> path <> "." <> to_string(attr)
    end
  end

  defp attribute_access_to_dotted({:variable, _, name}) when is_binary(name), do: name
  defp attribute_access_to_dotted(_), do: nil

  # -- Code generation -------------------------------------------------------

  defp generate_module(mod_atom, root_module, on_start, on_stop, on_phase_entries) do
    start_body = generate_start_body(root_module, on_start)
    stop_body = generate_stop_body(on_stop)
    start_phase_body = generate_start_phase_body(on_phase_entries)

    """
    defmodule :"#{mod_atom}" do
      use Application

      @impl Application
      def start(type, args) do
    #{start_body}
      end

      @impl Application
      def stop(state) do
    #{stop_body}
      end

    #{start_phase_body}
    end
    """
  end

  defp generate_start_body(root_module, []) do
    """
        _ = type
        _ = args
    #{start_root_module(root_module)}
    """
    |> String.trim_trailing()
  end

  defp generate_start_body(root_module, clauses) do
    clause_body =
      clauses
      |> Enum.map(&render_two_arg_clause/1)
      |> Enum.join("\n")

    """
        hook_result =
          case {type, args} do
    #{clause_body}
            _ -> :ok
          end

        case hook_result do
          {:error, _} = err ->
            err

          {:stop, _} = stop ->
            stop

          _ ->
    #{indent(start_root_module(root_module), 6)}
        end
    """
    |> String.trim_trailing()
  end

  defp start_root_module(nil) do
    """
    {:ok, self()}
    """
    |> String.trim_trailing()
  end

  defp start_root_module(mod) do
    """
    case #{inspect(mod)}.start_link() do
      {:ok, pid} -> {:ok, pid}
      {:error, {:already_started, pid}} -> {:ok, pid}
      {:error, _} = err -> err
      other -> {:ok, other}
    end
    """
    |> String.trim_trailing()
  end

  defp generate_stop_body([]) do
    """
        _ = state
        :ok
    """
    |> String.trim_trailing()
  end

  defp generate_stop_body(clauses) do
    clause_body =
      clauses
      |> Enum.map(&render_single_arg_clause/1)
      |> Enum.join("\n")

    """
        case {state} do
    #{clause_body}
          _ -> :ok
        end
    """
    |> String.trim_trailing()
  end

  defp generate_start_phase_body([]), do: ""

  defp generate_start_phase_body(entries) do
    clauses =
      Enum.map_join(entries, "\n", fn {phase, clauses} ->
        render_phase_block(phase, clauses)
      end)

    """
      @impl Application
      def start_phase(phase, start_type, phase_args) do
        case phase do
    #{clauses}
          _ -> :ok
        end
      end
    """
    |> String.trim_trailing()
  end

  defp render_phase_block(phase, clauses) do
    clause_body =
      clauses
      |> Enum.map(&render_three_arg_phase_clause/1)
      |> Enum.join("\n")

    """
          #{inspect(phase)} ->
            case {phase_args, start_type, phase_args} do
    #{clause_body}
              _ -> :ok
            end
    """
    |> String.trim_trailing()
  end

  # -- Clause rendering ------------------------------------------------------

  # Render a 1-argument clause parsed by parse_fsm_callback: `(state) -> body`.
  defp render_single_arg_clause({:match_arm, meta, [body]}) do
    pattern = Keyword.get(meta, :pattern)
    guard = Keyword.get(meta, :guard)

    pat_str =
      case pattern do
        {:tuple, _, [single]} -> Cure.FSM.Compiler.cure_ast_to_elixir(single)
        other -> Cure.FSM.Compiler.cure_ast_to_elixir(other)
      end

    body_str = Cure.FSM.Compiler.cure_ast_to_elixir(body)
    guard_str = render_guard(guard)

    "      {#{pat_str}}#{guard_str} -> #{body_str}"
  end

  # 2-argument clauses: `(type, args) -> body`.
  defp render_two_arg_clause({:match_arm, meta, [body]}) do
    pattern = Keyword.get(meta, :pattern)
    guard = Keyword.get(meta, :guard)

    {type_ast, args_ast} =
      case pattern do
        {:tuple, _, [t, a]} -> {t, a}
        {:tuple, _, [t]} -> {t, {:variable, [], "_"}}
        other -> {other, {:variable, [], "_"}}
      end

    type_str = Cure.FSM.Compiler.cure_ast_to_elixir(type_ast)
    args_str = Cure.FSM.Compiler.cure_ast_to_elixir(args_ast)
    body_str = Cure.FSM.Compiler.cure_ast_to_elixir(body)
    guard_str = render_guard(guard)

    "          {#{type_str}, #{args_str}}#{guard_str} -> #{body_str}"
  end

  # Phase clauses bind `(args, start_type, phase_args)`. The parser
  # normalises them to 1-3 element tuples inside `{:match_arm, ...}`.
  defp render_three_arg_phase_clause({:match_arm, meta, [body]}) do
    pattern = Keyword.get(meta, :pattern)
    guard = Keyword.get(meta, :guard)

    {arg_ast, type_ast, start_args_ast} =
      case pattern do
        {:tuple, _, [a, t, s]} -> {a, t, s}
        {:tuple, _, [a, t]} -> {a, t, {:variable, [], "_"}}
        {:tuple, _, [a]} -> {a, {:variable, [], "_"}, {:variable, [], "_"}}
        other -> {other, {:variable, [], "_"}, {:variable, [], "_"}}
      end

    arg_str = Cure.FSM.Compiler.cure_ast_to_elixir(arg_ast)
    type_str = Cure.FSM.Compiler.cure_ast_to_elixir(type_ast)
    start_args_str = Cure.FSM.Compiler.cure_ast_to_elixir(start_args_ast)
    body_str = Cure.FSM.Compiler.cure_ast_to_elixir(body)
    guard_str = render_guard(guard)

    "              {#{arg_str}, #{type_str}, #{start_args_str}}#{guard_str} -> #{body_str}"
  end

  defp render_guard(nil), do: ""

  defp render_guard(guard_ast) do
    " when #{Cure.FSM.Compiler.cure_ast_to_elixir(guard_ast)}"
  end

  # -- Formatting helpers ----------------------------------------------------

  defp indent(string, n) do
    pad = String.duplicate(" ", n)

    string
    |> String.split("\n")
    |> Enum.map(fn
      "" -> ""
      line -> pad <> line
    end)
    |> Enum.join("\n")
  end
end
