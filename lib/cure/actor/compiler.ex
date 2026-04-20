defmodule Cure.Actor.Compiler do
  @moduledoc """
  Compiles Cure `actor` containers into BEAM modules.

  The generated module is a `GenServer` whose primary state is a
  `%Cure.Actor.State{}` struct and whose `handle_info/2` dispatches
  each `on_message` clause in source order. Lifecycle hooks are wired
  as follows:

    * `on_start`  -> `init/1`
    * `on_stop`   -> `terminate/2`
    * `on_message` -> `handle_info/2`

  The compiler reuses the Cure-AST-to-Elixir translator exported by
  `Cure.FSM.Compiler` (via `cure_ast_to_elixir/1`) for the body of
  each clause and emits the module via `Code.compile_string/2`, so the
  generated code participates in the VM exactly like a hand-written
  GenServer.

  ## Return value

  Mirroring the FSM callback mode, the compiler loads the generated
  module eagerly and returns `{:ok, {:actor, module_atom}}`. The
  caller (usually `Cure.Compiler.Codegen.dispatch_container/4`) does
  not need to feed the result through `:compile.forms/2` -- the
  module is already loaded in the VM.
  """

  alias Cure.Pipeline.Events

  @doc """
  Compile an `{:container, [container_type: :actor, ...], body}` node.

  Returns `{:ok, {:actor, module_atom}}` on success.
  """
  @spec compile(tuple(), keyword()) :: {:ok, {:actor, module()}}
  def compile(ast, opts \\ []) do
    emit? = Keyword.get(opts, :emit_events, true)
    file = Keyword.get(opts, :file, "nofile")

    {:container, meta, _body} = ast
    name = Keyword.get(meta, :name, "unnamed")
    mod_atom = actor_module_atom(name)
    line = Keyword.get(meta, :line, 1)

    on_message = Keyword.get(meta, :on_message, [])
    on_start = Keyword.get(meta, :on_start, [])
    on_stop = Keyword.get(meta, :on_stop, [])
    init_expr = Keyword.get(meta, :init)

    module_code =
      generate_module(
        mod_atom,
        init_expr,
        on_message,
        on_start,
        on_stop
      )

    {result, _diagnostics} =
      Code.with_diagnostics([log: false], fn ->
        Code.compile_string(module_code, file)
      end)

    [{^mod_atom, bytecode}] = result
    :code.purge(mod_atom)
    {:module, ^mod_atom} = :code.load_binary(mod_atom, ~c"#{file}", bytecode)

    if emit? do
      Events.emit(:codegen, :module_assembled, mod_atom, Events.meta(file, line))
    end

    {:ok, {:actor, mod_atom}}
  end

  @doc false
  def actor_module_atom(name) do
    String.to_atom("Cure.Actor." <> name)
  end

  # -- Code generation ---------------------------------------------------------

  defp generate_module(mod_atom, init_expr, on_message, on_start, on_stop) do
    init_payload_literal =
      case init_expr do
        nil -> "nil"
        ast -> Cure.FSM.Compiler.cure_ast_to_elixir(ast)
      end

    on_start_code = generate_on_start_fun(on_start)
    on_message_clauses = generate_on_message_clauses(on_message)
    on_stop_code = generate_on_stop_fun(on_stop)

    """
    defmodule :"#{mod_atom}" do
      use GenServer
      alias Cure.Actor.State, as: ActorState

      @default_payload #{init_payload_literal}

      # -- Public API -----------------------------------------------------------

      def start_link, do: start_link(%ActorState{payload: @default_payload})

      def start_link(init) do
        GenServer.start_link(__MODULE__, init)
      end

      def send_message(pid, msg), do: send(pid, msg)

      def get_state(pid), do: GenServer.call(pid, :__actor_get_state__)

      def get_actor_state(pid), do: GenServer.call(pid, :__actor_get_full_state__)

      # -- GenServer callbacks --------------------------------------------------

      @impl GenServer
      def init(init_data) do
        base = ActorState.from_init(init_data)

        base =
          case base.payload do
            nil -> %ActorState{base | payload: @default_payload}
            _ -> base
          end

        ActorState.register_self(base)

        new_state =
          case do_on_start(base) do
            {:ok, %ActorState{} = s} ->
              ActorState.register_self(s)

            {:ok, bare} ->
              merged = ActorState.merge(base, bare)
              ActorState.register_self(merged)

            :ok ->
              base

            _ ->
              base
          end

        {:ok, new_state}
      end

      @impl GenServer
      def terminate(reason, state) do
        _ = do_on_stop(reason, state)
        :ok
      end

      @impl GenServer
      def handle_call(:__actor_get_state__, _from, state) do
        {:reply, state.payload, state}
      end

      def handle_call(:__actor_get_full_state__, _from, state) do
        {:reply, state, state}
      end

      @impl GenServer
      def handle_info(msg, state) do
        do_on_message(msg, state)
      end

      # -- Helpers available inside lifecycle hook bodies ----------------------

      defp notify(message), do: ActorState.notify_self(message)

      defp caller do
        case ActorState.current() do
          %ActorState{caller: c} -> c
          _ -> nil
        end
      end

      defp actor_self, do: self()

      # -- Handler bodies ------------------------------------------------------

      #{on_start_code}

      #{on_message_clauses}

      #{on_stop_code}
    end
    """
  end

  # -- on_start body generation -----------------------------------------------

  defp generate_on_start_fun([]) do
    """
    defp do_on_start(state), do: {:ok, state}
    """
  end

  defp generate_on_start_fun(clauses) do
    clause_body =
      clauses
      |> Enum.map(&render_single_arg_clause(&1, "_unhandled"))
      |> Enum.join("\n")

    """
    defp do_on_start(state) do
      result =
        case {state} do
          #{clause_body}
          _ -> state
        end

      case result do
        %ActorState{} = s -> {:ok, s}
        :ok -> :ok
        {:ok, _} = tagged -> tagged
        other -> {:ok, other}
      end
    end
    """
  end

  # -- on_message body generation ---------------------------------------------

  defp generate_on_message_clauses([]) do
    """
    defp do_on_message(_msg, state), do: {:noreply, state}
    """
  end

  defp generate_on_message_clauses(clauses) do
    # Each clause is `{:match_arm, [pattern: {:tuple, _, [msg_pat, payload_pat]}, ...], [body]}`
    # The tuple pattern has two elements: message and payload.
    clause_strs =
      clauses
      |> Enum.map(&render_two_arg_clause/1)
      |> Enum.join("\n")

    """
    defp do_on_message(msg, state) do
      payload = state.payload

      new_payload =
        case {msg, payload} do
          #{clause_strs}
          _ -> payload
        end

      merged =
        case new_payload do
          %ActorState{} = s -> s
          bare -> ActorState.merge(state, bare)
        end

      ActorState.register_self(merged)
      {:noreply, merged}
    end
    """
  end

  # -- on_stop body generation ------------------------------------------------

  defp generate_on_stop_fun([]) do
    """
    defp do_on_stop(_reason, _state), do: :ok
    """
  end

  defp generate_on_stop_fun(clauses) do
    clause_body =
      clauses
      |> Enum.map(&render_reason_state_clause/1)
      |> Enum.join("\n")

    """
    defp do_on_stop(reason, state) do
      case {reason, state} do
        #{clause_body}
        _ -> :ok
      end
    end
    """
  end

  # -- Clause rendering --------------------------------------------------------

  # Render a 1-argument callback clause parsed by parse_fsm_callback.
  # The pattern is a `{:tuple, _, [one_ast]}` wrapping the single param.
  defp render_single_arg_clause({:match_arm, meta, [body]}, fallback) do
    pattern = Keyword.get(meta, :pattern)
    guard = Keyword.get(meta, :guard)

    pat_str =
      case pattern do
        {:tuple, _, [single]} -> Cure.FSM.Compiler.cure_ast_to_elixir(single)
        other -> Cure.FSM.Compiler.cure_ast_to_elixir(other)
      end

    body_str = Cure.FSM.Compiler.cure_ast_to_elixir(body)
    guard_str = render_guard(guard)

    _ = fallback
    "  {#{pat_str}}#{guard_str} -> #{body_str}"
  end

  # 2-argument clauses: `(msg_pattern, payload_pattern) -> body`.
  defp render_two_arg_clause({:match_arm, meta, [body]}) do
    pattern = Keyword.get(meta, :pattern)
    guard = Keyword.get(meta, :guard)

    {msg_ast, payload_ast} =
      case pattern do
        {:tuple, _, [m, p]} -> {m, p}
        # Single-argument `on_message` clauses bind the message only;
        # use a wildcard for the payload so existing state flows through.
        {:tuple, _, [m]} -> {m, {:variable, [], "_"}}
        other -> {other, {:variable, [], "_"}}
      end

    msg_str = Cure.FSM.Compiler.cure_ast_to_elixir(msg_ast)
    payload_str = Cure.FSM.Compiler.cure_ast_to_elixir(payload_ast)
    body_str = Cure.FSM.Compiler.cure_ast_to_elixir(body)
    guard_str = render_guard(guard)

    "  {#{msg_str}, #{payload_str}}#{guard_str} -> #{body_str}"
  end

  # on_stop clauses: `(reason, state) -> body`.
  defp render_reason_state_clause({:match_arm, meta, [body]}) do
    pattern = Keyword.get(meta, :pattern)
    guard = Keyword.get(meta, :guard)

    {reason_ast, state_ast} =
      case pattern do
        {:tuple, _, [r, s]} -> {r, s}
        {:tuple, _, [r]} -> {r, {:variable, [], "_"}}
        other -> {other, {:variable, [], "_"}}
      end

    reason_str = Cure.FSM.Compiler.cure_ast_to_elixir(reason_ast)
    state_str = Cure.FSM.Compiler.cure_ast_to_elixir(state_ast)
    body_str = Cure.FSM.Compiler.cure_ast_to_elixir(body)
    guard_str = render_guard(guard)

    "  {#{reason_str}, #{state_str}}#{guard_str} -> #{body_str}"
  end

  defp render_guard(nil), do: ""

  defp render_guard(guard_ast) do
    " when #{Cure.FSM.Compiler.cure_ast_to_elixir(guard_ast)}"
  end
end
