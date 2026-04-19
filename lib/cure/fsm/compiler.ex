defmodule Cure.FSM.Compiler do
  @moduledoc """
  Compiles Cure FSM MetaAST definitions into BEAM modules.

  Supports two compilation modes:

  - **Simple mode** (no `on_transition` block): generates a `gen_statem` module
    with one `handle_event/4` clause per transition. Supports `when` guards,
    `do` actions, and `!`/`?` event suffixes.

  - **Callback mode** (`on_transition` present): generates a `GenServer`-based
    module that embeds a transition table and delegates to user-defined
    `on_transition` clauses, plus optional lifecycle callbacks (`on_enter`,
    `on_exit`, `on_failure`, `on_timer`).

  Both modes export a uniform API: `start_link/0,1`, `send_event/2`,
  `get_state/1`, plus `transitions/0` and `allowed?/2` for introspection.
  """

  alias Cure.Pipeline.Events

  @doc """
  Compile an FSM MetaAST node to Erlang abstract forms.

  For **simple-mode** FSMs returns `{:ok, forms}` where `forms` is a list of
  Erlang abstract forms ready for `:compile.forms/2`.

  For **callback-mode** FSMs (when the container carries an `:on_transition`
  metadata key) the module is generated, compiled and loaded eagerly as a
  side-effect, and the function returns `{:ok, {:callback_mode, module}}`
  where `module` is the loaded module atom. In that case there are no forms
  to write to disk -- the caller should not invoke `:compile.forms/2`.
  """
  @spec compile(tuple(), keyword()) ::
          {:ok, list()} | {:ok, {:callback_mode, module()}}
  def compile(ast, opts \\ []) do
    {:container, meta, _transition_nodes} = ast

    if Keyword.has_key?(meta, :on_transition) do
      compile_callback_mode(ast, opts)
    else
      compile_simple_mode(ast, opts)
    end
  end

  # ============================================================================
  # Simple mode: gen_statem (backward-compatible)
  # ============================================================================

  defp compile_simple_mode(ast, opts) do
    emit? = Keyword.get(opts, :emit_events, true)
    file = Keyword.get(opts, :file, "nofile")

    {:container, meta, transition_nodes} = ast
    name = Keyword.get(meta, :name, "unnamed")
    mod_atom = fsm_module_atom(name)
    line = Keyword.get(meta, :line, 1)

    transitions = extract_transitions(transition_nodes)
    all_states = collect_states(transitions)
    initial_state = determine_initial_state(transitions)
    initial_atom = String.to_atom(String.downcase(initial_state || "unknown"))

    forms =
      [
        {:attribute, line, :module, mod_atom},
        {:attribute, line, :behaviour, :gen_statem},
        {:attribute, line, :export,
         [
           {:start_link, 0},
           {:start_link, 1},
           {:send_event, 2},
           {:get_state, 1},
           {:transitions, 0},
           {:allowed, 2},
           {:callback_mode, 0},
           {:init, 1},
           {:handle_event, 4}
         ]}
      ] ++
        [
          gen_callback_mode(line),
          gen_start_link_0(mod_atom, initial_atom, line),
          gen_start_link_1(mod_atom, line),
          gen_send_event(line),
          gen_get_state(line),
          gen_transitions_fn(transitions, line),
          gen_allowed_fn(transitions, line),
          gen_init(initial_atom, line),
          gen_handle_event(transitions, all_states, line)
        ]

    if emit? do
      Events.emit(:codegen, :module_assembled, forms, Events.meta(file, line))
    end

    {:ok, forms}
  end

  # ============================================================================
  # Callback mode: GenServer with on_transition dispatch
  # ============================================================================

  defp compile_callback_mode(ast, opts) do
    emit? = Keyword.get(opts, :emit_events, true)
    file = Keyword.get(opts, :file, "nofile")

    {:container, meta, transition_nodes} = ast
    name = Keyword.get(meta, :name, "unnamed")
    mod_atom = fsm_module_atom(name)
    line = Keyword.get(meta, :line, 1)
    timer = Keyword.get(meta, :timer)
    on_transition_clauses = Keyword.get(meta, :on_transition, [])
    on_enter_clauses = Keyword.get(meta, :on_enter, [])
    on_exit_clauses = Keyword.get(meta, :on_exit, [])
    on_failure_clauses = Keyword.get(meta, :on_failure, [])
    on_timer_clauses = Keyword.get(meta, :on_timer, [])
    on_start_clauses = Keyword.get(meta, :on_start, [])
    on_stop_clauses = Keyword.get(meta, :on_stop, [])
    notify_transitions? = Keyword.get(meta, :notify_transitions, false)
    auto_caller? = Keyword.get(meta, :auto_caller, false)

    transitions = extract_transitions(transition_nodes)
    initial_state = Keyword.get(meta, :initial_state) || determine_initial_state(transitions)
    initial_atom = String.to_atom(String.downcase(initial_state || "unknown"))

    # Build the transition table as a list of {from, event, to, kind} tuples
    trans_table = build_transition_table(transitions)

    # Detect hard states: states where the sole outgoing event is hard (!)
    hard_states = detect_hard_states(transitions)

    # Detect soft events
    soft_events = detect_soft_events(transitions)

    # Generate the Elixir module source and compile it
    module_code =
      generate_genserver_module(
        mod_atom,
        initial_atom,
        trans_table,
        hard_states,
        soft_events,
        timer,
        on_transition_clauses,
        on_enter_clauses,
        on_exit_clauses,
        on_failure_clauses,
        on_timer_clauses,
        on_start_clauses,
        on_stop_clauses,
        notify_transitions?,
        auto_caller?
      )

    # Compile the generated Elixir source to BEAM. The generated module
    # contains several defensive branches (partial-struct returns,
    # on_start variants, soft-event fallthroughs, etc.) that the Elixir
    # type system cannot prove reachable from the closed-world view of a
    # single callback clause -- silence that noise during compilation.
    {result, _diagnostics} =
      Code.with_diagnostics([log: false], fn ->
        Code.compile_string(module_code, file)
      end)

    [{^mod_atom, bytecode}] = result

    # Load the module
    :code.purge(mod_atom)
    {:module, ^mod_atom} = :code.load_binary(mod_atom, ~c"#{file}", bytecode)

    if emit? do
      Events.emit(:codegen, :module_assembled, mod_atom, Events.meta(file, line))
    end

    # The module has already been compiled and loaded as a side-effect above;
    # return a tagged marker carrying the module atom so the caller does not
    # need to re-derive it from the AST.
    {:ok, {:callback_mode, mod_atom}}
  end

  # -- Transition table helpers ------------------------------------------------

  defp build_transition_table(transitions) do
    Enum.map(transitions, fn t ->
      from = if t.from == "*", do: :wildcard, else: String.to_atom(String.downcase(t.from))
      to = String.to_atom(String.downcase(t.to))
      event = String.to_atom(String.downcase(t.event))
      kind = Map.get(t, :event_kind, :normal)
      {from, event, to, kind}
    end)
  end

  defp detect_hard_states(transitions) do
    transitions
    |> Enum.filter(&(Map.get(&1, :event_kind) == :hard))
    |> Enum.group_by(& &1.from)
    |> Enum.flat_map(fn {from, trans} ->
      all_events = transitions |> Enum.filter(&(&1.from == from)) |> Enum.map(& &1.event) |> Enum.uniq()

      if length(all_events) == 1 do
        event = String.to_atom(String.downcase(hd(trans).event))
        [{String.to_atom(String.downcase(from)), event}]
      else
        []
      end
    end)
  end

  defp detect_soft_events(transitions) do
    transitions
    |> Enum.filter(&(Map.get(&1, :event_kind) == :soft))
    |> Enum.map(fn t -> String.to_atom(String.downcase(t.event)) end)
    |> Enum.uniq()
  end

  # -- Elixir source generation for callback mode ------------------------------

  defp generate_genserver_module(
         mod_atom,
         initial_atom,
         trans_table,
         hard_states,
         soft_events,
         timer,
         on_transition_clauses,
         on_enter_clauses,
         on_exit_clauses,
         on_failure_clauses,
         on_timer_clauses,
         on_start_clauses,
         on_stop_clauses,
         notify_transitions?,
         auto_caller?
       ) do
    trans_table_str = inspect(trans_table)
    hard_states_str = inspect(hard_states)
    soft_events_str = inspect(soft_events)

    on_transition_fn = generate_callback_fn(:do_on_transition, 4, on_transition_clauses)
    on_enter_fn = generate_lifecycle_fn(:do_on_enter, 2, on_enter_clauses)
    on_exit_fn = generate_lifecycle_fn(:do_on_exit, 2, on_exit_clauses)
    on_failure_fn = generate_lifecycle_fn(:do_on_failure, 3, on_failure_clauses)
    on_timer_fn = generate_lifecycle_fn(:do_on_timer, 2, on_timer_clauses)
    on_start_fn = generate_lifecycle_fn(:do_on_start, 1, on_start_clauses)
    on_stop_fn = generate_lifecycle_fn(:do_on_stop, 2, on_stop_clauses)

    timer_init = if timer, do: "Process.send_after(self(), :on_timer, #{timer})", else: ""
    timer_handler = if timer, do: generate_timer_handler(timer), else: ""
    auto_caller_init = if auto_caller?, do: "true", else: "false"
    notify_transitions_flag = if notify_transitions?, do: "true", else: "false"

    """
    defmodule :"#{mod_atom}" do
      use GenServer

      alias Cure.FSM.State, as: FsmState

      @transition_table #{trans_table_str}
      @hard_states #{hard_states_str}
      @soft_events #{soft_events_str}
      @notify_transitions #{notify_transitions_flag}
      @auto_caller #{auto_caller_init}

      # -- Public API ----------------------------------------------------------

      def start_link, do: start_link(%FsmState{})
      def start_link(init_data) do
        GenServer.start_link(__MODULE__, init_data)
      end

      def send_event(pid, event), do: GenServer.cast(pid, {:event, event, nil})
      def send_event(pid, event, payload), do: GenServer.cast(pid, {:event, event, payload})

      def get_state(pid), do: GenServer.call(pid, :get_state)

      def get_fsm_state(pid), do: GenServer.call(pid, :get_fsm_state)

      def transitions, do: @transition_table

      def initial_state, do: :#{initial_atom}

      def allowed?(from, to) do
        Enum.any?(@transition_table, fn {f, _e, t, _k} ->
          (f == from or f == :wildcard) and t == to
        end)
      end

      def responds?(from, event) do
        Enum.any?(@transition_table, fn {f, e, _t, _k} ->
          (f == from or f == :wildcard) and e == event
        end)
      end

      # -- GenServer callbacks -------------------------------------------------

      @impl GenServer
      def init(init_data) do
        fsm_state = FsmState.from_init(init_data)

        fsm_state =
          if @auto_caller and is_nil(fsm_state.caller) do
            # When no caller was provided, fall back to the spawning process
            # recorded by Cure.FSM.Runtime, if any.
            case Process.get(:cure_fsm_spawner) do
              pid when is_pid(pid) -> %FsmState{fsm_state | caller: pid}
              _ -> fsm_state
            end
          else
            fsm_state
          end

        FsmState.register_self(fsm_state)

        fsm_state =
          case do_on_start(fsm_state) do
            {:ok, %FsmState{} = s} -> FsmState.register_self(s)
            {:ok, partial} ->
              s = FsmState.merge(fsm_state, partial)
              FsmState.register_self(s)
            _ -> fsm_state
          end

        #{timer_init}
        {:ok, %{current: :#{initial_atom}, fsm_state: fsm_state, history: []}}
      end

      @impl GenServer
      def terminate(reason, state) do
        _ = do_on_stop(reason, state.fsm_state)
        :ok
      end

      @impl GenServer
      def handle_call(:get_state, _from, state) do
        {:reply, {state.current, state.fsm_state.payload}, state}
      end

      def handle_call(:get_fsm_state, _from, state) do
        {:reply, {state.current, state.fsm_state}, state}
      end

      @impl GenServer
      def handle_cast({:event, event, event_payload}, state) do
        # Check if the transition is allowed
        allowed_targets =
          Enum.flat_map(@transition_table, fn {from, ev, to, _kind} ->
            if (from == state.current or from == :wildcard) and ev == event, do: [to], else: []
          end)

        if allowed_targets == [] do
          # No transition for this event from current state
          if event in @soft_events do
            {:noreply, state}
          else
            do_on_failure(event, event_payload, state.fsm_state)
            {:noreply, state}
          end
        else
          # Call on_exit
          _ = do_on_exit(state.current, state.fsm_state)

          # Call on_transition
          case do_on_transition(state.current, event, event_payload, state.fsm_state) do
            {:ok, :__same__, new_payload} ->
              merged = FsmState.merge(state.fsm_state, new_payload)
              FsmState.register_self(merged)
              new_state = %{state | fsm_state: merged}
              {:noreply, new_state}

            {:ok, next, new_payload} ->
              merged = FsmState.merge(state.fsm_state, new_payload)
              actual_next = if next in allowed_targets, do: next, else: hd(allowed_targets)
              FsmState.register_self(merged)
              new_state = %{state |
                current: actual_next,
                fsm_state: merged,
                history: [{state.current, event} | Enum.take(state.history, 49)]
              }
              _ = do_on_enter(actual_next, merged)
              if @notify_transitions do
                FsmState.notify(merged, {:cure_fsm, self(),
                  {:transition, state.current, event, actual_next, merged.payload}})
              end
              case Keyword.get(@hard_states, actual_next) do
                nil -> {:noreply, new_state}
                hard_event -> {:noreply, new_state, {:continue, {:auto_transition, hard_event}}}
              end

            {:error, _reason} ->
              if event in @soft_events do
                {:noreply, state}
              else
                do_on_failure(event, event_payload, state.fsm_state)
                {:noreply, state}
              end
          end
        end
      end

      @impl GenServer
      def handle_continue({:auto_transition, event}, state) do
        handle_cast({:event, event, nil}, state)
      end

      #{timer_handler}

      # -- Helpers available inside lifecycle hook bodies ---------------------

      defp notify(message), do: Cure.FSM.State.notify_self(message)

      defp caller do
        case Cure.FSM.State.current() do
          %Cure.FSM.State{caller: c} -> c
          _ -> nil
        end
      end

      defp fsm_self, do: self()

      # -- Callback implementations --------------------------------------------

      #{on_transition_fn}
      #{on_enter_fn}
      #{on_exit_fn}
      #{on_failure_fn}
      #{on_timer_fn}
      #{on_start_fn}
      #{on_stop_fn}
    end
    """
  end

  defp generate_timer_handler(timer_ms) do
    """
      @impl GenServer
      def handle_info(:on_timer, state) do
        case do_on_timer(state.current, state.fsm_state) do
          :ok ->
            Process.send_after(self(), :on_timer, #{timer_ms})
            {:noreply, state}
          {:ok, new_payload} ->
            merged = Cure.FSM.State.merge(state.fsm_state, new_payload)
            Cure.FSM.State.register_self(merged)
            Process.send_after(self(), :on_timer, #{timer_ms})
            {:noreply, %{state | fsm_state: merged}}
          {:transition, event, new_payload} ->
            merged = Cure.FSM.State.merge(state.fsm_state, new_payload)
            Cure.FSM.State.register_self(merged)
            Process.send_after(self(), :on_timer, #{timer_ms})
            new_state = %{state | fsm_state: merged}
            handle_cast({:event, event, nil}, new_state)
          {:reschedule, new_ms} ->
            Process.send_after(self(), :on_timer, new_ms)
            {:noreply, state}
        end
      end
    """
  end

  # Generate the on_transition function from parsed clauses.
  # The clauses are match_arm AST nodes from the parser.
  # Since these are Cure AST, we generate Elixir pattern-match function clauses.
  defp generate_callback_fn(fn_name, _arity, clauses) when clauses != [] do
    clause_strs =
      Enum.map(clauses, fn {:match_arm, meta, [body]} ->
        pattern = Keyword.get(meta, :pattern)
        guard = Keyword.get(meta, :guard)
        # If the pattern is a tuple, expand its elements as separate function args
        args_str = expand_pattern_to_args(pattern)
        body_str = cure_ast_to_elixir(body)
        guard_str = if guard, do: " when #{cure_ast_to_elixir(guard)}", else: ""
        "  defp #{fn_name}(#{args_str})#{guard_str}, do: #{body_str}"
      end)

    Enum.join(clause_strs, "\n")
  end

  defp generate_callback_fn(fn_name, _arity, _clauses) do
    args = Enum.map_join(1..4, ", ", fn i -> "_arg#{i}" end)
    "  defp #{fn_name}(#{args}), do: {:ok, :__same__, _arg4}"
  end

  defp generate_lifecycle_fn(fn_name, arity, clauses) when clauses != [] do
    generate_callback_fn(fn_name, arity, clauses)
  end

  defp generate_lifecycle_fn(fn_name, arity, _clauses) do
    args = Enum.map_join(1..arity, ", ", fn i -> "_arg#{i}" end)
    "  defp #{fn_name}(#{args}), do: :ok"
  end

  # Expand a tuple pattern into comma-separated args for a function head.
  # {:tuple, [], [a, b, c, d]} -> "a, b, c, d" (4 separate args)
  # Non-tuple patterns are emitted as a single arg.
  defp expand_pattern_to_args({:tuple, _meta, elements}) do
    Enum.map_join(elements, ", ", &cure_ast_to_elixir/1)
  end

  defp expand_pattern_to_args(pattern) do
    cure_ast_to_elixir(pattern)
  end

  # -- Cure AST to Elixir source string ----------------------------------------
  # Translator for the subset used in FSM callback clauses.
  #
  # Handles literals, variables, binary/unary ops, tuples, maps, lists,
  # blocks, assignments, function calls (bare, module-qualified, and
  # common Elixir kernel calls like `send`), conditionals (`if/then/else`),
  # pattern matches, and attribute access.

  defp cure_ast_to_elixir(ast) do
    case ast do
      # Function calls: bare, module-qualified, `tuple(...)` constructor,
      # or Elixir Kernel.send/2 (which the parser emits as name = "send").
      {:function_call, meta, args} ->
        name = Keyword.get(meta, :name, "")

        case name do
          "tuple" ->
            inner = Enum.map_join(args, ", ", &cure_ast_to_elixir/1)
            "{#{inner}}"

          _ ->
            arg_strs = Enum.map_join(args, ", ", &cure_ast_to_elixir/1)
            "#{name}(#{arg_strs})"
        end

      # Literal values
      {:literal, _meta, value} when is_atom(value) ->
        inspect(value)

      {:literal, _meta, value} when is_binary(value) ->
        inspect(value)

      {:literal, _meta, value} when is_integer(value) ->
        Integer.to_string(value)

      {:literal, _meta, value} when is_float(value) ->
        Float.to_string(value)

      {:literal, _meta, value} ->
        inspect(value)

      # Variable reference
      {:variable, _meta, name} ->
        name

      # Binary operations
      {:binary_op, meta, [left, right]} ->
        op = Keyword.get(meta, :op) || Keyword.get(meta, :operator, "+")
        op_str = binary_op_to_elixir(op)
        "(#{cure_ast_to_elixir(left)} #{op_str} #{cure_ast_to_elixir(right)})"

      # Unary operations
      {:unary_op, meta, [operand]} ->
        op = Keyword.get(meta, :op) || Keyword.get(meta, :operator, "-")
        op_str = unary_op_to_elixir(op)
        "#{op_str}#{cure_ast_to_elixir(operand)}"

      # Tuple expression (direct tuple syntax)
      {:tuple, _meta, elements} ->
        inner = Enum.map_join(elements, ", ", &cure_ast_to_elixir/1)
        "{#{inner}}"

      # Map
      {:map, _meta, pairs} ->
        inner =
          Enum.map_join(pairs, ", ", fn
            {:pair, _, [k, v]} ->
              "#{cure_ast_to_elixir(k)} => #{cure_ast_to_elixir(v)}"

            {k, v} ->
              "#{cure_ast_to_elixir(k)} => #{cure_ast_to_elixir(v)}"
          end)

        "%{#{inner}}"

      # List
      {:list, _meta, elements} ->
        inner = Enum.map_join(elements, ", ", &cure_ast_to_elixir/1)
        "[#{inner}]"

      # Block: chain statements with newlines; Elixir evaluates the last
      # expression as the block's value.
      {:block, _meta, stmts} ->
        body = stmts |> Enum.map_join("\n", &cure_ast_to_elixir/1)
        "(#{body})"

      # Pattern match / assignment
      {:assignment, _meta, [lhs, rhs]} ->
        "#{cure_ast_to_elixir(lhs)} = #{cure_ast_to_elixir(rhs)}"

      # Conditional: if cond then a else b
      {:conditional, _meta, [cond_ast, then_ast, else_ast]} ->
        c = cure_ast_to_elixir(cond_ast)
        t = cure_ast_to_elixir(then_ast)
        e = cure_ast_to_elixir(else_ast)
        "(if #{c}, do: (#{t}), else: (#{e}))"

      # Attribute access: obj.field
      {:attribute_access, meta, [obj]} ->
        attr = Keyword.get(meta, :attribute)
        "#{cure_ast_to_elixir(obj)}.#{attr}"

      # Pattern match expression (match x -> arms)
      {:pattern_match, _meta, [scrutinee | arms]} ->
        scrut = cure_ast_to_elixir(scrutinee)

        arm_strs =
          Enum.map_join(arms, "\n", fn
            {:match_arm, arm_meta, [body]} ->
              pat = Keyword.get(arm_meta, :pattern)
              guard = Keyword.get(arm_meta, :guard)
              pat_str = cure_ast_to_elixir(pat)
              body_str = cure_ast_to_elixir(body)
              guard_str = if guard, do: " when #{cure_ast_to_elixir(guard)}", else: ""
              "  #{pat_str}#{guard_str} -> #{body_str}"
          end)

        "(case #{scrut} do\n#{arm_strs}\nend)"

      # Send: send(pid, msg) -- parser emits this as a function_call with
      # name "send"; handled by the function_call clause above.

      # Atom (direct)
      atom when is_atom(atom) ->
        inspect(atom)

      # String (direct)
      str when is_binary(str) ->
        inspect(str)

      # Integer (direct)
      int when is_integer(int) ->
        Integer.to_string(int)

      # Fallback
      other ->
        inspect(other)
    end
  end

  # Translate Cure operator atoms/strings into valid Elixir operator
  # source. Most match 1:1; `<>` concatenation and comparison operators
  # are kept as-is.
  defp binary_op_to_elixir(op) when is_atom(op), do: Atom.to_string(op)
  defp binary_op_to_elixir(op) when is_binary(op), do: op
  defp binary_op_to_elixir(_), do: "+"

  defp unary_op_to_elixir(op) when is_atom(op), do: Atom.to_string(op)
  defp unary_op_to_elixir(op) when is_binary(op), do: op
  defp unary_op_to_elixir(_), do: "-"

  # ============================================================================
  # Shared: Transition Extraction
  # ============================================================================

  defp extract_transitions(transition_nodes) do
    Enum.flat_map(transition_nodes, fn
      {:function_call, meta, _} ->
        if Keyword.get(meta, :name) == "transition" do
          [
            %{
              from: Keyword.get(meta, :from, "*"),
              event: Keyword.get(meta, :event, ""),
              to: Keyword.get(meta, :to, ""),
              guard: Keyword.get(meta, :guard),
              action: Keyword.get(meta, :action),
              event_kind: Keyword.get(meta, :event_kind, :normal)
            }
          ]
        else
          []
        end

      _ ->
        []
    end)
  end

  defp collect_states(transitions) do
    froms = Enum.map(transitions, & &1.from) |> Enum.reject(&(&1 == "*"))
    tos = Enum.map(transitions, & &1.to)
    (froms ++ tos) |> Enum.uniq()
  end

  defp determine_initial_state(transitions) do
    case Enum.find(transitions, fn t -> t.from != "*" end) do
      %{from: from} -> from
      nil -> nil
    end
  end

  # ============================================================================
  # Simple mode: gen_statem forms generation
  # ============================================================================

  defp gen_callback_mode(l) do
    body =
      {:cons, l, {:atom, l, :handle_event_function}, {:cons, l, {:atom, l, :state_enter}, {nil, l}}}

    {:function, l, :callback_mode, 0, [{:clause, l, [], [], [body]}]}
  end

  defp gen_start_link_0(mod_atom, _initial_atom, l) do
    body =
      {:call, l, {:remote, l, {:atom, l, :gen_statem}, {:atom, l, :start_link}},
       [{:atom, l, mod_atom}, {:map, l, []}, {nil, l}]}

    {:function, l, :start_link, 0, [{:clause, l, [], [], [body]}]}
  end

  defp gen_start_link_1(mod_atom, l) do
    body =
      {:call, l, {:remote, l, {:atom, l, :gen_statem}, {:atom, l, :start_link}},
       [{:atom, l, mod_atom}, {:var, l, :V_init_data}, {nil, l}]}

    {:function, l, :start_link, 1, [{:clause, l, [{:var, l, :V_init_data}], [], [body]}]}
  end

  defp gen_send_event(l) do
    body =
      {:call, l, {:remote, l, {:atom, l, :gen_statem}, {:atom, l, :cast}}, [{:var, l, :V_pid}, {:var, l, :V_event}]}

    {:function, l, :send_event, 2, [{:clause, l, [{:var, l, :V_pid}, {:var, l, :V_event}], [], [body]}]}
  end

  defp gen_get_state(l) do
    body =
      {:call, l, {:remote, l, {:atom, l, :gen_statem}, {:atom, l, :call}}, [{:var, l, :V_pid}, {:atom, l, :get_state}]}

    {:function, l, :get_state, 1, [{:clause, l, [{:var, l, :V_pid}], [], [body]}]}
  end

  # transitions/0 -- returns the compiled transition table as a list
  defp gen_transitions_fn(transitions, l) do
    table_elements =
      Enum.reduce(Enum.reverse(transitions), {nil, l}, fn t, acc ->
        from_atom = if t.from == "*", do: :wildcard, else: String.to_atom(String.downcase(t.from))
        to_atom = String.to_atom(String.downcase(t.to))
        event_atom = String.to_atom(String.downcase(t.event))
        kind = Map.get(t, :event_kind, :normal)

        elem =
          {:tuple, l,
           [
             {:atom, l, from_atom},
             {:atom, l, event_atom},
             {:atom, l, to_atom},
             {:atom, l, kind}
           ]}

        {:cons, l, elem, acc}
      end)

    {:function, l, :transitions, 0, [{:clause, l, [], [], [table_elements]}]}
  end

  # allowed/2 -- check if a (from, event) pair has a valid target
  defp gen_allowed_fn(transitions, l) do
    # Build clauses for each transition
    match_clauses =
      Enum.map(transitions, fn t ->
        from_pat = if t.from == "*", do: {:var, l, :_}, else: {:atom, l, String.to_atom(String.downcase(t.from))}
        event_atom = String.to_atom(String.downcase(t.event))
        {:clause, l, [from_pat, {:atom, l, event_atom}], [], [{:atom, l, true}]}
      end)

    catch_all = {:clause, l, [{:var, l, :_}, {:var, l, :_}], [], [{:atom, l, false}]}

    {:function, l, :allowed, 2, match_clauses ++ [catch_all]}
  end

  defp gen_init(initial_atom, l) do
    body =
      {:tuple, l,
       [
         {:atom, l, :ok},
         {:atom, l, initial_atom},
         {:var, l, :V_init_data}
       ]}

    {:function, l, :init, 1, [{:clause, l, [{:var, l, :V_init_data}], [], [body]}]}
  end

  defp gen_handle_event(transitions, _all_states, l) do
    # Separate hard events for auto-fire actions
    hard_transitions = Enum.filter(transitions, &(Map.get(&1, :event_kind) == :hard))

    soft_events =
      transitions |> Enum.filter(&(Map.get(&1, :event_kind) == :soft)) |> Enum.map(& &1.event) |> Enum.uniq()

    transition_clauses =
      Enum.flat_map(transitions, fn trans ->
        to_atom = String.to_atom(String.downcase(trans.to))
        event_atom = String.to_atom(String.downcase(trans.event))
        guard_ast = Map.get(trans, :guard)
        action_ast = Map.get(trans, :action)

        from =
          if trans.from == "*" do
            :_
          else
            String.to_atom(String.downcase(trans.from))
          end

        event_kind = Map.get(trans, :event_kind, :normal)
        [gen_transition_clause(from, event_atom, to_atom, guard_ast, action_ast, event_kind, hard_transitions, l)]
      end)

    # Soft-event catch-all: silently keep state for unmatched soft events
    soft_catch_alls =
      Enum.map(soft_events, fn event ->
        event_atom = String.to_atom(String.downcase(event))

        {:clause, l, [{:atom, l, :cast}, {:atom, l, event_atom}, {:var, l, :_}, {:var, l, :_}], [],
         [{:atom, l, :keep_state_and_data}]}
      end)

    get_state_clause = gen_get_state_clause(l)
    enter_clause = gen_enter_clause(l)

    catch_all =
      {:clause, l, [{:var, l, :_}, {:var, l, :_}, {:var, l, :_}, {:var, l, :_}], [], [{:atom, l, :keep_state_and_data}]}

    all_clauses = [get_state_clause, enter_clause] ++ transition_clauses ++ soft_catch_alls ++ [catch_all]

    {:function, l, :handle_event, 4, all_clauses}
  end

  defp gen_transition_clause(from, event_atom, to_atom, guard_ast, action_ast, _event_kind, hard_transitions, l) do
    from_pattern =
      case from do
        :_ -> {:var, l, :_}
        atom -> {:atom, l, atom}
      end

    guard_forms =
      if guard_ast do
        {:ok, guard_form} = Cure.Compiler.Codegen.compile_expr(guard_ast)
        [[guard_form]]
      else
        []
      end

    data_expr =
      if action_ast do
        {:ok, action_form} = Cure.Compiler.Codegen.compile_expr(action_ast)
        action_form
      else
        {:var, l, :V_data}
      end

    # For hard events (!) entering a state that has a sole hard outgoing event,
    # emit {next_state, To, Data, [{next_event, internal, HardEvent}]}
    next_hard =
      Enum.find(hard_transitions, fn ht ->
        ht.from != "*" and String.to_atom(String.downcase(ht.from)) == to_atom
      end)

    body =
      if next_hard do
        next_event_atom = String.to_atom(String.downcase(next_hard.event))
        # {next_state, To, Data, [{next_event, cast, Event}]}
        action_list =
          {:cons, l, {:tuple, l, [{:atom, l, :next_event}, {:atom, l, :cast}, {:atom, l, next_event_atom}]}, {nil, l}}

        {:tuple, l,
         [
           {:atom, l, :next_state},
           {:atom, l, to_atom},
           data_expr,
           action_list
         ]}
      else
        {:tuple, l,
         [
           {:atom, l, :next_state},
           {:atom, l, to_atom},
           data_expr
         ]}
      end

    {:clause, l,
     [
       {:atom, l, :cast},
       {:atom, l, event_atom},
       from_pattern,
       {:var, l, :V_data}
     ], guard_forms, [body]}
  end

  defp gen_get_state_clause(l) do
    reply_action =
      {:tuple, l,
       [
         {:atom, l, :reply},
         {:var, l, :V_from},
         {:tuple, l, [{:var, l, :V_state}, {:var, l, :V_data}]}
       ]}

    body =
      {:tuple, l,
       [
         {:atom, l, :keep_state_and_data},
         {:cons, l, reply_action, {nil, l}}
       ]}

    {:clause, l,
     [
       {:tuple, l, [{:atom, l, :call}, {:var, l, :V_from}]},
       {:atom, l, :get_state},
       {:var, l, :V_state},
       {:var, l, :V_data}
     ], [], [body]}
  end

  defp gen_enter_clause(l) do
    {:clause, l,
     [
       {:atom, l, :enter},
       {:var, l, :_},
       {:var, l, :_},
       {:var, l, :_}
     ], [], [{:tuple, l, [{:atom, l, :keep_state_and_data}, {nil, l}]}]}
  end

  # -- Helpers -----------------------------------------------------------------

  @doc false
  def fsm_module_atom(name) do
    String.to_atom("Cure.FSM." <> name)
  end
end
