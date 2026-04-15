defmodule Cure.FSM.Compiler do
  @moduledoc """
  Compiles Cure FSM MetaAST definitions into `gen_statem` BEAM modules.

  Takes a `{:container, [container_type: :fsm, ...], transitions}` node and
  produces Erlang abstract forms that implement the OTP `gen_statem` behaviour.

  The generated module exports:
  - `start_link/0`, `start_link/1` -- start the FSM process
  - `send_event/2` -- cast an event to the FSM
  - `get_state/1` -- synchronous call returning `{state, data}`
  - `callback_mode/0`, `init/1`, `handle_event/4` -- gen_statem callbacks
  """

  alias Cure.Pipeline.Events

  @doc """
  Compile an FSM MetaAST node to Erlang abstract forms.

  Returns `{:ok, forms}` where forms are ready for `:compile.forms/2`.
  """
  @spec compile(tuple(), keyword()) :: {:ok, list()}
  def compile(ast, opts \\ []) do
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
          gen_init(initial_atom, line),
          gen_handle_event(transitions, all_states, line)
        ]

    if emit? do
      Events.emit(:codegen, :module_assembled, forms, Events.meta(file, line))
    end

    {:ok, forms}
  end

  # -- Transition Extraction ---------------------------------------------------

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
              action: Keyword.get(meta, :action)
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

  # -- gen_statem callback_mode ------------------------------------------------

  defp gen_callback_mode(l) do
    # callback_mode() -> [handle_event_function, state_enter].
    body =
      {:cons, l, {:atom, l, :handle_event_function}, {:cons, l, {:atom, l, :state_enter}, {nil, l}}}

    {:function, l, :callback_mode, 0, [{:clause, l, [], [], [body]}]}
  end

  # -- start_link/0 -----------------------------------------------------------

  defp gen_start_link_0(mod_atom, initial_atom, l) do
    # start_link() -> gen_statem:start_link(Module, InitialState, []).
    body =
      {:call, l, {:remote, l, {:atom, l, :gen_statem}, {:atom, l, :start_link}},
       [{:atom, l, mod_atom}, {:atom, l, initial_atom}, {nil, l}]}

    {:function, l, :start_link, 0, [{:clause, l, [], [], [body]}]}
  end

  # -- start_link/1 -----------------------------------------------------------

  defp gen_start_link_1(mod_atom, l) do
    # start_link(InitData) -> gen_statem:start_link(Module, InitData, []).
    body =
      {:call, l, {:remote, l, {:atom, l, :gen_statem}, {:atom, l, :start_link}},
       [{:atom, l, mod_atom}, {:var, l, :V_init_data}, {nil, l}]}

    {:function, l, :start_link, 1, [{:clause, l, [{:var, l, :V_init_data}], [], [body]}]}
  end

  # -- send_event/2 -----------------------------------------------------------

  defp gen_send_event(l) do
    # send_event(Pid, Event) -> gen_statem:cast(Pid, Event).
    body =
      {:call, l, {:remote, l, {:atom, l, :gen_statem}, {:atom, l, :cast}}, [{:var, l, :V_pid}, {:var, l, :V_event}]}

    {:function, l, :send_event, 2, [{:clause, l, [{:var, l, :V_pid}, {:var, l, :V_event}], [], [body]}]}
  end

  # -- get_state/1 -----------------------------------------------------------

  defp gen_get_state(l) do
    # get_state(Pid) -> gen_statem:call(Pid, get_state).
    body =
      {:call, l, {:remote, l, {:atom, l, :gen_statem}, {:atom, l, :call}}, [{:var, l, :V_pid}, {:atom, l, :get_state}]}

    {:function, l, :get_state, 1, [{:clause, l, [{:var, l, :V_pid}], [], [body]}]}
  end

  # -- init/1 -----------------------------------------------------------------

  defp gen_init(initial_atom, l) do
    # init(InitState) -> {ok, InitState, #{}}.
    # We use the argument as initial state atom if it's an atom, otherwise use the default.
    body =
      {:tuple, l,
       [
         {:atom, l, :ok},
         {:atom, l, initial_atom},
         {:map, l, []}
       ]}

    # Clause for atom argument (from start_link/0)
    clause_atom =
      {:clause, l, [{:var, l, :_}], [], [body]}

    {:function, l, :init, 1, [clause_atom]}
  end

  # -- handle_event/4 ----------------------------------------------------------

  defp gen_handle_event(transitions, _all_states, l) do
    # Generate one clause per transition (with optional guards and actions)
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

        [gen_transition_clause(from, event_atom, to_atom, guard_ast, action_ast, l)]
      end)

    # get_state handler: handle_event({call, From}, get_state, State, Data) ->
    #   {keep_state_and_data, [{reply, From, {State, Data}}]}
    get_state_clause = gen_get_state_clause(l)

    # state_enter handler (no-op)
    enter_clause = gen_enter_clause(l)

    # Catch-all clause: handle_event(_, _, _, _) -> keep_state_and_data
    catch_all =
      {:clause, l, [{:var, l, :_}, {:var, l, :_}, {:var, l, :_}, {:var, l, :_}], [], [{:atom, l, :keep_state_and_data}]}

    all_clauses = [get_state_clause, enter_clause] ++ transition_clauses ++ [catch_all]

    {:function, l, :handle_event, 4, all_clauses}
  end

  defp gen_transition_clause(from, event_atom, to_atom, guard_ast, action_ast, l) do
    from_pattern =
      case from do
        :_ -> {:var, l, :_}
        atom -> {:atom, l, atom}
      end

    # Compile guard if present
    guard_forms =
      if guard_ast do
        # Compile the guard AST to an Erlang guard expression
        case Cure.Compiler.Codegen.compile_expr(guard_ast) do
          {:ok, guard_form} -> [[guard_form]]
          _ -> []
        end
      else
        []
      end

    # If there's an action, the body updates Data; otherwise just pass Data through
    data_expr =
      if action_ast do
        # Action modifies the data map. Compile the action expression.
        case Cure.Compiler.Codegen.compile_expr(action_ast) do
          {:ok, action_form} -> action_form
          _ -> {:var, l, :V_data}
        end
      else
        {:var, l, :V_data}
      end

    body =
      {:tuple, l,
       [
         {:atom, l, :next_state},
         {:atom, l, to_atom},
         data_expr
       ]}

    {:clause, l,
     [
       {:atom, l, :cast},
       {:atom, l, event_atom},
       from_pattern,
       {:var, l, :V_data}
     ], guard_forms, [body]}
  end

  defp gen_get_state_clause(l) do
    # handle_event({call, From}, get_state, State, Data) ->
    #   {keep_state_and_data, [{reply, From, {State, Data}}]}
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
    # handle_event(enter, _OldState, _State, Data) -> {keep_state_and_data, []}
    {:clause, l,
     [
       {:atom, l, :enter},
       {:var, l, :_},
       {:var, l, :_},
       {:var, l, :_}
     ], [], [{:tuple, l, [{:atom, l, :keep_state_and_data}, {nil, l}]}]}
  end

  # -- Helpers -----------------------------------------------------------------

  defp fsm_module_atom(name) do
    # "TrafficLight" -> :"Cure.FSM.TrafficLight"
    # Elixir-style module atom with Cure.FSM. prefix, preserving PascalCase
    String.to_atom("Cure.FSM." <> name)
  end
end
