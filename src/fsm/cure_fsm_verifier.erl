-module(cure_fsm_verifier).

%% FSM Verification using SMT
%% Checks: Deadlocks, Reachability, Liveness, Safety properties
-export([
    verify_fsm/1,
    check_deadlocks/1,
    check_reachability/3,
    check_liveness/1,
    check_safety/2,
    verify_all_properties/1,
    format_verification_result/1
]).

-include("../parser/cure_ast.hrl").

%% Type definitions
-type verification_result() ::
    {ok, [property_result()]} | {error, term()}.

-type property_result() ::
    {deadlock_free}
    | {has_deadlock, state_name()}
    | {reachable, state_name()}
    | {unreachable, state_name()}
    | {liveness_satisfied}
    | {liveness_violated, term()}
    | {safety_satisfied}
    | {safety_violated, counterexample()}.

-type state_name() :: atom().
-type counterexample() :: #{state_name() => term()}.

%% ============================================================================
%% Main API
%% ============================================================================

%% @doc Verify all properties of an FSM
-spec verify_fsm(FsmDef :: term()) -> verification_result().
verify_fsm(#fsm_def{name = Name} = FsmDef) ->
    io:format("Verifying FSM: ~p~n", [Name]),

    try
        % Run all verification checks
        DeadlockResults = check_deadlocks(FsmDef),
        ReachabilityResults = check_all_reachability(FsmDef),
        LivenessResults = check_liveness(FsmDef),

        AllResults = DeadlockResults ++ ReachabilityResults ++ LivenessResults,
        {ok, AllResults}
    catch
        Error:Reason:_Stack ->
            {error, {verification_failed, Error, Reason}}
    end;
verify_fsm(_) ->
    {error, not_an_fsm}.

%% @doc Verify all properties and generate detailed report
-spec verify_all_properties(FsmDef :: term()) -> [property_result()].
verify_all_properties(FsmDef) ->
    case verify_fsm(FsmDef) of
        {ok, Results} -> Results;
        {error, _} -> []
    end.

%% ============================================================================
%% Deadlock Detection
%% ============================================================================

%% @doc Check if the FSM has any deadlock states
-spec check_deadlocks(FsmDef :: term()) -> [property_result()].
check_deadlocks(#fsm_def{state_defs = StateDefs}) ->
    % For each state, check if there's at least one outgoing transition
    lists:filtermap(
        fun(StateDef) ->
            case has_outgoing_transition(StateDef) of
                true ->
                    % No deadlock
                    false;
                false ->
                    {true, {has_deadlock, get_state_name(StateDef)}}
            end
        end,
        StateDefs
    ).

has_outgoing_transition(#state_def{transitions = Transitions}) when length(Transitions) > 0 ->
    true;
has_outgoing_transition(_) ->
    false.

get_state_name(#state_def{name = Name}) ->
    Name;
get_state_name(_) ->
    unknown.

%% ============================================================================
%% Reachability Analysis
%% ============================================================================

%% @doc Check if a target state is reachable from initial state
-spec check_reachability(
    FsmDef :: term(),
    InitialState :: state_name(),
    TargetState :: state_name()
) -> property_result().
check_reachability(#fsm_def{state_defs = StateDefs}, InitialState, TargetState) ->
    % Build transition graph
    TransitionGraph = build_transition_graph(StateDefs),

    % Perform breadth-first search to check reachability
    case bfs_reachable(InitialState, TargetState, TransitionGraph, [InitialState], #{}) of
        true -> {reachable, TargetState};
        false -> {unreachable, TargetState}
    end;
check_reachability(_, _, _) ->
    {error, invalid_fsm}.

%% @doc Check reachability for all states from initial state
check_all_reachability(#fsm_def{initial = Initial, state_defs = StateDefs} = FsmDef) ->
    AllStates = [get_state_name(S) || S <- StateDefs],
    lists:map(
        fun(TargetState) ->
            check_reachability(FsmDef, Initial, TargetState)
        end,
        AllStates
    );
check_all_reachability(_) ->
    [].

%% Build a map of state -> [reachable states]
build_transition_graph(StateDefs) ->
    lists:foldl(
        fun(StateDef, Acc) ->
            StateName = get_state_name(StateDef),
            Targets = get_transition_targets(StateDef),
            maps:put(StateName, Targets, Acc)
        end,
        #{},
        StateDefs
    ).

get_transition_targets(#state_def{transitions = Transitions}) ->
    lists:filtermap(
        fun
            (#transition{target = Target}) when Target =/= undefined ->
                {true, Target};
            (_) ->
                false
        end,
        Transitions
    );
get_transition_targets(_) ->
    [].

%% Breadth-first search for reachability
bfs_reachable(Current, Target, _Graph, _Queue, _Visited) when Current =:= Target ->
    true;
bfs_reachable(_Current, _Target, _Graph, [], _Visited) ->
    % Queue empty, not reachable
    false;
bfs_reachable(Current, Target, Graph, [Current | RestQueue], Visited) ->
    case maps:is_key(Current, Visited) of
        true ->
            % Already visited, skip
            bfs_reachable(Current, Target, Graph, RestQueue, Visited);
        false ->
            % Mark as visited
            NewVisited = maps:put(Current, true, Visited),

            % Get neighbors
            Neighbors = maps:get(Current, Graph, []),

            % Check if target is in neighbors
            case lists:member(Target, Neighbors) of
                true ->
                    true;
                false ->
                    % Add neighbors to queue
                    NewQueue = RestQueue ++ Neighbors,
                    case NewQueue of
                        [] ->
                            false;
                        [Next | _] ->
                            bfs_reachable(Next, Target, Graph, NewQueue, NewVisited)
                    end
            end
    end.

%% ============================================================================
%% Liveness Properties
%% ============================================================================

%% @doc Check liveness properties (system can always make progress)
-spec check_liveness(FsmDef :: term()) -> [property_result()].
check_liveness(#fsm_def{} = FsmDef) ->
    % Check for terminal states (states with no outgoing transitions)
    % If all states have transitions, liveness is satisfied
    DeadlockResults = check_deadlocks(FsmDef),

    case DeadlockResults of
        [] ->
            % No deadlocks = liveness satisfied
            [{liveness_satisfied}];
        Deadlocks ->
            % Deadlocks violate liveness
            [{liveness_violated, {deadlocks, Deadlocks}}]
    end;
check_liveness(_) ->
    [{error, invalid_fsm}].

%% ============================================================================
%% Safety Properties
%% ============================================================================

%% @doc Check safety property (bad states are never reached)
-spec check_safety(FsmDef :: term(), BadStates :: [state_name()]) -> property_result().
check_safety(#fsm_def{initial = Initial} = FsmDef, BadStates) ->
    % Check if any bad state is reachable from initial state
    ReachableBadStates = lists:filter(
        fun(BadState) ->
            case check_reachability(FsmDef, Initial, BadState) of
                {reachable, _} -> true;
                _ -> false
            end
        end,
        BadStates
    ),

    case ReachableBadStates of
        [] ->
            {safety_satisfied};
        [BadState | _] ->
            % Found reachable bad state - generate counterexample
            Path = find_path_to_state(FsmDef, Initial, BadState),
            {safety_violated, #{
                bad_state => BadState,
                path => Path
            }}
    end;
check_safety(_, _) ->
    {error, invalid_fsm}.

%% Find a path from initial state to target state
find_path_to_state(#fsm_def{state_defs = StateDefs}, InitialState, TargetState) ->
    TransitionGraph = build_transition_graph(StateDefs),
    bfs_find_path(InitialState, TargetState, TransitionGraph, [{InitialState, []}], #{}).

bfs_find_path(_Current, _Target, _Graph, [], _Visited) ->
    no_path;
bfs_find_path(Current, Target, Graph, [{Current, Path} | RestQueue], Visited) ->
    case Current =:= Target of
        true ->
            lists:reverse([Current | Path]);
        false ->
            case maps:is_key(Current, Visited) of
                true ->
                    bfs_find_path(Current, Target, Graph, RestQueue, Visited);
                false ->
                    NewVisited = maps:put(Current, true, Visited),
                    Neighbors = maps:get(Current, Graph, []),

                    NewQueue = RestQueue ++ [{N, [Current | Path]} || N <- Neighbors],
                    case NewQueue of
                        [] ->
                            no_path;
                        [{Next, _} | _] ->
                            bfs_find_path(Next, Target, Graph, NewQueue, NewVisited)
                    end
            end
    end.

%% ============================================================================
%% SMT-based Verification (Advanced)
%% ============================================================================

%% @doc Verify FSM properties using Z3 (bounded model checking)
verify_with_smt(#fsm_def{state_defs = StateDefs}, Property, MaxDepth) ->
    % Encode FSM as SMT constraints
    StateConstraints = encode_states_to_smt(StateDefs),
    TransitionConstraints = encode_transitions_to_smt(StateDefs),

    % Encode property to verify
    PropertyConstraint = encode_property_to_smt(Property),

    % Build bounded model checking query
    Query = [
        "(set-logic QF_UF)\n",
        StateConstraints,
        TransitionConstraints,
        "(push)\n",
        PropertyConstraint,
        "(check-sat)\n",
        "(pop)\n"
    ],

    % Query Z3
    case cure_z3:query(Query) of
        {ok, "sat"} ->
            {sat, can_violate_property};
        {ok, "unsat"} ->
            {unsat, property_holds};
        {error, Reason} ->
            {error, Reason}
    end.

encode_states_to_smt(StateDefs) ->
    StateNames = [atom_to_list(get_state_name(S)) || S <- StateDefs],
    [
        "(declare-datatype State (",
        string:join(["(" ++ S ++ ")" || S <- StateNames], " "),
        "))\n"
    ].

encode_transitions_to_smt(StateDefs) ->
    Transitions = lists:flatmap(
        fun(StateDef) ->
            Source = get_state_name(StateDef),
            Targets = get_transition_targets(StateDef),
            [{Source, Target} || Target <- Targets]
        end,
        StateDefs
    ),

    [
        "(declare-fun transition (State) State)\n",
        [
            io_lib:format("(assert (= (transition ~s) ~s))~n", [Source, Target])
         || {Source, Target} <- Transitions
        ]
    ].

encode_property_to_smt(_Property) ->
    % Placeholder - would encode specific property
    % For now, check if initial state can reach any deadlock
    "(assert (not (exists ((s State)) (and (= s Deadlock) (= (transition s) s)))))\n".

%% ============================================================================
%% Result Formatting
%% ============================================================================

%% @doc Format verification results for display
-spec format_verification_result(verification_result()) -> binary().
format_verification_result({ok, Results}) ->
    ResultStrings = lists:map(fun format_property_result/1, Results),
    iolist_to_binary([
        "FSM Verification Results:\n",
        string:join(ResultStrings, "\n")
    ]);
format_verification_result({error, Reason}) ->
    iolist_to_binary(io_lib:format("Verification error: ~p", [Reason])).

format_property_result({deadlock_free}) ->
    "  ✓ No deadlocks detected";
format_property_result({has_deadlock, State}) ->
    io_lib:format("  ✗ Deadlock detected in state: ~p", [State]);
format_property_result({reachable, State}) ->
    io_lib:format("  ✓ State ~p is reachable", [State]);
format_property_result({unreachable, State}) ->
    io_lib:format("  ⚠ Warning: State ~p is unreachable", [State]);
format_property_result({liveness_satisfied}) ->
    "  ✓ Liveness property satisfied (system can always progress)";
format_property_result({liveness_violated, Reason}) ->
    io_lib:format("  ✗ Liveness violated: ~p", [Reason]);
format_property_result({safety_satisfied}) ->
    "  ✓ Safety property satisfied (bad states unreachable)";
format_property_result({safety_violated, #{bad_state := BadState, path := Path}}) ->
    io_lib:format("  ✗ Safety violated: bad state ~p reachable via path: ~p", [BadState, Path]);
format_property_result(Other) ->
    io_lib:format("  ? Unknown result: ~p", [Other]).
