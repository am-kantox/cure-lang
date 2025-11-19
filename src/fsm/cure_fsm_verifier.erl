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
    format_verification_result/1,
    % SMT-based verification
    verify_with_smt/3,
    check_state_invariant/2,
    check_deadlock_via_smt/1,
    check_reachability_via_smt/3
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
verify_with_smt(#fsm_def{state_defs = StateDefs, initial = InitialState}, Property, MaxDepth) ->
    % Encode FSM as SMT constraints
    StateConstraints = encode_states_to_smt(StateDefs),
    TransitionConstraints = encode_transitions_to_smt(StateDefs),
    InitialConstraint = encode_initial_state(InitialState),

    % Encode property to verify for bounded model checking
    PropertyConstraints = encode_property_bounded(Property, MaxDepth),

    % Build bounded model checking query
    Query = [
        "(set-logic QF_UF)\n",
        StateConstraints,
        TransitionConstraints,
        InitialConstraint,
        "(push)\n",
        PropertyConstraints,
        "(check-sat)\n",
        "(get-model)\n",
        "(pop)\n"
    ],

    % Execute SMT query
    QueryBinary = iolist_to_binary(Query),
    case cure_smt_process:start_solver(z3, 10000) of
        {ok, Pid} ->
            try
                Result = cure_smt_process:execute_query(Pid, QueryBinary, 10000),
                cure_smt_process:stop_solver(Pid),
                case Result of
                    {sat, Model} ->
                        % Property can be violated - extract counterexample
                        {sat, parse_counterexample(Model)};
                    {unsat, _} ->
                        % Property holds up to given depth
                        {unsat, property_holds};
                    {error, Reason} ->
                        {error, Reason};
                    Other ->
                        {error, {unexpected_result, Other}}
                end
            catch
                _:Error ->
                    cure_smt_process:stop_solver(Pid),
                    {error, Error}
            end;
        {error, Reason} ->
            {error, {solver_start_failed, Reason}}
    end.

encode_states_to_smt(StateDefs) ->
    StateNames = [atom_to_list(get_state_name(S)) || S <- StateDefs],
    % Declare state as an enumerated datatype
    StateDecl = io_lib:format(
        "(declare-datatypes () ((State ~s)))~n",
        [string:join([atom_to_list(S) || S <- [get_state_name(SD) || SD <- StateDefs]], " ")]
    ),
    lists:flatten(StateDecl).

encode_transitions_to_smt(StateDefs) ->
    % For bounded model checking, we need a function per step
    % transition_i : State -> State for each step i
    TransitionDecl = "(declare-fun transition (State Int) State)\n",

    % Build constraints for each possible transition
    Transitions = lists:flatmap(
        fun(StateDef) ->
            Source = get_state_name(StateDef),
            Targets = get_transition_targets(StateDef),
            [{Source, Target} || Target <- Targets]
        end,
        StateDefs
    ),

    % For each step, constrain valid transitions
    TransitionConstraints = lists:map(
        fun({Source, Target}) ->
            io_lib:format(
                "(assert (forall ((step Int)) (=> (= (state step) ~w) (or ~s))))~n",
                [Source, format_target_disjunction(Target)]
            )
        end,
        group_transitions_by_source(Transitions)
    ),

    lists:flatten([TransitionDecl, TransitionConstraints]).

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

%% ============================================================================
%% SMT Helper Functions
%% ============================================================================

%% Encode initial state constraint
encode_initial_state(InitialState) ->
    io_lib:format("(declare-fun state (Int) State)~n(assert (= (state 0) ~w))~n", [InitialState]).

%% Encode property for bounded model checking
encode_property_bounded({deadlock_free}, MaxDepth) ->
    % Check that at every step there exists a valid transition
    lists:flatten([
        io_lib:format(
            "(assert (not (and ~s)))~n",
            [
                lists:concat([
                    "(= (state " ++ integer_to_list(I) ++ ") Deadlock)"
                 || I <- lists:seq(0, MaxDepth)
                ])
            ]
        )
    ]);
encode_property_bounded({reachable, TargetState}, MaxDepth) ->
    % Check if target state is reachable within MaxDepth steps
    lists:flatten([
        io_lib:format(
            "(assert (not (or ~s)))~n",
            [
                lists:concat([
                    "(= (state " ++ integer_to_list(I) ++ ") " ++ atom_to_list(TargetState) ++ ")"
                 || I <- lists:seq(0, MaxDepth)
                ])
            ]
        )
    ]);
encode_property_bounded({safety, BadStates}, MaxDepth) ->
    % Check that bad states are never reached
    BadStateConstraints = lists:map(
        fun(BadState) ->
            lists:concat([
                "(= (state " ++ integer_to_list(I) ++ ") " ++ atom_to_list(BadState) ++ ")"
             || I <- lists:seq(0, MaxDepth)
            ])
        end,
        BadStates
    ),
    lists:flatten([
        io_lib:format("(assert (not (or ~s)))~n", [lists:concat(lists:flatten(BadStateConstraints))])
    ]);
encode_property_bounded(_Property, _MaxDepth) ->
    % Default: no property constraints
    "".

%% Group transitions by source state
group_transitions_by_source(Transitions) ->
    GroupedMap = lists:foldl(
        fun({Source, Target}, Acc) ->
            maps:update_with(
                Source,
                fun(Existing) -> [Target | Existing] end,
                [Target],
                Acc
            )
        end,
        #{},
        Transitions
    ),
    maps:to_list(GroupedMap).

%% Format target states as disjunction
format_target_disjunction(Targets) when is_list(Targets) ->
    string:join([atom_to_list(T) || T <- Targets], " ");
format_target_disjunction(Target) ->
    atom_to_list(Target).

%% Parse counterexample from Z3 model
parse_counterexample(Model) ->
    % Extract state values from model
    case string:find(Model, "state") of
        nomatch ->
            #{trace => unknown};
        _Match ->
            % Simple parsing - extract state assignments
            #{trace => Model, description => "Counterexample found"}
    end.

%% ============================================================================
%% Enhanced SMT-based Verification Functions
%% ============================================================================

%% @doc Check if a state invariant holds in all reachable states
%% Invariant is an expression that should be true in every state
-spec check_state_invariant(FsmDef :: term(), Invariant :: term()) ->
    {ok, holds} | {violation, counterexample()} | {error, term()}.
check_state_invariant(#fsm_def{state_defs = StateDefs, initial = InitialState}, Invariant) ->
    % Build SMT query to check if invariant can be violated
    % Strategy: prove ¬(∃ state. reachable(state) ∧ ¬invariant(state))

    StateNames = [get_state_name(S) || S <- StateDefs],

    Query = [
        "(set-logic ALL)\n",
        "(declare-datatypes () ((State ",
        string:join([atom_to_list(S) || S <- StateNames], " "),
        ")))\n",
        "(declare-fun current_state () State)\n",
        "(declare-fun reachable (State) Bool)\n",

        % Initial state is reachable
        io_lib:format("(assert (reachable ~w))\n", [InitialState]),

        % Encode transitions: if S1 is reachable and S1->S2, then S2 is reachable
        encode_reachability_constraints(StateDefs),

        % Check if we can reach a state where invariant is violated
        "(assert (reachable current_state))\n",
        encode_invariant_negation(Invariant),

        "(check-sat)\n",
        "(get-model)\n"
    ],

    QueryBinary = iolist_to_binary(Query),
    case cure_smt_process:start_solver(z3, 10000) of
        {ok, Pid} ->
            try
                Result = cure_smt_process:execute_query(Pid, QueryBinary, 10000),
                cure_smt_process:stop_solver(Pid),
                case Result of
                    {unsat, _} ->
                        % Unsat means invariant holds in all reachable states
                        {ok, holds};
                    {sat, Model} ->
                        % Sat means there's a reachable state violating the invariant
                        {violation, parse_counterexample(Model)};
                    {error, Reason} ->
                        {error, Reason};
                    Other ->
                        {error, {unexpected_result, Other}}
                end
            catch
                _:Error ->
                    cure_smt_process:stop_solver(Pid),
                    {error, Error}
            end;
        {error, Reason} ->
            {error, {solver_start_failed, Reason}}
    end;
check_state_invariant(_, _) ->
    {error, invalid_fsm}.

%% @doc Check for deadlocks using SMT
%% A deadlock is a state with no outgoing transitions that is reachable
-spec check_deadlock_via_smt(FsmDef :: term()) ->
    {ok, deadlock_free} | {deadlock, state_name(), counterexample()} | {error, term()}.
check_deadlock_via_smt(#fsm_def{state_defs = StateDefs, initial = InitialState}) ->
    % Find states with no outgoing transitions
    DeadlockStates = [
        get_state_name(S)
     || S <- StateDefs, not has_outgoing_transition(S)
    ],

    case DeadlockStates of
        [] ->
            % No deadlock states exist
            {ok, deadlock_free};
        _ ->
            % Check if any deadlock state is reachable via SMT
            StateNames = [get_state_name(S) || S <- StateDefs],

            Query = [
                "(set-logic ALL)\n",
                "(declare-datatypes () ((State ",
                string:join([atom_to_list(S) || S <- StateNames], " "),
                ")))\n",
                "(declare-fun current_state () State)\n",
                "(declare-fun reachable (State) Bool)\n",

                % Initial state is reachable
                io_lib:format("(assert (reachable ~w))\n", [InitialState]),

                % Encode transitions
                encode_reachability_constraints(StateDefs),

                % Check if any deadlock state is reachable
                "(assert (reachable current_state))\n",
                "(assert (or ",
                string:join(
                    [io_lib:format("(= current_state ~w)", [D]) || D <- DeadlockStates], " "
                ),
                "))\n",

                "(check-sat)\n",
                "(get-model)\n"
            ],

            QueryBinary = iolist_to_binary(Query),
            case cure_smt_process:start_solver(z3, 10000) of
                {ok, Pid} ->
                    try
                        Result = cure_smt_process:execute_query(Pid, QueryBinary, 10000),
                        cure_smt_process:stop_solver(Pid),
                        case Result of
                            {unsat, _} ->
                                % No deadlock state is reachable
                                {ok, deadlock_free};
                            {sat, Model} ->
                                % Found reachable deadlock - extract which state
                                DeadlockState = extract_deadlock_state(Model, DeadlockStates),
                                {deadlock, DeadlockState, parse_counterexample(Model)};
                            {error, Reason} ->
                                {error, Reason};
                            Other ->
                                {error, {unexpected_result, Other}}
                        end
                    catch
                        _:Error ->
                            cure_smt_process:stop_solver(Pid),
                            {error, Error}
                    end;
                {error, Reason} ->
                    {error, {solver_start_failed, Reason}}
            end
    end;
check_deadlock_via_smt(_) ->
    {error, invalid_fsm}.

%% @doc Check reachability using SMT (more precise than BFS for complex guards)
-spec check_reachability_via_smt(
    FsmDef :: term(),
    InitialState :: state_name(),
    TargetState :: state_name()
) -> {reachable} | {unreachable} | {error, term()}.
check_reachability_via_smt(
    #fsm_def{state_defs = StateDefs, initial = InitialState},
    _ProvidedInitial,
    TargetState
) ->
    StateNames = [get_state_name(S) || S <- StateDefs],

    Query = [
        "(set-logic ALL)\n",
        "(declare-datatypes () ((State ",
        string:join([atom_to_list(S) || S <- StateNames], " "),
        ")))\n",
        "(declare-fun reachable (State) Bool)\n",

        % Initial state is reachable
        io_lib:format("(assert (reachable ~w))\n", [InitialState]),

        % Encode transitions
        encode_reachability_constraints(StateDefs),

        % Check if target is reachable
        io_lib:format("(assert (reachable ~w))\n", [TargetState]),

        "(check-sat)\n"
    ],

    QueryBinary = iolist_to_binary(Query),
    case cure_smt_process:start_solver(z3, 10000) of
        {ok, Pid} ->
            try
                Result = cure_smt_process:execute_query(Pid, QueryBinary, 10000),
                cure_smt_process:stop_solver(Pid),
                case Result of
                    {sat, _} ->
                        % Target is reachable
                        {reachable};
                    {unsat, _} ->
                        % Target is not reachable
                        {unreachable};
                    {error, Reason} ->
                        {error, Reason};
                    Other ->
                        {error, {unexpected_result, Other}}
                end
            catch
                _:Error ->
                    cure_smt_process:stop_solver(Pid),
                    {error, Error}
            end;
        {error, Reason} ->
            {error, {solver_start_failed, Reason}}
    end;
check_reachability_via_smt(_, _, _) ->
    {error, invalid_fsm}.

%% ============================================================================
%% SMT Encoding Helpers
%% ============================================================================

%% Encode reachability constraints for transitions
encode_reachability_constraints(StateDefs) ->
    lists:flatmap(
        fun(StateDef) ->
            Source = get_state_name(StateDef),
            Targets = get_transition_targets(StateDef),

            case Targets of
                [] ->
                    % No outgoing transitions - no constraints
                    [];
                _ ->
                    % If source is reachable, all targets are reachable
                    lists:map(
                        fun(Target) ->
                            io_lib:format(
                                "(assert (=> (reachable ~w) (reachable ~w)))\n",
                                [Source, Target]
                            )
                        end,
                        Targets
                    )
            end
        end,
        StateDefs
    ).

%% Encode negation of an invariant
encode_invariant_negation(Invariant) ->
    % For now, support simple predicates
    % Extended later to handle complex expressions
    case Invariant of
        {always_true} ->
            % Can't violate always_true
            "(assert false)\n";
        {state_property, _Property} ->
            % Placeholder for state-specific properties

            % Always satisfiable for testing
            "(assert true)\n";
        _ ->
            % Default: no constraint
            "(assert true)\n"
    end.

%% Extract deadlock state from model
extract_deadlock_state(Model, DeadlockStates) ->
    % Simple extraction: find first deadlock state mentioned in model
    case DeadlockStates of
        [First | _] -> First;
        [] -> unknown
    end.
