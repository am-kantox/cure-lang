%% Cure Programming Language - Enhanced SMT Guard Verification
%% Phase 4: Advanced guard analysis using Z3 SMT solver
-module(cure_guard_smt).

-moduledoc """
# Enhanced SMT Guard Verification

Phase 4 enhancement for guard analysis using Z3 SMT solver.

## Features

### Guard Completeness Verification
Prove that guards cover all possible input cases:
```cure
def abs(x: Int): Int when x >= 0 = x
def abs(x: Int): Int when x < 0 = -x
% SMT proves: ∀x. (x >= 0) ∨ (x < 0)  ✅ Complete
```

### Counterexample Generation
Find inputs not covered by any guard:
```cure
def sign(x: Int): Int when x > 0 = 1
def sign(x: Int): Int when x < 0 = -1
% SMT finds: x = 0 is uncovered  ⚠️
```

### Guard Consistency Verification
Detect contradictory or unreachable guards:
```cure
def foo(x: Int): Int when x > 0 and x < 0 = 1
% SMT proves: ∀x. ¬(x > 0 ∧ x < 0)  ❌ Inconsistent
```

### Subsumption Detection
Find guards subsumed by earlier guards:
```cure
def foo(x: Int): Int when x > 0 = x
def foo(x: Int): Int when x > 5 = x * 2
% SMT proves: (x > 5) ⊆ (x > 0)  ⚠️ Clause 2 unreachable
```

## SMT Integration

Uses Z3 via the `cure_smt_process` module:
- Generates SMT-LIB 2.0 queries
- Handles integer and boolean constraints
- Provides counterexamples when available
""".

-include("../parser/cure_ast.hrl").

-export([
    % Completeness verification
    verify_guard_completeness/2,
    find_uncovered_inputs/2,

    % Consistency verification
    verify_guard_consistency/1,
    check_guard_satisfiability/1,

    % Subsumption detection
    verify_guard_subsumption/2,
    find_subsumed_clauses/1,

    % Counterexample generation
    generate_counterexample/2,
    format_counterexample/1,

    % SMT query generation
    generate_completeness_query/2,
    generate_subsumption_query/2,
    generate_consistency_query/1
]).

%% ============================================================================
%% Guard Completeness Verification
%% ============================================================================

%% @doc Verify that guards cover all possible inputs
%% Returns {complete, []} or {incomplete, Counterexamples}
-spec verify_guard_completeness([#function_clause{}], map()) ->
    {complete, []} | {incomplete, [term()]}.
verify_guard_completeness(Clauses, TypeEnv) ->
    % Extract all guards
    Guards = [
        C#function_clause.constraint
     || C <- Clauses,
        C#function_clause.constraint =/= undefined
    ],

    case Guards of
        [] ->
            % No guards - incomplete (needs catch-all)
            {incomplete, [{reason, no_guards}]};
        _ ->
            % Check if any clause has no guard (catch-all)
            HasCatchAll = lists:any(
                fun(C) -> C#function_clause.constraint =:= undefined end,
                Clauses
            ),

            case HasCatchAll of
                true ->
                    {complete, []};
                false ->
                    % Use SMT to check completeness
                    verify_guards_complete_smt(Guards, TypeEnv)
            end
    end.

%% Verify completeness using SMT
verify_guards_complete_smt(Guards, _TypeEnv) ->
    try
        % Generate completeness query: ∀x. G1 ∨ G2 ∨ ... ∨ Gn
        Query = generate_completeness_query(Guards, #{}),

        % Send to SMT solver
        case cure_smt_process:query(Query) of
            {ok, <<"unsat", _/binary>>} ->
                % unsat means ¬(G1 ∨ G2 ∨ ...) is unsatisfiable
                % Therefore G1 ∨ G2 ∨ ... is a tautology
                {complete, []};
            {ok, <<"sat", _/binary>>} ->
                % sat means we found a counterexample
                {incomplete, [{smt_result, sat}]};
            {ok, <<"unknown", _/binary>>} ->
                % SMT solver couldn't decide - conservative
                {incomplete, [{smt_result, unknown}]};
            {error, Reason} ->
                % SMT error - assume incomplete
                {incomplete, [{smt_error, Reason}]}
        end
    catch
        _:_ ->
            % On error, conservatively assume incomplete
            {incomplete, [{error, smt_failure}]}
    end.

%% @doc Find specific inputs not covered by any guard
-spec find_uncovered_inputs([#function_clause{}], map()) -> [term()].
find_uncovered_inputs(Clauses, TypeEnv) ->
    case verify_guard_completeness(Clauses, TypeEnv) of
        {complete, []} ->
            [];
        {incomplete, _} ->
            % Try to find concrete counterexamples
            Guards = [
                C#function_clause.constraint
             || C <- Clauses,
                C#function_clause.constraint =/= undefined
            ],
            generate_counterexample(Guards, TypeEnv)
    end.

%% ============================================================================
%% Guard Consistency Verification
%% ============================================================================

%% @doc Verify that a guard is satisfiable (not contradictory)
-spec verify_guard_consistency(expr()) -> consistent | inconsistent | unknown.
verify_guard_consistency(undefined) ->
    consistent;
verify_guard_consistency(Guard) ->
    case check_guard_satisfiability(Guard) of
        {satisfiable, _} -> consistent;
        unsatisfiable -> inconsistent;
        unknown -> unknown
    end.

%% @doc Check if a guard is satisfiable
-spec check_guard_satisfiability(expr()) ->
    {satisfiable, term()} | unsatisfiable | unknown.
check_guard_satisfiability(Guard) ->
    try
        Query = generate_consistency_query(Guard),
        case cure_smt_process:query(Query) of
            {ok, <<"sat", _/binary>>} ->
                {satisfiable, true};
            {ok, <<"unsat", _/binary>>} ->
                unsatisfiable;
            {ok, <<"unknown", _/binary>>} ->
                unknown;
            {error, _} ->
                unknown
        end
    catch
        _:_ ->
            unknown
    end.

%% ============================================================================
%% Guard Subsumption Detection
%% ============================================================================

%% @doc Check if Guard1 subsumes Guard2 (Guard1 ⊆ Guard2)
%% Meaning: whenever Guard1 is true, Guard2 is also true
-spec verify_guard_subsumption(expr(), expr()) -> boolean() | unknown.
verify_guard_subsumption(Guard1, Guard2) ->
    try
        % Check if Guard1 => Guard2 is valid
        Query = generate_subsumption_query(Guard1, Guard2),
        case cure_smt_process:query(Query) of
            {ok, <<"unsat", _/binary>>} ->
                % unsat means (Guard1 ∧ ¬Guard2) is unsatisfiable
                % Therefore Guard1 => Guard2 is valid
                true;
            {ok, <<"sat", _/binary>>} ->
                % sat means we found a case where Guard1 is true but Guard2 is false
                false;
            {ok, <<"unknown", _/binary>>} ->
                unknown;
            {error, _} ->
                unknown
        end
    catch
        _:_ ->
            unknown
    end.

%% @doc Find clauses whose guards are subsumed by earlier clauses
-spec find_subsumed_clauses([#function_clause{}]) -> [{integer(), integer()}].
find_subsumed_clauses(Clauses) ->
    ClausesWithIndices = lists:zip(lists:seq(1, length(Clauses)), Clauses),

    lists:flatten(
        lists:map(
            fun({Idx, Clause}) ->
                Guard = Clause#function_clause.constraint,
                case Guard of
                    undefined ->
                        [];
                    _ ->
                        % Check against all previous clauses
                        EarlierClauses = lists:sublist(ClausesWithIndices, Idx - 1),
                        lists:filtermap(
                            fun({EarlierIdx, EarlierClause}) ->
                                EarlierGuard = EarlierClause#function_clause.constraint,
                                case EarlierGuard of
                                    undefined ->
                                        % Catch-all subsumes everything
                                        {true, {Idx, EarlierIdx}};
                                    _ ->
                                        % Check subsumption using SMT
                                        case verify_guard_subsumption(EarlierGuard, Guard) of
                                            true ->
                                                {true, {Idx, EarlierIdx}};
                                            _ ->
                                                false
                                        end
                                end
                            end,
                            EarlierClauses
                        )
                end
            end,
            ClausesWithIndices
        )
    ).

%% ============================================================================
%% Counterexample Generation
%% ============================================================================

%% @doc Generate counterexamples for incomplete guards
-spec generate_counterexample([expr()], map()) -> [term()].
generate_counterexample([], _TypeEnv) ->
    [{uncovered, all_inputs}];
generate_counterexample(Guards, _TypeEnv) ->
    try
        % Create query to find input not covered by any guard
        % ∃x. ¬(G1 ∨ G2 ∨ ... ∨ Gn)
        Query = generate_negated_completeness_query(Guards),

        case cure_smt_process:query(Query) of
            {ok, <<"sat\n", Model/binary>>} ->
                % Parse model to extract counterexample
                parse_smt_model(Model);
            {ok, <<"unsat", _/binary>>} ->
                % No counterexample (guards are complete)
                [];
            _ ->
                [{smt_unavailable, true}]
        end
    catch
        _:_ ->
            [{error, counterexample_generation_failed}]
    end.

%% Parse SMT model to extract variable values
parse_smt_model(Model) ->
    % Simple parsing for demonstration
    % Real implementation would parse full SMT model
    [{example_input, Model}].

%% @doc Format counterexample for display
-spec format_counterexample(term()) -> binary().
format_counterexample({uncovered, all_inputs}) ->
    <<"All inputs are uncovered (no guards)">>;
format_counterexample({example_input, Value}) ->
    iolist_to_binary(io_lib:format("Example uncovered input: ~p", [Value]));
format_counterexample({smt_unavailable, true}) ->
    <<"SMT solver unavailable - cannot generate counterexample">>;
format_counterexample(Other) ->
    iolist_to_binary(io_lib:format("~p", [Other])).

%% ============================================================================
%% SMT Query Generation
%% ============================================================================

%% @doc Generate SMT query to check guard completeness
%% Query: (assert (not (or G1 G2 ... Gn)))
%% If unsat, guards are complete
-spec generate_completeness_query([expr()], map()) -> iolist().
generate_completeness_query(Guards, _TypeEnv) ->
    % Collect all variables
    Vars = collect_guard_variables(Guards),

    % Generate variable declarations
    VarDecls = [io_lib:format("(declare-const ~s Int)~n", [[V]]) || V <- Vars],

    % Generate guard expressions
    GuardExprs = [guard_to_smt(G) || G <- Guards],

    % Create disjunction of all guards
    Disjunction =
        case GuardExprs of
            [] -> "false";
            [Single] -> Single;
            Multiple -> ["(or ", string:join(Multiple, " "), ")"]
        end,

    % Assert negation (to check if there exists an input not covered)
    [
        VarDecls,
        "(assert (not ",
        Disjunction,
        "))~n",
        "(check-sat)~n",
        "(get-model)~n"
    ].

%% Generate query with negation for counterexample finding
generate_negated_completeness_query(Guards) ->
    generate_completeness_query(Guards, #{}).

%% @doc Generate SMT query to check guard subsumption
%% Query: (assert (and G1 (not G2)))
%% If unsat, G1 => G2 (G1 subsumes G2)
-spec generate_subsumption_query(expr(), expr()) -> iolist().
generate_subsumption_query(Guard1, Guard2) ->
    Vars = collect_guard_variables([Guard1, Guard2]),
    VarDecls = [io_lib:format("(declare-const ~s Int)~n", [[V]]) || V <- Vars],

    G1_SMT = guard_to_smt(Guard1),
    G2_SMT = guard_to_smt(Guard2),

    [
        VarDecls,
        "(assert (and ",
        G1_SMT,
        " (not ",
        G2_SMT,
        ")))~n",
        "(check-sat)~n"
    ].

%% @doc Generate SMT query to check guard consistency
%% Query: (assert G)
%% If unsat, guard is inconsistent
-spec generate_consistency_query(expr()) -> iolist().
generate_consistency_query(Guard) ->
    Vars = collect_guard_variables([Guard]),
    VarDecls = [io_lib:format("(declare-const ~s Int)~n", [[V]]) || V <- Vars],

    GuardSMT = guard_to_smt(Guard),

    [
        VarDecls,
        "(assert ",
        GuardSMT,
        ")~n",
        "(check-sat)~n"
    ].

%% ============================================================================
%% Helper Functions
%% ============================================================================

%% Collect all variables used in guards
collect_guard_variables(Guards) ->
    lists:usort(
        lists:flatten(
            [collect_vars_from_expr(G) || G <- Guards, G =/= undefined]
        )
    ).

collect_vars_from_expr(#identifier_expr{name = Name}) ->
    [atom_to_list(Name)];
collect_vars_from_expr(#binary_op_expr{left = Left, right = Right}) ->
    collect_vars_from_expr(Left) ++ collect_vars_from_expr(Right);
collect_vars_from_expr(#unary_op_expr{operand = Operand}) ->
    collect_vars_from_expr(Operand);
collect_vars_from_expr(_) ->
    [].

%% Convert guard expression to SMT-LIB format
guard_to_smt(#binary_op_expr{op = 'andalso', left = Left, right = Right}) ->
    ["(and ", guard_to_smt(Left), " ", guard_to_smt(Right), ")"];
guard_to_smt(#binary_op_expr{op = 'orelse', left = Left, right = Right}) ->
    ["(or ", guard_to_smt(Left), " ", guard_to_smt(Right), ")"];
guard_to_smt(#binary_op_expr{op = 'not', left = Expr}) ->
    ["(not ", guard_to_smt(Expr), ")"];
guard_to_smt(#binary_op_expr{op = '>', left = Left, right = Right}) ->
    ["(> ", expr_to_smt(Left), " ", expr_to_smt(Right), ")"];
guard_to_smt(#binary_op_expr{op = '<', left = Left, right = Right}) ->
    ["(< ", expr_to_smt(Left), " ", expr_to_smt(Right), ")"];
guard_to_smt(#binary_op_expr{op = '>=', left = Left, right = Right}) ->
    ["(>= ", expr_to_smt(Left), " ", expr_to_smt(Right), ")"];
guard_to_smt(#binary_op_expr{op = '=<', left = Left, right = Right}) ->
    ["(<= ", expr_to_smt(Left), " ", expr_to_smt(Right), ")"];
guard_to_smt(#binary_op_expr{op = '<=', left = Left, right = Right}) ->
    ["(<= ", expr_to_smt(Left), " ", expr_to_smt(Right), ")"];
guard_to_smt(#binary_op_expr{op = '==', left = Left, right = Right}) ->
    ["(= ", expr_to_smt(Left), " ", expr_to_smt(Right), ")"];
guard_to_smt(#binary_op_expr{op = '=:=', left = Left, right = Right}) ->
    ["(= ", expr_to_smt(Left), " ", expr_to_smt(Right), ")"];
guard_to_smt(#binary_op_expr{op = '/=', left = Left, right = Right}) ->
    ["(not (= ", expr_to_smt(Left), " ", expr_to_smt(Right), "))"];
guard_to_smt(#binary_op_expr{op = '=/=', left = Left, right = Right}) ->
    ["(not (= ", expr_to_smt(Left), " ", expr_to_smt(Right), "))"];
guard_to_smt(#literal_expr{value = true}) ->
    "true";
guard_to_smt(#literal_expr{value = false}) ->
    "false";
guard_to_smt(_) ->
    "true".

expr_to_smt(#identifier_expr{name = Name}) ->
    atom_to_list(Name);
expr_to_smt(#literal_expr{value = Value}) when is_integer(Value) ->
    integer_to_list(Value);
expr_to_smt(#binary_op_expr{op = '+', left = Left, right = Right}) ->
    ["(+ ", expr_to_smt(Left), " ", expr_to_smt(Right), ")"];
expr_to_smt(#binary_op_expr{op = '-', left = Left, right = Right}) ->
    ["(- ", expr_to_smt(Left), " ", expr_to_smt(Right), ")"];
expr_to_smt(#binary_op_expr{op = '*', left = Left, right = Right}) ->
    ["(* ", expr_to_smt(Left), " ", expr_to_smt(Right), ")"];
expr_to_smt(#binary_op_expr{op = '/', left = Left, right = Right}) ->
    ["(div ", expr_to_smt(Left), " ", expr_to_smt(Right), ")"];
expr_to_smt(#binary_op_expr{op = '%', left = Left, right = Right}) ->
    ["(mod ", expr_to_smt(Left), " ", expr_to_smt(Right), ")"];
expr_to_smt(#binary_op_expr{op = 'rem', left = Left, right = Right}) ->
    ["(mod ", expr_to_smt(Left), " ", expr_to_smt(Right), ")"];
expr_to_smt(#unary_op_expr{op = '-', operand = Operand}) ->
    ["(- ", expr_to_smt(Operand), ")"];
expr_to_smt(_) ->
    "0".
