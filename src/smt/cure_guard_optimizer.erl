%% Cure Programming Language - Guard Optimization via SMT
%% Detects and eliminates redundant guards using Z3/SMT solver
-module(cure_guard_optimizer).

-moduledoc """
# Guard Optimization with SMT

This module uses SMT solvers to detect and eliminate redundant guards in
Cure code. A guard is redundant if it's always true given preceding guards,
or if it's implied by other guards.

## Examples

### Redundant Guard Detection
```cure
if n > 10 then
    if n > 5 then  % Redundant! n > 10 implies n > 5
        ...
    end
end
```

### Guard Implication
```cure
match x with
| n when n > 10 -> ...  % Guard 1
| n when n > 5 -> ...   % Reachable
| n when n > 0 -> ...   % Reachable
end
```

## Usage

```erlang
% Check if Guard2 is redundant given Guard1
case cure_guard_optimizer:is_guard_redundant(Guard1, Guard2) of
    {redundant, Reason} -> remove_guard(Guard2);
    {independent} -> keep_guard(Guard2)
end.
```
""".

-export([
    % Guard analysis
    is_guard_redundant/2,
    check_guard_implication/2,
    find_redundant_guards/1,

    % Optimization
    optimize_guards/1,
    optimize_nested_guards/1,

    % Guard ordering
    order_guards_by_specificity/1,
    guard_specificity/1,

    % Utilities
    simplify_guard/1
]).

-include("../parser/cure_ast.hrl").

%% ============================================================================
%% Guard Redundancy Detection
%% ============================================================================

%% @doc Check if Guard2 is redundant given Guard1
%% Returns {redundant, Reason} if Guard2 is always true when Guard1 is true
-spec is_guard_redundant(expr(), expr()) ->
    {redundant, binary()} | {independent} | {error, term()}.
is_guard_redundant(Guard1, Guard2) ->
    case check_guard_implication(Guard1, Guard2) of
        {implies, true} ->
            {redundant, <<"Guard is implied by preceding guard">>};
        {implies, false} ->
            {independent};
        {error, Reason} ->
            {error, Reason}
    end.

%% @doc Check if Guard1 implies Guard2 (i.e., Guard1 => Guard2)
%% Uses SMT to prove: ∀vars. Guard1 => Guard2
-spec check_guard_implication(expr(), expr()) ->
    {implies, boolean()} | {error, term()}.
check_guard_implication(Guard1, Guard2) ->
    % Collect variables from both guards
    Vars = collect_guard_variables([Guard1, Guard2]),
    Env = maps:from_list([{V, {type, int}} || V <- Vars]),

    % To prove implication, check if (Guard1 AND NOT Guard2) is unsat
    % If unsat, then whenever Guard1 is true, Guard2 must be true
    Negation = #binary_op_expr{
        op = 'and',
        left = Guard1,
        right = #unary_op_expr{
            op = 'not',
            operand = Guard2,
            location = #location{}
        },
        location = #location{}
    },

    Query = cure_smt_translator:generate_query(Negation, Env, #{get_model => false}),

    case execute_smt_query(Query) of
        {unsat, _} ->
            % Unsat means Guard1 => Guard2
            {implies, true};
        {sat, _} ->
            % Sat means there exists a case where Guard1 is true but Guard2 is false
            {implies, false};
        {unknown, _} ->
            % Conservative: assume independent
            {implies, false};
        {error, Reason} ->
            {error, Reason}
    end.

%% @doc Find all redundant guards in a list
%% Returns list of {Index, Reason} for redundant guards
-spec find_redundant_guards([expr()]) -> [{integer(), binary()}].
find_redundant_guards(Guards) ->
    find_redundant_guards_impl(Guards, 1, []).

find_redundant_guards_impl([], _Index, Redundant) ->
    lists:reverse(Redundant);
find_redundant_guards_impl([Guard | Rest], Index, Redundant) ->
    AllGuards = [Guard | Rest],
    % Check if this guard is redundant given any previous guards
    PreviousGuards = lists:sublist(AllGuards, 1, Index - 1),

    IsRedundant = lists:any(
        fun(PrevGuard) ->
            case is_guard_redundant(PrevGuard, Guard) of
                {redundant, _} -> true;
                _ -> false
            end
        end,
        PreviousGuards
    ),

    NewRedundant =
        case IsRedundant of
            true ->
                [{Index, <<"Redundant: implied by earlier guard">>} | Redundant];
            false ->
                Redundant
        end,

    find_redundant_guards_impl(Rest, Index + 1, NewRedundant).

%% ============================================================================
%% Guard Optimization
%% ============================================================================

%% @doc Optimize a list of guards by removing redundant ones
-spec optimize_guards([expr()]) -> [expr()].
optimize_guards(Guards) ->
    optimize_guards_impl(Guards, []).

optimize_guards_impl([], Optimized) ->
    lists:reverse(Optimized);
optimize_guards_impl([Guard | Rest], Optimized) ->
    % Check if this guard is redundant given accumulated guards
    IsRedundant = lists:any(
        fun(PrevGuard) ->
            case is_guard_redundant(PrevGuard, Guard) of
                {redundant, _} -> true;
                _ -> false
            end
        end,
        Optimized
    ),

    case IsRedundant of
        true ->
            % Skip redundant guard
            optimize_guards_impl(Rest, Optimized);
        false ->
            % Keep non-redundant guard
            optimize_guards_impl(Rest, [Guard | Optimized])
    end.

%% @doc Optimize nested guards in match clauses
%% Returns simplified match clause list
-spec optimize_nested_guards([#match_clause{}]) -> [#match_clause{}].
optimize_nested_guards(MatchClauses) ->
    % For each clause, simplify its guard based on preceding clause guards
    optimize_nested_guards_impl(MatchClauses, [], []).

optimize_nested_guards_impl([], _AccGuards, AccClauses) ->
    lists:reverse(AccClauses);
optimize_nested_guards_impl([Clause | Rest], AccGuards, AccClauses) ->
    % Check if this clause's guard is redundant given accumulated guards
    #match_clause{guard = Guard} = Clause,

    SimplifiedClause =
        case Guard of
            undefined ->
                Clause;
            _ ->
                % Check if guard is redundant given any previous guard
                IsRedundant = lists:any(
                    fun(PrevGuard) ->
                        case is_guard_redundant(PrevGuard, Guard) of
                            {redundant, _} -> true;
                            _ -> false
                        end
                    end,
                    AccGuards
                ),

                case IsRedundant of
                    true ->
                        % Replace with trivial true guard
                        Clause#match_clause{
                            guard = #literal_expr{value = true, location = #location{}}
                        };
                    false ->
                        Clause
                end
        end,

    NewAccGuards =
        case Guard of
            undefined -> AccGuards;
            _ -> [Guard | AccGuards]
        end,

    optimize_nested_guards_impl(Rest, NewAccGuards, [SimplifiedClause | AccClauses]).

%% ============================================================================
%% Guard Ordering
%% ============================================================================

%% @doc Order guards from most specific to least specific
%% More restrictive guards should come first
-spec order_guards_by_specificity([{expr(), term()}]) -> [{expr(), term()}].
order_guards_by_specificity(GuardsWithBodies) ->
    % Sort by specificity score (higher = more specific)
    lists:sort(
        fun({G1, _}, {G2, _}) ->
            guard_specificity(G1) >= guard_specificity(G2)
        end,
        GuardsWithBodies
    ).

%% @doc Calculate specificity score for a guard
%% Higher score = more specific/restrictive
-spec guard_specificity(expr()) -> integer().
guard_specificity(#binary_op_expr{op = 'and', left = L, right = R}) ->
    % AND increases specificity
    guard_specificity(L) + guard_specificity(R) + 1;
guard_specificity(#binary_op_expr{op = 'or', left = L, right = R}) ->
    % OR decreases specificity
    min(guard_specificity(L), guard_specificity(R));
guard_specificity(#binary_op_expr{op = '==', left = _, right = #literal_expr{}}) ->
    % Equality with literal is very specific
    10;
guard_specificity(#binary_op_expr{op = '>', left = _, right = #literal_expr{value = V}}) when
    V > 0
->
    % Positive comparison is fairly specific
    5;
guard_specificity(#binary_op_expr{op = '>=', left = _, right = #literal_expr{value = V}}) when
    V > 0
->
    4;
guard_specificity(#binary_op_expr{op = '<', left = _, right = #literal_expr{}}) ->
    4;
guard_specificity(#binary_op_expr{op = '<=', left = _, right = #literal_expr{}}) ->
    3;
guard_specificity(#binary_op_expr{op = '/=', left = _, right = _}) ->
    % Not-equal is less specific
    2;
guard_specificity(#unary_op_expr{op = 'not', operand = Operand}) ->
    % Negation inverts specificity
    -guard_specificity(Operand);
guard_specificity(_) ->
    1.

%% ============================================================================
%% Guard Simplification
%% ============================================================================

%% @doc Simplify a guard expression using algebraic rules
-spec simplify_guard(expr()) -> expr().
% Double negation: not (not x) => x
simplify_guard(#unary_op_expr{op = 'not', operand = #unary_op_expr{op = 'not', operand = X}}) ->
    simplify_guard(X);
% AND with true: x and true => x
simplify_guard(#binary_op_expr{op = 'and', left = X, right = #literal_expr{value = true}}) ->
    simplify_guard(X);
simplify_guard(#binary_op_expr{op = 'and', left = #literal_expr{value = true}, right = X}) ->
    simplify_guard(X);
% AND with false: x and false => false
simplify_guard(#binary_op_expr{op = 'and', left = _, right = #literal_expr{value = false}} = Expr) ->
    Expr#binary_op_expr.right;
simplify_guard(#binary_op_expr{op = 'and', left = #literal_expr{value = false}, right = _} = Expr) ->
    Expr#binary_op_expr.left;
% OR with true: x or true => true
simplify_guard(#binary_op_expr{op = 'or', left = _, right = #literal_expr{value = true}} = Expr) ->
    Expr#binary_op_expr.right;
simplify_guard(#binary_op_expr{op = 'or', left = #literal_expr{value = true}, right = _} = Expr) ->
    Expr#binary_op_expr.left;
% OR with false: x or false => x
simplify_guard(#binary_op_expr{op = 'or', left = X, right = #literal_expr{value = false}}) ->
    simplify_guard(X);
simplify_guard(#binary_op_expr{op = 'or', left = #literal_expr{value = false}, right = X}) ->
    simplify_guard(X);
% Recursive simplification
simplify_guard(#binary_op_expr{op = _Op, left = L, right = R} = Expr) ->
    Expr#binary_op_expr{
        left = simplify_guard(L),
        right = simplify_guard(R)
    };
simplify_guard(#unary_op_expr{op = _Op, operand = Operand} = Expr) ->
    Expr#unary_op_expr{
        operand = simplify_guard(Operand)
    };
% Base case
simplify_guard(Expr) ->
    Expr.

%% ============================================================================
%% Utility Functions
%% ============================================================================

%% @doc Collect all variables used in guards
collect_guard_variables(Guards) ->
    lists:usort(lists:flatmap(fun collect_vars_from_expr/1, Guards)).

collect_vars_from_expr(#identifier_expr{name = Name}) when Name =/= '_' ->
    [Name];
collect_vars_from_expr(#binary_op_expr{left = L, right = R}) ->
    collect_vars_from_expr(L) ++ collect_vars_from_expr(R);
collect_vars_from_expr(#unary_op_expr{operand = Op}) ->
    collect_vars_from_expr(Op);
collect_vars_from_expr(_) ->
    [].

%% @doc Execute SMT query using the SMT process
execute_smt_query(Query) ->
    QueryBinary = iolist_to_binary(Query),
    case cure_smt_process:start_solver(z3, 5000) of
        {ok, Pid} ->
            try
                Result = cure_smt_process:execute_query(Pid, QueryBinary, 5000),
                cure_smt_process:stop_solver(Pid),
                Result
            catch
                _:Error ->
                    cure_smt_process:stop_solver(Pid),
                    {error, Error}
            end;
        {error, Reason} ->
            {error, Reason}
    end.
