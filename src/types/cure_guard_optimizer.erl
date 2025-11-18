-module(cure_guard_optimizer).

%% Guard Optimization using SMT
%% Simplifies guard conditions by eliminating redundancies and finding optimal ordering
-export([
    optimize_guard/1,
    optimize_guards/1,
    eliminate_redundant_conditions/1,
    find_optimal_ordering/1,
    simplify_guard_expression/1,
    check_guard_equivalence/2,
    check_guard_implication/2,
    format_optimized_guard/1
]).

-include("../parser/cure_ast.hrl").

%% Type definitions

% AST expression used as guard
-type guard_expr() :: term().
-type optimization_result() ::
    {optimized, guard_expr(), [optimization()]} | {unchanged, guard_expr()}.

-type optimization() ::
    {redundancy_eliminated, guard_expr()}
    | {reordered, [guard_expr()]}
    | {simplified, guard_expr(), guard_expr()}.

%% ============================================================================
%% Main API
%% ============================================================================

%% @doc Optimize a single guard expression
-spec optimize_guard(Guard :: guard_expr()) -> optimization_result().
optimize_guard(Guard) ->
    % Apply multiple optimization passes
    Pass1 = eliminate_redundant_conditions(Guard),
    Pass2 = simplify_guard_expression(Pass1),
    Pass3 = find_optimal_ordering(Pass2),

    % Check if any optimizations were applied
    case Guard =:= Pass3 of
        true ->
            {unchanged, Guard};
        false ->
            Optimizations = collect_optimizations(Guard, Pass3),
            {optimized, Pass3, Optimizations}
    end.

%% @doc Optimize multiple guards in a list
-spec optimize_guards(Guards :: [guard_expr()]) -> [{guard_expr(), optimization_result()}].
optimize_guards(Guards) ->
    [{Guard, optimize_guard(Guard)} || Guard <- Guards].

%% ============================================================================
%% Redundancy Elimination
%% ============================================================================

%% @doc Remove redundant conditions from a guard
-spec eliminate_redundant_conditions(Guard :: guard_expr()) -> guard_expr().
eliminate_redundant_conditions(#binary_op_expr{op = 'andalso', left = Left, right = Right} = Guard) ->
    % Check if Left implies Right
    case check_guard_implication(Left, Right) of
        true ->
            % Right is redundant (implied by Left)
            eliminate_redundant_conditions(Left);
        false ->
            % Check if Right implies Left
            case check_guard_implication(Right, Left) of
                true ->
                    % Left is redundant (implied by Right)
                    eliminate_redundant_conditions(Right);
                false ->
                    % Neither implies the other - keep both but optimize recursively
                    OptLeft = eliminate_redundant_conditions(Left),
                    OptRight = eliminate_redundant_conditions(Right),
                    Guard#binary_op_expr{left = OptLeft, right = OptRight}
            end
    end;
eliminate_redundant_conditions(#binary_op_expr{op = 'orelse', left = Left, right = Right} = Guard) ->
    % For OR: check if one subsumes the other
    OptLeft = eliminate_redundant_conditions(Left),
    OptRight = eliminate_redundant_conditions(Right),
    Guard#binary_op_expr{left = OptLeft, right = OptRight};
eliminate_redundant_conditions(Guard) ->
    % Base case: no optimization
    Guard.

%% ============================================================================
%% Guard Simplification
%% ============================================================================

%% @doc Simplify a guard expression using algebraic rules and SMT
-spec simplify_guard_expression(Guard :: guard_expr()) -> guard_expr().
simplify_guard_expression(#binary_op_expr{op = 'andalso', left = Left, right = Right} = Guard) ->
    % Simplify subexpressions first
    SimpleLeft = simplify_guard_expression(Left),
    SimpleRight = simplify_guard_expression(Right),

    % Apply simplification rules
    case {SimpleLeft, SimpleRight} of
        % true AND X = X
        {#literal_expr{value = true}, X} ->
            X;
        % X AND true = X
        {X, #literal_expr{value = true}} ->
            X;
        % false AND X = false
        {#literal_expr{value = false}, _} ->
            #literal_expr{value = false, location = Guard#binary_op_expr.location};
        % X AND false = false
        {_, #literal_expr{value = false}} ->
            #literal_expr{value = false, location = Guard#binary_op_expr.location};
        % X AND X = X (idempotency)
        {X, X} ->
            X;
        % No simplification
        _ ->
            Guard#binary_op_expr{left = SimpleLeft, right = SimpleRight}
    end;
simplify_guard_expression(#binary_op_expr{op = 'orelse', left = Left, right = Right} = Guard) ->
    % Simplify subexpressions first
    SimpleLeft = simplify_guard_expression(Left),
    SimpleRight = simplify_guard_expression(Right),

    % Apply simplification rules
    case {SimpleLeft, SimpleRight} of
        % true OR X = true
        {#literal_expr{value = true}, _} ->
            #literal_expr{value = true, location = Guard#binary_op_expr.location};
        % X OR true = true
        {_, #literal_expr{value = true}} ->
            #literal_expr{value = true, location = Guard#binary_op_expr.location};
        % false OR X = X
        {#literal_expr{value = false}, X} ->
            X;
        % X OR false = X
        {X, #literal_expr{value = false}} ->
            X;
        % X OR X = X (idempotency)
        {X, X} ->
            X;
        % No simplification
        _ ->
            Guard#binary_op_expr{left = SimpleLeft, right = SimpleRight}
    end;
simplify_guard_expression(#binary_op_expr{op = 'not', left = Expr} = Guard) ->
    SimpleExpr = simplify_guard_expression(Expr),
    case SimpleExpr of
        % NOT true = false
        #literal_expr{value = true} ->
            #literal_expr{value = false, location = Guard#binary_op_expr.location};
        % NOT false = true
        #literal_expr{value = false} ->
            #literal_expr{value = true, location = Guard#binary_op_expr.location};
        % Double negation: NOT (NOT X) = X
        #binary_op_expr{op = 'not', left = InnerExpr} ->
            InnerExpr;
        % No simplification
        _ ->
            Guard#binary_op_expr{left = SimpleExpr}
    end;
simplify_guard_expression(#binary_op_expr{op = Op, left = Left, right = Right} = Guard) when
    Op =:= '>'; Op =:= '<'; Op =:= '>='; Op =:= '=<'; Op =:= '=:='; Op =:= '=/='
->
    % Simplify comparison operators
    SimpleLeft = simplify_guard_expression(Left),
    SimpleRight = simplify_guard_expression(Right),

    % Check for constant comparisons
    case {SimpleLeft, SimpleRight} of
        {#literal_expr{value = V1}, #literal_expr{value = V2}} ->
            % Both constants - evaluate at compile time
            Result = evaluate_comparison(Op, V1, V2),
            #literal_expr{value = Result, location = Guard#binary_op_expr.location};
        _ ->
            Guard#binary_op_expr{left = SimpleLeft, right = SimpleRight}
    end;
simplify_guard_expression(Guard) ->
    % No simplification for other expressions
    Guard.

%% Evaluate comparison at compile time
evaluate_comparison('>', V1, V2) -> V1 > V2;
evaluate_comparison('<', V1, V2) -> V1 < V2;
evaluate_comparison('>=', V1, V2) -> V1 >= V2;
evaluate_comparison('=<', V1, V2) -> V1 =< V2;
evaluate_comparison('=:=', V1, V2) -> V1 =:= V2;
evaluate_comparison('=/=', V1, V2) -> V1 =/= V2.

%% ============================================================================
%% Optimal Ordering
%% ============================================================================

%% @doc Find optimal ordering of guard conditions (put cheaper checks first)
-spec find_optimal_ordering(Guard :: guard_expr()) -> guard_expr().
find_optimal_ordering(#binary_op_expr{op = 'andalso', left = Left, right = Right} = Guard) ->
    % For AND: put cheaper/more selective checks first
    LeftCost = estimate_guard_cost(Left),
    RightCost = estimate_guard_cost(Right),

    if
        RightCost < LeftCost ->
            % Swap: cheaper check first
            #binary_op_expr{
                op = 'andalso',
                left = find_optimal_ordering(Right),
                right = find_optimal_ordering(Left),
                location = Guard#binary_op_expr.location
            };
        true ->
            % Keep order but optimize recursively
            Guard#binary_op_expr{
                left = find_optimal_ordering(Left),
                right = find_optimal_ordering(Right)
            }
    end;
find_optimal_ordering(Guard) ->
    Guard.

%% Estimate cost of evaluating a guard (lower is cheaper)
estimate_guard_cost(#literal_expr{}) ->
    % Constants are cheapest
    1;
estimate_guard_cost(#identifier_expr{}) ->
    % Variable access
    2;
estimate_guard_cost(#binary_op_expr{op = Op}) when Op =:= '=:='; Op =:= '=/=' ->
    % Simple equality
    3;
estimate_guard_cost(#binary_op_expr{op = Op}) when
    Op =:= '>'; Op =:= '<'; Op =:= '>='; Op =:= '=<'
->
    % Numeric comparison
    4;
estimate_guard_cost(#binary_op_expr{op = 'andalso', left = Left, right = Right}) ->
    estimate_guard_cost(Left) + estimate_guard_cost(Right);
estimate_guard_cost(#binary_op_expr{op = 'orelse', left = Left, right = Right}) ->
    estimate_guard_cost(Left) + estimate_guard_cost(Right);
estimate_guard_cost(#function_call_expr{}) ->
    % Function calls are expensive
    10;
estimate_guard_cost(_) ->
    % Default cost
    5.

%% ============================================================================
%% SMT-Based Optimization
%% ============================================================================

%% @doc Check if two guards are logically equivalent
-spec check_guard_equivalence(Guard1 :: guard_expr(), Guard2 :: guard_expr()) -> boolean().
check_guard_equivalence(Guard1, Guard2) ->
    % Encode guards to SMT
    SMT1 = encode_guard_to_smt(Guard1),
    SMT2 = encode_guard_to_smt(Guard2),

    % Check if G1 <=> G2 is valid (i.e., !(G1 <=> G2) is unsat)
    Query = [
        "(declare-const x Int)\n",
        "(declare-const y Int)\n",
        "(assert (not (= ",
        SMT1,
        " ",
        SMT2,
        ")))\n",
        "(check-sat)\n"
    ],

    case cure_smt_process:query(Query) of
        {ok, Result} ->
            % unsat means they're equivalent
            string:trim(Result) =:= "unsat";
        {error, _} ->
            % Can't determine, assume not equivalent
            false
    end.

%% @doc Check if Guard1 implies Guard2 (G1 => G2)
-spec check_guard_implication(Guard1 :: guard_expr(), Guard2 :: guard_expr()) -> boolean().
check_guard_implication(Guard1, Guard2) ->
    % Encode guards to SMT
    SMT1 = encode_guard_to_smt(Guard1),
    SMT2 = encode_guard_to_smt(Guard2),

    % Check if G1 => G2 is valid (i.e., G1 AND NOT G2 is unsat)
    Query = [
        "(declare-const x Int)\n",
        "(declare-const y Int)\n",
        "(assert ",
        SMT1,
        ")\n",
        "(assert (not ",
        SMT2,
        "))\n",
        "(check-sat)\n"
    ],

    case cure_smt_process:query(Query) of
        {ok, Result} ->
            % unsat means implication holds
            string:trim(Result) =:= "unsat";
        {error, _} ->
            % Can't determine, assume no implication
            false
    end.

%% ============================================================================
%% SMT Encoding
%% ============================================================================

%% @doc Encode guard expression to SMT-LIB format
encode_guard_to_smt(#binary_op_expr{op = 'andalso', left = Left, right = Right}) ->
    ["(and ", encode_guard_to_smt(Left), " ", encode_guard_to_smt(Right), ")"];
encode_guard_to_smt(#binary_op_expr{op = 'orelse', left = Left, right = Right}) ->
    ["(or ", encode_guard_to_smt(Left), " ", encode_guard_to_smt(Right), ")"];
encode_guard_to_smt(#binary_op_expr{op = 'not', left = Expr}) ->
    ["(not ", encode_guard_to_smt(Expr), ")"];
encode_guard_to_smt(#binary_op_expr{op = '>', left = Left, right = Right}) ->
    ["(> ", encode_expr_to_smt(Left), " ", encode_expr_to_smt(Right), ")"];
encode_guard_to_smt(#binary_op_expr{op = '<', left = Left, right = Right}) ->
    ["(< ", encode_expr_to_smt(Left), " ", encode_expr_to_smt(Right), ")"];
encode_guard_to_smt(#binary_op_expr{op = '>=', left = Left, right = Right}) ->
    ["(>= ", encode_expr_to_smt(Left), " ", encode_expr_to_smt(Right), ")"];
encode_guard_to_smt(#binary_op_expr{op = '=<', left = Left, right = Right}) ->
    ["(<= ", encode_expr_to_smt(Left), " ", encode_expr_to_smt(Right), ")"];
encode_guard_to_smt(#binary_op_expr{op = '=:=', left = Left, right = Right}) ->
    ["(= ", encode_expr_to_smt(Left), " ", encode_expr_to_smt(Right), ")"];
encode_guard_to_smt(#binary_op_expr{op = '=/=', left = Left, right = Right}) ->
    ["(not (= ", encode_expr_to_smt(Left), " ", encode_expr_to_smt(Right), "))"];
encode_guard_to_smt(#literal_expr{value = true}) ->
    "true";
encode_guard_to_smt(#literal_expr{value = false}) ->
    "false";
encode_guard_to_smt(_) ->
    % Default for unsupported expressions
    "true".

encode_expr_to_smt(#identifier_expr{name = Name}) ->
    atom_to_list(Name);
encode_expr_to_smt(#literal_expr{value = Value}) when is_integer(Value) ->
    integer_to_list(Value);
encode_expr_to_smt(#binary_op_expr{op = '+', left = Left, right = Right}) ->
    ["(+ ", encode_expr_to_smt(Left), " ", encode_expr_to_smt(Right), ")"];
encode_expr_to_smt(#binary_op_expr{op = '-', left = Left, right = Right}) ->
    ["(- ", encode_expr_to_smt(Left), " ", encode_expr_to_smt(Right), ")"];
encode_expr_to_smt(#binary_op_expr{op = '*', left = Left, right = Right}) ->
    ["(* ", encode_expr_to_smt(Left), " ", encode_expr_to_smt(Right), ")"];
encode_expr_to_smt(_) ->
    % Default
    "0".

%% ============================================================================
%% Utility Functions
%% ============================================================================

%% Collect optimizations applied
collect_optimizations(Original, Optimized) ->
    % Simple heuristic: if they're different, something changed
    case Original =:= Optimized of
        true ->
            [];
        false ->
            [{simplified, Original, Optimized}]
    end.

%% @doc Format optimized guard for display
-spec format_optimized_guard(optimization_result()) -> binary().
format_optimized_guard({unchanged, _Guard}) ->
    <<"No optimizations applied">>;
format_optimized_guard({optimized, Guard, Optimizations}) ->
    GuardStr = format_guard_expr(Guard),
    OptStrs = [format_optimization(Opt) || Opt <- Optimizations],
    iolist_to_binary([
        <<"Optimized guard: ">>,
        GuardStr,
        <<"\n">>,
        <<"Optimizations applied:\n">>,
        string:join(OptStrs, "\n")
    ]).

format_optimization({redundancy_eliminated, Expr}) ->
    io_lib:format("  - Eliminated redundant condition: ~s", [format_guard_expr(Expr)]);
format_optimization({reordered, Exprs}) ->
    io_lib:format("  - Reordered ~p conditions for efficiency", [length(Exprs)]);
format_optimization({simplified, From, To}) ->
    io_lib:format("  - Simplified: ~s => ~s", [format_guard_expr(From), format_guard_expr(To)]).

format_guard_expr(#binary_op_expr{op = Op, left = Left, right = Right}) ->
    io_lib:format("(~s ~s ~s)", [format_guard_expr(Left), Op, format_guard_expr(Right)]);
format_guard_expr(#literal_expr{value = Value}) ->
    io_lib:format("~p", [Value]);
format_guard_expr(#identifier_expr{name = Name}) ->
    atom_to_list(Name);
format_guard_expr(_) ->
    "?".
