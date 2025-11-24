-module(cure_smt_solver).

-moduledoc """
# SMT Solver Integration for Cure

This module provides integration with SMT (Satisfiability Modulo Theories) solvers
for dependent type constraint verification and optimization. It supports multiple
backend solvers including Z3, CVC5, and others.

## Features

- **Constraint Verification**: Prove or disprove type constraints at compile time
- **Constraint Simplification**: Algebraic and SMT-based constraint simplification
- **Guard Optimization**: Eliminate redundant runtime checks
- **Counterexample Generation**: Provide examples when constraints fail
- **Multiple Backends**: Support for Z3, CVC5, and fallback to symbolic evaluation

## Usage

### Basic Constraint Checking
```erlang
Constraint = #binary_op_expr{op = '>', left = VarN, right = Zero},
case cure_smt_solver:check_constraint(Constraint, Env) of
    {sat, Model} -> % Constraint is satisfiable
        io:format("Satisfiable with model: ~p~n", [Model]);
    unsat -> % Constraint is unsatisfiable
        io:format("Constraint cannot be satisfied~n");
    unknown -> % Solver couldn't determine
        io:format("Unknown, need runtime check~n")
end.
```

### Simplifying Constraints
```erlang
% Simplify constraint using algebraic rules and SMT solver
Constraint = #binary_op_expr{op = '+', left = VarX, right = Zero},
Simplified = cure_smt_solver:simplify_constraint(Constraint, Env).
% => Returns VarX (since x + 0 = x)
```

### Proving Constraints
```erlang
% Prove that n > 0 implies length(list) > 0
Result = cure_smt_solver:prove_implication(Antecedent, Consequent, Env).
```

## SMT Backend Selection

The module automatically selects available SMT solvers in order of preference:
1. Z3 (if available)
2. CVC5 (if available)
3. Symbolic evaluation fallback

## Constraint Translation

Cure constraints are translated to SMT-LIB format:
- Arithmetic: +, -, *, div, rem
- Comparisons: <, >, =<, >=, ==, /=
- Boolean: and, or, not
- Quantifiers: forall, exists (for dependent types)
""".

-export([
    check_constraint/2,
    check_constraint/3,
    prove_implication/3,
    prove_constraint/2,
    find_counterexample/2,
    simplify_constraint/2,
    solve_constraints/1,
    available_solvers/0,
    set_solver/1,
    % Helper functions for LSP integration
    equality_constraint/2,
    inequality_constraint/3,
    variable_term/1,
    constant_term/1,
    % S-expression parser functions for testing
    parse_sexp_to_constraint/1,
    tokenize_sexp/2,
    parse_sexp_tokens/1,
    sexp_term_to_constraint/1
]).

-include("../parser/cure_ast.hrl").

-record(smt_context, {
    solver = z3 :: atom(),
    timeout = 5000 :: integer(),
    options = #{} :: map()
}).

%%% Public API %%%

%% @doc Check if a constraint is satisfiable
-spec check_constraint(expr(), map()) -> sat | unsat | unknown | {sat, map()}.
check_constraint(Constraint, Env) ->
    check_constraint(Constraint, Env, #{}).

%% @doc Check constraint with options
-spec check_constraint(expr(), map(), map()) -> sat | unsat | unknown | {sat, map()}.
check_constraint(Constraint, Env, Opts) ->
    Context = create_context(Opts),

    case Context#smt_context.solver of
        z3 -> check_with_z3(Constraint, Env, Context);
        cvc5 -> check_with_cvc5(Constraint, Env, Context);
        symbolic -> check_with_symbolic(Constraint, Env, Context);
        _ -> unknown
    end.

%% @doc Prove an implication: Antecedent => Consequent
-spec prove_implication(expr(), expr(), map()) -> true | false | unknown.
prove_implication(Antecedent, Consequent, Env) ->
    % To prove A => C, we check if (A and not C) is unsatisfiable
    NotConsequent = negate_constraint(Consequent),
    Combined = make_conjunction(Antecedent, NotConsequent),

    case check_constraint(Combined, Env) of
        % Implication holds
        unsat -> true;
        % Implication doesn't hold
        {sat, _} -> false;
        sat -> false;
        unknown -> unknown
    end.

%% @doc Prove a constraint always holds
-spec prove_constraint(expr(), map()) -> true | false | unknown.
prove_constraint(Constraint, Env) ->
    % Check if the negation is unsatisfiable
    NotConstraint = negate_constraint(Constraint),

    case check_constraint(NotConstraint, Env) of
        % Constraint always holds
        unsat -> true;
        % Constraint doesn't always hold
        {sat, _} -> false;
        sat -> false;
        unknown -> unknown
    end.

%% @doc Find a counterexample where constraint doesn't hold
-spec find_counterexample(expr(), map()) -> {ok, map()} | none | unknown.
find_counterexample(Constraint, Env) ->
    NotConstraint = negate_constraint(Constraint),

    case check_constraint(NotConstraint, Env) of
        {sat, Model} -> {ok, Model};
        sat -> {ok, #{}};
        unsat -> none;
        unknown -> unknown
    end.

%% @doc Simplify a constraint using algebraic rules and SMT solver
%%
%% Applies multiple simplification strategies:
%% 1. Local algebraic simplifications (fast, no solver needed)
%%    - Arithmetic identities: x + 0 = x, x * 1 = x, x * 0 = 0
%%    - Boolean identities: x and true = x, x or false = x
%%    - Constant folding: 2 + 3 = 5, true and false = false
%%    - Comparison simplifications: x == x = true, x < x = false
%%    - Double negation: not (not x) = x, -(-x) = x
%% 2. SMT-based simplifications (if Z3 available)
%%    - Leverages Z3's simplify command for complex expressions
%%
%% @param Constraint The constraint expression to simplify
%% @param Env Environment mapping variables to types
%% @returns Simplified constraint expression
%%
%% @example
%% % Arithmetic identity
%% X = #identifier_expr{name = x},
%% Zero = #literal_expr{value = 0},
%% Constraint = #binary_op_expr{op = '+', left = X, right = Zero},
%% Simplified = simplify_constraint(Constraint, #{}),
%% % Returns: X (since x + 0 = x)
-spec simplify_constraint(expr(), map()) -> expr().
simplify_constraint(Constraint, Env) ->
    % Apply multiple simplification strategies:
    % 1. Local algebraic simplifications (fast)
    % 2. SMT-based simplifications (if solver available)

    % First apply local simplifications
    LocalSimplified = simplify_local(Constraint, Env),

    % Then try SMT-based simplification if Z3 is available
    case find_z3() of
        true ->
            simplify_with_smt(LocalSimplified, Env);
        false ->
            LocalSimplified
    end.

%% @doc Solve multiple constraints (conjunction)
-spec solve_constraints([expr()]) -> sat | unsat | unknown | {sat, map()}.
solve_constraints([]) ->
    sat;
solve_constraints([SingleConstraint]) ->
    check_constraint(SingleConstraint, #{});
solve_constraints(Constraints) ->
    % Combine all constraints with AND
    Combined = lists:foldl(
        fun(C, Acc) ->
            case Acc of
                undefined -> C;
                _ -> make_conjunction(Acc, C)
            end
        end,
        undefined,
        Constraints
    ),
    check_constraint(Combined, #{}).

%% @doc Get list of available SMT solvers
-spec available_solvers() -> [atom()].
available_solvers() ->
    Solvers = [
        {z3, find_z3()},
        {cvc5, find_cvc5()},
        % Always available
        {symbolic, true}
    ],
    [Solver || {Solver, true} <- Solvers].

%% @doc Set the preferred SMT solver
-spec set_solver(atom()) -> ok | {error, term()}.
set_solver(Solver) ->
    case lists:member(Solver, available_solvers()) of
        true ->
            put(smt_solver, Solver),
            ok;
        false ->
            {error, {solver_not_available, Solver}}
    end.

%%% Internal Functions %%%

%% Create SMT context
create_context(Opts) ->
    DefaultSolver = get_default_solver(),
    Solver = maps:get(solver, Opts, DefaultSolver),
    Timeout = maps:get(timeout, Opts, 5000),

    #smt_context{
        solver = Solver,
        timeout = Timeout,
        options = Opts
    }.

%% Get default solver
get_default_solver() ->
    case get(smt_solver) of
        undefined ->
            % Auto-select first available
            case available_solvers() of
                [First | _] -> First;
                [] -> symbolic
            end;
        Solver ->
            Solver
    end.

%% Check with Z3
check_with_z3(Constraint, Env, Context) ->
    case find_z3() of
        false ->
            % Provide helpful message when Z3 is not available
            cure_utils:debug(
                "SMT: Z3 solver not found in PATH. Falling back to symbolic evaluation.~n"
            ),
            cure_utils:debug(
                "Hint: Install Z3 for better constraint solving (https://github.com/Z3Prover/z3)~n"
            ),
            check_with_symbolic(Constraint, Env, Context);
        true ->
            try
                % 1. Generate SMT-LIB query
                Query = cure_smt_translator:generate_query(Constraint, Env),

                % 2. Start solver
                {ok, Pid} = cure_smt_process:start_solver(z3, Context#smt_context.timeout),

                % 3. Execute query
                Result = cure_smt_process:execute_query(Pid, Query),

                % 4. Parse result
                ParsedResult =
                    case Result of
                        {sat, ModelLines} ->
                            case cure_smt_parser:parse_model(ModelLines) of
                                {ok, Model} ->
                                    {sat, Model};
                                {error, ParseErr} ->
                                    cure_utils:debug("SMT: Failed to parse Z3 model: ~p~n", [
                                        ParseErr
                                    ]),
                                    cure_utils:debug("Model lines: ~p~n", [ModelLines]),
                                    {sat, #{}}
                            end;
                        {unsat, _} ->
                            unsat;
                        {unknown, _} ->
                            cure_utils:debug("SMT: Z3 returned 'unknown' for constraint~n"),
                            cure_utils:debug("Constraint: ~p~n", [format_constraint(Constraint)]),
                            cure_utils:debug(
                                "Hint: Constraint may be too complex or timeout was too short (~p ms)~n",
                                [Context#smt_context.timeout]
                            ),
                            unknown;
                        {error, timeout} ->
                            cure_utils:debug("SMT: Z3 timed out after ~p ms~n", [
                                Context#smt_context.timeout
                            ]),
                            cure_utils:debug("Constraint: ~p~n", [format_constraint(Constraint)]),
                            cure_utils:debug(
                                "Hint: Try increasing timeout with --smt-timeout <ms>~n"
                            ),
                            unknown;
                        {error, Reason} ->
                            cure_utils:debug("SMT: Z3 execution error: ~p~n", [Reason]),
                            cure_utils:debug("Constraint: ~p~n", [format_constraint(Constraint)]),
                            cure_utils:debug("Query: ~s~n", [Query]),
                            unknown
                    end,

                % 5. Clean up
                cure_smt_process:stop_solver(Pid),
                ParsedResult
            catch
                Class:Error:Stack ->
                    % Provide detailed error information
                    cure_utils:debug("SMT: Z3 execution failed with ~p:~p~n", [Class, Error]),
                    cure_utils:debug("Constraint: ~p~n", [format_constraint(Constraint)]),
                    case os:getenv("CURE_DEBUG") of
                        "1" -> cure_utils:debug("Stack: ~p~n", [Stack]);
                        _ -> cure_utils:debug("Hint: Set CURE_DEBUG=1 for full stack trace~n")
                    end,
                    cure_utils:debug("Falling back to symbolic evaluation~n"),
                    check_with_symbolic(Constraint, Env, Context)
            end
    end.

%% Check with CVC5
check_with_cvc5(Constraint, Env, Context) ->
    case find_cvc5() of
        false ->
            % Provide helpful message when CVC5 is not available
            cure_utils:debug(
                "SMT: CVC5 solver not found in PATH. Falling back to symbolic evaluation.~n"
            ),
            cure_utils:debug(
                "Hint: Install CVC5 for alternative SMT solving (https://cvc5.github.io/)~n"
            ),
            check_with_symbolic(Constraint, Env, Context);
        true ->
            try
                % 1. Generate SMT-LIB query for CVC5
                Query = cure_smt_translator:generate_query(Constraint, Env),

                % 2. Start solver (CVC5 dialect)
                {ok, Pid} = cure_smt_process:start_solver(cvc5, Context#smt_context.timeout),

                % 3. Execute query
                Result = cure_smt_process:execute_query(Pid, Query),

                % 4. Parse result (CVC5 uses similar SMT-LIB output format)
                ParsedResult =
                    case Result of
                        {sat, ModelLines} ->
                            % CVC5 outputs models in SMT-LIB format, similar to Z3
                            case parse_cvc5_model(ModelLines) of
                                {ok, Model} ->
                                    {sat, Model};
                                {error, ParseErr} ->
                                    cure_utils:debug("SMT: Failed to parse CVC5 model: ~p~n", [
                                        ParseErr
                                    ]),
                                    cure_utils:debug("Model lines: ~p~n", [ModelLines]),
                                    {sat, #{}}
                            end;
                        {unsat, _} ->
                            unsat;
                        {unknown, _} ->
                            cure_utils:debug("SMT: CVC5 returned 'unknown' for constraint~n"),
                            cure_utils:debug("Constraint: ~p~n", [format_constraint(Constraint)]),
                            cure_utils:debug(
                                "Hint: Constraint may be too complex or timeout was too short (~p ms)~n",
                                [Context#smt_context.timeout]
                            ),
                            unknown;
                        {error, timeout} ->
                            cure_utils:debug("SMT: CVC5 timed out after ~p ms~n", [
                                Context#smt_context.timeout
                            ]),
                            cure_utils:debug("Constraint: ~p~n", [format_constraint(Constraint)]),
                            cure_utils:debug(
                                "Hint: Try increasing timeout with --smt-timeout <ms>~n"
                            ),
                            unknown;
                        {error, Reason} ->
                            cure_utils:debug("SMT: CVC5 execution error: ~p~n", [Reason]),
                            cure_utils:debug("Constraint: ~p~n", [format_constraint(Constraint)]),
                            cure_utils:debug("Query: ~s~n", [Query]),
                            unknown
                    end,

                % 5. Clean up
                cure_smt_process:stop_solver(Pid),
                ParsedResult
            catch
                Class:Error:Stack ->
                    % Provide detailed error information
                    cure_utils:debug("SMT: CVC5 execution failed with ~p:~p~n", [Class, Error]),
                    cure_utils:debug("Constraint: ~p~n", [format_constraint(Constraint)]),
                    case os:getenv("CURE_DEBUG") of
                        "1" -> cure_utils:debug("Stack: ~p~n", [Stack]);
                        _ -> cure_utils:debug("Hint: Set CURE_DEBUG=1 for full stack trace~n")
                    end,
                    cure_utils:debug("Falling back to symbolic evaluation~n"),
                    check_with_symbolic(Constraint, Env, Context)
            end
    end.

%% Check with symbolic evaluation
check_with_symbolic(Constraint, Env, _Context) ->
    % Simple symbolic evaluation for basic constraints
    try
        case eval_symbolic(Constraint, Env) of
            true ->
                sat;
            false ->
                unsat;
            _ ->
                cure_utils:debug("SMT: Symbolic evaluation unable to determine satisfiability~n"),
                cure_utils:debug("Constraint: ~p~n", [format_constraint(Constraint)]),
                cure_utils:debug("Hint: Install Z3 or CVC5 for better constraint solving~n"),
                unknown
        end
    catch
        Class:Error:Stack ->
            cure_utils:debug("SMT: Symbolic evaluation failed with ~p:~p~n", [Class, Error]),
            cure_utils:debug("Constraint: ~p~n", [format_constraint(Constraint)]),
            case os:getenv("CURE_DEBUG") of
                "1" -> cure_utils:debug("Stack: ~p~n", [Stack]);
                _ -> ok
            end,
            unknown
    end.

%% Symbolic evaluation
eval_symbolic(#literal_expr{value = Value}, _Env) when is_boolean(Value) ->
    Value;
eval_symbolic(#binary_op_expr{op = Op, left = Left, right = Right}, Env) ->
    LeftVal = eval_symbolic(Left, Env),
    RightVal = eval_symbolic(Right, Env),

    case {LeftVal, RightVal} of
        {unknown, _} -> unknown;
        {_, unknown} -> unknown;
        _ -> eval_binary_op(Op, LeftVal, RightVal)
    end;
eval_symbolic(#unary_op_expr{op = 'not', operand = Operand}, Env) ->
    case eval_symbolic(Operand, Env) of
        true -> false;
        false -> true;
        unknown -> unknown
    end;
eval_symbolic(#identifier_expr{name = Name}, Env) ->
    case maps:get(Name, Env, undefined) of
        undefined -> unknown;
        {value, Value} -> Value;
        _ -> unknown
    end;
eval_symbolic(_, _) ->
    unknown.

%% Evaluate binary operation
eval_binary_op('+', L, R) when is_number(L), is_number(R) -> L + R;
eval_binary_op('-', L, R) when is_number(L), is_number(R) -> L - R;
eval_binary_op('*', L, R) when is_number(L), is_number(R) -> L * R;
eval_binary_op('/', L, R) when is_number(L), is_number(R), R =/= 0 -> L / R;
eval_binary_op('div', L, R) when is_integer(L), is_integer(R), R =/= 0 -> L div R;
eval_binary_op('rem', L, R) when is_integer(L), is_integer(R), R =/= 0 -> L rem R;
eval_binary_op('==', L, R) -> L == R;
eval_binary_op('/=', L, R) -> L /= R;
eval_binary_op('<', L, R) when is_number(L), is_number(R) -> L < R;
eval_binary_op('>', L, R) when is_number(L), is_number(R) -> L > R;
eval_binary_op('=<', L, R) when is_number(L), is_number(R) -> L =< R;
eval_binary_op('>=', L, R) when is_number(L), is_number(R) -> L >= R;
eval_binary_op('and', L, R) when is_boolean(L), is_boolean(R) -> L andalso R;
eval_binary_op('or', L, R) when is_boolean(L), is_boolean(R) -> L orelse R;
eval_binary_op(_, _, _) -> unknown.

%% Negate a constraint
negate_constraint(#unary_op_expr{op = 'not', operand = Operand}) ->
    Operand;
negate_constraint(#binary_op_expr{op = '==', left = _L, right = _R} = Expr) ->
    Expr#binary_op_expr{op = '/='};
negate_constraint(#binary_op_expr{op = '/=', left = _L, right = _R} = Expr) ->
    Expr#binary_op_expr{op = '=='};
negate_constraint(#binary_op_expr{op = '<', left = _L, right = _R} = Expr) ->
    Expr#binary_op_expr{op = '>='};
negate_constraint(#binary_op_expr{op = '>', left = _L, right = _R} = Expr) ->
    Expr#binary_op_expr{op = '=<'};
negate_constraint(#binary_op_expr{op = '=<', left = _L, right = _R} = Expr) ->
    Expr#binary_op_expr{op = '>'};
negate_constraint(#binary_op_expr{op = '>=', left = _L, right = _R} = Expr) ->
    Expr#binary_op_expr{op = '<'};
negate_constraint(Constraint) ->
    #unary_op_expr{
        op = 'not',
        operand = Constraint,
        location = #location{line = 0, column = 0, file = undefined}
    }.

%% Make conjunction of two constraints
make_conjunction(Left, Right) ->
    #binary_op_expr{
        op = 'and',
        left = Left,
        right = Right,
        location = #location{line = 0, column = 0, file = undefined}
    }.

%% Find Z3 executable
find_z3() ->
    case os:find_executable("z3") of
        false -> false;
        _ -> true
    end.

%% Find CVC5 executable
find_cvc5() ->
    case os:find_executable("cvc5") of
        false -> false;
        _ -> true
    end.

%% ============================================================================
%% Constraint Simplification
%% ============================================================================

%% Local algebraic simplifications (no SMT solver required)
simplify_local(Constraint, Env) ->
    % Apply simplifications recursively until no more changes
    case simplify_once(Constraint, Env) of
        % No change, we're done
        Constraint -> Constraint;
        % Changed, try again
        Simplified -> simplify_local(Simplified, Env)
    end.

%% Apply one pass of simplifications
simplify_once(#binary_op_expr{op = Op, left = L, right = R} = Expr, Env) ->
    % First simplify children
    L1 = simplify_once(L, Env),
    R1 = simplify_once(R, Env),

    % Then try to simplify this node
    Expr1 = Expr#binary_op_expr{left = L1, right = R1},
    simplify_binary_op(Op, L1, R1, Expr1, Env);
simplify_once(#unary_op_expr{op = Op, operand = Operand} = Expr, Env) ->
    % Simplify operand first
    Operand1 = simplify_once(Operand, Env),
    simplify_unary_op(Op, Operand1, Expr#unary_op_expr{operand = Operand1}, Env);
simplify_once(Expr, _Env) ->
    % Literals, identifiers, etc. - no simplification
    Expr.

%% Simplify binary operations
% Arithmetic identities

% 0 + x = x
simplify_binary_op('+', #literal_expr{value = 0}, R, _Expr, _Env) ->
    R;
% x + 0 = x
simplify_binary_op('+', L, #literal_expr{value = 0}, _Expr, _Env) ->
    L;
% 0 * x = 0
simplify_binary_op('*', #literal_expr{value = 0}, _R, Expr, _Env) ->
    Expr#binary_op_expr{
        left = #literal_expr{value = 0, location = Expr#binary_op_expr.location},
        right = #literal_expr{value = 0, location = Expr#binary_op_expr.location}
    };
% x * 0 = 0
simplify_binary_op('*', _L, #literal_expr{value = 0}, Expr, _Env) ->
    Expr#binary_op_expr{
        left = #literal_expr{value = 0, location = Expr#binary_op_expr.location},
        right = #literal_expr{value = 0, location = Expr#binary_op_expr.location}
    };
% 1 * x = x
simplify_binary_op('*', #literal_expr{value = 1}, R, _Expr, _Env) ->
    R;
% x * 1 = x
simplify_binary_op('*', L, #literal_expr{value = 1}, _Expr, _Env) ->
    L;
% x - 0 = x
simplify_binary_op('-', L, #literal_expr{value = 0}, _Expr, _Env) ->
    L;
% Constant folding
simplify_binary_op(Op, #literal_expr{value = L}, #literal_expr{value = R}, Expr, _Env) when
    is_number(L), is_number(R)
->
    case eval_binary_op(Op, L, R) of
        unknown -> Expr;
        Result -> #literal_expr{value = Result, location = Expr#binary_op_expr.location}
    end;
% Boolean identities

% true and x = x
simplify_binary_op('and', #literal_expr{value = true}, R, _Expr, _Env) ->
    R;
% x and true = x
simplify_binary_op('and', L, #literal_expr{value = true}, _Expr, _Env) ->
    L;
% false and x = false
simplify_binary_op('and', #literal_expr{value = false}, _R, Expr, _Env) ->
    #literal_expr{value = false, location = Expr#binary_op_expr.location};
% x and false = false
simplify_binary_op('and', _L, #literal_expr{value = false}, Expr, _Env) ->
    #literal_expr{value = false, location = Expr#binary_op_expr.location};
% false or x = x
simplify_binary_op('or', #literal_expr{value = false}, R, _Expr, _Env) ->
    R;
% x or false = x
simplify_binary_op('or', L, #literal_expr{value = false}, _Expr, _Env) ->
    L;
% true or x = true
simplify_binary_op('or', #literal_expr{value = true}, _R, Expr, _Env) ->
    #literal_expr{value = true, location = Expr#binary_op_expr.location};
% x or true = true
simplify_binary_op('or', _L, #literal_expr{value = true}, Expr, _Env) ->
    #literal_expr{value = true, location = Expr#binary_op_expr.location};
% Comparison simplifications
% x == x => true (for pure expressions)
simplify_binary_op('==', L, R, Expr, _Env) when L =:= R ->
    case is_pure_expr(L) of
        true -> #literal_expr{value = true, location = Expr#binary_op_expr.location};
        false -> Expr
    end;
% x /= x => false (for pure expressions)
simplify_binary_op('/=', L, R, Expr, _Env) when L =:= R ->
    case is_pure_expr(L) of
        true -> #literal_expr{value = false, location = Expr#binary_op_expr.location};
        false -> Expr
    end;
% x < x => false
simplify_binary_op('<', L, R, Expr, _Env) when L =:= R ->
    case is_pure_expr(L) of
        true -> #literal_expr{value = false, location = Expr#binary_op_expr.location};
        false -> Expr
    end;
% x > x => false
simplify_binary_op('>', L, R, Expr, _Env) when L =:= R ->
    case is_pure_expr(L) of
        true -> #literal_expr{value = false, location = Expr#binary_op_expr.location};
        false -> Expr
    end;
% x =< x => true
simplify_binary_op('=<', L, R, Expr, _Env) when L =:= R ->
    case is_pure_expr(L) of
        true -> #literal_expr{value = true, location = Expr#binary_op_expr.location};
        false -> Expr
    end;
% x >= x => true
simplify_binary_op('>=', L, R, Expr, _Env) when L =:= R ->
    case is_pure_expr(L) of
        true -> #literal_expr{value = true, location = Expr#binary_op_expr.location};
        false -> Expr
    end;
% No simplification applies
simplify_binary_op(_Op, _L, _R, Expr, _Env) ->
    Expr.

%% Simplify unary operations
% Double negation: not (not x) = x
simplify_unary_op('not', #unary_op_expr{op = 'not', operand = X}, _Expr, _Env) ->
    X;
% Negation of constants
simplify_unary_op('not', #literal_expr{value = true}, Expr, _Env) ->
    #literal_expr{value = false, location = Expr#unary_op_expr.location};
simplify_unary_op('not', #literal_expr{value = false}, Expr, _Env) ->
    #literal_expr{value = true, location = Expr#unary_op_expr.location};
% Numeric negation of constants
simplify_unary_op('-', #literal_expr{value = N}, Expr, _Env) when is_number(N) ->
    #literal_expr{value = -N, location = Expr#unary_op_expr.location};
% Double negation (numeric): -(-x) = x
simplify_unary_op('-', #unary_op_expr{op = '-', operand = X}, _Expr, _Env) ->
    X;
% No simplification
simplify_unary_op(_Op, _Operand, Expr, _Env) ->
    Expr.

%% Check if expression is pure (no side effects, deterministic)
is_pure_expr(#literal_expr{}) -> true;
is_pure_expr(#identifier_expr{}) -> true;
is_pure_expr(#binary_op_expr{left = L, right = R}) -> is_pure_expr(L) andalso is_pure_expr(R);
is_pure_expr(#unary_op_expr{operand = Op}) -> is_pure_expr(Op);
is_pure_expr(_) -> false.

%% SMT-based simplification using Z3's simplify command
simplify_with_smt(Constraint, Env) ->
    try
        % Generate SMT-LIB query with simplify command
        Query = generate_simplify_query(Constraint, Env),

        % Start Z3 solver
        {ok, Pid} = cure_smt_process:start_solver(z3, 2000),

        % Execute simplification
        Result = cure_smt_process:execute_query(Pid, Query),

        % Parse simplified result
        SimplifiedConstraint = parse_simplified_result(Result, Constraint),

        % Clean up
        cure_smt_process:stop_solver(Pid),

        SimplifiedConstraint
    catch
        _Class:_Error ->
            % If SMT simplification fails, return local simplification
            Constraint
    end.

%% Generate SMT-LIB query for simplification
generate_simplify_query(Constraint, Env) ->
    % Collect variables and declare them
    Vars = cure_smt_translator:collect_variables(Constraint, Env),
    Declarations = [cure_smt_translator:declare_variable(V, Env) || V <- Vars],

    % Translate constraint
    Translated = cure_smt_translator:translate_expr(Constraint, Env),

    % Use Z3's simplify command
    [
        "(set-logic QF_LIA)\n",
        Declarations,
        "(simplify ",
        Translated,
        ")\n"
    ].

%% Parse the simplified result from Z3
parse_simplified_result({sat, Lines}, _OriginalConstraint) when length(Lines) > 0 ->
    % Z3's simplify returns the simplified expression
    % For now, if we can't parse it easily, return original
    % TODO: Implement proper S-expression parser for simplified results
    case parse_sexp_to_constraint(Lines) of
        {ok, Simplified} -> Simplified;
        {error, _} -> _OriginalConstraint
    end;
parse_simplified_result(_Result, OriginalConstraint) ->
    % If we can't parse the result, return original
    OriginalConstraint.

%% Parse S-expression back to constraint AST
%% Handles S-expressions from Z3 simplify command output
parse_sexp_to_constraint(Lines) when is_list(Lines) ->
    % Join lines and convert to string if needed
    ExprStr =
        case Lines of
            [Binary | _] when is_binary(Binary) ->
                lists:concat([binary_to_list(L) || L <- Lines]);
            [String | _] when is_list(String) ->
                lists:concat(Lines);
            _ ->
                ""
        end,

    % Try to tokenize and parse the S-expression
    try
        case tokenize_sexp(ExprStr, []) of
            {ok, Tokens} ->
                case parse_sexp_tokens(Tokens) of
                    {ok, {Term, []}} ->
                        case sexp_term_to_constraint(Term) of
                            {ok, Constraint} -> {ok, Constraint};
                            {error, _} = Error -> Error
                        end;
                    {ok, _} ->
                        {error, unexpected_tokens};
                    {error, Reason} ->
                        {error, Reason}
                end;
            {error, Reason} ->
                {error, {tokenize_error, Reason}}
        end
    catch
        _:_ -> {error, parse_exception}
    end;
parse_sexp_to_constraint(_) ->
    {error, invalid_format}.

%% Tokenize S-expression string into tokens
tokenize_sexp([], Acc) ->
    {ok, lists:reverse(Acc)};
tokenize_sexp([C | Rest], Acc) when C =:= $( ->
    tokenize_sexp(Rest, [{'(', 1} | Acc]);
tokenize_sexp([C | Rest], Acc) when C =:= $) ->
    tokenize_sexp(Rest, [{')', 1} | Acc]);
tokenize_sexp([C | Rest], Acc) when C =:= 32 orelse C =:= 9 orelse C =:= 10 ->
    % Skip whitespace
    tokenize_sexp(Rest, Acc);
tokenize_sexp(String, Acc) ->
    % Try to parse a symbol/number
    case parse_atom_or_number(String) of
        {ok, Token, Rest} ->
            tokenize_sexp(Rest, [Token | Acc]);
        {error, Reason} ->
            {error, Reason}
    end.

%% Parse atom or number from string
parse_atom_or_number([C | Rest] = String) ->
    case C of
        $- when Rest =/= "" ->
            % Could be negative number
            case parse_number_chars(Rest, [C]) of
                {ok, NumStr, Remaining} ->
                    {ok, {number, list_to_integer(NumStr)}, Remaining};
                {error, _} ->
                    % Not a number, parse as atom
                    parse_symbol_chars(String, [])
            end;
        _ when C >= $0, C =< $9 ->
            % Number
            case parse_number_chars(String, []) of
                {ok, NumStr, Remaining} ->
                    {ok, {number, list_to_integer(NumStr)}, Remaining};
                {error, _} = Error ->
                    Error
            end;
        _ ->
            % Symbol
            parse_symbol_chars(String, [])
    end.

%% Parse number characters
parse_number_chars([C | Rest], NumAcc) when (C >= $0 andalso C =< $9) orelse C =:= $. ->
    parse_number_chars(Rest, [C | NumAcc]);
parse_number_chars([C | _] = Rest, NumAcc) when C =:= $( orelse C =:= $) orelse C =:= 32 ->
    {ok, lists:reverse(NumAcc), Rest};
parse_number_chars([], NumAcc) ->
    {ok, lists:reverse(NumAcc), []};
parse_number_chars(_, _) ->
    {error, invalid_number}.

%% Parse symbol characters
parse_symbol_chars([C | Rest], SymAcc) when
    (C >= $a andalso C =< $z) orelse (C >= $A andalso C =< $Z) orelse
        (C >= $0 andalso C =< $9) orelse C =:= $_ orelse C =:= $- orelse C =:= $? orelse
        C =:= $+ orelse C =:= $* orelse C =:= $/ orelse C =:= $= orelse C =:= $< orelse C =:= $>
->
    parse_symbol_chars(Rest, [C | SymAcc]);
parse_symbol_chars([C | _] = Rest, SymAcc) when C =:= $( orelse C =:= $) orelse C =:= 32 ->
    case SymAcc of
        [] -> {error, invalid_symbol};
        _ -> {ok, {symbol, list_to_atom(lists:reverse(SymAcc))}, Rest}
    end;
parse_symbol_chars([], SymAcc) when length(SymAcc) > 0 ->
    {ok, {symbol, list_to_atom(lists:reverse(SymAcc))}, []};
parse_symbol_chars(_, _) ->
    {error, invalid_symbol}.

%% Parse S-expression tokens into terms
parse_sexp_tokens(Tokens) ->
    parse_sexp_term(Tokens, []).

parse_sexp_term([{'(', _} | Rest], Stack) ->
    % Start of list
    parse_sexp_term(Rest, [[] | Stack]);
parse_sexp_term([{')', _} | Rest], [List | ParentStack]) ->
    % End of list
    Term = {list, lists:reverse(List)},
    case ParentStack of
        [] -> {ok, {Term, Rest}};
        [Parent | Grandparents] -> parse_sexp_term(Rest, [[Term | Parent] | Grandparents])
    end;
parse_sexp_term([Token | Rest], [[] | _] = Stack) ->
    % First element in a list
    parse_sexp_term(Rest, [[Token] | tl(Stack)]);
parse_sexp_term([Token | Rest], [[List | _] | _] = Stack) ->
    % Add to current list
    parse_sexp_term(Rest, [[Token | List] | tl(Stack)]);
parse_sexp_term([], [[Term]]) ->
    {ok, {Term, []}};
parse_sexp_term([], _) ->
    {error, incomplete_expression};
parse_sexp_term(_, _) ->
    {error, parse_error}.

%% Convert S-expression term to Cure constraint AST
sexp_term_to_constraint({symbol, true}) ->
    {ok, #literal_expr{value = true, location = #location{line = 0, column = 0, file = undefined}}};
sexp_term_to_constraint({symbol, false}) ->
    {ok, #literal_expr{value = false, location = #location{line = 0, column = 0, file = undefined}}};
sexp_term_to_constraint({number, Num}) ->
    {ok, #literal_expr{value = Num, location = #location{line = 0, column = 0, file = undefined}}};
sexp_term_to_constraint({symbol, Name}) ->
    {ok, #identifier_expr{
        name = Name, location = #location{line = 0, column = 0, file = undefined}
    }};
sexp_term_to_constraint({list, []}) ->
    {error, empty_list};
sexp_term_to_constraint({list, [{symbol, Op} | Args]}) ->
    % Binary or unary operation
    case length(Args) of
        1 ->
            % Unary operation
            case sexp_term_to_constraint(hd(Args)) of
                {ok, Arg} ->
                    {ok, #unary_op_expr{
                        op = Op,
                        operand = Arg,
                        location = #location{line = 0, column = 0, file = undefined}
                    }};
                {error, _} = Error ->
                    Error
            end;
        2 ->
            % Binary operation
            case
                {
                    sexp_term_to_constraint(lists:nth(1, Args)),
                    sexp_term_to_constraint(lists:nth(2, Args))
                }
            of
                {{ok, Left}, {ok, Right}} ->
                    {ok, #binary_op_expr{
                        op = Op,
                        left = Left,
                        right = Right,
                        location = #location{line = 0, column = 0, file = undefined}
                    }};
                {{error, _} = Error, _} ->
                    Error;
                {_, {error, _} = Error} ->
                    Error
            end;
        _ ->
            {error, {unsupported_arity, Op, length(Args)}}
    end;
sexp_term_to_constraint(_) ->
    {error, invalid_constraint_term}.

%% Parse CVC5 model output
%% CVC5 outputs satisfying models in a format similar to Z3
parse_cvc5_model(Lines) when is_list(Lines) ->
    % Filter out empty lines and comments
    FilteredLines = [Line || Line <- Lines, Line =/= "", not is_comment_line(Line)],

    % Extract variable assignments from model
    % CVC5 format: (define-fun var_name () Type Value)
    % or simpler format: var_name = value
    case extract_cvc5_assignments(FilteredLines, #{}) of
        {ok, Model} when is_map(Model) ->
            {ok, Model};
        {error, Reason} ->
            {error, {cvc5_parse_error, Reason}}
    end;
parse_cvc5_model(_) ->
    {error, invalid_model_format}.

%% Check if line is a comment
is_comment_line(Line) when is_list(Line) ->
    case string:left(string:strip(Line), 1) of
        ";" -> true;
        _ -> false
    end;
is_comment_line(_) ->
    false.

%% Extract variable assignments from CVC5 model lines
extract_cvc5_assignments([], Acc) ->
    {ok, Acc};
extract_cvc5_assignments([Line | Rest], Acc) ->
    case parse_cvc5_assignment(Line) of
        {ok, VarName, Value} ->
            extract_cvc5_assignments(Rest, maps:put(VarName, Value, Acc));
        skip ->
            % Line doesn't contain assignment, skip
            extract_cvc5_assignments(Rest, Acc);
        {error, Reason} ->
            {error, {assignment_parse_error, Line, Reason}}
    end.

%% Parse a single CVC5 assignment line
%% Handles both: (define-fun x () Int 42) and simpler formats
parse_cvc5_assignment(Line) when is_list(Line) ->
    Trimmed = string:strip(Line),
    case string:str(Trimmed, "=") of
        0 ->
            % Try define-fun format
            case string:str(Trimmed, "define-fun") of
                0 -> skip;
                _ -> parse_define_fun(Trimmed)
            end;
        Pos ->
            % Simple assignment format: name = value
            VarPart = string:sub_string(Trimmed, 1, Pos - 1),
            ValuePart = string:sub_string(Trimmed, Pos + 1, length(Trimmed)),
            VarName = string:strip(VarPart),
            ValueStr = string:strip(ValuePart),
            case parse_value(ValueStr) of
                {ok, Value} -> {ok, list_to_atom(VarName), Value};
                {error, Reason} -> {error, Reason}
            end
    end;
parse_cvc5_assignment(_) ->
    skip.

%% Parse (define-fun x () Type Value) format
parse_define_fun(Line) ->
    % This is a simplified parser for define-fun
    % Full parsing would need proper S-expression parsing
    case
        re:match(Line, "\\(define-fun\\s+(\\w+).*\\s+(\\d+|true|false)\\)", [{capture, ['all']}])
    of
        {match, [_All, VarStr, ValueStr]} ->
            VarName = binary_to_list(VarStr),
            case parse_value(binary_to_list(ValueStr)) of
                {ok, Value} -> {ok, list_to_atom(VarName), Value};
                {error, Reason} -> {error, Reason}
            end;
        nomatch ->
            skip
    end.

%% Parse a value string to Erlang term
parse_value("true") ->
    {ok, true};
parse_value("false") ->
    {ok, false};
parse_value(Str) ->
    case string:to_integer(Str) of
        {Int, ""} ->
            {ok, Int};
        {_Int, _Rest} ->
            case string:to_float(Str) of
                {Float, ""} -> {ok, Float};
                {error, _} -> {error, {invalid_value, Str}}
            end;
        {error, _} ->
            {error, {invalid_value, Str}}
    end.

%% Format constraint for user-friendly display
format_constraint(#binary_op_expr{op = Op, left = Left, right = Right}) ->
    io_lib:format("(~s ~s ~s)", [format_constraint(Left), Op, format_constraint(Right)]);
format_constraint(#unary_op_expr{op = Op, operand = Operand}) ->
    io_lib:format("(~s ~s)", [Op, format_constraint(Operand)]);
format_constraint(#identifier_expr{name = Name}) ->
    atom_to_list(Name);
format_constraint(#literal_expr{value = Value}) ->
    io_lib:format("~p", [Value]);
format_constraint(#function_call_expr{function = Fun, args = Args}) ->
    ArgStrs = lists:map(fun format_constraint/1, Args),
    io_lib:format("~s(~s)", [format_constraint(Fun), string:join(ArgStrs, ", ")]);
format_constraint(Other) ->
    io_lib:format("~p", [Other]).

%% ============================================================================
%% Helper Functions for LSP Integration
%% ============================================================================

%% @doc Create an equality constraint for SMT
equality_constraint(Left, Right) ->
    #binary_op_expr{
        op = '==',
        left = Left,
        right = Right,
        location = #location{line = 0, column = 0, file = undefined}
    }.

%% @doc Create an inequality constraint for SMT
inequality_constraint(Left, Op, Right) ->
    #binary_op_expr{
        op = Op,
        left = Left,
        right = Right,
        location = #location{line = 0, column = 0, file = undefined}
    }.

%% @doc Create a variable term
variable_term(Name) when is_atom(Name) ->
    #identifier_expr{
        name = Name,
        location = #location{line = 0, column = 0, file = undefined}
    };
variable_term(Name) when is_list(Name) ->
    variable_term(list_to_atom(Name)).

%% @doc Create a constant term
constant_term(Value) ->
    #literal_expr{
        value = Value,
        location = #location{line = 0, column = 0, file = undefined}
    }.
