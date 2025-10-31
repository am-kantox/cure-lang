-module(cure_smt_solver).

-moduledoc """
# SMT Solver Integration for Cure

This module provides integration with SMT (Satisfiability Modulo Theories) solvers
for dependent type constraint verification and optimization. It supports multiple
backend solvers including Z3, CVC5, and others.

## Features

- **Constraint Verification**: Prove or disprove type constraints at compile time
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
    available_solvers/0,
    set_solver/1
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

%% @doc Simplify a constraint using SMT solver
-spec simplify_constraint(expr(), map()) -> expr().
simplify_constraint(Constraint, _Env) ->
    % TODO: Use SMT solver to simplify constraint
    % For now, return as-is
    Constraint.

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
            % Fallback to symbolic
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
                                {ok, Model} -> {sat, Model};
                                {error, _} -> {sat, #{}}
                            end;
                        {unsat, _} ->
                            unsat;
                        {unknown, _} ->
                            unknown;
                        {error, _Reason} ->
                            unknown
                    end,

                % 5. Clean up
                cure_smt_process:stop_solver(Pid),
                ParsedResult
            catch
                _:_ ->
                    % Fall back to symbolic on any error
                    check_with_symbolic(Constraint, Env, Context)
            end
    end.

%% Check with CVC5
check_with_cvc5(Constraint, Env, Context) ->
    case find_cvc5() of
        false ->
            % Fallback to symbolic
            check_with_symbolic(Constraint, Env, Context);
        true ->
            % TODO: Implement actual CVC5 integration
            % For now, use symbolic fallback
            check_with_symbolic(Constraint, Env, Context)
    end.

%% Check with symbolic evaluation
check_with_symbolic(Constraint, Env, _Context) ->
    % Simple symbolic evaluation for basic constraints
    try
        case eval_symbolic(Constraint, Env) of
            true -> sat;
            false -> unsat;
            _ -> unknown
        end
    catch
        _:_ -> unknown
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
