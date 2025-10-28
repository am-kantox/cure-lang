-module(cure_guard_codegen).

-moduledoc """
# Guard Validation Code Generation

This module generates runtime validation code for dependent type guards.
It translates guard constraints into executable BEAM code that validates
values against dependent type requirements.

## Features

- **Dependent Type Validation**: Generate checks for dependent type constraints
- **Optimized Code**: Efficient guard code with minimal runtime overhead
- **SMT Integration**: Use SMT solver results to optimize guard checks
- **Error Reporting**: Generate informative error messages for failed guards

## Guard Types

### Numeric Constraints
```cure
Vector(T, n: Nat) when n > 0
```
Generates: Runtime check that n > 0

### Refinement Types
```cure
NonEmpty(T) = List(T, n) when n > 0
```
Generates: Length check for lists

### Complex Constraints
```cure
Matrix(T, rows: Nat, cols: Nat) when rows > 0 and cols > 0
```
Generates: Multiple validation checks

## Code Generation Strategy

1. **Static Analysis**: Use SMT solver to prove constraints at compile time
2. **Runtime Guards**: Generate checks for constraints that can't be proven
3. **Optimization**: Eliminate redundant checks through dataflow analysis
4. **Caching**: Cache validation results for expensive computations
""".

-export([
    generate_guard/2,
    generate_guard/3,
    generate_validation_function/3,
    optimize_guard/2,
    compile_constraint/2
]).

-include("../parser/cure_ast.hrl").

%%% Public API %%%

%% @doc Generate guard validation code from constraint expression
-spec generate_guard(expr(), map()) -> {ok, erl_syntax:syntaxTree()} | {error, term()}.
generate_guard(Constraint, Env) ->
    generate_guard(Constraint, Env, #{}).

%% @doc Generate guard with options
-spec generate_guard(expr(), map(), map()) -> {ok, erl_syntax:syntaxTree()} | {error, term()}.
generate_guard(Constraint, Env, Opts) ->
    % First try to prove the constraint statically
    case try_static_proof(Constraint, Env, Opts) of
        {proven, true} ->
            % Constraint always holds, no runtime check needed
            {ok, erl_syntax:atom(true)};
        {proven, false} ->
            % Constraint never holds, generate compile-time error
            {error, {constraint_never_holds, Constraint}};
        unknown ->
            % Need runtime check
            generate_runtime_guard(Constraint, Env, Opts)
    end.

%% @doc Generate a validation function for a dependent type
-spec generate_validation_function(atom(), [#param{}], expr()) -> {ok, erl_syntax:syntaxTree()}.
generate_validation_function(TypeName, Params, Constraint) ->
    % Generate function: validate_TypeName(Param1, Param2, ...) -> boolean()
    FunctionName = list_to_atom("validate_" ++ atom_to_list(TypeName)),

    ParamVars = [erl_syntax:variable(atom_to_list(P#param.name)) || P <- Params],

    Env = lists:foldl(
        fun(P, AccEnv) ->
            maps:put(P#param.name, P#param.type, AccEnv)
        end,
        #{},
        Params
    ),

    case generate_guard(Constraint, Env, #{}) of
        {ok, GuardCode} ->
            Function = erl_syntax:function(
                erl_syntax:atom(FunctionName),
                [erl_syntax:clause(ParamVars, none, [GuardCode])]
            ),
            {ok, Function};
        {error, Error} ->
            {error, Error}
    end.

%% @doc Optimize guard by removing redundant checks
-spec optimize_guard(erl_syntax:syntaxTree(), map()) -> erl_syntax:syntaxTree().
optimize_guard(GuardAST, Env) ->
    % Apply optimization passes
    GuardAST1 = fold_constants(GuardAST),
    GuardAST2 = eliminate_dead_checks(GuardAST1, Env),
    GuardAST3 = combine_conjunctions(GuardAST2),
    GuardAST3.

%% @doc Compile constraint expression to BEAM-compatible guard expression
-spec compile_constraint(expr(), map()) -> {ok, erl_syntax:syntaxTree()} | {error, term()}.
compile_constraint(Constraint, Env) ->
    generate_runtime_guard(Constraint, Env, #{}).

%%% Internal Functions %%%

%% Try to prove constraint statically using SMT solver
try_static_proof(_Constraint, _Env, Opts) ->
    UseSMT = maps:get(use_smt, Opts, true),

    case UseSMT of
        true ->
            % TODO: Integrate with SMT solver
            % For now, return unknown
            unknown;
        false ->
            unknown
    end.

%% Generate runtime guard code
generate_runtime_guard(Constraint, Env, _Opts) ->
    compile_constraint_expr(Constraint, Env).

%% Compile constraint expression to Erlang AST
compile_constraint_expr(#binary_op_expr{op = Op, left = Left, right = Right}, Env) ->
    case compile_constraint_expr(Left, Env) of
        {ok, LeftCode} ->
            case compile_constraint_expr(Right, Env) of
                {ok, RightCode} ->
                    OpCode = compile_operator(Op),
                    {ok, erl_syntax:infix_expr(LeftCode, OpCode, RightCode)};
                Error ->
                    Error
            end;
        Error ->
            Error
    end;
compile_constraint_expr(#unary_op_expr{op = Op, operand = Operand}, Env) ->
    case compile_constraint_expr(Operand, Env) of
        {ok, OperandCode} ->
            OpCode = compile_unary_operator(Op),
            {ok, erl_syntax:prefix_expr(OpCode, OperandCode)};
        Error ->
            Error
    end;
compile_constraint_expr(#identifier_expr{name = Name}, Env) ->
    % Look up variable in environment
    case maps:get(Name, Env, undefined) of
        undefined ->
            {error, {undefined_variable, Name}};
        _Type ->
            % Generate variable reference
            VarName = atom_to_list(Name),
            {ok, erl_syntax:variable(VarName)}
    end;
compile_constraint_expr(#literal_expr{value = Value}, _Env) ->
    {ok, compile_literal(Value)};
compile_constraint_expr(#function_call_expr{function = FuncExpr, args = Args}, Env) ->
    case compile_constraint_expr(FuncExpr, Env) of
        {ok, FuncCode} ->
            case compile_argument_list(Args, Env) of
                {ok, ArgsCode} ->
                    {ok, erl_syntax:application(FuncCode, ArgsCode)};
                Error ->
                    Error
            end;
        Error ->
            Error
    end;
compile_constraint_expr(Expr, _Env) ->
    {error, {unsupported_constraint_expr, Expr}}.

%% Compile operator to Erlang operator
compile_operator('+') -> erl_syntax:operator('+');
compile_operator('-') -> erl_syntax:operator('-');
compile_operator('*') -> erl_syntax:operator('*');
compile_operator('/') -> erl_syntax:operator('/');
compile_operator('div') -> erl_syntax:operator('div');
compile_operator('rem') -> erl_syntax:operator('rem');
compile_operator('==') -> erl_syntax:operator('==');
compile_operator('/=') -> erl_syntax:operator('/=');
compile_operator('<') -> erl_syntax:operator('<');
compile_operator('>') -> erl_syntax:operator('>');
compile_operator('=<') -> erl_syntax:operator('=<');
compile_operator('>=') -> erl_syntax:operator('>=');
compile_operator('and') -> erl_syntax:operator('andalso');
compile_operator('or') -> erl_syntax:operator('orelse');
compile_operator(Op) -> erl_syntax:operator(Op).

%% Compile unary operator
compile_unary_operator('not') -> erl_syntax:operator('not');
compile_unary_operator('-') -> erl_syntax:operator('-');
compile_unary_operator(Op) -> erl_syntax:operator(Op).

%% Compile literal value
compile_literal(Value) when is_integer(Value) ->
    erl_syntax:integer(Value);
compile_literal(Value) when is_float(Value) ->
    erl_syntax:float(Value);
compile_literal(Value) when is_boolean(Value) ->
    erl_syntax:atom(Value);
compile_literal(Value) when is_atom(Value) ->
    erl_syntax:atom(Value);
compile_literal(Value) when is_binary(Value) ->
    erl_syntax:string(binary_to_list(Value));
compile_literal(Value) when is_list(Value) ->
    Elements = [compile_literal(E) || E <- Value],
    erl_syntax:list(Elements).

%% Compile argument list
compile_argument_list(Args, Env) ->
    compile_argument_list(Args, Env, []).

compile_argument_list([], _Env, Acc) ->
    {ok, lists:reverse(Acc)};
compile_argument_list([Arg | Rest], Env, Acc) ->
    case compile_constraint_expr(Arg, Env) of
        {ok, ArgCode} ->
            compile_argument_list(Rest, Env, [ArgCode | Acc]);
        Error ->
            Error
    end.

%%% Optimization Passes %%%

%% Constant folding
fold_constants(AST) ->
    erl_syntax_lib:map(fun fold_constant_node/1, AST).

fold_constant_node(Node) ->
    case erl_syntax:type(Node) of
        infix_expr ->
            Left = erl_syntax:infix_expr_left(Node),
            Right = erl_syntax:infix_expr_right(Node),
            _Op = erl_syntax:infix_expr_operator(Node),

            case {is_constant(Left), is_constant(Right)} of
                {true, true} ->
                    % Both operands are constant, evaluate
                    try
                        Result = evaluate_constant_expr(Node),
                        compile_literal(Result)
                    catch
                        _:_ -> Node
                    end;
                _ ->
                    Node
            end;
        _ ->
            Node
    end.

is_constant(Node) ->
    Type = erl_syntax:type(Node),
    lists:member(Type, [integer, float, atom, string]).

evaluate_constant_expr(_Node) ->
    % This is a simplified evaluator
    % In practice, you'd use erl_eval or similar
    throw({not_implemented, evaluate_constant_expr}).

%% Eliminate dead checks (checks that are always true)
eliminate_dead_checks(AST, _Env) ->
    erl_syntax_lib:map(
        fun(Node) ->
            case erl_syntax:type(Node) of
                infix_expr ->
                    Op = erl_syntax:infix_expr_operator(Node),
                    case erl_syntax:operator_name(Op) of
                        'andalso' ->
                            Left = erl_syntax:infix_expr_left(Node),
                            Right = erl_syntax:infix_expr_right(Node),

                            % If left is 'true', return right
                            case is_true_literal(Left) of
                                true ->
                                    Right;
                                false ->
                                    % If right is 'true', return left
                                    case is_true_literal(Right) of
                                        true -> Left;
                                        false -> Node
                                    end
                            end;
                        'orelse' ->
                            Left = erl_syntax:infix_expr_left(Node),
                            Right = erl_syntax:infix_expr_right(Node),

                            % If left is 'true', return 'true'
                            case is_true_literal(Left) of
                                true -> erl_syntax:atom(true);
                                false -> Node
                            end;
                        _ ->
                            Node
                    end;
                _ ->
                    Node
            end
        end,
        AST
    ).

is_true_literal(Node) ->
    case erl_syntax:type(Node) of
        atom ->
            erl_syntax:atom_value(Node) =:= true;
        _ ->
            false
    end.

%% Combine adjacent conjunctions
combine_conjunctions(AST) ->
    % Flatten nested andalso expressions
    erl_syntax_lib:map(
        fun(Node) ->
            case erl_syntax:type(Node) of
                infix_expr ->
                    Op = erl_syntax:infix_expr_operator(Node),
                    case erl_syntax:operator_name(Op) of
                        'andalso' ->
                            flatten_conjunction(Node);
                        _ ->
                            Node
                    end;
                _ ->
                    Node
            end
        end,
        AST
    ).

flatten_conjunction(Node) ->
    % Extract all conjuncts
    Conjuncts = collect_conjuncts(Node),

    % Rebuild as right-associated andalso chain
    build_conjunction(Conjuncts).

collect_conjuncts(Node) ->
    case erl_syntax:type(Node) of
        infix_expr ->
            Op = erl_syntax:infix_expr_operator(Node),
            case erl_syntax:operator_name(Op) of
                'andalso' ->
                    Left = erl_syntax:infix_expr_left(Node),
                    Right = erl_syntax:infix_expr_right(Node),
                    collect_conjuncts(Left) ++ collect_conjuncts(Right);
                _ ->
                    [Node]
            end;
        _ ->
            [Node]
    end.

build_conjunction([]) ->
    erl_syntax:atom(true);
build_conjunction([Single]) ->
    Single;
build_conjunction([First | Rest]) ->
    Right = build_conjunction(Rest),
    erl_syntax:infix_expr(First, erl_syntax:operator('andalso'), Right).
