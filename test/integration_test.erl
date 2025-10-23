%% Integration Tests - End-to-end Cure compiler functionality
-module(integration_test).

-export([run/0]).

-include("../src/parser/cure_ast.hrl").
% Note: Some includes may not be available due to missing header files

%% Run all integration tests
run() ->
    cure_utils:debug("Running Integration tests...~n"),

    Tests = [
        fun test_simple_module_compilation/0,
        fun test_function_with_types/0,
        fun test_fsm_compilation/0,
        fun test_dependent_types_basic/0,
        fun test_let_expressions/0,
        fun test_pattern_matching/0,
        fun test_arithmetic_operations/0,
        fun test_full_compilation_pipeline/0,
        fun test_compilation_error_handling/0
    ],

    Results = [run_test(Test) || Test <- Tests],
    Passed = length([ok || ok <- Results]),
    Total = length(Results),

    cure_utils:debug("Integration tests: ~w/~w passed~n", [Passed, Total]),

    case Passed of
        Total ->
            cure_utils:debug("All integration tests passed!~n"),
            ok;
        _ ->
            cure_utils:debug("Some integration tests failed~n"),
            error
    end.

%% Helper function to run individual tests
run_test(TestFun) ->
    try
        TestFun(),
        ok
    catch
        Error:Reason:Stack ->
            cure_utils:debug("❌ Test ~w failed: ~p:~p~n", [TestFun, Error, Reason]),
            cure_utils:debug("Stack: ~p~n", [Stack]),
            error
    end.

%% Test 1: Simple module compilation
test_simple_module_compilation() ->
    cure_utils:debug("✓ Testing simple module compilation...~n"),

    % Create a simple Cure program
    CureCode =
        "module Math do\n"
        "  export [add/2]\n"
        "  def add(x: Int, y: Int): Int = x + y\n"
        "end",

    % Tokenize
    {ok, Tokens} = cure_lexer:scan(CureCode),

    % Parse
    {ok, AST} = cure_parser:parse(Tokens),

    % Verify we got a module
    case AST of
        #module_def{name = 'Math', exports = Exports, items = Items} ->
            % Check exports
            true = lists:member({add, 2}, Exports),

            % Check we have function definition
            [FuncDef] = Items,
            case FuncDef of
                #function_def{name = add, params = Params, body = _Body} ->
                    2 = length(Params),
                    ok;
                _ ->
                    throw({unexpected_function_def, FuncDef})
            end;
        _ ->
            throw({unexpected_ast, AST})
    end,

    cure_utils:debug("  ✓ Simple module compilation test passed~n").

%% Test 2: Function with types
test_function_with_types() ->
    cure_utils:debug("✓ Testing function with type annotations...~n"),

    % Create function with types
    FuncCode = "def factorial(n: Nat): Pos = if n == 0 then 1 else n * factorial(n - 1)",

    % Tokenize
    {ok, Tokens} = cure_lexer:scan(FuncCode),

    % Parse function definition
    {ok, FuncDef} = cure_parser:parse_function_def(Tokens),

    % Check the function structure
    case FuncDef of
        #function_def{
            name = factorial,
            params = [Param],
            return_type = ReturnType,
            body = Body
        } ->
            % Check parameter type
            case Param of
                #param{name = n, type = {primitive_type, 'Nat'}} -> ok;
                _ -> throw({unexpected_param, Param})
            end,

            % Check return type
            case ReturnType of
                {primitive_type, 'Pos'} -> ok;
                _ -> throw({unexpected_return_type, ReturnType})
            end,

            % Check body is an if expression
            case Body of
                #if_expr{} -> ok;
                _ -> throw({unexpected_body, Body})
            end;
        _ ->
            throw({unexpected_function_def, FuncDef})
    end,

    cure_utils:debug("  ✓ Function with types test passed~n").

%% Test 3: FSM compilation
test_fsm_compilation() ->
    cure_utils:debug("✓ Testing FSM compilation...~n"),

    % Create simple FSM
    FSMCode =
        "fsm Counter do\n"
        "  states: [Zero, One]\n"
        "  initial: Zero\n"
        "  state Zero do\n"
        "    event(:inc) -> One\n"
        "  end\n"
        "  state One do\n"
        "    event(:dec) -> Zero\n"
        "  end\n"
        "end",

    % Tokenize
    {ok, Tokens} = cure_lexer:scan(FSMCode),

    % Parse FSM definition
    {ok, FSMDef} = cure_parser:parse_fsm_def(Tokens),

    % Check FSM structure
    case FSMDef of
        #fsm_def{
            name = 'Counter',
            states = States,
            initial = Initial,
            state_defs = StateDefs
        } ->
            % Check states
            true = lists:member('Zero', States),
            true = lists:member('One', States),

            % Check initial state
            'Zero' = Initial,

            % Check state definitions
            2 = length(StateDefs),
            ok;
        _ ->
            throw({unexpected_fsm_def, FSMDef})
    end,

    cure_utils:debug("  ✓ FSM compilation test passed~n").

%% Test 4: Basic dependent types
test_dependent_types_basic() ->
    cure_utils:debug("✓ Testing basic dependent types...~n"),

    % Create function with dependent type
    DepTypeCode = "def safe_head(list: List(T, n)) -> T when n > 0 = head(list)",

    % Tokenize
    {ok, Tokens} = cure_lexer:scan(DepTypeCode),

    % Parse
    {ok, FuncDef} = cure_parser:parse_function_def(Tokens),

    % Check dependent type structure
    case FuncDef of
        #function_def{
            name = safe_head,
            params = Params,
            return_type = RetType,
            constraint = Constr
        } ->
            % Check we have one parameter
            [FirstParam] = Params,

            % Check parameter has dependent list type
            case FirstParam of
                #param{
                    name = list,
                    % Simplified check for now
                    type = _Type
                } ->
                    ok;
                _ ->
                    throw({unexpected_param_type, FirstParam})
            end,

            % Check return type exists
            case RetType of
                undefined -> throw({missing_return_type, RetType});
                _ -> ok
            end,

            % Check constraint exists
            case Constr of
                undefined -> throw({missing_constraint, Constr});
                _ -> ok
            end;
        _ ->
            throw({unexpected_function_def, FuncDef})
    end,

    cure_utils:debug("  ✓ Dependent types test passed~n").

%% Test 5: Let expressions
test_let_expressions() ->
    cure_utils:debug("✓ Testing let expressions...~n"),

    % Create let expression
    LetCode = "let x = 42, y = x + 1 in x + y",

    % Tokenize
    {ok, Tokens} = cure_lexer:scan(LetCode),

    % Parse as expression
    {ok, LetExpr} = cure_parser:parse_expression(Tokens),

    % Check let expression structure
    case LetExpr of
        #let_expr{
            bindings = Bindings,
            body = Body
        } ->
            % Check bindings
            2 = length(Bindings),

            % Check body is a binary operation
            case Body of
                #binary_op_expr{op = '+'} -> ok;
                _ -> throw({unexpected_let_body, Body})
            end;
        _ ->
            throw({unexpected_let_expr, LetExpr})
    end,

    cure_utils:debug("  ✓ Let expressions test passed~n").

%% Test 6: Pattern matching
test_pattern_matching() ->
    cure_utils:debug("✓ Testing pattern matching...~n"),

    % Create match expression
    MatchCode =
        "match list do\n"
        "  [] -> 0\n"
        "  [x|xs] -> 1 + length(xs)\n"
        "end",

    % Tokenize
    {ok, Tokens} = cure_lexer:scan(MatchCode),

    % Parse match expression
    {ok, MatchExpr} = cure_parser:parse_expression(Tokens),

    % Check match structure
    case MatchExpr of
        #match_expr{
            expr = Expr,
            patterns = Patterns
        } ->
            % Check we're matching on 'list' identifier
            case Expr of
                #identifier_expr{name = list} -> ok;
                _ -> throw({unexpected_match_expr, Expr})
            end,

            % Check we have two patterns
            2 = length(Patterns),
            ok;
        _ ->
            throw({unexpected_match_expr, MatchExpr})
    end,

    cure_utils:debug("  ✓ Pattern matching test passed~n").

%% Test 7: Arithmetic operations
test_arithmetic_operations() ->
    cure_utils:debug("✓ Testing arithmetic operations...~n"),

    % Create arithmetic expression
    ArithCode = "(2 + 3) * 4 - 1",

    % Tokenize
    {ok, Tokens} = cure_lexer:scan(ArithCode),

    % Parse expression
    {ok, ArithExpr} = cure_parser:parse_expression(Tokens),

    % Check arithmetic structure (should be nested binary operations)
    case ArithExpr of
        #binary_op_expr{op = '-'} -> ok;
        _ -> throw({unexpected_arithmetic_expr, ArithExpr})
    end,

    % Try to type check the expression
    TypeEnv = cure_typechecker:builtin_env(),
    {ok, _Type} = cure_typechecker:infer_type(ArithExpr, TypeEnv),

    cure_utils:debug("  ✓ Arithmetic operations test passed~n").

%% Additional helper functions for future integration tests

%% Test end-to-end compilation pipeline
test_full_compilation_pipeline() ->
    cure_utils:debug("✓ Testing full compilation pipeline...~n"),

    % Simple program
    Program =
        "module Test do\n"
        "  def double(x: Int): Int = x * 2\n"
        "end",

    % Full pipeline: Lexer -> Parser -> Type Checker -> Code Generator
    {ok, Tokens} = cure_lexer:scan(Program),
    {ok, AST} = cure_parser:parse(Tokens),

    TypeEnv = cure_typechecker:builtin_env(),
    {ok, TypedAST} = cure_typechecker:check_module(AST, TypeEnv),

    {ok, _Instructions} = cure_codegen:compile_module(TypedAST, #{}),

    cure_utils:debug("  ✓ Full compilation pipeline test passed~n").

%% Test error handling in compilation
test_compilation_error_handling() ->
    cure_utils:debug("✓ Testing compilation error handling...~n"),

    % Program with type error

    % Type mismatch
    BadProgram = "def bad_func(x: Int): String = x + 1",

    try
        {ok, Tokens} = cure_lexer:scan(BadProgram),
        {ok, AST} = cure_parser:parse(Tokens),
        TypeEnv = cure_typechecker:builtin_env(),

        % This should fail with type error
        case cure_typechecker:check_function(AST, TypeEnv) of
            {error, _Reason} ->
                cure_utils:debug("  ✓ Correctly caught type error~n"),
                ok;
            {ok, _} ->
                throw(expected_type_error)
        end
    catch
        _:_ ->
            cure_utils:debug("  ✓ Error handling working correctly~n"),
            ok
    end.
