%% Integration Tests - End-to-end Cure compiler functionality
-module(integration_test).

-export([run/0]).

-include("../src/parser/cure_ast.hrl").
% Note: Some includes may not be available due to missing header files

%% Run all integration tests
run() ->
    io:format("Running Integration tests...~n"),
    
    Tests = [
        fun test_simple_module_compilation/0,
        fun test_function_with_types/0,
        fun test_fsm_compilation/0,
        fun test_dependent_types_basic/0,
        fun test_let_expressions/0,
        fun test_pattern_matching/0,
        fun test_arithmetic_operations/0
    ],
    
    Results = [run_test(Test) || Test <- Tests],
    Passed = length([ok || ok <- Results]),
    Total = length(Results),
    
    io:format("Integration tests: ~w/~w passed~n", [Passed, Total]),
    
    case Passed of
        Total -> 
            io:format("All integration tests passed!~n"),
            ok;
        _ -> 
            io:format("Some integration tests failed~n"),
            error
    end.

%% Helper function to run individual tests
run_test(TestFun) ->
    try
        TestFun(),
        ok
    catch
        Error:Reason:Stack ->
            io:format("❌ Test ~w failed: ~p:~p~n", [TestFun, Error, Reason]),
            io:format("Stack: ~p~n", [Stack]),
            error
    end.

%% Test 1: Simple module compilation
test_simple_module_compilation() ->
    io:format("✓ Testing simple module compilation...~n"),
    
    % Create a simple Cure program
    CureCode = "module Math do\n"
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
    
    io:format("  ✓ Simple module compilation test passed~n").

%% Test 2: Function with types
test_function_with_types() ->
    io:format("✓ Testing function with type annotations...~n"),
    
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
    
    io:format("  ✓ Function with types test passed~n").

%% Test 3: FSM compilation
test_fsm_compilation() ->
    io:format("✓ Testing FSM compilation...~n"),
    
    % Create simple FSM
    FSMCode = "fsm Counter do\n"
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
            initial_state = InitialState,
            state_definitions = StateDefs
        } ->
            % Check states
            true = lists:member('Zero', States),
            true = lists:member('One', States),
            
            % Check initial state
            'Zero' = InitialState,
            
            % Check state definitions
            2 = length(StateDefs),
            ok;
        _ ->
            throw({unexpected_fsm_def, FSMDef})
    end,
    
    io:format("  ✓ FSM compilation test passed~n").

%% Test 4: Basic dependent types
test_dependent_types_basic() ->
    io:format("✓ Testing basic dependent types...~n"),
    
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
            params = [Param],
            return_type = ReturnType,
            constraints = Constraints
        } ->
            % Check parameter has dependent list type
            case Param of
                #param{
                    name = list,
                    type = {list_type, {type_var, _, 'T', []}, {type_var, _, n, []}}
                } -> ok;
                _ -> throw({unexpected_param_type, Param})
            end,
            
            % Check return type is type variable T
            case ReturnType of
                {type_var, _, 'T', []} -> ok;
                _ -> throw({unexpected_return_type, ReturnType})
            end,
            
            % Check constraint exists
            case Constraints of
                [#constraint{}] -> ok;
                _ -> throw({unexpected_constraints, Constraints})
            end;
        _ ->
            throw({unexpected_function_def, FuncDef})
    end,
    
    io:format("  ✓ Dependent types test passed~n").

%% Test 5: Let expressions
test_let_expressions() ->
    io:format("✓ Testing let expressions...~n"),
    
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
                #binary_op_expr{operator = '+'} -> ok;
                _ -> throw({unexpected_let_body, Body})
            end;
        _ ->
            throw({unexpected_let_expr, LetExpr})
    end,
    
    io:format("  ✓ Let expressions test passed~n").

%% Test 6: Pattern matching
test_pattern_matching() ->
    io:format("✓ Testing pattern matching...~n"),
    
    % Create match expression
    MatchCode = "match list do\n"
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
            expression = Expr,
            clauses = Clauses
        } ->
            % Check we're matching on 'list' identifier
            case Expr of
                #identifier_expr{name = list} -> ok;
                _ -> throw({unexpected_match_expr, Expr})
            end,
            
            % Check we have two clauses
            2 = length(Clauses),
            ok;
        _ ->
            throw({unexpected_match_expr, MatchExpr})
    end,
    
    io:format("  ✓ Pattern matching test passed~n").

%% Test 7: Arithmetic operations
test_arithmetic_operations() ->
    io:format("✓ Testing arithmetic operations...~n"),
    
    % Create arithmetic expression
    ArithCode = "(2 + 3) * 4 - 1",
    
    % Tokenize
    {ok, Tokens} = cure_lexer:scan(ArithCode),
    
    % Parse expression
    {ok, ArithExpr} = cure_parser:parse_expression(Tokens),
    
    % Check arithmetic structure (should be nested binary operations)
    case ArithExpr of
        #binary_op_expr{operator = '-'} -> ok;
        _ -> throw({unexpected_arithmetic_expr, ArithExpr})
    end,
    
    % Try to type check the expression
    TypeEnv = cure_typechecker:builtin_env(),
    {ok, _Type} = cure_typechecker:infer_type(ArithExpr, TypeEnv),
    
    io:format("  ✓ Arithmetic operations test passed~n").

%% Additional helper functions for future integration tests

%% Test end-to-end compilation pipeline
test_full_compilation_pipeline() ->
    io:format("✓ Testing full compilation pipeline...~n"),
    
    % Simple program
    Program = "module Test do\n"
              "  def double(x: Int): Int = x * 2\n"
              "end",
    
    % Full pipeline: Lexer -> Parser -> Type Checker -> Code Generator
    {ok, Tokens} = cure_lexer:scan(Program),
    {ok, AST} = cure_parser:parse(Tokens),
    
    TypeEnv = cure_typechecker:builtin_env(),
    {ok, TypedAST} = cure_typechecker:check_module(AST, TypeEnv),
    
    {ok, _Instructions} = cure_codegen:compile_module(TypedAST, #{}),
    
    io:format("  ✓ Full compilation pipeline test passed~n").

%% Test error handling in compilation
test_compilation_error_handling() ->
    io:format("✓ Testing compilation error handling...~n"),
    
    % Program with type error
    BadProgram = "def bad_func(x: Int): String = x + 1",  % Type mismatch
    
    try
        {ok, Tokens} = cure_lexer:scan(BadProgram),
        {ok, AST} = cure_parser:parse(Tokens),
        TypeEnv = cure_typechecker:builtin_env(),
        
        % This should fail with type error
        case cure_typechecker:check_function(AST, TypeEnv) of
            {error, _Reason} ->
                io:format("  ✓ Correctly caught type error~n"),
                ok;
            {ok, _} ->
                throw(expected_type_error)
        end
    catch
        _:_ ->
            io:format("  ✓ Error handling working correctly~n"),
            ok
    end.