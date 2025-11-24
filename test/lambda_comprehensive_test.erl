-module(lambda_comprehensive_test).
-author("Warp AI Assistant").

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").

%% BEAM instruction record for testing
-record(beam_instr, {
    % Instruction opcode
    op,
    % Instruction arguments
    args = [],
    % Source location for debugging
    location
}).

%% ============================================================================
%% Lambda Expression Tests - Comprehensive Test Suite
%% ============================================================================

%% Test: Basic lambda parsing
test_basic_lambda_parsing() ->
    % Test lambda inside a function: def f(): Int = let double = fn(x) -> x * 2 end in 0
    Code = <<"def f(): Int = let double = fn(x) -> x * 2 end in 0">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, [FuncDef]} = cure_parser:parse(Tokens),

    % Extract let expression from function body
    ?assertMatch(#function_def{}, FuncDef),
    LetExpr = FuncDef#function_def.body,
    ?assertMatch(#let_expr{}, LetExpr),

    % Extract lambda from binding
    [Binding] = LetExpr#let_expr.bindings,
    Lambda = Binding#binding.value,

    % Verify lambda structure
    ?assertMatch(#lambda_expr{}, Lambda),
    ?assertEqual(1, length(Lambda#lambda_expr.params)),
    [Param] = Lambda#lambda_expr.params,
    ?assertEqual(x, Param#param.name),

    % Verify body is binary operation
    Body = Lambda#lambda_expr.body,
    ?assertMatch(#binary_op_expr{op = '*'}, Body),

    cure_utils:debug("✓ Basic lambda parsing test passed~n").

%% Test: Multi-parameter lambda parsing
test_multi_param_lambda_parsing() ->
    % Test: fn(x, y) -> x + y end
    Code = <<"fn(x, y) -> x + y end">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, [Expr]} = cure_parser:parse(Tokens),

    % Verify lambda with 2 parameters
    ?assertMatch(#lambda_expr{}, Expr),
    Lambda = Expr,
    ?assertEqual(2, length(Lambda#lambda_expr.params)),

    [Param1, Param2] = Lambda#lambda_expr.params,
    ?assertEqual(x, Param1#param.name),
    ?assertEqual(y, Param2#param.name),

    cure_utils:debug("✓ Multi-parameter lambda parsing test passed~n").

%% Test: Nested lambda parsing
test_nested_lambda_parsing() ->
    % Test: fn(x) -> fn(y) -> x + y end end
    Code = <<"fn(x) -> fn(y) -> x + y end end">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, [Expr]} = cure_parser:parse(Tokens),

    % Verify outer lambda
    ?assertMatch(#lambda_expr{}, Expr),
    OuterLambda = Expr,
    ?assertEqual(1, length(OuterLambda#lambda_expr.params)),

    % Verify body is another lambda
    InnerLambda = OuterLambda#lambda_expr.body,
    ?assertMatch(#lambda_expr{}, InnerLambda),
    ?assertEqual(1, length(InnerLambda#lambda_expr.params)),

    cure_utils:debug("✓ Nested lambda parsing test passed~n").

%% Test: Lambda with complex body (match expression)
test_lambda_with_match_body() ->
    % Test: fn(x) -> match x do 0 -> true _ -> false end end
    Code = <<"fn(x) -> match x do 0 -> true _ -> false end end">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, [Expr]} = cure_parser:parse(Tokens),

    % Verify lambda
    ?assertMatch(#lambda_expr{}, Expr),
    Lambda = Expr,

    % Verify body is match expression
    Body = Lambda#lambda_expr.body,
    ?assertMatch(#match_expr{}, Body),

    % Verify match expression has 2 clauses
    MatchExpr = Body,
    ?assertEqual(2, length(MatchExpr#match_expr.patterns)),

    cure_utils:debug("✓ Lambda with match body test passed~n").

%% Test: Lambda compilation to BEAM instructions
test_lambda_compilation() ->
    % Create lambda AST: fn(x) -> x * 2 end
    Lambda = #lambda_expr{
        params = [#param{name = x, type = undefined, location = create_location(1, 4)}],
        body = #binary_op_expr{
            op = '*',
            left = #identifier_expr{name = x, location = create_location(1, 13)},
            right = #literal_expr{value = 2, location = create_location(1, 17)},
            location = create_location(1, 13)
        },
        location = create_location(1, 1)
    },

    % Compile lambda
    {Instructions, _State} = cure_codegen:compile_expression(Lambda),

    % Verify lambda instruction is generated
    ?assert(length(Instructions) > 0),

    % Check for make_lambda instruction
    LambdaInstructions = [I || I <- Instructions, I#beam_instr.op == make_lambda],
    ?assertEqual(1, length(LambdaInstructions)),

    % Verify lambda instruction structure
    [LambdaInstr] = LambdaInstructions,
    Args = LambdaInstr#beam_instr.args,
    % [Name, Params, Body, Arity]
    ?assertEqual(4, length(Args)),

    cure_utils:debug("✓ Lambda compilation test passed~n").

%% Test: Lambda in let binding
test_lambda_in_let_binding() ->
    % Test: let double = fn(x) -> x * 2 end in double
    Code = <<"let double = fn(x) -> x * 2 end in double">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, [Expr]} = cure_parser:parse(Tokens),

    % Verify let expression
    ?assertMatch(#let_expr{}, Expr),
    LetExpr = Expr,

    % Verify binding contains lambda
    [Binding] = LetExpr#let_expr.bindings,
    ?assertMatch(#lambda_expr{}, Binding#binding.value),

    cure_utils:debug("✓ Lambda in let binding test passed~n").

%% Test: Lambda as function argument (higher-order function)
test_lambda_as_function_argument() ->
    % Test: map([1, 2, 3], fn(x) -> x * 2 end)
    Code = <<"map([1, 2, 3], fn(x) -> x * 2 end)">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, [Expr]} = cure_parser:parse(Tokens),

    % Verify function call
    ?assertMatch(#function_call_expr{}, Expr),
    FuncCall = Expr,

    % Verify has 2 arguments: list and lambda
    ?assertEqual(2, length(FuncCall#function_call_expr.args)),
    [_ListArg, LambdaArg] = FuncCall#function_call_expr.args,

    % Verify second argument is lambda
    ?assertMatch(#lambda_expr{}, LambdaArg),

    cure_utils:debug("✓ Lambda as function argument test passed~n").

%% Test: Lambda closure - capturing variables
test_lambda_closure_compilation() ->
    % Test compilation of: let x = 10 in fn(y) -> x + y end
    % This tests variable capture from outer scope

    ClosureExpr = #let_expr{
        bindings = [
            #binding{
                pattern = #identifier_pattern{name = x, location = create_location(1, 5)},
                value = #literal_expr{value = 10, location = create_location(1, 9)},
                location = create_location(1, 1)
            }
        ],
        body = #lambda_expr{
            params = [#param{name = y, type = undefined, location = create_location(2, 7)}],
            body = #binary_op_expr{
                op = '+',
                left = #identifier_expr{name = x, location = create_location(2, 13)},
                right = #identifier_expr{name = y, location = create_location(2, 17)},
                location = create_location(2, 13)
            },
            location = create_location(2, 1)
        },
        location = create_location(1, 1)
    },

    % Compile closure expression
    {Instructions, _State} = cure_codegen:compile_expression(ClosureExpr),

    % Verify instructions are generated
    ?assert(length(Instructions) > 0),

    % Check for lambda instruction
    LambdaInstructions = [I || I <- Instructions, I#beam_instr.op == make_lambda],
    ?assertEqual(1, length(LambdaInstructions)),

    cure_utils:debug("✓ Lambda closure compilation test passed~n").

%% Test: Zero-parameter lambda (thunk)
test_zero_param_lambda() ->
    % Test: fn() -> 42 end
    Code = <<"fn() -> 42 end">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, [Expr]} = cure_parser:parse(Tokens),

    % Verify lambda with no parameters
    ?assertMatch(#lambda_expr{}, Expr),
    Lambda = Expr,
    ?assertEqual(0, length(Lambda#lambda_expr.params)),

    % Verify body is literal
    ?assertMatch(#literal_expr{value = 42}, Lambda#lambda_expr.body),

    cure_utils:debug("✓ Zero-parameter lambda test passed~n").

%% Test: Lambda type inference (if implemented)
test_lambda_type_inference() ->
    % This test verifies that lambdas can be type-checked
    % Even without explicit type annotations

    Lambda = #lambda_expr{
        params = [#param{name = x, type = undefined, location = create_location(1, 4)}],
        body = #binary_op_expr{
            op = '+',
            left = #identifier_expr{name = x, location = create_location(1, 13)},
            right = #literal_expr{value = 1, location = create_location(1, 17)},
            location = create_location(1, 13)
        },
        location = create_location(1, 1)
    },

    % Compilation should succeed even without explicit types
    Result = cure_codegen:compile_expression(Lambda),
    ?assertMatch({_Instructions, _State}, Result),

    cure_utils:debug("✓ Lambda type inference test passed~n").

%% Helper functions
create_location(Line, Column) ->
    #location{line = Line, column = Column}.

%% ============================================================================
%% Test Suite Entry Point
%% ============================================================================

run() ->
    cure_utils:debug("~n=== Lambda Expression Tests ===~n"),
    test_basic_lambda_parsing(),
    test_multi_param_lambda_parsing(),
    test_nested_lambda_parsing(),
    test_lambda_with_match_body(),
    test_lambda_compilation(),
    test_lambda_in_let_binding(),
    test_lambda_as_function_argument(),
    test_lambda_closure_compilation(),
    test_zero_param_lambda(),
    test_lambda_type_inference(),
    cure_utils:debug("~n✓ All lambda expression tests passed!~n~n"),
    ok.
