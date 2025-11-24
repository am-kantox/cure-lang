-module(lambda_simple_test).
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
%% Lambda Expression Tests - Simple Test Suite
%% ============================================================================

%% Test: Basic lambda parsing in function
test_lambda_in_function() ->
    % Test lambda inside a function
    Code = <<"def f(): Int = let double = fn(x) -> x * 2 end 0">>,
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

    io:format("✓ Lambda in function test passed~n").

%% Test: Multi-parameter lambda
test_multi_param_lambda() ->
    % Test multi-param lambda in function argument
    Code = <<"def f(): Int = let add = fn(x, y) -> x + y end 0">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, [FuncDef]} = cure_parser:parse(Tokens),

    LetExpr = FuncDef#function_def.body,
    [Binding] = LetExpr#let_expr.bindings,
    Lambda = Binding#binding.value,

    % Verify lambda with 2 parameters
    ?assertMatch(#lambda_expr{}, Lambda),
    ?assertEqual(2, length(Lambda#lambda_expr.params)),

    [Param1, Param2] = Lambda#lambda_expr.params,
    ?assertEqual(x, Param1#param.name),
    ?assertEqual(y, Param2#param.name),

    io:format("✓ Multi-parameter lambda test passed~n").

%% Test: Nested lambda
test_nested_lambda() ->
    % Test nested lambda
    Code = <<"def f(): Int = let curried = fn(x) -> fn(y) -> x + y end end 0">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, [FuncDef]} = cure_parser:parse(Tokens),

    LetExpr = FuncDef#function_def.body,
    [Binding] = LetExpr#let_expr.bindings,
    OuterLambda = Binding#binding.value,

    % Verify outer lambda
    ?assertMatch(#lambda_expr{}, OuterLambda),
    ?assertEqual(1, length(OuterLambda#lambda_expr.params)),

    % Verify body is another lambda
    InnerLambda = OuterLambda#lambda_expr.body,
    ?assertMatch(#lambda_expr{}, InnerLambda),
    ?assertEqual(1, length(InnerLambda#lambda_expr.params)),

    io:format("✓ Nested lambda test passed~n").

%% Test: Lambda as higher-order function argument
test_lambda_as_argument() ->
    % Test lambda passed to map function
    Code = <<"def f(): Int = map([1, 2, 3], fn(x) -> x * 2 end)">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, [FuncDef]} = cure_parser:parse(Tokens),

    % Extract map call from function body
    MapCall = FuncDef#function_def.body,
    ?assertMatch(#function_call_expr{}, MapCall),

    % Verify has 2 arguments: list and lambda
    ?assertEqual(2, length(MapCall#function_call_expr.args)),
    [_ListArg, LambdaArg] = MapCall#function_call_expr.args,

    % Verify second argument is lambda
    ?assertMatch(#lambda_expr{}, LambdaArg),

    io:format("✓ Lambda as argument test passed~n").

%% Test: Lambda compilation
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

    io:format("✓ Lambda compilation test passed~n").

%% Test: Lambda closure compilation
test_lambda_closure() ->
    % Test compilation of: let x = 10 in fn(y) -> x + y end
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

    io:format("✓ Lambda closure test passed~n").

%% Helper functions
create_location(Line, Column) ->
    #location{line = Line, column = Column}.

%% ============================================================================
%% Test Suite Entry Point
%% ============================================================================

run() ->
    io:format("~n=== Lambda Expression Tests (Simple) ===~n"),
    test_lambda_in_function(),
    test_multi_param_lambda(),
    test_nested_lambda(),
    test_lambda_as_argument(),
    test_lambda_compilation(),
    test_lambda_closure(),
    io:format("~n✓ All lambda expression tests passed! (6/6)~n~n"),
    ok.
