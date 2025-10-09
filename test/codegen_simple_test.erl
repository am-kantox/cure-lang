%% Simplified Code Generation Tests - Compatible with actual codegen
-module(codegen_simple_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast_simple.hrl").

%% BEAM instruction record for testing
-record(beam_instr, {
    % Instruction opcode
    op,
    % Instruction arguments
    args = [],
    % Source location for debugging
    location
}).

%% Run all simplified code generation tests
run() ->
    io:format("Running Code Generation Simple tests...~n"),
    test_basic_expression_compilation(),
    test_simple_function_compilation(),
    test_basic_let_expressions(),
    io:format("All code generation simple tests passed!~n").

%% Test basic expression compilation
test_basic_expression_compilation() ->
    % Test literal compilation
    LiteralExpr = #literal_expr{value = 42, location = create_location(1, 1)},
    {Instructions, _State} = cure_codegen:compile_expression(LiteralExpr),

    ?assert(length(Instructions) > 0),
    [Instruction] = Instructions,
    ?assertEqual(load_literal, Instruction#beam_instr.op),
    ?assertEqual([42], Instruction#beam_instr.args),

    % Test binary operation compilation
    BinaryExpr = #binary_op_expr{
        op = '+',
        left = #literal_expr{value = 1, location = create_location(1, 1)},
        right = #literal_expr{value = 2, location = create_location(1, 1)},
        location = create_location(1, 1)
    },

    {BinaryInstructions, _BinaryState} = cure_codegen:compile_expression(BinaryExpr),
    % load_literal, load_literal, binary_op
    ?assert(length(BinaryInstructions) >= 3),

    io:format("✓ Basic expression compilation test passed~n").

%% Test simple function compilation
test_simple_function_compilation() ->
    % Create a simple function: def add(x, y) = x + y
    Function = #function_def{
        name = add,
        params = [
            #param{name = x, type = undefined, location = create_location(1, 1)},
            #param{name = y, type = undefined, location = create_location(1, 1)}
        ],
        return_type = undefined,
        constraint = undefined,
        body = #binary_op_expr{
            op = '+',
            left = #identifier_expr{name = x, location = create_location(1, 1)},
            right = #identifier_expr{name = y, location = create_location(1, 1)},
            location = create_location(1, 1)
        },
        location = create_location(1, 1)
    },

    % Compile function
    case cure_codegen:compile_function(Function) of
        {ok, {function, CompiledFunction}, _State} ->
            ?assertEqual(add, maps:get(name, CompiledFunction)),
            ?assertEqual(2, maps:get(arity, CompiledFunction)),
            ?assertEqual([x, y], maps:get(params, CompiledFunction)),

            Instructions = maps:get(instructions, CompiledFunction),
            ?assert(length(Instructions) > 0),

            io:format("✓ Simple function compilation test passed~n");
        {error, Reason} ->
            ?assert(false, {function_compilation_failed, Reason})
    end.

%% Test basic let expressions
test_basic_let_expressions() ->
    % Test: let x = 5 in x + 1
    LetExpr = #let_expr{
        bindings = [
            #binding{
                pattern = #identifier_pattern{name = x, location = create_location(1, 1)},
                value = #literal_expr{value = 5, location = create_location(1, 1)},
                location = create_location(1, 1)
            }
        ],
        body = #binary_op_expr{
            op = '+',
            left = #identifier_expr{name = x, location = create_location(1, 1)},
            right = #literal_expr{value = 1, location = create_location(1, 1)},
            location = create_location(1, 1)
        },
        location = create_location(1, 1)
    },

    % Compile the let expression
    {Instructions, _State} = cure_codegen:compile_expression(LetExpr),

    % Verify instructions are generated correctly
    ?assert(length(Instructions) > 0),

    % Check for proper variable binding instructions
    LoadInstructions = [I || I <- Instructions, I#beam_instr.op == load_literal],
    % Should load 5 and 1
    ?assert(length(LoadInstructions) >= 2),

    io:format("✓ Basic let expressions test passed~n").

%% Helper functions
create_location(Line, Column) ->
    #location{line = Line, column = Column, file = "test"}.
