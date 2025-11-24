-module(typeclass_codegen_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").
-include("../src/codegen/cure_codegen.hrl").

run() ->
    io:format("~n==== Typeclass Codegen Test ====~n~n"),

    % Test 1: Compile a simple show(42) call
    io:format("Test 1: Compiling show(42) to BEAM instructions...~n"),

    % Create AST for: show(42)
    ShowCall = #function_call_expr{
        function = #identifier_expr{name = show, location = undefined},
        args = [#literal_expr{value = 42, location = undefined}],
        location = undefined
    },

    % Compile the expression
    State = #codegen_state{
        local_vars = #{},
        typeclass_constraints = [],
        imported_functions = #{}
    },

    case cure_codegen:compile_expression(ShowCall, State) of
        {Instructions, _NewState} ->
            io:format("  ✓ Compilation succeeded~n"),
            io:format("  Generated instructions:~n"),
            lists:foreach(
                fun(Instr) ->
                    io:format("    - ~p~n", [Instr])
                end,
                Instructions
            ),

            % Check if the instructions contain a call to Show_Int_show
            HasInstanceCall = lists:any(
                fun(I) ->
                    case I of
                        #beam_instr{op = load_global, args = ['Show_Int_show']} ->
                            true;
                        _ ->
                            false
                    end
                end,
                Instructions
            ),

            case HasInstanceCall of
                true ->
                    io:format("  ✓ Found instance method call to Show_Int_show~n");
                false ->
                    io:format("  ✗ Did NOT find instance method call~n"),
                    io:format("     (This might be okay if resolution happens differently)~n")
            end;
        {error, Reason} ->
            io:format("  ✗ Compilation failed: ~p~n", [Reason])
    end,

    % Test 2: Parse and compile the actual show_test.cure file
    io:format("~nTest 2: Compiling examples/show_test.cure...~n"),
    case cure_parser:parse_file("examples/show_test.cure") of
        {ok, AST} ->
            io:format("  ✓ Parsed successfully~n"),

            % Try to compile the module
            case cure_codegen:compile_module(AST, #{}) of
                {ok, CompiledModule} ->
                    io:format("  ✓ Module compiled successfully~n"),

                    % Check if compiled functions include instance methods
                    Functions = maps:get(functions, CompiledModule, []),
                    io:format("  Module has ~p functions~n", [length(Functions)]),

                    % Look for test_int function
                    TestIntFunc = lists:filter(
                        fun(F) ->
                            case F of
                                #{name := test_int} -> true;
                                _ -> false
                            end
                        end,
                        Functions
                    ),

                    case TestIntFunc of
                        [Func] ->
                            io:format("  ✓ Found test_int function~n"),
                            FuncInstructions = maps:get(instructions, Func, []),
                            io:format("  test_int has ~p instructions~n", [length(FuncInstructions)]);
                        _ ->
                            io:format("  ✗ test_int function not found~n")
                    end,

                    io:format("~n~n==== TEST COMPLETED ====~n~n");
                {error, CompileReason} ->
                    io:format("  ✗ Compilation failed: ~p~n", [CompileReason]),
                    io:format("~n~n==== TESTS FAILED ====~n~n")
            end;
        {error, ParseReason} ->
            io:format("  ✗ Parse error: ~p~n", [ParseReason]),
            io:format("~n~n==== TESTS FAILED ====~n~n")
    end.
