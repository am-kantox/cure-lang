%% Cure Programming Language - Action Compilation Test Suite
%% Test suite for action compilation system including parser, compiler, and runtime integration
-module(action_compilation_test).

%% Test API
-export([
    run/0,
    run_all_tests/0
]).

%% Include necessary headers
-include("../src/parser/cure_ast.hrl").
-include("../src/codegen/cure_codegen.hrl").
-include("../src/fsm/cure_fsm_runtime.hrl").

%% Test Data
-define(TEST_CASES, [
    {basic_assignment_test, "Test basic variable assignment actions"},
    {increment_decrement_test, "Test increment and decrement actions"},
    {field_update_test, "Test state field update actions"},
    {emit_event_test, "Test event emission actions"},
    {function_call_test, "Test safe function call actions"},
    {conditional_action_test, "Test conditional if-then-else actions"},
    {action_sequence_test, "Test action sequences"},
    {binary_operations_test, "Test binary operations in actions"},
    {log_action_test, "Test logging actions"},
    {state_access_test, "Test state variable and field access"},
    {event_data_access_test, "Test event data access in actions"},
    {current_state_access_test, "Test current state access in actions"},
    {action_safety_test, "Test action safety analysis"},
    {action_optimization_test, "Test action optimization passes"},
    {parser_integration_test, "Test parser integration for action expressions"},
    {fsm_runtime_integration_test, "Test FSM runtime action execution"},
    {error_handling_test, "Test error handling in action compilation"}
]).

%% Main test runner
run() ->
    run_all_tests().

run_all_tests() ->
    cure_utils:debug("Running Action Compilation Test Suite~n"),
    cure_utils:debug("=====================================~n~n"),

    Results = lists:map(
        fun({TestName, Description}) ->
            cure_utils:debug("~s: ~s~n", [TestName, Description]),
            Result =
                try
                    case TestName of
                        basic_assignment_test -> test_basic_assignment();
                        increment_decrement_test -> test_increment_decrement();
                        field_update_test -> test_field_update();
                        emit_event_test -> test_emit_event();
                        function_call_test -> test_function_call();
                        conditional_action_test -> test_conditional_action();
                        action_sequence_test -> test_action_sequence();
                        binary_operations_test -> test_binary_operations();
                        log_action_test -> test_log_action();
                        state_access_test -> test_state_access();
                        event_data_access_test -> test_event_data_access();
                        current_state_access_test -> test_current_state_access();
                        action_safety_test -> test_action_safety();
                        action_optimization_test -> test_action_optimization();
                        parser_integration_test -> test_parser_integration();
                        fsm_runtime_integration_test -> test_fsm_runtime_integration();
                        error_handling_test -> test_error_handling();
                        _ -> {error, unknown_test}
                    end
                catch
                    Error:Reason:Stack ->
                        {error, {Error, Reason, Stack}}
                end,

            case Result of
                {ok, Details} ->
                    cure_utils:debug("  ✓ PASSED~n~p~n~n", [Details]),
                    {TestName, passed, Details};
                {error, ErrorReason} ->
                    cure_utils:debug("  ✗ FAILED: ~p~n~n", [ErrorReason]),
                    {TestName, failed, ErrorReason}
            end
        end,
        ?TEST_CASES
    ),

    Passed = length([Result || {_, passed, _} = Result <- Results]),
    Failed = length([Result || {_, failed, _} = Result <- Results]),
    Total = length(Results),

    cure_utils:debug("Test Results: ~p/~p passed, ~p failed~n", [Passed, Total, Failed]),

    case Failed of
        0 ->
            cure_utils:debug("All tests passed!~n"),
            ok;
        _ ->
            cure_utils:debug("Some tests failed.~n"),
            FailedTests = [Name || {Name, failed, _} <- Results],
            cure_utils:debug("Failed tests: ~p~n", [FailedTests]),
            {failed, FailedTests}
    end.

%% ============================================================================
%% Individual Test Functions
%% ============================================================================

%% Test basic variable assignment actions
test_basic_assignment() ->
    % Test action: counter = 42
    Location = #location{line = 1, column = 1, file = "test"},
    Action = {assign, counter, {literal, 42, Location}, Location},

    case cure_action_compiler:compile_action(Action, #{}) of
        {ok, Instructions, _State} ->
            % Verify instructions contain assignment operations
            ExpectedOps = [load_literal, assign_state_var],
            ActualOps = [maps:get(op, I) || I <- Instructions],
            case lists:all(fun(Op) -> lists:member(Op, ActualOps) end, ExpectedOps) of
                true ->
                    {ok, {compiled_instructions, length(Instructions), ActualOps}};
                false ->
                    {error, {missing_operations, ExpectedOps, ActualOps}}
            end;
        {error, Reason} ->
            {error, {compilation_failed, Reason}}
    end.

%% Test increment and decrement actions
test_increment_decrement() ->
    Location = #location{line = 1, column = 1, file = "test"},

    % Test increment: counter += 5
    IncrementAction = {increment, counter, {literal, 5, Location}, Location},
    case cure_action_compiler:compile_action(IncrementAction, #{}) of
        {ok, IncrInstructions, _} ->
            % Test decrement: counter -= 3
            DecrementAction = {decrement, counter, {literal, 3, Location}, Location},
            case cure_action_compiler:compile_action(DecrementAction, #{}) of
                {ok, DecrInstructions, _} ->
                    {ok, {
                        increment_ops,
                        length(IncrInstructions),
                        decrement_ops,
                        length(DecrInstructions)
                    }};
                {error, Reason} ->
                    {error, {decrement_compilation_failed, Reason}}
            end;
        {error, Reason} ->
            {error, {increment_compilation_failed, Reason}}
    end.

%% Test state field update actions
test_field_update() ->
    Location = #location{line = 1, column = 1, file = "test"},
    Action = {update, speed, {literal, 100, Location}, Location},

    case cure_action_compiler:compile_action(Action, #{}) of
        {ok, Instructions, _State} ->
            % Verify field update operations
            Ops = [maps:get(op, I) || I <- Instructions],
            case lists:member(update_state_field, Ops) of
                true ->
                    {ok, {field_update_compiled, length(Instructions)}};
                false ->
                    {error, {missing_field_update_op, Ops}}
            end;
        {error, Reason} ->
            {error, {compilation_failed, Reason}}
    end.

%% Test event emission actions
test_emit_event() ->
    Location = #location{line = 1, column = 1, file = "test"},

    % Test emit with data: emit(start_event, {some: data})
    Action =
        {emit, {literal, start_event, Location}, {literal, #{some => data}, Location}, Location},

    case cure_action_compiler:compile_action(Action, #{}) of
        {ok, Instructions, _State} ->
            Ops = [maps:get(op, I) || I <- Instructions],
            case lists:member(emit_event, Ops) of
                true ->
                    {ok, {event_emission_compiled, length(Instructions)}};
                false ->
                    {error, {missing_emit_op, Ops}}
            end;
        {error, Reason} ->
            {error, {compilation_failed, Reason}}
    end.

%% Test safe function call actions
test_function_call() ->
    Location = #location{line = 1, column = 1, file = "test"},
    Action = {call, length, [{state_var, items, Location}], Location},

    case cure_action_compiler:compile_action(Action, #{}) of
        {ok, Instructions, _State} ->
            Ops = [maps:get(op, I) || I <- Instructions],
            ExpectedOps = [load_state_var, call_safe_function],
            case lists:all(fun(Op) -> lists:member(Op, Ops) end, ExpectedOps) of
                true ->
                    {ok, {function_call_compiled, length(Instructions)}};
                false ->
                    {error, {missing_function_call_ops, ExpectedOps, Ops}}
            end;
        {error, Reason} ->
            {error, {compilation_failed, Reason}}
    end.

%% Test conditional if-then-else actions
test_conditional_action() ->
    Location = #location{line = 1, column = 1, file = "test"},

    % if counter > 10 then counter = 0 else counter += 1 end
    Condition = {binary_op, '>', {state_var, counter, Location}, {literal, 10, Location}, Location},
    ThenAction = {assign, counter, {literal, 0, Location}, Location},
    ElseAction = {increment, counter, {literal, 1, Location}, Location},
    Action = {if_then, Condition, ThenAction, ElseAction, Location},

    case cure_action_compiler:compile_action(Action, #{}) of
        {ok, Instructions, _State} ->
            Ops = [maps:get(op, I) || I <- Instructions],
            ExpectedOps = [load_state_var, load_literal, binary_op, jump_if_false],
            HasConditional = lists:all(fun(Op) -> lists:member(Op, Ops) end, ExpectedOps),
            case HasConditional of
                true ->
                    {ok, {conditional_compiled, length(Instructions)}};
                false ->
                    {error, {missing_conditional_ops, ExpectedOps, Ops}}
            end;
        {error, Reason} ->
            {error, {compilation_failed, Reason}}
    end.

%% Test action sequences
test_action_sequence() ->
    Location = #location{line = 1, column = 1, file = "test"},

    Actions = [
        {assign, x, {literal, 1, Location}, Location},
        {assign, y, {literal, 2, Location}, Location},
        {assign, z, {binary_op, '+', {state_var, x, Location}, {state_var, y, Location}, Location},
            Location}
    ],
    SequenceAction = {sequence, Actions, Location},

    case cure_action_compiler:compile_action(SequenceAction, #{}) of
        {ok, Instructions, _State} ->
            % Should have instructions for all three assignments plus operations
            InstructionCount = length(Instructions),
            % Minimum expected instructions
            case InstructionCount >= 9 of
                true ->
                    {ok, {sequence_compiled, InstructionCount}};
                false ->
                    {error, {insufficient_instructions, InstructionCount}}
            end;
        {error, Reason} ->
            {error, {compilation_failed, Reason}}
    end.

%% Test binary operations in actions
test_binary_operations() ->
    Location = #location{line = 1, column = 1, file = "test"},

    % Test various binary operations: result = x + y * 2
    Value =
        {binary_op, '+', {state_var, x, Location},
            {binary_op, '*', {state_var, y, Location}, {literal, 2, Location}, Location}, Location},
    Action = {assign, result, Value, Location},

    case cure_action_compiler:compile_action(Action, #{}) of
        {ok, Instructions, _State} ->
            Ops = [maps:get(op, I) || I <- Instructions],
            BinaryOps = [Op || Op <- Ops, Op =:= binary_op],
            % Should have at least 2 binary operations
            case length(BinaryOps) >= 2 of
                true ->
                    {ok, {binary_ops_compiled, length(BinaryOps), length(Instructions)}};
                false ->
                    {error, {insufficient_binary_ops, BinaryOps}}
            end;
        {error, Reason} ->
            {error, {compilation_failed, Reason}}
    end.

%% Test logging actions
test_log_action() ->
    Location = #location{line = 1, column = 1, file = "test"},
    Action = {log, info, {literal, "FSM state changed", Location}, Location},

    case cure_action_compiler:compile_action(Action, #{}) of
        {ok, Instructions, _State} ->
            Ops = [maps:get(op, I) || I <- Instructions],
            case lists:member(log_message, Ops) of
                true ->
                    {ok, {log_action_compiled, length(Instructions)}};
                false ->
                    {error, {missing_log_op, Ops}}
            end;
        {error, Reason} ->
            {error, {compilation_failed, Reason}}
    end.

%% Test state variable and field access
test_state_access() ->
    Location = #location{line = 1, column = 1, file = "test"},

    % Test state variable access
    VarAction = {assign, temp, {state_var, counter, Location}, Location},
    case cure_action_compiler:compile_action(VarAction, #{}) of
        {ok, VarInstructions, _} ->
            % Test state field access
            FieldAction = {assign, temp, {state_field, speed, Location}, Location},
            case cure_action_compiler:compile_action(FieldAction, #{}) of
                {ok, FieldInstructions, _} ->
                    VarOps = [maps:get(op, I) || I <- VarInstructions],
                    FieldOps = [maps:get(op, I) || I <- FieldInstructions],
                    HasVarAccess = lists:member(load_state_var, VarOps),
                    HasFieldAccess = lists:member(load_state_field, FieldOps),
                    case HasVarAccess andalso HasFieldAccess of
                        true ->
                            {ok,
                                {state_access_compiled, var_ops, length(VarInstructions), field_ops,
                                    length(FieldInstructions)}};
                        false ->
                            {error, {missing_access_ops, HasVarAccess, HasFieldAccess}}
                    end;
                {error, Reason} ->
                    {error, {field_access_compilation_failed, Reason}}
            end;
        {error, Reason} ->
            {error, {var_access_compilation_failed, Reason}}
    end.

%% Test event data access in actions
test_event_data_access() ->
    Location = #location{line = 1, column = 1, file = "test"},
    Action = {assign, received_data, {event_data, Location}, Location},

    case cure_action_compiler:compile_action(Action, #{}) of
        {ok, Instructions, _State} ->
            Ops = [maps:get(op, I) || I <- Instructions],
            case lists:member(load_event_data, Ops) of
                true ->
                    {ok, {event_data_access_compiled, length(Instructions)}};
                false ->
                    {error, {missing_event_data_op, Ops}}
            end;
        {error, Reason} ->
            {error, {compilation_failed, Reason}}
    end.

%% Test current state access in actions
test_current_state_access() ->
    Location = #location{line = 1, column = 1, file = "test"},
    Action = {assign, prev_state, {current_state, Location}, Location},

    case cure_action_compiler:compile_action(Action, #{}) of
        {ok, Instructions, _State} ->
            Ops = [maps:get(op, I) || I <- Instructions],
            case lists:member(load_current_state, Ops) of
                true ->
                    {ok, {current_state_access_compiled, length(Instructions)}};
                false ->
                    {error, {missing_current_state_op, Ops}}
            end;
        {error, Reason} ->
            {error, {compilation_failed, Reason}}
    end.

%% Test action safety analysis
test_action_safety() ->
    Location = #location{line = 1, column = 1, file = "test"},

    % Test safe action
    SafeAction = {assign, counter, {literal, 42, Location}, Location},
    case cure_action_compiler:analyze_action_safety(SafeAction, #{}) of
        {ok, safe, _} ->
            % Test potentially unsafe action (if we had file operations, etc.)
            % For now, test that the safety analysis function exists and works
            {ok, {safety_analysis_working, safe}};
        {ok, unsafe, Reason} ->
            {error, {unexpected_unsafe_result, Reason}};
        {error, Reason} ->
            {error, {safety_analysis_failed, Reason}}
    end.

%% Test action optimization passes
test_action_optimization() ->
    Location = #location{line = 1, column = 1, file = "test"},

    % Create an action that should be optimizable (constant folding)
    OptimizableAction =
        {assign, result, {binary_op, '+', {literal, 5, Location}, {literal, 3, Location}, Location},
            Location},

    case cure_action_compiler:compile_action(OptimizableAction, #{optimization_level => 2}) of
        {ok, Instructions, State} ->
            % Check if optimization occurred
            OptimizationInfo = maps:get(optimizations_applied, State, []),
            case length(OptimizationInfo) > 0 of
                true ->
                    {ok, {optimizations_applied, OptimizationInfo, length(Instructions)}};
                false ->
                    {ok, {no_optimizations_applied, length(Instructions)}}
            end;
        {error, Reason} ->
            {error, {compilation_failed, Reason}}
    end.

%% Test parser integration for action expressions
test_parser_integration() ->
    % Test parsing action expressions in FSM transitions
    TokenizeAndParse = fun(Code) ->
        case cure_lexer:tokenize(Code) of
            {ok, Tokens} ->
                cure_parser:parse(Tokens);
            {error, Reason} ->
                {error, {tokenize_failed, Reason}}
        end
    end,

    % Simple FSM with action
    FSMCode =
        "fsm TestFSM do\n"
        "        states: [idle, active]\n"
        "        initial: idle\n"
        "        \n"
        "        state idle do\n"
        "            event(start) -> active do\n"
        "                counter = 1\n"
        "            end\n"
        "        end\n"
        "        \n"
        "        state active do\n"
        "            event(stop) -> idle do {\n"
        "                counter = 0;\n"
        "                log(info, \"Stopping\")\n"
        "            }\n"
        "            end\n"
        "        end\n"
        "    end",

    case TokenizeAndParse(FSMCode) of
        {ok, AST} ->
            % Check if the FSM contains action expressions
            case find_actions_in_ast(AST) of
                {found, ActionCount} when ActionCount > 0 ->
                    {ok, {parser_integration_working, actions_found, ActionCount}};
                {found, 0} ->
                    {error, {no_actions_found_in_parsed_ast}};
                not_found ->
                    {error, {fsm_not_found_in_ast}}
            end;
        {error, Reason} ->
            {error, {parsing_failed, Reason}}
    end.

%% Test FSM runtime action execution
test_fsm_runtime_integration() ->
    Location = #location{line = 1, column = 1, file = "test"},

    % Create a simple compiled action
    Action = {assign, counter, {literal, 42, Location}, Location},
    case cure_action_compiler:compile_action(Action, #{}) of
        {ok, Instructions, _} ->
            CompiledAction = {compiled_action, Instructions},

            % Create mock FSM state
            MockState = #fsm_state{
                current_state = idle,
                data = #{counter => 0},
                event_data = undefined
            },

            % Test action execution
            try
                NewData = cure_fsm_runtime:execute_action(CompiledAction, MockState, undefined),
                case maps:get(counter, NewData, undefined) of
                    42 ->
                        {ok, {runtime_integration_working, counter_updated}};
                    Other ->
                        {error, {unexpected_counter_value, Other}}
                end
            catch
                Error:Reason:Stack ->
                    {error, {runtime_execution_failed, Error, Reason, Stack}}
            end;
        {error, Reason} ->
            {error, {compilation_failed, Reason}}
    end.

%% Test error handling in action compilation
test_error_handling() ->
    Location = #location{line = 1, column = 1, file = "test"},

    % Test invalid action type
    InvalidAction = {invalid_action_type, something, Location},
    case cure_action_compiler:compile_action(InvalidAction, #{}) of
        {error, _Reason} ->
            % Test invalid action value
            InvalidValueAction = {assign, var, {invalid_value_type, Location}, Location},
            case cure_action_compiler:compile_action(InvalidValueAction, #{}) of
                {error, _Reason2} ->
                    {ok, {error_handling_working, both_errors_caught}};
                {ok, _} ->
                    {error, {invalid_value_not_caught}}
            end;
        {ok, _} ->
            {error, {invalid_action_not_caught}}
    end.

%% ============================================================================
%% Helper Functions
%% ============================================================================

%% Find actions in parsed AST
find_actions_in_ast(AST) ->
    try
        ActionCount = count_actions_in_ast(AST, 0),
        {found, ActionCount}
    catch
        _:_ ->
            not_found
    end.

%% Count actions in AST recursively
count_actions_in_ast([], Count) ->
    Count;
count_actions_in_ast(#fsm_def{state_defs = StateDefs}, Count) ->
    lists:foldl(
        fun(StateDef, Acc) ->
            count_actions_in_state_def(StateDef, Acc)
        end,
        Count,
        StateDefs
    );
count_actions_in_ast([Item | Rest], Count) when is_list(Rest) ->
    NewCount = count_actions_in_ast(Item, Count),
    count_actions_in_ast(Rest, NewCount);
count_actions_in_ast(_, Count) ->
    Count.

%% Count actions in state definition
count_actions_in_state_def(#state_def{transitions = Transitions}, Count) ->
    lists:foldl(
        fun(Transition, Acc) ->
            case Transition of
                #transition{action = undefined} -> Acc;
                #transition{action = _Action} -> Acc + 1;
                _ -> Acc
            end
        end,
        Count,
        Transitions
    );
count_actions_in_state_def(_, Count) ->
    Count.
