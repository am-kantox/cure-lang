%% Cure Programming Language - Guard Compilation Tests
%% Tests for guard compilation and execution
-module(guard_compilation_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").
-include("../src/codegen/cure_codegen.hrl").

%% Run all guard compilation tests
run() ->
    io:format("Running Guard Compilation tests...~n"),
    test_guard_safety_analysis(),
    test_simple_comparison_guards(),
    test_boolean_logic_guards(),
    test_type_guards(),
    test_arithmetic_guards(),
    test_nested_guard_expressions(),
    test_guard_optimization(),
    test_fsm_guard_compilation(),
    test_match_clause_guards(),
    test_guard_error_handling(),
    io:format("All guard compilation tests passed!~n").

%% Test 1: Guard safety analysis
test_guard_safety_analysis() ->
    % Safe guards
    SafeGuard1 = #binary_op_expr{
        op = '>',
        left = #identifier_expr{name = x, location = undefined},
        right = #literal_expr{value = 10, location = undefined},
        location = undefined
    },
    ?assert(cure_guard_compiler:is_guard_safe(SafeGuard1)),
    
    % Safe type guard
    SafeGuard2 = #function_call_expr{
        function = #identifier_expr{name = is_integer, location = undefined},
        args = [#identifier_expr{name = value, location = undefined}],
        location = undefined
    },
    ?assert(cure_guard_compiler:is_guard_safe(SafeGuard2)),
    
    % Unsafe guard (arbitrary function call)
    UnsafeGuard = #function_call_expr{
        function = #identifier_expr{name = some_function, location = undefined},
        args = [],
        location = undefined
    },
    ?assertNot(cure_guard_compiler:is_guard_safe(UnsafeGuard)),
    
    io:format("✓ Guard safety analysis test passed~n").

%% Test 2: Simple comparison guards
test_simple_comparison_guards() ->
    State = #codegen_state{local_vars = #{}},
    
    % Test x > 10
    Guard1 = #binary_op_expr{
        op = '>',
        left = #identifier_expr{name = x, location = undefined},
        right = #literal_expr{value = 10, location = undefined},
        location = undefined
    },
    
    {ok, Instructions1, _} = cure_guard_compiler:compile_guard(Guard1, State),
    ?assert(length(Instructions1) > 0),
    
    % Verify instruction structure
    ?assertMatch([
        #beam_instr{op = load_param, args = [x]},
        #beam_instr{op = load_literal, args = [10]},
        #beam_instr{op = guard_bif, args = ['>', 2]}
    ], Instructions1),
    
    % Test x == y
    Guard2 = #binary_op_expr{
        op = '==',
        left = #identifier_expr{name = x, location = undefined},
        right = #identifier_expr{name = y, location = undefined},
        location = undefined
    },
    
    {ok, Instructions2, _} = cure_guard_compiler:compile_guard(Guard2, State),
    ?assertMatch([
        #beam_instr{op = load_param, args = [x]},
        #beam_instr{op = load_param, args = [y]},
        #beam_instr{op = guard_bif, args = ['==', 2]}
    ], Instructions2),
    
    io:format("✓ Simple comparison guards test passed~n").

%% Test 3: Boolean logic guards
test_boolean_logic_guards() ->
    State = #codegen_state{local_vars = #{}},
    
    % Test x > 5 and y < 10
    Guard = #binary_op_expr{
        op = 'and',
        left = #binary_op_expr{
            op = '>',
            left = #identifier_expr{name = x, location = undefined},
            right = #literal_expr{value = 5, location = undefined},
            location = undefined
        },
        right = #binary_op_expr{
            op = '<',
            left = #identifier_expr{name = y, location = undefined},
            right = #literal_expr{value = 10, location = undefined},
            location = undefined
        },
        location = undefined
    },
    
    {ok, Instructions, _} = cure_guard_compiler:compile_guard(Guard, State),
    ?assert(length(Instructions) > 0),
    
    % Should contain all the necessary load and comparison instructions
    LoadInstructions = [I || I <- Instructions, I#beam_instr.op =:= load_param orelse I#beam_instr.op =:= load_literal],
    GuardBifInstructions = [I || I <- Instructions, I#beam_instr.op =:= guard_bif],
    
    ?assertEqual(4, length(LoadInstructions)), % x, 5, y, 10
    ?assertEqual(3, length(GuardBifInstructions)), % >, <, and
    
    io:format("✓ Boolean logic guards test passed~n").

%% Test 4: Type guards
test_type_guards() ->
    State = #codegen_state{local_vars = #{}},
    
    % Test is_integer(x)
    Guard = #function_call_expr{
        function = #identifier_expr{name = is_integer, location = undefined},
        args = [#identifier_expr{name = x, location = undefined}],
        location = undefined
    },
    
    {ok, Instructions, _} = cure_guard_compiler:compile_guard(Guard, State),
    ?assertMatch([
        #beam_instr{op = load_param, args = [x]},
        #beam_instr{op = guard_bif, args = [is_integer, 1]}
    ], Instructions),
    
    io:format("✓ Type guards test passed~n").

%% Test 5: Arithmetic guards
test_arithmetic_guards() ->
    State = #codegen_state{local_vars = #{}},
    
    % Test x + y > z
    Guard = #binary_op_expr{
        op = '>',
        left = #binary_op_expr{
            op = '+',
            left = #identifier_expr{name = x, location = undefined},
            right = #identifier_expr{name = y, location = undefined},
            location = undefined
        },
        right = #identifier_expr{name = z, location = undefined},
        location = undefined
    },
    
    {ok, Instructions, _} = cure_guard_compiler:compile_guard(Guard, State),
    ?assert(length(Instructions) > 0),
    
    % Should contain arithmetic operation followed by comparison
    GuardBifInstructions = [I || I <- Instructions, I#beam_instr.op =:= guard_bif],
    ?assertEqual(2, length(GuardBifInstructions)), % + and >
    
    io:format("✓ Arithmetic guards test passed~n").

%% Test 6: Nested guard expressions
test_nested_guard_expressions() ->
    State = #codegen_state{local_vars = #{}},
    
    % Test (x > 5 and y < 10) or z == 0
    Guard = #binary_op_expr{
        op = 'or',
        left = #binary_op_expr{
            op = 'and',
            left = #binary_op_expr{
                op = '>',
                left = #identifier_expr{name = x, location = undefined},
                right = #literal_expr{value = 5, location = undefined},
                location = undefined
            },
            right = #binary_op_expr{
                op = '<',
                left = #identifier_expr{name = y, location = undefined},
                right = #literal_expr{value = 10, location = undefined},
                location = undefined
            },
            location = undefined
        },
        right = #binary_op_expr{
            op = '==',
            left = #identifier_expr{name = z, location = undefined},
            right = #literal_expr{value = 0, location = undefined},
            location = undefined
        },
        location = undefined
    },
    
    {ok, Instructions, _} = cure_guard_compiler:compile_guard(Guard, State),
    ?assert(length(Instructions) > 0),
    
    % Should contain all necessary instructions
    GuardBifInstructions = [I || I <- Instructions, I#beam_instr.op =:= guard_bif],
    ?assertEqual(5, length(GuardBifInstructions)), % >, <, and, ==, or
    
    io:format("✓ Nested guard expressions test passed~n").

%% Test 7: Guard optimization
test_guard_optimization() ->
    % Test constant folding
    Guard1 = #binary_op_expr{
        op = '+',
        left = #literal_expr{value = 5, location = undefined},
        right = #literal_expr{value = 3, location = undefined},
        location = undefined
    },
    
    OptimizedGuard1 = cure_guard_compiler:optimize_guard(Guard1),
    ?assertMatch(#literal_expr{value = 8}, OptimizedGuard1),
    
    % Test boolean simplification
    Guard2 = #binary_op_expr{
        op = 'andalso',
        left = #literal_expr{value = true, location = undefined},
        right = #identifier_expr{name = x, location = undefined},
        location = undefined
    },
    
    OptimizedGuard2 = cure_guard_compiler:optimize_guard(Guard2),
    ?assertMatch(#identifier_expr{name = x}, OptimizedGuard2),
    
    io:format("✓ Guard optimization test passed~n").

%% Test 8: FSM guard compilation integration
test_fsm_guard_compilation() ->
    % Test FSM transition with guard
    Transition = #transition{
        event = #literal_expr{value = timeout, location = undefined},
        guard = #binary_op_expr{
            op = '>',
            left = #identifier_expr{name = count, location = undefined},
            right = #literal_expr{value = 0, location = undefined},
            location = undefined
        },
        target = 'NewState',
        action = undefined,
        location = undefined
    },
    
    % Test guard evaluation in FSM context
    _MockState = #{
        current_state => 'OldState',
        data => #{count => 5},
        event_data => undefined
    },
    
    % Compile guard
    State = #codegen_state{local_vars = #{}},
    {ok, GuardInstructions, _} = cure_guard_compiler:compile_guard(Transition#transition.guard, State),
    
    % Test guard instruction execution (simulated)
    ?assert(length(GuardInstructions) > 0),
    
    io:format("✓ FSM guard compilation integration test passed~n").

%% Test 9: Match clause guards
test_match_clause_guards() ->
    State = #codegen_state{local_vars = #{}},
    
    % Create match clause with guard
    MatchClause = #match_clause{
        pattern = #identifier_pattern{name = x, location = undefined},
        guard = #binary_op_expr{
            op = '>',
            left = #identifier_expr{name = x, location = undefined},
            right = #literal_expr{value = 0, location = undefined},
            location = undefined
        },
        body = #literal_expr{value = positive, location = undefined},
        location = undefined
    },
    
    {ok, Instructions, _} = cure_codegen:compile_match_pattern(MatchClause, undefined, State),
    ?assert(length(Instructions) > 0),
    
    % Should contain pattern matching and guard instructions
    GuardBifInstructions = [I || I <- Instructions, I#beam_instr.op =:= guard_bif],
    ?assertEqual(1, length(GuardBifInstructions)),
    
    io:format("✓ Match clause guards test passed~n").

%% Test 10: Guard error handling
test_guard_error_handling() ->
    State = #codegen_state{local_vars = #{}},
    
    % Test unsafe guard compilation
    UnsafeGuard = #function_call_expr{
        function = #identifier_expr{name = unsafe_function, location = undefined},
        args = [],
        location = undefined
    },
    
    Result = cure_guard_compiler:compile_guard(UnsafeGuard, State),
    ?assertMatch({error, {unsafe_guard, _}}, Result),
    
    % Test invalid guard operator
    InvalidGuard = #binary_op_expr{
        op = 'invalid_op',
        left = #identifier_expr{name = x, location = undefined},
        right = #literal_expr{value = 10, location = undefined},
        location = undefined
    },
    
    Result2 = cure_guard_compiler:compile_guard(InvalidGuard, State),
    ?assertMatch({error, {invalid_guard_op, invalid_op}}, Result2),
    
    io:format("✓ Guard error handling test passed~n").