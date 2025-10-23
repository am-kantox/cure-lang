%% Cure Programming Language - Advanced Parser Tests
%% Tests for FSM transitions with guards and unary operators
-module(parser_advanced_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").

%% Run all advanced parser tests
run() ->
    cure_utils:debug("Running Advanced Parser tests...~n"),
    test_fsm_transition_with_guard(),
    test_fsm_transition_without_guard(),
    test_fsm_complex_guard_expressions(),
    test_unary_minus_operator(),
    test_unary_plus_operator(),
    test_nested_unary_operators(),
    test_unary_operators_in_complex_expressions(),
    cure_utils:debug("All advanced parser tests passed!~n").

%% Test 1: Verify that FSM transitions with a "when" clause are correctly parsed
test_fsm_transition_with_guard() ->
    Code =
        <<
            "fsm TrafficLight do\n"
            "              states: [Red, Yellow, Green]\n"
            "              initial: Red\n"
            "              \n"
            "              state Red do\n"
            "                event(:timer_expired) when timer_value > 30 -> Yellow\n"
            "              end\n"
            "              \n"
            "              state Yellow do\n"
            "                event(:timer_expired) -> Green\n"
            "              end\n"
            "              \n"
            "              state Green do\n"
            "                event(:timer_expired) when traffic_detected -> Red\n"
            "              end\n"
            "            end"
        >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FSMDef] = AST,
    ?assertMatch(#fsm_def{name = 'TrafficLight'}, FSMDef),

    % Extract state definitions
    StateDefs = FSMDef#fsm_def.state_defs,
    ?assertEqual(3, length(StateDefs)),

    % Find Red state and check its transitions
    [RedState | _] = [S || S <- StateDefs, S#state_def.name =:= 'Red'],
    RedTransitions = RedState#state_def.transitions,
    ?assertEqual(1, length(RedTransitions)),

    [RedTransition] = RedTransitions,
    ?assertMatch(
        #transition{
            event = #literal_expr{value = timer_expired},
            target = 'Yellow'
        },
        RedTransition
    ),

    % Verify the guard expression is present and correctly parsed
    ?assertNotEqual(undefined, RedTransition#transition.guard),
    Guard = RedTransition#transition.guard,
    ?assertMatch(
        #binary_op_expr{
            op = '>',
            left = #identifier_expr{name = timer_value},
            right = #literal_expr{value = 30}
        },
        Guard
    ),

    % Find Green state and check its guard
    [GreenState | _] = [S || S <- StateDefs, S#state_def.name =:= 'Green'],
    GreenTransitions = GreenState#state_def.transitions,
    ?assertEqual(1, length(GreenTransitions)),

    [GreenTransition] = GreenTransitions,
    ?assertNotEqual(undefined, GreenTransition#transition.guard),
    GreenGuard = GreenTransition#transition.guard,
    ?assertMatch(#identifier_expr{name = traffic_detected}, GreenGuard),

    cure_utils:debug("✓ FSM transition with guard parsing test passed~n").

%% Test 2: Ensure that FSM transitions without a "when" clause continue to parse correctly
test_fsm_transition_without_guard() ->
    Code =
        <<
            "fsm SimpleCounter do\n"
            "              states: [Zero, Positive]\n"
            "              initial: Zero\n"
            "              \n"
            "              state Zero do\n"
            "                event(:increment) -> Positive\n"
            "                event(:decrement) -> Zero\n"
            "              end\n"
            "              \n"
            "              state Positive do\n"
            "                event(:reset) -> Zero\n"
            "                event(:increment) -> Positive\n"
            "              end\n"
            "            end"
        >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FSMDef] = AST,
    ?assertMatch(#fsm_def{name = 'SimpleCounter'}, FSMDef),

    % Extract state definitions
    StateDefs = FSMDef#fsm_def.state_defs,
    ?assertEqual(2, length(StateDefs)),

    % Check all transitions have no guard (undefined guard)
    AllTransitions = lists:flatten([S#state_def.transitions || S <- StateDefs]),
    ?assertEqual(4, length(AllTransitions)),

    % Verify all transitions have undefined guard
    lists:foreach(
        fun(Transition) ->
            ?assertEqual(undefined, Transition#transition.guard),
            ?assertMatch(
                #transition{
                    event = #literal_expr{value = _},
                    target = _
                },
                Transition
            )
        end,
        AllTransitions
    ),

    % Specifically check Zero state transitions
    [ZeroState | _] = [S || S <- StateDefs, S#state_def.name =:= 'Zero'],
    ZeroTransitions = ZeroState#state_def.transitions,
    ?assertEqual(2, length(ZeroTransitions)),

    [IncrTransition, DecrTransition] = ZeroTransitions,
    ?assertEqual(undefined, IncrTransition#transition.guard),
    ?assertEqual(undefined, DecrTransition#transition.guard),
    ?assertEqual('Positive', IncrTransition#transition.target),
    ?assertEqual('Zero', DecrTransition#transition.target),

    cure_utils:debug("✓ FSM transition without guard parsing test passed~n").

%% Test 3: Test complex guard expressions with supported operators
test_fsm_complex_guard_expressions() ->
    Code =
        <<
            "fsm ComplexFSM do\n"
            "              states: [A, B, C]\n"
            "              initial: A\n"
            "              \n"
            "              state A do\n"
            "                event(:complex_event) when x > 10 -> B\n"
            "                event(:another_event) when counter == 0 -> C\n"
            "                event(:third_event) when value <= threshold -> A\n"
            "              end\n"
            "            end"
        >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FSMDef] = AST,

    % Extract state A
    StateDefs = FSMDef#fsm_def.state_defs,
    [StateA | _] = [S || S <- StateDefs, S#state_def.name =:= 'A'],
    Transitions = StateA#state_def.transitions,
    ?assertEqual(3, length(Transitions)),

    % Check first transition with comparison guard
    [ComplexTransition, EqualTransition, LessEqualTransition] = Transitions,

    % Verify first guard structure: x > 10
    ?assertNotEqual(undefined, ComplexTransition#transition.guard),
    ComplexGuard = ComplexTransition#transition.guard,
    ?assertMatch(
        #binary_op_expr{
            op = '>',
            left = #identifier_expr{name = x},
            right = #literal_expr{value = 10}
        },
        ComplexGuard
    ),

    % Check second transition with equality guard
    ?assertNotEqual(undefined, EqualTransition#transition.guard),
    EqualGuard = EqualTransition#transition.guard,
    ?assertMatch(
        #binary_op_expr{
            op = '==',
            left = #identifier_expr{name = counter},
            right = #literal_expr{value = 0}
        },
        EqualGuard
    ),

    % Check third transition with less-equal guard
    ?assertNotEqual(undefined, LessEqualTransition#transition.guard),
    LessEqualGuard = LessEqualTransition#transition.guard,
    ?assertMatch(
        #binary_op_expr{
            op = '<=',
            left = #identifier_expr{name = value},
            right = #identifier_expr{name = threshold}
        },
        LessEqualGuard
    ),

    cure_utils:debug("✓ FSM complex guard expressions test passed~n").

%% Test 4: Validate correct parsing of expressions using unary minus operator
test_unary_minus_operator() ->
    Code = <<"def test_unary_minus() = -42">>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,
    ?assertMatch(#function_def{name = test_unary_minus}, FunctionDef),

    % Check that body is a unary operation
    Body = FunctionDef#function_def.body,
    ?assertMatch(
        #unary_op_expr{
            op = '-',
            operand = #literal_expr{value = 42}
        },
        Body
    ),

    % Test unary minus with identifier
    Code2 = <<"def test_unary_minus_var() = -x">>,
    {ok, Tokens2} = cure_lexer:tokenize(Code2),
    {ok, AST2} = cure_parser:parse(Tokens2),

    [FunctionDef2] = AST2,
    Body2 = FunctionDef2#function_def.body,
    ?assertMatch(
        #unary_op_expr{
            op = '-',
            operand = #identifier_expr{name = x}
        },
        Body2
    ),

    % Test unary minus in expression
    Code3 = <<"def test_unary_minus_expr() = -x + 5">>,
    {ok, Tokens3} = cure_lexer:tokenize(Code3),
    {ok, AST3} = cure_parser:parse(Tokens3),

    [FunctionDef3] = AST3,
    Body3 = FunctionDef3#function_def.body,
    ?assertMatch(
        #binary_op_expr{
            op = '+',
            left = #unary_op_expr{op = '-', operand = #identifier_expr{name = x}},
            right = #literal_expr{value = 5}
        },
        Body3
    ),

    cure_utils:debug("✓ Unary minus operator parsing test passed~n").

%% Test 5: Validate correct parsing of expressions using unary plus operator
test_unary_plus_operator() ->
    Code = <<"def test_unary_plus() = +42">>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,
    ?assertMatch(#function_def{name = test_unary_plus}, FunctionDef),

    % Check that body is a unary operation
    Body = FunctionDef#function_def.body,
    ?assertMatch(
        #unary_op_expr{
            op = '+',
            operand = #literal_expr{value = 42}
        },
        Body
    ),

    % Test unary plus with identifier
    Code2 = <<"def test_unary_plus_var() = +y">>,
    {ok, Tokens2} = cure_lexer:tokenize(Code2),
    {ok, AST2} = cure_parser:parse(Tokens2),

    [FunctionDef2] = AST2,
    Body2 = FunctionDef2#function_def.body,
    ?assertMatch(
        #unary_op_expr{
            op = '+',
            operand = #identifier_expr{name = y}
        },
        Body2
    ),

    % Test unary plus in expression
    Code3 = <<"def test_unary_plus_expr() = +y * 3">>,
    {ok, Tokens3} = cure_lexer:tokenize(Code3),
    {ok, AST3} = cure_parser:parse(Tokens3),

    [FunctionDef3] = AST3,
    Body3 = FunctionDef3#function_def.body,
    ?assertMatch(
        #binary_op_expr{
            op = '*',
            left = #unary_op_expr{op = '+', operand = #identifier_expr{name = y}},
            right = #literal_expr{value = 3}
        },
        Body3
    ),

    cure_utils:debug("✓ Unary plus operator parsing test passed~n").

%% Test 6: Test nested unary operators (with spaces to avoid -- token)
test_nested_unary_operators() ->
    % Space between operators
    Code = <<"def test_nested_unary() = - -x">>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,

    % Check nested unary operations: -(-x)
    Body = FunctionDef#function_def.body,
    ?assertMatch(
        #unary_op_expr{
            op = '-',
            operand = #unary_op_expr{
                op = '-',
                operand = #identifier_expr{name = x}
            }
        },
        Body
    ),

    % Test mixed unary operators: + -x should be +(-(x))

    % Space between operators
    Code2 = <<"def test_mixed_unary() = + -x">>,
    {ok, Tokens2} = cure_lexer:tokenize(Code2),
    {ok, AST2} = cure_parser:parse(Tokens2),

    [FunctionDef2] = AST2,
    Body2 = FunctionDef2#function_def.body,
    ?assertMatch(
        #unary_op_expr{
            op = '+',
            operand = #unary_op_expr{
                op = '-',
                operand = #identifier_expr{name = x}
            }
        },
        Body2
    ),

    % Test that -- is treated as a single token (not two unary minus)
    % This should fail to parse as an expression but succeed as a token
    {ok, TokensDoubleOp} = cure_lexer:tokenize(<<"--">>),
    ?assertEqual(1, length(TokensDoubleOp)),
    [DoubleOpToken] = TokensDoubleOp,
    ?assertEqual('--', DoubleOpToken#token.type),

    cure_utils:debug("✓ Nested unary operators test passed~n").

%% Test 7: Test unary operators in complex expressions
test_unary_operators_in_complex_expressions() ->
    % Test unary in function calls
    Code = <<"def test_unary_in_call() = Math.abs(-5)">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    [FunctionDef] = AST,
    Body = FunctionDef#function_def.body,
    ?assertMatch(
        #function_call_expr{
            function = #binary_op_expr{op = '.'},
            args = [#unary_op_expr{op = '-', operand = #literal_expr{value = 5}}]
        },
        Body
    ),

    % Test unary in FSM guard
    Code2 =
        <<
            "fsm TestFSM do\n"
            "               states: [A, B]\n"
            "               initial: A\n"
            "               \n"
            "               state A do\n"
            "                 event(:test) when -counter < 0 -> B\n"
            "               end\n"
            "             end"
        >>,
    {ok, Tokens2} = cure_lexer:tokenize(Code2),
    {ok, AST2} = cure_parser:parse(Tokens2),

    [FSMDef] = AST2,
    StateDefs = FSMDef#fsm_def.state_defs,
    [StateA] = [S || S <- StateDefs, S#state_def.name =:= 'A'],
    [Transition] = StateA#state_def.transitions,

    % Verify guard has unary expression
    Guard = Transition#transition.guard,
    ?assertMatch(
        #binary_op_expr{
            op = '<',
            left = #unary_op_expr{op = '-', operand = #identifier_expr{name = counter}},
            right = #literal_expr{value = 0}
        },
        Guard
    ),

    % Test unary in parentheses
    Code3 = <<"def test_unary_paren() = -(x + y)">>,
    {ok, Tokens3} = cure_lexer:tokenize(Code3),
    {ok, AST3} = cure_parser:parse(Tokens3),

    [FunctionDef3] = AST3,
    Body3 = FunctionDef3#function_def.body,
    ?assertMatch(
        #unary_op_expr{
            op = '-',
            operand = #binary_op_expr{
                op = '+',
                left = #identifier_expr{name = x},
                right = #identifier_expr{name = y}
            }
        },
        Body3
    ),

    cure_utils:debug("✓ Unary operators in complex expressions test passed~n").
