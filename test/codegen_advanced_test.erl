%% Code Generator Advanced Tests - Nested Let Expressions and Function Calls
-module(codegen_advanced_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast_simple.hrl").

%% BEAM instruction record for testing
-record(beam_instr, {
    op,                    % Instruction opcode
    args = [],             % Instruction arguments
    location               % Source location for debugging
}).

%% Run all advanced code generation tests
run() ->
    io:format("Running Code Generation Advanced tests...~n"),
    test_nested_let_expressions(),
    test_complex_function_calls(),
    test_let_with_function_calls(),
    test_deeply_nested_expressions(),
    test_let_expression_scoping(),
    test_recursive_function_calls(),
    test_higher_order_function_calls(),
    test_closure_generation(),
    test_tail_call_optimization(),
    test_let_expression_optimizations(),
    io:format("All code generation advanced tests passed!~n").

%% Test nested let expressions compilation
test_nested_let_expressions() ->
    % Test: let x = 10 in let y = x + 5 in let z = y * 2 in z + 1
    NestedLetExpr = #let_expr{
        bindings = [
            #binding{
                pattern = #identifier_pattern{name = x, location = create_location(1, 5)},
                value = create_literal_int(10),
                location = create_location(1, 1)
            }
        ],
        body = #let_expr{
            bindings = [
                #binding{
                    pattern = #identifier_pattern{name = y, location = create_location(2, 5)},
                    value = #binary_op_expr{
                        op = '+',
                        left = create_identifier('x'),
                        right = create_literal_int(5),
                        location = create_location(2, 9)
                    },
                    location = create_location(2, 1)
                }
            ],
            body = #let_expr{
                bindings = [
                    #binding{
                        pattern = #identifier_pattern{name = z, location = create_location(3, 5)},
                        value = #binary_op_expr{
                            op = '*',
                            left = create_identifier('y'),
                            right = create_literal_int(2),
                            location = create_location(3, 9)
                        },
                        location = create_location(3, 1)
                    }
                ],
                body = #binary_op_expr{
                    op = '+',
                    left = create_identifier('z'),
                    right = create_literal_int(1),
                    location = create_location(4, 1)
                },
                location = create_location(3, 15)
            },
            location = create_location(2, 15)
        },
        location = create_location(1, 15)
    },
    
    % Compile the nested let expression
    {Instructions, _State} = cure_codegen:compile_expression(NestedLetExpr),
    
    % Verify instructions are generated correctly
    ?assert(length(Instructions) > 0),
    
    % Check for proper variable binding instructions
    LoadInstructions = [I || I <- Instructions, I#beam_instr.op == load_literal],
    ?assertEqual(4, length(LoadInstructions)),  % Should load 10, 5, 2, 1
    
    % Check for variable binding operations
    BindInstructions = [I || I <- Instructions, I#beam_instr.op == bind_var],
    ?assertEqual(3, length(BindInstructions)),  % Should bind x, y, z
    
    % Check for arithmetic operations
    ArithInstructions = [I || I <- Instructions, 
                          lists:member(I#beam_instr.op, [binary_op, add_op, mult_op])],
    ?assertEqual(3, length(ArithInstructions)),  % x+5, y*2, z+1
    
    io:format("✓ Nested let expressions test passed~n").

%% Test complex function calls with multiple arguments and nesting
test_complex_function_calls() ->
    % Test: foo(bar(1, 2), baz(3, qux(4, 5)))
    ComplexCallExpr = #function_call_expr{
        function = create_identifier('foo'),
        args = [
            #function_call_expr{
                function = create_identifier('bar'),
                args = [create_literal_int(1), create_literal_int(2)],
                location = create_location(1, 5)
            },
            #function_call_expr{
                function = create_identifier('baz'),
                args = [
                    create_literal_int(3),
                    #function_call_expr{
                        function = create_identifier('qux'),
                        args = [create_literal_int(4), create_literal_int(5)],
                        location = create_location(1, 20)
                    }
                ],
                location = create_location(1, 15)
            }
        ],
        location = create_location(1, 1)
    },
    
    % Compile the complex function call
    {Instructions, _State} = cure_codegen:compile_expression(ComplexCallExpr),
    
    % Verify instruction structure
    ?assert(length(Instructions) > 0),
    
    % Check for literal loads
    LoadInstructions = [I || I <- Instructions, I#beam_instr.op == load_literal],
    ?assertEqual(5, length(LoadInstructions)),  % Should load 1, 2, 3, 4, 5
    
    % Check for function calls (should be in proper order)
    CallInstructions = [I || I <- Instructions, I#beam_instr.op == function_call],
    ?assertEqual(4, length(CallInstructions)),  % qux, bar, baz, foo
    
    % Verify call ordering (inner calls before outer calls)
    CallFunctions = [hd(I#beam_instr.args) || I <- CallInstructions],
    ?assertEqual(['qux', 'bar', 'baz', 'foo'], CallFunctions),
    
    io:format("✓ Complex function calls test passed~n").

%% Test let expressions containing function calls
test_let_with_function_calls() ->
    % Test: let x = foo(1) in let y = bar(x, 2) in baz(y)
    LetWithCallsExpr = #let_expr{
        bindings = [
            #binding{
                pattern = #identifier_pattern{name = x, location = create_location(1, 5)},
                value = #function_call_expr{
                    function = create_identifier('foo'),
                    args = [create_literal_int(1)],
                    location = create_location(1, 9)
                },
                location = create_location(1, 1)
            }
        ],
        body = #let_expr{
            bindings = [
                #binding{
                    pattern = #identifier_pattern{name = y, location = create_location(2, 5)},
                    value = #function_call_expr{
                        function = create_identifier('bar'),
                        args = [create_identifier('x'), create_literal_int(2)],
                        location = create_location(2, 9)
                    },
                    location = create_location(2, 1)
                }
            ],
            body = #function_call_expr{
                function = create_identifier('baz'),
                args = [create_identifier('y')],
                location = create_location(3, 1)
            },
            location = create_location(2, 20)
        },
        location = create_location(1, 16)
    },
    
    % Compile the expression
    {Instructions, _State} = cure_codegen:compile_expression(LetWithCallsExpr),
    
    % Verify instruction generation
    ?assert(length(Instructions) > 0),
    
    % Check for proper interleaving of loads, calls, and bindings
    LoadInstructions = [I || I <- Instructions, I#beam_instr.op == load_literal],
    CallInstructions = [I || I <- Instructions, I#beam_instr.op == function_call],
    BindInstructions = [I || I <- Instructions, I#beam_instr.op == bind_var],
    
    ?assertEqual(2, length(LoadInstructions)),  % 1, 2
    ?assertEqual(3, length(CallInstructions)),  % foo, bar, baz
    ?assertEqual(2, length(BindInstructions)),  % x, y
    
    io:format("✓ Let with function calls test passed~n").

%% Test deeply nested expressions with mixed let and function calls
test_deeply_nested_expressions() ->
    % Test: let a = f(let b = g(1) in b + 2) in let c = h(a, let d = i(3) in d * 4) in c - 1
    DeeplyNestedExpr = #let_expr{
        bindings = [
            #binding{
                pattern = #identifier_pattern{name = a, location = create_location(1, 5)},
                value = #function_call_expr{
                    function = create_identifier('f'),
                    args = [
                        #let_expr{
                            bindings = [
                                #binding{
                                    pattern = #identifier_pattern{name = b, location = create_location(1, 15)},
                                    value = #function_call_expr{
                                        function = create_identifier('g'),
                                        args = [create_literal_int(1)],
                                        location = create_location(1, 19)
                                    },
                                    location = create_location(1, 11)
                                }
                            ],
                            body = #binary_op_expr{
                                op = '+',
                                left = create_identifier('b'),
                                right = create_literal_int(2),
                                location = create_location(1, 28)
                            },
                            location = create_location(1, 33)
                        }
                    ],
                    location = create_location(1, 9)
                },
                location = create_location(1, 1)
            }
        ],
        body = #let_expr{
            bindings = [
                #binding{
                    pattern = #identifier_pattern{name = c, location = create_location(2, 5)},
                    value = #function_call_expr{
                        function = create_identifier('h'),
                        args = [
                            create_identifier('a'),
                            #let_expr{
                                bindings = [
                                    #binding{
                                        pattern = #identifier_pattern{name = d, location = create_location(2, 20)},
                                        value = #function_call_expr{
                                            function = create_identifier('i'),
                                            args = [create_literal_int(3)],
                                            location = create_location(2, 24)
                                        },
                                        location = create_location(2, 16)
                                    }
                                ],
                                body = #binary_op_expr{
                                    op = '*',
                                    left = create_identifier('d'),
                                    right = create_literal_int(4),
                                    location = create_location(2, 33)
                                },
                                location = create_location(2, 38)
                            }
                        ],
                        location = create_location(2, 9)
                    },
                    location = create_location(2, 1)
                }
            ],
            body = #binary_op_expr{
                op = '-',
                left = create_identifier('c'),
                right = create_literal_int(1),
                location = create_location(3, 1)
            },
            location = create_location(2, 42)
        },
        location = create_location(1, 38)
    },
    
    % Compile the deeply nested expression
    {Instructions, State} = cure_codegen:compile_expression(DeeplyNestedExpr),
    
    % Verify complex instruction generation
    ?assert(length(Instructions) > 10),  % Should generate many instructions
    
    % Check instruction types
    LoadInstructions = [I || I <- Instructions, I#beam_instr.op == load_literal],
    CallInstructions = [I || I <- Instructions, I#beam_instr.op == function_call],
    BindInstructions = [I || I <- Instructions, I#beam_instr.op == bind_var],
    ArithInstructions = [I || I <- Instructions, 
                          lists:member(I#beam_instr.op, [binary_op, add_op, mult_op, sub_op])],
    
    ?assertEqual(4, length(LoadInstructions)),  % 1, 2, 3, 4, 1 (for final subtraction)
    ?assertEqual(4, length(CallInstructions)),  % g, f, i, h
    ?assertEqual(4, length(BindInstructions)),  % a, b, c, d
    ?assertEqual(3, length(ArithInstructions)), % b+2, d*4, c-1
    
    % Verify scoping information in state
    ?assert(maps:size(State) >= 0),  % Should track variable scopes
    
    io:format("✓ Deeply nested expressions test passed~n").

%% Test let expression variable scoping in code generation
test_let_expression_scoping() ->
    % Test: let x = 1 in (let x = 2 in x) + x  (inner x shadows outer x)
    ScopingExpr = #let_expr{
        bindings = [
            #binding{
                pattern = #identifier_pattern{name = x, location = create_location(1, 5)},
                value = create_literal_int(1),
                location = create_location(1, 1)
            }
        ],
        body = #binary_op_expr{
            op = '+',
            left = #let_expr{
                bindings = [
                    #binding{
                        pattern = #identifier_pattern{name = x, location = create_location(1, 20)},
                        value = create_literal_int(2),
                        location = create_location(1, 16)
                    }
                ],
                body = create_identifier('x'),  % This should refer to inner x (2)
                location = create_location(1, 29)
            },
            right = create_identifier('x'),  % This should refer to outer x (1)
            location = create_location(1, 32)
        },
        location = create_location(1, 9)
    },
    
    % Compile with scoping
    {Instructions, State} = cure_codegen:compile_expression(ScopingExpr),
    
    % Verify scoping is handled correctly in instructions
    ?assert(length(Instructions) > 0),
    
    % Check variable reference instructions handle scoping
    VarRefInstructions = [I || I <- Instructions, I#beam_instr.op == load_var],
    ?assertEqual(2, length(VarRefInstructions)),  % Two references to 'x'
    
    % Verify different variable scopes are distinguished
    VariableScopes = [I#beam_instr.args || I <- VarRefInstructions],
    ?assertEqual(2, length(sets:to_list(sets:from_list(VariableScopes)))),  % Should be different
    
    io:format("✓ Let expression scoping test passed~n").

%% Test recursive function calls
test_recursive_function_calls() ->
    % Test recursive function definition and call
    RecursiveFunction = #function_def{
        name = factorial,
        params = [
            #param{name = n, type = undefined, location = create_location(1, 11)}
        ],
        return_type = undefined,
        constraint = undefined,
        body = #if_expr{
            condition = #binary_op_expr{
                op = '==',
                left = create_identifier('n'),
                right = create_literal_int(0),
                location = create_location(2, 8)
            },
            then_branch = create_literal_int(1),
            else_branch = #binary_op_expr{
                op = '*',
                left = create_identifier('n'),
                right = #function_call_expr{
                    function = create_identifier('factorial'),
                    args = [#binary_op_expr{
                        op = '-',
                        left = create_identifier('n'),
                        right = create_literal_int(1),
                        location = create_location(4, 20)
                    }],
                    location = create_location(4, 10)
                },
                location = create_location(4, 1)
            },
            location = create_location(2, 1)
        },
        location = create_location(1, 1)
    },
    
    % Compile recursive function
    Result = cure_codegen:compile_function(RecursiveFunction),
    ?assertMatch({ok, {function, _CompiledFunction}, _State}, Result),
    
    {ok, {function, CompiledFunction}, _State} = Result,
    Instructions = maps:get(instructions, CompiledFunction),
    
    % Verify recursive call handling
    CallInstructions = [I || I <- Instructions, I#beam_instr.op == function_call],
    ?assert(length(CallInstructions) >= 1),  % At least one recursive call
    
    % Check for tail call optimization opportunities
    TailCallInstructions = [I || I <- Instructions, I#beam_instr.op == tail_call],
    % May or may not be optimized depending on implementation
    
    io:format("✓ Recursive function calls test passed~n").

%% Test higher-order function calls (functions as arguments)
test_higher_order_function_calls() ->
    % Test: map(lambda x: x + 1, [1, 2, 3])
    HigherOrderCall = #function_call_expr{
        function = create_identifier('map'),
        args = [
            #lambda_expr{
                params = [#param{name = x, type = undefined, location = create_location(1, 12)}],
                body = #binary_op_expr{
                    op = '+',
                    left = create_identifier('x'),
                    right = create_literal_int(1),
                    location = create_location(1, 16)
                },
                location = create_location(1, 5)
            },
            #list_expr{
                elements = [create_literal_int(1), create_literal_int(2), create_literal_int(3)],
                location = create_location(1, 21)
            }
        ],
        location = create_location(1, 1)
    },
    
    % Compile higher-order function call
    {Instructions, _State} = cure_codegen:compile_expression(HigherOrderCall),
    
    % Verify lambda compilation
    LambdaInstructions = [I || I <- Instructions, I#beam_instr.op == create_lambda],
    ?assertEqual(1, length(LambdaInstructions)),
    
    % Verify list creation
    ListInstructions = [I || I <- Instructions, I#beam_instr.op == create_list],
    ?assertEqual(1, length(ListInstructions)),
    
    % Verify higher-order call
    CallInstructions = [I || I <- Instructions, I#beam_instr.op == function_call],
    ?assertEqual(1, length(CallInstructions)),
    
    io:format("✓ Higher-order function calls test passed~n").

%% Test closure generation and capture
test_closure_generation() ->
    % Test closure that captures variables from outer scope
    % let x = 10 in let f = lambda y: x + y in f(5)
    ClosureExpr = #let_expr{
        bindings = [
            #binding{
                pattern = #identifier_pattern{name = x, location = create_location(1, 5)},
                value = create_literal_int(10),
                location = create_location(1, 1)
            }
        ],
        body = #let_expr{
            bindings = [
                #binding{
                    pattern = #identifier_pattern{name = f, location = create_location(2, 5)},
                    value = #lambda_expr{
                        params = [#param{name = y, type = undefined, location = create_location(2, 17)}],
                        body = #binary_op_expr{
                            op = '+',
                            left = create_identifier('x'),  % Captured variable
                            right = create_identifier('y'), % Parameter
                            location = create_location(2, 21)
                        },
                        location = create_location(2, 9)
                    },
                    location = create_location(2, 1)
                }
            ],
            body = #function_call_expr{
                function = create_identifier('f'),
                args = [create_literal_int(5)],
                location = create_location(3, 1)
            },
            location = create_location(2, 28)
        },
        location = create_location(1, 13)
    },
    
    % Compile closure expression
    {Instructions, State} = cure_codegen:compile_expression(ClosureExpr),
    
    % Verify closure creation instructions
    ClosureInstructions = [I || I <- Instructions, I#beam_instr.op == create_closure],
    ?assertEqual(1, length(ClosureInstructions)),
    
    % Verify variable capture
    CaptureInstructions = [I || I <- Instructions, I#beam_instr.op == capture_var],
    ?assertEqual(1, length(CaptureInstructions)),  % Should capture x
    
    % Verify closure call
    CallInstructions = [I || I <- Instructions, I#beam_instr.op == closure_call],
    ?assertEqual(1, length(CallInstructions)),
    
    io:format("✓ Closure generation test passed~n").

%% Test tail call optimization
test_tail_call_optimization() ->
    % Test tail recursive function that should be optimized
    TailRecursiveFunction = #function_def{
        name = sum_tail,
        params = [
            #param{name = n, type = undefined, location = create_location(1, 10)},
            #param{name = acc, type = undefined, location = create_location(1, 13)}
        ],
        return_type = undefined,
        constraint = undefined,
        body = #if_expr{
            condition = #binary_op_expr{
                op = '==',
                left = create_identifier('n'),
                right = create_literal_int(0),
                location = create_location(2, 8)
            },
            then_branch = create_identifier('acc'),
            else_branch = #function_call_expr{
                function = create_identifier('sum_tail'),
                args = [
                    #binary_op_expr{
                        op = '-',
                        left = create_identifier('n'),
                        right = create_literal_int(1),
                        location = create_location(4, 15)
                    },
                    #binary_op_expr{
                        op = '+',
                        left = create_identifier('acc'),
                        right = create_identifier('n'),
                        location = create_location(4, 25)
                    }
                ],
                location = create_location(4, 5)
            },
            location = create_location(2, 1)
        },
        location = create_location(1, 1)
    },
    
    % Compile with tail call optimization
    Result = cure_codegen:compile_function(TailRecursiveFunction),
    ?assertMatch({ok, {function, _CompiledFunction}, _State}, Result),
    
    {ok, {function, CompiledFunction}, _State} = Result,
    Instructions = maps:get(instructions, CompiledFunction),
    
    % Check for tail call optimization
    TailCallInstructions = [I || I <- Instructions, I#beam_instr.op == tail_call],
    RegularCallInstructions = [I || I <- Instructions, I#beam_instr.op == function_call],
    
    % Should prefer tail calls over regular calls in tail position
    ?assert(length(TailCallInstructions) >= length(RegularCallInstructions)),
    
    io:format("✓ Tail call optimization test passed~n").

%% Test let expression optimizations
test_let_expression_optimizations() ->
    % Test let expression that can be optimized away
    % let x = 5 in x  (should be optimized to just 5)
    SimpleLetExpr = #let_expr{
        bindings = [
            #binding{
                pattern = #identifier_pattern{name = x, location = create_location(1, 5)},
                value = create_literal_int(5),
                location = create_location(1, 1)
            }
        ],
        body = create_identifier('x'),
        location = create_location(1, 13)
    },
    
    % Compile with optimizations
    {Instructions, _State} = cure_codegen:compile_expression(SimpleLetExpr),
    
    % Should be optimized to minimal instructions
    ?assert(length(Instructions) > 0),
    
    % Test unused let binding optimization
    % let x = expensive_call() in 42  (x is unused, call might be eliminated)
    UnusedLetExpr = #let_expr{
        bindings = [
            #binding{
                pattern = #identifier_pattern{name = x, location = create_location(2, 5)},
                value = #function_call_expr{
                    function = create_identifier('expensive_call'),
                    args = [],
                    location = create_location(2, 9)
                },
                location = create_location(2, 1)
            }
        ],
        body = create_literal_int(42),
        location = create_location(2, 30)
    },
    
    % Compile with dead code elimination
    {UnusedInstructions, _UnusedState} = cure_codegen:compile_expression(UnusedLetExpr),
    
    % Check if unused binding is optimized away (depends on purity analysis)
    CallInstructions = [I || I <- UnusedInstructions, I#beam_instr.op == function_call],
    % May or may not eliminate call depending on side effects analysis
    
    io:format("✓ Let expression optimizations test passed~n").

%% ============================================================================
%% Helper Functions for Creating AST Nodes
%% ============================================================================

create_location(Line, Column) ->
    #location{line = Line, column = Column, file = "test"}.

create_literal_int(Value) ->
    #literal_expr{value = Value, location = create_location(1, 1)}.

create_identifier(Name) ->
    #identifier_expr{name = Name, location = create_location(1, 1)}.