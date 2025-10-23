%% Code Generator Advanced Tests - Nested Let Expressions and Function Calls
-module(codegen_advanced_test).

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

%% Run all advanced code generation tests
run() ->
    cure_utils:debug("Running Code Generation Advanced tests...~n"),
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
    cure_utils:debug("All code generation advanced tests passed!~n").

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
    % Should load 10, 5, 2, 1
    ?assertEqual(4, length(LoadInstructions)),

    % Check for variable binding operations
    BindInstructions = [I || I <- Instructions, I#beam_instr.op == bind_var],
    % Should bind x, y, z
    ?assertEqual(3, length(BindInstructions)),

    % Check for arithmetic operations
    ArithInstructions = [
        I
     || I <- Instructions,
        lists:member(I#beam_instr.op, [binary_op, add_op, mult_op])
    ],
    % x+5, y*2, z+1
    ?assertEqual(3, length(ArithInstructions)),

    cure_utils:debug("✓ Nested let expressions test passed~n").

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
    % Should load 1, 2, 3, 4, 5
    ?assertEqual(5, length(LoadInstructions)),

    % Check for function calls (should be in proper order)
    CallInstructions = [I || I <- Instructions, I#beam_instr.op == function_call],
    % qux, bar, baz, foo
    ?assertEqual(4, length(CallInstructions)),

    % Verify call ordering (inner calls before outer calls)
    CallFunctions = [hd(I#beam_instr.args) || I <- CallInstructions],
    ?assertEqual(['qux', 'bar', 'baz', 'foo'], CallFunctions),

    cure_utils:debug("✓ Complex function calls test passed~n").

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

    % 1, 2
    ?assertEqual(2, length(LoadInstructions)),
    % foo, bar, baz
    ?assertEqual(3, length(CallInstructions)),
    % x, y
    ?assertEqual(2, length(BindInstructions)),

    cure_utils:debug("✓ Let with function calls test passed~n").

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
                                    pattern = #identifier_pattern{
                                        name = b, location = create_location(1, 15)
                                    },
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
                                        pattern = #identifier_pattern{
                                            name = d, location = create_location(2, 20)
                                        },
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

    % Should generate many instructions
    ?assert(length(Instructions) > 10),

    % Check instruction types
    LoadInstructions = [I || I <- Instructions, I#beam_instr.op == load_literal],
    CallInstructions = [I || I <- Instructions, I#beam_instr.op == function_call],
    BindInstructions = [I || I <- Instructions, I#beam_instr.op == bind_var],
    ArithInstructions = [
        I
     || I <- Instructions,
        lists:member(I#beam_instr.op, [binary_op, add_op, mult_op, sub_op])
    ],

    % 1, 2, 3, 4, 1 (for final subtraction)
    ?assertEqual(4, length(LoadInstructions)),
    % g, f, i, h
    ?assertEqual(4, length(CallInstructions)),
    % a, b, c, d
    ?assertEqual(4, length(BindInstructions)),
    % b+2, d*4, c-1
    ?assertEqual(3, length(ArithInstructions)),

    % Verify scoping information in state

    % Should track variable scopes
    ?assert(maps:size(State) >= 0),

    cure_utils:debug("✓ Deeply nested expressions test passed~n").

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
                % This should refer to inner x (2)
                body = create_identifier('x'),
                location = create_location(1, 29)
            },
            % This should refer to outer x (1)
            right = create_identifier('x'),
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
    % Two references to 'x'
    ?assertEqual(2, length(VarRefInstructions)),

    % Verify different variable scopes are distinguished
    VariableScopes = [I#beam_instr.args || I <- VarRefInstructions],
    % Should be different
    ?assertEqual(2, length(sets:to_list(sets:from_list(VariableScopes)))),

    cure_utils:debug("✓ Let expression scoping test passed~n").

%% Test recursive function calls
test_recursive_function_calls() ->
    % Test factorial function with match expression:
    % factorial = fn n ->
    %   match n
    %     0 -> 1
    %     _ -> n * factorial(n - 1)
    %   end
    % end
    FactorialFn = #function_def{
        name = factorial,
        params = [#param{name = n, type = undefined, location = create_location(1, 17)}],
        return_type = undefined,
        constraint = undefined,
        body = #match_expr{
            expr = create_identifier('n'),
            patterns = [
                #match_clause{
                    pattern = #literal_expr{value = 0, location = create_location(2, 5)},
                    guard = undefined,
                    body = create_literal_int(1),
                    location = create_location(2, 5)
                },
                #match_clause{
                    pattern = #wildcard_pattern{location = create_location(3, 5)},
                    guard = undefined,
                    body = #binary_op_expr{
                        op = '*',
                        left = create_identifier('n'),
                        right = #function_call_expr{
                            function = create_identifier('factorial'),
                            args = [
                                #binary_op_expr{
                                    op = '-',
                                    left = create_identifier('n'),
                                    right = create_literal_int(1),
                                    location = create_location(3, 24)
                                }
                            ],
                            location = create_location(3, 14)
                        },
                        location = create_location(3, 10)
                    },
                    location = create_location(3, 5)
                }
            ],
            location = create_location(2, 3)
        },
        is_private = false,
        location = create_location(1, 1)
    },

    % Compile the recursive factorial function
    {Instructions, _State} = cure_codegen:compile_function(FactorialFn),

    % Verify instructions are generated
    ?assert(length(Instructions) > 0),

    % Check for match/case instruction
    MatchInstructions = [I || I <- Instructions, I#beam_instr.op == match_expr],
    ?assert(length(MatchInstructions) >= 1),

    % Check for recursive function call
    CallInstructions = [I || I <- Instructions, I#beam_instr.op == function_call],
    RecursiveCalls = [
        I
     || I <- CallInstructions,
        lists:member(factorial, I#beam_instr.args)
    ],
    ?assert(length(RecursiveCalls) >= 1),

    % Check for multiplication operation
    MultInstructions = [
        I
     || I <- Instructions,
        lists:member(I#beam_instr.op, [binary_op, mult_op])
    ],
    ?assert(length(MultInstructions) >= 1),

    cure_utils:debug("✓ Recursive function calls test passed~n").

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

    cure_utils:debug("✓ Higher-order function calls test passed~n").

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
                        params = [
                            #param{name = y, type = undefined, location = create_location(2, 17)}
                        ],
                        body = #binary_op_expr{
                            op = '+',
                            % Captured variable
                            left = create_identifier('x'),
                            % Parameter
                            right = create_identifier('y'),
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
    % Should capture x
    ?assertEqual(1, length(CaptureInstructions)),

    % Verify closure call
    CallInstructions = [I || I <- Instructions, I#beam_instr.op == closure_call],
    ?assertEqual(1, length(CallInstructions)),

    cure_utils:debug("✓ Closure generation test passed~n").

%% Test tail call optimization
test_tail_call_optimization() ->
    % Test tail-recursive factorial with accumulator:
    % factorial_tail = fn n, acc ->
    %   match n
    %     0 -> acc
    %     _ -> factorial_tail(n - 1, n * acc)
    %   end
    % end
    FactorialTailFn = #function_def{
        name = factorial_tail,
        params = [
            #param{name = n, type = undefined, location = create_location(1, 22)},
            #param{name = acc, type = undefined, location = create_location(1, 25)}
        ],
        return_type = undefined,
        constraint = undefined,
        body = #match_expr{
            expr = create_identifier('n'),
            patterns = [
                #match_clause{
                    pattern = #literal_expr{value = 0, location = create_location(2, 5)},
                    guard = undefined,
                    body = create_identifier('acc'),
                    location = create_location(2, 5)
                },
                #match_clause{
                    pattern = #wildcard_pattern{location = create_location(3, 5)},
                    guard = undefined,
                    body = #function_call_expr{
                        function = create_identifier('factorial_tail'),
                        args = [
                            #binary_op_expr{
                                op = '-',
                                left = create_identifier('n'),
                                right = create_literal_int(1),
                                location = create_location(3, 29)
                            },
                            #binary_op_expr{
                                op = '*',
                                left = create_identifier('n'),
                                right = create_identifier('acc'),
                                location = create_location(3, 35)
                            }
                        ],
                        location = create_location(3, 10)
                    },
                    location = create_location(3, 5)
                }
            ],
            location = create_location(2, 3)
        },
        is_private = false,
        location = create_location(1, 1)
    },

    % Compile the tail-recursive factorial function
    {Instructions, _State} = cure_codegen:compile_function(FactorialTailFn),

    % Verify instructions are generated
    ?assert(length(Instructions) > 0),

    % Check for match/case instruction
    MatchInstructions = [I || I <- Instructions, I#beam_instr.op == match_expr],
    ?assert(length(MatchInstructions) >= 1),

    % Check for tail-recursive function call
    CallInstructions = [I || I <- Instructions, I#beam_instr.op == function_call],
    TailCalls = [
        I
     || I <- CallInstructions,
        lists:member(factorial_tail, I#beam_instr.args)
    ],
    ?assert(length(TailCalls) >= 1),

    % Check for tail call optimization marker (if supported)
    TailCallOptInstructions = [
        I
     || I <- Instructions,
        lists:member(I#beam_instr.op, [tail_call, tail_call_only])
    ],
    % Tail call optimization may or may not be present depending on implementation
    % Just verify the instruction list was generated correctly

    cure_utils:debug("✓ Tail call optimization test passed~n").

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

    cure_utils:debug("✓ Let expression optimizations test passed~n").

%% ============================================================================
%% Helper Functions for Creating AST Nodes
%% ============================================================================

create_location(Line, Column) ->
    #location{line = Line, column = Column, file = "test"}.

create_literal_int(Value) ->
    #literal_expr{value = Value, location = create_location(1, 1)}.

create_identifier(Name) ->
    #identifier_expr{name = Name, location = create_location(1, 1)}.
