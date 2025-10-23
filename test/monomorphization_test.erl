%% Monomorphization Pass Tests - Polymorphic Function Specialization
-module(monomorphization_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").
-include("../src/types/cure_type_optimizer.hrl").

%% Run all monomorphization tests
run() ->
    cure_utils:debug("Running Monomorphization Pass tests...~n"),
    test_basic_polymorphic_function(),
    test_multiple_type_instances(),
    test_nested_polymorphic_calls(),
    test_generic_data_structures(),
    test_higher_order_function_monomorphization(),
    test_recursive_polymorphic_functions(),
    test_cross_module_monomorphization(),
    test_monomorphization_optimization(),
    test_behavior_preservation(),
    test_specialization_pruning(),
    cure_utils:debug("All monomorphization pass tests passed!~n").

%% Test basic polymorphic function monomorphization
test_basic_polymorphic_function() ->
    % Test: def identity(x: T) -> T = x
    PolymorphicFunction = #function_def{
        name = identity,
        params = [
            #param{name = x, type = create_type_variable('T'), location = create_location(1, 11)}
        ],
        return_type = create_type_variable('T'),
        constraint = undefined,
        body = create_identifier('x'),
        location = create_location(1, 1)
    },

    % Create usage sites with different types
    UsageSites = [
        % Int instance
        create_function_call('identity', [create_literal_int(42)]),
        % String instance
        create_function_call('identity', [create_literal_string("hello")]),
        % Bool instance
        create_function_call('identity', [create_literal_bool(true)])
    ],

    % Create AST with function and usage sites
    OriginalAST = [PolymorphicFunction | create_wrapper_functions(UsageSites)],

    % Run monomorphization
    Config = cure_type_optimizer:default_optimization_config(),
    Context = cure_type_optimizer:initialize_optimization_context(Config),
    MonomorphizedAST = cure_type_optimizer:monomorphization_pass(OriginalAST, Context),

    % Verify monomorphization results
    Functions = extract_functions(MonomorphizedAST),

    % Should generate specialized versions for each type
    IdentityFunctions = [
        F
     || F <- Functions,
        string:prefix(atom_to_list(F#function_def.name), "identity") =/= nomatch
    ],
    % At least Int, String, Bool versions
    ?assert(length(IdentityFunctions) >= 3),

    % Verify specialized function names
    FunctionNames = [F#function_def.name || F <- IdentityFunctions],
    ?assert(lists:member('identity_Int', FunctionNames)),
    ?assert(lists:member('identity_String', FunctionNames)),
    ?assert(lists:member('identity_Bool', FunctionNames)),

    % Verify type annotations are concrete
    lists:foreach(
        fun(F) ->
            case F#function_def.name of
                'identity_Int' ->
                    ?assertMatch(
                        #primitive_type{name = 'Int'},
                        (hd(F#function_def.params))#param.type
                    );
                'identity_String' ->
                    ?assertMatch(
                        #primitive_type{name = 'String'},
                        (hd(F#function_def.params))#param.type
                    );
                'identity_Bool' ->
                    ?assertMatch(
                        #primitive_type{name = 'Bool'},
                        (hd(F#function_def.params))#param.type
                    );
                _ ->
                    ok
            end
        end,
        IdentityFunctions
    ),

    cure_utils:debug("✓ Basic polymorphic function test passed~n").

%% Test multiple type instances with complex types
test_multiple_type_instances() ->
    % Test: def pair(x: T, y: U) -> (T, U) = (x, y)
    PolymorphicPairFunction = #function_def{
        name = pair,
        params = [
            #param{name = x, type = create_type_variable('T'), location = create_location(1, 10)},
            #param{name = y, type = create_type_variable('U'), location = create_location(1, 15)}
        ],
        return_type = #tuple_type{
            element_types = [create_type_variable('T'), create_type_variable('U')],
            location = create_location(1, 20)
        },
        constraint = undefined,
        body = #tuple_expr{
            elements = [create_identifier('x'), create_identifier('y')],
            location = create_location(2, 1)
        },
        location = create_location(1, 1)
    },

    % Create usage sites with different type combinations
    UsageSites = [
        % Int, String
        create_function_call('pair', [create_literal_int(1), create_literal_string("a")]),
        % Bool, Int
        create_function_call('pair', [create_literal_bool(true), create_literal_int(2)]),
        % String, String
        create_function_call('pair', [create_literal_string("x"), create_literal_string("y")]),
        % Int, Int
        create_function_call('pair', [create_literal_int(3), create_literal_int(4)])
    ],

    OriginalAST = [PolymorphicPairFunction | create_wrapper_functions(UsageSites)],

    % Run monomorphization
    Config = cure_type_optimizer:default_optimization_config(),
    Context = cure_type_optimizer:initialize_optimization_context(Config),
    MonomorphizedAST = cure_type_optimizer:monomorphization_pass(OriginalAST, Context),

    % Verify specialized versions
    Functions = extract_functions(MonomorphizedAST),
    PairFunctions = [
        F
     || F <- Functions,
        string:prefix(atom_to_list(F#function_def.name), "pair") =/= nomatch
    ],

    % Should generate 4 specialized versions
    ?assert(length(PairFunctions) >= 4),

    % Verify specific specializations exist
    FunctionNames = [F#function_def.name || F <- PairFunctions],
    ?assert(lists:member('pair_Int_String', FunctionNames)),
    ?assert(lists:member('pair_Bool_Int', FunctionNames)),
    ?assert(lists:member('pair_String_String', FunctionNames)),
    ?assert(lists:member('pair_Int_Int', FunctionNames)),

    cure_utils:debug("✓ Multiple type instances test passed~n").

%% Test nested polymorphic function calls
test_nested_polymorphic_calls() ->
    % Test: def compose(f: U -> V, g: T -> U, x: T) -> V = f(g(x))
    ComposeFunction = #function_def{
        name = compose,
        params = [
            #param{
                name = f,
                type = #function_type{
                    params = [create_type_variable('U')],
                    return_type = create_type_variable('V'),
                    location = create_location(1, 13)
                },
                location = create_location(1, 13)
            },
            #param{
                name = g,
                type = #function_type{
                    params = [create_type_variable('T')],
                    return_type = create_type_variable('U'),
                    location = create_location(1, 25)
                },
                location = create_location(1, 25)
            },
            #param{name = x, type = create_type_variable('T'), location = create_location(1, 37)}
        ],
        return_type = create_type_variable('V'),
        constraint = undefined,
        body = #function_call_expr{
            function = create_identifier('f'),
            args = [
                #function_call_expr{
                    function = create_identifier('g'),
                    args = [create_identifier('x')],
                    location = create_location(2, 3)
                }
            ],
            location = create_location(2, 1)
        },
        location = create_location(1, 1)
    },

    % Helper functions for composition
    HelperFunctions = [
        create_simple_function(
            double,
            [#param{name = x, type = #primitive_type{name = 'Int'}}],
            #primitive_type{name = 'Int'},
            #binary_op_expr{
                op = '*',
                left = create_identifier('x'),
                right = create_literal_int(2)
            }
        ),
        create_simple_function(
            to_string,
            [#param{name = x, type = #primitive_type{name = 'Int'}}],
            #primitive_type{name = 'String'},
            create_function_call('int_to_string', [create_identifier('x')])
        ),
        create_simple_function(
            length_fn,
            [#param{name = s, type = #primitive_type{name = 'String'}}],
            #primitive_type{name = 'Int'},
            create_function_call('string_length', [create_identifier('s')])
        )
    ],

    % Usage with nested type instantiations: compose(length_fn, to_string, double(5))
    UsageSite = create_function_call('compose', [
        create_identifier('length_fn'),
        create_identifier('to_string'),
        create_function_call('double', [create_literal_int(5)])
    ]),

    OriginalAST = [ComposeFunction | HelperFunctions] ++ [create_wrapper_function(UsageSite)],

    % Run monomorphization
    Config = cure_type_optimizer:default_optimization_config(),
    Context = cure_type_optimizer:initialize_optimization_context(Config),
    MonomorphizedAST = cure_type_optimizer:monomorphization_pass(OriginalAST, Context),

    % Verify compose function gets specialized
    Functions = extract_functions(MonomorphizedAST),
    ComposeFunctions = [
        F
     || F <- Functions,
        string:prefix(atom_to_list(F#function_def.name), "compose") =/= nomatch
    ],

    ?assert(length(ComposeFunctions) >= 1),

    % Verify the specialized version has concrete types
    SpecializedCompose = hd(ComposeFunctions),
    ParamTypes = [P#param.type || P <- SpecializedCompose#function_def.params],

    % Should have concrete function types, not type variables
    lists:foreach(
        fun(Type) ->
            ?assertNot(is_type_variable(Type))
        end,
        ParamTypes
    ),

    cure_utils:debug("✓ Nested polymorphic calls test passed~n").

%% Test generic data structures
test_generic_data_structures() ->
    % Test: def map_list(f: T -> U, list: List(T)) -> List(U)
    MapFunction = #function_def{
        name = map_list,
        params = [
            #param{
                name = f,
                type = #function_type{
                    params = [create_type_variable('T')],
                    return_type = create_type_variable('U'),
                    location = create_location(1, 13)
                },
                location = create_location(1, 13)
            },
            #param{
                name = list,
                type = #list_type{
                    element_type = create_type_variable('T'),
                    length = undefined,
                    location = create_location(1, 25)
                },
                location = create_location(1, 25)
            }
        ],
        return_type = #list_type{
            element_type = create_type_variable('U'),
            length = undefined,
            location = create_location(1, 35)
        },
        constraint = undefined,
        body = create_map_implementation(),
        location = create_location(1, 1)
    },

    % Usage sites with different list types
    UsageSites = [
        create_function_call('map_list', [
            create_identifier('double'),
            % List(Int) -> List(Int)
            create_list_literal([1, 2, 3])
        ]),
        create_function_call('map_list', [
            create_identifier('to_upper'),
            % List(String) -> List(String)
            create_list_literal(["a", "b", "c"])
        ])
    ],

    OriginalAST = [MapFunction | create_wrapper_functions(UsageSites)],

    % Run monomorphization
    Config = cure_type_optimizer:default_optimization_config(),
    Context = cure_type_optimizer:initialize_optimization_context(Config),
    MonomorphizedAST = cure_type_optimizer:monomorphization_pass(OriginalAST, Context),

    % Verify specialized versions
    Functions = extract_functions(MonomorphizedAST),
    MapFunctions = [
        F
     || F <- Functions,
        string:prefix(atom_to_list(F#function_def.name), "map_list") =/= nomatch
    ],

    % Int->Int and String->String versions
    ?assert(length(MapFunctions) >= 2),

    % Verify list types are specialized
    lists:foreach(
        fun(F) ->
            ListParam = lists:nth(2, F#function_def.params),
            ?assertMatch(#list_type{element_type = #primitive_type{}}, ListParam#param.type)
        end,
        MapFunctions
    ),

    cure_utils:debug("✓ Generic data structures test passed~n").

%% Test higher-order function monomorphization
test_higher_order_function_monomorphization() ->
    % Test: def apply_twice(f: T -> T, x: T) -> T = f(f(x))
    ApplyTwiceFunction = #function_def{
        name = apply_twice,
        params = [
            #param{
                name = f,
                type = #function_type{
                    params = [create_type_variable('T')],
                    return_type = create_type_variable('T'),
                    location = create_location(1, 15)
                },
                location = create_location(1, 15)
            },
            #param{name = x, type = create_type_variable('T'), location = create_location(1, 27)}
        ],
        return_type = create_type_variable('T'),
        constraint = undefined,
        body = #function_call_expr{
            function = create_identifier('f'),
            args = [
                #function_call_expr{
                    function = create_identifier('f'),
                    args = [create_identifier('x')],
                    location = create_location(2, 3)
                }
            ],
            location = create_location(2, 1)
        },
        location = create_location(1, 1)
    },

    % Helper functions
    HelperFunctions = [
        create_simple_function(
            increment,
            [#param{name = x, type = #primitive_type{name = 'Int'}}],
            #primitive_type{name = 'Int'},
            #binary_op_expr{
                op = '+',
                left = create_identifier('x'),
                right = create_literal_int(1)
            }
        ),
        create_simple_function(
            negate,
            [#param{name = b, type = #primitive_type{name = 'Bool'}}],
            #primitive_type{name = 'Bool'},
            #unary_op_expr{op = 'not', operand = create_identifier('b')}
        )
    ],

    % Usage sites
    UsageSites = [
        create_function_call('apply_twice', [create_identifier('increment'), create_literal_int(5)]),
        create_function_call('apply_twice', [create_identifier('negate'), create_literal_bool(true)])
    ],

    OriginalAST = [ApplyTwiceFunction | HelperFunctions] ++ create_wrapper_functions(UsageSites),

    % Run monomorphization
    Config = cure_type_optimizer:default_optimization_config(),
    Context = cure_type_optimizer:initialize_optimization_context(Config),
    MonomorphizedAST = cure_type_optimizer:monomorphization_pass(OriginalAST, Context),

    % Verify specialization
    Functions = extract_functions(MonomorphizedAST),
    ApplyTwiceFunctions = [
        F
     || F <- Functions,
        string:prefix(atom_to_list(F#function_def.name), "apply_twice") =/= nomatch
    ],

    % Int and Bool versions
    ?assert(length(ApplyTwiceFunctions) >= 2),

    % Verify function parameter types are specialized
    lists:foreach(
        fun(F) ->
            FunctionParam = hd(F#function_def.params),
            case FunctionParam#param.type of
                #function_type{params = [ParamType], return_type = ReturnType} ->
                    ?assertMatch(#primitive_type{}, ParamType),
                    ?assertEqual(ParamType, ReturnType);
                _ ->
                    % Should be a function type
                    ?assert(false)
            end
        end,
        ApplyTwiceFunctions
    ),

    cure_utils:debug("✓ Higher-order function monomorphization test passed~n").

%% Test recursive polymorphic functions
test_recursive_polymorphic_functions() ->
    % Test: def list_length(list: List(T)) -> Int
    ListLengthFunction = #function_def{
        name = list_length,
        params = [
            #param{
                name = list,
                type = #list_type{
                    element_type = create_type_variable('T'),
                    length = undefined,
                    location = create_location(1, 17)
                },
                location = create_location(1, 17)
            }
        ],
        return_type = #primitive_type{name = 'Int', location = create_location(1, 30)},
        constraint = undefined,
        body = #match_expr{
            expr = create_identifier('list'),
            patterns = [
                #match_clause{
                    pattern = #list_pattern{elements = [], tail = undefined},
                    guard = undefined,
                    body = create_literal_int(0),
                    location = create_location(2, 5)
                },
                #match_clause{
                    pattern = #list_pattern{
                        elements = [#wildcard_pattern{}],
                        tail = #identifier_pattern{name = tail}
                    },
                    guard = undefined,
                    body = #binary_op_expr{
                        op = '+',
                        left = create_literal_int(1),
                        right = #function_call_expr{
                            function = create_identifier('list_length'),
                            args = [create_identifier('tail')],
                            location = create_location(3, 15)
                        },
                        location = create_location(3, 9)
                    },
                    location = create_location(3, 5)
                }
            ],
            location = create_location(2, 1)
        },
        location = create_location(1, 1)
    },

    % Usage sites with different list types
    UsageSites = [
        create_function_call('list_length', [create_list_literal([1, 2, 3])]),
        create_function_call('list_length', [create_list_literal(["a", "b"])])
    ],

    OriginalAST = [ListLengthFunction | create_wrapper_functions(UsageSites)],

    % Run monomorphization
    Config = cure_type_optimizer:default_optimization_config(),
    Context = cure_type_optimizer:initialize_optimization_context(Config),
    MonomorphizedAST = cure_type_optimizer:monomorphization_pass(OriginalAST, Context),

    % Verify recursive function gets specialized correctly
    Functions = extract_functions(MonomorphizedAST),
    LengthFunctions = [
        F
     || F <- Functions,
        string:prefix(atom_to_list(F#function_def.name), "list_length") =/= nomatch
    ],

    % Int and String list versions
    ?assert(length(LengthFunctions) >= 2),

    % Verify recursive calls use specialized function names
    lists:foreach(
        fun(F) ->
            RecursiveCalls = find_recursive_calls_in_function(F),
            lists:foreach(
                fun(Call) ->
                    FuncName = get_function_call_name(Call),
                    % Recursive calls should use the specialized name, not the original
                    ?assertNotEqual('list_length', FuncName)
                end,
                RecursiveCalls
            )
        end,
        LengthFunctions
    ),

    cure_utils:debug("✓ Recursive polymorphic functions test passed~n").

%% Test cross-module monomorphization
test_cross_module_monomorphization() ->
    % Simulate cross-module polymorphic function usage
    % Module A defines: def generic_function(x: T) -> T
    ModuleAFunction = #function_def{
        name = generic_function,
        params = [#param{name = x, type = create_type_variable('T')}],
        return_type = create_type_variable('T'),
        constraint = undefined,
        body = create_identifier('x'),
        location = create_location(1, 1)
    },

    % Module B uses generic_function with specific types
    ModuleBUsages = [
        create_function_call('generic_function', [create_literal_int(10)]),
        create_function_call('generic_function', [create_literal_string("test")])
    ],

    % Create combined AST representing multi-module program
    OriginalAST = [ModuleAFunction | create_wrapper_functions(ModuleBUsages)],

    % Run monomorphization across modules
    Config = cure_type_optimizer:default_optimization_config(),
    Context = cure_type_optimizer:initialize_optimization_context(Config),
    MonomorphizedAST = cure_type_optimizer:monomorphization_pass(OriginalAST, Context),

    % Verify cross-module specialization
    Functions = extract_functions(MonomorphizedAST),
    GenericFunctions = [
        F
     || F <- Functions,
        string:prefix(atom_to_list(F#function_def.name), "generic_function") =/= nomatch
    ],

    % Int and String versions
    ?assert(length(GenericFunctions) >= 2),

    % Verify call sites are updated to use specialized versions
    WrapperFunctions = [
        F
     || F <- Functions,
        F#function_def.name =/= generic_function,
        not lists:member(
            F#function_def.name,
            ['generic_function_Int', 'generic_function_String']
        )
    ],

    lists:foreach(
        fun(F) ->
            Calls = find_function_calls_in_function(F),
            GenericCalls = [
                C
             || C <- Calls,
                string:prefix(
                    atom_to_list(get_function_call_name(C)),
                    "generic_function"
                ) =/= nomatch
            ],
            % Should use specialized names, not original
            lists:foreach(
                fun(Call) ->
                    ?assertNotEqual('generic_function', get_function_call_name(Call))
                end,
                GenericCalls
            )
        end,
        WrapperFunctions
    ),

    cure_utils:debug("✓ Cross-module monomorphization test passed~n").

%% Test monomorphization optimization decisions
test_monomorphization_optimization() ->
    % Test function used only once (might not need monomorphization)
    SingleUseFunction = #function_def{
        name = single_use,
        params = [#param{name = x, type = create_type_variable('T')}],
        return_type = create_type_variable('T'),
        constraint = undefined,
        body = create_identifier('x'),
        location = create_location(1, 1)
    },

    % Function used many times with same type (good candidate)
    MultiUseFunction = #function_def{
        name = multi_use,
        params = [#param{name = x, type = create_type_variable('T')}],
        return_type = create_type_variable('T'),
        constraint = undefined,
        body = create_identifier('x'),
        location = create_location(3, 1)
    },

    % Single usage
    SingleUsage = [create_function_call('single_use', [create_literal_int(1)])],

    % Multiple usages with same type
    MultipleUsages = lists:duplicate(
        10,
        create_function_call('multi_use', [create_literal_string("test")])
    ),

    OriginalAST = [
        SingleUseFunction,
        MultiUseFunction
        | create_wrapper_functions(SingleUsage ++ MultipleUsages)
    ],

    % Configure optimization thresholds
    Config = #optimization_config{
        enable_monomorphization = true,
        % Only specialize if used 3+ times
        specialization_threshold = 3,
        max_specializations = 5
    },
    Context = cure_type_optimizer:initialize_optimization_context(Config),

    MonomorphizedAST = cure_type_optimizer:monomorphization_pass(OriginalAST, Context),

    % Verify optimization decisions
    Functions = extract_functions(MonomorphizedAST),

    % single_use might not be monomorphized (used only once)
    SingleUseFunctions = [
        F
     || F <- Functions,
        string:prefix(atom_to_list(F#function_def.name), "single_use") =/= nomatch
    ],
    % Original + at most 1 specialization
    ?assert(length(SingleUseFunctions) =< 2),

    % multi_use should be monomorphized (used 10 times)
    MultiUseFunctions = [
        F
     || F <- Functions,
        string:prefix(atom_to_list(F#function_def.name), "multi_use") =/= nomatch
    ],
    % Should have specialized version
    ?assert(length(MultiUseFunctions) >= 1),

    cure_utils:debug("✓ Monomorphization optimization test passed~n").

%% Test behavior preservation after monomorphization
test_behavior_preservation() ->
    % Test complex polymorphic function that needs to preserve behavior
    SortFunction = #function_def{
        name = bubble_sort,
        params = [
            #param{
                name = list,
                type = #list_type{
                    element_type = create_type_variable('T'),
                    length = undefined
                }
            },
            #param{
                name = compare,
                type = #function_type{
                    params = [create_type_variable('T'), create_type_variable('T')],
                    return_type = #primitive_type{name = 'Bool'}
                }
            }
        ],
        return_type = #list_type{
            element_type = create_type_variable('T'),
            length = undefined
        },
        constraint = undefined,
        body = create_sort_implementation(),
        location = create_location(1, 1)
    },

    % Usage with different types
    IntCompare = create_simple_function(
        int_compare,
        [
            #param{name = a, type = #primitive_type{name = 'Int'}},
            #param{name = b, type = #primitive_type{name = 'Int'}}
        ],
        #primitive_type{name = 'Bool'},
        #binary_op_expr{
            op = '<',
            left = create_identifier('a'),
            right = create_identifier('b')
        }
    ),

    StringCompare = create_simple_function(
        string_compare,
        [
            #param{name = a, type = #primitive_type{name = 'String'}},
            #param{name = b, type = #primitive_type{name = 'String'}}
        ],
        #primitive_type{name = 'Bool'},
        create_function_call(
            'string_less_than',
            [create_identifier('a'), create_identifier('b')]
        )
    ),

    UsageSites = [
        create_function_call('bubble_sort', [
            create_list_literal([3, 1, 4, 1, 5]),
            create_identifier('int_compare')
        ]),
        create_function_call('bubble_sort', [
            create_list_literal(["zebra", "apple", "banana"]),
            create_identifier('string_compare')
        ])
    ],

    OriginalAST = [SortFunction, IntCompare, StringCompare | create_wrapper_functions(UsageSites)],

    % Run monomorphization
    Config = cure_type_optimizer:default_optimization_config(),
    Context = cure_type_optimizer:initialize_optimization_context(Config),
    MonomorphizedAST = cure_type_optimizer:monomorphization_pass(OriginalAST, Context),

    % Verify behavior preservation through semantic equivalence checks
    Functions = extract_functions(MonomorphizedAST),
    SortFunctions = [
        F
     || F <- Functions,
        string:prefix(atom_to_list(F#function_def.name), "bubble_sort") =/= nomatch
    ],

    % Should have specialized versions
    ?assert(length(SortFunctions) >= 2),

    % Verify each specialized function has the correct structure
    lists:foreach(
        fun(F) ->
            % Should have 2 parameters (list and compare function)
            ?assertEqual(2, length(F#function_def.params)),

            % Parameters should have concrete types, not type variables
            lists:foreach(
                fun(P) ->
                    ?assertNot(is_type_variable(P#param.type))
                end,
                F#function_def.params
            ),

            % Function body should be preserved (same structure as original)
            ?assertEqual(create_sort_implementation(), F#function_def.body)
        end,
        SortFunctions
    ),

    cure_utils:debug("✓ Behavior preservation test passed~n").

%% Test specialization pruning (removing unused specializations)
test_specialization_pruning() ->
    % Create function with potential for many specializations
    OverlyGenericFunction = #function_def{
        name = overly_generic,
        params = [
            #param{name = x, type = create_type_variable('T')},
            #param{name = y, type = create_type_variable('U')},
            #param{name = z, type = create_type_variable('V')}
        ],
        return_type = create_type_variable('T'),
        constraint = undefined,
        % Only uses first parameter
        body = create_identifier('x'),
        location = create_location(1, 1)
    },

    % Create many usage sites with different type combinations
    UsageSites = [
        create_function_call('overly_generic', [
            create_literal_int(1), create_literal_string("a"), create_literal_bool(true)
        ]),
        create_function_call('overly_generic', [
            create_literal_int(2), create_literal_string("b"), create_literal_bool(false)
        ]),
        create_function_call('overly_generic', [
            create_literal_int(3), create_literal_int(4), create_literal_string("c")
        ]),
        % Many more combinations...
        create_function_call('overly_generic', [
            create_literal_string("x"), create_literal_int(5), create_literal_bool(true)
        ])
        | lists:duplicate(
            20,
            create_function_call(
                'overly_generic',
                [create_literal_int(42), create_literal_string("common"), create_literal_bool(true)]
            )
        )
    ],

    OriginalAST = [OverlyGenericFunction | create_wrapper_functions(UsageSites)],

    % Configure with specialization limits
    Config = #optimization_config{
        enable_monomorphization = true,
        % Limit to 3 specializations
        max_specializations = 3,
        % Only create if used 5+ times
        specialization_threshold = 5
    },
    Context = cure_type_optimizer:initialize_optimization_context(Config),

    MonomorphizedAST = cure_type_optimizer:monomorphization_pass(OriginalAST, Context),

    % Verify pruning works
    Functions = extract_functions(MonomorphizedAST),
    GenericFunctions = [
        F
     || F <- Functions,
        string:prefix(atom_to_list(F#function_def.name), "overly_generic") =/= nomatch
    ],

    % Should respect the limit
    ?assert(length(GenericFunctions) =< 3),

    % The most common specialization should be kept
    FunctionNames = [F#function_def.name || F <- GenericFunctions],
    % The version used 20+ times should definitely exist
    ?assert(
        lists:any(
            fun(Name) ->
                string:find(atom_to_list(Name), "Int_String_Bool") =/= nomatch
            end,
            FunctionNames
        )
    ),

    cure_utils:debug("✓ Specialization pruning test passed~n").

%% ============================================================================
%% Helper Functions
%% ============================================================================

create_location(Line, Column) ->
    #location{line = Line, column = Column, file = "test"}.

create_literal_int(Value) ->
    #literal_expr{value = Value, location = create_location(1, 1)}.

create_literal_string(Value) ->
    #literal_expr{value = Value, location = create_location(1, 1)}.

create_literal_bool(Value) ->
    #literal_expr{value = Value, location = create_location(1, 1)}.

create_identifier(Name) ->
    #identifier_expr{name = Name, location = create_location(1, 1)}.

create_type_variable(Name) ->
    #primitive_type{name = Name, location = create_location(1, 1)}.

create_function_call(FuncName, Args) ->
    #function_call_expr{
        function = create_identifier(FuncName),
        args = Args,
        location = create_location(1, 1)
    }.

create_list_literal(Values) ->
    Elements = [
        if
            is_integer(V) -> create_literal_int(V);
            is_list(V) -> create_literal_string(V);
            is_boolean(V) -> create_literal_bool(V)
        end
     || V <- Values
    ],
    #list_expr{elements = Elements, location = create_location(1, 1)}.

create_wrapper_function(CallExpr) ->
    #function_def{
        name = list_to_atom("wrapper_" ++ integer_to_list(rand:uniform(10000))),
        params = [],
        return_type = undefined,
        constraint = undefined,
        body = CallExpr,
        location = create_location(1, 1)
    }.

create_wrapper_functions(CallExprs) ->
    [create_wrapper_function(Call) || Call <- CallExprs].

create_simple_function(Name, Params, ReturnType, Body) ->
    #function_def{
        name = Name,
        params = Params,
        return_type = ReturnType,
        constraint = undefined,
        body = Body,
        location = create_location(1, 1)
    }.

extract_functions(AST) ->
    [Item || Item <- AST, is_record(Item, function_def)].

is_type_variable(#primitive_type{name = Name}) ->
    NameStr = atom_to_list(Name),
    length(NameStr) == 1 andalso hd(NameStr) >= $A andalso hd(NameStr) =< $Z;
is_type_variable(_) ->
    false.

find_recursive_calls_in_function(#function_def{name = FuncName, body = Body}) ->
    find_function_calls_with_name(Body, FuncName).

find_function_calls_in_function(#function_def{body = Body}) ->
    find_all_function_calls(Body).

find_function_calls_with_name(Expr, TargetName) ->
    Calls = find_all_function_calls(Expr),
    [Call || Call <- Calls, get_function_call_name(Call) == TargetName].

find_all_function_calls(#function_call_expr{} = Call) ->
    [Call | lists:append([find_all_function_calls(Arg) || Arg <- Call#function_call_expr.args])];
find_all_function_calls(#let_expr{bindings = Bindings, body = Body}) ->
    BindingCalls = lists:append([find_all_function_calls(B#binding.value) || B <- Bindings]),
    BodyCalls = find_all_function_calls(Body),
    BindingCalls ++ BodyCalls;
find_all_function_calls(#binary_op_expr{left = Left, right = Right}) ->
    find_all_function_calls(Left) ++ find_all_function_calls(Right);
find_all_function_calls(#match_expr{expr = Expr, patterns = Patterns}) ->
    ExprCalls = find_all_function_calls(Expr),
    PatternCalls = lists:append([find_all_function_calls(C#match_clause.body) || C <- Patterns]),
    ExprCalls ++ PatternCalls;
find_all_function_calls(_) ->
    [].

get_function_call_name(#function_call_expr{function = #identifier_expr{name = Name}}) ->
    Name;
get_function_call_name(_) ->
    undefined.

%% Placeholder implementations
create_map_implementation() ->
    create_identifier('not_implemented').

create_sort_implementation() ->
    create_identifier('not_implemented').
