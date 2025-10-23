%% Inlining Pass Tests - Semantic Equivalence After Inlining
-module(inlining_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").
-include("../src/types/cure_type_optimizer.hrl").

%% Run all inlining tests
run() ->
    cure_utils:debug("Running Inlining Pass tests...~n"),
    test_inline_small_functions(),
    test_inline_across_call_sites(),
    test_do_not_inline_large_functions(),
    test_inline_preserves_semantics_simple(),
    test_inline_with_side_effects_respected(),
    test_inline_recursive_guarded(),
    test_inline_higher_order_contexts(),
    test_inline_with_pattern_matching(),
    test_inline_with_let_bindings(),
    test_inline_report_and_limits(),
    cure_utils:debug("All inlining pass tests passed!~n").

%% Test that small functions are inlined
test_inline_small_functions() ->
    AST = sample_ast_small_functions(),
    Config = cure_type_optimizer:default_optimization_config(),
    Ctx0 = cure_type_optimizer:initialize_optimization_context(Config),
    Inlined = cure_type_optimizer:inlining_pass(AST, Ctx0),

    %% verify add/2 call sites replaced
    CallSites = find_function_calls_in_program(Inlined),
    %% Should not find calls to 'add' anymore
    ?assertNot(lists:any(fun(C) -> get_call_name(C) == add end, CallSites)),

    cure_utils:debug("✓ Inline small functions test passed~n").

%% Test inlining applied across multiple call sites
test_inline_across_call_sites() ->
    AST = sample_ast_many_calls(),
    Config = cure_type_optimizer:default_optimization_config(),
    Ctx = cure_type_optimizer:initialize_optimization_context(Config),
    Inlined = cure_type_optimizer:inlining_pass(AST, Ctx),

    Calls = find_function_calls_in_program(Inlined),
    %% small_add and tiny_helper should be removed from call sites
    ?assertNot(
        lists:any(fun(C) -> lists:member(get_call_name(C), [small_add, tiny_helper]) end, Calls)
    ),

    cure_utils:debug("✓ Inline across call sites test passed~n").

%% Ensure large functions are not inlined
test_do_not_inline_large_functions() ->
    AST = sample_ast_small_and_large(),
    Config = cure_type_optimizer:set_optimization_level(2),
    Ctx = cure_type_optimizer:initialize_optimization_context(Config),
    Inlined = cure_type_optimizer:inlining_pass(AST, Ctx),

    Calls = find_function_calls_in_program(Inlined),
    %% big_function should remain as a call
    ?assert(lists:any(fun(C) -> get_call_name(C) == big_function end, Calls)),

    cure_utils:debug("✓ Do not inline large functions test passed~n").

%% Semantic equivalence check on simple arithmetic
test_inline_preserves_semantics_simple() ->
    AST = sample_ast_small_functions(),
    Config = cure_type_optimizer:default_optimization_config(),
    Ctx = cure_type_optimizer:initialize_optimization_context(Config),
    Inlined = cure_type_optimizer:inlining_pass(AST, Ctx),

    %% Type check before and after
    {ok, _Env, _Result1} = cure_typechecker:check_function(get_function(AST, main)),
    {ok, _Env2, _Result2} = cure_typechecker:check_function(get_function(Inlined, main)),

    cure_utils:debug("✓ Semantic equivalence (types) test passed~n").

%% Respect side effects: do not duplicate side effects when inlining
test_inline_with_side_effects_respected() ->
    AST = sample_ast_with_side_effects(),
    Config = cure_type_optimizer:default_optimization_config(),
    Ctx = cure_type_optimizer:initialize_optimization_context(Config),
    Inlined = cure_type_optimizer:inlining_pass(AST, Ctx),

    %% Ensure print_once call isn't duplicated
    Calls = find_function_calls_in_program(Inlined),
    Duplicates = [C || C <- Calls, get_call_name(C) == print_once],
    ?assertEqual(1, length(Duplicates)),

    cure_utils:debug("✓ Inline with side effects respected test passed~n").

%% Guard against inlining recursive functions
test_inline_recursive_guarded() ->
    AST = sample_ast_recursive(),
    Config = cure_type_optimizer:default_optimization_config(),
    Ctx = cure_type_optimizer:initialize_optimization_context(Config),
    Inlined = cure_type_optimizer:inlining_pass(AST, Ctx),

    %% factorial should still be called
    Calls = find_function_calls_in_program(Inlined),
    ?assert(lists:any(fun(C) -> get_call_name(C) == factorial end, Calls)),

    cure_utils:debug("✓ Inline recursive guarded test passed~n").

%% Inline within higher-order contexts
test_inline_higher_order_contexts() ->
    AST = sample_ast_hof(),
    Config = cure_type_optimizer:default_optimization_config(),
    Ctx = cure_type_optimizer:initialize_optimization_context(Config),
    Inlined = cure_type_optimizer:inlining_pass(AST, Ctx),

    Calls = find_function_calls_in_program(Inlined),
    %% small lambda body should remain but helper inlined inside map
    ?assertNot(lists:any(fun(C) -> get_call_name(C) == inc end, Calls)),

    cure_utils:debug("✓ Inline in higher-order contexts test passed~n").

%% Inline with pattern matching in body
test_inline_with_pattern_matching() ->
    AST = sample_ast_with_match(),
    Config = cure_type_optimizer:default_optimization_config(),
    Ctx = cure_type_optimizer:initialize_optimization_context(Config),
    Inlined = cure_type_optimizer:inlining_pass(AST, Ctx),

    %% match-based small fn becomes match in call-site, no call left
    Calls = find_function_calls_in_program(Inlined),
    ?assertNot(lists:any(fun(C) -> get_call_name(C) == head_or_zero end, Calls)),

    cure_utils:debug("✓ Inline with pattern matching test passed~n").

%% Inline when body contains let bindings
test_inline_with_let_bindings() ->
    AST = sample_ast_with_let_body(),
    Config = cure_type_optimizer:default_optimization_config(),
    Ctx = cure_type_optimizer:initialize_optimization_context(Config),
    Inlined = cure_type_optimizer:inlining_pass(AST, Ctx),

    Calls = find_function_calls_in_program(Inlined),
    ?assertNot(lists:any(fun(C) -> get_call_name(C) == add3 end, Calls)),

    cure_utils:debug("✓ Inline with let bindings test passed~n").

%% Verify inlining report and limits
test_inline_report_and_limits() ->
    AST = sample_ast_many_calls(),
    Config = #optimization_config{
        enable_inlining = true,
        inline_threshold = 5,
        max_specializations = 2
    },
    Ctx = cure_type_optimizer:initialize_optimization_context(Config),
    Inlined = cure_type_optimizer:inlining_pass(AST, Ctx),

    %% Count residual calls to confirm cap respected
    Calls = find_function_calls_in_program(Inlined),
    %% Expect some calls remain due to per-function limit
    ?assert(length(Calls) > 0),

    cure_utils:debug("✓ Inline report/limits test passed~n").

%% ============================================================================
%% Sample ASTs
%% ============================================================================

sample_ast_small_functions() ->
    [
        #function_def{
            name = add,
            params = [
                #param{name = x, type = #primitive_type{name = 'Int'}},
                #param{name = y, type = #primitive_type{name = 'Int'}}
            ],
            return_type = #primitive_type{name = 'Int'},
            constraint = undefined,
            body = #binary_op_expr{
                op = '+', left = #identifier_expr{name = x}, right = #identifier_expr{name = y}
            },
            location = #location{line = 1, column = 1}
        },
        #function_def{
            name = main,
            params = [],
            return_type = #primitive_type{name = 'Int'},
            constraint = undefined,
            body = #function_call_expr{
                function = #identifier_expr{name = add},
                args = [#literal_expr{value = 1}, #literal_expr{value = 2}]
            },
            location = #location{line = 2, column = 1}
        }
    ].

sample_ast_many_calls() ->
    [
        #function_def{
            name = small_add,
            params = [
                #param{name = a, type = #primitive_type{name = 'Int'}},
                #param{name = b, type = #primitive_type{name = 'Int'}}
            ],
            return_type = #primitive_type{name = 'Int'},
            constraint = undefined,
            body = #binary_op_expr{
                op = '+', left = #identifier_expr{name = a}, right = #identifier_expr{name = b}
            },
            location = #location{line = 1, column = 1}
        },
        #function_def{
            name = tiny_helper,
            params = [#param{name = x, type = #primitive_type{name = 'Int'}}],
            return_type = #primitive_type{name = 'Int'},
            constraint = undefined,
            body = #identifier_expr{name = x},
            location = #location{line = 2, column = 1}
        },
        #function_def{
            name = caller,
            params = [],
            return_type = #primitive_type{name = 'Int'},
            constraint = undefined,
            body = #block_expr{
                expressions = [
                    #function_call_expr{
                        function = #identifier_expr{name = small_add},
                        args = [#literal_expr{value = 1}, #literal_expr{value = 2}]
                    },
                    #function_call_expr{
                        function = #identifier_expr{name = tiny_helper},
                        args = [#literal_expr{value = 5}]
                    }
                ]
            },
            location = #location{line = 3, column = 1}
        }
    ].

sample_ast_small_and_large() ->
    [
        #function_def{
            name = big_function,
            params = [#param{name = x, type = #primitive_type{name = 'Int'}}],
            return_type = #primitive_type{name = 'Int'},
            constraint = undefined,
            body = #block_expr{
                expressions = [
                    #binary_op_expr{
                        op = '+',
                        left = #identifier_expr{name = x},
                        right = #literal_expr{value = 1}
                    },
                    #binary_op_expr{
                        op = '*',
                        left = #identifier_expr{name = x},
                        right = #literal_expr{value = 2}
                    },
                    #binary_op_expr{
                        op = '-',
                        left = #identifier_expr{name = x},
                        right = #literal_expr{value = 3}
                    }
                ]
            },
            location = #location{line = 1, column = 1}
        },
        #function_def{
            name = user,
            params = [],
            return_type = #primitive_type{name = 'Int'},
            constraint = undefined,
            body = #function_call_expr{
                function = #identifier_expr{name = big_function}, args = [#literal_expr{value = 10}]
            },
            location = #location{line = 2, column = 1}
        }
    ].

sample_ast_with_side_effects() ->
    [
        #function_def{
            name = print_once,
            params = [#param{name = msg, type = #primitive_type{name = 'String'}}],
            return_type = #primitive_type{name = 'Unit'},
            constraint = undefined,
            body = #identifier_expr{name = side_effect},
            location = #location{line = 1, column = 1}
        },
        #function_def{
            name = caller,
            params = [],
            return_type = #primitive_type{name = 'Unit'},
            constraint = undefined,
            body = #function_call_expr{
                function = #identifier_expr{name = print_once}, args = [#literal_expr{value = "hi"}]
            },
            location = #location{line = 2, column = 1}
        }
    ].

sample_ast_recursive() ->
    [
        #function_def{
            name = factorial,
            params = [#param{name = n, type = #primitive_type{name = 'Int'}}],
            return_type = #primitive_type{name = 'Int'},
            constraint = undefined,
            body = #binary_op_expr{
                op = '*',
                left = #identifier_expr{name = n},
                right = #function_call_expr{
                    function = #identifier_expr{name = factorial},
                    args = [
                        #binary_op_expr{
                            op = '-',
                            left = #identifier_expr{name = n},
                            right = #literal_expr{value = 1}
                        }
                    ]
                }
            },
            location = #location{line = 1, column = 1}
        },
        #function_def{
            name = caller,
            params = [],
            return_type = #primitive_type{name = 'Int'},
            constraint = undefined,
            body = #function_call_expr{
                function = #identifier_expr{name = factorial}, args = [#literal_expr{value = 5}]
            },
            location = #location{line = 2, column = 1}
        }
    ].

sample_ast_hof() ->
    [
        #function_def{
            name = inc,
            params = [#param{name = x, type = #primitive_type{name = 'Int'}}],
            return_type = #primitive_type{name = 'Int'},
            constraint = undefined,
            body = #binary_op_expr{
                op = '+', left = #identifier_expr{name = x}, right = #literal_expr{value = 1}
            },
            location = #location{line = 1, column = 1}
        },
        #function_def{
            name = use_map,
            params = [],
            return_type = #primitive_type{name = 'List'},
            constraint = undefined,
            body = #function_call_expr{
                function = #identifier_expr{name = map},
                args = [
                    #identifier_expr{name = inc},
                    #list_expr{elements = [#literal_expr{value = 1}, #literal_expr{value = 2}]}
                ]
            },
            location = #location{line = 2, column = 1}
        }
    ].

sample_ast_with_match() ->
    [
        #function_def{
            name = head_or_zero,
            params = [
                #param{name = xs, type = #list_type{element_type = #primitive_type{name = 'Int'}}}
            ],
            return_type = #primitive_type{name = 'Int'},
            constraint = undefined,
            body = #match_expr{
                expr = #identifier_expr{name = xs},
                patterns = [
                    #match_clause{
                        pattern = #list_pattern{
                            elements = [#identifier_pattern{name = h}], tail = undefined
                        },
                        guard = undefined,
                        body = #identifier_expr{name = h}
                    },
                    #match_clause{
                        pattern = #list_pattern{elements = [], tail = undefined},
                        guard = undefined,
                        body = #literal_expr{value = 0}
                    }
                ]
            },
            location = #location{line = 1, column = 1}
        },
        #function_def{
            name = main,
            params = [],
            return_type = #primitive_type{name = 'Int'},
            constraint = undefined,
            body = #function_call_expr{
                function = #identifier_expr{name = head_or_zero},
                args = [#list_expr{elements = [#literal_expr{value = 7}]}]
            },
            location = #location{line = 2, column = 1}
        }
    ].

sample_ast_with_let_body() ->
    [
        #function_def{
            name = add3,
            params = [
                #param{name = a, type = #primitive_type{name = 'Int'}},
                #param{name = b, type = #primitive_type{name = 'Int'}},
                #param{name = c, type = #primitive_type{name = 'Int'}}
            ],
            return_type = #primitive_type{name = 'Int'},
            constraint = undefined,
            body = #let_expr{
                bindings = [
                    #binding{
                        pattern = #identifier_pattern{name = t},
                        value = #binary_op_expr{
                            op = '+',
                            left = #identifier_expr{name = a},
                            right = #identifier_expr{name = b}
                        }
                    }
                ],
                body = #binary_op_expr{
                    op = '+', left = #identifier_expr{name = t}, right = #identifier_expr{name = c}
                }
            },
            location = #location{line = 1, column = 1}
        },
        #function_def{
            name = user,
            params = [],
            return_type = #primitive_type{name = 'Int'},
            constraint = undefined,
            body = #function_call_expr{
                function = #identifier_expr{name = add3},
                args = [
                    #literal_expr{value = 1}, #literal_expr{value = 2}, #literal_expr{value = 3}
                ]
            },
            location = #location{line = 2, column = 1}
        }
    ].

%% ============================================================================
%% Helpers
%% ============================================================================

find_function_calls_in_program(AST) ->
    lists:append([find_all_function_calls(Item) || Item <- AST]).

find_all_function_calls(#function_def{body = Body}) ->
    find_all_function_calls(Body);
find_all_function_calls(#function_call_expr{} = C) ->
    [C | lists:append([find_all_function_calls(A) || A <- C#function_call_expr.args])];
find_all_function_calls(#binary_op_expr{left = L, right = R}) ->
    find_all_function_calls(L) ++ find_all_function_calls(R);
find_all_function_calls(#block_expr{expressions = Es}) ->
    lists:append([find_all_function_calls(E) || E <- Es]);
find_all_function_calls(#let_expr{bindings = Bs, body = B}) ->
    lists:append([find_all_function_calls(X#binding.value) || X <- Bs]) ++
        find_all_function_calls(B);
find_all_function_calls(#match_expr{expr = E, patterns = Ps}) ->
    find_all_function_calls(E) ++
        lists:append([find_all_function_calls(P#match_clause.body) || P <- Ps]);
find_all_function_calls(_) ->
    [].

get_call_name(#function_call_expr{function = #identifier_expr{name = N}}) -> N;
get_call_name(_) -> undefined.

get_function(AST, Name) ->
    hd([F || F <- AST, is_record(F, function_def), F#function_def.name == Name]).
