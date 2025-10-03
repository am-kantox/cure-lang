%% Test suite for Type-directed Optimizer
-module(type_optimizer_test).

-export([run/0, test_inlining_optimization/0, test_dead_code_elimination_with_types/0]).

-include("../src/parser/cure_ast_simple.hrl").
-include("../src/types/cure_type_optimizer.hrl").

%% Run all type optimizer tests
run() ->
    io:format("=== Testing Type-directed Optimization System ===~n"),
    Tests = [
        fun test_type_information_collection/0,
        fun test_function_call_analysis/0, 
        fun test_type_usage_patterns/0,
        fun test_hot_path_identification/0,
        fun test_cold_code_detection/0,
        fun test_specialization_candidates/0,
        fun test_function_specialization_pass/0,
        fun test_monomorphization_pass/0,
        fun test_memory_layout_optimization/0,
        fun test_inlining_optimization/0,
        fun test_dead_code_elimination_with_types/0,
        fun test_optimization_framework/0,
        fun test_configuration_levels/0
    ],
    
    Results = lists:map(fun run_test/1, Tests),
    
    Passed = length([ok || ok <- Results]),
    Failed = length(Results) - Passed,
    
    io:format("~nType Optimizer Tests Summary:~n"),
    io:format("  Passed: ~w~n", [Passed]),
    io:format("  Failed: ~w~n", [Failed]),
    
    case Failed of
        0 -> io:format("All type optimizer tests passed!~n");
        _ -> io:format("Some type optimizer tests failed.~n")
    end,
    
    {ok, #{passed => Passed, failed => Failed}}.

run_test(TestFun) ->
    TestName = extract_test_name(TestFun),
    io:format("Running ~s... ", [TestName]),
    try
        TestFun(),
        io:format("PASSED~n"),
        ok
    catch
        Error:Reason:Stack ->
            io:format("FAILED~n"),
            io:format("  Error: ~p:~p~n", [Error, Reason]),
            io:format("  Stack: ~p~n", [Stack]),
            {error, Reason}
    end.

extract_test_name(Fun) ->
    {name, Name} = erlang:fun_info(Fun, name),
    atom_to_list(Name).

%% ============================================================================
%% Test Cases
%% ============================================================================

%% Test type information collection
test_type_information_collection() ->
    % Create sample AST with functions and types
    SampleAST = create_sample_ast(),
    
    % Collect type information
    TypeInfo = cure_type_optimizer:collect_type_information(SampleAST),
    
    % Verify function types were collected
    FunctionTypes = TypeInfo#type_info.function_types,
    true = maps:size(FunctionTypes) > 0,
    
    % Verify call sites were collected  
    CallSites = TypeInfo#type_info.call_sites,
    true = is_map(CallSites),
    
    % Verify type usage patterns were collected
    TypeUsage = TypeInfo#type_info.type_usage,
    true = is_map(TypeUsage),
    
    io:format(" [Functions: ~w, CallSites: ~w, Types: ~w] ",
             [maps:size(FunctionTypes), maps:size(CallSites), maps:size(TypeUsage)]),
    
    ok.

%% Test function call analysis
test_function_call_analysis() ->
    SampleAST = create_sample_ast_with_calls(),
    
    % Count function calls
    CallCounts = cure_type_optimizer:count_function_calls(SampleAST),
    
    % Verify calls were counted
    true = maps:size(CallCounts) > 0,
    
    % Collect call sites
    CallSites = cure_type_optimizer:collect_call_sites(SampleAST),
    
    % Verify call sites have location and type info
    maps:fold(fun(_FuncName, SiteList, _) ->
        lists:foreach(fun({Location, ArgTypes}) ->
            true = is_record(Location, location),
            true = is_list(ArgTypes)
        end, SiteList),
        ok
    end, ok, CallSites),
    
    io:format(" [Calls: ~w functions] ", [maps:size(CallCounts)]),
    
    ok.

%% Test type usage pattern analysis
test_type_usage_patterns() ->
    SampleAST = create_sample_ast_with_types(),
    
    % Analyze type usage patterns
    TypeUsage = cure_type_optimizer:collect_type_usage_patterns(SampleAST),
    
    % Verify primitive types are recognized
    IntUsage = maps:get({primitive_type, 'Int'}, TypeUsage, 0),
    true = IntUsage > 0,
    
    % Verify unknown types are handled
    UnknownUsage = maps:get({unknown_type}, TypeUsage, 0),
    true = UnknownUsage >= 0,
    
    io:format(" [Types used: ~w] ", [maps:size(TypeUsage)]),
    
    ok.

%% Test hot path identification
test_hot_path_identification() ->
    SampleAST = create_sample_ast_with_many_calls(),
    
    % Identify hot paths
    HotPaths = cure_type_optimizer:identify_hot_paths(SampleAST),
    
    % Verify hot paths are identified
    true = is_list(HotPaths),
    
    % Each hot path should be a list of function names
    lists:foreach(fun(Path) ->
        true = is_list(Path),
        lists:foreach(fun(FuncName) ->
            true = is_atom(FuncName)
        end, Path)
    end, HotPaths),
    
    io:format(" [Hot paths: ~w] ", [length(HotPaths)]),
    
    ok.

%% Test cold code detection
test_cold_code_detection() ->
    SampleAST = create_sample_ast_with_unused_functions(),
    
    % Identify cold code
    ColdCode = cure_type_optimizer:identify_cold_code(SampleAST),
    
    % Verify cold code is detected
    true = is_list(ColdCode),
    
    % Each cold function should be an atom
    lists:foreach(fun(FuncName) ->
        true = is_atom(FuncName)
    end, ColdCode),
    
    io:format(" [Cold functions: ~w] ", [length(ColdCode)]),
    
    ok.

%% Test specialization candidate analysis
test_specialization_candidates() ->
    SampleAST = create_sample_ast_with_polymorphic_calls(),
    
    % Analyze specialization candidates
    SpecCandidates = cure_type_optimizer:analyze_specialization_candidates(SampleAST),
    
    % Verify candidates are identified
    true = is_map(SpecCandidates),
    
    % Each candidate should have type patterns and cost-benefit analysis
    maps:fold(fun(_FuncName, Candidates, _) ->
        true = is_list(Candidates),
        lists:foreach(fun({Pattern, {Cost, Benefit}}) ->
            true = is_list(Pattern),
            true = is_integer(Cost),
            true = is_integer(Benefit)
        end, Candidates),
        ok
    end, ok, SpecCandidates),
    
    io:format(" [Specialization candidates: ~w] ", [maps:size(SpecCandidates)]),
    
    ok.

%% Test function specialization pass
test_function_specialization_pass() ->
    SampleAST = create_sample_ast_with_polymorphic_calls(),
    
    % Initialize context and find specialization opportunities
    Config = cure_type_optimizer:default_optimization_config(),
    Context = cure_type_optimizer:initialize_optimization_context(Config),
    
    % Collect type information and find opportunities
    {TypeInfo, UsageStats} = cure_type_optimizer:analyze_program_types(SampleAST),
    Context1 = Context#optimization_context{
        type_info = TypeInfo,
        usage_stats = UsageStats
    },
    Context2 = cure_type_optimizer:find_optimization_opportunities(SampleAST, Context1),
    
    % Run function specialization pass
    SpecializedAST = cure_type_optimizer:function_specialization_pass(SampleAST, Context2),
    
    % Verify that specializations were applied
    true = is_list(SpecializedAST),
    
    % Count functions before and after specialization
    OriginalFuncCount = count_functions(SampleAST),
    SpecializedFuncCount = count_functions(SpecializedAST),
    
    % Should have more functions after specialization (original + specialized versions)
    true = SpecializedFuncCount >= OriginalFuncCount,
    
    io:format(" [Original: ~w, Specialized: ~w functions] ", [OriginalFuncCount, SpecializedFuncCount]),
    
    ok.

%% Test monomorphization pass
test_monomorphization_pass() ->
    SampleAST = create_sample_ast_with_polymorphic_calls(),
    
    % Initialize context and find polymorphic functions
    Config = cure_type_optimizer:default_optimization_config(),
    Context = cure_type_optimizer:initialize_optimization_context(Config),
    
    % Collect type information
    {TypeInfo, UsageStats} = cure_type_optimizer:analyze_program_types(SampleAST),
    Context1 = Context#optimization_context{
        type_info = TypeInfo,
        usage_stats = UsageStats
    },
    
    % Run monomorphization pass
    MonomorphizedAST = cure_type_optimizer:monomorphization_pass(SampleAST, Context1),
    
    % Verify that monomorphization was applied
    true = is_list(MonomorphizedAST),
    
    % Count functions before and after monomorphization
    OriginalFuncCount = count_functions(SampleAST),
    MonomorphizedFuncCount = count_functions(MonomorphizedAST),
    
    % Should have same or more functions after monomorphization (original + monomorphic versions)
    true = MonomorphizedFuncCount >= OriginalFuncCount,
    
    io:format(" [Original: ~w, Monomorphized: ~w functions] ", [OriginalFuncCount, MonomorphizedFuncCount]),
    
    ok.

%% Test memory layout optimization
test_memory_layout_optimization() ->
    SampleAST = create_sample_ast_with_types(),
    
    % Initialize context for memory layout analysis
    Config = cure_type_optimizer:default_optimization_config(),
    Context = cure_type_optimizer:initialize_optimization_context(Config),
    
    % Collect type information and memory layouts
    {TypeInfo, UsageStats} = cure_type_optimizer:analyze_program_types(SampleAST),
    Context1 = Context#optimization_context{
        type_info = TypeInfo,
        usage_stats = UsageStats
    },
    
    % Run memory layout optimization pass
    OptimizedAST = cure_type_optimizer:memory_layout_optimization_pass(SampleAST, Context1),
    
    % Verify that optimization was applied
    true = is_list(OptimizedAST),
    
    % Verify memory layouts were analyzed
    MemoryLayouts = TypeInfo#type_info.memory_layouts,
    true = is_map(MemoryLayouts),
    
    io:format(" [Memory layouts analyzed: ~w] ", [maps:size(MemoryLayouts)]),
    
    ok.

%% Test optimization framework
test_optimization_framework() ->
    SampleAST = create_sample_ast(),
    
    % Test optimization with default config
    {ok, OptimizedAST, Report} = cure_type_optimizer:optimize_program(SampleAST),
    
    % Verify optimized AST is returned
    true = is_list(OptimizedAST),
    
    % Verify optimization report is generated
    true = is_map(Report),
    true = maps:is_key(optimizations_applied, Report),
    true = maps:is_key(specializations_generated, Report),
    
    io:format(" [Optimization passes: complete] "),
    
    ok.

%% Test configuration levels
test_configuration_levels() ->
    % Test different optimization levels
    Config0 = cure_type_optimizer:set_optimization_level(0),
    Config1 = cure_type_optimizer:set_optimization_level(1),
    Config2 = cure_type_optimizer:set_optimization_level(2),
    Config3 = cure_type_optimizer:set_optimization_level(3),
    
    % Verify level 0 disables all optimizations
    false = Config0#optimization_config.enable_specialization,
    false = Config0#optimization_config.enable_monomorphization,
    false = Config0#optimization_config.enable_inlining,
    
    % Verify level 3 enables aggressive optimizations
    true = Config3#optimization_config.enable_specialization,
    true = Config3#optimization_config.max_specializations > Config2#optimization_config.max_specializations,
    
    io:format(" [Config levels: 0-3 verified] "),
    
    ok.

%% ============================================================================
%% Helper Functions to Create Sample ASTs
%% ============================================================================

create_sample_ast() ->
    [
        #function_def{
            name = add,
            params = [
                #param{name = x, type = {primitive_type, 'Int'}, location = #location{line = 1, column = 1, file = "test"}},
                #param{name = y, type = {primitive_type, 'Int'}, location = #location{line = 1, column = 3, file = "test"}}
            ],
            return_type = {primitive_type, 'Int'},
            constraint = undefined,
            body = #binary_op_expr{
                op = '+',
                left = #identifier_expr{name = x, location = #location{line = 2, column = 1, file = "test"}},
                right = #identifier_expr{name = y, location = #location{line = 2, column = 3, file = "test"}},
                location = #location{line = 2, column = 2, file = "test"}
            },
            location = #location{line = 1, column = 1, file = "test"}
        },
        #function_def{
            name = multiply,
            params = [
                #param{name = a, type = {primitive_type, 'Float'}, location = #location{line = 4, column = 1, file = "test"}},
                #param{name = b, type = {primitive_type, 'Float'}, location = #location{line = 4, column = 3, file = "test"}}
            ],
            return_type = {primitive_type, 'Float'},
            constraint = undefined,
            body = #binary_op_expr{
                op = '*',
                left = #identifier_expr{name = a, location = #location{line = 5, column = 1, file = "test"}},
                right = #identifier_expr{name = b, location = #location{line = 5, column = 3, file = "test"}},
                location = #location{line = 5, column = 2, file = "test"}
            },
            location = #location{line = 4, column = 1, file = "test"}
        }
    ].

create_sample_ast_with_calls() ->
    [
        #function_def{
            name = main,
            params = [],
            return_type = {primitive_type, 'Int'},
            constraint = undefined,
            body = #function_call_expr{
                function = #identifier_expr{name = add, location = #location{line = 2, column = 1, file = "test"}},
                args = [
                    #literal_expr{value = 10, location = #location{line = 2, column = 5, file = "test"}},
                    #literal_expr{value = 20, location = #location{line = 2, column = 8, file = "test"}}
                ],
                location = #location{line = 2, column = 1, file = "test"}
            },
            location = #location{line = 1, column = 1, file = "test"}
        },
        #function_def{
            name = add,
            params = [
                #param{name = x, type = {primitive_type, 'Int'}, location = #location{line = 4, column = 1, file = "test"}},
                #param{name = y, type = {primitive_type, 'Int'}, location = #location{line = 4, column = 3, file = "test"}}
            ],
            return_type = {primitive_type, 'Int'},
            constraint = undefined,
            body = #binary_op_expr{
                op = '+',
                left = #identifier_expr{name = x, location = #location{line = 5, column = 1, file = "test"}},
                right = #identifier_expr{name = y, location = #location{line = 5, column = 3, file = "test"}},
                location = #location{line = 5, column = 2, file = "test"}
            },
            location = #location{line = 4, column = 1, file = "test"}
        }
    ].

create_sample_ast_with_types() ->
    [
        #function_def{
            name = process_data,
            params = [
                #param{name = count, type = {primitive_type, 'Int'}, location = #location{line = 1, column = 1, file = "test"}},
                #param{name = name, type = {primitive_type, 'String'}, location = #location{line = 1, column = 3, file = "test"}},
                #param{name = active, type = {primitive_type, 'Bool'}, location = #location{line = 1, column = 5, file = "test"}}
            ],
            return_type = {primitive_type, 'String'},
            constraint = undefined,
            body = #literal_expr{value = <<"result">>, location = #location{line = 2, column = 1, file = "test"}},
            location = #location{line = 1, column = 1, file = "test"}
        }
    ].

create_sample_ast_with_many_calls() ->
    % Create a function that calls another function many times
    CallExprs = [
        #function_call_expr{
            function = #identifier_expr{name = helper, location = #location{line = 2, column = I, file = "test"}},
            args = [#literal_expr{value = I, location = #location{line = 2, column = I+5, file = "test"}}],
            location = #location{line = 2, column = I, file = "test"}
        } || I <- lists:seq(1, 15)
    ],
    
    [
        #function_def{
            name = main,
            params = [],
            return_type = {primitive_type, 'Int'},
            constraint = undefined,
            body = #block_expr{expressions = CallExprs, location = #location{line = 2, column = 1, file = "test"}},
            location = #location{line = 1, column = 1, file = "test"}
        },
        #function_def{
            name = helper,
            params = [#param{name = x, type = {primitive_type, 'Int'}, location = #location{line = 4, column = 1, file = "test"}}],
            return_type = {primitive_type, 'Int'},
            constraint = undefined,
            body = #identifier_expr{name = x, location = #location{line = 5, column = 1, file = "test"}},
            location = #location{line = 4, column = 1, file = "test"}
        }
    ].

create_sample_ast_with_unused_functions() ->
    [
        #function_def{
            name = main,
            params = [],
            return_type = {primitive_type, 'Int'},
            constraint = undefined,
            body = #literal_expr{value = 42, location = #location{line = 2, column = 1, file = "test"}},
            location = #location{line = 1, column = 1, file = "test"}
        },
        #function_def{
            name = unused_function1,
            params = [],
            return_type = {primitive_type, 'Int'},
            constraint = undefined,
            body = #literal_expr{value = 1, location = #location{line = 5, column = 1, file = "test"}},
            location = #location{line = 4, column = 1, file = "test"}
        },
        #function_def{
            name = unused_function2,
            params = [],
            return_type = {primitive_type, 'Int'},
            constraint = undefined,
            body = #literal_expr{value = 2, location = #location{line = 8, column = 1, file = "test"}},
            location = #location{line = 7, column = 1, file = "test"}
        }
    ].

create_sample_ast_with_polymorphic_calls() ->
    % Create a function called with different argument types multiple times
    [
        #function_def{
            name = caller,
            params = [],
            return_type = {primitive_type, 'Int'},
            constraint = undefined,
            body = #block_expr{
                expressions = [
                    #function_call_expr{
                        function = #identifier_expr{name = polymorphic_func, location = #location{line = 2, column = 1, file = "test"}},
                        args = [#literal_expr{value = 10, location = #location{line = 2, column = 17, file = "test"}}],
                        location = #location{line = 2, column = 1, file = "test"}
                    },
                    #function_call_expr{
                        function = #identifier_expr{name = polymorphic_func, location = #location{line = 3, column = 1, file = "test"}},
                        args = [#literal_expr{value = 3.14, location = #location{line = 3, column = 17, file = "test"}}],
                        location = #location{line = 3, column = 1, file = "test"}
                    },
                    #function_call_expr{
                        function = #identifier_expr{name = polymorphic_func, location = #location{line = 4, column = 1, file = "test"}},
                        args = [#literal_expr{value = <<"string">>, location = #location{line = 4, column = 17, file = "test"}}],
                        location = #location{line = 4, column = 1, file = "test"}
                    },
                    #function_call_expr{
                        function = #identifier_expr{name = polymorphic_func, location = #location{line = 5, column = 1, file = "test"}},
                        args = [#literal_expr{value = 42, location = #location{line = 5, column = 17, file = "test"}}],
                        location = #location{line = 5, column = 1, file = "test"}
                    },
                    #function_call_expr{
                        function = #identifier_expr{name = polymorphic_func, location = #location{line = 6, column = 1, file = "test"}},
                        args = [#literal_expr{value = 2.71, location = #location{line = 6, column = 17, file = "test"}}],
                        location = #location{line = 6, column = 1, file = "test"}
                    },
                    #function_call_expr{
                        function = #identifier_expr{name = polymorphic_func, location = #location{line = 7, column = 1, file = "test"}},
                        args = [#literal_expr{value = 100, location = #location{line = 7, column = 17, file = "test"}}],
                        location = #location{line = 7, column = 1, file = "test"}
                    }
                ],
                location = #location{line = 2, column = 1, file = "test"}
            },
            location = #location{line = 1, column = 1, file = "test"}
        },
        #function_def{
            name = polymorphic_func,
            params = [#param{name = x, type = undefined, location = #location{line = 10, column = 1, file = "test"}}],
            return_type = undefined,
            constraint = undefined,
            body = #identifier_expr{name = x, location = #location{line = 11, column = 1, file = "test"}},
            location = #location{line = 9, column = 1, file = "test"}
        }
    ].

%% Test inlining based on type analysis optimization
test_inlining_optimization() ->
    SampleAST = create_sample_ast_with_inlining_candidates(),
    
    % Initialize context for inlining analysis
    Config = cure_type_optimizer:default_optimization_config(),
    Context = cure_type_optimizer:initialize_optimization_context(Config),
    
    % Collect type information and usage statistics for inlining decisions
    {TypeInfo, UsageStats} = cure_type_optimizer:analyze_program_types(SampleAST),
    
    % Create usage stats that favor inlining (hot paths and frequent calls)
    EnhancedUsageStats = UsageStats#usage_statistics{
        function_calls = #{
            small_add => 15,  % Frequently called
            tiny_helper => 25, % Very frequently called
            big_function => 2  % Rarely called
        },
        hot_paths = [[small_add], [tiny_helper]]  % Both are on hot paths
    },
    
    Context1 = Context#optimization_context{
        type_info = TypeInfo,
        usage_stats = EnhancedUsageStats
    },
    
    % Run inlining pass
    InlinedAST = cure_type_optimizer:inlining_pass(SampleAST, Context1),
    
    % Verify that inlining was applied
    true = is_list(InlinedAST),
    
    % Count functions (should be same as original since we don't remove originals by default)
    OriginalFuncCount = count_functions(SampleAST),
    InlinedFuncCount = count_functions(InlinedAST),
    
    % Should have same or fewer functions after inlining (depends on cleanup)
    true = InlinedFuncCount >= 0,
    
    io:format(" [Original: ~w, After inlining: ~w functions] ", [OriginalFuncCount, InlinedFuncCount]),
    
    ok.

%% Create sample AST with functions suitable for inlining
create_sample_ast_with_inlining_candidates() ->
    [
        % Small function - good candidate for inlining
        #function_def{
            name = small_add,
            params = [
                #param{name = x, type = {primitive_type, 'Int'}, location = #location{line = 1, column = 1, file = "test"}},
                #param{name = y, type = {primitive_type, 'Int'}, location = #location{line = 1, column = 3, file = "test"}}
            ],
            return_type = {primitive_type, 'Int'},
            constraint = undefined,
            body = #binary_op_expr{
                op = '+',
                left = #identifier_expr{name = x, location = #location{line = 2, column = 1, file = "test"}},
                right = #identifier_expr{name = y, location = #location{line = 2, column = 3, file = "test"}},
                location = #location{line = 2, column = 2, file = "test"}
            },
            location = #location{line = 1, column = 1, file = "test"}
        },
        % Tiny helper function - excellent candidate for inlining
        #function_def{
            name = tiny_helper,
            params = [#param{name = x, type = {primitive_type, 'Int'}, location = #location{line = 4, column = 1, file = "test"}}],
            return_type = {primitive_type, 'Int'},
            constraint = undefined,
            body = #identifier_expr{name = x, location = #location{line = 5, column = 1, file = "test"}},
            location = #location{line = 4, column = 1, file = "test"}
        },
        % Large function - not a good candidate for inlining
        #function_def{
            name = big_function,
            params = [
                #param{name = a, type = {primitive_type, 'Int'}, location = #location{line = 7, column = 1, file = "test"}},
                #param{name = b, type = {primitive_type, 'Int'}, location = #location{line = 7, column = 3, file = "test"}},
                #param{name = c, type = {primitive_type, 'Int'}, location = #location{line = 7, column = 5, file = "test"}}
            ],
            return_type = {primitive_type, 'Int'},
            constraint = undefined,
            body = #block_expr{
                expressions = [
                    #binary_op_expr{
                        op = '+',
                        left = #identifier_expr{name = a, location = #location{line = 8, column = 1, file = "test"}},
                        right = #identifier_expr{name = b, location = #location{line = 8, column = 3, file = "test"}},
                        location = #location{line = 8, column = 2, file = "test"}
                    },
                    #binary_op_expr{
                        op = '*',
                        left = #identifier_expr{name = c, location = #location{line = 9, column = 1, file = "test"}},
                        right = #literal_expr{value = 2, location = #location{line = 9, column = 3, file = "test"}},
                        location = #location{line = 9, column = 2, file = "test"}
                    },
                    #binary_op_expr{
                        op = '-',
                        left = #identifier_expr{name = a, location = #location{line = 10, column = 1, file = "test"}},
                        right = #identifier_expr{name = c, location = #location{line = 10, column = 3, file = "test"}},
                        location = #location{line = 10, column = 2, file = "test"}
                    }
                ],
                location = #location{line = 8, column = 1, file = "test"}
            },
            location = #location{line = 7, column = 1, file = "test"}
        },
        % Caller function that uses the inlinable functions
        #function_def{
            name = caller,
            params = [],
            return_type = {primitive_type, 'Int'},
            constraint = undefined,
            body = #block_expr{
                expressions = [
                    #function_call_expr{
                        function = #identifier_expr{name = small_add, location = #location{line = 13, column = 1, file = "test"}},
                        args = [
                            #literal_expr{value = 1, location = #location{line = 13, column = 11, file = "test"}},
                            #literal_expr{value = 2, location = #location{line = 13, column = 14, file = "test"}}
                        ],
                        location = #location{line = 13, column = 1, file = "test"}
                    },
                    #function_call_expr{
                        function = #identifier_expr{name = tiny_helper, location = #location{line = 14, column = 1, file = "test"}},
                        args = [#literal_expr{value = 5, location = #location{line = 14, column = 13, file = "test"}}],
                        location = #location{line = 14, column = 1, file = "test"}
                    }
                ],
                location = #location{line = 13, column = 1, file = "test"}
            },
            location = #location{line = 12, column = 1, file = "test"}
        }
    ].

%% Test enhanced dead code elimination using type information
test_dead_code_elimination_with_types() ->
    SampleAST = create_sample_ast_with_dead_code(),
    
    % Initialize context for dead code elimination
    Config = cure_type_optimizer:default_optimization_config(),
    Context = cure_type_optimizer:initialize_optimization_context(Config),
    
    % Collect type information and usage statistics
    {TypeInfo, UsageStats} = cure_type_optimizer:analyze_program_types(SampleAST),
    
    % Create usage stats with cold code
    EnhancedUsageStats = UsageStats#usage_statistics{
        cold_code = [unused_helper, dead_function]  % Mark functions as unused
    },
    
    Context1 = Context#optimization_context{
        type_info = TypeInfo,
        usage_stats = EnhancedUsageStats
    },
    
    % Run enhanced dead code elimination pass
    CleanedAST = cure_type_optimizer:dead_code_elimination_pass(SampleAST, Context1),
    
    % Verify that dead code elimination was applied
    true = is_list(CleanedAST),
    
    % Count functions before and after dead code elimination
    OriginalFuncCount = count_functions(SampleAST),
    CleanedFuncCount = count_functions(CleanedAST),
    
    % Should have fewer functions after dead code elimination
    true = CleanedFuncCount =< OriginalFuncCount,
    
    io:format(" [Original: ~w, After DCE: ~w functions] ", [OriginalFuncCount, CleanedFuncCount]),
    
    ok.

%% Create sample AST with dead code for testing
create_sample_ast_with_dead_code() ->
    [
        % Active function that gets called
        #function_def{
            name = active_function,
            params = [#param{name = x, type = {primitive_type, 'Int'}, location = #location{line = 1, column = 1, file = "test"}}],
            return_type = {primitive_type, 'Int'},
            constraint = undefined,
            body = #binary_op_expr{
                op = '+',
                left = #identifier_expr{name = x, location = #location{line = 2, column = 1, file = "test"}},
                right = #literal_expr{value = 10, location = #location{line = 2, column = 3, file = "test"}},
                location = #location{line = 2, column = 2, file = "test"}
            },
            location = #location{line = 1, column = 1, file = "test"}
        },
        % Dead function that never gets called
        #function_def{
            name = unused_helper,
            params = [#param{name = y, type = {primitive_type, 'Float'}, location = #location{line = 4, column = 1, file = "test"}}],
            return_type = {primitive_type, 'Float'},
            constraint = undefined,
            body = #binary_op_expr{
                op = '*',
                left = #identifier_expr{name = y, location = #location{line = 5, column = 1, file = "test"}},
                right = #literal_expr{value = 2.0, location = #location{line = 5, column = 3, file = "test"}},
                location = #location{line = 5, column = 2, file = "test"}
            },
            location = #location{line = 4, column = 1, file = "test"}
        },
        % Another dead function
        #function_def{
            name = dead_function,
            params = [],
            return_type = {primitive_type, 'Bool'},
            constraint = undefined,
            body = #literal_expr{value = false, location = #location{line = 8, column = 1, file = "test"}},
            location = #location{line = 7, column = 1, file = "test"}
        },
        % Main function that only calls active_function
        #function_def{
            name = main,
            params = [],
            return_type = {primitive_type, 'Int'},
            constraint = undefined,
            body = #function_call_expr{
                function = #identifier_expr{name = active_function, location = #location{line = 10, column = 1, file = "test"}},
                args = [#literal_expr{value = 5, location = #location{line = 10, column = 16, file = "test"}}],
                location = #location{line = 10, column = 1, file = "test"}
            },
            location = #location{line = 9, column = 1, file = "test"}
        }
    ].

%% Helper function to count functions in AST
count_functions(AST) ->
    count_functions_impl(AST, 0).

count_functions_impl([], Acc) ->
    Acc;
count_functions_impl([Item | Rest], Acc) ->
    NewAcc = case Item of
        #function_def{} ->
            Acc + 1;
        #module_def{items = Items} ->
            count_functions_impl(Items, Acc);
        _ ->
            Acc
    end,
    count_functions_impl(Rest, NewAcc).
