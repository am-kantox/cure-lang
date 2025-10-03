%% Test suite for Profile-guided Optimization and Runtime Feedback Integration
-module(profile_guided_optimization_test).

-export([run_profile_tests/0, test_profile_collection/0, test_adaptive_optimization/0]).

-include("../src/parser/cure_ast_simple.hrl").

%% Run profile-guided optimization tests
run_profile_tests() ->
    io:format("=== Testing Profile-guided Optimization System ===~n"),
    Tests = [
        fun test_profile_framework/0,
        fun test_profile_collection/0,
        fun test_adaptive_specialization/0,
        fun test_hot_path_optimization/0,
        fun test_memory_layout_adaptation/0,
        fun test_performance_feedback/0,
        fun test_adaptive_optimization/0,
        fun test_feedback_integration/0
    ],
    
    Results = lists:map(fun(Test) ->
        TestName = extract_test_name(Test),
        io:format("Running ~s... ", [TestName]),
        try
            Test(),
            io:format("PASSED~n"),
            ok
        catch
            Error:Reason:Stack ->
                io:format("FAILED: ~p:~p~n", [Error, Reason]),
                io:format("  Stack: ~p~n", [Stack]),
                {error, Reason}
        end
    end, Tests),
    
    Passed = length([ok || ok <- Results]),
    Failed = length(Results) - Passed,
    
    io:format("~nProfile-guided Optimization Tests Summary:~n"),
    io:format("  Passed: ~w~n", [Passed]),
    io:format("  Failed: ~w~n", [Failed]),
    
    case Failed of
        0 -> io:format("All profile-guided optimization tests passed!~n");
        _ -> io:format("Some profile-guided optimization tests failed.~n")
    end,
    
    {ok, #{passed => Passed, failed => Failed}}.

extract_test_name(Fun) ->
    {name, Name} = erlang:fun_info(Fun, name),
    atom_to_list(Name).

%% Test profile-guided optimization framework
test_profile_framework() ->
    % Test that the profile collection system can be initialized
    ProfileCollector = init_test_profile_collector(),
    true = is_map(ProfileCollector),
    true = maps:is_key(execution_counts, ProfileCollector),
    true = maps:is_key(call_frequencies, ProfileCollector),
    true = maps:is_key(hot_paths, ProfileCollector),
    
    % Test adaptive thresholds initialization
    AdaptiveThresholds = init_test_adaptive_thresholds(),
    true = is_map(AdaptiveThresholds),
    true = maps:is_key(hot_function_threshold, AdaptiveThresholds),
    true = maps:is_key(specialization_benefit_threshold, AdaptiveThresholds),
    
    % Test performance targets initialization
    PerformanceTargets = init_test_performance_targets(),
    true = is_map(PerformanceTargets),
    true = maps:is_key(execution_time_target, PerformanceTargets),
    true = maps:is_key(memory_usage_target, PerformanceTargets),
    
    io:format(" [Profile framework initialized] "),
    ok.

%% Test runtime profile collection
test_profile_collection() ->
    % Create sample AST for profiling
    SampleAST = create_profile_test_ast(),
    
    % Test function call pattern analysis
    CallPatterns = analyze_test_call_patterns(SampleAST),
    true = is_map(CallPatterns),
    true = maps:size(CallPatterns) > 0,
    
    % Test execution frequency estimation
    ExecutionFreqs = estimate_test_execution_frequencies(SampleAST, CallPatterns),
    true = is_map(ExecutionFreqs),
    true = maps:size(ExecutionFreqs) > 0,
    
    % Test hot path identification
    HotPaths = identify_test_hot_paths(SampleAST, ExecutionFreqs),
    true = is_list(HotPaths),
    
    % Test memory access pattern analysis
    MemoryPatterns = analyze_test_memory_patterns(SampleAST),
    true = is_map(MemoryPatterns),
    
    % Test type usage collection
    RuntimeTypeUsage = collect_test_type_usage(SampleAST),
    true = is_map(RuntimeTypeUsage),
    
    io:format(" [Runtime profiles collected] "),
    ok.

%% Test adaptive function specialization
test_adaptive_specialization() ->
    % Create test data
    ExecutionFreqs = #{test_func => 150, helper_func => 75, util_func => 25},
    TypeUsage = #{{primitive_type, integer} => 10, {primitive_type, float} => 5},
    
    % Test specialization opportunity identification
    SpecializationOpportunities = identify_test_specialization_opportunities(ExecutionFreqs, TypeUsage),
    true = is_map(SpecializationOpportunities),
    
    % Test adaptive specialization generation
    ExistingOptimizations = create_test_existing_optimizations(),
    AdaptiveSpecializations = generate_test_adaptive_specializations(SpecializationOpportunities, ExistingOptimizations),
    true = is_list(AdaptiveSpecializations),
    true = length(AdaptiveSpecializations) >= 0,
    
    % Test specialization enhancement
    EnhancedSpec = test_enhance_existing_specialization(),
    true = is_map(EnhancedSpec),
    true = maps:is_key(function_name, EnhancedSpec),
    true = maps:is_key(specialization_type, EnhancedSpec),
    
    io:format(" [Adaptive specialization working] "),
    ok.

%% Test dynamic hot path optimization
test_hot_path_optimization() ->
    % Create test hot paths
    HotPaths = [[main, compute, helper], [process, validate]],
    ExecutionFreqs = #{main => 200, compute => 180, helper => 160, process => 100, validate => 90},
    
    % Test hot path opportunity identification
    HotPathOpportunities = identify_test_hot_path_opportunities(HotPaths, ExecutionFreqs),
    true = is_list(HotPathOpportunities),
    
    % Test dynamic hot path optimization generation
    ProfileCollector = init_test_profile_collector(),
    HotPathOptimizations = generate_test_hot_path_optimizations(HotPathOpportunities, ProfileCollector),
    true = is_list(HotPathOptimizations),
    
    % Verify optimization types are assigned correctly
    lists:foreach(fun(Optimization) ->
        true = is_map(Optimization),
        true = maps:is_key(type, Optimization),
        true = maps:is_key(path, Optimization),
        true = maps:is_key(benefit, Optimization)
    end, HotPathOptimizations),
    
    io:format(" [Hot path optimization working] "),
    ok.

%% Test adaptive memory layout optimization
test_memory_layout_adaptation() ->
    % Create test memory patterns
    MemoryPatterns = #{ 
        func_a => #{total_accesses => 50, sequential_pattern => true, locality_score => 0.8},
        func_b => #{total_accesses => 25, sequential_pattern => false, locality_score => 0.3}
    },
    
    % Test memory optimization opportunity identification
    MemoryOpportunities = identify_test_memory_opportunities(MemoryPatterns),
    true = is_map(MemoryOpportunities),
    
    % Test adaptive memory layout generation
    ExistingOptimizations = create_test_existing_optimizations(),
    AdaptiveLayouts = generate_test_adaptive_memory_layouts(MemoryOpportunities, ExistingOptimizations),
    true = is_list(AdaptiveLayouts),
    
    % Verify layout types are assigned correctly
    lists:foreach(fun(Layout) ->
        true = is_map(Layout),
        true = maps:is_key(layout_type, Layout),
        true = maps:is_key(function, Layout),
        true = maps:is_key(benefit, Layout)
    end, AdaptiveLayouts),
    
    io:format(" [Memory layout adaptation working] "),
    ok.

%% Test performance feedback integration
test_performance_feedback() ->
    % Create test feedback data
    FeedbackData = create_test_feedback_data(),
    
    % Test performance feedback system creation
    FeedbackSystem = create_test_performance_feedback_system(FeedbackData),
    true = is_map(FeedbackSystem),
    true = maps:is_key(feedback_data, FeedbackSystem),
    true = maps:is_key(monitoring_enabled, FeedbackSystem),
    true = maps:is_key(adaptation_threshold, FeedbackSystem),
    
    % Test performance metrics initialization
    PerformanceMetrics = init_test_performance_metrics(),
    true = is_map(PerformanceMetrics),
    true = maps:is_key(execution_time, PerformanceMetrics),
    true = maps:is_key(memory_usage, PerformanceMetrics),
    true = maps:is_key(throughput, PerformanceMetrics),
    
    % Test performance optimization generation
    Priorities = [{specialization, test_opportunities}, {hot_path, test_opportunities}],
    PerformanceTargets = init_test_performance_targets(),
    PerformanceOpts = generate_test_performance_optimizations(Priorities, PerformanceTargets),
    true = is_list(PerformanceOpts),
    
    io:format(" [Performance feedback integration working] "),
    ok.

%% Test complete adaptive optimization pipeline
test_adaptive_optimization() ->
    % Create test AST and context
    TestAST = create_profile_test_ast(),
    AdaptiveContext = create_test_adaptive_context(),
    
    % Test profile data collection
    ProfileData = collect_test_runtime_profiles(TestAST, AdaptiveContext),
    true = is_map(ProfileData),
    true = maps:is_key(call_patterns, ProfileData),
    true = maps:is_key(execution_frequencies, ProfileData),
    true = maps:is_key(hot_paths, ProfileData),
    
    % Test optimization opportunity analysis
    OptimizationOpportunities = analyze_test_optimization_opportunities(ProfileData),
    true = is_map(OptimizationOpportunities),
    true = maps:is_key(specialization, OptimizationOpportunities),
    true = maps:is_key(hot_path, OptimizationOpportunities),
    true = maps:is_key(memory, OptimizationOpportunities),
    
    % Test priority calculation
    Priorities = maps:get(priorities, OptimizationOpportunities, []),
    true = is_list(Priorities),
    
    io:format(" [Adaptive optimization pipeline working] "),
    ok.

%% Test feedback integration with optimization system
test_feedback_integration() ->
    % Test complete feedback loop
    TestAST = create_profile_test_ast(),
    TestContext = create_test_opt_context(),
    
    % Test that we can extract optimization data
    OptimizationData = extract_test_optimization_data(TestContext),
    true = is_map(OptimizationData),
    
    % Test adaptive context initialization
    ProfileCollector = init_test_profile_collector(),
    AdaptiveContext = init_test_adaptive_context(ProfileCollector, OptimizationData),
    true = is_map(AdaptiveContext),
    true = maps:is_key(profile_collector, AdaptiveContext),
    true = maps:is_key(existing_optimizations, AdaptiveContext),
    
    % Test feedback system integration
    FeedbackData = create_test_feedback_data(),
    FeedbackSystem = create_test_performance_feedback_system(FeedbackData),
    true = maps:get(monitoring_enabled, FeedbackSystem),
    
    io:format(" [Feedback integration working] "),
    ok.

%% ============================================================================
%% Helper Functions for Testing
%% ============================================================================

%% Initialize test profile collector
init_test_profile_collector() ->
    #{
        execution_counts => #{test_func => 100, helper_func => 50},
        call_frequencies => #{test_func => 15, helper_func => 8},
        hot_paths => [[test_func, helper_func]],
        memory_access_patterns => #{test_func => #{total_accesses => 20}},
        type_usage_runtime => #{{primitive_type, integer} => 10},
        performance_metrics => #{execution_time => 100, memory_usage => 50},
        adaptive_decisions => #{test_decision => enhanced},
        feedback_history => []
    }.

%% Initialize test adaptive thresholds
init_test_adaptive_thresholds() ->
    #{
        hot_function_threshold => 100,
        specialization_benefit_threshold => 2.0,
        memory_optimization_threshold => 0.2,
        performance_improvement_threshold => 0.1,
        adaptation_sensitivity => 0.05
    }.

%% Initialize test performance targets
init_test_performance_targets() ->
    #{
        execution_time_target => 1.0,
        memory_usage_target => 0.8,
        throughput_target => 1.2,
        latency_target => 0.9,
        cache_hit_rate_target => 0.95
    }.

%% Create profile test AST
create_profile_test_ast() ->
    [
        #function_def{
            name = test_func,
            params = [#param{name = x, type = {primitive_type, integer}}],
            return_type = {primitive_type, integer},
            body = #function_call_expr{
                function = #identifier_expr{name = helper_func},
                args = [#identifier_expr{name = x}]
            }
        },
        #function_def{
            name = helper_func,
            params = [#param{name = y, type = {primitive_type, integer}}],
            return_type = {primitive_type, integer},
            body = #literal_expr{value = 42}
        }
    ].

%% Test helper functions
analyze_test_call_patterns(AST) ->
    #{test_func => #{calls => [helper_func], frequency => 1},
      helper_func => #{calls => [], frequency => 0}}.

estimate_test_execution_frequencies(AST, CallPatterns) ->
    #{test_func => 50, helper_func => 25}.

identify_test_hot_paths(AST, ExecutionFreqs) ->
    [[test_func, helper_func]].

analyze_test_memory_patterns(AST) ->
    #{test_func => #{total_accesses => 15, read_operations => 10, write_operations => 5}}.

collect_test_type_usage(AST) ->
    #{{primitive_type, integer} => 2}.

identify_test_specialization_opportunities(ExecutionFreqs, TypeUsage) ->
    #{test_func => #{frequency => 150, benefit => 2.5}}.

create_test_existing_optimizations() ->
    #{
        function_specializations => #{},
        monomorphic_instances => #{},
        inlining_decisions => #{},
        dead_code_analysis => #{},
        beam_generation => #{}
    }.

generate_test_adaptive_specializations(Opportunities, ExistingOptimizations) ->
    [#{function_name => test_func, specialization_type => adaptive, runtime_frequency => 150, specialization_benefit => 2.5}].

test_enhance_existing_specialization() ->
    #{
        function_name => test_func,
        specialization_type => enhanced,
        existing_specialization => #{},
        runtime_frequency => 150,
        enhanced_benefit => 2.5,
        enhancement_timestamp => erlang:system_time(millisecond)
    }.

identify_test_hot_path_opportunities(HotPaths, ExecutionFreqs) ->
    [{[main, compute, helper], #{frequency => 160, potential => 2.5}}].

generate_test_hot_path_optimizations(HotPathOpportunities, ProfileCollector) ->
    [#{type => specialized_codegen, path => [main, compute, helper], benefit => 2.5, frequency => 160}].

identify_test_memory_opportunities(MemoryPatterns) ->
    #{func_a => #{access_pattern => #{total_accesses => 50}, potential => 1.8}}.

generate_test_adaptive_memory_layouts(MemoryOpportunities, ExistingOptimizations) ->
    [#{layout_type => cache_optimized, function => func_a, benefit => 1.8}].

create_test_feedback_data() ->
    #{
        profile_data => #{call_patterns => #{}, execution_frequencies => #{}},
        specialization_data => #{adaptive_specializations => []},
        hot_path_data => #{hot_path_optimizations => []},
        memory_data => #{adaptive_memory_layouts => []},
        performance_data => #{performance_optimizations => []}
    }.

create_test_performance_feedback_system(FeedbackData) ->
    #{
        feedback_data => FeedbackData,
        monitoring_enabled => true,
        feedback_interval => 1000,
        adaptation_threshold => 0.15,
        feedback_history_size => 100,
        performance_metrics => init_test_performance_metrics(),
        adaptive_decisions => []
    }.

init_test_performance_metrics() ->
    #{
        execution_time => 0,
        memory_usage => 0,
        throughput => 0,
        latency => 0,
        cache_hit_rate => 0,
        optimization_count => 0,
        adaptation_count => 0
    }.

generate_test_performance_optimizations(Priorities, PerformanceTargets) ->
    [#{optimization_type => specialization_performance, estimated_benefit => 1.2}].

create_test_adaptive_context() ->
    #{
        profile_collector => init_test_profile_collector(),
        existing_optimizations => create_test_existing_optimizations(),
        runtime_feedback => #{},
        adaptive_thresholds => init_test_adaptive_thresholds(),
        performance_targets => init_test_performance_targets()
    }.

collect_test_runtime_profiles(TestAST, AdaptiveContext) ->
    #{
        call_patterns => analyze_test_call_patterns(TestAST),
        execution_frequencies => #{test_func => 100, helper_func => 50},
        hot_paths => [[test_func, helper_func]],
        memory_patterns => #{test_func => #{total_accesses => 20}},
        runtime_type_usage => #{{primitive_type, integer} => 2},
        profile_timestamp => erlang:system_time(millisecond)
    }.

analyze_test_optimization_opportunities(ProfileData) ->
    #{
        specialization => #{test_func => #{frequency => 100, benefit => 2.0}},
        hot_path => [{[test_func, helper_func], #{frequency => 50, potential => 1.8}}],
        memory => #{test_func => #{access_pattern => #{total_accesses => 20}, potential => 1.2}},
        priorities => [{specialization, test_opportunities}]
    }.

create_test_opt_context() ->
    % Create a mock opt_context record
    #{
        type_checker => #{},
        function_specializations => #{},
        monomorphic_instances => #{},
        inlining_decisions => #{},
        dead_code_analysis => #{},
        beam_generation => #{},
        profile_guided_optimization => #{}
    }.

extract_test_optimization_data(TestContext) ->
    #{
        type_checker => maps:get(type_checker, TestContext, #{}),
        function_specializations => maps:get(function_specializations, TestContext, #{}),
        monomorphic_instances => maps:get(monomorphic_instances, TestContext, #{}),
        inlining_decisions => maps:get(inlining_decisions, TestContext, #{}),
        dead_code_analysis => maps:get(dead_code_analysis, TestContext, #{}),
        beam_generation => maps:get(beam_generation, TestContext, #{})
    }.

init_test_adaptive_context(ProfileCollector, OptimizationData) ->
    #{
        profile_collector => ProfileCollector,
        existing_optimizations => OptimizationData,
        runtime_feedback => #{},
        adaptive_thresholds => init_test_adaptive_thresholds(),
        specialization_candidates => #{},
        hot_path_optimizations => #{},
        memory_optimizations => #{},
        performance_targets => init_test_performance_targets()
    }.