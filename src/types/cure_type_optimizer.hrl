%% Cure Type Optimizer - Header File
%% Record definitions for type-directed optimization system

%% Optimization configuration
-record(optimization_config, {
    level = 2 :: 0..3,                    % Optimization level (0=none, 3=aggressive)
    enable_specialization = true :: boolean(),
    enable_monomorphization = true :: boolean(), 
    enable_inlining = true :: boolean(),
    enable_dce = true :: boolean(),       % Dead code elimination
    enable_memory_opts = true :: boolean(),
    max_specializations = 10 :: pos_integer(),
    inline_threshold = 50 :: pos_integer(),
    specialization_threshold = 5 :: pos_integer()
}).

%% Type information collected during analysis
-record(type_info, {
    function_types = #{} :: #{atom() => term()},
    call_sites = #{} :: #{atom() => [term()]},
    type_usage = #{} :: #{term() => non_neg_integer()},
    monomorphic_instances = #{} :: #{atom() => [term()]},
    memory_layouts = #{} :: #{term() => term()}
}).

%% Usage statistics for optimization decisions
-record(usage_statistics, {
    function_calls = #{} :: #{atom() => non_neg_integer()},
    type_frequencies = #{} :: #{term() => non_neg_integer()},
    hot_paths = [] :: [[atom()]],
    cold_code = [] :: [atom()]
}).

%% Specialization tracking
-record(specialization_map, {
    candidates = #{} :: #{atom() => [term()]},
    generated = #{} :: #{atom() => [term()]},
    cost_benefit = #{} :: #{atom() => term()}
}).

%% Type optimization context
-record(optimization_context, {
    config :: #optimization_config{},
    type_info :: #type_info{},
    usage_stats :: #usage_statistics{},
    specializations :: #specialization_map{},
    inlining_decisions :: #{atom() => term()}
}).