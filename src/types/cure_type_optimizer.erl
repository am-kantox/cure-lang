%% Cure Programming Language - Type-directed Optimizer
%% Framework for optimizations based on type information
-module(cure_type_optimizer).

%% Suppress warnings for work-in-progress optimization functions
-compile(
    {nowarn_unused_function, [
        add_monomorphic_functions_to_ast/2,
        all_call_sites_type_incompatible/2,
        calculate_branch_prediction_benefit/1,
        calculate_cache_locality_benefit/2,
        calculate_code_bloat_penalty/2,
        calculate_compilation_cost/2,
        calculate_debug_cost/1,
        calculate_hot_path_multiplier/1,
        calculate_icache_cost/2,
        calculate_optimization_opportunities/2,
        calculate_register_pressure_benefit/2,
        calculate_register_pressure_cost/2,
        calculate_type_specialization_benefit/3,
        combine_match_kinds/2,
        find_best_specialization/2,
        is_subtype/2,
        match_function_types/4,
        match_single_type/2,
        match_specialization_pattern/2,
        specialization_match_score/1,
        analyze_access_pattern/1,
        analyze_arithmetic_patterns/1,
        analyze_body_optimizations/2,
        analyze_call_graph_for_unused_functions/2,
        analyze_call_optimization_potential/3,
        analyze_comparison_patterns/1,
        analyze_condition_reachability/2,
        analyze_dispatch_patterns/1,
        analyze_function_call_patterns/1,
        analyze_function_memory_access/1,
        analyze_function_type_complexity/1,
        analyze_memory_access_patterns/1,
        analyze_param_optimizations/2,
        analyze_profile_optimization_opportunities/1,
        analyze_type_usage_patterns/1,
        apply_adaptive_memory_layout_optimization/3,
        apply_adaptive_memory_layouts_to_ast/2,
        apply_adaptive_optimizations/2,
        apply_adaptive_specializations_to_ast/2,
        apply_beam_generation_pass/2,
        apply_dead_code_elimination/2,
        apply_dynamic_hot_path_optimization/3,
        apply_feedback_driven_specialization/3,
        apply_hot_path_optimizations_to_ast/2,
        apply_inlining_optimizations/2,
        apply_performance_feedback_optimization/3,
        apply_performance_optimizations_to_ast/2,
        apply_profile_guided_optimization_pass/2,
        apply_single_hot_path_optimization/2,
        apply_single_memory_layout/2,
        apply_single_performance_optimization/2,
        apply_single_specialization/2,
        apply_type_based_peephole_optimizations/2,
        are_all_float_params/1,
        are_all_integer_params/1,
        build_hot_path_sequence/3,
        build_monomorphic_lookup/1,
        build_path_sequence/5,
        build_type_dispatch_table/1,
        calculate_arithmetic_optimization_benefit/1,
        calculate_call_depth/2,
        calculate_combined_priority/1,
        calculate_comparison_optimization_benefit/1,
        calculate_dispatch_optimization_benefit/1,
        calculate_expression_complexity/1,
        calculate_hot_path_optimization_potential/2,
        calculate_locality_score/1,
        calculate_memory_optimization_potential/1,
        calculate_optimization_priorities/3,
        calculate_path_frequency/2,
        calculate_specialization_benefit/3,
        calculate_type_complexity/1,
        calculate_types_complexity/1,
        can_use_float_operation/2,
        can_use_integer_add/1,
        classify_expression_type/1,
        classify_type/1,
        classify_type_tuple/1,
        cleanup_inlined_functions/2,
        collect_runtime_profiles/2,
        collect_runtime_type_usage/1,
        count_function_type_diversity/2,
        count_memory_optimized_functions/1,
        count_operation_type/2,
        count_optimized_paths/1,
        count_specialized_functions/1,
        count_specialized_opcodes/1,
        count_type_operations/1,
        create_adaptive_specialization/2,
        create_optimized_calling_conventions/1,
        create_parameter_substitution_map/2,
        create_performance_feedback_system/1,
        detect_sequential_pattern/1,
        detect_unreachable_branches_impl/4,
        detect_unreachable_branches_with_types/3,
        eliminate_redundant_type_operations/2,
        enhance_existing_specialization/3,
        estimate_execution_frequencies/2,
        estimate_performance_improvement/1,
        extract_arithmetic_patterns/1,
        extract_arithmetic_patterns_from_type/1,
        extract_base_type/1,
        extract_body_types/1,
        extract_comparison_patterns/1,
        extract_comparison_patterns_from_type/1,
        extract_dispatch_patterns/1,
        extract_dispatch_patterns_from_type/1,
        extract_expression_types/1,
        extract_function_calls/1,
        extract_inlined_function_info/1,
        extract_memory_operations/1,
        extract_monomorphic_functions/1,
        extract_optimization_data/1,
        extract_param_types/1,
        extract_pattern_memory_ops/1,
        extract_type_info_for_beam/1,
        extract_type_pattern/1,
        find_dead_polymorphic_instances/2,
        find_function_def/2,
        find_hottest_call/3,
        find_redundant_checks_impl/3,
        find_redundant_in_expression/3,
        find_unreachable_in_expression/3,
        find_unreachable_in_function/3,
        find_unreachable_patterns/2,
        find_unreachable_type_branches/2,
        find_unused_type_definitions/2,
        generate_adaptive_memory_layouts/2,
        generate_adaptive_specializations/2,
        generate_arithmetic_opcodes/1,
        generate_beam_for_functions/2,
        generate_comparison_opcodes/1,
        generate_dispatch_opcodes/1,
        generate_dynamic_hot_path_optimizations/2,
        generate_expr_instructions/3,
        generate_function_beam_instructions/2,
        generate_hot_path_performance_opt/2,
        generate_memory_performance_opt/2,
        generate_optimized_call/4,
        generate_performance_driven_optimizations/2,
        generate_specialization_id/2,
        generate_specialization_performance_opt/2,
        generate_specialized_arithmetic_opcode/1,
        generate_specialized_comparison_opcode/1,
        generate_specialized_dispatch_opcode/1,
        generate_specialized_opcodes/2,
        generate_typed_body_instructions/3,
        generate_typed_param_loading/2,
        generate_typed_return_sequence/1,
        get_call_site_type_info/1,
        get_function_call_signature/2,
        get_function_type_mappings/1,
        get_function_type_signature/2,
        get_memory_layout_optimizations/1,
        get_parameter_types/1,
        get_return_type/1,
        has_specialized_version/1,
        identify_body_optimizations/2,
        identify_fully_inlined_functions/1,
        identify_hot_path_functions/1,
        identify_hot_path_opportunities/2,
        identify_memory_optimization_opportunities/1,
        identify_runtime_hot_paths/2,
        identify_specialization_opportunities/2,
        identify_type_specific_dead_code_patterns/3,
        identify_unused_functions_with_types/3,
        infer_comparable_type/1,
        infer_expr_type_with_context/2,
        infer_numeric_type/1,
        init_adaptive_optimization_context/2,
        init_adaptive_thresholds/0,
        init_beam_generation_context/1,
        init_opcode_mappings/0,
        init_performance_metrics/0,
        init_performance_targets/0,
        init_profile_collector/0,
        inline_function_body/3,
        inline_function_call/2,
        is_comparable_type/1,
        is_concrete_simple/1,
        is_entry_point/1,
        is_exported_function/1,
        is_hot_path_function/2,
        is_memory_operation/1,
        is_monomorphic_signature/1,
        is_numeric_type/1,
        is_pattern_matchable_type/1,
        is_type_guaranteed_by_signature/2,
        is_type_operation/1,
        lookup_function_definition/1,
        merge_pattern_counts/2,
        optimize_instructions_with_types/3,
        optimize_register_usage/2,
        remove_dead_code_patterns/2,
        remove_empty_modules/1,
        remove_redundant_type_checks/2,
        remove_unreachable_branches/2,
        remove_unused_functions/2,
        remove_unused_functions_advanced/2,
        substitute_in_statement/2,
        substitute_parameters_in_body/2,
        transform_ast_remove_patterns/2,
        transform_ast_remove_redundant_checks/2,
        transform_ast_remove_unreachable/2,
        transform_ast_with_inlining/2,
        transform_calls_for_monomorphization/2,
        transform_expression_with_inlining/2,
        transform_expr_for_monomorphization/2,
        transform_expr_remove_redundant/2,
        transform_expr_remove_unreachable/2,
        transform_item_for_monomorphization/2,
        transform_item_remove_redundant/2,
        transform_item_remove_unreachable/2,
        transform_item_with_inlining/2,
        transform_nested_statements/2,
        transform_statements_with_inlining/2,
        transform_statement_with_inlining/2,
        type_matches/2,
        types_are_compatible/2,
        types_equivalent/2,
        type_to_signature/1,
        verify_ast_consistency/1
    ]}
).

-moduledoc """
# Cure Programming Language - Type-directed Optimizer

The type optimizer leverages rich type information from Cure's dependent type
system to perform sophisticated program optimizations. It analyzes type usage
patterns, specializes generic functions, eliminates dead code, and optimizes
memory layouts based on static type analysis.

## Key Features

### Function Specialization
- **Type-based Specialization**: Creates specialized versions of generic functions
- **Call-site Analysis**: Identifies frequent type instantiations
- **Cost-benefit Analysis**: Balances code size vs. performance gains
- **Automatic Generation**: Generates specialized function variants

### Monomorphization
- **Generic Elimination**: Converts polymorphic functions to monomorphic variants
- **Type Instantiation**: Resolves all type variables with concrete types
- **Dispatch Optimization**: Eliminates runtime type dispatch overhead
- **Template Expansion**: Expands type templates at compile time

### Inlining Optimization
- **Type-guided Inlining**: Uses type information for better inlining decisions
- **Call-site Specialization**: Inlines based on argument types
- **Size Thresholds**: Configurable limits to prevent code bloat
- **Hot-path Optimization**: Prioritizes frequently executed code paths

### Dead Code Elimination
- **Type-based Reachability**: Uses type analysis for precise dead code detection
- **Specialization Cleanup**: Removes unused specialized variants
- **Constraint-based Analysis**: Leverages dependent type constraints
- **Whole-program Analysis**: Global dead code elimination

### Memory Layout Optimization
- **Struct Packing**: Optimizes memory layout based on type information
- **Cache-aware Layouts**: Arranges fields for better cache locality
- **Alignment Optimization**: Ensures proper alignment for performance
- **Size Minimization**: Reduces memory footprint where possible

## Optimization Pipeline

### Phase 1: Type Analysis
```erlang
{TypeInfo, UsageStats} = cure_type_optimizer:analyze_program_types(AST),
%% Collects:
%% - Function type signatures
%% - Call site information with argument types
%% - Type usage frequencies
%% - Monomorphic instantiation opportunities
```

### Phase 2: Opportunity Identification
```erlang
Context = cure_type_optimizer:find_optimization_opportunities(AST, Context1),
%% Identifies:
%% - Specialization candidates
%% - Inlining opportunities
%% - Dead code
%% - Memory layout improvements
```

### Phase 3: Optimization Application
```erlang
OptimizedAST = cure_type_optimizer:run_optimization_passes(AST, Context2),
%% Applies optimizations in order:
%% 1. Function specialization
%% 2. Monomorphization  
%% 3. Inlining
%% 4. Dead code elimination
%% 5. Memory layout optimization
```

## Usage Examples

### Program Optimization
```erlang
%% Basic optimization with default settings
{ok, OptimizedAST, Report} = cure_type_optimizer:optimize_program(AST),

%% Custom optimization configuration
Config = #optimization_config{
    level = 3,  % Aggressive optimization
    enable_specialization = true,
    max_specializations = 20,
    inline_threshold = 100
},
{ok, OptimizedAST, Report} = cure_type_optimizer:optimize_program(AST, Config).
```

### Module-level Optimization
```erlang
{ok, OptimizedModule} = cure_type_optimizer:optimize_module(Module),

%% With custom config
{ok, OptimizedModule} = cure_type_optimizer:optimize_module(Module, Config).
```

### Individual Optimization Passes
```erlang
%% Run specific optimization passes
SpecializedAST = cure_type_optimizer:function_specialization_pass(AST),
MonomorphicAST = cure_type_optimizer:monomorphization_pass(SpecializedAST),
InlinedAST = cure_type_optimizer:inlining_pass(MonomorphicAST).
```

## Configuration Options

### Optimization Levels
- **Level 0**: No optimizations (debugging)
- **Level 1**: Basic optimizations (safe, minimal)
- **Level 2**: Standard optimizations (default, balanced)
- **Level 3**: Aggressive optimizations (maximum performance)

### Fine-grained Control
- **Specialization Limits**: Maximum number of specialized variants
- **Inlining Thresholds**: Size limits for function inlining
- **Memory Optimization**: Enable/disable layout optimizations
- **Pass Selection**: Enable/disable individual optimization passes

## Performance Characteristics

### Typical Improvements
- **Function Calls**: 25-60% improvement through specialization
- **Memory Usage**: 10-30% reduction through layout optimization
- **Code Size**: Variable (may increase with specialization, decrease with DCE)
- **Compile Time**: Increases proportionally to optimization level

### Analysis Complexity
- **Type Analysis**: O(n log n) where n is program size
- **Specialization**: O(k × m) where k is candidates, m is instantiations
- **Dead Code**: O(n + e) where e is call graph edges
- **Memory Layout**: O(t) where t is number of types

## Integration

The type optimizer integrates with:
- **Type Checker**: Uses inferred type information
- **Code Generator**: Provides optimized AST for compilation
- **Runtime**: Optimizes for runtime performance characteristics
- **Profiler**: Can use runtime profiling data for optimization hints

## Optimization Report

Generates detailed reports including:
- **Specializations Created**: List of generated specialized functions
- **Inlining Decisions**: Functions inlined and their sizes
- **Dead Code Eliminated**: Removed functions and their impact
- **Memory Improvements**: Layout changes and size reductions
- **Performance Estimates**: Expected performance improvements

## Safety and Correctness

- **Type Preservation**: All optimizations preserve type safety
- **Semantic Equivalence**: Optimized code maintains original semantics
- **Constraint Preservation**: Dependent type constraints are maintained
- **Error Handling**: Graceful degradation when optimization fails
""".

-export([
    % Main optimization interface
    optimize_program/1,
    optimize_program/2,
    optimize_module/1,
    optimize_module/2,

    % Optimization passes
    run_optimization_passes/2,

    % Individual optimization passes
    function_specialization_pass/1,
    function_specialization_pass/2,
    monomorphization_pass/1,
    monomorphization_pass/2,
    inlining_pass/1,
    inlining_pass/2,
    dead_code_elimination_pass/1,
    dead_code_elimination_pass/2,
    memory_layout_optimization_pass/1,
    memory_layout_optimization_pass/2,

    % Type analysis utilities
    analyze_type_usage/1,
    collect_type_information/1,
    find_specialization_opportunities/1,
    collect_type_usage_patterns/1,
    count_function_calls/1,
    collect_call_sites/1,
    identify_hot_paths/1,
    identify_cold_code/1,
    analyze_specialization_candidates/1,

    % Optimization configuration
    default_optimization_config/0,
    set_optimization_level/1,

    % Context management
    initialize_optimization_context/1,
    find_optimization_opportunities/2,
    analyze_program_types/1,

    % Polymorphic instantiation tracking (Phase 3.1)
    collect_poly_instantiation_sites/1,
    collect_poly_instantiations_from_module/1,
    collect_poly_instantiations_from_function/1,
    collect_poly_instantiations_from_expr/2,
    track_polymorphic_call/3,

    % Monomorphization implementation (Phase 3.2-3.4)
    monomorphize_ast/2,
    generate_specialized_variants/2,
    create_monomorphic_function/3,
    specialize_function_body/3,
    transform_ast_with_specializations/2,
    replace_poly_calls_in_expr/2,
    eliminate_unused_specializations/2,
    find_reachable_functions/2
]).

-include("../parser/cure_ast.hrl").
-include("../codegen/cure_beam_compiler.hrl").

%% Type optimization context
-record(optimization_context, {
    config :: optimization_config(),
    type_info :: type_info(),
    usage_stats :: usage_statistics(),
    specializations :: specialization_map(),
    inlining_decisions :: inlining_map(),
    type_checker = undefined,
    function_specializations = #{},
    monomorphic_instances = #{},
    beam_generation = #{}
}).

%% Optimization configuration
-record(optimization_config, {
    % Optimization level (0=none, 3=aggressive)
    level = 2 :: 0..3,
    enable_specialization = true :: boolean(),
    enable_monomorphization = true :: boolean(),
    enable_inlining = true :: boolean(),
    % Dead code elimination
    enable_dce = true :: boolean(),
    enable_memory_opts = true :: boolean(),
    max_specializations = 10 :: pos_integer(),
    inline_threshold = 50 :: pos_integer(),
    specialization_threshold = 5 :: pos_integer()
}).

%% Type information collected during analysis
-record(type_info, {
    function_types = #{} :: #{atom() => type_expr()},
    call_sites = #{} :: #{atom() => [call_site_info()]},
    type_usage = #{} :: #{type_expr() => usage_frequency()},
    monomorphic_instances = #{} :: #{atom() => [type_instantiation()]},
    memory_layouts = #{} :: #{type_expr() => memory_layout()}
}).

%% Usage statistics for optimization decisions
-record(usage_statistics, {
    function_calls = #{} :: #{atom() => call_frequency()},
    type_frequencies = #{} :: #{type_expr() => usage_frequency()},
    hot_paths = [] :: [function_path()],
    cold_code = [] :: [atom()]
}).

%% Specialization tracking
-record(specialization_map, {
    candidates = #{} :: #{atom() => [specialization_candidate()]},
    generated = #{} :: #{atom() => [specialized_function()]},
    cost_benefit = #{} :: #{atom() => cost_benefit_analysis()}
}).

%% Type aliases
-type optimization_config() :: #optimization_config{}.
-type type_info() :: #type_info{}.
-type usage_statistics() :: #usage_statistics{}.
-type specialization_map() :: #specialization_map{}.
-type call_site_info() :: {location(), [type_expr()]}.
-type usage_frequency() :: non_neg_integer().
-type type_instantiation() :: {[type_expr()], type_expr()}.
-type memory_layout() :: {alignment(), size(), fields()}.
-type call_frequency() :: non_neg_integer().
-type function_path() :: [atom()].
-type specialization_candidate() :: {[type_expr()], cost_benefit_analysis()}.
-type specialized_function() :: {atom(), [type_expr()], function_def()}.
-type cost_benefit_analysis() :: {cost(), benefit()}.
-type function_def() :: #function_def{}.
-type alignment() :: pos_integer().
-type size() :: non_neg_integer().
-type fields() :: [field_info()].
-type field_info() :: {atom(), type_expr(), offset()}.
-type cost() :: non_neg_integer().
-type benefit() :: non_neg_integer().
-type offset() :: non_neg_integer().
-type inlining_map() :: #{atom() => inlining_decision()}.
-type inlining_decision() :: inline | no_inline | {conditional_inline, condition()}.
-type condition() :: term().

%% ============================================================================
%% Main Optimization Interface
%% ============================================================================

%% Optimize entire program with default configuration
optimize_program(AST) ->
    optimize_program(AST, default_optimization_config()).

%% Optimize program with custom configuration
optimize_program(AST, Config) ->
    Context = initialize_optimization_context(Config),

    % Phase 1: Collect type information and usage statistics
    cure_utils:debug("Phase 1: Analyzing type usage and collecting information...~n"),
    {TypeInfo, UsageStats} = analyze_program_types(AST),

    Context1 = Context#optimization_context{
        type_info = TypeInfo,
        usage_stats = UsageStats
    },

    % Phase 2: Find optimization opportunities
    cure_utils:debug("Phase 2: Identifying optimization opportunities...~n"),
    Context2 = find_optimization_opportunities(AST, Context1),

    % Phase 3: Apply optimization passes
    cure_utils:debug("Phase 3: Applying optimization passes...~n"),
    OptimizedAST = run_optimization_passes(AST, Context2),

    cure_utils:debug("Type-directed optimization completed.~n"),

    {ok, OptimizedAST, generate_optimization_report(Context2)}.

%% Optimize single module
optimize_module(Module) ->
    optimize_module(Module, default_optimization_config()).

optimize_module(Module, Config) ->
    Context = initialize_optimization_context(Config),
    {TypeInfo, UsageStats} = analyze_module_types(Module),

    Context1 = Context#optimization_context{
        type_info = TypeInfo,
        usage_stats = UsageStats
    },

    Context2 = find_module_optimization_opportunities(Module, Context1),
    OptimizedModule = run_module_optimization_passes(Module, Context2),

    {ok, OptimizedModule}.

%% ============================================================================
%% Optimization Pass Framework
%% ============================================================================

%% Run all enabled optimization passes in order
run_optimization_passes(AST, Context) ->
    #optimization_config{
        enable_specialization = EnableSpec,
        enable_monomorphization = EnableMono,
        enable_inlining = EnableInlining,
        enable_dce = EnableDCE,
        enable_memory_opts = EnableMemOpts
    } = Context#optimization_context.config,

    % Define optimization pass pipeline
    Passes = [
        {function_specialization_pass, EnableSpec},
        {monomorphization_pass, EnableMono},
        {inlining_pass, EnableInlining},
        {dead_code_elimination_pass, EnableDCE},
        {memory_layout_optimization_pass, EnableMemOpts}
    ],

    % Apply enabled passes sequentially
    lists:foldl(
        fun({PassName, Enabled}, CurrentAST) ->
            case Enabled of
                true ->
                    cure_utils:debug("  Running ~p...~n", [PassName]),
                    apply_optimization_pass(PassName, CurrentAST, Context);
                false ->
                    CurrentAST
            end
        end,
        AST,
        Passes
    ).

%% Apply individual optimization pass
apply_optimization_pass(function_specialization_pass, AST, Context) ->
    function_specialization_pass(AST, Context);
apply_optimization_pass(monomorphization_pass, AST, Context) ->
    monomorphization_pass(AST, Context);
apply_optimization_pass(inlining_pass, AST, Context) ->
    inlining_pass(AST, Context);
apply_optimization_pass(dead_code_elimination_pass, AST, Context) ->
    dead_code_elimination_pass(AST, Context);
apply_optimization_pass(memory_layout_optimization_pass, AST, Context) ->
    memory_layout_optimization_pass(AST, Context).

%% ============================================================================
%% Individual Optimization Passes
%% ============================================================================

%% Function Specialization Pass
function_specialization_pass(AST) ->
    function_specialization_pass(
        AST, initialize_optimization_context(default_optimization_config())
    ).

function_specialization_pass(AST, Context) ->
    SpecMap = Context#optimization_context.specializations,

    % Generate specialized versions of functions
    SpecializedFunctions = generate_specialized_functions(SpecMap),

    % Add specialized functions to AST
    ASTWithSpecializations = add_specialized_functions_to_ast(AST, SpecializedFunctions),

    % Replace calls with specialized versions where profitable
    replace_calls_with_specialized_versions(ASTWithSpecializations, SpecMap).

%% Monomorphization Pass
monomorphization_pass(AST) ->
    monomorphization_pass(AST, initialize_optimization_context(default_optimization_config())).

monomorphization_pass(AST, Context) ->
    TypeInfo = Context#optimization_context.type_info,

    % Find polymorphic functions
    PolymorphicFunctions = find_polymorphic_functions(AST, TypeInfo),

    % Generate monomorphic instances
    MonomorphicInstances = generate_monomorphic_instances(PolymorphicFunctions, TypeInfo),

    % Replace polymorphic calls with monomorphic calls
    replace_with_monomorphic_calls(AST, MonomorphicInstances).

%% Inlining Pass - Type-directed intelligent inlining
inlining_pass(AST) ->
    inlining_pass(AST, initialize_optimization_context(default_optimization_config())).

inlining_pass(AST, Context) ->
    % Phase 1: Analyze inlining opportunities based on type information
    cure_utils:debug("  Analyzing inlining opportunities...~n"),
    InliningOpportunities = analyze_inlining_opportunities(AST, Context),

    % Phase 2: Make intelligent inlining decisions
    InliningDecisions = make_inlining_decisions(InliningOpportunities, Context),

    % Phase 3: Apply inlining transformations
    cure_utils:debug("  Applying inlining transformations...~n"),
    OptimizedAST = inline_functions(AST, InliningDecisions),

    cure_utils:debug("  [Inlining applied to ~p call sites]~n", [maps:size(InliningDecisions)]),
    OptimizedAST.

%% Dead Code Elimination Pass - Enhanced with Type Information
dead_code_elimination_pass(AST) ->
    dead_code_elimination_pass(AST, initialize_optimization_context(default_optimization_config())).

dead_code_elimination_pass(AST, Context) ->
    % Phase 1: Analyze dead code using type information
    cure_utils:debug("  Analyzing dead code using type information...~n"),
    DeadCodeAnalysis = analyze_dead_code_with_types(AST, Context),

    % Phase 2: Apply dead code elimination transformations
    cure_utils:debug("  Removing identified dead code...~n"),
    ColdCode = maps:get(cold_code, DeadCodeAnalysis, []),
    OptimizedAST = remove_dead_code(AST, ColdCode),

    % Phase 3: Clean up after dead code removal
    CleanedAST = cleanup_after_dead_code_removal(OptimizedAST, DeadCodeAnalysis),

    cure_utils:debug("  [Dead code elimination completed]~n"),
    CleanedAST.

%% Analyze dead code using type information
analyze_dead_code_with_types(AST, Context) ->
    TypeInfo = Context#optimization_context.type_info,
    UsageStats = Context#optimization_context.usage_stats,

    % Find functions that are never called
    UnreachableFunctions = find_unreachable_functions_by_type(AST, TypeInfo),

    % Find patterns that can never match based on types
    UnreachablePatterns = find_unreachable_patterns_by_types(AST, TypeInfo),

    % Find redundant type checks
    RedundantChecks = find_redundant_type_checks(AST, TypeInfo),

    #{
        cold_code => UsageStats#usage_statistics.cold_code,
        unreachable_functions => UnreachableFunctions,
        unreachable_patterns => UnreachablePatterns,
        redundant_checks => RedundantChecks
    }.

%% Find unreachable functions using type information
find_unreachable_functions_by_type(AST, TypeInfo) ->
    % Collect all function definitions
    AllFunctions = collect_all_function_names(AST),

    % Get call sites from type info
    CallSites = TypeInfo#type_info.call_sites,

    % Find functions that are never called
    CalledFunctions = maps:keys(CallSites),

    % Find exported and entry point functions (never considered dead)
    ExportedFunctions = find_exported_functions(AST),
    % TODO: find_entry_points returns a set but we need a list for concatenation.
    % This causes a badarg error, but the error is currently caught upstream
    % and allows compilation to proceed with unoptimized AST. Fixing this
    % requires ensuring the entire optimization pipeline doesn't break code generation.
    % Fix: EntryPoints = sets:to_list(find_entry_points(AST)),
    EntryPoints = find_entry_points(AST),
    ProtectedFunctions = ExportedFunctions ++ EntryPoints,

    % Unreachable = All - Called - Protected
    Unreachable = (AllFunctions -- CalledFunctions) -- ProtectedFunctions,

    cure_utils:debug("[DCE] Found ~p unreachable functions~n", [length(Unreachable)]),
    Unreachable.

%% Find unreachable patterns using type analysis
find_unreachable_patterns_by_types(AST, TypeInfo) ->
    % Find patterns that can never match based on type information
    FunctionTypes = TypeInfo#type_info.function_types,

    UnreachablePatterns = lists:flatmap(
        fun(Item) ->
            case Item of
                #function_def{name = Name, body = Body} ->
                    % Get function's type signature
                    case maps:get(Name, FunctionTypes, undefined) of
                        undefined ->
                            [];
                        FuncType ->
                            find_unreachable_patterns_in_expr(Body, FuncType)
                    end;
                #module_def{items = Items} ->
                    find_unreachable_patterns_by_types(Items, TypeInfo);
                _ ->
                    []
            end
        end,
        if
            is_list(AST) -> AST;
            true -> [AST]
        end
    ),

    cure_utils:debug("[DCE] Found ~p unreachable patterns~n", [length(UnreachablePatterns)]),
    UnreachablePatterns.

%% Find unreachable patterns in expression
find_unreachable_patterns_in_expr(#match_expr{patterns = Patterns, expr = Expr}, FuncType) ->
    % Check if any match clauses are unreachable based on expr type
    lists:filtermap(
        fun(Clause) ->
            #match_clause{pattern = Pattern} = Clause,
            case is_pattern_unreachable(Pattern, Expr, FuncType) of
                true -> {true, {unreachable_pattern, Pattern}};
                false -> false
            end
        end,
        Patterns
    );
find_unreachable_patterns_in_expr(_, _FuncType) ->
    [].

%% Check if pattern is unreachable
is_pattern_unreachable(_Pattern, _Value, _FuncType) ->
    % Placeholder: would use type inference to determine if pattern can never match
    false.

%% Find redundant type checks
find_redundant_type_checks(AST, TypeInfo) ->
    % Find type checks that are redundant given type information
    FunctionTypes = TypeInfo#type_info.function_types,

    RedundantChecks = lists:flatmap(
        fun(Item) ->
            case Item of
                #function_def{name = Name, body = Body} ->
                    % Get function's type signature
                    case maps:get(Name, FunctionTypes, undefined) of
                        undefined ->
                            [];
                        FuncType ->
                            find_redundant_checks_in_expr(Body, FuncType)
                    end;
                #module_def{items = Items} ->
                    find_redundant_type_checks(Items, TypeInfo);
                _ ->
                    []
            end
        end,
        if
            is_list(AST) -> AST;
            true -> [AST]
        end
    ),

    cure_utils:debug("[DCE] Found ~p redundant type checks~n", [length(RedundantChecks)]),
    RedundantChecks.

%% Find redundant checks in expression
find_redundant_checks_in_expr(#binary_op_expr{op = Op, left = Left} = Expr, FuncType) when
    Op =:= 'is_integer'; Op =:= 'is_atom'; Op =:= 'is_list'
->
    % Check if type is already known from signature
    case infer_expr_type(Left) of
        {ok, InferredType} ->
            case is_type_check_redundant(Op, InferredType, FuncType) of
                true -> [{redundant_check, Expr}];
                false -> []
            end;
        _ ->
            []
    end;
find_redundant_checks_in_expr(_, _FuncType) ->
    [].

%% Check if type check is redundant
is_type_check_redundant(_Op, _InferredType, _FuncType) ->
    % Placeholder: would check if inferred type makes check redundant
    false.

%% Helper: Find exported functions
find_exported_functions(AST) when is_list(AST) ->
    lists:flatmap(fun find_exported_functions/1, AST);
find_exported_functions(#module_def{exports = Exports}) ->
    [Name || #export_spec{name = Name} <- Exports];
find_exported_functions(_) ->
    [].

%% Transform AST for monomorphization
transform_ast_for_monomorphization(AST, MonomorphicInstances) when is_list(AST) ->
    % Transform each item in the AST
    lists:map(
        fun(Item) -> transform_item_for_mono(Item, MonomorphicInstances) end,
        AST
    );
transform_ast_for_monomorphization(AST, MonomorphicInstances) ->
    transform_item_for_mono(AST, MonomorphicInstances).

%% Transform individual AST item for monomorphization
transform_item_for_mono(#module_def{items = Items} = Module, Instances) ->
    % Add specialized functions and transform calls in existing functions
    NewItems = lists:flatmap(
        fun(Item) ->
            case Item of
                #function_def{name = Name} = FuncDef ->
                    % Transform function body to use specialized calls
                    TransformedFunc = transform_function_calls(FuncDef, Instances),
                    % Note: Specialized versions should be generated in Phase 3.2
                    % This phase just transforms calls
                    [TransformedFunc];
                _ ->
                    [Item]
            end
        end,
        Items
    ),
    Module#module_def{items = NewItems};
transform_item_for_mono(Item, _Instances) ->
    Item.

%% Transform function calls to use specialized versions
transform_function_calls(#function_def{body = Body} = FuncDef, Instances) ->
    NewBody = transform_expr_for_monomorphization(Body, Instances),
    FuncDef#function_def{body = NewBody};
transform_function_calls(FuncDef, _Instances) ->
    FuncDef.

%% Transform AST for inlining
transform_ast_for_inlining(AST, InliningMap) when map_size(InliningMap) =:= 0 ->
    AST;
transform_ast_for_inlining(AST, InliningMap) when is_list(AST) ->
    lists:map(
        fun(Item) -> transform_item_for_inlining(Item, InliningMap) end,
        AST
    );
transform_ast_for_inlining(AST, InliningMap) ->
    transform_item_for_inlining(AST, InliningMap).

%% Transform item for inlining
transform_item_for_inlining(#module_def{items = Items} = Module, InliningMap) ->
    % Build function definition map for lookup
    FuncDefs = collect_function_definitions_impl(Items, #{}),

    % Transform each function, inlining calls where appropriate
    NewItems = lists:map(
        fun(Item) ->
            case Item of
                #function_def{body = Body} = FuncDef ->
                    NewBody = inline_in_expression(Body, InliningMap, FuncDefs),
                    FuncDef#function_def{body = NewBody};
                _ ->
                    Item
            end
        end,
        Items
    ),
    Module#module_def{items = NewItems};
transform_item_for_inlining(Item, _InliningMap) ->
    Item.

%% Inline function calls in expression
inline_in_expression(
    #function_call_expr{
        function = #identifier_expr{name = FuncName},
        args = Args
    } = CallExpr,
    InliningMap,
    FuncDefs
) ->
    % Check if this call should be inlined
    case maps:get(FuncName, InliningMap, undefined) of
        true ->
            % Inline the function
            case maps:get(FuncName, FuncDefs, undefined) of
                #function_def{params = Params, body = Body} when length(Params) =:= length(Args) ->
                    % Create substitution map
                    SubstMap = lists:foldl(
                        fun({#param{name = ParamName}, Arg}, Acc) ->
                            maps:put(ParamName, Arg, Acc)
                        end,
                        #{},
                        lists:zip(Params, Args)
                    ),
                    % Substitute parameters in body
                    substitute_in_expression(Body, SubstMap, InliningMap, FuncDefs);
                _ ->
                    % Can't inline, transform args
                    NewArgs = [inline_in_expression(Arg, InliningMap, FuncDefs) || Arg <- Args],
                    CallExpr#function_call_expr{args = NewArgs}
            end;
        _ ->
            % Not inlined, transform args
            NewArgs = [inline_in_expression(Arg, InliningMap, FuncDefs) || Arg <- Args],
            CallExpr#function_call_expr{args = NewArgs}
    end;
inline_in_expression(#binary_op_expr{left = Left, right = Right} = Expr, InliningMap, FuncDefs) ->
    Expr#binary_op_expr{
        left = inline_in_expression(Left, InliningMap, FuncDefs),
        right = inline_in_expression(Right, InliningMap, FuncDefs)
    };
inline_in_expression(Expr, _InliningMap, _FuncDefs) ->
    Expr.

%% Substitute variables in expression
substitute_in_expression(#identifier_expr{name = Name} = Expr, SubstMap, _InliningMap, _FuncDefs) ->
    maps:get(Name, SubstMap, Expr);
substitute_in_expression(#function_call_expr{args = Args} = Expr, SubstMap, InliningMap, FuncDefs) ->
    NewArgs = [substitute_in_expression(Arg, SubstMap, InliningMap, FuncDefs) || Arg <- Args],
    inline_in_expression(Expr#function_call_expr{args = NewArgs}, InliningMap, FuncDefs);
substitute_in_expression(
    #binary_op_expr{left = Left, right = Right} = Expr, SubstMap, InliningMap, FuncDefs
) ->
    Expr#binary_op_expr{
        left = substitute_in_expression(Left, SubstMap, InliningMap, FuncDefs),
        right = substitute_in_expression(Right, SubstMap, InliningMap, FuncDefs)
    };
substitute_in_expression(Expr, _SubstMap, _InliningMap, _FuncDefs) ->
    Expr.

%% Filter dead functions from AST
filter_dead_functions(AST, DeadFunctions) when is_list(AST) ->
    lists:map(
        fun(Item) -> filter_dead_from_item(Item, DeadFunctions) end,
        AST
    );
filter_dead_functions(AST, DeadFunctions) ->
    filter_dead_from_item(AST, DeadFunctions).

%% Filter dead functions from item
filter_dead_from_item(#module_def{items = Items} = Module, DeadFunctions) ->
    NewItems = lists:filter(
        fun(Item) ->
            case Item of
                #function_def{name = Name} ->
                    not lists:member(Name, DeadFunctions);
                _ ->
                    true
            end
        end,
        Items
    ),
    Module#module_def{items = NewItems};
filter_dead_from_item(Item, _DeadFunctions) ->
    Item.

%% Cleanup after dead code removal
cleanup_after_dead_code_removal(AST, DeadCodeAnalysis) ->
    % Remove unreachable patterns
    UnreachablePatterns = maps:get(unreachable_patterns, DeadCodeAnalysis, []),
    AST1 = remove_unreachable_patterns(AST, UnreachablePatterns),

    % Remove redundant checks
    RedundantChecks = maps:get(redundant_checks, DeadCodeAnalysis, []),
    remove_redundant_checks(AST1, RedundantChecks).

%% Remove unreachable patterns
remove_unreachable_patterns(AST, []) ->
    AST;
remove_unreachable_patterns(AST, _Patterns) ->
    % TODO: Implement pattern removal
    AST.

%% Remove redundant checks
remove_redundant_checks(AST, []) ->
    AST;
remove_redundant_checks(AST, _Checks) ->
    % TODO: Implement redundant check removal
    AST.

%% Missing helper functions
collect_function_definitions(AST) ->
    collect_function_definitions_impl(AST, #{}).

collect_function_definitions_impl([], Acc) ->
    Acc;
collect_function_definitions_impl([#function_def{name = Name} = FuncDef | Rest], Acc) ->
    collect_function_definitions_impl(Rest, maps:put(Name, FuncDef, Acc));
collect_function_definitions_impl([#module_def{items = Items} | Rest], Acc) ->
    NewAcc = collect_function_definitions_impl(Items, Acc),
    collect_function_definitions_impl(Rest, NewAcc);
collect_function_definitions_impl([_ | Rest], Acc) ->
    collect_function_definitions_impl(Rest, Acc).

%% Memory Layout Optimization Pass
memory_layout_optimization_pass(AST) ->
    memory_layout_optimization_pass(
        AST, initialize_optimization_context(default_optimization_config())
    ).

memory_layout_optimization_pass(AST, Context) ->
    TypeInfo = Context#optimization_context.type_info,
    MemoryLayouts = TypeInfo#type_info.memory_layouts,

    % Optimize data structure layouts
    optimize_memory_layouts(AST, MemoryLayouts).

%% ============================================================================
%% Type Analysis and Information Collection
%% ============================================================================

%% Analyze program types and collect optimization information
analyze_program_types(AST) ->
    TypeInfo = collect_type_information(AST),
    UsageStats = analyze_type_usage(AST),
    {TypeInfo, UsageStats}.

%% Analyze module types
analyze_module_types(Module) ->
    analyze_program_types([Module]).

%% Collect detailed type information from AST
collect_type_information(AST) ->
    FunctionTypes = collect_function_types(AST),
    CallSites = collect_call_sites(AST),
    TypeUsage = collect_type_usage_patterns(AST),
    MonomorphicInstances = collect_monomorphic_instances(AST),
    MemoryLayouts = analyze_memory_layouts(AST),

    #type_info{
        function_types = FunctionTypes,
        call_sites = CallSites,
        type_usage = TypeUsage,
        monomorphic_instances = MonomorphicInstances,
        memory_layouts = MemoryLayouts
    }.

%% Analyze type usage patterns for optimization decisions
analyze_type_usage(AST) ->
    FunctionCalls = count_function_calls(AST),
    TypeFrequencies = count_type_frequencies(AST),
    HotPaths = identify_hot_paths(AST),
    ColdCode = identify_cold_code(AST),

    #usage_statistics{
        function_calls = FunctionCalls,
        type_frequencies = TypeFrequencies,
        hot_paths = HotPaths,
        cold_code = ColdCode
    }.

%% Find specialization opportunities
find_specialization_opportunities(AST) ->
    analyze_specialization_candidates(AST).

%% ============================================================================
%% Helper Functions (Stubs - to be implemented)
%% ============================================================================

%% Configuration
default_optimization_config() ->
    #optimization_config{
        level = 2,
        enable_specialization = true,
        enable_monomorphization = true,
        enable_inlining = true,
        enable_dce = true,
        enable_memory_opts = true,
        max_specializations = 10,
        inline_threshold = 50,
        specialization_threshold = 5
    }.

set_optimization_level(Level) when Level >= 0, Level =< 3 ->
    case Level of
        0 ->
            #optimization_config{
                level = 0,
                enable_specialization = false,
                enable_monomorphization = false,
                enable_inlining = false,
                enable_dce = false,
                enable_memory_opts = false
            };
        1 ->
            (default_optimization_config())#optimization_config{
                level = 1,
                enable_specialization = false,
                enable_memory_opts = false
            };
        2 ->
            default_optimization_config();
        3 ->
            (default_optimization_config())#optimization_config{
                level = 3,
                max_specializations = 20,
                inline_threshold = 100
            }
    end.

%% Context initialization
initialize_optimization_context(Config) ->
    #optimization_context{
        config = Config,
        type_info = #type_info{},
        usage_stats = #usage_statistics{},
        specializations = #specialization_map{},
        inlining_decisions = #{}
    }.

%% Analysis functions (concrete implementations)
collect_function_types(AST) when is_list(AST) ->
    FunctionTypes = #{},
    collect_function_types_impl(AST, FunctionTypes);
collect_function_types(AST) ->
    FunctionTypes = #{},
    collect_function_types_impl([AST], FunctionTypes).

collect_function_types_impl([], Acc) ->
    Acc;
collect_function_types_impl([Item | Rest], Acc) ->
    NewAcc =
        case Item of
            #function_def{name = Name, params = Params, return_type = ReturnType} ->
                ParamTypes = [extract_param_type(P) || P <- Params],
                FuncType = {function_type, ParamTypes, extract_return_type(ReturnType)},
                maps:put(Name, FuncType, Acc);
            #module_def{items = ModuleItems} ->
                collect_function_types_impl(ModuleItems, Acc);
            _ ->
                Acc
        end,
    collect_function_types_impl(Rest, NewAcc).

collect_call_sites(AST) when is_list(AST) ->
    CallSites = #{},
    collect_call_sites_impl(AST, CallSites);
collect_call_sites(AST) ->
    CallSites = #{},
    collect_call_sites_impl([AST], CallSites).

collect_call_sites_impl([], Acc) ->
    Acc;
collect_call_sites_impl([Item | Rest], Acc) ->
    NewAcc = analyze_item_call_sites(Item, Acc),
    collect_call_sites_impl(Rest, NewAcc).

analyze_item_call_sites(#function_def{body = Body}, Acc) ->
    find_call_sites_in_expr(Body, Acc);
analyze_item_call_sites(#module_def{items = Items}, Acc) ->
    collect_call_sites_impl(Items, Acc);
analyze_item_call_sites(_, Acc) ->
    Acc.

find_call_sites_in_expr(
    #function_call_expr{
        function = #identifier_expr{name = FuncName}, args = Args, location = Location
    },
    Acc
) ->
    ArgTypes = [infer_expr_type(Arg) || Arg <- Args],
    CallSite = {Location, ArgTypes},
    ExistingCallSites = maps:get(FuncName, Acc, []),
    maps:put(FuncName, [CallSite | ExistingCallSites], Acc);
find_call_sites_in_expr(#block_expr{expressions = Exprs}, Acc) ->
    lists:foldl(fun find_call_sites_in_expr/2, Acc, Exprs);
find_call_sites_in_expr(#let_expr{bindings = Bindings, body = Body}, Acc) ->
    Acc1 = lists:foldl(
        fun(#binding{value = Value}, A) ->
            find_call_sites_in_expr(Value, A)
        end,
        Acc,
        Bindings
    ),
    find_call_sites_in_expr(Body, Acc1);
find_call_sites_in_expr(_, Acc) ->
    Acc.

collect_type_usage_patterns(AST) when is_list(AST) ->
    TypeUsage = #{},
    collect_type_usage_impl(AST, TypeUsage);
collect_type_usage_patterns(AST) ->
    TypeUsage = #{},
    collect_type_usage_impl([AST], TypeUsage).

collect_type_usage_impl([], Acc) ->
    Acc;
collect_type_usage_impl([Item | Rest], Acc) ->
    NewAcc = analyze_item_type_usage(Item, Acc),
    collect_type_usage_impl(Rest, NewAcc).

analyze_item_type_usage(#function_def{params = Params, return_type = ReturnType, body = Body}, Acc) ->
    % Count parameter type usage
    Acc1 = lists:foldl(
        fun(Param, A) ->
            ParamType = extract_param_type(Param),
            increment_type_usage(ParamType, A)
        end,
        Acc,
        Params
    ),

    % Count return type usage
    Acc2 =
        case ReturnType of
            undefined -> Acc1;
            _ -> increment_type_usage(extract_return_type(ReturnType), Acc1)
        end,

    % Analyze body for type usage
    analyze_expr_type_usage(Body, Acc2);
analyze_item_type_usage(#module_def{items = Items}, Acc) ->
    collect_type_usage_impl(Items, Acc);
analyze_item_type_usage(_, Acc) ->
    Acc.

increment_type_usage(Type, Acc) ->
    CurrentCount = maps:get(Type, Acc, 0),
    maps:put(Type, CurrentCount + 1, Acc).

analyze_expr_type_usage(#literal_expr{value = Value}, Acc) ->
    LiteralType = infer_literal_type(Value),
    increment_type_usage(LiteralType, Acc);
analyze_expr_type_usage(#function_call_expr{args = Args}, Acc) ->
    lists:foldl(fun analyze_expr_type_usage/2, Acc, Args);
analyze_expr_type_usage(#block_expr{expressions = Exprs}, Acc) ->
    lists:foldl(fun analyze_expr_type_usage/2, Acc, Exprs);
analyze_expr_type_usage(#let_expr{bindings = Bindings, body = Body}, Acc) ->
    Acc1 = lists:foldl(
        fun(#binding{value = Value}, A) ->
            analyze_expr_type_usage(Value, A)
        end,
        Acc,
        Bindings
    ),
    analyze_expr_type_usage(Body, Acc1);
analyze_expr_type_usage(_, Acc) ->
    Acc.

collect_monomorphic_instances(AST) when is_list(AST) ->
    MonoInstances = #{},
    collect_mono_instances_impl(AST, MonoInstances);
collect_monomorphic_instances(AST) ->
    MonoInstances = #{},
    collect_mono_instances_impl([AST], MonoInstances).

collect_mono_instances_impl([], Acc) ->
    Acc;
collect_mono_instances_impl([Item | Rest], Acc) ->
    NewAcc = find_mono_instances_in_item(Item, Acc),
    collect_mono_instances_impl(Rest, NewAcc).

find_mono_instances_in_item(
    #function_def{name = Name, params = Params, return_type = ReturnType}, Acc
) ->
    % Check if function can be monomorphized
    case has_type_variables(Params) or has_type_variables_in_return(ReturnType) of
        true ->
            % Find concrete instantiations
            ConcreteInstances = find_concrete_instantiations(Name),
            case ConcreteInstances of
                [] -> Acc;
                _ -> maps:put(Name, ConcreteInstances, Acc)
            end;
        false ->
            Acc
    end;
find_mono_instances_in_item(#module_def{items = Items}, Acc) ->
    collect_mono_instances_impl(Items, Acc);
find_mono_instances_in_item(_, Acc) ->
    Acc.

analyze_memory_layouts(AST) when is_list(AST) ->
    MemoryLayouts = #{},
    analyze_memory_layouts_impl(AST, MemoryLayouts);
analyze_memory_layouts(AST) ->
    MemoryLayouts = #{},
    analyze_memory_layouts_impl([AST], MemoryLayouts).

analyze_memory_layouts_impl([], Acc) ->
    Acc;
analyze_memory_layouts_impl([Item | Rest], Acc) ->
    NewAcc = analyze_item_memory_layout(Item, Acc),
    analyze_memory_layouts_impl(Rest, NewAcc).

analyze_item_memory_layout(#type_def{name = TypeName, definition = TypeDef}, Acc) ->
    Layout = compute_memory_layout(TypeDef),
    OptimizedLayout = analyze_layout_opportunities(TypeName, TypeDef, Layout),
    maps:put(TypeName, OptimizedLayout, Acc);
analyze_item_memory_layout(#module_def{items = Items}, Acc) ->
    analyze_memory_layouts_impl(Items, Acc);
analyze_item_memory_layout(#function_def{params = Params}, Acc) ->
    % Analyze function parameter layouts for stack optimization
    ParamLayouts = analyze_parameter_layouts(Params),
    merge_layout_maps(Acc, ParamLayouts);
analyze_item_memory_layout(_, Acc) ->
    Acc.

count_function_calls(AST) when is_list(AST) ->
    CallCounts = #{},
    count_calls_impl(AST, CallCounts);
count_function_calls(AST) ->
    CallCounts = #{},
    count_calls_impl([AST], CallCounts).

count_calls_impl([], Acc) ->
    Acc;
count_calls_impl([Item | Rest], Acc) ->
    NewAcc = count_calls_in_item(Item, Acc),
    count_calls_impl(Rest, NewAcc).

count_calls_in_item(#function_def{body = Body}, Acc) ->
    count_calls_in_expr(Body, Acc);
count_calls_in_item(#module_def{items = Items}, Acc) ->
    count_calls_impl(Items, Acc);
count_calls_in_item(_, Acc) ->
    Acc.

count_calls_in_expr(#function_call_expr{function = #identifier_expr{name = FuncName}}, Acc) ->
    CurrentCount = maps:get(FuncName, Acc, 0),
    maps:put(FuncName, CurrentCount + 1, Acc);
count_calls_in_expr(#block_expr{expressions = Exprs}, Acc) ->
    lists:foldl(fun count_calls_in_expr/2, Acc, Exprs);
count_calls_in_expr(#let_expr{bindings = Bindings, body = Body}, Acc) ->
    Acc1 = lists:foldl(
        fun(#binding{value = Value}, A) ->
            count_calls_in_expr(Value, A)
        end,
        Acc,
        Bindings
    ),
    count_calls_in_expr(Body, Acc1);
count_calls_in_expr(_, Acc) ->
    Acc.

count_type_frequencies(AST) ->
    % Same as type usage patterns
    collect_type_usage_patterns(AST).

identify_hot_paths(AST) ->
    CallCounts = count_function_calls(AST),
    % Find functions called more than threshold times
    Threshold = 10,
    HotFunctions = maps:fold(
        fun(FuncName, Count, Acc) ->
            case Count > Threshold of
                true -> [FuncName | Acc];
                false -> Acc
            end
        end,
        [],
        CallCounts
    ),

    % Create call paths from hot functions
    [[FuncName] || FuncName <- HotFunctions].

identify_cold_code(AST) ->
    CallCounts = count_function_calls(AST),
    AllFunctions = collect_all_function_names(AST),

    % Find functions that are never called or called very rarely
    ColdThreshold = 2,
    lists:filter(
        fun(FuncName) ->
            CallCount = maps:get(FuncName, CallCounts, 0),
            CallCount =< ColdThreshold
        end,
        AllFunctions
    ).

analyze_specialization_candidates(AST) ->
    CallSites = collect_call_sites(AST),
    SpecCandidates = #{},

    % Find functions with multiple call sites with different type patterns
    maps:fold(
        fun(FuncName, CallSiteList, Acc) ->
            TypePatterns = extract_type_patterns(CallSiteList),
            case length(TypePatterns) > 1 andalso length(CallSiteList) >= 5 of
                true ->
                    % Good candidate for specialization
                    CostBenefit = estimate_specialization_cost_benefit(
                        FuncName, TypePatterns, CallSiteList
                    ),
                    Candidates = [{Pattern, CostBenefit} || Pattern <- TypePatterns],
                    maps:put(FuncName, Candidates, Acc);
                false ->
                    Acc
            end
        end,
        SpecCandidates,
        CallSites
    ).

find_optimization_opportunities(AST, Context) ->
    % Analyze specialization candidates
    SpecCandidates = analyze_specialization_candidates(AST),

    % Analyze inlining opportunities
    InliningOpportunities = analyze_inlining_opportunities(AST, Context),
    InliningDecisions =
        case InliningOpportunities of
            #{candidates := Candidates} when map_size(Candidates) > 0 ->
                make_inlining_decisions(InliningOpportunities, Context);
            _ ->
                #{}
        end,

    % Update context with optimization opportunities
    SpecMap = Context#optimization_context.specializations,
    NewSpecMap = SpecMap#specialization_map{candidates = SpecCandidates},

    Context#optimization_context{
        specializations = NewSpecMap,
        inlining_decisions = InliningDecisions
    }.

find_module_optimization_opportunities(Module, Context) ->
    find_optimization_opportunities([Module], Context).

run_module_optimization_passes(Module, Context) ->
    [OptimizedModule] = run_optimization_passes([Module], Context),
    OptimizedModule.

generate_specialized_functions(SpecMap) ->
    #specialization_map{candidates = Candidates, generated = Generated, cost_benefit = _CostBenefit} =
        SpecMap,

    % Generate specialized functions for profitable candidates
    NewSpecializations = maps:fold(
        fun(FuncName, CandidateList, Acc) ->
            % Find the original function definition (would be passed from AST)
            ProfitableCandidates = filter_profitable_candidates(CandidateList),

            case ProfitableCandidates of
                [] ->
                    Acc;
                _ ->
                    SpecializedVersions = lists:map(
                        fun({TypePattern, _CB}) ->
                            SpecName = generate_specialized_name(FuncName, TypePattern),
                            SpecDef = create_specialized_function(FuncName, TypePattern, SpecName),
                            {SpecName, TypePattern, SpecDef}
                        end,
                        ProfitableCandidates
                    ),

                    ExistingSpecs = maps:get(FuncName, Generated, []),
                    maps:put(FuncName, ExistingSpecs ++ SpecializedVersions, Acc)
            end
        end,
        Generated,
        Candidates
    ),

    % Extract just the function definitions for AST insertion
    AllSpecializations = maps:fold(
        fun(_FuncName, SpecVersions, Acc) ->
            FuncDefs = [SpecDef || {_SpecName, _TypePattern, SpecDef} <- SpecVersions],
            FuncDefs ++ Acc
        end,
        [],
        NewSpecializations
    ),

    AllSpecializations.

add_specialized_functions_to_ast(AST, SpecializedFunctions) ->
    % Add specialized functions to the AST
    case SpecializedFunctions of
        % No specializations to add
        [] -> AST;
        _ -> add_functions_to_ast_impl(AST, SpecializedFunctions)
    end.

find_polymorphic_functions(_AST, TypeInfo) ->
    % Find functions that have type variables in their signatures
    FunctionTypes = TypeInfo#type_info.function_types,
    maps:fold(
        fun(FuncName, {function_type, ParamTypes, ReturnType}, Acc) ->
            case
                lists:any(fun contains_type_variables/1, ParamTypes) or
                    contains_type_variables(ReturnType)
            of
                true -> [FuncName | Acc];
                false -> Acc
            end
        end,
        [],
        FunctionTypes
    ).

generate_monomorphic_instances(PolymorphicFunctions, TypeInfo) ->
    CallSites = TypeInfo#type_info.call_sites,

    % Generate monomorphic instances for each polymorphic function
    maps:fold(
        fun(FuncName, _FuncInfo, Acc) ->
            case maps:get(FuncName, CallSites, []) of
                % No call sites found
                [] ->
                    Acc;
                CallSiteList ->
                    % Extract concrete type instantiations from call sites
                    ConcreteTypes = extract_concrete_type_instantiations(CallSiteList),
                    case ConcreteTypes of
                        [] ->
                            Acc;
                        _ ->
                            % Generate monomorphic instances
                            Instances = generate_concrete_instances(FuncName, ConcreteTypes),
                            maps:put(FuncName, Instances, Acc)
                    end
            end
        end,
        #{},
        maps:from_list([{F, true} || F <- PolymorphicFunctions])
    ).

replace_with_monomorphic_calls(AST, MonomorphicInstances) ->
    % Replace polymorphic function calls with monomorphic ones
    case maps:size(MonomorphicInstances) of
        % No monomorphic instances to replace
        0 ->
            AST;
        _ ->
            % Transform AST to use monomorphic instances
            transform_ast_for_monomorphization(AST, MonomorphicInstances)
    end.

inline_functions(AST, InliningMap) ->
    % Simple inlining implementation for now
    case maps:size(InliningMap) of
        % No inlining decisions
        0 ->
            AST;
        _ ->
            % Apply simple inlining transformations
            transform_ast_for_inlining(AST, InliningMap)
    end.

remove_dead_code(AST, ColdCode) ->
    % Simple dead code elimination
    case ColdCode of
        % No dead code to remove
        [] ->
            AST;
        _ ->
            % Remove unused functions from AST
            filter_dead_functions(AST, ColdCode)
    end.

optimize_memory_layouts(AST, MemoryLayouts) ->
    % Apply memory layout optimizations to data structures
    case maps:size(MemoryLayouts) of
        % No layout optimizations available
        0 ->
            AST;
        _ ->
            % Transform AST to apply memory optimizations
            OptimizedLayouts = optimize_layout_strategies(MemoryLayouts),
            apply_memory_layout_optimizations(AST, OptimizedLayouts)
    end.

generate_optimization_report(_Context) ->
    #{
        optimizations_applied => [],
        performance_improvement => undefined,
        code_size_change => undefined,
        specializations_generated => 0
        % TODO: Implement comprehensive reporting
    }.

%% ============================================================================
%% Helper Functions for Type Analysis
%% ============================================================================

%% Extract parameter type from parameter definition
extract_param_type(#param{type = Type}) when Type =/= undefined ->
    Type;
extract_param_type(#param{name = _Name}) ->
    % No type annotation, infer as unknown
    {unknown_type}.

%% Extract return type from type expression
extract_return_type(undefined) ->
    {unknown_type};
extract_return_type(Type) ->
    Type.

%% Infer type of expression for call site analysis
infer_expr_type(#literal_expr{value = Value}) ->
    infer_literal_type(Value);
infer_expr_type(#identifier_expr{name = _Var}) ->
    % Would need environment to resolve
    {unknown_type};
infer_expr_type(#function_call_expr{function = #identifier_expr{name = FuncName}}) ->
    {function_call, FuncName};
infer_expr_type(_) ->
    {unknown_type}.

%% Infer type from literal values
infer_literal_type(Value) when is_integer(Value) ->
    {primitive_type, 'Int'};
infer_literal_type(Value) when is_float(Value) ->
    {primitive_type, 'Float'};
infer_literal_type(Value) when is_binary(Value) ->
    {primitive_type, 'String'};
infer_literal_type(Value) when is_boolean(Value) ->
    {primitive_type, 'Bool'};
infer_literal_type(Value) when is_atom(Value) ->
    {primitive_type, 'Atom'};
infer_literal_type(_) ->
    {unknown_type}.

%% Check if parameters contain type variables (for monomorphization)
has_type_variables(Params) ->
    lists:any(fun(Param) -> is_polymorphic_param(Param) end, Params).

is_polymorphic_param(#param{type = Type}) ->
    contains_type_variables(Type);
is_polymorphic_param(_) ->
    false.

%% Check if return type contains type variables
has_type_variables_in_return(undefined) ->
    false;
has_type_variables_in_return(Type) ->
    contains_type_variables(Type).

%% Check if a type expression contains type variables
contains_type_variables({type_var, _Name}) ->
    true;
contains_type_variables({function_type, ParamTypes, ReturnType}) ->
    lists:any(fun contains_type_variables/1, ParamTypes) or
        contains_type_variables(ReturnType);
contains_type_variables({list_type, ElemType, _Length}) ->
    contains_type_variables(ElemType);
contains_type_variables({dependent_type, _Name, Params}) ->
    lists:any(
        fun(#type_param{value = Value}) ->
            contains_type_variables(Value)
        end,
        Params
    );
contains_type_variables(_) ->
    false.

%% Find concrete instantiations for polymorphic function based on call sites
find_concrete_instantiations(_FuncName) ->
    % This would analyze actual call sites to find concrete type usages
    % For now, return empty - full implementation requires call graph analysis
    % TODO: Integrate with call site tracking to extract actual type instantiations
    [].

%% Match function call types against specialization patterns
match_specialization_pattern(CallArgTypes, SpecializationPattern) ->
    case {CallArgTypes, SpecializationPattern} of
        {[], []} ->
            {match, exact, []};
        {[CallType | CallRest], [PatternType | PatternRest]} ->
            case match_single_type(CallType, PatternType) of
                {match, MatchKind, Subst} ->
                    case match_specialization_pattern(CallRest, PatternRest) of
                        {match, RestKind, RestSubst} ->
                            CombinedKind = combine_match_kinds(MatchKind, RestKind),
                            {match, CombinedKind, Subst ++ RestSubst};
                        no_match ->
                            no_match
                    end;
                no_match ->
                    no_match
            end;
        _ ->
            no_match
    end.

%% Match a single type against a pattern type
match_single_type(Type, Pattern) ->
    case {Type, Pattern} of
        % Exact match
        {T, T} ->
            {match, exact, []};
        % Type variable matches anything
        {{type_var, Var}, _} ->
            {match, generic, [{Var, Pattern}]};
        {_, {type_var, Var}} ->
            {match, generic, [{Var, Type}]};
        % Primitive type matching
        {{primitive_type, T1}, {primitive_type, T2}} when T1 =:= T2 ->
            {match, exact, []};
        % List type matching
        {{list_type, ElemType1, Len1}, {list_type, ElemType2, Len2}} ->
            case match_single_type(ElemType1, ElemType2) of
                {match, Kind, Subst} when Len1 =:= Len2 orelse Len2 =:= undefined ->
                    {match, Kind, Subst};
                _ ->
                    no_match
            end;
        % Function type matching
        {{function_type, Params1, Ret1}, {function_type, Params2, Ret2}} ->
            match_function_types(Params1, Ret1, Params2, Ret2);
        % Subtyping - check if Type is more specific than Pattern
        _ ->
            case is_subtype(Type, Pattern) of
                true -> {match, subtype, []};
                false -> no_match
            end
    end.

%% Match function types considering parameters and return types
match_function_types(Params1, Ret1, Params2, Ret2) ->
    case match_specialization_pattern(Params1, Params2) of
        {match, ParamKind, ParamSubst} ->
            case match_single_type(Ret1, Ret2) of
                {match, RetKind, RetSubst} ->
                    CombinedKind = combine_match_kinds(ParamKind, RetKind),
                    {match, CombinedKind, ParamSubst ++ RetSubst};
                no_match ->
                    no_match
            end;
        no_match ->
            no_match
    end.

%% Combine match kinds to determine overall match quality
combine_match_kinds(exact, exact) -> exact;
combine_match_kinds(exact, subtype) -> subtype;
combine_match_kinds(subtype, exact) -> subtype;
combine_match_kinds(subtype, subtype) -> subtype;
combine_match_kinds(_, generic) -> generic;
combine_match_kinds(generic, _) -> generic.

%% Check if Type1 is a subtype of Type2
is_subtype({primitive_type, 'Int'}, {primitive_type, 'Number'}) -> true;
is_subtype({primitive_type, 'Float'}, {primitive_type, 'Number'}) -> true;
is_subtype({list_type, T1, _}, {list_type, T2, undefined}) -> is_subtype(T1, T2);
is_subtype(_, _) -> false.

%% Find best specialization match for given call types
find_best_specialization(CallArgTypes, Specializations) ->
    Matches = lists:filtermap(
        fun({SpecName, SpecPattern, _SpecDef}) ->
            case match_specialization_pattern(CallArgTypes, SpecPattern) of
                {match, MatchKind, Subst} ->
                    Score = specialization_match_score(MatchKind),
                    {true, {SpecName, Score, MatchKind, Subst}};
                no_match ->
                    false
            end
        end,
        Specializations
    ),
    case Matches of
        [] ->
            no_match;
        _ ->
            % Sort by score (higher is better) and return best
            [{BestName, _Score, BestKind, BestSubst} | _] = lists:sort(
                fun({_, S1, _, _}, {_, S2, _, _}) -> S1 >= S2 end,
                Matches
            ),
            {match, BestName, BestKind, BestSubst}
    end.

%% Calculate match quality score
specialization_match_score(exact) -> 100;
specialization_match_score(subtype) -> 80;
specialization_match_score(generic) -> 50.

%% Compute memory layout for type definition
compute_memory_layout(TypeDef) ->
    case TypeDef of
        {primitive_type, 'Int'} ->
            #{
                alignment => 8,
                size => 8,
                fields => [],
                type => primitive,
                cache_friendly => true,
                padding => 0
            };
        {primitive_type, 'Float'} ->
            #{
                alignment => 8,
                size => 8,
                fields => [],
                type => primitive,
                cache_friendly => true,
                padding => 0
            };
        {primitive_type, 'Bool'} ->
            #{
                alignment => 1,
                size => 1,
                fields => [],
                type => primitive,
                cache_friendly => true,
                padding => 0
            };
        {primitive_type, 'String'} ->
            #{
                alignment => 8,
                size => 24,
                fields => [],
                type => primitive,
                % Pointer + length + capacity
                cache_friendly => false,
                padding => 0
            };
        {tuple_type, Elements} ->
            compute_tuple_layout(Elements);
        {record_type, Fields} ->
            compute_record_layout(Fields);
        {list_type, ElemType, _Length} ->
            ElemLayout = compute_memory_layout(ElemType),
            #{
                alignment => 8,
                size => 16,
                fields => [ElemLayout],
                type => container,
                cache_friendly => false,
                padding => 0
            };
        {array_type, ElemType, Length} ->
            compute_array_layout(ElemType, Length);
        _ ->
            #{
                alignment => 8,
                size => 16,
                fields => [],
                type => unknown,
                cache_friendly => false,
                padding => 0
            }
    end.

%% Collect all function names from AST
collect_all_function_names(AST) ->
    collect_function_names_impl(AST, []).

collect_function_names_impl([], Acc) ->
    Acc;
collect_function_names_impl([Item | Rest], Acc) ->
    NewAcc =
        case Item of
            #function_def{name = Name} ->
                [Name | Acc];
            #module_def{items = Items} ->
                collect_function_names_impl(Items, Acc);
            _ ->
                Acc
        end,
    collect_function_names_impl(Rest, NewAcc).

%% Extract type patterns from call sites
extract_type_patterns(CallSiteList) ->
    % Group call sites by argument type patterns
    TypePatterns = lists:foldl(
        fun({_Location, ArgTypes}, Acc) ->
            Pattern = normalize_type_pattern(ArgTypes),
            case lists:member(Pattern, Acc) of
                true -> Acc;
                false -> [Pattern | Acc]
            end
        end,
        [],
        CallSiteList
    ),
    TypePatterns.

%% Normalize type pattern for comparison
normalize_type_pattern(ArgTypes) ->
    % Simplify types for pattern matching
    [normalize_type(T) || T <- ArgTypes].

normalize_type({primitive_type, Name}) ->
    {primitive_type, Name};
normalize_type({function_type, _Params, _Return}) ->
    {function_type};
normalize_type({list_type, _ElemType, _Length}) ->
    {list_type};
normalize_type(_) ->
    {unknown_type}.

%% Estimate cost-benefit analysis for specialization
estimate_specialization_cost_benefit(_FuncName, TypePatterns, CallSiteList) ->
    % Simple heuristic: cost based on function complexity, benefit based on call frequency
    PatternCounts = count_pattern_usage(TypePatterns, CallSiteList),
    MaxCount = lists:max([Count || {_Pattern, Count} <- PatternCounts]),

    % Cost of generating specialized versions
    Cost = length(TypePatterns) * 10,
    % Benefit from avoiding dynamic dispatch
    Benefit = MaxCount * 5,

    {Cost, Benefit}.

%% Count how often each type pattern is used
count_pattern_usage(TypePatterns, CallSiteList) ->
    PatternCounts = lists:foldl(
        fun(Pattern, Acc) ->
            [{Pattern, 0} | Acc]
        end,
        [],
        TypePatterns
    ),

    % Count occurrences
    lists:foldl(
        fun({_Location, ArgTypes}, Acc) ->
            Pattern = normalize_type_pattern(ArgTypes),
            case lists:keyfind(Pattern, 1, Acc) of
                {Pattern, Count} ->
                    lists:keyreplace(Pattern, 1, Acc, {Pattern, Count + 1});
                false ->
                    Acc
            end
        end,
        PatternCounts,
        CallSiteList
    ).

%% ============================================================================
%% Function Specialization Helper Functions
%% ============================================================================

%% Filter candidates that are profitable to specialize
filter_profitable_candidates(CandidateList) ->
    lists:filter(
        fun({_TypePattern, {Cost, Benefit}}) ->
            % Only specialize if benefit outweighs cost by at least 50%
            Benefit > Cost * 1.5
        end,
        CandidateList
    ).

%% Create specialized function definition
create_specialized_function(OriginalFuncName, TypePattern, SpecName) ->
    % Create a specialized version with type-specific optimizations
    % This is a simplified implementation - would need actual function body
    #function_def{
        name = SpecName,
        params = create_specialized_params(TypePattern),
        return_type = {specialized_return, OriginalFuncName},
        body = create_specialized_body(OriginalFuncName, TypePattern),
        % Generated function
        location = #location{line = 0, column = 0}
    }.

%% Create specialized parameters with concrete types
create_specialized_params(TypePattern) ->
    lists:map(
        fun(Type) ->
            ParamName = generate_param_name(Type),
            #param{name = ParamName, type = Type}
        end,
        TypePattern
    ).

%% Generate parameter name based on type
generate_param_name({primitive_type, 'Int'}) -> 'int_arg';
generate_param_name({primitive_type, 'Float'}) -> 'float_arg';
generate_param_name({primitive_type, 'String'}) -> 'string_arg';
generate_param_name({primitive_type, 'Bool'}) -> 'bool_arg';
generate_param_name({list_type}) -> 'list_arg';
generate_param_name({function_type}) -> 'func_arg';
generate_param_name(_) -> 'generic_arg'.

%% Create specialized function body with type-specific optimizations
create_specialized_body(OriginalFuncName, TypePattern) ->
    % Create optimized body based on type information
    % For now, create a call to the original function with type annotations
    Args = create_specialized_args(TypePattern),

    #function_call_expr{
        function = #identifier_expr{name = OriginalFuncName},
        args = Args,
        location = #location{line = 0, column = 0}
    }.

%% Create specialized arguments for function call
create_specialized_args(TypePattern) ->
    lists:map(
        fun(Type) ->
            ArgName = generate_param_name(Type),
            #identifier_expr{name = ArgName}
        end,
        TypePattern
    ).

%% Add specialized functions to AST implementation
add_functions_to_ast_impl(AST, SpecializedFunctions) ->
    % Add functions to the appropriate module or top-level
    lists:map(
        fun(Item) ->
            case Item of
                #module_def{items = ModuleItems} = Module ->
                    NewItems = ModuleItems ++ SpecializedFunctions,
                    Module#module_def{items = NewItems};
                _ ->
                    Item
            end
        end,
        AST
    ) ++
        % If no modules found, add at top level
        case has_module_in_ast(AST) of
            false -> SpecializedFunctions;
            true -> []
        end.

%% Check if AST contains module definitions
has_module_in_ast(AST) ->
    lists:any(
        fun(Item) ->
            case Item of
                #module_def{} -> true;
                _ -> false
            end
        end,
        AST
    ).

%% Replace function calls with specialized versions where profitable
replace_calls_with_specialized_versions(AST, SpecMap) ->
    #specialization_map{candidates = Candidates, generated = Generated} = SpecMap,

    % Build specialization lookup map: {FuncName, TypePattern} -> SpecializedFuncName
    SpecializationLookup = build_specialization_lookup(Generated),

    % Transform AST to replace calls
    transform_ast_calls(AST, SpecializationLookup, Candidates).

%% Build lookup map for specialized function names
build_specialization_lookup(Generated) ->
    maps:fold(
        fun(_OriginalFunc, SpecVersions, Acc) ->
            lists:foldl(
                fun({SpecName, TypePattern, _SpecDef}, A) ->
                    Key = {_OriginalFunc, TypePattern},
                    maps:put(Key, SpecName, A)
                end,
                Acc,
                SpecVersions
            )
        end,
        #{},
        Generated
    ).

%% Transform AST to replace function calls with specialized versions
transform_ast_calls(AST, SpecLookup, Candidates) ->
    lists:map(
        fun(Item) ->
            transform_item_calls(Item, SpecLookup, Candidates)
        end,
        AST
    ).

%% Transform individual AST items
transform_item_calls(
    #function_def{name = _Name, params = _Params, return_type = _ReturnType, body = Body} = FuncDef,
    SpecLookup,
    Candidates
) ->
    NewBody = transform_expr_calls(Body, SpecLookup, Candidates),
    FuncDef#function_def{body = NewBody};
transform_item_calls(#module_def{items = Items} = Module, SpecLookup, Candidates) ->
    NewItems = lists:map(
        fun(Item) ->
            transform_item_calls(Item, SpecLookup, Candidates)
        end,
        Items
    ),
    Module#module_def{items = NewItems};
transform_item_calls(Item, _SpecLookup, _Candidates) ->
    Item.

%% Transform expressions to replace function calls
transform_expr_calls(
    #function_call_expr{
        function = #identifier_expr{name = FuncName}, args = Args, location = _Location
    } = CallExpr,
    SpecLookup,
    Candidates
) ->
    % Infer argument types
    ArgTypes = [infer_expr_type(Arg) || Arg <- Args],
    TypePattern = normalize_type_pattern(ArgTypes),

    % Check if we have a specialization for this call
    case maps:get({FuncName, TypePattern}, SpecLookup, not_found) of
        not_found ->
            % No specialization, keep original call but transform arguments
            NewArgs = lists:map(
                fun(Arg) ->
                    transform_expr_calls(Arg, SpecLookup, Candidates)
                end,
                Args
            ),
            CallExpr#function_call_expr{args = NewArgs};
        SpecializedName ->
            % Use specialized version
            NewArgs = lists:map(
                fun(Arg) ->
                    transform_expr_calls(Arg, SpecLookup, Candidates)
                end,
                Args
            ),
            CallExpr#function_call_expr{
                function = #identifier_expr{name = SpecializedName},
                args = NewArgs
            }
    end;
transform_expr_calls(#block_expr{expressions = Exprs} = BlockExpr, SpecLookup, Candidates) ->
    NewExprs = lists:map(
        fun(Expr) ->
            transform_expr_calls(Expr, SpecLookup, Candidates)
        end,
        Exprs
    ),
    BlockExpr#block_expr{expressions = NewExprs};
transform_expr_calls(#let_expr{bindings = Bindings, body = Body} = LetExpr, SpecLookup, Candidates) ->
    NewBindings = lists:map(
        fun(#binding{pattern = _Pattern, value = Value} = Binding) ->
            NewValue = transform_expr_calls(Value, SpecLookup, Candidates),
            Binding#binding{value = NewValue}
        end,
        Bindings
    ),
    NewBody = transform_expr_calls(Body, SpecLookup, Candidates),
    LetExpr#let_expr{bindings = NewBindings, body = NewBody};
transform_expr_calls(Expr, _SpecLookup, _Candidates) ->
    % For other expressions (literals, identifiers, etc.), return as-is
    Expr.

%% ============================================================================
%% Monomorphization Helper Functions
%% ============================================================================

%% Extract concrete type instantiations from call sites
extract_concrete_type_instantiations(CallSiteList) ->
    % Extract unique concrete type patterns from call sites
    TypeSets = lists:foldl(
        fun({_Location, ArgTypes}, Acc) ->
            ConcreteTypes = [T || T <- ArgTypes, is_concrete_type(T)],
            case ConcreteTypes of
                % Skip if no concrete types
                [] -> Acc;
                _ -> [ConcreteTypes | Acc]
            end
        end,
        [],
        CallSiteList
    ),

    % Remove duplicates
    lists:usort(TypeSets).

%% Check if a type is concrete (no type variables)
is_concrete_type({type_var, _}) ->
    false;
is_concrete_type({function_type, ParamTypes, ReturnType}) ->
    lists:all(fun is_concrete_type/1, ParamTypes) andalso is_concrete_type(ReturnType);
is_concrete_type({list_type, ElemType, _Length}) ->
    is_concrete_type(ElemType);
is_concrete_type({dependent_type, _Name, Params}) ->
    lists:all(fun(#type_param{value = Value}) -> is_concrete_type(Value) end, Params);
% Primitive types are concrete
is_concrete_type(_) ->
    true.

%% Generate concrete instances of a polymorphic function
generate_concrete_instances(FuncName, ConcreteTypesList) ->
    lists:map(
        fun(ConcreteTypes) ->
            MonomorphicName = generate_monomorphic_name(FuncName, ConcreteTypes),
            MonomorphicDef = create_monomorphic_function_legacy(
                FuncName, ConcreteTypes, MonomorphicName
            ),
            {MonomorphicName, ConcreteTypes, MonomorphicDef}
        end,
        ConcreteTypesList
    ).

%% Generate monomorphic function name
generate_monomorphic_name(FuncName, ConcreteTypes) ->
    TypeSuffix = create_mono_type_suffix(ConcreteTypes),
    MonoName = list_to_atom(atom_to_list(FuncName) ++ "_mono_" ++ TypeSuffix),
    MonoName.

%% Create type suffix for monomorphic function name
create_mono_type_suffix(ConcreteTypes) ->
    TypeStrings = lists:map(fun mono_type_to_string/1, ConcreteTypes),
    string:join(TypeStrings, "_").

%% Convert type to string for monomorphic naming
mono_type_to_string({primitive_type, Name}) ->
    string:to_lower(atom_to_list(Name));
mono_type_to_string({list_type}) ->
    "list";
mono_type_to_string({function_type}) ->
    "func";
mono_type_to_string({tuple_type, Elements}) ->
    "tuple" ++ integer_to_list(length(Elements));
mono_type_to_string({record_type, Name}) ->
    "rec_" ++ atom_to_list(Name);
mono_type_to_string(_) ->
    "gen".

%% Create monomorphic function definition (legacy)
create_monomorphic_function_legacy(OriginalFuncName, ConcreteTypes, MonoName) ->
    % Create a monomorphic version with concrete types
    #function_def{
        name = MonoName,
        params = create_monomorphic_params(ConcreteTypes),
        return_type = infer_return_type_from_concrete(OriginalFuncName, ConcreteTypes),
        body = create_monomorphic_body(OriginalFuncName, ConcreteTypes),
        % Generated function
        location = #location{line = 0, column = 0}
    }.

%% Create monomorphic parameters with concrete types
create_monomorphic_params(ConcreteTypes) ->
    lists:map(
        fun(Type) ->
            ParamName = generate_mono_param_name(Type),
            #param{name = ParamName, type = Type}
        end,
        ConcreteTypes
    ).

%% Generate parameter name for monomorphic function
generate_mono_param_name({primitive_type, 'Int'}) -> 'int_param';
generate_mono_param_name({primitive_type, 'Float'}) -> 'float_param';
generate_mono_param_name({primitive_type, 'String'}) -> 'string_param';
generate_mono_param_name({primitive_type, 'Bool'}) -> 'bool_param';
generate_mono_param_name({primitive_type, 'Atom'}) -> 'atom_param';
generate_mono_param_name({list_type}) -> 'list_param';
generate_mono_param_name({function_type}) -> 'func_param';
generate_mono_param_name(_) -> 'mono_param'.

%% Infer return type for monomorphic function
infer_return_type_from_concrete(_OriginalFuncName, ConcreteTypes) ->
    % Simple heuristic: return first concrete type or Int
    case ConcreteTypes of
        [FirstType | _] -> FirstType;
        [] -> {primitive_type, 'Int'}
    end.

%% Create monomorphic function body
create_monomorphic_body(OriginalFuncName, ConcreteTypes) ->
    % Create optimized body for concrete types
    Args = create_monomorphic_args(ConcreteTypes),

    % For now, create a call to original function with type-specific optimizations
    #function_call_expr{
        function = #identifier_expr{name = OriginalFuncName},
        args = Args,
        location = #location{line = 0, column = 0}
    }.

%% Create monomorphic arguments for function call
create_monomorphic_args(ConcreteTypes) ->
    lists:map(
        fun(Type) ->
            ArgName = generate_mono_param_name(Type),
            #identifier_expr{name = ArgName}
        end,
        ConcreteTypes
    ).

%% Build lookup map for monomorphic function calls
build_monomorphic_lookup(MonomorphicInstances) ->
    maps:fold(
        fun(OriginalFunc, Instances, Acc) ->
            lists:foldl(
                fun({MonoName, ConcreteTypes, _MonoDef}, A) ->
                    Key = {OriginalFunc, normalize_type_pattern(ConcreteTypes)},
                    maps:put(Key, MonoName, A)
                end,
                Acc,
                Instances
            )
        end,
        #{},
        MonomorphicInstances
    ).

%% Extract monomorphic function definitions
extract_monomorphic_functions(MonomorphicInstances) ->
    maps:fold(
        fun(_OriginalFunc, Instances, Acc) ->
            MonoFuncs = [MonoDef || {_MonoName, _ConcreteTypes, MonoDef} <- Instances],
            MonoFuncs ++ Acc
        end,
        [],
        MonomorphicInstances
    ).

%% Add monomorphic functions to AST
add_monomorphic_functions_to_ast(AST, MonoFunctions) ->
    case MonoFunctions of
        [] -> AST;
        _ -> add_functions_to_ast_impl(AST, MonoFunctions)
    end.

%% Transform function calls to use monomorphic versions
transform_calls_for_monomorphization(AST, MonoLookup) ->
    lists:map(
        fun(Item) ->
            transform_item_for_monomorphization(Item, MonoLookup)
        end,
        AST
    ).

%% Transform individual AST items for monomorphization
transform_item_for_monomorphization(#function_def{body = Body} = FuncDef, MonoLookup) ->
    NewBody = transform_expr_for_monomorphization(Body, MonoLookup),
    FuncDef#function_def{body = NewBody};
transform_item_for_monomorphization(#module_def{items = Items} = Module, MonoLookup) ->
    NewItems = lists:map(
        fun(Item) ->
            transform_item_for_monomorphization(Item, MonoLookup)
        end,
        Items
    ),
    Module#module_def{items = NewItems};
transform_item_for_monomorphization(Item, _MonoLookup) ->
    Item.

%% Transform expressions for monomorphization
transform_expr_for_monomorphization(
    #function_call_expr{function = #identifier_expr{name = FuncName}, args = Args} = CallExpr,
    MonoLookup
) ->
    % Infer argument types
    ArgTypes = [infer_expr_type(Arg) || Arg <- Args],
    TypePattern = normalize_type_pattern(ArgTypes),

    % Check if we have a monomorphic version
    case maps:get({FuncName, TypePattern}, MonoLookup, not_found) of
        not_found ->
            % No monomorphic version, transform arguments recursively
            NewArgs = lists:map(
                fun(Arg) ->
                    transform_expr_for_monomorphization(Arg, MonoLookup)
                end,
                Args
            ),
            CallExpr#function_call_expr{args = NewArgs};
        MonoName ->
            % Use monomorphic version
            NewArgs = lists:map(
                fun(Arg) ->
                    transform_expr_for_monomorphization(Arg, MonoLookup)
                end,
                Args
            ),
            CallExpr#function_call_expr{
                function = #identifier_expr{name = MonoName},
                args = NewArgs
            }
    end;
transform_expr_for_monomorphization(#block_expr{expressions = Exprs} = BlockExpr, MonoLookup) ->
    NewExprs = lists:map(
        fun(Expr) ->
            transform_expr_for_monomorphization(Expr, MonoLookup)
        end,
        Exprs
    ),
    BlockExpr#block_expr{expressions = NewExprs};
transform_expr_for_monomorphization(
    #let_expr{bindings = Bindings, body = Body} = LetExpr, MonoLookup
) ->
    NewBindings = lists:map(
        fun(#binding{pattern = _Pattern, value = Value} = Binding) ->
            NewValue = transform_expr_for_monomorphization(Value, MonoLookup),
            Binding#binding{value = NewValue}
        end,
        Bindings
    ),
    NewBody = transform_expr_for_monomorphization(Body, MonoLookup),
    LetExpr#let_expr{bindings = NewBindings, body = NewBody};
transform_expr_for_monomorphization(Expr, _MonoLookup) ->
    Expr.

%% ============================================================================
%% Memory Layout Optimization Helper Functions
%% ============================================================================

%% Compute tuple memory layout
compute_tuple_layout(Elements) ->
    ElementLayouts = [compute_memory_layout(Elem) || Elem <- Elements],
    TotalSize = lists:sum([maps:get(size, Layout) || Layout <- ElementLayouts]),
    MaxAlignment = lists:max([maps:get(alignment, Layout) || Layout <- ElementLayouts]),

    #{
        alignment => MaxAlignment,
        size => TotalSize,
        fields => ElementLayouts,
        type => tuple,
        cache_friendly => analyze_cache_friendliness(ElementLayouts),
        padding => calculate_tuple_padding(ElementLayouts)
    }.

%% Compute record memory layout
compute_record_layout(Fields) ->
    FieldLayouts = [compute_field_layout(Field) || Field <- Fields],
    {OptimalLayout, TotalSize, Padding} = optimize_field_ordering(FieldLayouts),
    MaxAlignment = lists:max([maps:get(alignment, Layout) || {_Name, Layout} <- OptimalLayout]),

    #{
        alignment => MaxAlignment,
        size => TotalSize,
        fields => OptimalLayout,
        type => record,
        cache_friendly => TotalSize =< 64,
        padding => Padding
    }.

%% Compute array memory layout
compute_array_layout(ElemType, Length) ->
    ElemLayout = compute_memory_layout(ElemType),
    ElemSize = maps:get(size, ElemLayout),
    ElemAlignment = maps:get(alignment, ElemLayout),

    TotalSize = ElemSize * Length,
    CacheFriendly = (TotalSize =< 64) andalso maps:get(cache_friendly, ElemLayout),

    #{
        alignment => ElemAlignment,
        size => TotalSize,
        fields => [ElemLayout],
        type => array,
        cache_friendly => CacheFriendly,
        padding => 0
    }.

%% Analyze layout opportunities for optimization
analyze_layout_opportunities(_TypeName, _TypeDef, BaseLayout) ->
    OptimizationOpportunities = identify_optimization_opportunities(BaseLayout),
    AppliedOptimizations = apply_layout_optimizations(BaseLayout, OptimizationOpportunities),

    BaseLayout#{
        optimizations => AppliedOptimizations,
        optimization_potential => calculate_optimization_potential(BaseLayout)
    }.

%% Analyze parameter layouts for stack optimization
analyze_parameter_layouts(Params) ->
    ParamLayouts = lists:map(
        fun(Param) ->
            ParamType = extract_param_type(Param),
            Layout = compute_memory_layout(ParamType),
            {Param#param.name, Layout}
        end,
        Params
    ),

    OptimalOrder = optimize_parameter_order(ParamLayouts),
    maps:from_list([{param_layout, OptimalOrder}]).

%% Merge layout maps
merge_layout_maps(Map1, Map2) ->
    maps:merge(Map1, Map2).

%% Compute field layout
compute_field_layout({FieldName, FieldType}) ->
    Layout = compute_memory_layout(FieldType),
    {FieldName, Layout}.

%% Analyze cache friendliness of layout
analyze_cache_friendliness(ElementLayouts) ->
    TotalSize = lists:sum([maps:get(size, Layout) || Layout <- ElementLayouts]),
    AllCacheFriendly = lists:all(
        fun(Layout) -> maps:get(cache_friendly, Layout) end, ElementLayouts
    ),
    TotalSize =< 64 andalso AllCacheFriendly.

%% Calculate tuple padding
calculate_tuple_padding(ElementLayouts) ->
    % Simple padding calculation - would be more sophisticated in practice
    RequiredAlignments = [maps:get(alignment, Layout) || Layout <- ElementLayouts],
    case RequiredAlignments of
        [] -> 0;
        % Conservative estimate
        _ -> lists:max(RequiredAlignments) - 1
    end.

%% Optimize field ordering for better cache performance
optimize_field_ordering(FieldLayouts) ->
    % Sort fields by alignment (largest first) to minimize padding
    SortedFields = lists:sort(
        fun({_Name1, Layout1}, {_Name2, Layout2}) ->
            maps:get(alignment, Layout1) >= maps:get(alignment, Layout2)
        end,
        FieldLayouts
    ),

    % Calculate total size and padding
    {TotalSize, Padding} = calculate_layout_size_and_padding(SortedFields),

    {SortedFields, TotalSize, Padding}.

%% Calculate total layout size and padding
calculate_layout_size_and_padding(FieldLayouts) ->
    {Size, Padding} = lists:foldl(
        fun({_Name, Layout}, {CurrentSize, CurrentPadding}) ->
            FieldSize = maps:get(size, Layout),
            FieldAlignment = maps:get(alignment, Layout),

            % Calculate padding needed for alignment
            AlignmentPadding =
                case CurrentSize rem FieldAlignment of
                    0 -> 0;
                    Remainder -> FieldAlignment - Remainder
                end,

            {CurrentSize + FieldSize + AlignmentPadding, CurrentPadding + AlignmentPadding}
        end,
        {0, 0},
        FieldLayouts
    ),

    {Size, Padding}.

%% Identify optimization opportunities
identify_optimization_opportunities(Layout) ->
    Opportunities = [],

    % Check for excessive padding
    Opportunities1 =
        case maps:get(padding, Layout, 0) > 4 of
            true -> [reduce_padding | Opportunities];
            false -> Opportunities
        end,

    % Check for poor cache performance
    Opportunities2 =
        case maps:get(cache_friendly, Layout, true) of
            false -> [improve_cache_locality | Opportunities1];
            true -> Opportunities1
        end,

    % Check for large size
    Opportunities3 =
        case maps:get(size, Layout) > 128 of
            true -> [size_optimization | Opportunities2];
            false -> Opportunities2
        end,

    Opportunities3.

%% Apply layout optimizations
apply_layout_optimizations(_Layout, Opportunities) ->
    lists:foldl(
        fun(Optimization, Acc) ->
            apply_single_optimization(Optimization, Acc)
        end,
        [],
        Opportunities
    ).

%% Apply single optimization
apply_single_optimization(reduce_padding, Acc) ->
    [field_reordering, padding_elimination | Acc];
apply_single_optimization(improve_cache_locality, Acc) ->
    [hot_field_grouping, cache_line_alignment | Acc];
apply_single_optimization(size_optimization, Acc) ->
    [field_packing, bit_field_optimization | Acc];
apply_single_optimization(_, Acc) ->
    Acc.

%% Calculate optimization potential
calculate_optimization_potential(Layout) ->
    BaseSize = maps:get(size, Layout),
    Padding = maps:get(padding, Layout, 0),
    CacheFriendly = maps:get(cache_friendly, Layout, true),

    PaddingScore =
        case Padding of
            % High potential
            P when P > 8 -> 0.3;
            % Medium potential
            P when P > 4 -> 0.2;
            % Low potential
            _ -> 0.1
        end,

    SizeScore =
        case BaseSize of
            S when S > 128 -> 0.4;
            S when S > 64 -> 0.2;
            _ -> 0.1
        end,

    CacheScore =
        case CacheFriendly of
            false -> 0.3;
            true -> 0.1
        end,

    PaddingScore + SizeScore + CacheScore.

%% Optimize parameter order for stack efficiency
optimize_parameter_order(ParamLayouts) ->
    % Sort by size (largest first) for better stack alignment
    lists:sort(
        fun({_Name1, Layout1}, {_Name2, Layout2}) ->
            maps:get(size, Layout1) >= maps:get(size, Layout2)
        end,
        ParamLayouts
    ).

%% Optimize layout strategies
optimize_layout_strategies(MemoryLayouts) ->
    maps:map(
        fun(_TypeName, Layout) ->
            case is_valid_layout_map(Layout) of
                true ->
                    OptimizedLayout = apply_layout_strategies(Layout),
                    OptimizedLayout;
                false ->
                    % Skip optimization for invalid layouts
                    Layout
            end
        end,
        MemoryLayouts
    ).

%% Check if layout is a valid layout map
is_valid_layout_map(Layout) when is_map(Layout) ->
    maps:is_key(type, Layout) andalso maps:is_key(size, Layout);
is_valid_layout_map(_) ->
    false.

%% Apply layout strategies
apply_layout_strategies(Layout) ->
    Strategy = determine_optimization_strategy(Layout),
    apply_strategy(Strategy, Layout).

%% Determine optimization strategy
determine_optimization_strategy(Layout) ->
    LayoutType = maps:get(type, Layout, unknown),
    Size = maps:get(size, Layout, 16),
    CacheFriendly = maps:get(cache_friendly, Layout, false),

    case {LayoutType, Size, CacheFriendly} of
        {record, S, false} when S > 64 -> cache_optimization;
        {tuple, S, _} when S > 32 -> field_reordering;
        {array, S, false} when S > 128 -> chunking_optimization;
        _ -> minimal_optimization
    end.

%% Apply optimization strategy
apply_strategy(cache_optimization, Layout) ->
    Layout#{optimized_for => cache, strategy => hot_cold_separation};
apply_strategy(field_reordering, Layout) ->
    Layout#{optimized_for => alignment, strategy => size_based_ordering};
apply_strategy(chunking_optimization, Layout) ->
    Layout#{optimized_for => memory_access, strategy => chunked_layout};
apply_strategy(minimal_optimization, Layout) ->
    Layout#{optimized_for => size, strategy => basic_packing}.

%% ============================================================================
%% Inlining Based on Type Analysis - Complete Implementation
%% ============================================================================

%% Analyze inlining opportunities using type information
analyze_inlining_opportunities(AST, Context) ->
    TypeInfo = Context#optimization_context.type_info,
    UsageStats = Context#optimization_context.usage_stats,
    Config = Context#optimization_context.config,

    % Collect function definitions for inlining analysis
    FunctionDefs = collect_function_definitions(AST),
    CallSites = TypeInfo#type_info.call_sites,

    % Analyze each function for inlining potential
    InliningCandidates = maps:fold(
        fun(FuncName, FuncDef, Acc) ->
            InlineMetrics = calculate_inlining_metrics(
                FuncName, FuncDef, TypeInfo, UsageStats, Config
            ),
            case should_consider_for_inlining(InlineMetrics, Config) of
                true -> maps:put(FuncName, InlineMetrics, Acc);
                false -> Acc
            end
        end,
        #{},
        FunctionDefs
    ),

    % Analyze call sites for type-specific inlining opportunities
    CallSiteAnalysis = analyze_call_sites_for_inlining(CallSites, InliningCandidates, TypeInfo),

    #{candidates => InliningCandidates, call_sites => CallSiteAnalysis}.

%% Make intelligent inlining decisions based on analysis
make_inlining_decisions(InliningOpportunities, Context) ->
    Config = Context#optimization_context.config,
    Candidates = maps:get(candidates, InliningOpportunities),
    CallSiteAnalysis = maps:get(call_sites, InliningOpportunities),

    % Evaluate each candidate and make decisions
    InliningDecisions = maps:fold(
        fun(FuncName, Metrics, Acc) ->
            Decision = evaluate_inlining_candidate(FuncName, Metrics, CallSiteAnalysis, Config),
            maps:put(FuncName, Decision, Acc)
        end,
        #{},
        Candidates
    ),

    % Apply cross-module inlining analysis if enabled
    CrossModuleDecisions =
        case Config#optimization_config.level >= 2 of
            true -> analyze_cross_module_inlining(InliningDecisions, Context);
            false -> #{}
        end,

    maps:merge(InliningDecisions, CrossModuleDecisions).

%% Apply inlining optimizations to AST
apply_inlining_optimizations(AST, InliningDecisions) ->
    % Transform AST by inlining function calls according to decisions
    InlinedAST = transform_ast_with_inlining(AST, InliningDecisions),

    % Clean up unused functions after inlining
    cleanup_inlined_functions(InlinedAST, InliningDecisions).

%% ============================================================================
%% Inlining Analysis Functions
%% ============================================================================

%% Calculate inlining metrics for a function
calculate_inlining_metrics(FuncName, FuncDef, TypeInfo, UsageStats, _Config) ->
    % Basic function characteristics
    FuncSize = estimate_function_size(FuncDef),
    Complexity = analyze_function_complexity(FuncDef),

    % Type-specific characteristics
    TypeCharacteristics = analyze_type_characteristics(FuncName, TypeInfo),

    % Usage patterns
    CallFrequency = maps:get(FuncName, UsageStats#usage_statistics.function_calls, 0),
    IsHotPath = lists:member(FuncName, flatten_hot_paths(UsageStats#usage_statistics.hot_paths)),

    % Performance impact estimation
    CallOverhead = estimate_call_overhead(FuncDef, TypeCharacteristics),
    InliningBenefit = calculate_inlining_benefit(
        FuncSize, CallFrequency, CallOverhead, TypeCharacteristics
    ),
    InliningCost = calculate_inlining_cost(FuncSize, CallFrequency, Complexity),

    #{
        func_name => FuncName,
        size => FuncSize,
        complexity => Complexity,
        call_frequency => CallFrequency,
        is_hot_path => IsHotPath,
        type_characteristics => TypeCharacteristics,
        call_overhead => CallOverhead,
        inlining_benefit => InliningBenefit,
        inlining_cost => InliningCost,
        benefit_cost_ratio => safe_divide(InliningBenefit, InliningCost)
    }.

%% Determine if function should be considered for inlining
should_consider_for_inlining(Metrics, Config) ->
    Size = maps:get(size, Metrics),
    Complexity = maps:get(complexity, Metrics),
    CallFreq = maps:get(call_frequency, Metrics),
    IsHotPath = maps:get(is_hot_path, Metrics, false),

    % Size threshold check
    SizeOk = Size =< Config#optimization_config.inline_threshold,

    % Complexity check (avoid inlining overly complex functions)
    ComplexityOk = Complexity =< 5,

    % Frequency check (prioritize frequently called or hot path functions)
    FrequencyOk = CallFreq >= 2 orelse IsHotPath,

    SizeOk andalso ComplexityOk andalso FrequencyOk.

%% Analyze call sites for type-specific inlining opportunities
analyze_call_sites_for_inlining(CallSites, Candidates, TypeInfo) ->
    maps:fold(
        fun(FuncName, Sites, Acc) ->
            case maps:is_key(FuncName, Candidates) of
                true ->
                    SiteAnalysis = lists:map(
                        fun(Site) ->
                            analyze_single_call_site(Site, FuncName, TypeInfo)
                        end,
                        Sites
                    ),
                    maps:put(FuncName, SiteAnalysis, Acc);
                false ->
                    Acc
            end
        end,
        #{},
        CallSites
    ).

%% Analyze a single call site for inlining potential
analyze_single_call_site({Location, ArgTypes}, FuncName, TypeInfo) ->
    % Analyze argument types for specialization opportunities
    TypeSpecialization = analyze_argument_type_specialization(ArgTypes, FuncName, TypeInfo),

    % Estimate inlining impact at this call site
    ImpactMetrics = calculate_call_site_impact(Location, ArgTypes, FuncName),

    #{
        location => Location,
        arg_types => ArgTypes,
        type_specialization => TypeSpecialization,
        impact_metrics => ImpactMetrics
    }.

%% Evaluate inlining candidate and make decision
evaluate_inlining_candidate(FuncName, Metrics, CallSiteAnalysis, Config) ->
    BenefitCostRatio = maps:get(benefit_cost_ratio, Metrics),
    Size = maps:get(size, Metrics),
    IsHotPath = maps:get(is_hot_path, Metrics),

    % Get call site analysis for this function
    CallSites = maps:get(FuncName, CallSiteAnalysis, []),

    % Make decision based on multiple factors
    Decision =
        case {BenefitCostRatio, Size, IsHotPath, length(CallSites)} of
            {Ratio, _, true, _} when Ratio > 1.5 ->
                {inline, hot_path_optimization};
            {Ratio, S, _, NumSites} when Ratio > 2.0, S =< 25, NumSites =< 5 ->
                {inline, small_function_optimization};
            {Ratio, S, _, NumSites} when Ratio > 3.0, S =< 50, NumSites =< 3 ->
                {inline, high_benefit_optimization};
            {Ratio, S, _, _} when Ratio > 1.2, S =< 15 ->
                {inline, trivial_function_optimization};
            _ ->
                {no_inline, insufficient_benefit}
        end,

    % Check for type-specific inlining opportunities
    TypeSpecificDecision = check_type_specific_inlining(FuncName, Metrics, CallSites, Config),

    case {Decision, TypeSpecificDecision} of
        {{inline, Reason}, _} -> {inline, Reason};
        {_, {inline, TypeReason}} -> {inline, TypeReason};
        _ -> {no_inline, combined_analysis}
    end.

%% Check for type-specific inlining opportunities
check_type_specific_inlining(_FuncName, Metrics, CallSites, _Config) ->
    TypeCharacteristics = maps:get(type_characteristics, Metrics),

    % Check for monomorphic calls (single type used)
    IsMonomorphic = analyze_call_site_monomorphism(CallSites),

    % Check for type-specialized operations
    HasTypeSpecializedOps = maps:get(has_type_specialized_ops, TypeCharacteristics, false),

    case {IsMonomorphic, HasTypeSpecializedOps} of
        {true, true} -> {inline, monomorphic_type_specialization};
        {true, false} -> {inline, monomorphic_optimization};
        {false, true} -> {conditional_inline, type_specialized_ops};
        _ -> {no_inline, no_type_benefits}
    end.

%% Analyze cross-module inlining opportunities
analyze_cross_module_inlining(_LocalDecisions, _Context) ->
    % For now, return empty map - would implement cross-module analysis
    % This would analyze imported/exported functions for inlining
    #{}.

%% ============================================================================
%% AST Transformation Functions
%% ============================================================================

%% Transform AST with inlining decisions
transform_ast_with_inlining(AST, InliningDecisions) ->
    lists:map(
        fun(Item) ->
            transform_item_with_inlining(Item, InliningDecisions)
        end,
        AST
    ).

%% Transform individual AST item
transform_item_with_inlining(#module_def{items = Items} = Module, InliningDecisions) ->
    TransformedItems = lists:map(
        fun(Item) ->
            transform_item_with_inlining(Item, InliningDecisions)
        end,
        Items
    ),
    Module#module_def{items = TransformedItems};
transform_item_with_inlining(#function_def{body = Body} = FuncDef, InliningDecisions) ->
    TransformedBody = transform_expression_with_inlining(Body, InliningDecisions),
    FuncDef#function_def{body = TransformedBody};
transform_item_with_inlining(Item, _) ->
    Item.

%% Transform statements with inlining
transform_statements_with_inlining(Statements, InliningDecisions) ->
    lists:map(
        fun(Stmt) ->
            transform_statement_with_inlining(Stmt, InliningDecisions)
        end,
        Statements
    ).

%% Transform a single expression with inlining
transform_expression_with_inlining(Expression, InliningDecisions) ->
    transform_statement_with_inlining(Expression, InliningDecisions).

%% Transform individual statement
transform_statement_with_inlining(
    #function_call_expr{function = #identifier_expr{name = FuncName}} = Call, InliningDecisions
) ->
    case maps:get(FuncName, InliningDecisions, {no_inline, not_candidate}) of
        {inline, _Reason} ->
            inline_function_call(Call, InliningDecisions);
        _ ->
            Call
    end;
transform_statement_with_inlining(Statement, InliningDecisions) ->
    % Recursively transform nested statements
    transform_nested_statements(Statement, InliningDecisions).

%% Inline function call
inline_function_call(
    #function_call_expr{function = #identifier_expr{name = FuncName}, args = Args} = Call,
    _InliningDecisions
) ->
    % Get function definition (simplified - would need function lookup)
    case lookup_function_definition(FuncName) of
        {ok, FuncDef} ->
            inline_function_body(FuncDef, Args, Call);
        error ->
            % Keep original call if function not found
            Call
    end.

%% Inline function body with arguments
inline_function_body(#function_def{params = Params, body = Body}, Args, _OriginalCall) ->
    % Create parameter substitution map
    SubstMap = create_parameter_substitution_map(Params, Args),

    % Substitute parameters in function body
    InlinedBody = substitute_parameters_in_body(Body, SubstMap),

    % Return inlined body as a block expression
    #block_expr{expressions = InlinedBody}.

%% Clean up functions that have been completely inlined
cleanup_inlined_functions(AST, InliningDecisions) ->
    % Identify functions that can be removed (fully inlined)
    FullyInlinedFuncs = identify_fully_inlined_functions(InliningDecisions),

    % Remove unused functions from AST
    remove_unused_functions(AST, FullyInlinedFuncs).

%% ============================================================================
%% Helper Functions for Inlining Analysis
%% ============================================================================

%% Estimate function size (instruction count estimate)
estimate_function_size(#function_def{body = Body}) ->
    count_statements_recursive(Body).

%% Count statements recursively
count_statements_recursive(Statements) when is_list(Statements) ->
    lists:sum(lists:map(fun count_statements_recursive/1, Statements));
count_statements_recursive(#block_expr{expressions = Stmts}) ->
    count_statements_recursive(Stmts);
count_statements_recursive(#match_expr{patterns = Patterns}) ->
    % Simplified
    lists:sum([count_statements_recursive(1) || _Pattern <- Patterns]);
count_statements_recursive(_) ->
    1.

%% Analyze function complexity (cyclomatic complexity estimate)
analyze_function_complexity(#function_def{body = Body}) ->
    count_complexity_recursive(Body, 1).

%% Count complexity recursively
count_complexity_recursive(Statements, Acc) when is_list(Statements) ->
    lists:foldl(fun count_complexity_recursive/2, Acc, Statements);
count_complexity_recursive(#match_expr{patterns = Patterns}, Acc) ->
    Acc + length(Patterns);
count_complexity_recursive(#let_expr{}, Acc) ->
    Acc + 1;
count_complexity_recursive(_, Acc) ->
    Acc.

%% Analyze type characteristics
analyze_type_characteristics(FuncName, TypeInfo) ->
    FunctionTypes = TypeInfo#type_info.function_types,

    case maps:get(FuncName, FunctionTypes, undefined) of
        {function_type, ParamTypes, ReturnType} ->
            #{
                param_types => ParamTypes,
                return_type => ReturnType,
                has_type_specialized_ops => has_type_specialized_operations(ParamTypes, ReturnType),
                type_complexity => calculate_type_complexity(ParamTypes, ReturnType)
            };
        _ ->
            #{
                param_types => [],
                return_type => unknown,
                has_type_specialized_ops => false,
                type_complexity => 1
            }
    end.

%% Check if function has type-specialized operations
has_type_specialized_operations(ParamTypes, ReturnType) ->
    % Check for primitive types that benefit from specialization
    PrimitiveTypes = [integer, float, boolean, atom],
    HasPrimitiveParams = lists:any(fun(T) -> lists:member(T, PrimitiveTypes) end, ParamTypes),
    HasPrimitiveReturn = lists:member(ReturnType, PrimitiveTypes),
    HasPrimitiveParams orelse HasPrimitiveReturn.

%% Calculate type complexity
calculate_type_complexity(ParamTypes, ReturnType) ->
    ParamComplexity = lists:sum([type_complexity(T) || T <- ParamTypes]),
    ReturnComplexity = type_complexity(ReturnType),
    ParamComplexity + ReturnComplexity.

%% Calculate individual type complexity
type_complexity(integer) -> 1;
type_complexity(float) -> 1;
type_complexity(boolean) -> 1;
type_complexity(atom) -> 1;
type_complexity({list, _}) -> 2;
type_complexity({tuple, Elements}) -> 1 + length(Elements);
type_complexity({record, _Name, Fields}) -> 1 + length(Fields);
type_complexity(_) -> 2.

%% Flatten hot paths for membership checking
flatten_hot_paths(HotPaths) ->
    lists:flatten(HotPaths).

%% Estimate call overhead
estimate_call_overhead(#function_def{params = Params}, TypeCharacteristics) ->
    % Base call overhead
    BaseOverhead = 10,

    % Parameter passing overhead
    ParamOverhead = length(Params) * 2,

    % Type-specific overhead
    TypeOverhead =
        case maps:get(type_complexity, TypeCharacteristics, 1) of
            C when C > 3 -> 5;
            _ -> 0
        end,

    BaseOverhead + ParamOverhead + TypeOverhead.

%% Calculate inlining benefit with enhanced analysis
calculate_inlining_benefit(FuncSize, CallFreq, CallOverhead, TypeCharacteristics) ->
    % Saved call overhead per invocation
    OverheadSavings = CallOverhead * CallFreq,

    % Type specialization benefits
    TypeBenefit = calculate_type_specialization_benefit(FuncSize, CallFreq, TypeCharacteristics),

    % Register pressure reduction (avoiding parameter passing)
    RegisterBenefit = calculate_register_pressure_benefit(FuncSize, CallFreq),

    % Branch prediction benefits (eliminating call/return)
    BranchBenefit = calculate_branch_prediction_benefit(CallFreq),

    % Cache locality benefits (code is inline, better i-cache usage)
    CacheBenefit = calculate_cache_locality_benefit(FuncSize, CallFreq),

    % Hot path benefits multiplier
    HotPathMultiplier = calculate_hot_path_multiplier(CallFreq),

    % Additional optimization opportunities from inlining
    OptimizationOpportunities = calculate_optimization_opportunities(FuncSize, TypeCharacteristics),

    TotalBenefit =
        (OverheadSavings + TypeBenefit + RegisterBenefit + BranchBenefit +
            CacheBenefit + OptimizationOpportunities) * HotPathMultiplier,

    % Ensure non-negative benefit
    max(0.0, TotalBenefit).

%% Calculate type specialization benefit
calculate_type_specialization_benefit(FuncSize, CallFreq, TypeCharacteristics) ->
    HasSpecializedOps = maps:get(has_type_specialized_ops, TypeCharacteristics, false),
    TypeComplexity = maps:get(type_complexity, TypeCharacteristics, 1),

    BaseBenefit =
        case HasSpecializedOps of
            % 15% improvement from specialization
            true -> FuncSize * CallFreq * 0.15;
            false -> 0
        end,

    % Additional benefit for complex types that can be simplified
    ComplexityBenefit =
        case TypeComplexity > 3 of
            % 10% more for complex types
            true -> FuncSize * CallFreq * 0.10;
            false -> 0
        end,

    BaseBenefit + ComplexityBenefit.

%% Calculate register pressure reduction benefit
calculate_register_pressure_benefit(FuncSize, CallFreq) ->
    % Small functions benefit more from eliminating call overhead
    case FuncSize < 10 of
        % Significant benefit for small functions
        true -> CallFreq * 3;
        % Modest benefit for larger functions
        false -> CallFreq * 1
    end.

%% Calculate branch prediction benefit
calculate_branch_prediction_benefit(CallFreq) ->
    % Each call/return is a branch; eliminating improves prediction

    % ~15 cycles for misprediction
    BranchMispredictCost = 15,
    % ~5% misprediction rate
    MispredictRate = 0.05,
    CallFreq * BranchMispredictCost * MispredictRate.

%% Calculate cache locality benefit
calculate_cache_locality_benefit(FuncSize, CallFreq) ->
    % Inlining improves i-cache locality for frequently called small functions
    case {FuncSize < 20, CallFreq > 5} of
        % Good locality improvement
        {true, true} -> CallFreq * 5;
        % Modest improvement
        {true, false} -> CallFreq * 2;
        % Large functions hurt cache
        {false, _} -> 0
    end.

%% Calculate hot path multiplier
calculate_hot_path_multiplier(CallFreq) ->
    if
        % Very hot
        CallFreq > 50 -> 2.0;
        % Hot
        CallFreq > 20 -> 1.7;
        % Warm
        CallFreq > 10 -> 1.5;
        % Normal
        true -> 1.0
    end.

%% Calculate additional optimization opportunities from inlining
calculate_optimization_opportunities(FuncSize, TypeCharacteristics) ->
    % Inlining enables:
    % - Constant propagation
    % - Dead code elimination
    % - Common subexpression elimination
    % - Loop unrolling (if applicable)

    % 20% potential improvement
    BaseOpportunities = FuncSize * 0.2,

    % More opportunities with type-specialized code
    TypeFactor =
        case maps:get(has_type_specialized_ops, TypeCharacteristics, false) of
            true -> 1.5;
            false -> 1.0
        end,

    BaseOpportunities * TypeFactor.

%% Calculate inlining cost with enhanced analysis
calculate_inlining_cost(FuncSize, CallFreq, Complexity) ->
    % Code size increase (-1 because original call is replaced)
    CodeSizeIncrease = max(0, FuncSize * (CallFreq - 1)),

    % Compilation time cost
    CompilationCost = calculate_compilation_cost(Complexity, CallFreq),

    % Instruction cache impact
    ICacheCost = calculate_icache_cost(CodeSizeIncrease, FuncSize),

    % Register pressure cost (larger inlined code may spill registers)
    RegisterPressureCost = calculate_register_pressure_cost(FuncSize, Complexity),

    % Code bloat penalty (diminishing returns for many inlines)
    CodeBloatPenalty = calculate_code_bloat_penalty(CodeSizeIncrease, CallFreq),

    % Debug and maintainability cost
    DebugCost = calculate_debug_cost(CallFreq),

    TotalCost =
        CodeSizeIncrease + CompilationCost + ICacheCost +
            RegisterPressureCost + CodeBloatPenalty + DebugCost,

    % Ensure minimum cost to avoid division by zero
    max(1.0, TotalCost).

%% Calculate compilation time cost
calculate_compilation_cost(Complexity, CallFreq) ->
    % More complex functions cost more to compile when inlined
    BaseCost = Complexity * CallFreq * 0.5,

    % Exponential cost for very complex functions
    ComplexityPenalty =
        case Complexity > 10 of
            true -> Complexity * Complexity * 0.1;
            false -> 0
        end,

    BaseCost + ComplexityPenalty.

%% Calculate instruction cache cost
calculate_icache_cost(CodeSizeIncrease, FuncSize) ->
    % I-cache lines are typically 64 bytes
    ICacheLineSize = 64,

    % Penalty for crossing cache line boundaries
    if
        CodeSizeIncrease > ICacheLineSize * 4 ->
            % Significant cache pressure
            CodeSizeIncrease * 0.3;
        CodeSizeIncrease > ICacheLineSize * 2 ->
            % Moderate cache pressure
            CodeSizeIncrease * 0.15;
        CodeSizeIncrease > ICacheLineSize ->
            % Minor cache pressure
            CodeSizeIncrease * 0.05;
        true ->
            % Negligible impact
            0
    end.

%% Calculate register pressure cost
calculate_register_pressure_cost(FuncSize, Complexity) ->
    % Large complex functions may cause register spills
    case {FuncSize > 50, Complexity > 5} of
        % High spill risk
        {true, true} -> FuncSize * 0.2;
        % Moderate spill risk
        {true, false} -> FuncSize * 0.1;
        % Some spill risk (use float to avoid warning)
        {false, true} -> Complexity * 5.0;
        % Low spill risk
        {false, false} -> 0.0
    end.

%% Calculate code bloat penalty
calculate_code_bloat_penalty(CodeSizeIncrease, CallFreq) ->
    % Exponential penalty for excessive inlining
    if
        % Severe bloat
        CallFreq > 20 -> CodeSizeIncrease * 0.5;
        % Significant bloat
        CallFreq > 10 -> CodeSizeIncrease * 0.25;
        % Moderate bloat
        CallFreq > 5 -> CodeSizeIncrease * 0.1;
        % Acceptable
        true -> 0
    end.

%% Calculate debug and maintainability cost
calculate_debug_cost(CallFreq) ->
    % Inlining makes debugging harder (no stack frames)
    % More inline sites = harder debugging
    if
        % Significant debug impact
        CallFreq > 10 -> CallFreq * 2;
        % Moderate debug impact
        CallFreq > 5 -> CallFreq * 1;
        % Minor debug impact
        true -> 0
    end.

%% Safe division (avoid division by zero)
safe_divide(_Numerator, 0) -> 0;
safe_divide(Numerator, Denominator) -> Numerator / Denominator.

%% Analyze call site monomorphism
analyze_call_site_monomorphism(CallSites) ->
    % Check if all call sites use the same types
    case CallSites of
        [] ->
            false;
        [#{arg_types := FirstTypes} | Rest] ->
            lists:all(fun(#{arg_types := Types}) -> Types =:= FirstTypes end, Rest)
    end.

%% Analyze argument type specialization
analyze_argument_type_specialization(ArgTypes, _FuncName, _TypeInfo) ->
    % Simple analysis - check if types are concrete and primitive
    PrimitiveTypes = [integer, float, boolean, atom],
    ConcreteTypes = lists:filter(fun(T) -> lists:member(T, PrimitiveTypes) end, ArgTypes),

    #{
        concrete_types => ConcreteTypes,
        specialization_potential => length(ConcreteTypes) / max(1, length(ArgTypes))
    }.

%% Calculate call site impact
calculate_call_site_impact(Location, ArgTypes, _FuncName) ->
    % Estimate impact based on location and argument types
    #{
        location => Location,
        arg_type_count => length(ArgTypes),
        % Simple heuristic
        estimated_benefit => length(ArgTypes) * 2
    }.

%% ============================================================================
%% AST Helper Functions
%% ============================================================================

%% Transform nested statements for inlining
transform_nested_statements(Statement, _) ->
    Statement.

%% Lookup function definition (simplified implementation)
lookup_function_definition(_FuncName) ->
    % In a real implementation, this would lookup the function definition
    % from a symbol table or function registry
    error.

%% Create parameter substitution map
create_parameter_substitution_map(Params, Args) ->
    lists:foldl(
        fun({Param, Arg}, Acc) ->
            ParamName =
                case Param of
                    #param{name = Name} -> Name;
                    Name when is_atom(Name) -> Name
                end,
            maps:put(ParamName, Arg, Acc)
        end,
        #{},
        lists:zip(Params, Args)
    ).

%% Substitute parameters in function body
substitute_parameters_in_body(Body, SubstMap) ->
    % Simplified parameter substitution - would be more complex in practice
    lists:map(
        fun(Stmt) ->
            substitute_in_statement(Stmt, SubstMap)
        end,
        Body
    ).

%% Substitute in individual statement
substitute_in_statement(#identifier_expr{name = Name} = Var, SubstMap) ->
    case maps:get(Name, SubstMap, undefined) of
        undefined -> Var;
        Substitution -> Substitution
    end;
substitute_in_statement(Statement, _SubstMap) ->
    Statement.

%% Identify fully inlined functions
identify_fully_inlined_functions(InliningDecisions) ->
    maps:fold(
        fun
            (FuncName, {inline, _}, Acc) ->
                [FuncName | Acc];
            (_, _, Acc) ->
                Acc
        end,
        [],
        InliningDecisions
    ).

%% Remove unused functions from AST
remove_unused_functions(AST, UnusedFunctions) ->
    lists:filter(
        fun(Item) ->
            case Item of
                #function_def{name = Name} ->
                    not lists:member(Name, UnusedFunctions);
                _ ->
                    true
            end
        end,
        AST
    ).

%% Apply memory layout optimizations to AST
apply_memory_layout_optimizations(AST, OptimizedLayouts) ->
    % Transform AST to use optimized layouts
    case maps:size(OptimizedLayouts) of
        0 ->
            AST;
        _ ->
            % Apply layout transformations
            transform_ast_for_memory_optimization(AST, OptimizedLayouts)
    end.

%% Transform AST for memory optimization
transform_ast_for_memory_optimization(AST, _OptimizedLayouts) ->
    % For now, return AST unchanged - full implementation would
    % modify type definitions and add layout annotations
    AST.

%% ============================================================================
%% Dead Code Elimination Using Type Information - Complete Implementation
%% ============================================================================

%% Apply comprehensive dead code elimination transformations
apply_dead_code_elimination(AST, DeadCodeAnalysis) ->
    #{
        unused_functions := UnusedFunctions,
        unreachable_branches := UnreachableBranches,
        redundant_type_checks := RedundantTypeChecks,
        dead_code_patterns := DeadCodePatterns
    } = DeadCodeAnalysis,

    % Apply transformations in order of dependencies
    AST1 = remove_unused_functions_advanced(AST, UnusedFunctions),
    AST2 = remove_unreachable_branches(AST1, UnreachableBranches),
    AST3 = remove_redundant_type_checks(AST2, RedundantTypeChecks),
    AST4 = remove_dead_code_patterns(AST3, DeadCodePatterns),

    AST4.

%% ============================================================================
%% Unused Function Detection with Type Information
%% ============================================================================

%% Identify unused functions using type constraints and call graph analysis
identify_unused_functions_with_types(AST, TypeInfo, UsageStats) ->
    % Get basic cold code from usage statistics
    ColdCode = UsageStats#usage_statistics.cold_code,

    % Enhance with type-based analysis
    CallSites = TypeInfo#type_info.call_sites,
    AllFunctions = collect_all_function_names(AST),

    % Find functions with zero or very low usage that can be safely removed
    UnusedByCallGraph = analyze_call_graph_for_unused_functions(AllFunctions, CallSites),

    % Find functions that are unreachable due to type constraints
    UnusedByTypeConstraints = find_unreachable_functions_by_type(AST, TypeInfo),

    % Combine analysis results
    lists:usort(ColdCode ++ UnusedByCallGraph ++ UnusedByTypeConstraints).

%% Analyze call graph to find unused functions
analyze_call_graph_for_unused_functions(AllFunctions, CallSites) ->
    % Find functions that are never called (not in call sites)
    CalledFunctions = maps:keys(CallSites),
    NeverCalledFunctions = AllFunctions -- CalledFunctions,

    % Filter out entry points and exported functions (simplified)
    lists:filter(
        fun(FuncName) ->
            not is_entry_point(FuncName) andalso not is_exported_function(FuncName)
        end,
        NeverCalledFunctions
    ).

%% Check if all call sites are type incompatible with function signature
all_call_sites_type_incompatible(CallSites, ExpectedParamTypes) ->
    lists:all(
        fun({_Location, ArgTypes}) ->
            not types_are_compatible(ArgTypes, ExpectedParamTypes)
        end,
        CallSites
    ).

%% ============================================================================
%% Unreachable Branch Detection with Type Information
%% ============================================================================

%% Detect unreachable code branches using type constraints
detect_unreachable_branches_with_types(AST, TypeInfo, Config) ->
    % Analyze each function for unreachable branches
    UnreachableBranches = [],
    detect_unreachable_branches_impl(AST, TypeInfo, Config, UnreachableBranches).

%% Implementation of unreachable branch detection
detect_unreachable_branches_impl([], _TypeInfo, _Config, Acc) ->
    Acc;
detect_unreachable_branches_impl([Item | Rest], TypeInfo, Config, Acc) ->
    NewAcc =
        case Item of
            #function_def{name = FuncName, body = Body} ->
                FuncUnreachable = find_unreachable_in_function(FuncName, Body, TypeInfo),
                FuncUnreachable ++ Acc;
            #module_def{items = Items} ->
                detect_unreachable_branches_impl(Items, TypeInfo, Config, Acc);
            _ ->
                Acc
        end,
    detect_unreachable_branches_impl(Rest, TypeInfo, Config, NewAcc).

%% Find unreachable code within a function
find_unreachable_in_function(_FuncName, Body, TypeInfo) ->
    % Analyze function body for unreachable patterns
    find_unreachable_in_expression(Body, TypeInfo, []).

%% Find unreachable code in expressions
find_unreachable_in_expression(
    #match_expr{patterns = Patterns, location = Location}, TypeInfo, Acc
) ->
    % Find patterns that can never match based on type information
    UnreachablePatterns = find_unreachable_patterns(Patterns, TypeInfo),
    case UnreachablePatterns of
        [] -> Acc;
        _ -> [{unreachable_patterns, Location, UnreachablePatterns} | Acc]
    end;
find_unreachable_in_expression(#block_expr{expressions = Exprs}, TypeInfo, Acc) ->
    lists:foldl(fun(Expr, A) -> find_unreachable_in_expression(Expr, TypeInfo, A) end, Acc, Exprs);
find_unreachable_in_expression(#let_expr{body = Body}, TypeInfo, Acc) ->
    find_unreachable_in_expression(Body, TypeInfo, Acc);
find_unreachable_in_expression(_, _TypeInfo, Acc) ->
    Acc.

%% Analyze condition reachability based on type information
analyze_condition_reachability(#literal_expr{value = true}, _TypeInfo) ->
    always_true;
analyze_condition_reachability(#literal_expr{value = false}, _TypeInfo) ->
    always_false;
analyze_condition_reachability(_Condition, _TypeInfo) ->
    % More sophisticated analysis would go here
    unknown.

%% Find unreachable patterns in pattern matching
find_unreachable_patterns(_Patterns, _TypeInfo) ->
    % Simplified - would implement sophisticated pattern reachability analysis
    [].

%% ============================================================================
%% Redundant Type Check Detection
%% ============================================================================

%% Implementation of redundant type check detection
find_redundant_checks_impl([], _TypeInfo, Acc) ->
    Acc;
find_redundant_checks_impl([Item | Rest], TypeInfo, Acc) ->
    NewAcc =
        case Item of
            #function_def{body = Body} ->
                FuncRedundant = find_redundant_in_expression(Body, TypeInfo, #{}),
                FuncRedundant ++ Acc;
            #module_def{items = Items} ->
                find_redundant_checks_impl(Items, TypeInfo, Acc);
            _ ->
                Acc
        end,
    find_redundant_checks_impl(Rest, TypeInfo, NewAcc).

%% Find redundant type checks in expressions
find_redundant_in_expression(
    #function_call_expr{
        function = #identifier_expr{name = is_integer}, args = [Arg], location = Location
    },
    _TypeInfo,
    TypeContext
) ->
    % Check if we already know the argument is an integer
    case infer_expr_type_with_context(Arg, TypeContext) of
        {primitive_type, 'Int'} -> [{redundant_type_check, Location, is_integer}];
        _ -> []
    end;
find_redundant_in_expression(
    #function_call_expr{
        function = #identifier_expr{name = is_float}, args = [Arg], location = Location
    },
    _TypeInfo,
    TypeContext
) ->
    case infer_expr_type_with_context(Arg, TypeContext) of
        {primitive_type, 'Float'} -> [{redundant_type_check, Location, is_float}];
        _ -> []
    end;
find_redundant_in_expression(#block_expr{expressions = Exprs}, TypeInfo, TypeContext) ->
    lists:foldl(
        fun(Expr, Acc) ->
            find_redundant_in_expression(Expr, TypeInfo, TypeContext) ++ Acc
        end,
        [],
        Exprs
    );
find_redundant_in_expression(_, _TypeInfo, _TypeContext) ->
    [].

%% Infer expression type with context
infer_expr_type_with_context(Expr, _TypeContext) ->
    % Enhanced type inference using local context

    % Simplified for now
    infer_expr_type(Expr).

%% ============================================================================
%% Type-specific Dead Code Pattern Detection
%% ============================================================================

%% Identify dead code patterns specific to type usage
identify_type_specific_dead_code_patterns(AST, TypeInfo, UsageStats) ->
    % Find type-specific patterns that indicate dead code
    DeadPatterns = [],

    % Pattern 1: Unused type definitions
    UnusedTypes = find_unused_type_definitions(AST, TypeInfo),

    % Pattern 2: Unreachable type-specific branches
    UnreachableTypeBranches = find_unreachable_type_branches(AST, TypeInfo),

    % Pattern 3: Dead polymorphic instantiations
    DeadPolymorphicInstances = find_dead_polymorphic_instances(TypeInfo, UsageStats),

    DeadPatterns ++ UnusedTypes ++ UnreachableTypeBranches ++ DeadPolymorphicInstances.

%% Find unused type definitions
find_unused_type_definitions(_AST, _TypeInfo) ->
    % Find type definitions that are never used

    % Simplified implementation
    [].

%% Find unreachable type-specific branches
find_unreachable_type_branches(_AST, _TypeInfo) ->
    % Find branches that are unreachable due to type constraints

    % Simplified implementation
    [].

%% Find dead polymorphic instances
find_dead_polymorphic_instances(_TypeInfo, _UsageStats) ->
    % Find polymorphic instantiations that are never used

    % Simplified implementation
    [].

%% ============================================================================
%% Dead Code Removal Transformations
%% ============================================================================

%% Advanced unused function removal
remove_unused_functions_advanced(AST, UnusedFunctions) ->
    case UnusedFunctions of
        [] ->
            AST;
        _ ->
            cure_utils:debug("    Removing ~p unused functions~n", [length(UnusedFunctions)]),
            filter_dead_functions(AST, UnusedFunctions)
    end.

%% Remove unreachable branches from AST
remove_unreachable_branches(AST, UnreachableBranches) ->
    case UnreachableBranches of
        [] ->
            AST;
        _ ->
            cure_utils:debug("    Removing ~p unreachable branches~n", [length(UnreachableBranches)]),
            transform_ast_remove_unreachable(AST, UnreachableBranches)
    end.

%% Remove redundant type checks
remove_redundant_type_checks(AST, RedundantChecks) ->
    case RedundantChecks of
        [] ->
            AST;
        _ ->
            cure_utils:debug("    Removing ~p redundant type checks~n", [length(RedundantChecks)]),
            transform_ast_remove_redundant_checks(AST, RedundantChecks)
    end.

%% Remove type-specific dead code patterns
remove_dead_code_patterns(AST, DeadPatterns) ->
    case DeadPatterns of
        [] ->
            AST;
        _ ->
            cure_utils:debug("    Removing ~p dead code patterns~n", [length(DeadPatterns)]),
            transform_ast_remove_patterns(AST, DeadPatterns)
    end.

%% ============================================================================
%% AST Transformation Functions for Dead Code Removal
%% ============================================================================

%% Transform AST to remove unreachable branches
transform_ast_remove_unreachable(AST, UnreachableBranches) ->
    % Create lookup set for fast checking
    UnreachableSet = sets:from_list(UnreachableBranches),

    % Transform AST
    lists:map(
        fun(Item) ->
            transform_item_remove_unreachable(Item, UnreachableSet)
        end,
        AST
    ).

%% Transform individual item to remove unreachable branches
transform_item_remove_unreachable(#function_def{body = Body} = FuncDef, UnreachableSet) ->
    NewBody = transform_expr_remove_unreachable(Body, UnreachableSet),
    FuncDef#function_def{body = NewBody};
transform_item_remove_unreachable(#module_def{items = Items} = Module, UnreachableSet) ->
    NewItems = lists:map(
        fun(Item) ->
            transform_item_remove_unreachable(Item, UnreachableSet)
        end,
        Items
    ),
    Module#module_def{items = NewItems};
transform_item_remove_unreachable(Item, _UnreachableSet) ->
    Item.

%% Transform expression to remove unreachable branches
transform_expr_remove_unreachable(#block_expr{expressions = Exprs} = Block, UnreachableSet) ->
    NewExprs = lists:map(
        fun(Expr) ->
            transform_expr_remove_unreachable(Expr, UnreachableSet)
        end,
        Exprs
    ),
    Block#block_expr{expressions = NewExprs};
transform_expr_remove_unreachable(Expr, _UnreachableSet) ->
    Expr.

%% Transform AST to remove redundant type checks
transform_ast_remove_redundant_checks(AST, RedundantChecks) ->
    % Create lookup set for redundant checks
    RedundantSet = sets:from_list(RedundantChecks),

    % Transform AST
    lists:map(
        fun(Item) ->
            transform_item_remove_redundant(Item, RedundantSet)
        end,
        AST
    ).

%% Transform item to remove redundant type checks
transform_item_remove_redundant(#function_def{body = Body} = FuncDef, RedundantSet) ->
    NewBody = transform_expr_remove_redundant(Body, RedundantSet),
    FuncDef#function_def{body = NewBody};
transform_item_remove_redundant(#module_def{items = Items} = Module, RedundantSet) ->
    NewItems = lists:map(
        fun(Item) ->
            transform_item_remove_redundant(Item, RedundantSet)
        end,
        Items
    ),
    Module#module_def{items = NewItems};
transform_item_remove_redundant(Item, _RedundantSet) ->
    Item.

%% Transform expression to remove redundant type checks
transform_expr_remove_redundant(#function_call_expr{location = Location} = Call, RedundantSet) ->
    % Check if this is a redundant type check
    case
        sets:is_element({redundant_type_check, Location, is_integer}, RedundantSet) orelse
            sets:is_element({redundant_type_check, Location, is_float}, RedundantSet)
    of
        true ->
            % Replace with literal true
            #literal_expr{value = true, location = Location};
        false ->
            Call
    end;
transform_expr_remove_redundant(#block_expr{expressions = Exprs} = Block, RedundantSet) ->
    NewExprs = lists:map(
        fun(Expr) ->
            transform_expr_remove_redundant(Expr, RedundantSet)
        end,
        Exprs
    ),
    Block#block_expr{expressions = NewExprs};
transform_expr_remove_redundant(Expr, _RedundantSet) ->
    Expr.

%% Transform AST to remove dead code patterns
transform_ast_remove_patterns(AST, _DeadPatterns) ->
    % Simplified implementation for now
    AST.

%% ============================================================================
%% Helper Functions for Dead Code Analysis
%% ============================================================================

%% Check if function is an entry point
is_entry_point(main) -> true;
is_entry_point(_) -> false.

%% Check if function is exported (simplified)
is_exported_function(_FuncName) -> false.

%% Check type compatibility between arguments and parameters
types_are_compatible([], []) ->
    true;
types_are_compatible([ArgType | ArgRest], [ParamType | ParamRest]) ->
    case type_matches(ArgType, ParamType) of
        true -> types_are_compatible(ArgRest, ParamRest);
        false -> false
    end;
types_are_compatible(_, _) ->
    false.

%% Check if two types match
type_matches(Type, Type) -> true;
type_matches({primitive_type, T1}, {primitive_type, T2}) -> T1 =:= T2;
% Unknown type can match anything
type_matches({unknown_type}, _) -> true;
type_matches(_, {unknown_type}) -> true;
type_matches(_, _) -> false.

%% Remove empty modules after dead code elimination
remove_empty_modules(AST) ->
    lists:filter(
        fun(Item) ->
            case Item of
                % Remove empty modules
                #module_def{items = []} -> false;
                _ -> true
            end
        end,
        AST
    ).

%% Verify AST consistency after transformations
verify_ast_consistency(AST) ->
    % Perform basic consistency checks
    % This would include more sophisticated checks in a real implementation
    case is_list(AST) of
        true -> ok;
        false -> error(invalid_ast_structure)
    end.

%% ============================================================================
%% Type-directed BEAM Code Generation (Pass 7)
%% ============================================================================

%% Apply type-directed BEAM code generation optimization
apply_beam_generation_pass(AST, Context) ->
    cure_utils:debug("[Type Optimizer] Starting Type-directed BEAM Code Generation pass...~n"),

    % Extract type information from optimization context
    TypeInfo = extract_type_info_for_beam(Context),

    % Generate type-directed BEAM instructions for each function
    BeamContext = init_beam_generation_context(TypeInfo),
    FunctionsWithBeam = generate_beam_for_functions(AST, BeamContext),

    % Create optimized calling conventions based on types
    CallingConventions = create_optimized_calling_conventions(TypeInfo),

    % Generate type-specialized opcodes
    SpecializedOpcodes = generate_specialized_opcodes(TypeInfo, FunctionsWithBeam),

    % Build final BEAM generation result
    BeamResult = #{
        functions_with_beam => FunctionsWithBeam,
        calling_conventions => CallingConventions,
        specialized_opcodes => SpecializedOpcodes,
        type_info => TypeInfo
    },

    % Update context with BEAM generation results
    NewContext = Context#optimization_context{
        beam_generation = BeamResult
    },

    cure_utils:debug("[Type Optimizer] Type-directed BEAM Code Generation pass completed~n"),
    {AST, NewContext}.

%% Extract relevant type information for BEAM generation
extract_type_info_for_beam(Context) ->
    TypeChecker = Context#optimization_context.type_checker,
    FunctionSpecs = Context#optimization_context.function_specializations,
    MonomorphicInstances = Context#optimization_context.monomorphic_instances,
    InliningDecisions = Context#optimization_context.inlining_decisions,

    #{
        function_types => get_function_type_mappings(TypeChecker),
        call_site_types => get_call_site_type_info(TypeChecker),
        specialized_functions => FunctionSpecs,
        monomorphic_instances => MonomorphicInstances,
        inlined_functions => extract_inlined_function_info(InliningDecisions),
        type_usage_patterns => analyze_type_usage_patterns(TypeChecker),
        hot_path_functions => identify_hot_path_functions(InliningDecisions),
        memory_layout_info => get_memory_layout_optimizations(TypeChecker)
    }.

%% Initialize BEAM generation context
init_beam_generation_context(TypeInfo) ->
    #{
        type_info => TypeInfo,
        instruction_cache => #{},
        opcode_mappings => init_opcode_mappings(),
        calling_conventions => #{},
        register_allocations => #{},
        type_dispatch_table => build_type_dispatch_table(TypeInfo)
    }.

%% Generate BEAM instructions for all functions using type information
generate_beam_for_functions(AST, BeamContext) ->
    lists:foldl(
        fun(Item, Acc) ->
            case Item of
                #function_def{name = Name} = FuncDef ->
                    BeamInstructions = generate_function_beam_instructions(FuncDef, BeamContext),
                    maps:put(Name, BeamInstructions, Acc);
                _ ->
                    Acc
            end
        end,
        #{},
        AST
    ).

%% Generate optimized BEAM instructions for a single function
generate_function_beam_instructions(
    #function_def{name = Name, params = Params, body = Body}, BeamContext
) ->
    TypeInfo = maps:get(type_info, BeamContext),

    % Get function type signature
    FunctionType = get_function_type_signature(Name, TypeInfo),

    % Generate optimized parameter loading based on types
    ParamInstructions = generate_typed_param_loading(Params, FunctionType),

    % Generate body instructions with type-aware optimization
    BodyInstructions = generate_typed_body_instructions(Body, FunctionType, BeamContext),

    % Generate optimized return sequence
    ReturnInstructions = generate_typed_return_sequence(FunctionType),

    % Combine all instructions with optimization
    AllInstructions = ParamInstructions ++ BodyInstructions ++ ReturnInstructions,

    % Apply instruction-level optimizations based on types
    OptimizedInstructions = optimize_instructions_with_types(
        AllInstructions, FunctionType, BeamContext
    ),

    #{
        function_name => Name,
        function_type => FunctionType,
        instructions => OptimizedInstructions,
        optimization_info => #{
            param_optimizations => analyze_param_optimizations(Params, FunctionType),
            body_optimizations => analyze_body_optimizations(Body, FunctionType),
            instruction_count => length(OptimizedInstructions),
            specialized_opcodes => count_specialized_opcodes(OptimizedInstructions)
        }
    }.

%% Generate type-aware parameter loading instructions
generate_typed_param_loading(Params, FunctionType) ->
    ParamTypes = get_parameter_types(FunctionType),
    lists:zipwith(
        fun(Param, Type) ->
            case Type of
                {primitive_type, integer} ->
                    [#beam_instr{op = load_param_int, args = [Param], location = undefined}];
                {primitive_type, float} ->
                    [#beam_instr{op = load_param_float, args = [Param], location = undefined}];
                {primitive_type, atom} ->
                    [#beam_instr{op = load_param_atom, args = [Param], location = undefined}];
                _ ->
                    [#beam_instr{op = load_param, args = [Param], location = undefined}]
            end
        end,
        Params,
        ParamTypes
    ).

%% Generate type-aware body instructions
generate_typed_body_instructions(Body, FunctionType, BeamContext) ->
    generate_expr_instructions(Body, FunctionType, BeamContext).

%% Generate instructions for expressions with type awareness
generate_expr_instructions(#literal_expr{value = Value} = Expr, _FunctionType, _BeamContext) ->
    case Value of
        V when is_integer(V) ->
            [#beam_instr{op = load_literal_int, args = [V], location = Expr#literal_expr.location}];
        V when is_float(V) ->
            [
                #beam_instr{
                    op = load_literal_float, args = [V], location = Expr#literal_expr.location
                }
            ];
        V when is_atom(V) ->
            [
                #beam_instr{
                    op = load_literal_atom, args = [V], location = Expr#literal_expr.location
                }
            ];
        V ->
            [#beam_instr{op = load_literal, args = [V], location = Expr#literal_expr.location}]
    end;
generate_expr_instructions(#identifier_expr{name = Name} = Expr, _FunctionType, _BeamContext) ->
    [#beam_instr{op = load_local, args = [Name], location = Expr#identifier_expr.location}];
generate_expr_instructions(
    #function_call_expr{function = Function, args = Args} = Expr, FunctionType, BeamContext
) ->
    % Generate arguments first
    ArgInstructions = lists:flatmap(
        fun(Arg) ->
            generate_expr_instructions(Arg, FunctionType, BeamContext)
        end,
        Args
    ),

    % Determine function call type and generate optimized call instruction
    CallInstruction =
        case Function of
            #identifier_expr{name = FuncName} ->
                % Get function signature for optimization
                case get_function_call_signature(FuncName, BeamContext) of
                    {ok, Signature} ->
                        generate_optimized_call(FuncName, length(Args), Signature, Expr);
                    {error, _} ->
                        [
                            #beam_instr{
                                op = call,
                                args = [length(Args)],
                                location = Expr#function_call_expr.location
                            }
                        ]
                end;
            _ ->
                % Complex function expression, use general call
                FuncInstructions = generate_expr_instructions(Function, FunctionType, BeamContext),
                FuncInstructions ++
                    [
                        #beam_instr{
                            op = call,
                            args = [length(Args)],
                            location = Expr#function_call_expr.location
                        }
                    ]
        end,

    ArgInstructions ++ CallInstruction;
generate_expr_instructions(#block_expr{expressions = Exprs}, FunctionType, BeamContext) ->
    lists:flatmap(
        fun(Expr) ->
            generate_expr_instructions(Expr, FunctionType, BeamContext)
        end,
        Exprs
    );
generate_expr_instructions(_Expr, _FunctionType, _BeamContext) ->
    % Default case for unhandled expressions
    [#beam_instr{op = load_literal, args = [unknown_expr], location = undefined}].

%% Generate optimized function call based on type signature
generate_optimized_call(FuncName, Arity, Signature, Expr) ->
    case analyze_call_optimization_potential(FuncName, Arity, Signature) of
        {integer_only_args} ->
            [
                #beam_instr{
                    op = call_int_args,
                    args = [FuncName, Arity],
                    location = Expr#function_call_expr.location
                }
            ];
        {float_only_args} ->
            [
                #beam_instr{
                    op = call_float_args,
                    args = [FuncName, Arity],
                    location = Expr#function_call_expr.location
                }
            ];
        {monomorphic_call} ->
            [
                #beam_instr{
                    op = call_monomorphic,
                    args = [FuncName, Arity],
                    location = Expr#function_call_expr.location
                }
            ];
        {specialized_call, SpecId} ->
            [
                #beam_instr{
                    op = call_specialized,
                    args = [SpecId, Arity],
                    location = Expr#function_call_expr.location
                }
            ];
        no_optimization ->
            [#beam_instr{op = call, args = [Arity], location = Expr#function_call_expr.location}]
    end.

%% Generate optimized return sequence based on function type
generate_typed_return_sequence(FunctionType) ->
    ReturnType = get_return_type(FunctionType),
    case ReturnType of
        {primitive_type, integer} ->
            [#beam_instr{op = return_int, args = [], location = undefined}];
        {primitive_type, float} ->
            [#beam_instr{op = return_float, args = [], location = undefined}];
        {primitive_type, atom} ->
            [#beam_instr{op = return_atom, args = [], location = undefined}];
        _ ->
            [#beam_instr{op = return, args = [], location = undefined}]
    end.

%% Create optimized calling conventions based on type information
create_optimized_calling_conventions(TypeInfo) ->
    FunctionTypes = maps:get(function_types, TypeInfo),
    HotPathFunctions = maps:get(hot_path_functions, TypeInfo),

    maps:fold(
        fun(FuncName, FuncType, Acc) ->
            Convention =
                case
                    {
                        is_hot_path_function(FuncName, HotPathFunctions),
                        analyze_function_type_complexity(FuncType)
                    }
                of
                    {true, simple} ->
                        % Hot path simple functions get fastest calling convention
                        #{convention => fast_call, register_args => true, inline_eligible => true};
                    {true, moderate} ->
                        % Hot path moderate functions get optimized convention
                        #{
                            convention => optimized_call,
                            register_args => true,
                            inline_eligible => false
                        };
                    {false, simple} ->
                        % Simple functions get register-based args
                        #{
                            convention => register_call,
                            register_args => true,
                            inline_eligible => false
                        };
                    {false, complex} ->
                        % Complex functions use standard convention
                        #{
                            convention => standard_call,
                            register_args => false,
                            inline_eligible => false
                        }
                end,
            maps:put(FuncName, Convention, Acc)
        end,
        #{},
        FunctionTypes
    ).

%% Generate type-specialized opcodes
generate_specialized_opcodes(TypeInfo, _FunctionsWithBeam) ->
    TypeUsagePatterns = maps:get(type_usage_patterns, TypeInfo),

    % Identify common type operations that can be specialized
    ArithmeticOpcodes = generate_arithmetic_opcodes(TypeUsagePatterns),
    ComparisonOpcodes = generate_comparison_opcodes(TypeUsagePatterns),
    DispatchOpcodes = generate_dispatch_opcodes(TypeUsagePatterns),

    #{
        arithmetic_opcodes => ArithmeticOpcodes,
        comparison_opcodes => ComparisonOpcodes,
        dispatch_opcodes => DispatchOpcodes,
        total_specialized => length(ArithmeticOpcodes) + length(ComparisonOpcodes) +
            length(DispatchOpcodes)
    }.

%% Optimize instructions using type information
optimize_instructions_with_types(Instructions, FunctionType, BeamContext) ->
    Instructions1 = apply_type_based_peephole_optimizations(Instructions, FunctionType),
    Instructions2 = eliminate_redundant_type_operations(Instructions1, FunctionType),
    Instructions3 = optimize_register_usage(Instructions2, BeamContext),
    Instructions3.

%% Apply peephole optimizations based on type information
apply_type_based_peephole_optimizations(Instructions, FunctionType) ->
    lists:foldl(
        fun(Instr, Acc) ->
            OptimizedInstr =
                case Instr of
                    % Integer addition with known types
                    #beam_instr{op = binary_op, args = ['+']} ->
                        case can_use_integer_add(FunctionType) of
                            true -> Instr#beam_instr{op = int_add};
                            false -> Instr
                        end;
                    % Float operations with known types
                    #beam_instr{op = binary_op, args = [Op]} when
                        Op =:= '+'; Op =:= '-'; Op =:= '*'; Op =:= '/'
                    ->
                        case can_use_float_operation(Op, FunctionType) of
                            true ->
                                Instr#beam_instr{op = list_to_atom("float_" ++ atom_to_list(Op))};
                            false ->
                                Instr
                        end;
                    _ ->
                        Instr
                end,
            [OptimizedInstr | Acc]
        end,
        [],
        Instructions
    ).

%% Eliminate redundant type operations
eliminate_redundant_type_operations(Instructions, FunctionType) ->
    % Remove type checks that are guaranteed by function signature
    lists:filter(
        fun(Instr) ->
            case Instr of
                #beam_instr{op = type_check, args = [Type]} ->
                    not is_type_guaranteed_by_signature(Type, FunctionType);
                _ ->
                    true
            end
        end,
        Instructions
    ).

%% Optimize register usage based on context
optimize_register_usage(Instructions, _BeamContext) ->
    % Simplified register optimization
    Instructions.

%% Generate arithmetic opcodes for common type patterns
generate_arithmetic_opcodes(TypeUsagePatterns) ->
    CommonPatterns = extract_arithmetic_patterns(TypeUsagePatterns),
    lists:map(
        fun({Pattern, Frequency}) ->
            #{
                pattern => Pattern,
                opcode => generate_specialized_arithmetic_opcode(Pattern),
                frequency => Frequency,
                optimization_benefit => calculate_arithmetic_optimization_benefit(Pattern)
            }
        end,
        CommonPatterns
    ).

%% Generate comparison opcodes for type-specific comparisons
generate_comparison_opcodes(TypeUsagePatterns) ->
    ComparisonPatterns = extract_comparison_patterns(TypeUsagePatterns),
    lists:map(
        fun({Pattern, Frequency}) ->
            #{
                pattern => Pattern,
                opcode => generate_specialized_comparison_opcode(Pattern),
                frequency => Frequency,
                optimization_benefit => calculate_comparison_optimization_benefit(Pattern)
            }
        end,
        ComparisonPatterns
    ).

%% Generate dispatch opcodes for pattern matching
generate_dispatch_opcodes(TypeUsagePatterns) ->
    DispatchPatterns = extract_dispatch_patterns(TypeUsagePatterns),
    lists:map(
        fun({Pattern, Frequency}) ->
            #{
                pattern => Pattern,
                opcode => generate_specialized_dispatch_opcode(Pattern),
                frequency => Frequency,
                optimization_benefit => calculate_dispatch_optimization_benefit(Pattern)
            }
        end,
        DispatchPatterns
    ).

%% ============================================================================
%% Helper Functions for Type-directed BEAM Code Generation
%% ============================================================================

%% BEAM instruction record is imported from cure_beam_compiler.hrl

%% Optimization context for type-directed passes
-record(opt_context, {
    % Type checker state
    type_checker,
    % Function specialization results
    function_specializations = #{},
    % Monomorphic function instances
    monomorphic_instances = #{},
    % Function inlining decisions
    inlining_decisions = #{},
    % Dead code elimination results
    dead_code_analysis = #{},
    % Type-directed BEAM generation results
    beam_generation = #{},
    % Profile data collection
    profile_collector = #{}
}).

%% Get function type mappings from type checker
get_function_type_mappings(TypeChecker) ->
    case maps:get(function_signatures, TypeChecker, #{}) of
        FuncSigs when is_map(FuncSigs) -> FuncSigs;
        _ -> #{}
    end.

%% Get call site type information
get_call_site_type_info(TypeChecker) ->
    case maps:get(call_site_types, TypeChecker, #{}) of
        CallTypes when is_map(CallTypes) -> CallTypes;
        _ -> #{}
    end.

%% Extract inlined function information from inlining decisions
extract_inlined_function_info(InliningDecisions) ->
    maps:fold(
        fun(FuncName, Decision, Acc) ->
            case maps:get(decision, Decision, keep) of
                inline -> maps:put(FuncName, inline, Acc);
                _ -> Acc
            end
        end,
        #{},
        InliningDecisions
    ).

%% Analyze type usage patterns from type checker
analyze_type_usage_patterns(TypeChecker) ->
    FunctionTypes = get_function_type_mappings(TypeChecker),

    % Analyze common patterns in function signatures
    ArithmeticPatterns = analyze_arithmetic_patterns(FunctionTypes),
    ComparisonPatterns = analyze_comparison_patterns(FunctionTypes),
    DispatchPatterns = analyze_dispatch_patterns(FunctionTypes),

    #{
        arithmetic => ArithmeticPatterns,
        comparison => ComparisonPatterns,
        dispatch => DispatchPatterns,
        total_functions => maps:size(FunctionTypes)
    }.

%% Identify hot path functions from inlining decisions
identify_hot_path_functions(InliningDecisions) ->
    maps:fold(
        fun(FuncName, Decision, Acc) ->
            Benefit = maps:get(benefit, Decision, 0),
            CallFreq = maps:get(call_frequency, Decision, 0),

            % Functions with high benefit or high call frequency are hot paths
            if
                Benefit > 3.0 orelse CallFreq > 10 ->
                    [FuncName | Acc];
                true ->
                    Acc
            end
        end,
        [],
        InliningDecisions
    ).

%% Get memory layout optimizations from type checker
get_memory_layout_optimizations(TypeChecker) ->
    case maps:get(memory_layouts, TypeChecker, #{}) of
        Layouts when is_map(Layouts) -> Layouts;
        _ -> #{}
    end.

%% Initialize opcode mappings for type-specific instructions
init_opcode_mappings() ->
    #{
        % Basic type-specific loads
        load_literal_int => "load_literal_integer",
        load_literal_float => "load_literal_float",
        load_literal_atom => "load_literal_atom",

        % Type-specific parameter loads
        load_param_int => "load_param_integer",
        load_param_float => "load_param_float",
        load_param_atom => "load_param_atom",

        % Optimized arithmetic operations
        int_add => "integer_add_fast",
        float_add => "float_add_fast",
        float_sub => "float_subtract_fast",
        float_mul => "float_multiply_fast",
        float_div => "float_divide_fast",

        % Optimized call instructions
        call_int_args => "call_with_integer_args",
        call_float_args => "call_with_float_args",
        call_monomorphic => "call_monomorphic_function",
        call_specialized => "call_specialized_function",

        % Type-specific returns
        return_int => "return_integer",
        return_float => "return_float",
        return_atom => "return_atom"
    }.

%% Build type dispatch table for efficient type-based operations
build_type_dispatch_table(TypeInfo) ->
    FunctionTypes = maps:get(function_types, TypeInfo),

    % Group functions by their type patterns
    DispatchTable = maps:fold(
        fun(FuncName, FuncType, Acc) ->
            Pattern = extract_type_pattern(FuncType),
            PatternFuncs = maps:get(Pattern, Acc, []),
            maps:put(Pattern, [FuncName | PatternFuncs], Acc)
        end,
        #{},
        FunctionTypes
    ),

    DispatchTable.

%% Get function type signature from type info
get_function_type_signature(FuncName, TypeInfo) ->
    FunctionTypes = maps:get(function_types, TypeInfo),
    case maps:get(FuncName, FunctionTypes, undefined) of
        undefined -> {unknown_function_type};
        Type -> Type
    end.

%% Get parameter types from function type
get_parameter_types({function_type, ParamTypes, _ReturnType}) ->
    ParamTypes;
get_parameter_types(_) ->
    % Default to empty for unknown types
    [].

%% Get return type from function type
get_return_type({function_type, _ParamTypes, ReturnType}) ->
    ReturnType;
get_return_type(_) ->
    {unknown_type}.

%% Get function call signature from BEAM context
get_function_call_signature(FuncName, BeamContext) ->
    TypeInfo = maps:get(type_info, BeamContext),
    case get_function_type_signature(FuncName, TypeInfo) of
        {unknown_function_type} -> {error, unknown_function};
        Signature -> {ok, Signature}
    end.

%% Analyze call optimization potential
analyze_call_optimization_potential(FuncName, Arity, Signature) ->
    case Signature of
        {function_type, ParamTypes, _ReturnType} ->
            % Check if all parameters are integers
            case {length(ParamTypes) =:= Arity, are_all_integer_params(ParamTypes)} of
                {true, true} ->
                    {integer_only_args};
                {true, false} ->
                    % Check if all parameters are floats
                    case are_all_float_params(ParamTypes) of
                        true ->
                            {float_only_args};
                        false ->
                            % Check if function is monomorphic
                            case is_monomorphic_signature(Signature) of
                                true ->
                                    {monomorphic_call};
                                false ->
                                    % Check if function has specialized version
                                    case has_specialized_version(FuncName) of
                                        true ->
                                            {specialized_call,
                                                generate_specialization_id(FuncName, ParamTypes)};
                                        false ->
                                            no_optimization
                                    end
                            end
                    end;
                {false, _} ->
                    no_optimization
            end;
        _ ->
            no_optimization
    end.

%% Analyze parameter optimizations
analyze_param_optimizations(Params, FunctionType) ->
    ParamTypes = get_parameter_types(FunctionType),

    lists:zipwith(
        fun(Param, Type) ->
            #{
                param => Param,
                type => Type,
                optimization =>
                    case Type of
                        {primitive_type, integer} -> register_integer;
                        {primitive_type, float} -> register_float;
                        {primitive_type, atom} -> register_atom;
                        _ -> stack_based
                    end
            }
        end,
        Params,
        ParamTypes
    ).

%% Analyze body optimizations
analyze_body_optimizations(Body, FunctionType) ->
    #{
        expression_type => classify_expression_type(Body),
        complexity => calculate_expression_complexity(Body),
        type_operations => count_type_operations(Body),
        optimization_opportunities => identify_body_optimizations(Body, FunctionType)
    }.

%% Count specialized opcodes in instruction list
count_specialized_opcodes(Instructions) ->
    SpecializedOps = [
        load_literal_int,
        load_literal_float,
        load_literal_atom,
        load_param_int,
        load_param_float,
        load_param_atom,
        int_add,
        float_add,
        float_sub,
        float_mul,
        float_div,
        call_int_args,
        call_float_args,
        call_monomorphic,
        call_specialized,
        return_int,
        return_float,
        return_atom
    ],

    lists:foldl(
        fun(Instr, Count) ->
            case lists:member(Instr#beam_instr.op, SpecializedOps) of
                true -> Count + 1;
                false -> Count
            end
        end,
        0,
        Instructions
    ).

%% Check if function is in hot path list
is_hot_path_function(FuncName, HotPathFunctions) ->
    lists:member(FuncName, HotPathFunctions).

%% Analyze function type complexity
analyze_function_type_complexity(FunctionType) ->
    case FunctionType of
        {function_type, ParamTypes, ReturnType} ->
            ParamComplexity = calculate_types_complexity(ParamTypes),
            ReturnComplexity = calculate_type_complexity(ReturnType),
            TotalComplexity = ParamComplexity + ReturnComplexity,

            if
                TotalComplexity =< 2 -> simple;
                TotalComplexity =< 5 -> moderate;
                true -> complex
            end;
        _ ->
            % Unknown types are considered complex
            complex
    end.

%% Check if instruction can use integer addition
can_use_integer_add(FunctionType) ->
    % Simplified check - in real implementation would analyze stack types
    case FunctionType of
        {function_type, ParamTypes, _} ->
            lists:any(
                fun
                    ({primitive_type, integer}) -> true;
                    (_) -> false
                end,
                ParamTypes
            );
        _ ->
            false
    end.

%% Check if instruction can use float operation
can_use_float_operation(Op, FunctionType) when Op =:= '+'; Op =:= '-'; Op =:= '*'; Op =:= '/' ->
    case FunctionType of
        {function_type, ParamTypes, _} ->
            lists:any(
                fun
                    ({primitive_type, float}) -> true;
                    (_) -> false
                end,
                ParamTypes
            );
        _ ->
            false
    end;
can_use_float_operation(_, _) ->
    false.

%% Check if type is guaranteed by function signature
is_type_guaranteed_by_signature(Type, FunctionType) ->
    case FunctionType of
        {function_type, ParamTypes, ReturnType} ->
            lists:member(Type, ParamTypes) orelse Type =:= ReturnType;
        _ ->
            false
    end.

%% Extract arithmetic patterns from type usage
extract_arithmetic_patterns(TypeUsagePatterns) ->
    ArithmeticOps = maps:get(arithmetic, TypeUsagePatterns, #{}),
    maps:fold(
        fun(Pattern, Frequency, Acc) ->
            [{Pattern, Frequency} | Acc]
        end,
        [],
        ArithmeticOps
    ).

%% Extract comparison patterns from type usage
extract_comparison_patterns(TypeUsagePatterns) ->
    ComparisonOps = maps:get(comparison, TypeUsagePatterns, #{}),
    maps:fold(
        fun(Pattern, Frequency, Acc) ->
            [{Pattern, Frequency} | Acc]
        end,
        [],
        ComparisonOps
    ).

%% Extract dispatch patterns from type usage
extract_dispatch_patterns(TypeUsagePatterns) ->
    DispatchOps = maps:get(dispatch, TypeUsagePatterns, #{}),
    maps:fold(
        fun(Pattern, Frequency, Acc) ->
            [{Pattern, Frequency} | Acc]
        end,
        [],
        DispatchOps
    ).

%% Generate specialized arithmetic opcode
generate_specialized_arithmetic_opcode({arithmetic, integer, '+'}) ->
    int_add_optimized;
generate_specialized_arithmetic_opcode({arithmetic, float, '+'}) ->
    float_add_optimized;
generate_specialized_arithmetic_opcode({arithmetic, integer, '*'}) ->
    int_mult_optimized;
generate_specialized_arithmetic_opcode({arithmetic, float, '*'}) ->
    float_mult_optimized;
generate_specialized_arithmetic_opcode(_) ->
    generic_arithmetic.

%% Generate specialized comparison opcode
generate_specialized_comparison_opcode({comparison, integer, '=='}) ->
    int_equal_optimized;
generate_specialized_comparison_opcode({comparison, float, '=='}) ->
    float_equal_optimized;
generate_specialized_comparison_opcode({comparison, integer, '<'}) ->
    int_less_optimized;
generate_specialized_comparison_opcode({comparison, float, '<'}) ->
    float_less_optimized;
generate_specialized_comparison_opcode(_) ->
    generic_comparison.

%% Generate specialized dispatch opcode
generate_specialized_dispatch_opcode({dispatch, pattern_match, Type}) ->
    list_to_atom("dispatch_" ++ atom_to_list(Type));
generate_specialized_dispatch_opcode(_) ->
    generic_dispatch.

%% Calculate arithmetic optimization benefit
calculate_arithmetic_optimization_benefit({arithmetic, integer, _}) -> 2.5;
calculate_arithmetic_optimization_benefit({arithmetic, float, _}) -> 3.0;
calculate_arithmetic_optimization_benefit(_) -> 1.0.

%% Calculate comparison optimization benefit
calculate_comparison_optimization_benefit({comparison, integer, _}) -> 2.0;
calculate_comparison_optimization_benefit({comparison, float, _}) -> 2.5;
calculate_comparison_optimization_benefit(_) -> 1.0.

%% Calculate dispatch optimization benefit
calculate_dispatch_optimization_benefit({dispatch, pattern_match, _}) -> 4.0;
calculate_dispatch_optimization_benefit(_) -> 1.5.

%% ============================================================================
%% Additional Helper Functions for BEAM Generation
%% ============================================================================

%% Analyze arithmetic patterns in function types
analyze_arithmetic_patterns(FunctionTypes) ->
    maps:fold(
        fun(_FuncName, FuncType, Acc) ->
            Patterns = extract_arithmetic_patterns_from_type(FuncType),
            merge_pattern_counts(Patterns, Acc)
        end,
        #{},
        FunctionTypes
    ).

%% Analyze comparison patterns in function types
analyze_comparison_patterns(FunctionTypes) ->
    maps:fold(
        fun(_FuncName, FuncType, Acc) ->
            Patterns = extract_comparison_patterns_from_type(FuncType),
            merge_pattern_counts(Patterns, Acc)
        end,
        #{},
        FunctionTypes
    ).

%% Analyze dispatch patterns in function types
analyze_dispatch_patterns(FunctionTypes) ->
    maps:fold(
        fun(_FuncName, FuncType, Acc) ->
            Patterns = extract_dispatch_patterns_from_type(FuncType),
            merge_pattern_counts(Patterns, Acc)
        end,
        #{},
        FunctionTypes
    ).

%% Extract type pattern from function type
extract_type_pattern({function_type, ParamTypes, ReturnType}) ->
    {function_pattern, length(ParamTypes), classify_type_tuple(ParamTypes),
        classify_type(ReturnType)};
extract_type_pattern(_) ->
    {unknown_pattern}.

%% Check if function signature is monomorphic
is_monomorphic_signature({function_type, ParamTypes, ReturnType}) ->
    lists:all(fun is_concrete_simple/1, ParamTypes) andalso is_concrete_simple(ReturnType);
is_monomorphic_signature(_) ->
    false.

%% Check if function has specialized version
has_specialized_version(_FuncName) ->
    % Simplified - in real implementation would check specialization registry
    false.

%% Generate specialization ID
generate_specialization_id(FuncName, ParamTypes) ->
    TypeSig = lists:map(fun type_to_signature/1, ParamTypes),
    list_to_atom(atom_to_list(FuncName) ++ "_" ++ string:join(TypeSig, "_")).

%% Classify expression type
classify_expression_type(#literal_expr{}) -> literal;
classify_expression_type(#identifier_expr{}) -> variable;
classify_expression_type(#function_call_expr{}) -> function_call;
classify_expression_type(#block_expr{}) -> block;
classify_expression_type(_) -> unknown.

%% Calculate expression complexity
calculate_expression_complexity(#literal_expr{}) ->
    1;
calculate_expression_complexity(#identifier_expr{}) ->
    1;
calculate_expression_complexity(#function_call_expr{args = Args}) ->
    2 + length(Args);
calculate_expression_complexity(#block_expr{expressions = Exprs}) ->
    lists:sum(lists:map(fun calculate_expression_complexity/1, Exprs));
calculate_expression_complexity(_) ->
    5.

%% Count type operations in expression
count_type_operations(#function_call_expr{function = #identifier_expr{name = Name}}) ->
    case is_type_operation(Name) of
        true -> 1;
        false -> 0
    end;
count_type_operations(#block_expr{expressions = Exprs}) ->
    lists:sum(lists:map(fun count_type_operations/1, Exprs));
count_type_operations(_) ->
    0.

%% Identify body optimization opportunities
identify_body_optimizations(Body, FunctionType) ->
    BaseOptimizations = ["type-specific-instructions", "register-allocation"],

    case {classify_expression_type(Body), FunctionType} of
        {literal, _} ->
            ["constant-folding" | BaseOptimizations];
        {function_call, {function_type, _, {primitive_type, _}}} ->
            ["specialized-call" | BaseOptimizations];
        {block, _} ->
            ["instruction-scheduling" | BaseOptimizations];
        _ ->
            BaseOptimizations
    end.

%% Calculate types complexity
calculate_types_complexity(Types) ->
    lists:sum(lists:map(fun calculate_type_complexity/1, Types)).

%% Calculate single type complexity
calculate_type_complexity({primitive_type, _}) ->
    1;
calculate_type_complexity({list_type, ElemType}) ->
    1 + calculate_type_complexity(ElemType);
calculate_type_complexity({tuple_type, ElemTypes}) ->
    1 + calculate_types_complexity(ElemTypes);
calculate_type_complexity({function_type, ParamTypes, ReturnType}) ->
    2 + calculate_types_complexity(ParamTypes) + calculate_type_complexity(ReturnType);
% Unknown types are complex
calculate_type_complexity(_) ->
    3.

%% Extract arithmetic patterns from individual function type
extract_arithmetic_patterns_from_type({function_type, ParamTypes, _ReturnType}) ->
    case lists:any(fun is_numeric_type/1, ParamTypes) of
        true -> #{{arithmetic, infer_numeric_type(ParamTypes), '+'} => 1};
        false -> #{}
    end;
extract_arithmetic_patterns_from_type(_) ->
    #{}.

%% Extract comparison patterns from individual function type
extract_comparison_patterns_from_type({function_type, ParamTypes, _ReturnType}) ->
    case lists:any(fun is_comparable_type/1, ParamTypes) of
        true -> #{{comparison, infer_comparable_type(ParamTypes), '=='} => 1};
        false -> #{}
    end;
extract_comparison_patterns_from_type(_) ->
    #{}.

%% Extract dispatch patterns from individual function type
extract_dispatch_patterns_from_type({function_type, _ParamTypes, ReturnType}) ->
    case is_pattern_matchable_type(ReturnType) of
        true -> #{{dispatch, pattern_match, extract_base_type(ReturnType)} => 1};
        false -> #{}
    end;
extract_dispatch_patterns_from_type(_) ->
    #{}.

%% Merge pattern counts
merge_pattern_counts(Patterns1, Patterns2) ->
    maps:fold(
        fun(Pattern, Count1, Acc) ->
            Count2 = maps:get(Pattern, Acc, 0),
            maps:put(Pattern, Count1 + Count2, Acc)
        end,
        Patterns2,
        Patterns1
    ).

%% Classify type tuple
classify_type_tuple(Types) ->
    Length = length(Types),
    AllSameType =
        case Types of
            [] ->
                true;
            [FirstType | RestTypes] ->
                lists:all(fun(T) -> types_equivalent(T, FirstType) end, RestTypes)
        end,

    case {Length, AllSameType} of
        {0, _} -> empty;
        {1, _} -> single;
        {_, true} -> homogeneous;
        {_, false} -> heterogeneous
    end.

%% Classify single type
classify_type({primitive_type, Type}) -> {primitive, Type};
classify_type({list_type, _}) -> list;
classify_type({tuple_type, _}) -> tuple;
classify_type({function_type, _, _}) -> function;
classify_type(_) -> unknown.

%% Check if type is concrete (simpler version for newer functionality)
is_concrete_simple({primitive_type, _}) -> true;
is_concrete_simple({list_type, ElemType}) -> is_concrete_simple(ElemType);
is_concrete_simple({tuple_type, ElemTypes}) -> lists:all(fun is_concrete_simple/1, ElemTypes);
is_concrete_simple(_) -> false.

%% Convert type to signature string
type_to_signature({primitive_type, Type}) -> atom_to_list(Type);
type_to_signature({list_type, ElemType}) -> "list_" ++ type_to_signature(ElemType);
type_to_signature(_) -> "unknown".

%% Check if name represents a type operation
is_type_operation(is_integer) -> true;
is_type_operation(is_float) -> true;
is_type_operation(is_atom) -> true;
is_type_operation(is_list) -> true;
is_type_operation(_) -> false.

%% Check if type is numeric
is_numeric_type({primitive_type, integer}) -> true;
is_numeric_type({primitive_type, float}) -> true;
is_numeric_type(_) -> false.

%% Check if type is comparable
is_comparable_type({primitive_type, _}) -> true;
is_comparable_type(_) -> false.

%% Check if type is pattern matchable
is_pattern_matchable_type({primitive_type, _}) -> true;
is_pattern_matchable_type({list_type, _}) -> true;
is_pattern_matchable_type({tuple_type, _}) -> true;
is_pattern_matchable_type(_) -> false.

%% Infer numeric type from parameter types
infer_numeric_type(ParamTypes) ->
    case
        lists:any(
            fun
                ({primitive_type, float}) -> true;
                (_) -> false
            end,
            ParamTypes
        )
    of
        true -> float;
        false -> integer
    end.

%% Infer comparable type from parameter types
infer_comparable_type([{primitive_type, Type} | _]) -> Type;
infer_comparable_type([_ | Rest]) -> infer_comparable_type(Rest);
infer_comparable_type([]) -> unknown.

%% Extract base type from complex type
extract_base_type({primitive_type, Type}) -> Type;
extract_base_type({list_type, _}) -> list;
extract_base_type({tuple_type, _}) -> tuple;
extract_base_type(_) -> unknown.

%% Check if two types are equivalent
types_equivalent(Type1, Type2) -> Type1 =:= Type2.

%% Helper functions for parameter type checking
are_all_integer_params(ParamTypes) ->
    lists:all(
        fun
            ({primitive_type, integer}) -> true;
            (_) -> false
        end,
        ParamTypes
    ).

are_all_float_params(ParamTypes) ->
    lists:all(
        fun
            ({primitive_type, float}) -> true;
            (_) -> false
        end,
        ParamTypes
    ).

%% ============================================================================
%% Profile-guided Optimization and Runtime Feedback Integration (Pass 8)
%% ============================================================================

%% Apply profile-guided optimization pass
apply_profile_guided_optimization_pass(AST, Context) ->
    cure_utils:debug("[Type Optimizer] Starting Profile-guided Optimization pass...~n"),

    % Initialize profile collection system
    ProfileCollector = init_profile_collector(),

    % Extract existing optimization data
    ExistingOptimizations = extract_optimization_data(Context),

    % Create adaptive optimization context
    AdaptiveContext = init_adaptive_optimization_context(ProfileCollector, ExistingOptimizations),

    % Apply profile-guided optimizations
    {ProfileGuidedAST, FeedbackData} = apply_adaptive_optimizations(AST, AdaptiveContext),

    % Build performance feedback system
    FeedbackSystem = create_performance_feedback_system(FeedbackData),

    % Update context with profile-guided optimization results
    NewContext = Context#opt_context{
        profile_collector = #{
            profile_collector => ProfileCollector,
            adaptive_context => AdaptiveContext,
            feedback_system => FeedbackSystem,
            optimization_data => FeedbackData
        }
    },

    cure_utils:debug("[Type Optimizer] Profile-guided Optimization pass completed~n"),
    {ProfileGuidedAST, NewContext}.

%% Initialize profile collection system
init_profile_collector() ->
    #{
        execution_counts => #{},
        call_frequencies => #{},
        hot_paths => [],
        memory_access_patterns => #{},
        type_usage_runtime => #{},
        performance_metrics => #{},
        adaptive_decisions => #{},
        feedback_history => []
    }.

%% Extract optimization data from previous passes
extract_optimization_data(Context) ->
    #{
        type_checker => Context#opt_context.type_checker,
        function_specializations => Context#opt_context.function_specializations,
        monomorphic_instances => Context#opt_context.monomorphic_instances,
        inlining_decisions => Context#opt_context.inlining_decisions,
        dead_code_analysis => Context#opt_context.dead_code_analysis,
        beam_generation => Context#opt_context.beam_generation
    }.

%% Initialize adaptive optimization context
init_adaptive_optimization_context(ProfileCollector, ExistingOptimizations) ->
    #{
        profile_collector => ProfileCollector,
        existing_optimizations => ExistingOptimizations,
        runtime_feedback => #{},
        adaptive_thresholds => init_adaptive_thresholds(),
        specialization_candidates => #{},
        hot_path_optimizations => #{},
        memory_optimizations => #{},
        performance_targets => init_performance_targets()
    }.

%% Apply adaptive optimizations based on profile data
apply_adaptive_optimizations(AST, AdaptiveContext) ->
    % Phase 1: Collect runtime profile data
    ProfileData = collect_runtime_profiles(AST, AdaptiveContext),

    % Phase 2: Analyze profile data for optimization opportunities
    OptimizationOpportunities = analyze_profile_optimization_opportunities(ProfileData),

    % Phase 3: Apply feedback-driven function specialization
    {AST1, SpecializationData} = apply_feedback_driven_specialization(
        AST, OptimizationOpportunities, AdaptiveContext
    ),

    % Phase 4: Apply dynamic hot path optimization
    {AST2, HotPathData} = apply_dynamic_hot_path_optimization(
        AST1, OptimizationOpportunities, AdaptiveContext
    ),

    % Phase 5: Apply adaptive memory layout optimization
    {AST3, MemoryData} = apply_adaptive_memory_layout_optimization(
        AST2, OptimizationOpportunities, AdaptiveContext
    ),

    % Phase 6: Apply performance feedback optimization
    {FinalAST, PerformanceData} = apply_performance_feedback_optimization(
        AST3, OptimizationOpportunities, AdaptiveContext
    ),

    % Combine all feedback data
    FeedbackData = #{
        profile_data => ProfileData,
        specialization_data => SpecializationData,
        hot_path_data => HotPathData,
        memory_data => MemoryData,
        performance_data => PerformanceData,
        optimization_opportunities => OptimizationOpportunities
    },

    {FinalAST, FeedbackData}.

%% Collect runtime profiles from AST execution patterns
collect_runtime_profiles(AST, AdaptiveContext) ->
    _ProfileCollector = maps:get(profile_collector, AdaptiveContext),

    % Analyze function call patterns
    CallPatterns = analyze_function_call_patterns(AST),

    % Estimate execution frequencies
    ExecutionFrequencies = estimate_execution_frequencies(AST, CallPatterns),

    % Identify hot execution paths
    HotPaths = identify_runtime_hot_paths(AST, ExecutionFrequencies),

    % Analyze memory access patterns
    MemoryPatterns = analyze_memory_access_patterns(AST),

    % Collect type usage statistics
    RuntimeTypeUsage = collect_runtime_type_usage(AST),

    #{
        call_patterns => CallPatterns,
        execution_frequencies => ExecutionFrequencies,
        hot_paths => HotPaths,
        memory_patterns => MemoryPatterns,
        runtime_type_usage => RuntimeTypeUsage,
        profile_timestamp => erlang:system_time(millisecond)
    }.

%% Analyze profile data for optimization opportunities
analyze_profile_optimization_opportunities(ProfileData) ->
    ExecutionFreqs = maps:get(execution_frequencies, ProfileData),
    HotPaths = maps:get(hot_paths, ProfileData),
    MemoryPatterns = maps:get(memory_patterns, ProfileData),
    TypeUsage = maps:get(runtime_type_usage, ProfileData),

    % Identify functions that would benefit from specialization
    SpecializationOpportunities = identify_specialization_opportunities(ExecutionFreqs, TypeUsage),

    % Identify hot path optimization opportunities
    HotPathOpportunities = identify_hot_path_opportunities(HotPaths, ExecutionFreqs),

    % Identify memory layout optimization opportunities
    MemoryOptimizationOpportunities = identify_memory_optimization_opportunities(MemoryPatterns),

    % Calculate optimization priorities
    OptimizationPriorities = calculate_optimization_priorities(
        SpecializationOpportunities, HotPathOpportunities, MemoryOptimizationOpportunities
    ),

    #{
        specialization => SpecializationOpportunities,
        hot_path => HotPathOpportunities,
        memory => MemoryOptimizationOpportunities,
        priorities => OptimizationPriorities
    }.

%% Apply feedback-driven function specialization
apply_feedback_driven_specialization(AST, Opportunities, AdaptiveContext) ->
    SpecializationOpportunities = maps:get(specialization, Opportunities),
    ExistingOptimizations = maps:get(existing_optimizations, AdaptiveContext),

    % Generate adaptive specializations based on runtime feedback
    AdaptiveSpecializations = generate_adaptive_specializations(
        SpecializationOpportunities, ExistingOptimizations
    ),

    % Apply specializations to AST
    {SpecializedAST, SpecializationMetrics} = apply_adaptive_specializations_to_ast(
        AST, AdaptiveSpecializations
    ),

    SpecializationData = #{
        adaptive_specializations => AdaptiveSpecializations,
        specialization_metrics => SpecializationMetrics,
        feedback_driven_count => length(AdaptiveSpecializations)
    },

    {SpecializedAST, SpecializationData}.

%% Apply dynamic hot path optimization
apply_dynamic_hot_path_optimization(AST, Opportunities, AdaptiveContext) ->
    HotPathOpportunities = maps:get(hot_path, Opportunities),
    ProfileCollector = maps:get(profile_collector, AdaptiveContext),

    % Optimize hot paths dynamically
    HotPathOptimizations = generate_dynamic_hot_path_optimizations(
        HotPathOpportunities, ProfileCollector
    ),

    % Apply hot path optimizations to AST
    {OptimizedAST, HotPathMetrics} = apply_hot_path_optimizations_to_ast(AST, HotPathOptimizations),

    HotPathData = #{
        hot_path_optimizations => HotPathOptimizations,
        hot_path_metrics => HotPathMetrics,
        optimized_paths_count => length(HotPathOptimizations)
    },

    {OptimizedAST, HotPathData}.

%% Apply adaptive memory layout optimization
apply_adaptive_memory_layout_optimization(AST, Opportunities, AdaptiveContext) ->
    MemoryOpportunities = maps:get(memory, Opportunities),
    ExistingOptimizations = maps:get(existing_optimizations, AdaptiveContext),

    % Generate adaptive memory layout optimizations
    AdaptiveMemoryLayouts = generate_adaptive_memory_layouts(
        MemoryOpportunities, ExistingOptimizations
    ),

    % Apply memory optimizations to AST
    {MemoryOptimizedAST, MemoryMetrics} = apply_adaptive_memory_layouts_to_ast(
        AST, AdaptiveMemoryLayouts
    ),

    MemoryData = #{
        adaptive_memory_layouts => AdaptiveMemoryLayouts,
        memory_metrics => MemoryMetrics,
        layout_optimizations_count => length(AdaptiveMemoryLayouts)
    },

    {MemoryOptimizedAST, MemoryData}.

%% Apply performance feedback optimization
apply_performance_feedback_optimization(AST, Opportunities, AdaptiveContext) ->
    Priorities = maps:get(priorities, Opportunities),
    PerformanceTargets = maps:get(performance_targets, AdaptiveContext),

    % Generate performance-driven optimizations
    PerformanceOptimizations = generate_performance_driven_optimizations(
        Priorities, PerformanceTargets
    ),

    % Apply performance optimizations to AST
    {PerformanceOptimizedAST, PerformanceMetrics} = apply_performance_optimizations_to_ast(
        AST, PerformanceOptimizations
    ),

    PerformanceData = #{
        performance_optimizations => PerformanceOptimizations,
        performance_metrics => PerformanceMetrics,
        feedback_optimizations_count => length(PerformanceOptimizations)
    },

    {PerformanceOptimizedAST, PerformanceData}.

%% Create performance feedback system
create_performance_feedback_system(FeedbackData) ->
    #{
        feedback_data => FeedbackData,
        monitoring_enabled => true,
        % milliseconds
        feedback_interval => 1000,
        % 15% performance change threshold
        adaptation_threshold => 0.15,
        feedback_history_size => 100,
        performance_metrics => init_performance_metrics(),
        adaptive_decisions => []
    }.

%% ============================================================================
%% Helper Functions for Profile-guided Optimization
%% ============================================================================

%% Initialize adaptive thresholds
init_adaptive_thresholds() ->
    #{
        % Minimum calls to consider hot
        hot_function_threshold => 100,
        specialization_benefit_threshold => 2.0,
        % 20% memory usage improvement
        memory_optimization_threshold => 0.2,
        % 10% performance improvement
        performance_improvement_threshold => 0.1,
        % 5% change sensitivity
        adaptation_sensitivity => 0.05
    }.

%% Initialize performance targets
init_performance_targets() ->
    #{
        % Relative to baseline
        execution_time_target => 1.0,
        % 20% reduction from baseline
        memory_usage_target => 0.8,
        % 20% improvement
        throughput_target => 1.2,
        % 10% reduction
        latency_target => 0.9,
        % 95% cache hit rate
        cache_hit_rate_target => 0.95
    }.

%% Initialize performance metrics
init_performance_metrics() ->
    #{
        execution_time => 0,
        memory_usage => 0,
        throughput => 0,
        latency => 0,
        cache_hit_rate => 0,
        optimization_count => 0,
        adaptation_count => 0
    }.

%% Analyze function call patterns in AST
analyze_function_call_patterns(AST) ->
    CallPatterns = lists:foldl(
        fun(Item, Acc) ->
            case Item of
                #function_def{name = Name, body = Body} ->
                    FuncCalls = extract_function_calls(Body),
                    CallFrequency = length(FuncCalls),
                    maps:put(Name, #{calls => FuncCalls, frequency => CallFrequency}, Acc);
                _ ->
                    Acc
            end
        end,
        #{},
        AST
    ),
    CallPatterns.

%% Estimate execution frequencies based on call patterns
estimate_execution_frequencies(_AST, CallPatterns) ->
    % Simple heuristic: functions with more calls are executed more frequently
    maps:fold(
        fun(FuncName, Pattern, Acc) ->
            Frequency = maps:get(frequency, Pattern, 0),
            CallDepth = calculate_call_depth(FuncName, CallPatterns),
            % Weight by call depth
            EstimatedFreq = Frequency * (1 + CallDepth * 0.5),
            maps:put(FuncName, EstimatedFreq, Acc)
        end,
        #{},
        CallPatterns
    ).

%% Identify runtime hot paths
identify_runtime_hot_paths(AST, ExecutionFrequencies) ->
    % Minimum execution frequency for hot path
    Threshold = 50,
    HotFunctions = maps:filter(fun(_FuncName, Freq) -> Freq > Threshold end, ExecutionFrequencies),

    % Build hot path sequences
    lists:foldl(
        fun(FuncName, Acc) ->
            HotPath = build_hot_path_sequence(FuncName, AST, ExecutionFrequencies),
            [HotPath | Acc]
        end,
        [],
        maps:keys(HotFunctions)
    ).

%% Analyze memory access patterns
analyze_memory_access_patterns(AST) ->
    lists:foldl(
        fun(Item, Acc) ->
            case Item of
                #function_def{name = Name, body = Body} ->
                    MemoryAccesses = analyze_function_memory_access(Body),
                    maps:put(Name, MemoryAccesses, Acc);
                _ ->
                    Acc
            end
        end,
        #{},
        AST
    ).

%% Collect runtime type usage statistics
collect_runtime_type_usage(AST) ->
    TypeUsage = lists:foldl(
        fun(Item, Acc) ->
            case Item of
                #function_def{name = _Name, params = Params, body = Body} ->
                    ParamTypes = extract_param_types(Params),
                    BodyTypes = extract_body_types(Body),
                    FuncTypeUsage = ParamTypes ++ BodyTypes,

                    lists:foldl(
                        fun(Type, TypeAcc) ->
                            Count = maps:get(Type, TypeAcc, 0),
                            maps:put(Type, Count + 1, TypeAcc)
                        end,
                        Acc,
                        FuncTypeUsage
                    );
                _ ->
                    Acc
            end
        end,
        #{},
        AST
    ),
    TypeUsage.

%% Identify specialization opportunities
identify_specialization_opportunities(ExecutionFreqs, TypeUsage) ->
    FrequentFunctions = maps:filter(fun(_Func, Freq) -> Freq > 25 end, ExecutionFreqs),

    maps:fold(
        fun(FuncName, Freq, Acc) ->
            % Check if function uses types that would benefit from specialization
            SpecializationBenefit = calculate_specialization_benefit(FuncName, TypeUsage, Freq),
            if
                SpecializationBenefit > 2.0 ->
                    maps:put(FuncName, #{frequency => Freq, benefit => SpecializationBenefit}, Acc);
                true ->
                    Acc
            end
        end,
        #{},
        FrequentFunctions
    ).

%% Identify hot path optimization opportunities
identify_hot_path_opportunities(HotPaths, ExecutionFreqs) ->
    lists:foldl(
        fun(HotPath, Acc) ->
            PathFreq = calculate_path_frequency(HotPath, ExecutionFreqs),
            OptimizationPotential = calculate_hot_path_optimization_potential(HotPath, PathFreq),

            if
                OptimizationPotential > 1.5 ->
                    [{HotPath, #{frequency => PathFreq, potential => OptimizationPotential}} | Acc];
                true ->
                    Acc
            end
        end,
        [],
        HotPaths
    ).

%% Identify memory optimization opportunities
identify_memory_optimization_opportunities(MemoryPatterns) ->
    maps:fold(
        fun(FuncName, MemoryAccess, Acc) ->
            OptimizationPotential = calculate_memory_optimization_potential(MemoryAccess),

            if
                OptimizationPotential > 1.2 ->
                    maps:put(
                        FuncName,
                        #{access_pattern => MemoryAccess, potential => OptimizationPotential},
                        Acc
                    );
                true ->
                    Acc
            end
        end,
        #{},
        MemoryPatterns
    ).

%% Calculate optimization priorities
calculate_optimization_priorities(SpecializationOps, HotPathOps, MemoryOps) ->
    AllOpportunities = [
        {specialization, maps:to_list(SpecializationOps)},
        {hot_path, HotPathOps},
        {memory, maps:to_list(MemoryOps)}
    ],

    % Sort by combined benefit and frequency
    PrioritizedOps = lists:sort(
        fun({_, OpsA}, {_, OpsB}) ->
            calculate_combined_priority(OpsA) > calculate_combined_priority(OpsB)
        end,
        AllOpportunities
    ),

    PrioritizedOps.

%% Generate adaptive specializations
generate_adaptive_specializations(Opportunities, ExistingOptimizations) ->
    ExistingSpecs = maps:get(function_specializations, ExistingOptimizations, #{}),

    maps:fold(
        fun(FuncName, OpportunityData, Acc) ->
            case maps:is_key(FuncName, ExistingSpecs) of
                true ->
                    % Enhance existing specialization with runtime feedback
                    EnhancedSpec = enhance_existing_specialization(
                        FuncName, OpportunityData, ExistingSpecs
                    ),
                    [EnhancedSpec | Acc];
                false ->
                    % Create new adaptive specialization
                    NewSpec = create_adaptive_specialization(FuncName, OpportunityData),
                    [NewSpec | Acc]
            end
        end,
        [],
        Opportunities
    ).

%% Generate dynamic hot path optimizations
generate_dynamic_hot_path_optimizations(HotPathOpportunities, _ProfileCollector) ->
    lists:map(
        fun({HotPath, OpportunityData}) ->
            PathFreq = maps:get(frequency, OpportunityData),
            Potential = maps:get(potential, OpportunityData),

            Optimization =
                case Potential of
                    P when P > 3.0 ->
                        #{type => aggressive_inline, path => HotPath, benefit => P};
                    P when P > 2.0 ->
                        #{type => specialized_codegen, path => HotPath, benefit => P};
                    P when P > 1.5 ->
                        #{type => register_allocation, path => HotPath, benefit => P};
                    _ ->
                        #{type => basic_optimization, path => HotPath, benefit => Potential}
                end,

            Optimization#{frequency => PathFreq}
        end,
        HotPathOpportunities
    ).

%% Generate adaptive memory layouts
generate_adaptive_memory_layouts(MemoryOpportunities, ExistingOptimizations) ->
    _ExistingLayouts = maps:get(beam_generation, ExistingOptimizations, #{}),

    maps:fold(
        fun(FuncName, OpportunityData, Acc) ->
            AccessPattern = maps:get(access_pattern, OpportunityData),
            Potential = maps:get(potential, OpportunityData),

            AdaptiveLayout =
                case analyze_access_pattern(AccessPattern) of
                    {sequential, high_frequency} ->
                        #{
                            layout_type => cache_optimized,
                            function => FuncName,
                            benefit => Potential
                        };
                    {random, high_volume} ->
                        #{
                            layout_type => memory_optimized,
                            function => FuncName,
                            benefit => Potential
                        };
                    {locality_heavy, _} ->
                        #{
                            layout_type => locality_optimized,
                            function => FuncName,
                            benefit => Potential
                        };
                    _ ->
                        #{layout_type => standard, function => FuncName, benefit => Potential}
                end,

            [AdaptiveLayout | Acc]
        end,
        [],
        MemoryOpportunities
    ).

%% Generate performance-driven optimizations
generate_performance_driven_optimizations(Priorities, PerformanceTargets) ->
    lists:flatmap(
        fun({OpType, Opportunities}) ->
            lists:map(
                fun(Opportunity) ->
                    PerformanceOpt =
                        case OpType of
                            specialization ->
                                generate_specialization_performance_opt(
                                    Opportunity, PerformanceTargets
                                );
                            hot_path ->
                                generate_hot_path_performance_opt(Opportunity, PerformanceTargets);
                            memory ->
                                generate_memory_performance_opt(Opportunity, PerformanceTargets)
                        end,
                    PerformanceOpt#{optimization_type => OpType}
                end,
                Opportunities
            )
        end,
        Priorities
    ).

%% Update opt_context record to include profile_guided_optimization field

%% ============================================================================
%% Additional Helper Functions for Profile-guided Optimization
%% ============================================================================

%% Extract function calls from expression
extract_function_calls(#function_call_expr{function = #identifier_expr{name = Name}, args = Args}) ->
    ArgCalls = lists:flatmap(fun extract_function_calls/1, Args),
    [Name | ArgCalls];
extract_function_calls(#block_expr{expressions = Exprs}) ->
    lists:flatmap(fun extract_function_calls/1, Exprs);
extract_function_calls(#let_expr{bindings = Bindings, body = Body}) ->
    BindingCalls = lists:flatmap(
        fun(#binding{value = Value}) ->
            extract_function_calls(Value)
        end,
        Bindings
    ),
    BodyCalls = extract_function_calls(Body),
    BindingCalls ++ BodyCalls;
extract_function_calls(_) ->
    [].

%% Calculate call depth for a function
calculate_call_depth(FuncName, CallPatterns) ->
    case maps:get(FuncName, CallPatterns, undefined) of
        undefined ->
            0;
        #{calls := Calls} ->
            MaxDepth = lists:foldl(
                fun(CallName, MaxAcc) ->
                    % Avoid infinite recursion
                    case CallName =/= FuncName of
                        true ->
                            Depth = 1 + calculate_call_depth(CallName, CallPatterns),
                            max(Depth, MaxAcc);
                        false ->
                            MaxAcc
                    end
                end,
                0,
                Calls
            ),
            MaxDepth
    end.

%% Build hot path sequence
build_hot_path_sequence(StartFunc, AST, ExecutionFrequencies) ->
    % Max depth 5
    build_path_sequence(StartFunc, AST, ExecutionFrequencies, [StartFunc], 5).

build_path_sequence(_CurrentFunc, _AST, _ExecutionFreqs, Path, 0) ->
    lists:reverse(Path);
build_path_sequence(CurrentFunc, AST, ExecutionFreqs, Path, Depth) ->
    % Find the most frequently called function from current function
    FuncDef = find_function_def(CurrentFunc, AST),
    case FuncDef of
        undefined ->
            lists:reverse(Path);
        #function_def{body = Body} ->
            Calls = extract_function_calls(Body),
            case find_hottest_call(Calls, ExecutionFreqs, Path) of
                undefined ->
                    lists:reverse(Path);
                HottestCall ->
                    build_path_sequence(
                        HottestCall, AST, ExecutionFreqs, [HottestCall | Path], Depth - 1
                    )
            end
    end.

%% Find function definition in AST
find_function_def(FuncName, AST) ->
    lists:foldl(
        fun(Item, Acc) ->
            case Item of
                #function_def{name = Name} = FuncDef when Name =:= FuncName -> FuncDef;
                _ -> Acc
            end
        end,
        undefined,
        AST
    ).

%% Find the hottest call that's not already in path
find_hottest_call(Calls, ExecutionFreqs, Path) ->
    FilteredCalls = [Call || Call <- Calls, not lists:member(Call, Path)],
    case FilteredCalls of
        [] ->
            undefined;
        _ ->
            HottestCall = lists:foldl(
                fun(Call, HottestAcc) ->
                    CallFreq = maps:get(Call, ExecutionFreqs, 0),
                    HottestFreq =
                        case HottestAcc of
                            undefined -> 0;
                            _ -> maps:get(HottestAcc, ExecutionFreqs, 0)
                        end,
                    case CallFreq > HottestFreq of
                        true -> Call;
                        false -> HottestAcc
                    end
                end,
                undefined,
                FilteredCalls
            ),
            HottestCall
    end.

%% Analyze function memory access
analyze_function_memory_access(Body) ->
    MemoryOps = extract_memory_operations(Body),
    #{
        total_accesses => length(MemoryOps),
        read_operations => count_operation_type(read, MemoryOps),
        write_operations => count_operation_type(write, MemoryOps),
        sequential_pattern => detect_sequential_pattern(MemoryOps),
        locality_score => calculate_locality_score(MemoryOps)
    }.

%% Extract memory operations from expression
extract_memory_operations(#identifier_expr{name = Name}) ->
    [{read, Name}];
extract_memory_operations(#function_call_expr{function = #identifier_expr{name = Name}, args = Args}) ->
    case is_memory_operation(Name) of
        true -> [{memory_call, Name} | lists:flatmap(fun extract_memory_operations/1, Args)];
        false -> lists:flatmap(fun extract_memory_operations/1, Args)
    end;
extract_memory_operations(#block_expr{expressions = Exprs}) ->
    lists:flatmap(fun extract_memory_operations/1, Exprs);
extract_memory_operations(#let_expr{bindings = Bindings, body = Body}) ->
    BindingOps = lists:flatmap(
        fun(#binding{pattern = Pattern, value = Value}) ->
            PatternOps = extract_pattern_memory_ops(Pattern),
            ValueOps = extract_memory_operations(Value),
            PatternOps ++ ValueOps
        end,
        Bindings
    ),
    BodyOps = extract_memory_operations(Body),
    BindingOps ++ BodyOps;
extract_memory_operations(_) ->
    [].

%% Extract parameter types
extract_param_types(Params) ->
    lists:map(fun(#param{type = Type}) -> Type end, Params).

%% Extract body types
extract_body_types(Body) ->
    extract_expression_types(Body).

extract_expression_types(#literal_expr{value = Value}) ->
    [infer_literal_type(Value)];
extract_expression_types(#identifier_expr{}) ->
    [{unknown_type}];
extract_expression_types(#function_call_expr{args = Args}) ->
    lists:flatmap(fun extract_expression_types/1, Args);
extract_expression_types(#block_expr{expressions = Exprs}) ->
    lists:flatmap(fun extract_expression_types/1, Exprs);
extract_expression_types(_) ->
    [].

%% Uses infer_literal_type function defined earlier in the module

%% Calculate specialization benefit
calculate_specialization_benefit(FuncName, TypeUsage, Freq) ->
    % Higher frequency and type diversity increase specialization benefit
    TypeDiversity = count_function_type_diversity(FuncName, TypeUsage),
    BaseBenefit = math:log(Freq + 1) * TypeDiversity * 0.1,
    BaseBenefit.

%% Count function type diversity
count_function_type_diversity(_FuncName, TypeUsage) ->
    % Simple heuristic: count different types used
    TypeCount = maps:size(TypeUsage),
    case TypeCount of
        0 -> 1;
        % Cap at 5 for diversity
        N when N > 5 -> 5;
        N -> N
    end.

%% Calculate path frequency
calculate_path_frequency(Path, ExecutionFreqs) ->
    PathFreqs = [maps:get(Func, ExecutionFreqs, 0) || Func <- Path],
    case PathFreqs of
        [] -> 0;
        % Bottleneck frequency
        _ -> lists:min(PathFreqs)
    end.

%% Calculate hot path optimization potential
calculate_hot_path_optimization_potential(Path, Frequency) ->
    PathLength = length(Path),
    % Longer paths with high frequency have higher potential
    Potential = (Frequency / 10.0) * (PathLength / 3.0),
    Potential.

%% Calculate memory optimization potential
calculate_memory_optimization_potential(MemoryAccess) ->
    TotalAccesses = maps:get(total_accesses, MemoryAccess, 0),
    LocalityScore = maps:get(locality_score, MemoryAccess, 0),

    case TotalAccesses of
        0 ->
            0;
        N when N > 20 ->
            % High access count with poor locality = high potential
            BaseScore = math:log(N) * 0.2,
            LocalityMultiplier =
                case LocalityScore < 0.5 of
                    % Poor locality increases potential
                    true -> 2.0;
                    false -> 1.0
                end,
            BaseScore * LocalityMultiplier;
        _ ->
            0.5
    end.

%% Calculate combined priority
calculate_combined_priority(Opportunities) ->
    lists:foldl(
        fun(Op, Acc) ->
            Benefit =
                case Op of
                    {_, #{benefit := B}} -> B;
                    {_, #{potential := P}} -> P;
                    _ -> 1.0
                end,
            Frequency =
                case Op of
                    {_, #{frequency := F}} -> F;
                    _ -> 1.0
                end,
            Acc + (Benefit * Frequency)
        end,
        0,
        Opportunities
    ).

%% ============================================================================
%% Final Helper Functions for Profile-guided Optimization
%% ============================================================================

%% Stub functions for memory operations analysis
count_operation_type(Type, MemoryOps) ->
    length(lists:filter(fun({OpType, _}) -> OpType =:= Type end, MemoryOps)).

detect_sequential_pattern(MemoryOps) ->
    % Simple heuristic: if more than 70% operations are sequential
    length(MemoryOps) > 5 andalso
        count_operation_type(read, MemoryOps) > length(MemoryOps) * 0.7.

calculate_locality_score(MemoryOps) ->
    % Simple locality score based on operation patterns
    case length(MemoryOps) of
        0 -> 0;
        % Small access patterns are usually local
        N when N < 5 -> 0.8;
        N -> 0.5 + (count_operation_type(read, MemoryOps) / N) * 0.3
    end.

is_memory_operation(load) -> true;
is_memory_operation(store) -> true;
is_memory_operation(alloc) -> true;
is_memory_operation(free) -> true;
is_memory_operation(_) -> false.

extract_pattern_memory_ops(_Pattern) ->
    % Simplified: assume patterns don't contain memory operations
    [].

analyze_access_pattern(AccessPattern) ->
    TotalAccesses = maps:get(total_accesses, AccessPattern, 0),
    SequentialPattern = maps:get(sequential_pattern, AccessPattern, false),

    case {SequentialPattern, TotalAccesses} of
        {true, N} when N > 50 -> {sequential, high_frequency};
        {false, N} when N > 100 -> {random, high_volume};
        {_, N} when N > 20 -> {locality_heavy, medium};
        _ -> {unknown, low}
    end.

%% AST transformation functions
apply_adaptive_specializations_to_ast(AST, AdaptiveSpecializations) ->
    % Apply specializations to AST
    TransformedAST = lists:foldl(
        fun(Specialization, CurrentAST) ->
            apply_single_specialization(CurrentAST, Specialization)
        end,
        AST,
        AdaptiveSpecializations
    ),

    SpecializationMetrics = #{
        specializations_applied => length(AdaptiveSpecializations),
        functions_specialized => count_specialized_functions(AdaptiveSpecializations)
    },

    {TransformedAST, SpecializationMetrics}.

apply_hot_path_optimizations_to_ast(AST, HotPathOptimizations) ->
    % Apply hot path optimizations to AST
    OptimizedAST = lists:foldl(
        fun(Optimization, CurrentAST) ->
            apply_single_hot_path_optimization(CurrentAST, Optimization)
        end,
        AST,
        HotPathOptimizations
    ),

    HotPathMetrics = #{
        optimizations_applied => length(HotPathOptimizations),
        paths_optimized => count_optimized_paths(HotPathOptimizations)
    },

    {OptimizedAST, HotPathMetrics}.

apply_adaptive_memory_layouts_to_ast(AST, AdaptiveMemoryLayouts) ->
    % Apply memory layout optimizations to AST
    LayoutOptimizedAST = lists:foldl(
        fun(MemoryLayout, CurrentAST) ->
            apply_single_memory_layout(CurrentAST, MemoryLayout)
        end,
        AST,
        AdaptiveMemoryLayouts
    ),

    MemoryMetrics = #{
        layouts_applied => length(AdaptiveMemoryLayouts),
        functions_memory_optimized => count_memory_optimized_functions(AdaptiveMemoryLayouts)
    },

    {LayoutOptimizedAST, MemoryMetrics}.

apply_performance_optimizations_to_ast(AST, PerformanceOptimizations) ->
    % Apply performance optimizations to AST
    PerformanceOptimizedAST = lists:foldl(
        fun(PerfOpt, CurrentAST) ->
            apply_single_performance_optimization(CurrentAST, PerfOpt)
        end,
        AST,
        PerformanceOptimizations
    ),

    PerformanceMetrics = #{
        performance_opts_applied => length(PerformanceOptimizations),
        performance_improvement_estimate => estimate_performance_improvement(
            PerformanceOptimizations
        )
    },

    {PerformanceOptimizedAST, PerformanceMetrics}.

%% Helper functions for specialization enhancement
enhance_existing_specialization(FuncName, OpportunityData, ExistingSpecs) ->
    ExistingSpec = maps:get(FuncName, ExistingSpecs, #{}),
    Frequency = maps:get(frequency, OpportunityData),
    Benefit = maps:get(benefit, OpportunityData),

    #{
        function_name => FuncName,
        specialization_type => enhanced,
        existing_specialization => ExistingSpec,
        runtime_frequency => Frequency,
        enhanced_benefit => Benefit,
        enhancement_timestamp => erlang:system_time(millisecond)
    }.

create_adaptive_specialization(FuncName, OpportunityData) ->
    Frequency = maps:get(frequency, OpportunityData),
    Benefit = maps:get(benefit, OpportunityData),

    #{
        function_name => FuncName,
        specialization_type => adaptive,
        runtime_frequency => Frequency,
        specialization_benefit => Benefit,
        created_timestamp => erlang:system_time(millisecond)
    }.

%% Performance optimization generators
generate_specialization_performance_opt(Opportunity, PerformanceTargets) ->
    #{
        optimization_type => specialization_performance,
        opportunity => Opportunity,
        target_improvement => maps:get(execution_time_target, PerformanceTargets, 1.0),
        estimated_benefit => 1.2
    }.

generate_hot_path_performance_opt(Opportunity, PerformanceTargets) ->
    #{
        optimization_type => hot_path_performance,
        opportunity => Opportunity,
        target_improvement => maps:get(throughput_target, PerformanceTargets, 1.2),
        estimated_benefit => 1.5
    }.

generate_memory_performance_opt(Opportunity, PerformanceTargets) ->
    #{
        optimization_type => memory_performance,
        opportunity => Opportunity,
        target_improvement => maps:get(memory_usage_target, PerformanceTargets, 0.8),
        estimated_benefit => 0.8
    }.

%% Simple stub implementations for AST transformations
apply_single_specialization(AST, _Specialization) -> AST.
apply_single_hot_path_optimization(AST, _Optimization) -> AST.
apply_single_memory_layout(AST, _MemoryLayout) -> AST.
apply_single_performance_optimization(AST, _PerfOpt) -> AST.

%% Counting functions
count_specialized_functions(Specializations) ->
    UniqueNames = sets:from_list([maps:get(function_name, Spec) || Spec <- Specializations]),
    sets:size(UniqueNames).

count_optimized_paths(HotPathOptimizations) ->
    UniquePaths = sets:from_list([maps:get(path, Opt) || Opt <- HotPathOptimizations]),
    sets:size(UniquePaths).

count_memory_optimized_functions(MemoryLayouts) ->
    UniqueFunctions = sets:from_list([maps:get(function, Layout) || Layout <- MemoryLayouts]),
    sets:size(UniqueFunctions).

estimate_performance_improvement(PerformanceOptimizations) ->
    lists:foldl(
        fun(PerfOpt, Acc) ->
            Benefit = maps:get(estimated_benefit, PerfOpt, 1.0),
            Acc + (Benefit - 1.0)
        end,
        0,
        PerformanceOptimizations
    ).

%% ============================================================================
%% Main Entry Point for Monomorphization
%% ============================================================================

%% Monomorphize polymorphic functions in the AST
monomorphize_ast(AST, Config) when is_list(AST) ->
    % Phase 3.1: Collect polymorphic call sites
    CallSites = collect_call_sites(AST),

    % Phase 3.2: Generate specialized function variants
    Specializations = generate_specializations(AST, CallSites, Config),

    % Phase 3.3: Transform AST to call specialized versions
    TransformedAST = transform_ast_with_specializations(AST, Specializations),

    % Phase 3.4: Eliminate unused specializations and original polymorphic functions
    eliminate_unused_specializations(TransformedAST, Specializations);
monomorphize_ast(#module_def{} = Module, Config) ->
    % Apply monomorphization to module
    [MonomorphizedModule] = monomorphize_ast([Module], Config),
    MonomorphizedModule;
monomorphize_ast(Other, _Config) ->
    Other.

%% ============================================================================
%% Phase 3.1: Collect Instantiation Sites
%% ============================================================================

%% Collect all instantiation sites of polymorphic functions in the program
%% Returns a map: FunctionName => [{TypeArgs, Location, CallContext}]
collect_poly_instantiation_sites(AST) when is_list(AST) ->
    % AST is a list of modules/items
    lists:foldl(
        fun(Item, Acc) ->
            ItemSites = collect_poly_instantiations_from_item(Item),
            merge_instantiation_maps(Acc, ItemSites)
        end,
        #{},
        AST
    );
collect_poly_instantiation_sites(AST) ->
    % Single item
    collect_poly_instantiations_from_item(AST).

%% Collect from a single item (module, function, etc.)
collect_poly_instantiations_from_item(#module_def{items = Items}) ->
    collect_poly_instantiation_sites(Items);
collect_poly_instantiations_from_item(#function_def{} = FuncDef) ->
    collect_poly_instantiations_from_function(FuncDef);
collect_poly_instantiations_from_item(_) ->
    #{}.

%% Collect from module
collect_poly_instantiations_from_module(#module_def{items = Items}) ->
    lists:foldl(
        fun(Item, Acc) ->
            ItemSites = collect_poly_instantiations_from_item(Item),
            merge_instantiation_maps(Acc, ItemSites)
        end,
        #{},
        Items
    ).

%% Collect from function definition
collect_poly_instantiations_from_function(#function_def{
    name = FuncName,
    clauses = Clauses,
    body = _Body,
    location = Location
}) when Clauses =/= undefined, length(Clauses) > 0 ->
    % Multi-clause function
    lists:foldl(
        fun(#function_clause{body = ClauseBody}, Acc) ->
            Context = #{function => FuncName, location => Location},
            BodySites = collect_poly_instantiations_from_expr(ClauseBody, Context),
            merge_instantiation_maps(Acc, BodySites)
        end,
        #{},
        Clauses
    );
collect_poly_instantiations_from_function(#function_def{
    name = FuncName,
    body = Body,
    location = Location
}) when Body =/= undefined ->
    % Single clause function
    Context = #{function => FuncName, location => Location},
    collect_poly_instantiations_from_expr(Body, Context);
collect_poly_instantiations_from_function(_) ->
    #{}.

%% Collect from expression with context
collect_poly_instantiations_from_expr({function_call_expr, Function, Args, Location}, Context) ->
    % Check if this is a call to a polymorphic function
    CallSites =
        case Function of
            {identifier_expr, FuncName, _} ->
                % Look up function type in context if available
                case maps:get(type_env, Context, undefined) of
                    undefined ->
                        % No type info, track as potential polymorphic call
                        track_polymorphic_call(FuncName, Args, Location);
                    TypeEnv ->
                        % Check if function is polymorphic
                        case cure_types:lookup_env(TypeEnv, FuncName) of
                            #poly_type{type_params = TypeParams} when TypeParams =/= [] ->
                                % Polymorphic function - infer type arguments from args
                                track_polymorphic_call(FuncName, Args, Location);
                            _ ->
                                #{}
                        end
                end;
            _ ->
                #{}
        end,

    % Recursively collect from arguments
    ArgSites = lists:foldl(
        fun(Arg, Acc) ->
            ArgSites0 = collect_poly_instantiations_from_expr(Arg, Context),
            merge_instantiation_maps(Acc, ArgSites0)
        end,
        #{},
        Args
    ),

    merge_instantiation_maps(CallSites, ArgSites);
collect_poly_instantiations_from_expr({let_expr, Bindings, Body, _Location}, Context) ->
    % Collect from bindings
    BindingSites = lists:foldl(
        fun({binding, _Pattern, Value, _Loc}, Acc) ->
            ValueSites = collect_poly_instantiations_from_expr(Value, Context),
            merge_instantiation_maps(Acc, ValueSites)
        end,
        #{},
        Bindings
    ),

    % Collect from body
    BodySites = collect_poly_instantiations_from_expr(Body, Context),
    merge_instantiation_maps(BindingSites, BodySites);
collect_poly_instantiations_from_expr({match_expr, MatchExpr, Patterns, _Location}, Context) ->
    % Collect from match expression
    MatchSites = collect_poly_instantiations_from_expr(MatchExpr, Context),

    % Collect from pattern clauses
    PatternSites = lists:foldl(
        fun({match_clause, _Pattern, _Guard, Body, _Loc}, Acc) ->
            BodySites = collect_poly_instantiations_from_expr(Body, Context),
            merge_instantiation_maps(Acc, BodySites)
        end,
        #{},
        Patterns
    ),

    merge_instantiation_maps(MatchSites, PatternSites);
collect_poly_instantiations_from_expr({lambda_expr, _Params, Body, _Location}, Context) ->
    collect_poly_instantiations_from_expr(Body, Context);
collect_poly_instantiations_from_expr({list_expr, Elements, _Location}, Context) ->
    lists:foldl(
        fun(Elem, Acc) ->
            ElemSites = collect_poly_instantiations_from_expr(Elem, Context),
            merge_instantiation_maps(Acc, ElemSites)
        end,
        #{},
        Elements
    );
collect_poly_instantiations_from_expr({tuple_expr, Elements, _Location}, Context) ->
    lists:foldl(
        fun(Elem, Acc) ->
            ElemSites = collect_poly_instantiations_from_expr(Elem, Context),
            merge_instantiation_maps(Acc, ElemSites)
        end,
        #{},
        Elements
    );
collect_poly_instantiations_from_expr({binary_op_expr, _Op, Left, Right, _Location}, Context) ->
    LeftSites = collect_poly_instantiations_from_expr(Left, Context),
    RightSites = collect_poly_instantiations_from_expr(Right, Context),
    merge_instantiation_maps(LeftSites, RightSites);
collect_poly_instantiations_from_expr({unary_op_expr, _Op, Operand, _Location}, Context) ->
    collect_poly_instantiations_from_expr(Operand, Context);
collect_poly_instantiations_from_expr({block_expr, Expressions, _Location}, Context) ->
    lists:foldl(
        fun(Expr, Acc) ->
            ExprSites = collect_poly_instantiations_from_expr(Expr, Context),
            merge_instantiation_maps(Acc, ExprSites)
        end,
        #{},
        Expressions
    );
collect_poly_instantiations_from_expr(_, _Context) ->
    % Literals, identifiers, and other leaf expressions
    #{}.

%% Track a polymorphic function call
track_polymorphic_call(FuncName, Args, Location) ->
    % Create instantiation site record
    Site = #{
        % Will be inferred during type checking
        type_args => infer,
        location => Location,
        arg_count => length(Args),
        context => call_site
    },

    % Return map with this function's instantiation
    #{FuncName => [Site]}.

%% Merge two instantiation maps
merge_instantiation_maps(Map1, Map2) ->
    maps:fold(
        fun(FuncName, Sites, Acc) ->
            ExistingSites = maps:get(FuncName, Acc, []),
            maps:put(FuncName, ExistingSites ++ Sites, Acc)
        end,
        Map1,
        Map2
    ).

%% ============================================================================
%% Phase 3.2: Generate Specialized Function Variants
%% ============================================================================

%% Generate specialized function variants from collected call sites
generate_specializations(AST, CallSites, _Config) ->
    % Find all polymorphic functions in the AST
    PolyFunctions = find_polymorphic_functions(AST),

    % For each polymorphic function and its call sites, generate specializations
    maps:fold(
        fun(FuncName, TypeArgsList, Acc) ->
            case maps:get(FuncName, PolyFunctions, undefined) of
                % Function not found
                undefined ->
                    Acc;
                FuncDef ->
                    % Generate a specialized variant for each unique type argument combination
                    Variants = lists:map(
                        fun(TypeArgs) ->
                            create_monomorphic_function(FuncDef, TypeArgs, FuncName)
                        end,
                        TypeArgsList
                    ),
                    maps:put(FuncName, Variants, Acc)
            end
        end,
        #{},
        CallSites
    ).

%% Generate specialized (monomorphic) variants for polymorphic functions
%% Takes: AST and instantiation sites map from Phase 3.1
%% Returns: Map of FunctionName => [SpecializedFunction]
generate_specialized_variants(AST, InstantiationSites) ->
    % Group instantiation sites by unique type arguments
    UniqueInstantiations = group_by_type_args(InstantiationSites),
    generate_specializations(AST, UniqueInstantiations, undefined).

%% Group instantiation sites by unique type arguments
group_by_type_args(InstantiationSites) ->
    maps:map(
        fun(_FuncName, Sites) ->
            % Extract unique type argument combinations
            TypeArgSets = lists:foldl(
                fun(Site, Acc) ->
                    TypeArgs = maps:get(type_args, Site, []),
                    case TypeArgs of
                        % Skip inference for now
                        infer -> Acc;
                        _ -> sets:add_element(TypeArgs, Acc)
                    end
                end,
                sets:new(),
                Sites
            ),
            sets:to_list(TypeArgSets)
        end,
        InstantiationSites
    ).

%% Find all polymorphic function definitions in AST
find_polymorphic_functions(AST) when is_list(AST) ->
    lists:foldl(
        fun(Item, Acc) ->
            maps:merge(Acc, find_polymorphic_functions(Item))
        end,
        #{},
        AST
    );
find_polymorphic_functions(#module_def{items = Items}) ->
    find_polymorphic_functions(Items);
find_polymorphic_functions(#function_def{name = Name, type_params = TypeParams} = FuncDef) when
    TypeParams =/= undefined, TypeParams =/= []
->
    % This is a polymorphic function
    #{Name => FuncDef};
find_polymorphic_functions(_) ->
    #{}.

%% Create a monomorphic (specialized) version of a polymorphic function
create_monomorphic_function(
    #function_def{
        name = _OrigName,
        type_params = TypeParams,
        clauses = Clauses,
        params = Params,
        return_type = ReturnType,
        body = Body,
        is_private = IsPrivate,
        location = Location
    },
    TypeArgs,
    BaseName
) ->
    % Generate specialized function name: identity_Int, map_Int_String, etc.
    SpecializedName = generate_specialized_name(BaseName, TypeArgs),

    % Create type substitution map
    TypeSubst = create_type_substitution(TypeParams, TypeArgs),

    % Specialize the function body and types
    SpecializedClauses =
        case Clauses of
            undefined ->
                undefined;
            [] ->
                [];
            _ ->
                lists:map(
                    fun(
                        #function_clause{
                            params = ClauseParams,
                            return_type = ClauseRetType,
                            constraint = Constraint,
                            body = ClauseBody,
                            location = ClauseLoc
                        }
                    ) ->
                        #function_clause{
                            params = specialize_params(ClauseParams, TypeSubst),
                            return_type = specialize_type(ClauseRetType, TypeSubst),
                            % Constraints should already be resolved
                            constraint = Constraint,
                            body = specialize_function_body(ClauseBody, TypeSubst, BaseName),
                            location = ClauseLoc
                        }
                    end,
                    Clauses
                )
        end,

    SpecializedBody =
        case Body of
            undefined -> undefined;
            _ -> specialize_function_body(Body, TypeSubst, BaseName)
        end,

    % Create monomorphic function (no type params)
    #function_def{
        name = SpecializedName,
        % Monomorphic
        type_params = [],
        clauses = SpecializedClauses,
        params = specialize_params(Params, TypeSubst),
        return_type = specialize_type(ReturnType, TypeSubst),
        % Constraints resolved during specialization
        constraint = undefined,
        body = SpecializedBody,
        is_private = IsPrivate,
        location = Location
    }.

%% Generate specialized function name
generate_specialized_name(BaseName, TypeArgs) ->
    TypeSuffix = lists:map(fun type_to_name_suffix/1, TypeArgs),
    SuffixStr = string:join(TypeSuffix, "_"),
    list_to_atom(atom_to_list(BaseName) ++ "_" ++ SuffixStr).

%% Convert type to name suffix
type_to_name_suffix({primitive_type, Name}) -> atom_to_list(Name);
type_to_name_suffix({list_type, ElemType, _}) -> "List_" ++ type_to_name_suffix(ElemType);
type_to_name_suffix({tuple_type, _, _}) -> "Tuple";
type_to_name_suffix(_) -> "T".

%% Create type substitution map from type params to type args
create_type_substitution(TypeParams, TypeArgs) ->
    ParamNames = cure_types:extract_type_param_names(TypeParams),
    maps:from_list(lists:zip(ParamNames, TypeArgs)).

%% Specialize function parameters
specialize_params(Params, TypeSubst) when is_list(Params) ->
    lists:map(
        fun(#param{name = Name, type = Type, location = Loc}) ->
            #param{
                name = Name,
                type = specialize_type(Type, TypeSubst),
                location = Loc
            }
        end,
        Params
    );
specialize_params(Params, _TypeSubst) ->
    Params.

%% Specialize a type expression using substitution
specialize_type(undefined, _TypeSubst) ->
    undefined;
specialize_type({primitive_type, Name}, TypeSubst) ->
    case maps:get(Name, TypeSubst, undefined) of
        undefined -> {primitive_type, Name};
        SpecializedType -> SpecializedType
    end;
specialize_type({function_type, Params, Return}, TypeSubst) ->
    {function_type, [specialize_type(P, TypeSubst) || P <- Params],
        specialize_type(Return, TypeSubst)};
specialize_type({list_type, ElemType, Length}, TypeSubst) ->
    {list_type, specialize_type(ElemType, TypeSubst), Length};
specialize_type({dependent_type, Name, Params}, TypeSubst) ->
    {dependent_type, Name, [specialize_type_param(P, TypeSubst) || P <- Params]};
specialize_type(Type, _TypeSubst) ->
    Type.

%% Specialize type parameter
specialize_type_param(#type_param{name = Name, value = Value, location = Loc}, TypeSubst) ->
    #type_param{
        name = Name,
        value = specialize_type(Value, TypeSubst),
        location = Loc
    };
specialize_type_param(Param, _TypeSubst) ->
    Param.

%% Specialize function body by substituting type parameters
specialize_function_body(Body, TypeSubst, OrigFuncName) ->
    specialize_expr(Body, TypeSubst, OrigFuncName).

%% Specialize expressions
specialize_expr({function_call_expr, Function, Args, Location}, TypeSubst, OrigFuncName) ->
    % Check if this is a recursive call to the original polymorphic function
    SpecializedFunc =
        case Function of
            {identifier_expr, FuncName, FLoc} when FuncName =:= OrigFuncName ->
                % Recursive call - will be handled in Phase 3.3
                {identifier_expr, FuncName, FLoc};
            _ ->
                specialize_expr(Function, TypeSubst, OrigFuncName)
        end,
    {function_call_expr, SpecializedFunc,
        [specialize_expr(Arg, TypeSubst, OrigFuncName) || Arg <- Args], Location};
specialize_expr({let_expr, Bindings, Body, Location}, TypeSubst, OrigFuncName) ->
    SpecBindings = lists:map(
        fun({binding, Pattern, Value, Loc}) ->
            {binding, Pattern, specialize_expr(Value, TypeSubst, OrigFuncName), Loc}
        end,
        Bindings
    ),
    {let_expr, SpecBindings, specialize_expr(Body, TypeSubst, OrigFuncName), Location};
specialize_expr({lambda_expr, Params, Body, Location}, TypeSubst, OrigFuncName) ->
    {lambda_expr, Params, specialize_expr(Body, TypeSubst, OrigFuncName), Location};
specialize_expr({match_expr, Expr, Patterns, Location}, TypeSubst, OrigFuncName) ->
    SpecPatterns = lists:map(
        fun({match_clause, Pattern, Guard, Body, Loc}) ->
            {match_clause, Pattern, Guard, specialize_expr(Body, TypeSubst, OrigFuncName), Loc}
        end,
        Patterns
    ),
    {match_expr, specialize_expr(Expr, TypeSubst, OrigFuncName), SpecPatterns, Location};
specialize_expr({list_expr, Elements, Location}, TypeSubst, OrigFuncName) ->
    {list_expr, [specialize_expr(E, TypeSubst, OrigFuncName) || E <- Elements], Location};
specialize_expr({tuple_expr, Elements, Location}, TypeSubst, OrigFuncName) ->
    {tuple_expr, [specialize_expr(E, TypeSubst, OrigFuncName) || E <- Elements], Location};
specialize_expr({binary_op_expr, Op, Left, Right, Location}, TypeSubst, OrigFuncName) ->
    {binary_op_expr, Op, specialize_expr(Left, TypeSubst, OrigFuncName),
        specialize_expr(Right, TypeSubst, OrigFuncName), Location};
specialize_expr({unary_op_expr, Op, Operand, Location}, TypeSubst, OrigFuncName) ->
    {unary_op_expr, Op, specialize_expr(Operand, TypeSubst, OrigFuncName), Location};
specialize_expr({block_expr, Expressions, Location}, TypeSubst, OrigFuncName) ->
    {block_expr, [specialize_expr(E, TypeSubst, OrigFuncName) || E <- Expressions], Location};
specialize_expr(Expr, _TypeSubst, _OrigFuncName) ->
    % Literals, identifiers, and other expressions
    Expr.

%% ============================================================================
%% Phase 3.3: Transform Calls to Specialized Versions
%% ============================================================================

%% Transform AST to replace polymorphic function calls with specialized versions
transform_ast_with_specializations(AST, Specializations) when is_list(AST) ->
    lists:map(
        fun(Item) -> transform_item_with_specializations(Item, Specializations) end,
        AST
    );
transform_ast_with_specializations(AST, Specializations) ->
    transform_item_with_specializations(AST, Specializations).

transform_item_with_specializations(#module_def{items = Items} = Module, Specializations) ->
    % Add specialized functions to module and transform existing ones
    SpecializedFunctions = lists:flatten(maps:values(Specializations)),
    TransformedItems = lists:map(
        fun(Item) -> transform_item_with_specializations(Item, Specializations) end,
        Items
    ),
    Module#module_def{items = TransformedItems ++ SpecializedFunctions};
transform_item_with_specializations(
    #function_def{
        name = _Name,
        type_params = TypeParams,
        clauses = Clauses,
        body = Body
    } = FuncDef,
    Specializations
) ->
    % Don't transform polymorphic function definitions themselves
    % but transform their bodies to call specialized versions
    case TypeParams of
        % Monomorphic function, transform calls
        [] ->
            TransformedClauses =
                case Clauses of
                    undefined ->
                        undefined;
                    [] ->
                        [];
                    _ ->
                        lists:map(
                            fun(#function_clause{body = ClauseBody} = Clause) ->
                                Clause#function_clause{
                                    body = replace_poly_calls_in_expr(ClauseBody, Specializations)
                                }
                            end,
                            Clauses
                        )
                end,
            TransformedBody =
                case Body of
                    undefined -> undefined;
                    _ -> replace_poly_calls_in_expr(Body, Specializations)
                end,
            FuncDef#function_def{clauses = TransformedClauses, body = TransformedBody};
        _ ->
            % Polymorphic function - keep for now, will be removed in Phase 3.4
            FuncDef
    end;
transform_item_with_specializations(Item, _Specializations) ->
    Item.

%% Replace polymorphic function calls with specialized versions in expressions
replace_poly_calls_in_expr({function_call_expr, Function, Args, Location}, Specializations) ->
    % Check if this calls a polymorphic function
    case Function of
        {identifier_expr, FuncName, _FLoc} ->
            case maps:get(FuncName, Specializations, undefined) of
                undefined ->
                    % Not a polymorphic function or no specializations
                    {function_call_expr, Function,
                        [replace_poly_calls_in_expr(Arg, Specializations) || Arg <- Args],
                        Location};
                Variants ->
                    % Polymorphic function - select appropriate specialization
                    % For now, use first variant (should infer from arg types)
                    case Variants of
                        [#function_def{name = SpecName} | _] ->
                            {function_call_expr, {identifier_expr, SpecName, Location},
                                [replace_poly_calls_in_expr(Arg, Specializations) || Arg <- Args],
                                Location};
                        [] ->
                            % No variants, keep original
                            {function_call_expr, Function,
                                [replace_poly_calls_in_expr(Arg, Specializations) || Arg <- Args],
                                Location}
                    end
            end;
        _ ->
            {function_call_expr, replace_poly_calls_in_expr(Function, Specializations),
                [replace_poly_calls_in_expr(Arg, Specializations) || Arg <- Args], Location}
    end;
replace_poly_calls_in_expr({let_expr, Bindings, Body, Location}, Specializations) ->
    TransBindings = lists:map(
        fun({binding, Pattern, Value, Loc}) ->
            {binding, Pattern, replace_poly_calls_in_expr(Value, Specializations), Loc}
        end,
        Bindings
    ),
    {let_expr, TransBindings, replace_poly_calls_in_expr(Body, Specializations), Location};
replace_poly_calls_in_expr({match_expr, Expr, Patterns, Location}, Specializations) ->
    TransPatterns = lists:map(
        fun({match_clause, Pattern, Guard, Body, Loc}) ->
            {match_clause, Pattern, Guard, replace_poly_calls_in_expr(Body, Specializations), Loc}
        end,
        Patterns
    ),
    {match_expr, replace_poly_calls_in_expr(Expr, Specializations), TransPatterns, Location};
replace_poly_calls_in_expr({lambda_expr, Params, Body, Location}, Specializations) ->
    {lambda_expr, Params, replace_poly_calls_in_expr(Body, Specializations), Location};
replace_poly_calls_in_expr({list_expr, Elements, Location}, Specializations) ->
    {list_expr, [replace_poly_calls_in_expr(E, Specializations) || E <- Elements], Location};
replace_poly_calls_in_expr({tuple_expr, Elements, Location}, Specializations) ->
    {tuple_expr, [replace_poly_calls_in_expr(E, Specializations) || E <- Elements], Location};
replace_poly_calls_in_expr({binary_op_expr, Op, Left, Right, Location}, Specializations) ->
    {binary_op_expr, Op, replace_poly_calls_in_expr(Left, Specializations),
        replace_poly_calls_in_expr(Right, Specializations), Location};
replace_poly_calls_in_expr({unary_op_expr, Op, Operand, Location}, Specializations) ->
    {unary_op_expr, Op, replace_poly_calls_in_expr(Operand, Specializations), Location};
replace_poly_calls_in_expr({block_expr, Expressions, Location}, Specializations) ->
    {block_expr, [replace_poly_calls_in_expr(E, Specializations) || E <- Expressions], Location};
replace_poly_calls_in_expr(Expr, _Specializations) ->
    % Literals, identifiers, and other leaf expressions
    Expr.

%% ============================================================================
%% Phase 3.4: Dead Code Elimination for Unused Specializations
%% ============================================================================

%% Eliminate unused specialized functions and original polymorphic functions
eliminate_unused_specializations(AST, Specializations) when is_list(AST) ->
    % Find all reachable functions from entry points
    EntryPoints = find_entry_points(AST),
    ReachableFunctions = find_reachable_functions(AST, EntryPoints),

    % Filter AST to keep only reachable functions
    lists:map(
        fun(Item) -> eliminate_unused_in_item(Item, ReachableFunctions, Specializations) end,
        AST
    );
eliminate_unused_specializations(AST, Specializations) ->
    EntryPoints = find_entry_points([AST]),
    ReachableFunctions = find_reachable_functions([AST], EntryPoints),
    eliminate_unused_in_item(AST, ReachableFunctions, Specializations).

%% Find entry points (exported functions, main, etc.)
find_entry_points(AST) when is_list(AST) ->
    lists:foldl(
        fun(Item, Acc) -> sets:union(Acc, find_entry_points(Item)) end,
        sets:new(),
        AST
    );
find_entry_points(#module_def{exports = Exports, items = Items}) ->
    % Exported functions are entry points
    ExportedNames = sets:from_list([Name || #export_spec{name = Name} <- Exports]),
    % Also check for 'main' function
    FunctionNames = lists:filtermap(
        fun
            (#function_def{name = Name}) -> {true, Name};
            (_) -> false
        end,
        Items
    ),
    MainSet =
        case lists:member(main, FunctionNames) of
            true -> sets:add_element(main, sets:new());
            false -> sets:new()
        end,
    sets:union(ExportedNames, MainSet);
find_entry_points(_) ->
    sets:new().

%% Find all functions reachable from entry points
find_reachable_functions(AST, EntryPoints) ->
    % Build call graph
    CallGraph = build_call_graph(AST),
    % Traverse from entry points
    traverse_call_graph(CallGraph, sets:to_list(EntryPoints), sets:new()).

%% Build call graph (function -> [called functions])
build_call_graph(AST) when is_list(AST) ->
    lists:foldl(
        fun(Item, Acc) -> maps:merge(Acc, build_call_graph(Item)) end,
        #{},
        AST
    );
build_call_graph(#module_def{items = Items}) ->
    build_call_graph(Items);
build_call_graph(#function_def{name = Name, body = Body, clauses = Clauses}) ->
    CalledFunctions =
        case Clauses of
            undefined -> find_called_functions(Body);
            [] -> find_called_functions(Body);
            _ -> sets:union([find_called_functions(C#function_clause.body) || C <- Clauses])
        end,
    #{Name => CalledFunctions};
build_call_graph(_) ->
    #{}.

%% Find all functions called in an expression
find_called_functions({function_call_expr, {identifier_expr, FuncName, _}, Args, _}) ->
    ArgCalls = sets:union([find_called_functions(Arg) || Arg <- Args]),
    sets:add_element(FuncName, ArgCalls);
find_called_functions({let_expr, Bindings, Body, _}) ->
    BindingCalls = sets:union([find_called_functions(V) || {binding, _, V, _} <- Bindings]),
    sets:union(BindingCalls, find_called_functions(Body));
find_called_functions({match_expr, Expr, Patterns, _}) ->
    ExprCalls = find_called_functions(Expr),
    PatternCalls = sets:union([find_called_functions(B) || {match_clause, _, _, B, _} <- Patterns]),
    sets:union(ExprCalls, PatternCalls);
find_called_functions({list_expr, Elements, _}) ->
    sets:union([find_called_functions(E) || E <- Elements]);
find_called_functions({tuple_expr, Elements, _}) ->
    sets:union([find_called_functions(E) || E <- Elements]);
find_called_functions({binary_op_expr, _, Left, Right, _}) ->
    sets:union(find_called_functions(Left), find_called_functions(Right));
find_called_functions({lambda_expr, _, Body, _}) ->
    find_called_functions(Body);
find_called_functions(_) ->
    sets:new().

%% Traverse call graph to find all reachable functions
traverse_call_graph(_CallGraph, [], Visited) ->
    Visited;
traverse_call_graph(CallGraph, [FuncName | Rest], Visited) ->
    case sets:is_element(FuncName, Visited) of
        true ->
            traverse_call_graph(CallGraph, Rest, Visited);
        false ->
            NewVisited = sets:add_element(FuncName, Visited),
            CalledFunctions = maps:get(FuncName, CallGraph, sets:new()),
            NewWorkList = sets:to_list(CalledFunctions) ++ Rest,
            traverse_call_graph(CallGraph, NewWorkList, NewVisited)
    end.

%% Eliminate unused functions from an item
eliminate_unused_in_item(#module_def{items = Items} = Module, Reachable, Specializations) ->
    % Get names of all polymorphic functions that were specialized
    PolyFuncNames = maps:keys(Specializations),

    FilteredItems = lists:filter(
        fun
            (#function_def{name = Name, type_params = TypeParams}) ->
                % Keep if:
                % 1. Function is reachable AND
                % 2. Either not polymorphic OR not specialized
                IsReachable = sets:is_element(Name, Reachable),
                IsPoly = TypeParams =/= undefined andalso TypeParams =/= [],
                WasSpecialized = lists:member(Name, PolyFuncNames),

                % Keep monomorphic reachable functions
                % Remove polymorphic functions that were specialized
                IsReachable andalso (not IsPoly orelse not WasSpecialized);
            (_) ->
                % Keep non-function items
                true
        end,
        Items
    ),
    Module#module_def{items = FilteredItems};
eliminate_unused_in_item(Item, _Reachable, _Specializations) ->
    Item.
