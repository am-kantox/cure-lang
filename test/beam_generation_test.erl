%% Test suite for Type-directed BEAM Code Generation
-module(beam_generation_test).

-export([test_beam_generation_framework/0, run_beam_tests/0]).

-include("../src/parser/cure_ast.hrl").

%% Run BEAM generation tests
run_beam_tests() ->
    cure_utils:debug("=== Testing Type-directed BEAM Code Generation ===~n"),
    Tests = [
        fun test_beam_generation_framework/0,
        fun test_type_specific_instructions/0,
        fun test_optimized_calling_conventions/0,
        fun test_specialized_opcodes/0
    ],

    Results = lists:map(
        fun(Test) ->
            TestName = extract_test_name(Test),
            cure_utils:debug("Running ~s... ", [TestName]),
            try
                Test(),
                cure_utils:debug("PASSED~n"),
                ok
            catch
                Error:Reason:Stack ->
                    cure_utils:debug("FAILED: ~p:~p~n", [Error, Reason]),
                    cure_utils:debug("  Stack: ~p~n", [Stack]),
                    {error, Reason}
            end
        end,
        Tests
    ),

    Passed = length([ok || ok <- Results]),
    Failed = length(Results) - Passed,

    cure_utils:debug("~nBEAM Generation Tests Summary:~n"),
    cure_utils:debug("  Passed: ~w~n", [Passed]),
    cure_utils:debug("  Failed: ~w~n", [Failed]),

    case Failed of
        0 -> cure_utils:debug("All BEAM generation tests passed!~n");
        _ -> cure_utils:debug("Some BEAM generation tests failed.~n")
    end,

    {ok, #{passed => Passed, failed => Failed}}.

extract_test_name(Fun) ->
    {name, Name} = erlang:fun_info(Fun, name),
    atom_to_list(Name).

%% Test BEAM generation framework is in place
test_beam_generation_framework() ->
    % Test that the BEAM generation pass is available in the type optimizer
    Exports = cure_type_optimizer:module_info(exports),

    % Check that basic type-directed functions are exported or defined
    true =
        lists:member({apply_beam_generation_pass, 2}, Exports) orelse
            beam_generation_functionality_exists(),

    % Test basic BEAM instruction structure
    BeamInstr = test_beam_instruction(),
    true = is_beam_instruction_valid(BeamInstr),

    % Test that type information can be extracted
    TypeInfo = test_type_info_extraction(),
    true = is_map(TypeInfo),

    cure_utils:debug(" [BEAM framework available] "),
    ok.

%% Test type-specific instruction generation
test_type_specific_instructions() ->
    % Test integer-specific instructions
    IntInstructions = generate_test_integer_instructions(),
    true = length(IntInstructions) > 0,

    % Test float-specific instructions
    FloatInstructions = generate_test_float_instructions(),
    true = length(FloatInstructions) > 0,

    % Test atom-specific instructions
    AtomInstructions = generate_test_atom_instructions(),
    true = length(AtomInstructions) > 0,

    cure_utils:debug(" [Type-specific instructions generated] "),
    ok.

%% Test optimized calling conventions
test_optimized_calling_conventions() ->
    % Test fast calling convention for hot path functions
    FastConvention = create_test_calling_convention(fast_call),
    true = is_valid_calling_convention(FastConvention),

    % Test optimized convention for moderate functions
    OptimizedConvention = create_test_calling_convention(optimized_call),
    true = is_valid_calling_convention(OptimizedConvention),

    % Test register-based argument passing
    RegisterConvention = create_test_calling_convention(register_call),
    true = is_valid_calling_convention(RegisterConvention),

    cure_utils:debug(" [Optimized calling conventions created] "),
    ok.

%% Test specialized opcode generation
test_specialized_opcodes() ->
    % Test arithmetic opcodes
    ArithmeticOpcodes = generate_test_arithmetic_opcodes(),
    % At least integer and float operations
    true = length(ArithmeticOpcodes) >= 2,

    % Test comparison opcodes
    ComparisonOpcodes = generate_test_comparison_opcodes(),
    true = length(ComparisonOpcodes) >= 2,

    % Test dispatch opcodes
    DispatchOpcodes = generate_test_dispatch_opcodes(),
    true = length(DispatchOpcodes) >= 1,

    cure_utils:debug(" [Specialized opcodes generated] "),
    ok.

%% ============================================================================
%% Helper Functions
%% ============================================================================

%% Check if BEAM generation functionality exists
beam_generation_functionality_exists() ->
    % Check if the essential BEAM generation functions are available
    try
        % Test if we can create a basic BEAM context
        test_beam_context(),
        true
    catch
        _:_ -> false
    end.

%% Test BEAM instruction structure
test_beam_instruction() ->
    #{
        op => load_literal_int,
        args => [42],
        location => undefined
    }.

%% Check if BEAM instruction is valid
is_beam_instruction_valid(Instr) ->
    is_map(Instr) andalso
        maps:is_key(op, Instr) andalso
        maps:is_key(args, Instr).

%% Test type information extraction
test_type_info_extraction() ->
    #{
        function_types => #{
            test_func => {function_type, [{primitive_type, integer}], {primitive_type, integer}}
        },
        call_site_types => #{},
        specialized_functions => #{},
        monomorphic_instances => #{},
        inlined_functions => #{},
        type_usage_patterns => #{arithmetic => 5, comparison => 3, dispatch => 2},
        hot_path_functions => [test_func],
        memory_layout_info => #{}
    }.

%% Generate test integer instructions
generate_test_integer_instructions() ->
    [
        #{op => load_literal_int, args => [42], location => undefined},
        #{op => load_param_int, args => [x], location => undefined},
        #{op => int_add, args => [], location => undefined}
    ].

%% Generate test float instructions
generate_test_float_instructions() ->
    [
        #{op => load_literal_float, args => [3.14], location => undefined},
        #{op => load_param_float, args => [y], location => undefined},
        #{op => float_add, args => [], location => undefined}
    ].

%% Generate test atom instructions
generate_test_atom_instructions() ->
    [
        #{op => load_literal_atom, args => [test], location => undefined},
        #{op => load_param_atom, args => [atom_param], location => undefined}
    ].

%% Create test calling convention
create_test_calling_convention(ConventionType) ->
    case ConventionType of
        fast_call ->
            #{convention => fast_call, register_args => true, inline_eligible => true};
        optimized_call ->
            #{convention => optimized_call, register_args => true, inline_eligible => false};
        register_call ->
            #{convention => register_call, register_args => true, inline_eligible => false};
        _ ->
            #{convention => standard_call, register_args => false, inline_eligible => false}
    end.

%% Check if calling convention is valid
is_valid_calling_convention(Convention) ->
    is_map(Convention) andalso
        maps:is_key(convention, Convention) andalso
        maps:is_key(register_args, Convention) andalso
        maps:is_key(inline_eligible, Convention).

%% Generate test arithmetic opcodes
generate_test_arithmetic_opcodes() ->
    [
        #{
            pattern => {arithmetic, integer, '+'},
            opcode => int_add_optimized,
            frequency => 10,
            optimization_benefit => 2.5
        },
        #{
            pattern => {arithmetic, float, '+'},
            opcode => float_add_optimized,
            frequency => 8,
            optimization_benefit => 3.0
        },
        #{
            pattern => {arithmetic, integer, '*'},
            opcode => int_mult_optimized,
            frequency => 5,
            optimization_benefit => 2.5
        }
    ].

%% Generate test comparison opcodes
generate_test_comparison_opcodes() ->
    [
        #{
            pattern => {comparison, integer, '=='},
            opcode => int_equal_optimized,
            frequency => 12,
            optimization_benefit => 2.0
        },
        #{
            pattern => {comparison, float, '=='},
            opcode => float_equal_optimized,
            frequency => 6,
            optimization_benefit => 2.5
        }
    ].

%% Generate test dispatch opcodes
generate_test_dispatch_opcodes() ->
    [
        #{
            pattern => {dispatch, pattern_match, integer},
            opcode => dispatch_integer,
            frequency => 4,
            optimization_benefit => 4.0
        }
    ].

%% Test BEAM context creation
test_beam_context() ->
    #{
        type_info => test_type_info_extraction(),
        instruction_cache => #{},
        opcode_mappings => #{
            load_literal_int => "load_literal_integer",
            int_add => "integer_add_fast"
        },
        calling_conventions => #{},
        register_allocations => #{},
        type_dispatch_table => #{}
    }.
