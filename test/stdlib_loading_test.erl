%% Standard Library Loading Unit Tests
%% Tests for cure_typechecker functions that dynamically load and parse .cure stdlib files
-module(stdlib_loading_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast_simple.hrl").

%% Type environment record definition (from cure_types.erl)
-record(type_env, {
    bindings :: #{atom() => term()},
    constraints :: [term()],
    parent :: term() | undefined
}).

%% Run all stdlib loading tests
run() ->
    io:format("Running Cure Standard Library Loading tests...~n"),
    test_load_stdlib_modules(),
    test_extract_module_functions(),
    test_add_std_function_types(),
    test_get_stdlib_function_type(),
    test_create_function_type_from_signature(),
    test_create_function_type_from_signature_records(),
    test_full_workflow(),
    test_error_handling(),
    io:format("All standard library loading tests passed!~n").

%% ============================================================================
%% Test 1: load_stdlib_modules/0 successfully loads and parses all .cure files
%% ============================================================================

test_load_stdlib_modules() ->
    io:format("Testing load_stdlib_modules/0...~n"),

    % Clean process dictionary to ensure fresh load
    erase(stdlib_functions),

    % Test loading stdlib modules
    StdlibFunctions = cure_typechecker:load_stdlib_modules(),

    % Verify result is a map
    ?assert(is_map(StdlibFunctions)),

    % Should not be empty (we have several stdlib modules)
    ?assert(map_size(StdlibFunctions) > 0),

    % Verify some expected functions are loaded
    % From Std.Core module
    ?assert(maps:is_key({'Std.Core', identity, 1}, StdlibFunctions)),
    ?assert(maps:is_key({'Std.Core', compose, 2}, StdlibFunctions)),
    ?assert(maps:is_key({'Std.Core', 'not', 1}, StdlibFunctions)),
    ?assert(maps:is_key({'Std.Core', 'and', 2}, StdlibFunctions)),
    ?assert(maps:is_key({'Std.Core', compare, 2}, StdlibFunctions)),

    % From Std.List module
    ?assert(maps:is_key({'Std.List', length, 1}, StdlibFunctions)),
    ?assert(maps:is_key({'Std.List', head, 2}, StdlibFunctions)),
    ?assert(maps:is_key({'Std.List', map, 2}, StdlibFunctions)),
    ?assert(maps:is_key({'Std.List', filter, 2}, StdlibFunctions)),

    % Verify function types are proper tuples
    {ok, IdentityType} = maps:find({'Std.Core', identity, 1}, StdlibFunctions),
    ?assertMatch({function_type, _, _}, IdentityType),

    {ok, ComposeType} = maps:find({'Std.Core', compose, 2}, StdlibFunctions),
    ?assertMatch({function_type, [_, _], _}, ComposeType),

    io:format("✓ load_stdlib_modules/0 test passed~n").

%% ============================================================================
%% Test 2: extract_module_functions/1 correctly extracts public function definitions
%% ============================================================================

test_extract_module_functions() ->
    io:format("Testing extract_module_functions/1...~n"),

    % Create sample module AST with various function definitions
    SampleAST = [
        {module_def, 'TestModule', [],
            [
                {export_spec, add, 2},
                {export_spec, multiply, 2}
            ],
            [
                % Public function
                {function_def, add,
                    [
                        {param, x, {primitive_type, 'Int'}, undefined},
                        {param, y, {primitive_type, 'Int'}, undefined}
                    ],
                    {primitive_type, 'Int'}, undefined,
                    {binary_op_expr, '+', {identifier_expr, x, undefined},
                        {identifier_expr, y, undefined}, undefined},
                    false, undefined},

                % Public function without return type
                {function_def, multiply,
                    [
                        {param, a, {primitive_type, 'Int'}, undefined},
                        {param, b, {primitive_type, 'Int'}, undefined}
                    ],
                    undefined, undefined,
                    {binary_op_expr, '*', {identifier_expr, a, undefined},
                        {identifier_expr, b, undefined}, undefined},
                    false, undefined},

                % Private function (should not be extracted)
                {function_def, helper,
                    [
                        {param, x, {primitive_type, 'Int'}, undefined}
                    ],
                    {primitive_type, 'Int'}, undefined, {identifier_expr, x, undefined}, true,
                    undefined}
            ],
            undefined}
    ],

    % Extract functions
    Functions = cure_typechecker:extract_module_functions(SampleAST),

    % Verify result is a map
    ?assert(is_map(Functions)),

    % Should contain public functions only
    ?assert(maps:is_key({'TestModule', add, 2}, Functions)),
    ?assert(maps:is_key({'TestModule', multiply, 2}, Functions)),

    % Should NOT contain private function
    ?assertNot(maps:is_key({'TestModule', helper, 1}, Functions)),

    % Verify function types
    {ok, AddType} = maps:find({'TestModule', add, 2}, Functions),
    ?assertMatch({function_type, [_, _], _}, AddType),

    {ok, MultiplyType} = maps:find({'TestModule', multiply, 2}, Functions),
    ?assertMatch({function_type, [_, _], _}, MultiplyType),

    % Test with empty AST
    EmptyFunctions = cure_typechecker:extract_module_functions([]),
    ?assertEqual(#{}, EmptyFunctions),

    io:format("✓ extract_module_functions/1 test passed~n").

%% ============================================================================
%% Test 3: add_std_function_types/1 populates environment correctly
%% ============================================================================

test_add_std_function_types() ->
    io:format("Testing add_std_function_types/1...~n"),

    % Create base environment
    Env = cure_typechecker:builtin_env(),

    % Clean process dictionary to force fresh load
    erase(stdlib_functions),

    % Add stdlib functions to environment
    EnvWithStd = cure_typechecker:add_std_function_types(Env),

    % Verify environment is still a proper environment record
    ?assert(is_record(EnvWithStd, type_env)),

    % Test that some stdlib functions are now available
    % Note: Functions are added with just their name, not module-qualified

    % From Std.Core
    IdentityType = cure_types:lookup_env(EnvWithStd, identity),
    ?assertNotEqual(undefined, IdentityType),
    ?assertMatch({function_type, _, _}, IdentityType),

    ComposeType = cure_types:lookup_env(EnvWithStd, compose),
    ?assertNotEqual(undefined, ComposeType),
    ?assertMatch({function_type, [_, _], _}, ComposeType),

    % From Std.List
    LengthType = cure_types:lookup_env(EnvWithStd, length),
    ?assertNotEqual(undefined, LengthType),
    ?assertMatch({function_type, _, _}, LengthType),

    % Functions that should remain undefined (not in stdlib)
    UndefinedFunc = cure_types:lookup_env(EnvWithStd, nonexistent_function),
    ?assertEqual(undefined, UndefinedFunc),

    % Test idempotency - calling again shouldn't break
    EnvWithStd2 = cure_typechecker:add_std_function_types(EnvWithStd),
    ?assert(is_record(EnvWithStd2, type_env)),

    io:format("✓ add_std_function_types/1 test passed~n").

%% ============================================================================
%% Test 4: get_stdlib_function_type/3 retrieves accurate types
%% ============================================================================

test_get_stdlib_function_type() ->
    io:format("Testing get_stdlib_function_type/3...~n"),

    % Clean process dictionary for fresh test
    erase(stdlib_functions),

    % Test valid stdlib function lookups

    % Std.Core functions
    ?assertMatch(
        {ok, {function_type, _, _}},
        cure_typechecker:get_stdlib_function_type('Std.Core', identity, 1)
    ),

    ?assertMatch(
        {ok, {function_type, [_, _], _}},
        cure_typechecker:get_stdlib_function_type('Std.Core', compose, 2)
    ),

    ?assertMatch(
        {ok, {function_type, [_], _}},
        cure_typechecker:get_stdlib_function_type('Std.Core', 'not', 1)
    ),

    ?assertMatch(
        {ok, {function_type, [_, _], _}},
        cure_typechecker:get_stdlib_function_type('Std.Core', 'and', 2)
    ),

    % Std.List functions
    ?assertMatch(
        {ok, {function_type, [_], _}},
        cure_typechecker:get_stdlib_function_type('Std.List', length, 1)
    ),

    ?assertMatch(
        {ok, {function_type, [_, _], _}},
        cure_typechecker:get_stdlib_function_type('Std.List', head, 2)
    ),

    % Test non-existent functions
    ?assertEqual(
        not_found,
        cure_typechecker:get_stdlib_function_type('Std.Core', nonexistent, 1)
    ),

    ?assertEqual(
        not_found,
        cure_typechecker:get_stdlib_function_type('NonexistentModule', func, 1)
    ),

    % Test wrong arity
    ?assertEqual(
        not_found,
        cure_typechecker:get_stdlib_function_type('Std.Core', identity, 2)
    ),

    % Test caching - second call should use cached result
    ?assertMatch(
        {ok, {function_type, _, _}},
        cure_typechecker:get_stdlib_function_type('Std.Core', identity, 1)
    ),

    io:format("✓ get_stdlib_function_type/3 test passed~n").

%% ============================================================================
%% Test 5: create_function_type_from_signature correctly constructs function types
%% ============================================================================

test_create_function_type_from_signature() ->
    io:format("Testing create_function_type_from_signature/2...~n"),

    % Test with defined return type
    Params1 = [
        {param, x, {primitive_type, 'Int'}, undefined},
        {param, y, {primitive_type, 'String'}, undefined}
    ],
    ReturnType1 = {primitive_type, 'Bool'},

    FuncType1 = cure_typechecker:create_function_type_from_signature(Params1, ReturnType1),
    ?assertMatch({function_type, [_, _], _}, FuncType1),

    {function_type, ParamTypes1, ActualReturnType1} = FuncType1,
    ?assertEqual(2, length(ParamTypes1)),
    ?assertMatch({primitive_type, 'Bool'}, ActualReturnType1),

    % Test with undefined return type (should create type variable)
    Params2 = [
        {param, a, {primitive_type, 'Float'}, undefined}
    ],
    ReturnType2 = undefined,

    FuncType2 = cure_typechecker:create_function_type_from_signature(Params2, ReturnType2),
    ?assertMatch({function_type, [_], _}, FuncType2),

    {function_type, ParamTypes2, ActualReturnType2} = FuncType2,
    ?assertEqual(1, length(ParamTypes2)),
    % Return type should be a type variable when undefined
    ?assert(cure_types:is_type_var(ActualReturnType2)),

    % Test with no parameters
    Params3 = [],
    ReturnType3 = {primitive_type, 'Unit'},

    FuncType3 = cure_typechecker:create_function_type_from_signature(Params3, ReturnType3),
    ?assertMatch({function_type, [], _}, FuncType3),

    {function_type, ParamTypes3, ActualReturnType3} = FuncType3,
    ?assertEqual([], ParamTypes3),
    ?assertMatch({primitive_type, 'Unit'}, ActualReturnType3),

    % Test with complex parameter types
    Params4 = [
        {param, lst, {list_type, {primitive_type, 'Int'}, undefined}, undefined},
        {param, func, {function_type, [{primitive_type, 'Int'}], {primitive_type, 'String'}},
            undefined}
    ],
    ReturnType4 = {list_type, {primitive_type, 'String'}, undefined},

    FuncType4 = cure_typechecker:create_function_type_from_signature(Params4, ReturnType4),
    ?assertMatch({function_type, [_, _], _}, FuncType4),

    io:format("✓ create_function_type_from_signature/2 test passed~n").

%% ============================================================================
%% Test 6: create_function_type_from_signature_records handles record format
%% ============================================================================

test_create_function_type_from_signature_records() ->
    io:format("Testing create_function_type_from_signature_records/2...~n"),

    % Test with record format parameters and defined return type
    Params1 = [
        #param{name = x, type = {primitive_type, 'Int'}, location = undefined},
        #param{name = y, type = {primitive_type, 'String'}, location = undefined}
    ],
    ReturnType1 = {primitive_type, 'Bool'},

    FuncType1 = cure_typechecker:create_function_type_from_signature_records(Params1, ReturnType1),
    ?assertMatch({function_type, [_, _], _}, FuncType1),

    {function_type, ParamTypes1, ActualReturnType1} = FuncType1,
    ?assertEqual(2, length(ParamTypes1)),
    ?assertMatch({primitive_type, 'Bool'}, ActualReturnType1),

    % Test with undefined return type (should create type variable)
    Params2 = [
        #param{name = a, type = {primitive_type, 'Float'}, location = undefined}
    ],
    ReturnType2 = undefined,

    FuncType2 = cure_typechecker:create_function_type_from_signature_records(Params2, ReturnType2),
    ?assertMatch({function_type, [_], _}, FuncType2),

    {function_type, ParamTypes2, ActualReturnType2} = FuncType2,
    ?assertEqual(1, length(ParamTypes2)),
    % Return type should be a type variable when undefined
    ?assert(cure_types:is_type_var(ActualReturnType2)),

    % Test with empty parameter list
    Params3 = [],
    ReturnType3 = {primitive_type, 'Unit'},

    FuncType3 = cure_typechecker:create_function_type_from_signature_records(Params3, ReturnType3),
    ?assertMatch({function_type, [], _}, FuncType3),

    {function_type, ParamTypes3, ActualReturnType3} = FuncType3,
    ?assertEqual([], ParamTypes3),
    ?assertMatch({primitive_type, 'Unit'}, ActualReturnType3),

    % Test mixed parameter format (tuple format fallback)
    Params4 = [
        % Tuple format
        {param, x, {primitive_type, 'Int'}, undefined},
        % Record format
        #param{name = y, type = {primitive_type, 'String'}, location = undefined}
    ],
    ReturnType4 = {primitive_type, 'Bool'},

    FuncType4 = cure_typechecker:create_function_type_from_signature_records(Params4, ReturnType4),
    ?assertMatch({function_type, [_, _], _}, FuncType4),

    {function_type, ParamTypes4, ActualReturnType4} = FuncType4,
    ?assertEqual(2, length(ParamTypes4)),
    ?assertMatch({primitive_type, 'Bool'}, ActualReturnType4),

    io:format("✓ create_function_type_from_signature_records/2 test passed~n").

%% ============================================================================
%% Integration Test: Full workflow from loading to type retrieval
%% ============================================================================

test_full_workflow() ->
    io:format("Testing full stdlib loading workflow...~n"),

    % Clean state
    erase(stdlib_functions),

    % Step 1: Load stdlib modules
    StdlibFunctions = cure_typechecker:load_stdlib_modules(),
    ?assert(map_size(StdlibFunctions) > 0),

    % Step 2: Create environment with stdlib
    BaseEnv = cure_typechecker:builtin_env(),
    EnvWithStd = cure_typechecker:add_std_function_types(BaseEnv),

    % Step 3: Verify functions are accessible in environment
    IdentityType = cure_types:lookup_env(EnvWithStd, identity),
    ?assertNotEqual(undefined, IdentityType),

    % Step 4: Test direct type retrieval
    {ok, DirectType} = cure_typechecker:get_stdlib_function_type('Std.Core', identity, 1),
    ?assertMatch({function_type, _, _}, DirectType),

    io:format("✓ Full stdlib loading workflow test passed~n").

%% ============================================================================
%% Error Handling Tests
%% ============================================================================

test_error_handling() ->
    io:format("Testing error handling in stdlib loading...~n"),

    % Test with invalid directory (should return empty map)
    % This requires modifying the stdlib path temporarily
    % For now, we test the graceful handling of parsing errors

    % Test extract_module_functions with invalid AST
    % Use a tuple that won't match expected patterns but won't crash element/2
    InvalidAST = [{invalid_item_type, some_data}],
    Functions = cure_typechecker:extract_module_functions(InvalidAST),
    ?assert(is_map(Functions)),

    % Test get_stdlib_function_type with invalid inputs
    ?assertEqual(
        not_found,
        cure_typechecker:get_stdlib_function_type('', '', 0)
    ),

    ?assertEqual(
        not_found,
        cure_typechecker:get_stdlib_function_type(invalid_atom, func, -1)
    ),

    io:format("✓ Error handling test passed~n").
