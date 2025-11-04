-module(typeclass_resolution_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

run() ->
    io:format("~n=== Typeclass Resolution Tests ===~n~n"),

    test_create_environment(),
    test_register_typeclass(),
    test_register_instance(),
    test_lookup_instance(),
    test_overlapping_instances(),
    test_method_resolution(),

    io:format("~n=== All Typeclass Resolution Tests Passed ===~n").

test_create_environment() ->
    io:format("Testing environment creation...~n"),
    Env = cure_typeclass:new_env(),
    io:format("  ✓ Created new typeclass environment~n"),
    Env.

test_register_typeclass() ->
    io:format("~nTesting typeclass registration...~n"),
    Env = cure_typeclass:new_env(),

    % Create a simple Show typeclass
    ShowSig = #method_signature{
        name = show,
        type_params = [],
        params = [
            #param{
                name = x,
                type = #primitive_type{
                    name = 'T', location = #location{line = 1, column = 1, file = "test"}
                },
                location = #location{line = 1, column = 1, file = "test"}
            }
        ],
        return_type = #primitive_type{
            name = 'String', location = #location{line = 1, column = 1, file = "test"}
        },
        default_impl = undefined,
        location = #location{line = 1, column = 1, file = "test"}
    },

    ShowDef = #typeclass_def{
        name = 'Show',
        type_params = ['T'],
        constraints = [],
        methods = [ShowSig],
        default_methods = [],
        location = #location{line = 1, column = 1, file = "test"}
    },

    {ok, NewEnv} = cure_typeclass:register_typeclass(ShowDef, Env),
    io:format("  ✓ Registered Show typeclass~n"),

    % Verify lookup
    {ok, _Info} = cure_typeclass:lookup_typeclass('Show', NewEnv),
    io:format("  ✓ Can lookup registered typeclass~n"),

    NewEnv.

test_register_instance() ->
    io:format("~nTesting instance registration...~n"),
    Env = test_register_typeclass(),

    % Create Show(Int) instance
    ShowMethod = #function_def{
        name = show,
        type_params = [],
        clauses = [],
        params = [
            #param{
                name = x,
                type = #primitive_type{
                    name = 'Int', location = #location{line = 1, column = 1, file = "test"}
                },
                location = #location{line = 1, column = 1, file = "test"}
            }
        ],
        return_type = #primitive_type{
            name = 'String', location = #location{line = 1, column = 1, file = "test"}
        },
        constraint = undefined,
        body = #literal_expr{
            value = "42", location = #location{line = 1, column = 1, file = "test"}
        },
        is_private = false,
        location = #location{line = 1, column = 1, file = "test"}
    },

    IntType = #primitive_type{
        name = 'Int', location = #location{line = 1, column = 1, file = "test"}
    },

    ShowIntInstance = #instance_def{
        typeclass = 'Show',
        type_args = [IntType],
        constraints = [],
        methods = [ShowMethod],
        location = #location{line = 1, column = 1, file = "test"}
    },

    {ok, NewEnv} = cure_typeclass:register_instance(ShowIntInstance, Env),
    io:format("  ✓ Registered Show(Int) instance~n"),

    % Verify lookup
    {ok, _Instance} = cure_typeclass:lookup_instance('Show', [IntType], NewEnv),
    io:format("  ✓ Can lookup registered instance~n"),

    NewEnv.

test_lookup_instance() ->
    io:format("~nTesting instance lookup...~n"),
    Env = test_register_instance(),

    IntType = #primitive_type{
        name = 'Int', location = #location{line = 1, column = 1, file = "test"}
    },

    % Test exact lookup
    {ok, _} = cure_typeclass:lookup_instance('Show', [IntType], Env),
    io:format("  ✓ Exact instance lookup works~n"),

    % Test missing instance
    BoolType = #primitive_type{
        name = 'Bool', location = #location{line = 1, column = 1, file = "test"}
    },
    not_found = cure_typeclass:lookup_instance('Show', [BoolType], Env),
    io:format("  ✓ Missing instance returns not_found~n"),

    ok.

test_overlapping_instances() ->
    io:format("~nTesting overlapping instance detection...~n"),
    Env = test_register_instance(),

    % Try to register duplicate Show(Int) instance
    IntType = #primitive_type{
        name = 'Int', location = #location{line = 1, column = 1, file = "test"}
    },

    ShowMethod = #function_def{
        name = show,
        type_params = [],
        clauses = [],
        params = [
            #param{
                name = x, type = IntType, location = #location{line = 1, column = 1, file = "test"}
            }
        ],
        return_type = #primitive_type{
            name = 'String', location = #location{line = 1, column = 1, file = "test"}
        },
        constraint = undefined,
        body = #literal_expr{
            value = "different", location = #location{line = 1, column = 1, file = "test"}
        },
        is_private = false,
        location = #location{line = 1, column = 1, file = "test"}
    },

    DuplicateInstance = #instance_def{
        typeclass = 'Show',
        type_args = [IntType],
        constraints = [],
        methods = [ShowMethod],
        location = #location{line = 2, column = 1, file = "test"}
    },

    {error, {overlapping_instance, _}} = cure_typeclass:register_instance(DuplicateInstance, Env),
    io:format("  ✓ Overlapping instance detected~n"),

    ok.

test_method_resolution() ->
    io:format("~nTesting method resolution...~n"),
    Env = test_register_instance(),

    IntType = #primitive_type{
        name = 'Int', location = #location{line = 1, column = 1, file = "test"}
    },

    % Resolve show method for Int
    {ok, _Method} = cure_typeclass:resolve_method('Show', show, IntType, Env),
    io:format("  ✓ Method resolution successful~n"),

    % Try to resolve for unregistered type
    BoolType = #primitive_type{
        name = 'Bool', location = #location{line = 1, column = 1, file = "test"}
    },
    {error, {no_instance, 'Show', _}} = cure_typeclass:resolve_method('Show', show, BoolType, Env),
    io:format("  ✓ Method resolution fails for missing instance~n"),

    ok.
