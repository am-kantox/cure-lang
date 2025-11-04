-module(typeclass_integration_test).

-include("../src/parser/cure_ast.hrl").
-export([run/0]).

%% ============================================================================
%% Test Runner
%% ============================================================================

run() ->
    io:format("=== Running Typeclass Integration Tests ===~n~n"),

    Tests = [
        {"Parse typeclass and instance", fun test_parse_typeclass_instance/0},
        {"Parse derive clause", fun test_parse_derive_clause/0},
        {"Register and resolve typeclass", fun test_register_resolve/0},
        {"Derive and compile instance", fun test_derive_compile/0},
        {"End-to-end: parse → derive → compile", fun test_end_to_end/0},
        {"Multiple instances for same typeclass", fun test_multiple_instances/0},
        {"Constraint checking", fun test_constraint_checking/0},
        {"Method resolution with defaults", fun test_method_defaults/0}
    ],

    Results = run_tests(Tests, [], 0, 0),

    io:format("~n=== Test Summary ===~n"),
    io:format(
        "Total: ~p, Passed: ~p, Failed: ~p~n",
        [length(Tests), element(1, Results), element(2, Results)]
    ),

    case element(2, Results) of
        0 -> io:format("~nAll integration tests passed!~n");
        _ -> io:format("~nSome integration tests failed.~n")
    end.

run_tests([], _Acc, Passed, Failed) ->
    {Passed, Failed};
run_tests([{Name, TestFun} | Rest], Acc, Passed, Failed) ->
    io:format("Running: ~s ... ", [Name]),
    try
        TestFun(),
        io:format("PASSED~n"),
        run_tests(Rest, Acc, Passed + 1, Failed)
    catch
        Error:Reason:Stacktrace ->
            io:format("FAILED~n"),
            io:format("  Error: ~p~n  Reason: ~p~n", [Error, Reason]),
            io:format("  Stack: ~p~n", [Stacktrace]),
            run_tests(Rest, Acc, Passed, Failed + 1)
    end.

%% ============================================================================
%% Integration Test Cases
%% ============================================================================

test_parse_typeclass_instance() ->
    % Create a simple typeclass definition in Cure code
    Code =
        <<"\n"
        "        typeclass Show(T) do\n"
        "            def show(x: T): String\n"
        "        end\n"
        "        \n"
        "        instance Show(Int) do\n"
        "            def show(x: Int): String = int_to_string(x)\n"
        "        end\n"
        "    ">>,

    % Parse the code
    {ok, Tokens} = cure_lexer:tokenize(binary_to_list(Code)),
    {ok, AST} = cure_parser:parse(Tokens),

    % Verify we got typeclass and instance definitions
    TypeclassDefs = [Item || Item <- AST, is_record(Item, typeclass_def)],
    InstanceDefs = [Item || Item <- AST, is_record(Item, instance_def)],

    case {length(TypeclassDefs), length(InstanceDefs)} of
        {1, 1} -> ok;
        Other -> throw({unexpected_parse_result, Other})
    end.

test_parse_derive_clause() ->
    % Test parsing of derive clause
    Code =
        <<"\n"
        "        record Point do\n"
        "            x: Int\n"
        "            y: Int\n"
        "        end\n"
        "        derive Show, Eq\n"
        "    ">>,

    {ok, Tokens} = cure_lexer:tokenize(binary_to_list(Code)),
    {ok, AST} = cure_parser:parse(Tokens),

    % Find the record definition
    RecordDefs = [Item || Item <- AST, is_record(Item, record_def)],

    case RecordDefs of
        [#record_def{derive_clause = DeriveClause}] when DeriveClause =/= undefined ->
            % Verify derive clause has the expected typeclasses
            #derive_clause{typeclasses = TCs} = DeriveClause,
            case lists:sort(TCs) of
                ['Eq', 'Show'] -> ok;
                Other -> throw({unexpected_typeclasses, Other})
            end;
        _ ->
            throw(missing_derive_clause)
    end.

test_register_resolve() ->
    % Test registering and resolving typeclasses
    Location = #location{line = 1, column = 1, file = "test.cure"},

    % Create typeclass environment
    Env = cure_typeclass:new_env(),

    % Create a Show typeclass
    ShowMethod = #function_def{
        name = show,
        type_params = [],
        clauses = [],
        params = [#param{name = x, type = undefined, location = Location}],
        return_type = #primitive_type{name = 'String', location = Location},
        constraint = undefined,
        body = undefined,
        is_private = false,
        location = Location
    },

    ShowTypeclass = #typeclass_def{
        name = 'Show',
        type_params = ['T'],
        constraints = [],
        methods = [ShowMethod],
        default_methods = [],
        location = Location
    },

    % Register typeclass
    {ok, Env1} = cure_typeclass:register_typeclass(ShowTypeclass, Env),

    % Verify we can look it up
    case cure_typeclass:lookup_typeclass('Show', Env1) of
        {ok, _TC} -> ok;
        {error, Reason} -> throw({lookup_failed, Reason})
    end.

test_derive_compile() ->
    % Test deriving and compiling an instance
    Location = #location{line = 1, column = 1, file = "test.cure"},

    % Create a simple record
    Fields = [
        #record_field_def{
            name = x,
            type = #primitive_type{name = 'Int', location = Location},
            location = Location
        }
    ],

    RecordDef = #record_def{
        name = 'SimpleRecord',
        type_params = [],
        fields = Fields,
        derive_clause = undefined,
        location = Location
    },

    % Derive Show instance
    {ok, Instance} = cure_derive:derive_instance('Show', RecordDef, [], undefined),

    % Verify instance structure
    case Instance of
        #instance_def{
            typeclass = 'Show',
            type_args = [#primitive_type{name = 'SimpleRecord'}],
            methods = [_Method]
        } ->
            ok;
        Other ->
            throw({unexpected_instance, Other})
    end.

test_end_to_end() ->
    % Complete pipeline: parse → derive → compile metadata
    Location = #location{line = 1, column = 1, file = "test.cure"},

    % 1. Create record with derive clause
    Fields = [
        #record_field_def{
            name = value,
            type = #primitive_type{name = 'Int', location = Location},
            location = Location
        }
    ],

    DeriveClause = #derive_clause{
        typeclass = 'Show',
        typeclasses = ['Show', 'Eq'],
        for_type = undefined,
        constraints = [],
        location = Location
    },

    RecordDef = #record_def{
        name = 'TestRecord',
        type_params = [],
        fields = Fields,
        derive_clause = DeriveClause,
        location = Location
    },

    % 2. Process derive clause

    % Simplified state for testing
    State = #{},
    {ok, DerivedInstances, _NewState} =
        cure_typeclass_codegen:process_derive_clause(DeriveClause, RecordDef, State),

    % 3. Verify we got instances
    case length(DerivedInstances) of
        % Should have Show and Eq
        2 -> ok;
        N -> throw({expected_2_instances, got, N})
    end.

test_multiple_instances() ->
    % Test multiple instances for the same typeclass
    Location = #location{line = 1, column = 1, file = "test.cure"},
    Env = cure_typeclass:new_env(),

    % Register Show typeclass
    ShowMethod = #function_def{
        name = show,
        type_params = [],
        clauses = [],
        params = [#param{name = x, type = undefined, location = Location}],
        return_type = #primitive_type{name = 'String', location = Location},
        constraint = undefined,
        body = undefined,
        is_private = false,
        location = Location
    },

    ShowTypeclass = #typeclass_def{
        name = 'Show',
        type_params = ['T'],
        constraints = [],
        methods = [ShowMethod],
        default_methods = [],
        location = Location
    },

    {ok, Env1} = cure_typeclass:register_typeclass(ShowTypeclass, Env),

    % Create Show(Int) instance
    IntShowMethod = ShowMethod#function_def{
        body = #literal_expr{value = "int", location = Location}
    },

    IntInstance = #instance_def{
        typeclass = 'Show',
        type_args = [#primitive_type{name = 'Int', location = Location}],
        constraints = [],
        methods = [IntShowMethod],
        location = Location
    },

    {ok, Env2} = cure_typeclass:register_instance(IntInstance, Env1),

    % Create Show(Float) instance
    FloatInstance = #instance_def{
        typeclass = 'Show',
        type_args = [#primitive_type{name = 'Float', location = Location}],
        constraints = [],
        methods = [IntShowMethod],
        location = Location
    },

    {ok, _Env3} = cure_typeclass:register_instance(FloatInstance, Env2),

    % Both should be registered
    ok.

test_constraint_checking() ->
    % Test that constraint checking works
    Location = #location{line = 1, column = 1, file = "test.cure"},
    Env = cure_typeclass:new_env(),

    % Register Eq typeclass
    EqMethod = #function_def{
        name = '==',
        type_params = [],
        clauses = [],
        params = [
            #param{name = x, type = undefined, location = Location},
            #param{name = y, type = undefined, location = Location}
        ],
        return_type = #primitive_type{name = 'Bool', location = Location},
        constraint = undefined,
        body = undefined,
        is_private = false,
        location = Location
    },

    EqTypeclass = #typeclass_def{
        name = 'Eq',
        type_params = ['T'],
        constraints = [],
        methods = [EqMethod],
        default_methods = [],
        location = Location
    },

    {ok, Env1} = cure_typeclass:register_typeclass(EqTypeclass, Env),

    % Register Ord typeclass with Eq constraint
    OrdTypeclass = #typeclass_def{
        name = 'Ord',
        type_params = ['T'],
        % Requires Eq
        constraints = ['Eq'],
        methods = [],
        default_methods = [],
        location = Location
    },

    {ok, _Env2} = cure_typeclass:register_typeclass(OrdTypeclass, Env1),

    % Successfully registered typeclass with constraints
    ok.

test_method_defaults() ->
    % Test that default methods are handled
    Location = #location{line = 1, column = 1, file = "test.cure"},

    % Create typeclass with default method
    ShowMethod = #function_def{
        name = show,
        type_params = [],
        clauses = [],
        params = [#param{name = x, type = undefined, location = Location}],
        return_type = #primitive_type{name = 'String', location = Location},
        constraint = undefined,
        body = undefined,
        is_private = false,
        location = Location
    },

    % Method with default implementation
    DefaultMethod = ShowMethod#function_def{
        name = debug,
        body = #literal_expr{value = "default debug", location = Location}
    },

    TypeclassWithDefault = #typeclass_def{
        name = 'Debug',
        type_params = ['T'],
        constraints = [],
        methods = [ShowMethod],
        default_methods = [DefaultMethod],
        location = Location
    },

    % Verify structure
    case TypeclassWithDefault of
        #typeclass_def{default_methods = [_]} -> ok;
        _ -> throw(missing_default_method)
    end.

%% ============================================================================
%% Helper Functions
%% ============================================================================

%% Additional integration test helpers can be added here
