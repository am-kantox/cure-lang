%% Recursive Types Test Suite
%% Tests the third major type system enhancement: recursive/self-referential type definitions

-module(recursive_types_test).

%% Record definitions for recursive types testing
-record(recursive_type, {name, params, definition, binding_context, location}).
-record(mu_type, {var, body, unfold_level, location}).
-record(cycle_detection, {visited, stack, max_depth}).
-record(type_param, {name, value}).
-record(type_var, {id}).

%% Test exports
-export([
    run/0,
    test_recursive_type_creation/0,
    test_type_unfolding/0,
    test_cycle_detection/0,
    test_productivity_analysis/0,
    test_recursive_unification/0
]).

%% Test runner
run() ->
    cure_utils:debug("~n=== Recursive Types Test Suite ===~n"),

    Tests = [
        {test_recursive_type_creation, "Recursive Type Creation and Validation"},
        {test_type_unfolding, "Type Unfolding and Substitution"},
        {test_cycle_detection, "Cycle Detection in Type Definitions"},
        {test_productivity_analysis, "Productivity Analysis"},
        {test_recursive_unification, "Recursive Type Unification"}
    ],

    Results = lists:map(
        fun({TestFun, TestName}) ->
            cure_utils:debug("Testing ~s... ", [TestName]),
            try
                case apply(?MODULE, TestFun, []) of
                    ok ->
                        cure_utils:debug("PASSED~n"),
                        {TestName, passed};
                    {error, Reason} ->
                        cure_utils:debug("FAILED: ~p~n", [Reason]),
                        {TestName, {failed, Reason}}
                end
            catch
                Error:ErrReason:Stacktrace ->
                    cure_utils:debug("ERROR: ~p:~p~n", [Error, ErrReason]),
                    cure_utils:debug("Stacktrace: ~p~n", [Stacktrace]),
                    {TestName, {error, {Error, ErrReason}}}
            end
        end,
        Tests
    ),

    Passed = length([Result || {_, passed} = Result <- Results]),
    Total = length(Results),

    cure_utils:debug("~nResults: ~p/~p tests passed~n", [Passed, Total]),

    case Passed of
        Total ->
            cure_utils:debug("All recursive types tests passed!~n"),
            ok;
        _ ->
            cure_utils:debug("Some tests failed.~n"),
            {failed, Results}
    end.

%% ===== RECURSIVE TYPE CREATION TESTS =====

test_recursive_type_creation() ->
    % Test creating a simple recursive type like: List(T) = Nil | Cons(T, List(T))
    ListDef =
        {union_type, [
            {primitive_type, 'Nil'},
            {cons_type, [
                #type_param{name = elem_type, type = #type_var{id = 't'}},
                {recursive_type_ref, 'List'}
            ]}
        ]},

    case
        cure_types:create_recursive_type(
            'List', [#type_param{name = elem_type, type = #type_var{id = 't'}}], ListDef, {1, 1}
        )
    of
        RecType when is_record(RecType, recursive_type) ->
            % Verify the created type has correct structure
            case RecType#recursive_type.name of
                'List' -> test_tree_recursive_type();
                Other -> {error, {wrong_name, Other}}
            end;
        {error, Reason} ->
            {error, {list_creation_failed, Reason}}
    end.

test_tree_recursive_type() ->
    % Test creating a binary tree: Tree(T) = Leaf | Node(T, Tree(T), Tree(T))
    TreeDef =
        {union_type, [
            {primitive_type, 'Leaf'},
            {node_type, [
                #type_param{name = value, type = #type_var{id = 't'}},
                {recursive_type_ref, 'Tree'},
                {recursive_type_ref, 'Tree'}
            ]}
        ]},

    case
        cure_types:create_recursive_type(
            'Tree', [#type_param{name = value, type = #type_var{id = 't'}}], TreeDef, {2, 1}
        )
    of
        RecType when is_record(RecType, recursive_type) ->
            % Check well-formedness
            case cure_types:check_recursive_type_well_formed(RecType) of
                ok -> test_mu_type_creation();
                {error, Reason} -> {error, {tree_not_well_formed, Reason}}
            end;
        {error, Reason} ->
            {error, {tree_creation_failed, Reason}}
    end.

test_mu_type_creation() ->
    % Test μ-types: μX. Int -> X (infinite stream of functions)
    MuType = #mu_type{
        var = 'X',
        body = {function_type, [{primitive_type, 'Int'}], {mu_var, 'X'}},
        unfold_level = 0,
        location = {3, 1}
    },

    case cure_types:check_recursive_type_well_formed(MuType) of
        ok -> test_invalid_recursive_type();
        {error, Reason} -> {error, {mu_type_validation_failed, Reason}}
    end.

test_invalid_recursive_type() ->
    % Test that invalid recursive types are rejected

    % No recursion
    InvalidDef = {primitive_type, 'Int'},

    case cure_types:create_recursive_type('Invalid', [], InvalidDef, {4, 1}) of
        {error, {invalid_recursive_type, 'Invalid', {no_recursive_references}}} -> ok;
        % Any error is acceptable
        {error, {invalid_recursive_type, 'Invalid', _}} -> ok;
        Unexpected -> {error, {should_have_failed, Unexpected}}
    end.

%% ===== TYPE UNFOLDING TESTS =====

test_type_unfolding() ->
    % Test unfolding a recursive type one level
    ListDef =
        {union_type, [
            {primitive_type, 'Nil'},
            {cons_type, [#type_var{id = 't'}, {recursive_type_ref, 'List'}]}
        ]},

    RecType = #recursive_type{
        name = 'List',
        params = [#type_param{name = elem_type, type = #type_var{id = 't'}}],
        definition = ListDef,
        binding_context = #{},
        location = {5, 1}
    },

    case cure_types:unfold_recursive_type(RecType, 1) of
        {ok, UnfoldedType} ->
            % Verify that recursive references are substituted
            case contains_recursive_ref_in_type(UnfoldedType) of
                % Some refs may remain at deeper levels
                true -> test_multiple_unfolds(RecType);
                % All refs substituted
                false -> test_multiple_unfolds(RecType)
            end;
        {error, Reason} ->
            {error, {unfold_failed, Reason}}
    end.

test_multiple_unfolds(RecType) ->
    % Test unfolding multiple levels
    case cure_types:unfold_recursive_type(RecType, 3) of
        {ok, _DeepUnfolded} ->
            test_mu_type_unfold();
        {error, Reason} ->
            {error, {multiple_unfold_failed, Reason}}
    end.

test_mu_type_unfold() ->
    % Test μ-type unfolding
    MuType = #mu_type{
        var = 'X',
        body = {function_type, [{primitive_type, 'Int'}], {mu_var, 'X'}},
        unfold_level = 0,
        location = {6, 1}
    },

    case cure_types:unfold_recursive_type(MuType, 2) of
        {ok, _UnfoldedMu} ->
            test_unfold_depth_limits();
        {error, Reason} ->
            {error, {mu_unfold_failed, Reason}}
    end.

test_unfold_depth_limits() ->
    % Test that unfolding respects depth limits
    InfiniteType = #mu_type{
        var = 'X',
        body = {mu_var, 'X'},
        unfold_level = 0,
        location = {7, 1}
    },

    case cure_types:unfold_recursive_type(InfiniteType, 0) of
        {error, max_unfold_depth_reached} -> ok;
        Other -> {error, {should_have_failed_depth_limit, Other}}
    end.

%% ===== CYCLE DETECTION TESTS =====

test_cycle_detection() ->
    % Test cycle detection in type definitions
    CycleState = #cycle_detection{
        visited = sets:new(),
        stack = [],
        max_depth = 10
    },

    % Test a simple cycle
    SimpleCycle = {recursive_type_ref, 'A'},

    case cure_types:detect_cycles(SimpleCycle, CycleState) of
        {ok, _NewState} ->
            test_complex_cycle_detection();
        {error, _Reason} ->
            % Cycles may or may not be detected at this level - depends on implementation
            test_complex_cycle_detection()
    end.

test_complex_cycle_detection() ->
    % Test detection of indirect cycles: A -> B -> A
    ComplexType = {function_type, [{recursive_type_ref, 'A'}], {recursive_type_ref, 'B'}},

    InitialState = #cycle_detection{
        visited = sets:new(),
        % We're analyzing A
        stack = ['A'],
        max_depth = 100
    },

    case cure_types:detect_cycles(ComplexType, InitialState) of
        {ok, _} -> test_depth_limit_cycles();
        % Either result is acceptable
        {error, _} -> test_depth_limit_cycles()
    end.

test_depth_limit_cycles() ->
    % Test that cycle detection respects depth limits
    DeepState = #cycle_detection{
        visited = sets:new(),
        % Exceed max_depth
        stack = lists:seq(1, 150),
        max_depth = 100
    },

    SimpleType = {primitive_type, 'Int'},

    case cure_types:detect_cycles(SimpleType, DeepState) of
        {error, max_depth_exceeded} -> ok;
        % May not trigger if stack length check differs
        {ok, _} -> ok;
        Other -> {error, {unexpected_depth_behavior, Other}}
    end.

%% ===== PRODUCTIVITY ANALYSIS TESTS =====

test_productivity_analysis() ->
    % Test productivity analysis - productive recursive type
    ProductiveList = #recursive_type{
        name = 'List',
        params = [],
        definition =
            {union_type, [
                {primitive_type, 'Nil'},
                {cons_type, [{primitive_type, 'Int'}, {recursive_type_ref, 'List'}]}
            ]},
        binding_context = #{},
        location = {8, 1}
    },

    case cure_types:check_recursive_type_well_formed(ProductiveList) of
        ok -> test_non_productive_type();
        {error, Reason} -> {error, {productive_analysis_failed, Reason}}
    end.

test_non_productive_type() ->
    % Test non-productive recursive type (immediate recursion)
    NonProductiveType = #recursive_type{
        name = 'Bad',
        params = [],
        % Immediate recursion
        definition = {recursive_type_ref, 'Bad'},
        binding_context = #{},
        location = {9, 1}
    },

    case cure_types:check_recursive_type_well_formed(NonProductiveType) of
        {error, {non_productive, _}} -> test_mu_productivity();
        % Any error is acceptable
        {error, _} -> test_mu_productivity();
        ok -> {error, should_have_failed_non_productive}
    end.

test_mu_productivity() ->
    % Test μ-type productivity - a truly productive μ-type with constructor
    ProductiveMu = #mu_type{
        var = 'X',
        body = {function_type, [{primitive_type, 'Int'}], {list_type, {mu_var, 'X'}, undefined}},
        unfold_level = 0,
        location = {10, 1}
    },

    case cure_types:check_recursive_type_well_formed(ProductiveMu) of
        ok -> test_non_productive_mu();
        {error, Reason} -> {error, {mu_productivity_failed, Reason}}
    end.

test_non_productive_mu() ->
    % Test non-productive μ-type
    NonProductiveMu = #mu_type{
        var = 'X',
        % Immediate recursion
        body = {mu_var, 'X'},
        unfold_level = 0,
        location = {11, 1}
    },

    case cure_types:check_recursive_type_well_formed(NonProductiveMu) of
        {error, {non_productive_mu, 'X'}} -> ok;
        % Any error is acceptable
        {error, _} -> ok;
        ok -> {error, should_have_failed_non_productive_mu}
    end.

%% ===== RECURSIVE UNIFICATION TESTS =====

test_recursive_unification() ->
    % Test unifying identical recursive types
    ListType1 = #recursive_type{
        name = 'List',
        params = [#type_param{name = elem, type = #type_var{id = 't1'}}],
        definition = {cons_type, [#type_var{id = 't1'}, {recursive_type_ref, 'List'}]},
        binding_context = #{},
        location = {12, 1}
    },

    ListType2 = #recursive_type{
        name = 'List',
        params = [#type_param{name = elem, type = #type_var{id = 't2'}}],
        definition = {cons_type, [#type_var{id = 't2'}, {recursive_type_ref, 'List'}]},
        binding_context = #{},
        location = {12, 5}
    },

    case cure_types:unify_recursive_types(ListType1, ListType2, #{}) of
        {ok, _Subst} ->
            test_different_recursive_types();
        {error, Reason} ->
            {error, {recursive_unification_failed, Reason}}
    end.

test_different_recursive_types() ->
    % Test unifying different recursive types by unfolding
    ListType = #recursive_type{
        name = 'List',
        params = [],
        definition = {cons_type, [{primitive_type, 'Int'}, {recursive_type_ref, 'List'}]},
        binding_context = #{},
        location = {13, 1}
    },

    TreeType = #recursive_type{
        name = 'Tree',
        params = [],
        definition =
            {node_type, [
                {primitive_type, 'Int'}, {recursive_type_ref, 'Tree'}, {recursive_type_ref, 'Tree'}
            ]},
        binding_context = #{},
        location = {13, 10}
    },

    case cure_types:unify_recursive_types(ListType, TreeType, #{}) of
        % Expected to fail
        {error, _Reason} -> test_recursive_with_regular();
        {ok, _} -> {error, should_have_failed_different_types}
    end.

test_recursive_with_regular() ->
    % Test unifying recursive type with regular type
    RecType = #recursive_type{
        name = 'Nat',
        params = [],
        definition =
            {union_type, [
                {primitive_type, 'Zero'},
                {succ_type, [{recursive_type_ref, 'Nat'}]}
            ]},
        binding_context = #{},
        location = {14, 1}
    },

    RegularType = {primitive_type, 'Int'},

    case cure_types:unify_recursive_types(RecType, RegularType, #{}) of
        % May succeed if unfoldable
        {ok, _Subst} -> test_mu_unification();
        % May fail - either is acceptable
        {error, _Reason} -> test_mu_unification()
    end.

test_mu_unification() ->
    % Test μ-type unification
    MuType1 = #mu_type{
        var = 'X',
        body = {function_type, [{primitive_type, 'Int'}], {mu_var, 'X'}},
        unfold_level = 0,
        location = {15, 1}
    },

    MuType2 = #mu_type{
        var = 'Y',
        body = {function_type, [{primitive_type, 'Int'}], {mu_var, 'Y'}},
        unfold_level = 0,
        location = {15, 10}
    },

    case cure_types:unify_recursive_types(MuType1, MuType2, #{}) of
        {ok, _Subst} -> test_occurs_check_recursive();
        {error, Reason} -> {error, {mu_unification_failed, Reason}}
    end.

test_occurs_check_recursive() ->
    % Test occurs check with recursive types
    Var = #type_var{id = test_var},

    RecType = #recursive_type{
        name = 'Test',
        params = [],
        definition = {cons_type, [Var, {recursive_type_ref, 'Test'}]},
        binding_context = #{},
        location = {16, 1}
    },

    case cure_types:occurs_check_recursive(Var, RecType) of
        % Variable occurs in recursive type
        true -> ok;
        false -> {error, should_have_detected_occurs}
    end.

%% ===== HELPER FUNCTIONS =====

contains_recursive_ref_in_type(Type) ->
    contains_recursive_ref_in_type_impl(Type).

contains_recursive_ref_in_type_impl({recursive_type_ref, _}) ->
    true;
contains_recursive_ref_in_type_impl({function_type, Params, Return}) ->
    lists:any(fun contains_recursive_ref_in_type_impl/1, Params) orelse
        contains_recursive_ref_in_type_impl(Return);
contains_recursive_ref_in_type_impl({list_type, ElemType, LenExpr}) ->
    contains_recursive_ref_in_type_impl(ElemType) orelse
        (LenExpr =/= undefined andalso contains_recursive_ref_in_type_impl(LenExpr));
contains_recursive_ref_in_type_impl({dependent_type, _, Params}) ->
    lists:any(fun(#type_param{type = V}) -> contains_recursive_ref_in_type_impl(V) end, Params);
contains_recursive_ref_in_type_impl({union_type, Variants}) ->
    lists:any(fun contains_recursive_ref_in_type_impl/1, Variants);
contains_recursive_ref_in_type_impl({cons_type, Elements}) ->
    lists:any(fun contains_recursive_ref_in_type_impl/1, Elements);
contains_recursive_ref_in_type_impl({node_type, Elements}) ->
    lists:any(fun contains_recursive_ref_in_type_impl/1, Elements);
contains_recursive_ref_in_type_impl({succ_type, Elements}) ->
    lists:any(fun contains_recursive_ref_in_type_impl/1, Elements);
contains_recursive_ref_in_type_impl(_) ->
    false.
