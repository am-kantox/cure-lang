%% Higher-Kinded Types Test Suite
%% Tests the fourth major type system enhancement: higher-kinded types with kind checking

-module(higher_kinded_types_test).

%% Record definitions for higher-kinded types testing
-record(kind, {constructor, args, result, arity, location}).
-record(type_constructor, {name, kind, params, definition, constraints, location}).
-record(higher_kinded_type, {constructor, applied_args, remaining_args, location}).
-record(type_family, {name, kind, equations, location}).
-record(type_family_equation, {pattern, result, constraints, location}).
-record(constraint, {class, args, location}).
-record(type_param, {name, value}).
-record(type_var, {id}).

%% Test exports
-export([
    run/0,
    test_kind_creation_and_inference/0,
    test_type_constructor_creation/0,
    test_higher_kinded_type_application/0,
    test_type_families/0,
    test_constraint_checking/0
]).

%% Test runner
run() ->
    cure_utils:debug("~n=== Higher-Kinded Types Test Suite ===~n"),

    Tests = [
        {test_kind_creation_and_inference, "Kind Creation and Inference"},
        {test_type_constructor_creation, "Type Constructor Creation and Validation"},
        {test_higher_kinded_type_application, "Higher-Kinded Type Application"},
        {test_type_families, "Type Families and Type-Level Computation"},
        {test_constraint_checking, "Constraint Checking and Type Classes"}
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
            cure_utils:debug("All higher-kinded types tests passed!~n"),
            ok;
        _ ->
            cure_utils:debug("Some tests failed.~n"),
            {failed, Results}
    end.

%% ===== KIND CREATION AND INFERENCE TESTS =====

test_kind_creation_and_inference() ->
    % Test basic kind creation
    StarKind = cure_types:create_kind(star, [], {1, 1}),
    case StarKind#kind.constructor of
        star -> test_higher_order_kinds();
        Other -> {error, {wrong_star_kind, Other}}
    end.

test_higher_order_kinds() ->
    % Test higher-order kinds like * -> *
    StarKind = #kind{constructor = star, args = [], result = star, arity = 0, location = undefined},
    ArrowKind = cure_types:create_kind(arrow, [StarKind, StarKind], {2, 1}),

    case ArrowKind#kind.constructor of
        arrow -> test_kind_inference_primitive();
        Other -> {error, {wrong_arrow_kind, Other}}
    end.

test_kind_inference_primitive() ->
    % Test kind inference for primitive types
    KindEnv = #{},
    case cure_types:infer_kind({primitive_type, 'Int'}, KindEnv) of
        {ok, Kind} when Kind#kind.constructor =:= star ->
            test_kind_inference_function();
        {ok, Kind} ->
            {error, {wrong_primitive_kind, Kind}};
        {error, Reason} ->
            {error, {primitive_kind_inference_failed, Reason}}
    end.

test_kind_inference_function() ->
    % Test kind inference for function types
    KindEnv = #{},
    FuncType = {function_type, [{primitive_type, 'Int'}], {primitive_type, 'Bool'}},

    case cure_types:infer_kind(FuncType, KindEnv) of
        {ok, Kind} when Kind#kind.constructor =:= star ->
            test_kind_inference_dependent();
        {ok, Kind} ->
            {error, {wrong_function_kind, Kind}};
        {error, Reason} ->
            {error, {function_kind_inference_failed, Reason}}
    end.

test_kind_inference_dependent() ->
    % Test kind inference for dependent types (higher-kinded)
    KindEnv = #{},
    ListType =
        {dependent_type, 'List', [#type_param{name = elem, type = {primitive_type, 'Int'}}]},

    case cure_types:infer_kind(ListType, KindEnv) of
        {ok, Kind} when Kind#kind.constructor =:= arrow ->
            test_kind_unification();
        {ok, Kind} ->
            {error, {wrong_list_kind, Kind}};
        {error, Reason} ->
            {error, {list_kind_inference_failed, Reason}}
    end.

test_kind_unification() ->
    % Test unifying compatible kinds
    StarKind1 = #kind{constructor = star, args = [], result = star, arity = 0, location = {3, 1}},
    StarKind2 = #kind{constructor = star, args = [], result = star, arity = 0, location = {3, 5}},

    case cure_types:unify_kinds(StarKind1, StarKind2) of
        {ok, _} -> test_kind_unification_failure();
        {error, Reason} -> {error, {star_unification_failed, Reason}}
    end.

test_kind_unification_failure() ->
    % Test that incompatible kinds fail to unify
    StarKind = #kind{constructor = star, args = [], result = star, arity = 0, location = undefined},
    NatKind = #kind{constructor = nat, args = [], result = nat, arity = 0, location = undefined},

    case cure_types:unify_kinds(StarKind, NatKind) of
        % Expected failure
        {error, _Reason} -> ok;
        {ok, _} -> {error, should_have_failed_kind_unification}
    end.

%% ===== TYPE CONSTRUCTOR CREATION TESTS =====

test_type_constructor_creation() ->
    % Test creating a simple type constructor like Maybe
    StarKind = #kind{constructor = star, args = [], result = star, arity = 0, location = undefined},
    ArrowKind = #kind{
        constructor = arrow,
        args = [StarKind, StarKind],
        result = star,
        arity = 1,
        location = undefined
    },

    Params = [#type_param{name = a, type = #type_var{id = type_var_a}}],

    case cure_types:create_type_constructor('Maybe', ArrowKind, Params, undefined, {4, 1}) of
        Constructor when is_record(Constructor, type_constructor) ->
            case Constructor#type_constructor.name of
                'Maybe' -> test_functor_constructor();
                Other -> {error, {wrong_constructor_name, Other}}
            end;
        {error, Reason} ->
            {error, {maybe_constructor_failed, Reason}}
    end.

test_functor_constructor() ->
    % Test creating a Functor type class constructor
    StarKind = #kind{constructor = star, args = [], result = star, arity = 0, location = undefined},
    HigherOrderKind = #kind{
        constructor = arrow,
        args = [StarKind, StarKind],
        result = star,
        arity = 1,
        location = undefined
    },
    ConstraintKind = #kind{
        constructor = constraint, args = [], result = constraint, arity = 0, location = undefined
    },
    FunctorKind = #kind{
        constructor = arrow,
        args = [HigherOrderKind, ConstraintKind],
        result = constraint,
        arity = 1,
        location = undefined
    },

    Params = [#type_param{name = f, type = #type_var{id = type_var_f}}],

    case cure_types:create_type_constructor('Functor', FunctorKind, Params, undefined, {5, 1}) of
        Constructor when is_record(Constructor, type_constructor) ->
            test_constructor_validation();
        {error, Reason} ->
            {error, {functor_constructor_failed, Reason}}
    end.

test_constructor_validation() ->
    % Test that invalid constructors are rejected (arity mismatch)
    StarKind = #kind{constructor = star, args = [], result = star, arity = 0, location = undefined},
    TooManyParams = [
        #type_param{name = a, type = #type_var{id = var_a}},
        #type_param{name = b, type = #type_var{id = var_b}}
    ],

    case
        cure_types:create_type_constructor('Invalid', StarKind, TooManyParams, undefined, {6, 1})
    of
        {error, {invalid_type_constructor, 'Invalid', {arity_mismatch, 0, 2}}} -> ok;
        % Any error is acceptable
        {error, {invalid_type_constructor, 'Invalid', _}} -> ok;
        Unexpected -> {error, {should_have_failed, Unexpected}}
    end.

%% ===== HIGHER-KINDED TYPE APPLICATION TESTS =====

test_higher_kinded_type_application() ->
    % Test applying a type constructor to create a higher-kinded type
    StarKind = #kind{constructor = star, args = [], result = star, arity = 0, location = undefined},
    ArrowKind = #kind{
        constructor = arrow,
        args = [StarKind, StarKind],
        result = star,
        arity = 1,
        location = undefined
    },

    MaybeConstructor = #type_constructor{
        name = 'Maybe',
        kind = ArrowKind,
        params = [#type_param{name = a, type = #type_var{id = type_var_a}}],
        definition = undefined,
        constraints = [],
        location = {7, 1}
    },

    Args = [{primitive_type, 'Int'}],

    case cure_types:apply_type_constructor(MaybeConstructor, Args, {7, 10}) of
        HKType when is_record(HKType, higher_kinded_type) ->
            % Should be fully saturated (no remaining args)
            case HKType#higher_kinded_type.remaining_args of
                0 -> test_partial_application();
                N -> {error, {wrong_remaining_args, N, expected, 0}}
            end;
        {error, Reason} ->
            {error, {maybe_int_application_failed, Reason}}
    end.

test_partial_application() ->
    % Test partial application of a type constructor
    StarKind = #kind{constructor = star, args = [], result = star, arity = 0, location = undefined},
    ArrowKind = #kind{
        constructor = arrow,
        args = [StarKind, StarKind, StarKind],
        result = star,
        arity = 2,
        location = undefined
    },

    BinaryConstructor = #type_constructor{
        name = 'Either',
        kind = ArrowKind,
        params = [
            #type_param{name = a, type = #type_var{id = type_var_a}},
            #type_param{name = b, type = #type_var{id = type_var_b}}
        ],
        definition = undefined,
        constraints = [],
        location = {8, 1}
    },

    % Apply only one argument
    Args = [{primitive_type, 'String'}],

    case cure_types:apply_type_constructor(BinaryConstructor, Args, {8, 10}) of
        HKType when is_record(HKType, higher_kinded_type) ->
            % Should have 1 remaining argument
            case HKType#higher_kinded_type.remaining_args of
                1 -> test_over_application();
                N -> {error, {wrong_remaining_args_partial, N, expected, 1}}
            end;
        {error, Reason} ->
            {error, {either_partial_application_failed, Reason}}
    end.

test_over_application() ->
    % Test that over-application is rejected
    StarKind = #kind{constructor = star, args = [], result = star, arity = 0, location = undefined},
    ArrowKind = #kind{
        constructor = arrow,
        args = [StarKind, StarKind],
        result = star,
        arity = 1,
        location = undefined
    },

    MaybeConstructor = #type_constructor{
        name = 'Maybe',
        kind = ArrowKind,
        params = [#type_param{name = a, type = #type_var{id = type_var_a}}],
        definition = undefined,
        constraints = [],
        location = {9, 1}
    },

    % Try to apply too many arguments
    TooManyArgs = [{primitive_type, 'Int'}, {primitive_type, 'String'}],

    case cure_types:apply_type_constructor(MaybeConstructor, TooManyArgs, {9, 10}) of
        {error, {too_many_arguments, 2, 1}} -> test_saturation_check();
        % Any error is acceptable
        {error, _} -> test_saturation_check();
        Unexpected -> {error, {should_have_failed_over_application, Unexpected}}
    end.

test_saturation_check() ->
    % Test saturation checking
    FullyAppliedType = #higher_kinded_type{
        % Don't need full constructor for this test
        constructor = undefined,
        applied_args = [{primitive_type, 'Int'}],
        remaining_args = 0,
        location = {10, 1}
    },

    PartiallyAppliedType = #higher_kinded_type{
        constructor = undefined,
        applied_args = [{primitive_type, 'Int'}],
        remaining_args = 1,
        location = {10, 5}
    },

    case
        {
            cure_types:is_saturated_type(FullyAppliedType),
            cure_types:is_saturated_type(PartiallyAppliedType)
        }
    of
        {true, false} -> ok;
        {SatResult1, SatResult2} -> {error, {wrong_saturation_results, SatResult1, SatResult2}}
    end.

%% ===== TYPE FAMILIES TESTS =====

test_type_families() ->
    % Test creating a type family
    StarKind = #kind{constructor = star, args = [], result = star, arity = 0, location = undefined},
    NatKind = #kind{constructor = nat, args = [], result = nat, arity = 0, location = undefined},
    TypeFamilyKind = #kind{
        constructor = arrow,
        args = [StarKind, NatKind],
        result = nat,
        arity = 1,
        location = undefined
    },

    % Length type family: Length :: [*] -> Nat
    Equations = [
        #type_family_equation{
            % Empty list pattern
            pattern = [{list_type, [], undefined}],
            result = {literal_expr, 0, {11, 10}},
            constraints = [],
            location = {11, 5}
        },
        #type_family_equation{
            % Cons pattern
            pattern = [{list_type, [#type_var{id = head}], #type_var{id = tail}}],
            result = {succ, {type_family_app, 'Length', [#type_var{id = tail}]}},
            constraints = [],
            location = {12, 5}
        }
    ],

    case cure_types:create_type_family('Length', TypeFamilyKind, Equations, {11, 1}) of
        TypeFamily when is_record(TypeFamily, type_family) ->
            test_type_family_evaluation(TypeFamily);
        {error, Reason} ->
            {error, {length_type_family_failed, Reason}}
    end.

test_type_family_evaluation(LengthFamily) ->
    % Test evaluating type family with concrete arguments
    EmptyListArg = [{list_type, [], undefined}],

    case cure_types:evaluate_type_family(LengthFamily, EmptyListArg) of
        {ok, Result} ->
            % Should return 0 for empty list
            case Result of
                {literal_expr, 0, _} -> test_type_family_no_match(LengthFamily);
                Other -> {error, {wrong_empty_list_result, Other}}
            end;
        {error, Reason} ->
            {error, {empty_list_evaluation_failed, Reason}}
    end.

test_type_family_no_match(LengthFamily) ->
    % Test that non-matching arguments return error
    NonListArg = [{primitive_type, 'Int'}],

    case cure_types:evaluate_type_family(LengthFamily, NonListArg) of
        {error, no_matching_equation} -> test_type_family_equation_solving();
        % Any error is acceptable
        {error, _} -> test_type_family_equation_solving();
        {ok, _} -> {error, should_have_failed_non_list_arg}
    end.

test_type_family_equation_solving() ->
    % Test solving individual type family equations
    Equation = #type_family_equation{
        % Use atom directly for simplified testing
        pattern = [x],
        % Result should also be atom for consistency
        result = x,
        constraints = [],
        location = {13, 1}
    },

    Args = [{primitive_type, 'Bool'}],
    KindEnv = #{},

    case cure_types:solve_type_family_equation(Equation, Args, KindEnv) of
        {ok, Result} ->
            case Result of
                % Should substitute x with Bool
                {primitive_type, 'Bool'} -> ok;
                Other -> {error, {wrong_equation_result, Other}}
            end;
        {error, Reason} ->
            {error, {equation_solving_failed, Reason}}
    end.

%% ===== CONSTRAINT CHECKING TESTS =====

test_constraint_checking() ->
    % Test basic constraint satisfaction checking
    EqConstraint = #constraint{
        class = 'Eq',
        args = [{primitive_type, 'Int'}],
        location = {14, 1}
    },

    KindEnv = #{},

    case cure_types:check_constraint_satisfaction(EqConstraint, KindEnv) of
        ok -> test_functor_constraint();
        {error, Reason} -> {error, {eq_constraint_failed, Reason}}
    end.

test_functor_constraint() ->
    % Test higher-kinded constraint checking
    FunctorConstraint = #constraint{
        class = 'Functor',
        args = [{dependent_type, 'Maybe', []}],
        location = {15, 1}
    },

    KindEnv = #{},

    case cure_types:check_constraint_satisfaction(FunctorConstraint, KindEnv) of
        ok -> test_well_formed_checking();
        {error, Reason} -> {error, {functor_constraint_failed, Reason}}
    end.

test_well_formed_checking() ->
    % Test higher-kinded type well-formedness checking
    StarKind = #kind{constructor = star, args = [], result = star, arity = 0, location = undefined},
    ArrowKind = #kind{
        constructor = arrow,
        args = [StarKind, StarKind],
        result = star,
        arity = 1,
        location = undefined
    },

    ValidConstructor = #type_constructor{
        name = 'List',
        kind = ArrowKind,
        params = [#type_param{name = a, type = #type_var{id = type_var_a}}],
        definition = undefined,
        constraints = [],
        location = {16, 1}
    },

    ValidHKType = #higher_kinded_type{
        constructor = ValidConstructor,
        applied_args = [{primitive_type, 'String'}],
        remaining_args = 0,
        location = {16, 10}
    },

    case cure_types:check_higher_kinded_well_formed(ValidHKType) of
        ok -> test_malformed_checking();
        {error, Reason} -> {error, {well_formed_check_failed, Reason}}
    end.

test_malformed_checking() ->
    % Test that malformed higher-kinded types are rejected
    InvalidConstructor = #type_constructor{
        name = 'Invalid',
        kind = #kind{constructor = star, args = [], result = star, arity = 0, location = undefined},
        % Arity mismatch
        params = [#type_param{name = a, type = #type_var{id = var_a}}],
        definition = undefined,
        constraints = [],
        location = {17, 1}
    },

    MalformedHKType = #higher_kinded_type{
        constructor = InvalidConstructor,
        applied_args = [{primitive_type, 'Int'}],
        remaining_args = 0,
        location = {17, 10}
    },

    case cure_types:check_higher_kinded_well_formed(MalformedHKType) of
        % Expected failure
        {error, _Reason} -> test_kind_arity();
        ok -> {error, should_have_failed_malformed_check}
    end.

test_kind_arity() ->
    % Test kind arity calculation
    StarKind = #kind{constructor = star, args = [], result = star, arity = 0, location = undefined},
    BinaryKind = #kind{
        constructor = arrow,
        args = [StarKind, StarKind, StarKind],
        result = star,
        arity = 2,
        location = undefined
    },

    case {cure_types:kind_arity(StarKind), cure_types:kind_arity(BinaryKind)} of
        {0, 2} -> ok;
        {Arity1, Arity2} -> {error, {wrong_arities, Arity1, Arity2, expected, {0, 2}}}
    end.

%% ===== HELPER FUNCTIONS =====
