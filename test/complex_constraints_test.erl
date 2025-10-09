%% Test suite for complex dependent type constraints
-module(complex_constraints_test).

-export([run/0]).

-include("../src/parser/cure_ast_simple.hrl").

%% Test result tracking
-record(test_result, {
    name :: string(),
    passed :: boolean(),
    details :: term()
}).

%% Run all complex constraint tests
run() ->
    io:format("=== Complex Type Constraints Test Suite ===~n"),

    Results = [
        test_implication_constraints(),
        test_equivalence_constraints(),
        test_bounds_constraints(),
        test_invariant_constraints(),
        test_variance_constraints(),
        test_dependent_relations(),
        test_complex_refinement_types(),
        test_structural_invariants()
    ],

    % Report results
    Passed = length([R || R <- Results, R#test_result.passed]),
    Total = length(Results),

    io:format("~n=== Test Summary ===~n"),
    io:format("Passed: ~p/~p tests~n", [Passed, Total]),

    % Report failures
    Failures = [R || R <- Results, not R#test_result.passed],
    lists:foreach(
        fun(#test_result{name = Name, details = Details}) ->
            io:format("FAILED: ~s - ~p~n", [Name, Details])
        end,
        Failures
    ),

    case Passed of
        Total ->
            io:format("All complex constraints tests PASSED!~n"),
            ok;
        _ ->
            io:format("~p tests FAILED~n", [Total - Passed]),
            error
    end.

%% Test implication constraints
test_implication_constraints() ->
    io:format("Testing implication constraints...~n"),
    try
        % Test A => B where A is satisfied
        PositiveInt = {refined_type, {primitive_type, 'Int'}, fun(X) -> X > 0 end},
        NonZeroInt = {refined_type, {primitive_type, 'Int'}, fun(X) -> X =/= 0 end},

        % Positive integers imply non-zero integers
        case cure_types:solve_implication_constraint(PositiveInt, NonZeroInt, #{}) of
            {ok, _Subst} ->
                % Test A => B where A is not satisfied
                NegativeInt = {refined_type, {primitive_type, 'Int'}, fun(X) -> X < 0 end},
                PositiveFloat = {refined_type, {primitive_type, 'Float'}, fun(X) -> X > 0.0 end},

                case cure_types:solve_implication_constraint(NegativeInt, PositiveFloat, #{}) of
                    {ok, _} ->
                        make_result("Implication constraints", true, implication_logic_valid);
                    Error ->
                        make_result(
                            "Implication constraints", false, {second_implication_failed, Error}
                        )
                end;
            Error ->
                make_result("Implication constraints", false, {first_implication_failed, Error})
        end
    catch
        ErrorClass:ErrorReason ->
            make_result("Implication constraints", false, {ErrorClass, ErrorReason})
    end.

%% Test equivalence constraints
test_equivalence_constraints() ->
    io:format("Testing equivalence constraints...~n"),
    try
        % Test A <=> B with matching predicates
        EvenInt1 = {refined_type, {primitive_type, 'Int'}, fun(X) -> X rem 2 =:= 0 end},
        EvenInt2 = {refined_type, {primitive_type, 'Int'}, fun(X) -> X rem 2 =:= 0 end},

        case cure_types:solve_equivalence_constraint(EvenInt1, EvenInt2, #{}) of
            {ok, _Subst} ->
                % Test A <=> B with different predicates
                OddInt = {refined_type, {primitive_type, 'Int'}, fun(X) -> X rem 2 =:= 1 end},

                case cure_types:solve_equivalence_constraint(EvenInt1, OddInt, #{}) of
                    {error, _} ->
                        make_result("Equivalence constraints", true, equivalence_logic_valid);
                    {ok, _} ->
                        make_result(
                            "Equivalence constraints",
                            false,
                            should_have_failed_different_predicates
                        )
                end;
            Error ->
                make_result("Equivalence constraints", false, {equivalence_failed, Error})
        end
    catch
        ErrorClass:ErrorReason ->
            make_result("Equivalence constraints", false, {ErrorClass, ErrorReason})
    end.

%% Test bounds constraints
test_bounds_constraints() ->
    io:format("Testing bounds constraints...~n"),
    try
        % Test integer bounds
        IntType = {primitive_type, 'Int'},
        Bounds = {range, 0, 100},

        case cure_types:solve_bounds_constraint(IntType, Bounds, #{}) of
            {ok, _Subst} ->
                % Test refined type with compatible bounds
                PositiveInt = {refined_type, IntType, fun(X) -> X > 0 end},

                case cure_types:solve_bounds_constraint(PositiveInt, Bounds, #{}) of
                    {ok, _} ->
                        % Test refined type with incompatible bounds
                        NegativeInt = {refined_type, IntType, fun(X) -> X < 0 end},

                        case cure_types:solve_bounds_constraint(NegativeInt, Bounds, #{}) of
                            {error, _} ->
                                make_result("Bounds constraints", true, bounds_validation_correct);
                            {ok, _} ->
                                make_result(
                                    "Bounds constraints",
                                    false,
                                    should_have_failed_incompatible_bounds
                                )
                        end;
                    Error ->
                        make_result("Bounds constraints", false, {compatible_bounds_failed, Error})
                end;
            Error ->
                make_result("Bounds constraints", false, {basic_bounds_failed, Error})
        end
    catch
        ErrorClass:ErrorReason ->
            make_result("Bounds constraints", false, {ErrorClass, ErrorReason})
    end.

%% Test invariant constraints
test_invariant_constraints() ->
    io:format("Testing invariant constraints...~n"),
    try
        % Test structural invariant for Vector type
        VectorType =
            {dependent_type, 'Vector', [
                #type_param{name = elem_type, value = {primitive_type, 'Float'}},
                #type_param{name = length, value = {literal_expr, 3, undefined}}
            ]},

        % Invariant: Vector length must be positive
        Invariant = {structural_invariant, [{length, positive}]},

        case cure_types:solve_invariant_constraint(VectorType, Invariant, #{}) of
            {ok, _Subst} ->
                % Test with zero-length vector (should fail)
                ZeroVectorType =
                    {dependent_type, 'Vector', [
                        #type_param{name = elem_type, value = {primitive_type, 'Float'}},
                        #type_param{name = length, value = {literal_expr, 0, undefined}}
                    ]},

                case cure_types:solve_invariant_constraint(ZeroVectorType, Invariant, #{}) of
                    {error, _} ->
                        make_result("Invariant constraints", true, invariant_validation_correct);
                    {ok, _} ->
                        make_result("Invariant constraints", false, should_have_failed_zero_length)
                end;
            Error ->
                make_result("Invariant constraints", false, {positive_invariant_failed, Error})
        end
    catch
        ErrorClass:ErrorReason ->
            make_result("Invariant constraints", false, {ErrorClass, ErrorReason})
    end.

%% Test variance constraints
test_variance_constraints() ->
    io:format("Testing variance constraints...~n"),
    try
        % Test covariance for List type
        ListType =
            {dependent_type, 'List', [
                #type_param{name = elem_type, value = {primitive_type, 'Int'}},
                #type_param{name = length, value = {literal_expr, 5, undefined}}
            ]},

        case
            cure_types:solve_variance_constraint(ListType, {primitive_type, 'Int'}, covariant, #{})
        of
            {ok, _Subst} ->
                % Test invariance for Vector type
                VectorType =
                    {dependent_type, 'Vector', [
                        #type_param{name = elem_type, value = {primitive_type, 'Float'}},
                        #type_param{name = length, value = {literal_expr, 3, undefined}}
                    ]},

                case
                    cure_types:solve_variance_constraint(
                        VectorType, {primitive_type, 'Float'}, invariant, #{}
                    )
                of
                    {ok, _} ->
                        % Test invalid variance (should fail)
                        case
                            cure_types:solve_variance_constraint(
                                VectorType, {primitive_type, 'Float'}, covariant, #{}
                            )
                        of
                            {error, _} ->
                                make_result(
                                    "Variance constraints", true, variance_validation_correct
                                );
                            {ok, _} ->
                                make_result(
                                    "Variance constraints",
                                    false,
                                    should_have_failed_invalid_variance
                                )
                        end;
                    Error ->
                        make_result(
                            "Variance constraints", false, {vector_invariance_failed, Error}
                        )
                end;
            Error ->
                make_result("Variance constraints", false, {list_covariance_failed, Error})
        end
    catch
        ErrorClass:ErrorReason ->
            make_result("Variance constraints", false, {ErrorClass, ErrorReason})
    end.

%% Test dependent relations
test_dependent_relations() ->
    io:format("Testing dependent relations...~n"),
    try
        % Test type predicate evaluation for Vector
        VectorType =
            {dependent_type, 'Vector', [
                #type_param{name = elem_type, value = {primitive_type, 'Float'}},
                #type_param{name = length, value = {literal_expr, 5, undefined}}
            ]},

        case cure_types:evaluate_type_predicate(VectorType, #{}) of
            {ok, true} ->
                % Test invalid Vector (negative length)
                InvalidVectorType =
                    {dependent_type, 'Vector', [
                        #type_param{name = elem_type, value = {primitive_type, 'Float'}},
                        #type_param{name = length, value = {literal_expr, -1, undefined}}
                    ]},

                case cure_types:evaluate_type_predicate(InvalidVectorType, #{}) of
                    {ok, false} ->
                        make_result("Dependent relations", true, predicate_evaluation_correct);
                    Other ->
                        make_result(
                            "Dependent relations", false, {invalid_vector_should_fail, Other}
                        )
                end;
            Error ->
                make_result("Dependent relations", false, {valid_vector_failed, Error})
        end
    catch
        ErrorClass:ErrorReason ->
            make_result("Dependent relations", false, {ErrorClass, ErrorReason})
    end.

%% Test complex refinement types
test_complex_refinement_types() ->
    io:format("Testing complex refinement types...~n"),
    try
        % Create a complex refinement type: positive even integers
        PositiveEvenInt =
            {refined_type, {primitive_type, 'Int'}, fun(X) -> X > 0 andalso X rem 2 =:= 0 end},

        % Test bounds compatibility
        Bounds = {range, 2, 20},

        case cure_types:solve_bounds_constraint(PositiveEvenInt, Bounds, #{}) of
            {ok, _Subst} ->
                % Test with incompatible bounds
                IncompatibleBounds = {range, -10, -1},

                case cure_types:solve_bounds_constraint(PositiveEvenInt, IncompatibleBounds, #{}) of
                    {error, _} ->
                        make_result(
                            "Complex refinement types", true, refinement_bounds_validation_correct
                        );
                    {ok, _} ->
                        make_result(
                            "Complex refinement types",
                            false,
                            should_have_failed_incompatible_refinement
                        )
                end;
            Error ->
                make_result("Complex refinement types", false, {refinement_bounds_failed, Error})
        end
    catch
        ErrorClass:ErrorReason ->
            make_result("Complex refinement types", false, {ErrorClass, ErrorReason})
    end.

%% Test structural invariants
test_structural_invariants() ->
    io:format("Testing structural invariants...~n"),
    try
        % Test Matrix type with structural invariants
        MatrixType =
            {dependent_type, 'Matrix', [
                #type_param{name = rows, value = {literal_expr, 3, undefined}},
                #type_param{name = cols, value = {literal_expr, 4, undefined}},
                #type_param{name = elem_type, value = {primitive_type, 'Float'}}
            ]},

        case cure_types:evaluate_type_predicate(MatrixType, #{}) of
            {ok, true} ->
                % Test Matrix with invalid dimensions
                InvalidMatrixType =
                    {dependent_type, 'Matrix', [
                        #type_param{name = rows, value = {literal_expr, 0, undefined}},
                        #type_param{name = cols, value = {literal_expr, -1, undefined}},
                        #type_param{name = elem_type, value = {primitive_type, 'Float'}}
                    ]},

                case cure_types:evaluate_type_predicate(InvalidMatrixType, #{}) of
                    {ok, false} ->
                        make_result("Structural invariants", true, matrix_invariants_correct);
                    Other ->
                        make_result(
                            "Structural invariants", false, {invalid_matrix_should_fail, Other}
                        )
                end;
            Error ->
                make_result("Structural invariants", false, {valid_matrix_failed, Error})
        end
    catch
        ErrorClass:ErrorReason ->
            make_result("Structural invariants", false, {ErrorClass, ErrorReason})
    end.

%% Helper functions
make_result(Name, Passed, Details) ->
    #test_result{name = Name, passed = Passed, details = Details}.
