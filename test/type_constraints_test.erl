%% Type Constraints Test Suite
-module(type_constraints_test).

-export([run/0]).

-include("src/types/cure_types.hrl").

%% Run all tests
run() ->
    io:format("~n=== Type Constraints Test Suite ===~n"),
    Tests = [
        fun test_implication_constraints/0,
        fun test_equivalence_constraints/0,
        fun test_bounds_constraints/0,
        fun test_invariant_constraints/0,
        fun test_variance_constraints/0
    ],
    Results = [run_test(Test) || Test <- Tests],
    Passed = length([R || R <- Results, R =:= ok]),
    Total = length(Results),
    io:format("~nResults: ~w/~w tests passed~n", [Passed, Total]),
    case Passed of
        Total -> io:format("All type constraints tests passed!~n");
        _ -> io:format("Some tests failed.~n")
    end.

run_test(Test) ->
    try
        Result = Test(),
        case Result of
            ok ->
                io:format("PASSED~n"),
                ok;
            {error, Reason} ->
                io:format("FAILED: ~p~n", [Reason]),
                error
        end
    catch
        Class:Reason:Stack ->
            io:format("FAILED: ~p:~p~n", [Class, Reason]),
            io:format("Stack: ~p~n", [Stack]),
            error
    end.

%% Test implication constraints (A => B)
test_implication_constraints() ->
    io:format("Testing Implication Constraints... "),

    % Create a basic implication: Int => Number
    Constraint = #type_constraint{
        left = {primitive_type, 'Int'},
        op = 'implies',
        right = {primitive_type, 'Number'},
        location = {1, 1}
    },

    case cure_types:solve_implication_constraint(Constraint, #{}, #{}) of
        {ok, _} -> ok;
        Error -> {error, {implication_solving_failed, Error}}
    end.

%% Test equivalence constraints (A <=> B)
test_equivalence_constraints() ->
    io:format("Testing Equivalence Constraints... "),

    Constraint = #type_constraint{
        left = {primitive_type, 'Bool'},
        op = 'iff',
        right = {primitive_type, 'Bool'},
        location = {2, 1}
    },

    case cure_types:solve_equivalence_constraint(Constraint, #{}, #{}) of
        {ok, _} -> ok;
        Error -> {error, {equivalence_solving_failed, Error}}
    end.

%% Test bounds constraints
test_bounds_constraints() ->
    io:format("Testing Bounds Constraints... "),

    % Test range constraint: x in [1, 10]
    Constraint = #type_constraint{
        left = #type_var{id = x},
        op = 'bounds',
        right = {range, 1, 10},
        location = {3, 1}
    },

    case cure_types:solve_bounds_constraint(Constraint, #{}, #{}) of
        {ok, _} -> ok;
        Error -> {error, {bounds_solving_failed, Error}}
    end.

%% Test invariant constraints
test_invariant_constraints() ->
    io:format("Testing Invariant Constraints... "),

    % Test structural invariant
    Invariant = #type_invariant{
        name = list_length_positive,
        % Simplified predicate
        predicate = fun(_Type) -> true end,
        applies_to = [{list_type, #type_var{id = elem}, undefined}],
        location = {4, 1}
    },

    Constraint = #type_constraint{
        left = {list_type, {primitive_type, 'Int'}, undefined},
        op = 'invariant',
        right = Invariant,
        location = {4, 5}
    },

    case cure_types:solve_invariant_constraint(Constraint, #{}, #{}) of
        {ok, _} -> ok;
        Error -> {error, {invariant_solving_failed, Error}}
    end.

%% Test variance constraints
test_variance_constraints() ->
    io:format("Testing Variance Constraints... "),

    % Test covariance: List[A] is covariant in A
    Constraint = #variance_constraint{
        type_constructor = 'List',
        parameter = a,
        variance = covariant,
        context = [],
        location = {5, 1}
    },

    TypeConstraint = #type_constraint{
        left = {dependent_type, 'List', [#type_param{name = a, value = {primitive_type, 'Int'}}]},
        op = 'covariant',
        right = Constraint,
        location = {5, 5}
    },

    case cure_types:solve_variance_constraint(TypeConstraint, #{}, #{}, #{}) of
        {ok, _} -> ok;
        Error -> {error, {variance_solving_failed, Error}}
    end.
