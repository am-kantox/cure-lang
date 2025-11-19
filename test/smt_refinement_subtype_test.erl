%% Test for refinement type subtyping with SMT verification
-module(smt_refinement_subtype_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

run() ->
    io:format("~n=== SMT Refinement Type Subtyping Test ===~n~n"),

    Tests = [
        fun test_positive_subtype_nonzero/0,
        fun test_percentage_subtype_positive/0,
        fun test_even_not_subtype_odd/0,
        fun test_range_subtyping/0
    ],

    Results = lists:map(fun run_test/1, Tests),

    Passed = length([R || R <- Results, R =:= ok]),
    Failed = length(Results) - Passed,

    io:format("~n=== Results ===~n"),
    io:format("Passed: ~p~n", [Passed]),
    io:format("Failed: ~p~n", [Failed]),

    case Failed of
        0 -> io:format("~n✅ All refinement subtyping tests passed!~n~n");
        _ -> io:format("~n❌ Some refinement subtyping tests failed!~n~n")
    end,

    ok.

run_test(TestFun) ->
    try
        TestFun(),
        ok
    catch
        Class:Reason:Stack ->
            io:format("  ❌ FAILED: ~p:~p~n", [Class, Reason]),
            io:format("     Stack: ~p~n", [Stack]),
            error
    end.

%% ============================================================================
%% Test: Positive <: NonZero
%% ============================================================================

test_positive_subtype_nonzero() ->
    io:format("Testing Positive <: NonZero... "),

    % type Positive = Int when x > 0
    Positive = cure_refinement_types:create_refinement_type(
        #primitive_type{name = 'Int', location = #location{line = 1, column = 1}},
        x,
        #binary_op_expr{
            op = '>',
            left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
            right = #literal_expr{value = 0, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        }
    ),

    % type NonZero = Int when x /= 0
    NonZero = cure_refinement_types:create_refinement_type(
        #primitive_type{name = 'Int', location = #location{line = 1, column = 1}},
        x,
        #binary_op_expr{
            op = '/=',
            left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
            right = #literal_expr{value = 0, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        }
    ),

    % Check subtyping: x > 0 => x /= 0
    case cure_refinement_types:check_subtype(Positive, NonZero, #{}) of
        {ok, true} ->
            io:format("✅ Subtyping proven~n"),
            ok;
        {ok, false} ->
            io:format("❌ Subtyping failed (should be true)~n"),
            error(subtyping_should_hold);
        {error, Reason} ->
            io:format("❌ Error: ~p~n", [Reason]),
            error(Reason)
    end.

%% ============================================================================
%% Test: Percentage <: Positive (should fail)
%% ============================================================================

test_percentage_subtype_positive() ->
    io:format("Testing Percentage NOT <: Positive (0 is in Percentage but not Positive)... "),

    % type Percentage = Int when x >= 0 and x =< 100
    Percentage = cure_refinement_types:create_refinement_type(
        #primitive_type{name = 'Int', location = #location{line = 1, column = 1}},
        x,
        #binary_op_expr{
            op = 'and',
            left = #binary_op_expr{
                op = '>=',
                left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
                right = #literal_expr{value = 0, location = #location{line = 1, column = 1}},
                location = #location{line = 1, column = 1}
            },
            right = #binary_op_expr{
                op = '=<',
                left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
                right = #literal_expr{value = 100, location = #location{line = 1, column = 1}},
                location = #location{line = 1, column = 1}
            },
            location = #location{line = 1, column = 1}
        }
    ),

    % type Positive = Int when x > 0
    Positive = cure_refinement_types:create_refinement_type(
        #primitive_type{name = 'Int', location = #location{line = 1, column = 1}},
        x,
        #binary_op_expr{
            op = '>',
            left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
            right = #literal_expr{value = 0, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        }
    ),

    % Check subtyping: x >= 0 and x <= 100 => x > 0 (should be FALSE because 0 is in Percentage)
    case cure_refinement_types:check_subtype(Percentage, Positive, #{}) of
        {ok, false} ->
            io:format("✅ Correctly rejected~n"),
            ok;
        {ok, true} ->
            io:format("❌ Subtyping should NOT hold~n"),
            error(subtyping_should_not_hold);
        {error, Reason} ->
            io:format("❌ Error: ~p~n", [Reason]),
            error(Reason)
    end.

%% ============================================================================
%% Test: Even NOT <: Odd
%% ============================================================================

test_even_not_subtype_odd() ->
    io:format("Testing Even NOT <: Odd... "),

    % type Even = Int when x mod 2 == 0
    Even = cure_refinement_types:create_refinement_type(
        #primitive_type{name = 'Int', location = #location{line = 1, column = 1}},
        x,
        #binary_op_expr{
            op = '==',
            left = #binary_op_expr{
                op = 'mod',
                left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
                right = #literal_expr{value = 2, location = #location{line = 1, column = 1}},
                location = #location{line = 1, column = 1}
            },
            right = #literal_expr{value = 0, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        }
    ),

    % type Odd = Int when x mod 2 == 1
    Odd = cure_refinement_types:create_refinement_type(
        #primitive_type{name = 'Int', location = #location{line = 1, column = 1}},
        x,
        #binary_op_expr{
            op = '==',
            left = #binary_op_expr{
                op = 'mod',
                left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
                right = #literal_expr{value = 2, location = #location{line = 1, column = 1}},
                location = #location{line = 1, column = 1}
            },
            right = #literal_expr{value = 1, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        }
    ),

    % Check subtyping: x mod 2 == 0 => x mod 2 == 1 (should be FALSE - disjoint)
    case cure_refinement_types:check_subtype(Even, Odd, #{}) of
        {ok, false} ->
            io:format("✅ Correctly rejected~n"),
            ok;
        {ok, true} ->
            io:format("❌ Even should NOT be subtype of Odd~n"),
            error(disjoint_types);
        {error, Reason} ->
            io:format("❌ Error: ~p~n", [Reason]),
            error(Reason)
    end.

%% ============================================================================
%% Test: Range Subtyping
%% ============================================================================

test_range_subtyping() ->
    io:format("Testing Range10 <: Range100... "),

    % type Range10 = Int when x >= 0 and x <= 10
    Range10 = cure_refinement_types:create_refinement_type(
        #primitive_type{name = 'Int', location = #location{line = 1, column = 1}},
        x,
        #binary_op_expr{
            op = 'and',
            left = #binary_op_expr{
                op = '>=',
                left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
                right = #literal_expr{value = 0, location = #location{line = 1, column = 1}},
                location = #location{line = 1, column = 1}
            },
            right = #binary_op_expr{
                op = '=<',
                left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
                right = #literal_expr{value = 10, location = #location{line = 1, column = 1}},
                location = #location{line = 1, column = 1}
            },
            location = #location{line = 1, column = 1}
        }
    ),

    % type Range100 = Int when x >= 0 and x <= 100
    Range100 = cure_refinement_types:create_refinement_type(
        #primitive_type{name = 'Int', location = #location{line = 1, column = 1}},
        x,
        #binary_op_expr{
            op = 'and',
            left = #binary_op_expr{
                op = '>=',
                left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
                right = #literal_expr{value = 0, location = #location{line = 1, column = 1}},
                location = #location{line = 1, column = 1}
            },
            right = #binary_op_expr{
                op = '=<',
                left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
                right = #literal_expr{value = 100, location = #location{line = 1, column = 1}},
                location = #location{line = 1, column = 1}
            },
            location = #location{line = 1, column = 1}
        }
    ),

    % Check subtyping: [0,10] <: [0,100] (should be TRUE)
    case cure_refinement_types:check_subtype(Range10, Range100, #{}) of
        {ok, true} ->
            io:format("✅ Range subtyping proven~n"),
            ok;
        {ok, false} ->
            io:format("❌ Range subtyping should hold~n"),
            error(range_subtyping_should_hold);
        {error, Reason} ->
            io:format("❌ Error: ~p~n", [Reason]),
            error(Reason)
    end.
