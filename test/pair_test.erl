%% Test module for Pair(KT, VT) primitive type
-module(pair_test).

-include("../src/parser/cure_ast.hrl").

-export([run/0]).

run() ->
    io:format("~n=== Pair Type Tests ===~n"),

    % Test 1: Pair type parsing
    test_pair_parsing(),

    % Test 2: Pair type unification
    test_pair_unification(),

    % Test 3: Pair as tuple equivalence
    test_pair_tuple_equivalence(),

    io:format("~n=== All Pair Tests Passed ===~n"),
    ok.

%% Test 1: Pair type parsing
test_pair_parsing() ->
    io:format("~nTest 1: Pair type parsing...~n"),

    % Parse "type Entry = Pair(String, Int)"
    Code = <<"type Entry = Pair(String, Int)">>,

    case cure_lexer:tokenize(Code) of
        {ok, Tokens} when is_list(Tokens) ->
            io:format("  Tokens: ~p~n", [Tokens]),

            case cure_parser:parse(Tokens) of
                {ok, AST} ->
                    io:format("  Parsed AST successfully~n"),
                    io:format("  AST: ~200p~n", [AST]),
                    io:format("  ✓ Pair parsing test passed~n");
                {error, Reason} ->
                    io:format("  ✗ Parse error: ~p~n", [Reason]),
                    throw({parse_error, Reason})
            end;
        {error, Reason} ->
            io:format("  ✗ Tokenization error: ~p~n", [Reason]),
            throw({tokenize_error, Reason})
    end.

%% Test 2: Pair type unification
test_pair_unification() ->
    io:format("~nTest 2: Pair type unification...~n"),

    % Create Pair(String, Int) and Pair(String, Int) - should unify
    Location = #location{line = 1, column = 1, file = <<"test">>},

    StringType = #primitive_type{name = 'String', location = Location},
    IntType = #primitive_type{name = 'Int', location = Location},

    StringParam = #type_param{
        name = undefined,
        type = StringType,
        location = Location
    },
    IntParam = #type_param{
        name = undefined,
        type = IntType,
        location = Location
    },

    Pair1 = #dependent_type{
        name = 'Pair',
        type_params = [],
        value_params = [StringParam, IntParam],
        location = Location
    },

    Pair2 = #dependent_type{
        name = 'Pair',
        type_params = [],
        value_params = [StringParam, IntParam],
        location = Location
    },

    case cure_types:unify(Pair1, Pair2) of
        {ok, _Subst} ->
            io:format("  ✓ Pair(String, Int) unifies with Pair(String, Int)~n");
        {error, Reason} ->
            io:format("  ✗ Unification failed: ~p~n", [Reason]),
            throw({unification_error, Reason})
    end,

    % Create Pair(String, Int) and Pair(Int, String) - should not unify
    PairReversed = #dependent_type{
        name = 'Pair',
        type_params = [],
        value_params = [IntParam, StringParam],
        location = Location
    },

    case cure_types:unify(Pair1, PairReversed) of
        {error, _} ->
            io:format("  ✓ Pair(String, Int) does not unify with Pair(Int, String)~n");
        {ok, _} ->
            io:format("  ✗ Should not unify different Pair types~n"),
            throw(unexpected_unification)
    end.

%% Test 3: Pair as tuple equivalence
test_pair_tuple_equivalence() ->
    io:format("~nTest 3: Pair as tuple equivalence...~n"),

    % Create Pair(String, Int)
    Location = #location{line = 1, column = 1, file = <<"test">>},

    StringType = #primitive_type{name = 'String', location = Location},
    IntType = #primitive_type{name = 'Int', location = Location},

    StringParam = #type_param{
        name = undefined,
        type = StringType,
        location = Location
    },
    IntParam = #type_param{
        name = undefined,
        type = IntType,
        location = Location
    },

    PairType = #dependent_type{
        name = 'Pair',
        type_params = [],
        value_params = [StringParam, IntParam],
        location = Location
    },

    % Create tuple type {String, Int}
    TupleType = #tuple_type{
        element_types = [StringType, IntType],
        location = Location
    },

    % These should unify since Pair(KT, VT) is equivalent to {KT, VT}
    case cure_types:unify(PairType, TupleType) of
        {ok, _Subst1} ->
            io:format("  ✓ Pair(String, Int) unifies with {String, Int}~n");
        {error, Reason1} ->
            io:format("  ✗ Unification failed: ~p~n", [Reason1]),
            throw({tuple_unification_error, Reason1})
    end,

    % Test reverse direction
    case cure_types:unify(TupleType, PairType) of
        {ok, _Subst2} ->
            io:format("  ✓ {String, Int} unifies with Pair(String, Int)~n");
        {error, Reason2} ->
            io:format("  ✗ Reverse unification failed: ~p~n", [Reason2]),
            throw({reverse_tuple_unification_error, Reason2})
    end.
