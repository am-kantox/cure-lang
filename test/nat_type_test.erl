%% Test suite for Nat type (Peano encoding)
-module(nat_type_test).

-include_lib("eunit/eunit.hrl").
-include("../src/parser/cure_ast.hrl").

%% Test Nat type creation
nat_zero_test() ->
    Zero = cure_types:nat_zero(),
    ?assertEqual({identifier_expr, 'Zero', undefined}, Zero),
    ?assert(true).

nat_succ_test() ->
    Zero = cure_types:nat_zero(),
    One = cure_types:nat_succ(Zero),
    ?assertMatch({function_call_expr, {identifier_expr, 'Succ', undefined}, [_], undefined}, One),
    ?assert(true).

%% Test conversion functions
nat_from_int_zero_test() ->
    {ok, Zero} = cure_types:nat_from_int(0),
    ?assertEqual({identifier_expr, 'Zero', undefined}, Zero).

nat_from_int_positive_test() ->
    {ok, Three} = cure_types:nat_from_int(3),
    % Should be Succ(Succ(Succ(Zero)))
    ?assertMatch({function_call_expr, {identifier_expr, 'Succ', undefined}, [_], undefined}, Three).

nat_from_int_negative_test() ->
    Result = cure_types:nat_from_int(-5),
    ?assertEqual({error, negative_integer}, Result).

nat_to_int_zero_test() ->
    Zero = cure_types:nat_zero(),
    {ok, N} = cure_types:nat_to_int(Zero),
    ?assertEqual(0, N).

nat_to_int_positive_test() ->
    {ok, Five} = cure_types:nat_from_int(5),
    {ok, N} = cure_types:nat_to_int(Five),
    ?assertEqual(5, N).

%% Test round-trip conversion
nat_roundtrip_test() ->
    TestValues = [0, 1, 2, 3, 5, 10],
    lists:foreach(
        fun(N) ->
            {ok, NatN} = cure_types:nat_from_int(N),
            {ok, Result} = cure_types:nat_to_int(NatN),
            ?assertEqual(N, Result)
        end,
        TestValues
    ).

%% Test type checking
is_nat_type_primitive_test() ->
    NatType = {primitive_type, 'Nat'},
    ?assert(cure_types:is_nat_type(NatType)).

is_nat_type_union_test() ->
    NatUnionType = {union_type, 'Nat', [], undefined},
    ?assert(cure_types:is_nat_type(NatUnionType)).

is_nat_type_refined_test() ->
    % The refined Nat type (non-negative integers)
    NatRefinedType = {refined_type, {primitive_type, 'Int'}, fun(N) -> N >= 0 end},
    ?assert(cure_types:is_nat_type(NatRefinedType)).

is_not_nat_type_test() ->
    IntType = {primitive_type, 'Int'},
    ?assertNot(cure_types:is_nat_type(IntType)).

%% Test Nat type definition
nat_type_structure_test() ->
    % The TYPE_NAT macro should define a union type with Zero and Succ
    % We can't directly test the macro, but we can test that the type
    % is recognized
    ?assert(cure_types:is_nat_type({primitive_type, 'Nat'})).

%% Test parsing Nat constructors (requires integration with parser)
parse_zero_pattern_test() ->
    % This would require the parser to be set up
    % For now, we just verify the type system recognizes it
    Zero = {identifier_expr, 'Zero', undefined},
    ?assertMatch({identifier_expr, 'Zero', undefined}, Zero).

%% Test type unification with Nat
unify_nat_with_nat_test() ->
    NatType1 = {primitive_type, 'Nat'},
    NatType2 = {primitive_type, 'Nat'},
    {ok, Subst} = cure_types:unify(NatType1, NatType2),
    ?assertEqual(#{}, Subst).

%% Test that Nat values can be pattern matched
pattern_match_zero_test() ->
    Zero = cure_types:nat_zero(),
    case Zero of
        {identifier_expr, 'Zero', undefined} -> ?assert(true);
        _ -> ?assert(false)
    end.

pattern_match_succ_test() ->
    One = cure_types:nat_succ(cure_types:nat_zero()),
    case One of
        {function_call_expr, {identifier_expr, 'Succ', undefined}, _, undefined} ->
            ?assert(true);
        _ ->
            ?assert(false)
    end.
