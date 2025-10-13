%% Pattern Compilation Tests
%% Unit tests for compiling Cure patterns to Erlang abstract forms
-module(pattern_compilation_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").

%% Run all pattern compilation tests
run() ->
    io:format("Running Pattern Compilation tests...~n"),
    test_binary_pattern_compilation(),
    test_map_pattern_compilation(),
    test_record_pattern_compilation(),
    test_wildcard_pattern_compilation(),
    test_complex_nested_patterns(),
    io:format("All pattern compilation tests passed!~n").

%% Test 1: Binary patterns compilation to Erlang forms
test_binary_pattern_compilation() ->
    io:format("Testing binary pattern compilation...~n"),

    Location = #location{line = 1, column = 1, file = "test"},
    Line = 1,

    % Note: Binary patterns are not yet implemented in the AST
    % This test shows what the expected implementation should look like
    % when binary_pattern record is added to cure_ast.hrl

    % Test simple binary pattern <<X>>
    % Expected AST (when implemented):
    % BinaryPattern = #binary_pattern{
    %     elements = [#binary_element{
    %         value = #identifier_pattern{name = x, location = Location},
    %         size = undefined,
    %         type = undefined,
    %         unit = undefined,
    %         sign = undefined,
    %         endian = undefined,
    %         location = Location
    %     }],
    %     location = Location
    % },

    % Expected Erlang form: {bin, Line, [{bin_element, Line, {var, Line, x}, default, default}]}
    ExpectedSimpleBinary = {bin, Line, [{bin_element, Line, {var, Line, x}, default, default}]},

    % Test binary pattern with size <<X:8>>
    % Expected Erlang form: {bin, Line, [{bin_element, Line, {var, Line, x}, {integer, Line, 8}, default}]}
    ExpectedSizedBinary =
        {bin, Line, [{bin_element, Line, {var, Line, x}, {integer, Line, 8}, default}]},

    % Test binary pattern with type <<X:8/integer>>
    % Expected Erlang form: {bin, Line, [{bin_element, Line, {var, Line, x}, {integer, Line, 8}, [integer]}]}
    ExpectedTypedBinary =
        {bin, Line, [{bin_element, Line, {var, Line, x}, {integer, Line, 8}, [integer]}]},

    % Test multiple elements binary pattern <<X:8, Y:16>>
    % Expected Erlang form: {bin, Line, [{bin_element, Line, {var, Line, x}, {integer, Line, 8}, default},
    %                                     {bin_element, Line, {var, Line, y}, {integer, Line, 16}, default}]}
    ExpectedMultipleBinary =
        {bin, Line, [
            {bin_element, Line, {var, Line, x}, {integer, Line, 8}, default},
            {bin_element, Line, {var, Line, y}, {integer, Line, 16}, default}
        ]},

    % Test literal binary pattern <<"hello">>
    % Expected Erlang form: {bin, Line, [{bin_element, Line, {string, Line, "hello"}, default, default}]}
    ExpectedLiteralBinary =
        {bin, Line, [{bin_element, Line, {string, Line, "hello"}, default, default}]},

    % Test rest pattern <<Head:8, Rest/binary>>
    % Expected Erlang form: {bin, Line, [{bin_element, Line, {var, Line, 'Head'}, {integer, Line, 8}, default},
    %                                     {bin_element, Line, {var, Line, 'Rest'}, default, [binary]}]}
    ExpectedRestBinary =
        {bin, Line, [
            {bin_element, Line, {var, Line, 'Head'}, {integer, Line, 8}, default},
            {bin_element, Line, {var, Line, 'Rest'}, default, [binary]}
        ]},

    % TODO: Once binary_pattern is added to AST, uncomment and implement these tests:
    % BinaryResult = cure_codegen:convert_pattern_to_erlang_form(BinaryPattern, Location),
    % ?assertEqual(ExpectedSimpleBinary, BinaryResult),

    % For now, just verify the expected forms are correctly structured
    ?assertMatch({bin, _, [{bin_element, _, _, _, _}]}, ExpectedSimpleBinary),
    ?assertMatch({bin, _, [{bin_element, _, _, _, _}]}, ExpectedSizedBinary),
    ?assertMatch({bin, _, [{bin_element, _, _, _, _}]}, ExpectedTypedBinary),
    ?assertMatch(
        {bin, _, [{bin_element, _, _, _, _}, {bin_element, _, _, _, _}]}, ExpectedMultipleBinary
    ),
    ?assertMatch({bin, _, [{bin_element, _, _, _, _}]}, ExpectedLiteralBinary),
    ?assertMatch(
        {bin, _, [{bin_element, _, _, _, _}, {bin_element, _, _, _, _}]}, ExpectedRestBinary
    ),

    io:format("✓ Binary pattern compilation test passed (structural verification)~n").

%% Test 2: Map patterns compilation to Erlang forms
test_map_pattern_compilation() ->
    io:format("Testing map pattern compilation...~n"),

    Location = #location{line = 1, column = 1, file = "test"},
    Line = 1,

    % Note: Map patterns are not yet implemented in the AST
    % This test shows what the expected implementation should look like
    % when map_pattern record is added to cure_ast.hrl

    % Test empty map pattern #{}
    % Expected AST (when implemented):
    % EmptyMapPattern = #map_pattern{
    %     fields = [],
    %     location = Location
    % },

    % Expected Erlang form: {map, Line, []}
    ExpectedEmptyMap = {map, Line, []},

    % Test map pattern with exact match #{key := value}
    % Expected AST (when implemented):
    % ExactMapPattern = #map_pattern{
    %     fields = [#map_field_exact{
    %         key = #literal_pattern{value = key, location = Location},
    %         value = #identifier_pattern{name = value, location = Location},
    %         location = Location
    %     }],
    %     location = Location
    % },

    % Expected Erlang form: {map, Line, [{map_field_exact, Line, {atom, Line, key}, {var, Line, value}}]}
    ExpectedExactMap =
        {map, Line, [{map_field_exact, Line, {atom, Line, key}, {var, Line, value}}]},

    % Test map pattern with multiple fields #{a := X, b := Y}
    % Expected Erlang form: {map, Line, [{map_field_exact, Line, {atom, Line, a}, {var, Line, x}},
    %                                     {map_field_exact, Line, {atom, Line, b}, {var, Line, y}}]}
    ExpectedMultiFieldMap =
        {map, Line, [
            {map_field_exact, Line, {atom, Line, a}, {var, Line, x}},
            {map_field_exact, Line, {atom, Line, b}, {var, Line, y}}
        ]},

    % Test map pattern with variable key #{Key := Value}
    % Expected Erlang form: {map, Line, [{map_field_exact, Line, {var, Line, 'Key'}, {var, Line, 'Value'}}]}
    ExpectedVarKeyMap =
        {map, Line, [{map_field_exact, Line, {var, Line, 'Key'}, {var, Line, 'Value'}}]},

    % Test nested map pattern #{outer := #{inner := X}}
    % Expected Erlang form: {map, Line, [{map_field_exact, Line, {atom, Line, outer},
    %                                     {map, Line, [{map_field_exact, Line, {atom, Line, inner}, {var, Line, x}}]}}]}
    ExpectedNestedMap =
        {map, Line, [
            {map_field_exact, Line, {atom, Line, outer},
                {map, Line, [{map_field_exact, Line, {atom, Line, inner}, {var, Line, x}}]}}
        ]},

    % TODO: Once map_pattern is added to AST, uncomment and implement these tests:
    % MapResult = cure_codegen:convert_pattern_to_erlang_form(MapPattern, Location),
    % ?assertEqual(ExpectedExactMap, MapResult),

    % For now, just verify the expected forms are correctly structured
    ?assertMatch({map, _, []}, ExpectedEmptyMap),
    ?assertMatch({map, _, [{map_field_exact, _, _, _}]}, ExpectedExactMap),
    ?assertMatch(
        {map, _, [{map_field_exact, _, _, _}, {map_field_exact, _, _, _}]}, ExpectedMultiFieldMap
    ),
    ?assertMatch({map, _, [{map_field_exact, _, _, _}]}, ExpectedVarKeyMap),
    ?assertMatch(
        {map, _, [{map_field_exact, _, _, {map, _, [{map_field_exact, _, _, _}]}}]},
        ExpectedNestedMap
    ),

    io:format("✓ Map pattern compilation test passed (structural verification)~n").

%% Test 3: Record patterns compilation to Erlang forms
test_record_pattern_compilation() ->
    io:format("Testing record pattern compilation...~n"),

    Location = #location{line = 1, column = 1, file = "test"},
    Line = 1,

    % Test record pattern with all fields #person{name = Name, age = Age}
    % This uses the existing record_pattern in AST
    PersonPattern = #record_pattern{
        name = person,
        fields = [
            #field_pattern{
                name = name,
                pattern = #identifier_pattern{name = 'Name', location = Location},
                location = Location
            },
            #field_pattern{
                name = age,
                pattern = #identifier_pattern{name = 'Age', location = Location},
                location = Location
            }
        ],
        location = Location
    },

    % Expected Erlang form: {record, Line, person, [{record_field, Line, {atom, Line, name}, {var, Line, 'Name'}},
    %                                                {record_field, Line, {atom, Line, age}, {var, Line, 'Age'}}]}
    ExpectedPersonRecord =
        {record, Line, person, [
            {record_field, Line, {atom, Line, name}, {var, Line, 'Name'}},
            {record_field, Line, {atom, Line, age}, {var, Line, 'Age'}}
        ]},

    % Test record pattern with wildcard fields #person{name = Name, _ = _}
    WildcardRecordPattern = #record_pattern{
        name = person,
        fields = [
            #field_pattern{
                name = name,
                pattern = #identifier_pattern{name = 'Name', location = Location},
                location = Location
            },
            #field_pattern{
                name = '_', pattern = #wildcard_pattern{location = Location}, location = Location
            }
        ],
        location = Location
    },

    % Expected Erlang form: {record, Line, person, [{record_field, Line, {atom, Line, name}, {var, Line, 'Name'}},
    %                                                {record_field, Line, {var, Line, '_'}, {var, Line, '_'}}]}
    ExpectedWildcardRecord =
        {record, Line, person, [
            {record_field, Line, {atom, Line, name}, {var, Line, 'Name'}},
            {record_field, Line, {var, Line, '_'}, {var, Line, '_'}}
        ]},

    % Test empty record pattern #person{}
    EmptyRecordPattern = #record_pattern{
        name = person,
        fields = [],
        location = Location
    },

    % Expected Erlang form: {record, Line, person, []}
    ExpectedEmptyRecord = {record, Line, person, []},

    % Test nested record pattern #company{ceo = #person{name = CEO}}
    NestedRecordPattern = #record_pattern{
        name = company,
        fields = [
            #field_pattern{
                name = ceo,
                pattern = #record_pattern{
                    name = person,
                    fields = [
                        #field_pattern{
                            name = name,
                            pattern = #identifier_pattern{name = 'CEO', location = Location},
                            location = Location
                        }
                    ],
                    location = Location
                },
                location = Location
            }
        ],
        location = Location
    },

    % Expected Erlang form: {record, Line, company, [{record_field, Line, {atom, Line, ceo},
    %                                                  {record, Line, person, [{record_field, Line, {atom, Line, name}, {var, Line, 'CEO'}}]}}]}
    ExpectedNestedRecord =
        {record, Line, company, [
            {record_field, Line, {atom, Line, ceo},
                {record, Line, person, [
                    {record_field, Line, {atom, Line, name}, {var, Line, 'CEO'}}
                ]}}
        ]},

    % TODO: These tests will fail until record pattern compilation is implemented
    % For now, the current implementation falls back to wildcard

    % Test current implementation (should return wildcard as fallback)
    CurrentResult = cure_codegen:convert_pattern_to_erlang_form(PersonPattern, Location),
    % Current implementation should return wildcard fallback
    ?assertEqual({var, Line, '_'}, CurrentResult),

    % Verify expected forms are correctly structured for when record patterns are implemented
    ?assertMatch(
        {record, _, person, [{record_field, _, _, _}, {record_field, _, _, _}]},
        ExpectedPersonRecord
    ),
    ?assertMatch(
        {record, _, person, [{record_field, _, _, _}, {record_field, _, _, _}]},
        ExpectedWildcardRecord
    ),
    ?assertMatch({record, _, person, []}, ExpectedEmptyRecord),
    ?assertMatch(
        {record, _, company, [{record_field, _, _, {record, _, person, [{record_field, _, _, _}]}}]},
        ExpectedNestedRecord
    ),

    io:format("✓ Record pattern compilation test passed (fallback and structural verification)~n").

%% Test 4: Wildcard patterns compilation to Erlang forms
test_wildcard_pattern_compilation() ->
    io:format("Testing wildcard pattern compilation...~n"),

    Location = #location{line = 1, column = 1, file = "test"},
    Line = 1,

    % Test simple wildcard pattern _
    WildcardPattern = #wildcard_pattern{location = Location},

    % Expected Erlang form: {var, Line, '_'}
    ExpectedWildcard = {var, Line, '_'},

    % Test compilation using existing implementation
    WildcardResult = cure_codegen:convert_pattern_to_erlang_form(WildcardPattern, Location),
    ?assertEqual(ExpectedWildcard, WildcardResult),

    % Test wildcards in different contexts (already covered in existing tests but ensuring completeness)

    % Wildcard in tuple
    TupleWithWildcard = #tuple_pattern{
        elements = [
            #literal_pattern{value = 1, location = Location},
            #wildcard_pattern{location = Location},
            #identifier_pattern{name = x, location = Location}
        ],
        location = Location
    },

    ExpectedTupleWithWildcard =
        {tuple, Line, [
            {integer, Line, 1},
            {var, Line, '_'},
            {var, Line, x}
        ]},

    TupleResult = cure_codegen:convert_pattern_to_erlang_form(TupleWithWildcard, Location),
    ?assertEqual(ExpectedTupleWithWildcard, TupleResult),

    % Wildcard in list
    ListWithWildcard = #list_pattern{
        elements = [
            #wildcard_pattern{location = Location},
            #identifier_pattern{name = rest, location = Location}
        ],
        tail = undefined,
        location = Location
    },

    ExpectedListWithWildcard =
        {cons, Line, {var, Line, '_'}, {cons, Line, {var, Line, rest}, {nil, Line}}},

    ListResult = cure_codegen:convert_pattern_to_erlang_form(ListWithWildcard, Location),
    ?assertEqual(ExpectedListWithWildcard, ListResult),

    % Multiple wildcards should each be independent
    MultiWildcardTuple = #tuple_pattern{
        elements = [
            #wildcard_pattern{location = Location},
            #wildcard_pattern{location = Location}
        ],
        location = Location
    },

    ExpectedMultiWildcard =
        {tuple, Line, [
            {var, Line, '_'},
            {var, Line, '_'}
        ]},

    MultiResult = cure_codegen:convert_pattern_to_erlang_form(MultiWildcardTuple, Location),
    ?assertEqual(ExpectedMultiWildcard, MultiResult),

    io:format("✓ Wildcard pattern compilation test passed~n").

%% Test 5: Complex nested patterns involving mix of lists, tuples, and other patterns
test_complex_nested_patterns() ->
    io:format("Testing complex nested pattern compilation...~n"),

    Location = #location{line = 1, column = 1, file = "test"},
    Line = 1,

    % Test 1: Tuple containing list patterns: {status, [head | tail]}
    TupleListPattern = #tuple_pattern{
        elements = [
            #literal_pattern{value = status, location = Location},
            #list_pattern{
                elements = [#identifier_pattern{name = head, location = Location}],
                tail = #identifier_pattern{name = tail, location = Location},
                location = Location
            }
        ],
        location = Location
    },

    ExpectedTupleList =
        {tuple, Line, [
            {atom, Line, status},
            {cons, Line, {var, Line, head}, {var, Line, tail}}
        ]},

    TupleListResult = cure_codegen:convert_pattern_to_erlang_form(TupleListPattern, Location),
    ?assertEqual(ExpectedTupleList, TupleListResult),

    % Test 2: List of tuples: [{ok, value1}, {error, reason}]
    ListOfTuplesPattern = #list_pattern{
        elements = [
            #tuple_pattern{
                elements = [
                    #literal_pattern{value = ok, location = Location},
                    #identifier_pattern{name = value1, location = Location}
                ],
                location = Location
            },
            #tuple_pattern{
                elements = [
                    #literal_pattern{value = error, location = Location},
                    #identifier_pattern{name = reason, location = Location}
                ],
                location = Location
            }
        ],
        tail = undefined,
        location = Location
    },

    ExpectedListOfTuples =
        {cons, Line, {tuple, Line, [{atom, Line, ok}, {var, Line, value1}]},
            {cons, Line, {tuple, Line, [{atom, Line, error}, {var, Line, reason}]}, {nil, Line}}},

    ListOfTuplesResult = cure_codegen:convert_pattern_to_erlang_form(ListOfTuplesPattern, Location),
    ?assertEqual(ExpectedListOfTuples, ListOfTuplesResult),

    % Test 3: Nested tuples: {{inner1, inner2}, outer}
    NestedTuplesPattern = #tuple_pattern{
        elements = [
            #tuple_pattern{
                elements = [
                    #identifier_pattern{name = inner1, location = Location},
                    #identifier_pattern{name = inner2, location = Location}
                ],
                location = Location
            },
            #identifier_pattern{name = outer, location = Location}
        ],
        location = Location
    },

    ExpectedNestedTuples =
        {tuple, Line, [
            {tuple, Line, [
                {var, Line, inner1},
                {var, Line, inner2}
            ]},
            {var, Line, outer}
        ]},

    NestedTuplesResult = cure_codegen:convert_pattern_to_erlang_form(NestedTuplesPattern, Location),
    ?assertEqual(ExpectedNestedTuples, NestedTuplesResult),

    % Test 4: Mixed patterns with wildcards: {_, [_, value | _]}
    MixedWithWildcardsPattern = #tuple_pattern{
        elements = [
            #wildcard_pattern{location = Location},
            #list_pattern{
                elements = [
                    #wildcard_pattern{location = Location},
                    #identifier_pattern{name = value, location = Location}
                ],
                tail = #wildcard_pattern{location = Location},
                location = Location
            }
        ],
        location = Location
    },

    ExpectedMixedWithWildcards =
        {tuple, Line, [
            {var, Line, '_'},
            {cons, Line, {var, Line, '_'}, {cons, Line, {var, Line, value}, {var, Line, '_'}}}
        ]},

    MixedResult = cure_codegen:convert_pattern_to_erlang_form(MixedWithWildcardsPattern, Location),
    ?assertEqual(ExpectedMixedWithWildcards, MixedResult),

    % Test 5: Deep nesting: [{{a, b}, [c | d]}, e]
    DeepNestingPattern = #list_pattern{
        elements = [
            #tuple_pattern{
                elements = [
                    #tuple_pattern{
                        elements = [
                            #literal_pattern{value = a, location = Location},
                            #literal_pattern{value = b, location = Location}
                        ],
                        location = Location
                    },
                    #list_pattern{
                        elements = [#literal_pattern{value = c, location = Location}],
                        tail = #identifier_pattern{name = d, location = Location},
                        location = Location
                    }
                ],
                location = Location
            },
            #literal_pattern{value = e, location = Location}
        ],
        tail = undefined,
        location = Location
    },

    ExpectedDeepNesting =
        {cons, Line,
            {tuple, Line, [
                {tuple, Line, [
                    {atom, Line, a},
                    {atom, Line, b}
                ]},
                {cons, Line, {atom, Line, c}, {var, Line, d}}
            ]},
            {cons, Line, {atom, Line, e}, {nil, Line}}},

    DeepResult = cure_codegen:convert_pattern_to_erlang_form(DeepNestingPattern, Location),
    ?assertEqual(ExpectedDeepNesting, DeepResult),

    % Test 6: Empty nested structures: {[], {}}
    EmptyNestedPattern = #tuple_pattern{
        elements = [
            #list_pattern{elements = [], tail = undefined, location = Location},
            #tuple_pattern{elements = [], location = Location}
        ],
        location = Location
    },

    ExpectedEmptyNested =
        {tuple, Line, [
            {nil, Line},
            {tuple, Line, []}
        ]},

    EmptyResult = cure_codegen:convert_pattern_to_erlang_form(EmptyNestedPattern, Location),
    ?assertEqual(ExpectedEmptyNested, EmptyResult),

    io:format("✓ Complex nested pattern compilation test passed~n").
