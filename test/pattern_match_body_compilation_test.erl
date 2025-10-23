%% Pattern Match Body Compilation Tests
-module(pattern_match_body_compilation_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").

%% Run all pattern match body compilation tests
run() ->
    cure_utils:debug("Running Pattern Match Body Compilation tests...~n"),
    test_identifier_expr_in_pattern_match_body(),
    test_empty_list_pattern_conversion(),
    test_fixed_length_list_pattern_conversion(),
    test_head_tail_list_pattern_conversion(),
    test_tuple_pattern_conversion(),
    cure_utils:debug("All pattern match body compilation tests passed!~n").

%% Test 1: Handle identifier_expr in pattern match body compilation
test_identifier_expr_in_pattern_match_body() ->
    cure_utils:debug("Testing identifier_expr in pattern match body...~n"),

    % Create test location
    Location = #location{line = 1, column = 1, file = "test"},

    % Create identifier expression for pattern match body
    IdentifierExpr = #identifier_expr{
        name = variable_name,
        location = Location
    },

    % Test convert_body_expression_to_erlang/2 function
    Result = cure_codegen:convert_body_expression_to_erlang(IdentifierExpr, Location),

    % Verify the result is correct Erlang form
    ExpectedForm = {var, 1, variable_name},
    ?assertMatch({ok, ExpectedForm}, Result),

    % Test within actual pattern match compilation context
    PatternClause = #match_clause{
        pattern = #identifier_pattern{name = x, location = Location},
        guard = undefined,
        body = IdentifierExpr,
        location = Location
    },

    % Test that pattern match compilation handles identifier_expr properly
    State = cure_codegen:new_state(),
    {CaseClauses, _} = cure_codegen:compile_patterns_to_case_clauses([PatternClause], State),

    ?assertEqual(1, length(CaseClauses)),
    [CaseClause] = CaseClauses,

    % Extract the body from the case clause
    {clause, _, [_Pattern], [], Body} = CaseClause,
    ?assertEqual([ExpectedForm], Body),

    cure_utils:debug("✓ identifier_expr pattern match body test passed~n").

%% Test 2: Correctly convert empty list patterns to Erlang forms
test_empty_list_pattern_conversion() ->
    cure_utils:debug("Testing empty list pattern conversion...~n"),

    % Test empty list pattern []
    Line = 1,
    EmptyListResult = cure_codegen:convert_list_pattern_to_erlang_form([], undefined, Line),

    % Empty list should convert to {nil, Line}
    ?assertEqual({nil, Line}, EmptyListResult),

    % Test within list_pattern record context
    Location = #location{line = Line, column = 1, file = "test"},
    EmptyListPattern = #list_pattern{
        elements = [],
        tail = undefined,
        location = Location
    },

    ErlangPattern = cure_codegen:convert_pattern_to_erlang_form(EmptyListPattern, Location),
    ?assertEqual({nil, Line}, ErlangPattern),

    cure_utils:debug("✓ Empty list pattern conversion test passed~n").

%% Test 3: Correctly convert fixed-length list patterns to Erlang forms
test_fixed_length_list_pattern_conversion() ->
    cure_utils:debug("Testing fixed-length list pattern conversion...~n"),

    Location = #location{line = 1, column = 1, file = "test"},
    Line = 1,

    % Create test patterns for list elements
    Elements = [
        #literal_pattern{value = 1, location = Location},
        #literal_pattern{value = 2, location = Location},
        #literal_pattern{value = 3, location = Location}
    ],

    % Test convert_list_pattern_to_erlang_form with elements but no tail
    Result = cure_codegen:convert_list_pattern_to_erlang_form(Elements, undefined, Line),

    % Should produce nested cons structure: [1 | [2 | [3 | []]]]
    % Which is: {cons, Line, {integer, Line, 1}, {cons, Line, {integer, Line, 2}, {cons, Line, {integer, Line, 3}, {nil, Line}}}}
    ExpectedForm =
        {cons, Line, {integer, Line, 1},
            {cons, Line, {integer, Line, 2}, {cons, Line, {integer, Line, 3}, {nil, Line}}}},
    ?assertEqual(ExpectedForm, Result),

    % Test within list_pattern record context
    ListPattern = #list_pattern{
        elements = Elements,
        tail = undefined,
        location = Location
    },

    ErlangPattern = cure_codegen:convert_pattern_to_erlang_form(ListPattern, Location),
    ?assertEqual(ExpectedForm, ErlangPattern),

    cure_utils:debug("✓ Fixed-length list pattern conversion test passed~n").

%% Test 4: Correctly convert head-tail list patterns to Erlang forms
test_head_tail_list_pattern_conversion() ->
    cure_utils:debug("Testing head-tail list pattern conversion...~n"),

    Location = #location{line = 1, column = 1, file = "test"},
    Line = 1,

    % Test simple head-tail pattern [h | t]
    HeadElement = #identifier_pattern{name = h, location = Location},
    TailPattern = #identifier_pattern{name = t, location = Location},

    Result1 = cure_codegen:convert_list_pattern_to_erlang_form([HeadElement], TailPattern, Line),

    % Should produce: {cons, Line, {var, Line, h}, {var, Line, t}}
    ExpectedForm1 = {cons, Line, {var, Line, h}, {var, Line, t}},
    ?assertEqual(ExpectedForm1, Result1),

    % Test multi-element head-tail pattern [a, b | t]
    Elements = [
        #literal_pattern{value = a, location = Location},
        #literal_pattern{value = b, location = Location}
    ],

    Result2 = cure_codegen:convert_list_pattern_to_erlang_form(Elements, TailPattern, Line),

    % Should produce: {cons, Line, {atom, Line, a}, {cons, Line, {atom, Line, b}, {var, Line, t}}}
    ExpectedForm2 = {cons, Line, {atom, Line, a}, {cons, Line, {atom, Line, b}, {var, Line, t}}},
    ?assertEqual(ExpectedForm2, Result2),

    % Test within list_pattern record context
    ListPattern = #list_pattern{
        elements = Elements,
        tail = TailPattern,
        location = Location
    },

    ErlangPattern = cure_codegen:convert_pattern_to_erlang_form(ListPattern, Location),
    ?assertEqual(ExpectedForm2, ErlangPattern),

    % Test edge case: empty head with just tail
    Result3 = cure_codegen:convert_list_pattern_to_erlang_form([], TailPattern, Line),
    % Should just return the tail pattern
    ExpectedForm3 = {var, Line, t},
    ?assertEqual(ExpectedForm3, Result3),

    cure_utils:debug("✓ Head-tail list pattern conversion test passed~n").

%% Test 5: Correctly convert tuple patterns to Erlang forms
test_tuple_pattern_conversion() ->
    cure_utils:debug("Testing tuple pattern conversion...~n"),

    Location = #location{line = 1, column = 1, file = "test"},
    Line = 1,

    % Test empty tuple pattern {}
    EmptyTuplePattern = #tuple_pattern{
        elements = [],
        location = Location
    },

    EmptyResult = cure_codegen:convert_pattern_to_erlang_form(EmptyTuplePattern, Location),
    ?assertEqual({tuple, Line, []}, EmptyResult),

    % Test single-element tuple pattern {x}
    SingleElement = [#identifier_pattern{name = x, location = Location}],
    SingleTuplePattern = #tuple_pattern{
        elements = SingleElement,
        location = Location
    },

    SingleResult = cure_codegen:convert_pattern_to_erlang_form(SingleTuplePattern, Location),
    ExpectedSingle = {tuple, Line, [{var, Line, x}]},
    ?assertEqual(ExpectedSingle, SingleResult),

    % Test multi-element tuple pattern {1, "hello", variable}
    Elements = [
        #literal_pattern{value = 1, location = Location},
        #literal_pattern{value = "hello", location = Location},
        #identifier_pattern{name = variable, location = Location}
    ],

    TuplePattern = #tuple_pattern{
        elements = Elements,
        location = Location
    },

    Result = cure_codegen:convert_pattern_to_erlang_form(TuplePattern, Location),

    % Should produce: {tuple, Line, [{integer, Line, 1}, {string, Line, "hello"}, {var, Line, variable}]}
    ExpectedForm =
        {tuple, Line, [
            {integer, Line, 1},
            {string, Line, "hello"},
            {var, Line, variable}
        ]},
    ?assertEqual(ExpectedForm, Result),

    % Test nested tuple pattern {{a, b}, c}
    NestedElements = [
        #tuple_pattern{
            elements = [
                #literal_pattern{value = a, location = Location},
                #literal_pattern{value = b, location = Location}
            ],
            location = Location
        },
        #literal_pattern{value = c, location = Location}
    ],

    NestedTuplePattern = #tuple_pattern{
        elements = NestedElements,
        location = Location
    },

    NestedResult = cure_codegen:convert_pattern_to_erlang_form(NestedTuplePattern, Location),

    % Should produce nested tuple structure
    ExpectedNested =
        {tuple, Line, [
            {tuple, Line, [
                {atom, Line, a},
                {atom, Line, b}
            ]},
            {atom, Line, c}
        ]},
    ?assertEqual(ExpectedNested, NestedResult),

    cure_utils:debug("✓ Tuple pattern conversion test passed~n").
