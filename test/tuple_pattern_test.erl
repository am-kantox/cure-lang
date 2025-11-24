-module(tuple_pattern_test).
-author("Warp AI Assistant").

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").

%% ============================================================================
%% Tuple Pattern Matching Tests - Comprehensive Test Suite
%% ============================================================================

%% Test: Basic tuple pattern parsing
test_basic_tuple_pattern() ->
    % Test: {x, y}
    Code = <<"def f(): Int = match {10, 20} do {x, y} -> x + y end">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, [FuncDef]} = cure_parser:parse(Tokens),

    % Extract match expression from function body
    ?assertMatch(#function_def{}, FuncDef),
    MatchExpr = FuncDef#function_def.body,
    ?assertMatch(#match_expr{}, MatchExpr),

    % Extract tuple pattern from first clause
    [Clause] = MatchExpr#match_expr.patterns,
    Pattern = Clause#match_clause.pattern,

    % Verify tuple pattern structure
    ?assertMatch(#tuple_pattern{}, Pattern),
    TuplePattern = Pattern,
    ?assertEqual(2, length(TuplePattern#tuple_pattern.elements)),

    [Elem1, Elem2] = TuplePattern#tuple_pattern.elements,
    ?assertMatch(#identifier_pattern{name = x}, Elem1),
    ?assertMatch(#identifier_pattern{name = y}, Elem2),

    io:format("✓ Basic tuple pattern parsing test passed~n").

%% Test: Empty tuple pattern
test_empty_tuple_pattern() ->
    % Test: {}
    Code = <<"def f(): Int = match {} do {} -> 0 end">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, [FuncDef]} = cure_parser:parse(Tokens),

    MatchExpr = FuncDef#function_def.body,
    [Clause] = MatchExpr#match_expr.patterns,
    Pattern = Clause#match_clause.pattern,

    % Verify empty tuple pattern
    ?assertMatch(#tuple_pattern{}, Pattern),
    ?assertEqual(0, length(Pattern#tuple_pattern.elements)),

    io:format("✓ Empty tuple pattern test passed~n").

%% Test: Three-element tuple pattern
test_three_element_tuple() ->
    % Test: {x, y, z}
    Code = <<"def f(): Int = match {1, 2, 3} do {x, y, z} -> x + y + z end">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, [FuncDef]} = cure_parser:parse(Tokens),

    MatchExpr = FuncDef#function_def.body,
    [Clause] = MatchExpr#match_expr.patterns,
    Pattern = Clause#match_clause.pattern,

    % Verify three-element tuple
    ?assertMatch(#tuple_pattern{}, Pattern),
    ?assertEqual(3, length(Pattern#tuple_pattern.elements)),

    io:format("✓ Three-element tuple test passed~n").

%% Test: Nested tuple patterns
test_nested_tuple_pattern() ->
    % Test: {{a, b}, {c, d}}
    Code = <<"def f(): Int = match {{1, 2}, {3, 4}} do {{a, b}, {c, d}} -> a + d end">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, [FuncDef]} = cure_parser:parse(Tokens),

    MatchExpr = FuncDef#function_def.body,
    [Clause] = MatchExpr#match_expr.patterns,
    Pattern = Clause#match_clause.pattern,

    % Verify outer tuple
    ?assertMatch(#tuple_pattern{}, Pattern),
    ?assertEqual(2, length(Pattern#tuple_pattern.elements)),

    % Verify inner tuples
    [Inner1, Inner2] = Pattern#tuple_pattern.elements,
    ?assertMatch(#tuple_pattern{}, Inner1),
    ?assertMatch(#tuple_pattern{}, Inner2),
    ?assertEqual(2, length(Inner1#tuple_pattern.elements)),
    ?assertEqual(2, length(Inner2#tuple_pattern.elements)),

    io:format("✓ Nested tuple pattern test passed~n").

%% Test: Tuple with wildcard
test_tuple_with_wildcard() ->
    % Test: {x, _, z}
    Code = <<"def f(): Int = match {1, 2, 3} do {x, _, z} -> x + z end">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, [FuncDef]} = cure_parser:parse(Tokens),

    MatchExpr = FuncDef#function_def.body,
    [Clause] = MatchExpr#match_expr.patterns,
    Pattern = Clause#match_clause.pattern,

    % Verify tuple with wildcard
    ?assertMatch(#tuple_pattern{}, Pattern),
    [Elem1, Elem2, Elem3] = Pattern#tuple_pattern.elements,
    ?assertMatch(#identifier_pattern{name = x}, Elem1),
    ?assertMatch(#wildcard_pattern{}, Elem2),
    ?assertMatch(#identifier_pattern{name = z}, Elem3),

    io:format("✓ Tuple with wildcard test passed~n").

%% Test: Tuple with literal patterns
test_tuple_with_literals() ->
    % Test: {0, 0}
    Code = <<"def f(): Int = match {0, 0} do {0, 0} -> 1 _ -> 0 end">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, [FuncDef]} = cure_parser:parse(Tokens),

    MatchExpr = FuncDef#function_def.body,
    [Clause1, _Clause2] = MatchExpr#match_expr.patterns,
    Pattern = Clause1#match_clause.pattern,

    % Verify tuple with literal patterns
    ?assertMatch(#tuple_pattern{}, Pattern),
    [Elem1, Elem2] = Pattern#tuple_pattern.elements,
    ?assertMatch(#literal_pattern{value = 0}, Elem1),
    ?assertMatch(#literal_pattern{value = 0}, Elem2),

    io:format("✓ Tuple with literals test passed~n").

%% Test: Tuple pattern with guards
test_tuple_with_guards() ->
    % Test: {x, y} when x > 0
    Code = <<"def f(): Int = match {5, 10} do {x, y} when x > 0 -> x + y _ -> 0 end">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, [FuncDef]} = cure_parser:parse(Tokens),

    MatchExpr = FuncDef#function_def.body,
    [Clause1, _Clause2] = MatchExpr#match_expr.patterns,
    Pattern = Clause1#match_clause.pattern,

    % Verify tuple pattern
    ?assertMatch(#tuple_pattern{}, Pattern),

    % Verify guard exists
    Guard = Clause1#match_clause.guard,
    ?assertMatch(#binary_op_expr{op = '>'}, Guard),

    io:format("✓ Tuple with guards test passed~n").

%% Test: Tuple in function parameter
test_tuple_in_parameter() ->
    % Test: def f(point: {Int, Int})
    Code = <<"def distance(point: {Int, Int}): Int = match point do {x, y} -> x * x + y * y end">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, [FuncDef]} = cure_parser:parse(Tokens),

    % Verify function has tuple type parameter
    ?assertMatch(#function_def{name = distance}, FuncDef),
    [Param] = FuncDef#function_def.params,
    ?assertMatch(#param{name = point}, Param),

    % Verify parameter type is tuple
    ParamType = Param#param.type,
    ?assertMatch(#tuple_type{}, ParamType),

    io:format("✓ Tuple in parameter test passed~n").

%% Test: Mixed tuple and list patterns
test_mixed_tuple_list() ->
    % Test: {[h | t], x}
    Code = <<"def f(): Int = match {[1, 2], 3} do {[h | t], x} -> h + x _ -> 0 end">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, [FuncDef]} = cure_parser:parse(Tokens),

    MatchExpr = FuncDef#function_def.body,
    [Clause1, _Clause2] = MatchExpr#match_expr.patterns,
    Pattern = Clause1#match_clause.pattern,

    % Verify tuple pattern with list inside
    ?assertMatch(#tuple_pattern{}, Pattern),
    [Elem1, Elem2] = Pattern#tuple_pattern.elements,
    ?assertMatch(#list_pattern{}, Elem1),
    ?assertMatch(#identifier_pattern{name = x}, Elem2),

    % Verify list pattern details
    ListPattern = Elem1,
    ?assertEqual(1, length(ListPattern#list_pattern.elements)),
    ?assertMatch(#identifier_pattern{}, ListPattern#list_pattern.tail),

    io:format("✓ Mixed tuple/list pattern test passed~n").

%% Test: Tuple in Result/Option constructor
test_tuple_in_constructor() ->
    % Test: Ok({x, y})
    Code = <<"def f(): Int = match Ok({10, 20}) do Ok({x, y}) -> x + y Error(e) -> 0 end">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, [FuncDef]} = cure_parser:parse(Tokens),

    MatchExpr = FuncDef#function_def.body,
    [Clause1, _Clause2] = MatchExpr#match_expr.patterns,
    Pattern = Clause1#match_clause.pattern,

    % Verify constructor pattern with tuple inside
    ?assertMatch(#constructor_pattern{name = 'Ok'}, Pattern),
    [InnerPattern] = Pattern#constructor_pattern.args,
    ?assertMatch(#tuple_pattern{}, InnerPattern),

    % Verify tuple inside constructor
    ?assertEqual(2, length(InnerPattern#tuple_pattern.elements)),

    io:format("✓ Tuple in constructor test passed~n").

%% Test: Tuple compilation
test_tuple_compilation() ->
    % Create tuple expression AST: {10, 20}
    TupleExpr = #tuple_expr{
        elements = [
            #literal_expr{value = 10, location = create_location(1, 1)},
            #literal_expr{value = 20, location = create_location(1, 5)}
        ],
        location = create_location(1, 1)
    },

    % Compile tuple expression
    {Instructions, _State} = cure_codegen:compile_expression(TupleExpr),

    % Verify instructions are generated
    ?assert(length(Instructions) > 0),

    io:format("✓ Tuple compilation test passed~n").

%% Helper functions
create_location(Line, Column) ->
    #location{line = Line, column = Column}.

%% ============================================================================
%% Test Suite Entry Point
%% ============================================================================

run() ->
    io:format("~n=== Tuple Pattern Matching Tests ===~n"),
    test_basic_tuple_pattern(),
    test_empty_tuple_pattern(),
    test_three_element_tuple(),
    test_nested_tuple_pattern(),
    test_tuple_with_wildcard(),
    test_tuple_with_literals(),
    test_tuple_with_guards(),
    test_tuple_in_parameter(),
    test_mixed_tuple_list(),
    test_tuple_in_constructor(),
    test_tuple_compilation(),
    io:format("~n✓ All tuple pattern matching tests passed! (11/11)~n~n"),
    ok.
