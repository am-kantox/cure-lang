%% Cure Programming Language - Vector Literal Tests
-module(vector_literal_test).

-export([
    run/0,
    test_lexer_vector_delimiters/0,
    test_parser_empty_vector/0,
    test_parser_single_element/0,
    test_parser_multiple_elements/0,
    test_parser_nested_vectors/0,
    test_parser_vector_with_expressions/0
]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").

%% Run all tests
run() ->
    io:format("Running vector literal tests...~n"),
    test_lexer_vector_delimiters(),
    test_parser_empty_vector(),
    test_parser_single_element(),
    test_parser_multiple_elements(),
    test_parser_nested_vectors(),
    test_parser_vector_with_expressions(),
    io:format("All vector literal tests passed!~n").

%% Test that lexer recognizes vector delimiters
test_lexer_vector_delimiters() ->
    % UTF-8 encoding of ‹ (U+2039) and › (U+203A)
    % Using byte values instead of Unicode literals for portability

    % ‹› in UTF-8
    Code = <<226, 128, 185, 226, 128, 186>>,
    {ok, Tokens} = cure_lexer:tokenize(Code),

    ?assertEqual(2, length(Tokens)),
    [Open, Close] = Tokens,
    ?assertEqual(vector_open, cure_lexer:token_type(Open)),
    ?assertEqual(vector_close, cure_lexer:token_type(Close)),

    io:format("✓ Lexer vector delimiters test passed~n").

%% Test parsing an empty vector ‹›
test_parser_empty_vector() ->
    % Since this is just an expression, not a complete program, we need to parse it
    % as an expression. For now, let's test it in a context like a function
    % UTF-8: def test() = ‹›
    FuncCode = <<"def test() = ", 226, 128, 185, 226, 128, 186>>,
    {ok, FuncTokens} = cure_lexer:tokenize(FuncCode),
    {ok, AST} = cure_parser:parse(FuncTokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,
    ?assertMatch(#function_def{name = test}, FunctionDef),

    % Get the first clause's body
    [Clause] = FunctionDef#function_def.clauses,
    Body = Clause#function_clause.body,

    ?assertMatch(#vector_expr{}, Body),
    VectorExpr = Body,
    ?assertEqual([], VectorExpr#vector_expr.elements),

    io:format("✓ Empty vector parsing test passed~n").

%% Test parsing a vector with a single element ‹42›
test_parser_single_element() ->
    % UTF-8: def test() = ‹42›
    Code = <<"def test() = ", 226, 128, 185, "42", 226, 128, 186>>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,
    [Clause] = FunctionDef#function_def.clauses,
    Body = Clause#function_clause.body,

    ?assertMatch(#vector_expr{}, Body),
    VectorExpr = Body,
    ?assertEqual(1, length(VectorExpr#vector_expr.elements)),

    [Element] = VectorExpr#vector_expr.elements,
    ?assertMatch(#literal_expr{value = 42}, Element),

    io:format("✓ Single element vector parsing test passed~n").

%% Test parsing a vector with multiple elements ‹1, 2, 3›
test_parser_multiple_elements() ->
    % UTF-8: def test() = ‹1, 2, 3›
    Code = <<"def test() = ", 226, 128, 185, "1, 2, 3", 226, 128, 186>>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,
    [Clause] = FunctionDef#function_def.clauses,
    Body = Clause#function_clause.body,

    ?assertMatch(#vector_expr{}, Body),
    VectorExpr = Body,
    ?assertEqual(3, length(VectorExpr#vector_expr.elements)),

    [E1, E2, E3] = VectorExpr#vector_expr.elements,
    ?assertMatch(#literal_expr{value = 1}, E1),
    ?assertMatch(#literal_expr{value = 2}, E2),
    ?assertMatch(#literal_expr{value = 3}, E3),

    io:format("✓ Multiple elements vector parsing test passed~n").

%% Test parsing nested vectors ‹1, ‹2, 3›, 4›
test_parser_nested_vectors() ->
    % UTF-8: def test() = ‹1, ‹2, 3›, 4›
    Code =
        <<"def test() = ", 226, 128, 185, "1, ", 226, 128, 185, "2, 3", 226, 128, 186, ", 4", 226,
            128, 186>>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,
    [Clause] = FunctionDef#function_def.clauses,
    Body = Clause#function_clause.body,

    ?assertMatch(#vector_expr{}, Body),
    VectorExpr = Body,
    ?assertEqual(3, length(VectorExpr#vector_expr.elements)),

    [E1, E2, E3] = VectorExpr#vector_expr.elements,
    ?assertMatch(#literal_expr{value = 1}, E1),
    % Nested vector
    ?assertMatch(#vector_expr{}, E2),
    ?assertMatch(#literal_expr{value = 4}, E3),

    % Check nested vector elements
    NestedVector = E2,
    ?assertEqual(2, length(NestedVector#vector_expr.elements)),
    [N1, N2] = NestedVector#vector_expr.elements,
    ?assertMatch(#literal_expr{value = 2}, N1),
    ?assertMatch(#literal_expr{value = 3}, N2),

    io:format("✓ Nested vectors parsing test passed~n").

%% Test parsing a vector with expressions ‹x + 1, y * 2›
test_parser_vector_with_expressions() ->
    % UTF-8: def test(x: Int, y: Int) = ‹x + 1, y * 2›
    Code = <<"def test(x: Int, y: Int) = ", 226, 128, 185, "x + 1, y * 2", 226, 128, 186>>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,
    [Clause] = FunctionDef#function_def.clauses,
    Body = Clause#function_clause.body,

    ?assertMatch(#vector_expr{}, Body),
    VectorExpr = Body,
    ?assertEqual(2, length(VectorExpr#vector_expr.elements)),

    [E1, E2] = VectorExpr#vector_expr.elements,
    ?assertMatch(#binary_op_expr{op = '+'}, E1),
    ?assertMatch(#binary_op_expr{op = '*'}, E2),

    io:format("✓ Vector with expressions parsing test passed~n").
