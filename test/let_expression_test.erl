%% Cure Programming Language - Let Expression Parser Tests
-module(let_expression_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").

%% Helper function to tokenize and parse a let expression
parse_let_expression_from_code(Code) ->
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, [AST]} = cure_parser:parse(Tokens),
    AST.

%% Run all tests
run() ->
    io:format("Running Let Expression parser tests...~n"),
    test_explicit_let_in_syntax(),
    test_implicit_let_with_continuation(),
    test_implicit_let_without_body(),
    test_is_let_body_continuation_valid_tokens(),
    test_is_let_body_continuation_terminators(),
    test_nested_let_expressions(),
    test_complex_let_expressions(),
    io:format("All Let Expression tests passed!~n").

%% Test Case 1: parse_let_expression correctly parses explicit let...in syntax
test_explicit_let_in_syntax() ->
    io:format("Testing explicit let...in syntax...~n"),

    % Test simple let...in with identifier body
    Code1 = <<"def test() = let x = 42 in x">>,
    FunDef1 = parse_let_expression_from_code(Code1),
    ?assertMatch(#function_def{}, FunDef1),

    LetExpr1 = FunDef1#function_def.body,
    ?assertMatch(#let_expr{}, LetExpr1),
    ?assertEqual(1, length(LetExpr1#let_expr.bindings)),

    [Binding1] = LetExpr1#let_expr.bindings,
    ?assertMatch(#binding{}, Binding1),
    ?assertMatch(#identifier_pattern{name = x}, Binding1#binding.pattern),
    ?assertMatch(#literal_expr{value = 42}, Binding1#binding.value),
    ?assertMatch(#identifier_expr{name = x}, LetExpr1#let_expr.body),

    % Test let...in with arithmetic body
    Code2 = <<"def test() = let y = 10 in y + 5">>,
    FunDef2 = parse_let_expression_from_code(Code2),
    LetExpr2 = FunDef2#function_def.body,
    ?assertMatch(#let_expr{}, LetExpr2),
    ?assertMatch(#binary_op_expr{op = '+'}, LetExpr2#let_expr.body),

    io:format("✓ Explicit let...in syntax test passed~n").

%% Test Case 2: parse_let_expression correctly parses implicit syntax with body continuation
test_implicit_let_with_continuation() ->
    io:format("Testing implicit let syntax with body continuation...~n"),

    % Test implicit let with identifier continuation
    Code1 = <<"def test() = let x = 42 x">>,
    FunDef1 = parse_let_expression_from_code(Code1),
    LetExpr1 = FunDef1#function_def.body,
    ?assertMatch(#let_expr{}, LetExpr1),
    ?assertMatch(#identifier_expr{name = x}, LetExpr1#let_expr.body),

    % Test implicit let with number continuation
    Code2 = <<"def test() = let x = 10 42">>,
    FunDef2 = parse_let_expression_from_code(Code2),
    LetExpr2 = FunDef2#function_def.body,
    ?assertMatch(#let_expr{}, LetExpr2),
    ?assertMatch(#literal_expr{value = 42}, LetExpr2#let_expr.body),

    % Test implicit let with parenthesized expression continuation
    Code3 = <<"def test() = let x = 5 (x + 1)">>,
    FunDef3 = parse_let_expression_from_code(Code3),
    LetExpr3 = FunDef3#function_def.body,
    ?assertMatch(#let_expr{}, LetExpr3),
    ?assertMatch(#binary_op_expr{op = '+'}, LetExpr3#let_expr.body),

    % Test implicit let with list continuation
    Code4 = <<"def test() = let x = 1 [x, 2, 3]">>,
    FunDef4 = parse_let_expression_from_code(Code4),
    LetExpr4 = FunDef4#function_def.body,
    ?assertMatch(#let_expr{}, LetExpr4),
    ?assertMatch(#list_expr{}, LetExpr4#let_expr.body),

    % Test implicit let with tuple continuation
    Code5 = <<"def test() = let x = 1 {x, 2}">>,
    FunDef5 = parse_let_expression_from_code(Code5),
    LetExpr5 = FunDef5#function_def.body,
    ?assertMatch(#let_expr{}, LetExpr5),
    ?assertMatch(#tuple_expr{}, LetExpr5#let_expr.body),

    % Test implicit let with string continuation
    Code6 = <<"def test() = let x = 1 \"hello\"">>,
    FunDef6 = parse_let_expression_from_code(Code6),
    LetExpr6 = FunDef6#function_def.body,
    ?assertMatch(#let_expr{}, LetExpr6),
    ?assertMatch(#literal_expr{value = "hello"}, LetExpr6#let_expr.body),

    io:format("✓ Implicit let with body continuation test passed~n").

%% Test Case 3: parse_let_expression handles no explicit 'in' and no valid body
test_implicit_let_without_body() ->
    io:format("Testing implicit let syntax without body...~n"),

    % Test let without body - should use variable as body
    Code1 = <<"def test() = let x = 42">>,
    FunDef1 = parse_let_expression_from_code(Code1),
    LetExpr1 = FunDef1#function_def.body,
    ?assertMatch(#let_expr{}, LetExpr1),

    [Binding1] = LetExpr1#let_expr.bindings,
    ?assertMatch(#identifier_pattern{name = x}, Binding1#binding.pattern),
    ?assertMatch(#literal_expr{value = 42}, Binding1#binding.value),
    % Body should be the bound variable when no explicit body
    ?assertMatch(#identifier_expr{name = x}, LetExpr1#let_expr.body),

    io:format("✓ Implicit let without body test passed~n").

%% Test Case 4: is_let_body_continuation correctly identifies valid continuation tokens
test_is_let_body_continuation_valid_tokens() ->
    io:format("Testing is_let_body_continuation for valid tokens...~n"),

    % Test implicit let expressions with different valid continuation tokens
    % These should all parse successfully as implicit let expressions

    % Test with identifier continuation
    Code1 = <<"def test() = let x = 42 y">>,
    ?assertMatch(#function_def{body = #let_expr{}}, parse_let_expression_from_code(Code1)),

    % Test with number continuation
    Code2 = <<"def test() = let x = 42 100">>,
    ?assertMatch(#function_def{body = #let_expr{}}, parse_let_expression_from_code(Code2)),

    % Test with parenthesized expression continuation
    Code3 = <<"def test() = let x = 42 (x + 1)">>,
    ?assertMatch(#function_def{body = #let_expr{}}, parse_let_expression_from_code(Code3)),

    % Test with list continuation
    Code4 = <<"def test() = let x = 42 [1, 2]">>,
    ?assertMatch(#function_def{body = #let_expr{}}, parse_let_expression_from_code(Code4)),

    % Test with tuple continuation
    Code5 = <<"def test() = let x = 42 {1, 2}">>,
    ?assertMatch(#function_def{body = #let_expr{}}, parse_let_expression_from_code(Code5)),

    % Test with string continuation
    Code6 = <<"def test() = let x = 42 \"hello\"">>,
    ?assertMatch(#function_def{body = #let_expr{}}, parse_let_expression_from_code(Code6)),

    io:format("✓ Valid continuation tokens test passed~n").

%% Test Case 5: is_let_body_continuation correctly identifies terminator tokens
test_is_let_body_continuation_terminators() ->
    io:format("Testing is_let_body_continuation for terminators...~n"),

    % Test that let expressions properly terminate at end of function or context
    % These should parse as let expressions without explicit body

    % Test let at end of function (EOF terminator)
    Code1 = <<"def test() = let x = 42">>,
    FunDef1 = parse_let_expression_from_code(Code1),
    LetExpr1 = FunDef1#function_def.body,
    ?assertMatch(#let_expr{}, LetExpr1),
    % Should use the bound variable as the body
    ?assertMatch(#identifier_expr{name = x}, LetExpr1#let_expr.body),

    % Test let within match expression that terminates at clause boundary
    Code2 = <<"def test() = match 42 do x -> let y = x y end">>,
    FunDef2 = parse_let_expression_from_code(Code2),
    MatchExpr = FunDef2#function_def.body,
    ?assertMatch(#match_expr{}, MatchExpr),

    [Clause] = MatchExpr#match_expr.patterns,
    ?assertMatch(#match_clause{}, Clause),
    ?assertMatch(#let_expr{}, Clause#match_clause.body),

    io:format("✓ Terminator tokens test passed~n").

%% Test Case 6: Nested let expressions
test_nested_let_expressions() ->
    io:format("Testing nested let expressions...~n"),

    % Test nested let expressions
    Code1 = <<"def test() = let x = 1 in let y = 2 in x + y">>,
    FunDef1 = parse_let_expression_from_code(Code1),
    LetExpr1 = FunDef1#function_def.body,
    ?assertMatch(#let_expr{}, LetExpr1),

    % The body should be another let expression
    InnerLet = LetExpr1#let_expr.body,
    ?assertMatch(#let_expr{}, InnerLet),

    % The inner let's body should be x + y
    ?assertMatch(#binary_op_expr{op = '+'}, InnerLet#let_expr.body),

    % Test implicit nested let
    Code2 = <<"def test() = let x = 1 let y = x + 1 y * 2">>,
    FunDef2 = parse_let_expression_from_code(Code2),
    LetExpr2 = FunDef2#function_def.body,
    ?assertMatch(#let_expr{}, LetExpr2),

    % The body should be another let expression
    InnerLet2 = LetExpr2#let_expr.body,
    ?assertMatch(#let_expr{}, InnerLet2),

    io:format("✓ Nested let expressions test passed~n").

%% Test Case 7: Complex let expressions
test_complex_let_expressions() ->
    io:format("Testing complex let expressions...~n"),

    % Test let with function call value
    Code1 = <<"def test() = let result = foo(1, 2) in result + 3">>,
    FunDef1 = parse_let_expression_from_code(Code1),
    LetExpr1 = FunDef1#function_def.body,
    ?assertMatch(#let_expr{}, LetExpr1),

    [Binding1] = LetExpr1#let_expr.bindings,
    ?assertMatch(#function_call_expr{}, Binding1#binding.value),
    ?assertMatch(#binary_op_expr{op = '+'}, LetExpr1#let_expr.body),

    % Test let with complex expressions
    Code2 = <<"def test() = let x = (1 + 2) * 3 in x / 2">>,
    FunDef2 = parse_let_expression_from_code(Code2),
    LetExpr2 = FunDef2#function_def.body,
    ?assertMatch(#let_expr{}, LetExpr2),

    [Binding2] = LetExpr2#let_expr.bindings,
    ?assertMatch(#binary_op_expr{op = '*'}, Binding2#binding.value),
    ?assertMatch(#binary_op_expr{op = '/'}, LetExpr2#let_expr.body),

    io:format("✓ Complex let expressions test passed~n").
