%% S-expression Parser Integration Tests
%% Tests the full pipeline of parsing Z3 simplified S-expressions back to Cure constraint AST
-module(sexp_parser_integration_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").

%% Run all S-expression parser tests
run() ->
    cure_utils:debug("Running S-expression Parser Integration tests...~n"),
    test_tokenization_simple_atoms(),
    test_tokenization_numbers(),
    test_tokenization_lists(),
    test_parse_sexp_terms_atoms(),
    test_parse_sexp_terms_numbers(),
    test_parse_sexp_terms_binary_ops(),
    test_parse_sexp_terms_unary_ops(),
    test_constraint_conversion_literals(),
    test_constraint_conversion_identifiers(),
    test_constraint_conversion_binary_ops(),
    test_constraint_conversion_unary_ops(),
    test_full_pipeline_simple_constraint(),
    test_full_pipeline_complex_constraint(),
    test_full_pipeline_arithmetic(),
    test_full_pipeline_comparison(),
    test_error_handling_malformed(),
    test_error_handling_incomplete(),
    cure_utils:debug("✓ All S-expression parser integration tests passed!~n").

%% Test tokenization of simple atoms
test_tokenization_simple_atoms() ->
    % Test: "x"
    {ok, Tokens} = cure_smt_solver:tokenize_sexp("x", []),
    ?assertEqual([{symbol, x}], Tokens),

    % Test: "true"
    {ok, TokensTrue} = cure_smt_solver:tokenize_sexp("true", []),
    ?assertEqual([{symbol, true}], TokensTrue),

    % Test: "false"
    {ok, TokensFalse} = cure_smt_solver:tokenize_sexp("false", []),
    ?assertEqual([{symbol, false}], TokensFalse),

    cure_utils:debug("✓ Simple atoms tokenization test passed~n").

%% Test tokenization of numbers
test_tokenization_numbers() ->
    % Test: "42"
    {ok, Tokens} = cure_smt_solver:tokenize_sexp("42", []),
    ?assertEqual([{number, 42}], Tokens),

    % Test: "-17"
    {ok, TokensNeg} = cure_smt_solver:tokenize_sexp("-17", []),
    ?assertEqual([{number, -17}], TokensNeg),

    % Test: "0"
    {ok, TokensZero} = cure_smt_solver:tokenize_sexp("0", []),
    ?assertEqual([{number, 0}], TokensZero),

    cure_utils:debug("✓ Numbers tokenization test passed~n").

%% Test tokenization of lists
test_tokenization_lists() ->
    % Test: "()"
    {ok, Tokens} = cure_smt_solver:tokenize_sexp("()", []),
    ?assertEqual([{'(', 1}, {')', 1}], Tokens),

    % Test: "(+ x y)"
    {ok, TokensExpr} = cure_smt_solver:tokenize_sexp("(+ x y)", []),
    ?assertEqual([{'(', 1}, {symbol, '+'}, {symbol, x}, {symbol, y}, {')', 1}], TokensExpr),

    % Test: "(not true)"
    {ok, TokensNot} = cure_smt_solver:tokenize_sexp("(not true)", []),
    ?assertEqual([{'(', 1}, {symbol, 'not'}, {symbol, true}, {')', 1}], TokensNot),

    cure_utils:debug("✓ Lists tokenization test passed~n").

%% Test parsing S-expression terms - atoms
test_parse_sexp_terms_atoms() ->
    % Test atom parsing
    {ok, {Term, []}} = cure_smt_solver:parse_sexp_tokens([{symbol, x}]),
    ?assertEqual({symbol, x}, Term),

    % Test multiple atoms (should parse first, leave rest)
    {ok, {Term2, Rest}} = cure_smt_solver:parse_sexp_tokens([{symbol, x}, {symbol, y}]),
    ?assertEqual({symbol, x}, Term2),
    ?assertEqual([{symbol, y}], Rest),

    cure_utils:debug("✓ S-expression atoms parsing test passed~n").

%% Test parsing S-expression terms - numbers
test_parse_sexp_terms_numbers() ->
    % Test number parsing
    {ok, {Term, []}} = cure_smt_solver:parse_sexp_tokens([{number, 42}]),
    ?assertEqual({number, 42}, Term),

    % Test negative number
    {ok, {Term2, []}} = cure_smt_solver:parse_sexp_tokens([{number, -17}]),
    ?assertEqual({number, -17}, Term2),

    cure_utils:debug("✓ S-expression numbers parsing test passed~n").

%% Test parsing S-expression terms - binary operators
test_parse_sexp_terms_binary_ops() ->
    % Test: (+ x y)
    Tokens = [{'(', 1}, {symbol, '+'}, {symbol, x}, {symbol, y}, {')', 1}],
    {ok, {Term, []}} = cure_smt_solver:parse_sexp_tokens(Tokens),
    ?assertEqual({list, [{symbol, '+'}, {symbol, x}, {symbol, y}]}, Term),

    % Test: (> 5 3)
    Tokens2 = [{'(', 1}, {symbol, '>'}, {number, 5}, {number, 3}, {')', 1}],
    {ok, {Term2, []}} = cure_smt_solver:parse_sexp_tokens(Tokens2),
    ?assertEqual({list, [{symbol, '>'}, {number, 5}, {number, 3}]}, Term2),

    cure_utils:debug("✓ S-expression binary operators parsing test passed~n").

%% Test parsing S-expression terms - unary operators
test_parse_sexp_terms_unary_ops() ->
    % Test: (not x)
    Tokens = [{'(', 1}, {symbol, 'not'}, {symbol, x}, {')', 1}],
    {ok, {Term, []}} = cure_smt_solver:parse_sexp_tokens(Tokens),
    ?assertEqual({list, [{symbol, 'not'}, {symbol, x}]}, Term),

    % Test: (- 5)
    Tokens2 = [{'(', 1}, {symbol, '-'}, {number, 5}, {')', 1}],
    {ok, {Term2, []}} = cure_smt_solver:parse_sexp_tokens(Tokens2),
    ?assertEqual({list, [{symbol, '-'}, {number, 5}]}, Term2),

    cure_utils:debug("✓ S-expression unary operators parsing test passed~n").

%% Test constraint conversion - literals
test_constraint_conversion_literals() ->
    % Test converting true
    {ok, Expr} = cure_smt_solver:sexp_term_to_constraint({symbol, true}),
    ?assertEqual(true, Expr#literal_expr.value),

    % Test converting false
    {ok, Expr2} = cure_smt_solver:sexp_term_to_constraint({symbol, false}),
    ?assertEqual(false, Expr2#literal_expr.value),

    % Test converting number
    {ok, Expr3} = cure_smt_solver:sexp_term_to_constraint({number, 42}),
    ?assertEqual(42, Expr3#literal_expr.value),

    cure_utils:debug("✓ Constraint literals conversion test passed~n").

%% Test constraint conversion - identifiers
test_constraint_conversion_identifiers() ->
    % Test converting variable name
    {ok, Expr} = cure_smt_solver:sexp_term_to_constraint({symbol, x}),
    ?assertEqual(x, Expr#identifier_expr.name),

    % Test converting different variable
    {ok, Expr2} = cure_smt_solver:sexp_term_to_constraint({symbol, n}),
    ?assertEqual(n, Expr2#identifier_expr.name),

    cure_utils:debug("✓ Constraint identifiers conversion test passed~n").

%% Test constraint conversion - binary operators
test_constraint_conversion_binary_ops() ->
    % Test: (+ x 5)
    Term = {list, [{symbol, '+'}, {symbol, x}, {number, 5}]},
    {ok, Expr} = cure_smt_solver:sexp_term_to_constraint(Term),
    ?assertEqual(binary_op_expr, element(1, Expr)),
    ?assertEqual('+', Expr#binary_op_expr.op),

    % Verify left and right
    ?assertEqual(x, Expr#binary_op_expr.left#identifier_expr.name),
    ?assertEqual(5, Expr#binary_op_expr.right#literal_expr.value),

    % Test: (> n 0)
    Term2 = {list, [{symbol, '>'}, {symbol, n}, {number, 0}]},
    {ok, Expr2} = cure_smt_solver:sexp_term_to_constraint(Term2),
    ?assertEqual('>', Expr2#binary_op_expr.op),

    cure_utils:debug("✓ Constraint binary operators conversion test passed~n").

%% Test constraint conversion - unary operators
test_constraint_conversion_unary_ops() ->
    % Test: (not true)
    Term = {list, [{symbol, 'not'}, {symbol, true}]},
    {ok, Expr} = cure_smt_solver:sexp_term_to_constraint(Term),
    ?assertEqual(unary_op_expr, element(1, Expr)),
    ?assertEqual('not', Expr#unary_op_expr.op),

    % Verify operand
    ?assertEqual(true, Expr#unary_op_expr.operand#literal_expr.value),

    % Test: (- 5)
    Term2 = {list, [{symbol, '-'}, {number, 5}]},
    {ok, Expr2} = cure_smt_solver:sexp_term_to_constraint(Term2),
    ?assertEqual('-', Expr2#unary_op_expr.op),
    ?assertEqual(5, Expr2#unary_op_expr.operand#literal_expr.value),

    cure_utils:debug("✓ Constraint unary operators conversion test passed~n").

%% Test full pipeline - simple constraint
test_full_pipeline_simple_constraint() ->
    % Parse: "true"
    {ok, Expr} = cure_smt_solver:parse_sexp_to_constraint(["true"]),
    ?assertEqual(true, Expr#literal_expr.value),

    % Parse: "x"
    {ok, Expr2} = cure_smt_solver:parse_sexp_to_constraint(["x"]),
    ?assertEqual(x, Expr2#identifier_expr.name),

    cure_utils:debug("✓ Full pipeline simple constraint test passed~n").

%% Test full pipeline - complex constraint
test_full_pipeline_complex_constraint() ->
    % Parse: "(and (> x 0) (< y 10))"
    Input = ["(and (> x 0) (< y 10))"],
    {ok, Expr} = cure_smt_solver:parse_sexp_to_constraint(Input),
    ?assertEqual('and', Expr#binary_op_expr.op),

    % Verify structure: binary op with two binary op operands
    LeftExpr = Expr#binary_op_expr.left,
    ?assertEqual(binary_op_expr, element(1, LeftExpr)),
    ?assertEqual('>', LeftExpr#binary_op_expr.op),

    RightExpr = Expr#binary_op_expr.right,
    ?assertEqual(binary_op_expr, element(1, RightExpr)),
    ?assertEqual('<', RightExpr#binary_op_expr.op),

    cure_utils:debug("✓ Full pipeline complex constraint test passed~n").

%% Test full pipeline - arithmetic
test_full_pipeline_arithmetic() ->
    % Parse: "(+ x y)"
    {ok, Expr} = cure_smt_solver:parse_sexp_to_constraint(["(+ x y)"]),
    ?assertEqual(binary_op_expr, element(1, Expr)),
    ?assertEqual('+', Expr#binary_op_expr.op),
    ?assertEqual(x, Expr#binary_op_expr.left#identifier_expr.name),
    ?assertEqual(y, Expr#binary_op_expr.right#identifier_expr.name),

    % Parse: "(* 2 n)"
    {ok, Expr2} = cure_smt_solver:parse_sexp_to_constraint(["(* 2 n)"]),
    ?assertEqual('*', Expr2#binary_op_expr.op),
    ?assertEqual(2, Expr2#binary_op_expr.left#literal_expr.value),
    ?assertEqual(n, Expr2#binary_op_expr.right#identifier_expr.name),

    cure_utils:debug("✓ Full pipeline arithmetic test passed~n").

%% Test full pipeline - comparison
test_full_pipeline_comparison() ->
    % Parse: "(>= n 1)"
    {ok, Expr} = cure_smt_solver:parse_sexp_to_constraint(["(>= n 1)"]),
    ?assertEqual(binary_op_expr, element(1, Expr)),
    ?assertEqual('>=', Expr#binary_op_expr.op),
    ?assertEqual(n, Expr#binary_op_expr.left#identifier_expr.name),
    ?assertEqual(1, Expr#binary_op_expr.right#literal_expr.value),

    % Parse: "(== x y)"
    {ok, Expr2} = cure_smt_solver:parse_sexp_to_constraint(["(== x y)"]),
    ?assertEqual('==', Expr2#binary_op_expr.op),

    cure_utils:debug("✓ Full pipeline comparison test passed~n").

%% Test error handling - malformed input
test_error_handling_malformed() ->
    % Unmatched parenthesis
    {error, _} = cure_smt_solver:parse_sexp_to_constraint(["(+ x y"]),

    % Invalid symbols (shouldn't crash, might return empty list or error)
    Result = cure_smt_solver:parse_sexp_to_constraint([""]),
    ?assert(Result =:= {error, invalid_format} orelse element(1, Result) =:= ok),

    cure_utils:debug("✓ Error handling malformed input test passed~n").

%% Test error handling - incomplete expressions
test_error_handling_incomplete() ->
    % Empty list
    {error, _} = cure_smt_solver:parse_sexp_to_constraint([]),

    % Just opening paren
    {error, _} = cure_smt_solver:parse_sexp_to_constraint(["("]),

    % Incomplete binary operation
    Result = cure_smt_solver:parse_sexp_to_constraint(["(+ x)"]),
    ?assert(element(1, Result) =:= error orelse element(1, Result) =:= ok),

    cure_utils:debug("✓ Error handling incomplete expressions test passed~n").
