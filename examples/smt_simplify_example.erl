#!/usr/bin/env escript
%% -*- erlang -*-
%%! -pa ../_build/ebin

%% Example demonstrating SMT constraint simplification
%% This shows how cure_smt_solver can simplify complex constraints

-include("../src/parser/cure_ast.hrl").

main(_) ->
    io:format("~n╔══════════════════════════════════════════════════════╗~n"),
    io:format("║  Cure SMT Constraint Simplification Examples        ║~n"),
    io:format("╚══════════════════════════════════════════════════════╝~n~n"),
    
    % Example 1: Arithmetic simplifications
    example_arithmetic(),
    
    % Example 2: Boolean logic simplifications
    example_boolean(),
    
    % Example 3: Complex nested expressions
    example_nested(),
    
    % Example 4: Guard optimizations
    example_guards(),
    
    io:format("~n╔══════════════════════════════════════════════════════╗~n"),
    io:format("║  All examples completed successfully!               ║~n"),
    io:format("╚══════════════════════════════════════════════════════╝~n~n"),
    ok.

%% Helper functions
lit(Value) ->
    #literal_expr{value = Value, location = #location{line = 0, column = 0, file = undefined}}.

var(Name) ->
    #identifier_expr{name = Name, location = #location{line = 0, column = 0, file = undefined}}.

binop(Op, Left, Right) ->
    #binary_op_expr{
        op = Op,
        left = Left,
        right = Right,
        location = #location{line = 0, column = 0, file = undefined}
    }.

unop(Op, Operand) ->
    #unary_op_expr{
        op = Op,
        operand = Operand,
        location = #location{line = 0, column = 0, file = undefined}
    }.

format_expr(#literal_expr{value = V}) ->
    io_lib:format("~p", [V]);
format_expr(#identifier_expr{name = N}) ->
    io_lib:format("~p", [N]);
format_expr(#binary_op_expr{op = Op, left = L, right = R}) ->
    io_lib:format("(~s ~s ~s)", [format_expr(L), Op, format_expr(R)]);
format_expr(#unary_op_expr{op = Op, operand = O}) ->
    io_lib:format("(~s ~s)", [Op, format_expr(O)]).

show_simplification(Description, Original, Env) ->
    io:format("  ~s~n", [Description]),
    io:format("    Original:   ~s~n", [format_expr(Original)]),
    Simplified = cure_smt_solver:simplify_constraint(Original, Env),
    io:format("    Simplified: ~s~n", [format_expr(Simplified)]),
    io:format("~n"),
    ok.

%% Example 1: Arithmetic simplifications
example_arithmetic() ->
    io:format("1. Arithmetic Identity Simplifications~n"),
    io:format("   ───────────────────────────────────~n~n"),
    
    % x + 0 -> x
    show_simplification(
        "Adding zero (x + 0)",
        binop('+', var(x), lit(0)),
        #{}
    ),
    
    % (x * 1) + 0 -> x
    show_simplification(
        "Multiple identities ((x * 1) + 0)",
        binop('+', binop('*', var(x), lit(1)), lit(0)),
        #{}
    ),
    
    % (5 + 3) * 2 -> 16
    show_simplification(
        "Constant folding ((5 + 3) * 2)",
        binop('*', binop('+', lit(5), lit(3)), lit(2)),
        #{}
    ),
    
    ok.

%% Example 2: Boolean logic simplifications
example_boolean() ->
    io:format("2. Boolean Logic Simplifications~n"),
    io:format("   ─────────────────────────────~n~n"),
    
    % x and true -> x
    show_simplification(
        "Conjunction with true (x and true)",
        binop('and', var(x), lit(true)),
        #{}
    ),
    
    % (x or false) and true -> x
    show_simplification(
        "Multiple boolean identities ((x or false) and true)",
        binop('and', binop('or', var(x), lit(false)), lit(true)),
        #{}
    ),
    
    % not (not x) -> x
    show_simplification(
        "Double negation (not (not x))",
        unop('not', unop('not', var(x))),
        #{}
    ),
    
    ok.

%% Example 3: Complex nested expressions
example_nested() ->
    io:format("3. Complex Nested Expression Simplifications~n"),
    io:format("   ──────────────────────────────────────────~n~n"),
    
    % ((x + 0) * 1) - 0 -> x
    show_simplification(
        "Nested arithmetic identities (((x + 0) * 1) - 0)",
        binop('-', binop('*', binop('+', var(x), lit(0)), lit(1)), lit(0)),
        #{}
    ),
    
    % (x and true) or (false and y) -> x
    show_simplification(
        "Mixed boolean operations ((x and true) or (false and y))",
        binop('or', binop('and', var(x), lit(true)), binop('and', lit(false), var(y))),
        #{}
    ),
    
    % (2 + 3) > (10 - 5) -> false
    show_simplification(
        "Constant comparison (2 + 3) > (10 - 5)",
        binop('>', binop('+', lit(2), lit(3)), binop('-', lit(10), lit(5))),
        #{}
    ),
    
    ok.

%% Example 4: Guard optimizations
example_guards() ->
    io:format("4. Guard Optimization Use Cases~n"),
    io:format("   ─────────────────────────────~n~n"),
    
    io:format("  These simplifications are particularly useful for:~n"),
    io:format("  • Eliminating redundant runtime checks~n"),
    io:format("  • Optimizing dependent type constraints~n"),
    io:format("  • Proving guard conditions at compile time~n~n"),
    
    % x == x -> true (useful for proving reflexivity)
    show_simplification(
        "Reflexive equality (x == x)",
        binop('==', var(x), var(x)),
        #{}
    ),
    
    % x >= x -> true (useful for boundary checks)
    show_simplification(
        "Reflexive comparison (x >= x)",
        binop('>=', var(x), var(x)),
        #{}
    ),
    
    % (n > 0) and true -> (n > 0)
    show_simplification(
        "Guard with redundant conjunction ((n > 0) and true)",
        binop('and', binop('>', var(n), lit(0)), lit(true)),
        #{}
    ),
    
    ok.
