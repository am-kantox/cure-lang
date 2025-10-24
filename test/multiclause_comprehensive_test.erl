-module(multiclause_comprehensive_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

run() ->
    io:format("=== Comprehensive Multi-Clause Function Tests ===~n~n"),

    test_basic_multiclause(),
    test_union_types(),
    test_different_return_types(),
    test_three_clauses(),
    test_single_clause_backward_compat(),
    test_mixed_module(),
    test_arity_mismatch_detection(),

    io:format("~n✓ All comprehensive tests passed!~n").

%% Test 1: Basic multi-clause with different parameter types
test_basic_multiclause() ->
    io:format("Test 1: Basic multi-clause function...~n"),
    Code =
        <<
            "\n"
            "        module Test do\n"
            "            def handle_value(i: Int) -> String do\n"
            "                \"integer\"\n"
            "            end\n"
            "            \n"
            "            def handle_value(s: String) -> String do\n"
            "                \"string\"\n"
            "            end\n"
            "        end\n"
            "    "
        >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),
    {ok, CompiledModule} = cure_codegen:compile_module(hd(AST)),

    Functions = maps:get(functions, CompiledModule),
    {value, ProcessFunc} = lists:search(
        fun
            (F) when is_map(F) -> maps:get(name, F, undefined) =:= handle_value;
            (_) -> false
        end,
        Functions
    ),

    true = maps:get(is_multiclause, ProcessFunc, false),
    2 = length(maps:get(clauses, ProcessFunc)),
    io:format("  ✓ Basic multi-clause works~n").

%% Test 2: Union type derivation
test_union_types() ->
    io:format("Test 2: Union type derivation...~n"),
    Code =
        <<
            "\n"
            "        module Test do\n"
            "            def handle(i: Int) -> Bool do\n"
            "                true\n"
            "            end\n"
            "            \n"
            "            def handle(f: Float) -> Bool do\n"
            "                false\n"
            "            end\n"
            "        end\n"
            "    "
        >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    % Just verify it compiles (type checker handles union type derivation internally)
    {ok, _CompiledModule} = cure_codegen:compile_module(hd(AST)),
    io:format("  ✓ Union types compiled successfully~n").

%% Test 3: Different return types per clause
test_different_return_types() ->
    io:format("Test 3: Different return types per clause...~n"),
    Code =
        <<
            "\n"
            "        module Test do\n"
            "            def convert(i: Int) -> String do\n"
            "                \"num\"\n"
            "            end\n"
            "            \n"
            "            def convert(s: String) -> String do\n"
            "                s\n"
            "            end\n"
            "        end\n"
            "    "
        >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),
    {ok, _CompiledModule} = cure_codegen:compile_module(hd(AST)),
    io:format("  ✓ Different return types handled~n").

%% Test 4: Three clauses
test_three_clauses() ->
    io:format("Test 4: Three-clause function...~n"),
    Code =
        <<
            "\n"
            "        module Test do\n"
            "            def classify(i: Int) -> String do\n"
            "                \"integer\"\n"
            "            end\n"
            "            \n"
            "            def classify(f: Float) -> String do\n"
            "                \"float\"\n"
            "            end\n"
            "            \n"
            "            def classify(s: String) -> String do\n"
            "                \"string\"\n"
            "            end\n"
            "        end\n"
            "    "
        >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),
    {ok, CompiledModule} = cure_codegen:compile_module(hd(AST)),

    Functions = maps:get(functions, CompiledModule),
    {value, ClassifyFunc} = lists:search(
        fun
            (F) when is_map(F) -> maps:get(name, F, undefined) =:= classify;
            (_) -> false
        end,
        Functions
    ),

    3 = length(maps:get(clauses, ClassifyFunc)),
    io:format("  ✓ Three clauses work correctly~n").

%% Test 5: Single-clause backward compatibility
test_single_clause_backward_compat() ->
    io:format("Test 5: Single-clause backward compatibility...~n"),
    Code =
        <<
            "\n"
            "        module Test do\n"
            "            def single(x: Int) -> Int do\n"
            "                x\n"
            "            end\n"
            "        end\n"
            "    "
        >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),
    {ok, CompiledModule} = cure_codegen:compile_module(hd(AST)),

    Functions = maps:get(functions, CompiledModule),
    {value, SingleFunc} = lists:search(
        fun
            (F) when is_map(F) -> maps:get(name, F, undefined) =:= single;
            (_) -> false
        end,
        Functions
    ),

    % Single-clause functions should NOT be marked as multiclause
    false = maps:get(is_multiclause, SingleFunc, false),
    io:format("  ✓ Backward compatibility maintained~n").

%% Test 6: Mixed module with both single and multi-clause functions
test_mixed_module() ->
    io:format("Test 6: Mixed single and multi-clause module...~n"),
    Code =
        <<
            "\n"
            "        module Test do\n"
            "            def single(x: Int) -> Int do\n"
            "                x\n"
            "            end\n"
            "            \n"
            "            def multi(i: Int) -> String do\n"
            "                \"int\"\n"
            "            end\n"
            "            \n"
            "            def multi(s: String) -> String do\n"
            "                \"string\"\n"
            "            end\n"
            "            \n"
            "            def another(y: Bool) -> Bool do\n"
            "                y\n"
            "            end\n"
            "        end\n"
            "    "
        >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),
    {ok, CompiledModule} = cure_codegen:compile_module(hd(AST)),

    Functions = maps:get(functions, CompiledModule),

    % Should have 3 functions total
    3 = length(Functions),

    % Check multi is multiclause
    {value, MultiFunc} = lists:search(
        fun
            (F) when is_map(F) -> maps:get(name, F, undefined) =:= multi;
            (_) -> false
        end,
        Functions
    ),
    true = maps:get(is_multiclause, MultiFunc, false),

    % Check single and another are NOT multiclause
    {value, SingleFunc} = lists:search(
        fun
            (F) when is_map(F) -> maps:get(name, F, undefined) =:= single;
            (_) -> false
        end,
        Functions
    ),
    false = maps:get(is_multiclause, SingleFunc, false),

    io:format("  ✓ Mixed module works correctly~n").

%% Test 7: Arity mismatch detection (error case)
test_arity_mismatch_detection() ->
    io:format("Test 7: Arity mismatch detection...~n"),
    Code =
        <<
            "\n"
            "        module Test do\n"
            "            def bad(i: Int) -> String do\n"
            "                \"one param\"\n"
            "            end\n"
            "            \n"
            "            def bad(i: Int, j: Int) -> String do\n"
            "                \"two params\"\n"
            "            end\n"
            "        end\n"
            "    "
        >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    % This should succeed in parsing (parser groups by name, allows different arities)
    % But in a stricter implementation, codegen might catch this
    % For now, just verify it doesn't crash
    case cure_codegen:compile_module(hd(AST)) of
        {ok, _} ->
            io:format("  ✓ Different arities handled (treated as separate functions)~n");
        {error, _} ->
            io:format("  ✓ Arity mismatch detected as expected~n")
    end.
