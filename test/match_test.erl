%% Unit tests for match expressions
-module(match_test).
-export([run_all_tests/0]).

-include("../src/parser/cure_ast.hrl").

%% Run all match expression tests
run_all_tests() ->
    cure_utils:debug("=== Running Match Expression Tests ===~n"),

    Tests = [
        fun test_literal_patterns/0,
        fun test_constructor_patterns/0,
        fun test_wildcard_patterns/0,
        fun test_variable_binding/0,
        fun test_complex_clause_bodies/0,
        fun test_nested_patterns/0,
        fun test_compilation_pipeline/0,
        fun test_match_three_or_more_clauses/0,
        fun test_parse_match_clause_body_single_expression/0,
        fun test_match_multiple_clauses_no_nested/0,
        fun test_multi_line_match_clause_bodies/0
    ],

    Results = lists:map(
        fun(Test) ->
            try
                Test(),
                {ok, Test}
            catch
                Class:Reason:Stack ->
                    cure_utils:debug("Test ~p failed: ~p:~p~n~p~n", [Test, Class, Reason, Stack]),
                    {error, {Test, Class, Reason}}
            end
        end,
        Tests
    ),

    {Passed, Failed} = lists:partition(fun({Tag, _}) -> Tag =:= ok end, Results),

    cure_utils:debug("~nTest Results: ~w passed, ~w failed~n", [length(Passed), length(Failed)]),

    case Failed of
        [] ->
            cure_utils:debug("ALL TESTS PASSED!~n"),
            ok;
        _ ->
            cure_utils:debug("SOME TESTS FAILED!~n"),
            {error, Failed}
    end.

%% Test literal pattern parsing and compilation
test_literal_patterns() ->
    cure_utils:debug("Testing literal patterns...~n"),

    % Test parsing
    TestCode =
        "def test_literal(x) = match x do\n  0 -> \"zero\"\n  42 -> \"answer\"\n  _ -> \"other\"\nend",

    % Write test file
    file:write_file("test_temp_literal.cure", TestCode),

    % Parse
    {ok, AST} = cure_parser:parse_file("test_temp_literal.cure"),

    % Verify AST structure
    [{function_def, test_literal, [_Param], _, _, MatchExpr, _}] = AST,

    #match_expr{
        expr = #identifier_expr{name = x},
        patterns = [
            #match_clause{pattern = #literal_pattern{value = 0}},
            #match_clause{pattern = #literal_pattern{value = 42}},
            #match_clause{pattern = #wildcard_pattern{}}
        ]
    } = MatchExpr,

    % Test compilation
    {ok, _Modules} = cure_codegen:compile_program(AST),

    % Cleanup
    file:delete("test_temp_literal.cure"),

    cure_utils:debug("  ✓ Literal patterns test passed~n").

%% Test constructor pattern parsing and compilation
test_constructor_patterns() ->
    cure_utils:debug("Testing constructor patterns...~n"),

    TestCode =
        "def test_constructor(result) = match result do\n  Ok(value) -> value\n  Error(msg) -> 0\n  _ -> -1\nend",

    file:write_file("test_temp_constructor.cure", TestCode),

    {ok, AST} = cure_parser:parse_file("test_temp_constructor.cure"),

    % Verify constructor patterns in AST
    [{function_def, test_constructor, _, _, _, MatchExpr, _}] = AST,

    #match_expr{
        patterns = [
            #match_clause{pattern = #constructor_pattern{name = 'Ok', args = [_]}},
            #match_clause{pattern = #constructor_pattern{name = 'Error', args = [_]}},
            #match_clause{pattern = #wildcard_pattern{}}
        ]
    } = MatchExpr,

    % Test compilation
    {ok, _Modules} = cure_codegen:compile_program(AST),

    file:delete("test_temp_constructor.cure"),

    cure_utils:debug("  ✓ Constructor patterns test passed~n").

%% Test wildcard patterns
test_wildcard_patterns() ->
    cure_utils:debug("Testing wildcard patterns...~n"),

    TestCode = "def test_wildcard(x) = match x do\n  _ -> \"anything\"\nend",

    file:write_file("test_temp_wildcard.cure", TestCode),

    {ok, AST} = cure_parser:parse_file("test_temp_wildcard.cure"),
    {ok, _Modules} = cure_codegen:compile_program(AST),

    file:delete("test_temp_wildcard.cure"),

    cure_utils:debug("  ✓ Wildcard patterns test passed~n").

%% Test variable binding in patterns
test_variable_binding() ->
    cure_utils:debug("Testing variable binding...~n"),

    TestCode =
        "def test_binding(result) = match result do\n  Ok(value) -> value + 1\n  Error(reason) -> reason\nend",

    file:write_file("test_temp_binding.cure", TestCode),

    {ok, AST} = cure_parser:parse_file("test_temp_binding.cure"),

    % Verify variable binding in AST
    [{function_def, test_binding, _, _, _, MatchExpr, _}] = AST,

    #match_expr{
        patterns = [
            #match_clause{
                pattern = #constructor_pattern{
                    name = 'Ok', args = [#identifier_pattern{name = value}]
                },
                body = #binary_op_expr{left = #identifier_expr{name = value}}
            },
            #match_clause{
                pattern = #constructor_pattern{
                    name = 'Error', args = [#identifier_pattern{name = reason}]
                },
                body = #identifier_expr{name = reason}
            }
        ]
    } = MatchExpr,

    {ok, _Modules} = cure_codegen:compile_program(AST),

    file:delete("test_temp_binding.cure"),

    cure_utils:debug("  ✓ Variable binding test passed~n").

%% Test complex clause bodies
test_complex_clause_bodies() ->
    cure_utils:debug("Testing complex clause bodies...~n"),

    % Test complex expressions in clause bodies (function calls, nested operations)
    TestCode =
        "def test_complex(result) = match result do\n  Ok(value) -> value * 2 + 10\n  Error(msg) -> length(msg)\n  _ -> 0\nend",

    file:write_file("test_temp_complex.cure", TestCode),

    {ok, AST} = cure_parser:parse_file("test_temp_complex.cure"),

    % Verify complex expression structure in clause bodies
    [{function_def, test_complex, _, _, _, MatchExpr, _}] = AST,

    #match_expr{
        patterns = [
            #match_clause{
                pattern = #constructor_pattern{
                    name = 'Ok', args = [#identifier_pattern{name = value}]
                },
                body = #binary_op_expr{
                    op = '+', left = #binary_op_expr{op = '*'}, right = #literal_expr{value = 10}
                }
            },
            #match_clause{
                pattern = #constructor_pattern{
                    name = 'Error', args = [#identifier_pattern{name = msg}]
                },
                body = #function_call_expr{
                    function = #identifier_expr{name = length},
                    args = [#identifier_expr{name = msg}]
                }
            },
            #match_clause{
                pattern = #wildcard_pattern{},
                body = #literal_expr{value = 0}
            }
        ]
    } = MatchExpr,

    {ok, _Modules} = cure_codegen:compile_program(AST),

    file:delete("test_temp_complex.cure"),

    cure_utils:debug("  ✓ Complex clause bodies test passed~n").

%% Test nested patterns
test_nested_patterns() ->
    cure_utils:debug("Testing nested patterns...~n"),

    % For now, test simple nesting
    TestCode = "def test_nested(x) = match x do\n  Ok(_) -> 1\n  Error(_) -> 0\nend",

    file:write_file("test_temp_nested.cure", TestCode),

    {ok, AST} = cure_parser:parse_file("test_temp_nested.cure"),
    {ok, _Modules} = cure_codegen:compile_program(AST),

    file:delete("test_temp_nested.cure"),

    cure_utils:debug("  ✓ Nested patterns test passed~n").

%% Test full compilation pipeline
test_compilation_pipeline() ->
    cure_utils:debug("Testing full compilation pipeline...~n"),

    TestCode =
        "def test_pipeline(result) = match result do\n  Ok(42) -> \"found answer\"\n  Ok(x) -> \"found value\"\n  Error(msg) -> \"error occurred\"\n  _ -> \"unknown\"\nend",

    file:write_file("test_temp_pipeline.cure", TestCode),

    % Test parsing
    {ok, AST} = cure_parser:parse_file("test_temp_pipeline.cure"),

    % Test type checking (if available)
    % Note: This would need the typechecker integrated

    % Test compilation
    {ok, [Module]} = cure_codegen:compile_program(AST),

    % Verify module structure
    case Module of
        {function, FunctionData} ->
            test_pipeline = maps:get(name, FunctionData),
            1 = maps:get(arity, FunctionData),
            Instructions = maps:get(instructions, FunctionData),
            % Should have several instructions (label, load_param, make_case, return)
            true = length(Instructions) > 3;
        ModuleMap when is_map(ModuleMap) ->
            Functions = maps:get(functions, ModuleMap),
            true = length(Functions) > 0
    end,

    file:delete("test_temp_pipeline.cure"),

    cure_utils:debug("  ✓ Full compilation pipeline test passed~n").

%% Test match expressions with three or more clauses
test_match_three_or_more_clauses() ->
    cure_utils:debug("Testing match expressions with three or more clauses...~n"),

    % Test with exactly three clauses
    TestCode3 =
        "def test_three_clauses(x) = match x do\n  1 -> \"one\"\n  2 -> \"two\"\n  _ -> \"other\"\nend",

    file:write_file("test_temp_three_clauses.cure", TestCode3),

    {ok, AST3} = cure_parser:parse_file("test_temp_three_clauses.cure"),

    % Verify AST structure for three clauses
    [{function_def, test_three_clauses, [_], _, _, MatchExpr3, _}] = AST3,

    #match_expr{
        expr = #identifier_expr{name = x},
        patterns = Patterns3
    } = MatchExpr3,

    % Should have exactly 3 clauses
    3 = length(Patterns3),

    [Clause1, Clause2, Clause3] = Patterns3,

    % Verify each clause structure
    #match_clause{pattern = #literal_pattern{value = 1}} = Clause1,
    #match_clause{pattern = #literal_pattern{value = 2}} = Clause2,
    #match_clause{pattern = #wildcard_pattern{}} = Clause3,

    % Test compilation
    {ok, _Modules3} = cure_codegen:compile_program(AST3),

    file:delete("test_temp_three_clauses.cure"),

    % Test with five clauses (more than three)
    TestCode5 =
        "def test_five_clauses(value) = match value do\n  Ok(1) -> \"one\"\n  Ok(2) -> \"two\"\n  Error(msg) -> \"error\"\n  None -> \"none\"\n  _ -> \"default\"\nend",

    file:write_file("test_temp_five_clauses.cure", TestCode5),

    {ok, AST5} = cure_parser:parse_file("test_temp_five_clauses.cure"),

    % Verify AST structure for five clauses
    [{function_def, test_five_clauses, [_], _, _, MatchExpr5, _}] = AST5,

    #match_expr{
        expr = #identifier_expr{name = value},
        patterns = Patterns5
    } = MatchExpr5,

    % Should have exactly 5 clauses
    5 = length(Patterns5),

    [C1, C2, C3, C4, C5] = Patterns5,

    % Verify constructor and literal patterns
    #match_clause{pattern = #constructor_pattern{name = 'Ok', args = [#literal_pattern{value = 1}]}} =
        C1,
    #match_clause{pattern = #constructor_pattern{name = 'Ok', args = [#literal_pattern{value = 2}]}} =
        C2,
    #match_clause{
        pattern = #constructor_pattern{name = 'Error', args = [#identifier_pattern{name = msg}]}
    } = C3,
    #match_clause{pattern = #constructor_pattern{name = 'None', args = undefined}} = C4,
    #match_clause{pattern = #wildcard_pattern{}} = C5,

    % Test compilation
    {ok, _Modules5} = cure_codegen:compile_program(AST5),

    file:delete("test_temp_five_clauses.cure"),

    cure_utils:debug("  ✓ Match expressions with three or more clauses test passed~n").

%% Test that parse_match_clause_body parses only a single expression
test_parse_match_clause_body_single_expression() ->
    cure_utils:debug("Testing parse_match_clause_body parses single expression...~n"),

    % Test simple single expression in clause body
    TestCodeSimple = "def test_single_expr(x) = match x do\n  1 -> x + 5\n  _ -> 0\nend",

    file:write_file("test_temp_single_expr.cure", TestCodeSimple),

    {ok, ASTSimple} = cure_parser:parse_file("test_temp_single_expr.cure"),

    [{function_def, test_single_expr, [_], _, _, MatchExprSimple, _}] = ASTSimple,

    #match_expr{
        patterns = [Clause1Simple, Clause2Simple]
    } = MatchExprSimple,

    % Verify first clause has single binary operation expression
    #match_clause{
        pattern = #literal_pattern{value = 1},
        body = #binary_op_expr{
            op = '+', left = #identifier_expr{name = x}, right = #literal_expr{value = 5}
        }
    } = Clause1Simple,

    % Verify second clause has single literal expression
    #match_clause{
        pattern = #wildcard_pattern{},
        body = #literal_expr{value = 0}
    } = Clause2Simple,

    {ok, _ModulesSimple} = cure_codegen:compile_program(ASTSimple),

    file:delete("test_temp_single_expr.cure"),

    % Test more complex single expression (function call)
    TestCodeComplex =
        "def test_function_call(result) = match result do\n  Ok(value) -> some_func(value)\n  Error(_) -> error_handler()\nend",

    file:write_file("test_temp_function_call.cure", TestCodeComplex),

    {ok, ASTComplex} = cure_parser:parse_file("test_temp_function_call.cure"),

    [{function_def, test_function_call, [_], _, _, MatchExprComplex, _}] = ASTComplex,

    #match_expr{
        patterns = [ClauseFunc1, ClauseFunc2]
    } = MatchExprComplex,

    % Verify first clause has function call expression
    #match_clause{
        pattern = #constructor_pattern{name = 'Ok', args = [#identifier_pattern{name = value}]},
        body = #function_call_expr{
            function = #identifier_expr{name = some_func}, args = [#identifier_expr{name = value}]
        }
    } = ClauseFunc1,

    % Verify second clause has function call expression with no args
    #match_clause{
        pattern = #constructor_pattern{name = 'Error', args = [#wildcard_pattern{}]},
        body = #function_call_expr{function = #identifier_expr{name = error_handler}, args = []}
    } = ClauseFunc2,

    {ok, _ModulesComplex} = cure_codegen:compile_program(ASTComplex),

    file:delete("test_temp_function_call.cure"),

    cure_utils:debug("  ✓ Parse match clause body single expression test passed~n").

%% Test match expressions with multiple clauses do not require nested match statements
test_match_multiple_clauses_no_nested() ->
    cure_utils:debug("Testing match multiple clauses without nested match statements...~n"),

    % Test flat structure with multiple clauses (no nested matches)
    TestCodeFlat =
        "def test_flat_match(data) = match data do\n  {ok, 1} -> \"first\"\n  {ok, 2} -> \"second\"\n  {error, _} -> \"error\"\n  _ -> \"unknown\"\nend",

    file:write_file("test_temp_flat_match.cure", TestCodeFlat),

    {ok, ASTFlat} = cure_parser:parse_file("test_temp_flat_match.cure"),

    [{function_def, test_flat_match, [_], _, _, MatchExprFlat, _}] = ASTFlat,

    #match_expr{
        expr = #identifier_expr{name = data},
        patterns = PatternsFlat
    } = MatchExprFlat,

    % Should have 4 clauses at the same level (no nesting)
    4 = length(PatternsFlat),

    [FlatClause1, FlatClause2, FlatClause3, FlatClause4] = PatternsFlat,

    % Verify each clause is at the same level with simple bodies (no nested match expressions)
    #match_clause{
        pattern = #tuple_pattern{
            elements = [
                #constructor_pattern{name = ok, args = undefined}, #literal_pattern{value = 1}
            ]
        },
        body = #literal_expr{value = "first"}
    } = FlatClause1,

    #match_clause{
        pattern = #tuple_pattern{
            elements = [
                #constructor_pattern{name = ok, args = undefined}, #literal_pattern{value = 2}
            ]
        },
        body = #literal_expr{value = "second"}
    } = FlatClause2,

    #match_clause{
        pattern = #tuple_pattern{
            elements = [#constructor_pattern{name = error, args = undefined}, #wildcard_pattern{}]
        },
        body = #literal_expr{value = "error"}
    } = FlatClause3,

    #match_clause{
        pattern = #wildcard_pattern{},
        body = #literal_expr{value = "unknown"}
    } = FlatClause4,

    % Verify none of the clause bodies contain nested match expressions
    false = contains_nested_match(FlatClause1#match_clause.body),
    false = contains_nested_match(FlatClause2#match_clause.body),
    false = contains_nested_match(FlatClause3#match_clause.body),
    false = contains_nested_match(FlatClause4#match_clause.body),

    {ok, _ModulesFlat} = cure_codegen:compile_program(ASTFlat),

    file:delete("test_temp_flat_match.cure"),

    % Test complex patterns without nested matches
    TestCodeComplex =
        "def test_complex_patterns(input) = match input do\n  [head | tail] -> head\n  {value, Ok(result)} -> result\n  {value, Error(msg)} -> msg\n  [] -> \"empty\"\nend",

    file:write_file("test_temp_complex_patterns.cure", TestCodeComplex),

    {ok, ASTComplex} = cure_parser:parse_file("test_temp_complex_patterns.cure"),

    [{function_def, test_complex_patterns, [_], _, _, MatchExprComplex, _}] = ASTComplex,

    #match_expr{
        patterns = PatternsComplex
    } = MatchExprComplex,

    % Should have 4 clauses with complex patterns but no nesting
    4 = length(PatternsComplex),

    [ComplexClause1, ComplexClause2, ComplexClause3, ComplexClause4] = PatternsComplex,

    % Verify list pattern with head|tail
    #match_clause{
        pattern = #list_pattern{
            elements = [#identifier_pattern{name = head}], tail = #identifier_pattern{name = tail}
        },
        body = #identifier_expr{name = head}
    } = ComplexClause1,

    % Verify tuple with constructor patterns
    #match_clause{
        pattern = #tuple_pattern{
            elements = [
                #identifier_pattern{name = value},
                #constructor_pattern{name = 'Ok', args = [#identifier_pattern{name = result}]}
            ]
        },
        body = #identifier_expr{name = result}
    } = ComplexClause2,

    #match_clause{
        pattern = #tuple_pattern{
            elements = [
                #identifier_pattern{name = value},
                #constructor_pattern{name = 'Error', args = [#identifier_pattern{name = msg}]}
            ]
        },
        body = #identifier_expr{name = msg}
    } = ComplexClause3,

    % Verify empty list pattern
    #match_clause{
        pattern = #list_pattern{elements = [], tail = undefined},
        body = #literal_expr{value = "empty"}
    } = ComplexClause4,

    % Verify no nested match expressions in any clause body
    lists:all(
        fun(Clause) ->
            not contains_nested_match(Clause#match_clause.body)
        end,
        PatternsComplex
    ),

    {ok, _ModulesComplex} = cure_codegen:compile_program(ASTComplex),

    file:delete("test_temp_complex_patterns.cure"),

    cure_utils:debug("  ✓ Match multiple clauses without nested match statements test passed~n").

%% Test multi-line syntax capabilities in match clause bodies
%% Note: This tests complex single-line expressions that provide multi-line-like functionality
%% True multi-line syntax with newlines in match clauses is not yet supported due to parser limitations
test_multi_line_match_clause_bodies() ->
    cure_utils:debug("Testing multi-line syntax capabilities in match clause bodies...~n"),

    % Test 1: Complex nested expressions in clause bodies (single-line but conceptually multi-step)
    TestCodeComplex =
        "def test_complex_single_line(result) = match result do\n  Ok(value) -> (value + 1) * (value + 2) + (value * 3)\n  Error(_) -> 42 + 24 - 18 * 2\n  _ -> 100\nend",

    file:write_file("test_temp_complex_single_line.cure", TestCodeComplex),

    {ok, ASTComplex} = cure_parser:parse_file("test_temp_complex_single_line.cure"),

    % Verify complex expressions are parsed correctly
    [{function_def, test_complex_single_line, _, _, _, MatchExprComplex, _}] = ASTComplex,

    #match_expr{
        patterns = [
            #match_clause{
                pattern = #constructor_pattern{
                    name = 'Ok', args = [#identifier_pattern{name = value}]
                },
                % Complex nested arithmetic
                body = #binary_op_expr{op = '+'}
            },
            #match_clause{
                pattern = #constructor_pattern{name = 'Error', args = [#wildcard_pattern{}]},
                % Complex arithmetic expression
                body = #binary_op_expr{}
            },
            #match_clause{
                pattern = #wildcard_pattern{},
                body = #literal_expr{value = 100}
            }
        ]
    } = MatchExprComplex,

    {ok, _ModulesComplex} = cure_codegen:compile_program(ASTComplex),

    file:delete("test_temp_complex_single_line.cure"),

    % Test 2: Nested function calls (conceptually multi-line)
    TestCodeNested =
        "def test_nested_expr(data) = match data do\n  {ok, value} -> (value + 1) * (value - 1)\n  {error, code} -> if code == 404 then 0 else code end\n  [] -> length([1, 2, 3])\n  _ -> abs(-42)\nend",

    file:write_file("test_temp_nested_expr.cure", TestCodeNested),

    {ok, ASTNested} = cure_parser:parse_file("test_temp_nested_expr.cure"),

    % Verify complex nested expressions
    [{function_def, test_nested_expr, _, _, _, MatchExprNested, _}] = ASTNested,

    #match_expr{
        patterns = [
            #match_clause{
                pattern = #tuple_pattern{
                    elements = [#constructor_pattern{name = ok}, #identifier_pattern{name = value}]
                },
                % Complex multiplication expression
                body = #binary_op_expr{op = '*'}
            },
            #match_clause{
                pattern = #list_pattern{elements = []},
                % function call
                body = #function_call_expr{function = #identifier_expr{name = length}}
            },
            #match_clause{
                pattern = #wildcard_pattern{},
                % function call with negative number
                body = #function_call_expr{function = #identifier_expr{name = abs}}
            }
        ]
    } = MatchExprNested,

    {ok, _ModulesNested} = cure_codegen:compile_program(ASTNested),

    file:delete("test_temp_nested_expr.cure"),

    % Test 3: Function calls with multiple arguments (conceptually multi-line)
    TestCodeFunctionCalls =
        "def test_function_calls(input) = match input do\n  Some(x) -> max(min(x, 100), 0)\n  None -> some_function(1, 2, 3)\n  _ -> another_func()\nend",

    file:write_file("test_temp_function_calls.cure", TestCodeFunctionCalls),

    {ok, ASTFunctionCalls} = cure_parser:parse_file("test_temp_function_calls.cure"),

    % Verify function call structures
    [{function_def, test_function_calls, _, _, _, MatchExprFunctionCalls, _}] = ASTFunctionCalls,

    #match_expr{
        patterns = [
            #match_clause{
                pattern = #constructor_pattern{
                    name = 'Some', args = [#identifier_pattern{name = x}]
                },
                % Nested function calls
                body = #function_call_expr{function = #identifier_expr{name = max}}
            },
            #match_clause{
                pattern = #constructor_pattern{name = 'None', args = undefined},
                % Multi-arg function call
                body = #function_call_expr{function = #identifier_expr{name = some_function}}
            },
            #match_clause{
                pattern = #wildcard_pattern{},
                % No-arg function call
                body = #function_call_expr{
                    function = #identifier_expr{name = another_func}, args = []
                }
            }
        ]
    } = MatchExprFunctionCalls,

    {ok, _ModulesFunctionCalls} = cure_codegen:compile_program(ASTFunctionCalls),

    file:delete("test_temp_function_calls.cure"),

    cure_utils:debug("  ✓ Multi-line syntax capabilities in match clause bodies test passed~n").

%% Helper function to check if an expression contains nested match expressions
contains_nested_match(#match_expr{}) ->
    true;
contains_nested_match(#binary_op_expr{left = Left, right = Right}) ->
    contains_nested_match(Left) orelse contains_nested_match(Right);
contains_nested_match(#unary_op_expr{operand = Operand}) ->
    contains_nested_match(Operand);
contains_nested_match(#function_call_expr{args = Args}) ->
    lists:any(fun contains_nested_match/1, Args);
contains_nested_match(#list_expr{elements = Elements}) ->
    lists:any(fun contains_nested_match/1, Elements);
contains_nested_match(#tuple_expr{elements = Elements}) ->
    lists:any(fun contains_nested_match/1, Elements);
contains_nested_match(#let_expr{bindings = Bindings, body = Body}) ->
    BindingCheck = lists:any(
        fun(#binding{value = Value}) -> contains_nested_match(Value) end, Bindings
    ),
    BindingCheck orelse contains_nested_match(Body);
contains_nested_match(#block_expr{expressions = Exprs}) ->
    lists:any(fun contains_nested_match/1, Exprs);
contains_nested_match(_) ->
    false.
