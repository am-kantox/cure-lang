%% Unit tests for match expressions
-module(match_test).
-export([run_all_tests/0]).

-include("../src/parser/cure_ast_simple.hrl").

%% Run all match expression tests
run_all_tests() ->
    io:format("=== Running Match Expression Tests ===~n"),
    
    Tests = [
        fun test_literal_patterns/0,
        fun test_constructor_patterns/0,
        fun test_wildcard_patterns/0,
        fun test_variable_binding/0,
        fun test_complex_clause_bodies/0,
        fun test_nested_patterns/0,
        fun test_compilation_pipeline/0
    ],
    
    Results = lists:map(fun(Test) ->
        try
            Test(),
            {ok, Test}
        catch
            Class:Reason:Stack ->
                io:format("Test ~p failed: ~p:~p~n~p~n", [Test, Class, Reason, Stack]),
                {error, {Test, Class, Reason}}
        end
    end, Tests),
    
    {Passed, Failed} = lists:partition(fun({Tag, _}) -> Tag =:= ok end, Results),
    
    io:format("~nTest Results: ~w passed, ~w failed~n", [length(Passed), length(Failed)]),
    
    case Failed of
        [] ->
            io:format("ALL TESTS PASSED!~n"),
            ok;
        _ ->
            io:format("SOME TESTS FAILED!~n"),
            {error, Failed}
    end.

%% Test literal pattern parsing and compilation
test_literal_patterns() ->
    io:format("Testing literal patterns...~n"),
    
    % Test parsing
    TestCode = "def test_literal(x) = match x do\n  0 -> \"zero\"\n  42 -> \"answer\"\n  _ -> \"other\"\nend",
    
    % Write test file
    file:write_file("test_temp_literal.cure", TestCode),
    
    % Parse
    {ok, AST} = cure_parser:parse_file("test_temp_literal.cure"),
    
    % Verify AST structure
    [{function_def, test_literal, [Param], _, _, MatchExpr, _}] = AST,
    
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
    
    io:format("  ✓ Literal patterns test passed~n").

%% Test constructor pattern parsing and compilation  
test_constructor_patterns() ->
    io:format("Testing constructor patterns...~n"),
    
    TestCode = "def test_constructor(result) = match result do\n  Ok(value) -> value\n  Error(msg) -> 0\n  _ -> -1\nend",
    
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
    
    io:format("  ✓ Constructor patterns test passed~n").

%% Test wildcard patterns
test_wildcard_patterns() ->
    io:format("Testing wildcard patterns...~n"),
    
    TestCode = "def test_wildcard(x) = match x do\n  _ -> \"anything\"\nend",
    
    file:write_file("test_temp_wildcard.cure", TestCode),
    
    {ok, AST} = cure_parser:parse_file("test_temp_wildcard.cure"),
    {ok, _Modules} = cure_codegen:compile_program(AST),
    
    file:delete("test_temp_wildcard.cure"),
    
    io:format("  ✓ Wildcard patterns test passed~n").

%% Test variable binding in patterns
test_variable_binding() ->
    io:format("Testing variable binding...~n"),
    
    TestCode = "def test_binding(result) = match result do\n  Ok(value) -> value + 1\n  Error(reason) -> reason\nend",
    
    file:write_file("test_temp_binding.cure", TestCode),
    
    {ok, AST} = cure_parser:parse_file("test_temp_binding.cure"),
    
    % Verify variable binding in AST
    [{function_def, test_binding, _, _, _, MatchExpr, _}] = AST,
    
    #match_expr{
        patterns = [
            #match_clause{
                pattern = #constructor_pattern{name = 'Ok', args = [#identifier_pattern{name = value}]},
                body = #binary_op_expr{left = #identifier_expr{name = value}}
            },
            #match_clause{
                pattern = #constructor_pattern{name = 'Error', args = [#identifier_pattern{name = reason}]},
                body = #identifier_expr{name = reason}
            }
        ]
    } = MatchExpr,
    
    {ok, _Modules} = cure_codegen:compile_program(AST),
    
    file:delete("test_temp_binding.cure"),
    
    io:format("  ✓ Variable binding test passed~n").

%% Test complex clause bodies
test_complex_clause_bodies() ->
    io:format("Testing complex clause bodies...~n"),
    
    TestCode = "def test_complex(result) = match result do\n  Ok(value) ->\n    let doubled = value * 2\n    doubled + 10\n  _ -> 0\nend",
    
    file:write_file("test_temp_complex.cure", TestCode),
    
    {ok, AST} = cure_parser:parse_file("test_temp_complex.cure"),
    {ok, _Modules} = cure_codegen:compile_program(AST),
    
    file:delete("test_temp_complex.cure"),
    
    io:format("  ✓ Complex clause bodies test passed~n").

%% Test nested patterns
test_nested_patterns() ->
    io:format("Testing nested patterns...~n"),
    
    % For now, test simple nesting
    TestCode = "def test_nested(x) = match x do\n  Ok(_) -> 1\n  Error(_) -> 0\nend",
    
    file:write_file("test_temp_nested.cure", TestCode),
    
    {ok, AST} = cure_parser:parse_file("test_temp_nested.cure"),
    {ok, _Modules} = cure_codegen:compile_program(AST),
    
    file:delete("test_temp_nested.cure"),
    
    io:format("  ✓ Nested patterns test passed~n").

%% Test full compilation pipeline
test_compilation_pipeline() ->
    io:format("Testing full compilation pipeline...~n"),
    
    TestCode = "def test_pipeline(result) = match result do\n  Ok(42) -> \"found answer\"\n  Ok(x) -> \"found value\"\n  Error(msg) -> \"error occurred\"\n  _ -> \"unknown\"\nend",
    
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
            true = length(Instructions) > 5; % Should have several instructions
        ModuleMap when is_map(ModuleMap) ->
            Functions = maps:get(functions, ModuleMap),
            true = length(Functions) > 0
    end,
    
    file:delete("test_temp_pipeline.cure"),
    
    io:format("  ✓ Full compilation pipeline test passed~n").