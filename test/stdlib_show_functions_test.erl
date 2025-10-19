%% Standard Library Show Functions Tests
%% Tests for show, print, and println functions behavior and integration

-module(stdlib_show_functions_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").

%% Test runner
run() ->
    io:format("~n=== Standard Library Show Functions Test Suite ===~n"),

    Tests = [
        {test_show_function_parsing, "Show Function Parsing"},
        {test_print_function_parsing, "Print Function Parsing"},
        {test_println_function_parsing, "Println Function Parsing"},
        {test_show_functions_in_expressions, "Show Functions in Expressions"},
        {test_show_functions_with_different_types, "Show Functions with Different Types"},
        {test_show_functions_integration, "Show Functions Integration"},
        {test_show_library_structure, "Show Library Structure"},
        {test_show_functions_type_signatures, "Show Functions Type Signatures"}
    ],

    Results = lists:map(
        fun({TestFun, TestName}) ->
            io:format("Testing ~s... ", [TestName]),
            try
                case apply(?MODULE, TestFun, []) of
                    ok ->
                        io:format("PASSED~n"),
                        {TestName, passed};
                    {error, Reason} ->
                        io:format("FAILED: ~p~n", [Reason]),
                        {TestName, {failed, Reason}}
                end
            catch
                Error:ErrReason:Stacktrace ->
                    io:format("ERROR: ~p:~p~n", [Error, ErrReason]),
                    io:format("Stacktrace: ~p~n", [Stacktrace]),
                    {TestName, {error, {Error, ErrReason}}}
            end
        end,
        Tests
    ),

    Passed = length([R || {_, passed} = R <- Results]),
    Total = length(Results),

    io:format("~nResults: ~p/~p tests passed~n", [Passed, Total]),

    case Passed of
        Total ->
            io:format("All show functions tests passed!~n"),
            ok;
        _ ->
            io:format("Some tests failed.~n"),
            {failed, Results}
    end.

%% ===== SHOW FUNCTION PARSING TESTS =====

%% Test parsing of show function calls
test_show_function_parsing() ->
    Code = <<
        "def test_show(x: Int): String =\n"
        "          show(x)\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,

    % Check function structure
    ?assertMatch(#function_def{name = test_show}, FunctionDef),

    % Check that body is a function call to 'show'
    Body = FunctionDef#function_def.body,
    ?assertMatch(#function_call_expr{}, Body),

    #function_call_expr{function = FuncExpr, args = Args} = Body,
    ?assertMatch(#identifier_expr{name = show}, FuncExpr),
    ?assertEqual(1, length(Args)),

    ok.

%% ===== PRINT FUNCTION PARSING TESTS =====

%% Test parsing of print function calls
test_print_function_parsing() ->
    Code = <<
        "def test_print(s: String): Unit =\n"
        "          print(s)\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,

    % Check function structure
    ?assertMatch(#function_def{name = test_print}, FunctionDef),

    % Check that body is a function call to 'print'
    Body = FunctionDef#function_def.body,
    ?assertMatch(#function_call_expr{}, Body),

    #function_call_expr{function = FuncExpr, args = Args} = Body,
    ?assertMatch(#identifier_expr{name = print}, FuncExpr),
    ?assertEqual(1, length(Args)),

    ok.

%% ===== PRINTLN FUNCTION PARSING TESTS =====

%% Test parsing of println function calls
test_println_function_parsing() ->
    Code = <<
        "def test_println(s: String): Unit =\n"
        "          println(s)\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,

    % Check function structure
    ?assertMatch(#function_def{name = test_println}, FunctionDef),

    % Check that body is a function call to 'println'
    Body = FunctionDef#function_def.body,
    ?assertMatch(#function_call_expr{}, Body),

    #function_call_expr{function = FuncExpr, args = Args} = Body,
    ?assertMatch(#identifier_expr{name = println}, FuncExpr),
    ?assertEqual(1, length(Args)),

    ok.

%% ===== SHOW FUNCTIONS IN EXPRESSIONS =====

%% Test show functions used in complex expressions
test_show_functions_in_expressions() ->
    Code = <<
        "def format_output(x: Int, y: Int): Unit =\n"
        "          let sum = x + y\n"
        "          let sum_str = show(sum)\n"
        "          let output = \\\"Sum: \\\" ++ sum_str\n"
        "          println(output)\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,

    % Check function structure
    ?assertMatch(#function_def{name = format_output}, FunctionDef),

    % Check that body is a let expression (multi-statement function)
    Body = FunctionDef#function_def.body,
    ?assertMatch(#let_expr{}, Body),

    % The let expression should contain bindings for sum, sum_str, output, and println call
    #let_expr{bindings = Bindings} = Body,
    ?assertEqual(3, length(Bindings)),

    ok.

%% ===== SHOW FUNCTIONS WITH DIFFERENT TYPES =====

%% Test show functions with various data types
test_show_functions_with_different_types() ->
    Code = <<
        "def test_various_shows(): Unit =\n"
        "          let int_str = show(42)\n"
        "          let float_str = show(3.14)  % This would require Float overload\n"
        "          let bool_str = show(true)   % This would require Bool overload\n"
        "          println(int_str)\n"
        "          println(float_str)\n"
        "          println(bool_str)\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,

    % Check function structure - should parse even if not all overloads exist yet
    ?assertMatch(#function_def{name = test_various_shows}, FunctionDef),

    Body = FunctionDef#function_def.body,
    ?assertMatch(#let_expr{}, Body),

    ok.

%% ===== SHOW FUNCTIONS INTEGRATION =====

%% Test integration of show functions in real-world scenarios
test_show_functions_integration() ->
    Code = <<
        "record Person { name: String, age: Int }\n"
        "        \n"
        "        def greet_person(person: Person): Unit =\n"
        "          case person of\n"
        "            Person{name: name, age: age} ->\n"
        "              let age_str = show(age)\n"
        "              let greeting = \\\"Hello \\\" ++ name ++ \\\", you are \\\" ++ age_str ++ \\\" years old.\\\"\n"
        "              println(greeting)\n"
        "            _ ->\n"
        "              println(\\\"Hello, unknown person!\\\")\n"
        "          end\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(2, length(AST)),
    [RecordDef, FunctionDef] = AST,

    % Check record definition
    ?assertMatch(#record_def{name = 'Person'}, RecordDef),

    % Check function with show integration
    ?assertMatch(#function_def{name = greet_person}, FunctionDef),

    Body = FunctionDef#function_def.body,
    ?assertMatch(#match_expr{}, Body),

    ok.

%% ===== SHOW LIBRARY STRUCTURE =====

%% Test that the show library module is properly structured
test_show_library_structure() ->
    % Read the show.cure file and verify its structure
    ShowFile = "/opt/Proyectos/Ammotion/cure/lib/std/show.cure",
    case file:read_file(ShowFile) of
        {ok, Content} ->
            {ok, Tokens} = cure_lexer:tokenize(Content),
            {ok, AST} = cure_parser:parse(Tokens),

            ?assertEqual(1, length(AST)),
            [ModuleDef] = AST,

            % Check module definition
            ?assertMatch(#module_def{name = 'Std.Show'}, ModuleDef),

            % Check exports
            #module_def{exports = Exports} = ModuleDef,
            ?assertNotEqual([], Exports),

            % Check that show, print, and println are exported
            ExportNames = [Name || #export_spec{name = Name} <- Exports],
            ?assert(lists:member(show, ExportNames)),
            ?assert(lists:member(print, ExportNames)),
            ?assert(lists:member(println, ExportNames)),

            ok;
        {error, Reason} ->
            {error, {file_read_failed, Reason}}
    end.

%% ===== SHOW FUNCTIONS TYPE SIGNATURES =====

%% Test type signatures of show functions
test_show_functions_type_signatures() ->
    Code = <<
        "import Std.Show [show/1, print/1, println/1]\n"
        "        \n"
        "        def test_type_signatures(): Unit =\n"
        "          let x: Int = 42\n"
        "          let s: String = show(x)    % show(Int): String\n"
        "          print(s)                   % print(String): Unit\n"
        "          println(\\\"Done\\\")           % println(String): Unit\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(2, length(AST)),
    [ImportDef, FunctionDef] = AST,

    % Check import definition
    ?assertMatch(#import_def{module = 'Std.Show'}, ImportDef),

    % Check that the import includes the show functions with correct arity
    #import_def{items = ImportItems} = ImportDef,
    ?assertEqual(3, length(ImportItems)),

    % Check that show/1, print/1, println/1 are imported
    [ShowImport, PrintImport, PrintlnImport] = ImportItems,
    ?assertMatch(#function_import{name = show, arity = 1}, ShowImport),
    ?assertMatch(#function_import{name = print, arity = 1}, PrintImport),
    ?assertMatch(#function_import{name = println, arity = 1}, PrintlnImport),

    % Check function definition
    ?assertMatch(#function_def{name = test_type_signatures}, FunctionDef),

    ok.

%% ===== HELPER FUNCTIONS =====

%% Helper to check if a function call exists in expression
contains_function_call(#function_call_expr{function = #identifier_expr{name = Name}}, Name) ->
    true;
contains_function_call(#let_expr{bindings = Bindings, body = Body}, FuncName) ->
    BindingsContain = lists:any(
        fun(#binding{value = Value}) ->
            contains_function_call(Value, FuncName)
        end,
        Bindings
    ),
    BodyContains = contains_function_call(Body, FuncName),
    BindingsContain orelse BodyContains;
contains_function_call(#match_expr{patterns = Patterns}, FuncName) ->
    lists:any(
        fun(#match_clause{body = Body}) ->
            contains_function_call(Body, FuncName)
        end,
        Patterns
    );
contains_function_call(_, _) ->
    false.
