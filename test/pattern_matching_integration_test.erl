%% Pattern Matching Integration Test
%% Comprehensive test demonstrating all pattern matching features working together

-module(pattern_matching_integration_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast_simple.hrl").

%% Test runner
run() ->
    io:format("~n=== Pattern Matching Integration Test ===~n"),

    try
        test_comprehensive_pattern_matching(),
        io:format("✓ Comprehensive pattern matching test passed~n"),

        test_case_with_records_and_constructors(),
        io:format("✓ Case with records and constructors test passed~n"),

        test_show_functions_integration(),
        io:format("✓ Show functions integration test passed~n"),

        io:format("All pattern matching integration tests passed!~n")
    catch
        Error:Reason:Stacktrace ->
            io:format("Test failed: ~p:~p~n", [Error, Reason]),
            io:format("Stacktrace: ~p~n", [Stacktrace])
    end.

%% Test comprehensive pattern matching with all features
test_comprehensive_pattern_matching() ->
    Code = <<
        "record Person do name: String age: Int end\n"
        "        record Address do street: String city: String end\n"
        "        record Employee do person: Person address: Address id: Int end\n"
        "        \n"
        "        def process_employee(emp: Employee): String =\n"
        "          case emp of\n"
        "            Employee{person: Person{name: n}, address: Address{city: c}, id: i} when i > 0 ->\n"
        "              \"Employee: \" ++ n ++ \" in \" ++ c\n"
        "            Employee{person: Person{name: n}} ->\n"
        "              \"Employee: \" ++ n\n"
        "            _ ->\n"
        "              \"Unknown employee\"\n"
        "          end\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(4, length(AST)),
    [PersonDef, AddressDef, EmployeeDef, ProcessFunc] = AST,

    % Check record definitions
    ?assertMatch(#record_def{name = 'Person'}, PersonDef),
    ?assertMatch(#record_def{name = 'Address'}, AddressDef),
    ?assertMatch(#record_def{name = 'Employee'}, EmployeeDef),

    % Check function with complex nested pattern matching
    ?assertMatch(#function_def{name = process_employee}, ProcessFunc),

    Body = ProcessFunc#function_def.body,
    ?assertMatch(#match_expr{}, Body),

    #match_expr{patterns = Patterns} = Body,
    ?assertEqual(3, length(Patterns)),

    % First pattern should have a guard
    [FirstClause, SecondClause, ThirdClause] = Patterns,
    ?assertMatch(
        #match_clause{
            pattern = #record_pattern{name = 'Employee'},
            guard = Guard1
        } when Guard1 =/= undefined,
        FirstClause
    ),

    ?assertMatch(
        #match_clause{
            pattern = #record_pattern{name = 'Employee'},
            guard = undefined
        },
        SecondClause
    ),

    ?assertMatch(
        #match_clause{
            pattern = #wildcard_pattern{},
            guard = undefined
        },
        ThirdClause
    ),

    ok.

%% Test case expressions with records and constructor patterns
test_case_with_records_and_constructors() ->
    Code = <<
        "record User do name: String status: String end\n"
        "        \n"
        "        def handle_result(result: Result(User, String)): String =\n"
        "          case result of\n"
        "            Ok(User{name: username, status: \"active\"}) ->\n"
        "              \"Active user: \" ++ username\n"
        "            Ok(User{name: username}) ->\n"
        "              \"User: \" ++ username\n"
        "            Error(msg) ->\n"
        "              \"Error: \" ++ msg\n"
        "          end\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(2, length(AST)),
    [UserDef, HandleFunc] = AST,

    % Check record definition
    ?assertMatch(#record_def{name = 'User'}, UserDef),

    % Check function with constructor and record patterns
    ?assertMatch(#function_def{name = handle_result}, HandleFunc),

    Body = HandleFunc#function_def.body,
    ?assertMatch(#match_expr{}, Body),

    #match_expr{patterns = Patterns} = Body,
    ?assertEqual(3, length(Patterns)),

    % Check constructor patterns with nested record patterns
    [OkActiveClause, OkUserClause, ErrorClause] = Patterns,
    ?assertMatch(
        #match_clause{
            pattern = #constructor_pattern{name = 'Ok'}
        },
        OkActiveClause
    ),

    ?assertMatch(
        #match_clause{
            pattern = #constructor_pattern{name = 'Ok'}
        },
        OkUserClause
    ),

    ?assertMatch(
        #match_clause{
            pattern = #constructor_pattern{name = 'Error'}
        },
        ErrorClause
    ),

    ok.

%% Test show functions integration with pattern matching
test_show_functions_integration() ->
    Code = <<
        "def debug_value(opt: Option(Int)): String =\n"
        "          case opt of\n"
        "            Some(x) ->\n"
        "              let str = show(x)\n"
        "              \"Value: \" ++ str\n"
        "            None ->\n"
        "              \"No value\"\n"
        "          end\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,

    % Check function structure
    ?assertMatch(#function_def{name = debug_value}, FunctionDef),

    Body = FunctionDef#function_def.body,
    ?assertMatch(#match_expr{}, Body),

    #match_expr{patterns = Patterns} = Body,
    ?assertEqual(2, length(Patterns)),

    % Check that we have Some and None patterns
    [SomeClause, NoneClause] = Patterns,
    ?assertMatch(
        #match_clause{
            pattern = #constructor_pattern{name = 'Some'}
        },
        SomeClause
    ),

    ?assertMatch(
        #match_clause{
            pattern = #constructor_pattern{name = 'None'}
        },
        NoneClause
    ),

    ok.
