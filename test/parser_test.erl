%% Cure Programming Language - Parser Tests
-module(parser_test).

-export([
    run/0,
    test_simple_function/0,
    test_fsm/0,
    test_import_basic/0,
    test_import_function_list/0,
    test_import_mixed_list/0,
    test_import_complex/0
]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast_simple.hrl").

%% Run all tests
run() ->
    io:format("Running Cure parser tests...~n"),
    test_simple_function(),
    test_fsm(),
    test_import_basic(),
    test_import_function_list(),
    test_import_mixed_list(),
    test_import_complex(),
    io:format("All parser tests passed!~n").

%% Test parsing a simple function
test_simple_function() ->
    Code = <<"def add(x: Int, y: Int): Int = x + y">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,
    ?assertMatch(#function_def{name = add}, FunctionDef),
    ?assertEqual(2, length(FunctionDef#function_def.params)),

    io:format("✓ Simple function parsing test passed~n").

%% Test parsing an FSM
test_fsm() ->
    Code =
        <<
            "fsm Counter do\n"
            "              states: [Zero, Positive]\n"
            "              initial: Zero\n"
            "              \n"
            "              state Zero do\n"
            "                event(:increment) -> Positive\n"
            "              end\n"
            "              \n"
            "              state Positive do\n"
            "                event(:reset) -> Zero\n"
            "              end\n"
            "            end"
        >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FSMDef] = AST,
    ?assertMatch(#fsm_def{name = 'Counter'}, FSMDef),
    ?assertEqual(['Zero', 'Positive'], FSMDef#fsm_def.states),
    ?assertEqual('Zero', FSMDef#fsm_def.initial),
    ?assertEqual(2, length(FSMDef#fsm_def.state_defs)),

    io:format("✓ FSM parsing test passed~n").

%% Test basic import without function list
test_import_basic() ->
    Code = <<"import Std">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [ImportDef] = AST,
    ?assertMatch(#import_def{module = 'Std', items = all}, ImportDef),

    io:format("✓ Basic import parsing test passed~n").

%% Test import with function/arity list
test_import_function_list() ->
    Code = <<"import Std [abs/1, sqrt/1, max/2]">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [ImportDef] = AST,
    ?assertMatch(#import_def{module = 'Std'}, ImportDef),

    Items = ImportDef#import_def.items,
    ?assertEqual(3, length(Items)),

    [Abs, Sqrt, Max] = Items,
    ?assertMatch(#function_import{name = abs, arity = 1}, Abs),
    ?assertMatch(#function_import{name = sqrt, arity = 1}, Sqrt),
    ?assertMatch(#function_import{name = max, arity = 2}, Max),

    io:format("✓ Function list import parsing test passed~n").

%% Test import with mixed function/arity and plain identifiers
test_import_mixed_list() ->
    Code = <<"import Std [abs/1, Option, Result, sqrt/1, ok]">>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [ImportDef] = AST,
    ?assertMatch(#import_def{module = 'Std'}, ImportDef),

    Items = ImportDef#import_def.items,
    ?assertEqual(5, length(Items)),

    [Abs, Option, Result, Sqrt, Ok] = Items,
    ?assertMatch(#function_import{name = abs, arity = 1}, Abs),
    ?assertEqual('Option', Option),
    ?assertEqual('Result', Result),
    ?assertMatch(#function_import{name = sqrt, arity = 1}, Sqrt),
    ?assertEqual(ok, Ok),

    io:format("✓ Mixed import list parsing test passed~n").

%% Test complex import with many functions of different arities
test_import_complex() ->
    Code =
        <<
            "import Math [\n"
            "        sin/1, cos/1, tan/1,\n"
            "        atan2/2, pow/2, log/2,\n"
            "        PI, E,\n"
            "        factorial/1, gcd/2, lcm/2\n"
            "    ]"
        >>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [ImportDef] = AST,
    ?assertMatch(#import_def{module = 'Math'}, ImportDef),

    Items = ImportDef#import_def.items,
    ?assertEqual(11, length(Items)),

    % Check some specific items
    [Sin, _Cos, _Tan, Atan2, _Pow, _Log2, Pi, E, Factorial, _Gcd, Lcm] = Items,
    ?assertMatch(#function_import{name = sin, arity = 1}, Sin),
    ?assertMatch(#function_import{name = atan2, arity = 2}, Atan2),
    ?assertEqual('PI', Pi),
    ?assertEqual('E', E),
    ?assertMatch(#function_import{name = factorial, arity = 1}, Factorial),
    ?assertMatch(#function_import{name = lcm, arity = 2}, Lcm),

    io:format("✓ Complex import parsing test passed~n").
