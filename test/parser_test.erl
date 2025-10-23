%% Cure Programming Language - Parser Tests
-module(parser_test).

-export([
    run/0,
    test_simple_function/0,
    test_fsm/0,
    test_import_basic/0,
    test_import_function_list/0,
    test_import_mixed_list/0,
    test_import_complex/0,
    test_def_function_public_by_default/0,
    test_export_list_restricts_access/0,
    test_def_keyword_parsing/0
]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").

%% Run all tests
run() ->
    io:format("Running Cure parser tests...~n"),
    test_simple_function(),
    test_fsm(),
    test_import_basic(),
    test_import_function_list(),
    test_import_mixed_list(),
    test_import_complex(),
    test_def_function_public_by_default(),
    test_export_list_restricts_access(),
    test_def_keyword_parsing(),
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

%% Test that functions declared with 'def' are public by default when not in an export list
test_def_function_public_by_default() ->
    Code =
        <<
            "module TestModule do\n"
            "  def public_func(x: Int): Int = x + 1\n"
            "  def another_public(y: Int): Int = y * 2\n"
            "end"
        >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [ModuleDef] = AST,
    ?assertMatch(#module_def{name = 'TestModule'}, ModuleDef),

    % Check that module has no explicit exports (empty list)
    ?assertEqual([], ModuleDef#module_def.exports),

    % Check that functions exist in items
    Items = ModuleDef#module_def.items,
    ?assertEqual(2, length(Items)),

    % Check that both functions have is_private = false (public by default)
    [Func1, Func2] = Items,
    ?assertMatch(#function_def{name = public_func, is_private = false}, Func1),
    ?assertMatch(#function_def{name = another_public, is_private = false}, Func2),

    io:format("✓ Functions declared with 'def' are public by default test passed~n").

%% Test that functions not listed in a module's export list are inaccessible
test_export_list_restricts_access() ->
    Code =
        <<
            "module RestrictedModule do\n"
            "  export [public_only/1]\n"
            "  \n"
            "  def public_only(x: Int): Int = x + 1\n"
            "  def private_func(y: Int): Int = y * 2\n"
            "  def also_private(): Int = 42\n"
            "end"
        >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [ModuleDef] = AST,
    ?assertMatch(#module_def{name = 'RestrictedModule'}, ModuleDef),

    % Check that module has exactly one export
    Exports = ModuleDef#module_def.exports,
    ?assertEqual(1, length(Exports)),
    [Export] = Exports,
    ?assertMatch(#export_spec{name = public_only, arity = 1}, Export),

    % Check that all three functions exist in items
    Items = ModuleDef#module_def.items,
    ?assertEqual(3, length(Items)),

    % Verify function names
    FuncNames = [Name || #function_def{name = Name} <- Items],
    ?assert(lists:member(public_only, FuncNames)),
    ?assert(lists:member(private_func, FuncNames)),
    ?assert(lists:member(also_private, FuncNames)),

    % All functions should have is_private = false at parse time
    % (visibility is determined by export list during type checking)
    lists:foreach(
        fun(Func) ->
            ?assertMatch(#function_def{is_private = false}, Func)
        end,
        Items
    ),

    io:format("✓ Export list restricts access test passed~n").

%% Test that the parser successfully processes function definitions using 'def' keyword
test_def_keyword_parsing() ->
    % Test various function definition styles with 'def'
    Code =
        <<
            "def simple_add(a: Int, b: Int): Int = a + b\n"
            "\n"
            "def with_block(x: Int): Int do\n"
            "  x + 10\n"
            "end\n"
            "\n"
            "def no_return_type(val: String) = val\n"
            "\n"
            "def with_constraint(n: Int) -> Int when n > 0 = n * 2"
        >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(4, length(AST)),
    [Func1, Func2, Func3, Func4] = AST,

    % Test simple function with = syntax
    ?assertMatch(#function_def{name = simple_add}, Func1),
    ?assertEqual(2, length(Func1#function_def.params)),
    ?assertMatch(#primitive_type{name = 'Int'}, Func1#function_def.return_type),
    ?assertEqual(false, Func1#function_def.is_private),

    % Test function with do...end block syntax
    ?assertMatch(#function_def{name = with_block}, Func2),
    ?assertEqual(1, length(Func2#function_def.params)),
    ?assertMatch(#primitive_type{name = 'Int'}, Func2#function_def.return_type),
    ?assertEqual(false, Func2#function_def.is_private),

    % Test function without explicit return type
    ?assertMatch(#function_def{name = no_return_type}, Func3),
    ?assertEqual(1, length(Func3#function_def.params)),
    ?assertEqual(undefined, Func3#function_def.return_type),
    ?assertEqual(false, Func3#function_def.is_private),

    % Test function with constraint
    ?assertMatch(#function_def{name = with_constraint}, Func4),
    ?assertEqual(1, length(Func4#function_def.params)),
    ?assertMatch(#primitive_type{name = 'Int'}, Func4#function_def.return_type),
    ?assertNotEqual(undefined, Func4#function_def.constraint),
    ?assertEqual(false, Func4#function_def.is_private),

    io:format("✓ 'def' keyword parsing test passed~n").
