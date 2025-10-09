%% Test for Extended Syntax Features in Cure Parser
%% Tests guards in pattern matching and type parameters
-module(extended_syntax_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast_simple.hrl").

%% Run all extended syntax tests
run() ->
    io:format("Running Extended Syntax tests...~n"),
    setup(),
    try
        guards_in_match_test(),
        type_parameters_test(),
        import_arity_test(),
        complex_guards_test(),
        std_demo_parsing_test(),
        io:format("All extended syntax tests passed!~n")
    after
        teardown(ok)
    end.

%% Helper functions for testing
setup() ->
    application:ensure_all_started(cure).

teardown(_) ->
    ok.

%% Test guards in pattern matching
guards_in_match_test() ->
    Code =
        <<
            "\n"
            "        module TestModule do\n"
            "          def test_guards(x: Int): String =\n"
            "            match x do\n"
            "              n when n > 0 -> \"positive\"\n"
            "              n when n < 0 -> \"negative\"\n"
            "              _ -> \"zero\"\n"
            "            end\n"
            "        end\n"
            "    "
        >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    % Extract the module
    [Module] = AST,
    ?assertMatch(#module_def{}, Module),

    % Extract the function
    [Function] = Module#module_def.items,
    ?assertMatch(#function_def{}, Function),

    % Extract the match expression
    MatchExpr = Function#function_def.body,
    ?assertMatch(#match_expr{}, MatchExpr),

    % Check that we have 3 match clauses
    Patterns = MatchExpr#match_expr.patterns,
    ?assertEqual(3, length(Patterns)),

    % Check first clause has a guard
    [FirstClause, SecondClause, ThirdClause] = Patterns,
    ?assertMatch(#match_clause{guard = Guard} when Guard =/= undefined, FirstClause),
    ?assertMatch(#match_clause{guard = Guard} when Guard =/= undefined, SecondClause),
    ?assertMatch(#match_clause{guard = undefined}, ThirdClause).

%% Test type parameters in type definitions
type_parameters_test() ->
    Code =
        <<
            "\n"
            "        module TestModule do\n"
            "          type Optional(T) = T\n"
            "          type Pair(T, U) = T  \n"
            "          type Simple = Int\n"
            "        end\n"
            "    "
        >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    % Extract the module
    [Module] = AST,
    ?assertMatch(#module_def{}, Module),

    % Extract the type definitions
    [OptionalType, PairType, SimpleType] = Module#module_def.items,

    % Check Optional(T)
    ?assertMatch(#type_def{name = 'Optional', params = ['T']}, OptionalType),

    % Check Pair(T, U)
    ?assertMatch(#type_def{name = 'Pair', params = ['T', 'U']}, PairType),

    % Check Simple (no parameters)
    ?assertMatch(#type_def{name = 'Simple', params = []}, SimpleType).

%% Test function arity specifications in import lists
import_arity_test() ->
    Code =
        <<
            "\n"
            "        module TestModule do\n"
            "          import Std [abs/1, sqrt/1, map/2, filter/2]\n"
            "          import Std.Math [sin/1, cos/1]\n"
            "          import Types [Option, Result]\n"
            "        end\n"
            "    "
        >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    % Extract the module
    [Module] = AST,
    ?assertMatch(#module_def{}, Module),

    % Extract the imports
    [StdImport, _MathImport, TypesImport] = Module#module_def.items,

    % Check Std import with arity specifications
    ?assertMatch(#import_def{module = 'Std'}, StdImport),
    StdItems = StdImport#import_def.items,
    ?assertEqual(4, length(StdItems)),

    % Check that we have function imports with arity
    [AbsImport | _] = StdItems,
    ?assertMatch(#function_import{name = abs, arity = 1}, AbsImport),

    % Check Types import (plain identifiers)
    ?assertMatch(#import_def{module = 'Types'}, TypesImport),
    TypesItems = TypesImport#import_def.items,
    ?assertEqual(2, length(TypesItems)),
    [OptionImport, ResultImport] = TypesItems,
    ?assertEqual('Option', OptionImport),
    ?assertEqual('Result', ResultImport).

%% Test complex guard expressions
complex_guards_test() ->
    Code =
        <<
            "\n"
            "        module TestModule do\n"
            "          def classify(x: Int, y: Int): String =\n"
            "            match {x, y} do\n"
            "              {a, b} when a > 0 and b > 0 -> \"both_positive\"\n"
            "              {a, b} when a < 0 or b < 0 -> \"at_least_one_negative\"\n"
            "              _ -> \"mixed\"\n"
            "            end\n"
            "        end\n"
            "    "
        >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    % Extract the module
    [Module] = AST,
    ?assertMatch(#module_def{}, Module),

    % Extract the function
    [Function] = Module#module_def.items,
    ?assertMatch(#function_def{}, Function),

    % Extract the match expression
    MatchExpr = Function#function_def.body,
    ?assertMatch(#match_expr{}, MatchExpr),

    % Check that we have 3 match clauses with proper guard handling
    Patterns = MatchExpr#match_expr.patterns,
    ?assertEqual(3, length(Patterns)),

    % Check that first two clauses have guards
    [FirstClause, SecondClause, ThirdClause] = Patterns,
    ?assertMatch(#match_clause{guard = Guard} when Guard =/= undefined, FirstClause),
    ?assertMatch(#match_clause{guard = Guard} when Guard =/= undefined, SecondClause),
    ?assertMatch(#match_clause{guard = undefined}, ThirdClause).

%% Test that the std_demo.cure file now parses correctly
std_demo_parsing_test() ->
    {ok, Tokens} = cure_lexer:tokenize_file(
        "/opt/Proyectos/Ammotion/cure/lib/examples/std_demo.cure"
    ),
    Result = cure_parser:parse(Tokens),
    ?assertMatch({ok, _}, Result).
