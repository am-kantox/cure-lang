%% Cure Programming Language - Atom Bridge Tests
%% Tests for Atom type bridge to Erlang native atoms
-module(atom_bridge_test).

-export([
    run/0,
    test_atom_lexing/0,
    test_atom_parsing/0,
    test_atom_type_inference/0,
    test_atom_codegen/0,
    test_atom_pattern_matching/0
]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").

% Include inference_result record definition
-record(inference_result, {
    type,
    constraints,
    substitution
}).

run() ->
    cure_utils:debug("Running Atom bridge tests...~n"),
    test_atom_lexing(),
    test_atom_parsing(),
    test_atom_type_inference(),
    test_atom_codegen(),
    test_atom_pattern_matching(),
    cure_utils:debug("All Atom bridge tests passed!~n").

%% Test atom lexing
test_atom_lexing() ->
    % Test unquoted atoms
    {ok, Tokens1} = cure_lexer:tokenize(<<":ok :error :my_atom">>),
    AtomValues1 = [T#token.value || T <- Tokens1, T#token.type =:= atom],
    ?assertEqual([ok, error, my_atom], AtomValues1),

    % Test quoted atoms with spaces
    {ok, Tokens2} = cure_lexer:tokenize(<<"'hello world' 'another atom'">>),
    AtomValues2 = [T#token.value || T <- Tokens2, T#token.type =:= atom],
    ?assertEqual(['hello world', 'another atom'], AtomValues2),

    % Test atoms in expressions
    {ok, Tokens3} = cure_lexer:tokenize(<<"let x = :ok">>),
    TokenTypes3 = [T#token.type || T <- Tokens3],
    ?assert(lists:member(atom, TokenTypes3)),

    cure_utils:debug("✓ Atom lexing tests passed~n").

%% Test atom parsing
test_atom_parsing() ->
    % Parse atom in function
    Code = <<
        "module Test do\n"
        "  export [get_status/0]\n"
        "  def get_status(): Atom = :ok\n"
        "end"
    >>,
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, _AST} = cure_parser:parse(Tokens),

    % Parse function with atom pattern matching
    Code2 = <<
        "module Test2 do\n"
        "  export [describe/1]\n"
        "  def describe(x: Atom): String =\n"
        "    match x do\n"
        "      :ok -> \"success\"\n"
        "      :error -> \"failure\"\n"
        "      _ -> \"unknown\"\n"
        "    end\n"
        "end"
    >>,
    {ok, Tokens2} = cure_lexer:tokenize(Code2),
    {ok, _AST2} = cure_parser:parse(Tokens2),

    cure_utils:debug("✓ Atom parsing tests passed~n").

%% Test atom type inference
test_atom_type_inference() ->
    % Create environment
    Env = cure_types:new_env(),

    % Test atom literal type inference
    AtomExpr = #literal_expr{value = hello, location = {location, 1, 1, undefined}},
    {ok, Result} = cure_types:infer_type(AtomExpr, Env),
    AtomType = Result#inference_result.type,
    ?assertEqual({primitive_type, 'Atom'}, AtomType),

    % Test different atom values
    Atoms = [ok, error, success, failure, my_atom],
    lists:foreach(
        fun(A) ->
            Expr = #literal_expr{value = A, location = {location, 1, 1, undefined}},
            {ok, Res} = cure_types:infer_type(Expr, Env),
            Type = Res#inference_result.type,
            ?assertEqual({primitive_type, 'Atom'}, Type)
        end,
        Atoms
    ),

    cure_utils:debug("✓ Atom type inference tests passed~n").

%% Test atom code generation
test_atom_codegen() ->
    Location = {location, 1, 1, undefined},

    % Test atom value compilation
    AtomForm1 = cure_codegen:compile_value_to_erlang_form(hello, Location),
    ?assertEqual({atom, 1, hello}, AtomForm1),

    AtomForm2 = cure_codegen:compile_value_to_erlang_form(ok, Location),
    ?assertEqual({atom, 1, ok}, AtomForm2),

    AtomForm3 = cure_codegen:compile_value_to_erlang_form(my_atom, Location),
    ?assertEqual({atom, 1, my_atom}, AtomForm3),

    cure_utils:debug("✓ Atom code generation tests passed~n").

%% Test atom pattern matching
test_atom_pattern_matching() ->
    Location = {location, 1, 1, undefined},

    % Test literal atom pattern
    Pattern1 = #literal_pattern{value = ok, location = Location},
    ErlangPattern1 = cure_codegen:convert_pattern_to_erlang_form(Pattern1, Location),
    ?assertEqual({atom, 1, ok}, ErlangPattern1),

    Pattern2 = #literal_pattern{value = error, location = Location},
    ErlangPattern2 = cure_codegen:convert_pattern_to_erlang_form(Pattern2, Location),
    ?assertEqual({atom, 1, error}, ErlangPattern2),

    cure_utils:debug("✓ Atom pattern matching tests passed~n").

%% Helper function to extract first expression from parsed AST
extract_first_expr(#module_def{items = Items}) ->
    extract_first_expr_from_items(Items);
extract_first_expr(_) ->
    undefined.

extract_first_expr_from_items([]) ->
    undefined;
extract_first_expr_from_items([#function_def{body = Body} | _]) when Body =/= undefined ->
    Body;
extract_first_expr_from_items([_ | Rest]) ->
    extract_first_expr_from_items(Rest).
