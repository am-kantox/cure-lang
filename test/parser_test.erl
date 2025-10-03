%% Cure Programming Language - Parser Tests
-module(parser_test).

-export([run/0, test_simple_function/0, test_fsm/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast_simple.hrl").

%% Run all tests
run() ->
    io:format("Running Cure parser tests...~n"),
    test_simple_function(),
    test_fsm(),
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
    Code = <<"fsm Counter do
              states: [Zero, Positive]
              initial: Zero
              
              state Zero do
                event(:increment) -> Positive
              end
              
              state Positive do
                event(:reset) -> Zero
              end
            end">>,
    
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),
    
    ?assertEqual(1, length(AST)),
    [FSMDef] = AST,
    ?assertMatch(#fsm_def{name = 'Counter'}, FSMDef),
    ?assertEqual(['Zero', 'Positive'], FSMDef#fsm_def.states),
    ?assertEqual('Zero', FSMDef#fsm_def.initial),
    ?assertEqual(2, length(FSMDef#fsm_def.state_defs)),
    
    io:format("✓ FSM parsing test passed~n").