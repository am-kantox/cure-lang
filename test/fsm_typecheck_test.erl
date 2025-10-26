%% Cure Programming Language - FSM Type Checking Tests
-module(fsm_typecheck_test).

-export([run/0, test_turnstile_fsm/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").

%% Run all tests
run() ->
    cure_utils:debug("Running FSM type checking tests...~n"),
    test_turnstile_fsm(),
    cure_utils:debug("All FSM type checking tests passed!~n").

%% Test simple turnstile FSM type checking
test_turnstile_fsm() ->
    Code =
        <<
            "fsm TurnstilePayload{coins_inserted: 0, people_passed: 0} do\n"
            "    Locked --> |insert_coin| Ready\n"
            "    Ready --> |push| Unlocked\n"
            "    Unlocked --> |pass| Locked\n"
            "end"
        >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    % Type check the FSM
    Result = cure_typechecker:check_program(AST),
    io:format("Result: ~p~n", [Result]),

    % Pattern match to extract fields (record is opaque)
    {typecheck_result, Success, Type, Errors, _Warnings} = Result,

    ?assertEqual(true, Success),
    ?assertEqual([], Errors),
    % Should have FSM type in result
    ?assertMatch({fsm_type, 'TurnstilePayload', _, _}, Type),

    cure_utils:debug("✓ Turnstile FSM type checking passed~n").
