#!/usr/bin/env escript
%% Test code actions for type holes

-module(test_code_actions).
-mode(compile).

-include("../src/parser/cure_ast.hrl").

main(_) ->
    % Add paths
    code:add_pathsa([
        "../_build/ebin",
        "../_build/ebin/lexer",
        "../_build/ebin/parser",
        "../_build/ebin/types",
        "../_build/ebin/codegen",
        "../_build/ebin/fsm",
        "../_build/ebin/smt",
        "../_build/lsp"
    ]),

    io:format("~n=== Testing Code Actions for Type Holes ===~n~n"),

    % Read test file
    {ok, Text} = file:read_file("../examples/type_holes_demo.cure"),
    Uri = <<"file:///opt/Proyectos/Ammotion/cure/examples/type_holes_demo.cure">>,

    % Parse to AST
    {ok, Tokens} = cure_lexer:tokenize(Text),
    {ok, AST} = cure_parser:parse(Tokens),

    % Generate diagnostics
    io:format("Generating diagnostics...~n"),
    Diagnostics = cure_lsp_type_holes:generate_hole_diagnostics(Uri, AST),
    io:format("Found ~p diagnostics~n~n", [length(Diagnostics)]),

    % Print each diagnostic
    lists:foreach(
        fun(Diag) ->
            Code = maps:get(<<"code">>, Diag, undefined),
            Range = maps:get(<<"range">>, Diag, undefined),
            Message = maps:get(<<"message">>, Diag, undefined),
            io:format("Diagnostic:~n"),
            io:format("  Code: ~p~n", [Code]),
            io:format("  Range: ~p~n", [Range]),
            io:format("  Message: ~s~n~n", [Message])
        end,
        Diagnostics
    ),

    % Test code action for first diagnostic (line 12, double_list)
    io:format("~n=== Testing Code Action for Line 12 (double_list) ===~n~n"),
    case Diagnostics of
        [FirstDiag | _] ->
            % Line 12 (0-indexed = 11), column 40
            test_code_action(Uri, FirstDiag, AST, 11, 40);
        [] ->
            io:format("ERROR: No diagnostics found!~n")
    end,

    % Test with second diagnostic if available
    case Diagnostics of
        [_, SecondDiag | _] ->
            io:format("~n=== Testing Code Action for Line 17 (process_data) ===~n~n"),
            % Line 17 (0-indexed = 16), column 36
            test_code_action(Uri, SecondDiag, AST, 16, 36);
        _ ->
            ok
    end,

    io:format("~nTest complete.~n").

test_code_action(Uri, Diag, AST, Line, Char) ->
    % Simulate cursor position
    Range = maps:get(<<"range">>, Diag, undefined),
    io:format("Diagnostic range: ~p~n", [Range]),
    io:format("Cursor position: line=~p, character=~p~n", [Line, Char]),

    % Check if cursor is in range
    #{
        <<"start">> := #{<<"line">> := StartLine, <<"character">> := StartChar},
        <<"end">> := #{<<"line">> := EndLine, <<"character">> := EndChar}
    } = Range,

    InRange =
        (Line =:= StartLine andalso Line =:= EndLine andalso
            Char >= StartChar andalso Char =< EndChar),
    io:format("Cursor in range: ~p~n", [InRange]),

    % Generate code action
    Actions = cure_lsp_type_holes:generate_hole_code_actions(Uri, Diag, AST),
    io:format("Generated ~p actions~n", [length(Actions)]),

    lists:foreach(
        fun(Action) ->
            Title = maps:get(<<"title">>, Action, undefined),
            Kind = maps:get(<<"kind">>, Action, undefined),
            Edit = maps:get(<<"edit">>, Action, undefined),
            io:format("~nAction:~n"),
            io:format("  Title: ~s~n", [Title]),
            io:format("  Kind: ~p~n", [Kind]),
            io:format("  Edit: ~p~n", [Edit])
        end,
        Actions
    ).
