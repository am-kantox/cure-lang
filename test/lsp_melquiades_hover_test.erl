-module(lsp_melquiades_hover_test).
-export([run/0, test_melquiades_hover/0]).

-include("../src/parser/cure_ast.hrl").

run() ->
    io:format("Running Melquiades operator LSP hover tests...~n"),
    test_melquiades_hover(),
    io:format("All tests passed!~n"),
    ok.

test_melquiades_hover() ->
    io:format("  Testing hover on |-> operator...~n"),

    % Test code with Melquiades operator
    Code = <<
        "module Test do\n"
        "  def send_msg(): Unit = (\n"
        "    let msg = \"hello\"\n"
        "    msg |-> :server\n"
        "  )\n"
        "end\n"
    >>,

    % Cursor position on the |-> operator (line 3, character 8-10)
    Line = 3,
    % Middle of |->
    Character = 9,

    % Get hover info
    Result = cure_lsp_analyzer:get_hover_info(Code, Line, Character),

    % Verify we got hover info
    case Result of
        null ->
            io:format("    FAIL: Expected hover info but got null~n"),
            error(test_failed);
        #{contents := #{kind := <<"markdown">>, value := Content}} ->
            % Check if the content mentions Melquíades
            case binary:match(Content, <<"Melquíades">>) of
                {_, _} ->
                    io:format("    PASS: Got Melquíades operator hover info~n"),
                    io:format("    Content preview: ~s~n", [
                        binary:part(Content, 0, min(100, byte_size(Content)))
                    ]);
                nomatch ->
                    io:format("    FAIL: Hover content doesn't mention Melquíades~n"),
                    io:format("    Got: ~s~n", [Content]),
                    error(test_failed)
            end;
        Other ->
            io:format("    FAIL: Unexpected result format: ~p~n", [Other]),
            error(test_failed)
    end,

    % Test cursor not on operator (should return null or other symbol info)
    Line2 = 3,
    % On 'msg'
    Character2 = 4,
    Result2 = cure_lsp_analyzer:get_hover_info(Code, Line2, Character2),
    io:format("    Testing cursor not on operator: ~p~n", [Result2]),

    ok.
