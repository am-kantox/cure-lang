-module(utf8_lexer_error_test).

-export([run/0]).

%% Test UTF-8 character error reporting in lexer
run() ->
    io:format("~n=== UTF-8 Lexer Error Reporting Test ===~n~n"),

    % Test 1: Ellipsis character (U+2026)
    io:format("Test 1: Ellipsis character '…' (U+2026)...~n"),
    Code1 = <<"module Test\n\nfunc foo() -> Int {\n  …\n}">>,
    case cure_lexer:tokenize(Code1) of
        {error, {Reason1, Line1, Col1}} ->
            io:format("  Error at line ~p, column ~p: ~p~n", [Line1, Col1, Reason1]),
            case Reason1 of
                {unexpected_character, Char1} when is_integer(Char1) ->
                    io:format("  Character code: ~p (~c)~n", [Char1, Char1]),
                    io:format("  ✓ PASS - Got Unicode codepoint: ~p~n", [Char1]);
                {unexpected_character, Byte1} ->
                    io:format("  ✗ FAIL - Got byte value instead: ~p~n", [Byte1])
            end;
        {ok, _Tokens1} ->
            io:format("  ✗ FAIL - Should have failed but got tokens~n")
    end,

    % Test 2: Em-dash (U+2014)
    io:format("~nTest 2: Em-dash character '—' (U+2014)...~n"),
    Code2 = <<"x — y">>,
    case cure_lexer:tokenize(Code2) of
        {error, {Reason2, Line2, Col2}} ->
            io:format("  Error at line ~p, column ~p: ~p~n", [Line2, Col2, Reason2]),
            case Reason2 of
                {unexpected_character, Char2} when is_integer(Char2), Char2 > 255 ->
                    io:format("  Character code: ~p~n", [Char2]),
                    io:format("  ✓ PASS - Got Unicode codepoint: ~p~n", [Char2]);
                {unexpected_character, _} ->
                    io:format("  ✗ FAIL - Got byte value instead~n")
            end;
        {ok, _Tokens2} ->
            io:format("  ✗ FAIL - Should have failed but got tokens~n")
    end,

    % Test 3: Greek letter (U+03B1 α)
    io:format("~nTest 3: Greek letter 'α' (U+03B1)...~n"),
    Code3 = <<"x α y">>,
    case cure_lexer:tokenize(Code3) of
        {error, {Reason3, Line3, Col3}} ->
            io:format("  Error at line ~p, column ~p: ~p~n", [Line3, Col3, Reason3]),
            case Reason3 of
                {unexpected_character, 16#03B1} ->
                    io:format("  ✓ PASS - Got correct Greek alpha codepoint~n");
                {unexpected_character, Char3} when is_integer(Char3), Char3 > 255 ->
                    io:format("  ⚠ Got Unicode codepoint but wrong value: ~p~n", [Char3]);
                {unexpected_character, _} ->
                    io:format("  ✗ FAIL - Got byte value instead~n")
            end;
        {ok, _Tokens3} ->
            io:format("  ✗ FAIL - Should have failed but got tokens~n")
    end,

    % Test 4: Emoji (U+1F600 😀)
    io:format("~nTest 4: Emoji '😀' (U+1F600)...~n"),
    Code4 = <<"x 😀 y">>,
    case cure_lexer:tokenize(Code4) of
        {error, {Reason4, Line4, Col4}} ->
            io:format("  Error at line ~p, column ~p: ~p~n", [Line4, Col4, Reason4]),
            case Reason4 of
                {unexpected_character, Char4} when is_integer(Char4), Char4 > 16#FFFF ->
                    io:format("  Character code: ~p (0x~.16B)~n", [Char4, Char4]),
                    io:format("  ✓ PASS - Got 4-byte UTF-8 codepoint~n");
                {unexpected_character, Char4} when is_integer(Char4) ->
                    io:format("  ⚠ Got integer but value seems wrong: ~p (0x~.16B)~n", [
                        Char4, Char4
                    ]);
                {unexpected_character, _} ->
                    io:format("  ✗ FAIL - Got byte value instead~n")
            end;
        {ok, _Tokens4} ->
            io:format("  ✗ FAIL - Should have failed but got tokens~n")
    end,

    % Test 5: Verify location is preserved
    io:format("~nTest 5: Location tracking with UTF-8...~n"),
    Code5 = <<"x = 1\ny = …\nz = 3">>,
    case cure_lexer:tokenize(Code5) of
        {error, {{unexpected_character, _}, Line5, Col5}} ->
            io:format("  Error at line ~p, column ~p~n", [Line5, Col5]),
            if
                Line5 =:= 2 ->
                    io:format("  ✓ PASS - Correct line number~n");
                true ->
                    io:format("  ✗ FAIL - Wrong line: expected 2, got ~p~n", [Line5])
            end;
        {error, {Reason5, Line5, Col5}} ->
            io:format("  Error at line ~p, column ~p: ~p~n", [Line5, Col5, Reason5]),
            io:format("  ⚠ Unexpected error format~n");
        {ok, _Tokens5} ->
            io:format("  ✗ FAIL - Should have failed~n")
    end,

    io:format("~n✓ UTF-8 lexer error reporting tests completed~n"),
    ok.
