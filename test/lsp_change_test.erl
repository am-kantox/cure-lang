-module(lsp_change_test).
-export([run/0]).

run() ->
    io:format("Testing LSP document change handling...~n"),

    % Test 1: Full document sync
    OriginalText = <<"module Test do\n  def foo() = 42\nend">>,
    NewText = <<"module Test do\n  def bar() = 100\nend">>,

    % Change without range (full document sync mode 1)
    Change1 = #{text => NewText},
    Result1 = cure_lsp:apply_single_change(Change1, OriginalText),

    case Result1 =:= NewText of
        true ->
            io:format("✓ Full document sync works~n");
        false ->
            io:format("✗ Full document sync failed~n"),
            io:format("  Expected: ~p~n", [NewText]),
            io:format("  Got: ~p~n", [Result1])
    end,

    % Test 2: Incremental change (single line)
    % Change "42" to "100" at line 1, characters 14-16
    Change2 = #{
        range => #{
            start => #{line => 1, character => 14},
            'end' => #{line => 1, character => 16}
        },
        text => <<"100">>
    },

    try
        Result2 = cure_lsp:apply_single_change(Change2, OriginalText),
        Expected2 = <<"module Test do\n  def foo() = 100\nend">>,

        case Result2 =:= Expected2 of
            true ->
                io:format("✓ Incremental sync works~n");
            false ->
                io:format("✗ Incremental sync failed~n"),
                io:format("  Expected: ~p~n", [Expected2]),
                io:format("  Got: ~p~n", [Result2])
        end
    catch
        Error:Reason ->
            io:format("✗ Incremental sync crashed: ~p:~p~n", [Error, Reason])
    end,

    % Test 3: Insert text
    Change3 = #{
        range => #{
            start => #{line => 1, character => 2},
            'end' => #{line => 1, character => 2}
        },
        text => <<"% comment\n  ">>
    },

    try
        Result3 = cure_lsp:apply_single_change(Change3, OriginalText),
        Expected3 = <<"module Test do\n  % comment\n  def foo() = 42\nend">>,

        case Result3 =:= Expected3 of
            true ->
                io:format("✓ Text insertion works~n");
            false ->
                io:format("✗ Text insertion failed~n"),
                io:format("  Expected: ~p~n", [Expected3]),
                io:format("  Got: ~p~n", [Result3])
        end
    catch
        Error2:Reason2 ->
            io:format("✗ Text insertion crashed: ~p:~p~n", [Error2, Reason2])
    end,

    io:format("~nLSP change handling tests complete.~n"),
    ok.
