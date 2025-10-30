-module(string_lexer_test).
-include_lib("eunit/include/eunit.hrl").

%% ============================================================================
%% String Literal Tests (Double Quotes "")
%% ============================================================================

basic_string_test() ->
    {ok, Tokens} = cure_lexer:scan(<<"\"hello\"">>),
    ?assertMatch([{string, _, "hello"}, {eof, _}], Tokens).

empty_string_test() ->
    {ok, Tokens} = cure_lexer:scan(<<"\"\"">>),
    ?assertMatch([{string, _, ""}, {eof, _}], Tokens).

string_with_spaces_test() ->
    {ok, Tokens} = cure_lexer:scan(<<"\"hello world\"">>),
    ?assertMatch([{string, _, "hello world"}, {eof, _}], Tokens).

string_with_numbers_test() ->
    {ok, Tokens} = cure_lexer:scan(<<"\"hello123\"">>),
    ?assertMatch([{string, _, "hello123"}, {eof, _}], Tokens).

%% ============================================================================
%% String Escape Sequences
%% ============================================================================

string_escape_newline_test() ->
    {ok, Tokens} = cure_lexer:scan(<<"\"line1\\nline2\"">>),
    [{string, _, Value}, {eof, _}] = Tokens,
    ?assertEqual("line1\nline2", Value).

string_escape_tab_test() ->
    {ok, Tokens} = cure_lexer:scan(<<"\"hello\\tworld\"">>),
    [{string, _, Value}, {eof, _}] = Tokens,
    ?assertEqual("hello\tworld", Value).

string_escape_backslash_test() ->
    {ok, Tokens} = cure_lexer:scan(<<"\"path\\\\to\\\\file\"">>),
    [{string, _, Value}, {eof, _}] = Tokens,
    ?assertEqual("path\\to\\file", Value).

string_escape_quote_test() ->
    {ok, Tokens} = cure_lexer:scan(<<"\"say \\\"hello\\\"\"">>),
    [{string, _, Value}, {eof, _}] = Tokens,
    ?assertEqual("say \"hello\"", Value).

%% ============================================================================
%% Unicode String Tests
%% ============================================================================

unicode_string_basic_test() ->
    {ok, Tokens} = cure_lexer:scan(<<"\"Hello 世界\"">>),
    ?assertMatch([{string, _, _}, {eof, _}], Tokens).

unicode_string_emoji_test() ->
    {ok, Tokens} = cure_lexer:scan(<<"\"Hello 🌍\"">>),
    [{string, _, Value}, {eof, _}] = Tokens,
    % Just check it's a string
    ?assert(is_list(Value)).

unicode_string_mixed_test() ->
    {ok, Tokens} = cure_lexer:scan(<<"\"Café ☕ 日本語\"">>),
    [{string, _, Value}, {eof, _}] = Tokens,
    ?assert(is_list(Value)).

%% ============================================================================
%% Charlist Literal Tests (Unicode Quotes '')
%% ============================================================================

basic_charlist_test() ->
    % Unicode quotes: U+2018 (') and U+2019 (')
    % UTF-8 bytes: E2 80 98 and E2 80 99
    {ok, Tokens} = cure_lexer:scan(<<226, 128, 152, "hello", 226, 128, 153>>),
    [{charlist, _, Value}, {eof, _}] = Tokens,
    % Charlist is stored as list of codepoints
    ?assertEqual([104, 101, 108, 108, 111], Value).

empty_charlist_test() ->
    {ok, Tokens} = cure_lexer:scan(<<226, 128, 152, 226, 128, 153>>),
    [{charlist, _, Value}, {eof, _}] = Tokens,
    ?assertEqual([], Value).

single_char_charlist_test() ->
    {ok, Tokens} = cure_lexer:scan(<<226, 128, 152, "A", 226, 128, 153>>),
    [{charlist, _, Value}, {eof, _}] = Tokens,
    ?assertEqual([65], Value).

charlist_with_spaces_test() ->
    {ok, Tokens} = cure_lexer:scan(<<226, 128, 152, "h e l l o", 226, 128, 153>>),
    [{charlist, _, Value}, {eof, _}] = Tokens,
    ?assertEqual([104, 32, 101, 32, 108, 32, 108, 32, 111], Value).

%% ============================================================================
%% Charlist Escape Sequences
%% ============================================================================

charlist_escape_newline_test() ->
    {ok, Tokens} = cure_lexer:scan(<<226, 128, 152, "a\\nb", 226, 128, 153>>),
    [{charlist, _, Value}, {eof, _}] = Tokens,
    ?assertEqual([97, 10, 98], Value).

charlist_escape_tab_test() ->
    {ok, Tokens} = cure_lexer:scan(<<226, 128, 152, "a\\tb", 226, 128, 153>>),
    [{charlist, _, Value}, {eof, _}] = Tokens,
    ?assertEqual([97, 9, 98], Value).

charlist_escape_backslash_test() ->
    {ok, Tokens} = cure_lexer:scan(<<226, 128, 152, "a\\\\b", 226, 128, 153>>),
    [{charlist, _, Value}, {eof, _}] = Tokens,
    ?assertEqual([97, 92, 98], Value).

%% ============================================================================
%% Unicode Charlist Tests
%% ============================================================================

unicode_charlist_test() ->
    % Build proper UTF-8 encoded charlist input
    Input = iolist_to_binary([<<226, 128, 152>>, <<"café"/utf8>>, <<226, 128, 153>>]),
    {ok, Tokens} = cure_lexer:scan(Input),
    [{charlist, _, Value}, {eof, _}] = Tokens,
    ?assertEqual([99, 97, 102, 233], Value).

unicode_charlist_chinese_test() ->
    % Build proper UTF-8 encoded charlist input
    Input = iolist_to_binary([<<226, 128, 152>>, <<"世界"/utf8>>, <<226, 128, 153>>]),
    {ok, Tokens} = cure_lexer:scan(Input),
    [{charlist, _, Value}, {eof, _}] = Tokens,
    % 世 = 19990, 界 = 30028
    ?assertEqual([19990, 30028], Value).

unicode_charlist_emoji_test() ->
    % Build proper UTF-8 encoded charlist input: 😀 = U+1F600 = 128512
    Input = iolist_to_binary([<<226, 128, 152>>, <<"😀"/utf8>>, <<226, 128, 153>>]),
    {ok, Tokens} = cure_lexer:scan(Input),
    [{charlist, _, Value}, {eof, _}] = Tokens,
    ?assertEqual([128512], Value).

%% ============================================================================
%% String Concatenation Operator <>
%% ============================================================================

concat_operator_test() ->
    {ok, Tokens} = cure_lexer:scan(<<"\"hello\" <> \"world\"">>),
    ?assertMatch(
        [{string, _, "hello"}, {'<>', _}, {string, _, "world"}, {eof, _}],
        Tokens
    ).

concat_in_expression_test() ->
    {ok, Tokens} = cure_lexer:scan(<<"let x = \"a\" <> \"b\"">>),
    ?assertMatch(
        [
            {'let', _},
            {identifier, _, "x"},
            {'=', _},
            {string, _, "a"},
            {'<>', _},
            {string, _, "b"},
            {eof, _}
        ],
        Tokens
    ).

%% ============================================================================
%% String Interpolation Tests
%% ============================================================================

string_interpolation_basic_test() ->
    {ok, Tokens} = cure_lexer:scan(<<"\"Hello #{name}!\"">>),
    % Should produce multiple tokens for interpolation
    ?assert(length(Tokens) > 3).

string_interpolation_multiple_test() ->
    {ok, Tokens} = cure_lexer:scan(<<"\"#{x} + #{y} = #{z}\"">>),
    ?assert(length(Tokens) > 5).

%% ============================================================================
%% Error Cases
%% ============================================================================

unterminated_string_test() ->
    Result = cure_lexer:scan(<<"\"hello">>),
    ?assertMatch({error, {unterminated_string, _, _}}, Result).

unterminated_charlist_test() ->
    Result = cure_lexer:scan(<<226, 128, 152, "hello">>),
    ?assertMatch({error, {{unterminated_charlist, _, _}, _, _}}, Result).

%% ============================================================================
%% Mixed Code Tests
%% ============================================================================

string_in_function_test() ->
    {ok, Tokens} = cure_lexer:scan(<<"def greet() = \"Hello\"">>),
    ?assertMatch(
        [
            {def, _},
            {identifier, _, "greet"},
            {'(', _},
            {')', _},
            {'=', _},
            {string, _, "Hello"},
            {eof, _}
        ],
        Tokens
    ).

charlist_in_function_test() ->
    Input = iolist_to_binary([
        "def chars() = ",
        <<226, 128, 152>>,
        "abc",
        <<226, 128, 153>>
    ]),
    {ok, Tokens} = cure_lexer:scan(Input),
    ?assertMatch(
        [
            {def, _},
            {identifier, _, "chars"},
            {'(', _},
            {')', _},
            {'=', _},
            {charlist, _, [97, 98, 99]},
            {eof, _}
        ],
        Tokens
    ).

string_and_charlist_together_test() ->
    Input = iolist_to_binary([
        "\"string\" <> ",
        <<226, 128, 152>>,
        "chars",
        <<226, 128, 153>>
    ]),
    {ok, Tokens} = cure_lexer:scan(Input),
    ?assertMatch(
        [{string, _, "string"}, {'<>', _}, {charlist, _, _}, {eof, _}],
        Tokens
    ).

%% ============================================================================
%% Backward Compatibility Tests (ASCII single quote for atoms)
%% ============================================================================

ascii_single_quote_atom_test() ->
    {ok, Tokens} = cure_lexer:scan(<<"'atom_name'">>),
    [{atom, _, Value}, {eof, _}] = Tokens,
    ?assertEqual(atom_name, Value).

atom_vs_charlist_distinction_test() ->
    % ASCII single quote = atom
    {ok, AtomTokens} = cure_lexer:scan(<<"'atom'">>),
    ?assertMatch([{atom, _, atom}, {eof, _}], AtomTokens),
    % Unicode single quotes = charlist
    {ok, CharlistTokens} = cure_lexer:scan(<<226, 128, 152, "atom", 226, 128, 153>>),
    ?assertMatch([{charlist, _, _}, {eof, _}], CharlistTokens).
