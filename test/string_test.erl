-module(string_test).

%% Comprehensive tests for Cure string implementation
%% Covers lexer, parser, type system, runtime, and standard library

-export([run/0]).

run() ->
    io:format("Running Cure String Tests~n"),
    io:format("========================~n~n"),

    % Basic string operations
    test_basic_strings(),
    test_charlists(),
    test_string_concatenation(),

    % Conversions
    test_conversions(),

    % String manipulation
    test_string_slicing(),
    test_string_splitting(),
    test_string_trimming(),

    % Case transformations
    test_case_transformations(),

    % Predicates
    test_string_predicates(),

    % Pattern matching
    test_pattern_matching(),

    % Unicode support
    test_unicode_operations(),

    % Utilities
    test_string_utilities(),

    io:format("~n========================~n"),
    io:format("All string tests passed!~n"),
    ok.

%% ============================================================================
%% Basic String Operations
%% ============================================================================

test_basic_strings() ->
    io:format("Testing basic strings...~n"),

    % String literals
    S1 = <<"hello">>,
    S2 = <<"world">>,

    assert_equal(<<"hello">>, S1, "string literal"),
    assert_equal(true, is_binary(S1), "string is binary"),

    % Empty string
    Empty = <<>>,
    assert_equal(<<>>, Empty, "empty string"),

    % String with Unicode
    Unicode = <<"世界"/utf8>>,
    assert_equal(true, is_binary(Unicode), "unicode string is binary"),

    io:format("  ✓ Basic strings passed~n"),
    ok.

test_charlists() ->
    io:format("Testing charlists...~n"),

    % Charlist literals (represented as Erlang lists)

    % "hello"
    C1 = [104, 101, 108, 108, 111],
    assert_equal([104, 101, 108, 108, 111], C1, "charlist literal"),
    assert_equal(true, is_list(C1), "charlist is list"),

    % Unicode charlist

    % 世界
    UnicodeCharlist = [19990, 30028],
    assert_equal(true, is_list(UnicodeCharlist), "unicode charlist is list"),

    io:format("  ✓ Charlists passed~n"),
    ok.

test_string_concatenation() ->
    io:format("Testing string concatenation...~n"),

    % Using cure_string_native:concat/2
    S1 = <<"hello">>,
    S2 = <<" ">>,
    S3 = <<"world">>,

    Result = cure_string_native:concat(S1, S2),
    assert_equal(<<"hello ">>, Result, "concat two strings"),

    Result2 = cure_string_native:concat(Result, S3),
    assert_equal(<<"hello world">>, Result2, "concat multiple strings"),

    % Empty string concatenation
    EmptyResult = cure_string_native:concat(<<>>, <<"test">>),
    assert_equal(<<"test">>, EmptyResult, "concat with empty string"),

    io:format("  ✓ String concatenation passed~n"),
    ok.

%% ============================================================================
%% Conversions
%% ============================================================================

test_conversions() ->
    io:format("Testing conversions...~n"),

    % String to charlist
    String = <<"hello">>,
    Charlist = cure_string_native:to_charlist(String),
    assert_equal([104, 101, 108, 108, 111], Charlist, "string to charlist"),

    % Charlist to string
    BackToString = cure_string_native:from_charlist(Charlist),
    assert_equal(String, BackToString, "charlist to string"),

    % Binary validation
    ValidBinary = <<"test">>,
    {ok, ValidString} = cure_string_native:from_binary(ValidBinary),
    assert_equal(<<"test">>, ValidString, "valid binary to string"),

    % Invalid UTF-8 binary
    InvalidBinary = <<255, 255>>,
    {error, invalid_utf8} = cure_string_native:from_binary(InvalidBinary),

    % String to atom
    AtomResult = cure_string_native:to_atom(<<"test">>),
    assert_equal(test, AtomResult, "string to atom"),

    io:format("  ✓ Conversions passed~n"),
    ok.

%% ============================================================================
%% String Manipulation
%% ============================================================================

test_string_slicing() ->
    io:format("Testing string slicing...~n"),

    String = <<"hello world">>,

    % Length
    Len = cure_string_native:length(String),
    assert_equal(11, Len, "string length"),

    % Byte size
    ByteSize = cure_string_native:byte_size(String),
    assert_equal(11, ByteSize, "string byte size"),

    % Slice
    Slice1 = cure_string_native:slice(String, 0, 5),
    assert_equal(<<"hello">>, Slice1, "slice from start"),

    Slice2 = cure_string_native:slice(String, 6, 5),
    assert_equal(<<"world">>, Slice2, "slice from middle"),

    % At
    {ok, Char} = cure_string_native:at(String, 0),
    assert_equal(<<"h">>, Char, "get character at index"),

    {error, out_of_bounds} = cure_string_native:at(String, 100),

    % First and last
    {ok, First} = cure_string_native:first(String),
    assert_equal(<<"h">>, First, "get first character"),

    {ok, Last} = cure_string_native:last(String),
    assert_equal(<<"d">>, Last, "get last character"),

    {error, empty_string} = cure_string_native:first(<<>>),

    io:format("  ✓ String slicing passed~n"),
    ok.

test_string_splitting() ->
    io:format("Testing string splitting...~n"),

    % Split by delimiter
    CSV = <<"a,b,c">>,
    Parts = cure_string_native:split(CSV, <<",">>),
    assert_equal([<<"a">>, <<"b">>, <<"c">>], Parts, "split by comma"),

    % Split at index
    String = <<"hello world">>,
    {Left, Right} = cure_string_native:split_at(String, 5),
    assert_equal(<<"hello">>, Left, "split left part"),
    assert_equal(<<" world">>, Right, "split right part"),

    % Join
    Words = [<<"hello">>, <<"world">>],
    Joined = cure_string_native:join(Words, <<" ">>),
    assert_equal(<<"hello world">>, Joined, "join strings"),

    EmptyJoined = cure_string_native:join([], <<",">>),
    assert_equal(<<>>, EmptyJoined, "join empty list"),

    io:format("  ✓ String splitting passed~n"),
    ok.

test_string_trimming() ->
    io:format("Testing string trimming...~n"),

    % Trim both sides
    Padded = <<"  hello  ">>,
    Trimmed = cure_string_native:trim(Padded),
    assert_equal(<<"hello">>, Trimmed, "trim both sides"),

    % Trim left
    TrimmedLeft = cure_string_native:trim_left(Padded),
    assert_equal(<<"hello  ">>, TrimmedLeft, "trim left"),

    % Trim right
    TrimmedRight = cure_string_native:trim_right(Padded),
    assert_equal(<<"  hello">>, TrimmedRight, "trim right"),

    % No whitespace
    NoSpace = <<"hello">>,
    assert_equal(NoSpace, cure_string_native:trim(NoSpace), "trim no whitespace"),

    io:format("  ✓ String trimming passed~n"),
    ok.

%% ============================================================================
%% Case Transformations
%% ============================================================================

test_case_transformations() ->
    io:format("Testing case transformations...~n"),

    String = <<"hello">>,

    % Upcase
    Upper = cure_string_native:upcase(String),
    assert_equal(<<"HELLO">>, Upper, "upcase"),

    % Downcase
    Lower = cure_string_native:downcase(<<"WORLD">>),
    assert_equal(<<"world">>, Lower, "downcase"),

    % Capitalize
    Capitalized = cure_string_native:capitalize(String),
    assert_equal(<<"Hello">>, Capitalized, "capitalize"),

    % Unicode case transformation
    UnicodeString = <<"café"/utf8>>,
    UnicodeUpper = cure_string_native:upcase(UnicodeString),
    assert_equal(<<"CAFÉ"/utf8>>, UnicodeUpper, "unicode upcase"),

    io:format("  ✓ Case transformations passed~n"),
    ok.

%% ============================================================================
%% Predicates
%% ============================================================================

test_string_predicates() ->
    io:format("Testing string predicates...~n"),

    String = <<"hello world">>,

    % Starts with
    assert_equal(true, cure_string_native:starts_with(String, <<"hello">>), "starts with"),
    assert_equal(false, cure_string_native:starts_with(String, <<"world">>), "doesn't start with"),

    % Ends with
    assert_equal(true, cure_string_native:ends_with(String, <<"world">>), "ends with"),
    assert_equal(false, cure_string_native:ends_with(String, <<"hello">>), "doesn't end with"),

    % Contains
    assert_equal(true, cure_string_native:contains(String, <<"lo wo">>), "contains substring"),
    assert_equal(false, cure_string_native:contains(String, <<"xyz">>), "doesn't contain"),

    % Is empty
    assert_equal(true, cure_string_native:is_empty(<<>>), "empty string"),
    assert_equal(false, cure_string_native:is_empty(String), "non-empty string"),

    io:format("  ✓ String predicates passed~n"),
    ok.

%% ============================================================================
%% Pattern Matching
%% ============================================================================

test_pattern_matching() ->
    io:format("Testing pattern matching...~n"),

    String = <<"hello world">>,

    % Replace first occurrence
    Replaced = cure_string_native:replace(String, <<"world">>, <<"cure">>),
    assert_equal(<<"hello cure">>, Replaced, "replace first occurrence"),

    % Replace all occurrences
    Multiple = <<"aaa">>,
    ReplacedAll = cure_string_native:replace_all(Multiple, <<"a">>, <<"b">>),
    assert_equal(<<"bbb">>, ReplacedAll, "replace all occurrences"),

    % No match
    NoMatch = cure_string_native:replace(String, <<"xyz">>, <<"abc">>),
    assert_equal(String, NoMatch, "replace with no match"),

    io:format("  ✓ Pattern matching passed~n"),
    ok.

%% ============================================================================
%% Unicode Operations
%% ============================================================================

test_unicode_operations() ->
    io:format("Testing Unicode operations...~n"),

    % ASCII string
    ASCII = <<"hello">>,
    ASCIIGraphemes = cure_string_native:graphemes(ASCII),
    assert_equal([<<"h">>, <<"e">>, <<"l">>, <<"l">>, <<"o">>], ASCIIGraphemes, "ASCII graphemes"),

    % Unicode string
    Unicode = <<"世界"/utf8>>,
    UnicodeGraphemes = cure_string_native:graphemes(Unicode),
    assert_equal([<<"世"/utf8>>, <<"界"/utf8>>], UnicodeGraphemes, "Unicode graphemes"),

    % Codepoints
    Codepoints = cure_string_native:codepoints(<<"hello">>),
    assert_equal([104, 101, 108, 108, 111], Codepoints, "string codepoints"),

    % Valid UTF-8
    assert_equal(true, cure_string_native:valid_utf8(<<"hello">>), "valid UTF-8"),
    assert_equal(true, cure_string_native:valid_utf8(<<"世界"/utf8>>), "valid UTF-8 unicode"),
    assert_equal(false, cure_string_native:valid_utf8(<<255, 255>>), "invalid UTF-8"),

    io:format("  ✓ Unicode operations passed~n"),
    ok.

%% ============================================================================
%% Utilities
%% ============================================================================

test_string_utilities() ->
    io:format("Testing string utilities...~n"),

    % Reverse
    String = <<"hello">>,
    Reversed = cure_string_native:reverse(String),
    assert_equal(<<"olleh">>, Reversed, "reverse string"),

    % Unicode reverse
    UnicodeString = <<"世界"/utf8>>,
    UnicodeReversed = cure_string_native:reverse(UnicodeString),
    assert_equal(<<"界世"/utf8>>, UnicodeReversed, "reverse unicode string"),

    % Duplicate
    Duplicated = cure_string_native:duplicate(<<"ab">>, 3),
    assert_equal(<<"ababab">>, Duplicated, "duplicate string"),

    % Pad left
    PaddedLeft = cure_string_native:pad_left(<<"hi">>, 5, <<" ">>),
    assert_equal(<<"   hi">>, PaddedLeft, "pad left"),

    % Pad right
    PaddedRight = cure_string_native:pad_right(<<"hi">>, 5, <<" ">>),
    assert_equal(<<"hi   ">>, PaddedRight, "pad right"),

    % No padding needed
    NoPad = cure_string_native:pad_left(<<"hello">>, 3, <<" ">>),
    assert_equal(<<"hello">>, NoPad, "no padding needed"),

    io:format("  ✓ String utilities passed~n"),
    ok.

%% ============================================================================
%% Test Helpers
%% ============================================================================

assert_equal(Expected, Actual, TestName) ->
    case Expected =:= Actual of
        true ->
            ok;
        false ->
            io:format("FAIL: ~s~n", [TestName]),
            io:format("  Expected: ~p~n", [Expected]),
            io:format("  Actual:   ~p~n", [Actual]),
            error({test_failed, TestName})
    end.
