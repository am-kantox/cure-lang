-module(cure_string_native).

-moduledoc """
Native Erlang implementations of string operations for Cure.

Provides high-performance string manipulation functions that operate on
UTF-8 binaries (String type) and charlists (Charlist type).
""".

-export([
    % Conversion functions
    to_charlist/1,
    from_charlist/1,
    to_binary/1,
    from_binary/1,
    to_atom/1,

    % String operations
    concat/2,
    length/1,
    byte_size/1,
    is_empty/1,

    % Manipulation
    slice/3,
    at/2,
    first/1,
    last/1,

    % Splitting and joining
    split/2,
    split_at/2,
    join/2,

    % Trimming
    trim/1,
    trim_left/1,
    trim_right/1,

    % Case transformations
    upcase/1,
    downcase/1,
    capitalize/1,

    % Predicates
    starts_with/2,
    ends_with/2,
    contains/2,

    % Pattern matching
    replace/3,
    replace_all/3,

    % Unicode operations
    graphemes/1,
    codepoints/1,
    valid_utf8/1,

    % Utilities
    reverse/1,
    duplicate/2,
    pad_left/3,
    pad_right/3
]).

%% ============================================================================
%% Conversion Functions
%% ============================================================================

-doc """
Convert a UTF-8 string to a charlist.
""".
-spec to_charlist(binary()) -> list().
to_charlist(String) when is_binary(String) ->
    unicode:characters_to_list(String).

-doc """
Convert a charlist to a UTF-8 string.
""".
-spec from_charlist(list()) -> binary().
from_charlist(Charlist) when is_list(Charlist) ->
    unicode:characters_to_binary(Charlist).

-doc """
Convert string to raw binary (identity function for strings).
""".
-spec to_binary(binary()) -> binary().
to_binary(String) when is_binary(String) ->
    String.

-doc """
Convert a binary to a string, validating UTF-8.
Returns {ok, String} or {error, invalid_utf8}.
""".
-spec from_binary(binary()) -> {ok, binary()} | {error, atom()}.
from_binary(Bin) when is_binary(Bin) ->
    case unicode:characters_to_binary(Bin) of
        Bin -> {ok, Bin};
        _ -> {error, invalid_utf8}
    end.

-doc """
Convert string to atom.
""".
-spec to_atom(binary()) -> atom().
to_atom(String) when is_binary(String) ->
    binary_to_atom(String, utf8).

%% ============================================================================
%% String Operations
%% ============================================================================

-doc """
Concatenate two strings efficiently.
""".
-spec concat(binary(), binary()) -> binary().
concat(S1, S2) when is_binary(S1), is_binary(S2) ->
    <<S1/binary, S2/binary>>.

-doc """
Get the length of a string in graphemes (Unicode-aware).
""".
-spec length(binary()) -> non_neg_integer().
length(String) when is_binary(String) ->
    string:length(String).

-doc """
Get the byte size of a string.
""".
-spec byte_size(binary()) -> non_neg_integer().
byte_size(String) when is_binary(String) ->
    erlang:byte_size(String).

-doc """
Check if a string is empty.
""".
-spec is_empty(binary()) -> boolean().
is_empty(<<>>) -> true;
is_empty(_) -> false.

%% ============================================================================
%% Manipulation
%% ============================================================================

-doc """
Extract a substring by grapheme position and length.
""".
-spec slice(binary(), integer(), non_neg_integer()) -> binary().
slice(String, Start, Length) when is_binary(String), is_integer(Start), is_integer(Length) ->
    % Convert to list of graphemes
    Graphemes = collect_graphemes(String, []),
    % Get the slice
    SlicedGraphemes = lists:sublist(Graphemes, Start + 1, Length),
    iolist_to_binary(SlicedGraphemes).

% Helper to collect all graphemes from a string
collect_graphemes(<<>>, Acc) ->
    lists:reverse(Acc);
collect_graphemes(String, Acc) ->
    case string:next_grapheme(String) of
        [] ->
            lists:reverse(Acc);
        [Grapheme | Rest] ->
            % Convert grapheme to binary if it's an integer
            GraphemeBin =
                case is_integer(Grapheme) of
                    true -> <<Grapheme/utf8>>;
                    false -> Grapheme
                end,
            % Rest is the remaining string (binary), not a list
            collect_graphemes(Rest, [GraphemeBin | Acc])
    end.

-doc """
Get the grapheme at a specific index (0-based).
Returns {ok, Grapheme} or {error, out_of_bounds}.
""".
-spec at(binary(), integer()) -> {ok, binary()} | {error, atom()}.
at(String, Index) when is_binary(String), is_integer(Index) ->
    Graphemes = collect_graphemes(String, []),
    case Index >= 0 andalso Index < erlang:length(Graphemes) of
        true -> {ok, lists:nth(Index + 1, Graphemes)};
        false -> {error, out_of_bounds}
    end.

-doc """
Get the first grapheme of a string.
""".
-spec first(binary()) -> {ok, binary()} | {error, atom()}.
first(<<>>) ->
    {error, empty_string};
first(String) when is_binary(String) ->
    case string:next_grapheme(String) of
        [] ->
            {error, empty_string};
        [First | _Rest] ->
            GraphemeBin =
                case is_integer(First) of
                    true -> <<First/utf8>>;
                    false -> First
                end,
            {ok, GraphemeBin}
    end.

-doc """
Get the last grapheme of a string.
""".
-spec last(binary()) -> {ok, binary()} | {error, atom()}.
last(<<>>) ->
    {error, empty_string};
last(String) when is_binary(String) ->
    Graphemes = collect_graphemes(String, []),
    case Graphemes of
        [] -> {error, empty_string};
        _ -> {ok, lists:last(Graphemes)}
    end.

%% ============================================================================
%% Splitting and Joining
%% ============================================================================

-doc """
Split a string by a pattern.
""".
-spec split(binary(), binary()) -> [binary()].
split(String, Pattern) when is_binary(String), is_binary(Pattern) ->
    binary:split(String, Pattern, [global]).

-doc """
Split a string at a specific grapheme index.
""".
-spec split_at(binary(), integer()) -> {binary(), binary()}.
split_at(String, Index) when is_binary(String), is_integer(Index) ->
    Graphemes = collect_graphemes(String, []),
    {Left, Right} = lists:split(min(Index, erlang:length(Graphemes)), Graphemes),
    {iolist_to_binary(Left), iolist_to_binary(Right)}.

-doc """
Join a list of strings with a separator.
""".
-spec join([binary()], binary()) -> binary().
join([], _Sep) ->
    <<>>;
join([H], _Sep) ->
    H;
join([H | T], Sep) when is_binary(Sep) ->
    iolist_to_binary([H | [[Sep, S] || S <- T]]).

%% ============================================================================
%% Trimming
%% ============================================================================

-doc """
Trim whitespace from both ends of a string.
""".
-spec trim(binary()) -> binary().
trim(String) when is_binary(String) ->
    string:trim(String, both).

-doc """
Trim whitespace from the left side of a string.
""".
-spec trim_left(binary()) -> binary().
trim_left(String) when is_binary(String) ->
    string:trim(String, leading).

-doc """
Trim whitespace from the right side of a string.
""".
-spec trim_right(binary()) -> binary().
trim_right(String) when is_binary(String) ->
    string:trim(String, trailing).

%% ============================================================================
%% Case Transformations
%% ============================================================================

-doc """
Convert string to uppercase (Unicode-aware).
""".
-spec upcase(binary()) -> binary().
upcase(String) when is_binary(String) ->
    string:uppercase(String).

-doc """
Convert string to lowercase (Unicode-aware).
""".
-spec downcase(binary()) -> binary().
downcase(String) when is_binary(String) ->
    string:lowercase(String).

-doc """
Capitalize the first grapheme of a string.
""".
-spec capitalize(binary()) -> binary().
capitalize(<<>>) ->
    <<>>;
capitalize(String) when is_binary(String) ->
    case string:next_grapheme(String) of
        [] ->
            <<>>;
        [First | Rest] ->
            % Convert first grapheme to binary if needed
            FirstBin =
                case is_integer(First) of
                    true -> <<First/utf8>>;
                    false -> First
                end,
            iolist_to_binary([string:uppercase(FirstBin), Rest])
    end.

%% ============================================================================
%% Predicates
%% ============================================================================

-doc """
Check if a string starts with a given prefix.
""".
-spec starts_with(binary(), binary()) -> boolean().
starts_with(String, Prefix) when is_binary(String), is_binary(Prefix) ->
    PrefixSize = erlang:byte_size(Prefix),
    case String of
        <<Prefix:PrefixSize/binary, _/binary>> -> true;
        _ -> false
    end.

-doc """
Check if a string ends with a given suffix.
""".
-spec ends_with(binary(), binary()) -> boolean().
ends_with(String, Suffix) when is_binary(String), is_binary(Suffix) ->
    SuffixSize = erlang:byte_size(Suffix),
    StringSize = erlang:byte_size(String),
    case StringSize >= SuffixSize of
        true ->
            Offset = StringSize - SuffixSize,
            case String of
                <<_:Offset/binary, Suffix:SuffixSize/binary>> -> true;
                _ -> false
            end;
        false ->
            false
    end.

-doc """
Check if a string contains a substring.
""".
-spec contains(binary(), binary()) -> boolean().
contains(String, Substring) when is_binary(String), is_binary(Substring) ->
    case binary:match(String, Substring) of
        nomatch -> false;
        _ -> true
    end.

%% ============================================================================
%% Pattern Matching and Replacement
%% ============================================================================

-doc """
Replace the first occurrence of a pattern.
""".
-spec replace(binary(), binary(), binary()) -> binary().
replace(String, Pattern, Replacement) when
    is_binary(String), is_binary(Pattern), is_binary(Replacement)
->
    case binary:split(String, Pattern) of
        % No match
        [String] -> String;
        [Before, After] -> <<Before/binary, Replacement/binary, After/binary>>
    end.

-doc """
Replace all occurrences of a pattern.
""".
-spec replace_all(binary(), binary(), binary()) -> binary().
replace_all(String, Pattern, Replacement) when
    is_binary(String), is_binary(Pattern), is_binary(Replacement)
->
    Parts = binary:split(String, Pattern, [global]),
    iolist_to_binary(lists:join(Replacement, Parts)).

%% ============================================================================
%% Unicode Operations
%% ============================================================================

-doc """
Split a string into a list of grapheme clusters.
""".
-spec graphemes(binary()) -> [binary()].
graphemes(String) when is_binary(String) ->
    collect_graphemes(String, []).

-doc """
Get a list of Unicode codepoints from a string.
""".
-spec codepoints(binary()) -> [integer()].
codepoints(String) when is_binary(String) ->
    unicode:characters_to_list(String).

-doc """
Check if a binary is valid UTF-8.
""".
-spec valid_utf8(binary()) -> boolean().
valid_utf8(Bin) when is_binary(Bin) ->
    case unicode:characters_to_binary(Bin) of
        Bin -> true;
        _ -> false
    end.

%% ============================================================================
%% Utilities
%% ============================================================================

-doc """
Reverse a string (Unicode-aware, reverses graphemes).
""".
-spec reverse(binary()) -> binary().
reverse(String) when is_binary(String) ->
    Graphemes = collect_graphemes(String, []),
    iolist_to_binary(lists:reverse(Graphemes)).

-doc """
Duplicate a string n times.
""".
-spec duplicate(binary(), non_neg_integer()) -> binary().
duplicate(String, N) when is_binary(String), is_integer(N), N >= 0 ->
    iolist_to_binary(lists:duplicate(N, String)).

-doc """
Pad a string on the left to a given width.
""".
-spec pad_left(binary(), non_neg_integer(), binary()) -> binary().
pad_left(String, Width, Padding) when
    is_binary(String), is_integer(Width), is_binary(Padding)
->
    Len = string:length(String),
    case Width > Len of
        true ->
            PadCount = Width - Len,
            PadString = duplicate(Padding, PadCount),
            <<PadString/binary, String/binary>>;
        false ->
            String
    end.

-doc """
Pad a string on the right to a given width.
""".
-spec pad_right(binary(), non_neg_integer(), binary()) -> binary().
pad_right(String, Width, Padding) when
    is_binary(String), is_integer(Width), is_binary(Padding)
->
    Len = string:length(String),
    case Width > Len of
        true ->
            PadCount = Width - Len,
            PadString = duplicate(Padding, PadCount),
            <<String/binary, PadString/binary>>;
        false ->
            String
    end.
