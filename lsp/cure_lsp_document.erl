-module(cure_lsp_document).
-export([new/3, apply_change/2, get_text/1, get_line/2, get_position_offset/3]).
-export([get_word_at_position/3]).

-record(document, {
    uri :: binary(),
    text :: binary(),
    version :: integer(),
    lines :: [binary()]
}).

%% Create new document
new(Uri, Text, Version) ->
    Lines = binary:split(Text, <<"\n">>, [global]),
    #document{
        uri = Uri,
        text = Text,
        version = Version,
        lines = Lines
    }.

%% Apply incremental change to document
apply_change(Doc, Change) ->
    case maps:get(range, Change, undefined) of
        undefined ->
            % Full document sync
            NewText = maps:get(text, Change),
            new(Doc#document.uri, NewText, Doc#document.version + 1);
        Range ->
            % Incremental change
            apply_range_change(Doc, Range, maps:get(text, Change))
    end.

apply_range_change(Doc, Range, NewText) ->
    Start = maps:get(start, Range),
    End = maps:get('end', Range),

    StartLine = maps:get(line, Start),
    StartChar = maps:get(character, Start),
    EndLine = maps:get(line, End),
    EndChar = maps:get(character, End),

    Lines = Doc#document.lines,

    % Get text before change
    BeforeLines = lists:sublist(Lines, StartLine),
    BeforeLine = lists:nth(StartLine + 1, Lines),
    BeforeText = binary:part(BeforeLine, 0, StartChar),

    % Get text after change
    AfterLines = lists:nthtail(EndLine + 1, Lines),
    AfterLine = lists:nth(EndLine + 1, Lines),
    AfterText = binary:part(AfterLine, EndChar, byte_size(AfterLine) - EndChar),

    % Combine
    NewLines = binary:split(list_to_binary(NewText), <<"\n">>, [global]),
    FirstNewLine = <<BeforeText/binary, (hd(NewLines))/binary>>,
    LastNewLine = <<(lists:last(NewLines))/binary, AfterText/binary>>,

    MiddleNewLines =
        case length(NewLines) of
            1 -> [];
            _ -> lists:sublist(NewLines, 2, length(NewLines) - 2)
        end,

    UpdatedLines = BeforeLines ++ [FirstNewLine] ++ MiddleNewLines ++ [LastNewLine] ++ AfterLines,
    UpdatedText = iolist_to_binary(lists:join(<<"\n">>, UpdatedLines)),

    #document{
        uri = Doc#document.uri,
        text = UpdatedText,
        version = Doc#document.version + 1,
        lines = UpdatedLines
    }.

%% Get full text
get_text(#document{text = Text}) ->
    Text.

%% Get specific line (0-indexed)
get_line(#document{lines = Lines}, LineNum) when LineNum >= 0, LineNum < length(Lines) ->
    lists:nth(LineNum + 1, Lines);
get_line(_, _) ->
    <<>>.

%% Get byte offset for line/character position
get_position_offset(#document{lines = Lines}, Line, Character) ->
    if
        Line >= length(Lines) ->
            {error, line_out_of_bounds};
        true ->
            PreviousLines = lists:sublist(Lines, Line),
            % +1 for newline
            PreviousBytes = lists:sum([byte_size(L) + 1 || L <- PreviousLines]),
            CurrentLine = lists:nth(Line + 1, Lines),
            if
                Character > byte_size(CurrentLine) ->
                    {error, character_out_of_bounds};
                true ->
                    {ok, PreviousBytes + Character}
            end
    end.

%% Get word at position (for hover/completion)
get_word_at_position(Text, Line, Character) when is_binary(Text) ->
    Lines = binary:split(Text, <<"\n">>, [global]),
    case Line >= 0 andalso Line < length(Lines) of
        true ->
            LineText = lists:nth(Line + 1, Lines),
            extract_word_at_position(LineText, Character);
        false ->
            {error, invalid_position}
    end;
get_word_at_position(#document{lines = Lines}, Line, Character) ->
    case get_line(#document{lines = Lines}, Line) of
        <<>> ->
            {error, invalid_position};
        LineText ->
            extract_word_at_position(LineText, Character)
    end.

extract_word_at_position(LineText, Character) ->
    % Find word boundaries around character position
    Before = binary:part(LineText, 0, min(Character, byte_size(LineText))),
    After = binary:part(
        LineText,
        min(Character, byte_size(LineText)),
        byte_size(LineText) - min(Character, byte_size(LineText))
    ),

    % Extract word before cursor
    BeforeWord = extract_word_backward(Before),
    % Extract word after cursor
    AfterWord = extract_word_forward(After),

    Word = <<BeforeWord/binary, AfterWord/binary>>,
    case byte_size(Word) of
        0 -> {error, no_word};
        _ -> {ok, Word}
    end.

extract_word_backward(Binary) ->
    extract_word_backward(Binary, <<>>).

extract_word_backward(<<>>, Acc) ->
    Acc;
extract_word_backward(Binary, Acc) ->
    Size = byte_size(Binary),
    <<Before:Size/binary>> = Binary,
    case binary:last(Before) of
        C when
            (C >= $a andalso C =< $z) orelse
                (C >= $A andalso C =< $Z) orelse
                (C >= $0 andalso C =< $9) orelse
                C =:= $_
        ->
            NewSize = Size - 1,
            <<NewBefore:NewSize/binary, Char>> = Before,
            extract_word_backward(NewBefore, <<Char, Acc/binary>>);
        _ ->
            Acc
    end.

extract_word_forward(<<>>) ->
    <<>>;
extract_word_forward(Binary) ->
    extract_word_forward(Binary, <<>>).

extract_word_forward(<<>>, Acc) ->
    Acc;
extract_word_forward(<<C, Rest/binary>>, Acc) when
    (C >= $a andalso C =< $z) orelse
        (C >= $A andalso C =< $Z) orelse
        (C >= $0 andalso C =< $9) orelse
        C =:= $_
->
    extract_word_forward(Rest, <<Acc/binary, C>>);
extract_word_forward(_, Acc) ->
    Acc.
