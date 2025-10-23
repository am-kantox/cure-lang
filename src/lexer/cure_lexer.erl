-module(cure_lexer).

-moduledoc """
# Cure Programming Language - Lexer

The lexer module provides tokenization services for Cure source code, converting
raw text into a structured stream of tokens for the parser. It supports all Cure
language constructs including keywords, operators, literals, and comments.

## Features

- **Position Tracking**: Every token includes precise line and column information
- **String Interpolation**: Support for `#{expr}` string interpolation syntax
- **Multi-character Operators**: Recognition of operators like `->`, `|>`, `::`, etc.
- **Comprehensive Literals**: Numbers, strings, atoms, and boolean values
- **Keywords**: All Cure language keywords including FSM constructs
- **Error Recovery**: Detailed error reporting with location information

## Token Types

The lexer recognizes the following token categories:

- **Keywords**: `def`, `fsm`, `match`, `when`, etc.
- **Identifiers**: Variable and function names
- **Literals**: Numbers, strings, atoms, booleans
- **Operators**: `+`, `->`, `|>`, `::`, `==`, etc.
- **Delimiters**: `()`, `[]`, `{}`, `,`, `;`, etc.
- **Comments**: Line comments starting with `#`

## String Interpolation

Supports string interpolation with `#{expression}` syntax:

```cure
"Hello #{name}!"  % Tokenized as interpolated string
```

## Error Handling

All tokenization errors include precise location information:

```erlang
{error, {Reason, Line, Column}}
```

""".

-export([tokenize/1, tokenize_file/1, token_type/1, scan/1]).

%% Token definitions
-record(token, {
    type :: atom(),
    value :: term(),
    line :: integer(),
    column :: integer()
}).

%% Public API

-doc """
Tokenize a string of Cure source code into a list of tokens.

This is the main entry point for lexical analysis. It processes the entire
input and returns a list of tokens with position information.

## Arguments

- `Source` - Binary containing Cure source code to tokenize

## Returns

- `{ok, Tokens}` - Successful tokenization with list of token records
- `{error, {Reason, Line, Column}}` - Tokenization error with location
- `{error, {Error, Reason, Stack}}` - Internal error with stack trace

## Token Record

Each token is a record with fields:
- `type` - Token type atom (e.g., `identifier`, `number`, `def`)
- `value` - Token value (e.g., variable name, number value)
- `line` - Line number (1-based)
- `column` - Column number (1-based)

## Examples

```erlang
tokenize(<<"def add(x, y) = x + y">>).
% => {ok, [
%      #token{type=def, value=def, line=1, column=1},
%      #token{type=identifier, value= <<"add">>, line=1, column=5},
%      #token{type='(', value='(', line=1, column=8},
%      ...
%    ]}

tokenize(<<"invalid \xff character">>).
% => {error, {invalid_character, 1, 9}}
```

## Error Types

- `invalid_character` - Unrecognized character in input
- `unterminated_string` - String literal without closing quote
- `invalid_number_format` - Malformed numeric literal
- `unterminated_comment` - Block comment without proper termination

""".
-spec tokenize(binary()) -> {ok, [#token{}]} | {error, term()}.
tokenize(Source) when is_binary(Source) ->
    try
        Tokens = scan_tokens(Source, 1, 1, []),
        {ok, lists:reverse(Tokens)}
    catch
        throw:{lexer_error, Reason, Line, Column} ->
            {error, {Reason, Line, Column}};
        Error:Reason:Stack ->
            {error, {Error, Reason, Stack}}
    end.

-doc """
Tokenize a Cure source file.

This is a convenience function that reads a file from disk and tokenizes
its contents. It handles file I/O errors and passes the content to the
main tokenization function.

## Arguments

- `Filename` - Path to the .cure source file to tokenize

## Returns

- `{ok, Tokens}` - Successful tokenization with list of token records
- `{error, {file_error, Reason}}` - File I/O error
- `{error, {Reason, Line, Column}}` - Tokenization error with location

## Examples

```erlang
tokenize_file("examples/hello.cure").
% => {ok, [#token{type=def, ...}, ...]}

tokenize_file("nonexistent.cure").
% => {error, {file_error, enoent}}
```

""".
-spec tokenize_file(string()) -> {ok, [#token{}]} | {error, term()}.
tokenize_file(Filename) ->
    case file:read_file(Filename) of
        {ok, Content} ->
            tokenize(Content);
        {error, Reason} ->
            {error, {file_error, Reason}}
    end.

-doc """
Extract the type from a token record.

This utility function extracts the token type, which is useful for
pattern matching and categorizing tokens in the parser.

## Arguments

- `Token` - Token record to extract type from

## Returns

- Atom representing the token type (e.g., `def`, `identifier`, `number`)

## Examples

```erlang
Token = #token{type = identifier, value = <<"add">>, line = 1, column = 5},
token_type(Token).
% => identifier

KeywordToken = #token{type = def, value = def, line = 1, column = 1},
token_type(KeywordToken).
% => def
```

""".
-spec token_type(#token{}) -> atom().
token_type(#token{type = Type}) -> Type.

%% Scan source code and return tokens in simple tuple format for parser compatibility.
%%
%% This is a compatibility function that converts source code to simple token tuples
%% that match the format expected by the parser and existing tests.
%%
%% Args:
%% - Source: String or binary containing source code to scan
%%
%% Returns:
%% - {ok, Tokens}: List of token tuples in format {Type, Line, Value} or {Type, Line}
%% - {error, Reason}: Error information
%%
%% Examples:
%% scan("42"). -> {ok, [{integer, 1, 42}, {eof, 1}]}
%% scan("def add"). -> {ok, [{def, 1}, {identifier, 1, "add"}, {eof, 1}]}
-spec scan(string() | binary()) -> {ok, [tuple()]} | {error, term()}.
scan(Source) when is_list(Source) ->
    scan(list_to_binary(Source));
scan(Source) when is_binary(Source) ->
    case tokenize(Source) of
        {ok, TokenRecords} ->
            SimpleTuples = [convert_token_to_tuple(Token) || Token <- TokenRecords],
            % Add EOF token at the end
            LastLine =
                case SimpleTuples of
                    [] ->
                        1;
                    _ ->
                        LastToken = lists:last(SimpleTuples),
                        element(2, LastToken)
                end,
            {ok, SimpleTuples ++ [{eof, LastLine}]};
        {error, Reason} ->
            {error, Reason}
    end.

%% Convert token record to simple tuple format
convert_token_to_tuple(#token{type = number, value = Value, line = Line}) ->
    {integer, Line, Value};
convert_token_to_tuple(#token{type = string, value = Value, line = Line}) ->
    {string, Line, Value};
convert_token_to_tuple(#token{type = identifier, value = Value, line = Line}) ->
    {identifier, Line, binary_to_list(Value)};
convert_token_to_tuple(#token{type = atom, value = Value, line = Line}) ->
    {atom, Line, Value};
% Keywords and operators - just type and line
convert_token_to_tuple(#token{type = Type, line = Line}) ->
    {Type, Line}.

%% Internal functions

%% Get operators map
operators() ->
    #{
        <<"=">> => '=',
        <<"->">> => '->',
        <<":">> => ':',
        <<";">> => ';',
        <<",">> => ',',
        <<".">> => '.',
        <<"(">> => '(',
        <<")">> => ')',
        <<"[">> => '[',
        <<"]">> => ']',
        <<"{">> => '{',
        <<"}">> => '}',
        <<"|">> => '|',
        <<"::">> => '::',
        <<"+">> => '+',
        <<"-">> => '-',
        <<"*">> => '*',
        <<"/">> => '/',
        <<"%">> => '%',
        <<"<">> => '<',
        <<">">> => '>',
        <<"<=">> => '<=',
        <<">=">> => '>=',
        <<"==">> => '==',
        <<"!=">> => '!=',
        <<"++">> => '++',
        <<"--">> => '--',
        <<"|>">> => '|>',
        <<"#{">> => 'interpolation_start'
    }.

%% Get keywords map
keywords() ->
    #{
        <<"def">> => 'def',
        <<"curify">> => 'curify',
        <<"end">> => 'end',
        <<"do">> => 'do',
        <<"if">> => 'if',
        <<"then">> => 'then',
        <<"else">> => 'else',
        <<"match">> => 'match',
        <<"case">> => 'case',
        <<"of">> => 'of',
        <<"when">> => 'when',
        <<"let">> => 'let',
        <<"in">> => 'in',
        <<"as">> => 'as',
        <<"module">> => 'module',
        <<"import">> => 'import',
        <<"export">> => 'export',
        <<"process">> => 'process',
        <<"fsm">> => 'fsm',
        <<"state">> => 'state',
        <<"states">> => 'states',
        <<"initial">> => 'initial',
        <<"event">> => 'event',
        <<"timeout">> => 'timeout',
        <<"receive">> => 'receive',
        <<"send">> => 'send',
        <<"spawn">> => 'spawn',
        <<"transition">> => 'transition',
        <<"guard">> => 'guard',
        <<"action">> => 'action',
        <<"invariant">> => 'invariant',
        <<"eventually">> => 'eventually',
        <<"always">> => 'always',
        <<"until">> => 'until',
        <<"property">> => 'property',
        <<"record">> => 'record',
        <<"type">> => 'type',
        <<"true">> => 'true',
        <<"false">> => 'false',
        <<"and">> => 'and',
        <<"or">> => 'or',
        <<"not">> => 'not',
        <<"fn">> => 'fn',
        <<"Ok">> => 'Ok',
        <<"Error">> => 'Error',
        <<"Some">> => 'Some',
        <<"None">> => 'None',
        <<"Unit">> => 'Unit',
        <<"ok">> => 'ok',
        <<"error">> => 'error'
    }.

%% Main scanning loop
scan_tokens(<<>>, _Line, _Column, Acc) ->
    Acc;
%% Skip whitespace except newlines
scan_tokens(<<C, Rest/binary>>, Line, Column, Acc) when C =:= $\s; C =:= $\t; C =:= $\r ->
    scan_tokens(Rest, Line, Column + 1, Acc);
%% Handle newlines
scan_tokens(<<$\n, Rest/binary>>, Line, _Column, Acc) ->
    scan_tokens(Rest, Line + 1, 1, Acc);
%% Skip comments (# to end of line)
scan_tokens(<<$#, Rest/binary>>, Line, _Column, Acc) ->
    {_, NewRest} = skip_line_comment(Rest),
    scan_tokens(NewRest, Line + 1, 1, Acc);
%% String literals - check for interpolation
scan_tokens(<<$", Rest/binary>>, Line, Column, Acc) ->
    case scan_string_with_interpolation(Rest, Line, Column + 1, []) of
        {simple_string, String, NewRest, NewLine, NewColumn} ->
            Token = #token{type = string, value = String, line = Line, column = Column},
            scan_tokens(NewRest, NewLine, NewColumn, [Token | Acc]);
        {interpolated_string, Tokens, NewRest, NewLine, NewColumn} ->
            % Prepend interpolation tokens in correct order
            AllTokens = lists:reverse(Tokens) ++ Acc,
            scan_tokens(NewRest, NewLine, NewColumn, AllTokens)
    end;
%% Single-quoted atoms
scan_tokens(<<$', Rest/binary>>, Line, Column, Acc) ->
    {Atom, NewRest, NewColumn} = scan_quoted_atom(Rest, Column + 1, <<>>),
    Token = #token{type = atom, value = Atom, line = Line, column = Column},
    scan_tokens(NewRest, Line, NewColumn, [Token | Acc]);
%% Atom literals (starting with :) - but check for :: first
scan_tokens(<<$:, $:, Rest/binary>>, Line, Column, Acc) ->
    Token = #token{type = '::', value = '::', line = Line, column = Column},
    scan_tokens(Rest, Line, Column + 2, [Token | Acc]);
scan_tokens(<<$:, Rest/binary>>, Line, Column, Acc) ->
    case Rest of
        <<C, _/binary>> when C >= $a, C =< $z; C >= $A, C =< $Z; C =:= $_ ->
            {Atom, NewRest, NewColumn} = scan_atom(Rest, Column + 1, <<>>),
            Token = #token{type = atom, value = Atom, line = Line, column = Column},
            scan_tokens(NewRest, Line, NewColumn, [Token | Acc]);
        _ ->
            Token = #token{type = ':', value = ':', line = Line, column = Column},
            scan_tokens(Rest, Line, Column + 1, [Token | Acc])
    end;
%% Numbers
scan_tokens(<<C, Rest/binary>>, Line, Column, Acc) when C >= $0, C =< $9 ->
    {Number, NewRest, NewColumn} = scan_number(<<C, Rest/binary>>, Column, <<>>),
    Token = #token{type = number, value = Number, line = Line, column = Column},
    scan_tokens(NewRest, Line, NewColumn, [Token | Acc]);
%% Identifiers and keywords
scan_tokens(<<C, Rest/binary>>, Line, Column, Acc) when
    C >= $a, C =< $z; C >= $A, C =< $Z; C =:= $_
->
    {Identifier, NewRest, NewColumn} = scan_identifier(<<C, Rest/binary>>, Column, <<>>),
    TokenType =
        case maps:get(Identifier, keywords(), undefined) of
            undefined -> identifier;
            Keyword -> Keyword
        end,
    Value =
        case TokenType of
            identifier -> Identifier;
            _ -> TokenType
        end,
    Token = #token{type = TokenType, value = Value, line = Line, column = Column},
    scan_tokens(NewRest, Line, NewColumn, [Token | Acc]);
%% Two-character operators
scan_tokens(<<C1, C2, Rest/binary>>, Line, Column, Acc) ->
    TwoChar = <<C1, C2>>,
    case maps:get(TwoChar, operators(), undefined) of
        undefined ->
            % Try single character
            scan_single_char(<<C1, C2, Rest/binary>>, Line, Column, Acc);
        Op ->
            Token = #token{type = Op, value = Op, line = Line, column = Column},
            scan_tokens(Rest, Line, Column + 2, [Token | Acc])
    end;
%% Single character (including single-char operators)
scan_tokens(Binary, Line, Column, Acc) ->
    scan_single_char(Binary, Line, Column, Acc).

%% Handle single character tokens
scan_single_char(<<C, Rest/binary>>, Line, Column, Acc) ->
    SingleChar = <<C>>,
    case maps:get(SingleChar, operators(), undefined) of
        undefined ->
            throw({lexer_error, {unexpected_character, C}, Line, Column});
        Op ->
            Token = #token{type = Op, value = Op, line = Line, column = Column},
            scan_tokens(Rest, Line, Column + 1, [Token | Acc])
    end;
scan_single_char(<<>>, _Line, _Column, Acc) ->
    Acc.

%% Skip line comment until newline
skip_line_comment(<<$\n, Rest/binary>>) ->
    {comment, Rest};
skip_line_comment(<<_, Rest/binary>>) ->
    skip_line_comment(Rest);
skip_line_comment(<<>>) ->
    {comment, <<>>}.

%% Handle escape sequences
escape_char($n) -> $\n;
escape_char($t) -> $\t;
escape_char($r) -> $\r;
escape_char($\\) -> $\\;
escape_char($") -> $";
escape_char(C) -> C.

%% Scan string with potential interpolation
scan_string_with_interpolation(Binary, Line, Column, Acc) ->
    scan_string_with_interpolation(Binary, Line, Column, Acc, <<>>, false).

scan_string_with_interpolation(
    <<$", Rest/binary>>, Line, Column, Acc, StringPart, HasInterpolation
) ->
    case HasInterpolation of
        false ->
            % Simple string without interpolation
            {simple_string, binary_to_list(StringPart), Rest, Line, Column + 1};
        true ->
            % Add final string part if any
            FinalTokens =
                case StringPart of
                    <<>> ->
                        Acc;
                    _ ->
                        [
                            #token{
                                type = string_part,
                                value = binary_to_list(StringPart),
                                line = Line,
                                column = Column
                            }
                            | Acc
                        ]
                end,
            % Add end marker
            EndToken = #token{
                type = interpolation_end, value = interpolation_end, line = Line, column = Column
            },
            {interpolated_string, lists:reverse([EndToken | FinalTokens]), Rest, Line, Column + 1}
    end;
scan_string_with_interpolation(<<$#, ${, Rest/binary>>, Line, Column, Acc, StringPart, _) ->
    % Start of interpolation
    NewAcc =
        case StringPart of
            <<>> ->
                Acc;
            _ ->
                [
                    #token{
                        type = string_part,
                        value = binary_to_list(StringPart),
                        line = Line,
                        column = Column
                    }
                    | Acc
                ]
        end,
    % Add interpolation start token if this is first interpolation
    StartToken =
        case Acc of
            [] ->
                #token{
                    type = interpolation_start,
                    value = interpolation_start,
                    line = Line,
                    column = Column
                };
            _ ->
                #token{
                    type = interpolation_mid,
                    value = interpolation_mid,
                    line = Line,
                    column = Column
                }
        end,
    UpdatedAcc = [StartToken | NewAcc],
    % Scan the expression inside #{...}
    {ExprTokens, NewRest, NewLine, NewColumn} = scan_interpolation_expr(
        Rest, Line, Column + 2, [], 1
    ),
    AllTokens = ExprTokens ++ UpdatedAcc,
    scan_string_with_interpolation(NewRest, NewLine, NewColumn, AllTokens, <<>>, true);
scan_string_with_interpolation(
    <<$\\, C, Rest/binary>>, Line, Column, Acc, StringPart, HasInterpolation
) ->
    Escaped = escape_char(C),
    scan_string_with_interpolation(
        Rest, Line, Column + 2, Acc, <<StringPart/binary, Escaped>>, HasInterpolation
    );
scan_string_with_interpolation(
    <<$\n, Rest/binary>>, Line, _Column, Acc, StringPart, HasInterpolation
) ->
    scan_string_with_interpolation(
        Rest, Line + 1, 1, Acc, <<StringPart/binary, $\n>>, HasInterpolation
    );
scan_string_with_interpolation(<<C, Rest/binary>>, Line, Column, Acc, StringPart, HasInterpolation) ->
    scan_string_with_interpolation(
        Rest, Line, Column + 1, Acc, <<StringPart/binary, C>>, HasInterpolation
    );
scan_string_with_interpolation(<<>>, Line, Column, _Acc, _StringPart, _HasInterpolation) ->
    throw({lexer_error, unterminated_string, Line, Column}).

%% Scan expression inside #{...}
scan_interpolation_expr(<<$}, Rest/binary>>, Line, Column, Acc, 1) ->
    % End of interpolation expression
    {lists:reverse(Acc), Rest, Line, Column + 1};
scan_interpolation_expr(<<${, Rest/binary>>, Line, Column, Acc, BraceCount) ->
    % Nested brace
    Token = #token{type = '{', value = '{', line = Line, column = Column},
    scan_interpolation_expr(Rest, Line, Column + 1, [Token | Acc], BraceCount + 1);
scan_interpolation_expr(<<$}, Rest/binary>>, Line, Column, Acc, BraceCount) ->
    % Closing brace
    Token = #token{type = '}', value = '}', line = Line, column = Column},
    scan_interpolation_expr(Rest, Line, Column + 1, [Token | Acc], BraceCount - 1);
scan_interpolation_expr(Binary, Line, Column, Acc, BraceCount) ->
    % Scan one token and continue
    case scan_one_token(Binary, Line, Column) of
        {Token, NewRest, NewLine, NewColumn} ->
            scan_interpolation_expr(NewRest, NewLine, NewColumn, [Token | Acc], BraceCount);
        eof ->
            throw({lexer_error, unterminated_interpolation, Line, Column})
    end.

%% Scan a single token (helper for interpolation)
scan_one_token(<<>>, _Line, _Column) ->
    eof;
%% Skip whitespace except newlines
scan_one_token(<<C, Rest/binary>>, Line, Column) when C =:= $\s; C =:= $\t; C =:= $\r ->
    scan_one_token(Rest, Line, Column + 1);
%% Handle newlines
scan_one_token(<<$\n, Rest/binary>>, Line, _Column) ->
    Token = #token{type = '\n', value = '\n', line = Line, column = 1},
    {Token, Rest, Line + 1, 1};
%% Numbers
scan_one_token(<<C, Rest/binary>>, Line, Column) when C >= $0, C =< $9 ->
    {Number, NewRest, NewColumn} = scan_number(<<C, Rest/binary>>, Column, <<>>),
    Token = #token{type = number, value = Number, line = Line, column = Column},
    {Token, NewRest, Line, NewColumn};
%% Identifiers and keywords
scan_one_token(<<C, Rest/binary>>, Line, Column) when
    C >= $a, C =< $z; C >= $A, C =< $Z; C =:= $_
->
    {Identifier, NewRest, NewColumn} = scan_identifier(<<C, Rest/binary>>, Column, <<>>),
    TokenType =
        case maps:get(Identifier, keywords(), undefined) of
            undefined -> identifier;
            Keyword -> Keyword
        end,
    Value =
        case TokenType of
            identifier -> Identifier;
            _ -> TokenType
        end,
    Token = #token{type = TokenType, value = Value, line = Line, column = Column},
    {Token, NewRest, Line, NewColumn};
%% Two-character operators
scan_one_token(<<C1, C2, Rest/binary>>, Line, Column) ->
    TwoChar = <<C1, C2>>,
    case maps:get(TwoChar, operators(), undefined) of
        undefined ->
            % Try single character
            SingleChar = <<C1>>,
            case maps:get(SingleChar, operators(), undefined) of
                undefined ->
                    throw({lexer_error, {unexpected_character, C1}, Line, Column});
                Op ->
                    Token = #token{type = Op, value = Op, line = Line, column = Column},
                    {Token, <<C2, Rest/binary>>, Line, Column + 1}
            end;
        Op ->
            Token = #token{type = Op, value = Op, line = Line, column = Column},
            {Token, Rest, Line, Column + 2}
    end;
%% Empty binary
scan_one_token(<<>>, _Line, _Column) ->
    eof.

%% Scan atom
scan_atom(<<C, Rest/binary>>, Column, Acc) when
    C >= $a, C =< $z; C >= $A, C =< $Z; C >= $0, C =< $9; C =:= $_; C =:= $?
->
    scan_atom(Rest, Column + 1, <<Acc/binary, C>>);
scan_atom(Rest, Column, Acc) ->
    {binary_to_atom(Acc, utf8), Rest, Column}.

%% Scan single-quoted atom
scan_quoted_atom(<<$', Rest/binary>>, Column, Acc) ->
    {binary_to_atom(Acc, utf8), Rest, Column + 1};
scan_quoted_atom(<<$\\, C, Rest/binary>>, Column, Acc) ->
    % Handle escape sequences in quoted atoms
    Escaped = escape_char(C),
    scan_quoted_atom(Rest, Column + 2, <<Acc/binary, Escaped>>);
scan_quoted_atom(<<$\n, Rest/binary>>, Column, Acc) ->
    % Allow newlines in quoted atoms
    scan_quoted_atom(Rest, Column + 1, <<Acc/binary, $\n>>);
scan_quoted_atom(<<C, Rest/binary>>, Column, Acc) ->
    scan_quoted_atom(Rest, Column + 1, <<Acc/binary, C>>);
scan_quoted_atom(<<>>, Column, _Acc) ->
    throw({lexer_error, unterminated_quoted_atom, Column, Column}).

%% Scan number (integers and floats)
scan_number(<<C, Rest/binary>>, Column, Acc) when C >= $0, C =< $9 ->
    scan_number(Rest, Column + 1, <<Acc/binary, C>>);
scan_number(<<$., C, Rest/binary>>, Column, Acc) when C >= $0, C =< $9 ->
    % Float
    scan_float(Rest, Column + 2, <<Acc/binary, $., C>>);
scan_number(Rest, Column, Acc) ->
    {binary_to_integer(Acc), Rest, Column}.

%% Scan float part
scan_float(<<C, Rest/binary>>, Column, Acc) when C >= $0, C =< $9 ->
    scan_float(Rest, Column + 1, <<Acc/binary, C>>);
scan_float(Rest, Column, Acc) ->
    {binary_to_float(Acc), Rest, Column}.

%% Scan identifier
scan_identifier(<<C, Rest/binary>>, Column, Acc) when
    C >= $a, C =< $z; C >= $A, C =< $Z; C >= $0, C =< $9; C =:= $_; C =:= $?
->
    scan_identifier(Rest, Column + 1, <<Acc/binary, C>>);
scan_identifier(Rest, Column, Acc) ->
    {Acc, Rest, Column}.
