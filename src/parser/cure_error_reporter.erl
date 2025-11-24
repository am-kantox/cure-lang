-module(cure_error_reporter).

-moduledoc """
# Cure Error Reporter

Enhanced error reporting module with precise location tracking and
user-friendly diagnostic messages. This module provides rich error
formatting for parser, lexer, and semantic analysis errors.

## Features

- **Rich Location Info**: Line, column, and file context
- **Snippet Display**: Show source code around errors
- **Suggestions**: Provide helpful hints for common mistakes
- **Color Formatting**: Terminal color support for better readability
- **Multi-error Support**: Report multiple errors in batch
""".

-export([
    format_error/2,
    format_error/3,
    format_parse_error/4,
    format_type_error/4,
    format_with_snippet/3,
    create_diagnostic/4
]).

-include("cure_ast.hrl").

-record(diagnostic, {
    severity :: error | warning | info,
    location :: #location{},
    message :: binary(),
    snippet :: binary() | undefined,
    suggestions :: [binary()]
}).

%% @doc Format a general error with location
-spec format_error(term(), #location{}) -> binary().
format_error(Error, Location) ->
    format_error(Error, Location, #{}).

%% @doc Format an error with location and options
-spec format_error(term(), #location{}, map()) -> binary().
format_error(Error, #location{line = Line, column = Col, file = File}, Opts) ->
    FileName =
        case File of
            undefined -> <<"<unknown>">>;
            F when is_list(F) -> list_to_binary(F);
            F when is_binary(F) -> F
        end,

    ErrorMsg = format_error_message(Error),

    Formatted =
        case maps:get(color, Opts, false) of
            true ->
                io_lib:format(
                    "\033[1;31merror\033[0m: ~s\n  \033[1;34m-->\033[0m ~s:~p:~p\n",
                    [ErrorMsg, FileName, Line, Col]
                );
            false ->
                io_lib:format(
                    "error: ~s\n  --> ~s:~p:~p\n",
                    [ErrorMsg, FileName, Line, Col]
                )
        end,

    iolist_to_binary(Formatted).

%% @doc Format a parse error with detailed context
-spec format_parse_error(term(), integer(), integer(), string() | undefined) -> binary().
format_parse_error(Reason, Line, Column, File) ->
    Location = #location{line = Line, column = Column, file = File},
    format_error(Reason, Location, #{color => true}).

%% @doc Format a type error with detailed context
-spec format_type_error(term(), #location{}, term(), term()) -> binary().
format_type_error(Reason, Location, Expected, Got) ->
    Error = {type_mismatch, Reason, Expected, Got},
    format_error(Error, Location, #{color => true}).

%% @doc Format error with source code snippet
-spec format_with_snippet(term(), #location{}, binary()) -> binary().
format_with_snippet(
    Error, #location{line = Line, column = Col, file = _File} = Location, SourceCode
) ->
    BaseError = format_error(Error, Location, #{color => true}),

    Snippet = extract_snippet(SourceCode, Line, Col),

    Formatted = [
        BaseError,
        "\n",
        Snippet
    ],

    iolist_to_binary(Formatted).

%% @doc Create a diagnostic record
-spec create_diagnostic(error | warning | info, #location{}, binary(), [binary()]) -> #diagnostic{}.
create_diagnostic(Severity, Location, Message, Suggestions) ->
    #diagnostic{
        severity = Severity,
        location = Location,
        message = Message,
        snippet = undefined,
        suggestions = Suggestions
    }.

%%% Internal Functions %%%

%% Format error message based on error type
format_error_message({expected, TokenType, got, ActualType}) ->
    BaseMsg = io_lib:format("expected ~p, but got ~p", [TokenType, ActualType]),
    case suggest_correction(TokenType, ActualType) of
        {ok, Suggestion} ->
            [BaseMsg, io_lib:format("~n  hint: did you mean '~p'?", [Suggestion])];
        none ->
            BaseMsg
    end;
format_error_message({unexpected_token, TokenType}) ->
    io_lib:format("unexpected token: ~p", [TokenType]);
format_error_message({undefined_variable, VarName}) ->
    io_lib:format("undefined variable: ~p", [VarName]);
format_error_message({type_mismatch, Reason, Expected, Got}) ->
    io_lib:format("type mismatch (~p): expected ~p, got ~p", [Reason, Expected, Got]);
format_error_message({duplicate_definition, Name}) ->
    io_lib:format("duplicate definition of '~p'", [Name]);
format_error_message({missing_return_type_for_curify}) ->
    <<"curify functions require explicit return type annotation">>;
format_error_message({arity_mismatch, Expected, Got}) ->
    io_lib:format("arity mismatch: expected ~p arguments, got ~p", [Expected, Got]);
format_error_message({invalid_pattern, Reason}) ->
    io_lib:format("invalid pattern: ~p", [Reason]);
format_error_message({fsm_error, Reason}) ->
    io_lib:format("FSM error: ~p", [Reason]);
format_error_message({guard_error, Reason}) ->
    io_lib:format("guard error: ~p", [Reason]);
format_error_message(Error) when is_atom(Error) ->
    atom_to_binary(Error, utf8);
format_error_message(Error) when is_binary(Error) ->
    Error;
format_error_message(Error) ->
    io_lib:format("~p", [Error]).

%% Extract source code snippet around error location
extract_snippet(SourceCode, Line, Column) ->
    Lines = binary:split(SourceCode, <<"\n">>, [global]),

    case Line =< length(Lines) andalso Line > 0 of
        true ->
            % Get lines around the error (context: 2 lines before and after)
            StartLine = max(1, Line - 2),
            EndLine = min(length(Lines), Line + 2),

            ContextLines = lists:sublist(Lines, StartLine, EndLine - StartLine + 1),

            % Format the snippet with line numbers
            Formatted = lists:map(
                fun({Idx, LineContent}) ->
                    LineNum = StartLine + Idx - 1,
                    Prefix =
                        case LineNum of
                            Line -> io_lib:format("~4w | ", [LineNum]);
                            _ -> io_lib:format("~4w | ", [LineNum])
                        end,

                    LineStr = [Prefix, LineContent, "\n"],

                    % Add error indicator for the error line
                    case LineNum of
                        Line ->
                            Spaces = lists:duplicate(Column + 6, $\s),
                            ErrorPointer = Spaces ++ "^\n",
                            [LineStr, ErrorPointer];
                        _ ->
                            LineStr
                    end
                end,
                lists:zip(lists:seq(1, length(ContextLines)), ContextLines)
            ),

            iolist_to_binary(["\n", Formatted]);
        false ->
            <<"">>
    end.

%%% Typo Suggestion System %%%

%% @doc Suggest correction for common typos using Levenshtein distance
-spec suggest_correction(atom(), atom()) -> {ok, atom()} | none.
suggest_correction(Expected, Got) when is_atom(Expected), is_atom(Got) ->
    % Convert atoms to strings
    ExpectedStr = atom_to_list(Expected),
    GotStr = atom_to_list(Got),

    % Calculate Levenshtein distance
    Distance = levenshtein_distance(ExpectedStr, GotStr),

    % Suggest if distance is small (1-2 characters difference)
    case Distance of
        % Single character typo
        1 ->
            {ok, Expected};
        % Two character typo
        2 ->
            {ok, Expected};
        _ ->
            % Also check against common keyword typos
            case suggest_common_keyword_typo(GotStr) of
                {ok, _} = Result -> Result;
                none -> none
            end
    end;
suggest_correction(_, _) ->
    none.

%% @doc Suggest corrections for common keyword typos
-spec suggest_common_keyword_typo(string()) -> {ok, atom()} | none.
suggest_common_keyword_typo(Typo) ->
    % Common typos mapped to correct keywords
    Corrections = #{
        "dn" => 'end',
        "ned" => 'end',
        "ened" => 'end',
        "endd" => 'end',
        "dne" => 'end',
        "deff" => def,
        "dfe" => def,
        "deef" => def,
        "modul" => module,
        "moduel" => module,
        "mdoule" => module,
        "modeul" => module,
        "macth" => 'match',
        "mtach" => 'match',
        "mathc" => 'match',
        "matc" => 'match',
        "od" => do,
        "doo" => do,
        "dont" => do,
        "lte" => 'let',
        "elt" => 'let',
        "lett" => 'let',
        "fi" => 'if',
        "iff" => 'if',
        "esle" => 'else',
        "els" => 'else',
        "eles" => 'else',
        "elsee" => 'else',
        "whne" => 'when',
        "wehn" => 'when',
        "whe" => 'when',
        "whenn" => 'when',
        "recrod" => record,
        "reocrd" => record,
        "rcord" => record,
        "recordd" => record,
        "tpye" => type,
        "tyep" => type,
        "typ" => type,
        "typee" => type,
        "fsms" => fsm,
        "fms" => fsm,
        "fssm" => fsm,
        "exoprt" => export,
        "exprot" => export,
        "expor" => export,
        "exort" => export,
        "imoprt" => 'import',
        "improt" => 'import',
        "impor" => 'import',
        "imort" => 'import'
    },

    case maps:get(Typo, Corrections, undefined) of
        undefined -> none;
        Correction -> {ok, Correction}
    end.

%% @doc Calculate Levenshtein distance between two strings
-spec levenshtein_distance(string(), string()) -> non_neg_integer().
levenshtein_distance(S1, S2) ->
    levenshtein_distance(S1, S2, #{}).

levenshtein_distance([], S2, _Cache) ->
    length(S2);
levenshtein_distance(S1, [], _Cache) ->
    length(S1);
levenshtein_distance([H | T1] = S1, [H | T2] = S2, Cache) ->
    % Same character, no cost
    Key = {S1, S2},
    case maps:get(Key, Cache, undefined) of
        undefined ->
            Result = levenshtein_distance(T1, T2, Cache),
            Result;
        Cached ->
            Cached
    end;
levenshtein_distance([_ | T1] = S1, [_ | T2] = S2, Cache) ->
    Key = {S1, S2},
    case maps:get(Key, Cache, undefined) of
        undefined ->
            % Different characters - try substitution, insertion, deletion
            Subst = levenshtein_distance(T1, T2, Cache),
            Insert = levenshtein_distance(S1, T2, Cache),
            Delete = levenshtein_distance(T1, S2, Cache),
            Result = 1 + lists:min([Subst, Insert, Delete]),
            Result;
        Cached ->
            Cached
    end.
