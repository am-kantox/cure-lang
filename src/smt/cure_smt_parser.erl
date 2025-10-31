%% Cure Programming Language - SMT Model Parser
%% Parses S-expressions from SMT solver output to extract variable bindings
-module(cure_smt_parser).

-moduledoc """
# Cure SMT Model Parser

Parses S-expression output from SMT solvers (Z3, CVC5) to extract
variable bindings and convert them to Erlang terms.

## Features

- Parse (model ...) sections
- Extract (define-fun ...) statements
- Convert SMT values to Erlang terms
- Handle Int, Bool, Real types
- Error handling for malformed output

## Usage

```erlang
% Parse model from Z3 output
Lines = [
    <<\"(\">>,
    <<\"  (define-fun x () Int 5)\">>,
    <<\"  (define-fun y () Int 3)\">>,
    <<\")\">>
],
{ok, Model} = cure_smt_parser:parse_model(Lines).
% => {ok, #{x => 5, y => 3}}
```
""".

-export([
    parse_model/1,
    extract_bindings/1,
    parse_define_fun/1,
    parse_value/2,
    parse_value/1
]).

%% ============================================================================
%% Public API
%% ============================================================================

-doc """
Parse a model from solver output lines.

Takes a list of binary lines from the solver and extracts variable bindings.

## Arguments
- `Lines` - List of binary lines from solver output

## Returns
- `{ok, Model}` - Map of variable names to values
- `{error, Reason}` - Parse error

## Example
```erlang
Lines = [<<\"(\">>, <<\"  (define-fun x () Int 5)\">>, <<\")\">>],
{ok, #{x => 5}} = parse_model(Lines).
```
""".
-spec parse_model([binary()]) -> {ok, map()} | {error, term()}.
parse_model([]) ->
    {ok, #{}};
parse_model(Lines) ->
    try
        % Join lines into single binary for easier parsing
        ModelText = iolist_to_binary([L || L <- Lines]),

        % Extract bindings
        Bindings = extract_bindings(ModelText),

        {ok, maps:from_list(Bindings)}
    catch
        Class:Reason:Stack ->
            {error, {parse_failed, Class, Reason, Stack}}
    end.

-doc """
Extract variable bindings from model text.

Finds all (define-fun ...) statements and extracts variable bindings.

## Arguments
- `ModelText` - Binary containing model S-expressions

## Returns
- List of {Name, Value} tuples
""".
-spec extract_bindings(binary()) -> [{atom(), term()}].
extract_bindings(ModelText) ->
    % Find all define-fun statements
    DefineRegex = <<"\\(define-fun\\s+(\\w+)\\s+\\(\\)\\s+(\\w+)\\s+([^)]+)\\)">>,

    case re:run(ModelText, DefineRegex, [global, {capture, all_but_first, binary}]) of
        {match, Matches} ->
            lists:map(fun parse_match/1, Matches);
        nomatch ->
            []
    end.

%% Parse a regex match into {Name, Value}
parse_match([NameBin, TypeBin, ValueBin]) ->
    Name = binary_to_atom(NameBin, utf8),
    Type = binary_to_atom(TypeBin, utf8),
    Value = parse_value(Type, ValueBin),
    {Name, Value}.

-doc """
Parse a (define-fun ...) statement.

Extracts variable name, type, and value from a define-fun statement.

## Arguments
- `Line` - Binary line containing define-fun

## Returns
- `{ok, {Name, Value}}` - Parsed binding
- `{error, Reason}` - Parse error
""".
-spec parse_define_fun(binary()) -> {ok, {atom(), term()}} | {error, term()}.
parse_define_fun(Line) ->
    % Remove leading/trailing whitespace
    Trimmed = string:trim(Line),

    % Try to match define-fun pattern
    case
        re:run(
            Trimmed,
            <<"\\(define-fun\\s+(\\w+)\\s+\\(\\)\\s+(\\w+)\\s+(.+)\\)">>,
            [{capture, all_but_first, binary}]
        )
    of
        {match, [NameBin, TypeBin, ValueBin]} ->
            Name = binary_to_atom(NameBin, utf8),
            Type = binary_to_atom(TypeBin, utf8),
            Value = parse_value(Type, ValueBin),
            {ok, {Name, Value}};
        nomatch ->
            {error, {invalid_define_fun, Line}}
    end.

-doc """
Parse a value based on its SMT type.

Converts SMT-LIB value representation to Erlang term.

## Arguments
- `Type` - SMT type atom ('Int', 'Bool', 'Real')
- `ValueBin` - Binary containing the value

## Returns
- Erlang term (integer, boolean, float)
""".
-spec parse_value(atom(), binary()) -> term().
parse_value('Int', ValueBin) ->
    ValueStr = string:trim(ValueBin),
    case string:to_integer(binary_to_list(ValueStr)) of
        % Default on parse error
        {error, _} -> 0;
        % Normal parse
        {Int, ""} -> Int;
        % Ignore trailing content
        {Int, _Rest} -> Int
    end;
parse_value('Bool', ValueBin) ->
    case string:trim(ValueBin) of
        <<"true">> -> true;
        <<"false">> -> false;
        % Default to false on parse error
        _ -> false
    end;
parse_value('Real', ValueBin) ->
    ValueStr = string:trim(ValueBin),
    case string:to_float(binary_to_list(ValueStr)) of
        {error, _} ->
            % Try parsing as integer then convert to float
            case string:to_integer(binary_to_list(ValueStr)) of
                {error, _} -> 0.0;
                {Int, _} -> float(Int)
            end;
        {Float, ""} ->
            Float;
        {Float, _Rest} ->
            Float
    end;
parse_value(_Type, ValueBin) ->
    % Unknown type, try to parse as integer
    ValueStr = string:trim(ValueBin),
    case string:to_integer(binary_to_list(ValueStr)) of
        % Return as-is if can't parse
        {error, _} -> ValueBin;
        {Int, _} -> Int
    end.

-doc """
Parse a value without type information.

Attempts to infer type and parse accordingly.

## Arguments
- `ValueBin` - Binary containing the value

## Returns
- Erlang term (guessed type)
""".
-spec parse_value(binary()) -> term().
parse_value(ValueBin) ->
    Trimmed = string:trim(ValueBin),

    % Try to guess type and parse
    case Trimmed of
        <<"true">> ->
            true;
        <<"false">> ->
            false;
        _ ->
            % Try integer
            case string:to_integer(binary_to_list(Trimmed)) of
                {error, _} ->
                    % Try float
                    case string:to_float(binary_to_list(Trimmed)) of
                        % Return as binary
                        {error, _} -> Trimmed;
                        {Float, _} -> Float
                    end;
                {Int, ""} ->
                    Int;
                {Int, _} ->
                    Int
            end
    end.

%% ============================================================================
%% Helper Functions
%% ============================================================================

%% Format model for display
-doc """
Format a model map as a human-readable string.

## Arguments
- `Model` - Map of variable bindings

## Returns
- Binary string representation
""".
-spec format_model(map()) -> binary().
format_model(Model) ->
    Entries = [
        iolist_to_binary(io_lib:format("~s = ~p", [Name, Value]))
     || {Name, Value} <- maps:to_list(Model)
    ],
    iolist_to_binary(string:join(Entries, ", ")).

%% ============================================================================
%% Unit Tests
%% ============================================================================

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

parse_int_test() ->
    ?assertEqual(5, parse_value('Int', <<"5">>)),
    ?assertEqual(42, parse_value('Int', <<"  42  ">>)),
    ?assertEqual(-10, parse_value('Int', <<"-10">>)).

parse_bool_test() ->
    ?assertEqual(true, parse_value('Bool', <<"true">>)),
    ?assertEqual(false, parse_value('Bool', <<"false">>)),
    ?assertEqual(false, parse_value('Bool', <<"  false  ">>)).

parse_real_test() ->
    ?assertEqual(3.14, parse_value('Real', <<"3.14">>)),
    ?assertEqual(2.0, parse_value('Real', <<"2">>)).

parse_simple_model_test() ->
    Lines = [
        <<"(">>,
        <<"  (define-fun x () Int 5)">>,
        <<"  (define-fun y () Int 3)">>,
        <<")">>
    ],
    {ok, Model} = parse_model(Lines),
    ?assertEqual(#{x => 5, y => 3}, Model).

parse_empty_model_test() ->
    {ok, Model} = parse_model([]),
    ?assertEqual(#{}, Model).

-endif.
