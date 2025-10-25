%% Cure Programming Language - Parser
%% Recursive descent parser that converts tokens to AST
-module(cure_parser).

-moduledoc """
# Cure Programming Language - Parser

The parser module implements a recursive descent parser that converts tokens from
the lexer into an Abstract Syntax Tree (AST). It handles the complete Cure language
grammar including modules, functions, finite state machines, types, records,
and expressions.

## Features

### Language Constructs
- **Modules**: Module definitions with exports and imports
- **Functions**: Function definitions with parameters, return types, and guards
- **FSMs**: Finite state machine definitions with states and transitions
- **Types**: User-defined types, records, and type aliases
- **Expressions**: Complete expression parsing including pattern matching
- **Literals**: Numbers, strings, atoms, lists, tuples, and maps

### Parser Architecture
- **Recursive Descent**: Top-down parsing with predictive lookahead
- **Error Recovery**: Comprehensive error reporting with location information
- **Token Stream**: Sequential token processing with position tracking
- **AST Generation**: Direct AST construction during parsing

### Error Handling
- **Syntax Errors**: Detailed error messages with expected vs. actual tokens
- **Location Tracking**: Line and column information for all parse errors
- **Error Recovery**: Attempts to continue parsing after errors where possible
- **Structured Errors**: Well-formed error tuples for programmatic handling

## Grammar Support

The parser supports the complete Cure language grammar:

### Top-Level Constructs
```cure
module MyModule do
  export [function/2, MyType]
  
  def function(param1: Type1, param2: Type2) -> ReturnType do
    # Function body
  end
  
  fsm StateMachine do
    state idle do
      on start -> running
    end
  end
end
```

### Expression Parsing
- **Arithmetic**: `+`, `-`, `*`, `/`, `div`, `rem`
- **Logical**: `and`, `or`, `not`, `andalso`, `orelse`
- **Comparison**: `==`, `/=`, `<`, `>`, `=<`, `>=`
- **Pattern Matching**: Complete pattern support with guards
- **Function Calls**: Local and remote function calls
- **Data Structures**: Lists, tuples, maps, records

### Type System Integration
- **Type Annotations**: Function parameters and return types
- **Type Definitions**: User-defined types and aliases
- **Generic Types**: Parameterized types with constraints
- **Dependent Types**: Types that depend on values

## API Usage

```erlang
%% Parse tokens directly
{ok, AST} = cure_parser:parse(Tokens).

%% Parse from file
{ok, AST} = cure_parser:parse_file("example.cure").

%% Handle parse errors
case cure_parser:parse_file("example.cure") of
    {ok, AST} -> 
        cure_utils:debug("Parsed successfully~n");
    {error, {parse_error, Reason, Line, Column}} ->
        cure_utils:debug("Parse error at ~p:~p: ~p~n", [Line, Column, Reason])
end.
```

## Parser State

The parser maintains state including:
- **Token Stream**: Current and remaining tokens
- **Position**: Current parsing position for error reporting
- **Filename**: Source file name for error messages
- **Context**: Current parsing context for better error messages

## Error Types

The parser can return these error types:
- `{parse_error, Reason, Line, Column}` - Syntax error with location
- `{expected, TokenType, got, ActualType}` - Expected token mismatch
- `{unexpected_token, TokenType}` - Unexpected token in context
- `{Error, Reason, Stack}` - Internal parser errors

## Performance Characteristics

- **Linear Time**: O(n) parsing time for well-formed input
- **Memory Efficient**: Streaming token processing
- **Early Termination**: Stops on first syntax error
- **Lookahead**: Minimal lookahead for efficient parsing

## Integration

The parser integrates with:
- **Lexer**: Consumes tokens from cure_lexer
- **AST**: Produces AST records defined in cure_ast.hrl
- **Type Checker**: Provides AST input for type checking
- **Compiler**: Part of the complete compilation pipeline
""".

-export([parse/1, parse_file/1]).

-include("cure_ast.hrl").

%% Parser state record
-record(parser_state, {
    tokens :: [term()],
    current :: term() | eof,
    position :: integer(),
    filename :: string() | undefined
}).

%% API Functions

-doc """
Parses a list of tokens into an Abstract Syntax Tree (AST).

This is the main parsing function that takes a list of tokens from the lexer
and produces a complete AST representing the Cure program structure.

## Arguments
- `Tokens` - List of token records from cure_lexer

## Returns
- `{ok, Program}` - Successfully parsed AST program
- `{error, {parse_error, Reason, Line, Column}}` - Syntax error with location
- `{error, {Error, Reason, Stack}}` - Internal parser error

## Example
```erlang
Tokens = cure_lexer:tokenize("def hello() -> :ok end"),
{ok, AST} = cure_parser:parse(Tokens).
```

## Error Handling
The parser provides detailed error information including:
- Specific error reason (expected token, unexpected construct, etc.)
- Line and column numbers for error location
- Full stack trace for internal errors
""".
-spec parse([term()]) -> {ok, cure_ast:program()} | {error, term()}.
parse(Tokens) ->
    try
        State = init_parser(Tokens, undefined),
        {Program, _FinalState} = parse_program(State),
        {ok, Program}
    catch
        throw:{parse_error, Reason, Line, Column} ->
            {error, {parse_error, Reason, Line, Column}};
        Error:Reason:Stack ->
            {error, {Error, Reason, Stack}}
    end.

-doc """
Parses a Cure source file into an Abstract Syntax Tree (AST).

This convenience function reads and tokenizes a file, then parses the tokens
into an AST. It handles both lexical and syntax errors from the complete
lexing and parsing pipeline.

## Arguments
- `Filename` - Path to the Cure source file to parse

## Returns
- `{ok, Program}` - Successfully parsed AST program
- `{error, {parse_error, Reason, Line, Column}}` - Syntax error with location
- `{error, LexError}` - Lexical error from tokenization
- `{error, {Error, Reason, Stack}}` - Internal parser error

## Example
```erlang
case cure_parser:parse_file("examples/hello.cure") of
    {ok, AST} ->
        cure_utils:debug("Successfully parsed file~n");
    {error, {parse_error, Reason, Line, Col}} ->
        cure_utils:debug("Parse error at ~p:~p: ~p~n", [Line, Col, Reason]);
    {error, Reason} ->
        cure_utils:debug("Error: ~p~n", [Reason])
end.
```

## Error Sources
This function can return errors from:
1. **File I/O**: File not found, permission errors
2. **Lexical Analysis**: Invalid tokens, malformed strings
3. **Syntax Analysis**: Grammar violations, unexpected tokens
""".
-spec parse_file(string()) -> {ok, cure_ast:program()} | {error, term()}.
parse_file(Filename) ->
    case cure_lexer:tokenize_file(Filename) of
        {ok, Tokens} ->
            try
                State = init_parser(Tokens, Filename),
                {Program, _FinalState} = parse_program(State),
                {ok, Program}
            catch
                throw:{parse_error, Reason, Line, Column} ->
                    {error, {parse_error, Reason, Line, Column}};
                Error:Reason:Stack ->
                    {error, {Error, Reason, Stack}}
            end;
        {error, Reason} ->
            {error, Reason}
    end.

%% Internal Functions

%% Initialize parser state
init_parser([], Filename) ->
    #parser_state{
        tokens = [],
        current = eof,
        position = 0,
        filename = Filename
    };
init_parser([First | Rest], Filename) ->
    #parser_state{
        tokens = Rest,
        current = First,
        position = 1,
        filename = Filename
    }.

%% Get current token
current_token(#parser_state{current = Current}) ->
    Current.

%% Advance to next token
advance(#parser_state{tokens = [], filename = Filename}) ->
    #parser_state{
        tokens = [],
        current = eof,
        position = 0,
        filename = Filename
    };
advance(#parser_state{tokens = [Next | Rest], position = Pos, filename = Filename}) ->
    #parser_state{
        tokens = Rest,
        current = Next,
        position = Pos + 1,
        filename = Filename
    }.

%% Check if current token matches expected type
match_token(State, TokenType) ->
    case current_token(State) of
        eof -> false;
        Token -> get_token_type(Token) =:= TokenType
    end.

%% Get token type from token record
get_token_type(Token) when is_record(Token, token) ->
    Token#token.type;
get_token_type(_) ->
    unknown.

%% Get token value from token record
get_token_value(Token) when is_record(Token, token) ->
    Token#token.value;
get_token_value(Token) ->
    Token.

%% Get token location
get_token_location(Token) when is_record(Token, token) ->
    get_token_location(Token, undefined);
get_token_location(_) ->
    #location{line = 0, column = 0, file = undefined}.

%% Get token location with filename
get_token_location(Token, Filename) when is_record(Token, token) ->
    #location{
        line = Token#token.line,
        column = Token#token.column,
        file = Filename
    };
get_token_location(_, Filename) ->
    #location{line = 0, column = 0, file = Filename}.

%% Get location from parser state and token
get_location(#parser_state{filename = Filename}, Token) ->
    get_token_location(Token, Filename).

%% Get token line and column as tuple
get_token_line_col(Token) when is_record(Token, token) ->
    {Token#token.line, Token#token.column};
get_token_line_col(eof) ->
    {0, 0};
get_token_line_col(_) ->
    {0, 0}.

%% Expect a specific token type and consume it
expect(State, TokenType) ->
    case match_token(State, TokenType) of
        true ->
            Token = current_token(State),
            {Token, advance(State)};
        false ->
            Current = current_token(State),
            {Line, Col} = get_token_line_col(Current),
            throw(
                {parse_error, {expected, TokenType, got, get_token_type(Current)}, Line, Col}
            )
    end.

%% Parse the entire program
parse_program(State) ->
    parse_items(State, []).

%% Parse top-level items
parse_items(State, Acc) ->
    case current_token(State) of
        eof ->
            {lists:reverse(Acc), State};
        _ ->
            {Item, NewState} = parse_item(State),
            parse_items(NewState, [Item | Acc])
    end.

%% Parse a single top-level item
parse_item(State) ->
    case get_token_type(current_token(State)) of
        module ->
            parse_module(State);
        def ->
            parse_function(State);
        curify ->
            parse_curify_function(State);
        record ->
            parse_record_def(State);
        fsm ->
            parse_fsm(State);
        type ->
            parse_type_def(State);
        import ->
            parse_import(State);
        _ ->
            Token = current_token(State),
            {Line, Col} = get_token_line_col(Token),
            throw({parse_error, {unexpected_token, get_token_type(Token)}, Line, Col})
    end.

%% Parse module definition
parse_module(State) ->
    {_, State1} = expect(State, module),
    {Name, State2} = parse_module_name(State1),
    {_, State3} = expect(State2, do),

    {Exports, State4} =
        case match_token(State3, export) of
            true ->
                parse_export_list(State3);
            false ->
                {[], State3}
        end,

    {Items, State5} = parse_module_items(State4, []),
    {_, State6} = expect(State5, 'end'),

    % Collect all exports from items
    {AllExports, FilteredItems} = collect_exports(Exports, Items),

    Location = get_token_location(current_token(State)),
    Module = #module_def{
        name = Name,
        exports = AllExports,
        items = FilteredItems,
        location = Location
    },
    {Module, State6}.

%% Parse export list
parse_export_list(State) ->
    {_, State1} = expect(State, export),
    {_, State2} = expect(State1, '['),
    {Exports, State3} = parse_export_specs(State2, []),
    {_, State4} = expect(State3, ']'),
    {Exports, State4}.

%% Parse export specifications
parse_export_specs(State, Acc) ->
    case match_token(State, ']') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {Export, State1} = parse_export_spec(State),
            case match_token(State1, ',') of
                true ->
                    {_, State2} = expect(State1, ','),
                    parse_export_specs(State2, [Export | Acc]);
                false ->
                    {lists:reverse([Export | Acc]), State1}
            end
    end.

%% Parse single export spec (name/arity or plain identifier)
parse_export_spec(State) ->
    % Allow certain keywords to be used as identifiers in export lists (same as imports)
    {NameToken, State1} =
        case get_token_type(current_token(State)) of
            identifier -> expect(State, identifier);
            atom -> expect(State, atom);
            'Ok' -> expect(State, 'Ok');
            'Error' -> expect(State, 'Error');
            'Some' -> expect(State, 'Some');
            'None' -> expect(State, 'None');
            'ok' -> expect(State, 'ok');
            'error' -> expect(State, 'error');
            'not' -> expect(State, 'not');
            'and' -> expect(State, 'and');
            'or' -> expect(State, 'or');
            _ -> expect(State, identifier)
        end,
    Name =
        case get_token_type(NameToken) of
            identifier -> binary_to_atom(get_token_value(NameToken), utf8);
            % Already an atom from lexer
            atom -> get_token_value(NameToken);
            'Ok' -> 'Ok';
            'Error' -> 'Error';
            'Some' -> 'Some';
            'None' -> 'None';
            'ok' -> ok;
            'error' -> error;
            'not' -> 'not';
            'and' -> 'and';
            'or' -> 'or'
        end,
    Location = get_token_location(NameToken),

    case match_token(State1, '/') of
        true ->
            % Function/arity specification
            {_, State2} = expect(State1, '/'),
            {ArityToken, State3} = expect(State2, number),
            Arity = get_token_value(ArityToken),

            Export = #export_spec{
                name = Name,
                arity = Arity,
                location = Location
            },
            {Export, State3};
        false ->
            % Plain identifier (type, constant, etc.)
            Export = #export_spec{
                name = Name,
                % undefined indicates a non-function export
                arity = undefined,
                location = Location
            },
            {Export, State1}
    end.

%% Parse export statement as module item
parse_export(State) ->
    {_, State1} = expect(State, export),
    {_, State2} = expect(State1, '['),
    {Exports, State3} = parse_export_specs(State2, []),
    {_, State4} = expect(State3, ']'),

    % Return as an export item
    {{export_list, Exports}, State4}.

%% Collect exports from module items and merge with header exports
collect_exports(HeaderExports, Items) ->
    collect_exports_helper(Items, HeaderExports, [], []).

collect_exports_helper([], ExportsAcc, ItemsAcc, _) ->
    {lists:reverse(ExportsAcc), lists:reverse(ItemsAcc)};
collect_exports_helper([{{export_list, Exports}} | Rest], ExportsAcc, ItemsAcc, _) ->
    collect_exports_helper(Rest, Exports ++ ExportsAcc, ItemsAcc, []);
collect_exports_helper([Item | Rest], ExportsAcc, ItemsAcc, _) ->
    collect_exports_helper(Rest, ExportsAcc, [Item | ItemsAcc], []).

%% Parse module items
parse_module_items(State, Acc) ->
    case get_token_type(current_token(State)) of
        'end' ->
            % Group function clauses before returning
            GroupedItems = group_function_clauses(lists:reverse(Acc)),
            {GroupedItems, State};
        _ ->
            {Item, State1} = parse_module_item(State),
            parse_module_items(State1, [Item | Acc])
    end.

%% Parse single module item (similar to parse_item but includes export)
parse_module_item(State) ->
    case get_token_type(current_token(State)) of
        def ->
            parse_function(State);
        curify ->
            parse_curify_function(State);
        record ->
            parse_record_def(State);
        fsm ->
            parse_fsm(State);
        type ->
            parse_type_def(State);
        import ->
            parse_import(State);
        export ->
            parse_export(State);
        _ ->
            Token = current_token(State),
            {Line, Col} = get_token_line_col(Token),
            throw({parse_error, {unexpected_token, get_token_type(Token)}, Line, Col})
    end.

%% Parse function definition
parse_function(State) ->
    {DefToken, State1} = expect(State, def),

    % Allow certain keywords to be used as function names (same as export specs)
    {NameToken, State2} =
        case get_token_type(current_token(State1)) of
            identifier -> expect(State1, identifier);
            atom -> expect(State1, atom);
            'Ok' -> expect(State1, 'Ok');
            'Error' -> expect(State1, 'Error');
            'Some' -> expect(State1, 'Some');
            'None' -> expect(State1, 'None');
            'ok' -> expect(State1, 'ok');
            'error' -> expect(State1, 'error');
            'not' -> expect(State1, 'not');
            'and' -> expect(State1, 'and');
            'or' -> expect(State1, 'or');
            _ -> expect(State1, identifier)
        end,
    Name =
        case get_token_type(NameToken) of
            identifier -> binary_to_atom(get_token_value(NameToken), utf8);
            % Already an atom from lexer
            atom -> get_token_value(NameToken);
            'Ok' -> 'Ok';
            'Error' -> 'Error';
            'Some' -> 'Some';
            'None' -> 'None';
            'ok' -> ok;
            'error' -> error;
            'not' -> 'not';
            'and' -> 'and';
            'or' -> 'or'
        end,

    {_, State3} = expect(State2, '('),
    {Params, State4} = parse_parameters(State3, []),
    {_, State5} = expect(State4, ')'),

    {ReturnType, State6} =
        case match_token(State5, ':') of
            true ->
                {_, State5a} = expect(State5, ':'),
                parse_type(State5a);
            false ->
                case match_token(State5, '->') of
                    true ->
                        {_, State5b} = expect(State5, '->'),
                        parse_type(State5b);
                    false ->
                        {undefined, State5}
                end
        end,

    % Support both syntax orderings:
    % 1. when constraint -> return_type (original)
    % 2. -> return_type when constraint (new)
    {Constraint, State7, ReturnType2} =
        case match_token(State6, 'when') of
            true ->
                % Original syntax: when constraint -> return_type
                {_, State6a} = expect(State6, 'when'),
                {ConstraintExpr, State6b} = parse_expression(State6a),
                % Check for -> return_type after when clause
                case match_token(State6b, '->') of
                    true ->
                        {_, State6c} = expect(State6b, '->'),
                        {RetType, State6d} = parse_type(State6c),
                        {ConstraintExpr, State6d, RetType};
                    false ->
                        {ConstraintExpr, State6b, ReturnType}
                end;
            false ->
                % Check if we have a return type already and there's a when clause after it
                % New syntax: -> return_type when constraint
                case (ReturnType =/= undefined) andalso match_token(State6, 'when') of
                    true ->
                        {_, State6a} = expect(State6, 'when'),
                        {ConstraintExpr, State6b} = parse_expression(State6a),
                        {ConstraintExpr, State6b, ReturnType};
                    false ->
                        {undefined, State6, ReturnType}
                end
        end,

    % Support both = syntax and do...end syntax
    {Body, State10} =
        case match_token(State7, do) of
            true ->
                % do...end syntax
                {_, State8} = expect(State7, do),
                {FuncBody, State9} = parse_function_body(State8),
                {_, State10_do} = expect(State9, 'end'),
                {FuncBody, State10_do};
            false ->
                % = syntax
                {_, State8} = expect(State7, '='),
                {FuncBody, State9} = parse_function_body(State8),
                {FuncBody, State9}
        end,

    % Use the correct return type (ReturnType2 if set, otherwise ReturnType)
    FinalReturnType =
        case ReturnType2 of
            undefined -> ReturnType;
            _ -> ReturnType2
        end,

    % All functions are private by default unless exported
    IsPrivate = false,

    Location = get_token_location(DefToken),

    % Create a function_clause for the new multi-clause representation
    Clause = #function_clause{
        params = Params,
        return_type = FinalReturnType,
        constraint = Constraint,
        body = Body,
        location = Location
    },

    % Create function_def with both new (clauses) and old (params/body) fields for backward compatibility
    Function = #function_def{
        name = Name,
        % New: list of clauses
        clauses = [Clause],
        % DEPRECATED: kept for backward compatibility
        params = Params,
        return_type = FinalReturnType,
        % DEPRECATED: kept for backward compatibility
        constraint = Constraint,
        % DEPRECATED: kept for backward compatibility
        body = Body,
        is_private = IsPrivate,
        location = Location
    },
    {Function, State10}.

%% Parse curify function definition
%% Syntax: curify name(params): Type = {module, function, arity}
parse_curify_function(State) ->
    {DefToken, State1} = expect(State, curify),

    % Allow certain keywords to be used as function names (same as regular functions)
    {NameToken, State2} =
        case get_token_type(current_token(State1)) of
            identifier -> expect(State1, identifier);
            atom -> expect(State1, atom);
            'Ok' -> expect(State1, 'Ok');
            'Error' -> expect(State1, 'Error');
            'Some' -> expect(State1, 'Some');
            'None' -> expect(State1, 'None');
            'ok' -> expect(State1, 'ok');
            'error' -> expect(State1, 'error');
            'not' -> expect(State1, 'not');
            'and' -> expect(State1, 'and');
            'or' -> expect(State1, 'or');
            _ -> expect(State1, identifier)
        end,
    Name =
        case get_token_type(NameToken) of
            identifier -> binary_to_atom(get_token_value(NameToken), utf8);
            % Already an atom from lexer
            atom -> get_token_value(NameToken);
            'Ok' -> 'Ok';
            'Error' -> 'Error';
            'Some' -> 'Some';
            'None' -> 'None';
            'ok' -> ok;
            'error' -> error;
            'not' -> 'not';
            'and' -> 'and';
            'or' -> 'or'
        end,

    {_, State3} = expect(State2, '('),
    {Params, State4} = parse_parameters(State3, []),
    {_, State5} = expect(State4, ')'),

    {ReturnType, State6} =
        case match_token(State5, ':') of
            true ->
                {_, State5a} = expect(State5, ':'),
                parse_type(State5a);
            false ->
                case match_token(State5, '->') of
                    true ->
                        {_, State5b} = expect(State5, '->'),
                        parse_type(State5b);
                    false ->
                        % For curify, return type is required for type safety
                        throw({parse_error, {missing_return_type_for_curify}, 0, 0})
                end
        end,

    {Constraint, State7} =
        case match_token(State6, 'when') of
            true ->
                {_, State6a} = expect(State6, 'when'),
                parse_expression(State6a);
            false ->
                {undefined, State6}
        end,

    {_, State8} = expect(State7, '='),

    % Parse the Erlang function reference tuple: {module, function, arity}
    {_, State9} = expect(State8, '{'),
    {ModuleToken, State10} = expect(State9, identifier),
    ErlangModule = binary_to_atom(get_token_value(ModuleToken), utf8),

    {_, State11} = expect(State10, ','),
    {FunctionToken, State12} = expect(State11, identifier),
    ErlangFunction = binary_to_atom(get_token_value(FunctionToken), utf8),

    {_, State13} = expect(State12, ','),
    {ArityToken, State14} = expect(State13, number),
    ErlangArity = get_token_value(ArityToken),

    {_, State15} = expect(State14, '}'),

    % Validate arity matches parameter count
    ParamCount = length(Params),
    case ErlangArity of
        ParamCount ->
            ok;
        _ ->
            throw({parse_error, {curify_arity_mismatch, ParamCount, ErlangArity}, 0, 0})
    end,

    IsPrivate = false,
    Location = get_token_location(DefToken),
    CurifyFunction = #curify_function_def{
        name = Name,
        params = Params,
        return_type = ReturnType,
        constraint = Constraint,
        erlang_module = ErlangModule,
        erlang_function = ErlangFunction,
        erlang_arity = ErlangArity,
        is_private = IsPrivate,
        location = Location
    },
    {CurifyFunction, State15}.

%% Parse function parameters
parse_parameters(State, Acc) ->
    case match_token(State, ')') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {Param, State1} = parse_parameter(State),
            case match_token(State1, ',') of
                true ->
                    {_, State2} = expect(State1, ','),
                    parse_parameters(State2, [Param | Acc]);
                false ->
                    {lists:reverse([Param | Acc]), State1}
            end
    end.

%% Parse single parameter
parse_parameter(State) ->
    {NameToken, State1} = expect(State, identifier),
    Name = binary_to_atom(get_token_value(NameToken), utf8),
    Location = get_token_location(NameToken),

    {Type, State2} =
        case match_token(State1, ':') of
            true ->
                {_, State1a} = expect(State1, ':'),
                parse_type(State1a);
            false ->
                % No type annotation - use a generic type
                DefaultType = #primitive_type{
                    name = 'Any',
                    location = Location
                },
                {DefaultType, State1}
        end,

    Param = #param{
        name = Name,
        type = Type,
        location = Location
    },
    {Param, State2}.

%% Parse record definition: record Name(Type1, Type2, ...) do field: Type end
parse_record_def(State) ->
    {_, State1} = expect(State, record),
    {NameToken, State2} = expect(State1, identifier),
    Name = binary_to_atom(get_token_value(NameToken), utf8),

    % Parse optional type parameters
    {TypeParams, State3} =
        case match_token(State2, '(') of
            true ->
                {_, State2a} = expect(State2, '('),
                {Params, State2b} = parse_type_parameters(State2a, []),
                {_, State2c} = expect(State2b, ')'),
                {Params, State2c};
            false ->
                {[], State2}
        end,

    {_, State4} = expect(State3, do),

    {Fields, State5} = parse_record_fields(State4, []),
    {_, State6} = expect(State5, 'end'),

    Location = get_token_location(NameToken),
    Record = #record_def{
        name = Name,
        type_params = TypeParams,
        fields = Fields,
        location = Location
    },
    {Record, State6}.

%% Parse record fields
parse_record_fields(State, Acc) ->
    case match_token(State, 'end') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {Field, State1} = parse_record_field(State),
            parse_record_fields(State1, [Field | Acc])
    end.

%% Parse single record field: name: Type
parse_record_field(State) ->
    {NameToken, State1} = expect(State, identifier),
    Name = binary_to_atom(get_token_value(NameToken), utf8),
    {_, State2} = expect(State1, ':'),
    {Type, State3} = parse_type(State2),

    Location = get_token_location(NameToken),
    Field = #record_field_def{
        name = Name,
        type = Type,
        default_value = undefined,
        location = Location
    },
    {Field, State3}.

%% Parse FSM definition
parse_fsm(State) ->
    {_, State1} = expect(State, fsm),
    {NameToken, State2} = expect(State1, identifier),
    Name = binary_to_atom(get_token_value(NameToken), utf8),
    {_, State3} = expect(State2, do),

    {States, State4} = parse_fsm_states_declaration(State3),
    {Initial, State5} = parse_fsm_initial(State4),
    {StateDefs, State6} = parse_fsm_state_definitions(State5, []),

    {_, State7} = expect(State6, 'end'),

    Location = get_token_location(NameToken),
    FSM = #fsm_def{
        name = Name,
        states = States,
        initial = Initial,
        state_defs = StateDefs,
        location = Location
    },
    {FSM, State7}.

%% Parse states declaration: states: [State1, State2, ...]
parse_fsm_states_declaration(State) ->
    {_, State1} = expect(State, states),
    {_, State2} = expect(State1, ':'),
    {_, State3} = expect(State2, '['),
    {States, State4} = parse_atom_list(State3, []),
    {_, State5} = expect(State4, ']'),
    {States, State5}.

%% Parse initial state: initial: StateName
parse_fsm_initial(State) ->
    {_, State1} = expect(State, initial),
    {_, State2} = expect(State1, ':'),
    {StateToken, State3} = expect(State2, identifier),
    Initial = binary_to_atom(get_token_value(StateToken), utf8),
    {Initial, State3}.

%% Parse FSM state definitions
parse_fsm_state_definitions(State, Acc) ->
    case get_token_type(current_token(State)) of
        'end' ->
            {lists:reverse(Acc), State};
        state ->
            {StateDef, State1} = parse_fsm_state_definition(State),
            parse_fsm_state_definitions(State1, [StateDef | Acc]);
        _ ->
            {lists:reverse(Acc), State}
    end.

%% Parse single FSM state definition
parse_fsm_state_definition(State) ->
    {_, State1} = expect(State, state),
    {NameToken, State2} = expect(State1, identifier),
    Name = binary_to_atom(get_token_value(NameToken), utf8),
    {_, State3} = expect(State2, do),

    {Transitions, State4} = parse_fsm_transitions(State3, []),
    {_, State5} = expect(State4, 'end'),

    Location = get_token_location(NameToken),
    StateDef = #state_def{
        name = Name,
        transitions = Transitions,
        location = Location
    },
    {StateDef, State5}.

%% Parse FSM transitions
parse_fsm_transitions(State, Acc) ->
    case get_token_type(current_token(State)) of
        'end' ->
            {lists:reverse(Acc), State};
        event ->
            {Transition, State1} = parse_fsm_transition(State),
            parse_fsm_transitions(State1, [Transition | Acc]);
        timeout ->
            {Transition, State1} = parse_fsm_transition(State),
            parse_fsm_transitions(State1, [Transition | Acc]);
        _ ->
            {lists:reverse(Acc), State}
    end.

%% Parse single FSM transition
parse_fsm_transition(State) ->
    case get_token_type(current_token(State)) of
        event ->
            {_, State1} = expect(State, event),
            {_, State2} = expect(State1, '('),
            {Event, State3} = parse_expression(State2),
            {_, State4} = expect(State3, ')'),

            % Optional guard condition with 'when'
            {Guard, State5} =
                case match_token(State4, 'when') of
                    true ->
                        {_, State4a} = expect(State4, 'when'),
                        parse_expression(State4a);
                    false ->
                        {undefined, State4}
                end,

            {_, State6} = expect(State5, '->'),
            {TargetToken, State7} = expect(State6, identifier),
            Target = binary_to_atom(get_token_value(TargetToken), utf8),
            EventLocation = get_token_location(current_token(State)),

            % Optional action with 'do' - now accepts full expressions or function names
            {Action, State8} =
                case match_token(State7, 'do') of
                    true ->
                        {_, State7a} = expect(State7, 'do'),
                        % Check if it's a simple identifier (function name) or full expression
                        case get_token_type(current_token(State7a)) of
                            identifier ->
                                % Could be function name - check if followed by 'end'
                                {NameToken, State7b} = expect(State7a, identifier),
                                case match_token(State7b, 'end') of
                                    true ->
                                        % Simple function name reference
                                        Name = binary_to_atom(get_token_value(NameToken), utf8),
                                        ActionLocation = get_token_location(NameToken),
                                        {{function_ref, Name, ActionLocation}, State7b};
                                    false ->
                                        % Full expression starting with identifier
                                        {Expr, State7c} = parse_expression(State7a),
                                        {_, State7d} = expect(State7c, 'end'),
                                        {Expr, State7d}
                                end;
                            _ ->
                                % Other expression types
                                {Expr, State7b} = parse_expression(State7a),
                                {_, State7c} = expect(State7b, 'end'),
                                {Expr, State7c}
                        end;
                    false ->
                        {undefined, State7}
                end,

            Transition = #transition{
                event = Event,
                guard = Guard,
                target = Target,
                action = Action,
                location = EventLocation
            },
            {Transition, State8};
        timeout ->
            {_, State1} = expect(State, timeout),
            {_, State2} = expect(State1, '('),
            {TimeoutExpr, State3} = parse_expression(State2),
            {_, State4} = expect(State3, ')'),

            % Optional guard condition with 'when' for timeout as well
            {Guard, State5} =
                case match_token(State4, 'when') of
                    true ->
                        {_, State4a} = expect(State4, 'when'),
                        parse_expression(State4a);
                    false ->
                        {undefined, State4}
                end,

            {_, State6} = expect(State5, '->'),
            {TargetToken, State7} = expect(State6, identifier),
            Target = binary_to_atom(get_token_value(TargetToken), utf8),
            TimeoutLocation = get_token_location(current_token(State)),

            % Optional action with 'do' - now accepts full expressions or function names
            {Action, State8} =
                case match_token(State7, 'do') of
                    true ->
                        {_, State7a} = expect(State7, 'do'),
                        % Check if it's a simple identifier (function name) or full expression
                        case get_token_type(current_token(State7a)) of
                            identifier ->
                                % Could be function name - check if followed by 'end'
                                {NameToken, State7b} = expect(State7a, identifier),
                                case match_token(State7b, 'end') of
                                    true ->
                                        % Simple function name reference
                                        Name = binary_to_atom(get_token_value(NameToken), utf8),
                                        ActionLocation = get_token_location(NameToken),
                                        {{function_ref, Name, ActionLocation}, State7b};
                                    false ->
                                        % Full expression starting with identifier
                                        {Expr, State7c} = parse_expression(State7a),
                                        {_, State7d} = expect(State7c, 'end'),
                                        {Expr, State7d}
                                end;
                            _ ->
                                % Other expression types
                                {Expr, State7b} = parse_expression(State7a),
                                {_, State7c} = expect(State7b, 'end'),
                                {Expr, State7c}
                        end;
                    false ->
                        {undefined, State7}
                end,

            Transition = #transition{
                event = TimeoutExpr,
                guard = Guard,
                target = Target,
                action = Action,
                location = TimeoutLocation
            },
            {Transition, State8}
    end.

%% Parse list of atoms/identifiers (backwards compatibility)
parse_atom_list(State, Acc) ->
    case match_token(State, ']') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {Token, State1} = expect(State, identifier),
            Atom = binary_to_atom(get_token_value(Token), utf8),
            case match_token(State1, ',') of
                true ->
                    {_, State2} = expect(State1, ','),
                    parse_atom_list(State2, [Atom | Acc]);
                false ->
                    {lists:reverse([Atom | Acc]), State1}
            end
    end.

%% Parse import items list (supports both plain identifiers and function/arity specs)
parse_import_items(State, Acc) ->
    case match_token(State, ']') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {Item, State1} = parse_import_item(State),
            case match_token(State1, ',') of
                true ->
                    {_, State2} = expect(State1, ','),
                    parse_import_items(State2, [Item | Acc]);
                false ->
                    {lists:reverse([Item | Acc]), State1}
            end
    end.

%% Parse single import item (identifier or function/arity spec)
parse_import_item(State) ->
    % Allow certain keywords to be used as identifiers in import lists
    {Token, State1} =
        case get_token_type(current_token(State)) of
            identifier -> expect(State, identifier);
            atom -> expect(State, atom);
            'Ok' -> expect(State, 'Ok');
            'Error' -> expect(State, 'Error');
            'Some' -> expect(State, 'Some');
            'None' -> expect(State, 'None');
            'ok' -> expect(State, 'ok');
            'error' -> expect(State, 'error');
            'not' -> expect(State, 'not');
            'and' -> expect(State, 'and');
            'or' -> expect(State, 'or');
            'spawn' -> expect(State, 'spawn');
            'send' -> expect(State, 'send');
            'receive' -> expect(State, 'receive');
            _ -> expect(State, identifier)
        end,
    Name =
        case get_token_type(Token) of
            identifier -> binary_to_atom(get_token_value(Token), utf8);
            % Already an atom from lexer
            atom -> get_token_value(Token);
            'Ok' -> 'Ok';
            'Error' -> 'Error';
            'Some' -> 'Some';
            'None' -> 'None';
            'ok' -> ok;
            'error' -> error;
            'not' -> 'not';
            'and' -> 'and';
            'or' -> 'or';
            'spawn' -> spawn;
            'send' -> send;
            'receive' -> 'receive'
        end,
    Location = get_token_location(Token),

    case match_token(State1, '/') of
        true ->
            % Function/arity specification
            {_, State2} = expect(State1, '/'),
            {ArityToken, State3} = expect(State2, number),
            Arity = get_token_value(ArityToken),

            % Check for optional 'as' alias
            {Alias, State4} =
                case match_token(State3, 'as') of
                    true ->
                        {_, State3a} = expect(State3, 'as'),
                        {AliasToken, State3b} = expect(State3a, identifier),
                        AliasName = binary_to_atom(get_token_value(AliasToken), utf8),
                        {AliasName, State3b};
                    false ->
                        {undefined, State3}
                end,

            FunctionImport = #function_import{
                name = Name,
                arity = Arity,
                alias = Alias,
                location = Location
            },
            {FunctionImport, State4};
        false ->
            % Plain identifier (e.g., type constructor, constant)
            % Check for optional 'as' alias for plain identifiers too
            {Alias, State2} =
                case match_token(State1, 'as') of
                    true ->
                        {_, State1a} = expect(State1, 'as'),
                        {AliasToken, State1b} = expect(State1a, identifier),
                        AliasName = binary_to_atom(get_token_value(AliasToken), utf8),
                        {AliasName, State1b};
                    false ->
                        {undefined, State1}
                end,

            % If we have an alias, create a function import-like structure
            case Alias of
                undefined ->
                    {Name, State2};
                _ ->
                    % Create alias import structure
                    AliasImport = {aliased_import, Name, Alias, Location},
                    {AliasImport, State2}
            end
    end.

%% Parse import statement
parse_import(State) ->
    {_, State1} = expect(State, import),
    {ModuleName, State2} = parse_module_name(State1),

    {Items, State3} =
        case match_token(State2, '[') of
            true ->
                {_, State2a} = expect(State2, '['),
                {ItemList, State2b} = parse_import_items(State2a, []),
                {_, State2c} = expect(State2b, ']'),
                {ItemList, State2c};
            false ->
                {all, State2}
        end,

    % TODO: proper location
    Location = #location{line = 0, column = 0, file = undefined},
    Import = #import_def{
        module = ModuleName,
        items = Items,
        location = Location
    },
    {Import, State3}.

%% Parse module name (supports dotted names like Std.Math)
parse_module_name(State) ->
    {FirstToken, State1} = expect(State, identifier),
    FirstPart = binary_to_atom(get_token_value(FirstToken), utf8),
    parse_module_name_parts(State1, [FirstPart]).

parse_module_name_parts(State, Acc) ->
    case match_token(State, '.') of
        true ->
            {_, State1} = expect(State, '.'),
            {PartToken, State2} = expect(State1, identifier),
            Part = binary_to_atom(get_token_value(PartToken), utf8),
            parse_module_name_parts(State2, [Part | Acc]);
        false ->
            % Combine parts into a dotted atom
            Parts = lists:reverse(Acc),
            ModuleName = list_to_atom(string:join([atom_to_list(P) || P <- Parts], ".")),
            {ModuleName, State}
    end.

%% Parse type definition
parse_type_def(State) ->
    {_, State1} = expect(State, type),
    {NameToken, State2} = expect(State1, identifier),
    Name = binary_to_atom(get_token_value(NameToken), utf8),

    % Parse type parameters if present: type MyType(T, U) = ...
    {TypeParams, State3} =
        case match_token(State2, '(') of
            true ->
                {_, State2a} = expect(State2, '('),
                {Params, State2b} = parse_type_parameter_names(State2a, []),
                {_, State2c} = expect(State2b, ')'),
                {Params, State2c};
            false ->
                {[], State2}
        end,

    {_, State4} = expect(State3, '='),
    {TypeExpr, State5} = parse_type(State4),

    % Parse optional when clause: when length(T) == n
    {Constraint, State6} =
        case match_token(State5, 'when') of
            true ->
                {_, State5a} = expect(State5, 'when'),
                {ConstraintExpr, State5b} = parse_expression(State5a),
                {ConstraintExpr, State5b};
            false ->
                {undefined, State5}
        end,

    Location = get_token_location(NameToken),
    TypeDef = #type_def{
        name = Name,
        params = TypeParams,
        definition = TypeExpr,
        constraint = Constraint,
        location = Location
    },
    {TypeDef, State6}.

%% Parse type parameter names (for type definitions)
parse_type_parameter_names(State, Acc) ->
    case match_token(State, ')') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {Token, State1} = expect(State, identifier),
            ParamName = binary_to_atom(get_token_value(Token), utf8),

            % Check if this is a named parameter with type annotation: "n: Nat"
            {FinalParam, State2} =
                case match_token(State1, ':') of
                    true ->
                        % Named parameter with type annotation
                        {_, State1a} = expect(State1, ':'),
                        {TypeExpr, State1b} = parse_type(State1a),
                        % Create a type_param record for named parameters
                        Location = get_token_location(Token),
                        TypeParam = #type_param{
                            name = ParamName,
                            value = TypeExpr,
                            location = Location
                        },
                        {TypeParam, State1b};
                    false ->
                        % Simple parameter name
                        {ParamName, State1}
                end,

            case match_token(State2, ',') of
                true ->
                    {_, State3} = expect(State2, ','),
                    parse_type_parameter_names(State3, [FinalParam | Acc]);
                false ->
                    {lists:reverse([FinalParam | Acc]), State2}
            end
    end.

%% Parse type expressions with enhanced dependent type support
parse_type(State) ->
    % Parse primary type, then handle union types, then arrow function types
    {PrimaryType, State1} = parse_primary_type(State),
    {UnionType, State2} = parse_type_with_unions(State1, PrimaryType),
    parse_type_with_arrows(State2, UnionType).

%% Parse type with union types (T | U | V)
parse_type_with_unions(State, LeftType) ->
    case match_token(State, '|') of
        true ->
            {_, State1} = expect(State, '|'),
            {RightType, State2} = parse_primary_type(State1),
            Location = get_type_location(LeftType),

            % Create or extend union type
            UnionType =
                case LeftType of
                    #union_type{types = ExistingTypes} ->
                        % Already a union type, add new variant
                        LeftType#union_type{
                            types = ExistingTypes ++ [RightType]
                        };
                    _ ->
                        % Create new union type with two variants
                        #union_type{
                            types = [LeftType, RightType],
                            location = Location
                        }
                end,
            % Continue parsing more union variants if present
            parse_type_with_unions(State2, UnionType);
        false ->
            {LeftType, State}
    end.

%% Parse type with arrow function types (T -> U -> V)
parse_type_with_arrows(State, LeftType) ->
    case match_token(State, '->') of
        true ->
            {_, State1} = expect(State, '->'),
            % Right associative
            {RightType, State2} = parse_type(State1),
            Location = get_type_location(LeftType),

            % Create function type: LeftType -> RightType
            FunctionType = #function_type{
                params = [LeftType],
                return_type = RightType,
                location = Location
            },
            {FunctionType, State2};
        false ->
            {LeftType, State}
    end.

%% Parse primary type expressions
parse_primary_type(State) ->
    Token = current_token(State),
    case get_token_type(Token) of
        identifier ->
            {IdToken, State1} = expect(State, identifier),
            Name = binary_to_atom(get_token_value(IdToken), utf8),
            Location = get_token_location(IdToken),

            % Check for parameterized type like Vector(Float, 3) or List(T)
            case match_token(State1, '(') of
                true ->
                    {_, State2} = expect(State1, '('),
                    {Params, State3} = parse_type_parameters(State2, []),
                    {_, State4} = expect(State3, ')'),

                    Type = #dependent_type{
                        name = Name,
                        params = Params,
                        location = Location
                    },
                    {Type, State4};
                false ->
                    % Simple type name (could be a type variable or primitive type)
                    Type = #primitive_type{
                        name = Name,
                        location = Location
                    },
                    {Type, State1}
            end;
        'Unit' ->
            {UnitToken, State1} = expect(State, 'Unit'),
            Location = get_token_location(UnitToken),
            Type = #primitive_type{
                name = 'Unit',
                location = Location
            },
            {Type, State1};
        % Support common type names that might not be tokenized as 'identifier'
        'Int' ->
            {IntToken, State1} = expect(State, 'Int'),
            Location = get_token_location(IntToken),
            Type = #primitive_type{
                name = 'Int',
                location = Location
            },
            {Type, State1};
        'Float' ->
            {FloatToken, State1} = expect(State, 'Float'),
            Location = get_token_location(FloatToken),
            Type = #primitive_type{
                name = 'Float',
                location = Location
            },
            {Type, State1};
        'String' ->
            {StringToken, State1} = expect(State, 'String'),
            Location = get_token_location(StringToken),
            Type = #primitive_type{
                name = 'String',
                location = Location
            },
            {Type, State1};
        'Bool' ->
            {BoolToken, State1} = expect(State, 'Bool'),
            Location = get_token_location(BoolToken),
            Type = #primitive_type{
                name = 'Bool',
                location = Location
            },
            {Type, State1};
        'Nat' ->
            {NatToken, State1} = expect(State, 'Nat'),
            Location = get_token_location(NatToken),
            Type = #primitive_type{
                name = 'Nat',
                location = Location
            },
            {Type, State1};
        % Type constructors for union types
        'Zero' ->
            {ZeroToken, State1} = expect(State, 'Zero'),
            Location = get_token_location(ZeroToken),
            % Zero is a nullary constructor for Nat
            Type = #primitive_type{
                name = 'Zero',
                location = Location
            },
            {Type, State1};
        'Succ' ->
            {SuccToken, State1} = expect(State, 'Succ'),
            Location = get_token_location(SuccToken),
            parse_type_constructor('Succ', Location, State1);
        'Ok' ->
            {OkToken, State1} = expect(State, 'Ok'),
            Location = get_token_location(OkToken),
            parse_type_constructor('Ok', Location, State1);
        'Error' ->
            {ErrorToken, State1} = expect(State, 'Error'),
            Location = get_token_location(ErrorToken),
            parse_type_constructor('Error', Location, State1);
        'Some' ->
            {SomeToken, State1} = expect(State, 'Some'),
            Location = get_token_location(SomeToken),
            parse_type_constructor('Some', Location, State1);
        'None' ->
            {NoneToken, State1} = expect(State, 'None'),
            Location = get_token_location(NoneToken),
            parse_type_constructor('None', Location, State1);
        fn ->
            parse_function_type(State);
        '(' ->
            % Parenthesized type for grouping: (T -> U) -> V
            {_, State1} = expect(State, '('),
            {Type, State2} = parse_type(State1),
            {_, State3} = expect(State2, ')'),
            {Type, State3};
        '{' ->
            % Tuple type: {T, U, V}
            {_, State1} = expect(State, '{'),
            Location = get_token_location(current_token(State)),

            % Parse tuple element types
            {ElementTypes, State2} = parse_tuple_type_elements(State1, []),
            {_, State3} = expect(State2, '}'),

            Type = #tuple_type{
                element_types = ElementTypes,
                location = Location
            },
            {Type, State3};
        _ ->
            CurrentToken = current_token(State),
            throw({parse_error, {expected_type_got, get_token_type(CurrentToken)}, 0, 0})
    end.

%% Parse type constructor (Ok, Error, Some, None) with optional parameters
parse_type_constructor(Name, Location, State) ->
    case match_token(State, '(') of
        true ->
            % Type constructor with parameters: Ok(T), Error(E)
            {_, State1} = expect(State, '('),
            {Params, State2} = parse_type_parameters(State1, []),
            {_, State3} = expect(State2, ')'),
            Type = #dependent_type{
                name = Name,
                params = Params,
                location = Location
            },
            {Type, State3};
        false ->
            % Type constructor without parameters: None
            Type = #primitive_type{
                name = Name,
                location = Location
            },
            {Type, State}
    end.

%% Parse function type: fn(T1, T2) -> ReturnType
parse_function_type(State) ->
    {FnToken, State1} = expect(State, fn),
    {_, State2} = expect(State1, '('),

    % Parse parameter types
    {ParamTypes, State3} = parse_function_param_types(State2, []),
    {_, State4} = expect(State3, ')'),
    {_, State5} = expect(State4, '->'),

    % Parse return type
    {ReturnType, State6} = parse_type(State5),

    Location = get_token_location(FnToken),
    FunctionType = #function_type{
        params = ParamTypes,
        return_type = ReturnType,
        location = Location
    },
    {FunctionType, State6}.

%% Parse function parameter types
parse_function_param_types(State, Acc) ->
    case match_token(State, ')') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {ParamType, State1} = parse_type(State),
            case match_token(State1, ',') of
                true ->
                    {_, State2} = expect(State1, ','),
                    parse_function_param_types(State2, [ParamType | Acc]);
                false ->
                    {lists:reverse([ParamType | Acc]), State1}
            end
    end.

%% Parse tuple type elements: {T, U, V}
parse_tuple_type_elements(State, Acc) ->
    case match_token(State, '}') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {ElementType, State1} = parse_type(State),
            case match_token(State1, ',') of
                true ->
                    {_, State2} = expect(State1, ','),
                    parse_tuple_type_elements(State2, [ElementType | Acc]);
                false ->
                    {lists:reverse([ElementType | Acc]), State1}
            end
    end.

%% Parse type parameters
parse_type_parameters(State, Acc) ->
    case match_token(State, ')') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {TypeParam, State1} = parse_type_parameter(State),
            case match_token(State1, ',') of
                true ->
                    {_, State2} = expect(State1, ','),
                    parse_type_parameters(State2, [TypeParam | Acc]);
                false ->
                    {lists:reverse([TypeParam | Acc]), State1}
            end
    end.

%% Parse single type parameter
parse_type_parameter(State) ->
    Token = current_token(State),
    case get_token_type(Token) of
        % Handle numeric literals as type-level values
        number ->
            {NumberToken, State1} = expect(State, number),
            Value = get_token_value(NumberToken),
            Location = get_token_location(NumberToken),
            Param = #type_param{
                name = undefined,
                value = #literal_expr{
                    value = Value,
                    location = Location
                },
                location = Location
            },
            {Param, State1};
        % Handle identifiers as type variables or types
        identifier ->
            % Check if this identifier is part of a larger expression (like n-1)
            % by looking ahead to see if there's an operator
            case match_operator_ahead(State) of
                true ->
                    % This identifier is part of an expression, parse the full expression
                    try
                        {Expr, StateExpr} = parse_type_parameter_expression(State),
                        ExprLocation = get_expr_location(Expr),
                        Param = #type_param{
                            name = undefined,
                            value = Expr,
                            location = ExprLocation
                        },
                        {Param, StateExpr}
                    catch
                        throw:{parse_error, _, _, _} ->
                            % Fall back to simple identifier handling
                            {IdToken, StateId} = expect(State, identifier),
                            Name = binary_to_atom(get_token_value(IdToken), utf8),
                            Location = get_token_location(IdToken),
                            TypeVar = #identifier_expr{
                                name = Name,
                                location = Location
                            },
                            FallbackParam = #type_param{
                                name = undefined,
                                value = TypeVar,
                                location = Location
                            },
                            {FallbackParam, StateId}
                    end;
                false ->
                    % Simple identifier case - could be type variable or parameterized type
                    {IdToken, State1} = expect(State, identifier),
                    Name = binary_to_atom(get_token_value(IdToken), utf8),
                    Location = get_token_location(IdToken),

                    % Check if this is a type constraint (name: Type)
                    case match_token(State1, ':') of
                        true ->
                            % This is a type constraint like 'rows: Nat'
                            {_, State2} = expect(State1, ':'),
                            {ConstraintType, State3} = parse_type(State2),
                            Param = #type_param{
                                name = Name,
                                value = ConstraintType,
                                location = Location
                            },
                            {Param, State3};
                        false ->
                            % Check if this is a parameterized type (e.g., List(T) within another type)
                            case match_token(State1, '(') of
                                true ->
                                    % This is a parameterized type, parse it as such
                                    {_, State2} = expect(State1, '('),
                                    {Params, State3} = parse_type_parameters(State2, []),
                                    {_, State4} = expect(State3, ')'),

                                    Type = #dependent_type{
                                        name = Name,
                                        params = Params,
                                        location = Location
                                    },
                                    Param = #type_param{
                                        name = undefined,
                                        value = Type,
                                        location = Location
                                    },
                                    {Param, State4};
                                false ->
                                    % This is either a type variable or a simple type
                                    % Create as type variable (identifier expression)
                                    TypeVar = #identifier_expr{
                                        name = Name,
                                        location = Location
                                    },
                                    Param = #type_param{
                                        name = undefined,
                                        value = TypeVar,
                                        location = Location
                                    },
                                    {Param, State1}
                            end
                    end
            end;
        % Handle other cases by trying expression parsing for type parameters
        _ ->
            try
                {Expr, State1} = parse_type_parameter_expression(State),
                ExprLocation = get_expr_location(Expr),
                Param = #type_param{
                    name = undefined,
                    value = Expr,
                    location = ExprLocation
                },
                {Param, State1}
            catch
                throw:{parse_error, _, _, _} ->
                    % If expression parsing fails, try type parsing
                    try
                        {Type, State2} = parse_type(State),
                        TypeLocation = get_expr_location(Type),
                        TypeParam = #type_param{
                            name = undefined,
                            value = Type,
                            location = TypeLocation
                        },
                        {TypeParam, State2}
                    catch
                        throw:{parse_error, _, _, _} ->
                            % If both fail, give a better error
                            CurrentToken = current_token(State),
                            throw(
                                {parse_error,
                                    {expected_type_parameter_got, get_token_type(CurrentToken)}, 0,
                                    0}
                            )
                    end
            end
    end.

%% Parse expressions with operator precedence
parse_expression(State) ->
    parse_expression_or_block(State).

%% Parse type parameter expressions - similar to parse_expression but stops at type parameter delimiters
parse_type_parameter_expression(State) ->
    parse_type_parameter_binary_expression(State, 0).

parse_type_parameter_binary_expression(State, MinPrec) ->
    {Left, State1} = parse_primary_expression(State),
    parse_type_parameter_binary_rest(State1, Left, MinPrec).

parse_type_parameter_binary_rest(State, Left, MinPrec) ->
    case current_token(State) of
        eof ->
            {Left, State};
        Token ->
            TokenType = get_token_type(Token),
            % Stop parsing at type parameter delimiters
            case TokenType of
                ',' ->
                    {Left, State};
                ')' ->
                    {Left, State};
                _ ->
                    case get_operator_info(TokenType) of
                        {Prec, Assoc} when Prec >= MinPrec ->
                            {_, State1} = expect(State, TokenType),
                            NextMinPrec =
                                case Assoc of
                                    left -> Prec + 1;
                                    right -> Prec
                                end,
                            {Right, State2} = parse_type_parameter_binary_expression(
                                State1, NextMinPrec
                            ),
                            Location = get_token_location(Token),
                            BinOp = #binary_op_expr{
                                op = TokenType,
                                left = Left,
                                right = Right,
                                location = Location
                            },
                            parse_type_parameter_binary_rest(State2, BinOp, MinPrec);
                        _ ->
                            {Left, State}
                    end
            end
    end.

%% Parse expression for match clause body - parse single expression only
parse_match_clause_body(State) ->
    % Parse a single expression for the match clause body
    % Don't try to parse blocks or sequences - keep it simple
    parse_binary_expression(State, 0).

%% Parse let value expression that stops at 'in' keyword
parse_let_value_expression(State) ->
    parse_let_value_binary_expression(State, 0).

parse_let_value_binary_expression(State, MinPrec) ->
    {Left, State1} = parse_primary_expression(State),
    parse_let_value_binary_rest(State1, Left, MinPrec).

parse_let_value_binary_rest(State, Left, MinPrec) ->
    case current_token(State) of
        eof ->
            {Left, State};
        Token ->
            TokenType = get_token_type(Token),
            % Stop parsing at 'in' keyword only
            case TokenType of
                'in' ->
                    {Left, State};
                'as' ->
                    % Special handling for type annotation in let context
                    {Prec, _} = get_operator_info('as'),
                    case Prec >= MinPrec of
                        true ->
                            {_, State1} = expect(State, 'as'),
                            {TypeExpr, State2} = parse_type(State1),
                            Location = get_token_location(Token),
                            TypeAnnotation = #type_annotation_expr{
                                expr = Left,
                                type = TypeExpr,
                                location = Location
                            },
                            parse_let_value_binary_rest(State2, TypeAnnotation, MinPrec);
                        false ->
                            {Left, State}
                    end;
                _ ->
                    case get_operator_info(TokenType) of
                        {Prec, Assoc} when Prec >= MinPrec ->
                            {_, State1} = expect(State, TokenType),
                            NextMinPrec =
                                case Assoc of
                                    left -> Prec + 1;
                                    right -> Prec
                                end,
                            {Right, State2} = parse_let_value_binary_expression(
                                State1, NextMinPrec
                            ),
                            Location = get_token_location(Token),
                            BinOp = #binary_op_expr{
                                op = TokenType,
                                left = Left,
                                right = Right,
                                location = Location
                            },
                            parse_let_value_binary_rest(State2, BinOp, MinPrec);
                        _ ->
                            {Left, State}
                    end
            end
    end.

%% Check if there should be a body expression after a let binding
is_let_body_continuation(State) ->
    case get_token_type(current_token(State)) of
        % These tokens suggest there's a body expression

        % Variable or function call
        identifier -> true;
        % Literal
        number -> true;
        % Literal
        string -> true;
        % Parenthesized expression
        '(' -> true;
        % List
        '[' -> true;
        % Tuple
        '{' -> true;
        % match expression
        'match' -> true;
        % nested let expression
        'let' -> true;
        % lambda
        'fn' -> true;
        % These tokens suggest end of let expression

        % End of match/if/etc
        'end' -> false;
        % End of input
        eof -> false;
        % Conservative: assume no body
        _ -> false
    end.

%% Parse expression or block of expressions
parse_expression_or_block(State) ->
    % Try to parse as a block first (multiple expressions)
    {FirstExpr, State1} = parse_binary_expression(State, 0),

    % Check if there's a newline followed by more expressions
    case is_block_continuation(State1) of
        true ->
            % Parse as a block
            {RestExprs, State2} = parse_expression_sequence(State1, []),
            Location = get_expr_location(FirstExpr),
            BlockExpr = #block_expr{
                expressions = [FirstExpr | RestExprs],
                location = Location
            },
            {BlockExpr, State2};
        false ->
            % Single expression
            {FirstExpr, State1}
    end.

%% Check if we should continue parsing as a block
is_block_continuation(State) ->
    % Check if next token starts a new expression or statement
    case current_token(State) of
        eof ->
            false;
        Token ->
            case get_token_type(Token) of
                'let' -> true;
                % Could be function call
                identifier -> true;
                _ -> false
            end
    end.

%% Parse sequence of expressions in a block
parse_expression_sequence(State, Acc) ->
    case is_block_continuation(State) of
        true ->
            {Expr, State1} = parse_binary_expression(State, 0),
            parse_expression_sequence(State1, [Expr | Acc]);
        false ->
            {lists:reverse(Acc), State}
    end.

%% Get location from expression
get_expr_location(#literal_expr{location = Loc}) -> Loc;
get_expr_location(#identifier_expr{location = Loc}) -> Loc;
get_expr_location(#binary_op_expr{location = Loc}) -> Loc;
get_expr_location(#unary_op_expr{location = Loc}) -> Loc;
get_expr_location(#function_call_expr{location = Loc}) -> Loc;
get_expr_location(#list_expr{location = Loc}) -> Loc;
get_expr_location(#cons_expr{location = Loc}) -> Loc;
get_expr_location(#type_annotation_expr{location = Loc}) -> Loc;
get_expr_location(#tuple_expr{location = Loc}) -> Loc;
get_expr_location(#let_expr{location = Loc}) -> Loc;
get_expr_location(#block_expr{location = Loc}) -> Loc;
get_expr_location(#string_interpolation_expr{location = Loc}) -> Loc;
get_expr_location(#field_access_expr{location = Loc}) -> Loc;
get_expr_location(#record_update_expr{location = Loc}) -> Loc;
get_expr_location(#record_expr{location = Loc}) -> Loc;
get_expr_location(#primitive_type{location = Loc}) -> Loc;
get_expr_location(#dependent_type{location = Loc}) -> Loc;
get_expr_location(_) -> #location{line = 0, column = 0, file = undefined}.

%% Parse binary expressions with precedence
parse_binary_expression(State, MinPrec) ->
    {Left, State1} = parse_primary_expression(State),
    {Postfix, State2} = parse_postfix_operators(State1, Left),
    parse_binary_rest(State2, Postfix, MinPrec).

%% Parse postfix operators like field access (.field)
parse_postfix_operators(State, Expr) ->
    case current_token(State) of
        eof ->
            {Expr, State};
        Token ->
            case get_token_type(Token) of
                '.' ->
                    % Could be field access or module qualification
                    % Peek ahead to see if next token is identifier followed by '('
                    {_, State1} = expect(State, '.'),
                    case current_token(State1) of
                        eof ->
                            % Incomplete, return as-is
                            {Expr, State};
                        NextToken ->
                            case get_token_type(NextToken) of
                                identifier ->
                                    {FieldToken, State2} = expect(State1, identifier),
                                    FieldName = binary_to_atom(get_token_value(FieldToken), utf8),
                                    FieldLocation = get_token_location(FieldToken),

                                    % Check if this is module.function(args) pattern
                                    case {Expr, match_token(State2, '(')} of
                                        {#identifier_expr{}, true} ->
                                            % This is module qualification, not field access
                                            % Return the original expression and backtrack
                                            % We'll handle this in the old code path
                                            {Expr, State};
                                        _ ->
                                            % Field access: expr.field
                                            FieldAccess = #field_access_expr{
                                                record = Expr,
                                                field = FieldName,
                                                location = FieldLocation
                                            },
                                            % Continue checking for more postfix operators
                                            parse_postfix_operators(State2, FieldAccess)
                                    end;
                                _ ->
                                    {Expr, State}
                            end
                    end;
                _ ->
                    {Expr, State}
            end
    end.

parse_binary_rest(State, Left, MinPrec) ->
    case current_token(State) of
        eof ->
            {Left, State};
        Token ->
            case get_token_type(Token) of
                'as' ->
                    % Special handling for type annotation
                    {Prec, _} = get_operator_info('as'),
                    case Prec >= MinPrec of
                        true ->
                            {_, State1} = expect(State, 'as'),
                            {TypeExpr, State2} = parse_type(State1),
                            Location = get_token_location(Token),
                            TypeAnnotation = #type_annotation_expr{
                                expr = Left,
                                type = TypeExpr,
                                location = Location
                            },
                            parse_binary_rest(State2, TypeAnnotation, MinPrec);
                        false ->
                            {Left, State}
                    end;
                _ ->
                    case get_operator_info(get_token_type(Token)) of
                        {Prec, Assoc} when Prec >= MinPrec ->
                            {_, State1} = expect(State, get_token_type(Token)),
                            NextMinPrec =
                                case Assoc of
                                    left -> Prec + 1;
                                    right -> Prec
                                end,
                            {Right, State2} = parse_binary_expression(State1, NextMinPrec),
                            Location = get_token_location(Token),
                            BinOp = #binary_op_expr{
                                op = get_token_type(Token),
                                left = Left,
                                right = Right,
                                location = Location
                            },
                            parse_binary_rest(State2, BinOp, MinPrec);
                        _ ->
                            {Left, State}
                    end
            end
    end.

%% Get operator precedence and associativity
get_operator_info('+') -> {10, left};
get_operator_info('-') -> {10, left};
get_operator_info('*') -> {20, left};
get_operator_info('/') -> {20, left};
get_operator_info('%') -> {20, left};
get_operator_info('++') -> {15, right};
get_operator_info('|>') -> {1, left};
get_operator_info('as') -> {2, left};
get_operator_info('<') -> {5, left};
get_operator_info('>') -> {5, left};
get_operator_info('<=') -> {5, left};
get_operator_info('>=') -> {5, left};
get_operator_info('==') -> {5, left};
get_operator_info('!=') -> {5, left};
get_operator_info('and') -> {3, left};
get_operator_info('or') -> {2, left};
get_operator_info(_) -> undefined.

%% Parse primary expressions
parse_primary_expression(State) ->
    case current_token(State) of
        eof ->
            throw({parse_error, unexpected_end_of_input, 0, 0});
        Token ->
            case get_token_type(Token) of
                identifier ->
                    parse_identifier_or_call(State);
                '-' ->
                    % Unary minus
                    {_, State1} = expect(State, '-'),
                    {Operand, State2} = parse_primary_expression(State1),
                    Location = get_token_location(current_token(State)),
                    UnaryExpr = #unary_op_expr{
                        op = '-',
                        operand = Operand,
                        location = Location
                    },
                    {UnaryExpr, State2};
                '+' ->
                    % Unary plus
                    {_, State1} = expect(State, '+'),
                    {Operand, State2} = parse_primary_expression(State1),
                    Location = get_token_location(current_token(State)),
                    UnaryExpr = #unary_op_expr{
                        op = '+',
                        operand = Operand,
                        location = Location
                    },
                    {UnaryExpr, State2};
                'not' ->
                    % Unary not
                    {_, State1} = expect(State, 'not'),
                    {Operand, State2} = parse_primary_expression(State1),
                    Location = get_token_location(current_token(State)),
                    UnaryExpr = #unary_op_expr{
                        op = 'not',
                        operand = Operand,
                        location = Location
                    },
                    {UnaryExpr, State2};
                number ->
                    {Token, State1} = expect(State, number),
                    Value = get_token_value(Token),
                    Location = get_token_location(Token),
                    Expr = #literal_expr{
                        value = Value,
                        location = Location
                    },
                    {Expr, State1};
                string ->
                    {Token, State1} = expect(State, string),
                    Value = get_token_value(Token),
                    Location = get_token_location(Token),
                    Expr = #literal_expr{
                        value = Value,
                        location = Location
                    },
                    {Expr, State1};
                interpolation_start ->
                    parse_string_interpolation(State);
                string_part ->
                    parse_string_interpolation(State);
                atom ->
                    {Token, State1} = expect(State, atom),
                    Value = get_token_value(Token),
                    Location = get_token_location(Token),
                    % Check if this is a constructor atom like 'Some', 'None', etc.
                    case Value of
                        'Some' ->
                            parse_atom_constructor_expression(State1, 'Some', Location);
                        'None' ->
                            parse_atom_constructor_expression(State1, 'None', Location);
                        'Ok' ->
                            parse_atom_constructor_expression(State1, 'Ok', Location);
                        'Error' ->
                            parse_atom_constructor_expression(State1, 'Error', Location);
                        ok ->
                            parse_atom_constructor_expression(State1, ok, Location);
                        error ->
                            parse_atom_constructor_expression(State1, error, Location);
                        _ ->
                            % Regular atom literal
                            Expr = #literal_expr{
                                value = Value,
                                location = Location
                            },
                            {Expr, State1}
                    end;
                true ->
                    {Token, State1} = expect(State, true),
                    Location = get_token_location(Token),
                    Expr = #literal_expr{
                        value = true,
                        location = Location
                    },
                    {Expr, State1};
                false ->
                    {Token, State1} = expect(State, false),
                    Location = get_token_location(Token),
                    Expr = #literal_expr{
                        value = false,
                        location = Location
                    },
                    {Expr, State1};
                'Ok' ->
                    parse_constructor_expression(State);
                'Error' ->
                    parse_constructor_expression(State);
                'Some' ->
                    parse_constructor_expression(State);
                'None' ->
                    parse_constructor_expression(State);
                'Zero' ->
                    parse_constructor_expression(State);
                'Succ' ->
                    parse_constructor_expression(State);
                'ok' ->
                    parse_constructor_expression(State);
                'error' ->
                    parse_constructor_expression(State);
                'let' ->
                    parse_let_expression(State);
                '[' ->
                    parse_list_literal(State);
                'fn' ->
                    parse_lambda_expression(State);
                'match' ->
                    parse_match_expression(State);
                'case' ->
                    parse_case_expression(State);
                '(' ->
                    {_, State1} = expect(State, '('),
                    % Check if this is an empty parentheses (unit literal)
                    case match_token(State1, ')') of
                        true ->
                            % Empty parentheses - this is a unit literal
                            {_, State2} = expect(State1, ')'),
                            Location = get_token_location(current_token(State)),
                            Expr = #literal_expr{
                                value = unit,
                                location = Location
                            },
                            {Expr, State2};
                        false ->
                            % Parenthesized expression
                            {Expr, State2} = parse_expression(State1),
                            {_, State3} = expect(State2, ')'),
                            {Expr, State3}
                    end;
                '{' ->
                    parse_tuple_expression(State);
                _ ->
                    throw(
                        {parse_error, {unexpected_token_in_expression, get_token_type(Token)}, 0, 0}
                    )
            end
    end.

%% Parse identifier or function call
parse_identifier_or_call(State) ->
    % Allow certain keywords to be used as identifiers in function calls
    {Token, State1} =
        case get_token_type(current_token(State)) of
            identifier -> expect(State, identifier);
            'ok' -> expect(State, 'ok');
            'error' -> expect(State, 'error');
            _ -> expect(State, identifier)
        end,
    Name =
        case get_token_type(Token) of
            identifier -> binary_to_atom(get_token_value(Token), utf8);
            'ok' -> ok;
            'error' -> error
        end,
    Location = get_location(State, Token),

    % Check for function call (identifier followed by '.')
    case match_token(State1, '.') of
        true ->
            {_, State2} = expect(State1, '.'),
            {FuncToken, State3} = expect(State2, identifier),
            FuncName = binary_to_atom(get_token_value(FuncToken), utf8),
            case match_token(State3, '(') of
                true ->
                    {_, State4} = expect(State3, '('),
                    {Args, State5} = parse_argument_list(State4, []),
                    {_, State6} = expect(State5, ')'),

                    % Create qualified function call
                    ModuleExpr = #identifier_expr{name = Name, location = Location},
                    FuncExpr = #identifier_expr{
                        name = FuncName, location = get_location(State3, FuncToken)
                    },
                    QualifiedFunc = #binary_op_expr{
                        op = '.',
                        left = ModuleExpr,
                        right = FuncExpr,
                        location = Location
                    },
                    CallExpr = #function_call_expr{
                        function = QualifiedFunc,
                        args = Args,
                        location = Location
                    },
                    {CallExpr, State6};
                false ->
                    % Module.function without call
                    ModuleExpr = #identifier_expr{name = Name, location = Location},
                    FuncExpr = #identifier_expr{
                        name = FuncName, location = get_location(State3, FuncToken)
                    },
                    QualifiedExpr = #binary_op_expr{
                        op = '.',
                        left = ModuleExpr,
                        right = FuncExpr,
                        location = Location
                    },
                    {QualifiedExpr, State3}
            end;
        false ->
            % Check for function call, record construction, or simple identifier
            case match_token(State1, '(') of
                true ->
                    % Function call
                    {_, State2} = expect(State1, '('),
                    {Args, State3} = parse_argument_list(State2, []),
                    {_, State4} = expect(State3, ')'),
                    FuncExpr = #identifier_expr{name = Name, location = Location},
                    CallExpr = #function_call_expr{
                        function = FuncExpr,
                        args = Args,
                        location = Location
                    },
                    {CallExpr, State4};
                false ->
                    % Check for record construction or update
                    case match_token(State1, '{') of
                        true ->
                            % Could be Record{field: value, ...} or Record{base | field: value, ...}
                            {_, State2} = expect(State1, '{'),

                            % Check for update syntax (base | fields)
                            case is_identifier_token(current_token(State2)) of
                                true ->
                                    % Peek ahead to see if there's a '|' after the identifier
                                    {MaybeBase, State3} = parse_expression(State2),
                                    case match_token(State3, '|') of
                                        true ->
                                            % Record update: Record{base | field: value}
                                            {_, State4} = expect(State3, '|'),
                                            {Fields, State5} = parse_record_expr_fields(State4, []),
                                            {_, State6} = expect(State5, '}'),
                                            UpdateExpr = #record_update_expr{
                                                name = Name,
                                                base = MaybeBase,
                                                fields = Fields,
                                                location = Location
                                            },
                                            {UpdateExpr, State6};
                                        false ->
                                            % Regular construction, but we already parsed first field name
                                            % We need to reparse as field_name: value
                                            % This is a limitation - for now, error out and reparse
                                            % For simplicity, check if next is ':'
                                            case match_token(State3, ':') of
                                                true ->
                                                    % Back up and parse as regular construction
                                                    {Fields, State4} = parse_record_expr_fields(
                                                        State2, []
                                                    ),
                                                    {_, State5} = expect(State4, '}'),
                                                    RecordExpr = #record_expr{
                                                        name = Name,
                                                        fields = Fields,
                                                        location = Location
                                                    },
                                                    {RecordExpr, State5};
                                                false ->
                                                    throw(
                                                        {parse_error,
                                                            expected_colon_or_pipe_in_record, 0, 0}
                                                    )
                                            end
                                    end;
                                false ->
                                    % Not an identifier, must be regular construction
                                    {Fields, State3} = parse_record_expr_fields(State2, []),
                                    {_, State4} = expect(State3, '}'),
                                    RecordExpr = #record_expr{
                                        name = Name,
                                        fields = Fields,
                                        location = Location
                                    },
                                    {RecordExpr, State4}
                            end;
                        false ->
                            % Simple identifier
                            Expr = #identifier_expr{
                                name = Name,
                                location = Location
                            },
                            {Expr, State1}
                    end
            end
    end.

%% Parse argument list for function calls
parse_argument_list(State, Acc) ->
    case match_token(State, ')') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {Arg, State1} = parse_expression(State),
            case match_token(State1, ',') of
                true ->
                    {_, State2} = expect(State1, ','),
                    parse_argument_list(State2, [Arg | Acc]);
                false ->
                    {lists:reverse([Arg | Acc]), State1}
            end
    end.

%% Parse let expression
parse_let_expression(State) ->
    {_, State1} = expect(State, 'let'),
    {BindingVar, State2} = expect(State1, identifier),
    {_, State3} = expect(State2, '='),
    % Parse binding value - use primary expression to avoid consuming 'in'
    {Value, State4} = parse_let_value_expression(State3),

    VarName = binary_to_atom(get_token_value(BindingVar), utf8),
    Location = get_location(State2, BindingVar),

    % Create a simple identifier pattern for the binding
    Pattern = #identifier_pattern{
        name = VarName,
        location = Location
    },

    Binding = #binding{
        pattern = Pattern,
        value = Value,
        location = Location
    },

    % Check if there's an explicit 'in' keyword or if we should parse the next expression as body
    case match_token(State4, 'in') of
        true ->
            % Explicit let...in syntax
            {_, State5} = expect(State4, 'in'),
            {Body, State6} = parse_expression(State5),
            LetExpr = #let_expr{
                bindings = [Binding],
                body = Body,
                location = Location
            },
            {LetExpr, State6};
        false ->
            % Implicit let syntax - next expression is the body
            % Check if there's another expression that could be the body
            case is_let_body_continuation(State4) of
                true ->
                    {Body, State5} = parse_expression(State4),
                    LetExpr = #let_expr{
                        bindings = [Binding],
                        body = Body,
                        location = Location
                    },
                    {LetExpr, State5};
                false ->
                    % No body, just return the binding variable
                    LetExpr = #let_expr{
                        bindings = [Binding],
                        body = #identifier_expr{name = VarName, location = Location},
                        location = Location
                    },
                    {LetExpr, State4}
            end
    end.

%% Parse tuple expression {1, 2, 3}
parse_tuple_expression(State) ->
    {_, State1} = expect(State, '{'),
    Location = get_token_location(current_token(State)),

    {Elements, State2} = parse_tuple_elements(State1, []),
    {_, State3} = expect(State2, '}'),

    TupleExpr = #tuple_expr{
        elements = Elements,
        location = Location
    },
    {TupleExpr, State3}.

%% Parse comma-separated tuple elements
parse_tuple_elements(State, Acc) ->
    case match_token(State, '}') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {Expr, State1} = parse_expression(State),
            case match_token(State1, ',') of
                true ->
                    {_, State2} = expect(State1, ','),
                    parse_tuple_elements(State2, [Expr | Acc]);
                false ->
                    {lists:reverse([Expr | Acc]), State1}
            end
    end.

%% Parse list literal [1, 2, 3] or [head | tail]
parse_list_literal(State) ->
    {_, State1} = expect(State, '['),
    Location = get_token_location(current_token(State)),

    {Elements, State2} = parse_expression_list(State1, []),
    {_, State3} = expect(State2, ']'),

    % Check if this is a cons expression
    case Elements of
        [{cons, ConsElements, TailExpr}] ->
            % Create a cons expression
            ConsExpr = #cons_expr{
                elements = ConsElements,
                tail = TailExpr,
                location = Location
            },
            {ConsExpr, State3};
        _ ->
            % Regular list expression
            ListExpr = #list_expr{
                elements = Elements,
                location = Location
            },
            {ListExpr, State3}
    end.

%% Parse comma-separated expression list (with support for cons syntax)
parse_expression_list(State, Acc) ->
    case match_token(State, ']') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {Expr, State1} = parse_expression(State),
            case match_token(State1, '|') of
                true ->
                    % Handle cons syntax [head | tail] in expression context
                    {_, State2} = expect(State1, '|'),
                    {TailExpr, State3} = parse_expression(State2),
                    % Create a special cons list expression
                    ConsElements = lists:reverse([Expr | Acc]),
                    {[{cons, ConsElements, TailExpr}], State3};
                false ->
                    case match_token(State1, ',') of
                        true ->
                            {_, State2} = expect(State1, ','),
                            parse_expression_list(State2, [Expr | Acc]);
                        false ->
                            {lists:reverse([Expr | Acc]), State1}
                    end
            end
    end.

%% Parse lambda expression: fn(x, y) -> x + y end
parse_lambda_expression(State) ->
    {_, State1} = expect(State, 'fn'),
    {_, State2} = expect(State1, '('),
    {Params, State3} = parse_lambda_parameters(State2, []),
    {_, State4} = expect(State3, ')'),
    {_, State5} = expect(State4, '->'),
    {Body, State6} = parse_expression(State5),
    {_, State7} = expect(State6, 'end'),

    Location = get_token_location(current_token(State)),
    LambdaExpr = #lambda_expr{
        params = Params,
        body = Body,
        location = Location
    },
    {LambdaExpr, State7}.

%% Parse lambda parameters
parse_lambda_parameters(State, Acc) ->
    case match_token(State, ')') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {Token, State1} = expect(State, identifier),
            ParamName = binary_to_atom(get_token_value(Token), utf8),
            Location = get_token_location(Token),

            % Create parameter without type for now
            Param = #param{
                name = ParamName,
                type = undefined,
                location = Location
            },

            case match_token(State1, ',') of
                true ->
                    {_, State2} = expect(State1, ','),
                    parse_lambda_parameters(State2, [Param | Acc]);
                false ->
                    {lists:reverse([Param | Acc]), State1}
            end
    end.

%% Parse match expression: match expr do pattern -> body end
parse_match_expression(State) ->
    {_, State1} = expect(State, 'match'),
    {Expr, State2} = parse_expression(State1),
    {_, State3} = expect(State2, 'do'),
    {Clauses, State4} = parse_match_clauses(State3, []),
    {_, State5} = expect(State4, 'end'),

    Location = get_token_location(current_token(State)),
    MatchExpr = #match_expr{
        expr = Expr,
        patterns = Clauses,
        location = Location
    },
    {MatchExpr, State5}.

%% Parse case expression: case expr of pattern -> body end
parse_case_expression(State) ->
    {_, State1} = expect(State, 'case'),
    {Expr, State2} = parse_expression(State1),
    {_, State3} = expect(State2, 'of'),
    {Clauses, State4} = parse_match_clauses(State3, []),
    {_, State5} = expect(State4, 'end'),

    Location = get_token_location(current_token(State)),
    % Reuse match_expr AST node since case is essentially the same as match
    MatchExpr = #match_expr{
        expr = Expr,
        patterns = Clauses,
        location = Location
    },
    {MatchExpr, State5}.

%% Parse match clauses
parse_match_clauses(State, Acc) ->
    case match_token(State, 'end') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {Clause, State1} = parse_match_clause(State),
            parse_match_clauses(State1, [Clause | Acc])
    end.

%% Parse single match clause: pattern -> body or pattern when guard -> body
parse_match_clause(State) ->
    {Pattern, State1} = parse_pattern(State),

    % Check if there's a guard clause
    {Guard, State2} =
        case match_token(State1, 'when') of
            true ->
                {_, State1a} = expect(State1, 'when'),
                {GuardExpr, State1b} = parse_expression(State1a),
                {GuardExpr, State1b};
            false ->
                {undefined, State1}
        end,

    {_, State3} = expect(State2, '->'),
    {Body, State4} = parse_match_clause_body(State3),

    Location = get_pattern_location(Pattern),
    Clause = #match_clause{
        pattern = Pattern,
        guard = Guard,
        body = Body,
        location = Location
    },
    {Clause, State4}.

%% Parse patterns
parse_pattern(State) ->
    case get_token_type(current_token(State)) of
        identifier ->
            {Token, State1} = expect(State, identifier),
            Name = binary_to_atom(get_token_value(Token), utf8),
            Location = get_token_location(Token),

            % Check for wildcard pattern
            case Name of
                '_' ->
                    Pattern = #wildcard_pattern{
                        location = Location
                    },
                    {Pattern, State1};
                _ ->
                    % Check if it's a constructor pattern like Ok(value), ok(value), etc.
                    case match_token(State1, '(') of
                        true ->
                            {_, State2} = expect(State1, '('),
                            % Check if there are no arguments (empty constructor)
                            case match_token(State2, ')') of
                                true ->
                                    {_, State3} = expect(State2, ')'),
                                    Pattern = #constructor_pattern{
                                        name = Name,
                                        args = [],
                                        location = Location
                                    },
                                    {Pattern, State3};
                                false ->
                                    % Constructor with arguments - parse all patterns
                                    {Patterns, State3} = parse_pattern_list_for_constructor(
                                        State2, []
                                    ),
                                    {_, State4} = expect(State3, ')'),
                                    Pattern = #constructor_pattern{
                                        name = Name,
                                        args = Patterns,
                                        location = Location
                                    },
                                    {Pattern, State4}
                            end;
                        false ->
                            % Check if it's a record pattern like Person{name: name}
                            case match_token(State1, '{') of
                                true ->
                                    parse_record_pattern(State1, Name, Location);
                                false ->
                                    % Simple identifier pattern
                                    Pattern = #identifier_pattern{
                                        name = Name,
                                        location = Location
                                    },
                                    {Pattern, State1}
                            end
                    end
            end;
        '[' ->
            parse_list_pattern(State);
        '{' ->
            parse_tuple_pattern(State);
        number ->
            {Token, State1} = expect(State, number),
            Value = get_token_value(Token),
            Location = get_token_location(Token),
            Pattern = #literal_pattern{
                value = Value,
                location = Location
            },
            {Pattern, State1};
        string ->
            {Token, State1} = expect(State, string),
            Value = get_token_value(Token),
            Location = get_token_location(Token),
            Pattern = #literal_pattern{
                value = Value,
                location = Location
            },
            {Pattern, State1};
        atom ->
            {Token, State1} = expect(State, atom),
            Value = get_token_value(Token),
            Location = get_token_location(Token),
            % Check if this is a constructor atom like 'Some', 'None', etc.
            case Value of
                'Some' ->
                    case match_token(State1, '(') of
                        true ->
                            {_, State2} = expect(State1, '('),
                            {InnerPattern, State3} = parse_pattern(State2),
                            {_, State4} = expect(State3, ')'),
                            Pattern = #constructor_pattern{
                                name = 'Some',
                                args = [InnerPattern],
                                location = Location
                            },
                            {Pattern, State4};
                        false ->
                            Pattern = #constructor_pattern{
                                name = 'Some',
                                args = undefined,
                                location = Location
                            },
                            {Pattern, State1}
                    end;
                'None' ->
                    case match_token(State1, '(') of
                        true ->
                            {_, State2} = expect(State1, '('),
                            case match_token(State2, ')') of
                                true ->
                                    % Empty constructor call: 'None'()
                                    {_, State3} = expect(State2, ')'),
                                    Pattern = #constructor_pattern{
                                        name = 'None',
                                        args = [],
                                        location = Location
                                    },
                                    {Pattern, State3};
                                false ->
                                    % Constructor with argument: 'None'(value)
                                    {InnerPattern, State3} = parse_pattern(State2),
                                    {_, State4} = expect(State3, ')'),
                                    Pattern = #constructor_pattern{
                                        name = 'None',
                                        args = [InnerPattern],
                                        location = Location
                                    },
                                    {Pattern, State4}
                            end;
                        false ->
                            Pattern = #constructor_pattern{
                                name = 'None',
                                args = undefined,
                                location = Location
                            },
                            {Pattern, State1}
                    end;
                'Ok' ->
                    case match_token(State1, '(') of
                        true ->
                            {_, State2} = expect(State1, '('),
                            {InnerPattern, State3} = parse_pattern(State2),
                            {_, State4} = expect(State3, ')'),
                            Pattern = #constructor_pattern{
                                name = 'Ok',
                                args = [InnerPattern],
                                location = Location
                            },
                            {Pattern, State4};
                        false ->
                            Pattern = #constructor_pattern{
                                name = 'Ok',
                                args = undefined,
                                location = Location
                            },
                            {Pattern, State1}
                    end;
                'Error' ->
                    case match_token(State1, '(') of
                        true ->
                            {_, State2} = expect(State1, '('),
                            {InnerPattern, State3} = parse_pattern(State2),
                            {_, State4} = expect(State3, ')'),
                            Pattern = #constructor_pattern{
                                name = 'Error',
                                args = [InnerPattern],
                                location = Location
                            },
                            {Pattern, State4};
                        false ->
                            Pattern = #constructor_pattern{
                                name = 'Error',
                                args = undefined,
                                location = Location
                            },
                            {Pattern, State1}
                    end;
                ok ->
                    case match_token(State1, '(') of
                        true ->
                            {_, State2} = expect(State1, '('),
                            {InnerPattern, State3} = parse_pattern(State2),
                            {_, State4} = expect(State3, ')'),
                            Pattern = #constructor_pattern{
                                name = ok,
                                args = [InnerPattern],
                                location = Location
                            },
                            {Pattern, State4};
                        false ->
                            Pattern = #constructor_pattern{
                                name = ok,
                                args = undefined,
                                location = Location
                            },
                            {Pattern, State1}
                    end;
                error ->
                    case match_token(State1, '(') of
                        true ->
                            {_, State2} = expect(State1, '('),
                            {InnerPattern, State3} = parse_pattern(State2),
                            {_, State4} = expect(State3, ')'),
                            Pattern = #constructor_pattern{
                                name = error,
                                args = [InnerPattern],
                                location = Location
                            },
                            {Pattern, State4};
                        false ->
                            Pattern = #constructor_pattern{
                                name = error,
                                args = undefined,
                                location = Location
                            },
                            {Pattern, State1}
                    end;
                _ ->
                    % Regular atom literal pattern
                    Pattern = #literal_pattern{
                        value = Value,
                        location = Location
                    },
                    {Pattern, State1}
            end;
        'Ok' ->
            {Token, State1} = expect(State, 'Ok'),
            Location = get_token_location(Token),
            case match_token(State1, '(') of
                true ->
                    {_, State2} = expect(State1, '('),
                    {InnerPattern, State3} = parse_pattern(State2),
                    {_, State4} = expect(State3, ')'),
                    Pattern = #constructor_pattern{
                        name = 'Ok',
                        args = [InnerPattern],
                        location = Location
                    },
                    {Pattern, State4};
                false ->
                    Pattern = #constructor_pattern{
                        name = 'Ok',
                        args = undefined,
                        location = Location
                    },
                    {Pattern, State1}
            end;
        'Error' ->
            {Token, State1} = expect(State, 'Error'),
            Location = get_token_location(Token),
            case match_token(State1, '(') of
                true ->
                    {_, State2} = expect(State1, '('),
                    {InnerPattern, State3} = parse_pattern(State2),
                    {_, State4} = expect(State3, ')'),
                    Pattern = #constructor_pattern{
                        name = 'Error',
                        args = [InnerPattern],
                        location = Location
                    },
                    {Pattern, State4};
                false ->
                    Pattern = #constructor_pattern{
                        name = 'Error',
                        args = undefined,
                        location = Location
                    },
                    {Pattern, State1}
            end;
        'Some' ->
            {Token, State1} = expect(State, 'Some'),
            Location = get_token_location(Token),
            case match_token(State1, '(') of
                true ->
                    {_, State2} = expect(State1, '('),
                    {InnerPattern, State3} = parse_pattern(State2),
                    {_, State4} = expect(State3, ')'),
                    Pattern = #constructor_pattern{
                        name = 'Some',
                        args = [InnerPattern],
                        location = Location
                    },
                    {Pattern, State4};
                false ->
                    Pattern = #constructor_pattern{
                        name = 'Some',
                        args = undefined,
                        location = Location
                    },
                    {Pattern, State1}
            end;
        'None' ->
            {Token, State1} = expect(State, 'None'),
            Location = get_token_location(Token),
            case match_token(State1, '(') of
                true ->
                    {_, State2} = expect(State1, '('),
                    {InnerPattern, State3} = parse_pattern(State2),
                    {_, State4} = expect(State3, ')'),
                    Pattern = #constructor_pattern{
                        name = 'None',
                        args = [InnerPattern],
                        location = Location
                    },
                    {Pattern, State4};
                false ->
                    Pattern = #constructor_pattern{
                        name = 'None',
                        args = undefined,
                        location = Location
                    },
                    {Pattern, State1}
            end;
        'ok' ->
            {Token, State1} = expect(State, 'ok'),
            Location = get_token_location(Token),
            case match_token(State1, '(') of
                true ->
                    {_, State2} = expect(State1, '('),
                    {InnerPattern, State3} = parse_pattern(State2),
                    {_, State4} = expect(State3, ')'),
                    Pattern = #constructor_pattern{
                        name = ok,
                        args = [InnerPattern],
                        location = Location
                    },
                    {Pattern, State4};
                false ->
                    Pattern = #constructor_pattern{
                        name = ok,
                        args = undefined,
                        location = Location
                    },
                    {Pattern, State1}
            end;
        'error' ->
            {Token, State1} = expect(State, 'error'),
            Location = get_token_location(Token),
            case match_token(State1, '(') of
                true ->
                    {_, State2} = expect(State1, '('),
                    {InnerPattern, State3} = parse_pattern(State2),
                    {_, State4} = expect(State3, ')'),
                    Pattern = #constructor_pattern{
                        name = error,
                        args = [InnerPattern],
                        location = Location
                    },
                    {Pattern, State4};
                false ->
                    Pattern = #constructor_pattern{
                        name = error,
                        args = undefined,
                        location = Location
                    },
                    {Pattern, State1}
            end;
        'Zero' ->
            {Token, State1} = expect(State, 'Zero'),
            Location = get_token_location(Token),
            % Zero is a nullary constructor - no arguments
            Pattern = #constructor_pattern{
                name = 'Zero',
                args = [],
                location = Location
            },
            {Pattern, State1};
        'Succ' ->
            {Token, State1} = expect(State, 'Succ'),
            Location = get_token_location(Token),
            case match_token(State1, '(') of
                true ->
                    {_, State2} = expect(State1, '('),
                    {InnerPattern, State3} = parse_pattern(State2),
                    {_, State4} = expect(State3, ')'),
                    Pattern = #constructor_pattern{
                        name = 'Succ',
                        args = [InnerPattern],
                        location = Location
                    },
                    {Pattern, State4};
                false ->
                    % Succ without arguments is malformed
                    throw({parse_error, {succ_requires_argument}, 0, 0})
            end;
        true ->
            {Token, State1} = expect(State, true),
            Location = get_token_location(Token),
            Pattern = #literal_pattern{
                value = true,
                location = Location
            },
            {Pattern, State1};
        false ->
            {Token, State1} = expect(State, false),
            Location = get_token_location(Token),
            Pattern = #literal_pattern{
                value = false,
                location = Location
            },
            {Pattern, State1};
        _ ->
            Token = current_token(State),
            throw({parse_error, {unexpected_token_in_pattern, get_token_type(Token)}, 0, 0})
    end.

%% Parse list pattern [head | tail] or [a, b, c]
parse_list_pattern(State) ->
    {_, State1} = expect(State, '['),
    Location = get_token_location(current_token(State)),

    case match_token(State1, ']') of
        true ->
            % Empty list []
            {_, State2} = expect(State1, ']'),
            Pattern = #list_pattern{
                elements = [],
                tail = undefined,
                location = Location
            },
            {Pattern, State2};
        false ->
            {FirstPattern, State2} = parse_pattern(State1),
            case match_token(State2, '|') of
                true ->
                    % [head | tail] pattern
                    {_, State3} = expect(State2, '|'),
                    {TailPattern, State4} = parse_pattern(State3),
                    {_, State5} = expect(State4, ']'),
                    Pattern = #list_pattern{
                        elements = [FirstPattern],
                        tail = TailPattern,
                        location = Location
                    },
                    {Pattern, State5};
                false ->
                    % [a, b, c] pattern - parse rest of elements
                    {RestElements, State3} = parse_pattern_list(State2, []),
                    {_, State4} = expect(State3, ']'),
                    Pattern = #list_pattern{
                        elements = [FirstPattern | RestElements],
                        tail = undefined,
                        location = Location
                    },
                    {Pattern, State4}
            end
    end.

%% Parse tuple pattern {a, b, c}
parse_tuple_pattern(State) ->
    {_, State1} = expect(State, '{'),
    Location = get_token_location(current_token(State)),

    case match_token(State1, '}') of
        true ->
            % Empty tuple {}
            {_, State2} = expect(State1, '}'),
            Pattern = #tuple_pattern{
                elements = [],
                location = Location
            },
            {Pattern, State2};
        false ->
            {FirstPattern, State2} = parse_pattern(State1),
            {RestPatterns, State3} = parse_tuple_pattern_list(State2, []),
            {_, State4} = expect(State3, '}'),
            Pattern = #tuple_pattern{
                elements = [FirstPattern | RestPatterns],
                location = Location
            },
            {Pattern, State4}
    end.

%% Parse comma-separated tuple pattern list
parse_tuple_pattern_list(State, Acc) ->
    case match_token(State, '}') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            case match_token(State, ',') of
                true ->
                    {_, State1} = expect(State, ','),
                    {Pattern, State2} = parse_pattern(State1),
                    parse_tuple_pattern_list(State2, [Pattern | Acc]);
                false ->
                    {lists:reverse(Acc), State}
            end
    end.

%% Parse comma-separated pattern list
parse_pattern_list(State, Acc) ->
    case match_token(State, ']') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            case match_token(State, ',') of
                true ->
                    {_, State1} = expect(State, ','),
                    {Pattern, State2} = parse_pattern(State1),
                    parse_pattern_list(State2, [Pattern | Acc]);
                false ->
                    {lists:reverse(Acc), State}
            end
    end.

%% Parse record pattern Person{name: name, age: age}
parse_record_pattern(State, RecordName, Location) ->
    % We already consumed the identifier, now expect '{'
    {_, State1} = expect(State, '{'),

    case match_token(State1, '}') of
        true ->
            % Empty record pattern Person{}
            {_, State2} = expect(State1, '}'),
            Pattern = #record_pattern{
                name = RecordName,
                fields = [],
                location = Location
            },
            {Pattern, State2};
        false ->
            % Record with field patterns
            {FieldPatterns, State2} = parse_record_field_patterns(State1, []),
            {_, State3} = expect(State2, '}'),
            Pattern = #record_pattern{
                name = RecordName,
                fields = FieldPatterns,
                location = Location
            },
            {Pattern, State3}
    end.

%% Parse record field patterns: name: pattern, age: pattern
parse_record_field_patterns(State, Acc) ->
    case match_token(State, '}') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            % Parse field name
            {NameToken, State1} = expect(State, identifier),
            FieldName = binary_to_atom(get_token_value(NameToken), utf8),
            FieldLocation = get_token_location(NameToken),

            % Expect colon
            {_, State2} = expect(State1, ':'),

            % Parse pattern
            {Pattern, State3} = parse_pattern(State2),

            % Create field pattern
            FieldPattern = #field_pattern{
                name = FieldName,
                pattern = Pattern,
                location = FieldLocation
            },

            % Check for comma (more fields) or end
            case match_token(State3, ',') of
                true ->
                    {_, State4} = expect(State3, ','),
                    parse_record_field_patterns(State4, [FieldPattern | Acc]);
                false ->
                    {lists:reverse([FieldPattern | Acc]), State3}
            end
    end.

%% Parse comma-separated pattern list for constructor arguments
parse_pattern_list_for_constructor(State, Acc) ->
    case match_token(State, ')') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {Pattern, State1} = parse_pattern(State),
            case match_token(State1, ',') of
                true ->
                    {_, State2} = expect(State1, ','),
                    parse_pattern_list_for_constructor(State2, [Pattern | Acc]);
                false ->
                    {lists:reverse([Pattern | Acc]), State1}
            end
    end.

%% Get pattern location
get_pattern_location(#identifier_pattern{location = Loc}) -> Loc;
get_pattern_location(#literal_pattern{location = Loc}) -> Loc;
get_pattern_location(#list_pattern{location = Loc}) -> Loc;
get_pattern_location(#tuple_pattern{location = Loc}) -> Loc;
get_pattern_location(#record_pattern{location = Loc}) -> Loc;
get_pattern_location(#wildcard_pattern{location = Loc}) -> Loc;
get_pattern_location(#constructor_pattern{location = Loc}) -> Loc;
get_pattern_location(_) -> #location{line = 0, column = 0, file = undefined}.

%% Get type location
get_type_location(#primitive_type{location = Loc}) -> Loc;
get_type_location(#dependent_type{location = Loc}) -> Loc;
get_type_location(#function_type{location = Loc}) -> Loc;
get_type_location(_) -> #location{line = 0, column = 0, file = undefined}.

%% Parse constructor expressions like Ok(value), Error("msg")
parse_constructor_expression(State) ->
    {Token, State1} =
        case get_token_type(current_token(State)) of
            'Ok' -> expect(State, 'Ok');
            'Error' -> expect(State, 'Error');
            'Some' -> expect(State, 'Some');
            'None' -> expect(State, 'None');
            'Zero' -> expect(State, 'Zero');
            'Succ' -> expect(State, 'Succ');
            'ok' -> expect(State, 'ok');
            'error' -> expect(State, 'error')
        end,

    Name =
        case get_token_type(Token) of
            'Ok' -> 'Ok';
            'Error' -> 'Error';
            'Some' -> 'Some';
            'None' -> 'None';
            'Zero' -> 'Zero';
            'Succ' -> 'Succ';
            'ok' -> ok;
            'error' -> error;
            _ -> get_token_value(Token)
        end,
    Location = get_token_location(Token),

    case match_token(State1, '(') of
        true ->
            % Constructor with argument: Ok(value)
            {_, State2} = expect(State1, '('),
            {Arg, State3} = parse_expression(State2),
            {_, State4} = expect(State3, ')'),

            % Represent as a function call
            ConstructorExpr = #identifier_expr{name = Name, location = Location},
            CallExpr = #function_call_expr{
                function = ConstructorExpr,
                args = [Arg],
                location = Location
            },
            {CallExpr, State4};
        false ->
            % Constructor without argument: None -> treat as None() function call
            ConstructorExpr = #identifier_expr{name = Name, location = Location},
            CallExpr = #function_call_expr{
                function = ConstructorExpr,
                args = [],
                location = Location
            },
            {CallExpr, State1}
    end.

%% Parse constructor expression from an atom token (for quoted atoms like 'Some')
parse_atom_constructor_expression(State, ConstructorName, Location) ->
    case match_token(State, '(') of
        true ->
            % Constructor with arguments: 'Some'(value) or 'None'()
            {_, State1} = expect(State, '('),
            {Args, State2} = parse_argument_list(State1, []),
            {_, State3} = expect(State2, ')'),

            % Represent as a function call
            ConstructorExpr = #identifier_expr{name = ConstructorName, location = Location},
            CallExpr = #function_call_expr{
                function = ConstructorExpr,
                args = Args,
                location = Location
            },
            {CallExpr, State3};
        false ->
            % Constructor without argument: 'None' -> treat as 'None'() function call
            ConstructorExpr = #identifier_expr{name = ConstructorName, location = Location},
            CallExpr = #function_call_expr{
                function = ConstructorExpr,
                args = [],
                location = Location
            },
            {CallExpr, State}
    end.

%% Parse function body (can be a sequence of statements)
parse_function_body(State) ->
    parse_statement_sequence(State, []).

%% Parse sequence of statements in function body
parse_statement_sequence(State, Acc) ->
    {Stmt, State1} = parse_expression(State),

    % Check for comma separator or end of body
    case match_token(State1, ',') of
        true ->
            % Comma-separated statement - consume comma and continue
            {_, State2} = expect(State1, ','),
            parse_statement_sequence(State2, [Stmt | Acc]);
        false ->
            % Check if this is the last statement or if there are more
            case is_end_of_body(State1) of
                true ->
                    % This is the last statement - return it or wrap in block
                    case Acc of
                        [] ->
                            {Stmt, State1};
                        _ ->
                            Location = get_expr_location(Stmt),
                            Block = #block_expr{
                                expressions = lists:reverse([Stmt | Acc]),
                                location = Location
                            },
                            {Block, State1}
                    end;
                false ->
                    % More statements follow (without comma)
                    parse_statement_sequence(State1, [Stmt | Acc])
            end
    end.

%% Check if we're at the end of a function body
is_end_of_body(State) ->
    CurrentToken = current_token(State),
    TokenType =
        case CurrentToken of
            eof -> eof;
            Token -> get_token_type(Token)
        end,
    case TokenType of
        eof -> true;
        'end' -> true;
        'else' -> true;
        'def' -> true;
        % Record definitions end function body
        'record' -> true;
        % Type definitions end function body
        'type' -> true;
        % FSM definitions end function body
        'fsm' -> true;
        % Import statements end function body
        'import' -> true;
        % Export statements end function body
        'export' -> true;
        _ -> false
    end.

%% ============================================================================
%% Action Expression Parsing
%% ============================================================================

%% Parse action expressions for FSM transitions
parse_action_expression(State) ->
    case get_token_type(current_token(State)) of
        '{' ->
            % Action sequence: do { action1; action2; ... }
            {_, State1} = expect(State, '{'),
            {Actions, State2} = parse_action_sequence(State1, []),
            {_, State3} = expect(State2, '}'),
            Location = get_token_location(current_token(State)),
            {{sequence, Actions, Location}, State3};
        identifier ->
            % Single action or assignment
            parse_single_action(State);
        'if' ->
            % Conditional action
            parse_conditional_action(State);
        'log' ->
            % Logging action
            parse_log_action(State);
        'emit' ->
            % Event emission action
            parse_emit_action(State);
        _ ->
            {error, {unexpected_token_in_action, get_token_type(current_token(State))}}
    end.

%% Parse a sequence of actions separated by semicolons
parse_action_sequence(State, Acc) ->
    case get_token_type(current_token(State)) of
        '}' ->
            {lists:reverse(Acc), State};
        _ ->
            {Action, State1} = parse_single_action(State),
            case match_token(State1, ';') of
                true ->
                    {_, State2} = expect(State1, ';'),
                    parse_action_sequence(State2, [Action | Acc]);
                false ->
                    {lists:reverse([Action | Acc]), State1}
            end
    end.

%% Parse a single action
parse_single_action(State) ->
    {NameToken, State1} = expect(State, identifier),
    Name = binary_to_atom(get_token_value(NameToken), utf8),
    Location = get_token_location(NameToken),

    case get_token_type(current_token(State1)) of
        '=' ->
            % Assignment: variable = value
            {_, State2} = expect(State1, '='),
            {Value, State3} = parse_action_value(State2),
            {{assign, Name, Value, Location}, State3};
        '+=' ->
            % Increment: variable += amount
            {_, State2} = expect(State1, '+='),
            {Amount, State3} = parse_action_value(State2),
            {{increment, Name, Amount, Location}, State3};
        '-=' ->
            % Decrement: variable -= amount
            {_, State2} = expect(State1, '-='),
            {Amount, State3} = parse_action_value(State2),
            {{decrement, Name, Amount, Location}, State3};
        '(' ->
            % Function call: function(args)
            {_, State2} = expect(State1, '('),
            {Args, State3} = parse_action_arguments(State2, []),
            {_, State4} = expect(State3, ')'),
            {{call, Name, Args, Location}, State4};
        _ ->
            % Just a variable reference or field access
            case match_token(State1, '.') of
                true ->
                    {_, State2} = expect(State1, '.'),
                    {FieldToken, State3} = expect(State2, identifier),
                    Field = binary_to_atom(get_token_value(FieldToken), utf8),

                    case match_token(State3, '=') of
                        true ->
                            {_, State4} = expect(State3, '='),
                            {Value, State5} = parse_action_value(State4),
                            {{update, Field, Value, Location}, State5};
                        false ->
                            {{state_field, Field, Location}, State3}
                    end;
                false ->
                    {{state_var, Name, Location}, State1}
            end
    end.

%% Parse conditional actions: if condition then action else action end
parse_conditional_action(State) ->
    {_, State1} = expect(State, 'if'),
    {Condition, State2} = parse_action_condition(State1),
    {_, State3} = expect(State2, 'then'),
    {ThenAction, State4} = parse_action_expression(State3),

    {ElseAction, State5} =
        case match_token(State4, 'else') of
            true ->
                {_, State4a} = expect(State4, 'else'),
                parse_action_expression(State4a);
            false ->
                {undefined, State4}
        end,

    {_, State6} = expect(State5, 'end'),
    Location = get_token_location(current_token(State)),
    {{if_then, Condition, ThenAction, ElseAction, Location}, State6}.

%% Parse log actions: log(level, message)
parse_log_action(State) ->
    {_, State1} = expect(State, 'log'),
    {_, State2} = expect(State1, '('),
    {LevelToken, State3} = expect(State2, identifier),
    Level = binary_to_atom(get_token_value(LevelToken), utf8),
    {_, State4} = expect(State3, ','),
    {Message, State5} = parse_action_value(State4),
    {_, State6} = expect(State5, ')'),
    Location = get_token_location(current_token(State)),
    {{log, Level, Message, Location}, State6}.

%% Parse emit actions: emit(event) or emit(event, data)
parse_emit_action(State) ->
    {_, State1} = expect(State, 'emit'),
    {_, State2} = expect(State1, '('),
    {Event, State3} = parse_action_value(State2),

    {Data, State4} =
        case match_token(State3, ',') of
            true ->
                {_, State3a} = expect(State3, ','),
                parse_action_value(State3a);
            false ->
                {undefined, State3}
        end,

    {_, State5} = expect(State4, ')'),
    Location = get_token_location(current_token(State)),
    {{emit, Event, Data, Location}, State5}.

%% Parse action conditions (similar to expressions)
parse_action_condition(State) ->
    parse_expression(State).

%% Parse action values (expressions that produce values)
parse_action_value(State) ->
    case get_token_type(current_token(State)) of
        number ->
            {Token, State1} = expect(State, number),
            Value = get_token_value(Token),
            Location = get_token_location(Token),
            {{literal, Value, Location}, State1};
        string ->
            {Token, State1} = expect(State, string),
            Value = get_token_value(Token),
            Location = get_token_location(Token),
            {{literal, Value, Location}, State1};
        atom ->
            {Token, State1} = expect(State, atom),
            Value = get_token_value(Token),
            Location = get_token_location(Token),
            {{literal, Value, Location}, State1};
        identifier ->
            {NameToken, State1} = expect(State, identifier),
            Name = binary_to_atom(get_token_value(NameToken), utf8),
            Location = get_token_location(NameToken),

            case Name of
                event_data ->
                    {{event_data, Location}, State1};
                current_state ->
                    {{current_state, Location}, State1};
                _ ->
                    case match_token(State1, '.') of
                        true ->
                            {_, State2} = expect(State1, '.'),
                            {FieldToken, State3} = expect(State2, identifier),
                            Field = binary_to_atom(get_token_value(FieldToken), utf8),
                            {{state_field, Field, Location}, State3};
                        false ->
                            case match_token(State1, '(') of
                                true ->
                                    % Function call
                                    {_, State2} = expect(State1, '('),
                                    {Args, State3} = parse_action_arguments(State2, []),
                                    {_, State4} = expect(State3, ')'),
                                    {{function_call, Name, Args, Location}, State4};
                                false ->
                                    {{state_var, Name, Location}, State1}
                            end
                    end
            end;
        '(' ->
            % Parenthesized expression or binary operation
            {_, State1} = expect(State, '('),
            {Value, State2} = parse_action_binary_expr(State1),
            {_, State3} = expect(State2, ')'),
            {Value, State3};
        _ ->
            {error, {unexpected_token_in_action_value, get_token_type(current_token(State))}}
    end.

%% Parse binary expressions in actions
parse_action_binary_expr(State) ->
    {Left, State1} = parse_action_value(State),
    case get_token_type(current_token(State1)) of
        '+' ->
            {_, State2} = expect(State1, '+'),
            {Right, State3} = parse_action_value(State2),
            Location = get_token_location(current_token(State)),
            {{binary_op, '+', Left, Right, Location}, State3};
        '-' ->
            {_, State2} = expect(State1, '-'),
            {Right, State3} = parse_action_value(State2),
            Location = get_token_location(current_token(State)),
            {{binary_op, '-', Left, Right, Location}, State3};
        '*' ->
            {_, State2} = expect(State1, '*'),
            {Right, State3} = parse_action_value(State2),
            Location = get_token_location(current_token(State)),
            {{binary_op, '*', Left, Right, Location}, State3};
        '/' ->
            {_, State2} = expect(State1, '/'),
            {Right, State3} = parse_action_value(State2),
            Location = get_token_location(current_token(State)),
            {{binary_op, '/', Left, Right, Location}, State3};
        _ ->
            {Left, State1}
    end.

%% Parse action function arguments
parse_action_arguments(State, Acc) ->
    case get_token_type(current_token(State)) of
        ')' ->
            {lists:reverse(Acc), State};
        _ ->
            {Arg, State1} = parse_action_value(State),
            case match_token(State1, ',') of
                true ->
                    {_, State2} = expect(State1, ','),
                    parse_action_arguments(State2, [Arg | Acc]);
                false ->
                    {lists:reverse([Arg | Acc]), State1}
            end
    end.

%% Parse string interpolation
parse_string_interpolation(State) ->
    parse_string_interpolation_parts(State, []).

parse_string_interpolation_parts(State, Acc) ->
    Token = current_token(State),
    case get_token_type(Token) of
        string_part ->
            % String part
            {Token, State1} = expect(State, string_part),
            Value = get_token_value(Token),
            Part = {string_part, Value},
            parse_string_interpolation_parts(State1, [Part | Acc]);
        interpolation_start ->
            % Start of interpolation - skip the start token and parse expression
            {_, State1} = expect(State, interpolation_start),
            {Expr, State2} = parse_interpolation_expression(State1),
            Part = {expr, Expr},
            parse_string_interpolation_parts(State2, [Part | Acc]);
        interpolation_mid ->
            % Middle of interpolation - skip the mid token and parse expression
            {_, State1} = expect(State, interpolation_mid),
            {Expr, State2} = parse_interpolation_expression(State1),
            Part = {expr, Expr},
            parse_string_interpolation_parts(State2, [Part | Acc]);
        interpolation_end ->
            % End of interpolation
            {Token, State1} = expect(State, interpolation_end),
            Location = get_token_location(Token),
            Expr = #string_interpolation_expr{
                parts = lists:reverse(Acc),
                location = Location
            },
            {Expr, State1};
        _ ->
            throw({parse_error, {unexpected_token_in_interpolation, get_token_type(Token)}, 0, 0})
    end.

%% Parse expression inside interpolation
parse_interpolation_expression(State) ->
    parse_binary_expression(State, 0).

%% Parse record expression fields (name: value pairs for record construction)
parse_record_expr_fields(State, Acc) ->
    case match_token(State, '}') of
        true ->
            {lists:reverse(Acc), State};
        false ->
            {FieldName, State1} = expect(State, identifier),
            Name = binary_to_atom(get_token_value(FieldName), utf8),
            Location = get_token_location(FieldName),

            % Expect colon
            {_, State2} = expect(State1, ':'),

            % Parse field value
            {Value, State3} = parse_expression(State2),

            % Create field expression
            Field = #field_expr{
                name = Name,
                value = Value,
                location = Location
            },

            % Check if there are more fields
            case match_token(State3, ',') of
                true ->
                    {_, State4} = expect(State3, ','),
                    parse_record_expr_fields(State4, [Field | Acc]);
                false ->
                    {lists:reverse([Field | Acc]), State3}
            end
    end.

%% Check if current token is an identifier
is_identifier_token(Token) ->
    case Token of
        eof -> false;
        _ -> get_token_type(Token) =:= identifier
    end.

%% Check if there's an operator token after the current identifier
match_operator_ahead(State) ->
    % Look at the next token after the current identifier
    case State#parser_state.tokens of
        [NextToken | _] ->
            NextTokenType = get_token_type(NextToken),
            case get_operator_info(NextTokenType) of
                undefined -> false;
                _ -> true
            end;
        [] ->
            false
    end.

%% Group multiple function definitions with the same name/arity into multi-clause functions
%% This enables Erlang-style multi-clause function definitions
group_function_clauses(Items) ->
    group_function_clauses_helper(Items, #{}, []).

group_function_clauses_helper([], _FuncMap, Acc) ->
    lists:reverse(Acc);
group_function_clauses_helper([Item | Rest], FuncMap, Acc) ->
    case Item of
        #function_def{name = Name, clauses = [Clause]} ->
            % Get arity from the clause
            Arity = length(Clause#function_clause.params),
            Key = {Name, Arity},

            case maps:get(Key, FuncMap, undefined) of
                undefined ->
                    % First occurrence - add to map with a placeholder in Acc
                    NewFuncMap = maps:put(Key, {Item, length(Acc)}, FuncMap),
                    group_function_clauses_helper(Rest, NewFuncMap, [Item | Acc]);
                {ExistingFunc, Position} ->
                    % Merge clauses into existing function
                    #function_def{clauses = ExistingClauses} = ExistingFunc,
                    MergedFunc = ExistingFunc#function_def{
                        clauses = ExistingClauses ++ [Clause],
                        % Clear deprecated fields for multi-clause functions
                        params = undefined,
                        body = undefined,
                        constraint = undefined
                    },
                    % Update the function in both map and accumulator
                    NewFuncMap = maps:put(Key, {MergedFunc, Position}, FuncMap),
                    NewAcc = update_list_at_position(Acc, Position, MergedFunc),
                    group_function_clauses_helper(Rest, NewFuncMap, NewAcc)
            end;
        _ ->
            % Not a function definition, keep as-is
            group_function_clauses_helper(Rest, FuncMap, [Item | Acc])
    end.

%% Helper to update a list element at a specific position (counting from the end)
update_list_at_position(List, Position, NewValue) ->
    Reversed = lists:reverse(List),
    Updated = update_at_index(Reversed, Position, NewValue),
    lists:reverse(Updated).

update_at_index([_ | Rest], 0, NewValue) ->
    [NewValue | Rest];
update_at_index([H | Rest], Index, NewValue) when Index > 0 ->
    [H | update_at_index(Rest, Index - 1, NewValue)];
update_at_index([], _, _) ->
    [].
