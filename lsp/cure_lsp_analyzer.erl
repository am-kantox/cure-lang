-module(cure_lsp_analyzer).
-export([analyze/1, analyze_document/1, extract_symbols/1]).
-export([get_definition/3, get_references/3, get_hover_info/3]).

-include("../src/parser/cure_ast.hrl").

%% Analyze document and return diagnostics
analyze(Text) ->
    case cure_lexer:tokenize(binary_to_list(Text)) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, AST} ->
                    % Type check if possible
                    type_check_diagnostics(AST);
                {error, {Line, Column, Message}} ->
                    [make_diagnostic(Line, Column, Message, error)]
            end;
        {error, {Line, Column, Message}} ->
            [make_diagnostic(Line, Column, Message, error)]
    end.

%% Analyze document and return full analysis result
analyze_document(Text) ->
    LexResult = cure_lexer:tokenize(binary_to_list(Text)),
    ParseResult =
        case LexResult of
            {ok, Tokens} -> cure_parser:parse(Tokens);
            _ -> {error, lexer_failed}
        end,

    #{
        lex_result => LexResult,
        parse_result => ParseResult,
        symbols => extract_symbols_from_parse(ParseResult),
        diagnostics => analyze(Text)
    }.

%% Extract symbols from parsed AST
extract_symbols(Text) ->
    case cure_lexer:tokenize(binary_to_list(Text)) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, AST} ->
                    extract_symbols_from_ast(AST);
                _ ->
                    []
            end;
        _ ->
            []
    end.

extract_symbols_from_parse({ok, AST}) ->
    extract_symbols_from_ast(AST);
extract_symbols_from_parse(_) ->
    [].

extract_symbols_from_ast(#module_def{name = ModName, items = Items}) ->
    Functions = [F || F <- Items, is_record(F, function_def)],
    FSMs = [F || F <- Items, is_record(F, fsm_def)],
    FunctionSymbols = lists:map(fun extract_function_symbol/1, Functions),
    FSMSymbols = lists:map(fun extract_fsm_symbol/1, FSMs),

    [
        #{
            name => atom_to_binary(ModName, utf8),
            % Module
            kind => 2,
            range => #{
                start => #{line => 0, character => 0}, 'end' => #{line => 999, character => 0}
            },
            selectionRange => #{
                start => #{line => 0, character => 0}, 'end' => #{line => 0, character => 10}
            }
        }
    ] ++ FunctionSymbols ++ FSMSymbols;
extract_symbols_from_ast(_) ->
    [].

extract_function_symbol(#function_def{name = Name, params = Params, location = Location}) ->
    Arity = length(Params),
    Line =
        case Location of
            #location{line = L} -> L;
            _ -> 0
        end,
    #{
        name => iolist_to_binary(io_lib:format("~s/~p", [Name, Arity])),
        % Function
        kind => 12,
        range => #{
            start => #{line => max(0, Line - 1), character => 0},
            'end' => #{line => Line + 5, character => 0}
        },
        selectionRange => #{
            start => #{line => max(0, Line - 1), character => 0},
            'end' => #{line => max(0, Line - 1), character => 20}
        }
    }.

extract_fsm_symbol(#fsm_def{name = Name, location = Location}) ->
    Line =
        case Location of
            #location{line = L} -> L;
            _ -> 0
        end,
    #{
        name => atom_to_binary(Name, utf8),
        % Class (closest to FSM)
        kind => 5,
        range => #{
            start => #{line => max(0, Line - 1), character => 0},
            'end' => #{line => Line + 10, character => 0}
        },
        selectionRange => #{
            start => #{line => max(0, Line - 1), character => 0},
            'end' => #{line => max(0, Line - 1), character => 20}
        }
    }.

%% Get definition location for symbol at position
get_definition(Text, Line, Character) ->
    % Parse and find symbol at position
    case analyze_document(Text) of
        #{parse_result := {ok, AST}} ->
            find_definition_in_ast(AST, Line, Character);
        _ ->
            null
    end.

find_definition_in_ast(_AST, _Line, _Character) ->
    % Placeholder - would need to walk AST to find symbol definition
    null.

%% Get references for symbol at position
get_references(Text, Line, Character) ->
    case analyze_document(Text) of
        #{parse_result := {ok, AST}} ->
            find_references_in_ast(AST, Line, Character);
        _ ->
            []
    end.

find_references_in_ast(_AST, _Line, _Character) ->
    % Placeholder - would need to walk AST to find all references
    [].

%% Get hover information for symbol at position
get_hover_info(Text, Line, Character) ->
    case analyze_document(Text) of
        #{parse_result := {ok, AST}} ->
            get_hover_from_ast(AST, Line, Character);
        _ ->
            null
    end.

get_hover_from_ast(_AST, _Line, _Character) ->
    % Placeholder - would extract type information and documentation
    null.

%% Type checking diagnostics
type_check_diagnostics(AST) ->
    % Placeholder for type checking integration
    % Would call cure_typechecker:check(AST) and convert errors to diagnostics
    case catch cure_typechecker:check(AST) of
        {ok, _TypedAST} ->
            [];
        {error, TypeErrors} when is_list(TypeErrors) ->
            lists:map(fun convert_type_error/1, TypeErrors);
        {'EXIT', _Reason} ->
            % Type checker not available or crashed
            [];
        _ ->
            []
    end.

convert_type_error({Line, Column, Message}) ->
    make_diagnostic(Line, Column, format_message(Message), warning);
convert_type_error({Line, Message}) ->
    make_diagnostic(Line, 0, format_message(Message), warning);
convert_type_error(Error) ->
    make_diagnostic(0, 0, format_message(Error), warning).

%% Helper functions
make_diagnostic(Line, Column, Message, Severity) ->
    #{
        range => #{
            start => #{line => max(0, Line - 1), character => Column},
            'end' => #{line => max(0, Line - 1), character => Column + 10}
        },
        severity => severity_to_int(Severity),
        source => <<"cure-lsp">>,
        message => format_message(Message)
    }.

severity_to_int(error) -> 1;
severity_to_int(warning) -> 2;
severity_to_int(info) -> 3;
severity_to_int(hint) -> 4.

format_message(Msg) when is_binary(Msg) ->
    Msg;
format_message(Msg) when is_list(Msg) ->
    list_to_binary(Msg);
format_message(Msg) when is_atom(Msg) ->
    atom_to_binary(Msg, utf8);
format_message(Msg) ->
    iolist_to_binary(io_lib:format("~p", [Msg])).
