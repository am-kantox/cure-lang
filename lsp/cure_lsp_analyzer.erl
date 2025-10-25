-module(cure_lsp_analyzer).
-export([analyze/1, analyze_document/1, extract_symbols/1]).
-export([get_definition/3, get_references/3, get_hover_info/3]).

-include("../src/parser/cure_ast.hrl").

%% Analyze document and return diagnostics
analyze(Text) when is_binary(Text) ->
    case cure_lexer:tokenize(Text) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, AST} ->
                    % Type check if possible
                    type_check_diagnostics(AST);
                {error, {Line, Column, Message}} ->
                    [make_diagnostic(Line, Column, Message, error)];
                {error, {parse_error, Reason, Line, Column}} ->
                    [make_diagnostic(Line, Column, Reason, error)];
                {error, Reason} ->
                    % Generic parse error
                    [make_diagnostic(0, 0, Reason, error)]
            end;
        {error, {Line, Column, Message}} ->
            [make_diagnostic(Line, Column, Message, error)];
        {error, Reason} ->
            % Generic lex error
            [make_diagnostic(0, 0, Reason, error)]
    end;
analyze(Text) when is_list(Text) ->
    analyze(list_to_binary(Text)).

%% Analyze document and return full analysis result
analyze_document(Text) when is_binary(Text) ->
    LexResult = cure_lexer:tokenize(Text),
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
    };
analyze_document(Text) when is_list(Text) ->
    analyze_document(list_to_binary(Text)).

%% Extract symbols from parsed AST
extract_symbols(Text) when is_binary(Text) ->
    case cure_lexer:tokenize(Text) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, AST} ->
                    extract_symbols_from_ast(AST);
                _ ->
                    []
            end;
        _ ->
            []
    end;
extract_symbols(Text) when is_list(Text) ->
    extract_symbols(list_to_binary(Text)).

extract_symbols_from_parse({ok, AST}) ->
    extract_symbols_from_ast(AST);
extract_symbols_from_parse(_) ->
    [].

%% Handle list of modules (parser returns a list)
extract_symbols_from_ast([ModuleDef | _Rest]) when is_record(ModuleDef, module_def) ->
    extract_symbols_from_module(ModuleDef);
extract_symbols_from_ast(ModuleDef) when is_record(ModuleDef, module_def) ->
    extract_symbols_from_module(ModuleDef);
extract_symbols_from_ast(_) ->
    [].

extract_symbols_from_module(#module_def{name = ModName, items = Items}) ->
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
    ] ++ FunctionSymbols ++ FSMSymbols.

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

%% Handle list of modules or single module
find_definition_in_ast([ModuleDef | _], Line, Character) when is_record(ModuleDef, module_def) ->
    find_definition_in_module(ModuleDef, Line, Character);
find_definition_in_ast(ModuleDef, Line, Character) when is_record(ModuleDef, module_def) ->
    find_definition_in_module(ModuleDef, Line, Character);
find_definition_in_ast(_, _, _) ->
    null.

find_definition_in_module(#module_def{name = _ModName, items = Items} = AST, Line, Character) ->
    % First, find what symbol the cursor is on
    case find_symbol_at_position(AST, Line, Character) of
        {ok, SymbolName, SymbolType} ->
            % Now find the definition of that symbol
            find_symbol_definition(Items, SymbolName, SymbolType);
        _ ->
            null
    end.

%% Find what symbol is at the given position
find_symbol_at_position(#module_def{items = Items}, Line, Character) ->
    % Walk through items and find if cursor is on any identifier
    % We need to pass the full list to determine function boundaries
    find_symbol_in_items_with_bounds(Items, Line, Character).

find_symbol_in_items_with_bounds(Items, Line, Character) ->
    find_symbol_in_items_with_bounds(Items, Line, Character, undefined).

find_symbol_in_items_with_bounds([], _Line, _Character, _PrevEnd) ->
    {error, not_found};
find_symbol_in_items_with_bounds([Item | Rest], Line, Character, _PrevEnd) ->
    % Get next item's start line to determine current item's end
    NextStartLine =
        case Rest of
            [NextItem | _] -> get_item_start_line(NextItem);
            % Last item, no next item
            [] -> undefined
        end,
    case find_symbol_in_item_with_end(Item, Line, Character, NextStartLine) of
        {ok, _, _} = Result -> Result;
        _ -> find_symbol_in_items_with_bounds(Rest, Line, Character, get_item_end_line(Item))
    end.

%% Get the starting line of an item
get_item_start_line(#function_def{location = #location{line = L}}) -> L;
get_item_start_line(#fsm_def{location = #location{line = L}}) -> L;
get_item_start_line(_) -> undefined.

get_item_end_line(#function_def{location = #location{line = L}}) -> L;
get_item_end_line(#fsm_def{location = #location{line = L}}) -> L;
get_item_end_line(_) -> undefined.

%% Check if cursor is within an item's bounds
%% NextStartLine is the line where the next item starts (or undefined for last item)
find_symbol_in_item_with_end(
    #function_def{name = Name, location = Location}, Line, _Character, NextStartLine
) ->
    case Location of
        #location{line = FuncLine} ->
            % LSP line numbers are 0-indexed
            CursorLine = Line + 1,
            % Function ends at the line before the next function/fsm/end
            FuncEndLine =
                case NextStartLine of
                    % Last item in module
                    undefined -> FuncLine + 1000;
                    NextLine -> NextLine - 1
                end,
            if
                CursorLine >= FuncLine andalso CursorLine =< FuncEndLine ->
                    {ok, Name, function};
                true ->
                    {error, not_found}
            end;
        _ ->
            {error, not_found}
    end;
find_symbol_in_item_with_end(
    #fsm_def{name = Name, location = Location}, Line, _Character, NextStartLine
) ->
    case Location of
        #location{line = FsmLine} ->
            CursorLine = Line + 1,
            FsmEndLine =
                case NextStartLine of
                    undefined -> FsmLine + 1000;
                    NextLine -> NextLine - 1
                end,
            if
                CursorLine >= FsmLine andalso CursorLine =< FsmEndLine ->
                    {ok, Name, fsm};
                true ->
                    {error, not_found}
            end;
        _ ->
            {error, not_found}
    end;
find_symbol_in_item_with_end(_, _, _, _) ->
    {error, not_found}.

%% Find the definition location for a symbol
find_symbol_definition(Items, SymbolName, function) ->
    case
        lists:search(
            fun
                (#function_def{name = N}) when N =:= SymbolName -> true;
                (_) -> false
            end,
            Items
        )
    of
        {value, #function_def{location = #location{line = L}}} ->
            #{
                range => #{
                    start => #{line => max(0, L - 1), character => 0},
                    'end' => #{line => max(0, L - 1), character => 100}
                }
            };
        _ ->
            null
    end;
find_symbol_definition(Items, SymbolName, fsm) ->
    case
        lists:search(
            fun
                (#fsm_def{name = N}) when N =:= SymbolName -> true;
                (_) -> false
            end,
            Items
        )
    of
        {value, #fsm_def{location = #location{line = L}}} ->
            #{
                range => #{
                    start => #{line => max(0, L - 1), character => 0},
                    'end' => #{line => max(0, L - 1), character => 100}
                }
            };
        _ ->
            null
    end;
find_symbol_definition(_, _, _) ->
    null.

%% Get references for symbol at position
get_references(Text, Line, Character) ->
    case analyze_document(Text) of
        #{parse_result := {ok, AST}} ->
            find_references_in_ast(AST, Line, Character);
        _ ->
            []
    end.

%% Handle list of modules or single module
find_references_in_ast([ModuleDef | _], Line, Character) when is_record(ModuleDef, module_def) ->
    find_references_in_module(ModuleDef, Line, Character);
find_references_in_ast(ModuleDef, Line, Character) when is_record(ModuleDef, module_def) ->
    find_references_in_module(ModuleDef, Line, Character);
find_references_in_ast(_, _, _) ->
    [].

find_references_in_module(#module_def{items = Items} = AST, Line, Character) ->
    % First, find what symbol the cursor is on
    case find_symbol_at_position(AST, Line, Character) of
        {ok, SymbolName, _SymbolType} ->
            % Now find all references to that symbol
            find_all_references(Items, SymbolName);
        _ ->
            []
    end.

%% Find all references to a symbol in the AST
find_all_references(Items, SymbolName) ->
    lists:flatmap(fun(Item) -> find_references_in_item(Item, SymbolName) end, Items).

find_references_in_item(#function_def{name = Name, body = Body, location = Location}, SymbolName) ->
    Refs =
        case Name of
            SymbolName ->
                [make_location_ref(Location)];
            _ ->
                []
        end,
    Refs ++ find_references_in_expr(Body, SymbolName);
find_references_in_item(#fsm_def{name = Name, location = Location}, SymbolName) ->
    case Name of
        SymbolName -> [make_location_ref(Location)];
        _ -> []
    end;
find_references_in_item(_, _) ->
    [].

find_references_in_expr(#identifier_expr{name = Name, location = Location}, SymbolName) ->
    case Name of
        SymbolName -> [make_location_ref(Location)];
        _ -> []
    end;
find_references_in_expr(#function_call_expr{function = Func, args = Args}, SymbolName) ->
    find_references_in_expr(Func, SymbolName) ++
        lists:flatmap(fun(Arg) -> find_references_in_expr(Arg, SymbolName) end, Args);
find_references_in_expr(#binary_op_expr{left = Left, right = Right}, SymbolName) ->
    find_references_in_expr(Left, SymbolName) ++ find_references_in_expr(Right, SymbolName);
find_references_in_expr(#let_expr{bindings = Bindings, body = Body}, SymbolName) ->
    BindingRefs = lists:flatmap(
        fun(#binding{value = Val}) ->
            find_references_in_expr(Val, SymbolName)
        end,
        Bindings
    ),
    BindingRefs ++ find_references_in_expr(Body, SymbolName);
find_references_in_expr(#block_expr{expressions = Exprs}, SymbolName) ->
    lists:flatmap(fun(Expr) -> find_references_in_expr(Expr, SymbolName) end, Exprs);
find_references_in_expr(#match_expr{expr = Expr, patterns = Patterns}, SymbolName) ->
    ExprRefs = find_references_in_expr(Expr, SymbolName),
    PatternRefs = lists:flatmap(
        fun(#match_clause{body = Body}) ->
            find_references_in_expr(Body, SymbolName)
        end,
        Patterns
    ),
    ExprRefs ++ PatternRefs;
find_references_in_expr(_, _) ->
    [].

make_location_ref(#location{line = Line}) ->
    #{
        range => #{
            start => #{line => max(0, Line - 1), character => 0},
            'end' => #{line => max(0, Line - 1), character => 100}
        }
    };
make_location_ref(_) ->
    #{
        range => #{
            start => #{line => 0, character => 0},
            'end' => #{line => 0, character => 0}
        }
    }.

%% Get hover information for symbol at position
get_hover_info(Text, Line, Character) ->
    case analyze_document(Text) of
        #{parse_result := {ok, AST}} ->
            get_hover_from_ast(AST, Line, Character);
        _ ->
            null
    end.

%% Handle list of modules or single module
get_hover_from_ast([ModuleDef | _], Line, Character) when is_record(ModuleDef, module_def) ->
    get_hover_from_module(ModuleDef, Line, Character);
get_hover_from_ast(ModuleDef, Line, Character) when is_record(ModuleDef, module_def) ->
    get_hover_from_module(ModuleDef, Line, Character);
get_hover_from_ast(_, _, _) ->
    null.

get_hover_from_module(#module_def{items = Items} = AST, Line, Character) ->
    % Find what symbol the cursor is on
    case find_symbol_at_position(AST, Line, Character) of
        {ok, SymbolName, SymbolType} ->
            % Get hover information for that symbol
            get_symbol_hover_info(Items, SymbolName, SymbolType);
        _ ->
            null
    end.

%% Get hover information for a specific symbol
get_symbol_hover_info(Items, SymbolName, function) ->
    case
        lists:search(
            fun
                (#function_def{name = N}) when N =:= SymbolName -> true;
                (_) -> false
            end,
            Items
        )
    of
        {value, #function_def{name = Name, params = Params, return_type = RetType}} ->
            ParamStr = format_params(Params),
            ReturnStr = format_type(RetType),
            Content = iolist_to_binary([
                <<"```cure\n">>,
                <<"def ">>,
                atom_to_binary(Name, utf8),
                <<"(">>,
                ParamStr,
                <<")">>,
                case ReturnStr of
                    <<>> -> <<>>;
                    _ -> [<<" -> ">>, ReturnStr]
                end,
                <<"\n```">>
            ]),
            #{
                contents => #{
                    kind => <<"markdown">>,
                    value => Content
                }
            };
        _ ->
            null
    end;
get_symbol_hover_info(Items, SymbolName, fsm) ->
    case
        lists:search(
            fun
                (#fsm_def{name = N}) when N =:= SymbolName -> true;
                (_) -> false
            end,
            Items
        )
    of
        {value, #fsm_def{name = Name, states = States}} ->
            StateNames = [atom_to_binary(S, utf8) || S <- States],
            StatesStr = iolist_to_binary(lists:join(<<", ">>, StateNames)),
            Content = iolist_to_binary([
                <<"```cure\n">>,
                <<"fsm ">>,
                atom_to_binary(Name, utf8),
                <<"\n">>,
                <<"states: ">>,
                StatesStr,
                <<"\n```">>
            ]),
            #{
                contents => #{
                    kind => <<"markdown">>,
                    value => Content
                }
            };
        _ ->
            null
    end;
get_symbol_hover_info(_, _, _) ->
    null.

%% Format function parameters for display
format_params(Params) when is_list(Params) ->
    ParamStrs = lists:map(fun format_param/1, Params),
    iolist_to_binary(lists:join(<<", ">>, ParamStrs));
format_params(_) ->
    <<>>.

format_param(#param{name = Name, type = Type}) ->
    TypeStr = format_type(Type),
    case TypeStr of
        <<>> -> atom_to_binary(Name, utf8);
        _ -> iolist_to_binary([atom_to_binary(Name, utf8), <<": ">>, TypeStr])
    end;
format_param(Name) when is_atom(Name) ->
    atom_to_binary(Name, utf8);
format_param(_) ->
    <<"_">>.

%% Format type expressions for display
format_type(#primitive_type{name = Name}) ->
    atom_to_binary(Name, utf8);
format_type(#function_type{params = Params, return_type = RetType}) ->
    ParamStr = format_type_list(Params),
    RetStr = format_type(RetType),
    iolist_to_binary([<<"(">>, ParamStr, <<") -> ">>, RetStr]);
format_type(#list_type{element_type = ElemType}) ->
    iolist_to_binary([<<"[">>, format_type(ElemType), <<"]">>]);
format_type(#tuple_type{element_types = ElemTypes}) ->
    TypesStr = format_type_list(ElemTypes),
    iolist_to_binary([<<"(">>, TypesStr, <<")">>]);
format_type(undefined) ->
    <<>>;
format_type(_) ->
    <<"_">>.

format_type_list(Types) when is_list(Types) ->
    TypeStrs = lists:map(fun format_type/1, Types),
    iolist_to_binary(lists:join(<<", ">>, TypeStrs));
format_type_list(_) ->
    <<>>.

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
