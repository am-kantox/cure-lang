-module(cure_lsp_analyzer).
-export([analyze/1, analyze_document/1, extract_symbols/1]).
-export([get_definition/3, get_references/3, get_hover_info/3]).

-include("../src/parser/cure_ast.hrl").

%% Type checker error and warning records
-record(typecheck_result, {
    success :: boolean(),
    type :: term() | undefined,
    errors :: [typecheck_error()],
    warnings :: [typecheck_warning()]
}).
-record(typecheck_error, {message :: string(), location :: location(), details :: term()}).
-record(typecheck_warning, {message :: string(), location :: location(), details :: term()}).

-type typecheck_error() :: #typecheck_error{}.
-type typecheck_warning() :: #typecheck_warning{}.

%% Analyze document and return diagnostics
analyze(Text) when is_binary(Text) ->
    case cure_lexer:tokenize(Text) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, AST} ->
                    % Type check if possible
                    type_check_diagnostics(AST);
                {error, {Line, Column, Message}} when is_integer(Line), is_integer(Column) ->
                    [make_diagnostic(Line, Column, Message, error)];
                {error, {parse_error, Reason, Line, Column}} when is_integer(Line), is_integer(Column) ->
                    [make_diagnostic(Line, Column, Reason, error)];
                {error, {parse_error, Reason, {Line, Column}}} when is_integer(Line), is_integer(Column) ->
                    [make_diagnostic(Line, Column, Reason, error)];
                {error, {Reason, Line, Column}} when is_integer(Line), is_integer(Column) ->
                    % Parser error with location
                    [make_diagnostic(Line, Column, Reason, error)];
                {error, Reason} ->
                    % Generic parse error without location - log for debugging
                    io:format("[LSP] Parser error without location: ~p~n", [Reason]),
                    [make_diagnostic(1, 1, Reason, error)]
            end;
        {error, {Reason, Line, Column}} when is_integer(Line), is_integer(Column) ->
            % Lexer error with location: {Reason, Line, Column}
            [make_diagnostic(Line, Column, Reason, error)];
        {error, {Line, Column, Message}} when is_integer(Line), is_integer(Column) ->
            % Alternative format: {Line, Column, Message}
            [make_diagnostic(Line, Column, Message, error)];
        {error, {{Reason, Detail}, Line, Column}} when is_integer(Line), is_integer(Column) ->
            % Lexer error with nested reason: {{Reason, Detail}, Line, Column}
            [make_diagnostic(Line, Column, {Reason, Detail}, error)];
        {error, Reason} ->
            % Generic lex error without location - log for debugging
            io:format("[LSP] Lexer error without location: ~p~n", [Reason]),
            [make_diagnostic(1, 1, Reason, error)]
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
    Records = [R || R <- Items, is_record(R, record_def)],
    Types = [T || T <- Items, is_record(T, type_def)],
    Traits = [T || T <- Items, is_record(T, trait_def)],
    TraitImpls = [I || I <- Items, is_record(I, trait_impl)],
    Typeclasses = [TC || TC <- Items, is_record(TC, typeclass_def)],
    Instances = [Inst || Inst <- Items, is_record(Inst, instance_def)],

    FunctionSymbols = lists:map(fun extract_function_symbol/1, Functions),
    FSMSymbols = lists:map(fun extract_fsm_symbol/1, FSMs),
    RecordSymbols = lists:map(fun extract_record_symbol/1, Records),
    TypeSymbols = lists:map(fun extract_type_symbol/1, Types),
    TraitSymbols = lists:map(fun extract_trait_symbol/1, Traits),
    TraitImplSymbols = lists:map(fun extract_trait_impl_symbol/1, TraitImpls),
    TypeclassSymbols = lists:map(fun extract_typeclass_symbol/1, Typeclasses),
    InstanceSymbols = lists:map(fun extract_instance_symbol/1, Instances),

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
    ] ++ FunctionSymbols ++ FSMSymbols ++ RecordSymbols ++ TypeSymbols ++
        TraitSymbols ++ TraitImplSymbols ++ TypeclassSymbols ++ InstanceSymbols.

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

%% Extract symbol for record definition
extract_record_symbol(#record_def{name = Name, location = Location}) ->
    Line =
        case Location of
            #location{line = L} -> L;
            _ -> 0
        end,
    #{
        name => atom_to_binary(Name, utf8),
        % Struct (LSP kind 23)
        kind => 23,
        range => #{
            start => #{line => max(0, Line - 1), character => 0},
            'end' => #{line => Line + 5, character => 0}
        },
        selectionRange => #{
            start => #{line => max(0, Line - 1), character => 0},
            'end' => #{line => max(0, Line - 1), character => 20}
        }
    }.

%% Extract symbol for type definition
extract_type_symbol(#type_def{name = Name, location = Location}) ->
    Line =
        case Location of
            #location{line = L} -> L;
            _ -> 0
        end,
    #{
        name => atom_to_binary(Name, utf8),
        % TypeParameter (LSP kind 25)
        kind => 25,
        range => #{
            start => #{line => max(0, Line - 1), character => 0},
            'end' => #{line => Line + 3, character => 0}
        },
        selectionRange => #{
            start => #{line => max(0, Line - 1), character => 0},
            'end' => #{line => max(0, Line - 1), character => 20}
        }
    }.

%% Extract symbol for trait definition
extract_trait_symbol(#trait_def{name = Name, location = Location}) ->
    Line =
        case Location of
            #location{line = L} -> L;
            _ -> 0
        end,
    #{
        name => atom_to_binary(Name, utf8),
        % Interface (LSP kind 11)
        kind => 11,
        range => #{
            start => #{line => max(0, Line - 1), character => 0},
            'end' => #{line => Line + 10, character => 0}
        },
        selectionRange => #{
            start => #{line => max(0, Line - 1), character => 0},
            'end' => #{line => max(0, Line - 1), character => 20}
        }
    }.

%% Extract symbol for trait implementation
extract_trait_impl_symbol(#trait_impl{
    trait_name = TraitName, for_type = ForType, location = Location
}) ->
    Line =
        case Location of
            #location{line = L} -> L;
            _ -> 0
        end,
    TypeName = format_type_for_display(ForType),
    Name = iolist_to_binary([atom_to_binary(TraitName, utf8), " for ", TypeName]),
    #{
        name => Name,
        % Class (LSP kind 5)
        kind => 5,
        range => #{
            start => #{line => max(0, Line - 1), character => 0},
            'end' => #{line => Line + 10, character => 0}
        },
        selectionRange => #{
            start => #{line => max(0, Line - 1), character => 0},
            'end' => #{line => max(0, Line - 1), character => 30}
        }
    }.

%% Extract symbol for typeclass definition
extract_typeclass_symbol(#typeclass_def{name = Name, location = Location}) ->
    Line =
        case Location of
            #location{line = L} -> L;
            _ -> 0
        end,
    #{
        name => atom_to_binary(Name, utf8),
        % Interface (LSP kind 11)
        kind => 11,
        range => #{
            start => #{line => max(0, Line - 1), character => 0},
            'end' => #{line => Line + 10, character => 0}
        },
        selectionRange => #{
            start => #{line => max(0, Line - 1), character => 0},
            'end' => #{line => max(0, Line - 1), character => 20}
        }
    }.

%% Extract symbol for instance definition
extract_instance_symbol(#instance_def{
    typeclass = Typeclass, type_args = TypeArgs, location = Location
}) ->
    Line =
        case Location of
            #location{line = L} -> L;
            _ -> 0
        end,
    TypeArgsStr = format_type_args(TypeArgs),
    Name = iolist_to_binary([atom_to_binary(Typeclass, utf8), "(", TypeArgsStr, ")"]),
    #{
        name => Name,
        % Class (LSP kind 5)
        kind => 5,
        range => #{
            start => #{line => max(0, Line - 1), character => 0},
            'end' => #{line => Line + 10, character => 0}
        },
        selectionRange => #{
            start => #{line => max(0, Line - 1), character => 0},
            'end' => #{line => max(0, Line - 1), character => 30}
        }
    }.

%% Helper to format type for display
format_type_for_display(#primitive_type{name = Name}) ->
    atom_to_binary(Name, utf8);
format_type_for_display(#dependent_type{name = Name}) ->
    atom_to_binary(Name, utf8);
format_type_for_display(Name) when is_atom(Name) ->
    atom_to_binary(Name, utf8);
format_type_for_display(_) ->
    <<"Type">>.

%% Helper to format type arguments
format_type_args([]) ->
    <<"">>;
format_type_args([Type]) ->
    format_type_for_display(Type);
format_type_args([Type | Rest]) ->
    iolist_to_binary([format_type_for_display(Type), ", ", format_type_args(Rest)]).

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
get_item_start_line(#record_def{location = #location{line = L}}) -> L;
get_item_start_line(#type_def{location = #location{line = L}}) -> L;
get_item_start_line(#trait_def{location = #location{line = L}}) -> L;
get_item_start_line(#trait_impl{location = #location{line = L}}) -> L;
get_item_start_line(#typeclass_def{location = #location{line = L}}) -> L;
get_item_start_line(#instance_def{location = #location{line = L}}) -> L;
get_item_start_line(_) -> undefined.

get_item_end_line(#function_def{location = #location{line = L}}) -> L;
get_item_end_line(#fsm_def{location = #location{line = L}}) -> L;
get_item_end_line(#record_def{location = #location{line = L}}) -> L;
get_item_end_line(#type_def{location = #location{line = L}}) -> L;
get_item_end_line(#trait_def{location = #location{line = L}}) -> L;
get_item_end_line(#trait_impl{location = #location{line = L}}) -> L;
get_item_end_line(#typeclass_def{location = #location{line = L}}) -> L;
get_item_end_line(#instance_def{location = #location{line = L}}) -> L;
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
find_symbol_in_item_with_end(
    #record_def{name = Name, location = Location}, Line, _Character, NextStartLine
) ->
    case Location of
        #location{line = RecLine} ->
            CursorLine = Line + 1,
            RecEndLine =
                case NextStartLine of
                    undefined -> RecLine + 1000;
                    NextLine -> NextLine - 1
                end,
            if
                CursorLine >= RecLine andalso CursorLine =< RecEndLine ->
                    {ok, Name, record};
                true ->
                    {error, not_found}
            end;
        _ ->
            {error, not_found}
    end;
find_symbol_in_item_with_end(
    #typeclass_def{name = Name, location = Location}, Line, _Character, NextStartLine
) ->
    case Location of
        #location{line = TcLine} ->
            CursorLine = Line + 1,
            TcEndLine =
                case NextStartLine of
                    undefined -> TcLine + 1000;
                    NextLine -> NextLine - 1
                end,
            if
                CursorLine >= TcLine andalso CursorLine =< TcEndLine ->
                    {ok, Name, typeclass};
                true ->
                    {error, not_found}
            end;
        _ ->
            {error, not_found}
    end;
find_symbol_in_item_with_end(
    #trait_def{name = Name, location = Location}, Line, _Character, NextStartLine
) ->
    case Location of
        #location{line = TraitLine} ->
            CursorLine = Line + 1,
            TraitEndLine =
                case NextStartLine of
                    undefined -> TraitLine + 1000;
                    NextLine -> NextLine - 1
                end,
            if
                CursorLine >= TraitLine andalso CursorLine =< TraitEndLine ->
                    {ok, Name, trait};
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
find_symbol_definition(Items, SymbolName, record) ->
    case
        lists:search(
            fun
                (#record_def{name = N}) when N =:= SymbolName -> true;
                (_) -> false
            end,
            Items
        )
    of
        {value, #record_def{location = #location{line = L}}} ->
            #{
                range => #{
                    start => #{line => max(0, L - 1), character => 0},
                    'end' => #{line => max(0, L - 1), character => 100}
                }
            };
        _ ->
            null
    end;
find_symbol_definition(Items, SymbolName, typeclass) ->
    case
        lists:search(
            fun
                (#typeclass_def{name = N}) when N =:= SymbolName -> true;
                (_) -> false
            end,
            Items
        )
    of
        {value, #typeclass_def{location = #location{line = L}}} ->
            #{
                range => #{
                    start => #{line => max(0, L - 1), character => 0},
                    'end' => #{line => max(0, L - 1), character => 100}
                }
            };
        _ ->
            null
    end;
find_symbol_definition(Items, SymbolName, trait) ->
    case
        lists:search(
            fun
                (#trait_def{name = N}) when N =:= SymbolName -> true;
                (_) -> false
            end,
            Items
        )
    of
        {value, #trait_def{location = #location{line = L}}} ->
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
get_symbol_hover_info(Items, SymbolName, record) ->
    case
        lists:search(
            fun
                (#record_def{name = N}) when N =:= SymbolName -> true;
                (_) -> false
            end,
            Items
        )
    of
        {value, #record_def{name = Name, fields = Fields}} ->
            FieldStrs = [format_record_field(F) || F <- Fields],
            FieldsStr = iolist_to_binary(lists:join(<<"\n  ">>, FieldStrs)),
            Content = iolist_to_binary([
                <<"```cure\n">>,
                <<"record ">>,
                atom_to_binary(Name, utf8),
                <<" do\n  ">>,
                FieldsStr,
                <<"\nend\n```">>
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
get_symbol_hover_info(Items, SymbolName, typeclass) ->
    case
        lists:search(
            fun
                (#typeclass_def{name = N}) when N =:= SymbolName -> true;
                (_) -> false
            end,
            Items
        )
    of
        {value, #typeclass_def{name = Name, type_params = TypeParams, methods = Methods}} ->
            TypeParamsStr = format_type_params(TypeParams),
            MethodStrs = [format_method_signature(M) || M <- Methods],
            MethodsStr = iolist_to_binary(lists:join(<<"\n  ">>, MethodStrs)),
            Content = iolist_to_binary([
                <<"```cure\n">>,
                <<"typeclass ">>,
                atom_to_binary(Name, utf8),
                <<"(">>,
                TypeParamsStr,
                <<") do\n  ">>,
                MethodsStr,
                <<"\nend\n```">>
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
get_symbol_hover_info(Items, SymbolName, trait) ->
    case
        lists:search(
            fun
                (#trait_def{name = N}) when N =:= SymbolName -> true;
                (_) -> false
            end,
            Items
        )
    of
        {value, #trait_def{name = Name, type_params = TypeParams, methods = Methods}} ->
            TypeParamsStr = format_type_params(TypeParams),
            MethodStrs = [format_method_signature(M) || M <- Methods],
            MethodsStr = iolist_to_binary(lists:join(<<"\n  ">>, MethodStrs)),
            Content = iolist_to_binary([
                <<"```cure\n">>,
                <<"trait ">>,
                atom_to_binary(Name, utf8),
                <<"(">>,
                TypeParamsStr,
                <<") do\n  ">>,
                MethodsStr,
                <<"\nend\n```">>
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
    % Call the type checker and convert results to LSP diagnostics
    try
        Result = cure_typechecker:check_program(AST),
        case Result of
            #typecheck_result{success = true, warnings = Warnings} ->
                % Type checking succeeded - convert warnings to diagnostics
                lists:map(fun convert_type_warning/1, Warnings);
            #typecheck_result{success = false, errors = Errors, warnings = Warnings} ->
                % Type checking failed - convert both errors and warnings
                ErrorDiags = lists:map(fun convert_type_error/1, Errors),
                WarningDiags = lists:map(fun convert_type_warning/1, Warnings),
                ErrorDiags ++ WarningDiags;
            _ ->
                % Unexpected result format
                []
        end
    catch
        error:undef ->
            % Type checker module not available
            [];
        _:Reason ->
            % Type checker crashed - log but don't fail LSP
            io:format("Type checker error: ~p~n", [Reason]),
            []
    end.

%% Convert type checker error record to LSP diagnostic
convert_type_error(#typecheck_error{message = Message, location = Location, details = _Details}) ->
    {Line, Column} = extract_location(Location),
    make_diagnostic(Line, Column, format_message(Message), error);
convert_type_error({error, Reason, #location{line = Line, column = Column}}) ->
    make_diagnostic(Line, Column, format_message(Reason), error);
convert_type_error({Line, Column, Message}) when is_integer(Line), is_integer(Column) ->
    make_diagnostic(Line, Column, format_message(Message), error);
convert_type_error({Line, Message}) when is_integer(Line) ->
    make_diagnostic(Line, 0, format_message(Message), error);
convert_type_error({Reason, Line, Column}) when is_integer(Line), is_integer(Column) ->
    make_diagnostic(Line, Column, format_message(Reason), error);
convert_type_error(Error) ->
    io:format("[LSP] Type error without location: ~p~n", [Error]),
    make_diagnostic(1, 1, format_message(Error), error).

%% Convert type checker warning record to LSP diagnostic
convert_type_warning(#typecheck_warning{message = Message, location = Location, details = _Details}) ->
    {Line, Column} = extract_location(Location),
    make_diagnostic(Line, Column, format_message(Message), warning);
convert_type_warning({warning, Reason, #location{line = Line, column = Column}}) ->
    make_diagnostic(Line, Column, format_message(Reason), warning);
convert_type_warning({Line, Column, Message}) when is_integer(Line), is_integer(Column) ->
    make_diagnostic(Line, Column, format_message(Message), warning);
convert_type_warning({Line, Message}) when is_integer(Line) ->
    make_diagnostic(Line, 0, format_message(Message), warning);
convert_type_warning({Reason, Line, Column}) when is_integer(Line), is_integer(Column) ->
    make_diagnostic(Line, Column, format_message(Reason), warning);
convert_type_warning(Warning) ->
    io:format("[LSP] Type warning without location: ~p~n", [Warning]),
    make_diagnostic(1, 1, format_message(Warning), warning).

%% Extract line and column from location record or tuple
extract_location(#location{line = Line, column = Col}) ->
    {Line, Col};
extract_location({Line, Col}) when is_integer(Line), is_integer(Col) ->
    {Line, Col};
extract_location(Line) when is_integer(Line) ->
    {Line, 0};
extract_location(_) ->
    {0, 0}.

%% Helper functions
make_diagnostic(Line, Column, Message, Severity) when is_integer(Line), is_integer(Column) ->
    #{
        range => #{
            start => #{line => max(0, Line - 1), character => Column},
            'end' => #{line => max(0, Line - 1), character => Column + 10}
        },
        severity => severity_to_int(Severity),
        source => <<"cure-lsp">>,
        message => format_message(Message)
    };
make_diagnostic(_Line, _Column, Message, Severity) ->
    % Fallback for when location is not provided properly
    #{
        range => #{
            start => #{line => 0, character => 0},
            'end' => #{line => 0, character => 10}
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

%% Format record field for display
format_record_field(#record_field_def{name = Name, type = Type}) ->
    TypeStr = format_type(Type),
    case TypeStr of
        <<>> -> atom_to_binary(Name, utf8);
        _ -> iolist_to_binary([atom_to_binary(Name, utf8), <<": ">>, TypeStr])
    end;
format_record_field(_) ->
    <<"field">>.

%% Format method signature for display
format_method_signature(#method_signature{name = Name, params = Params, return_type = RetType}) ->
    ParamStr = format_params(Params),
    RetStr = format_type(RetType),
    iolist_to_binary([
        <<"def ">>,
        atom_to_binary(Name, utf8),
        <<"(">>,
        ParamStr,
        <<")">>,
        case RetStr of
            <<>> -> <<>>;
            _ -> [<<": ">>, RetStr]
        end
    ]);
format_method_signature(_) ->
    <<"method">>.

%% Format type parameters
format_type_params([]) ->
    <<>>;
format_type_params(TypeParams) when is_list(TypeParams) ->
    ParamStrs = [format_type_param(TP) || TP <- TypeParams],
    iolist_to_binary(lists:join(<<", ">>, ParamStrs));
format_type_params(_) ->
    <<>>.

format_type_param(Param) when is_atom(Param) ->
    atom_to_binary(Param, utf8);
format_type_param(#type_param_decl{name = Name}) ->
    atom_to_binary(Name, utf8);
format_type_param(_) ->
    <<"T">>.
