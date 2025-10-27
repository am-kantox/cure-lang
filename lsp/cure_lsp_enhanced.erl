%% Enhanced Cure LSP Server with Advanced Features
-module(cure_lsp_enhanced).

-export([
    % Enhanced LSP handlers
    handle_code_action/3,
    handle_code_lens/3,
    handle_document_formatting/3,
    handle_document_range_formatting/3,
    handle_document_on_type_formatting/3,
    handle_rename/3,
    handle_prepare_rename/3,
    handle_folding_range/3,
    handle_selection_range/3,
    handle_semantic_tokens/3,
    handle_inlay_hints/3,
    handle_call_hierarchy/3,
    handle_type_hierarchy/3,
    handle_document_highlight/3,
    handle_signature_help/3,
    handle_workspace_symbol/3,

    % SMT-enhanced features
    handle_type_verification/3,
    handle_constraint_solving/3,
    handle_proof_generation/3,

    % Diagnostics enhancements
    generate_enhanced_diagnostics/2,
    generate_smt_diagnostics/2
]).

-include("../src/parser/cure_ast.hrl").

%% Include or define the LSP state record
-record(lsp_state, {
    transport = stdio :: stdio | tcp,
    socket = undefined,
    buffer = <<>> :: binary(),
    initialized = false :: boolean(),
    root_uri = undefined :: undefined | binary(),
    workspace_folders = [] :: list(),
    client_capabilities = #{} :: map(),
    documents = #{} :: map(),
    diagnostics = #{} :: map(),
    symbols = undefined
}).

%% ============================================================================
%% Code Actions
%% ============================================================================

%% @doc Handle code action requests (quick fixes, refactorings)
handle_code_action(Id, Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Range = maps:get(range, Params),
    Context = maps:get(context, Params, #{}),
    Uri = maps:get(uri, TextDocument),

    Actions =
        case maps:get(Uri, State#lsp_state.documents, undefined) of
            undefined ->
                [];
            Doc ->
                Text = maps:get(text, Doc),
                Diagnostics = maps:get(diagnostics, Context, []),
                generate_code_actions(Text, Range, Diagnostics, Uri)
        end,

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => Actions
    },
    cure_lsp:send_message(Response, State),
    State.

generate_code_actions(Text, Range, Diagnostics, Uri) ->
    % Generate various code actions based on context
    QuickFixes = generate_quick_fixes(Diagnostics, Uri),
    Refactorings = generate_refactorings(Text, Range, Uri),
    SmtActions = generate_smt_actions(Text, Range, Uri),

    QuickFixes ++ Refactorings ++ SmtActions.

generate_quick_fixes(Diagnostics, Uri) ->
    lists:flatmap(fun(Diag) -> quick_fixes_for_diagnostic(Diag, Uri) end, Diagnostics).

quick_fixes_for_diagnostic(#{message := Msg} = _Diag, Uri) ->
    case Msg of
        <<"Undefined function ", _/binary>> ->
            [
                #{
                    title => <<"Create function">>,
                    kind => <<"quickfix">>,
                    diagnostics => [],
                    edit => #{
                        changes => #{
                            Uri => []
                        }
                    }
                }
            ];
        <<"Type mismatch", _/binary>> ->
            [
                #{
                    title => <<"Add type annotation">>,
                    kind => <<"quickfix">>
                }
            ];
        _ ->
            []
    end.

generate_refactorings(_Text, Range, Uri) ->
    [
        #{
            title => <<"Extract function">>,
            kind => <<"refactor.extract">>,
            command => #{
                title => <<"Extract to function">>,
                command => <<"cure.refactor.extractFunction">>,
                arguments => [Uri, Range]
            }
        },
        #{
            title => <<"Inline function">>,
            kind => <<"refactor.inline">>,
            command => #{
                title => <<"Inline function call">>,
                command => <<"cure.refactor.inlineFunction">>,
                arguments => [Uri, Range]
            }
        },
        #{
            title => <<"Rename symbol">>,
            kind => <<"refactor.rename">>,
            command => #{
                title => <<"Rename">>,
                command => <<"cure.refactor.rename">>,
                arguments => [Uri, Range]
            }
        }
    ].

generate_smt_actions(_Text, Range, Uri) ->
    % SMT-enhanced actions for dependent types
    [
        #{
            title => <<"Verify type constraints">>,
            kind => <<"source.verifyConstraints">>,
            command => #{
                title => <<"Verify SMT constraints">>,
                command => <<"cure.smt.verifyConstraints">>,
                arguments => [Uri, Range]
            }
        },
        #{
            title => <<"Generate proof">>,
            kind => <<"source.generateProof">>,
            command => #{
                title => <<"Generate type proof">>,
                command => <<"cure.smt.generateProof">>,
                arguments => [Uri, Range]
            }
        },
        #{
            title => <<"Add refinement type">>,
            kind => <<"refactor.rewrite">>,
            command => #{
                title => <<"Add refinement type annotation">>,
                command => <<"cure.refactor.addRefinementType">>,
                arguments => [Uri, Range]
            }
        }
    ].

%% ============================================================================
%% Semantic Tokens
%% ============================================================================

handle_semantic_tokens(Id, Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Uri = maps:get(uri, TextDocument),

    Tokens =
        case maps:get(Uri, State#lsp_state.documents, undefined) of
            undefined ->
                [];
            Doc ->
                Text = maps:get(text, Doc),
                generate_semantic_tokens(Text)
        end,

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => #{data => Tokens}
    },
    cure_lsp:send_message(Response, State),
    State.

generate_semantic_tokens(Text) when is_binary(Text) ->
    case cure_lexer:tokenize(Text) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, AST} ->
                    encode_semantic_tokens(extract_semantic_tokens(AST));
                _ ->
                    []
            end;
        _ ->
            []
    end.

extract_semantic_tokens(#module_def{items = Items}) ->
    lists:flatmap(fun extract_tokens_from_item/1, Items);
extract_semantic_tokens(_) ->
    [].

extract_tokens_from_item(#function_def{name = Name, params = Params, body = Body, location = Loc}) ->
    FuncToken = {Loc, Name, function, []},
    ParamTokens = lists:map(
        fun(#param{name = N, location = L}) ->
            {L, N, parameter, []}
        end,
        Params
    ),
    BodyTokens = extract_tokens_from_expr(Body),
    [FuncToken | ParamTokens] ++ BodyTokens;
extract_tokens_from_item(#fsm_def{name = Name, location = Loc}) ->
    [{Loc, Name, class, []}];
extract_tokens_from_item(_) ->
    [].

extract_tokens_from_expr(#identifier_expr{name = Name, location = Loc}) ->
    [{Loc, Name, variable, []}];
extract_tokens_from_expr(#function_call_expr{function = Func, args = Args}) ->
    extract_tokens_from_expr(Func) ++
        lists:flatmap(fun extract_tokens_from_expr/1, Args);
extract_tokens_from_expr(#let_expr{bindings = Bindings, body = Body}) ->
    BindingTokens = lists:flatmap(
        fun(#binding{pattern = P, value = V, location = L}) ->
            case P of
                #identifier_pattern{name = N} ->
                    [{L, N, variable, [declaration]} | extract_tokens_from_expr(V)];
                _ ->
                    extract_tokens_from_expr(V)
            end
        end,
        Bindings
    ),
    BindingTokens ++ extract_tokens_from_expr(Body);
extract_tokens_from_expr(#block_expr{expressions = Exprs}) ->
    lists:flatmap(fun extract_tokens_from_expr/1, Exprs);
extract_tokens_from_expr(_) ->
    [].

encode_semantic_tokens(Tokens) ->
    % Convert to LSP delta-encoded format
    % [deltaLine, deltaStartChar, length, tokenType, tokenModifiers]
    SortedTokens = lists:sort(fun compare_token_positions/2, Tokens),
    encode_tokens_delta(SortedTokens, 0, 0, []).

compare_token_positions(
    {#location{line = L1, column = C1}, _, _, _},
    {#location{line = L2, column = C2}, _, _, _}
) ->
    if
        L1 < L2 -> true;
        L1 > L2 -> false;
        true -> C1 =< C2
    end;
compare_token_positions(_, _) ->
    true.

encode_tokens_delta([], _PrevLine, _PrevChar, Acc) ->
    lists:reverse(Acc);
encode_tokens_delta(
    [{#location{line = Line, column = Col}, Name, Type, Mods} | Rest],
    PrevLine,
    PrevChar,
    Acc
) ->
    DeltaLine = Line - PrevLine - 1,
    DeltaChar =
        if
            DeltaLine =:= 0 -> Col - PrevChar;
            true -> Col
        end,
    Length = byte_size(atom_to_binary(Name, utf8)),
    TypeInt = semantic_token_type_to_int(Type),
    ModsInt = semantic_token_mods_to_int(Mods),

    Token = [DeltaLine, DeltaChar, Length, TypeInt, ModsInt],
    encode_tokens_delta(Rest, Line - 1, Col, [Token | Acc]);
encode_tokens_delta([_ | Rest], PrevLine, PrevChar, Acc) ->
    encode_tokens_delta(Rest, PrevLine, PrevChar, Acc).

semantic_token_type_to_int(function) -> 0;
semantic_token_type_to_int(variable) -> 1;
semantic_token_type_to_int(parameter) -> 2;
semantic_token_type_to_int(type) -> 3;
semantic_token_type_to_int(class) -> 4;
semantic_token_type_to_int(property) -> 5;
semantic_token_type_to_int(keyword) -> 6;
semantic_token_type_to_int(_) -> 1.

semantic_token_mods_to_int(Mods) ->
    lists:foldl(
        fun(Mod, Acc) ->
            Acc bor semantic_token_mod_bit(Mod)
        end,
        0,
        Mods
    ).

semantic_token_mod_bit(declaration) -> 1;
semantic_token_mod_bit(definition) -> 2;
semantic_token_mod_bit(readonly) -> 4;
semantic_token_mod_bit(_) -> 0.

%% ============================================================================
%% Inlay Hints
%% ============================================================================

handle_inlay_hints(Id, Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Range = maps:get(range, Params),
    Uri = maps:get(uri, TextDocument),

    Hints =
        case maps:get(Uri, State#lsp_state.documents, undefined) of
            undefined ->
                [];
            Doc ->
                Text = maps:get(text, Doc),
                generate_inlay_hints(Text, Range)
        end,

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => Hints
    },
    cure_lsp:send_message(Response, State),
    State.

generate_inlay_hints(Text, _Range) when is_binary(Text) ->
    case cure_lexer:tokenize(Text) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, AST} ->
                    extract_inlay_hints(AST);
                _ ->
                    []
            end;
        _ ->
            []
    end.

extract_inlay_hints(#module_def{items = Items}) ->
    lists:flatmap(fun extract_hints_from_item/1, Items);
extract_inlay_hints(_) ->
    [].

extract_hints_from_item(#function_def{params = Params, return_type = RetType, body = Body}) ->
    % Type hints for parameters without explicit types
    ParamHints = lists:filtermap(
        fun(#param{name = Name, type = Type, location = Loc}) ->
            case Type of
                undefined ->
                    % Infer type from usage
                    InferredType = infer_param_type(Name, Body),
                    case InferredType of
                        unknown ->
                            false;
                        _ ->
                            {true, #{
                                position => location_to_position(Loc),
                                label => <<": ", (format_type_hint(InferredType))/binary>>,
                                % Type hint
                                kind => 1,
                                paddingLeft => false,
                                paddingRight => true
                            }}
                    end;
                _ ->
                    false
            end
        end,
        Params
    ),

    % Return type hints
    ReturnHint =
        case RetType of
            undefined ->
                InferredRet = infer_return_type(Body),
                case InferredRet of
                    unknown ->
                        [];
                    _ ->
                        [
                            #{
                                % Position at function end
                                position => #{line => 0, character => 0},
                                label => <<" -> ", (format_type_hint(InferredRet))/binary>>,
                                kind => 1,
                                paddingLeft => true,
                                paddingRight => false
                            }
                        ]
                end;
            _ ->
                []
        end,

    % SMT constraint hints
    ConstraintHints = extract_constraint_hints(Body),

    ParamHints ++ ReturnHint ++ ConstraintHints;
extract_hints_from_item(_) ->
    [].

infer_param_type(_Name, _Body) ->
    % Placeholder for type inference
    unknown.

infer_return_type(_Body) ->
    % Placeholder for return type inference
    unknown.

extract_constraint_hints(_Body) ->
    % Extract SMT constraints and show them as hints
    [].

format_type_hint(Type) ->
    atom_to_binary(Type, utf8).

location_to_position(#location{line = Line, column = Col}) ->
    #{line => max(0, Line - 1), character => Col};
location_to_position(_) ->
    #{line => 0, character => 0}.

%% ============================================================================
%% Call Hierarchy
%% ============================================================================

handle_call_hierarchy(Id, Params, State) ->
    Item = maps:get(item, Params, undefined),
    Direction = maps:get(direction, Params, incoming),

    Result =
        case Item of
            undefined ->
                % Prepare call hierarchy
                TextDocument = maps:get(textDocument, Params),
                Position = maps:get(position, Params),
                Uri = maps:get(uri, TextDocument),
                prepare_call_hierarchy(Uri, Position, State);
            _ ->
                % Get incoming/outgoing calls
                case Direction of
                    incoming -> get_incoming_calls(Item, State);
                    outgoing -> get_outgoing_calls(Item, State)
                end
        end,

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => Result
    },
    cure_lsp:send_message(Response, State),
    State.

prepare_call_hierarchy(Uri, Position, State) ->
    case maps:get(Uri, State#lsp_state.documents, undefined) of
        undefined ->
            null;
        Doc ->
            Text = maps:get(text, Doc),
            Line = maps:get(line, Position),
            Character = maps:get(character, Position),
            find_call_hierarchy_item(Text, Line, Character, Uri)
    end.

find_call_hierarchy_item(Text, Line, Character, Uri) ->
    case cure_lsp_analyzer:analyze_document(Text) of
        #{parse_result := {ok, AST}} ->
            case find_function_at_position(AST, Line, Character) of
                {ok, FuncDef} ->
                    function_to_call_hierarchy_item(FuncDef, Uri);
                _ ->
                    null
            end;
        _ ->
            null
    end.

find_function_at_position(#module_def{items = Items}, Line, Character) ->
    find_function_in_items(Items, Line, Character).

find_function_in_items([], _Line, _Character) ->
    {error, not_found};
find_function_in_items([#function_def{location = #location{line = L}} = Func | _], Line, _Char) when
    L =:= Line + 1
->
    {ok, Func};
find_function_in_items([_ | Rest], Line, Character) ->
    find_function_in_items(Rest, Line, Character).

function_to_call_hierarchy_item(#function_def{name = Name, params = Params, location = Loc}, Uri) ->
    Arity = length(Params),
    #{
        name => iolist_to_binary(io_lib:format("~s/~p", [Name, Arity])),
        % Function
        kind => 12,
        uri => Uri,
        range => location_to_range(Loc),
        selectionRange => location_to_range(Loc)
    }.

location_to_range(#location{line = Line}) ->
    #{
        start => #{line => max(0, Line - 1), character => 0},
        'end' => #{line => Line, character => 0}
    };
location_to_range(_) ->
    #{start => #{line => 0, character => 0}, 'end' => #{line => 0, character => 0}}.

get_incoming_calls(_Item, _State) ->
    % Find all functions that call this one
    [].

get_outgoing_calls(_Item, _State) ->
    % Find all functions called by this one
    [].

%% ============================================================================
%% Type Hierarchy
%% ============================================================================

handle_type_hierarchy(Id, Params, State) ->
    Item = maps:get(item, Params, undefined),
    Direction = maps:get(direction, Params, supertypes),

    Result =
        case Item of
            undefined ->
                % Prepare type hierarchy
                TextDocument = maps:get(textDocument, Params),
                Position = maps:get(position, Params),
                Uri = maps:get(uri, TextDocument),
                prepare_type_hierarchy(Uri, Position, State);
            _ ->
                % Get supertypes/subtypes
                case Direction of
                    supertypes -> get_supertypes(Item, State);
                    subtypes -> get_subtypes(Item, State)
                end
        end,

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => Result
    },
    cure_lsp:send_message(Response, State),
    State.

prepare_type_hierarchy(_Uri, _Position, _State) ->
    null.

get_supertypes(_Item, _State) ->
    [].

get_subtypes(_Item, _State) ->
    [].

%% ============================================================================
%% Rename
%% ============================================================================

handle_rename(Id, Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Position = maps:get(position, Params),
    NewName = maps:get(newName, Params),
    Uri = maps:get(uri, TextDocument),

    WorkspaceEdit =
        case maps:get(Uri, State#lsp_state.documents, undefined) of
            undefined ->
                null;
            Doc ->
                Text = maps:get(text, Doc),
                Line = maps:get(line, Position),
                Character = maps:get(character, Position),
                generate_rename_edits(Text, Line, Character, NewName, Uri)
        end,

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => WorkspaceEdit
    },
    cure_lsp:send_message(Response, State),
    State.

handle_prepare_rename(Id, Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Position = maps:get(position, Params),
    Uri = maps:get(uri, TextDocument),

    Result =
        case maps:get(Uri, State#lsp_state.documents, undefined) of
            undefined ->
                null;
            Doc ->
                Text = maps:get(text, Doc),
                Line = maps:get(line, Position),
                Character = maps:get(character, Position),
                check_rename_eligibility(Text, Line, Character)
        end,

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => Result
    },
    cure_lsp:send_message(Response, State),
    State.

generate_rename_edits(Text, Line, Character, NewName, Uri) ->
    case cure_lsp_analyzer:get_references(Text, Line, Character) of
        [] ->
            null;
        References ->
            Edits = lists:map(
                fun(Ref) ->
                    #{
                        range => maps:get(range, Ref),
                        newText => NewName
                    }
                end,
                References
            ),
            #{
                changes => #{
                    Uri => Edits
                }
            }
    end.

check_rename_eligibility(Text, Line, Character) ->
    case cure_lsp_document:get_word_at_position(Text, Line, Character) of
        {ok, Word} ->
            #{
                range => #{
                    start => #{line => Line, character => Character},
                    'end' => #{line => Line, character => Character + byte_size(Word)}
                },
                placeholder => Word
            };
        _ ->
            null
    end.

%% ============================================================================
%% Formatting
%% ============================================================================

handle_document_formatting(Id, Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    _Options = maps:get(options, Params),
    Uri = maps:get(uri, TextDocument),

    Edits =
        case maps:get(Uri, State#lsp_state.documents, undefined) of
            undefined ->
                [];
            Doc ->
                Text = maps:get(text, Doc),
                format_document(Text)
        end,

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => Edits
    },
    cure_lsp:send_message(Response, State),
    State.

handle_document_range_formatting(Id, Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Range = maps:get(range, Params),
    _Options = maps:get(options, Params),
    Uri = maps:get(uri, TextDocument),

    Edits =
        case maps:get(Uri, State#lsp_state.documents, undefined) of
            undefined ->
                [];
            Doc ->
                Text = maps:get(text, Doc),
                format_range(Text, Range)
        end,

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => Edits
    },
    cure_lsp:send_message(Response, State),
    State.

handle_document_on_type_formatting(Id, Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Position = maps:get(position, Params),
    Ch = maps:get(ch, Params),
    _Options = maps:get(options, Params),
    Uri = maps:get(uri, TextDocument),

    Edits =
        case maps:get(Uri, State#lsp_state.documents, undefined) of
            undefined ->
                [];
            Doc ->
                Text = maps:get(text, Doc),
                format_on_type(Text, Position, Ch)
        end,

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => Edits
    },
    cure_lsp:send_message(Response, State),
    State.

format_document(_Text) ->
    % Implement document formatting
    [].

format_range(_Text, _Range) ->
    % Implement range formatting
    [].

format_on_type(_Text, _Position, _Ch) ->
    % Implement on-type formatting
    [].

%% ============================================================================
%% Other LSP Features
%% ============================================================================

handle_code_lens(Id, Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Uri = maps:get(uri, TextDocument),

    Lenses =
        case maps:get(Uri, State#lsp_state.documents, undefined) of
            undefined ->
                [];
            Doc ->
                Text = maps:get(text, Doc),
                generate_code_lenses(Text, Uri)
        end,

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => Lenses
    },
    cure_lsp:send_message(Response, State),
    State.

generate_code_lenses(Text, Uri) ->
    case cure_lexer:tokenize(Text) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, AST} ->
                    extract_code_lenses(AST, Uri);
                _ ->
                    []
            end;
        _ ->
            []
    end.

extract_code_lenses(#module_def{items = Items}, Uri) ->
    lists:flatmap(fun(Item) -> code_lens_for_item(Item, Uri) end, Items);
extract_code_lenses(_, _) ->
    [].

code_lens_for_item(#function_def{name = Name, params = Params, location = Loc}, Uri) ->
    Arity = length(Params),
    [
        #{
            range => location_to_range(Loc),
            command => #{
                title => iolist_to_binary(io_lib:format("~p references", [0])),
                command => <<"cure.showReferences">>,
                arguments => [Uri, location_to_position(Loc), Name, Arity]
            }
        },
        #{
            range => location_to_range(Loc),
            command => #{
                title => <<"Run Tests">>,
                command => <<"cure.runTests">>,
                arguments => [Uri, Name, Arity]
            }
        }
    ];
code_lens_for_item(_, _) ->
    [].

handle_folding_range(Id, Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Uri = maps:get(uri, TextDocument),

    Ranges =
        case maps:get(Uri, State#lsp_state.documents, undefined) of
            undefined ->
                [];
            Doc ->
                Text = maps:get(text, Doc),
                generate_folding_ranges(Text)
        end,

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => Ranges
    },
    cure_lsp:send_message(Response, State),
    State.

generate_folding_ranges(_Text) ->
    [].

handle_selection_range(Id, Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Positions = maps:get(positions, Params),
    Uri = maps:get(uri, TextDocument),

    Ranges =
        case maps:get(Uri, State#lsp_state.documents, undefined) of
            undefined ->
                [];
            Doc ->
                Text = maps:get(text, Doc),
                lists:map(fun(Pos) -> generate_selection_range(Text, Pos) end, Positions)
        end,

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => Ranges
    },
    cure_lsp:send_message(Response, State),
    State.

generate_selection_range(_Text, _Position) ->
    null.

handle_document_highlight(Id, Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Position = maps:get(position, Params),
    Uri = maps:get(uri, TextDocument),

    Highlights =
        case maps:get(Uri, State#lsp_state.documents, undefined) of
            undefined ->
                [];
            Doc ->
                Text = maps:get(text, Doc),
                Line = maps:get(line, Position),
                Character = maps:get(character, Position),
                generate_document_highlights(Text, Line, Character)
        end,

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => Highlights
    },
    cure_lsp:send_message(Response, State),
    State.

generate_document_highlights(Text, Line, Character) ->
    % Find all occurrences of symbol at position
    case cure_lsp_analyzer:get_references(Text, Line, Character) of
        [] ->
            [];
        Refs ->
            lists:map(
                fun(Ref) ->
                    #{
                        range => maps:get(range, Ref),
                        % Text
                        kind => 1
                    }
                end,
                Refs
            )
    end.

handle_signature_help(Id, Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Position = maps:get(position, Params),
    Uri = maps:get(uri, TextDocument),

    Help =
        case maps:get(Uri, State#lsp_state.documents, undefined) of
            undefined ->
                null;
            Doc ->
                Text = maps:get(text, Doc),
                Line = maps:get(line, Position),
                Character = maps:get(character, Position),
                generate_signature_help(Text, Line, Character)
        end,

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => Help
    },
    cure_lsp:send_message(Response, State),
    State.

generate_signature_help(_Text, _Line, _Character) ->
    null.

handle_workspace_symbol(Id, Params, State) ->
    Query = maps:get(query, Params),

    Symbols = search_workspace_symbols(Query, State),

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => Symbols
    },
    cure_lsp:send_message(Response, State),
    State.

search_workspace_symbols(_Query, _State) ->
    [].

%% ============================================================================
%% SMT-Enhanced Features
%% ============================================================================

handle_type_verification(Id, Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Uri = maps:get(uri, TextDocument),

    Result =
        case maps:get(Uri, State#lsp_state.documents, undefined) of
            undefined ->
                #{verified => false, errors => []};
            Doc ->
                Text = maps:get(text, Doc),
                verify_types_with_smt(Text)
        end,

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => Result
    },
    cure_lsp:send_message(Response, State),
    State.

verify_types_with_smt(Text) when is_binary(Text) ->
    case cure_lexer:tokenize(Text) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, AST} ->
                    % Use SMT solver to verify dependent types
                    Constraints = cure_lsp_smt:extract_type_constraints(AST),
                    case cure_smt_solver:solve_constraints(Constraints) of
                        {sat, Solution} ->
                            #{verified => true, solution => Solution};
                        unsat ->
                            #{verified => false, reason => <<"Constraints unsatisfiable">>};
                        unknown ->
                            #{verified => false, reason => <<"Cannot determine">>}
                    end;
                {error, Reason} ->
                    #{verified => false, errors => [Reason]}
            end;
        {error, Reason} ->
            #{verified => false, errors => [Reason]}
    end.

handle_constraint_solving(Id, Params, State) ->
    Constraints = maps:get(constraints, Params),

    Result = cure_smt_solver:solve_constraints(Constraints),

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => Result
    },
    cure_lsp:send_message(Response, State),
    State.

handle_proof_generation(Id, Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Position = maps:get(position, Params),
    Uri = maps:get(uri, TextDocument),

    Proof =
        case maps:get(Uri, State#lsp_state.documents, undefined) of
            undefined ->
                null;
            Doc ->
                Text = maps:get(text, Doc),
                Line = maps:get(line, Position),
                Character = maps:get(character, Position),
                generate_proof_at_position(Text, Line, Character)
        end,

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => Proof
    },
    cure_lsp:send_message(Response, State),
    State.

generate_proof_at_position(_Text, _Line, _Character) ->
    null.

%% ============================================================================
%% Enhanced Diagnostics
%% ============================================================================

generate_enhanced_diagnostics(Text, Uri) ->
    BasicDiags = cure_lsp_analyzer:analyze(Text),
    SmtDiags = generate_smt_diagnostics(Text, Uri),
    BasicDiags ++ SmtDiags.

generate_smt_diagnostics(Text, _Uri) when is_binary(Text) ->
    case cure_lexer:tokenize(Text) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, AST} ->
                    verify_dependent_types(AST);
                _ ->
                    []
            end;
        _ ->
            []
    end.

verify_dependent_types(#module_def{items = Items}) ->
    lists:flatmap(fun verify_item_types/1, Items);
verify_dependent_types(_) ->
    [].

verify_item_types(#function_def{name = _Name, params = Params, body = Body, location = Loc}) ->
    % Extract type constraints from function
    ParamConstraints = lists:flatmap(fun extract_param_constraints/1, Params),
    BodyConstraints = extract_body_constraints(Body),

    AllConstraints = ParamConstraints ++ BodyConstraints,

    case cure_smt_solver:solve_constraints(AllConstraints) of
        {sat, _} ->
            [];
        unsat ->
            [
                #{
                    range => location_to_range(Loc),
                    % Error
                    severity => 1,
                    source => <<"cure-smt">>,
                    message => <<"Type constraints unsatisfiable">>
                }
            ];
        unknown ->
            []
    end;
verify_item_types(_) ->
    [].

extract_param_constraints(_Param) ->
    [].

extract_body_constraints(_Body) ->
    [].
