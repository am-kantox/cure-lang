-module(cure_lsp).
-export([start/0, start/1, stop/0]).

-behaviour(gen_server).
-export([init/1, handle_call/3, handle_cast/2, handle_info/2, terminate/2, code_change/3]).

-record(state, {
    transport = stdio :: stdio | tcp,
    socket = undefined,
    buffer = <<>> :: binary(),
    initialized = false :: boolean(),
    root_uri = undefined :: undefined | binary(),
    workspace_folders = [] :: list(),
    client_capabilities = #{} :: map(),
    % URI -> Document state
    documents = #{} :: map(),
    % URI -> Diagnostics
    diagnostics = #{} :: map(),
    % Symbol table for workspace
    symbols = undefined,
    % SMT verification state for refinement type checking
    smt_state = undefined
}).

%% Public API
start() ->
    start([{transport, stdio}]).

start(Options) ->
    gen_server:start_link({local, ?MODULE}, ?MODULE, Options, []).

stop() ->
    gen_server:stop(?MODULE).

%% gen_server callbacks
init(Options) ->
    Transport = proplists:get_value(transport, Options, stdio),
    SymbolTable = cure_lsp_symbols:new(),
    SmtState = cure_lsp_smt:init_verification_state(),
    State = #state{transport = Transport, symbols = SymbolTable, smt_state = SmtState},
    % Start stdin reader process
    spawn_link(fun() -> stdin_reader() end),
    {ok, State}.

handle_call(_Request, _From, State) ->
    {reply, ok, State}.

handle_cast(_Msg, State) ->
    {noreply, State}.

handle_info({io_request, From, ReplyAs, {get_until, _Prompt, _Mod, _Func, _Args}}, State) ->
    % Handle stdin reading
    From ! {io_reply, ReplyAs, eof},
    {noreply, State};
handle_info({stdin, Data}, State) ->
    NewBuffer = <<(State#state.buffer)/binary, Data/binary>>,
    {Messages, RemainingBuffer} = parse_messages(NewBuffer),

    NewState = lists:foldl(
        fun(Msg, AccState) -> process_message(Msg, AccState) end,
        State#state{buffer = RemainingBuffer},
        Messages
    ),

    {noreply, NewState};
handle_info(Info, State) ->
    io:format(standard_error, "Unexpected info: ~p~n", [Info]),
    {noreply, State}.

terminate(_Reason, _State) ->
    ok.

code_change(_OldVsn, State, _Extra) ->
    {ok, State}.

%% Internal functions
parse_messages(Buffer) ->
    parse_messages(Buffer, []).

parse_messages(Buffer, Acc) ->
    case parse_single_message(Buffer) of
        {ok, Message, Rest} ->
            parse_messages(Rest, [Message | Acc]);
        {incomplete, _} ->
            {lists:reverse(Acc), Buffer};
        {error, _Reason} ->
            {lists:reverse(Acc), <<>>}
    end.

parse_single_message(Buffer) ->
    case binary:split(Buffer, <<"\r\n\r\n">>) of
        [Header, Rest] ->
            case parse_header(Header) of
                {ok, ContentLength} ->
                    if
                        byte_size(Rest) >= ContentLength ->
                            <<Content:ContentLength/binary, Remaining/binary>> = Rest,
                            case decode_json(Content) of
                                {ok, Message} ->
                                    {ok, Message, Remaining};
                                {error, Reason} ->
                                    {error, {json_decode_error, Reason}}
                            end;
                        true ->
                            {incomplete, need_more_data}
                    end;
                {error, Reason} ->
                    {error, Reason}
            end;
        [_] ->
            {incomplete, need_headers}
    end.

parse_header(Header) ->
    Lines = binary:split(Header, <<"\r\n">>, [global]),
    parse_header_lines(Lines, undefined).

parse_header_lines([], undefined) ->
    {error, no_content_length};
parse_header_lines([], ContentLength) ->
    {ok, ContentLength};
parse_header_lines([Line | Rest], ContentLength) ->
    case binary:split(Line, <<": ">>) of
        [<<"Content-Length">>, LengthBin] ->
            Length = binary_to_integer(LengthBin),
            parse_header_lines(Rest, Length);
        [<<"Content-Type">>, _Type] ->
            parse_header_lines(Rest, ContentLength);
        _ ->
            parse_header_lines(Rest, ContentLength)
    end.

decode_json(Binary) ->
    try
        Decoded = json:decode(Binary),
        % Convert keys to atoms for compatibility with existing code
        {ok, atomize_keys(Decoded)}
    catch
        _:Error ->
            {error, Error}
    end.

encode_json(Term) ->
    % Convert atom keys to binary for json:encode
    PreparedTerm = binarize_keys(Term),
    % json:encode returns an iolist, convert to binary
    iolist_to_binary(json:encode(PreparedTerm)).

%% Helper functions for key conversion
atomize_keys(Map) when is_map(Map) ->
    maps:fold(
        fun(K, V, Acc) ->
            Key =
                if
                    is_binary(K) ->
                        try
                            binary_to_existing_atom(K, utf8)
                        catch
                            _:_ -> K
                        end;
                    true ->
                        K
                end,
            maps:put(Key, atomize_keys(V), Acc)
        end,
        #{},
        Map
    );
atomize_keys(List) when is_list(List) ->
    [atomize_keys(Item) || Item <- List];
atomize_keys(Other) ->
    Other.

binarize_keys(Map) when is_map(Map) ->
    maps:fold(
        fun(K, V, Acc) ->
            Key =
                if
                    is_atom(K) -> atom_to_binary(K, utf8);
                    true -> K
                end,
            maps:put(Key, binarize_keys(V), Acc)
        end,
        #{},
        Map
    );
binarize_keys(List) when is_list(List) ->
    [binarize_keys(Item) || Item <- List];
binarize_keys(Other) ->
    Other.

send_message(Message, State) ->
    Json = encode_json(Message),
    ContentLength = byte_size(Json),
    Response = iolist_to_binary([
        <<"Content-Length: ">>,
        integer_to_binary(ContentLength),
        <<"\r\n\r\n">>,
        Json
    ]),

    case State#state.transport of
        stdio ->
            io:put_chars(Response);
        tcp ->
            % TCP send implementation
            ok
    end.

process_message(Message, State) ->
    Method = maps:get(method, Message, undefined),
    Id = maps:get(id, Message, undefined),
    Params = maps:get(params, Message, #{}),

    case Method of
        <<"initialize">> ->
            handle_initialize(Id, Params, State);
        <<"initialized">> ->
            handle_initialized(State);
        <<"shutdown">> ->
            handle_shutdown(Id, State);
        <<"exit">> ->
            handle_exit(State);
        <<"textDocument/didOpen">> ->
            handle_did_open(Params, State);
        <<"textDocument/didChange">> ->
            handle_did_change(Params, State);
        <<"textDocument/didClose">> ->
            handle_did_close(Params, State);
        <<"textDocument/didSave">> ->
            handle_did_save(Params, State);
        <<"textDocument/completion">> ->
            handle_completion(Id, Params, State);
        <<"textDocument/hover">> ->
            handle_hover(Id, Params, State);
        <<"textDocument/definition">> ->
            handle_definition(Id, Params, State);
        <<"textDocument/references">> ->
            handle_references(Id, Params, State);
        <<"textDocument/documentSymbol">> ->
            handle_document_symbol(Id, Params, State);
        <<"textDocument/codeAction">> ->
            handle_code_action(Id, Params, State);
        _ ->
            io:format(standard_error, "Unhandled method: ~p~n", [Method]),
            State
    end.

handle_initialize(Id, Params, State) ->
    RootUri = maps:get(rootUri, Params, undefined),
    WorkspaceFolders = maps:get(workspaceFolders, Params, []),
    Capabilities = maps:get(capabilities, Params, #{}),

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => #{
            capabilities => #{
                textDocumentSync => #{
                    openClose => true,
                    % Full document sync (mode 1) - simpler and more reliable
                    change => 1,
                    save => #{includeText => true}
                },
                completionProvider => #{
                    triggerCharacters => [<<".">>, <<":">>]
                },
                hoverProvider => true,
                definitionProvider => true,
                referencesProvider => true,
                documentSymbolProvider => true,
                workspaceSymbolProvider => true,
                codeActionProvider => #{
                    codeActionKinds => [
                        <<"quickfix">>,
                        <<"refactor.rewrite">>
                    ]
                }
            },
            serverInfo => #{
                name => <<"cure-lsp">>,
                version => <<"0.1.0">>
            }
        }
    },

    send_message(Response, State),
    State#state{
        root_uri = RootUri,
        workspace_folders = WorkspaceFolders,
        client_capabilities = Capabilities
    }.

handle_initialized(State) ->
    State#state{initialized = true}.

handle_shutdown(Id, State) ->
    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => null
    },
    send_message(Response, State),
    State.

handle_exit(_State) ->
    init:stop(),
    exit(normal).

handle_did_open(Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Uri = maps:get(uri, TextDocument),
    Text = maps:get(text, TextDocument),
    Version = maps:get(version, TextDocument),

    Doc = #{
        uri => Uri,
        text => Text,
        version => Version
    },

    % Update symbol table with this document
    NewSymbols = update_symbols(Uri, Text, State#state.symbols),

    NewState = State#state{
        documents = maps:put(Uri, Doc, State#state.documents),
        symbols = NewSymbols
    },

    % Run diagnostics and get updated state
    diagnose_document(Uri, Text, NewState).

handle_did_change(Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Uri = maps:get(uri, TextDocument),
    Version = maps:get(version, TextDocument),
    ContentChanges = maps:get(contentChanges, Params),

    io:format(standard_error, "[LSP] Document changed: ~s (version ~p)~n", [Uri, Version]),

    case maps:get(Uri, State#state.documents, undefined) of
        undefined ->
            io:format(
                standard_error, "[LSP] Warning: Document not found in state, treating as new~n", []
            ),
            % Treat as new document
            NewText = get_text_from_changes(ContentChanges),
            NewParams = Params#{textDocument => TextDocument#{text => NewText}},
            handle_did_open(NewParams, State);
        Doc ->
            % Apply changes
            OldText = maps:get(text, Doc),
            NewText =
                try
                    apply_changes(OldText, ContentChanges)
                catch
                    Error:Reason:Stack ->
                        io:format(standard_error, "[LSP] Error applying changes: ~p:~p~n~p~n", [
                            Error, Reason, Stack
                        ]),
                        % Fall back to full text if available
                        get_text_from_changes(ContentChanges)
                end,

            io:format(standard_error, "[LSP] Text updated, length: ~p bytes~n", [byte_size(NewText)]),
            NewDoc = Doc#{text => NewText, version => Version},

            % Update symbol table
            NewSymbols =
                try
                    update_symbols(Uri, NewText, State#state.symbols)
                catch
                    _:SymErr ->
                        io:format(standard_error, "[LSP] Symbol update failed: ~p~n", [SymErr]),
                        State#state.symbols
                end,

            NewState = State#state{
                documents = maps:put(Uri, NewDoc, State#state.documents),
                symbols = NewSymbols
            },

            % Run diagnostics (with error handling)
            FinalState =
                try
                    UpdatedState = diagnose_document(Uri, NewText, NewState),
                    io:format(standard_error, "[LSP] Diagnostics sent for ~s~n", [Uri]),
                    UpdatedState
                catch
                    _:DiagErr:DiagStack ->
                        io:format(standard_error, "[LSP] Diagnostic error: ~p~n~p~n", [
                            DiagErr, DiagStack
                        ]),
                        % Send empty diagnostics on error
                        send_empty_diagnostics(Uri, NewState),
                        NewState
                end,
            FinalState
    end.

handle_did_close(Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Uri = maps:get(uri, TextDocument),

    State#state{
        documents = maps:remove(Uri, State#state.documents),
        diagnostics = maps:remove(Uri, State#state.diagnostics)
    }.

handle_did_save(_Params, State) ->
    State.

handle_completion(Id, Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Position = maps:get(position, Params),
    Uri = maps:get(uri, TextDocument),
    Line = maps:get(line, Position),
    Character = maps:get(character, Position),

    Completions =
        case maps:get(Uri, State#state.documents, undefined) of
            undefined ->
                [];
            Doc ->
                Text = maps:get(text, Doc),
                % Get word at cursor for filtering
                case cure_lsp_document:get_word_at_position(Text, Line, Character) of
                    {ok, Word} ->
                        cure_lsp_symbols:get_completions(State#state.symbols, Word);
                    _ ->
                        % No word, return all completions
                        cure_lsp_symbols:get_completions(State#state.symbols, <<>>)
                end
        end,

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => Completions
    },
    send_message(Response, State),
    State.

handle_hover(Id, Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Position = maps:get(position, Params),
    Uri = maps:get(uri, TextDocument),
    Line = maps:get(line, Position),
    Character = maps:get(character, Position),

    HoverResult =
        case maps:get(Uri, State#state.documents, undefined) of
            undefined ->
                null;
            Doc ->
                Text = maps:get(text, Doc),
                cure_lsp_analyzer:get_hover_info(Text, Line, Character)
        end,

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => HoverResult
    },
    send_message(Response, State),
    State.

handle_definition(Id, Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Position = maps:get(position, Params),
    Uri = maps:get(uri, TextDocument),
    Line = maps:get(line, Position),
    Character = maps:get(character, Position),

    DefinitionResult =
        case maps:get(Uri, State#state.documents, undefined) of
            undefined ->
                null;
            Doc ->
                Text = maps:get(text, Doc),
                cure_lsp_analyzer:get_definition(Text, Line, Character)
        end,

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => DefinitionResult
    },
    send_message(Response, State),
    State.

handle_references(Id, Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Position = maps:get(position, Params),
    Uri = maps:get(uri, TextDocument),
    Line = maps:get(line, Position),
    Character = maps:get(character, Position),

    References =
        case maps:get(Uri, State#state.documents, undefined) of
            undefined ->
                [];
            Doc ->
                Text = maps:get(text, Doc),
                cure_lsp_analyzer:get_references(Text, Line, Character)
        end,

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => References
    },
    send_message(Response, State),
    State.

handle_document_symbol(Id, Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Uri = maps:get(uri, TextDocument),

    Symbols =
        case maps:get(Uri, State#state.documents, undefined) of
            undefined ->
                [];
            Doc ->
                Text = maps:get(text, Doc),
                cure_lsp_analyzer:extract_symbols(Text)
        end,

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => Symbols
    },
    send_message(Response, State),
    State.

handle_code_action(Id, Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Uri = maps:get(uri, TextDocument),
    Context = maps:get(context, Params, #{}),
    Diagnostics = maps:get(diagnostics, Context, []),

    % Generate code actions for refinement type diagnostics
    Actions = lists:flatmap(
        fun(Diagnostic) ->
            Code = maps:get(code, Diagnostic, <<>>),
            case is_refinement_diagnostic(Code) of
                true ->
                    cure_lsp_smt:generate_code_actions(Diagnostic, Uri);
                false ->
                    []
            end
        end,
        Diagnostics
    ),

    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => Actions
    },
    send_message(Response, State),
    State.

%% Check if a diagnostic code is from refinement type checking
is_refinement_diagnostic(<<"refinement_", _/binary>>) -> true;
is_refinement_diagnostic(_) -> false.

apply_changes(Text, Changes) ->
    lists:foldl(fun apply_single_change/2, Text, Changes).

%% Apply a single change to the document
%% For full document sync (mode 1), changes contain the entire new text
%% For incremental sync (mode 2), changes contain a range and text to replace
apply_single_change(Change, Text) ->
    case maps:get(range, Change, undefined) of
        undefined ->
            % Full document replacement
            maps:get(text, Change, Text);
        Range ->
            % Incremental change - apply range-based edit
            StartPos = maps:get(start, Range),
            EndPos = maps:get('end', Range),
            NewText = maps:get(text, Change, <<>>),
            apply_range_change(Text, StartPos, EndPos, NewText)
    end.

%% Apply a range-based change to text
apply_range_change(Text, StartPos, EndPos, NewText) ->
    StartLine = maps:get(line, StartPos),
    StartChar = maps:get(character, StartPos),
    EndLine = maps:get('end', EndPos, maps:get(line, EndPos)),
    EndChar = maps:get(character, EndPos),

    % Split text into lines
    Lines = binary:split(Text, <<"\n">>, [global]),

    % Apply the change
    apply_range_change_to_lines(Lines, StartLine, StartChar, EndLine, EndChar, NewText).

%% Apply range change to lines
apply_range_change_to_lines(Lines, StartLine, StartChar, EndLine, EndChar, NewText) ->
    {BeforeLines, Rest1} = lists:split(StartLine, Lines),
    [StartLineText | AfterStart] = Rest1,

    % Handle same-line or multi-line change
    {AfterLines, EndLineText} =
        if
            StartLine =:= EndLine ->
                % Same line change
                {AfterStart, StartLineText};
            true ->
                % Multi-line change
                {_Skipped, After} = lists:split(EndLine - StartLine, AfterStart),
                [EndLine_ | RestAfter] = After,
                {RestAfter, EndLine_}
        end,

    % Extract parts of affected lines
    BeforePart = binary:part(StartLineText, 0, StartChar),
    AfterPart = binary:part(EndLineText, EndChar, byte_size(EndLineText) - EndChar),

    % Combine with new text
    NewLines = [BeforePart, NewText, AfterPart],
    NewLine = iolist_to_binary(NewLines),

    % Reconstruct document
    AllLines = BeforeLines ++ [NewLine | AfterLines],
    iolist_to_binary(lists:join(<<"\n">>, AllLines)).

diagnose_document(Uri, Text, State) ->
    % Run lexer and parser to get basic diagnostics
    BasicDiagnostics = cure_lsp_analyzer:analyze(Text),

    % Run SMT verification for refinement type checking
    {SmtDiagnostics, NewSmtState} = run_smt_verification(Uri, Text, State#state.smt_state),

    % Combine all diagnostics
    AllDiagnostics = BasicDiagnostics ++ SmtDiagnostics,

    Message = #{
        jsonrpc => <<"2.0">>,
        method => <<"textDocument/publishDiagnostics">>,
        params => #{
            uri => Uri,
            diagnostics => AllDiagnostics
        }
    },

    send_message(Message, State),

    % Return updated state with new SMT state
    State#state{smt_state = NewSmtState}.

send_empty_diagnostics(Uri, State) ->
    Message = #{
        jsonrpc => <<"2.0">>,
        method => <<"textDocument/publishDiagnostics">>,
        params => #{
            uri => Uri,
            diagnostics => []
        }
    },
    send_message(Message, State).

%% Run SMT verification on document
run_smt_verification(Uri, Text, SmtState) ->
    try
        % Parse document to get AST for SMT verification
        TextBin =
            if
                is_binary(Text) -> Text;
                is_list(Text) -> list_to_binary(Text);
                true -> <<>>
            end,

        case cure_lexer:tokenize(TextBin) of
            {ok, Tokens} ->
                case cure_parser:parse(Tokens) of
                    {ok, AST} ->
                        % Run incremental SMT verification
                        cure_lsp_smt:verify_document_incremental(SmtState, {Uri, AST});
                    {error, _ParseError} ->
                        % Parse error - no SMT diagnostics
                        {[], SmtState}
                end;
            {error, _LexError} ->
                % Lex error - no SMT diagnostics
                {[], SmtState}
        end
    catch
        _Error:_Reason:_Stack ->
            % SMT verification failed - return no diagnostics, keep old state
            {[], SmtState}
    end.

%% Extract text from content changes (for fallback)
get_text_from_changes([]) ->
    <<>>;
get_text_from_changes([Change | _]) ->
    % For full document sync, the first change contains the full text
    maps:get(text, Change, <<>>).

update_symbols(Uri, Text, SymbolTable) ->
    % Parse the document and update symbol table
    TextBin =
        if
            is_binary(Text) -> Text;
            is_list(Text) -> list_to_binary(Text);
            true -> <<>>
        end,
    case cure_lexer:tokenize(TextBin) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, AST} ->
                    cure_lsp_symbols:add_module(SymbolTable, Uri, AST);
                _ ->
                    SymbolTable
            end;
        _ ->
            SymbolTable
    end.

stdin_reader() ->
    % Open stdin as a port to read binary data
    Port = open_port({fd, 0, 1}, [stream, binary, eof]),
    stdin_reader_loop(Port).

stdin_reader_loop(Port) ->
    receive
        {Port, {data, Data}} ->
            ?MODULE ! {stdin, Data},
            stdin_reader_loop(Port);
        {Port, eof} ->
            io:format(standard_error, "stdin EOF~n", []),
            ok;
        Other ->
            io:format(standard_error, "stdin_reader unexpected: ~p~n", [Other]),
            stdin_reader_loop(Port)
    end.
