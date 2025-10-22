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
    diagnostics = #{} :: map()
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
    State = #state{transport = Transport},
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
        {ok, jsx:decode(Binary, [return_maps, {labels, atom}])}
    catch
        _:Error ->
            {error, Error}
    end.

encode_json(Term) ->
    jsx:encode(Term).

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
                    % Incremental
                    change => 2,
                    save => #{includeText => true}
                },
                completionProvider => #{
                    triggerCharacters => [<<".">>, <<":">>]
                },
                hoverProvider => true,
                definitionProvider => true,
                referencesProvider => true,
                documentSymbolProvider => true,
                workspaceSymbolProvider => true
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

    NewState = State#state{
        documents = maps:put(Uri, Doc, State#state.documents)
    },

    % Run diagnostics
    diagnose_document(Uri, Text, NewState),
    NewState.

handle_did_change(Params, State) ->
    TextDocument = maps:get(textDocument, Params),
    Uri = maps:get(uri, TextDocument),
    Version = maps:get(version, TextDocument),
    ContentChanges = maps:get(contentChanges, Params),

    case maps:get(Uri, State#state.documents, undefined) of
        undefined ->
            State;
        Doc ->
            % Apply incremental changes
            NewText = apply_changes(maps:get(text, Doc), ContentChanges),
            NewDoc = Doc#{text => NewText, version => Version},

            NewState = State#state{
                documents = maps:put(Uri, NewDoc, State#state.documents)
            },

            % Run diagnostics
            diagnose_document(Uri, NewText, NewState),
            NewState
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

handle_completion(Id, _Params, State) ->
    % Placeholder for completion logic
    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => []
    },
    send_message(Response, State),
    State.

handle_hover(Id, _Params, State) ->
    % Placeholder for hover logic
    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => null
    },
    send_message(Response, State),
    State.

handle_definition(Id, _Params, State) ->
    % Placeholder for definition logic
    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => null
    },
    send_message(Response, State),
    State.

handle_references(Id, _Params, State) ->
    % Placeholder for references logic
    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => []
    },
    send_message(Response, State),
    State.

handle_document_symbol(Id, _Params, State) ->
    % Placeholder for document symbol logic
    Response = #{
        jsonrpc => <<"2.0">>,
        id => Id,
        result => []
    },
    send_message(Response, State),
    State.

apply_changes(Text, Changes) ->
    lists:foldl(fun apply_single_change/2, Text, Changes).

apply_single_change(Change, Text) ->
    maps:get(text, Change, Text).

diagnose_document(Uri, Text, State) ->
    % Run lexer and parser to get diagnostics
    Diagnostics = cure_lsp_analyzer:analyze(Text),

    Message = #{
        jsonrpc => <<"2.0">>,
        method => <<"textDocument/publishDiagnostics">>,
        params => #{
            uri => Uri,
            diagnostics => Diagnostics
        }
    },

    send_message(Message, State).

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
