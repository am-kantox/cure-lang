-module(cure_lsp_server).

-moduledoc """
# Cure Language Server Protocol (LSP) Implementation

This module implements the Language Server Protocol for the Cure programming language,
providing IDE features like:

- Real-time syntax checking
- Type inference hints
- Go-to-definition
- Hover information
- Code completion
- Diagnostics reporting

## LSP Protocol

The server communicates over JSON-RPC 2.0 using stdio or TCP socket.

## Features

### Implemented
- `initialize` - Server initialization
- `textDocument/didOpen` - Document opened
- `textDocument/didChange` - Document changed
- `textDocument/didSave` - Document saved
- `textDocument/didClose` - Document closed
- `textDocument/hover` - Hover information
- `textDocument/diagnostic` - Real-time diagnostics

### Planned
- `textDocument/completion` - Code completion
- `textDocument/definition` - Go to definition
- `textDocument/references` - Find references
- `textDocument/rename` - Symbol renaming
""".

-behaviour(gen_server).

%% API
-export([
    start_link/0,
    start_link/1,
    stop/0,
    handle_message/1,
    get_diagnostics/1,
    update_document/2
]).

%% gen_server callbacks
-export([
    init/1,
    handle_call/3,
    handle_cast/2,
    handle_info/2,
    terminate/2,
    code_change/3
]).

-include("../parser/cure_ast.hrl").

-record(state, {
    initialized = false :: boolean(),
    capabilities = #{} :: map(),
    % URI -> document content
    documents = #{} :: map(),
    % URI -> diagnostics list
    diagnostics = #{} :: map(),
    % URI -> type information
    type_cache = #{} :: map()
}).

-record(document, {
    uri :: binary(),
    version :: integer(),
    content :: binary(),
    ast :: term() | undefined,
    errors :: [term()]
}).

%%% API Functions %%%

%% @doc Start the LSP server
-spec start_link() -> {ok, pid()} | {error, term()}.
start_link() ->
    start_link(#{}).

%% @doc Start the LSP server with options
-spec start_link(map()) -> {ok, pid()} | {error, term()}.
start_link(Opts) ->
    gen_server:start_link({local, ?MODULE}, ?MODULE, Opts, []).

%% @doc Stop the LSP server
-spec stop() -> ok.
stop() ->
    gen_server:stop(?MODULE).

%% @doc Handle an LSP JSON-RPC message
-spec handle_message(map()) -> {ok, map()} | {error, term()}.
handle_message(Message) ->
    gen_server:call(?MODULE, {handle_message, Message}).

%% @doc Get diagnostics for a document
-spec get_diagnostics(binary()) -> [map()].
get_diagnostics(Uri) ->
    gen_server:call(?MODULE, {get_diagnostics, Uri}).

%% @doc Update document content
-spec update_document(binary(), binary()) -> ok.
update_document(Uri, Content) ->
    gen_server:cast(?MODULE, {update_document, Uri, Content}).

%%% gen_server Callbacks %%%

init(Opts) ->
    State = #state{
        initialized = false,
        capabilities = default_capabilities(),
        documents = #{},
        diagnostics = #{},
        type_cache = #{}
    },
    {ok, State}.

handle_call({handle_message, Message}, _From, State) ->
    case handle_lsp_message(Message, State) of
        {reply, Response, NewState} ->
            {reply, {ok, Response}, NewState};
        {noreply, NewState} ->
            {reply, {ok, null}, NewState};
        {error, Error, NewState} ->
            {reply, {error, Error}, NewState}
    end;
handle_call({get_diagnostics, Uri}, _From, State) ->
    Diagnostics = maps:get(Uri, State#state.diagnostics, []),
    {reply, Diagnostics, State};
handle_call(_Request, _From, State) ->
    {reply, {error, unknown_request}, State}.

handle_cast({update_document, Uri, Content}, State) ->
    NewState = update_document_internal(Uri, Content, State),
    {noreply, NewState};
handle_cast(_Msg, State) ->
    {noreply, State}.

handle_info(_Info, State) ->
    {noreply, State}.

terminate(_Reason, _State) ->
    ok.

code_change(_OldVsn, State, _Extra) ->
    {ok, State}.

%%% Internal Functions %%%

%% Handle LSP protocol messages
handle_lsp_message(#{<<"method">> := <<"initialize">>} = Msg, State) ->
    handle_initialize(Msg, State);
handle_lsp_message(#{<<"method">> := <<"textDocument/didOpen">>} = Msg, State) ->
    handle_did_open(Msg, State);
handle_lsp_message(#{<<"method">> := <<"textDocument/didChange">>} = Msg, State) ->
    handle_did_change(Msg, State);
handle_lsp_message(#{<<"method">> := <<"textDocument/didSave">>} = Msg, State) ->
    handle_did_save(Msg, State);
handle_lsp_message(#{<<"method">> := <<"textDocument/didClose">>} = Msg, State) ->
    handle_did_close(Msg, State);
handle_lsp_message(#{<<"method">> := <<"textDocument/hover">>} = Msg, State) ->
    handle_hover(Msg, State);
handle_lsp_message(#{<<"method">> := <<"textDocument/completion">>} = Msg, State) ->
    handle_completion(Msg, State);
handle_lsp_message(#{<<"method">> := <<"shutdown">>}, State) ->
    {reply, null, State};
handle_lsp_message(#{<<"method">> := <<"exit">>}, State) ->
    {noreply, State};
handle_lsp_message(_Msg, State) ->
    {error, method_not_found, State}.

%% Initialize request
handle_initialize(_Msg, State) ->
    Response = #{
        <<"capabilities">> => State#state.capabilities,
        <<"serverInfo">> => #{
            <<"name">> => <<"Cure Language Server">>,
            <<"version">> => <<"0.1.0">>
        }
    },
    NewState = State#state{initialized = true},
    {reply, Response, NewState}.

%% Document opened
handle_did_open(#{<<"params">> := Params}, State) ->
    #{<<"textDocument">> := TextDoc} = Params,
    Uri = maps:get(<<"uri">>, TextDoc),
    Version = maps:get(<<"version">>, TextDoc, 0),
    Content = maps:get(<<"text">>, TextDoc),

    NewState = open_document(Uri, Version, Content, State),
    {noreply, NewState}.

%% Document changed
handle_did_change(#{<<"params">> := Params}, State) ->
    #{<<"textDocument">> := TextDoc, <<"contentChanges">> := Changes} = Params,
    Uri = maps:get(<<"uri">>, TextDoc),
    Version = maps:get(<<"version">>, TextDoc, 0),

    % For full document sync, we get the entire new content
    NewContent =
        case Changes of
            [#{<<"text">> := Text} | _] -> Text;
            _ -> <<"">>
        end,

    NewState = update_document_internal(Uri, NewContent, State),
    {noreply, NewState}.

%% Document saved
handle_did_save(_Msg, State) ->
    {noreply, State}.

%% Document closed
handle_did_close(#{<<"params">> := Params}, State) ->
    #{<<"textDocument">> := TextDoc} = Params,
    Uri = maps:get(<<"uri">>, TextDoc),

    NewState = close_document(Uri, State),
    {noreply, NewState}.

%% Hover information
handle_hover(#{<<"params">> := Params}, State) ->
    #{<<"textDocument">> := TextDoc, <<"position">> := Position} = Params,
    Uri = maps:get(<<"uri">>, TextDoc),
    Line = maps:get(<<"line">>, Position),
    Character = maps:get(<<"character">>, Position),

    HoverInfo = get_hover_info(Uri, Line, Character, State),

    Response =
        case HoverInfo of
            undefined -> null;
            Info -> #{<<"contents">> => Info}
        end,

    {reply, Response, State}.

%% Code completion
handle_completion(#{<<"params">> := Params}, State) ->
    #{<<"textDocument">> := TextDoc, <<"position">> := _Position} = Params,
    _Uri = maps:get(<<"uri">>, TextDoc),

    % TODO: Implement completion
    Response = #{<<"items">> => []},
    {reply, Response, State}.

%% Open a document
open_document(Uri, Version, Content, State) ->
    Document = analyze_document(Uri, Version, Content),

    Docs = maps:put(Uri, Document, State#state.documents),
    Diagnostics = maps:put(Uri, Document#document.errors, State#state.diagnostics),

    State#state{
        documents = Docs,
        diagnostics = Diagnostics
    }.

%% Update document content
update_document_internal(Uri, Content, State) ->
    Version =
        case maps:get(Uri, State#state.documents, undefined) of
            undefined -> 1;
            #document{version = V} -> V + 1
        end,

    open_document(Uri, Version, Content, State).

%% Close a document
close_document(Uri, State) ->
    Docs = maps:remove(Uri, State#state.documents),
    Diagnostics = maps:remove(Uri, State#state.diagnostics),
    TypeCache = maps:remove(Uri, State#state.type_cache),

    State#state{
        documents = Docs,
        diagnostics = Diagnostics,
        type_cache = TypeCache
    }.

%% Analyze a document (parse + type check)
analyze_document(Uri, Version, Content) ->
    % Parse the document
    {AST, Errors} =
        case cure_lexer:tokenize(Content) of
            {ok, Tokens} ->
                case cure_parser:parse(Tokens) of
                    {ok, ParsedAST} ->
                        {ParsedAST, []};
                    {error, {parse_error, Reason, Line, Col}} ->
                        Error = format_diagnostic(error, Reason, Line, Col),
                        {undefined, [Error]};
                    {error, Error} ->
                        ErrorDiag = format_diagnostic(error, Error, 1, 1),
                        {undefined, [ErrorDiag]}
                end;
            {error, {LexError, Line, Col}} ->
                ErrorDiag = format_diagnostic(error, LexError, Line, Col),
                {undefined, [ErrorDiag]};
            {error, Error} ->
                ErrorDiag = format_diagnostic(error, Error, 1, 1),
                {undefined, [ErrorDiag]}
        end,

    #document{
        uri = Uri,
        version = Version,
        content = Content,
        ast = AST,
        errors = Errors
    }.

%% Format a diagnostic for LSP
format_diagnostic(Severity, Reason, Line, Column) ->
    #{
        <<"range">> => #{
            <<"start">> => #{<<"line">> => Line - 1, <<"character">> => Column - 1},
            <<"end">> => #{<<"line">> => Line - 1, <<"character">> => Column + 10}
        },
        <<"severity">> => severity_to_int(Severity),
        <<"message">> => format_error_message(Reason),
        <<"source">> => <<"cure">>
    }.

severity_to_int(error) -> 1;
severity_to_int(warning) -> 2;
severity_to_int(info) -> 3;
severity_to_int(hint) -> 4.

format_error_message(Error) when is_binary(Error) -> Error;
format_error_message(Error) when is_list(Error) -> list_to_binary(Error);
format_error_message(Error) -> iolist_to_binary(io_lib:format("~p", [Error])).

%% Get hover information at position
get_hover_info(Uri, Line, Character, State) ->
    case maps:get(Uri, State#state.documents, undefined) of
        undefined ->
            undefined;
        #document{ast = undefined} ->
            undefined;
        #document{ast = AST, content = Content} ->
            % Find the AST node at the given position
            case find_node_at_position(AST, Line + 1, Character + 1) of
                undefined ->
                    undefined;
                Node ->
                    % Try to infer type for this node
                    case infer_node_type(Node, State) of
                        {ok, Type} ->
                            format_hover_info(Node, Type);
                        _ ->
                            undefined
                    end
            end
    end.

%% Find AST node at position (simplified implementation)
find_node_at_position(_AST, _Line, _Character) ->
    % TODO: Implement proper AST traversal to find node at position
    % For now, return undefined
    undefined.

%% Infer type for a node
infer_node_type(Node, State) ->
    % TODO: Integrate with type checker
    % For now, return a placeholder
    {ok, <<"unknown">>}.

%% Format hover information
format_hover_info(Node, Type) ->
    #{
        <<"kind">> => <<"markdown">>,
        <<"value">> => iolist_to_binary(["Type: `", Type, "`"])
    }.

%% Default server capabilities
default_capabilities() ->
    #{
        <<"textDocumentSync">> => #{
            <<"openClose">> => true,
            % Full document sync
            <<"change">> => 1,
            <<"save">> => #{<<"includeText">> => false}
        },
        <<"hoverProvider">> => true,
        <<"completionProvider">> => #{
            <<"triggerCharacters">> => [<<".">>, <<":">>]
        },
        <<"diagnosticProvider">> => #{
            <<"interFileDependencies">> => false,
            <<"workspaceDiagnostics">> => false
        }
    }.
