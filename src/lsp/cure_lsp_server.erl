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
    #{<<"textDocument">> := TextDoc, <<"position">> := Position} = Params,
    Uri = maps:get(<<"uri">>, TextDoc),
    Line = maps:get(<<"line">>, Position),
    Character = maps:get(<<"character">>, Position),

    % Get completion items based on context
    Items = get_completion_items(Uri, Line, Character, State),

    Response = #{<<"items">> => Items},
    {reply, Response, State}.

%% Get completion items at position
get_completion_items(Uri, _Line, _Character, State) ->
    case maps:get(Uri, State#state.documents, undefined) of
        undefined ->
            [];
        #document{ast = undefined} ->
            [];
        #document{ast = AST} ->
            % Collect completions from AST
            collect_completions(AST)
    end.

%% Collect completion items from AST
collect_completions(AST) when is_list(AST) ->
    lists:flatten(lists:map(fun collect_completions/1, AST));
collect_completions(#module_def{items = Items}) ->
    collect_completions(Items);
collect_completions(#function_def{name = Name, params = Params, return_type = RetType}) ->
    [create_completion_item(Name, function, format_function_signature(Name, Params, RetType))];
collect_completions(#type_def{name = Name, params = Params}) ->
    Detail =
        case Params of
            [] -> iolist_to_binary(["type ", atom_to_binary(Name, utf8)]);
            _ -> iolist_to_binary(["type ", atom_to_binary(Name, utf8), "(...)"])
        end,
    [create_completion_item(Name, type, Detail)];
collect_completions(#fsm_def{name = Name, states = States}) ->
    Item = create_completion_item(
        Name, fsm, iolist_to_binary(["fsm with ", integer_to_binary(length(States)), " states"])
    ),
    % Add state names as completions too
    StateItems = [create_completion_item(StateName, state, <<"state">>) || StateName <- States],
    [Item | StateItems];
collect_completions(#record_def{name = Name, fields = Fields}) ->
    Detail = iolist_to_binary(["record with ", integer_to_binary(length(Fields)), " fields"]),
    [create_completion_item(Name, record, Detail)];
collect_completions(#typeclass_def{name = Name, methods = Methods}) ->
    Detail = iolist_to_binary(["typeclass with ", integer_to_binary(length(Methods)), " methods"]),
    Item = create_completion_item(Name, typeclass, Detail),
    % Add method names as completions too
    MethodItems = [
        create_completion_item(MethodName, method, <<"method">>)
     || #method_signature{name = MethodName} <- Methods
    ],
    [Item | MethodItems];
collect_completions(#trait_def{name = Name, methods = Methods}) ->
    Detail = iolist_to_binary(["trait with ", integer_to_binary(length(Methods)), " methods"]),
    Item = create_completion_item(Name, trait, Detail),
    % Add method names as completions too
    MethodItems = [
        create_completion_item(MethodName, method, <<"method">>)
     || #method_signature{name = MethodName} <- Methods
    ],
    [Item | MethodItems];
collect_completions(#instance_def{typeclass = Typeclass}) ->
    Detail = iolist_to_binary(["instance ", atom_to_binary(Typeclass, utf8)]),
    [create_completion_item(Typeclass, instance, Detail)];
collect_completions(#trait_impl{trait_name = TraitName}) ->
    Detail = iolist_to_binary(["impl ", atom_to_binary(TraitName, utf8)]),
    [create_completion_item(TraitName, impl, Detail)];
collect_completions(_) ->
    [].

%% Create a completion item
create_completion_item(Name, Kind, Detail) ->
    #{
        <<"label">> => atom_to_binary(Name, utf8),
        <<"kind">> => completion_kind_to_int(Kind),
        <<"detail">> => Detail
    }.

%% Convert completion kind to LSP integer

% Function
completion_kind_to_int(function) -> 3;
% Struct (closest to type)
completion_kind_to_int(type) -> 22;
% Class (closest to FSM)
completion_kind_to_int(fsm) -> 5;
% Constant (for FSM states)
completion_kind_to_int(state) -> 13;
% Struct (for records)
completion_kind_to_int(record) -> 23;
% Interface (for typeclasses and traits)
completion_kind_to_int(typeclass) -> 11;
completion_kind_to_int(trait) -> 11;
% Method
completion_kind_to_int(method) -> 2;
% Class (for instances/impls)
completion_kind_to_int(instance) -> 5;
completion_kind_to_int(impl) -> 5;
% Text
completion_kind_to_int(_) -> 1.

%% Format function signature for completion
format_function_signature(Name, Params, RetType) ->
    ParamStr = format_params(Params),
    RetStr = format_type(RetType),
    iolist_to_binary(["def ", atom_to_binary(Name, utf8), "(", ParamStr, ") -> ", RetStr]).

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

%% Find AST node at position
%% Traverses the AST to find the most specific node at the given position
find_node_at_position(AST, Line, Character) when is_list(AST) ->
    % AST is a list of top-level items
    find_node_in_list(AST, Line, Character);
find_node_at_position(AST, Line, Character) ->
    % Single AST node
    find_node_in_item(AST, Line, Character).

%% Find node in a list of items
find_node_in_list([], _Line, _Character) ->
    undefined;
find_node_in_list([Item | Rest], Line, Character) ->
    case find_node_in_item(Item, Line, Character) of
        undefined -> find_node_in_list(Rest, Line, Character);
        Node -> Node
    end.

%% Find node in a specific AST item
find_node_in_item(#module_def{items = Items, location = Loc} = Node, Line, Character) ->
    case location_contains(Loc, Line, Character) of
        true ->
            % Check if any child item contains the position more specifically
            case find_node_in_list(Items, Line, Character) of
                % Return module if no more specific node found
                undefined -> Node;
                ChildNode -> ChildNode
            end;
        false ->
            undefined
    end;
find_node_in_item(#function_def{body = Body, location = Loc} = Node, Line, Character) ->
    case location_contains(Loc, Line, Character) of
        true ->
            % Check if body contains the position more specifically
            case find_node_in_expr(Body, Line, Character) of
                undefined -> Node;
                ChildNode -> ChildNode
            end;
        false ->
            undefined
    end;
find_node_in_item(#type_def{definition = Def, location = Loc} = Node, Line, Character) ->
    case location_contains(Loc, Line, Character) of
        true ->
            case find_node_in_type(Def, Line, Character) of
                undefined -> Node;
                ChildNode -> ChildNode
            end;
        false ->
            undefined
    end;
find_node_in_item(#fsm_def{state_defs = StateDefs, location = Loc} = Node, Line, Character) ->
    case location_contains(Loc, Line, Character) of
        true ->
            case find_node_in_list(StateDefs, Line, Character) of
                undefined -> Node;
                ChildNode -> ChildNode
            end;
        false ->
            undefined
    end;
find_node_in_item(#state_def{transitions = Trans, location = Loc} = Node, Line, Character) ->
    case location_contains(Loc, Line, Character) of
        true ->
            case find_node_in_list(Trans, Line, Character) of
                undefined -> Node;
                ChildNode -> ChildNode
            end;
        false ->
            undefined
    end;
find_node_in_item(_Node, _Line, _Character) ->
    undefined.

%% Find node in an expression
find_node_in_expr(undefined, _Line, _Character) ->
    undefined;
find_node_in_expr(#identifier_expr{location = Loc} = Node, Line, Character) ->
    case location_contains(Loc, Line, Character) of
        true -> Node;
        false -> undefined
    end;
find_node_in_expr(#literal_expr{location = Loc} = Node, Line, Character) ->
    case location_contains(Loc, Line, Character) of
        true -> Node;
        false -> undefined
    end;
find_node_in_expr(
    #function_call_expr{function = Func, args = Args, location = Loc} = Node, Line, Character
) ->
    case location_contains(Loc, Line, Character) of
        true ->
            % Check function and arguments
            case find_node_in_expr(Func, Line, Character) of
                undefined ->
                    case find_node_in_list(Args, Line, Character) of
                        undefined -> Node;
                        ArgNode -> ArgNode
                    end;
                FuncNode ->
                    FuncNode
            end;
        false ->
            undefined
    end;
find_node_in_expr(
    #binary_op_expr{left = Left, right = Right, location = Loc} = Node, Line, Character
) ->
    case location_contains(Loc, Line, Character) of
        true ->
            case find_node_in_expr(Left, Line, Character) of
                undefined ->
                    case find_node_in_expr(Right, Line, Character) of
                        undefined -> Node;
                        RightNode -> RightNode
                    end;
                LeftNode ->
                    LeftNode
            end;
        false ->
            undefined
    end;
find_node_in_expr(
    #let_expr{bindings = Bindings, body = Body, location = Loc} = Node, Line, Character
) ->
    case location_contains(Loc, Line, Character) of
        true ->
            case find_node_in_list(Bindings, Line, Character) of
                undefined ->
                    case find_node_in_expr(Body, Line, Character) of
                        undefined -> Node;
                        BodyNode -> BodyNode
                    end;
                BindingNode ->
                    BindingNode
            end;
        false ->
            undefined
    end;
find_node_in_expr(
    #match_expr{expr = Expr, patterns = Patterns, location = Loc} = Node, Line, Character
) ->
    case location_contains(Loc, Line, Character) of
        true ->
            case find_node_in_expr(Expr, Line, Character) of
                undefined ->
                    case find_node_in_list(Patterns, Line, Character) of
                        undefined -> Node;
                        PatternNode -> PatternNode
                    end;
                ExprNode ->
                    ExprNode
            end;
        false ->
            undefined
    end;
find_node_in_expr(#list_expr{elements = Elements, location = Loc} = Node, Line, Character) ->
    case location_contains(Loc, Line, Character) of
        true ->
            case find_node_in_list(Elements, Line, Character) of
                undefined -> Node;
                ElementNode -> ElementNode
            end;
        false ->
            undefined
    end;
find_node_in_expr(#tuple_expr{elements = Elements, location = Loc} = Node, Line, Character) ->
    case location_contains(Loc, Line, Character) of
        true ->
            case find_node_in_list(Elements, Line, Character) of
                undefined -> Node;
                ElementNode -> ElementNode
            end;
        false ->
            undefined
    end;
find_node_in_expr(_Node, _Line, _Character) ->
    undefined.

%% Find node in a type expression
find_node_in_type(#primitive_type{location = Loc} = Node, Line, Character) ->
    case location_contains(Loc, Line, Character) of
        true -> Node;
        false -> undefined
    end;
find_node_in_type(#dependent_type{params = Params, location = Loc} = Node, Line, Character) ->
    case location_contains(Loc, Line, Character) of
        true ->
            case find_node_in_list(Params, Line, Character) of
                undefined -> Node;
                ParamNode -> ParamNode
            end;
        false ->
            undefined
    end;
find_node_in_type(_Type, _Line, _Character) ->
    undefined.

%% Check if a location contains the given position
location_contains(undefined, _Line, _Character) ->
    false;
location_contains(#location{line = L, column = C}, Line, Character) when L =:= Line ->
    % Same line - check if character is at or after the column
    Character >= C;
location_contains(#location{line = L}, Line, _Character) when L =:= Line ->
    % Same line, assume it contains the position
    true;
location_contains(#location{line = L}, Line, _Character) when L < Line ->
    % Location line is before the target line - could contain if multi-line
    % For simplicity, assume single-line nodes for now
    false;
location_contains(_Location, _Line, _Character) ->
    false.

%% Infer type for a node
%% Provides basic type information based on AST node structure
infer_node_type(#literal_expr{value = Value}, _State) ->
    Type = infer_literal_type(Value),
    {ok, Type};
infer_node_type(#identifier_expr{name = Name}, State) ->
    % Try to find the identifier's type in scope
    % For now, return the identifier name with a type hint
    {ok, iolist_to_binary([atom_to_binary(Name, utf8), <<" :: unknown">>])};
infer_node_type(#function_def{name = Name, params = Params, return_type = RetType}, _State) ->
    % Format function signature
    ParamTypes = format_params(Params),
    ReturnType = format_type(RetType),
    Signature = iolist_to_binary([
        "def ", atom_to_binary(Name, utf8), "(", ParamTypes, ") -> ", ReturnType
    ]),
    {ok, Signature};
infer_node_type(#function_call_expr{function = #identifier_expr{name = Name}, args = Args}, _State) ->
    % Function call - show function name and arity
    Arity = length(Args),
    {ok, iolist_to_binary([atom_to_binary(Name, utf8), "/", integer_to_binary(Arity)])};
infer_node_type(#type_def{name = Name, params = Params}, _State) ->
    % Type definition
    case Params of
        [] ->
            {ok, iolist_to_binary(["type ", atom_to_binary(Name, utf8)])};
        _ ->
            ParamStr = format_type_params(Params),
            {ok, iolist_to_binary(["type ", atom_to_binary(Name, utf8), "(", ParamStr, ")"])}
    end;
infer_node_type(#primitive_type{name = TypeName}, _State) ->
    {ok, atom_to_binary(TypeName, utf8)};
infer_node_type(#dependent_type{name = TypeName, params = Params}, _State) ->
    ParamStr = format_type_params(Params),
    {ok, iolist_to_binary([atom_to_binary(TypeName, utf8), "(", ParamStr, ")"])};
infer_node_type(#binary_op_expr{op = Op, left = Left, right = Right}, State) ->
    % Binary operation - infer from operands
    case {infer_node_type(Left, State), infer_node_type(Right, State)} of
        {{ok, LeftType}, {ok, RightType}} ->
            {ok, iolist_to_binary([LeftType, " ", atom_to_binary(Op, utf8), " ", RightType])};
        _ ->
            {ok, iolist_to_binary(["(", atom_to_binary(Op, utf8), " expression)"])}
    end;
infer_node_type(#list_expr{}, _State) ->
    {ok, <<"List">>};
infer_node_type(#tuple_expr{elements = Elements}, _State) ->
    Size = length(Elements),
    {ok, iolist_to_binary(["Tuple(", integer_to_binary(Size), " elements)"])};
infer_node_type(#module_def{name = Name}, _State) ->
    {ok, iolist_to_binary(["module ", atom_to_binary(Name, utf8)])};
infer_node_type(#fsm_def{name = Name, states = States}, _State) ->
    StateCount = length(States),
    {ok,
        iolist_to_binary([
            "fsm ", atom_to_binary(Name, utf8), " (", integer_to_binary(StateCount), " states)"
        ])};
infer_node_type(_Node, _State) ->
    {ok, <<"unknown">>}.

%% Infer type from literal value
infer_literal_type(Value) when is_integer(Value) -> <<"Int">>;
infer_literal_type(Value) when is_float(Value) -> <<"Float">>;
infer_literal_type(Value) when is_binary(Value) -> <<"String">>;
infer_literal_type(Value) when is_atom(Value) ->
    case Value of
        true -> <<"Bool">>;
        false -> <<"Bool">>;
        unit -> <<"Unit">>;
        _ -> <<"Atom">>
    end;
infer_literal_type(_) ->
    <<"unknown">>.

%% Format function parameters
format_params(undefined) ->
    <<"">>;
format_params([]) ->
    <<"">>;
format_params(Params) when is_list(Params) ->
    ParamStrs = lists:map(fun format_param/1, Params),
    iolist_to_binary(lists:join(", ", ParamStrs));
format_params(_) ->
    <<"...">>.

format_param(#param{name = Name, type = Type}) ->
    TypeStr = format_type(Type),
    iolist_to_binary([atom_to_binary(Name, utf8), ": ", TypeStr]);
format_param(_) ->
    <<"_">>.

%% Format type expression
format_type(undefined) ->
    <<"_">>;
format_type(#primitive_type{name = Name}) ->
    atom_to_binary(Name, utf8);
format_type(#dependent_type{name = Name, params = Params}) ->
    ParamStr = format_type_params(Params),
    iolist_to_binary([atom_to_binary(Name, utf8), "(", ParamStr, ")"]);
format_type(#function_type{params = Params, return_type = RetType}) ->
    ParamStrs = lists:map(fun format_type/1, Params),
    ParamStr = iolist_to_binary(lists:join(", ", ParamStrs)),
    RetStr = format_type(RetType),
    iolist_to_binary(["fn(", ParamStr, ") -> ", RetStr]);
format_type(_) ->
    <<"unknown">>.

%% Format type parameters
format_type_params([]) ->
    <<"">>;
format_type_params(Params) when is_list(Params) ->
    ParamStrs = lists:map(fun format_type_param/1, Params),
    iolist_to_binary(lists:join(", ", ParamStrs));
format_type_params(_) ->
    <<"...">>.

format_type_param(#type_param{name = Name, value = Value}) when Name =/= undefined ->
    ValueStr = format_type(Value),
    iolist_to_binary([atom_to_binary(Name, utf8), ": ", ValueStr]);
format_type_param(#type_param{value = Value}) ->
    format_type(Value);
format_type_param(Atom) when is_atom(Atom) ->
    atom_to_binary(Atom, utf8);
format_type_param(_) ->
    <<"_">>.

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
