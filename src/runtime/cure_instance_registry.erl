-module(cure_instance_registry).
-behaviour(gen_server).

%% Typeclass Instance Registry
%%
%% This module implements a runtime registry for typeclass instances.
%% It allows:
%% - Registering typeclass instances when modules load
%% - Looking up instances by typeclass and type
%% - Resolving method implementations
%% - Caching for performance (< 100ns for cached lookups)

%% API
-export([
    start_link/0,
    register_instance/3,
    register_instance/4,
    lookup_instance/2,
    get_method/3,
    get_all_instances/1,
    clear_cache/0,
    stop/0
]).

%% Export record and types for use by other modules
-export_type([
    instance_entry/0,
    typeclass/0,
    type_key/0,
    compiled_method/0
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

-define(SERVER, ?MODULE).
-define(CACHE_TABLE, cure_instance_cache).

%% ============================================================================
%% Type Definitions
%% ============================================================================

-record(state, {
    instances = #{} :: instances_map(),
    index = #{} :: instance_index(),
    stats = #{} :: stats_map()
}).

-type instances_map() :: #{{typeclass(), type_key()} => instance_entry()}.
-type instance_index() :: #{typeclass() => [type_key()]}.
-type stats_map() :: #{atom() => integer()}.

-record(instance_entry, {
    typeclass :: atom(),
    type_key :: term(),
    methods :: #{atom() => compiled_method()},
    priority = 100 :: integer(),
    registered_at :: erlang:timestamp()
}).

-type typeclass() :: atom().
-type type_key() :: term().
-type compiled_method() :: {module(), atom(), arity()}.
-type instance_entry() :: #instance_entry{}.

%% ============================================================================
%% API Functions
%% ============================================================================

-spec start_link() -> {ok, pid()} | {error, term()}.
start_link() ->
    gen_server:start_link({local, ?SERVER}, ?MODULE, [], []).

-spec register_instance(typeclass(), term(), #{atom() => compiled_method()}) ->
    ok | {error, term()}.
register_instance(Typeclass, Type, Methods) ->
    register_instance(Typeclass, Type, Methods, 100).

-spec register_instance(typeclass(), term(), #{atom() => compiled_method()}, integer()) ->
    ok | {error, term()}.
register_instance(Typeclass, Type, Methods, Priority) ->
    gen_server:call(?SERVER, {register_instance, Typeclass, Type, Methods, Priority}).

-spec lookup_instance(typeclass(), term()) -> {ok, instance_entry()} | not_found.
lookup_instance(Typeclass, Type) ->
    TypeKey = normalize_type(Type),
    CacheKey = {Typeclass, TypeKey},

    % Try cache first (ETS lookup is very fast)
    case ets:lookup(?CACHE_TABLE, CacheKey) of
        [{_, Entry}] ->
            {ok, Entry};
        [] ->
            % Cache miss - call gen_server
            case gen_server:call(?SERVER, {lookup_instance, Typeclass, TypeKey}) of
                {ok, Entry} = Result ->
                    % Cache the result
                    ets:insert(?CACHE_TABLE, {CacheKey, Entry}),
                    Result;
                not_found = Result ->
                    Result
            end
    end.

-spec get_method(typeclass(), atom(), term()) -> {ok, compiled_method()} | {error, term()}.
get_method(Typeclass, MethodName, ReceiverType) ->
    case lookup_instance(Typeclass, ReceiverType) of
        {ok, #instance_entry{methods = Methods}} ->
            case maps:get(MethodName, Methods, undefined) of
                undefined ->
                    {error, {method_not_found, MethodName, Typeclass, ReceiverType}};
                Method ->
                    {ok, Method}
            end;
        not_found ->
            {error, {no_instance, Typeclass, ReceiverType}}
    end.

-spec get_all_instances(typeclass()) -> [instance_entry()].
get_all_instances(Typeclass) ->
    gen_server:call(?SERVER, {get_all_instances, Typeclass}).

-spec clear_cache() -> ok.
clear_cache() ->
    ets:delete_all_objects(?CACHE_TABLE),
    ok.

-spec stop() -> ok.
stop() ->
    gen_server:stop(?SERVER).

%% ============================================================================
%% gen_server Callbacks
%% ============================================================================

init([]) ->
    % Create ETS table for caching
    ?CACHE_TABLE = ets:new(?CACHE_TABLE, [
        named_table,
        public,
        set,
        {read_concurrency, true},
        {write_concurrency, true}
    ]),

    {ok, #state{
        instances = #{},
        index = #{},
        stats = #{
            registrations => 0,
            lookups => 0,
            cache_hits => 0,
            cache_misses => 0
        }
    }}.

handle_call({register_instance, Typeclass, Type, Methods, Priority}, _From, State) ->
    TypeKey = normalize_type(Type),

    % Check for duplicate registration
    InstanceKey = {Typeclass, TypeKey},
    case maps:is_key(InstanceKey, State#state.instances) of
        true ->
            {reply, {error, {duplicate_instance, Typeclass, TypeKey}}, State};
        false ->
            % Create instance entry
            Entry = #instance_entry{
                typeclass = Typeclass,
                type_key = TypeKey,
                methods = Methods,
                priority = Priority,
                registered_at = erlang:timestamp()
            },

            % Update instances map
            NewInstances = maps:put(InstanceKey, Entry, State#state.instances),

            % Update index
            CurrentTypes = maps:get(Typeclass, State#state.index, []),
            NewIndex = maps:put(Typeclass, [TypeKey | CurrentTypes], State#state.index),

            % Invalidate cache for this typeclass/type combination
            ets:delete(?CACHE_TABLE, InstanceKey),

            % Update stats
            Stats = State#state.stats,
            NewStats = maps:update_with(registrations, fun(N) -> N + 1 end, 1, Stats),

            NewState = State#state{
                instances = NewInstances,
                index = NewIndex,
                stats = NewStats
            },

            {reply, ok, NewState}
    end;
handle_call({lookup_instance, Typeclass, TypeKey}, _From, State) ->
    InstanceKey = {Typeclass, TypeKey},

    % Update lookup stats
    Stats = State#state.stats,
    NewStats = maps:update_with(lookups, fun(N) -> N + 1 end, 1, Stats),
    NewState = State#state{stats = NewStats},

    case maps:get(InstanceKey, State#state.instances, undefined) of
        undefined ->
            {reply, not_found, NewState};
        Entry ->
            {reply, {ok, Entry}, NewState}
    end;
handle_call({get_all_instances, Typeclass}, _From, State) ->
    TypeKeys = maps:get(Typeclass, State#state.index, []),

    Instances = lists:filtermap(
        fun(TypeKey) ->
            case maps:get({Typeclass, TypeKey}, State#state.instances, undefined) of
                undefined -> false;
                Entry -> {true, Entry}
            end
        end,
        TypeKeys
    ),

    % Sort by priority (highest first)
    SortedInstances = lists:sort(
        fun(#instance_entry{priority = P1}, #instance_entry{priority = P2}) ->
            P1 >= P2
        end,
        Instances
    ),

    {reply, SortedInstances, State};
handle_call(_Request, _From, State) ->
    {reply, {error, unknown_request}, State}.

handle_cast(_Request, State) ->
    {noreply, State}.

handle_info(_Info, State) ->
    {noreply, State}.

terminate(_Reason, _State) ->
    % Clean up ETS table
    catch ets:delete(?CACHE_TABLE),
    ok.

code_change(_OldVsn, State, _Extra) ->
    {ok, State}.

%% ============================================================================
%% Internal Functions
%% ============================================================================

%% Normalize type representation for consistent lookup
normalize_type({primitive_type, Name}) ->
    {primitive, Name};
normalize_type({dependent_type, Name, _Params}) ->
    % For now, just use the constructor name
    % In full implementation, would include parameter types
    {dependent, Name};
normalize_type({record_type, Name}) ->
    {record, Name};
normalize_type({record_type, Name, _Fields}) ->
    {record, Name};
normalize_type({tuple_type, Types}) when is_list(Types) ->
    {tuple, length(Types)};
normalize_type({list_type, _ElemType, _Len}) ->
    {dependent, 'List'};
normalize_type({function_type, Params, _Return}) ->
    {function, length(Params)};
normalize_type(Type) when is_atom(Type) ->
    {primitive, Type};
normalize_type(Type) ->
    % Fallback: use the type as-is
    Type.
