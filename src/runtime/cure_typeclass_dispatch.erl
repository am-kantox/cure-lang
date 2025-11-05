-module(cure_typeclass_dispatch).

%% Typeclass Method Dispatch
%%
%% This module provides runtime dispatch for typeclass method calls.
%% It supports:
%% - Dynamic method resolution based on runtime type inference
%% - High-performance caching using persistent_term
%% - Automatic fallback to slower gen_server lookup when cache misses
%%
%% Performance targets:
%% - Cached dispatch: < 100ns
%% - Uncached dispatch: < 1μs

-export([
    dispatch/4,
    dispatch_cached/4,
    call_method/3,
    infer_runtime_type/1,
    invalidate_cache/2,
    warm_cache/2
]).

-define(CACHE_KEY(TC, Method, Type), {cure_dispatch, TC, Method, Type}).

%% ============================================================================
%% API Functions
%% ============================================================================

%% @doc Dispatch a typeclass method call with runtime type inference
%% This is the main entry point for method dispatch.
-spec dispatch(atom(), atom(), term(), [term()]) -> term() | {error, term()}.
dispatch(Typeclass, Method, Receiver, Args) ->
    % Infer the runtime type of the receiver
    ReceiverType = infer_runtime_type(Receiver),

    % Try cached dispatch first
    case dispatch_cached(Typeclass, Method, ReceiverType, [Receiver | Args]) of
        {error, cache_miss} ->
            % Cache miss - do full lookup and dispatch
            case cure_instance_registry:get_method(Typeclass, Method, ReceiverType) of
                {ok, CompiledMethod} ->
                    % Cache the method for future calls
                    cache_method(Typeclass, Method, ReceiverType, CompiledMethod),
                    % Call the method
                    call_compiled_method(CompiledMethod, [Receiver | Args]);
                {error, _} = Error ->
                    Error
            end;
        Result ->
            Result
    end.

%% @doc Fast-path dispatch using persistent_term cache
%% Returns {error, cache_miss} if not in cache
-spec dispatch_cached(atom(), atom(), term(), [term()]) -> term() | {error, cache_miss}.
dispatch_cached(Typeclass, Method, ReceiverType, Args) ->
    CacheKey = ?CACHE_KEY(Typeclass, Method, ReceiverType),

    try persistent_term:get(CacheKey) of
        CompiledMethod ->
            call_compiled_method(CompiledMethod, Args)
    catch
        error:badarg ->
            % Not in cache
            {error, cache_miss}
    end.

%% @doc Call a typeclass method directly with a receiver value
%% Useful when you already know the method implementation
-spec call_method({module(), atom(), arity()}, term(), [term()]) -> term().
call_method({Module, Function, _Arity}, Receiver, Args) ->
    erlang:apply(Module, Function, [Receiver | Args]).

%% @doc Infer Cure type from Erlang runtime value
%% This allows dispatch to work with native Erlang values
-spec infer_runtime_type(term()) -> term().
infer_runtime_type(Value) when is_integer(Value) ->
    {primitive_type, 'Int'};
infer_runtime_type(Value) when is_float(Value) ->
    {primitive_type, 'Float'};
infer_runtime_type(Value) when is_boolean(Value) ->
    {primitive_type, 'Bool'};
infer_runtime_type(Value) when is_atom(Value) ->
    {primitive_type, 'Atom'};
infer_runtime_type(Value) when is_binary(Value) ->
    {primitive_type, 'String'};
infer_runtime_type([]) ->
    % Empty list - we don't know element type, use generic List
    {dependent_type, 'List', [{primitive_type, 'Any'}]};
infer_runtime_type([H | _] = Value) when is_list(Value) ->
    % Check if it's a printable string
    case io_lib:printable_list(Value) of
        true ->
            {primitive_type, 'String'};
        false ->
            % It's a list - infer element type from first element
            ElemType = infer_runtime_type(H),
            {dependent_type, 'List', [ElemType]}
    end;
infer_runtime_type(Value) when is_tuple(Value), tuple_size(Value) > 0 ->
    case element(1, Value) of
        Name when is_atom(Name) ->
            % Check if it's a record by seeing if it has the record name pattern
            % Records are tuples with an atom as first element
            case atom_to_list(Name) of
                [C | _] when C >= $a, C =< $z ->
                    % Looks like a record name (lowercase start)
                    {record_type, Name};
                _ ->
                    % Just a regular tuple
                    Elements = tuple_to_list(Value),
                    ElemTypes = [infer_runtime_type(E) || E <- Elements],
                    {tuple_type, ElemTypes}
            end;
        _ ->
            % Regular tuple
            Elements = tuple_to_list(Value),
            ElemTypes = [infer_runtime_type(E) || E <- Elements],
            {tuple_type, ElemTypes}
    end;
infer_runtime_type(Value) when is_function(Value) ->
    {arity, Arity} = erlang:fun_info(Value, arity),
    {function_type, lists:duplicate(Arity, {primitive_type, 'Any'}), {primitive_type, 'Any'}};
infer_runtime_type(Value) when is_map(Value) ->
    {map_type, {primitive_type, 'Any'}, {primitive_type, 'Any'}};
infer_runtime_type(_Value) ->
    % Unknown type
    {primitive_type, 'Any'}.

%% @doc Invalidate cached method for a typeclass/type combination
-spec invalidate_cache(atom(), term()) -> ok.
invalidate_cache(Typeclass, Type) ->
    % We need to invalidate all methods for this typeclass/type
    % Since we don't track which methods exist, we use a best-effort approach
    % In practice, this is called rarely (only when instances are redefined)

    % Get all instances for this typeclass
    Instances = cure_instance_registry:get_all_instances(Typeclass),

    % For each instance, invalidate its methods
    % instance_entry record: {instance_entry, Typeclass, TypeKey, Methods, Priority, RegisteredAt}
    lists:foreach(
        fun(InstanceEntry) ->
            TypeKey = element(3, InstanceEntry),
            Methods = element(4, InstanceEntry),
            case TypeKey =:= Type of
                true ->
                    maps:foreach(
                        fun(Method, _CompiledMethod) ->
                            CacheKey = ?CACHE_KEY(Typeclass, Method, Type),
                            catch persistent_term:erase(CacheKey)
                        end,
                        Methods
                    );
                false ->
                    ok
            end
        end,
        Instances
    ),
    ok.

%% @doc Pre-warm cache for a specific typeclass/type combination
%% Useful for hot paths where we want to ensure first call is fast
-spec warm_cache(atom(), term()) -> ok | {error, term()}.
warm_cache(Typeclass, Type) ->
    case cure_instance_registry:lookup_instance(Typeclass, Type) of
        {ok, InstanceEntry} ->
            % Extract methods from the instance entry tuple
            % instance_entry record: {instance_entry, Typeclass, TypeKey, Methods, Priority, RegisteredAt}
            Methods = element(4, InstanceEntry),
            maps:foreach(
                fun(Method, CompiledMethod) ->
                    cache_method(Typeclass, Method, Type, CompiledMethod)
                end,
                Methods
            ),
            ok;
        not_found ->
            {error, {no_instance, Typeclass, Type}}
    end.

%% ============================================================================
%% Internal Functions
%% ============================================================================

%% Cache a compiled method for fast lookup
cache_method(Typeclass, Method, Type, CompiledMethod) ->
    CacheKey = ?CACHE_KEY(Typeclass, Method, Type),
    persistent_term:put(CacheKey, CompiledMethod).

%% Call a compiled method (MFA tuple)
call_compiled_method({Module, Function, _Arity}, Args) ->
    erlang:apply(Module, Function, Args).
