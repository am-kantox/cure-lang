%% Cure Programming Language - SMT Solver Process Manager
%% Manages Z3/CVC5 solver processes with port-based communication
-module(cure_smt_process).

-moduledoc """
# Cure SMT Solver Process Manager

Manages external SMT solver processes (Z3, CVC5) using Erlang ports.
Provides process pooling, timeout enforcement, and resource management.

## Features

- Port-based communication with solvers
- Process pool for performance
- Timeout enforcement
- Automatic crash recovery
- Resource limits
- Query execution with model extraction

## Usage

```erlang
% Start a solver
{ok, Pid} = cure_smt_process:start_solver(z3, 5000).

% Execute a query
Query = \"(set-logic QF_LIA)\\n(check-sat)\\n\",
{sat, Lines} = cure_smt_process:execute_query(Pid, Query).

% Stop solver
cure_smt_process:stop_solver(Pid).
```
""".

-behaviour(gen_server).

%% Public API
-export([
    start_solver/2,
    start_solver/3,
    execute_query/2,
    execute_query/3,
    stop_solver/1,
    reset_solver/1,
    get_stats/1
]).

%% Process pool API
-export([
    start_pool/1,
    stop_pool/1,
    get_pooled_solver/2,
    return_solver/2
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

%% State record
-record(state, {
    port :: port() | undefined,
    solver :: z3 | cvc5,
    timeout :: integer(),
    query_count = 0 :: integer(),
    start_time :: integer(),
    buffer = <<>> :: binary()
}).

%% Pool state
-record(pool_state, {
    z3_available = [] :: [pid()],
    cvc5_available = [] :: [pid()],
    z3_in_use = [] :: [pid()],
    cvc5_in_use = [] :: [pid()],
    max_pool_size = 4 :: integer(),
    default_timeout = 5000 :: integer()
}).

%% ============================================================================
%% Public API
%% ============================================================================

-doc """
Start a solver process.

## Arguments
- `Solver` - Solver type (z3 or cvc5)
- `Timeout` - Query timeout in milliseconds

## Returns
- `{ok, Pid}` - Solver process PID
- `{error, Reason}` - Error starting solver
""".
-spec start_solver(z3 | cvc5, integer()) -> {ok, pid()} | {error, term()}.
start_solver(Solver, Timeout) ->
    start_solver(Solver, Timeout, []).

-spec start_solver(z3 | cvc5, integer(), list()) -> {ok, pid()} | {error, term()}.
start_solver(Solver, Timeout, Opts) ->
    gen_server:start_link(?MODULE, {Solver, Timeout, Opts}, []).

-doc """
Execute an SMT-LIB query on a solver process.

## Arguments
- `Pid` - Solver process PID
- `Query` - SMT-LIB query string or iolist

## Returns
- `{sat, Lines}` - Satisfiable with model lines
- `{unsat, []}` - Unsatisfiable
- `{unknown, []}` - Solver couldn't determine
- `{error, Reason}` - Execution error
""".
-spec execute_query(pid(), iolist()) ->
    {sat | unsat | unknown, [binary()]} | {error, term()}.
execute_query(Pid, Query) ->
    execute_query(Pid, Query, infinity).

-spec execute_query(pid(), iolist(), timeout()) ->
    {sat | unsat | unknown, [binary()]} | {error, term()}.
execute_query(Pid, Query, Timeout) ->
    gen_server:call(Pid, {execute_query, Query}, Timeout).

-doc """
Stop a solver process.
""".
-spec stop_solver(pid()) -> ok.
stop_solver(Pid) ->
    gen_server:stop(Pid).

-doc """
Reset a solver process (clear all assertions).
""".
-spec reset_solver(pid()) -> ok | {error, term()}.
reset_solver(Pid) ->
    gen_server:call(Pid, reset).

-doc """
Get solver statistics.
""".
-spec get_stats(pid()) -> map().
get_stats(Pid) ->
    gen_server:call(Pid, get_stats).

%% ============================================================================
%% Process Pool API
%% ============================================================================

-doc """
Start a solver process pool.
""".
-spec start_pool(map()) -> {ok, pid()}.
start_pool(Opts) ->
    gen_server:start_link({local, cure_smt_pool}, ?MODULE, {pool, Opts}, []).

-doc """
Stop the solver pool.
""".
-spec stop_pool(pid()) -> ok.
stop_pool(Pid) ->
    gen_server:stop(Pid).

-doc """
Get a solver from the pool.
""".
-spec get_pooled_solver(pid(), z3 | cvc5) -> {ok, pid()} | {error, term()}.
get_pooled_solver(PoolPid, Solver) ->
    gen_server:call(PoolPid, {get_solver, Solver}).

-doc """
Return a solver to the pool.
""".
-spec return_solver(pid(), pid()) -> ok.
return_solver(PoolPid, SolverPid) ->
    gen_server:cast(PoolPid, {return_solver, SolverPid}).

%% ============================================================================
%% gen_server callbacks
%% ============================================================================

init({Solver, Timeout, _Opts}) ->
    process_flag(trap_exit, true),

    case start_solver_port(Solver) of
        {ok, Port} ->
            State = #state{
                port = Port,
                solver = Solver,
                timeout = Timeout,
                start_time = erlang:monotonic_time(millisecond),
                buffer = <<>>
            },
            {ok, State};
        {error, Reason} ->
            {stop, Reason}
    end;
init({pool, Opts}) ->
    PoolState = #pool_state{
        max_pool_size = maps:get(max_pool_size, Opts, 4),
        default_timeout = maps:get(default_timeout, Opts, 5000)
    },
    {ok, PoolState}.

handle_call({execute_query, Query}, _From, State = #state{port = Port, timeout = Timeout}) ->
    % Send query to solver
    QueryBin = iolist_to_binary(Query),
    port_command(Port, QueryBin),

    % Receive response
    Result = receive_solver_response(Port, Timeout, State#state.buffer),

    % Always increment query count
    NewState = State#state{query_count = State#state.query_count + 1},

    case Result of
        {sat, Lines, NewBuffer} ->
            {reply, {sat, Lines}, NewState#state{buffer = NewBuffer}};
        {unsat, Lines, NewBuffer} ->
            {reply, {unsat, Lines}, NewState#state{buffer = NewBuffer}};
        {unknown, Lines, NewBuffer} ->
            {reply, {unknown, Lines}, NewState#state{buffer = NewBuffer}};
        {error, Reason} ->
            {reply, {error, Reason}, NewState}
    end;
handle_call(reset, _From, State = #state{port = Port}) ->
    % Send reset command
    port_command(Port, <<"(reset)\n">>),

    % Flush any pending messages
    flush_port_messages(Port),

    {reply, ok, State#state{buffer = <<>>}};
handle_call(get_stats, _From, State) ->
    Stats = #{
        solver => State#state.solver,
        query_count => State#state.query_count,
        uptime_ms => erlang:monotonic_time(millisecond) - State#state.start_time
    },
    {reply, Stats, State};
% Pool operations
handle_call({get_solver, z3}, _From, PoolState) ->
    case PoolState#pool_state.z3_available of
        [Pid | Rest] ->
            NewState = PoolState#pool_state{
                z3_available = Rest,
                z3_in_use = [Pid | PoolState#pool_state.z3_in_use]
            },
            {reply, {ok, Pid}, NewState};
        [] ->
            % Create new solver if under limit
            TotalZ3 = length(PoolState#pool_state.z3_in_use),
            if
                TotalZ3 < PoolState#pool_state.max_pool_size ->
                    case start_solver(z3, PoolState#pool_state.default_timeout) of
                        {ok, Pid} ->
                            NewState = PoolState#pool_state{
                                z3_in_use = [Pid | PoolState#pool_state.z3_in_use]
                            },
                            {reply, {ok, Pid}, NewState};
                        Error ->
                            {reply, Error, PoolState}
                    end;
                true ->
                    {reply, {error, pool_exhausted}, PoolState}
            end
    end;
handle_call({get_solver, cvc5}, _From, PoolState) ->
    case PoolState#pool_state.cvc5_available of
        [Pid | Rest] ->
            NewState = PoolState#pool_state{
                cvc5_available = Rest,
                cvc5_in_use = [Pid | PoolState#pool_state.cvc5_in_use]
            },
            {reply, {ok, Pid}, NewState};
        [] ->
            TotalCVC5 = length(PoolState#pool_state.cvc5_in_use),
            if
                TotalCVC5 < PoolState#pool_state.max_pool_size ->
                    case start_solver(cvc5, PoolState#pool_state.default_timeout) of
                        {ok, Pid} ->
                            NewState = PoolState#pool_state{
                                cvc5_in_use = [Pid | PoolState#pool_state.cvc5_in_use]
                            },
                            {reply, {ok, Pid}, NewState};
                        Error ->
                            {reply, Error, PoolState}
                    end;
                true ->
                    {reply, {error, pool_exhausted}, PoolState}
            end
    end.

handle_cast({return_solver, Pid}, PoolState) ->
    % Reset solver and return to pool
    catch reset_solver(Pid),

    % Determine which pool to return to
    case lists:member(Pid, PoolState#pool_state.z3_in_use) of
        true ->
            NewState = PoolState#pool_state{
                z3_in_use = lists:delete(Pid, PoolState#pool_state.z3_in_use),
                z3_available = [Pid | PoolState#pool_state.z3_available]
            },
            {noreply, NewState};
        false ->
            case lists:member(Pid, PoolState#pool_state.cvc5_in_use) of
                true ->
                    NewState = PoolState#pool_state{
                        cvc5_in_use = lists:delete(Pid, PoolState#pool_state.cvc5_in_use),
                        cvc5_available = [Pid | PoolState#pool_state.cvc5_available]
                    },
                    {noreply, NewState};
                false ->
                    {noreply, PoolState}
            end
    end.

handle_info({Port, {data, {eol, _Line}}}, State = #state{port = Port}) ->
    % Accumulate line in buffer (handled by receive_solver_response)
    {noreply, State};
handle_info({Port, {exit_status, Status}}, State = #state{port = Port}) ->
    cure_utils:debug("Solver exited with status ~p~n", [Status]),
    {stop, {solver_exit, Status}, State};
handle_info({'EXIT', Port, Reason}, State = #state{port = Port}) ->
    cure_utils:debug("Solver port exited: ~p~n", [Reason]),
    {stop, {port_exit, Reason}, State};
handle_info(_Info, State) ->
    {noreply, State}.

terminate(_Reason, #state{port = Port}) when Port =/= undefined ->
    catch port_close(Port),
    ok;
terminate(_Reason, _State) ->
    ok.

code_change(_OldVsn, State, _Extra) ->
    {ok, State}.

%% ============================================================================
%% Internal Functions
%% ============================================================================

%% Start solver port
start_solver_port(z3) ->
    case os:find_executable("z3") of
        false ->
            {error, z3_not_found};
        Z3Path ->
            try
                Port = open_port({spawn, Z3Path ++ " -smt2 -in"}, [
                    {line, 8192},
                    binary,
                    exit_status,
                    use_stdio,
                    hide
                ]),
                {ok, Port}
            catch
                error:Reason ->
                    {error, {port_open_failed, Reason}}
            end
    end;
start_solver_port(cvc5) ->
    case os:find_executable("cvc5") of
        false ->
            {error, cvc5_not_found};
        CVC5Path ->
            try
                Port = open_port({spawn, CVC5Path ++ " --lang smt2 --interactive"}, [
                    {line, 8192},
                    binary,
                    exit_status,
                    use_stdio,
                    hide
                ]),
                {ok, Port}
            catch
                error:Reason ->
                    {error, {port_open_failed, Reason}}
            end
    end.

%% Flush port messages
flush_port_messages(Port) ->
    receive
        {Port, {data, {eol, _}}} ->
            flush_port_messages(Port)
    after 10 ->
        ok
    end.

%% Receive solver response
receive_solver_response(Port, Timeout, Buffer) ->
    receive_solver_response(Port, Timeout, Buffer, [], none).

receive_solver_response(Port, Timeout, Buffer, Acc, Result) ->
    receive
        {Port, {data, {eol, Line}}} ->
            case Line of
                <<"sat">> when Result =:= none ->
                    % Got sat, wait briefly to see if model follows
                    receive
                        {Port, {data, {eol, NextLine}}} ->
                            case NextLine of
                                <<"(">> ->
                                    % Model starts
                                    receive_solver_response(Port, Timeout, Buffer, [NextLine], sat);
                                _ ->
                                    % No model, just sat
                                    {sat, [], Buffer}
                            end
                    after 100 ->
                        % No model came, query complete
                        {sat, [], Buffer}
                    end;
                <<"unsat">> ->
                    {unsat, lists:reverse(Acc), Buffer};
                <<"unknown">> ->
                    {unknown, lists:reverse(Acc), Buffer};
                _ ->
                    % Check if this is part of model
                    case {Result, Line} of
                        {sat, <<")">>} ->
                            % End of model
                            {sat, lists:reverse([Line | Acc]), Buffer};
                        {sat, _} ->
                            % Model line
                            receive_solver_response(Port, Timeout, Buffer, [Line | Acc], sat);
                        {none, _} ->
                            % Unexpected line before result
                            receive_solver_response(Port, Timeout, Buffer, [Line | Acc], none)
                    end
            end;
        {Port, {exit_status, Status}} ->
            {error, {solver_exit, Status}}
    after Timeout ->
        {error, timeout}
    end.
