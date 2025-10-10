%% Cure Programming Language - Standard Library Runtime
%% Provides core functions and types used by compiled Cure programs
-module(cure_std).

%% Core utility functions that cannot be implemented in Cure itself
%% (mainly Erlang interop and low-level runtime functions)
-export([
    % These remain in Erlang runtime as they need Erlang-specific features
    is_monad/1,
    pipe/2,
    print/1,
    println/1,
    fsm_create/2,
    fsm_send_safe/2,
    create_counter/1,
    list_to_string/1,
    join_ints/2,
    show/1
]).

% NOTE: Most standard library functions are now implemented in Cure itself (lib/std/)
% This module only contains runtime functions that require Erlang-specific features

%% ============================================================================
%% Runtime Helper Functions
%% ============================================================================

%% Helper: check if value is a Result (Ok/Error) - needed for pipe implementation
is_monad({'Ok', _}) ->
    true;
is_monad({'Error', _}) ->
    true;
is_monad(_) ->
    false.

%% Monadic-style pipe helper implementing the specified rules
%% pipe(LHO, RHO) where RHO is a function to call with the (possibly unwrapped) LHO
pipe({'Error', _} = Err, _RHO) ->
    % Rule 1: propagate error
    Err;
pipe({'Ok', V}, RHO) when is_function(RHO) ->
    % Rule 2: unwrap Ok(V), call RHO(V), wrap unless already a monad
    try
        Res = RHO(V),
        case is_monad(Res) of
            true -> Res;
            false -> {'Ok', Res}
        end
    catch
        Error:Reason -> {'Error', {pipe_runtime_error, Error, Reason}}
    end;
pipe(LHO, RHO) when is_function(RHO) ->
    % Rule 3: pass non-monad LHO to RHO, wrap unless already a monad
    try
        Res = RHO(LHO),
        case is_monad(Res) of
            true -> Res;
            false -> {'Ok', Res}
        end
    catch
        Error:Reason -> {'Error', {pipe_runtime_error, Error, Reason}}
    end.

%% ============================================================================
%% IO Operations
%% ============================================================================

%% Print without newline
print(Message) ->
    io:format("~ts", [Message]),
    ok.

%% Print with newline
println(Message) ->
    io:format("~ts~n", [Message]),
    ok.

%% ============================================================================
%% FSM Operations (Simplified Implementation)
%% ============================================================================

%% Create FSM (simplified)
fsm_create(_FSMType, _InitialState) ->
    % In a real implementation, this would create an actual FSM process
    {'Ok', make_ref()}.

%% Send message to FSM safely
fsm_send_safe(_FSMRef, _Message) ->
    % In a real implementation, this would send message to FSM process
    {'Ok', ok}.

%% Create counter FSM
create_counter(InitialValue) ->
    fsm_create(counter, InitialValue).

%% ============================================================================
%% Utility Functions
%% ============================================================================

%% Convert list of integers to string representation
list_to_string(List) ->
    "[" ++ join_ints(List, ", ") ++ "]".

%% Join integers with separator
join_ints([], _Sep) ->
    "";
join_ints([X], _Sep) ->
    integer_to_list(X);
join_ints([X | Rest], Sep) ->
    integer_to_list(X) ++ Sep ++ join_ints(Rest, Sep).

%% Show function - converts values to string representation
show({'Ok', Value}) ->
    "Ok(" ++ show(Value) ++ ")";
show({'Error', Reason}) ->
    "Error(" ++ show(Reason) ++ ")";
show({'Some', Value}) ->
    "Some(" ++ show(Value) ++ ")";
show('None') ->
    "None";
show(Value) when is_atom(Value) ->
    atom_to_list(Value);
show(Value) when is_integer(Value) ->
    integer_to_list(Value);
show(Value) when is_float(Value) ->
    float_to_list(Value);
show(Value) when is_list(Value) ->
    "[" ++ string:join([show(Item) || Item <- Value], ", ") ++ "]";
show(Value) when is_tuple(Value) ->
    case tuple_size(Value) of
        0 ->
            "{}";
        1 ->
            "{" ++ show(element(1, Value)) ++ "}";
        2 ->
            "{" ++ show(element(1, Value)) ++ ", " ++ show(element(2, Value)) ++ "}";
        3 ->
            "{" ++ show(element(1, Value)) ++ ", " ++ show(element(2, Value)) ++ ", " ++
                show(element(3, Value)) ++ "}";
        4 ->
            "{" ++ show(element(1, Value)) ++ ", " ++ show(element(2, Value)) ++ ", " ++
                show(element(3, Value)) ++ ", " ++ show(element(4, Value)) ++ "}";
        _ ->
            "{" ++ show(element(1, Value)) ++ ", " ++ show(element(2, Value)) ++ ", " ++
                show(element(3, Value)) ++ ", " ++ show(element(4, Value)) ++ ", ...}"
    end;
show(_Value) ->
    "unknown".
