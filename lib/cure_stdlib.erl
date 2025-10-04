%% Basic Cure Standard Library
%% Implements essential functions needed for std_demo.cure compilation
-module(cure_stdlib).

-export([
    % Result/Option types
    ok/1, error/1, some/1, none/0,
    
    % List operations
    map/2, filter/2, foldl/3, head/1, tail/1, length/1,
    
    % String operations
    string_concat/2, split/2, trim/1, to_upper/1,
    contains/2, starts_with/2,
    
    % Math operations
    abs/1, sqrt/1, pi/0,
    
    % FSM operations
    fsm_create/2, fsm_send_safe/2, create_counter/1,
    
    % Utility functions
    print/1, int_to_string/1, float_to_string/1, list_to_string/1,
    join_ints/2, string_empty/1, string_join/2
]).

%% ============================================================================
%% Result/Option types (represented as tagged tuples)
%% ============================================================================

ok(Value) -> {'Ok', Value}.
error(Reason) -> {'Error', Reason}.
some(Value) -> {'Some', Value}.
none() -> 'None'.

%% ============================================================================
%% List operations
%% ============================================================================

map(List, Fun) -> lists:map(Fun, List).
filter(List, Fun) -> lists:filter(Fun, List).
foldl(List, Acc, Fun) -> lists:foldl(Fun, Acc, List).
head([H|_]) -> H;
head([]) -> none().
tail([_|T]) -> T;
tail([]) -> [].
length(List) -> erlang:length(List).

%% ============================================================================
%% String operations
%% ============================================================================

% Note: ++ is handled as a built-in operator, not a function call
string_concat(Str1, Str2) -> Str1 ++ Str2.

split(String, Separator) ->
    % Simple implementation using string:split
    case string:split(String, Separator, all) of
        Result -> Result
    end.

trim(String) -> string:trim(String).
to_upper(String) -> string:uppercase(String).
contains(String, Substring) -> string:find(String, Substring) =/= nomatch.
starts_with(String, Prefix) -> string:prefix(String, Prefix) =/= nomatch.

%% ============================================================================
%% Math operations
%% ============================================================================

abs(N) -> erlang:abs(N).
sqrt(N) -> math:sqrt(N).
pi() -> math:pi().

%% ============================================================================
%% FSM operations (placeholder implementations)
%% ============================================================================

fsm_create(_Type, _InitialState) -> ok({'FsmPid', self()}).
fsm_send_safe(_Fsm, _Event) -> ok(sent).
create_counter(_InitialValue) -> ok({'Counter', 0}).

%% ============================================================================
%% Utility functions
%% ============================================================================

print(Message) ->
    io:format("~s~n", [Message]),
    ok.

int_to_string(Int) when is_integer(Int) -> integer_to_list(Int).
float_to_string(Float) when is_float(Float) -> float_to_list(Float).

list_to_string([]) -> "[]";
list_to_string(List) when is_list(List) ->
    "[" ++ join_ints(List, ", ") ++ "]".

join_ints([], _Separator) -> "";
join_ints([X], _Separator) when is_integer(X) -> integer_to_list(X);
join_ints([X|Rest], Separator) when is_integer(X) ->
    integer_to_list(X) ++ Separator ++ join_ints(Rest, Separator);
join_ints([_|Rest], Separator) ->
    "?" ++ Separator ++ join_ints(Rest, Separator).

string_empty("") -> true;
string_empty(_) -> false.

string_join([], _Separator) -> "";
string_join([H], _Separator) -> H;
string_join([H|T], Separator) -> H ++ Separator ++ string_join(T, Separator).