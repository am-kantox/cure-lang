%% Cure Programming Language - Standard Library Runtime
%% Provides core functions and types used by compiled Cure programs
-module(cure_std).

%% Core utility functions
-export([ok/1, error/1, some/1, none/0, is_ok/1, is_error/1, is_some/1, is_none/1,
         map_option/2, filter_option/2, get_option/2, map_ok/2, map_error/2, and_then/2, or_else/2,
         map/2, filter/2, foldl/3, foldr/3, head/1, tail/1, length/1, reverse/1, find/2, abs/1,
         sqrt/1, pi/0, safe_divide/2, safe_sqrt/1, gcd/2, factorial/1, string_concat/2, split/2,
         trim/1, to_upper/1, to_lower/1, contains/2, starts_with/2, ends_with/2, string_join/2,
         string_empty/1, int_to_string/1, float_to_string/1, string_to_int/1, string_to_float/1,
         print/1, println/1, fsm_create/2, fsm_send_safe/2, create_counter/1, list_to_string/1,
         join_ints/2]).

                           % Result and Option types

    % Option operations

    % Result operations

    % List operations

    % Math operations

    % String operations

    % Type conversion

    % IO operations

    % FSM operations

    % Utility functions

%% ============================================================================
%% Result and Option Types Implementation
%% ============================================================================

%% Create Ok result
ok(Value) ->
  {'Ok', Value}.

%% Create Error result
error(Reason) ->
  {'Error', Reason}.

%% Create Some option
some(Value) ->
  {'Some', Value}.

%% Create None option
none() ->
  'None'.

%% Type checking predicates
is_ok({'Ok', _}) ->
  true;
is_ok(_) ->
  false.

is_error({'Error', _}) ->
  true;
is_error(_) ->
  false.

is_some({'Some', _}) ->
  true;
is_some(_) ->
  false.

is_none('None') ->
  true;
is_none(_) ->
  false.

%% ============================================================================
%% Option Operations
%% ============================================================================

%% Map function over option value
map_option(F, {'Some', Value}) ->
  {'Some', F(Value)};
map_option(_F, 'None') ->
  'None'.

%% Filter option based on predicate
filter_option(Pred, {'Some', Value}) ->
  case Pred(Value) of
    true ->
      {'Some', Value};
    false ->
      'None'
  end;
filter_option(_Pred, 'None') ->
  'None'.

%% Get option value with default
get_option({'Some', Value}, _Default) ->
  Value;
get_option('None', Default) ->
  Default.

%% ============================================================================
%% Result Operations
%% ============================================================================

%% Map function over Ok result
map_ok(F, {'Ok', Value}) ->
  {'Ok', F(Value)};
map_ok(_F, Error) ->
  Error.

%% Map function over Error result
map_error(_F, {'Ok', _} = Ok) ->
  Ok;
map_error(F, {'Error', Reason}) ->
  {'Error', F(Reason)}.

%% Chain results (flatMap)
and_then(F, {'Ok', Value}) ->
  F(Value);
and_then(_F, Error) ->
  Error.

%% Use alternative on error
or_else(_F, {'Ok', _} = Ok) ->
  Ok;
or_else(F, {'Error', _Reason}) ->
  F().

%% ============================================================================
%% List Operations
%% ============================================================================

%% Map function over list
map(_F, []) ->
  [];
map(F, [H | T]) ->
  [F(H) | map(F, T)].

%% Filter list based on predicate
filter(_Pred, []) ->
  [];
filter(Pred, [H | T]) ->
  case Pred(H) of
    true ->
      [H | filter(Pred, T)];
    false ->
      filter(Pred, T)
  end.

%% Left fold over list
foldl(_F, Acc, []) ->
  Acc;
foldl(F, Acc, [H | T]) ->
  foldl(F, F(H, Acc), T).

%% Right fold over list
foldr(_F, Acc, []) ->
  Acc;
foldr(F, Acc, [H | T]) ->
  F(H, foldr(F, Acc, T)).

%% Get head of list
head([]) ->
  erlang:error("Empty list");
head([H | _]) ->
  H.

%% Get tail of list
tail([]) ->
  [];
tail([_ | T]) ->
  T.

%% Get length of list
length(List) ->
  erlang:length(List).

%% Reverse list
reverse(List) ->
  lists:reverse(List).

%% Find element in list
find(_Pred, []) ->
  'None';
find(Pred, [H | T]) ->
  case Pred(H) of
    true ->
      {'Some', H};
    false ->
      find(Pred, T)
  end.

%% ============================================================================
%% Math Operations
%% ============================================================================

%% Absolute value
abs(N) when N < 0 ->
  -N;
abs(N) ->
  N.

%% Square root
sqrt(N) when N >= 0 ->
  math:sqrt(N);
sqrt(_) ->
  erlang:error("Cannot take square root of negative number").

%% Pi constant
pi() ->
  math:pi().

%% Safe division
safe_divide(_X, 0) ->
  {'Error', "Division by zero"};
safe_divide(X, Y) ->
  {'Ok', X / Y}.

%% Safe square root
safe_sqrt(N) when N >= 0 ->
  {'Ok', math:sqrt(N)};
safe_sqrt(_) ->
  {'Error', "Cannot take square root of negative number"}.

%% Greatest common divisor
gcd(A, 0) ->
  erlang:abs(A);
gcd(A, B) ->
  gcd(B, A rem B).

%% Factorial
factorial(0) ->
  1;
factorial(N) when N > 0 ->
  N * factorial(N - 1);
factorial(_) ->
  erlang:error("Factorial of negative number").

%% ============================================================================
%% String Operations
%% ============================================================================

%% Concatenate strings
string_concat(S1, S2) ->
  S1 ++ S2.

%% Split string by separator
split(String, Sep) ->
  string:split(String, Sep, all).

%% Trim whitespace
trim(String) ->
  string:trim(String).

%% Convert to uppercase
to_upper(String) ->
  string:uppercase(String).

%% Convert to lowercase
to_lower(String) ->
  string:lowercase(String).

%% Check if string contains substring
contains(String, SubString) ->
  string:find(String, SubString) =/= nomatch.

%% Check if string starts with prefix
starts_with(String, Prefix) ->
  string:prefix(String, Prefix) =/= nomatch.

%% Check if string ends with suffix
ends_with(String, Suffix) ->
  erlang:length(String) >= erlang:length(Suffix) andalso lists:suffix(Suffix, String).

%% Join list of strings with separator
string_join([], _Sep) ->
  "";
string_join([H], _Sep) ->
  H;
string_join([H | T], Sep) ->
  H ++ Sep ++ string_join(T, Sep).

%% Check if string is empty
string_empty([]) ->
  true;
string_empty(_) ->
  false.

%% ============================================================================
%% Type Conversion
%% ============================================================================

%% Convert integer to string
int_to_string(N) ->
  integer_to_list(N).

%% Convert float to string
float_to_string(F) ->
  io_lib:format("~.2f", [F]).

%% Convert string to integer
string_to_int(S) ->
  try
    {'Ok', list_to_integer(S)}
  catch
    error:badarg ->
      {'Error', "Invalid integer format"}
  end.

%% Convert string to float
string_to_float(S) ->
  try
    {'Ok', list_to_float(S)}
  catch
    error:badarg ->
      {'Error', "Invalid float format"}
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
  int_to_string(X);
join_ints([X | Rest], Sep) ->
  int_to_string(X) ++ Sep ++ join_ints(Rest, Sep).
