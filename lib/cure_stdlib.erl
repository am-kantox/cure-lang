%% Basic Cure Standard Library
%% Implements essential functions needed for std_demo.cure compilation
-module(cure_stdlib).

-export([
    % Result/Option types
    'Ok'/1, 'Error'/1, 'Some'/1, 'None'/0,
    
    % FSM operations
    fsm_create/2, fsm_send_safe/2, create_counter/1, safe_div/2,
    
    % Utility functions
    print/1
]).

%% ============================================================================
%% Result/Option types (represented as tagged tuples)
%% ============================================================================

%% Constructor functions for capitalized versions
'Ok'(Value) -> {'Ok', Value}.
'Error'(Reason) -> {'Error', Reason}.
'Some'(Value) -> {'Some', Value}.
'None'() -> 'None'.

%% ============================================================================
%% FSM operations (placeholder implementations)
%% ============================================================================

fsm_create(_Type, _InitialState) -> 'Ok'({'FsmPid', self()}).
fsm_send_safe(_Fsm, _Event) -> 'Ok'(sent).
create_counter(_InitialValue) -> 'Ok'({'Counter', 0}).

%% Safe division that returns Result type
safe_div(_Numerator, 0) -> {'Error', "Division by zero"};
safe_div(Numerator, Denominator) -> 'Ok'(Numerator / Denominator).

%% ============================================================================
%% Utility functions
%% ============================================================================

print(Message) ->
    io:format("~s~n", [Message]),
    ok.

