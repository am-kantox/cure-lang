%% Cure FSM Action Compiler
%% Compiles FSM action blocks (from Mermaid-style syntax) into Erlang functions
-module(cure_fsm_action_compiler).

-export([compile_action/1, compile_action_to_fun/1]).

-include("../parser/cure_ast.hrl").
-include("../fsm/cure_fsm_runtime.hrl").

%% Compile an action block into an Erlang function
%% Action can be:
%% - {assign, VarName, ValueExpr, Location}
%% - {binary_op, Op, Left, Right, Location}
%% - {sequence, Actions, Location}
%% - undefined (no action)
compile_action(undefined) ->
    % No action - return identity function
    fun(State, _EventData) ->
        {State#fsm_state.data, State#fsm_state.payload}
    end;
compile_action({sequence, Actions, _Location}) ->
    % Multiple actions in sequence
    fun(State, EventData) ->
        Data = State#fsm_state.data,
        NewData = execute_action_sequence(Actions, Data, EventData),
        {NewData, State#fsm_state.payload}
    end;
compile_action(Action) ->
    % Single action
    fun(State, EventData) ->
        Data = State#fsm_state.data,
        NewData = execute_single_action(Action, Data, EventData),
        {NewData, State#fsm_state.payload}
    end.

%% Execute a sequence of actions
execute_action_sequence([], Data, _EventData) ->
    Data;
execute_action_sequence([Action | Rest], Data, EventData) ->
    NewData = execute_single_action(Action, Data, EventData),
    execute_action_sequence(Rest, NewData, EventData).

%% Execute a single action and return updated data
execute_single_action({assign, VarName, ValueExpr, _Location}, Data, EventData) ->
    Value = evaluate_action_value(ValueExpr, Data, EventData),
    maps:put(VarName, Value, Data);
execute_single_action(Action, Data, EventData) when is_tuple(Action) ->
    % Handle action tuples from parser
    case Action of
        {assign, VarName, ValueExpr, _Loc} ->
            Value = evaluate_action_value(ValueExpr, Data, EventData),
            maps:put(VarName, Value, Data);
        _ ->
            % Unknown action tuple, return data unchanged
            Data
    end;
execute_single_action(_Action, Data, _EventData) ->
    % For any other action format, return data unchanged
    Data.

%% Evaluate an action value expression
evaluate_action_value({binary_op, Op, Left, Right, _Location}, Data, EventData) ->
    LeftVal = evaluate_action_value(Left, Data, EventData),
    RightVal = evaluate_action_value(Right, Data, EventData),
    apply_binary_op(Op, LeftVal, RightVal);
evaluate_action_value({literal, Value, _Location}, _Data, _EventData) ->
    Value;
evaluate_action_value({state_var, VarName, _Location}, Data, _EventData) ->
    maps:get(VarName, Data, 0);
evaluate_action_value({identifier_expr, VarName, _Location}, Data, _EventData) ->
    maps:get(VarName, Data, 0);
evaluate_action_value(#identifier_expr{name = VarName}, Data, _EventData) ->
    maps:get(VarName, Data, 0);
evaluate_action_value(#literal_expr{value = Value}, _Data, _EventData) ->
    Value;
evaluate_action_value(#binary_op_expr{op = Op, left = Left, right = Right}, Data, EventData) ->
    LeftVal = evaluate_action_value(Left, Data, EventData),
    RightVal = evaluate_action_value(Right, Data, EventData),
    apply_binary_op(Op, LeftVal, RightVal);
evaluate_action_value(Value, _Data, _EventData) when is_integer(Value) ->
    Value;
evaluate_action_value(Value, _Data, _EventData) when is_atom(Value) ->
    % Could be a variable name - treat as 0 if not in data
    0;
evaluate_action_value(_Unknown, _Data, _EventData) ->
    0.

%% Apply binary operation
apply_binary_op('+', Left, Right) when is_number(Left), is_number(Right) -> Left + Right;
apply_binary_op('-', Left, Right) when is_number(Left), is_number(Right) -> Left - Right;
apply_binary_op('*', Left, Right) when is_number(Left), is_number(Right) -> Left * Right;
apply_binary_op('/', Left, Right) when is_number(Left), is_number(Right), Right =/= 0 ->
    Left / Right;
apply_binary_op('+', Left, Right) ->
    % Handle string concatenation or other types
    try_arithmetic('+', Left, Right);
apply_binary_op(Op, Left, Right) ->
    try_arithmetic(Op, Left, Right).

%% Try to coerce values to numbers for arithmetic
try_arithmetic('+', Left, Right) ->
    to_number(Left) + to_number(Right);
try_arithmetic('-', Left, Right) ->
    to_number(Left) - to_number(Right);
try_arithmetic('*', Left, Right) ->
    to_number(Left) * to_number(Right);
try_arithmetic('/', Left, Right) ->
    R = to_number(Right),
    case R of
        0 -> 0;
        _ -> to_number(Left) / R
    end;
try_arithmetic(_Op, Left, _Right) ->
    Left.

%% Convert value to number
to_number(N) when is_number(N) -> N;
to_number(true) -> 1;
to_number(false) -> 0;
to_number(_) -> 0.

%% Compile action to an Erlang abstract form (for direct code generation)
compile_action_to_fun(Action) ->
    % This creates an Erlang abstract syntax tree for a fun
    % For now, we'll use the runtime compilation approach above
    % and just return a placeholder that calls compile_action/1
    compile_action(Action).
