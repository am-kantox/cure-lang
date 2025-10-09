%% Cure Programming Language - Action Compiler
%% Compiles FSM action expressions to BEAM bytecode instructions
-module(cure_action_compiler).

-export([
    compile_action/2,
    compile_actions/2,
    is_action_safe/1,
    analyze_action_safety/2,
    optimize_action/1
]).

-include("cure_codegen.hrl").

%% ============================================================================
%% Main Action Compilation Interface
%% ============================================================================

%% Compile a single action expression
compile_action(undefined, State) ->
    % No action - return unchanged state
    {ok,
        [
            #beam_instr{
                op = load_literal,
                args = [no_action],
                location = undefined
            }
        ],
        State};
compile_action(Action, State) ->
    case is_action_safe(Action) of
        true ->
            OptimizedAction = optimize_action(Action),
            compile_action_expr(OptimizedAction, State);
        false ->
            {error, {unsafe_action, Action}}
    end.

%% Compile multiple actions (for complex action sequences)
compile_actions([], State) ->
    {ok, [], State};
compile_actions(Actions, State) ->
    compile_actions_impl(Actions, [], State).

compile_actions_impl([], Acc, State) ->
    {ok, lists:flatten(lists:reverse(Acc)), State};
compile_actions_impl([Action | Rest], Acc, State) ->
    case compile_action(Action, State) of
        {ok, Instructions, NewState} ->
            compile_actions_impl(Rest, [Instructions | Acc], NewState);
        {error, Reason} ->
            {error, Reason}
    end.

%% ============================================================================
%% Action Expression Compilation
%% ============================================================================

%% Compile individual action expressions
compile_action_expr({assign, Variable, Value, Location}, State) ->
    % Compile value expression
    {ok, ValueInstr, State1} = compile_action_value(Value, State),

    % Generate assignment instruction
    AssignInstr = #beam_instr{
        op = assign_state_var,
        args = [Variable],
        location = Location
    },

    Instructions = ValueInstr ++ [AssignInstr],
    {ok, Instructions, State1};
compile_action_expr({update, Field, Value, Location}, State) ->
    % Compile value expression
    {ok, ValueInstr, State1} = compile_action_value(Value, State),

    % Generate field update instruction
    UpdateInstr = #beam_instr{
        op = update_state_field,
        args = [Field],
        location = Location
    },

    Instructions = ValueInstr ++ [UpdateInstr],
    {ok, Instructions, State1};
compile_action_expr({increment, Variable, Amount, Location}, State) ->
    % Load current value
    LoadInstr = #beam_instr{
        op = load_state_var,
        args = [Variable],
        location = Location
    },

    % Compile increment amount
    {ok, AmountInstr, State1} = compile_action_value(Amount, State),

    % Generate increment instruction
    IncrInstr = #beam_instr{
        op = binary_op,
        args = ['+'],
        location = Location
    },

    % Store result back
    StoreInstr = #beam_instr{
        op = assign_state_var,
        args = [Variable],
        location = Location
    },

    Instructions = [LoadInstr] ++ AmountInstr ++ [IncrInstr, StoreInstr],
    {ok, Instructions, State1};
compile_action_expr({decrement, Variable, Amount, Location}, State) ->
    % Similar to increment but with subtraction
    LoadInstr = #beam_instr{
        op = load_state_var,
        args = [Variable],
        location = Location
    },

    {ok, AmountInstr, State1} = compile_action_value(Amount, State),

    DecrInstr = #beam_instr{
        op = binary_op,
        args = ['-'],
        location = Location
    },

    StoreInstr = #beam_instr{
        op = assign_state_var,
        args = [Variable],
        location = Location
    },

    Instructions = [LoadInstr] ++ AmountInstr ++ [DecrInstr, StoreInstr],
    {ok, Instructions, State1};
compile_action_expr({emit, Event, Data, Location}, State) ->
    % Compile event data
    {ok, DataInstr, State1} =
        case Data of
            undefined -> {ok, [], State};
            _ -> compile_action_value(Data, State)
        end,

    % Generate event emission instruction
    EmitInstr = #beam_instr{
        op = emit_event,
        args = [Event, Data =/= undefined],
        location = Location
    },

    Instructions = DataInstr ++ [EmitInstr],
    {ok, Instructions, State1};
compile_action_expr({call, Function, Args, Location}, State) ->
    % Compile function arguments
    {ok, ArgInstructions, State1} = compile_action_values(Args, State),

    % Generate function call instruction
    CallInstr = #beam_instr{
        op = call_action_function,
        args = [Function, length(Args)],
        location = Location
    },

    Instructions = ArgInstructions ++ [CallInstr],
    {ok, Instructions, State1};
compile_action_expr({sequence, Actions, Location}, State) ->
    % Compile sequence of actions
    {ok, ActionInstructions, State1} = compile_actions(Actions, State),

    % Add sequence markers for debugging
    StartInstr = #beam_instr{
        op = action_sequence_start,
        args = [],
        location = Location
    },

    EndInstr = #beam_instr{
        op = action_sequence_end,
        args = [],
        location = Location
    },

    Instructions = [StartInstr] ++ ActionInstructions ++ [EndInstr],
    {ok, Instructions, State1};
compile_action_expr({if_then, Condition, ThenAction, ElseAction, Location}, State) ->
    % Compile condition (similar to guards)
    {ok, CondInstr, State1} = compile_action_condition(Condition, State),

    % Generate labels
    {ElseLabel, State2} = new_label(State1),
    {EndLabel, State3} = new_label(State2),

    % Compile then and else actions
    {ok, ThenInstr, State4} = compile_action(ThenAction, State3),
    {ok, ElseInstr, State5} =
        case ElseAction of
            undefined -> {ok, [], State4};
            _ -> compile_action(ElseAction, State4)
        end,

    Instructions =
        CondInstr ++
            [
                #beam_instr{op = jump_if_false, args = [ElseLabel], location = Location}
            ] ++ ThenInstr ++
            [
                #beam_instr{op = jump, args = [EndLabel], location = Location},
                #beam_instr{op = label, args = [ElseLabel], location = Location}
            ] ++ ElseInstr ++
            [
                #beam_instr{op = label, args = [EndLabel], location = Location}
            ],

    {ok, Instructions, State5};
compile_action_expr({log, Level, Message, Location}, State) ->
    % Compile log message
    {ok, MessageInstr, State1} = compile_action_value(Message, State),

    % Generate logging instruction
    LogInstr = #beam_instr{
        op = log_action,
        args = [Level],
        location = Location
    },

    Instructions = MessageInstr ++ [LogInstr],
    {ok, Instructions, State1};
compile_action_expr(Action, _State) ->
    {error, {unsupported_action, Action}}.

%% ============================================================================
%% Action Value Compilation
%% ============================================================================

%% Compile action values (expressions that produce values for actions)
compile_action_value({literal, Value, Location}, State) ->
    Instruction = #beam_instr{
        op = load_literal,
        args = [Value],
        location = Location
    },
    {ok, [Instruction], State};
compile_action_value({state_var, Variable, Location}, State) ->
    Instruction = #beam_instr{
        op = load_state_var,
        args = [Variable],
        location = Location
    },
    {ok, [Instruction], State};
compile_action_value({state_field, Field, Location}, State) ->
    Instruction = #beam_instr{
        op = load_state_field,
        args = [Field],
        location = Location
    },
    {ok, [Instruction], State};
compile_action_value({event_data, Location}, State) ->
    Instruction = #beam_instr{
        op = load_event_data,
        args = [],
        location = Location
    },
    {ok, [Instruction], State};
compile_action_value({current_state, Location}, State) ->
    Instruction = #beam_instr{
        op = load_current_state,
        args = [],
        location = Location
    },
    {ok, [Instruction], State};
compile_action_value({binary_op, Op, Left, Right, Location}, State) ->
    {ok, LeftInstr, State1} = compile_action_value(Left, State),
    {ok, RightInstr, State2} = compile_action_value(Right, State1),

    OpInstr = #beam_instr{
        op = binary_op,
        args = [Op],
        location = Location
    },

    Instructions = LeftInstr ++ RightInstr ++ [OpInstr],
    {ok, Instructions, State2};
compile_action_value({function_call, Function, Args, Location}, State) ->
    {ok, ArgInstructions, State1} = compile_action_values(Args, State),

    CallInstr = #beam_instr{
        op = call_function,
        args = [Function, length(Args)],
        location = Location
    },

    Instructions = ArgInstructions ++ [CallInstr],
    {ok, Instructions, State1};
compile_action_value(Value, _State) ->
    {error, {unsupported_action_value, Value}}.

%% Compile multiple action values
compile_action_values(Values, State) ->
    compile_action_values_impl(Values, [], State).

compile_action_values_impl([], Acc, State) ->
    {ok, lists:flatten(lists:reverse(Acc)), State};
compile_action_values_impl([Value | Rest], Acc, State) ->
    case compile_action_value(Value, State) of
        {ok, Instructions, NewState} ->
            compile_action_values_impl(Rest, [Instructions | Acc], NewState);
        {error, Reason} ->
            {error, Reason}
    end.

%% ============================================================================
%% Action Condition Compilation
%% ============================================================================

%% Compile action conditions (similar to guards but with access to action context)
compile_action_condition(Condition, State) ->
    % Delegate to guard compiler but allow additional action-specific operations
    case cure_guard_compiler:compile_guard(Condition, State) of
        {ok, Instructions, NewState} -> {ok, Instructions, NewState};
        {error, _} -> compile_action_specific_condition(Condition, State)
    end.

compile_action_specific_condition({state_changed, Variable, Location}, State) ->
    Instruction = #beam_instr{
        op = check_state_changed,
        args = [Variable],
        location = Location
    },
    {ok, [Instruction], State};
compile_action_specific_condition({event_matches, Pattern, Location}, State) ->
    Instruction = #beam_instr{
        op = check_event_matches,
        args = [Pattern],
        location = Location
    },
    {ok, [Instruction], State};
compile_action_specific_condition(Condition, _State) ->
    {error, {unsupported_action_condition, Condition}}.

%% ============================================================================
%% Action Safety Analysis
%% ============================================================================

%% Check if an action expression is safe to execute in FSM context
is_action_safe(undefined) ->
    true;
is_action_safe({assign, _Variable, Value, _Location}) ->
    is_action_value_safe(Value);
is_action_safe({update, _Field, Value, _Location}) ->
    is_action_value_safe(Value);
is_action_safe({increment, _Variable, Amount, _Location}) ->
    is_action_value_safe(Amount);
is_action_safe({decrement, _Variable, Amount, _Location}) ->
    is_action_value_safe(Amount);
is_action_safe({emit, _Event, Data, _Location}) ->
    case Data of
        undefined -> true;
        _ -> is_action_value_safe(Data)
    end;
is_action_safe({call, Function, Args, _Location}) ->
    is_safe_action_function(Function) andalso
        lists:all(fun is_action_value_safe/1, Args);
is_action_safe({sequence, Actions, _Location}) ->
    lists:all(fun is_action_safe/1, Actions);
is_action_safe({if_then, Condition, ThenAction, ElseAction, _Location}) ->
    is_action_condition_safe(Condition) andalso
        is_action_safe(ThenAction) andalso
        (ElseAction =:= undefined orelse is_action_safe(ElseAction));
is_action_safe({log, _Level, Message, _Location}) ->
    is_action_value_safe(Message);
is_action_safe(_) ->
    false.

%% Check if action values are safe
is_action_value_safe({literal, _Value, _Location}) ->
    true;
is_action_value_safe({state_var, _Variable, _Location}) ->
    true;
is_action_value_safe({state_field, _Field, _Location}) ->
    true;
is_action_value_safe({event_data, _Location}) ->
    true;
is_action_value_safe({current_state, _Location}) ->
    true;
is_action_value_safe({binary_op, Op, Left, Right, _Location}) ->
    is_safe_binary_op(Op) andalso
        is_action_value_safe(Left) andalso
        is_action_value_safe(Right);
is_action_value_safe({function_call, Function, Args, _Location}) ->
    is_safe_action_function(Function) andalso
        lists:all(fun is_action_value_safe/1, Args);
is_action_value_safe(_) ->
    false.

%% Check if action conditions are safe
is_action_condition_safe(Condition) ->
    case cure_guard_compiler:is_guard_safe(Condition) of
        true -> true;
        false -> is_action_specific_condition_safe(Condition)
    end.

is_action_specific_condition_safe({state_changed, _Variable, _Location}) -> true;
is_action_specific_condition_safe({event_matches, _Pattern, _Location}) -> true;
is_action_specific_condition_safe(_) -> false.

%% Check if binary operations are safe in actions
is_safe_binary_op('+') -> true;
is_safe_binary_op('-') -> true;
is_safe_binary_op('*') -> true;
is_safe_binary_op('/') -> true;
is_safe_binary_op('div') -> true;
is_safe_binary_op('rem') -> true;
% List concatenation
is_safe_binary_op('++') -> true;
% List subtraction
is_safe_binary_op('--') -> true;
is_safe_binary_op(_) -> false.

%% Check if functions are safe to call in actions
is_safe_action_function(length) -> true;
is_safe_action_function(size) -> true;
is_safe_action_function(hd) -> true;
is_safe_action_function(tl) -> true;
is_safe_action_function(element) -> true;
is_safe_action_function(abs) -> true;
is_safe_action_function(max) -> true;
is_safe_action_function(min) -> true;
is_safe_action_function(round) -> true;
is_safe_action_function(trunc) -> true;
is_safe_action_function(lists_reverse) -> true;
is_safe_action_function(maps_get) -> true;
is_safe_action_function(maps_put) -> true;
% Disallow potentially dangerous functions
is_safe_action_function(spawn) -> false;
is_safe_action_function(send) -> false;
is_safe_action_function(exit) -> false;
is_safe_action_function(_) -> false.

%% ============================================================================
%% Action Optimization
%% ============================================================================

%% Optimize action expressions
optimize_action(Action) ->
    OptimizedAction = constant_fold_action(Action),
    simplify_action(OptimizedAction).

%% Constant folding for action expressions
constant_fold_action({assign, Variable, Value, Location}) ->
    {assign, Variable, constant_fold_action_value(Value), Location};
constant_fold_action({update, Field, Value, Location}) ->
    {update, Field, constant_fold_action_value(Value), Location};
constant_fold_action({increment, Variable, Amount, Location}) ->
    {increment, Variable, constant_fold_action_value(Amount), Location};
constant_fold_action({decrement, Variable, Amount, Location}) ->
    {decrement, Variable, constant_fold_action_value(Amount), Location};
constant_fold_action({sequence, Actions, Location}) ->
    OptimizedActions = [constant_fold_action(A) || A <- Actions],
    {sequence, OptimizedActions, Location};
constant_fold_action({if_then, Condition, ThenAction, ElseAction, Location}) ->
    OptimizedCondition = constant_fold_action_value(Condition),
    OptimizedThen = constant_fold_action(ThenAction),
    OptimizedElse =
        case ElseAction of
            undefined -> undefined;
            _ -> constant_fold_action(ElseAction)
        end,
    {if_then, OptimizedCondition, OptimizedThen, OptimizedElse, Location};
constant_fold_action(Action) ->
    Action.

%% Constant folding for action values
constant_fold_action_value({binary_op, Op, {literal, L, _}, {literal, R, _}, Location}) ->
    try
        Value =
            case Op of
                '+' -> L + R;
                '-' -> L - R;
                '*' -> L * R;
                '/' when R =/= 0 -> L / R;
                'div' when R =/= 0 -> L div R;
                'rem' when R =/= 0 -> L rem R;
                _ -> throw(no_fold)
            end,
        {literal, Value, Location}
    catch
        _:_ -> {binary_op, Op, {literal, L, Location}, {literal, R, Location}, Location}
    end;
constant_fold_action_value({binary_op, Op, Left, Right, Location}) ->
    OptimizedLeft = constant_fold_action_value(Left),
    OptimizedRight = constant_fold_action_value(Right),
    case {OptimizedLeft, OptimizedRight} of
        {{literal, L, _}, {literal, R, _}} ->
            constant_fold_action_value(
                {binary_op, Op, {literal, L, Location}, {literal, R, Location}, Location}
            );
        _ ->
            {binary_op, Op, OptimizedLeft, OptimizedRight, Location}
    end;
constant_fold_action_value(Value) ->
    Value.

%% Simplify action expressions
simplify_action({sequence, [SingleAction], _Location}) ->
    % Simplify single-action sequences
    simplify_action(SingleAction);
simplify_action({sequence, Actions, Location}) ->
    % Remove no-op actions and flatten nested sequences
    SimplifiedActions = simplify_action_sequence(Actions),
    case SimplifiedActions of
        [] -> undefined;
        [Single] -> simplify_action(Single);
        _ -> {sequence, SimplifiedActions, Location}
    end;
simplify_action({increment, Variable, {literal, 0, _}, _Location}) ->
    % Increment by zero is a no-op
    undefined;
simplify_action({decrement, Variable, {literal, 0, _}, _Location}) ->
    % Decrement by zero is a no-op
    undefined;
simplify_action(Action) ->
    Action.

%% Simplify action sequences
simplify_action_sequence(Actions) ->
    lists:filtermap(
        fun(Action) ->
            case simplify_action(Action) of
                undefined -> false;
                SimplifiedAction -> {true, SimplifiedAction}
            end
        end,
        Actions
    ).

%% ============================================================================
%% Action Safety Analysis
%% ============================================================================

%% Analyze action safety comprehensively
analyze_action_safety(Action, State) ->
    try
        case is_action_safe(Action) of
            true ->
                SafetyDetails = analyze_action_safety_details(Action, []),
                {ok, safe, SafetyDetails};
            false ->
                UnsafeReasons = find_unsafe_reasons(Action, []),
                {ok, unsafe, UnsafeReasons}
        end
    catch
        Error:Reason:Stack ->
            {error, {safety_analysis_failed, Error, Reason, Stack}}
    end.

%% Analyze safety details for safe actions
analyze_action_safety_details({assign, Variable, Value, _Location}, Acc) ->
    ValueDetails = analyze_value_safety_details(Value),
    [{assign_operation, Variable, safe} | ValueDetails ++ Acc];
analyze_action_safety_details({update, Field, Value, _Location}, Acc) ->
    ValueDetails = analyze_value_safety_details(Value),
    [{field_update_operation, Field, safe} | ValueDetails ++ Acc];
analyze_action_safety_details({increment, Variable, Amount, _Location}, Acc) ->
    AmountDetails = analyze_value_safety_details(Amount),
    [{increment_operation, Variable, safe} | AmountDetails ++ Acc];
analyze_action_safety_details({decrement, Variable, Amount, _Location}, Acc) ->
    AmountDetails = analyze_value_safety_details(Amount),
    [{decrement_operation, Variable, safe} | AmountDetails ++ Acc];
analyze_action_safety_details({emit, Event, Data, _Location}, Acc) ->
    EventDetails = analyze_value_safety_details(Event),
    DataDetails =
        case Data of
            undefined -> [];
            _ -> analyze_value_safety_details(Data)
        end,
    [{emit_operation, safe} | EventDetails ++ DataDetails ++ Acc];
analyze_action_safety_details({call, Function, Args, _Location}, Acc) ->
    FunctionSafety =
        case is_safe_action_function(Function) of
            true -> safe;
            false -> unsafe
        end,
    ArgsDetails = lists:flatten([analyze_value_safety_details(Arg) || Arg <- Args]),
    [{function_call, Function, FunctionSafety} | ArgsDetails ++ Acc];
analyze_action_safety_details({sequence, Actions, _Location}, Acc) ->
    SequenceDetails = lists:flatten([analyze_action_safety_details(A, []) || A <- Actions]),
    [{sequence_operation, safe} | SequenceDetails ++ Acc];
analyze_action_safety_details({if_then, Condition, ThenAction, ElseAction, _Location}, Acc) ->
    ConditionDetails = analyze_value_safety_details(Condition),
    ThenDetails = analyze_action_safety_details(ThenAction, []),
    ElseDetails =
        case ElseAction of
            undefined -> [];
            _ -> analyze_action_safety_details(ElseAction, [])
        end,
    [{conditional_operation, safe} | ConditionDetails ++ ThenDetails ++ ElseDetails ++ Acc];
analyze_action_safety_details({log, Level, Message, _Location}, Acc) ->
    MessageDetails = analyze_value_safety_details(Message),
    [{log_operation, Level, safe} | MessageDetails ++ Acc];
analyze_action_safety_details(undefined, Acc) ->
    [{no_action, safe} | Acc];
analyze_action_safety_details(_Action, Acc) ->
    [{unknown_action, unknown_safety} | Acc].

%% Analyze safety details for values
analyze_value_safety_details({literal, _Value, _Location}) ->
    [{literal_value, safe}];
analyze_value_safety_details({state_var, Variable, _Location}) ->
    [{state_variable_access, Variable, safe}];
analyze_value_safety_details({state_field, Field, _Location}) ->
    [{state_field_access, Field, safe}];
analyze_value_safety_details({event_data, _Location}) ->
    [{event_data_access, safe}];
analyze_value_safety_details({current_state, _Location}) ->
    [{current_state_access, safe}];
analyze_value_safety_details({binary_op, Op, Left, Right, _Location}) ->
    LeftDetails = analyze_value_safety_details(Left),
    RightDetails = analyze_value_safety_details(Right),
    OpSafety =
        case is_safe_binary_op(Op) of
            true -> safe;
            false -> unsafe
        end,
    [{binary_operation, Op, OpSafety} | LeftDetails ++ RightDetails];
analyze_value_safety_details({function_call, Function, Args, _Location}) ->
    FunctionSafety =
        case is_safe_action_function(Function) of
            true -> safe;
            false -> unsafe
        end,
    ArgsDetails = lists:flatten([analyze_value_safety_details(Arg) || Arg <- Args]),
    [{function_call_value, Function, FunctionSafety} | ArgsDetails];
analyze_value_safety_details(_Value) ->
    [{unknown_value, unknown_safety}].

%% Find reasons why an action is unsafe
find_unsafe_reasons({call, Function, Args, Location}, Acc) ->
    case is_safe_action_function(Function) of
        false ->
            Reason = {unsafe_function_call, Function, Location},
            ArgsReasons = lists:flatten([find_unsafe_value_reasons(Arg) || Arg <- Args]),
            [Reason | ArgsReasons ++ Acc];
        true ->
            ArgsReasons = lists:flatten([find_unsafe_value_reasons(Arg) || Arg <- Args]),
            ArgsReasons ++ Acc
    end;
find_unsafe_reasons({sequence, Actions, _Location}, Acc) ->
    SequenceReasons = lists:flatten([find_unsafe_reasons(A, []) || A <- Actions]),
    SequenceReasons ++ Acc;
find_unsafe_reasons({if_then, Condition, ThenAction, ElseAction, _Location}, Acc) ->
    ConditionReasons = find_unsafe_value_reasons(Condition),
    ThenReasons = find_unsafe_reasons(ThenAction, []),
    ElseReasons =
        case ElseAction of
            undefined -> [];
            _ -> find_unsafe_reasons(ElseAction, [])
        end,
    ConditionReasons ++ ThenReasons ++ ElseReasons ++ Acc;
find_unsafe_reasons(_Action, Acc) ->
    % Action is safe or we don't recognize it
    Acc.

%% Find unsafe reasons in values
find_unsafe_value_reasons({binary_op, Op, Left, Right, Location}) ->
    LeftReasons = find_unsafe_value_reasons(Left),
    RightReasons = find_unsafe_value_reasons(Right),
    OpReasons =
        case is_safe_binary_op(Op) of
            false -> [{unsafe_binary_operation, Op, Location}];
            true -> []
        end,
    LeftReasons ++ RightReasons ++ OpReasons;
find_unsafe_value_reasons({function_call, Function, Args, Location}) ->
    FunctionReasons =
        case is_safe_action_function(Function) of
            false -> [{unsafe_function_in_value, Function, Location}];
            true -> []
        end,
    ArgsReasons = lists:flatten([find_unsafe_value_reasons(Arg) || Arg <- Args]),
    FunctionReasons ++ ArgsReasons;
find_unsafe_value_reasons(_Value) ->
    [].

%% ============================================================================
%% Helper Functions
%% ============================================================================

%% Generate new label (reuse from codegen)
new_label(State) ->
    Counter = State#codegen_state.label_counter,
    Label = list_to_atom("action_label_" ++ integer_to_list(Counter)),
    NewState = State#codegen_state{label_counter = Counter + 1},
    {Label, NewState}.
