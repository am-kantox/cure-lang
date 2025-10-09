%% Cure Programming Language - Runtime Execution Engine
%% Interprets and executes generated BEAM instructions
-module(cure_runtime).

-export([
    execute_module/1,
    execute_function/3,
    call_function/3,
    run_program/1,
    create_runtime_state/0,
    load_module/2
]).

%% Runtime state for execution
-record(runtime_state, {
    stack = [],
    locals = #{},
    params = #{},
    modules = #{},
    globals = #{}
}).

%% ============================================================================
%% Main Execution Interface
%% ============================================================================

%% Execute a compiled module
execute_module(CompiledModule) ->
    State = create_runtime_state(),
    StateWithModule = cure_runtime:load_module(CompiledModule, State),

    % Look for main function and execute it
    case find_function(CompiledModule, main, 0) of
        {ok, _MainFunction} ->
            execute_function(main, [], StateWithModule);
        error ->
            {error, main_function_not_found}
    end.

%% Run a complete program (list of modules)
run_program([]) ->
    {error, no_modules};
run_program([FirstModule | RestModules]) ->
    State = create_runtime_state(),

    % Load all modules into runtime state
    StateWithModules = lists:foldl(fun cure_runtime:load_module/2, State, [
        FirstModule | RestModules
    ]),

    % Look for main function in any module
    case find_main_function([FirstModule | RestModules]) of
        {ok, _ModuleName, _MainFunction} ->
            execute_function(main, [], StateWithModules);
        error ->
            {error, main_function_not_found}
    end.

%% Create initial runtime state
create_runtime_state() ->
    GlobalFunctions = #{
        % Standard library functions from cure_std
        ok => {external, cure_std, ok, 1},
        error => {external, cure_std, error, 1},
        some => {external, cure_std, some, 1},
        none => {external, cure_std, none, 0},
        map => {external, cure_std, map, 2},
        filter => {external, cure_std, filter, 2},
        foldl => {external, cure_std, foldl, 3},
        head => {external, cure_std, head, 1},
        tail => {external, cure_std, tail, 1},
        length => {external, cure_std, length, 1},
        find => {external, cure_std, find, 2},
        abs => {external, cure_std, abs, 1},
        sqrt => {external, cure_std, sqrt, 1},
        pi => {external, cure_std, pi, 0},
        safe_divide => {external, cure_std, safe_divide, 2},
        safe_sqrt => {external, cure_std, safe_sqrt, 2},
        gcd => {external, cure_std, gcd, 2},
        factorial => {external, cure_std, factorial, 1},
        string_concat => {external, cure_std, string_concat, 2},
        split => {external, cure_std, split, 2},
        trim => {external, cure_std, trim, 1},
        to_upper => {external, cure_std, to_upper, 1},
        to_lower => {external, cure_std, to_lower, 1},
        contains => {external, cure_std, contains, 2},
        starts_with => {external, cure_std, starts_with, 2},
        ends_with => {external, cure_std, ends_with, 2},
        string_join => {external, cure_std, string_join, 2},
        string_empty => {external, cure_std, string_empty, 1},
        int_to_string => {external, cure_std, int_to_string, 1},
        float_to_string => {external, cure_std, float_to_string, 1},
        print => {external, cure_std, print, 1},
        println => {external, cure_std, println, 1},
        fsm_create => {external, cure_std, fsm_create, 2},
        fsm_send_safe => {external, cure_std, fsm_send_safe, 2},
        create_counter => {external, cure_std, create_counter, 1},
        list_to_string => {external, cure_std, list_to_string, 1},
        join_ints => {external, cure_std, join_ints, 2},
        map_ok => {external, cure_std, map_ok, 2},
        is_monad => {external, cure_std, is_monad, 1},
        pipe => {external, cure_std, pipe, 2}
    },
    #runtime_state{globals = GlobalFunctions}.

%% ============================================================================
%% Module Loading
%% ============================================================================

%% Load a compiled module into runtime state
load_module(CompiledModule, State) ->
    ModuleName = maps:get(name, CompiledModule),
    Functions = maps:get(functions, CompiledModule, []),

    % Add module functions to globals
    ModuleFunctions = lists:foldl(
        fun(Function, Acc) ->
            FuncName = maps:get(name, Function),
            _Arity = maps:get(arity, Function),
            maps:put(FuncName, {internal, ModuleName, Function}, Acc)
        end,
        State#runtime_state.globals,
        Functions
    ),

    NewModules = maps:put(ModuleName, CompiledModule, State#runtime_state.modules),
    State#runtime_state{
        globals = ModuleFunctions,
        modules = NewModules
    }.

%% Find a function in a module
find_function(CompiledModule, FuncName, Arity) ->
    Functions = maps:get(functions, CompiledModule, []),
    case
        lists:filter(
            fun(F) ->
                maps:get(name, F) =:= FuncName andalso maps:get(arity, F) =:= Arity
            end,
            Functions
        )
    of
        [] -> error;
        [Function | _] -> {ok, Function}
    end.

%% Find main function in any module
find_main_function([]) ->
    error;
find_main_function([Module | RestModules]) ->
    case find_function(Module, main, 0) of
        {ok, MainFunction} ->
            ModuleName = maps:get(name, Module),
            {ok, ModuleName, MainFunction};
        error ->
            find_main_function(RestModules)
    end.

%% ============================================================================
%% Function Execution
%% ============================================================================

%% Execute a function by name with arguments
call_function(FuncName, Args, State) ->
    case maps:get(FuncName, State#runtime_state.globals, undefined) of
        undefined ->
            {error, {function_not_found, FuncName}};
        {external, Module, Function, _Arity} ->
            % Call external Erlang function
            try
                Result = apply(Module, Function, Args),
                {ok, Result, State}
            catch
                Error:Reason ->
                    {error, {external_function_error, Error, Reason}}
            end;
        {internal, _ModuleName, Function} ->
            execute_function(FuncName, Args, State, Function)
    end.

%% Execute a function with given arguments
execute_function(FuncName, Args, State) ->
    case maps:get(FuncName, State#runtime_state.globals, undefined) of
        undefined ->
            {error, {function_not_found, FuncName}};
        {external, Module, Function, _Arity} ->
            % Call external Erlang function
            try
                Result = apply(Module, Function, Args),
                {ok, Result, State}
            catch
                Error:Reason ->
                    {error, {external_function_error, Error, Reason}}
            end;
        {internal, _ModuleName, Function} ->
            execute_function(FuncName, Args, State, Function)
    end.

%% Execute internal function with instructions
execute_function(FuncName, Args, State, Function) ->
    Instructions = maps:get(instructions, Function, []),
    Params = maps:get(params, Function, []),

    % Set up parameter bindings
    ParamBindings = create_param_bindings(Params, Args),

    FunctionState = State#runtime_state{
        stack = [],
        params = ParamBindings,
        locals = #{}
    },

    % Execute instructions
    case execute_instructions(Instructions, FunctionState) of
        {ok, Result, NewState} ->
            {ok, Result, NewState};
        {error, Reason} ->
            {error, {function_execution_error, FuncName, Reason}}
    end.

%% Create parameter bindings from parameter names and argument values
create_param_bindings(Params, Args) ->
    create_param_bindings(Params, Args, #{}).

create_param_bindings([], [], Acc) ->
    Acc;
create_param_bindings([Param | RestParams], [Arg | RestArgs], Acc) ->
    ParamName =
        case Param of
            {param, Name, _Type, _Location} -> Name;
            Name when is_atom(Name) -> Name;
            _ -> unknown_param
        end,
    create_param_bindings(RestParams, RestArgs, maps:put(ParamName, Arg, Acc));
create_param_bindings(_, _, Acc) ->
    % Mismatched parameter/argument count
    Acc.

%% ============================================================================
%% Instruction Execution
%% ============================================================================

%% Execute a sequence of instructions
execute_instructions([], State) ->
    % No instructions, return ok
    {ok, ok, State};
execute_instructions(Instructions, State) ->
    execute_instructions_loop(Instructions, State).

execute_instructions_loop([], State) ->
    % End of instructions, pop result from stack
    case State#runtime_state.stack of
        [Result | _] -> {ok, Result, State};
        [] -> {ok, ok, State}
    end;
execute_instructions_loop([Instruction | RestInstructions], State) ->
    case execute_instruction(Instruction, State) of
        {ok, NewState} ->
            execute_instructions_loop(RestInstructions, NewState);
        {jump, Label, NewState} ->
            % Find the label and jump to it
            case find_label(Label, RestInstructions) of
                {ok, NewInstructions} ->
                    execute_instructions_loop(NewInstructions, NewState);
                error ->
                    {error, {label_not_found, Label}}
            end;
        {return, Result, NewState} ->
            {ok, Result, NewState};
        {error, Reason} ->
            {error, Reason}
    end.

%% Execute a single instruction
execute_instruction(Instruction, State) ->
    case Instruction of
        % Handle record format from code generator
        {beam_instr, Op, Args, _Location} ->
            execute_instruction(#{op => Op, args => Args}, State);
        % Handle map format
        #{op := load_literal, args := [Value]} ->
            NewStack = [Value | State#runtime_state.stack],
            {ok, State#runtime_state{stack = NewStack}};
        #{op := load_param, args := [ParamName]} ->
            case maps:get(ParamName, State#runtime_state.params, undefined) of
                undefined ->
                    {error, {parameter_not_found, ParamName}};
                Value ->
                    NewStack = [Value | State#runtime_state.stack],
                    {ok, State#runtime_state{stack = NewStack}}
            end;
        #{op := load_local, args := [VarName]} ->
            case maps:get(VarName, State#runtime_state.locals, undefined) of
                undefined ->
                    {error, {local_variable_not_found, VarName}};
                Value ->
                    NewStack = [Value | State#runtime_state.stack],
                    {ok, State#runtime_state{stack = NewStack}}
            end;
        #{op := store_local, args := [VarName]} ->
            case State#runtime_state.stack of
                [Value | _RestStack] ->
                    NewLocals = maps:put(VarName, Value, State#runtime_state.locals),
                    NewState = State#runtime_state{
                        locals = NewLocals
                    },
                    {ok, NewState};
                [] ->
                    {error, stack_underflow}
            end;
        #{op := load_global, args := [FuncName]} ->
            % Push function reference onto stack
            NewStack = [{function_ref, FuncName} | State#runtime_state.stack],
            {ok, State#runtime_state{stack = NewStack}};
        #{op := call, args := [Arity]} ->
            % Pop function and arguments from stack
            case pop_call_args(Arity + 1, State#runtime_state.stack) of
                {ok, [{function_ref, FuncName} | Args], RestStack} ->
                    case call_function(FuncName, lists:reverse(Args), State) of
                        {ok, Result, NewState} ->
                            FinalStack = [Result | RestStack],
                            {ok, NewState#runtime_state{stack = FinalStack}};
                        {error, Reason} ->
                            {error, Reason}
                    end;
                {ok, [Function | Args], RestStack} when is_function(Function) ->
                    % Lambda function call
                    try
                        Result = apply(Function, lists:reverse(Args)),
                        FinalStack = [Result | RestStack],
                        {ok, State#runtime_state{stack = FinalStack}}
                    catch
                        Error:Reason ->
                            {error, {lambda_call_error, Error, Reason}}
                    end;
                {error, Reason} ->
                    {error, Reason}
            end;
        #{op := binary_op, args := [Op]} ->
            case State#runtime_state.stack of
                [Right, Left | RestStack] ->
                    case execute_binary_op(Op, Left, Right) of
                        {ok, Result} ->
                            NewStack = [Result | RestStack],
                            {ok, State#runtime_state{stack = NewStack}};
                        {error, Reason} ->
                            {error, Reason}
                    end;
                _ ->
                    {error, stack_underflow}
            end;
        #{op := unary_op, args := [Op]} ->
            case State#runtime_state.stack of
                [Operand | RestStack] ->
                    case execute_unary_op(Op, Operand) of
                        {ok, Result} ->
                            NewStack = [Result | RestStack],
                            {ok, State#runtime_state{stack = NewStack}};
                        {error, Reason} ->
                            {error, Reason}
                    end;
                [] ->
                    {error, stack_underflow}
            end;
        #{op := make_list, args := Args} ->
            % Handle different possible args formats
            Count =
                case Args of
                    [N] when is_integer(N) -> N;
                    N when is_integer(N) -> N;
                    % Default fallback for debugging
                    [_] -> 10;
                    % Default fallback
                    _ -> 10
                end,
            case pop_n_items(Count, State#runtime_state.stack) of
                {ok, Items, RestStack} ->
                    List = lists:reverse(Items),
                    NewStack = [List | RestStack],
                    {ok, State#runtime_state{stack = NewStack}};
                {error, Reason} ->
                    {error, Reason}
            end;
        #{op := make_lambda, args := [_LambdaName, Params, BodyInstructions]} ->
            % Create a lambda function (simplified implementation)
            Lambda = fun(Args) ->
                LambdaState = State#runtime_state{
                    stack = [],
                    params = create_param_bindings(Params, Args),
                    locals = #{}
                },
                case execute_instructions(BodyInstructions, LambdaState) of
                    {ok, Result, _} -> Result;
                    {error, Reason} -> throw({lambda_error, Reason})
                end
            end,
            NewStack = [Lambda | State#runtime_state.stack],
            {ok, State#runtime_state{stack = NewStack}};
        #{op := pattern_match, args := [_Patterns]} ->
            % Simplified pattern matching - just pop the value for now
            case State#runtime_state.stack of
                [_Value | RestStack] ->
                    % For now, just succeed and keep the value
                    {ok, State#runtime_state{stack = RestStack}};
                [] ->
                    {error, stack_underflow}
            end;
        #{op := jump_if_false, args := [Label]} ->
            case State#runtime_state.stack of
                [false | RestStack] ->
                    {jump, Label, State#runtime_state{stack = RestStack}};
                [_ | RestStack] ->
                    {ok, State#runtime_state{stack = RestStack}};
                [] ->
                    {error, stack_underflow}
            end;
        #{op := jump, args := [Label]} ->
            {jump, Label, State};
        #{op := label, args := [_Label]} ->
            % Labels are no-ops during execution
            {ok, State};
        #{op := return, args := []} ->
            case State#runtime_state.stack of
                [Result | _] -> {return, Result, State};
                [] -> {return, ok, State}
            end;
        #{op := pop, args := []} ->
            case State#runtime_state.stack of
                [_ | RestStack] ->
                    {ok, State#runtime_state{stack = RestStack}};
                [] ->
                    {error, stack_underflow}
            end;
        #{op := monadic_pipe_call, args := [Arity]} ->
            % Monadic pipe call: [Function, PipedValue, Args...] -> Result
            % Uses cure_std:pipe/2 to implement monadic pipe semantics
            case pop_call_args(Arity + 1, State#runtime_state.stack) of
                {ok, [FunctionRef | [PipedValue | Args]], RestStack} ->
                    % Create a lambda that will call the function with the piped value and args
                    Lambda = fun(UnwrappedValue) ->
                        case FunctionRef of
                            {function_ref, FuncName} ->
                                case call_function(FuncName, [UnwrappedValue | Args], State) of
                                    {ok, Result, _NewState} -> Result;
                                    {error, _Reason} -> throw(function_call_failed)
                                end;
                            Function when is_function(Function) ->
                                apply(Function, [UnwrappedValue | Args]);
                            _ ->
                                throw(invalid_function_reference)
                        end
                    end,

                    % Use cure_std:pipe/2 to handle the monadic pipe operation
                    case call_function(pipe, [PipedValue, Lambda], State) of
                        {ok, Result, NewState} ->
                            FinalStack = [Result | RestStack],
                            {ok, NewState#runtime_state{stack = FinalStack}};
                        {error, Reason} ->
                            {error, Reason}
                    end;
                {error, Reason} ->
                    {error, Reason}
            end;
        _ ->
            {error, {unsupported_instruction, Instruction}}
    end.

%% ============================================================================
%% Utility Functions
%% ============================================================================

%% Pop N items from stack
pop_n_items(0, Stack) ->
    {ok, [], Stack};
pop_n_items(N, Stack) when N > 0, length(Stack) >= N ->
    {Items, RestStack} = lists:split(N, Stack),
    {ok, Items, RestStack};
pop_n_items(N, Stack) ->
    {error, {insufficient_stack_items, N, length(Stack)}}.

%% Pop function and arguments for call
pop_call_args(Count, Stack) ->
    pop_n_items(Count, Stack).

%% Execute binary operations
execute_binary_op(Op, Left, Right) ->
    try
        Result =
            case Op of
                '+' -> Left + Right;
                '-' -> Left - Right;
                '*' -> Left * Right;
                '/' -> Left / Right;
                '%' -> Left rem Right;
                '++' -> Left ++ Right;
                '==' -> Left =:= Right;
                '!=' -> Left =/= Right;
                '<' -> Left < Right;
                '>' -> Left > Right;
                '<=' -> Left =< Right;
                '>=' -> Left >= Right;
                _ -> throw({unsupported_binary_op, Op})
            end,
        {ok, Result}
    catch
        Error:Reason ->
            {error, {binary_op_error, Op, Error, Reason}}
    end.

%% Execute unary operations
execute_unary_op(Op, Operand) ->
    try
        Result =
            case Op of
                '-' -> -Operand;
                '+' -> +Operand;
                'not' -> not Operand;
                _ -> throw({unsupported_unary_op, Op})
            end,
        {ok, Result}
    catch
        Error:Reason ->
            {error, {unary_op_error, Op, Error, Reason}}
    end.

%% Find label in instruction sequence
find_label(TargetLabel, Instructions) ->
    find_label_loop(TargetLabel, Instructions, []).

find_label_loop(_TargetLabel, [], _Acc) ->
    error;
find_label_loop(TargetLabel, [Instruction | RestInstructions], Acc) ->
    case Instruction of
        #{op := label, args := [Label]} when Label =:= TargetLabel ->
            {ok, RestInstructions};
        _ ->
            find_label_loop(TargetLabel, RestInstructions, [Instruction | Acc])
    end.
