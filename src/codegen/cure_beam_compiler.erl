%% Cure Programming Language - BEAM Instruction Compiler
%% Converts Cure internal instructions to proper Erlang abstract forms
-module(cure_beam_compiler).

-export([
    compile_instructions_to_forms/2,
    compile_function_to_erlang/2,
    optimize_instructions/1,
    validate_erlang_forms/1
]).

%% Include necessary headers
-include("../parser/cure_ast_simple.hrl").

%% BEAM instruction record for internal representation
-record(beam_instr, {
    op,                    % Instruction opcode
    args = [],             % Instruction arguments
    location               % Source location for debugging
}).

%% Compilation context for instruction conversion
-record(compile_context, {
    line = 1,
    variables = #{},
    labels = #{},
    temp_counter = 0,
    stack = []
}).

%% ============================================================================
%% Main Compilation Functions
%% ============================================================================

%% Compile a function with instructions to proper Erlang form
compile_function_to_erlang(#{name := Name, arity := Arity, params := Params, 
                            instructions := Instructions}, StartLine) ->
    Context = #compile_context{
        line = StartLine,
        variables = create_param_variables(Params, StartLine)
    },
    
    case compile_instructions_to_forms(Instructions, Context) of
        {ok, Body, _FinalContext} ->
            ParamVars = [{var, StartLine, Param} || Param <- Params],
            FunctionForm = {function, StartLine, Name, Arity, [
                {clause, StartLine, ParamVars, [], Body}
            ]},
            {ok, FunctionForm, StartLine + 20};
        {error, Reason} ->
            {error, Reason}
    end.

%% Create parameter variable mappings
create_param_variables(Params, Line) ->
    lists:foldl(fun(Param, Acc) ->
        maps:put(Param, {var, Line, Param}, Acc)
    end, #{}, Params).

%% Compile instructions to Erlang forms
compile_instructions_to_forms(Instructions, Context) ->
    compile_instructions_to_forms(Instructions, Context, []).

compile_instructions_to_forms([], Context, Acc) ->
    Body = lists:reverse(Acc),
    FinalBody = case Body of
        [] -> [{atom, Context#compile_context.line, ok}];
        _ -> Body
    end,
    {ok, FinalBody, Context};

compile_instructions_to_forms([Instruction | RestInstructions], Context, Acc) ->
    case compile_single_instruction(Instruction, Context) of
        {ok, Forms, NewContext} ->
            compile_instructions_to_forms(RestInstructions, NewContext, Forms ++ Acc);
        {error, Reason} ->
            {error, Reason}
    end.

%% ============================================================================
%% Single Instruction Compilation
%% ============================================================================

%% Compile individual instructions to Erlang forms
compile_single_instruction(#beam_instr{op = Op, args = Args, location = Location}, Context) ->
    Line = get_line_from_location(Location, Context#compile_context.line),
    NewContext = Context#compile_context{line = Line},
    
    case Op of
        load_literal -> compile_load_literal(Args, NewContext);
        load_param -> compile_load_param(Args, NewContext);
        load_local -> compile_load_local(Args, NewContext);
        load_global -> compile_load_global(Args, NewContext);
        store_local -> compile_store_local(Args, NewContext);
        binary_op -> compile_binary_op(Args, NewContext);
        call -> compile_call(Args, NewContext);
        make_list -> compile_make_list(Args, NewContext);
        jump_if_false -> compile_jump_if_false(Args, NewContext);
        jump -> compile_jump(Args, NewContext);
        label -> compile_label(Args, NewContext);
        pop -> compile_pop(Args, NewContext);
        return -> compile_return(Args, NewContext);
        _ -> {error, {unsupported_instruction, Op}}
    end.

%% Load literal value
compile_load_literal([Value], Context) ->
    Form = compile_value_to_form(Value, Context#compile_context.line),
    {ok, [Form], push_stack(Form, Context)}.

%% Load parameter
compile_load_param([ParamName], Context) ->
    case maps:get(ParamName, Context#compile_context.variables, undefined) of
        undefined ->
            {error, {undefined_parameter, ParamName}};
        VarForm ->
            {ok, [VarForm], push_stack(VarForm, Context)}
    end.

%% Load local variable
compile_load_local([VarName], Context) ->
    case maps:get(VarName, Context#compile_context.variables, undefined) of
        undefined ->
            Line = Context#compile_context.line,
            VarForm = {var, Line, VarName},
            NewVariables = maps:put(VarName, VarForm, Context#compile_context.variables),
            NewContext = Context#compile_context{variables = NewVariables},
            {ok, [VarForm], push_stack(VarForm, NewContext)};
        VarForm ->
            {ok, [VarForm], push_stack(VarForm, Context)}
    end.

%% Load global function or variable
compile_load_global([Name], Context) ->
    Line = Context#compile_context.line,
    
    % Check if it's a built-in function or FSM function
    Form = case is_builtin_function(Name) of
        true ->
            % Reference to built-in function
            {atom, Line, Name};
        false ->
            % External function reference - generate function call form
            {atom, Line, Name}
    end,
    
    {ok, [Form], push_stack(Form, Context)}.

%% Store value in local variable
compile_store_local([VarName], Context) ->
    case pop_stack(Context) of
        {Value, NewContext} ->
            Line = NewContext#compile_context.line,
            VarForm = {var, Line, VarName},
            MatchForm = {match, Line, VarForm, Value},
            
            NewVariables = maps:put(VarName, VarForm, NewContext#compile_context.variables),
            FinalContext = NewContext#compile_context{variables = NewVariables},
            
            {ok, [MatchForm], push_stack(VarForm, FinalContext)};
        {error, Reason} ->
            {error, Reason}
    end.

%% Compile binary operations
compile_binary_op([Operator], Context) ->
    case pop_two_from_stack(Context) of
        {Right, Left, NewContext} ->
            Line = NewContext#compile_context.line,
            OpForm = compile_binary_operator(Operator, Left, Right, Line),
            {ok, [OpForm], push_stack(OpForm, NewContext)};
        {error, Reason} ->
            {error, Reason}
    end.

%% Compile function calls
compile_call([Arity], Context) ->
    case pop_n_from_stack(Arity + 1, Context) of  % +1 for function itself
        {Elements, NewContext} ->
            [Function | Args] = lists:reverse(Elements),
            Line = NewContext#compile_context.line,
            
            CallForm = case Function of
                {atom, _, FuncName} ->
                    % Local function call
                    {call, Line, Function, Args};
                _ ->
                    % Complex function expression
                    {call, Line, Function, Args}
            end,
            
            {ok, [CallForm], push_stack(CallForm, NewContext)};
        {error, Reason} ->
            {error, Reason}
    end.

%% Create list from stack elements
compile_make_list([Count], Context) ->
    case pop_n_from_stack(Count, Context) of
        {Elements, NewContext} ->
            Line = NewContext#compile_context.line,
            ListForm = {cons, Line, Elements},
            {ok, [ListForm], push_stack(ListForm, NewContext)};
        {error, Reason} ->
            {error, Reason}
    end.

%% Conditional jump (for if expressions)
compile_jump_if_false([Label], Context) ->
    case pop_stack(Context) of
        {Condition, NewContext} ->
            % This is handled at a higher level in if expression compilation
            % For now, we'll store the condition and label information
            LabelInfo = {jump_if_false, Label, Condition},
            {ok, [], store_label_info(LabelInfo, NewContext)};
        {error, Reason} ->
            {error, Reason}
    end.

%% Unconditional jump
compile_jump([Label], Context) ->
    LabelInfo = {jump, Label},
    {ok, [], store_label_info(LabelInfo, Context)}.

%% Label definition
compile_label([LabelName], Context) ->
    NewLabels = maps:put(LabelName, Context#compile_context.line, Context#compile_context.labels),
    NewContext = Context#compile_context{labels = NewLabels},
    {ok, [], NewContext}.

%% Pop (discard top of stack)
compile_pop([], Context) ->
    case pop_stack(Context) of
        {_Value, NewContext} ->
            {ok, [], NewContext};
        {error, Reason} ->
            {error, Reason}
    end.

%% Return statement
compile_return([], Context) ->
    case Context#compile_context.stack of
        [ReturnValue | _] ->
            {ok, [ReturnValue], Context};
        [] ->
            Line = Context#compile_context.line,
            {ok, [{atom, Line, ok}], Context}
    end.

%% ============================================================================
%% Helper Functions
%% ============================================================================

%% Convert values to Erlang abstract form
compile_value_to_form(Value, Line) when is_integer(Value) ->
    {integer, Line, Value};
compile_value_to_form(Value, Line) when is_float(Value) ->
    {float, Line, Value};
compile_value_to_form(Value, Line) when is_atom(Value) ->
    {atom, Line, Value};
compile_value_to_form(Value, Line) when is_binary(Value) ->
    {string, Line, binary_to_list(Value)};
compile_value_to_form(Value, Line) when is_list(Value) ->
    case io_lib:printable_list(Value) of
        true -> {string, Line, Value};
        false -> compile_list_to_form(Value, Line)
    end;
compile_value_to_form(Value, Line) ->
    % Fallback for complex values
    {tuple, Line, [{atom, Line, complex_value}, {term, Line, Value}]}.

%% Convert list to proper list form
compile_list_to_form([], Line) ->
    {nil, Line};
compile_list_to_form([H | T], Line) ->
    HeadForm = compile_value_to_form(H, Line),
    TailForm = compile_list_to_form(T, Line),
    {cons, Line, HeadForm, TailForm}.

%% Compile binary operators
compile_binary_operator('+', Left, Right, Line) ->
    {op, Line, '+', Left, Right};
compile_binary_operator('-', Left, Right, Line) ->
    {op, Line, '-', Left, Right};
compile_binary_operator('*', Left, Right, Line) ->
    {op, Line, '*', Left, Right};
compile_binary_operator('/', Left, Right, Line) ->
    {op, Line, '/', Left, Right};
compile_binary_operator('==', Left, Right, Line) ->
    {op, Line, '==', Left, Right};
compile_binary_operator('!=', Left, Right, Line) ->
    {op, Line, '/=', Left, Right};
compile_binary_operator('<', Left, Right, Line) ->
    {op, Line, '<', Left, Right};
compile_binary_operator('>', Left, Right, Line) ->
    {op, Line, '>', Left, Right};
compile_binary_operator('<=', Left, Right, Line) ->
    {op, Line, '=<', Left, Right};
compile_binary_operator('>=', Left, Right, Line) ->
    {op, Line, '>=', Left, Right};
compile_binary_operator('and', Left, Right, Line) ->
    {op, Line, 'and', Left, Right};
compile_binary_operator('or', Left, Right, Line) ->
    {op, Line, 'or', Left, Right};
compile_binary_operator(Op, Left, Right, Line) ->
    % Generic binary operation
    {call, Line, {atom, Line, Op}, [Left, Right]}.

%% Check if a name is a built-in function
is_builtin_function(Name) ->
    BuiltinFunctions = [
        % Arithmetic
        '+', '-', '*', '/', 'div', 'rem',
        % Comparison  
        '==', '/=', '<', '>', '=<', '>=',
        % Boolean
        'and', 'or', 'not',
        % List operations
        'length', 'hd', 'tl',
        % FSM operations
        'fsm_spawn', 'fsm_send', 'fsm_state', 'fsm_stop',
        % Built-in functions
        'map', 'filter', 'foldl', 'foldr'
    ],
    lists:member(Name, BuiltinFunctions).

%% ============================================================================
%% Stack Management
%% ============================================================================

%% Push value onto compilation stack
push_stack(Value, Context) ->
    NewStack = [Value | Context#compile_context.stack],
    Context#compile_context{stack = NewStack}.

%% Pop value from compilation stack
pop_stack(Context) ->
    case Context#compile_context.stack of
        [Value | RestStack] ->
            NewContext = Context#compile_context{stack = RestStack},
            {Value, NewContext};
        [] ->
            {error, stack_underflow}
    end.

%% Pop two values from stack
pop_two_from_stack(Context) ->
    case pop_stack(Context) of
        {Value1, Context1} ->
            case pop_stack(Context1) of
                {Value2, Context2} ->
                    {Value1, Value2, Context2};
                {error, Reason} ->
                    {error, Reason}
            end;
        {error, Reason} ->
            {error, Reason}
    end.

%% Pop N values from stack
pop_n_from_stack(N, Context) ->
    pop_n_from_stack(N, Context, []).

pop_n_from_stack(0, Context, Acc) ->
    {Acc, Context};
pop_n_from_stack(N, Context, Acc) when N > 0 ->
    case pop_stack(Context) of
        {Value, NewContext} ->
            pop_n_from_stack(N - 1, NewContext, [Value | Acc]);
        {error, Reason} ->
            {error, Reason}
    end.

%% ============================================================================
%% Utility Functions
%% ============================================================================

%% Extract line number from location
get_line_from_location(undefined, DefaultLine) ->
    DefaultLine;
get_line_from_location(#location{line = Line}, _DefaultLine) ->
    Line;
get_line_from_location(_, DefaultLine) ->
    DefaultLine.

%% Store label information for later processing
store_label_info(LabelInfo, Context) ->
    % For now, we'll store label info in the context
    % In a full implementation, this would be used for proper control flow
    Context.

%% ============================================================================
%% Optimization Functions
%% ============================================================================

%% Optimize instruction sequence
optimize_instructions(Instructions) ->
    % Basic peephole optimizations
    Instructions1 = remove_redundant_loads(Instructions),
    Instructions2 = optimize_binary_ops(Instructions1),
    Instructions3 = remove_dead_code(Instructions2),
    Instructions3.

%% Remove redundant load instructions
remove_redundant_loads(Instructions) ->
    % Simplified optimization - remove consecutive loads of the same value
    remove_redundant_loads(Instructions, []).

remove_redundant_loads([], Acc) ->
    lists:reverse(Acc);
remove_redundant_loads([Instr1, Instr2 | Rest], Acc) ->
    case {Instr1#beam_instr.op, Instr2#beam_instr.op} of
        {load_literal, load_literal} ->
            case {Instr1#beam_instr.args, Instr2#beam_instr.args} of
                {[Value], [Value]} ->
                    % Remove duplicate literal load
                    remove_redundant_loads([Instr2 | Rest], Acc);
                _ ->
                    remove_redundant_loads([Instr2 | Rest], [Instr1 | Acc])
            end;
        _ ->
            remove_redundant_loads([Instr2 | Rest], [Instr1 | Acc])
    end;
remove_redundant_loads([Instr], Acc) ->
    lists:reverse([Instr | Acc]).

%% Optimize binary operations
optimize_binary_ops(Instructions) ->
    % Could optimize constant folding, strength reduction, etc.
    Instructions.

%% Remove dead code
remove_dead_code(Instructions) ->
    % Remove unreachable code after unconditional jumps
    Instructions.

%% ============================================================================
%% Validation Functions
%% ============================================================================

%% Validate generated Erlang forms
validate_erlang_forms(Forms) ->
    try
        % Use Erlang's built-in form validation
        case erl_lint:module(Forms) of
            {ok, Warnings} ->
                {ok, Warnings};
            {error, Errors, Warnings} ->
                {error, {validation_failed, Errors, Warnings}}
        end
    catch
        error:Reason ->
            {error, {validation_error, Reason}}
    end.