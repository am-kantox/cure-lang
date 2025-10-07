%% Cure Programming Language - BEAM Instruction Compiler
%% Converts Cure internal instructions to proper Erlang abstract forms
-module(cure_beam_compiler).

-export([
    compile_instructions_to_forms/2,
    compile_function_to_erlang/2,
    compile_erlang_function_to_erlang/2,
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
    end;

%% Compile an Erlang function (def_erl) to proper Erlang form
compile_function_to_erlang(#{name := Name, arity := Arity, params := Params, 
                            erlang_body := ErlangBody, is_erlang_function := true}, StartLine) ->
    compile_erlang_function_to_erlang(#{name => Name, arity => Arity, params => Params, erlang_body => ErlangBody}, StartLine).

%% Compile an Erlang function with raw Erlang body
compile_erlang_function_to_erlang(#{name := Name, arity := Arity, params := Params, erlang_body := ErlangBody}, StartLine) ->
    try
        % For def_erl functions, we need to parse the raw Erlang code
        % and insert it as the function body
        ParamVars = [{var, StartLine, Param} || Param <- Params],
        
        % Create parameter mapping from uppercase to lowercase
        ParamMapping = create_param_mapping(Params),
        
        % Parse the raw Erlang code to convert it to proper Erlang abstract syntax
        case parse_erlang_body(ErlangBody, StartLine, ParamMapping) of
            {ok, ParsedBody} ->
                FunctionForm = {function, StartLine, Name, Arity, [
                    {clause, StartLine, ParamVars, [], ParsedBody}
                ]},
                {ok, FunctionForm, StartLine + 20};
            {error, ParseReason} ->
                {error, {erlang_body_parse_failed, ParseReason}}
        end
    catch
        error:Reason:Stack ->
            {error, {erlang_function_compilation_failed, Name, Reason, Stack}}
    end.

%% Create mapping from uppercase variable names to parameter names
create_param_mapping(Params) ->
    lists:foldl(fun(Param, Acc) ->
        % Map both uppercase and same-case versions
        UpperParam = list_to_atom(string:uppercase(atom_to_list(Param))),
        maps:put(UpperParam, Param, maps:put(Param, Param, Acc))
    end, #{}, Params).

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
        monadic_pipe_call -> compile_monadic_pipe_call(Args, NewContext);
        make_list -> compile_make_list(Args, NewContext);
        make_tuple -> compile_make_tuple(Args, NewContext);
        make_lambda -> compile_make_lambda(Args, NewContext);
        match_tagged_tuple -> compile_match_tagged_tuple(Args, NewContext);
        match_result_tuple -> compile_match_result_tuple(Args, NewContext);
        match_list -> compile_match_list(Args, NewContext);
        match_constructor -> compile_match_constructor(Args, NewContext);
        match_literal -> compile_match_literal(Args, NewContext);
        match_any -> compile_match_any(Args, NewContext);
        advance_field -> compile_advance_field(Args, NewContext);
        bind_var -> compile_bind_var(Args, NewContext);
        pattern_fail -> compile_pattern_fail(Args, NewContext);
        jump_if_false -> compile_jump_if_false(Args, NewContext);
        jump -> compile_jump(Args, NewContext);
        label -> compile_label(Args, NewContext);
        pop -> compile_pop(Args, NewContext);
        execute_and_discard -> compile_execute_and_discard(Args, NewContext);
        return -> compile_return(Args, NewContext);
        _ -> {error, {unsupported_instruction, Op}}
    end.

%% Load literal value - just push to stack, don't generate forms
compile_load_literal([Value], Context) ->
    Form = compile_value_to_form(Value, Context#compile_context.line),
    {ok, [], push_stack(Form, Context)}.

%% Load parameter - just push to stack, don't generate forms
compile_load_param([ParamName], Context) ->
    case maps:get(ParamName, Context#compile_context.variables, undefined) of
        undefined ->
            {error, {undefined_parameter, ParamName}};
        VarForm ->
            {ok, [], push_stack(VarForm, Context)}
    end.

%% Load local variable - just push to stack, don't generate forms
compile_load_local([VarName], Context) ->
    case maps:get(VarName, Context#compile_context.variables, undefined) of
        undefined ->
            Line = Context#compile_context.line,
            VarForm = {var, Line, VarName},
            NewVariables = maps:put(VarName, VarForm, Context#compile_context.variables),
            NewContext = Context#compile_context{variables = NewVariables},
            {ok, [], push_stack(VarForm, NewContext)};
        VarForm ->
            {ok, [], push_stack(VarForm, Context)}
    end.

%% Load global function or variable - just push to stack, don't generate forms
compile_load_global([Name], Context) ->
    Line = Context#compile_context.line,
    
    % For now, just push the function name - we'll handle stdlib calls in call compilation
    Form = {atom, Line, Name},
    
    {ok, [], push_stack(Form, Context)}.

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
        Error ->
            Error
    end.

%% Compile binary operations - just push result to stack, don't generate forms
compile_binary_op([Operator], Context) ->
    case pop_two_from_stack(Context) of
        {Right, Left, NewContext} ->
            Line = NewContext#compile_context.line,
            OpForm = compile_binary_operator(Operator, Left, Right, Line),
            {ok, [], push_stack(OpForm, NewContext)};
        Error ->
            Error
    end.

%% Compile monadic pipe calls with automatic Result handling
compile_monadic_pipe_call([Arity], Context) ->
    case pop_n_from_stack(Arity + 1, Context) of  % +1 for function itself
        {Elements, NewContext} ->
            % With corrected instruction order (Function first, then Args),
            % the stack has Function at bottom, Args on top
            % After popping, we get [Function, Arg1, Arg2, ...] (no need to reverse)
            case Elements of
                [] -> 
                    {error, {empty_elements_for_call, Arity}};
                [Function | Args] when length(Args) =:= Arity ->
                    Line = NewContext#compile_context.line,
                    
                    % Create a monadic pipe operation that:
                    % 1. Wraps the first argument (piped value) with ok() if it's not already a Result
                    % 2. Checks if it's Ok(value) or Error(reason)
                    % 3. If Ok(value), unwrap and call function with unwrapped value + other args
                    % 4. If Error(reason), propagate error without calling function
                    
                    case Args of
                        [PipedValue | RestArgs] ->
                            % Generate the monadic pipe logic
                            MonadicPipeForm = generate_monadic_pipe_form(Function, PipedValue, RestArgs, Line),
                            {ok, [], push_stack(MonadicPipeForm, NewContext)};
                        [] ->
                            {error, {no_piped_value_for_monadic_pipe}}
                    end;
                _ ->
                    {error, {wrong_arity, Arity, length(Elements)}}
            end;
        Error ->
            Error
    end.

%% Compile function calls - just push result to stack, don't generate forms
compile_call([Arity], Context) ->
    case pop_n_from_stack(Arity + 1, Context) of  % +1 for function itself
        {Elements, NewContext} ->
            % With corrected instruction order (Function first, then Args),
            % the stack has Function at bottom, Args on top
            % After popping, we get [Function, Arg1, Arg2, ...] (no need to reverse)
            case Elements of
                [] -> 
                    {error, {empty_elements_for_call, Arity}};
                [Function | Args] when length(Args) =:= Arity ->
                    Line = NewContext#compile_context.line,
            
                    CallForm = case Function of
                {atom, _, FuncName} ->
                    % Check if it's a stdlib function
                    case is_stdlib_function(FuncName) of
                        true ->
                            % Remote call to stdlib
                            {call, Line, {remote, Line, {atom, Line, cure_std}, {atom, Line, FuncName}}, Args};
                        false ->
                            % Local function call
                            {call, Line, Function, Args}
                    end;
                _ ->
                    % Complex function expression
                    {call, Line, Function, Args}
                    end,
            
                    {ok, [], push_stack(CallForm, NewContext)};
                _ ->
                    {error, {wrong_arity, Arity, length(Elements)}}
            end;
        Error ->
            Error
    end.

%% Create list from stack elements
compile_make_list([Count], Context) ->
    case pop_n_from_stack(Count, Context) of
        {Elements, NewContext} ->
            Line = NewContext#compile_context.line,
            % Build proper cons list from elements
            ListForm = build_cons_list(Elements, Line),
            {ok, [], push_stack(ListForm, NewContext)};
        Error ->
            Error
    end.

%% Create tuple from stack elements
compile_make_tuple([Count], Context) ->
    case pop_n_from_stack(Count, Context) of
        {Elements, NewContext} ->
            Line = NewContext#compile_context.line,
            % Build tuple from elements
            TupleForm = {tuple, Line, Elements},
            {ok, [], push_stack(TupleForm, NewContext)};
        Error ->
            Error
    end.

%% Conditional jump (for if expressions)
compile_jump_if_false([Label], Context) ->
    case pop_stack(Context) of
        {Condition, NewContext} ->
            % This is handled at a higher level in if expression compilation
            % For now, we'll store the condition and label information
            LabelInfo = {jump_if_false, Label, Condition},
            {ok, [], store_label_info(LabelInfo, NewContext)};
        Error ->
            Error
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
        Error ->
            Error
    end.

%% Execute and discard (execute side-effecting expression and discard result)
compile_execute_and_discard([], Context) ->
    case pop_stack(Context) of
        {Value, NewContext} ->
            % Generate code that executes the expression but discards its result
            % We do this by wrapping it in a let expression that binds to _
            Line = NewContext#compile_context.line,
            ExecuteForm = {match, Line, {var, Line, '_'}, Value},
            {ok, [ExecuteForm], NewContext};
        Error ->
            Error
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

%% Lambda creation
compile_make_lambda([_LambdaName, ParamNames, _BodyInstructions, Arity], Context) ->
    Line = Context#compile_context.line,
    % Create a simple anonymous function reference for now
    % In a full implementation, this would compile the body instructions to a proper lambda
    ParamVars = [{var, Line, Param} || Param <- ParamNames],
    LambdaForm = {'fun', Line, {clauses, [
        {clause, Line, ParamVars, [], [{atom, Line, lambda_body}]}
    ]}},
    {ok, [], push_stack(LambdaForm, Context)}.

%% Tagged tuple matching (for records like Ok(value), Error(msg))
compile_match_tagged_tuple([Tag, FieldCount, _FailLabel], Context) ->
    % This should check that the value on stack is a tuple {Tag, Field1, Field2, ...}
    % For now, we'll just pop the value and push a match success
    case pop_stack(Context) of
        {Value, NewContext} ->
            Line = NewContext#compile_context.line,
            % Create a case expression to match the tagged tuple
            MatchForm = {'case', Line, Value, [
                {clause, Line, [{tuple, Line, [{atom, Line, Tag} | lists:duplicate(FieldCount, {var, Line, '_'})]}], [], [{atom, Line, match_success}]},
                {clause, Line, [{var, Line, '_'}], [], [{atom, Line, match_fail}]}
            ]},
            {ok, [], push_stack(MatchForm, NewContext)};
            Error ->
            Error
    end.

%% Result tuple matching (for Result/Option types like {'Ok', value}, {'Error', reason})
compile_match_result_tuple([Tag, FieldCount, _FailLabel], Context) ->
    % This matches Result/Option types which use simple tuple format: {'Ok', Value}, {'Error', Reason}
    io:format("DEBUG: compile_match_result_tuple called with Tag=~p, FieldCount=~p~n", [Tag, FieldCount]),
    case pop_stack(Context) of
        {Value, NewContext} ->
            Line = NewContext#compile_context.line,
            
            % FIXED VERSION: Generate proper case expression for Result pattern matching
            % The key insight is that we need to generate the complete case expression
            % that properly matches the tuple structure and binds variables correctly
            ResultCaseExpr = {'case', Line, Value, [
                % Ok(value) -> extract the value and return it
                {clause, Line, 
                 [{tuple, Line, [{atom, Line, 'Ok'}, {var, Line, 'Value'}]}], 
                 [], 
                 [{var, Line, 'Value'}]},
                % Error(reason) -> propagate the error by calling error(reason)
                {clause, Line, 
                 [{tuple, Line, [{atom, Line, 'Error'}, {var, Line, 'Reason'}]}], 
                 [], 
                 [{call, Line, {remote, Line, {atom, Line, erlang}, {atom, Line, error}}, [{var, Line, 'Reason'}]}]},
                % Fallback for other values - function clause error
                {clause, Line, 
                 [{var, Line, '_Other'}], 
                 [], 
                 [{call, Line, {remote, Line, {atom, Line, erlang}, {atom, Line, error}}, [{atom, Line, function_clause}]}]}
            ]},
            
            {ok, [], push_stack(ResultCaseExpr, NewContext)};
        Error ->
            Error
    end.

%% List pattern matching
compile_match_list([ElementCount, HasTail, _FailLabel], Context) ->
    case pop_stack(Context) of
        {Value, NewContext} ->
            Line = NewContext#compile_context.line,
            % Create pattern for list matching
            Pattern = case HasTail of
                true when ElementCount > 0 ->
                    Elements = lists:duplicate(ElementCount, {var, Line, '_'}),
                    TailVar = {var, Line, '_tail'},
                    build_list_pattern(Elements, TailVar, Line);
                false ->
                    Elements = lists:duplicate(ElementCount, {var, Line, '_'}),
                    build_list_pattern(Elements, {nil, Line}, Line)
            end,
            MatchForm = {'case', Line, Value, [
                {clause, Line, [Pattern], [], [{atom, Line, match_success}]},
                {clause, Line, [{var, Line, '_'}], [], [{atom, Line, match_fail}]}
            ]},
            {ok, [], push_stack(MatchForm, NewContext)};
        Error ->
            Error
    end.

%% Advance field (used in record pattern matching)
compile_advance_field([], Context) ->
    % This is a no-op in our simplified compilation
    % In a full implementation, this would advance to the next record field
    {ok, [], Context}.

%% Bind variable (pattern matching)
compile_bind_var([VarName], Context) ->
    case pop_stack(Context) of
        {Value, NewContext} ->
            Line = NewContext#compile_context.line,
            VarForm = {var, Line, VarName},
            MatchForm = {match, Line, VarForm, Value},
            NewVariables = maps:put(VarName, VarForm, NewContext#compile_context.variables),
            FinalContext = NewContext#compile_context{variables = NewVariables},
            {ok, [MatchForm], push_stack(VarForm, FinalContext)};
        Error ->
            Error
    end.

%% Constructor pattern matching (for Result/Option types like Ok(value), Error(reason))
compile_match_constructor([ConstructorName, ArgCount, _FailLabel], Context) ->
    case pop_stack(Context) of
        {Value, NewContext} ->
            Line = NewContext#compile_context.line,
            % Generate case expression that matches constructor patterns
            % Constructor patterns are represented as tuples: {'Ok', Value}, {'Error', Reason}, etc.
            case ArgCount of
                0 ->
                    % Constructor with no arguments like None
                    ConstructorCaseExpr = {'case', Line, Value, [
                        {clause, Line, [{atom, Line, ConstructorName}], [], [{atom, Line, match_success}]},
                        {clause, Line, [{var, Line, '_'}], [], [{atom, Line, match_fail}]}
                    ]},
                    {ok, [], push_stack(ConstructorCaseExpr, NewContext)};
                1 ->
                    % Constructor with single argument like Ok(value), Error(reason)
                    % Use underscore variables to avoid unsafe variable warnings
                    ConstructorCaseExpr = {'case', Line, Value, [
                        {clause, Line, 
                         [{tuple, Line, [{atom, Line, ConstructorName}, {var, Line, '_'}]}], 
                         [], 
                         [{atom, Line, match_success}]},
                        {clause, Line, [{var, Line, '_'}], [], [{atom, Line, match_fail}]}
                    ]},
                    {ok, [], push_stack(ConstructorCaseExpr, NewContext)};
                _ ->
                    % Constructor with multiple arguments
                    ArgVars = [{var, Line, list_to_atom("_Arg" ++ integer_to_list(I))} || I <- lists:seq(1, ArgCount)],
                    ConstructorCaseExpr = {'case', Line, Value, [
                        {clause, Line, 
                         [{tuple, Line, [{atom, Line, ConstructorName} | ArgVars]}], 
                         [], 
                         [{atom, Line, match_success}]},
                        {clause, Line, [{var, Line, '_'}], [], [{atom, Line, match_fail}]}
                    ]},
                    {ok, [], push_stack(ConstructorCaseExpr, NewContext)}
            end;
        Error ->
            Error
    end.

%% Literal pattern matching
compile_match_literal([LiteralValue, _FailLabel], Context) ->
    case pop_stack(Context) of
        {Value, NewContext} ->
            Line = NewContext#compile_context.line,
            % Generate case expression that matches literal values
            LiteralForm = compile_value_to_form(LiteralValue, Line),
            LiteralCaseExpr = {'case', Line, Value, [
                {clause, Line, [LiteralForm], [], [{atom, Line, match_success}]},
                {clause, Line, [{var, Line, '_'}], [], [{atom, Line, match_fail}]}
            ]},
            {ok, [], push_stack(LiteralCaseExpr, NewContext)};
        Error ->
            Error
    end.

%% Wildcard pattern matching (matches anything)
compile_match_any([], Context) ->
    case pop_stack(Context) of
        {_Value, NewContext} ->
            Line = NewContext#compile_context.line,
            % Wildcard always matches - just return match_success
            {ok, [], push_stack({atom, Line, match_success}, NewContext)};
        Error ->
            Error
    end.

%% Pattern match failure
compile_pattern_fail([], Context) ->
    Line = Context#compile_context.line,
    % Generate a function clause error
    FailForm = {call, Line, {remote, Line, {atom, Line, erlang}, {atom, Line, error}}, [{atom, Line, function_clause}]},
    {ok, [FailForm], Context}.

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

%% Check if function is from standard library
is_stdlib_function(ok) -> true;
is_stdlib_function(error) -> true;
is_stdlib_function(some) -> true;
is_stdlib_function(none) -> true;
is_stdlib_function('Ok') -> true;
is_stdlib_function('Error') -> true;
is_stdlib_function('Some') -> true;
is_stdlib_function('None') -> true;
is_stdlib_function(map_ok) -> true;
is_stdlib_function(bind_ok) -> true;
is_stdlib_function(map_error) -> true;
is_stdlib_function(map_some) -> true;
is_stdlib_function(bind_some) -> true;
is_stdlib_function(safe_div) -> true;
is_stdlib_function(map) -> true;
is_stdlib_function(filter) -> true;
is_stdlib_function(foldl) -> true;
is_stdlib_function(head) -> true;
is_stdlib_function(tail) -> true;
is_stdlib_function(length) -> true;
is_stdlib_function(string_concat) -> true;
is_stdlib_function(split) -> true;
is_stdlib_function(trim) -> true;
is_stdlib_function(to_upper) -> true;
is_stdlib_function(contains) -> true;
is_stdlib_function(starts_with) -> true;
is_stdlib_function(abs) -> true;
is_stdlib_function(sqrt) -> true;
is_stdlib_function(pi) -> true;
is_stdlib_function(fsm_create) -> true;
is_stdlib_function(fsm_send_safe) -> true;
is_stdlib_function(create_counter) -> true;
is_stdlib_function(print) -> true;
is_stdlib_function(println) -> true;
is_stdlib_function(int_to_string) -> true;
is_stdlib_function(float_to_string) -> true;
is_stdlib_function(list_to_string) -> true;
is_stdlib_function(join_ints) -> true;
is_stdlib_function(string_empty) -> true;
is_stdlib_function(string_join) -> true;
is_stdlib_function(_) -> false.

%% Get function arity for stdlib functions
get_function_arity(ok) -> 1;
get_function_arity(error) -> 1;
get_function_arity(some) -> 1;
get_function_arity(none) -> 0;
get_function_arity('Ok') -> 1;
get_function_arity('Error') -> 1;
get_function_arity('Some') -> 1;
get_function_arity('None') -> 0;
get_function_arity(map_ok) -> 2;
get_function_arity(bind_ok) -> 2;
get_function_arity(map_error) -> 2;
get_function_arity(map_some) -> 2;
get_function_arity(bind_some) -> 2;
get_function_arity(safe_div) -> 2;
get_function_arity(map) -> 2;
get_function_arity(filter) -> 2;
get_function_arity(foldl) -> 3;
get_function_arity(head) -> 1;
get_function_arity(tail) -> 1;
get_function_arity(length) -> 1;
get_function_arity(string_concat) -> 2;
get_function_arity(split) -> 2;
get_function_arity(trim) -> 1;
get_function_arity(to_upper) -> 1;
get_function_arity(contains) -> 2;
get_function_arity(starts_with) -> 2;
get_function_arity(abs) -> 1;
get_function_arity(sqrt) -> 1;
get_function_arity(pi) -> 0;
get_function_arity(fsm_create) -> 2;
get_function_arity(fsm_send_safe) -> 2;
get_function_arity(create_counter) -> 1;
get_function_arity(print) -> 1;
get_function_arity(println) -> 1;
get_function_arity(int_to_string) -> 1;
get_function_arity(float_to_string) -> 1;
get_function_arity(list_to_string) -> 1;
get_function_arity(join_ints) -> 2;
get_function_arity(string_empty) -> 1;
get_function_arity(string_join) -> 2;
get_function_arity(_) -> 0.

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
compile_binary_operator('++', Left, Right, Line) ->
    {op, Line, '++', Left, Right};
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
                Error ->
                    Error
            end;
        Error ->
            Error
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
        Error ->
            Error
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
store_label_info(_LabelInfo, Context) ->
    % For now, we'll store label info in the context
    % In a full implementation, this would be used for proper control flow
    Context.

%% ============================================================================
%% Optimization Functions
%% ============================================================================

%% Build proper cons list from elements
build_cons_list([], Line) ->
    {nil, Line};
build_cons_list([Element], Line) ->
    {cons, Line, Element, {nil, Line}};
build_cons_list([H | T], Line) ->
    {cons, Line, H, build_cons_list(T, Line)}.

%% Build list pattern for pattern matching
build_list_pattern([], Tail, _Line) ->
    Tail;
build_list_pattern([H | T], Tail, Line) ->
    {cons, Line, H, build_list_pattern(T, Tail, Line)}.

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

%% ============================================================================
%% Erlang Code Parsing for def_erl
%% ============================================================================

%% Parse raw Erlang code string into Erlang abstract syntax
%% This converts the tokenized Erlang body back to abstract forms
parse_erlang_body(ErlangBody, StartLine) ->
    parse_erlang_body(ErlangBody, StartLine, #{}).

parse_erlang_body(ErlangBody, StartLine, ParamMapping) ->
    try
        % The ErlangBody is a string containing raw Erlang code
        % For now, we'll create a simple body by parsing it as a simple expression
        case parse_simple_erlang_expression(ErlangBody, StartLine, ParamMapping) of
            {ok, ParsedExpr} ->
                {ok, [ParsedExpr]};
            {error, Reason} ->
                {error, Reason}
        end
    catch
        error:ParseError ->
            {error, {parse_error, ParseError}}
    end.

%% Parse simple Erlang expressions
%% This is a simplified parser for common Erlang patterns
parse_simple_erlang_expression(ErlangCode, Line) ->
    parse_simple_erlang_expression(ErlangCode, Line, #{}).

parse_simple_erlang_expression(ErlangCode, Line, ParamMapping) ->
    try
        % Handle common cases that def_erl will use
        TrimmedCode = string:trim(ErlangCode),
        
        case TrimmedCode of
            "length ( " ++ Rest ->
                % Handle length(list) calls
                case parse_function_call("length", Rest, Line, ParamMapping) of
                    {ok, Call} -> {ok, Call};
                    error -> parse_as_simple_term(TrimmedCode, Line, ParamMapping)
                end;
            "lists reverse ( " ++ Rest ->
                % Handle lists:reverse(list) calls
                case parse_remote_call("lists", "reverse", Rest, Line, ParamMapping) of
                    {ok, Call} -> {ok, Call};
                    error -> parse_as_simple_term(TrimmedCode, Line, ParamMapping)
                end;
            _ when TrimmedCode =:= "42" orelse 
                   TrimmedCode =:= "result" orelse
                   TrimmedCode =:= "Result" ->
                parse_as_simple_term(TrimmedCode, Line, ParamMapping);
            _ ->
                % For more complex cases, parse as general Erlang code
                parse_general_erlang_code(TrimmedCode, Line, ParamMapping)
        end
    catch
        error:Reason ->
            {error, {expression_parse_error, Reason}}
    end.

%% Parse function calls like "length(list)"
parse_function_call(FuncName, Rest, Line) ->
    parse_function_call(FuncName, Rest, Line, #{}).

parse_function_call(FuncName, Rest, Line, ParamMapping) ->
    case extract_args_from_call(Rest) of
        {ok, Args} ->
            ArgForms = [parse_simple_arg(Arg, Line, ParamMapping) || Arg <- Args],
            Call = {call, Line, {atom, Line, list_to_atom(FuncName)}, ArgForms},
            {ok, Call};
        error ->
            error
    end.

%% Parse remote calls like "lists:reverse(list)"
parse_remote_call(ModuleName, FuncName, Rest, Line) ->
    parse_remote_call(ModuleName, FuncName, Rest, Line, #{}).

parse_remote_call(ModuleName, FuncName, Rest, Line, ParamMapping) ->
    case extract_args_from_call(Rest) of
        {ok, Args} ->
            ArgForms = [parse_simple_arg(Arg, Line, ParamMapping) || Arg <- Args],
            Call = {call, Line, 
                   {remote, Line, {atom, Line, list_to_atom(ModuleName)}, 
                    {atom, Line, list_to_atom(FuncName)}}, 
                   ArgForms},
            {ok, Call};
        error ->
            error
    end.

%% Extract arguments from function call string
extract_args_from_call(CallRest) ->
    % Simple parsing for "arg1, arg2, ...)"
    case string:split(CallRest, ")", leading) of
        [ArgsStr, _] ->
            ArgsList = string:split(string:trim(ArgsStr), ",", all),
            CleanArgs = [string:trim(Arg) || Arg <- ArgsList, string:trim(Arg) =/= ""],
            {ok, CleanArgs};
        _ ->
            error
    end.

%% Parse simple arguments
parse_simple_arg(Arg, Line) ->
    parse_simple_arg(Arg, Line, #{}).

parse_simple_arg(Arg, Line, ParamMapping) ->
    case string:to_integer(Arg) of
        {Int, []} -> {integer, Line, Int};
        _ ->
            case string:to_float(Arg) of
                {Float, []} -> {float, Line, Float};
                _ ->
                    % Treat as variable - check parameter mapping first
                    VarName = list_to_atom(Arg),
                    case maps:get(VarName, ParamMapping, undefined) of
                        undefined ->
                            {var, Line, VarName};
                        MappedName ->
                            {var, Line, MappedName}
                    end
            end
    end.

%% Parse as simple term (literals, variables)
parse_as_simple_term(Term, Line) ->
    parse_as_simple_term(Term, Line, #{}).

parse_as_simple_term(Term, Line, ParamMapping) ->
    case string:to_integer(Term) of
        {Int, []} -> 
            {ok, {integer, Line, Int}};
        _ ->
            case string:to_float(Term) of
                {Float, []} -> 
                    {ok, {float, Line, Float}};
                _ ->
                    % Treat as variable name - check parameter mapping first
                    case Term of
                        [C|_] when C >= $A, C =< $Z; C >= $a, C =< $z ->
                            VarName = list_to_atom(Term),
                            case maps:get(VarName, ParamMapping, undefined) of
                                undefined ->
                                    {ok, {var, Line, VarName}};
                                MappedName ->
                                    {ok, {var, Line, MappedName}}
                            end;
                        _ ->
                            % Default to atom
                            AtomName = list_to_atom(Term),
                            {ok, {atom, Line, AtomName}}
                    end
            end
    end.

%% Parse general Erlang code using erl_scan and erl_parse
parse_general_erlang_code(ErlangCode, Line) ->
    parse_general_erlang_code(ErlangCode, Line, #{}).

parse_general_erlang_code(ErlangCode, Line, ParamMapping) ->
    try
        % Add a period if it doesn't end with one
        CodeWithPeriod = case lists:last(ErlangCode) of
            $. -> ErlangCode;
            _ -> ErlangCode ++ "."
        end,
        
        % Try to tokenize and parse the code
        case erl_scan:string(CodeWithPeriod, Line) of
            {ok, Tokens, _} ->
                case erl_parse:parse_exprs(Tokens) of
                    {ok, [Expr]} -> 
                        % Apply parameter mapping to the parsed expression
                        MappedExpr = apply_param_mapping_to_expr(Expr, ParamMapping),
                        {ok, MappedExpr};
                    {ok, Exprs} ->
                        % Multiple expressions, wrap in a block and apply mapping
                        MappedExprs = [apply_param_mapping_to_expr(E, ParamMapping) || E <- Exprs],
                        {ok, {block, Line, MappedExprs}};
                    {error, ParseError} ->
                        {error, {parse_error, ParseError}}
                end;
            {error, ScanError, _} ->
                {error, {scan_error, ScanError}}
        end
    catch
        error:GeneralError ->
            % If general parsing fails, fall back to atom
            {ok, {atom, Line, list_to_atom("erlang_code")}}
    end.

%% Apply parameter mapping to Erlang expression AST
apply_param_mapping_to_expr(Expr, ParamMapping) when map_size(ParamMapping) == 0 ->
    Expr;  % No mapping needed
apply_param_mapping_to_expr({var, Line, VarName}, ParamMapping) ->
    case maps:get(VarName, ParamMapping, undefined) of
        undefined -> {var, Line, VarName};
        MappedName -> {var, Line, MappedName}
    end;
apply_param_mapping_to_expr({call, Line, Func, Args}, ParamMapping) ->
    MappedFunc = apply_param_mapping_to_expr(Func, ParamMapping),
    MappedArgs = [apply_param_mapping_to_expr(Arg, ParamMapping) || Arg <- Args],
    {call, Line, MappedFunc, MappedArgs};
apply_param_mapping_to_expr({'case', Line, Expr, Clauses}, ParamMapping) ->
    MappedExpr = apply_param_mapping_to_expr(Expr, ParamMapping),
    MappedClauses = [apply_param_mapping_to_clause(Clause, ParamMapping) || Clause <- Clauses],
    {'case', Line, MappedExpr, MappedClauses};
apply_param_mapping_to_expr({block, Line, Exprs}, ParamMapping) ->
    MappedExprs = [apply_param_mapping_to_expr(E, ParamMapping) || E <- Exprs],
    {block, Line, MappedExprs};
apply_param_mapping_to_expr({op, Line, Op, Left, Right}, ParamMapping) ->
    MappedLeft = apply_param_mapping_to_expr(Left, ParamMapping),
    MappedRight = apply_param_mapping_to_expr(Right, ParamMapping),
    {op, Line, Op, MappedLeft, MappedRight};
apply_param_mapping_to_expr({match, Line, Left, Right}, ParamMapping) ->
    MappedLeft = apply_param_mapping_to_expr(Left, ParamMapping),
    MappedRight = apply_param_mapping_to_expr(Right, ParamMapping),
    {match, Line, MappedLeft, MappedRight};
apply_param_mapping_to_expr(Expr, _ParamMapping) ->
    Expr.  % For literals and other forms, no mapping needed

%% Apply parameter mapping to case clause
apply_param_mapping_to_clause({clause, Line, Patterns, Guards, Body}, ParamMapping) ->
    MappedPatterns = [apply_param_mapping_to_expr(P, ParamMapping) || P <- Patterns],
    MappedGuards = [apply_param_mapping_to_expr(G, ParamMapping) || G <- Guards],
    MappedBody = [apply_param_mapping_to_expr(B, ParamMapping) || B <- Body],
    {clause, Line, MappedPatterns, MappedGuards, MappedBody}.

%% ============================================================================
%% Monadic Pipe Operation Generation
%% ============================================================================

%% Generate monadic pipe operation form
%% This creates Erlang code that implements the monadic pipe behavior:
%% 1. Wrap the piped value with ok() if it's not already a Result
%% 2. Use cure_std:and_then to chain the operation monadically
generate_monadic_pipe_form(Function, PipedValue, RestArgs, Line) ->
    % First, wrap the piped value with ok()
    WrappedValue = {call, Line, 
                   {remote, Line, {atom, Line, cure_std}, {atom, Line, ok}}, 
                   [PipedValue]},
    
    % Create a lambda function that wraps the target function
    % This lambda will receive the unwrapped value and call the target function
    LambdaVar = {var, Line, 'X'},
    LambdaCallArgs = [LambdaVar | RestArgs],
    
    % Create the function call inside the lambda
    LambdaCall = case Function of
        {atom, _, FuncName} ->
            case is_stdlib_function(FuncName) of
                true ->
                    {call, Line, {remote, Line, {atom, Line, cure_std}, Function}, LambdaCallArgs};
                false ->
                    {call, Line, Function, LambdaCallArgs}
            end;
        _ ->
            {call, Line, Function, LambdaCallArgs}
    end,
    
    % For monadic pipe, we need to wrap the result in a Result type
    % Since the functions expect raw values but pipe chain expects Results
    WrappedCall = {call, Line, 
                  {remote, Line, {atom, Line, cure_std}, {atom, Line, ok}}, 
                  [LambdaCall]},
    
    % Create the lambda function
    LambdaFunction = {'fun', Line, {clauses, [
        {clause, Line, [LambdaVar], [], [WrappedCall]}
    ]}},
    
    % Use cure_std:and_then to chain the operations monadically
    % Note: and_then expects (Function, Result) order according to cure_std.erl
    {call, Line,
     {remote, Line, {atom, Line, cure_std}, {atom, Line, and_then}},
     [LambdaFunction, WrappedValue]}.
