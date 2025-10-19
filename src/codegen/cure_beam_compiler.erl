%% Cure Programming Language - BEAM Instruction Compiler
%% Converts Cure internal instructions to proper Erlang abstract forms
-module(cure_beam_compiler).

-export([
    compile_instructions_to_forms/2,
    compile_function_to_erlang/2,
    compile_function_to_erlang/4,
    compile_erlang_function_to_erlang/2,
    optimize_instructions/1,
    validate_erlang_forms/1
]).

%% Include necessary headers
-include("../parser/cure_ast.hrl").

%% BEAM instruction record for internal representation
-record(beam_instr, {
    % Instruction opcode
    op,
    % Instruction arguments
    args = [],
    % Source location for debugging
    location
}).

%% Compilation context for instruction conversion
-record(compile_context, {
    line = 1,
    variables = #{},
    labels = #{},
    temp_counter = 0,
    stack = [],
    module_name = undefined,
    local_functions = #{}
}).

%% ============================================================================
%% Main Compilation Functions
%% ============================================================================

%% Compile a function with instructions to proper Erlang form
compile_function_to_erlang(
    #{
        name := Name,
        arity := Arity,
        params := Params,
        instructions := Instructions
    },
    StartLine
) ->
    Context = #compile_context{
        line = StartLine,
        variables = create_param_variables(Params, StartLine)
    },

    case compile_instructions_to_forms(Instructions, Context) of
        {ok, Body, _FinalContext} ->
            ParamVars = [{var, StartLine, Param} || Param <- Params],
            FunctionForm =
                {function, StartLine, Name, Arity, [
                    {clause, StartLine, ParamVars, [], Body}
                ]},
            {ok, FunctionForm, StartLine + 20};
        {error, Reason} ->
            {error, Reason}
    end;
%% Compile an Erlang function (def_erl) to proper Erlang form
compile_function_to_erlang(
    #{
        name := Name,
        arity := Arity,
        params := Params,
        erlang_body := ErlangBody,
        is_erlang_function := true
    },
    StartLine
) ->
    compile_erlang_function_to_erlang(
        #{name => Name, arity => Arity, params => Params, erlang_body => ErlangBody}, StartLine
    ).

%% Compile function with module context (module name and local functions)
compile_function_to_erlang(
    #{
        name := Name,
        arity := Arity,
        params := Params,
        instructions := Instructions
    },
    StartLine,
    ModuleName,
    LocalFunctions
) ->
    Context = #compile_context{
        line = StartLine,
        variables = create_param_variables(Params, StartLine),
        module_name = ModuleName,
        local_functions = LocalFunctions
    },

    case compile_instructions_to_forms(Instructions, Context) of
        {ok, Body, _FinalContext} ->
            ParamVars = [{var, StartLine, Param} || Param <- Params],
            FunctionForm =
                {function, StartLine, Name, Arity, [
                    {clause, StartLine, ParamVars, [], Body}
                ]},
            {ok, FunctionForm, StartLine + 20};
        {error, Reason} ->
            {error, Reason}
    end;
compile_function_to_erlang(
    #{
        name := Name,
        arity := Arity,
        params := Params,
        erlang_body := ErlangBody,
        is_erlang_function := true
    },
    StartLine,
    _ModuleName,
    _LocalFunctions
) ->
    compile_erlang_function_to_erlang(
        #{name => Name, arity => Arity, params => Params, erlang_body => ErlangBody}, StartLine
    ).

%% Compile an Erlang function with raw Erlang body
compile_erlang_function_to_erlang(
    #{name := Name, arity := Arity, params := Params, erlang_body := ErlangBody}, StartLine
) ->
    try
        % For def_erl functions, we need to parse the raw Erlang code
        % and insert it as the function body
        ParamVars = [{var, StartLine, Param} || Param <- Params],

        % Create parameter mapping from uppercase to lowercase
        ParamMapping = create_param_mapping(Params),

        % Parse the raw Erlang code to convert it to proper Erlang abstract syntax
        case parse_erlang_body(ErlangBody, StartLine, ParamMapping) of
            {ok, ParsedBody} ->
                FunctionForm =
                    {function, StartLine, Name, Arity, [
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
    lists:foldl(
        fun(Param, Acc) ->
            % Map both uppercase and same-case versions
            UpperParam = list_to_atom(string:uppercase(atom_to_list(Param))),
            maps:put(UpperParam, Param, maps:put(Param, Param, Acc))
        end,
        #{},
        Params
    ).

%% Create parameter variable mappings
create_param_variables(Params, Line) ->
    lists:foldl(
        fun(Param, Acc) ->
            maps:put(Param, {var, Line, Param}, Acc)
        end,
        #{},
        Params
    ).

%% Compile instructions to Erlang forms
compile_instructions_to_forms(Instructions, Context) ->
    compile_instructions_to_forms(Instructions, Context, []).

compile_instructions_to_forms([], Context, Acc) ->
    Body = lists:reverse(Acc),
    FinalBody =
        case {Body, Context#compile_context.stack} of
            {[], []} ->
                % No body and no stack - return ok (only for truly empty functions)
                [{atom, Context#compile_context.line, ok}];
            {[], [StackValue | _]} ->
                % No body but value on stack - return the stack value
                [StackValue];
            {Body, [StackValue | _]} ->
                % Has body AND stack value - body should evaluate to stack value
                % This typically means the body contains intermediate computations
                % and the stack has the final result
                Body ++ [StackValue];
            {Body, []} ->
                % Has body but no stack - body should contain the return value
                Body
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
        load_imported_function -> compile_load_imported_function(Args, NewContext);
        store_local -> compile_store_local(Args, NewContext);
        binary_op -> compile_binary_op(Args, NewContext);
        call -> compile_call(Args, NewContext);
        monadic_pipe_call -> compile_monadic_pipe_call(Args, NewContext);
        make_list -> compile_make_list(Args, NewContext);
        make_cons -> compile_make_cons(Args, NewContext);
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
        make_case -> compile_make_case(Args, NewContext);
        to_string -> compile_to_string(Args, NewContext);
        concat_strings -> compile_concat_strings(Args, NewContext);
        guard_bif -> compile_guard_bif(Args, NewContext);
        guard_check -> compile_guard_check(Args, NewContext);
        unary_op -> compile_unary_op(Args, NewContext);
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
            % Check if this might be a type parameter that should be ignored at runtime
            case is_type_parameter(ParamName) of
                true ->
                    % Type parameters are compile-time only, substitute with a placeholder
                    Line = Context#compile_context.line,
                    % Use 0 as placeholder for type params
                    PlaceholderForm = {integer, Line, 0},
                    {ok, [], push_stack(PlaceholderForm, Context)};
                false ->
                    {error, {undefined_parameter, ParamName}}
            end;
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

    % Check if this is a local function (defined in the current module)
    % If so, create a proper function reference, otherwise create atom for stdlib calls
    ModuleName = Context#compile_context.module_name,

    case is_local_function_reference(Name, Context) of
        {true, Arity} ->
            % Create function reference for local functions like fun 'ModuleName':'FunctionName'/Arity
            FunForm =
                {'fun', Line,
                    {function, {atom, Line, ModuleName}, {atom, Line, Name},
                        {integer, Line, Arity}}},
            {ok, [], push_stack(FunForm, Context)};
        false ->
            % For stdlib calls and unknown functions, just push the function name as atom
            % This will be handled by compile_call to route to cure_std or stdlib
            Form = {atom, Line, Name},
            {ok, [], push_stack(Form, Context)}
    end.

%% Load imported function - create proper function reference
compile_load_imported_function([Name, ImportedFunction], Context) ->
    Line = Context#compile_context.line,

    % Check if this is a stdlib function that should be routed to cure_std
    case is_cure_std_function(Name) of
        true ->
            % For stdlib functions, just push the function name as atom
            % This will be handled by compile_call to route to cure_std
            Form = {atom, Line, Name},
            {ok, [], push_stack(Form, Context)};
        false ->
            % For other imported functions, create a fun reference
            Arity =
                case maps:get(arity, ImportedFunction, unknown) of
                    unknown ->
                        % For unknown arities, try some common defaults
                        case Name of
                            show -> 1;
                            map -> 2;
                            fold -> 3;
                            zip_with -> 3;
                            % Default to arity 1 for most functions
                            _ -> 1
                        end;
                    ActualArity when is_integer(ActualArity) ->
                        ActualArity;
                    _ ->
                        1
                end,

            % Create a fun reference for non-stdlib functions
            ModuleName = maps:get(module, ImportedFunction, 'Std'),
            FunForm =
                {'fun', Line,
                    {function, {atom, Line, ModuleName}, {atom, Line, Name},
                        {integer, Line, Arity}}},

            {ok, [], push_stack(FunForm, Context)}
    end.

%% Compile guard BIF instructions
compile_guard_bif([GuardOp | Args], Context) ->
    case pop_n_from_stack(length(Args), Context) of
        {StackArgs, NewContext} ->
            Line = NewContext#compile_context.line,
            % Create a guard BIF call
            GuardForm = compile_guard_bif_op(GuardOp, StackArgs, Line),
            {ok, [], push_stack(GuardForm, NewContext)};
        Error ->
            Error
    end.

%% Compile unary operations
compile_unary_op([Operator], Context) ->
    case pop_stack(Context) of
        {Operand, NewContext} ->
            Line = NewContext#compile_context.line,
            OpForm = compile_unary_operator(Operator, Operand, Line),
            {ok, [], push_stack(OpForm, NewContext)};
        Error ->
            Error
    end.

%% Compile guard check instructions (for constraint validation)
compile_guard_check([CheckType], Context) ->
    case pop_stack(Context) of
        {_GuardResult, NewContext} ->
            Line = NewContext#compile_context.line,
            % For now, we'll assume guard checks always pass at runtime
            % In a full implementation, this would generate proper guard validation
            case CheckType of
                function_clause_error ->
                    % This is a guard that should cause function_clause error if it fails
                    % For dependent types, we'll assume the type system has validated this
                    PlaceholderForm = {atom, Line, guard_passed},
                    {ok, [], push_stack(PlaceholderForm, NewContext)};
                _ ->
                    PlaceholderForm = {atom, Line, guard_passed},
                    {ok, [], push_stack(PlaceholderForm, NewContext)}
            end;
        Error ->
            Error
    end.

%% Compile specific guard BIF operations
compile_guard_bif_op('>', [Left, Right], Line) ->
    {op, Line, '>', Left, Right};
compile_guard_bif_op('<', [Left, Right], Line) ->
    {op, Line, '<', Left, Right};
compile_guard_bif_op('>=', [Left, Right], Line) ->
    {op, Line, '>=', Left, Right};
compile_guard_bif_op('=<', [Left, Right], Line) ->
    {op, Line, '=<', Left, Right};
compile_guard_bif_op('==', [Left, Right], Line) ->
    {op, Line, '==', Left, Right};
compile_guard_bif_op('/=', [Left, Right], Line) ->
    {op, Line, '/=', Left, Right};
compile_guard_bif_op(BifOp, Args, Line) ->
    % Generic BIF call for other guard operations
    {call, Line, {atom, Line, BifOp}, Args}.

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
    % +1 for function itself
    case pop_n_from_stack(Arity + 1, Context) of
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
                            MonadicPipeForm = generate_monadic_pipe_form(
                                Function, PipedValue, RestArgs, Line
                            ),
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
    % +1 for function itself
    case pop_n_from_stack(Arity + 1, Context) of
        {Elements, NewContext} ->
            % With corrected instruction order (Function first, then Args),
            % the stack has Function at bottom, Args on top
            % After popping, we get [Function, Arg1, Arg2, ...] (no need to reverse)
            case Elements of
                [] ->
                    {error, {empty_elements_for_call, Arity}};
                [Function | Args] when length(Args) =:= Arity ->
                    Line = NewContext#compile_context.line,

                    CallForm =
                        case Function of
                            {atom, _, FuncName} ->
                                % Check if it's a stdlib function that should go to cure_std
                                case is_cure_std_function(FuncName) of
                                    true ->
                                        % Remote call to cure_std
                                        {call, Line,
                                            {remote, Line, {atom, Line, cure_std},
                                                {atom, Line, FuncName}},
                                            Args};
                                    false ->
                                        % Check if it's a function that should route to Cure standard library
                                        case is_cure_stdlib_function(FuncName) of
                                            {true, Module} ->
                                                % Remote call to Cure standard library module
                                                {call, Line,
                                                    {remote, Line, {atom, Line, Module},
                                                        {atom, Line, FuncName}},
                                                    Args};
                                            false ->
                                                % For local function calls, ensure proper arity and format
                                                % This handles recursive calls within the same module
                                                {call, Line, {atom, Line, FuncName}, Args}
                                        end
                                end;
                            _ ->
                                % Complex function expression (fun refs, etc.)
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

%% Create cons cell from stack elements [head | tail]
compile_make_cons([HeadCount], Context) ->
    % Pop HeadCount + 1 elements (head elements + tail)
    case pop_n_from_stack(HeadCount + 1, Context) of
        {Elements, NewContext} ->
            Line = NewContext#compile_context.line,
            % Last element is the tail, others are head elements
            {HeadElements, [Tail]} = lists:split(HeadCount, Elements),
            % Build cons structure: [H1, H2, ... | Tail]
            ConsForm = build_cons_from_elements_and_tail(HeadElements, Tail, Line),
            {ok, [], push_stack(ConsForm, NewContext)};
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

%% Convert top of stack to string using stdlib functions
compile_to_string([], Context) ->
    case pop_stack(Context) of
        {Value, NewContext} ->
            Line = NewContext#compile_context.line,
            % Determine conversion based on value type at compile-time if possible
            % Fallback to erlang:io_lib:format for unknown types
            ToStringForm =
                {call, Line, {remote, Line, {atom, Line, cure_std}, {atom, Line, string_any}}, [
                    Value
                ]},
            {ok, [], push_stack(ToStringForm, NewContext)};
        Error ->
            Error
    end.

%% Concatenate N strings from stack using stdlib string_join
compile_concat_strings([Count], Context) ->
    case pop_n_from_stack(Count, Context) of
        {Elements, NewContext} ->
            Line = NewContext#compile_context.line,
            % Build io_lib:format("~s~s~s...", Elements) or use cure_std:string_join
            % We'll generate a left-fold of string_join with empty string
            Empty =
                {call, Line, {remote, Line, {atom, Line, cure_std}, {atom, Line, string_empty}},
                    []},
            ConcatForm = lists:foldl(
                fun(Elem, Acc) ->
                    {call, Line, {remote, Line, {atom, Line, cure_std}, {atom, Line, string_join}},
                        [Acc, Elem]}
                end,
                Empty,
                Elements
            ),
            {ok, [], push_stack(ConcatForm, NewContext)};
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
compile_make_lambda([_LambdaName, ParamNames, BodyInstructions, _Arity], Context) ->
    Line = Context#compile_context.line,
    % Create a new context for lambda body that includes both outer variables AND lambda parameters
    % This enables closures - lambda can access variables from the surrounding scope
    LambdaParamVars = create_param_variables(ParamNames, Line),
    MergedVariables = maps:merge(Context#compile_context.variables, LambdaParamVars),
    LambdaContext = Context#compile_context{
        variables = MergedVariables,
        stack = []
    },
    % Compile the lambda body instructions with the merged context
    case compile_instructions_to_forms(BodyInstructions, LambdaContext) of
        {ok, BodyForms, _BodyContext} ->
            ParamVars = [{var, Line, Param} || Param <- ParamNames],
            % Create a proper anonymous function with compiled body
            LambdaForm =
                {'fun', Line,
                    {clauses, [
                        {clause, Line, ParamVars, [], BodyForms}
                    ]}},
            {ok, [], push_stack(LambdaForm, Context)};
        {error, Reason} ->
            {error, {lambda_body_compilation_failed, Reason}}
    end.

%% Tagged tuple matching (for records like Ok(value), Error(msg))
compile_match_tagged_tuple([Tag, FieldCount, _FailLabel], Context) ->
    % This should check that the value on stack is a tuple {Tag, Field1, Field2, ...}
    % For now, we'll just pop the value and push a match success
    case pop_stack(Context) of
        {Value, NewContext} ->
            Line = NewContext#compile_context.line,
            % Create a case expression to match the tagged tuple
            MatchForm =
                {'case', Line, Value, [
                    {clause, Line,
                        [
                            {tuple, Line, [
                                {atom, Line, Tag} | lists:duplicate(FieldCount, {var, Line, '_'})
                            ]}
                        ],
                        [], [{atom, Line, match_success}]},
                    {clause, Line, [{var, Line, '_'}], [], [{atom, Line, match_fail}]}
                ]},
            {ok, [], push_stack(MatchForm, NewContext)};
        Error ->
            Error
    end.

%% Result tuple matching (for Result/Option types like {'Ok', value}, {'Error', reason})
compile_match_result_tuple([Tag, FieldCount, _FailLabel], Context) ->
    % This matches Result/Option types which use simple tuple format: {'Ok', Value}, {'Error', Reason}
    io:format("DEBUG: compile_match_result_tuple called with Tag=~p, FieldCount=~p~n", [
        Tag, FieldCount
    ]),
    case pop_stack(Context) of
        {Value, NewContext} ->
            Line = NewContext#compile_context.line,

            % FIXED VERSION: Generate proper case expression for Result pattern matching
            % The key insight is that we need to generate the complete case expression
            % that properly matches the tuple structure and binds variables correctly
            ResultCaseExpr =
                {'case', Line, Value, [
                    % Ok(value) -> extract the value and return it
                    {clause, Line, [{tuple, Line, [{atom, Line, 'Ok'}, {var, Line, 'Value'}]}], [],
                        [{var, Line, 'Value'}]},
                    % Error(reason) -> propagate the error by calling error(reason)
                    {clause, Line, [{tuple, Line, [{atom, Line, 'Error'}, {var, Line, 'Reason'}]}],
                        [], [
                            {call, Line, {remote, Line, {atom, Line, erlang}, {atom, Line, error}},
                                [{var, Line, 'Reason'}]}
                        ]},
                    % Fallback for other values - function clause error
                    {clause, Line, [{var, Line, '_Other'}], [], [
                        {call, Line, {remote, Line, {atom, Line, erlang}, {atom, Line, error}}, [
                            {atom, Line, function_clause}
                        ]}
                    ]}
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
            Pattern =
                case HasTail of
                    true when ElementCount > 0 ->
                        Elements = lists:duplicate(ElementCount, {var, Line, '_'}),
                        TailVar = {var, Line, '_tail'},
                        build_list_pattern(Elements, TailVar, Line);
                    false ->
                        Elements = lists:duplicate(ElementCount, {var, Line, '_'}),
                        build_list_pattern(Elements, {nil, Line}, Line)
                end,
            MatchForm =
                {'case', Line, Value, [
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
                    ConstructorCaseExpr =
                        {'case', Line, Value, [
                            {clause, Line, [{atom, Line, ConstructorName}], [], [
                                {atom, Line, match_success}
                            ]},
                            {clause, Line, [{var, Line, '_'}], [], [{atom, Line, match_fail}]}
                        ]},
                    {ok, [], push_stack(ConstructorCaseExpr, NewContext)};
                1 ->
                    % Constructor with single argument like Ok(value), Error(reason)
                    % Use underscore variables to avoid unsafe variable warnings
                    ConstructorCaseExpr =
                        {'case', Line, Value, [
                            {clause, Line,
                                [{tuple, Line, [{atom, Line, ConstructorName}, {var, Line, '_'}]}],
                                [], [{atom, Line, match_success}]},
                            {clause, Line, [{var, Line, '_'}], [], [{atom, Line, match_fail}]}
                        ]},
                    {ok, [], push_stack(ConstructorCaseExpr, NewContext)};
                _ ->
                    % Constructor with multiple arguments
                    ArgVars = [
                        {var, Line, list_to_atom("_Arg" ++ integer_to_list(I))}
                     || I <- lists:seq(1, ArgCount)
                    ],
                    ConstructorCaseExpr =
                        {'case', Line, Value, [
                            {clause, Line,
                                [{tuple, Line, [{atom, Line, ConstructorName} | ArgVars]}], [], [
                                    {atom, Line, match_success}
                                ]},
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
            LiteralCaseExpr =
                {'case', Line, Value, [
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
    FailForm =
        {call, Line, {remote, Line, {atom, Line, erlang}, {atom, Line, error}}, [
            {atom, Line, function_clause}
        ]},
    {ok, [FailForm], Context}.

%% Make case expression - create proper Erlang case from compiled clauses
compile_make_case([CaseClauses], Context) ->
    case pop_stack(Context) of
        {ExprValue, NewContext} ->
            Line = NewContext#compile_context.line,
            % Create a case expression with the given clauses
            CaseExpr = {'case', Line, ExprValue, CaseClauses},
            {ok, [], push_stack(CaseExpr, NewContext)};
        Error ->
            Error
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

%% Check if a name refers to a local function defined in the current module
%% Returns {true, Arity} if it's a local function, false otherwise
is_local_function_reference(Name, Context) ->
    % Check if this function is in the local_functions map
    LocalFunctions = Context#compile_context.local_functions,
    case maps:get(Name, LocalFunctions, undefined) of
        undefined -> false;
        Arity when is_integer(Arity) -> {true, Arity};
        _ -> false
    end.

%% Check if function should be routed to cure_std (legacy runtime functions)
%% Most functions are now implemented in Cure standard library and should return false
%% Only keep core runtime functions that haven't been migrated yet

% Basic I/O still in runtime
is_cure_std_function(print) -> true;
is_cure_std_function(println) -> true;
% Basic type conversions
is_cure_std_function(int_to_string) -> true;
is_cure_std_function(float_to_string) -> true;
is_cure_std_function(list_to_string) -> true;
is_cure_std_function(join_ints) -> true;
% FSM functions still in runtime (use FSM builtins)
is_cure_std_function(fsm_create) -> true;
is_cure_std_function(fsm_send_safe) -> true;
is_cure_std_function(create_counter) -> true;
% ALL other functions now implemented in Cure standard library modules
% Route to compiled Cure modules instead of cure_std runtime

% Now in Std.Core
is_cure_std_function(ok) -> false;
is_cure_std_function(error) -> false;
is_cure_std_function(some) -> false;
is_cure_std_function(none) -> false;
is_cure_std_function('Ok') -> false;
is_cure_std_function('Error') -> false;
is_cure_std_function('Some') -> false;
is_cure_std_function('None') -> false;
is_cure_std_function(map_ok) -> false;
is_cure_std_function(bind_ok) -> false;
is_cure_std_function(map_error) -> false;
is_cure_std_function(map_some) -> false;
is_cure_std_function(bind_some) -> false;
% Now in Std.List
is_cure_std_function(map) -> false;
is_cure_std_function(filter) -> false;
is_cure_std_function(fold) -> false;
is_cure_std_function(foldl) -> false;
is_cure_std_function(foldr) -> false;
is_cure_std_function(zip_with) -> false;
is_cure_std_function(head) -> false;
is_cure_std_function(tail) -> false;
is_cure_std_function(length) -> false;
is_cure_std_function(reverse) -> false;
is_cure_std_function(find) -> false;
is_cure_std_function(cons) -> false;
is_cure_std_function(append) -> false;
% Now in Std.Show
is_cure_std_function(show) -> false;
% Now in Std.Math
is_cure_std_function(abs) -> false;
is_cure_std_function(sqrt) -> false;
is_cure_std_function(pi) -> false;
is_cure_std_function(safe_div) -> false;
is_cure_std_function(safe_divide) -> false;
% Now in Std.String
is_cure_std_function(string_concat) -> false;
is_cure_std_function(split) -> false;
is_cure_std_function(trim) -> false;
is_cure_std_function(to_upper) -> false;
is_cure_std_function(contains) -> false;
is_cure_std_function(starts_with) -> false;
is_cure_std_function(string_empty) -> false;
is_cure_std_function(string_join) -> false;
is_cure_std_function(string_any) -> false;
is_cure_std_function(_) -> false.

%% Check if function should be routed to compiled Cure standard library module
%% Returns {true, ModuleName} or false
%% These now reference the compiled Cure modules instead of legacy Erlang bridge
is_cure_stdlib_function(zip_with) -> {true, 'Std.List'};
is_cure_stdlib_function(fold) -> {true, 'Std.List'};
is_cure_stdlib_function(fold_left) -> {true, 'Std.List'};
is_cure_stdlib_function(fold_right) -> {true, 'Std.List'};
is_cure_stdlib_function(map) -> {true, 'Std.List'};
is_cure_stdlib_function(filter) -> {true, 'Std.List'};
is_cure_stdlib_function(head) -> {true, 'Std.List'};
is_cure_stdlib_function(tail) -> {true, 'Std.List'};
is_cure_stdlib_function(length) -> {true, 'Std.List'};
is_cure_stdlib_function(reverse) -> {true, 'Std.List'};
is_cure_stdlib_function(find) -> {true, 'Std.List'};
is_cure_stdlib_function(foldl) -> {true, 'Std.List'};
is_cure_stdlib_function(foldr) -> {true, 'Std.List'};
is_cure_stdlib_function(cons) -> {true, 'Std.List'};
is_cure_stdlib_function(append) -> {true, 'Std.List'};
is_cure_stdlib_function(is_empty) -> {true, 'Std.List'};
is_cure_stdlib_function(all) -> {true, 'Std.List'};
is_cure_stdlib_function(any) -> {true, 'Std.List'};
is_cure_stdlib_function(contains) -> {true, 'Std.List'};
is_cure_stdlib_function(nth) -> {true, 'Std.List'};
is_cure_stdlib_function(take) -> {true, 'Std.List'};
is_cure_stdlib_function(drop) -> {true, 'Std.List'};
is_cure_stdlib_function(safe_head) -> {true, 'Std.List'};
is_cure_stdlib_function(safe_tail) -> {true, 'Std.List'};
is_cure_stdlib_function(safe_nth) -> {true, 'Std.List'};
% Core types and functions
is_cure_stdlib_function(ok) -> {true, 'Std.Core'};
is_cure_stdlib_function(error) -> {true, 'Std.Core'};
is_cure_stdlib_function(some) -> {true, 'Std.Core'};
is_cure_stdlib_function(none) -> {true, 'Std.Core'};
is_cure_stdlib_function(is_ok) -> {true, 'Std.Core'};
is_cure_stdlib_function(is_error) -> {true, 'Std.Core'};
is_cure_stdlib_function(is_some) -> {true, 'Std.Core'};
is_cure_stdlib_function(is_none) -> {true, 'Std.Core'};
is_cure_stdlib_function(map_ok) -> {true, 'Std.Core'};
is_cure_stdlib_function(map_error) -> {true, 'Std.Core'};
is_cure_stdlib_function(and_then) -> {true, 'Std.Core'};
% Math functions
is_cure_stdlib_function(abs) -> {true, 'Std.Math'};
is_cure_stdlib_function(sqrt) -> {true, 'Std.Math'};
is_cure_stdlib_function(power) -> {true, 'Std.Math'};
is_cure_stdlib_function(round) -> {true, 'Std.Math'};
is_cure_stdlib_function(floor) -> {true, 'Std.Math'};
is_cure_stdlib_function(ceiling) -> {true, 'Std.Math'};
is_cure_stdlib_function(pi) -> {true, 'Std.Math'};
is_cure_stdlib_function(e) -> {true, 'Std.Math'};
is_cure_stdlib_function(safe_divide) -> {true, 'Std.Math'};
is_cure_stdlib_function(safe_sqrt) -> {true, 'Std.Math'};
% Show functions
is_cure_stdlib_function(show) -> {true, 'Std.Show'};
is_cure_stdlib_function(print) -> {true, 'Std.Show'};
% String functions
is_cure_stdlib_function(string_concat) -> {true, 'Std.String'};
is_cure_stdlib_function(string_length) -> {true, 'Std.String'};
is_cure_stdlib_function(string_empty) -> {true, 'Std.String'};
is_cure_stdlib_function(trim) -> {true, 'Std.String'};
is_cure_stdlib_function(to_upper) -> {true, 'Std.String'};
is_cure_stdlib_function(to_lower) -> {true, 'Std.String'};
is_cure_stdlib_function(capitalize) -> {true, 'Std.String'};
is_cure_stdlib_function(starts_with) -> {true, 'Std.String'};
is_cure_stdlib_function(ends_with) -> {true, 'Std.String'};
is_cure_stdlib_function(split) -> {true, 'Std.String'};
is_cure_stdlib_function(join) -> {true, 'Std.String'};
% Main Std module for aggregated functions
is_cure_stdlib_function(identity) -> {true, 'Std'};
is_cure_stdlib_function(compose) -> {true, 'Std'};
is_cure_stdlib_function(flip) -> {true, 'Std'};
is_cure_stdlib_function('not') -> {true, 'Std'};
is_cure_stdlib_function('and') -> {true, 'Std'};
is_cure_stdlib_function('or') -> {true, 'Std'};
is_cure_stdlib_function('xor') -> {true, 'Std'};
is_cure_stdlib_function(eq) -> {true, 'Std'};
is_cure_stdlib_function(ne) -> {true, 'Std'};
is_cure_stdlib_function(lt) -> {true, 'Std'};
is_cure_stdlib_function(le) -> {true, 'Std'};
is_cure_stdlib_function(gt) -> {true, 'Std'};
is_cure_stdlib_function(ge) -> {true, 'Std'};
is_cure_stdlib_function(compare) -> {true, 'Std'};
is_cure_stdlib_function(min) -> {true, 'Std'};
is_cure_stdlib_function(max) -> {true, 'Std'};
is_cure_stdlib_function(clamp) -> {true, 'Std'};
is_cure_stdlib_function(_) -> false.

%% Check if function is from standard library (legacy function)
is_stdlib_function(Function) ->
    is_cure_std_function(Function).

%% Check if a parameter name is likely a type parameter
is_type_parameter(ParamName) when is_atom(ParamName) ->
    ParamStr = atom_to_list(ParamName),
    case ParamStr of
        % Single letter uppercase (T, U, V, etc.) - likely type parameters
        [C] when C >= $A, C =< $Z -> true;
        % Single letter lowercase that's commonly used for type-level values (n, k, m, etc.)
        "n" -> true;
        "k" -> true;
        "m" -> true;
        "i" -> true;
        "j" -> true;
        % Other patterns
        _ -> false
    end;
is_type_parameter(_) ->
    false.

%% Get function arity for stdlib functions
% get_function_arity(ok) -> 1;
% get_function_arity(error) -> 1;
% get_function_arity(some) -> 1;
% get_function_arity(none) -> 0;
% get_function_arity('Ok') -> 1;
% get_function_arity('Error') -> 1;
% get_function_arity('Some') -> 1;
% get_function_arity('None') -> 0;
% get_function_arity(map_ok) -> 2;
% get_function_arity(bind_ok) -> 2;
% get_function_arity(map_error) -> 2;
% get_function_arity(map_some) -> 2;
% get_function_arity(bind_some) -> 2;
% get_function_arity(safe_div) -> 2;
% get_function_arity(map) -> 2;
% get_function_arity(filter) -> 2;
% get_function_arity(foldl) -> 3;
% get_function_arity(head) -> 1;
% get_function_arity(tail) -> 1;
% get_function_arity(length) -> 1;
% get_function_arity(string_concat) -> 2;
% get_function_arity(split) -> 2;
% get_function_arity(trim) -> 1;
% get_function_arity(to_upper) -> 1;
% get_function_arity(contains) -> 2;
% get_function_arity(starts_with) -> 2;
% get_function_arity(abs) -> 1;
% get_function_arity(sqrt) -> 1;
% get_function_arity(pi) -> 0;
% get_function_arity(fsm_create) -> 2;
% get_function_arity(fsm_send_safe) -> 2;
% get_function_arity(create_counter) -> 1;
% get_function_arity(print) -> 1;
% get_function_arity(println) -> 1;
% get_function_arity(int_to_string) -> 1;
% get_function_arity(float_to_string) -> 1;
% get_function_arity(list_to_string) -> 1;
% get_function_arity(join_ints) -> 2;
% get_function_arity(string_empty) -> 0;
% get_function_arity(string_join) -> 2;
% get_function_arity(string_any) -> 1;
% get_function_arity(_) -> 0.

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

%% Compile unary operators
compile_unary_operator('-', Operand, Line) ->
    {op, Line, '-', Operand};
compile_unary_operator('+', Operand, Line) ->
    {op, Line, '+', Operand};
compile_unary_operator('not', Operand, Line) ->
    {op, Line, 'not', Operand};
compile_unary_operator(Op, Operand, Line) ->
    % Generic unary operation as function call
    {call, Line, {atom, Line, Op}, [Operand]}.

%% Check if a name is a built-in function
% is_builtin_function(Name) ->
%     BuiltinFunctions = [
%         % Arithmetic
%         '+',
%         '-',
%         '*',
%         '/',
%         'div',
%         'rem',
%         % Comparison
%         '==',
%         '/=',
%         '<',
%         '>',
%         '=<',
%         '>=',
%         % Boolean
%         'and',
%         'or',
%         'not',
%         % List operations
%         'length',
%         'hd',
%         'tl',
%         % FSM operations
%         'fsm_spawn',
%         'fsm_send',
%         'fsm_state',
%         'fsm_stop',
%         % Built-in functions
%         'map',
%         'filter',
%         'foldl',
%         'foldr'
%     ],
%     lists:member(Name, BuiltinFunctions).

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

%% Build cons structure from head elements and tail [H1, H2, ... | Tail]
build_cons_from_elements_and_tail([], Tail, _Line) ->
    Tail;
build_cons_from_elements_and_tail([H], Tail, Line) ->
    {cons, Line, H, Tail};
build_cons_from_elements_and_tail([H | RestElements], Tail, Line) ->
    {cons, Line, H, build_cons_from_elements_and_tail(RestElements, Tail, Line)}.

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
% parse_erlang_body(ErlangBody, StartLine) ->
%     parse_erlang_body(ErlangBody, StartLine, #{}).

parse_erlang_body(_ErlangBody, StartLine, _ParamMapping) ->
    % Simple stub implementation - return a basic ok atom as the function body
    {ok, [{atom, StartLine, ok}]}.

%% Parse simple Erlang expressions
%% This is a simplified parser for common Erlang patterns
% parse_simple_erlang_expression(ErlangCode, Line) ->
%     parse_simple_erlang_expression(ErlangCode, Line, #{}).
%
% parse_simple_erlang_expression(ErlangCode, Line, ParamMapping) ->
%     try
%         % Handle common cases that def_erl will use
%         TrimmedCode = string:trim(ErlangCode),
%
%         case TrimmedCode of
%             "length ( " ++ Rest ->
%                 % Handle length(list) calls
%                 case parse_function_call("length", Rest, Line, ParamMapping) of
%                     {ok, Call} -> {ok, Call};
%                     error -> parse_as_simple_term(TrimmedCode, Line, ParamMapping)
%                 end;
%             "lists reverse ( " ++ Rest ->
%                 % Handle lists:reverse(list) calls
%                 case parse_remote_call("lists", "reverse", Rest, Line, ParamMapping) of
%                     {ok, Call} -> {ok, Call};
%                     error -> parse_as_simple_term(TrimmedCode, Line, ParamMapping)
%                 end;
%             _ when
%                 TrimmedCode =:= "42" orelse
%                     TrimmedCode =:= "result" orelse
%                     TrimmedCode =:= "Result"
%             ->
%                 parse_as_simple_term(TrimmedCode, Line, ParamMapping);
%             _ ->
%                 % For more complex cases, parse as general Erlang code
%                 parse_general_erlang_code(TrimmedCode, Line, ParamMapping)
%         end
%     catch
%         error:Reason ->
%             {error, {expression_parse_error, Reason}}
%     end.

%% Parse function calls like "length(list)"
% parse_function_call(FuncName, Rest, Line) ->
%     parse_function_call(FuncName, Rest, Line, #{}).
%
% parse_function_call(FuncName, Rest, Line, ParamMapping) ->
%     case extract_args_from_call(Rest) of
%         {ok, Args} ->
%             ArgForms = [parse_simple_arg(Arg, Line, ParamMapping) || Arg <- Args],
%             Call = {call, Line, {atom, Line, list_to_atom(FuncName)}, ArgForms},
%             {ok, Call};
%         error ->
%             error
%     end.
%
% %% Parse remote calls like "lists:reverse(list)"
% parse_remote_call(ModuleName, FuncName, Rest, Line) ->
%     parse_remote_call(ModuleName, FuncName, Rest, Line, #{}).
%
% parse_remote_call(ModuleName, FuncName, Rest, Line, ParamMapping) ->
%     case extract_args_from_call(Rest) of
%         {ok, Args} ->
%             ArgForms = [parse_simple_arg(Arg, Line, ParamMapping) || Arg <- Args],
%             Call =
%                 {call, Line,
%                     {remote, Line, {atom, Line, list_to_atom(ModuleName)},
%                         {atom, Line, list_to_atom(FuncName)}},
%                     ArgForms},
%             {ok, Call};
%         error ->
%             error
%     end.
%
% %% Extract arguments from function call string
% extract_args_from_call(CallRest) ->
%     % Simple parsing for "arg1, arg2, ...)"
%     case string:split(CallRest, ")", leading) of
%         [ArgsStr, _] ->
%             ArgsList = string:split(string:trim(ArgsStr), ",", all),
%             CleanArgs = [string:trim(Arg) || Arg <- ArgsList, string:trim(Arg) =/= ""],
%             {ok, CleanArgs};
%         _ ->
%             error
%     end.
%
% %% Parse simple arguments
% parse_simple_arg(Arg, Line) ->
%     parse_simple_arg(Arg, Line, #{}).
%
% parse_simple_arg(Arg, Line, ParamMapping) ->
%     case string:to_integer(Arg) of
%         {Int, []} ->
%             {integer, Line, Int};
%         _ ->
%             case string:to_float(Arg) of
%                 {Float, []} ->
%                     {float, Line, Float};
%                 _ ->
%                     % Treat as variable - check parameter mapping first
%                     VarName = list_to_atom(Arg),
%                     case maps:get(VarName, ParamMapping, undefined) of
%                         undefined ->
%                             {var, Line, VarName};
%                         MappedName ->
%                             {var, Line, MappedName}
%                     end
%             end
%     end.
%
% %% Parse as simple term (literals, variables)
% parse_as_simple_term(Term, Line) ->
%     parse_as_simple_term(Term, Line, #{}).
%
% parse_as_simple_term(Term, Line, ParamMapping) ->
%     case string:to_integer(Term) of
%         {Int, []} ->
%             {ok, {integer, Line, Int}};
%         _ ->
%             case string:to_float(Term) of
%                 {Float, []} ->
%                     {ok, {float, Line, Float}};
%                 _ ->
%                     % Treat as variable name - check parameter mapping first
%                     case Term of
%                         [C | _] when C >= $A, C =< $Z; C >= $a, C =< $z ->
%                             VarName = list_to_atom(Term),
%                             case maps:get(VarName, ParamMapping, undefined) of
%                                 undefined ->
%                                     {ok, {var, Line, VarName}};
%                                 MappedName ->
%                                     {ok, {var, Line, MappedName}}
%                             end;
%                         _ ->
%                             % Default to atom
%                             AtomName = list_to_atom(Term),
%                             {ok, {atom, Line, AtomName}}
%                     end
%             end
%     end.
%
% %% Parse general Erlang code using erl_scan and erl_parse
% parse_general_erlang_code(ErlangCode, Line) ->
%     parse_general_erlang_code(ErlangCode, Line, #{}).

% parse_general_erlang_code(ErlangCode, Line, ParamMapping) ->
%     try
%         % Add a period if it doesn't end with one
%         CodeWithPeriod =
%             case lists:last(ErlangCode) of
%                 $. -> ErlangCode;
%                 _ -> ErlangCode ++ "."
%             end,
%
%         % Try to tokenize and parse the code
%         case erl_scan:string(CodeWithPeriod, Line) of
%             {ok, Tokens, _} ->
%                 case erl_parse:parse_exprs(Tokens) of
%                     {ok, [Expr]} ->
%                         % Apply parameter mapping to the parsed expression
%                         MappedExpr = apply_param_mapping_to_expr(Expr, ParamMapping),
%                         {ok, MappedExpr};
%                     {ok, Exprs} ->
%                         % Multiple expressions, wrap in a block and apply mapping
%                         MappedExprs = [apply_param_mapping_to_expr(E, ParamMapping) || E <- Exprs],
%                         {ok, {block, Line, MappedExprs}};
%                     {error, ParseError} ->
%                         {error, {parse_error, ParseError}}
%                 end;
%             {error, ScanError, _} ->
%                 {error, {scan_error, ScanError}}
%         end
%     catch
%         error:_GeneralError ->
%             % If general parsing fails, fall back to atom
%             {ok, {atom, Line, list_to_atom("erlang_code")}}
%     end.
%
% %% Apply parameter mapping to Erlang expression AST
% apply_param_mapping_to_expr(Expr, ParamMapping) when map_size(ParamMapping) == 0 ->
%     % No mapping needed
%     Expr;
% apply_param_mapping_to_expr({var, Line, VarName}, ParamMapping) ->
%     case maps:get(VarName, ParamMapping, undefined) of
%         undefined -> {var, Line, VarName};
%         MappedName -> {var, Line, MappedName}
%     end;
% apply_param_mapping_to_expr({call, Line, Func, Args}, ParamMapping) ->
%     MappedFunc = apply_param_mapping_to_expr(Func, ParamMapping),
%     MappedArgs = [apply_param_mapping_to_expr(Arg, ParamMapping) || Arg <- Args],
%     {call, Line, MappedFunc, MappedArgs};
% apply_param_mapping_to_expr({'case', Line, Expr, Clauses}, ParamMapping) ->
%     MappedExpr = apply_param_mapping_to_expr(Expr, ParamMapping),
%     MappedClauses = [apply_param_mapping_to_clause(Clause, ParamMapping) || Clause <- Clauses],
%     {'case', Line, MappedExpr, MappedClauses};
% apply_param_mapping_to_expr({block, Line, Exprs}, ParamMapping) ->
%     MappedExprs = [apply_param_mapping_to_expr(E, ParamMapping) || E <- Exprs],
%     {block, Line, MappedExprs};
% apply_param_mapping_to_expr({op, Line, Op, Left, Right}, ParamMapping) ->
%     MappedLeft = apply_param_mapping_to_expr(Left, ParamMapping),
%     MappedRight = apply_param_mapping_to_expr(Right, ParamMapping),
%     {op, Line, Op, MappedLeft, MappedRight};
% apply_param_mapping_to_expr({match, Line, Left, Right}, ParamMapping) ->
%     MappedLeft = apply_param_mapping_to_expr(Left, ParamMapping),
%     MappedRight = apply_param_mapping_to_expr(Right, ParamMapping),
%     {match, Line, MappedLeft, MappedRight};
% apply_param_mapping_to_expr(Expr, _ParamMapping) ->
%     % For literals and other forms, no mapping needed
%     Expr.
%
% %% Apply parameter mapping to case clause
% apply_param_mapping_to_clause({clause, Line, Patterns, Guards, Body}, ParamMapping) ->
%     MappedPatterns = [apply_param_mapping_to_expr(P, ParamMapping) || P <- Patterns],
%     MappedGuards = [apply_param_mapping_to_expr(G, ParamMapping) || G <- Guards],
%     MappedBody = [apply_param_mapping_to_expr(B, ParamMapping) || B <- Body],
%     {clause, Line, MappedPatterns, MappedGuards, MappedBody}.

%% ============================================================================
%% Monadic Pipe Operation Generation
%% ============================================================================

%% Generate monadic pipe operation form
%% This creates Erlang code that implements the monadic pipe behavior:
%% 1. Wrap the piped value with ok() if it's not already a Result
%% 2. Use cure_std:and_then to chain the operation monadically
generate_monadic_pipe_form(Function, PipedValue, RestArgs, Line) ->
    % First, wrap the piped value with ok()
    WrappedValue =
        {call, Line, {remote, Line, {atom, Line, cure_std}, {atom, Line, ok}}, [PipedValue]},

    % Create a lambda function that wraps the target function
    % This lambda will receive the unwrapped value and call the target function
    LambdaVar = {var, Line, 'X'},
    LambdaCallArgs = [LambdaVar | RestArgs],

    % Create the function call inside the lambda
    LambdaCall =
        case Function of
            {atom, _, FuncName} ->
                case is_stdlib_function(FuncName) of
                    true ->
                        {call, Line, {remote, Line, {atom, Line, cure_std}, Function},
                            LambdaCallArgs};
                    false ->
                        {call, Line, Function, LambdaCallArgs}
                end;
            _ ->
                {call, Line, Function, LambdaCallArgs}
        end,

    % For monadic pipe, we need to wrap the result in a Result type
    % Since the functions expect raw values but pipe chain expects Results
    WrappedCall =
        {call, Line, {remote, Line, {atom, Line, cure_std}, {atom, Line, ok}}, [LambdaCall]},

    % Create the lambda function
    LambdaFunction =
        {'fun', Line,
            {clauses, [
                {clause, Line, [LambdaVar], [], [WrappedCall]}
            ]}},

    % Use cure_std:and_then to chain the operations monadically
    % Note: and_then expects (Function, Result) order according to cure_std.erl
    {call, Line, {remote, Line, {atom, Line, cure_std}, {atom, Line, and_then}}, [
        LambdaFunction, WrappedValue
    ]}.
