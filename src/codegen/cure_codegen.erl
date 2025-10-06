%% Cure Programming Language - BEAM Code Generator
%% Generates BEAM bytecode from typed Cure AST
-module(cure_codegen).

-export([
    % Main compilation interface
    compile_module/1, compile_module/2,
    compile_function/1, compile_function/2,
    compile_program/1, compile_program/2,
    
    % Expression compilation
    compile_expression/1, compile_expression/2,
    
    % FSM compilation
    compile_fsm_impl/2,
    generate_fsm_functions/3,
    
    % State management
    new_state/0,
    
    % Utility functions
    generate_beam_file/2,
    write_beam_module/2,
    convert_to_erlang_forms/1,
    generate_module_attributes/1,
    
    % Configuration and options
    default_options/0,
    validate_options/1
]).

%% Include necessary headers
-include("../parser/cure_ast_simple.hrl").
-include("cure_codegen.hrl").


%% Default compilation options
default_options() ->
    [
        {debug_info, true},
        {optimize, 1},
        {warnings, true},
        {strict_types, true},
        {fsm_integration, true}
    ].

%% Validate compilation options
validate_options(Options) ->
    ValidOptions = [debug_info, optimize, warnings, strict_types, fsm_integration],
    case lists:all(fun({Key, _}) when is_atom(Key) -> 
                        lists:member(Key, ValidOptions);
                      (_) -> false 
                   end, Options) of
        true -> {ok, Options};
        false -> {error, invalid_options}
    end.

%% Create a new compilation state
new_state() ->
    #codegen_state{
        module_name = undefined,
        exports = [],
        functions = [],
        local_vars = #{},
        temp_counter = 0,
        label_counter = 0,
        constants = #{},
        type_info = cure_typechecker:builtin_env(),
        optimization_level = 0
    }.

%% ============================================================================
%% Main Compilation Interface
%% ============================================================================

%% Compile a complete program (list of modules/functions)
compile_program(AST) ->
    compile_program(AST, default_options()).

compile_program(AST, Options) ->
    case validate_options(Options) of
        {ok, ValidOptions} ->
            compile_program_impl(AST, ValidOptions);
        {error, Reason} ->
            {error, Reason}
    end.

compile_program_impl(AST, Options) when is_list(AST) ->
    Results = [compile_item(Item, Options) || Item <- AST],
    case lists:partition(fun({Tag, _}) -> Tag =:= ok end, Results) of
        {SuccessResults, []} ->
            Modules = [Module || {ok, Module} <- SuccessResults],
            {ok, Modules};
        {_, ErrorResults} ->
            Errors = [Error || {error, Error} <- ErrorResults],
            {error, {compilation_failed, Errors}}
    end.

%% Compile a single module
compile_module(ModuleAST) ->
    compile_module(ModuleAST, default_options()).

%% Support for new AST format
compile_module({module_def, Name, Imports, Exports, Items, _Location}, Options) ->
    % Using new AST format compilation path
    ConvertedExports = convert_exports_new(Exports, Items),
    State = #codegen_state{
        module_name = Name,
        exports = ConvertedExports,
        optimization_level = proplists:get_value(optimize, Options, 0),
        type_info = cure_typechecker:builtin_env()
    },
    
    % Process imports first
    StateWithImports = case process_imports_new(Imports, State) of
        {ok, ImportState} -> ImportState;
        {error, _} -> State  % Continue with basic state on import errors
    end,
    
    case compile_module_items(Items, StateWithImports) of
        {ok, CompiledState} ->
            generate_beam_module(CompiledState);
        {error, Reason} ->
            {error, Reason}
    end;

compile_module(#module_def{name = Name, exports = Exports, items = Items} = _Module, Options) ->
    % Using old AST format compilation path
    State = #codegen_state{
        module_name = Name,
        exports = convert_exports(Exports),
        optimization_level = proplists:get_value(optimize, Options, 0),
        type_info = cure_typechecker:builtin_env()
    },
    
    case compile_module_items(Items, State) of
        {ok, CompiledState} ->
            generate_beam_module(CompiledState);
        {error, Reason} ->
            {error, Reason}
    end;

compile_module(AST, _Options) ->
    {error, {not_a_module, AST}}.

%% Compile a single function
compile_function(FunctionAST) ->
    compile_function(FunctionAST, default_options()).

compile_function(#function_def{} = Function, Options) ->
    State = #codegen_state{
        module_name = test_module,
        optimization_level = proplists:get_value(optimize, Options, 0),
        type_info = cure_typechecker:builtin_env()
    },
    compile_function_impl(Function, State);

compile_function(AST, _Options) ->
    {error, {not_a_function, AST}}.

%% ============================================================================
%% Module Compilation
%% ============================================================================

compile_module_items(Items, State) ->
    compile_module_items(Items, State, []).

compile_module_items([], State, Acc) ->
    {ok, State#codegen_state{functions = lists:reverse(Acc)}};

compile_module_items([Item | RestItems], State, Acc) ->
    case compile_module_item(Item, State) of
        {ok, CompiledItem, NewState} ->
            compile_module_items(RestItems, NewState, [CompiledItem | Acc]);
        {error, Reason} ->
            {error, Reason}
    end.

compile_module_item(#function_def{} = Function, State) ->
    case compile_function_impl(Function, State) of
        {ok, CompiledFunction, NewState} ->
            {ok, CompiledFunction, NewState};
        {error, Reason} ->
            {error, Reason}
    end;

%% Handle new function definition format
compile_module_item({function_def, Name, Params, Body, Location}, State) ->
    % Convert to old format for compatibility
    Function = #function_def{
        name = Name,
        params = Params,
        body = Body,
        location = Location
    },
    case compile_function_impl(Function, State) of
        {ok, CompiledFunction, NewState} ->
            {ok, CompiledFunction, NewState};
        {error, Reason} ->
            {error, Reason}
    end;

%% Handle Erlang function definition (def_erl)
compile_module_item({erlang_function_def, Name, Params, _ReturnType, _Constraint, ErlangBody, Location}, State) ->
    case compile_erlang_function_impl(Name, Params, ErlangBody, Location, State) of
        {ok, CompiledFunction, NewState} ->
            {ok, CompiledFunction, NewState};
        {error, Reason} ->
            {error, Reason}
    end;

compile_module_item(#fsm_def{} = FSM, State) ->
    case compile_fsm_impl(FSM, State) of
        {ok, CompiledFSM, NewState} ->
            {ok, CompiledFSM, NewState};
        {error, Reason} ->
            {error, Reason}
    end;

compile_module_item(#type_def{} = TypeDef, State) ->
    % Type definitions don't generate runtime code, but may affect compilation
    {ok, {type_def, TypeDef}, State};

compile_module_item(#import_def{} = Import, State) ->
    % Process import for code generation context
    case process_import(Import, State) of
        {ok, NewState} ->
            % Import processing would be handled here in a full implementation
            FinalState = NewState,
            {ok, {import, Import}, FinalState};
        {error, Reason} ->
            {error, Reason}
    end;


%% Handle export list (metadata only - no code generation needed)
compile_module_item({export_list, _Exports, _Location}, State) ->
    % Export lists are handled during module setup, no code generation needed
    {ok, {export_list, metadata_only}, State};

%% Skip other metadata items that don't need code generation
compile_module_item(Item, State) when is_tuple(Item) ->
    case element(1, Item) of
        export_list ->
            {ok, {metadata, Item}, State};
        _ ->
            {error, {unsupported_module_item, Item}}
    end.

%% Process import for code generation
process_import(#import_def{module = Module, items = Items}, State) ->
    case process_import_items(Module, Items, State) of
        {ok, NewState} ->
            {ok, NewState};
        {error, Reason} ->
            {error, {import_processing_failed, Module, Reason}}
    end.

%% Process import items (functions and identifiers)
process_import_items(_Module, all, State) ->
    % Import all exports - no specific processing needed for code gen
    {ok, State};
process_import_items(Module, Items, State) when is_list(Items) ->
    % Process specific imported items
    process_imported_items(Module, Items, State).

%% Process individual import items
process_imported_items(_Module, [], State) ->
    {ok, State};
process_imported_items(Module, [Item | RestItems], State) ->
    case process_imported_item(Module, Item, State) of
        {ok, NewState} ->
            process_imported_items(Module, RestItems, NewState);
        {error, Reason} ->
            {error, Reason}
    end.

%% Process single imported item
process_imported_item(_Module, #function_import{name = _Name, arity = _Arity}, State) ->
    % Register function import for call resolution
    % In a full implementation, would verify the function exists in the module
    % and potentially generate import stubs or call wrappers
    % ImportInfo = {imported_function, Module, Name, Arity},
    % Could store this information in the state for later use during call compilation
    {ok, State};
process_imported_item(_Module, Identifier, State) when is_atom(Identifier) ->
    % Register identifier import (type constructor, constant, etc.)
    % In a full implementation, would handle identifier imports appropriately
    {ok, State}.

%% ============================================================================
%% Function Compilation
%% ============================================================================

compile_function_impl(#function_def{name = Name, params = Params, body = Body, 
                                   constraint = Constraint, location = Location} = _Function, State) ->
    % Create function compilation context
    FunctionState = State#codegen_state{
        local_vars = create_param_bindings(Params),
        temp_counter = 0,
        label_counter = 0
    },
    
    try
        % Compile parameter constraint guards if present
        {GuardInstructions, State1} = case Constraint of
            undefined -> {[], FunctionState};
            _ -> 
                case cure_guard_compiler:compile_guard(Constraint, FunctionState) of
                    {ok, Instructions, NewState} ->
                        {Instructions ++ [generate_guard_check_instruction(Location)], NewState};
                    {error, Reason} ->
                        throw({guard_compilation_failed, Reason})
                end
        end,
        
        % Compile function body
        {BodyInstructions, FinalState} = compile_expression(Body, State1),
        
        % Generate function prologue and epilogue
        FunctionCode = generate_function_code(Name, Params, GuardInstructions ++ BodyInstructions, Location),
        
        {ok, {function, FunctionCode}, FinalState}
    catch
        error:CompileReason:Stack ->
            {error, {function_compilation_failed, Name, CompileReason, Stack}}
    end;

% Legacy function definition support (without constraint field)
compile_function_impl(#function_def{name = Name, params = Params, body = Body, 
                                   location = Location}, State) ->
    % Convert to new format with undefined constraint
    NewFunction = #function_def{
        name = Name,
        params = Params,
        body = Body,
        constraint = undefined,
        location = Location
    },
    compile_function_impl(NewFunction, State).

%% Compile Erlang function (def_erl)
%% For def_erl functions, we generate a simple function that directly contains the raw Erlang code
compile_erlang_function_impl(Name, Params, ErlangBody, Location, State) ->
    try
        % For def_erl functions, we create a function with raw Erlang code in the body
        % This will be handled specially in the BEAM generation phase
        ParamList = [P#param.name || P <- Params],
        
        FunctionCode = #{
            name => Name,
            arity => length(Params),
            params => ParamList,
            erlang_body => ErlangBody,  % Store raw Erlang code
            is_erlang_function => true,  % Flag to identify this as def_erl
            location => Location
        },
        
        {ok, {function, FunctionCode}, State}
    catch
        error:CompileReason:Stack ->
            {error, {erlang_function_compilation_failed, Name, CompileReason, Stack}}
    end.

%% Create parameter bindings for local variable map
create_param_bindings(Params) ->
    lists:foldl(fun(#param{name = Name}, Acc) ->
        maps:put(Name, {param, Name}, Acc)
    end, #{}, Params).

%% Generate BEAM function code
generate_function_code(Name, Params, BodyInstructions, Location) ->
    ParamList = [P#param.name || P <- Params],
    
    #{
        name => Name,
        arity => length(Params),
        params => ParamList,
        instructions => [
            #beam_instr{op = label, args = [function_start], location = Location}
        ] ++ BodyInstructions ++ [
            #beam_instr{op = return, args = [], location = Location}
        ],
        location => Location
    }.

%% ============================================================================
%% Expression Compilation
%% ============================================================================

compile_expression(Expr) ->
    compile_expression(Expr, #codegen_state{}).

compile_expression(Expr, State) ->
    case Expr of
        #literal_expr{} -> compile_literal(Expr, State);
        #identifier_expr{} -> compile_identifier(Expr, State);
        #binary_op_expr{} -> compile_binary_op(Expr, State);
        #function_call_expr{} -> compile_function_call(Expr, State);
        #if_expr{} -> compile_if_expr(Expr, State);
        #let_expr{} -> compile_let_expr(Expr, State);
        #list_expr{} -> compile_list_expr(Expr, State);
        #tuple_expr{} -> compile_tuple_expr(Expr, State);
        #block_expr{} -> compile_block_expr(Expr, State);
        #lambda_expr{} -> compile_lambda_expr(Expr, State);
        #unary_op_expr{} -> compile_unary_op_expr(Expr, State);
        #match_expr{} -> compile_match_expr(Expr, State);
        % Note: pipe operators are parsed as binary_op_expr with op = '|>'
        % Note: constructor expressions are parsed as function_call_expr
        _ -> {error, {unsupported_expression, Expr}}
    end.

%% Compile literal expressions
compile_literal(#literal_expr{value = Value, location = Location}, State) ->
    Instruction = #beam_instr{
        op = load_literal,
        args = [Value],
        location = Location
    },
    {[Instruction], State}.

%% Compile identifier expressions (variables)
compile_identifier(#identifier_expr{name = Name, location = Location}, State) ->
    case maps:get(Name, State#codegen_state.local_vars, undefined) of
        undefined ->
            % Might be a global function or imported function
            Instruction = #beam_instr{
                op = load_global,
                args = [Name],
                location = Location
            },
            {[Instruction], State};
        {param, ParamName} ->
            Instruction = #beam_instr{
                op = load_param,
                args = [ParamName],
                location = Location
            },
            {[Instruction], State};
        {local, VarName} ->
            Instruction = #beam_instr{
                op = load_local,
                args = [VarName],
                location = Location
            },
            {[Instruction], State}
    end.

%% Compile binary operations
compile_binary_op(#binary_op_expr{op = Op, left = Left, right = Right, 
                                 location = Location}, State) ->
    case Op of
        '|>' ->
            % Pipe operator: Left |> Right becomes Right(Left)
            {LeftInstructions, State1} = compile_expression(Left, State),
            
            % Right should be a function call where Left becomes the first argument
            case Right of
                #function_call_expr{function = Function, args = Args} ->
                    % Compile function and original args
                    {FuncInstructions, State2} = compile_expression(Function, State1),
                    {ArgInstructions, State3} = compile_expressions(Args, State2),
                    
                    % Create call with Left as first argument
                    CallInstruction = #beam_instr{
                        op = call,
                        args = [length(Args) + 1], % +1 for the piped value
                        location = Location
                    },
                    
                    % Instructions: Function, Left, Args..., Call (correct stack order)
                    Instructions = FuncInstructions ++ LeftInstructions ++ ArgInstructions ++ [CallInstruction],
                    {Instructions, State3};
                _ ->
                    % Right is just a function, call it with Left as argument
                    {RightInstructions, State2} = compile_expression(Right, State1),
                    
                    CallInstruction = #beam_instr{
                        op = call,
                        args = [1], % One argument (the piped value)
                        location = Location
                    },
                    
                    % Instructions: Function, Left, Call (correct stack order)
                    Instructions = RightInstructions ++ LeftInstructions ++ [CallInstruction],
                    {Instructions, State2}
            end;
        _ ->
            % Regular binary operation
            {LeftInstructions, State1} = compile_expression(Left, State),
            {RightInstructions, State2} = compile_expression(Right, State1),
            
            BinaryOpInstruction = #beam_instr{
                op = binary_op,
                args = [Op],
                location = Location
            },
            
            Instructions = LeftInstructions ++ RightInstructions ++ [BinaryOpInstruction],
            {Instructions, State2}
    end.

%% Compile function calls
compile_function_call(#function_call_expr{function = Function, args = Args, 
                                         location = Location}, State) ->
    % Compile function expression first (function goes on bottom of stack)
    {FuncInstructions, State1} = compile_expression(Function, State),
    
    % Compile arguments (arguments go on top of stack)
    {ArgInstructions, State2} = compile_expressions(Args, State1),
    
    % Generate call instruction
    CallInstruction = #beam_instr{
        op = call,
        args = [length(Args)],
        location = Location
    },
    
    % Instructions: Function first, then Args, then Call
    Instructions = FuncInstructions ++ ArgInstructions ++ [CallInstruction],
    {Instructions, State2}.

%% Compile if expressions
compile_if_expr(#if_expr{condition = Condition, then_branch = ThenBranch,
                        else_branch = ElseBranch, location = Location}, State) ->
    {CondInstructions, State1} = compile_expression(Condition, State),
    {ThenInstructions, State2} = compile_expression(ThenBranch, State1),
    {ElseInstructions, State3} = compile_expression(ElseBranch, State2),
    
    % Generate labels
    {ElseLabel, State4} = new_label(State3),
    {EndLabel, State5} = new_label(State4),
    
    Instructions = CondInstructions ++ [
        #beam_instr{op = jump_if_false, args = [ElseLabel], location = Location}
    ] ++ ThenInstructions ++ [
        #beam_instr{op = jump, args = [EndLabel], location = Location},
        #beam_instr{op = label, args = [ElseLabel], location = Location}
    ] ++ ElseInstructions ++ [
        #beam_instr{op = label, args = [EndLabel], location = Location}
    ],
    
    {Instructions, State5}.

%% Compile let expressions
compile_let_expr(#let_expr{bindings = Bindings, body = Body, location = _Location}, State) ->
    {BindingInstructions, State1} = compile_bindings(Bindings, State),
    {BodyInstructions, State2} = compile_expression(Body, State1),
    
    Instructions = BindingInstructions ++ BodyInstructions,
    {Instructions, State2}.

%% Compile list expressions  
compile_list_expr(#list_expr{elements = Elements, location = Location}, State) ->
    {ElementInstructions, State1} = compile_expressions(Elements, State),
    
    ListInstruction = #beam_instr{
        op = make_list,
        args = [length(Elements)],
        location = Location
    },
    
    Instructions = ElementInstructions ++ [ListInstruction],
    {Instructions, State1}.

%% Compile tuple expressions
compile_tuple_expr(#tuple_expr{elements = Elements, location = Location}, State) ->
    {ElementInstructions, State1} = compile_expressions(Elements, State),
    
    TupleInstruction = #beam_instr{
        op = make_tuple,
        args = [length(Elements)],
        location = Location
    },
    
    Instructions = ElementInstructions ++ [TupleInstruction],
    {Instructions, State1}.

%% Compile block expressions
compile_block_expr(#block_expr{expressions = Expressions, location = _Location}, State) ->
    compile_expressions_sequence(Expressions, State).

%% Compile lambda expressions
compile_lambda_expr(#lambda_expr{params = Params, body = Body, location = Location}, State) ->
    % Generate lambda as anonymous function
    {LambdaName, State1} = new_temp_var(State),
    
    % Create parameter bindings for lambda
    ParamBindings = create_param_bindings(Params),
    LambdaState = State1#codegen_state{
        local_vars = maps:merge(State1#codegen_state.local_vars, ParamBindings)
    },
    
    % Compile lambda body
    {BodyInstructions, State2} = compile_expression(Body, LambdaState),
    
    % Generate lambda creation instruction with proper format
    % Lambda should create a proper function reference that can be called
    ParamNames = [P#param.name || P <- Params],
    LambdaInstruction = #beam_instr{
        op = make_lambda,
        args = [LambdaName, ParamNames, BodyInstructions, length(Params)],
        location = Location
    },
    
    {[LambdaInstruction], State2}.

%% Compile unary operations
compile_unary_op_expr(#unary_op_expr{op = Op, operand = Operand, location = Location}, State) ->
    {OperandInstructions, State1} = compile_expression(Operand, State),
    
    UnaryOpInstruction = #beam_instr{
        op = unary_op,
        args = [Op],
        location = Location
    },
    
    Instructions = OperandInstructions ++ [UnaryOpInstruction],
    {Instructions, State1}.

%% Compile pattern matching expressions
compile_match_expr(#match_expr{expr = Expr, patterns = Patterns, location = Location}, State) ->
    {ExprInstructions, State1} = compile_expression(Expr, State),
    
    % Compile patterns with guards
    {PatternInstructions, State2} = compile_match_patterns(Patterns, Location, State1),
    
    Instructions = ExprInstructions ++ PatternInstructions,
    {Instructions, State2}.


%% ============================================================================
%% FSM Compilation
%% ============================================================================

compile_fsm_impl(#fsm_def{name = Name, states = States, initial = Initial,
                         state_defs = StateDefs, location = Location}, State) ->
    try
        % Compile FSM definition to runtime format
        CompiledFSM = cure_fsm_runtime:compile_fsm_definition(#fsm_def{
            name = Name,
            states = States,
            initial = Initial,
            state_defs = StateDefs,
            location = Location
        }),
        
        % Generate BEAM functions for FSM module
        FSMFunctions = generate_fsm_functions(Name, CompiledFSM, Location),
        
        % Add FSM functions to module exports
        NewExports = add_fsm_exports(Name, State#codegen_state.exports),
        NewState = State#codegen_state{exports = NewExports},
        
        % Create FSM compilation result
        RegistrationCode = #{
            type => fsm_definition,
            name => Name,
            definition => CompiledFSM,
            functions => FSMFunctions,
            location => Location
        },
        
        {ok, {fsm, RegistrationCode}, NewState}
    catch
        error:Reason:Stack ->
            {error, {fsm_compilation_failed, Name, Reason, Stack}}
    end.

%% Generate BEAM functions for FSM access
generate_fsm_functions(FSMName, CompiledFSM, Location) ->
    [
        generate_fsm_spawn_function(FSMName, Location),
        generate_fsm_send_function(FSMName, Location),
        generate_fsm_state_function(FSMName, Location),
        generate_fsm_stop_function(FSMName, Location),
        generate_fsm_definition_function(FSMName, CompiledFSM, Location)
    ].

%% Generate FSM spawn function: FSMName_spawn/0, FSMName_spawn/1
generate_fsm_spawn_function(FSMName, Location) ->
    FunctionName = list_to_atom(atom_to_list(FSMName) ++ "_spawn"),
    
    % Generate spawn/0 function
    Spawn0 = #{
        name => FunctionName,
        arity => 0,
        instructions => [
            #beam_instr{op = load_literal, args = [FSMName], location = Location},
            #beam_instr{op = call_bif, args = [cure_fsm_runtime, spawn_fsm, 1], location = Location},
            #beam_instr{op = return, args = [], location = Location}
        ],
        location => Location
    },
    
    % Generate spawn/1 function with initial data
    Spawn1FunctionName = FunctionName,
    Spawn1 = #{
        name => Spawn1FunctionName,
        arity => 1,
        instructions => [
            #beam_instr{op = load_literal, args = [FSMName], location = Location},
            #beam_instr{op = load_param, args = [init_data], location = Location},
            #beam_instr{op = call_bif, args = [cure_fsm_runtime, spawn_fsm, 2], location = Location},
            #beam_instr{op = return, args = [], location = Location}
        ],
        location => Location
    },
    
    [Spawn0, Spawn1].

%% Generate FSM send function: FSMName_send/2
generate_fsm_send_function(FSMName, Location) ->
    FunctionName = list_to_atom(atom_to_list(FSMName) ++ "_send"),
    
    #{
        name => FunctionName,
        arity => 2,
        instructions => [
            #beam_instr{op = load_param, args = [fsm_pid], location = Location},
            #beam_instr{op = load_param, args = [event], location = Location},
            #beam_instr{op = call_bif, args = [cure_fsm_runtime, send_event, 2], location = Location},
            #beam_instr{op = return, args = [], location = Location}
        ],
        location => Location
    }.

%% Generate FSM state function: FSMName_state/1
generate_fsm_state_function(FSMName, Location) ->
    FunctionName = list_to_atom(atom_to_list(FSMName) ++ "_state"),
    
    #{
        name => FunctionName,
        arity => 1,
        instructions => [
            #beam_instr{op = load_param, args = [fsm_pid], location = Location},
            #beam_instr{op = call_bif, args = [cure_fsm_runtime, get_state, 1], location = Location},
            #beam_instr{op = return, args = [], location = Location}
        ],
        location => Location
    }.

%% Generate FSM stop function: FSMName_stop/1
generate_fsm_stop_function(FSMName, Location) ->
    FunctionName = list_to_atom(atom_to_list(FSMName) ++ "_stop"),
    
    #{
        name => FunctionName,
        arity => 1,
        instructions => [
            #beam_instr{op = load_param, args = [fsm_pid], location = Location},
            #beam_instr{op = call_bif, args = [cure_fsm_runtime, stop_fsm, 1], location = Location},
            #beam_instr{op = return, args = [], location = Location}
        ],
        location => Location
    }.

%% Generate FSM definition function for runtime registration
generate_fsm_definition_function(FSMName, CompiledFSM, Location) ->
    FunctionName = list_to_atom(atom_to_list(FSMName) ++ "_definition"),
    
    #{
        name => FunctionName,
        arity => 0,
        instructions => [
            #beam_instr{op = load_literal, args = [CompiledFSM], location = Location},
            #beam_instr{op = return, args = [], location = Location}
        ],
        location => Location
    }.

%% Add FSM exports to module export list
add_fsm_exports(FSMName, CurrentExports) ->
    FSMExports = [
        {list_to_atom(atom_to_list(FSMName) ++ "_spawn"), 0},
        {list_to_atom(atom_to_list(FSMName) ++ "_spawn"), 1},
        {list_to_atom(atom_to_list(FSMName) ++ "_send"), 2},
        {list_to_atom(atom_to_list(FSMName) ++ "_state"), 1},
        {list_to_atom(atom_to_list(FSMName) ++ "_stop"), 1},
        {list_to_atom(atom_to_list(FSMName) ++ "_definition"), 0}
    ],
    CurrentExports ++ FSMExports.

%% ============================================================================
%% Utility Functions
%% ============================================================================

%% Compile multiple expressions
compile_expressions(Expressions, State) ->
    compile_expressions(Expressions, State, []).

compile_expressions([], State, Acc) ->
    {lists:reverse(lists:flatten(Acc)), State};
compile_expressions([Expr | RestExprs], State, Acc) ->
    {Instructions, NewState} = compile_expression(Expr, State),
    compile_expressions(RestExprs, NewState, [Instructions | Acc]).

%% Compile expressions in sequence (for blocks)
compile_expressions_sequence([], State) ->
    {[], State};
compile_expressions_sequence([LastExpr], State) ->
    compile_expression(LastExpr, State);
compile_expressions_sequence([Expr | RestExprs], State) ->
    {Instructions1, State1} = compile_expression(Expr, State),
    {Instructions2, State2} = compile_expressions_sequence(RestExprs, State1),
    
    % Check if the expression has side effects (like print calls)
    % If so, we need to generate code that executes it but still discards the result
    case has_side_effects(Expr) of
        true ->
            % For side-effecting expressions, generate code to execute and discard result
            % but don't use pop instruction which prevents execution
            ExecuteInstr = #beam_instr{op = execute_and_discard, args = []},
            {Instructions1 ++ [ExecuteInstr] ++ Instructions2, State2};
        false ->
            % For pure expressions, use pop to discard intermediate results
            PopInstruction = #beam_instr{op = pop, args = []},
            {Instructions1 ++ [PopInstruction] ++ Instructions2, State2}
    end.

%% Compile let bindings
compile_bindings(Bindings, State) ->
    compile_bindings(Bindings, State, []).

compile_bindings([], State, Acc) ->
    {lists:flatten(lists:reverse(Acc)), State};
compile_bindings([#binding{pattern = Pattern, value = Value, location = Location} | RestBindings], State, Acc) ->
    {ValueInstructions, State1} = compile_expression(Value, State),
    {PatternInstructions, State2} = compile_pattern_binding(Pattern, Location, State1),
    
    % Ensure correct order: first load value, then store it
    Instructions = ValueInstructions ++ PatternInstructions,
    compile_bindings(RestBindings, State2, [Instructions | Acc]).

%% Compile pattern bindings (simplified - only identifier patterns for now)
compile_pattern_binding(#identifier_pattern{name = Name, location = Location}, _BindingLocation, State) ->
    % Store the value from the top of stack in a local variable
    % At this point, the value should already be on the stack from compile_expression
    {TempVar, State1} = new_temp_var(State),
    StoreInstruction = #beam_instr{
        op = store_local,
        args = [TempVar],
        location = Location
    },
    
    % Update local variable map to track this variable
    NewLocalVars = maps:put(Name, {local, TempVar}, State1#codegen_state.local_vars),
    State2 = State1#codegen_state{local_vars = NewLocalVars},
    
    {[StoreInstruction], State2};

compile_pattern_binding(Pattern, Location, _State) ->
    {error, {unsupported_pattern, Pattern, Location}}.

%% Generate new temporary variable
new_temp_var(State) ->
    Counter = State#codegen_state.temp_counter,
    TempVar = list_to_atom("_temp_" ++ integer_to_list(Counter)),
    NewState = State#codegen_state{temp_counter = Counter + 1},
    {TempVar, NewState}.

%% Generate new label
new_label(State) ->
    Counter = State#codegen_state.label_counter,
    Label = list_to_atom("label_" ++ integer_to_list(Counter)),
    NewState = State#codegen_state{label_counter = Counter + 1},
    {Label, NewState}.

%% Check if expression has side effects and should not be discarded
has_side_effects(#function_call_expr{function = Function}) ->
    case Function of
        #identifier_expr{name = FuncName} ->
            % Check if this is a side-effecting function like print
            is_side_effecting_function(FuncName);
        _ ->
            true  % Conservative: assume complex function calls have side effects
    end;
has_side_effects(#let_expr{}) -> true;  % Let expressions can have side effects in bindings
has_side_effects(#if_expr{}) -> true;   % If expressions can have side effects in branches
has_side_effects(#match_expr{}) -> true; % Match expressions can have side effects
has_side_effects(#block_expr{}) -> true; % Block expressions can have side effects
has_side_effects(_) -> false.  % Literals, identifiers, etc. are pure

%% Check if a function name represents a side-effecting function
is_side_effecting_function(print) -> true;
is_side_effecting_function(println) -> true;
is_side_effecting_function(fsm_send_safe) -> true;
is_side_effecting_function(create_counter) -> true;
is_side_effecting_function(_) -> false.

%% Generate guard check instruction
generate_guard_check_instruction(Location) ->
    #beam_instr{
        op = guard_check,
        args = [function_clause_error],
        location = Location
    }.

%% ============================================================================
%% BEAM Module Generation
%% ============================================================================

generate_beam_module(State) ->
    % Extract regular functions and FSM definitions
    RegularFunctions = [F || {function, F} <- State#codegen_state.functions],
    FSMDefinitions = [FSM || {fsm, FSM} <- State#codegen_state.functions],
    
    % Extract FSM functions and flatten them
    FSMFunctions = lists:flatten([maps:get(functions, FSM, []) || FSM <- FSMDefinitions]),
    
    % Combine all functions
    AllFunctions = RegularFunctions ++ FSMFunctions,
    
    Module = #{
        name => State#codegen_state.module_name,
        exports => State#codegen_state.exports,
        functions => AllFunctions,
        fsm_definitions => FSMDefinitions,
        attributes => generate_module_attributes(State),
        optimization_level => State#codegen_state.optimization_level
    },
    {ok, Module}.

generate_module_attributes(State) ->
    BaseAttributes = [
        {vsn, [erlang:unique_integer()]},
        {compile_info, [{optimization_level, State#codegen_state.optimization_level}]}
    ],
    
    % Add FSM registration attributes
    FSMDefinitions = [FSM || {fsm, FSM} <- State#codegen_state.functions],
    FSMAttributes = case FSMDefinitions of
        [] -> [];
        _ -> 
            FSMNames = [maps:get(name, FSM) || FSM <- FSMDefinitions],
            [{fsm_types, FSMNames}]
    end,
    
    % Add debug info if requested (default to true for now)
    DebugAttributes = [{debug_info, true}],
    
    BaseAttributes ++ FSMAttributes ++ DebugAttributes.

%% Convert export specifications
convert_exports(Exports) ->
    [{Name, Arity} || #export_spec{name = Name, arity = Arity} <- Exports].

%% Convert exports for new AST format
convert_exports_new(ExportList, Items) ->
    case ExportList of
        all ->
            extract_all_functions(Items);
        {export_list, Exports, _Location} ->
            convert_export_specs(Exports);
        _ ->
            []
    end.

%% Extract all function names and arities from items
extract_all_functions(Items) ->
    extract_all_functions(Items, []).

extract_all_functions([], Acc) ->
    lists:reverse(Acc);
extract_all_functions([{function_def, Name, Params, _Body, _Location} | Rest], Acc) ->
    Arity = length(Params),
    extract_all_functions(Rest, [{Name, Arity} | Acc]);
extract_all_functions([{erlang_function_def, Name, Params, _ReturnType, _Constraint, _ErlangBody, _Location} | Rest], Acc) ->
    Arity = length(Params),
    extract_all_functions(Rest, [{Name, Arity} | Acc]);
extract_all_functions([_ | Rest], Acc) ->
    extract_all_functions(Rest, Acc).

%% Convert export specifications for new format
convert_export_specs([]) ->
    [];
convert_export_specs([{export_spec, Name, Arity, _Location} | Rest]) ->
    [{Name, Arity} | convert_export_specs(Rest)];
convert_export_specs([_ | Rest]) ->
    convert_export_specs(Rest).

%% Process imports for new AST format
process_imports_new([], State) ->
    {ok, State};
process_imports_new([{import_def, _Module, _Imports, _Location} | Rest], State) ->
    % For now, just continue processing - full import resolution would need module loading
    process_imports_new(Rest, State);
process_imports_new([_ | Rest], State) ->
    process_imports_new(Rest, State).

%% Compile individual items (for program compilation)
compile_item(#module_def{} = Module, Options) ->
    compile_module(Module, Options);
compile_item(#function_def{} = Function, Options) ->
    compile_function(Function, Options);
compile_item(Item, _Options) ->
    {error, {unsupported_item, Item}}.

%% ============================================================================
%% BEAM File Generation
%% ============================================================================

generate_beam_file(Module, OutputPath) ->
    case convert_to_erlang_forms(Module) of
        {ok, Forms} ->
            case compile:forms(Forms, [binary, return_errors]) of
                {ok, ModuleName, Binary} ->
                    case file:write_file(OutputPath, Binary) of
                        ok -> {ok, {ModuleName, OutputPath}};
                        {error, Reason} -> {error, {write_failed, Reason}}
                    end;
                {error, Errors, Warnings} ->
                    {error, {compile_failed, Errors, Warnings}}
            end;
        {error, Reason} ->
            {error, Reason}
    end.

%% Convert internal representation to Erlang abstract forms
convert_to_erlang_forms(Module) ->
    try
        ModuleName = maps:get(name, Module),
        RawExports = maps:get(exports, Module, []),
        Functions = maps:get(functions, Module, []),
        % Auto-generate exports from functions if no exports specified
        Exports = case RawExports of
            [] -> 
                % Extract {name, arity} from all functions
                [{maps:get(name, F), maps:get(arity, F)} || F <- Functions, 
                 maps:is_key(name, F) andalso maps:is_key(arity, F)];
            _ -> 
                RawExports
        end,
        FSMDefinitions = maps:get(fsm_definitions, Module, []),
        Attributes = maps:get(attributes, Module, []),
        
        % Add module and export attributes
        BaseAttributes = [
            {attribute, 1, module, ModuleName},
            {attribute, 2, export, Exports}
        ],
        
        % Add custom attributes (including FSM types)
        AttributeForms = convert_attributes_to_forms(Attributes, 3),
        
        % Add on_load hook for FSM registration if FSMs present
        LoadHook = case FSMDefinitions of
            [] -> [];
            _ -> [{attribute, 3 + length(AttributeForms), on_load, {register_fsms, 0}}]
        end,
        
        % Convert functions to forms
        FunctionForms = convert_functions_to_forms(Functions, 4 + length(AttributeForms) + length(LoadHook)),
        
        % Add FSM registration function if needed
        FSMRegisterFunc = case FSMDefinitions of
            [] -> [];
            _ -> [generate_fsm_registration_function(FSMDefinitions, 4 + length(AttributeForms) + length(LoadHook) + length(FunctionForms))]
        end,
        
        Forms = BaseAttributes ++ AttributeForms ++ LoadHook ++ FunctionForms ++ FSMRegisterFunc,
        
        
        {ok, Forms}
    catch
        error:Reason:Stack ->
            {error, {form_conversion_failed, Reason, Stack}}
    end.

%% Convert compiled functions to Erlang forms
convert_functions_to_forms(Functions, LineStart) ->
    convert_functions_to_forms(Functions, LineStart, []).

convert_functions_to_forms([], _Line, Acc) ->
    lists:reverse(Acc);
convert_functions_to_forms([Function | RestFunctions], Line, Acc) ->
    case convert_function_to_form(Function, Line) of
        {ok, Form, NextLine} ->
            convert_functions_to_forms(RestFunctions, NextLine, [Form | Acc]);
        {error, Reason} ->
            % Skip invalid functions for now
            convert_functions_to_forms(RestFunctions, Line + 1, Acc)
    end.

%% Convert a single function to Erlang abstract form
convert_function_to_form(Function, Line) ->
    case cure_beam_compiler:compile_function_to_erlang(Function, Line) of
        {ok, FunctionForm, NextLine} ->
            {ok, FunctionForm, NextLine};
        {error, Reason} ->
            {error, Reason}
    end.


%% Convert attributes to Erlang abstract forms
convert_attributes_to_forms(Attributes, StartLine) ->
    convert_attributes_to_forms(Attributes, StartLine, []).

convert_attributes_to_forms([], _Line, Acc) ->
    lists:reverse(Acc);
convert_attributes_to_forms([{Name, Value} | Rest], Line, Acc) ->
    Form = {attribute, Line, Name, Value},
    convert_attributes_to_forms(Rest, Line + 1, [Form | Acc]).

%% Generate FSM registration function to be called on module load
generate_fsm_registration_function(FSMDefinitions, Line) ->
    FSMNames = [maps:get(name, FSM) || FSM <- FSMDefinitions],
    
    % Generate registration calls for each FSM
    RegistrationCalls = lists:map(fun(FSMName) ->
        DefFuncName = list_to_atom(atom_to_list(FSMName) ++ "_definition"),
        {call, Line, {remote, Line, {atom, Line, cure_fsm_runtime}, {atom, Line, register_fsm_type}},
         [{atom, Line, FSMName}, {call, Line, {atom, Line, DefFuncName}, []}]}
    end, FSMNames),
    
    % Create function body with all registration calls + ok return
    Body = RegistrationCalls ++ [{atom, Line, ok}],
    
    % Create the register_fsms/0 function
    {
        function, Line, register_fsms, 0,
        [{clause, Line, [], [], Body}]
    }.

%% Write compiled module to file
write_beam_module(Module, OutputPath) ->
    generate_beam_file(Module, OutputPath).

%% ============================================================================
%% Pattern Compilation with Guard Support
%% ============================================================================

%% Compile match patterns with guards
compile_match_patterns(Patterns, Location, State) ->
    compile_match_patterns_impl(Patterns, [], Location, State).

compile_match_patterns_impl([], Acc, _Location, State) ->
    {lists:flatten(lists:reverse(Acc)), State};
compile_match_patterns_impl([Pattern | Rest], Acc, Location, State) ->
    case compile_match_pattern(Pattern, Location, State) of
        {ok, Instructions, NewState} ->
            compile_match_patterns_impl(Rest, [Instructions | Acc], Location, NewState);
        {error, Reason} ->
            {error, Reason}
    end.

%% Compile a single match pattern with optional guard
compile_match_pattern(#match_clause{pattern = Pattern, guard = Guard, body = Body, location = Location}, _OverrideLocation, State) ->
    % Generate labels for control flow
    {FailLabel, State1} = new_label(State),
    {SuccessLabel, State2} = new_label(State1),
    
    % Compile pattern matching
    {PatternInstr, State3} = compile_pattern(Pattern, FailLabel, State2),
    
    % Compile guard if present
    case Guard of
        undefined ->
            % No guard, compile body directly
            {BodyInstr, State4} = compile_expression(Body, State3),
            
            % Assemble instructions
            Instructions = PatternInstr ++ BodyInstr ++ [
                #beam_instr{op = jump, args = [SuccessLabel], location = Location},
                #beam_instr{op = label, args = [FailLabel], location = Location},
                #beam_instr{op = pattern_fail, args = [], location = Location},
                #beam_instr{op = label, args = [SuccessLabel], location = Location}
            ],
            
            {ok, Instructions, State4};
        _ ->
            case cure_guard_compiler:compile_guard(Guard, State3) of
                {ok, GuardCode, GuardState} ->
                    GuardFailInstr = #beam_instr{
                        op = jump_if_false,
                        args = [FailLabel],
                        location = Location
                    },
                    
                    % Compile body
                    {BodyInstr, State5} = compile_expression(Body, GuardState),
                    
                    % Assemble instructions
                    Instructions = PatternInstr ++ GuardCode ++ [GuardFailInstr] ++ BodyInstr ++ [
                        #beam_instr{op = jump, args = [SuccessLabel], location = Location},
                        #beam_instr{op = label, args = [FailLabel], location = Location},
                        #beam_instr{op = pattern_fail, args = [], location = Location},
                        #beam_instr{op = label, args = [SuccessLabel], location = Location}
                    ],
                    
                    {ok, Instructions, State5};
                {error, GuardReason} ->
                    {error, GuardReason}
            end
    end;

compile_match_pattern(Pattern, Location, State) ->
    % Handle non-clause patterns (backward compatibility)
    {FailLabel, State1} = new_label(State),
    {PatternInstr, State2} = compile_pattern(Pattern, FailLabel, State1),
    
    Instructions = PatternInstr ++ [
        #beam_instr{op = label, args = [FailLabel], location = Location},
        #beam_instr{op = pattern_fail, args = [], location = Location}
    ],
    
    {ok, Instructions, State2}.

%% Compile individual patterns
compile_pattern(#literal_pattern{value = Value, location = Location}, FailLabel, State) ->
    Instructions = [
        #beam_instr{op = match_literal, args = [Value, FailLabel], location = Location}
    ],
    {Instructions, State};

compile_pattern(#identifier_pattern{name = Name, location = Location}, _FailLabel, State) ->
    {VarRef, State1} = new_temp_var(State),
    NewVars = maps:put(Name, {local, VarRef}, State#codegen_state.local_vars),
    
    Instructions = [
        #beam_instr{op = bind_var, args = [VarRef], location = Location}
    ],
    
    {Instructions, State1#codegen_state{local_vars = NewVars}};

compile_pattern(#wildcard_pattern{location = Location}, _FailLabel, State) ->
    Instructions = [
        #beam_instr{op = match_any, args = [], location = Location}
    ],
    {Instructions, State};

compile_pattern(#tuple_pattern{elements = Elements, location = Location}, FailLabel, State) ->
    % Match tuple structure first
    TupleMatchInstr = #beam_instr{
        op = match_tuple,
        args = [length(Elements), FailLabel],
        location = Location
    },
    
    % Compile element patterns
    {ElementInstr, State1} = compile_pattern_elements(Elements, FailLabel, State),
    
    Instructions = [TupleMatchInstr] ++ ElementInstr,
    {Instructions, State1};

compile_pattern(#list_pattern{elements = Elements, tail = Tail, location = Location}, FailLabel, State) ->
    % Match list structure
    ListMatchInstr = #beam_instr{
        op = match_list,
        args = [length(Elements), Tail =/= undefined, FailLabel],
        location = Location
    },
    
    % Compile element patterns
    {ElementInstr, State1} = compile_pattern_elements(Elements, FailLabel, State),
    
    % Compile tail pattern if present
    {TailInstr, State2} = case Tail of
        undefined -> {[], State1};
        _ -> compile_pattern(Tail, FailLabel, State1)
    end,
    
    Instructions = [ListMatchInstr] ++ ElementInstr ++ TailInstr,
    {Instructions, State2};

%% Record pattern
compile_pattern(#record_pattern{name = RecordName, fields = Fields, location = Location}, FailLabel, State) ->
    % First, match that it's the correct record type (represented as tagged tuple)
    % In Erlang, records are represented as {RecordName, Field1, Field2, ...}
    RecordMatchInstr = #beam_instr{
        op = match_tagged_tuple,
        args = [RecordName, length(Fields), FailLabel],
        location = Location
    },
    
    % Compile field patterns
    {FieldInstr, State1} = compile_record_field_patterns(Fields, FailLabel, State),
    
    Instructions = [RecordMatchInstr] ++ FieldInstr,
    {Instructions, State1};

compile_pattern(Pattern, _FailLabel, State) ->
    {error, {unsupported_pattern, Pattern}, State}.

%% Compile pattern elements (for tuples and lists)
compile_pattern_elements(Elements, FailLabel, State) ->
    compile_pattern_elements_impl(Elements, [], FailLabel, State).

%% Compile record field patterns
compile_record_field_patterns(Fields, FailLabel, State) ->
    compile_record_field_patterns_impl(Fields, [], FailLabel, State).

compile_record_field_patterns_impl([], Acc, _FailLabel, State) ->
    {lists:flatten(lists:reverse(Acc)), State};
compile_record_field_patterns_impl([#field_pattern{name = _FieldName, pattern = Pattern} | Rest], Acc, FailLabel, State) ->
    % For record patterns, we assume positional field matching
    % The field order must match the record definition
    case compile_pattern(Pattern, FailLabel, State) of
        {Instructions, NewState} ->
            % Add instruction to advance to next field position
            FieldInstr = Instructions ++ [#beam_instr{op = advance_field, args = [], location = undefined}],
            compile_record_field_patterns_impl(Rest, [FieldInstr | Acc], FailLabel, NewState);
        {error, Reason, ErrorState} ->
            {error, Reason, ErrorState}
    end.

compile_pattern_elements_impl([], Acc, _FailLabel, State) ->
    {lists:flatten(lists:reverse(Acc)), State};
compile_pattern_elements_impl([Element | Rest], Acc, FailLabel, State) ->
    case compile_pattern(Element, FailLabel, State) of
        {Instructions, NewState} ->
            compile_pattern_elements_impl(Rest, [Instructions | Acc], FailLabel, NewState);
        {error, Reason, ErrorState} ->
            {error, Reason, ErrorState}
    end.
