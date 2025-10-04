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

%% Code generation state
-record(codegen_state, {
    module_name,           % Current module being compiled
    functions = [],        % Accumulated function definitions
    exports = [],          % Export specifications
    imports = [],          % Import specifications  
    type_env,              % Type environment from type checker
    options = [],          % Compilation options
    temp_var_counter = 0,  % Counter for generating temporary variables
    label_counter = 0,     % Counter for generating labels
    current_function,      % Currently compiling function
    local_vars = #{}       % Local variable mappings
}).

%% BEAM instruction record for internal representation
-record(beam_instr, {
    op,                    % Instruction opcode
    args = [],             % Instruction arguments
    location               % Source location for debugging
}).

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
        imports = [],
        local_vars = #{},
        temp_var_counter = 0,
        label_counter = 0,
        current_function = undefined,
        type_env = cure_typechecker:builtin_env(),
        options = []
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

compile_module(#module_def{name = Name, exports = Exports, items = Items} = _Module, Options) ->
    State = #codegen_state{
        module_name = Name,
        exports = convert_exports(Exports),
        options = Options,
        type_env = cure_typechecker:builtin_env()
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
        options = Options,
        type_env = cure_typechecker:builtin_env()
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
            NewImports = [Import | NewState#codegen_state.imports],
            FinalState = NewState#codegen_state{imports = NewImports},
            {ok, {import, Import}, FinalState};
        {error, Reason} ->
            {error, Reason}
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
process_imported_item(Module, #function_import{name = Name, arity = Arity}, State) ->
    % Register function import for call resolution
    % In a full implementation, would verify the function exists in the module
    % and potentially generate import stubs or call wrappers
    ImportInfo = {imported_function, Module, Name, Arity},
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
                                   location = Location} = _Function, State) ->
    % Create function compilation context
    FunctionState = State#codegen_state{
        current_function = Name,
        local_vars = create_param_bindings(Params),
        temp_var_counter = 0,
        label_counter = 0
    },
    
    try
        % Compile function body
        {BodyInstructions, FinalState} = compile_expression(Body, FunctionState),
        
        % Generate function prologue and epilogue
        FunctionCode = generate_function_code(Name, Params, BodyInstructions, Location),
        
        {ok, {function, FunctionCode}, FinalState}
    catch
        error:Reason:Stack ->
            {error, {function_compilation_failed, Name, Reason, Stack}}
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
        #block_expr{} -> compile_block_expr(Expr, State);
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
    {LeftInstructions, State1} = compile_expression(Left, State),
    {RightInstructions, State2} = compile_expression(Right, State1),
    
    BinaryOpInstruction = #beam_instr{
        op = binary_op,
        args = [Op],
        location = Location
    },
    
    Instructions = LeftInstructions ++ RightInstructions ++ [BinaryOpInstruction],
    {Instructions, State2}.

%% Compile function calls
compile_function_call(#function_call_expr{function = Function, args = Args, 
                                         location = Location}, State) ->
    % Compile arguments
    {ArgInstructions, State1} = compile_expressions(Args, State),
    
    % Compile function expression
    {FuncInstructions, State2} = compile_expression(Function, State1),
    
    % Generate call instruction
    CallInstruction = #beam_instr{
        op = call,
        args = [length(Args)],
        location = Location
    },
    
    Instructions = ArgInstructions ++ FuncInstructions ++ [CallInstruction],
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

%% Compile block expressions
compile_block_expr(#block_expr{expressions = Expressions, location = _Location}, State) ->
    compile_expressions_sequence(Expressions, State).

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
    
    % Add pop instruction to discard intermediate results
    PopInstruction = #beam_instr{op = pop, args = []},
    {Instructions1 ++ [PopInstruction] ++ Instructions2, State2}.

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
    Counter = State#codegen_state.temp_var_counter,
    TempVar = list_to_atom("_temp_" ++ integer_to_list(Counter)),
    NewState = State#codegen_state{temp_var_counter = Counter + 1},
    {TempVar, NewState}.

%% Generate new label
new_label(State) ->
    Counter = State#codegen_state.label_counter,
    Label = list_to_atom("label_" ++ integer_to_list(Counter)),
    NewState = State#codegen_state{label_counter = Counter + 1},
    {Label, NewState}.

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
        options => State#codegen_state.options
    },
    {ok, Module}.

generate_module_attributes(State) ->
    BaseAttributes = [
        {vsn, [erlang:unique_integer()]},
        {compile_info, State#codegen_state.options}
    ],
    
    % Add FSM registration attributes
    FSMDefinitions = [FSM || {fsm, FSM} <- State#codegen_state.functions],
    FSMAttributes = case FSMDefinitions of
        [] -> [];
        _ -> 
            FSMNames = [maps:get(name, FSM) || FSM <- FSMDefinitions],
            [{fsm_types, FSMNames}]
    end,
    
    % Add debug info if requested
    DebugAttributes = case lists:keyfind(debug_info, 1, State#codegen_state.options) of
        {debug_info, true} ->
            [{debug_info, true}];
        _ ->
            []
    end,
    
    BaseAttributes ++ FSMAttributes ++ DebugAttributes.

%% Convert export specifications
convert_exports(Exports) ->
    [{Name, Arity} || #export_spec{name = Name, arity = Arity} <- Exports].

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
        Exports = maps:get(exports, Module, []),
        Functions = maps:get(functions, Module, []),
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
        {error, _Reason} ->
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
