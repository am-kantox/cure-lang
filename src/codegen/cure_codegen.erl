%% Cure Programming Language - BEAM Code Generator
%% Generates BEAM bytecode from typed Cure AST
-module(cure_codegen).

%% Suppress warnings for work-in-progress helper functions
-compile(
    {nowarn_unused_function, [
        get_record_field_order/1,
        create_ordered_field_patterns/3
    ]}
).

-moduledoc """
# Cure Programming Language - BEAM Code Generator

The code generator transforms typed Cure AST into BEAM bytecode, enabling Cure
programs to run on the Erlang Virtual Machine. It handles all Cure language
features including dependent types, finite state machines, pattern matching,
and integration with Erlang/OTP.

## Features

### Complete Language Support
- **Module Compilation**: Full module support with imports/exports
- **Function Compilation**: Regular and dependent function types
- **Expression Compilation**: All Cure expressions to BEAM instructions
- **Pattern Matching**: Efficient pattern compilation with optimization
- **Type Integration**: Uses type information for optimizations

### FSM Code Generation
- **Native FSM Support**: Compiles FSMs to gen_statem behaviors
- **State Optimization**: Optimizes state transitions and data access
- **Guard Compilation**: Efficient guard expression compilation
- **Action Compilation**: Action sequences to BEAM instructions

### BEAM Integration
- **Bytecode Generation**: Direct BEAM bytecode emission
- **Module Attributes**: Proper module metadata generation
- **Export Lists**: Correct function export handling
- **Debug Information**: Optional debug info generation

### Optimization Features
- **Configurable Levels**: Multiple optimization levels (0-3)
- **Type-directed**: Uses type information for better code
- **Dead Code Elimination**: Removes unused code paths
- **Instruction Optimization**: BEAM instruction-level optimizations

## Compilation Pipeline

### 1. Program Compilation
```erlang
%% Compile entire program
{ok, Modules} = cure_codegen:compile_program(AST),

%% With custom options
Options = [{optimize, 2}, {debug_info, true}],
{ok, Modules} = cure_codegen:compile_program(AST, Options).
```

### 2. Module Compilation
```erlang
%% Compile single module
Module = #module_def{name = 'MyModule', exports = Exports, items = Items},
{ok, CompiledModule} = cure_codegen:compile_module(Module),

%% Generate BEAM file
cure_codegen:write_beam_module(CompiledModule, "MyModule.beam").
```

### 3. Function Compilation
```erlang
%% Compile individual function
Func = #function_def{name = add, params = Params, body = Body},
{ok, CompiledFunc, State} = cure_codegen:compile_function(Func).
```

## Code Generation Process

### Phase 1: AST Analysis
- **Type Information**: Extract and validate type annotations
- **Import Resolution**: Process module imports and dependencies
- **Export Analysis**: Validate and process export specifications
- **Dependency Analysis**: Build function dependency graph

### Phase 2: Instruction Generation
- **Expression Compilation**: Convert expressions to BEAM instructions
- **Pattern Compilation**: Generate efficient pattern matching code
- **Guard Compilation**: Compile guard expressions
- **Control Flow**: Generate conditionals, loops, and jumps

### Phase 3: Optimization
- **Instruction Optimization**: Peephole optimizations
- **Register Allocation**: Efficient register usage
- **Jump Optimization**: Minimize jumps and labels
- **Constant Folding**: Compile-time constant evaluation

### Phase 4: Module Assembly
- **Function Assembly**: Combine compiled functions
- **Attribute Generation**: Create module attributes
- **Export List**: Generate proper export specifications
- **BEAM File**: Produce final BEAM bytecode file

## Compilation Options

### Standard Options
```erlang
Options = [
    {debug_info, true},      % Include debug information
    {optimize, 2},           % Optimization level 0-3
    {warnings, true},        % Enable compilation warnings
    {strict_types, true},    % Strict type checking
    {fsm_integration, true}  % Enable FSM features
].
```

### Optimization Levels
- **Level 0**: No optimizations (fastest compile, debugging)
- **Level 1**: Basic optimizations (safe, minimal impact)
- **Level 2**: Standard optimizations (default, balanced)
- **Level 3**: Aggressive optimizations (maximum performance)

## Expression Compilation

### Literals
```cure
42          → {integer, 42}
"hello"     → {string, "hello"}
true        → {atom, true}
[1,2,3]     → {cons, {integer,1}, {cons, {integer,2}, ...}}
```

### Function Calls
```cure
foo(x, y)   → {call, {atom, foo}, [VarX, VarY]}
Mod.func(x) → {call, {remote, {atom, 'Mod'}, {atom, func}}, [VarX]}
```

### Pattern Matching
```cure
match value do
    {ok, x} -> x
    error -> 0
end
```
Compiles to efficient jump table with pattern tests.

## FSM Compilation

Finite state machines compile to standard Erlang gen_statem:

```cure
fsm Counter do
    states: [idle, counting]
    initial: idle
    
    state idle do
        event start -> counting
    end
end
```

Generates:
- `init/1` callback for initialization
- State callback functions for each state
- Event handling with pattern matching
- State data management

## Error Handling

The code generator provides detailed error information:
- **Compilation Errors**: Unsupported constructs, type mismatches
- **Generation Errors**: BEAM instruction generation failures
- **Optimization Errors**: Failed optimizations (non-fatal)
- **File I/O Errors**: BEAM file writing errors

## Integration with Type System

Uses type information for:
- **Type Erasure**: Remove type annotations while preserving semantics
- **Optimization**: Type-directed optimizations and specializations
- **Error Prevention**: Catch type-related errors during compilation
- **Runtime Checks**: Generate minimal runtime type checks where needed

## BEAM Compatibility

Generates standard BEAM bytecode compatible with:
- **Erlang/OTP**: Full compatibility with Erlang runtime
- **Elixir**: Can be called from Elixir code
- **LFE/Gleam**: Compatible with other BEAM languages
- **Standard Tools**: Works with standard BEAM tools (debugger, profiler)

## Performance Characteristics

- **Compilation Speed**: Linear in program size for most constructs
- **Generated Code**: Comparable performance to hand-written Erlang
- **Memory Usage**: Efficient memory usage during compilation
- **Optimization Impact**: 10-40% performance improvement at higher levels

## Thread Safety

The code generator is stateless at the module level and can safely compile
multiple modules concurrently. Individual function compilation maintains
local state that is not shared between threads.
""".

-export([
    % Main compilation interface
    compile_module/1, compile_module/2,
    compile_function/1, compile_function/2,
    compile_function_impl/2,
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

    % Pattern compilation functions (for testing)
    convert_body_expression_to_erlang/2,
    convert_list_pattern_to_erlang_form/3,
    convert_pattern_to_erlang_form/2,
    compile_patterns_to_case_clauses/2,
    compile_value_to_erlang_form/2,

    % Configuration and options
    default_options/0,
    validate_options/1
]).

%% Include necessary headers
-include("../parser/cure_ast.hrl").
-include("cure_codegen.hrl").
-include("../fsm/cure_fsm_runtime.hrl").

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
    case
        lists:all(
            fun
                ({Key, _}) when is_atom(Key) ->
                    lists:member(Key, ValidOptions);
                (_) ->
                    false
            end,
            Options
        )
    of
        true -> {ok, Options};
        false -> {error, invalid_options}
    end.

%% Create a new compilation state
new_state() ->
    % Register builtin Nat type constructors
    BuiltinConstructors = #{
        % Nullary constructor
        'Zero' => 0,
        % Unary constructor
        'Succ' => 1,
        'Pred' => 1
    },
    #codegen_state{
        module_name = undefined,
        exports = [],
        functions = [],
        local_vars = #{},
        temp_counter = 0,
        label_counter = 0,
        constants = #{},
        type_info = cure_typechecker:builtin_env(),
        optimization_level = 0,
        type_constructors = BuiltinConstructors,
        typeclass_constraints = [],
        typeclass_env = undefined
    }.

%% ============================================================================
%% Main Compilation Interface
%% ============================================================================

-doc """
Compiles a complete Cure program to BEAM bytecode using default options.

This is a convenience function that calls compile_program/2 with default
compilation options.

## Arguments
- `AST` - List of top-level AST items (modules, functions, etc.)

## Returns
- `{ok, Modules}` - Successfully compiled modules
- `{error, {compilation_failed, Errors}}` - Compilation failures

## Example
```erlang
AST = cure_parser:parse_file("program.cure"),
{ok, Modules} = cure_codegen:compile_program(AST),
lists:foreach(fun(Module) ->
    cure_codegen:write_beam_module(Module, filename(Module))
end, Modules).
```

## Default Options
Uses standard compilation options: debug_info, optimization level 1,
warnings enabled, strict types, and FSM integration.
""".
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

-doc """
Compiles a single Cure module to BEAM bytecode using default options.

This function handles compilation of complete module definitions including
exports, imports, function definitions, FSM definitions, and type definitions.
It converts Cure module AST to BEAM-compatible Erlang forms.

## Arguments
- `ModuleAST` - Module AST node (module_def record or tuple format)

## Returns
- `{ok, CompiledModule}` - Successfully compiled module ready for BEAM
- `{error, Reason}` - Compilation error with details

## Example
```erlang
ModuleAST = #module_def{
    name = 'MyModule',
    exports = [{foo, 2}, {bar, 1}],
    items = [FuncDef1, FuncDef2]
},
{ok, BeamModule} = cure_codegen:compile_module(ModuleAST),
cure_codegen:write_beam_module(BeamModule, "MyModule.beam").
```

## Module Processing
- Processes imports and builds import environment
- Validates and converts export specifications
- Compiles all module items (functions, FSMs, types)
- Generates proper BEAM module structure with attributes
- Handles both old and new AST formats for compatibility

## Supported Module Items
- Function definitions (regular and Erlang functions)
- FSM definitions (compiled to gen_statem)
- Record and type definitions
- Import and export declarations
""".
compile_module(ModuleAST) ->
    compile_module(ModuleAST, default_options()).

%% Support for new AST format
compile_module({module_def, Name, Imports, Exports, Items, _Location}, Options) ->
    cure_utils:debug("Compiling module ~p with imports ~p~n", [Name, Imports]),
    % Using new AST format compilation path
    ConvertedExports = convert_exports(Exports, Items),
    % Register builtin Nat type constructors
    BuiltinConstructors = #{
        % Nullary constructor
        'Zero' => 0,
        % Unary constructor
        'Succ' => 1,
        'Pred' => 1
    },
    State = #codegen_state{
        module_name = Name,
        exports = ConvertedExports,
        optimization_level = proplists:get_value(optimize, Options, 0),
        type_info = cure_typechecker:builtin_env(),
        imported_functions = #{},
        type_constructors = BuiltinConstructors
    },

    % Process imports first
    StateWithImports =
        case process_imports(Imports, State) of
            {ok, ImportState} ->
                cure_utils:debug("Import processing succeeded~n"),
                ImportState;
            % Continue with basic state on import errors
            {error, Error} ->
                cure_utils:debug("Import processing failed: ~p~n", [Error]),
                State
        end,

    % Store imported functions in ETS for pattern body conversion
    ImportedFuncs = StateWithImports#codegen_state.imported_functions,
    TableName = cure_codegen_context,
    case ets:info(TableName) of
        undefined ->
            ets:new(TableName, [named_table, public, set]);
        _ ->
            ok
    end,
    ets:insert(TableName, {imported_functions_map, ImportedFuncs}),

    % Extract local function names/arities from AST before compilation
    % This allows is_function_name to work during pattern compilation
    LocalFuncs = extract_function_names_from_items(Items),
    ets:insert(TableName, {local_functions_map, LocalFuncs}),

    case compile_module_items(Items, StateWithImports) of
        {ok, CompiledState} ->
            generate_beam_module(CompiledState);
        {error, Reason} ->
            {error, Reason}
    end;
compile_module(#module_def{name = Name, exports = Exports, items = Items} = Module, Options) ->
    cure_utils:debug("Using old AST format path for module ~p~n", [Name]),
    cure_utils:debug("Module record: ~p~n", [Module]),
    % Check if there are any imports in the items
    Imports = [
        Item
     || Item <- Items, element(1, Item) =:= import_def orelse is_record(Item, import_def)
    ],
    cure_utils:debug("Found imports: ~p~n", [Imports]),
    % Using old AST format compilation path
    ConvertedExports = convert_exports(Exports, Items),
    % Register builtin Nat type constructors
    BuiltinConstructors = #{
        % Nullary constructor
        'Zero' => 0,
        % Unary constructor
        'Succ' => 1,
        'Pred' => 1
    },
    State = #codegen_state{
        module_name = Name,
        exports = ConvertedExports,
        optimization_level = proplists:get_value(optimize, Options, 0),
        type_info = cure_typechecker:builtin_env(),
        imported_functions = #{},
        type_constructors = BuiltinConstructors
    },

    % Process imports from items list
    StateWithImports =
        case process_imports(Imports, State) of
            {ok, ImportState} ->
                cure_utils:debug("Old path import processing succeeded~n"),
                ImportState;
            {error, Error} ->
                cure_utils:debug("Old path import processing failed: ~p~n", [Error]),
                State
        end,

    % Store imported functions in ETS for pattern body conversion
    TableName = cure_codegen_context,
    case ets:info(TableName) of
        undefined ->
            ets:new(TableName, [named_table, public, set]);
        _ ->
            ok
    end,
    ets:insert(
        TableName, {imported_functions_map, StateWithImports#codegen_state.imported_functions}
    ),

    % Extract local function names/arities from AST before compilation (old AST format)
    LocalFuncs = extract_function_names_from_items(Items),
    ets:insert(TableName, {local_functions_map, LocalFuncs}),

    case compile_module_items(Items, StateWithImports) of
        {ok, CompiledState} ->
            generate_beam_module(CompiledState);
        {error, Reason} ->
            {error, Reason}
    end;
compile_module(AST, _Options) ->
    {error, {not_a_module, AST}}.

-doc """
Compiles a single Cure function to BEAM bytecode using default options.

This function handles standalone function compilation, primarily used for
testing and development. In normal compilation, functions are compiled as
part of module compilation.

## Arguments
- `FunctionAST` - Function AST node (function_def record or tuple format)

## Returns
- `{ok, CompiledFunction, State}` - Successfully compiled function with state
- `{error, Reason}` - Compilation error details

## Example
```erlang
FuncAST = #function_def{
    name = add,
    params = [x, y],
    body = {binary_op, '+', {var, x}, {var, y}}
},
{ok, CompiledFunc, _State} = cure_codegen:compile_function(FuncAST).
```

## Function Processing
- Converts function parameters to BEAM registers
- Compiles function body expressions to BEAM instructions
- Handles pattern matching in parameters
- Generates proper function entry and exit code
- Applies function-level optimizations

## Limitations
- Creates minimal compilation state for standalone compilation
- May not have access to full module context for imports/types
- Primarily intended for testing individual functions
""".
compile_function(FunctionAST) ->
    compile_function(FunctionAST, default_options()).

compile_function(#function_def{} = Function, Options) ->
    State = #codegen_state{
        module_name = test_module,
        optimization_level = proplists:get_value(optimize, Options, 0),
        type_info = cure_typechecker:builtin_env(),
        imported_functions = #{}
    },
    case compile_function_impl(Function, State) of
        {ok, CompiledFunction, NewState} ->
            {ok, CompiledFunction, NewState};
        {error, Reason} ->
            {error, Reason}
    end;
compile_function(AST, _Options) ->
    {error, {not_a_function, AST}}.

%% ============================================================================
%% Module Compilation
%% ============================================================================

%% Pre-pass to register all type constructors before compiling functions
register_all_type_constructors([], State) ->
    State;
register_all_type_constructors([Item | Rest], State) ->
    NewState =
        case Item of
            #type_def{} = TypeDef ->
                register_type_constructors(TypeDef, State);
            _ ->
                State
        end,
    register_all_type_constructors(Rest, NewState).

compile_module_items(Items, State) ->
    % Pre-pass: Register all type constructors first
    StateWithConstructors = register_all_type_constructors(Items, State),
    cure_utils:debug("[CODEGEN] Registered type constructors: ~p~n", [
        maps:to_list(StateWithConstructors#codegen_state.type_constructors)
    ]),
    % Now compile all items with constructors available
    compile_module_items(Items, StateWithConstructors, []).

compile_module_items([], State, Acc) ->
    cure_utils:debug("[CODEGEN] Finished compiling items, accumulated ~p items~n", [length(Acc)]),
    lists:foreach(fun(Item) -> cure_utils:debug("  Item: ~p~n", [Item]) end, Acc),
    {ok, State#codegen_state{functions = lists:reverse(Acc)}};
compile_module_items([Item | RestItems], State, Acc) ->
    case compile_module_item(Item, State) of
        {ok, {union_type, _TypeDef, ConstructorFunctions}, NewState} ->
            % Add all constructor functions to the accumulator
            NewAcc = lists:reverse(ConstructorFunctions) ++ Acc,
            % Also add constructor functions to exports
            ConstructorExports = extract_constructor_exports(ConstructorFunctions),
            cure_utils:debug("Adding constructor exports: ~p~n", [ConstructorExports]),
            UpdatedExports = NewState#codegen_state.exports ++ ConstructorExports,
            cure_utils:debug("Updated exports list: ~p~n", [UpdatedExports]),
            NewStateWithExports = NewState#codegen_state{exports = UpdatedExports},
            compile_module_items(RestItems, NewStateWithExports, NewAcc);
        {ok, {record_with_derived, RecordAttr, DerivedInstances}, NewState} ->
            % Add record definition and derived instances
            RecordItem = {record_def, RecordAttr},
            InstanceItems = [{derived_instance, Inst} || Inst <- DerivedInstances],
            NewAcc = lists:reverse(InstanceItems) ++ [RecordItem | Acc],
            cure_utils:debug("Added record with ~p derived instances~n", [length(DerivedInstances)]),
            compile_module_items(RestItems, NewState, NewAcc);
        {ok, {instance, CompiledMethods}, NewState} ->
            % Instance methods need to be unwrapped and added as individual functions
            cure_utils:debug("[INSTANCE] Adding ~p instance methods to module~n", [
                length(CompiledMethods)
            ]),
            NewAcc = lists:reverse(CompiledMethods) ++ Acc,
            compile_module_items(RestItems, NewState, NewAcc);
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
%% Handle curify function definition (both record and tuple formats)
compile_module_item(CurifyFunc = #curify_function_def{}, State) ->
    case compile_curify_function_impl(CurifyFunc, State) of
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
compile_module_item(#record_def{} = RecordDef, State) ->
    % Record definitions generate Erlang record declarations
    % Records in Erlang are defined at compile time and used as tagged tuples
    #record_def{name = RecordName, fields = Fields, derive_clause = DeriveClause} = RecordDef,

    % Register the record definition in the state for later use
    NewRecords = maps:put(RecordName, RecordDef, State#codegen_state.type_constructors),
    NewState = State#codegen_state{type_constructors = NewRecords},

    % Store field order in ETS for pattern matching
    FieldOrder = [Field#record_field_def.name || Field <- Fields],
    cure_utils:debug("[RECORD_DEF] Storing field order for ~p: ~p~n", [RecordName, FieldOrder]),
    TableName = cure_codegen_context,
    case ets:info(TableName) of
        undefined -> ets:new(TableName, [named_table, public, set]);
        _ -> ok
    end,
    ets:insert(TableName, {{record_fields, RecordName}, FieldOrder}),
    cure_utils:debug("[RECORD_DEF] Stored in ETS: ~p~n", [{{record_fields, RecordName}, FieldOrder}]),

    % Process derive clause if present
    case cure_typeclass_codegen:process_derive_clause(DeriveClause, RecordDef, NewState) of
        {ok, DerivedInstances, StateWithDerived} ->
            cure_utils:debug(
                "[DERIVE] Generated ~p instances for ~p~n",
                [length(DerivedInstances), RecordName]
            ),
            % Generate Erlang record attribute for the module
            FieldDefs = generate_erlang_record_fields(Fields),
            RecordAttr = {record, RecordName, FieldDefs},
            % Return both record and derived instances
            {ok, {record_with_derived, RecordAttr, DerivedInstances}, StateWithDerived};
        {error, Reason} ->
            cure_utils:debug(
                "[DERIVE] Failed to process derive clause for ~p: ~p~n",
                [RecordName, Reason]
            ),
            % Continue without derived instances
            FieldDefs = generate_erlang_record_fields(Fields),
            RecordAttr = {record, RecordName, FieldDefs},
            {ok, {record_def, RecordAttr}, NewState}
    end;
compile_module_item(#typeclass_def{} = TypeclassDef, State) ->
    % Typeclass definitions compile to behaviour modules
    cure_utils:debug("[TYPECLASS] Compiling typeclass ~p~n", [TypeclassDef#typeclass_def.name]),
    case cure_typeclass_codegen:compile_typeclass(TypeclassDef, State) of
        {ok, CompiledTypeclass, NewState} ->
            {ok, CompiledTypeclass, NewState};
        {error, Reason} ->
            {error, {typeclass_compilation_failed, Reason}}
    end;
compile_module_item(#instance_def{} = InstanceDef, State) ->
    % Instance definitions compile to concrete method implementations
    cure_utils:debug(
        "[INSTANCE] Compiling instance ~p(~p)~n",
        [InstanceDef#instance_def.typeclass, InstanceDef#instance_def.type_args]
    ),
    case cure_typeclass_codegen:compile_instance(InstanceDef, State) of
        {ok, CompiledMethods, NewState} ->
            {ok, {instance, CompiledMethods}, NewState};
        {error, Reason} ->
            {error, {instance_compilation_failed, Reason}}
    end;
compile_module_item(#type_def{} = TypeDef, State) ->
    % Generate constructor functions for union types
    % Note: Constructors are already registered in the pre-pass
    cure_utils:debug("Processing type_def: ~p~n", [TypeDef]),
    case generate_union_type_constructors(TypeDef, State) of
        {ok, ConstructorFunctions, NewState} ->
            cure_utils:debug("Generated ~p constructor functions~n", [length(ConstructorFunctions)]),
            {ok, {union_type, TypeDef, ConstructorFunctions}, NewState};
        {no_constructors, NewState} ->
            % Not a union type or no constructors needed
            cure_utils:debug("No constructors generated for ~p~n", [TypeDef#type_def.name]),
            {ok, {type_def, TypeDef}, NewState};
        {error, Reason} ->
            cure_utils:debug("ERROR: Failed to generate constructors for ~p: ~p~n", [
                TypeDef#type_def.name, Reason
            ]),
            {error, Reason}
    end;
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
    % For Std module, automatically add core functions that are commonly used
    ExtendedItems =
        case Module of
            'Std' ->
                % Add commonly used functions that should be available from Std
                % Note: print is handled as a global function and routes to cure_std
                CoreFunctions = [zip_with, fold, map, show],
                Items ++ CoreFunctions;
            _ ->
                Items
        end,
    % Process specific imported items
    process_imported_items(Module, ExtendedItems, State).

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
    ImportedFunctions = State#codegen_state.imported_functions,

    % Create import info for the function
    ImportInfo = #{
        module => Module,
        name => Name,
        arity => Arity,
        type => function
    },

    % Store in imported functions map
    UpdatedImports = maps:put({Name, Arity}, ImportInfo, ImportedFunctions),
    UpdatedState = State#codegen_state{imported_functions = UpdatedImports},

    {ok, UpdatedState};
process_imported_item(Module, Identifier, State) when is_atom(Identifier) ->
    % Register identifier import (type constructor, constant, etc.)
    % For function identifiers, try to resolve their actual arity
    ImportedFunctions = State#codegen_state.imported_functions,

    % Attempt to resolve the function arity based on common standard library functions
    ResolvedArity = resolve_function_arity(Module, Identifier),

    % Create import info for the identifier (could be a function, type, or constant)
    ImportInfo = #{
        module => Module,
        name => Identifier,
        arity => ResolvedArity,
        type =>
            case ResolvedArity of
                unknown -> identifier;
                _ -> function
            end
    },

    % Store in imported functions map
    % Use both identifier key and {Name, Arity} key if arity is known
    UpdatedImports1 = maps:put(Identifier, ImportInfo, ImportedFunctions),
    UpdatedImports2 =
        case ResolvedArity of
            unknown ->
                UpdatedImports1;
            _ ->
                maps:put({Identifier, ResolvedArity}, ImportInfo, UpdatedImports1)
        end,

    UpdatedState = State#codegen_state{imported_functions = UpdatedImports2},

    {ok, UpdatedState}.

%% Resolve the arity of a function based on known standard library functions
resolve_function_arity('Std', FunctionName) ->
    case FunctionName of
        % Core list functions
        map -> 2;
        filter -> 2;
        fold -> 3;
        foldl -> 3;
        foldr -> 3;
        zip_with -> 3;
        zip -> 2;
        head -> 1;
        tail -> 1;
        cons -> 2;
        append -> 2;
        reverse -> 1;
        length -> 1;
        is_empty -> 1;
        concat -> 1;
        find -> 2;
        elem -> 2;
        all -> 2;
        any -> 2;
        take -> 2;
        drop -> 2;
        unzip -> 1;
        safe_head -> 1;
        safe_tail -> 1;
        safe_nth -> 2;
        % Show and string functions
        show -> 1;
        % Note: print is handled as global function routing to cure_std
        % Core functions
        identity -> 1;
        compose -> 2;
        flip -> 1;
        'not' -> 1;
        'and' -> 2;
        'or' -> 2;
        'xor' -> 2;
        % Comparison functions
        eq -> 2;
        ne -> 2;
        lt -> 2;
        le -> 2;
        gt -> 2;
        ge -> 2;
        compare -> 2;
        min -> 2;
        max -> 2;
        clamp -> 3;
        % Result/Option functions
        ok -> 1;
        error -> 1;
        some -> 1;
        none -> 0;
        is_ok -> 1;
        is_error -> 1;
        is_some -> 1;
        is_none -> 1;
        map_ok -> 2;
        map_error -> 2;
        and_then -> 2;
        map_option -> 2;
        flat_map_option -> 2;
        option_or -> 2;
        % Utility functions
        const -> 1;
        apply -> 2;
        pipe -> 2;
        % Math functions
        abs -> 1;
        sign -> 1;
        round -> 1;
        floor -> 1;
        ceiling -> 1;
        sqrt -> 1;
        power -> 2;
        safe_divide -> 2;
        safe_sqrt -> 1;
        % Default for unknown functions
        _ -> unknown
    end;
resolve_function_arity(_Module, _FunctionName) ->
    % For modules other than Std, we don't have arity information
    unknown.

%% ============================================================================
%% Function Compilation
%% ============================================================================

compile_function_impl(
    #function_def{
        name = Name,
        clauses = Clauses,
        params = _Params,
        body = _Body,
        constraint = _Constraint,
        location = Location
    } = _Function,
    State
) when Clauses =/= undefined andalso length(Clauses) > 1 ->
    % Multi-clause function - compile each clause as a separate BEAM function clause
    cure_utils:debug("[CODEGEN] Compiling multi-clause function ~p with ~p clauses~n", [
        Name, length(Clauses)
    ]),
    compile_multiclause_function(Name, Clauses, Location, State);
compile_function_impl(
    #function_def{
        name = Name,
        params = Params,
        body = Body,
        constraint = Constraint,
        where_clause = WhereClause,
        location = Location
    } = _Function,
    State
) ->
    % Extract typeclass constraints from where clause
    TypeclassConstraints = extract_typeclass_constraints(WhereClause),

    % Create function compilation context
    FunctionInfo = #{
        name => Name,
        params => Params,
        dimension_bindings => extract_dimension_bindings(Params)
    },
    FunctionState = State#codegen_state{
        local_vars = create_param_bindings(Params),
        temp_counter = 0,
        label_counter = 0,
        current_function = FunctionInfo,
        typeclass_constraints = TypeclassConstraints
    },

    try
        % Compile parameter constraint guards if present
        {GuardInstructions, State1} =
            case Constraint of
                undefined ->
                    {[], FunctionState};
                _ ->
                    case cure_guard_compiler:compile_guard(Constraint, FunctionState) of
                        {ok, Instructions, NewState} ->
                            {
                                Instructions ++ [generate_guard_check_instruction(Location)],
                                NewState
                            };
                        {error, Reason} ->
                            throw({guard_compilation_failed, Reason, Location})
                    end
            end,

        % Compile function body
        {BodyInstructions, FinalState} = compile_expression(Body, State1),

        % Generate function prologue and epilogue
        FunctionCode = generate_function_code(
            Name, Params, GuardInstructions ++ BodyInstructions, Location
        ),

        {ok, {function, FunctionCode}, FinalState}
    catch
        error:CompileReason:Stack ->
            {error, {function_compilation_failed, Name, CompileReason, Stack}}
    end.
% NOTE: Legacy function definition support (without constraint field) is now
% handled by the main clause above since the pattern will match with constraint = undefined

%% Compile multi-clause function into BEAM-compatible Erlang function clauses
compile_multiclause_function(Name, Clauses, Location, State) ->
    try
        % Filter out type parameters from all clauses
        FilteredClauses = lists:map(
            fun(#function_clause{params = Params} = Clause) ->
                RuntimeParams = filter_runtime_params(Params),
                Clause#function_clause{params = RuntimeParams}
            end,
            Clauses
        ),

        % Verify all clauses have the same arity
        Arity =
            case verify_clause_arities(FilteredClauses) of
                {ok, ArityVal} ->
                    ArityVal;
                {error, ArityError} ->
                    throw(ArityError)
            end,

        % Compile each clause into Erlang abstract form
        FunctionClauses = lists:map(
            fun(Clause) ->
                compile_single_function_clause(Clause, Name, Location, State)
            end,
            FilteredClauses
        ),

        % Generate function code map
        FirstClause = hd(FilteredClauses),
        ClauseParams = FirstClause#function_clause.params,
        ParamList = [P#param.name || P <- ClauseParams],
        FunctionCode = #{
            name => Name,
            arity => Arity,
            params => ParamList,
            % Store clauses for later conversion to Erlang abstract forms
            clauses => FunctionClauses,
            is_multiclause => true,
            location => Location
        },

        {ok, {function, FunctionCode}, State}
    catch
        error:CompileReason:Stack ->
            {error, {multiclause_function_compilation_failed, Name, CompileReason, Stack}}
    end.

%% Verify all clauses have the same arity
verify_clause_arities([]) ->
    {error, no_clauses};
verify_clause_arities([#function_clause{params = Params} | Rest]) ->
    Arity = length(Params),
    case all_clauses_have_arity(Rest, Arity) of
        true -> {ok, Arity};
        false -> {error, {mismatched_arities, Arity}}
    end.

all_clauses_have_arity([], _Arity) ->
    true;
all_clauses_have_arity([#function_clause{params = Params} | Rest], Arity) ->
    case length(Params) of
        Arity -> all_clauses_have_arity(Rest, Arity);
        _ -> false
    end.

%% Compile a single function clause (pattern, guard, body) into instructions
compile_single_function_clause(
    #function_clause{
        params = Params,
        body = Body,
        constraint = Constraint,
        location = ClauseLocation
    },
    FunctionName,
    _FunctionLocation,
    State
) ->
    % Create function compilation context for this clause
    FunctionInfo = #{
        name => FunctionName,
        params => Params,
        dimension_bindings => extract_dimension_bindings(Params)
    },
    ClauseState = State#codegen_state{
        local_vars = create_param_bindings(Params),
        temp_counter = 0,
        label_counter = 0,
        current_function = FunctionInfo
    },

    % Compile guard if present
    {GuardInstructions, State1} =
        case Constraint of
            undefined ->
                {[], ClauseState};
            _ ->
                case cure_guard_compiler:compile_guard(Constraint, ClauseState) of
                    {ok, Instructions, NewState} ->
                        {
                            Instructions ++ [generate_guard_check_instruction(ClauseLocation)],
                            NewState
                        };
                    {error, Reason} ->
                        throw({guard_compilation_failed, Reason, ClauseLocation})
                end
        end,

    % Compile body
    {BodyInstructions, _FinalState} = compile_expression(Body, State1),

    % Return clause info (params, guard, body instructions)
    #{
        params => Params,
        param_names => [P#param.name || P <- Params],
        guard_instructions => GuardInstructions,
        body_instructions => BodyInstructions,
        location => ClauseLocation
    }.

%% Compile curify function (wraps Erlang functions with auto-conversion)
%% Generates a Cure function that calls the specified Erlang function
%% and converts the return value to match the Cure signature
compile_curify_function_impl(
    #curify_function_def{
        name = Name,
        params = Params,
        return_type = ReturnType,
        erlang_module = ErlModule,
        erlang_function = ErlFunc,
        erlang_arity = ErlArity,
        location = Location
    },
    State
) ->
    try
        ParamList = [P#param.name || P <- Params],

        % Validate arity matches
        case length(Params) of
            ErlArity ->
                ok;
            ActualArity ->
                throw({curify_arity_mismatch, Name, ActualArity, ErlArity, Location})
        end,

        FunctionCode = #{
            name => Name,
            arity => length(Params),
            params => ParamList,
            % Store curify information
            erlang_module => ErlModule,
            erlang_function => ErlFunc,
            erlang_arity => ErlArity,
            return_type => ReturnType,
            % Flag to identify this as curify
            is_curify_function => true,
            location => Location
        },

        {ok, {function, FunctionCode}, State}
    catch
        error:CompileReason:Stack ->
            {error, {curify_function_compilation_failed, Name, CompileReason, Stack}}
    end.

%% Create parameter bindings for local variable map
create_param_bindings(Params) ->
    lists:foldl(
        fun(#param{name = Name}, Acc) ->
            maps:put(Name, {param, Name}, Acc)
        end,
        #{},
        Params
    ).

%% Generate BEAM function code
generate_function_code(Name, Params, BodyInstructions, Location) ->
    % Filter out type parameters - only keep actual runtime parameters
    RuntimeParams = filter_runtime_params(Params),
    ParamList = [P#param.name || P <- RuntimeParams],

    #{
        name => Name,
        arity => length(RuntimeParams),
        params => ParamList,
        instructions => [
            #beam_instr{op = label, args = [function_start], location = Location}
        ] ++ BodyInstructions,
        location => Location
    }.

%% ============================================================================
%% Expression Compilation
%% ============================================================================

-doc """
Compiles a Cure expression to BEAM instructions using default state.

This is the main expression compilation entry point that handles conversion
of all Cure expression types to equivalent BEAM bytecode instructions.

## Arguments
- `Expr` - Expression AST node (various expr record types)

## Returns
- `{Instructions, State}` - BEAM instructions and updated compilation state
- `{error, Reason}` - Compilation error details

## Example
```erlang
Expr = #binary_op_expr{op = '+', left = {literal, 5}, right = {literal, 3}},
{Instructions, _State} = cure_codegen:compile_expression(Expr).
```

## Supported Expression Types
- Literals (integers, atoms, strings, booleans)
- Identifiers (variables, function references)
- Binary operations (arithmetic, logical, comparison)
- Function calls (local and remote)
- Control flow (if/else, pattern matching)
- Data structures (lists, tuples, records)
- Lambda expressions and blocks
- String interpolation
- Type annotations

## Error Handling
Returns detailed error information for unsupported expressions,
type mismatches, and compilation failures.
""".
compile_expression(Expr) ->
    compile_expression(Expr, #codegen_state{}).

compile_expression(Expr, State) ->
    case Expr of
        #literal_expr{} -> compile_literal(Expr, State);
        #identifier_expr{} -> compile_identifier(Expr, State);
        #binary_op_expr{} -> compile_binary_op(Expr, State);
        #function_call_expr{} -> compile_function_call(Expr, State);
        #let_expr{} -> compile_let_expr(Expr, State);
        #list_expr{} -> compile_list_expr(Expr, State);
        #vector_expr{} -> compile_vector_expr(Expr, State);
        #cons_expr{} -> compile_cons_expr(Expr, State);
        #tuple_expr{} -> compile_tuple_expr(Expr, State);
        #block_expr{} -> compile_block_expr(Expr, State);
        #lambda_expr{} -> compile_lambda_expr(Expr, State);
        #unary_op_expr{} -> compile_unary_op_expr(Expr, State);
        #match_expr{} -> compile_match_expr(Expr, State);
        #string_interpolation_expr{} -> compile_string_interpolation(Expr, State);
        #type_annotation_expr{} -> compile_type_annotation(Expr, State);
        #record_expr{} -> compile_record_expr(Expr, State);
        #record_update_expr{} -> compile_record_update_expr(Expr, State);
        #field_access_expr{} -> compile_field_access_expr(Expr, State);
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
            % Check if it's a dependent type dimension parameter first
            case is_dependent_type_dimension(Name, State) of
                {true, Value} ->
                    % It's a dimension parameter, resolve to its concrete value
                    Instruction = #beam_instr{
                        op = load_literal,
                        args = [Value],
                        location = Location
                    },
                    {[Instruction], State};
                {runtime_length, ParamName} ->
                    % It's a runtime length computation - generate list length instruction
                    Instructions = [
                        #beam_instr{
                            op = load_param,
                            args = [ParamName],
                            location = Location
                        },
                        #beam_instr{
                            op = list_length,
                            args = [],
                            location = Location
                        }
                    ],
                    {Instructions, State};
                false ->
                    % Check if it's a nullary constructor (zero-arity type constructor)
                    % When we see a bare identifier that's a nullary constructor, just load it.
                    % The call instruction will be added if it's used in a function_call_expr.
                    case is_nullary_constructor(Name, State) of
                        true ->
                            % Just load the constructor name - don't call it yet
                            % The call will happen when this is used in function_call_expr
                            Instruction = #beam_instr{
                                op = load_global,
                                args = [Name],
                                location = Location
                            },
                            {[Instruction], State};
                        false ->
                            % Check if it's an imported function
                            case find_imported_function(Name, State) of
                                {ok, ImportedFunction} ->
                                    % Create a function reference to the imported function
                                    Instruction = #beam_instr{
                                        op = load_imported_function,
                                        args = [Name, ImportedFunction],
                                        location = Location
                                    },
                                    {[Instruction], State};
                                not_found ->
                                    % Might be a global function
                                    Instruction = #beam_instr{
                                        op = load_global,
                                        args = [Name],
                                        location = Location
                                    },
                                    {[Instruction], State}
                            end
                    end
            end;
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

%% Check if identifier is a dependent type dimension and resolve its value
is_dependent_type_dimension(Name, State) ->
    % If we're compiling a function that takes a Vector(T, n) parameter,
    % and we encounter identifier 'n', resolve it to a runtime length computation
    case State#codegen_state.current_function of
        undefined ->
            false;
        FunctionInfo ->
            % Look for dimension parameters in the function signature
            DimensionMap = maps:get(dimension_bindings, FunctionInfo, #{}),
            case maps:get(Name, DimensionMap, undefined) of
                undefined ->
                    % Try to infer from common patterns for legacy support
                    case Name of
                        n -> infer_list_length_from_context(State);
                        % Default for accumulator
                        m -> {true, 0};
                        _ -> false
                    end;
                {runtime_param_length, ParamName} ->
                    % Need to compute length of ParamName at runtime
                    {runtime_length, ParamName};
                Value when is_integer(Value) ->
                    % Static value
                    {true, Value};
                _ ->
                    false
            end
    end.

%% Extract dimension bindings from function parameters
extract_dimension_bindings(Params) ->
    % Look for Vector(T, n) patterns in parameters and extract dimension variables
    % For dependent types, we need to compute dimensions at runtime from actual values
    lists:foldl(
        fun(Param, Acc) ->
            case extract_dimension_from_param(Param) of
                {ok, DimVar, _ParamName} ->
                    maps:put(DimVar, {runtime_param_length, _ParamName}, Acc);
                error ->
                    Acc
            end
        end,
        #{},
        Params
    ).

%% Extract dimension variable from a parameter
extract_dimension_from_param(#param{name = ParamName, type = Type}) ->
    case Type of
        #dependent_type{name = 'Vector', type_params = TypeParams, value_params = ValueParams} ->
            AllParams = TypeParams ++ ValueParams,
            case AllParams of
                [_TypeParam, DimParam] ->
                    case DimParam of
                        #identifier_expr{name = DimVar} ->
                            {ok, DimVar, ParamName};
                        #type_param{type = #identifier_expr{name = DimVar}} ->
                            {ok, DimVar, ParamName};
                        {primitive_type, DimVar} when is_atom(DimVar) -> {ok, DimVar, ParamName};
                        _ ->
                            error
                    end;
                _ ->
                    error
            end;
        {dependent_type, 'Vector', [_TypeParam, DimParam]} ->
            case DimParam of
                #type_param{type = #identifier_expr{name = DimVar}} ->
                    {ok, DimVar, ParamName};
                #type_param{type = {primitive_type, DimVar}} when is_atom(DimVar) ->
                    {ok, DimVar, ParamName};
                _ ->
                    error
            end;
        _ ->
            error
    end;
extract_dimension_from_param(_) ->
    error.

%% Infer list length from context (runtime extraction)
infer_list_length_from_context(State) ->
    % For dependent type dimensions, we need to extract runtime length from parameters
    case State#codegen_state.current_function of
        #{name := length, params := Params} ->
            % For length function, find the vector parameter and extract its runtime length
            case find_vector_param(Params) of
                {ok, ParamName} -> {runtime_length, ParamName};
                error -> false
            end;
        #{name := is_empty, params := Params} ->
            % For is_empty function, same logic
            case find_vector_param(Params) of
                {ok, ParamName} -> {runtime_length, ParamName};
                error -> false
            end;
        _ ->
            false
    end.

%% Find the vector parameter in a list of parameters
find_vector_param([]) ->
    error;
find_vector_param([#param{name = ParamName, type = Type} | Rest]) ->
    case Type of
        #dependent_type{name = 'Vector'} -> {ok, ParamName};
        {dependent_type, 'Vector', _} -> {ok, ParamName};
        _ -> find_vector_param(Rest)
    end;
% find_vector_param([{param, ParamName, Type, _} | Rest]) ->
%     case Type of
%         #dependent_type{name = 'Vector'} -> {ok, ParamName};
%         {dependent_type, 'Vector', _} -> {ok, ParamName};
%         _ -> find_vector_param(Rest)
%     end;
find_vector_param([_ | Rest]) ->
    find_vector_param(Rest).

%% Check if identifier is a nullary (zero-arity) constructor
%% These are type constructors like Lt, Eq, Gt, None that have no arguments
is_nullary_constructor(Name, State) ->
    % Check in the registered type constructors map
    TypeConstructors = State#codegen_state.type_constructors,
    case maps:get(Name, TypeConstructors, undefined) of
        % Zero-arity constructor
        0 -> true;
        % Either doesn't exist or has non-zero arity
        _ -> false
    end.

%% Find imported function by name (with any arity)
find_imported_function(Name, State) ->
    ImportedFunctions = State#codegen_state.imported_functions,

    % First try to find by identifier name (for imports like "import Std [List, Result]")
    case maps:get(Name, ImportedFunctions, undefined) of
        undefined ->
            % Look for functions with this name and specific arity
            MatchingFunctions = maps:filter(
                fun
                    ({FuncName, _Arity}, _Data) -> FuncName =:= Name;
                    (FuncName, _Data) when is_atom(FuncName) -> FuncName =:= Name
                end,
                ImportedFunctions
            ),
            case maps:size(MatchingFunctions) of
                0 ->
                    not_found;
                _ ->
                    % Return the first matching function
                    {_Key, FunctionData} = hd(maps:to_list(MatchingFunctions)),
                    {ok, FunctionData}
            end;
        FunctionData ->
            % Found direct identifier match
            {ok, FunctionData}
    end.

%% Compile binary operations
compile_binary_op(
    #binary_op_expr{
        op = Op,
        left = Left,
        right = Right,
        location = Location
    },
    State
) ->
    case Op of
        '.' ->
            % Dot operator: field access or module-qualified call
            % Convert to field access expression
            case Right of
                #identifier_expr{name = FieldName, location = FieldLoc} ->
                    % This is field access: Left.FieldName
                    compile_field_access_expr(
                        #field_access_expr{
                            record = Left,
                            field = FieldName,
                            location = FieldLoc
                        },
                        State
                    );
                _ ->
                    % Not a simple identifier, might be complex module qualification
                    % Fall through to regular binary op handling
                    {LeftInstructions, State1} = compile_expression(Left, State),
                    {RightInstructions, State2} = compile_expression(Right, State1),

                    BinaryOpInstruction = #beam_instr{
                        op = binary_op,
                        args = [Op],
                        location = Location
                    },

                    Instructions = LeftInstructions ++ RightInstructions ++ [BinaryOpInstruction],
                    {Instructions, State2}
            end;
        '|>' ->
            % Monadic pipe operator: Left |> Right with automatic ok() wrapping and error propagation
            % The first argument is wrapped with ok(arg), then each pipe operation:
            % - If Left is Ok(value), unwrap and call Right(value), return Ok(result) or Error(reason)
            % - If Left is Error(reason), propagate error without calling Right
            {LeftInstructions, State1} = compile_expression(Left, State),

            % Create monadic pipe instruction
            case Right of
                #function_call_expr{function = Function, args = Args} ->
                    % Compile function and original args
                    {FuncInstructions, State2} = compile_expression(Function, State1),
                    {ArgInstructions, State3} = compile_expressions(Args, State2),

                    % Create monadic pipe with function call
                    MonadicPipeInstruction = #beam_instr{
                        op = monadic_pipe_call,
                        % +1 for the piped value
                        args = [length(Args) + 1],
                        location = Location
                    },

                    % Instructions: Function, Left, Args..., MonadicPipe (correct stack order)
                    Instructions =
                        FuncInstructions ++ LeftInstructions ++ ArgInstructions ++
                            [MonadicPipeInstruction],
                    {Instructions, State3};
                _ ->
                    % Right is just a function, call it with Left as argument
                    {RightInstructions, State2} = compile_expression(Right, State1),

                    % Create monadic pipe with simple function
                    MonadicPipeInstruction = #beam_instr{
                        op = monadic_pipe_call,
                        % One argument (the piped value)
                        args = [1],
                        location = Location
                    },

                    % Instructions: Function, Left, MonadicPipe (correct stack order)
                    Instructions =
                        RightInstructions ++ LeftInstructions ++ [MonadicPipeInstruction],
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
compile_function_call(
    #function_call_expr{
        function = Function,
        args = Args,
        location = Location
    },
    State
) ->
    % Check if this is a typeclass method call
    case try_resolve_typeclass_method(Function, Args, State) of
        {ok, ResolvedFunction} ->
            % Use resolved instance method
            compile_function_call(
                #function_call_expr{
                    function = ResolvedFunction,
                    args = Args,
                    location = Location
                },
                State#codegen_state{typeclass_constraints = []}
            );
        not_typeclass ->
            % Regular function call
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
            {Instructions, State2}
    end.

%% Compile type annotations (just compile the expression, ignore the type)
compile_type_annotation(#type_annotation_expr{expr = Expr, type = _Type}, State) ->
    % Type annotations are compile-time only, so just compile the expression
    compile_expression(Expr, State).

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

%% Compile vector expressions ‹elem1, elem2, ...›
%% Vectors are compiled to lists at runtime
compile_vector_expr(#vector_expr{elements = Elements, location = Location}, State) ->
    {ElementInstructions, State1} = compile_expressions(Elements, State),

    ListInstruction = #beam_instr{
        op = make_list,
        args = [length(Elements)],
        location = Location
    },

    Instructions = ElementInstructions ++ [ListInstruction],
    {Instructions, State1}.

%% Compile cons expressions [head | tail]
compile_cons_expr(#cons_expr{elements = Elements, tail = Tail, location = Location}, State) ->
    % Compile head elements
    {ElementInstructions, State1} = compile_expressions(Elements, State),

    % Compile tail
    {TailInstructions, State2} = compile_expression(Tail, State1),

    % Generate cons instruction
    ConsInstruction = #beam_instr{
        op = make_cons,
        % Number of head elements
        args = [length(Elements)],
        location = Location
    },

    % Instructions: Elements first, then tail, then cons operation
    Instructions = ElementInstructions ++ TailInstructions ++ [ConsInstruction],
    {Instructions, State2}.

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

%% Compile record expressions
compile_record_expr(#record_expr{name = RecordName, fields = Fields, location = Location}, State) ->
    % Compile field values
    {FieldInstructions, State1} = compile_record_field_exprs(Fields, State),

    % Create field name list for the record construction
    FieldNames = [Field#field_expr.name || Field <- Fields],

    % Generate record construction instruction
    RecordInstruction = #beam_instr{
        op = make_record,
        args = [RecordName, FieldNames, length(Fields)],
        location = Location
    },

    Instructions = FieldInstructions ++ [RecordInstruction],
    {Instructions, State1}.

%% Compile record update expressions
compile_record_update_expr(
    #record_update_expr{name = RecordName, base = BaseExpr, fields = Fields, location = Location},
    State
) ->
    % Compile base record expression
    {BaseInstructions, State1} = compile_expression(BaseExpr, State),

    % Compile field values
    {FieldInstructions, State2} = compile_record_field_exprs(Fields, State1),

    % Create field name list for the record update
    FieldNames = [Field#field_expr.name || Field <- Fields],

    % Generate record update instruction
    UpdateInstruction = #beam_instr{
        op = update_record,
        args = [RecordName, FieldNames, length(Fields)],
        location = Location
    },

    Instructions = BaseInstructions ++ FieldInstructions ++ [UpdateInstruction],
    {Instructions, State2}.

%% Compile field access expressions
compile_field_access_expr(
    #field_access_expr{record = RecordExpr, field = FieldName, location = Location}, State
) ->
    % Compile the record expression
    {RecordInstructions, State1} = compile_expression(RecordExpr, State),

    % Generate field access instruction
    FieldAccessInstruction = #beam_instr{
        op = record_field_access,
        args = [FieldName],
        location = Location
    },

    Instructions = RecordInstructions ++ [FieldAccessInstruction],
    {Instructions, State1}.

%% Compile record field expressions
compile_record_field_exprs(Fields, State) ->
    compile_record_field_exprs(Fields, State, []).

compile_record_field_exprs([], State, Acc) ->
    {lists:flatten(lists:reverse(Acc)), State};
compile_record_field_exprs([#field_expr{value = Value} | Rest], State, Acc) ->
    {ValueInstructions, State1} = compile_expression(Value, State),
    compile_record_field_exprs(Rest, State1, [ValueInstructions | Acc]).

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
    % Generate a case expression directly instead of using complex instruction sequences
    {ExprInstructions, State1} = compile_expression(Expr, State),

    % Build case clauses from patterns
    {CaseClauses, State2} = compile_patterns_to_case_clauses(Patterns, State1),

    % Create a case instruction that generates the proper Erlang case expression
    CaseInstruction = #beam_instr{
        op = make_case,
        args = [CaseClauses],
        location = Location
    },

    Instructions = ExprInstructions ++ [CaseInstruction],
    {Instructions, State2}.

%% Compile string interpolation expressions
compile_string_interpolation(#string_interpolation_expr{parts = Parts, location = Location}, State) ->
    compile_string_interpolation_parts(Parts, [], State, Location).

compile_string_interpolation_parts([], Acc, State, Location) ->
    % Create string concatenation instruction
    StringConcatInstruction = #beam_instr{
        op = concat_strings,
        args = [length(Acc)],
        location = Location
    },

    Instructions = lists:reverse(Acc) ++ [StringConcatInstruction],
    {Instructions, State};
compile_string_interpolation_parts([{string_part, String} | Rest], Acc, State, Location) ->
    % Compile string literal
    StringInstruction = #beam_instr{
        op = load_literal,
        args = [String],
        location = Location
    },
    compile_string_interpolation_parts(Rest, [StringInstruction | Acc], State, Location);
compile_string_interpolation_parts([{expr, Expr} | Rest], Acc, State, Location) ->
    % Compile expression and convert to string
    {ExprInstructions, State1} = compile_expression(Expr, State),
    ToStringInstruction = #beam_instr{
        op = to_string,
        args = [],
        location = Location
    },
    ExprWithToString = ExprInstructions ++ [ToStringInstruction],
    compile_string_interpolation_parts(Rest, ExprWithToString ++ Acc, State1, Location).

%% ============================================================================
%% FSM Compilation
%% ============================================================================

-doc """
Compiles a finite state machine definition to BEAM runtime functions.

This function transforms a Cure FSM definition into executable BEAM code
that integrates with the FSM runtime system. It generates helper functions
for spawning, controlling, and querying FSM instances.

## Arguments
- `FSMDef` - FSM definition AST node (#fsm_def{})
- `State` - Current compilation state

## Returns
- `{ok, {fsm, CompiledFSM}, NewState}` - Successfully compiled FSM
- `{error, Reason}` - Compilation error details

## Generated Functions
For an FSM named `Counter`, generates:
- `Counter_spawn/0` - Spawn FSM with default initial state
- `Counter_spawn/1` - Spawn FSM with custom initial data
- `Counter_send/2` - Send event to FSM instance
- `Counter_state/1` - Get current state of FSM instance
- `Counter_stop/1` - Stop FSM instance gracefully
- `Counter_definition/0` - Get compiled FSM definition

## Example
```erlang
FSM = #fsm_def{
    name = 'Counter',
    states = [idle, counting],
    initial = idle,
    state_defs = [IdleState, CountingState]
},
{ok, {fsm, CompiledFSM}, NewState} = compile_fsm_impl(FSM, State).
```

## FSM Runtime Integration
- Compiles FSM to cure_fsm_runtime format
- Generates proper BEAM bytecode for FSM operations
- Integrates with gen_statem behavior patterns
- Handles state transitions, events, and timeouts
- Provides type-safe FSM interface functions

## State Management
FSMs maintain state data through:
- Initial state setup from spawn parameters
- State data transformation during transitions
- Event payload integration with state data
- Timeout handling with state persistence
""".
compile_fsm_impl(
    #fsm_def{
        name = Name,
        states = States,
        initial = Initial,
        state_defs = StateDefs,
        location = Location
    } = FSMDef,
    State
) ->
    try
        % Optional: Run FSM verification pass
        % Set CURE_FSM_VERIFY=1 environment variable to enable verification
        case os:getenv("CURE_FSM_VERIFY") of
            "1" ->
                cure_utils:debug("[FSM_VERIFY] Running verification for FSM: ~p~n", [Name]),
                case cure_fsm_verifier:verify_fsm(FSMDef) of
                    {ok, VerificationResults} ->
                        report_verification_results(Name, VerificationResults);
                    {error, VerifyError} ->
                        cure_utils:debug(
                            "[FSM_VERIFY] Verification failed for ~p: ~p~n",
                            [Name, VerifyError]
                        )
                end;
            _ ->
                % Verification disabled
                ok
        end,

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

%% Report FSM verification results
report_verification_results(FSMName, Results) ->
    cure_utils:debug("[FSM_VERIFY] Verification results for ~p:~n", [FSMName]),
    lists:foreach(
        fun(Result) ->
            case Result of
                {reachable, State} ->
                    cure_utils:debug("  ✓ State ~p is reachable~n", [State]);
                {unreachable, State} ->
                    cure_utils:debug("  ⚠ Warning: State ~p is unreachable~n", [State]);
                {has_deadlock, State} ->
                    cure_utils:debug(
                        "  ⚠ Warning: State ~p is a deadlock (no outgoing transitions)~n", [State]
                    );
                {liveness_satisfied} ->
                    cure_utils:debug("  ✓ Liveness property satisfied~n");
                {liveness_violated, Reason} ->
                    cure_utils:debug("  ⚠ Warning: Liveness property violated: ~p~n", [Reason]);
                _ ->
                    cure_utils:debug("  ~ Result: ~p~n", [Result])
            end
        end,
        Results
    ).

%% Generate BEAM functions for FSM access
generate_fsm_functions(FSMName, CompiledFSM, Location) ->
    % generate_fsm_spawn_function returns a list with 2 functions (spawn/0 and spawn/1)
    % Others return single functions
    % generate_fsm_definition_function now returns an Erlang abstract form
    SpawnFunctions = generate_fsm_spawn_function(FSMName, Location),
    SendFunction = generate_fsm_send_function(FSMName, Location),
    StateFunction = generate_fsm_state_function(FSMName, Location),
    StopFunction = generate_fsm_stop_function(FSMName, Location),
    DefinitionFunction = generate_fsm_definition_function(FSMName, CompiledFSM, Location),

    % Flatten the list and include the Erlang form
    SpawnFunctions ++ [SendFunction, StateFunction, StopFunction, DefinitionFunction].

%% Generate FSM spawn function: FSMName_spawn/0, FSMName_spawn/1
generate_fsm_spawn_function(FSMName, Location) ->
    FunctionName = list_to_atom(atom_to_list(FSMName) ++ "_spawn"),

    % Generate spawn/0 function
    Spawn0 = #{
        name => FunctionName,
        arity => 0,
        params => [],
        instructions => [
            #beam_instr{op = load_literal, args = [FSMName], location = Location},
            #beam_instr{
                op = call_bif, args = [cure_fsm_runtime, start_fsm, 1], location = Location
            },
            #beam_instr{op = return, args = [], location = Location}
        ],
        location => Location
    },

    % Generate spawn/1 function with initial data
    Spawn1FunctionName = FunctionName,
    Spawn1 = #{
        name => Spawn1FunctionName,
        arity => 1,
        params => [init_data],
        instructions => [
            #beam_instr{op = load_literal, args = [FSMName], location = Location},
            #beam_instr{op = load_param, args = [init_data], location = Location},
            #beam_instr{
                op = call_bif, args = [cure_fsm_runtime, start_fsm, 2], location = Location
            },
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
        params => [fsm_pid, event],
        instructions => [
            #beam_instr{op = load_param, args = [fsm_pid], location = Location},
            #beam_instr{op = load_param, args = [event], location = Location},
            #beam_instr{
                op = call_bif, args = [cure_fsm_runtime, send_event, 2], location = Location
            },
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
        params => [fsm_pid],
        instructions => [
            #beam_instr{op = load_param, args = [fsm_pid], location = Location},
            #beam_instr{
                op = call_bif, args = [cure_fsm_runtime, get_state, 1], location = Location
            },
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
        params => [fsm_pid],
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
    Line = get_location_line(Location),

    % Extract FSM definition components
    #fsm_definition{
        name = Name,
        states = States,
        initial_state = InitialState,
        initial_payload = InitialPayload,
        transitions = Transitions,
        timeouts = Timeouts
    } = CompiledFSM,

    % Generate Erlang abstract form directly to avoid literal embedding issues
    % This constructs the #fsm_definition{} record at runtime
    RecordConstruction = {
        record,
        Line,
        fsm_definition,
        [
            {record_field, Line, {atom, Line, name}, {atom, Line, Name}},
            {record_field, Line, {atom, Line, states},
                {cons, Line, {atom, Line, hd(States)}, build_list(tl(States), Line)}},
            {record_field, Line, {atom, Line, initial_state}, {atom, Line, InitialState}},
            {record_field, Line, {atom, Line, initial_payload}, build_term(InitialPayload, Line)},
            {record_field, Line, {atom, Line, transitions}, build_map_literal(Transitions, Line)},
            {record_field, Line, {atom, Line, timeouts}, build_map_literal(Timeouts, Line)}
        ]
    },

    % Return as an already-formed Erlang function
    {function, Line, FunctionName, 0, [
        {clause, Line, [], [], [RecordConstruction]}
    ]}.

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

%% Helper function to get line number from location
get_location_line({location, Line, _, _}) -> Line;
get_location_line(_) -> 1.

%% Helper function to build Erlang abstract form for a list
build_list([], Line) ->
    {nil, Line};
build_list([H | T], Line) when is_atom(H) ->
    {cons, Line, {atom, Line, H}, build_list(T, Line)};
build_list([H | T], Line) ->
    {cons, Line, build_term(H, Line), build_list(T, Line)}.

%% Helper function to build Erlang abstract form for a map
build_map_literal(Map, Line) when map_size(Map) == 0 ->
    {map, Line, []};
build_map_literal(Map, Line) ->
    Assocs = maps:fold(
        fun(Key, Value, Acc) ->
            KeyForm = build_term(Key, Line),
            ValueForm = build_term(Value, Line),
            [{map_field_assoc, Line, KeyForm, ValueForm} | Acc]
        end,
        [],
        Map
    ),
    {map, Line, lists:reverse(Assocs)}.

%% Helper function to build Erlang abstract form for any term
build_term(Term, Line) when is_atom(Term) ->
    {atom, Line, Term};
build_term(Term, Line) when is_integer(Term) ->
    {integer, Line, Term};
build_term(Term, Line) when is_float(Term) ->
    {float, Line, Term};
build_term(Term, Line) when is_binary(Term) ->
    {bin, Line, [{bin_element, Line, {string, Line, binary_to_list(Term)}, default, default}]};
build_term(Term, Line) when is_list(Term) ->
    build_list(Term, Line);
build_term(Term, Line) when is_tuple(Term) ->
    Elements = [build_term(E, Line) || E <- tuple_to_list(Term)],
    {tuple, Line, Elements};
build_term(Term, Line) when is_map(Term) ->
    build_map_literal(Term, Line);
build_term(undefined, Line) ->
    {atom, Line, undefined};
build_term(_Term, Line) ->
    % For complex terms we can't easily represent, use undefined
    {atom, Line, undefined}.

%% ============================================================================
%% Utility Functions
%% ============================================================================

%% Compile multiple expressions
compile_expressions(Expressions, State) ->
    compile_expressions(Expressions, State, []).

compile_expressions([], State, Acc) ->
    % The accumulator is built in reverse order, so we need to reverse it
    % But the instructions within each expression should maintain their order
    ReversedAcc = lists:reverse(Acc),
    Flattened = lists:flatten(ReversedAcc),
    {Flattened, State};
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
compile_bindings(
    [#binding{pattern = Pattern, value = Value, location = Location} | RestBindings], State, Acc
) ->
    {ValueInstructions, State1} = compile_expression(Value, State),
    {PatternInstructions, State2} = compile_pattern_binding(Pattern, Location, State1),

    % Ensure correct order: first load value, then store it
    Instructions = ValueInstructions ++ PatternInstructions,
    compile_bindings(RestBindings, State2, [Instructions | Acc]).

%% Compile pattern bindings (simplified - only identifier patterns for now)
compile_pattern_binding(
    #identifier_pattern{name = Name, location = Location}, _BindingLocation, State
) ->
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
% new_label(State) ->
%     Counter = State#codegen_state.label_counter,
%     Label = list_to_atom("label_" ++ integer_to_list(Counter)),
%     NewState = State#codegen_state{label_counter = Counter + 1},
%     {Label, NewState}.

%% Filter out type parameters from function parameters
%% Type parameters are compile-time only and shouldn't appear in runtime function signatures
filter_runtime_params(Params) ->
    lists:filter(
        fun(#param{name = Name}) ->
            % Keep parameter if it's NOT a type parameter
            not is_likely_type_parameter(Name)
        end,
        Params
    ).

%% Check if a parameter name is likely a type parameter
is_likely_type_parameter(ParamName) when is_atom(ParamName) ->
    ParamStr = atom_to_list(ParamName),
    case ParamStr of
        % Single letter uppercase (T, U, V, etc.) - likely type parameters
        [C] when C >= $A, C =< $Z -> true;
        % NOTE: We don't filter single-letter lowercase names like "n", "k", "m", "i", "j"
        % because they're commonly used as runtime parameters (e.g., from_nat(n: Nat))
        % In a dependent type system, these could be either type-level or runtime parameters.
        % Proper filtering would require examining the parameter's type annotation.
        % Other patterns
        _ -> false
    end;
is_likely_type_parameter(_) ->
    false.

%% Check if expression has side effects and should not be discarded
has_side_effects(#function_call_expr{function = Function}) ->
    case Function of
        #identifier_expr{name = FuncName} ->
            % Check if this is a side-effecting function like print
            is_side_effecting_function(FuncName);
        _ ->
            % Conservative: assume complex function calls have side effects
            true
    end;
% Let expressions can have side effects in bindings
has_side_effects(#let_expr{}) ->
    true;
% Match expressions can have side effects
has_side_effects(#match_expr{}) ->
    true;
% Block expressions can have side effects
has_side_effects(#block_expr{}) ->
    true;
% Literals, identifiers, etc. are pure
has_side_effects(_) ->
    false.

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

%% Separate different types of items in the functions list
separate_functions(Functions) ->
    separate_functions(Functions, [], [], [], []).

separate_functions([], RegularAcc, FSMAcc, ConstructorAcc, RecordAcc) ->
    cure_utils:debug("[SEPARATE] Regular functions: ~p~n", [length(RegularAcc)]),
    cure_utils:debug("[SEPARATE] FSM functions: ~p~n", [length(FSMAcc)]),
    cure_utils:debug("[SEPARATE] Constructor functions: ~p~n", [length(ConstructorAcc)]),
    cure_utils:debug("[SEPARATE] Record definitions: ~p~n", [length(RecordAcc)]),
    {
        lists:reverse(RegularAcc),
        lists:reverse(FSMAcc),
        lists:reverse(ConstructorAcc),
        lists:reverse(RecordAcc)
    };
separate_functions([{function, F} | Rest], RegularAcc, FSMAcc, ConstructorAcc, RecordAcc) ->
    % Wrapped regular function
    separate_functions(Rest, [F | RegularAcc], FSMAcc, ConstructorAcc, RecordAcc);
separate_functions([{fsm, FSM} | Rest], RegularAcc, FSMAcc, ConstructorAcc, RecordAcc) ->
    % FSM definition
    separate_functions(Rest, RegularAcc, [FSM | FSMAcc], ConstructorAcc, RecordAcc);
separate_functions(
    [{record_def, RecordAttr} | Rest], RegularAcc, FSMAcc, ConstructorAcc, RecordAcc
) ->
    % Record definition attribute
    separate_functions(Rest, RegularAcc, FSMAcc, ConstructorAcc, [RecordAttr | RecordAcc]);
separate_functions(
    [{function, _Line, _Name, _Arity, _Clauses} = ErlangFunction | Rest],
    RegularAcc,
    FSMAcc,
    ConstructorAcc,
    RecordAcc
) ->
    % Erlang abstract form (constructor function)
    separate_functions(Rest, RegularAcc, FSMAcc, [ErlangFunction | ConstructorAcc], RecordAcc);
separate_functions([F | Rest], RegularAcc, FSMAcc, ConstructorAcc, RecordAcc) when is_map(F) ->
    % Unwrapped regular function (map format)
    separate_functions(Rest, [F | RegularAcc], FSMAcc, ConstructorAcc, RecordAcc);
separate_functions([_Other | Rest], RegularAcc, FSMAcc, ConstructorAcc, RecordAcc) ->
    % Skip unknown items
    separate_functions(Rest, RegularAcc, FSMAcc, ConstructorAcc, RecordAcc).

generate_beam_module(State) ->
    % Extract different types of items from the functions list
    {RegularFunctions, FSMDefinitions, ConstructorFunctions, RecordDefinitions} =
        separate_functions(State#codegen_state.functions),

    cure_utils:debug("BEAM generation - Constructor functions: ~p~n", [ConstructorFunctions]),
    cure_utils:debug("BEAM generation - Record definitions: ~p~n", [RecordDefinitions]),
    cure_utils:debug("BEAM generation - Exports: ~p~n", [State#codegen_state.exports]),

    % Extract FSM functions and flatten them
    FSMFunctions = lists:flatten([maps:get(functions, FSM, []) || FSM <- FSMDefinitions]),

    % Combine all functions: regular functions, FSM functions, and constructor functions
    AllFunctions = RegularFunctions ++ FSMFunctions ++ ConstructorFunctions,
    cure_utils:debug("BEAM generation - Total functions: ~p~n", [length(AllFunctions)]),

    Module = #{
        name => State#codegen_state.module_name,
        exports => State#codegen_state.exports,
        functions => AllFunctions,
        record_definitions => RecordDefinitions,
        fsm_definitions => FSMDefinitions,
        imported_functions => State#codegen_state.imported_functions,
        attributes => generate_module_attributes(State),
        optimization_level => State#codegen_state.optimization_level
    },

    % Debug: Show first few constructor functions to verify their format
    ConstructorSample = lists:sublist(ConstructorFunctions, 3),
    cure_utils:debug("Sample constructor functions: ~p~n", [ConstructorSample]),

    {ok, Module}.

generate_module_attributes(State) ->
    BaseAttributes = [
        {vsn, [erlang:unique_integer()]},
        {compile_info, [{optimization_level, State#codegen_state.optimization_level}]}
    ],

    % Add FSM registration attributes
    FSMDefinitions = [FSM || {fsm, FSM} <- State#codegen_state.functions],
    FSMAttributes =
        case FSMDefinitions of
            [] ->
                [];
            _ ->
                FSMNames = [maps:get(name, FSM) || FSM <- FSMDefinitions],
                [{fsm_types, FSMNames}]
        end,

    % Add debug info if requested (default to true for now)
    DebugAttributes = [{debug_info, true}],

    BaseAttributes ++ FSMAttributes ++ DebugAttributes.

%% Extract exports from constructor functions
extract_constructor_exports(ConstructorFunctions) ->
    lists:map(
        fun({function, _Line, Name, Arity, _Clauses}) ->
            {Name, Arity}
        end,
        ConstructorFunctions
    ).

%% Convert exports for new AST format
convert_exports(ExportList, Items) ->
    case ExportList of
        all ->
            extract_all_functions(Items);
        {export_list, Exports, _Location} ->
            convert_export_specs(Exports);
        Exports when is_list(Exports) ->
            % Handle plain list of export_spec tuples
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
extract_all_functions(
    [{erlang_function_def, Name, Params, _ReturnType, _Constraint, _ErlangBody, _Location} | Rest],
    Acc
) ->
    Arity = length(Params),
    extract_all_functions(Rest, [{Name, Arity} | Acc]);
%% Handle full function_def record format
extract_all_functions(
    [#function_def{name = Name, params = Params, is_private = IsPrivate} | Rest], Acc
) ->
    Arity = length(Params),
    case IsPrivate of
        true ->
            % Skip private functions from exports
            extract_all_functions(Rest, Acc);
        false ->
            % Include public functions in exports
            extract_all_functions(Rest, [{Name, Arity} | Acc])
    end;
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
process_imports([], State) ->
    {ok, State};
process_imports([{import_def, Module, Imports, _Location} | Rest], State) ->
    cure_utils:debug("Processing import ~p with items ~p~n", [Module, Imports]),
    case resolve_and_load_module(Module, Imports, State) of
        {ok, NewState} ->
            cure_utils:debug("Successfully imported ~p~n", [Module]),
            process_imports(Rest, NewState);
        {error, Reason} ->
            cure_utils:debug("Warning: Failed to import ~p: ~p~n", [Module, Reason]),
            % Continue with other imports
            process_imports(Rest, State)
    end;
process_imports([_ | Rest], State) ->
    process_imports(Rest, State).

%% Resolve and load a module for import
resolve_and_load_module(Module, Imports, State) ->
    case find_module_file(Module) of
        {ok, ModuleFile} ->
            case compile_and_extract_functions(ModuleFile, Module, Imports, State) of
                {ok, ImportedFunctions, NewState} ->
                    % Add imported functions to the state
                    CurrentImports = State#codegen_state.imported_functions,
                    UpdatedImports = maps:merge(CurrentImports, ImportedFunctions),
                    FinalState = NewState#codegen_state{imported_functions = UpdatedImports},
                    {ok, FinalState};
                {error, Reason} ->
                    {error, {compilation_failed, Module, Reason}}
            end;
        {error, Reason} ->
            {error, {module_not_found, Module, Reason}}
    end.

%% Find module file based on module name
%% Converts module names to file paths using generic conventions:
%% - Foo.Bar -> lib/foo/bar.cure or src/foo/bar.cure
%% - Foo -> lib/foo.cure or src/foo.cure
%% - MyModule -> lib/mymodule.cure or src/mymodule.cure
find_module_file(Module) ->
    ModuleStr = atom_to_list(Module),
    % Convert module name to file path components
    PathComponents = string:tokens(ModuleStr, "."),
    find_module_in_search_paths(PathComponents).

%% Search for module file in standard directories
find_module_in_search_paths(PathComponents) ->
    % Convert module path to file path (e.g., ["Std", "List"] -> "std/list.cure")
    RelativePath = string:join([string:to_lower(P) || P <- PathComponents], "/") ++ ".cure",
    SearchPaths = ["lib/", "src/", ""],
    find_in_paths(RelativePath, SearchPaths).

find_in_paths(_RelativePath, []) ->
    {error, {file_not_found, _RelativePath}};
find_in_paths(RelativePath, [SearchPath | Rest]) ->
    FullPath = SearchPath ++ RelativePath,
    case filelib:is_file(FullPath) of
        true -> {ok, FullPath};
        false -> find_in_paths(RelativePath, Rest)
    end.

%% Compile module and extract requested functions
compile_and_extract_functions(ModuleFile, Module, Imports, State) ->
    case cure_lexer:tokenize_file(ModuleFile) of
        {ok, Tokens} ->
            case cure_parser:parse(Tokens) of
                {ok, AST} ->
                    case extract_functions_from_ast(AST, Module, Imports) of
                        {ok, Functions} ->
                            {ok, Functions, State};
                        {error, Reason} ->
                            {error, {function_extraction_failed, Reason}}
                    end;
                {error, ParseError} ->
                    {error, {parse_error, ParseError}}
            end;
        {error, LexError} ->
            {error, {lex_error, LexError}}
    end.

%% Extract functions from parsed AST based on import specifications
extract_functions_from_ast(AST, Module, all) ->
    % Import all exported functions
    case find_exported_functions(AST, Module) of
        {ok, Functions} -> {ok, Functions};
        {error, Reason} -> {error, Reason}
    end;
extract_functions_from_ast(AST, Module, Imports) when is_list(Imports) ->
    % Import specific functions
    case find_exported_functions(AST, Module) of
        {ok, AllFunctions} ->
            RequestedFunctions = filter_requested_functions(AllFunctions, Imports),
            {ok, RequestedFunctions};
        {error, Reason} ->
            {error, Reason}
    end.

%% Find all exported functions in an AST
find_exported_functions(AST, Module) ->
    case AST of
        [#module_def{items = Items, exports = Exports}] ->
            extract_exported_function_bodies(Items, Module, Exports);
        Items when is_list(Items) ->
            % List of items without module wrapper
            extract_all_function_bodies(Items, Module);
        _ ->
            {error, {unsupported_ast_format, AST}}
    end.

%% Extract function bodies for all functions
extract_all_function_bodies(Items, Module) ->
    Functions = extract_function_bodies(Items, Module, []),
    {ok, Functions}.

%% Extract function bodies for exported functions only
extract_exported_function_bodies(Items, Module, Exports) ->
    AllFunctions = extract_function_bodies(Items, Module, []),
    ExportedFunctions = filter_by_exports(AllFunctions, Exports),
    {ok, ExportedFunctions}.

%% Extract function bodies from items
extract_function_bodies([], _Module, Acc) ->
    maps:from_list(lists:reverse(Acc));
extract_function_bodies(
    [#function_def{name = Name, params = Params, body = Body} | Rest], Module, Acc
) ->
    Arity = length(Params),
    FunctionKey = {Name, Arity},
    FunctionData = #{
        name => Name, arity => Arity, module => Module, params => Params, body => Body
    },
    extract_function_bodies(Rest, Module, [{FunctionKey, FunctionData} | Acc]);
extract_function_bodies([_ | Rest], Module, Acc) ->
    % Skip non-function items
    extract_function_bodies(Rest, Module, Acc).

%% Filter functions by export list
filter_by_exports(AllFunctions, []) ->
    % No exports specified, return all
    AllFunctions;
filter_by_exports(AllFunctions, Exports) ->
    ExportSet = export_list_to_set(Exports),
    maps:filter(fun(Key, _Value) -> sets:is_element(Key, ExportSet) end, AllFunctions).

%% Convert export list to set for efficient lookup
export_list_to_set(Exports) ->
    ExportTuples = lists:map(fun export_to_tuple/1, Exports),
    sets:from_list(ExportTuples).

export_to_tuple(#export_spec{name = Name, arity = Arity}) ->
    {Name, Arity};
export_to_tuple({Name, Arity}) ->
    {Name, Arity}.

%% Filter functions based on import specifications
filter_requested_functions(AllFunctions, Imports) ->
    RequestedKeys = import_list_to_keys(Imports),
    maps:filter(fun(Key, _Value) -> lists:member(Key, RequestedKeys) end, AllFunctions).

%% Convert import list to function keys
import_list_to_keys(Imports) ->
    lists:map(fun import_to_key/1, Imports).

import_to_key(#function_import{name = Name, arity = Arity}) ->
    {Name, Arity};
import_to_key({function_import, Name, Arity, _Location}) ->
    {Name, Arity};
import_to_key(Name) when is_atom(Name) ->
    % For plain atoms, we can't determine arity - this is a limitation
    % We'll need to match by name only during resolution
    {Name, any}.

%% Compile individual items (for program compilation)
compile_item(#module_def{} = Module, Options) ->
    compile_module(Module, Options);
compile_item(#function_def{} = Function, Options) ->
    compile_function(Function, Options);
% NOTE: {module_def, ...} tuple pattern is already handled by compile_module/2
% which is called from the clause above
compile_item(Item, _Options) ->
    {error, {unsupported_item, Item}}.

%% ============================================================================
%% BEAM File Generation
%% ============================================================================

-doc """
Generates a BEAM bytecode file from a compiled Cure module.

This function converts the internal compiled module representation to
standard Erlang abstract forms, then uses the Erlang compiler to produce
a BEAM bytecode file compatible with the Erlang Virtual Machine.

## Arguments
- `Module` - Compiled module data (map with functions, exports, etc.)
- `OutputPath` - File path where BEAM file should be written

## Returns
- `{ok, {ModuleName, OutputPath}}` - Successfully generated BEAM file
- `{error, Reason}` - Generation error details

## Example
```erlang
{ok, CompiledModule} = cure_codegen:compile_module(ModuleAST),
{ok, {MyModule, "MyModule.beam"}} = 
    cure_codegen:generate_beam_file(CompiledModule, "MyModule.beam").
```

## Process Steps
1. **Form Conversion**: Convert internal representation to Erlang forms
2. **Erlang Compilation**: Use Erlang compiler to generate bytecode
3. **File Writing**: Write binary BEAM data to specified path
4. **Error Handling**: Provide detailed errors at each step

## BEAM Compatibility
Generated BEAM files are fully compatible with:
- Standard Erlang/OTP runtime
- Elixir and other BEAM languages
- BEAM development and debugging tools
- Hot code reloading and distribution

## Error Types
- `{write_failed, Reason}` - File system errors
- `{compile_failed, Errors, Warnings}` - Erlang compiler errors
- Form conversion errors from convert_to_erlang_forms/1
""".
generate_beam_file(Module, OutputPath) ->
    case convert_to_erlang_forms(Module) of
        {ok, Forms} ->
            % Debug: Print record definitions
            RecordForms = [F || F = {attribute, _, record, _} <- Forms],
            io:format(standard_error, "~n=== RECORD DEFINITIONS ===~n", []),
            lists:foreach(fun(F) -> io:format(standard_error, "~p~n", [F]) end, RecordForms),
            io:format(standard_error, "=== END RECORDS ===~n~n", []),
            % The on_load attribute must be preserved - ensure it's not optimized out
            case
                compile:forms(Forms, [
                    binary,
                    return_errors,
                    return_warnings,
                    no_auto_import,
                    nowarn_undefined_function,
                    debug_info
                ])
            of
                {ok, ModuleName, Binary, _Warnings} ->
                    case file:write_file(OutputPath, Binary) of
                        ok -> {ok, {ModuleName, OutputPath}};
                        {error, Reason} -> {error, {write_failed, Reason}}
                    end;
                {ok, ModuleName, Binary} ->
                    case file:write_file(OutputPath, Binary) of
                        ok -> {ok, {ModuleName, OutputPath}};
                        {error, Reason} -> {error, {write_failed, Reason}}
                    end;
                {error, Errors, Warnings} ->
                    cure_utils:debug("Erlang compile errors: ~p~n", [Errors]),
                    cure_utils:debug("Erlang compile warnings: ~p~n", [Warnings]),
                    {error, {compile_failed, Errors, Warnings}}
            end;
        {error, Reason} ->
            {error, Reason}
    end.

%% Extract function exports from mixed function types (maps and Erlang forms)
extract_function_exports(Functions) ->
    extract_function_exports(Functions, []).

extract_function_exports([], Acc) ->
    lists:reverse(Acc);
extract_function_exports([F | Rest], Acc) ->
    case extract_single_function_export(F) of
        {ok, Export} ->
            extract_function_exports(Rest, [Export | Acc]);
        skip ->
            extract_function_exports(Rest, Acc)
    end.

%% Extract export info from a single function (map or Erlang abstract form)
extract_single_function_export(F) when is_map(F) ->
    case maps:is_key(name, F) andalso maps:is_key(arity, F) of
        true ->
            {ok, {maps:get(name, F), maps:get(arity, F)}};
        false ->
            skip
    end;
extract_single_function_export({function, _Line, Name, Arity, _Clauses}) ->
    % Erlang abstract form from union constructors
    {ok, {Name, Arity}};
extract_single_function_export(_) ->
    skip.

%% Extract typeclass constraints from where clause
extract_typeclass_constraints(undefined) ->
    [];
extract_typeclass_constraints(#where_clause{constraints = Constraints}) ->
    Constraints;
extract_typeclass_constraints(_) ->
    [].

%% Try to resolve typeclass method call to instance implementation
%% Returns: {ok, ResolvedFunction} | not_typeclass
try_resolve_typeclass_method(Function, Args, State) ->
    % Check if we have any typeclass constraints
    case State#codegen_state.typeclass_constraints of
        [] ->
            not_typeclass;
        Constraints ->
            % Check if Function is a simple identifier that matches a typeclass method
            case Function of
                #identifier_expr{name = MethodName} ->
                    % First check if this is actually a method in any of our constraints
                    case is_typeclass_method(MethodName, Constraints) of
                        false ->
                            % Not a typeclass method in our constraints
                            not_typeclass;
                        true ->
                            % Try to find which typeclass provides this method
                            case find_typeclass_for_method(MethodName, Constraints, Args, State) of
                                {ok, local, InstanceMethodName} ->
                                    % Local instance - use direct call
                                    ResolvedFunction = #identifier_expr{
                                        name = InstanceMethodName,
                                        location = undefined
                                    },
                                    {ok, ResolvedFunction};
                                {ok, InstanceModule, InstanceMethodName} ->
                                    % External instance - create module-qualified call
                                    ResolvedFunction = #binary_op_expr{
                                        op = '.',
                                        left = #identifier_expr{
                                            name = InstanceModule, location = undefined
                                        },
                                        right = #identifier_expr{
                                            name = InstanceMethodName, location = undefined
                                        },
                                        location = undefined
                                    },
                                    {ok, ResolvedFunction};
                                not_found ->
                                    not_typeclass
                            end
                    end;
                _ ->
                    % Not a simple identifier, can't be a typeclass method call
                    not_typeclass
            end
    end.

%% Check if a method name is defined in any of the typeclass constraints
is_typeclass_method(_MethodName, []) ->
    false;
is_typeclass_method(MethodName, [#typeclass_constraint{typeclass = TypeclassName} | Rest]) ->
    % Check if this typeclass defines the method
    % For now, we assume 'show' is in Show, 'eq' is in Eq, etc.
    % TODO: Look up actual typeclass definitions
    KnownMethods =
        case TypeclassName of
            'Show' -> [show];
            'Eq' -> [eq, ne];
            'Ord' -> [compare, lt, le, gt, ge];
            _ -> []
        end,
    case lists:member(MethodName, KnownMethods) of
        true -> true;
        false -> is_typeclass_method(MethodName, Rest)
    end;
is_typeclass_method(MethodName, [_ | Rest]) ->
    is_typeclass_method(MethodName, Rest).

%% Find which typeclass provides the method and resolve to instance implementation
find_typeclass_for_method(_MethodName, [], _Args, _State) ->
    not_found;
find_typeclass_for_method(MethodName, [Constraint | Rest], Args, State) ->
    % Extract typeclass and type from constraint
    case Constraint of
        #typeclass_constraint{typeclass = TypeclassName, type_args = [_TypeArg]} ->
            % Infer the concrete type from the argument
            case infer_type_from_arg(Args, State) of
                {ok, ConcreteType} ->
                    % Generate the instance method name
                    % Format: Show_Int_show (typeclass_codegen uses TypeclassName_TypeName_MethodName)
                    TypeclassStr = atom_to_list(TypeclassName),
                    TypeNameStr = type_to_string(ConcreteType),
                    MethodNameStr = atom_to_list(MethodName),
                    InstanceMethodName = list_to_atom(
                        TypeclassStr ++ "_" ++ TypeNameStr ++ "_" ++ MethodNameStr
                    ),
                    % For now, assume all instances are local (in the same module)
                    % TODO: Support cross-module instance lookup
                    {ok, local, InstanceMethodName};
                unknown ->
                    % Can't infer type, try next constraint
                    find_typeclass_for_method(MethodName, Rest, Args, State)
            end;
        _ ->
            find_typeclass_for_method(MethodName, Rest, Args, State)
    end.

%% Infer concrete type from the first argument
infer_type_from_arg([], _State) ->
    unknown;
infer_type_from_arg([FirstArg | _], _State) ->
    % Simple type inference based on literal values
    case FirstArg of
        #literal_expr{value = Value} ->
            case Value of
                V when is_integer(V) -> {ok, 'Int'};
                V when is_float(V) -> {ok, 'Float'};
                V when is_binary(V) -> {ok, 'String'};
                V when is_boolean(V) -> {ok, 'Bool'};
                _ -> unknown
            end;
        _ ->
            % For complex expressions, we'd need full type inference
            % For now, default to Int
            {ok, 'Int'}
    end.

%% Convert type to string for mangled name
type_to_string('Int') -> "Int";
type_to_string('Float') -> "Float";
type_to_string('String') -> "String";
type_to_string('Bool') -> "Bool";
type_to_string(Type) when is_atom(Type) -> atom_to_list(Type);
type_to_string(_) -> "Unknown".

%% Convert internal representation to Erlang abstract forms
convert_to_erlang_forms(Module) ->
    try
        % Handle both compiled modules (maps) and standalone functions
        {ModuleName, RawExports, Functions, RecordDefinitions, FSMDefinitions, ImportedFunctions,
            Attributes} =
            case Module of
                % Case 1: It's a proper module map
                #{name := Name, exports := ModuleExports, functions := Funcs} = ModuleMap ->
                    ModuleFSMs = maps:get(fsm_definitions, ModuleMap, []),
                    ModuleRecords = maps:get(record_definitions, ModuleMap, []),
                    ModuleImports = maps:get(imported_functions, ModuleMap, #{}),
                    ModuleAttrs = maps:get(attributes, ModuleMap, []),
                    {Name, ModuleExports, Funcs, ModuleRecords, ModuleFSMs, ModuleImports,
                        ModuleAttrs};
                % Case 2: It's a standalone function wrapped in a tuple
                {function, FunctionMap} when is_map(FunctionMap) ->
                    FuncName = maps:get(name, FunctionMap),
                    FuncArity = maps:get(arity, FunctionMap),
                    DefaultModuleName = test_module,
                    DefaultExports = [{FuncName, FuncArity}],
                    {DefaultModuleName, DefaultExports, [FunctionMap], [], [], #{}, []};
                % Case 3: It's a map that looks like a function
                #{name := Name, arity := Arity} = FunctionMap ->
                    DefaultModuleName = test_module,
                    DefaultExports = [{Name, Arity}],
                    {DefaultModuleName, DefaultExports, [FunctionMap], [], [], #{}, []};
                % Case 4: Legacy format - try to extract what we can
                _ ->
                    DefaultModuleName = test_module,
                    {DefaultModuleName, [], [], [], [], #{}, []}
            end,
        % Auto-generate exports from functions if no exports specified
        % For BEAM generation, we need to include ALL functions (exported and local)
        % The export list only controls external visibility
        AllFunctionExports = extract_function_exports(Functions),
        cure_utils:debug("RawExports: ~p~n", [RawExports]),
        cure_utils:debug("AllFunctionExports: ~p~n", [AllFunctionExports]),

        % Extract exports from FSM functions (they are always public)
        FSMFunctionExports = lists:flatten([
            extract_function_exports(maps:get(functions, FSM, []))
         || FSM <- FSMDefinitions
        ]),
        cure_utils:debug("FSMFunctionExports: ~p~n", [FSMFunctionExports]),

        Exports =
            case RawExports of
                [] ->
                    % No explicit exports - export all functions including FSM functions
                    AllFunctionExports ++ FSMFunctionExports;
                _ ->
                    % Use explicit exports but always add FSM functions
                    RawExports ++ FSMFunctionExports
            end,

        % Add register_fsms to exports if FSMs are present (required for on_load)
        ExportsWithRegistration =
            case FSMDefinitions of
                [] -> Exports;
                _ -> Exports ++ [{register_fsms, 0}]
            end,

        % Add module and export attributes
        cure_utils:debug("[EXPORTS] Module ~p exports: ~p~n", [ModuleName, ExportsWithRegistration]),
        BaseAttributes = [
            {attribute, 1, module, ModuleName},
            {attribute, 2, export, ExportsWithRegistration},
            % Import Nat constructors from cure_std
            {attribute, 3, import, {cure_std, [{'Zero', 0}, {'Succ', 1}, {'Pred', 1}]}}
        ],

        % Add compile attributes (include FSM header if FSMs present)
        CompileAttrs =
            case FSMDefinitions of
                [] ->
                    [];
                _ ->
                    [
                        {attribute, 3, file, {"cure_fsm_runtime.hrl", 1}},
                        {attribute, 3, record,
                            {fsm_definition, [
                                {record_field, 3, {atom, 3, name}},
                                {record_field, 3, {atom, 3, states}},
                                {record_field, 3, {atom, 3, initial_state}},
                                {record_field, 3, {atom, 3, initial_payload}},
                                {record_field, 3, {atom, 3, transitions}},
                                {record_field, 3, {atom, 3, timeouts}}
                            ]}}
                    ]
            end,

        % Add record definitions as attributes
        RecordForms = convert_record_definitions_to_forms(
            RecordDefinitions,
            3 + length(CompileAttrs)
        ),

        % Add custom attributes (including FSM types)
        AttributeForms = convert_attributes_to_forms(
            Attributes,
            3 + length(CompileAttrs) + length(RecordForms)
        ),

        % NOTE: on_load hook disabled for FSM registration due to ETS table ownership issues
        % The on_load process is temporary and the ETS table gets deleted when it exits
        % Users should call ModuleName:register_fsms() explicitly at application startup
        % or in their main() function before using FSMs
        LoadHook = [],

        % Set current module name for function reference generation
        put(current_module_name, ModuleName),

        % Create or clear ETS table for compilation context
        TableName = cure_codegen_context,
        case ets:info(TableName) of
            undefined ->
                ets:new(TableName, [named_table, public, set]);
            _ ->
                ets:delete_all_objects(TableName)
        end,

        % Store imported functions in ETS for pattern body conversion
        ets:insert(TableName, {imported_functions_map, ImportedFunctions}),

        % Store local functions in ETS for identifier resolution
        LocalFunctions = extract_local_functions_map(Functions),
        ets:insert(TableName, {local_functions_map, LocalFunctions}),

        % Convert functions to forms with imported functions for import resolution
        FunctionForms = convert_functions_to_forms(
            Functions,
            4 + length(CompileAttrs) + length(RecordForms) + length(AttributeForms) +
                length(LoadHook),
            ModuleName,
            ImportedFunctions
        ),

        % Add FSM registration function if needed
        FSMRegisterFunc =
            case FSMDefinitions of
                [] ->
                    [];
                _ ->
                    [
                        generate_fsm_registration_function(
                            FSMDefinitions,
                            4 + length(CompileAttrs) + length(RecordForms) + length(AttributeForms) +
                                length(LoadHook) +
                                length(FunctionForms)
                        )
                    ]
            end,

        Forms =
            BaseAttributes ++ CompileAttrs ++ RecordForms ++ AttributeForms ++ LoadHook ++
                FunctionForms ++
                FSMRegisterFunc,

        % Debug: Show a sample of the generated forms
        cure_utils:debug("Generated ~p forms total~n", [length(Forms)]),
        cure_utils:debug("[FORMS] Total forms: ~p~n", [length(Forms)]),
        cure_utils:debug("[FORMS] Function forms: ~p~n", [length(FunctionForms)]),
        cure_utils:debug("[FORMS] Functions in FunctionForms:~n"),
        lists:foreach(
            fun
                ({function, _, Name, Arity, _}) ->
                    cure_utils:debug("  Function: ~p/~p~n", [Name, Arity]);
                (_) ->
                    ok
            end,
            FunctionForms
        ),
        cure_utils:debug("[FORMS] Functions in final Forms:~n"),
        lists:foreach(
            fun
                ({function, _, Name, Arity, _}) ->
                    cure_utils:debug("  Final function: ~p/~p~n", [Name, Arity]);
                (_) ->
                    ok
            end,
            Forms
        ),
        AttributeSample = lists:sublist(Forms, 5),
        cure_utils:debug("First 5 forms: ~p~n", [AttributeSample]),

        % Find constructor functions in the forms
        ConstructorForms = [
            F
         || {function, _, Name, _, _} = F <- Forms,
            lists:member(Name, ['Ok', 'Error', 'Some', 'None', 'Lt', 'Eq', 'Gt'])
        ],
        cure_utils:debug("Constructor forms found: ~p~n", [length(ConstructorForms)]),
        if
            length(ConstructorForms) > 0 ->
                cure_utils:debug("Sample constructor form: ~p~n", [hd(ConstructorForms)]);
            true ->
                ok
        end,

        % Save forms to file for debugging
        file:write_file("/tmp/cure_forms.erl", io_lib:format("~p.~n", [Forms])),
        {ok, Forms}
    catch
        error:Reason:Stack ->
            {error, {form_conversion_failed, Reason, Stack}}
    end.

% %% Convert compiled functions to Erlang forms
% convert_functions_to_forms(Functions, LineStart) ->
%     % Extract local functions map for context
%     LocalFunctions = extract_local_functions_map(Functions),
%     convert_functions_to_forms(Functions, LineStart, [], undefined, LocalFunctions).

%% Convert compiled functions to Erlang forms with module name and imports
convert_functions_to_forms(Functions, LineStart, ModuleName, ImportedFunctions) ->
    % Extract local functions map for context
    LocalFunctions = extract_local_functions_map(Functions),
    cure_utils:debug("[LOCAL_FUNCS] Module ~p has local functions: ~p~n", [
        ModuleName, maps:to_list(LocalFunctions)
    ]),
    cure_utils:debug("[IMPORTED_FUNCS] Module ~p has imported functions: ~p~n", [
        ModuleName, maps:to_list(ImportedFunctions)
    ]),
    convert_functions_to_forms(
        Functions, LineStart, [], ModuleName, LocalFunctions, ImportedFunctions
    ).

convert_functions_to_forms([], _Line, Acc, _ModuleName, _LocalFunctions, _ImportedFunctions) ->
    cure_utils:debug("[CONVERT] Converted ~p functions to forms~n", [length(Acc)]),
    lists:reverse(Acc);
convert_functions_to_forms(
    [Function | RestFunctions], Line, Acc, ModuleName, LocalFunctions, ImportedFunctions
) ->
    case convert_function_to_form(Function, Line, ModuleName, LocalFunctions, ImportedFunctions) of
        {ok, Form, NextLine} ->
            convert_functions_to_forms(
                RestFunctions, NextLine, [Form | Acc], ModuleName, LocalFunctions, ImportedFunctions
            );
        {error, Reason} ->
            % Skip invalid functions but log the error
            cure_utils:debug("[CONVERT] Failed to convert function to form: ~p~n", [Reason]),
            convert_functions_to_forms(
                RestFunctions, Line + 1, Acc, ModuleName, LocalFunctions, ImportedFunctions
            )
    end.

%% Extract function names and arities from module items (before compilation)
%% This is used to populate the ETS table early so pattern compilation can work
extract_function_names_from_items(Items) ->
    lists:foldl(
        fun(Item, Acc) ->
            case Item of
                #function_def{name = Name, clauses = Clauses, params = _Params} when
                    Clauses =/= undefined, length(Clauses) > 0
                ->
                    % Multi-clause function - get arity from first clause
                    FirstClause = hd(Clauses),
                    Arity = length(FirstClause#function_clause.params),
                    maps:put(Name, Arity, Acc);
                #function_def{name = Name, params = Params} when Params =/= undefined ->
                    % Single-clause function
                    Arity = length(Params),
                    maps:put(Name, Arity, Acc);
                {function_def, Name, Params, _Body, _Location} ->
                    Arity = length(Params),
                    maps:put(Name, Arity, Acc);
                _ ->
                    % Skip non-function items
                    Acc
            end
        end,
        #{},
        Items
    ).

%% Extract local functions map for context
extract_local_functions_map(Functions) ->
    cure_utils:debug("[EXTRACT_MAP] Extracting from ~p functions~n", [length(Functions)]),
    lists:foreach(
        fun(F) ->
            case F of
                _ when is_map(F) ->
                    cure_utils:debug("  Map: ~p/~p~n", [
                        maps:get(name, F, undefined), maps:get(arity, F, undefined)
                    ]);
                {function, _, N, A, _} ->
                    cure_utils:debug("  Form: ~p/~p~n", [N, A]);
                _ ->
                    cure_utils:debug("  Other: ~p~n", [element(1, F)])
            end
        end,
        Functions
    ),
    Result = lists:foldl(
        fun(Function, Acc) ->
            case Function of
                _ when is_map(Function) ->
                    case
                        {maps:get(name, Function, undefined), maps:get(arity, Function, undefined)}
                    of
                        {undefined, _} ->
                            cure_utils:debug("    Skip: undefined name~n"),
                            Acc;
                        {_, undefined} ->
                            cure_utils:debug("    Skip: undefined arity~n"),
                            Acc;
                        {Name, Arity} ->
                            NewAcc = maps:put(Name, Arity, Acc),
                            cure_utils:debug("    Added: ~p/~p, Acc now: ~p~n", [
                                Name, Arity, maps:to_list(NewAcc)
                            ]),
                            NewAcc
                    end;
                {function, _Line, Name, Arity, _Clauses} ->
                    % Constructor function
                    NewAcc = maps:put(Name, Arity, Acc),
                    cure_utils:debug("    Added form: ~p/~p~n", [Name, Arity]),
                    NewAcc;
                _ ->
                    cure_utils:debug("    Skip: not a map or form~n"),
                    Acc
            end
        end,
        #{},
        Functions
    ),
    cure_utils:debug("[EXTRACT_MAP] Final result: ~p~n", [maps:to_list(Result)]),
    Result.

%% Convert a single function to Erlang abstract form (backward compatibility)
% convert_function_to_form(Function, Line) ->
%     convert_function_to_form(Function, Line, undefined, #{}).

%% Convert a single function to Erlang abstract form with module context
convert_function_to_form(Function, Line, ModuleName, LocalFunctions, ImportedFunctions) ->
    % Check if this is already an Erlang abstract form (from union type constructors)
    case Function of
        {function, _FormLine, Name, Arity, Clauses} ->
            % Already in Erlang abstract form, just update the line number
            cure_utils:debug("Converting constructor function ~p/~p~n", [Name, Arity]),
            UpdatedForm = {function, Line, Name, Arity, Clauses},
            {ok, UpdatedForm, Line + 1};
        _ when is_map(Function) ->
            % Normal function that needs compilation
            FuncName = maps:get(name, Function, unknown),
            FuncArity = maps:get(arity, Function, unknown),
            cure_utils:debug("Converting regular function ~p/~p~n", [FuncName, FuncArity]),
            case ModuleName of
                undefined ->
                    % No module context, use old function
                    case cure_beam_compiler:compile_function_to_erlang(Function, Line) of
                        {ok, FunctionForm, NextLine} ->
                            {ok, FunctionForm, NextLine};
                        {error, Reason} ->
                            {error, Reason}
                    end;
                _ ->
                    % Use new function with module context and imported functions
                    case
                        cure_beam_compiler:compile_function_to_erlang(
                            Function, Line, ModuleName, LocalFunctions, ImportedFunctions
                        )
                    of
                        {ok, FunctionForm, NextLine} ->
                            {ok, FunctionForm, NextLine};
                        {error, Reason} ->
                            {error, Reason}
                    end
            end;
        _ ->
            cure_utils:debug("Unknown function format: ~p~n", [Function]),
            {error, {unknown_function_format, Function}}
    end.

%% Convert record definitions to Erlang attribute forms
convert_record_definitions_to_forms(RecordDefinitions, StartLine) ->
    convert_record_definitions_to_forms(RecordDefinitions, StartLine, []).

convert_record_definitions_to_forms([], _Line, Acc) ->
    lists:reverse(Acc);
convert_record_definitions_to_forms([{record, RecordName, Fields} | Rest], Line, Acc) ->
    % Create record attribute: -record(RecordName, [Fields]).
    Form = {attribute, Line, record, {RecordName, Fields}},
    convert_record_definitions_to_forms(Rest, Line + 1, [Form | Acc]);
convert_record_definitions_to_forms([_ | Rest], Line, Acc) ->
    % Skip invalid record definitions
    convert_record_definitions_to_forms(Rest, Line, Acc).

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

    % Debug logging for on_load execution
    DebugLog =
        {call, Line, {remote, Line, {atom, Line, io}, {atom, Line, format}}, [
            {string, Line, "[FSM] Registering FSMs from on_load hook...~n"}
        ]},

    % Ensure cure_fsm_runtime module is loaded before registration
    EnsureLoaded =
        {call, Line, {remote, Line, {atom, Line, code}, {atom, Line, ensure_loaded}}, [
            {atom, Line, cure_fsm_runtime}
        ]},

    % Generate registration calls for each FSM with debug logging
    RegistrationCalls = lists:flatmap(
        fun(FSMName) ->
            DefFuncName = list_to_atom(atom_to_list(FSMName) ++ "_definition"),
            [
                % Debug log before registration
                {call, Line, {remote, Line, {atom, Line, io}, {atom, Line, format}}, [
                    {string, Line, "[FSM] Registering FSM type: ~p~n"},
                    {cons, Line, {atom, Line, FSMName}, {nil, Line}}
                ]},
                % Actual registration call
                {call, Line,
                    {remote, Line, {atom, Line, cure_fsm_runtime}, {atom, Line, register_fsm_type}},
                    [
                        {atom, Line, FSMName}, {call, Line, {atom, Line, DefFuncName}, []}
                    ]},
                % Debug log after registration
                {call, Line, {remote, Line, {atom, Line, io}, {atom, Line, format}}, [
                    {string, Line, "[FSM] Registered types: ~p~n"},
                    {cons, Line,
                        {call, Line,
                            {remote, Line, {atom, Line, cure_fsm_runtime},
                                {atom, Line, get_registered_fsm_types}},
                            []},
                        {nil, Line}}
                ]}
            ]
        end,
        FSMNames
    ),

    % Create function body: debug + ensure_loaded + registration calls + ok return
    Body = [DebugLog, EnsureLoaded | RegistrationCalls] ++ [{atom, Line, ok}],

    % Create the register_fsms/0 function
    {
        function,
        Line,
        register_fsms,
        0,
        [{clause, Line, [], [], Body}]
    }.

-doc """
Writes a compiled Cure module to a BEAM file.

This is a convenience function that calls generate_beam_file/2 to convert
a compiled module to BEAM bytecode and write it to the specified path.

## Arguments
- `Module` - Compiled module data from compile_module/1,2
- `OutputPath` - File path where BEAM file should be written

## Returns
- `{ok, {ModuleName, OutputPath}}` - Successfully written BEAM file
- `{error, Reason}` - File writing or compilation error

## Example
```erlang
{ok, CompiledModule} = cure_codegen:compile_module(AST),
{ok, {MyModule, "MyModule.beam"}} = 
    cure_codegen:write_beam_module(CompiledModule, "MyModule.beam"),

%% Load and test the module
code:load_file(MyModule),
MyModule:function_name(args).
```

## Use Cases
- Final step in Cure compilation pipeline
- Integration with build systems and tools
- Deployment of Cure modules to BEAM environments
- Testing and development workflows
""".
write_beam_module(Module, OutputPath) ->
    generate_beam_file(Module, OutputPath).

%% ============================================================================
%% Pattern Compilation with Guard Support
%% ============================================================================

%% Convert match clause patterns to Erlang case clauses
compile_patterns_to_case_clauses(Patterns, State) ->
    compile_patterns_to_case_clauses_impl(Patterns, [], State).

compile_patterns_to_case_clauses_impl([], Acc, State) ->
    {lists:reverse(Acc), State};
compile_patterns_to_case_clauses_impl(
    [#match_clause{pattern = Pattern, guard = Guard, body = Body, location = Location} | Rest],
    Acc,
    State
) ->
    % Check if this is a Succ pattern that needs special handling
    {ErlangPattern, ExtraGuards, BodyPrologue} =
        case Pattern of
            #constructor_pattern{name = 'Succ', args = [#identifier_pattern{name = VarName}]} ->
                % Succ(pred) pattern: match any positive integer, bind pred = value - 1
                Line = get_line_from_location(Location),
                TempVar = list_to_atom("_Succ_" ++ atom_to_list(VarName)),
                Pat = {var, Line, TempVar},
                % Guard: TempVar > 0
                GuardExpr = {op, Line, '>', {var, Line, TempVar}, {integer, Line, 0}},
                % Body prologue: VarName = TempVar - 1
                Prologue =
                    {match, Line, {var, Line, VarName},
                        {op, Line, '-', {var, Line, TempVar}, {integer, Line, 1}}},
                {Pat, [GuardExpr], [Prologue]};
            _ ->
                {convert_pattern_to_erlang_form(Pattern, Location), [], []}
        end,

    % Convert user-provided guard to Erlang guard form if present
    UserGuards =
        case Guard of
            undefined -> [];
            _ -> [convert_guard_to_erlang_form(Guard, Location)]
        end,

    % Combine extra guards from pattern with user guards
    ErlangGuard =
        case ExtraGuards ++ UserGuards of
            [] -> [];
            Guards -> [Guards]
        end,

    % For complex expressions, we need to create a more sophisticated approach
    % Instead of trying to convert complex expressions directly to Erlang forms,
    % we'll create a function call that executes the compiled instructions

    % First, try simple conversions for basic cases
    BodyLine = get_line_from_location(Location),
    BaseErlangBody =
        case Body of
            #literal_expr{value = Value} ->
                [compile_value_to_erlang_form(Value, Location)];
            #identifier_expr{name = Name} ->
                % Could be a variable reference or a nullary constructor
                % Check if it's uppercase (constructor) or lowercase (variable/function)
                case atom_to_list(Name) of
                    [First | _Rest] when First >= $A, First =< $Z ->
                        % Uppercase - nullary constructor, generate call
                        [{call, BodyLine, {atom, BodyLine, Name}, []}];
                    _ ->
                        % Lowercase - variable reference or function reference
                        case is_function_name(Name) of
                            true ->
                                % Known function - use atom
                                [{atom, BodyLine, Name}];
                            false ->
                                % Unknown lowercase - treat as variable
                                [{var, BodyLine, Name}]
                        end
                end;
            _ ->
                % For complex expressions, convert them to proper Erlang form
                case convert_complex_body_to_erlang(Body, Location) of
                    {ok, ErlangForm} ->
                        [ErlangForm];
                    error ->
                        % Fallback - this should not happen with proper implementation
                        [
                            {call, BodyLine,
                                {remote, BodyLine, {atom, BodyLine, erlang},
                                    {atom, BodyLine, error}},
                                [{atom, BodyLine, unimplemented_body_expression}]}
                        ]
                end
        end,

    % Prepend body prologue (for Succ pattern variable bindings)
    ErlangBody = BodyPrologue ++ BaseErlangBody,

    % Create Erlang case clause
    CaseClause =
        {clause, get_line_from_location(Location), [ErlangPattern], ErlangGuard, ErlangBody},

    compile_patterns_to_case_clauses_impl(Rest, [CaseClause | Acc], State);
compile_patterns_to_case_clauses_impl([Pattern | Rest], Acc, State) ->
    % Handle non-match_clause patterns (legacy)
    Location = {location, 1, 1, undefined},
    ErlangPattern = convert_pattern_to_erlang_form(Pattern, Location),
    ErlangBody = [compile_value_to_erlang_form(default_value_for_pattern(Pattern), Location)],
    CaseClause = {clause, 1, [ErlangPattern], [], ErlangBody},
    compile_patterns_to_case_clauses_impl(Rest, [CaseClause | Acc], State).

%% Convert Cure pattern to Erlang pattern form
convert_pattern_to_erlang_form(#literal_pattern{value = Value, location = Location}, _) ->
    compile_value_to_erlang_form(Value, Location);
convert_pattern_to_erlang_form(#wildcard_pattern{location = Location}, _) ->
    {var, get_line_from_location(Location), '_'};
convert_pattern_to_erlang_form(#identifier_pattern{name = Name, location = Location}, _) ->
    {var, get_line_from_location(Location), Name};
convert_pattern_to_erlang_form(
    #list_pattern{elements = Elements, tail = Tail, location = Location}, _
) ->
    Line = get_line_from_location(Location),
    convert_list_pattern_to_erlang_form(Elements, Tail, Line);
convert_pattern_to_erlang_form(#tuple_pattern{elements = Elements, location = Location}, _) ->
    Line = get_line_from_location(Location),
    ErlangElements = [convert_pattern_to_erlang_form(Element, Location) || Element <- Elements],
    {tuple, Line, ErlangElements};
convert_pattern_to_erlang_form(
    #constructor_pattern{name = ConstructorName, args = Args, location = Location}, _
) ->
    Line = get_line_from_location(Location),
    convert_constructor_pattern_to_erlang_form(ConstructorName, Args, Line, Location);
convert_pattern_to_erlang_form(
    #record_pattern{name = RecordName, fields = Fields, location = Location}, _
) ->
    Line = get_line_from_location(Location),
    convert_record_pattern_to_erlang_form(RecordName, Fields, Line, Location);
convert_pattern_to_erlang_form(_Pattern, Location) ->
    % Fallback for unsupported patterns
    {var, get_line_from_location(Location), '_'}.

%% Convert list pattern to Erlang pattern form
convert_list_pattern_to_erlang_form([], undefined, Line) ->
    % Empty list pattern []
    {nil, Line};
convert_list_pattern_to_erlang_form(Elements, undefined, Line) ->
    % Fixed-length list pattern [a, b, c]
    convert_fixed_list_to_erlang(Elements, Line);
convert_list_pattern_to_erlang_form(Elements, Tail, Line) ->
    % Head-tail pattern [h | t] or [a, b | t]
    convert_cons_pattern_to_erlang(Elements, Tail, Line).

%% Convert fixed-length list to Erlang pattern [a, b, c] -> [a | [b | [c | []]]]
convert_fixed_list_to_erlang([], Line) ->
    {nil, Line};
convert_fixed_list_to_erlang([Element | RestElements], Line) ->
    HeadPattern = convert_pattern_to_erlang_form(Element, {location, Line, 1, undefined}),
    TailPattern = convert_fixed_list_to_erlang(RestElements, Line),
    {cons, Line, HeadPattern, TailPattern}.

%% Convert head-tail pattern to Erlang cons pattern [h1, h2 | t] -> [h1 | [h2 | t]]
convert_cons_pattern_to_erlang([], Tail, Line) ->
    % No head elements, just the tail
    convert_pattern_to_erlang_form(Tail, {location, Line, 1, undefined});
convert_cons_pattern_to_erlang([HeadElement | RestElements], Tail, Line) ->
    HeadPattern = convert_pattern_to_erlang_form(HeadElement, {location, Line, 1, undefined}),
    TailPattern = convert_cons_pattern_to_erlang(RestElements, Tail, Line),
    {cons, Line, HeadPattern, TailPattern}.

%% Convert constructor patterns to Erlang tuple patterns
%% None -> {none}, Some(value) -> {some, Value}, Ok(value) -> {ok, Value}, etc.
%% Special handling for Nat constructors which use integer representation
convert_constructor_pattern_to_erlang_form(ConstructorName, Args, Line, Location) ->
    % Special case for Nat constructors (Zero and Succ)
    % These use integer representation in cure_std, not tagged tuples
    case ConstructorName of
        'Zero' ->
            % Zero matches integer 0
            {integer, Line, 0};
        'Succ' ->
            case Args of
                [#identifier_pattern{name = VarName}] ->
                    % Succ(pred) pattern:
                    % Match any positive integer and bind the variable to (value - 1)
                    % We use a fresh variable for the actual value, then bind pred = value - 1
                    % Pattern: _SuccN when _SuccN > 0
                    % Body will have: VarName = _SuccN - 1
                    % For now, just match a variable - we'll need special handling in the clause
                    {var, Line, VarName};
                _ ->
                    % Malformed Succ pattern or complex nested pattern
                    % Match any integer (will need guards to ensure > 0)
                    {var, Line, '_SuccValue'}
            end;
        _ ->
            % Standard constructor pattern (for Option, Result, etc.)
            % Convert constructor name to lowercase atom for Erlang representation
            ErlangConstructorName = normalize_constructor_name(ConstructorName),
            ConstructorAtom = {atom, Line, ErlangConstructorName},

            case Args of
                undefined ->
                    % Constructor with no arguments: None -> {none}
                    {tuple, Line, [ConstructorAtom]};
                [] ->
                    % Constructor with empty argument list: None() -> {none}
                    {tuple, Line, [ConstructorAtom]};
                [SingleArg] ->
                    % Constructor with single argument: Some(value) -> {some, Value}
                    ArgPattern = convert_pattern_to_erlang_form(SingleArg, Location),
                    {tuple, Line, [ConstructorAtom, ArgPattern]};
                MultipleArgs ->
                    % Constructor with multiple arguments: Constructor(a, b, c) -> {constructor, A, B, C}
                    ArgPatterns = [
                        convert_pattern_to_erlang_form(Arg, Location)
                     || Arg <- MultipleArgs
                    ],
                    {tuple, Line, [ConstructorAtom | ArgPatterns]}
            end
    end.

%% Convert record patterns to Erlang record patterns
%% Person{name: n, age: a} -> #'Person'{name = N, age = A} (record pattern)
convert_record_pattern_to_erlang_form(RecordName, Fields, Line, Location) ->
    % Convert field patterns to Erlang record_field forms
    ErlangFields = [convert_field_pattern_to_erlang_form(Field, Location) || Field <- Fields],
    % Generate Erlang record pattern: #RecordName{field1 = Pattern1, field2 = Pattern2, ...}
    {record, Line, RecordName, ErlangFields}.

%% Get record field order from ETS table (stored during type checking)
get_record_field_order(RecordName) ->
    TableName = cure_codegen_context,
    cure_utils:debug("[FIELD_ORDER] Looking up fields for record: ~p~n", [RecordName]),
    case ets:info(TableName) of
        undefined ->
            cure_utils:debug("[FIELD_ORDER] ETS table not found~n"),
            not_found;
        _ ->
            case ets:lookup(TableName, {record_fields, RecordName}) of
                [{_, FieldOrder}] ->
                    cure_utils:debug("[FIELD_ORDER] Found field order: ~p~n", [FieldOrder]),
                    {ok, FieldOrder};
                [] ->
                    cure_utils:debug("[FIELD_ORDER] No field order found~n"),
                    not_found
            end
    end.

%% Create ordered field patterns based on record definition order
create_ordered_field_patterns(Fields, FieldOrder, Location) ->
    % Create a map from field name to pattern
    FieldMap = maps:from_list([
        {Field#field_pattern.name, Field#field_pattern.pattern}
     || Field <- Fields
    ]),
    % Generate patterns in the order defined by the record
    [
        begin
            Pattern = maps:get(FieldName, FieldMap, #wildcard_pattern{location = Location}),
            convert_pattern_to_erlang_form(Pattern, Location)
        end
     || FieldName <- FieldOrder
    ].

%% Convert field patterns within records
convert_field_pattern_to_erlang_form(
    #field_pattern{name = FieldName, pattern = Pattern, location = _}, Location
) ->
    ErlangPattern = convert_pattern_to_erlang_form(Pattern, Location),
    Line = get_line_from_location(Location),
    {record_field, Line, {atom, Line, FieldName}, ErlangPattern}.

%% Normalize constructor names to lowercase atoms for consistent Erlang representation
normalize_constructor_name('None') ->
    none;
normalize_constructor_name('Some') ->
    some;
normalize_constructor_name('Ok') ->
    ok;
normalize_constructor_name('Error') ->
    error;
normalize_constructor_name('Lt') ->
    lt;
normalize_constructor_name('Eq') ->
    eq;
normalize_constructor_name('Gt') ->
    gt;
normalize_constructor_name(Name) when is_atom(Name) ->
    % Convert atom to string, lowercase it, and convert back to atom
    NameStr = atom_to_list(Name),
    LowerStr = string:to_lower(NameStr),
    list_to_atom(LowerStr);
normalize_constructor_name(Name) ->
    Name.

%% Convert guard to Erlang guard form
convert_guard_to_erlang_form(Guard, Location) ->
    % For now, simple guard conversion - would need full guard compiler integration
    Line = get_line_from_location(Location),
    case Guard of
        #binary_op_expr{op = Op, left = Left, right = Right} ->
            LeftForm = convert_guard_expr_to_form(Left, Line),
            RightForm = convert_guard_expr_to_form(Right, Line),
            % Note: <> is NOT allowed in guards for concatenation
            % It's only supported for pattern matching (handled elsewhere)
            % Also need to convert Cure operators to Erlang equivalents
            ErlangOp =
                case Op of
                    '<>' ->
                        % Cannot use <> in guards - it's not a valid Erlang guard BIF
                        % This should have been caught during type checking
                        throw({invalid_guard_expression, '<>', Line});
                    'and' ->
                        % Convert 'and' to 'andalso' for proper short-circuit evaluation in guards
                        'andalso';
                    'or' ->
                        % Convert 'or' to 'orelse' for proper short-circuit evaluation in guards
                        'orelse';
                    '<=' ->
                        % Convert '<=' to Erlang's '=<'
                        '=<';
                    '%' ->
                        % Convert '%' to 'rem' for Erlang modulo in guards
                        'rem';
                    _ ->
                        Op
                end,
            {op, Line, ErlangOp, LeftForm, RightForm};
        _ ->
            % Default to always true guard
            {atom, Line, true}
    end.

convert_guard_expr_to_form(#identifier_expr{name = Name}, Line) ->
    {var, Line, Name};
convert_guard_expr_to_form(#literal_expr{value = Value}, Line) ->
    compile_value_to_erlang_form(Value, {location, Line, 1, undefined});
convert_guard_expr_to_form(#binary_op_expr{op = Op, left = Left, right = Right}, Line) ->
    % Recursively handle nested binary operations in guards
    LeftForm = convert_guard_expr_to_form(Left, Line),
    RightForm = convert_guard_expr_to_form(Right, Line),
    % Convert operators to Erlang equivalents
    ErlangOp =
        case Op of
            'and' -> 'andalso';
            'or' -> 'orelse';
            '<=' -> '=<';
            '%' -> 'rem';
            '<>' -> throw({invalid_guard_expression, '<>', Line});
            _ -> Op
        end,
    {op, Line, ErlangOp, LeftForm, RightForm};
convert_guard_expr_to_form(#unary_op_expr{op = Op, operand = Operand}, Line) ->
    % Handle unary operations in guards (e.g., -273.15)
    OperandForm = convert_guard_expr_to_form(Operand, Line),
    {op, Line, Op, OperandForm};
convert_guard_expr_to_form(_, Line) ->
    {atom, Line, true}.

%% Compile value to Erlang form
compile_value_to_erlang_form(Value, Location) ->
    Line = get_line_from_location(Location),
    compile_value_to_erlang_form_impl(Value, Line).

compile_value_to_erlang_form_impl(Value, Line) when is_integer(Value) ->
    {integer, Line, Value};
compile_value_to_erlang_form_impl(Value, Line) when is_float(Value) ->
    {float, Line, Value};
compile_value_to_erlang_form_impl(Value, Line) when is_atom(Value) ->
    {atom, Line, Value};
compile_value_to_erlang_form_impl(Value, Line) when is_binary(Value) ->
    % Binary = String (UTF-8 binary)
    % Generate a binary form instead of string
    {bin, Line, [{bin_element, Line, {string, Line, binary_to_list(Value)}, default, [utf8]}]};
compile_value_to_erlang_form_impl(Value, Line) when is_list(Value) ->
    % Check if it's a charlist (printable Unicode list) or a regular list
    case io_lib:printable_unicode_list(Value) of
        true ->
            % Charlist - compile as Erlang list of integers
            compile_list_to_erlang_form(Value, Line);
        false ->
            % Regular list
            compile_list_to_erlang_form(Value, Line)
    end;
compile_value_to_erlang_form_impl(Value, Line) ->
    {tuple, Line, [{atom, Line, complex_value}, {term, Line, Value}]}.

compile_list_to_erlang_form([], Line) ->
    {nil, Line};
compile_list_to_erlang_form([H | T], Line) ->
    HeadForm = compile_value_to_erlang_form_impl(H, Line),
    TailForm = compile_list_to_erlang_form(T, Line),
    {cons, Line, HeadForm, TailForm}.

%% Convert body expression to Erlang form for pattern matching
convert_body_expression_to_erlang(#literal_expr{value = Value}, Location) ->
    {ok, compile_value_to_erlang_form(Value, Location)};
convert_body_expression_to_erlang(#identifier_expr{name = Name}, Location) ->
    {ok, {var, get_line_from_location(Location), Name}};
convert_body_expression_to_erlang(#binary_op_expr{op = Op, left = Left, right = Right}, Location) ->
    Line = get_line_from_location(Location),
    case convert_body_expression_to_erlang(Left, Location) of
        {ok, LeftForm} ->
            case convert_body_expression_to_erlang(Right, Location) of
                {ok, RightForm} ->
                    % Desugar <> operator to cure_string_native:concat/2
                    OpForm =
                        case Op of
                            '<>' ->
                                {call, Line,
                                    {remote, Line, {atom, Line, cure_string_native},
                                        {atom, Line, concat}},
                                    [LeftForm, RightForm]};
                            _ ->
                                {op, Line, Op, LeftForm, RightForm}
                        end,
                    {ok, OpForm};
                error ->
                    error
            end;
        error ->
            error
    end;
convert_body_expression_to_erlang(_, _) ->
    error.

%% Convert complex body expressions to Erlang form for pattern matching
%% This handles more complex expressions that the simple convert_body_expression_to_erlang cannot
convert_complex_body_to_erlang(#literal_expr{value = Value}, Location) ->
    {ok, compile_value_to_erlang_form(Value, Location)};
convert_complex_body_to_erlang(#identifier_expr{name = Name}, Location) ->
    Line = get_line_from_location(Location),
    % In match expression bodies, identifiers can be:
    % 1. Variables bound in the pattern (should use {var, ...})
    % 2. Function/constructor references (should use {atom, ...})
    %
    % Strategy:
    % - If uppercase -> atom (constructor reference - will be called)
    % - If lowercase and in known functions -> atom (function reference)
    % - If lowercase and not known -> var (parameter or let-binding)
    %
    % NOTE: For standalone nullary constructors like Lt, they should ideally be parsed
    % as function_call_expr with no args. But they come as identifier_expr, so we
    % handle them by generating calls at the identifier level ONLY when standalone.
    % However, we can't distinguish standalone from function-position here.
    % Solution: Always treat uppercase as atoms, and generate the call wrapper
    % at the function_call_expr level when we see a call with 0 args to uppercase function.
    case atom_to_list(Name) of
        [First | _Rest] when First >= $A, First =< $Z ->
            % Uppercase name - constructor reference as atom
            {ok, {atom, Line, Name}};
        _ ->
            % Lowercase identifier
            case is_function_name(Name) of
                true ->
                    % Known function - use atom
                    {ok, {atom, Line, Name}};
                false ->
                    % Unknown lowercase - treat as variable
                    {ok, {var, Line, Name}}
            end
    end;
convert_complex_body_to_erlang(#binary_op_expr{op = Op, left = Left, right = Right}, Location) ->
    Line = get_line_from_location(Location),
    cure_utils:debug("Converting binary op ~p at line ~p~n", [Op, Line]),
    case
        {
            convert_complex_body_to_erlang(Left, Location),
            convert_complex_body_to_erlang(Right, Location)
        }
    of
        {{ok, LeftForm}, {ok, RightForm}} ->
            % Desugar <> operator to cure_string_native:concat/2
            BinOpForm =
                case Op of
                    '<>' ->
                        {call, Line,
                            {remote, Line, {atom, Line, cure_string_native}, {atom, Line, concat}},
                            [LeftForm, RightForm]};
                    _ ->
                        {op, Line, Op, LeftForm, RightForm}
                end,
            cure_utils:debug("Generated binary op form: ~p~n", [BinOpForm]),
            {ok, BinOpForm};
        _ ->
            error
    end;
convert_complex_body_to_erlang(#function_call_expr{function = Function, args = Args}, Location) ->
    Line = get_line_from_location(Location),
    cure_utils:debug("Converting function call ~p with args ~p~n", [Function, Args]),
    case convert_complex_body_to_erlang(Function, Location) of
        {ok, FunctionForm} ->
            cure_utils:debug("Function form: ~p~n", [FunctionForm]),
            case convert_complex_args_to_erlang(Args, Location) of
                {ok, ArgForms} ->
                    % Check if this is a call to an imported function and convert to remote call if needed
                    FinalFunctionForm =
                        case FunctionForm of
                            {atom, _, FuncName} ->
                                % Check if this function is imported
                                ImportResult = get_imported_function_info(
                                    FuncName, length(ArgForms)
                                ),
                                case ImportResult of
                                    {ok, ModuleName} ->
                                        % Generate remote call
                                        {remote, Line, {atom, Line, ModuleName},
                                            {atom, Line, FuncName}};
                                    not_found ->
                                        % Keep as local call
                                        FunctionForm
                                end;
                            _ ->
                                FunctionForm
                        end,
                    CallForm = {call, Line, FinalFunctionForm, ArgForms},
                    cure_utils:debug("Generated call form: ~p~n", [CallForm]),
                    {ok, CallForm};
                error ->
                    error
            end;
        error ->
            error
    end;
convert_complex_body_to_erlang(#let_expr{bindings = Bindings, body = Body}, Location) ->
    Line = get_line_from_location(Location),
    case convert_complex_bindings_to_erlang(Bindings, Location) of
        {ok, BindingForms} ->
            case convert_complex_body_to_erlang(Body, Location) of
                {ok, BodyForm} ->
                    % Create a block with bindings followed by body
                    {ok, {block, Line, BindingForms ++ [BodyForm]}};
                error ->
                    error
            end;
        error ->
            error
    end;
convert_complex_body_to_erlang(#list_expr{elements = Elements}, Location) ->
    Line = get_line_from_location(Location),
    case convert_complex_args_to_erlang(Elements, Location) of
        {ok, ElementForms} ->
            ListForm = build_list_form(ElementForms, Line),
            {ok, ListForm};
        error ->
            error
    end;
convert_complex_body_to_erlang(#tuple_expr{elements = Elements}, Location) ->
    Line = get_line_from_location(Location),
    case convert_complex_args_to_erlang(Elements, Location) of
        {ok, ElementForms} ->
            {ok, {tuple, Line, ElementForms}};
        error ->
            error
    end;
convert_complex_body_to_erlang(#cons_expr{elements = Elements, tail = Tail}, Location) ->
    Line = get_line_from_location(Location),
    cure_utils:debug("Converting cons expr with elements ~p and tail ~p~n", [Elements, Tail]),
    case convert_complex_args_to_erlang(Elements, Location) of
        {ok, ElementForms} ->
            case convert_complex_body_to_erlang(Tail, Location) of
                {ok, TailForm} ->
                    % Build cons structure: [E1, E2, ... | Tail] -> [E1 | [E2 | ... | Tail]]
                    ConsForm = build_cons_form(ElementForms, TailForm, Line),
                    cure_utils:debug("Generated cons form: ~p~n", [ConsForm]),
                    {ok, ConsForm};
                error ->
                    error
            end;
        error ->
            error
    end;
convert_complex_body_to_erlang(#match_expr{expr = Expr, patterns = Patterns}, Location) ->
    Line = get_line_from_location(Location),
    cure_utils:debug("Converting match expr with ~p patterns~n", [length(Patterns)]),
    case convert_complex_body_to_erlang(Expr, Location) of
        {ok, ExprForm} ->
            case convert_match_patterns_to_erlang(Patterns, Location) of
                {ok, ClauseForms} ->
                    CaseForm = {'case', Line, ExprForm, ClauseForms},
                    cure_utils:debug("Generated case form: ~p~n", [CaseForm]),
                    {ok, CaseForm};
                error ->
                    error
            end;
        error ->
            error
    end;
convert_complex_body_to_erlang(
    #record_update_expr{name = RecordName, base = BaseExpr, fields = Fields}, Location
) ->
    Line = get_line_from_location(Location),
    cure_utils:debug("Converting record update for ~p with ~p fields~n", [
        RecordName, length(Fields)
    ]),
    case convert_complex_body_to_erlang(BaseExpr, Location) of
        {ok, BaseForm} ->
            case convert_record_field_values_to_erlang(Fields, Location) of
                {ok, FieldForms} ->
                    % Build record update: BaseRecord#RecordName{field1=Val1, field2=Val2, ...}
                    % In Erlang abstract form: {record, Line, BaseRecord, RecordName, FieldAssignments}
                    FieldNames = [Field#field_expr.name || Field <- Fields],
                    FieldAssignments = lists:zipwith(
                        fun(FieldName, FieldForm) ->
                            {record_field, Line, {atom, Line, FieldName}, FieldForm}
                        end,
                        FieldNames,
                        FieldForms
                    ),
                    RecordUpdateForm = {record, Line, BaseForm, RecordName, FieldAssignments},
                    cure_utils:debug("[RECORD_UPDATE] Generated for ~p: ~p~n", [
                        RecordName, RecordUpdateForm
                    ]),
                    cure_utils:debug("[RECORD_UPDATE] BaseForm: ~p~n", [BaseForm]),
                    cure_utils:debug("[RECORD_UPDATE] FieldAssignments: ~p~n", [FieldAssignments]),
                    {ok, RecordUpdateForm};
                error ->
                    error
            end;
        error ->
            error
    end;
convert_complex_body_to_erlang(_, _) ->
    error.

%% Helper function to convert argument lists
convert_complex_args_to_erlang([], _Location) ->
    {ok, []};
convert_complex_args_to_erlang([Arg | Rest], Location) ->
    case convert_complex_body_to_erlang(Arg, Location) of
        {ok, ArgForm} ->
            case convert_complex_args_to_erlang(Rest, Location) of
                {ok, RestForms} ->
                    {ok, [ArgForm | RestForms]};
                error ->
                    error
            end;
        error ->
            error
    end.

%% Helper function to convert let bindings
convert_complex_bindings_to_erlang([], _Location) ->
    {ok, []};
convert_complex_bindings_to_erlang([#binding{pattern = Pattern, value = Value} | Rest], Location) ->
    Line = get_line_from_location(Location),
    case convert_complex_body_to_erlang(Value, Location) of
        {ok, ValueForm} ->
            % Convert pattern to proper match form
            PatternForm =
                case Pattern of
                    #identifier_pattern{name = Name} -> {var, Line, Name};
                    _ -> convert_pattern_to_erlang_form(Pattern, Location)
                end,
            BindingForm = {match, Line, PatternForm, ValueForm},
            case convert_complex_bindings_to_erlang(Rest, Location) of
                {ok, RestForms} ->
                    {ok, [BindingForm | RestForms]};
                error ->
                    error
            end;
        error ->
            error
    end;
convert_complex_bindings_to_erlang([_ | Rest], Location) ->
    % Skip unsupported binding types for now
    convert_complex_bindings_to_erlang(Rest, Location).

%% Helper function to convert record field values
convert_record_field_values_to_erlang([], _Location) ->
    {ok, []};
convert_record_field_values_to_erlang([#field_expr{value = Value} | Rest], Location) ->
    case convert_complex_body_to_erlang(Value, Location) of
        {ok, ValueForm} ->
            case convert_record_field_values_to_erlang(Rest, Location) of
                {ok, RestForms} ->
                    {ok, [ValueForm | RestForms]};
                error ->
                    error
            end;
        error ->
            error
    end;
convert_record_field_values_to_erlang([_ | Rest], Location) ->
    % Skip unsupported field types
    convert_record_field_values_to_erlang(Rest, Location).

%% Get imported function info (module name) for a given function name and arity
%% Checks ETS table for imported functions stored during conversion
get_imported_function_info(FuncName, Arity) ->
    TableName = cure_codegen_context,
    ImportedFunctions =
        case ets:info(TableName) of
            undefined ->
                undefined;
            _ ->
                case ets:lookup(TableName, imported_functions_map) of
                    [{imported_functions_map, Map}] -> Map;
                    [] -> undefined
                end
        end,
    case ImportedFunctions of
        undefined ->
            not_found;
        ImportedFunctions when is_map(ImportedFunctions) ->
            % Try {Name, Arity} tuple first
            LookupResult = maps:get({FuncName, Arity}, ImportedFunctions, undefined),
            case LookupResult of
                undefined ->
                    % Try plain name
                    case maps:get(FuncName, ImportedFunctions, undefined) of
                        undefined ->
                            not_found;
                        ImportInfo when is_map(ImportInfo) ->
                            case maps:get(module, ImportInfo, undefined) of
                                undefined ->
                                    not_found;
                                ModName ->
                                    {ok, ModName}
                            end;
                        _ ->
                            not_found
                    end;
                ImportInfo when is_map(ImportInfo) ->
                    case maps:get(module, ImportInfo, undefined) of
                        undefined ->
                            not_found;
                        ModName ->
                            {ok, ModName}
                    end;
                _ ->
                    not_found
            end;
        _ ->
            not_found
    end.

%% Check if a name is a constructor or known function
%% Used in match expression bodies to distinguish function references from variables
% is_constructor_or_known_function(Name) ->
%     % Check if it's a known constructor or common function
%     is_function_name(Name).

%% Check if a name is a known function (constructor or regular function)
%% This determines whether identifier should be treated as atom (function call) or var (variable reference)
%% Uses dynamic lookup in local_functions_map and imported_functions_map stored in ETS
is_function_name(Name) ->
    % Check uppercase constructors first (type constructors like Ok, Error, Some, None, Lt, Eq, Gt)
    case atom_to_list(Name) of
        [First | _] when First >= $A, First =< $Z ->
            % Uppercase - likely a constructor
            true;
        _ ->
            % Lowercase - check if it's a local or imported function
            TableName = cure_codegen_context,
            {LocalFunctions, ImportedFunctions} =
                case ets:info(TableName) of
                    undefined ->
                        {undefined, undefined};
                    _ ->
                        Local =
                            case ets:lookup(TableName, local_functions_map) of
                                [{local_functions_map, LMap}] -> LMap;
                                [] -> undefined
                            end,
                        Imported =
                            case ets:lookup(TableName, imported_functions_map) of
                                [{imported_functions_map, IMap}] -> IMap;
                                [] -> undefined
                            end,
                        {Local, Imported}
                end,

            cure_utils:debug("[is_function_name] Checking ~p~n", [Name]),
            cure_utils:debug("  LocalFunctions: ~p~n", [LocalFunctions]),
            cure_utils:debug("  ImportedFunctions: ~p~n", [ImportedFunctions]),

            % Check if it exists as a local function (any arity)
            IsLocal =
                case LocalFunctions of
                    undefined ->
                        false;
                    LocalMap when is_map(LocalMap) ->
                        % Check if Name is a key in the map (Name -> Arity)
                        Result = maps:is_key(Name, LocalMap),
                        cure_utils:debug("  IsLocal for ~p: ~p~n", [Name, Result]),
                        Result;
                    _ ->
                        false
                end,

            % Check if it exists as an imported function
            IsImported =
                case ImportedFunctions of
                    undefined ->
                        false;
                    ImportMap when is_map(ImportMap) ->
                        % Check both {Name, _} keys and plain Name keys
                        ImportResult =
                            maps:is_key(Name, ImportMap) orelse
                                lists:any(
                                    fun
                                        ({K, _}) when is_tuple(K) ->
                                            element(1, K) =:= Name;
                                        (_) ->
                                            false
                                    end,
                                    maps:to_list(ImportMap)
                                ),
                        cure_utils:debug("  IsImported for ~p: ~p~n", [Name, ImportResult]),
                        ImportResult;
                    _ ->
                        false
                end,

            FinalResult = IsLocal orelse IsImported,
            cure_utils:debug("  Final result for ~p: ~p~n", [Name, FinalResult]),
            FinalResult
    end.

%% Helper function to build proper list forms
build_list_form([], Line) ->
    {nil, Line};
build_list_form([Element | Rest], Line) ->
    {cons, Line, Element, build_list_form(Rest, Line)}.

%% Helper function to build proper cons forms
%% Builds [E1, E2, ... | Tail] -> [E1 | [E2 | ... | Tail]]
build_cons_form([], TailForm, _Line) ->
    TailForm;
build_cons_form([Element | RestElements], TailForm, Line) ->
    RestConsForm = build_cons_form(RestElements, TailForm, Line),
    {cons, Line, Element, RestConsForm}.

%% Helper function to convert match patterns to Erlang case clauses
convert_match_patterns_to_erlang([], _Location) ->
    {ok, []};
convert_match_patterns_to_erlang(
    [#match_clause{pattern = Pattern, guard = Guard, body = Body} | Rest], Location
) ->
    Line = get_line_from_location(Location),
    ErlangPattern = convert_pattern_to_erlang_form(Pattern, Location),

    % Convert guard to Erlang guard form if present
    ErlangGuard =
        case Guard of
            undefined -> [];
            _ -> [convert_guard_to_erlang_form(Guard, Location)]
        end,

    % Convert body to Erlang form
    case convert_complex_body_to_erlang(Body, Location) of
        {ok, BodyForm} ->
            CaseClause = {clause, Line, [ErlangPattern], ErlangGuard, [BodyForm]},
            case convert_match_patterns_to_erlang(Rest, Location) of
                {ok, RestClauses} ->
                    {ok, [CaseClause | RestClauses]};
                error ->
                    error
            end;
        error ->
            error
    end;
convert_match_patterns_to_erlang([_ | Rest], Location) ->
    % Skip unsupported pattern types and continue
    convert_match_patterns_to_erlang(Rest, Location).

%% Get default values for patterns and bodies
default_value_for_pattern(#literal_pattern{value = Value}) -> Value;
default_value_for_pattern(_) -> undefined.

% default_value_for_body(#literal_expr{value = Value}) -> Value;
% default_value_for_body(_) -> ok.

%% Get line number from location
% get_line_from_location({location, Line, _Col, _File}, _Default) when is_integer(Line) -> Line;
% get_line_from_location(_, Default) -> Default.

%% Get line number from location (single argument version)
get_line_from_location({location, Line, _Col, _File}) when is_integer(Line) -> Line;
get_line_from_location(_) -> 1.

%% Compile match patterns with guards
% compile_match_patterns(Patterns, Location, State) ->
%     compile_match_patterns_impl(Patterns, [], Location, State).
%
% compile_match_patterns_impl([], Acc, _Location, State) ->
%     {lists:flatten(lists:reverse(Acc)), State};
% compile_match_patterns_impl([Pattern | Rest], Acc, Location, State) ->
%     case compile_match_pattern(Pattern, Location, State) of
%         {ok, Instructions, NewState} ->
%             compile_match_patterns_impl(Rest, [Instructions | Acc], Location, NewState);
%         {error, Reason} ->
%             {error, Reason}
%     end.

%% Compile a single match pattern with optional guard
% compile_match_pattern(
%     #match_clause{pattern = Pattern, guard = Guard, body = Body, location = Location},
%     _OverrideLocation,
%     State
% ) ->
%     % Generate labels for control flow
%     {FailLabel, State1} = new_label(State),
%     {SuccessLabel, State2} = new_label(State1),
%
%     % Compile pattern matching
%     {PatternInstr, State3} = compile_pattern(Pattern, FailLabel, State2),
%
%     % Compile guard if present
%     case Guard of
%         undefined ->
%             % No guard, compile body directly
%             {BodyInstr, State4} = compile_expression(Body, State3),
%
%             % Assemble instructions
%             Instructions =
%                 PatternInstr ++ BodyInstr ++
%                     [
%                         #beam_instr{op = jump, args = [SuccessLabel], location = Location},
%                         #beam_instr{op = label, args = [FailLabel], location = Location},
%                         #beam_instr{op = pattern_fail, args = [], location = Location},
%                         #beam_instr{op = label, args = [SuccessLabel], location = Location}
%                     ],
%
%             {ok, Instructions, State4};
%         _ ->
%             case cure_guard_compiler:compile_guard(Guard, State3) of
%                 {ok, GuardCode, GuardState} ->
%                     GuardFailInstr = #beam_instr{
%                         op = jump_if_false,
%                         args = [FailLabel],
%                         location = Location
%                     },
%
%                     % Compile body
%                     {BodyInstr, State5} = compile_expression(Body, GuardState),
%
%                     % Assemble instructions
%                     Instructions =
%                         PatternInstr ++ GuardCode ++ [GuardFailInstr] ++ BodyInstr ++
%                             [
%                                 #beam_instr{op = jump, args = [SuccessLabel], location = Location},
%                                 #beam_instr{op = label, args = [FailLabel], location = Location},
%                                 #beam_instr{op = pattern_fail, args = [], location = Location},
%                                 #beam_instr{op = label, args = [SuccessLabel], location = Location}
%                             ],
%
%                     {ok, Instructions, State5};
%                 {error, GuardReason} ->
%                     {error, GuardReason}
%             end
%     end;
% compile_match_pattern(Pattern, Location, State) ->
%     % Handle non-clause patterns (backward compatibility)
%     {FailLabel, State1} = new_label(State),
%     {PatternInstr, State2} = compile_pattern(Pattern, FailLabel, State1),
%
%     Instructions =
%         PatternInstr ++
%             [
%                 #beam_instr{op = label, args = [FailLabel], location = Location},
%                 #beam_instr{op = pattern_fail, args = [], location = Location}
%             ],
%
%     {ok, Instructions, State2}.

%% Compile individual patterns
% compile_pattern(#literal_pattern{value = Value, location = Location}, FailLabel, State) ->
%     Instructions = [
%         #beam_instr{op = match_literal, args = [Value, FailLabel], location = Location}
%     ],
%     {Instructions, State};
% compile_pattern(#identifier_pattern{name = Name, location = Location}, _FailLabel, State) ->
%     {VarRef, State1} = new_temp_var(State),
%     NewVars = maps:put(Name, {local, VarRef}, State#codegen_state.local_vars),
%
%     Instructions = [
%         #beam_instr{op = bind_var, args = [VarRef], location = Location}
%     ],
%
%     {Instructions, State1#codegen_state{local_vars = NewVars}};
% compile_pattern(#wildcard_pattern{location = Location}, _FailLabel, State) ->
%     Instructions = [
%         #beam_instr{op = match_any, args = [], location = Location}
%     ],
%     {Instructions, State};
% compile_pattern(#tuple_pattern{elements = Elements, location = Location}, FailLabel, State) ->
%     % Match tuple structure first
%     TupleMatchInstr = #beam_instr{
%         op = match_tuple,
%         args = [length(Elements), FailLabel],
%         location = Location
%     },
%
%     % Compile element patterns
%     {ElementInstr, State1} = compile_pattern_elements(Elements, FailLabel, State),
%
%     Instructions = [TupleMatchInstr] ++ ElementInstr,
%     {Instructions, State1};
% compile_pattern(
%     #list_pattern{elements = Elements, tail = Tail, location = Location}, FailLabel, State
% ) ->
%     % Match list structure
%     ListMatchInstr = #beam_instr{
%         op = match_list,
%         args = [length(Elements), Tail =/= undefined, FailLabel],
%         location = Location
%     },
%
%     % Compile element patterns
%     {ElementInstr, State1} = compile_pattern_elements(Elements, FailLabel, State),
%
%     % Compile tail pattern if present
%     {TailInstr, State2} =
%         case Tail of
%             undefined -> {[], State1};
%             _ -> compile_pattern(Tail, FailLabel, State1)
%         end,
%
%     Instructions = [ListMatchInstr] ++ ElementInstr ++ TailInstr,
%     {Instructions, State2};
% %% Record pattern - special handling for Result/Option types
% compile_pattern(
%     #record_pattern{name = RecordName, fields = Fields, location = Location}, FailLabel, State
% ) ->
%     % Check if this is a Result/Option type that should be treated as a tagged tuple
%     case is_result_or_option_type(RecordName) of
%         true ->
%             % These are represented as simple tuples: {'Ok', Value}, {'Error', Reason}, etc.
%             % Generate tuple pattern matching instead of record matching
%             RecordMatchInstr = #beam_instr{
%                 op = match_result_tuple,
%                 args = [RecordName, length(Fields), FailLabel],
%                 location = Location
%             },
%
%             % Compile field patterns
%             {FieldInstr, State1} = compile_record_field_patterns(Fields, FailLabel, State),
%
%             Instructions = [RecordMatchInstr] ++ FieldInstr,
%             {Instructions, State1};
%         false ->
%             % Traditional record pattern for actual records
%             % In Erlang, records are represented as {RecordName, Field1, Field2, ...}
%             RecordMatchInstr = #beam_instr{
%                 op = match_tagged_tuple,
%                 args = [RecordName, length(Fields), FailLabel],
%                 location = Location
%             },
%
%             % Compile field patterns
%             {FieldInstr, State1} = compile_record_field_patterns(Fields, FailLabel, State),
%
%             Instructions = [RecordMatchInstr] ++ FieldInstr,
%             {Instructions, State1}
%     end;
% %% Constructor pattern - for Result/Option types like Ok(value), Error(reason), etc.
% compile_pattern(
%     #constructor_pattern{name = ConstructorName, args = Args, location = Location}, FailLabel, State
% ) ->
%     % Check if this is a Result/Option type (both uppercase and lowercase)
%     case is_constructor_type(ConstructorName) of
%         true ->
%             case Args of
%                 undefined ->
%                     % Constructor with no arguments (like None)
%                     ConstructorMatchInstr = #beam_instr{
%                         op = match_constructor,
%                         args = [ConstructorName, 0, FailLabel],
%                         location = Location
%                     },
%                     {[ConstructorMatchInstr], State};
%                 [] ->
%                     % Constructor with empty argument list (like None())
%                     ConstructorMatchInstr = #beam_instr{
%                         op = match_constructor,
%                         args = [ConstructorName, 0, FailLabel],
%                         location = Location
%                     },
%                     {[ConstructorMatchInstr], State};
%                 [SingleArg] ->
%                     % Constructor with single argument (like Ok(value), Error(reason))
%                     ConstructorMatchInstr = #beam_instr{
%                         op = match_constructor,
%                         args = [ConstructorName, 1, FailLabel],
%                         location = Location
%                     },
%
%                     % Compile the argument pattern
%                     {ArgInstr, State1} = compile_pattern(SingleArg, FailLabel, State),
%
%                     Instructions = [ConstructorMatchInstr] ++ ArgInstr,
%                     {Instructions, State1};
%                 _ ->
%                     % Multiple arguments - not typical for Result/Option but handle it
%                     ConstructorMatchInstr = #beam_instr{
%                         op = match_constructor,
%                         args = [ConstructorName, length(Args), FailLabel],
%                         location = Location
%                     },
%
%                     % Compile all argument patterns
%                     {ArgInstrs, State1} = compile_pattern_elements(Args, FailLabel, State),
%
%                     Instructions = [ConstructorMatchInstr] ++ ArgInstrs,
%                     {Instructions, State1}
%             end;
%         false ->
%             {error, {unknown_constructor_pattern, ConstructorName}, State}
%     end;
% compile_pattern(Pattern, _FailLabel, State) ->
%     {error, {unsupported_pattern, Pattern}, State}.

%% Compile pattern elements (for tuples and lists)
% compile_pattern_elements(Elements, FailLabel, State) ->
%     compile_pattern_elements_impl(Elements, [], FailLabel, State).
%
% %% Compile record field patterns
% compile_record_field_patterns(Fields, FailLabel, State) ->
%     compile_record_field_patterns_impl(Fields, [], FailLabel, State).
%
% compile_record_field_patterns_impl([], Acc, _FailLabel, State) ->
%     {lists:flatten(lists:reverse(Acc)), State};
% compile_record_field_patterns_impl(
%     [#field_pattern{name = _FieldName, pattern = Pattern} | Rest], Acc, FailLabel, State
% ) ->
%     % For record patterns, we assume positional field matching
%     % The field order must match the record definition
%     case compile_pattern(Pattern, FailLabel, State) of
%         {Instructions, NewState} ->
%             % Add instruction to advance to next field position
%             FieldInstr =
%                 Instructions ++ [#beam_instr{op = advance_field, args = [], location = undefined}],
%             compile_record_field_patterns_impl(Rest, [FieldInstr | Acc], FailLabel, NewState);
%         {error, Reason, ErrorState} ->
%             {error, Reason, ErrorState}
%     end.
%
% compile_pattern_elements_impl([], Acc, _FailLabel, State) ->
%     {lists:flatten(lists:reverse(Acc)), State};
% compile_pattern_elements_impl([Element | Rest], Acc, FailLabel, State) ->
%     case compile_pattern(Element, FailLabel, State) of
%         {Instructions, NewState} ->
%             compile_pattern_elements_impl(Rest, [Instructions | Acc], FailLabel, NewState);
%         {error, Reason, ErrorState} ->
%             {error, Reason, ErrorState}
%     end.

%% ============================================================================
%% Helper Functions for Pattern Compilation
%% ============================================================================

%% Check if a record name represents a Result or Option type that uses tuple representation
% is_result_or_option_type('Ok') -> true;
% is_result_or_option_type('Error') -> true;
% is_result_or_option_type('Some') -> true;
% is_result_or_option_type('None') -> true;
% is_result_or_option_type(_) -> false.
%
% %% Check if a constructor name represents a valid Result/Option constructor (both cases)
% is_constructor_type('Ok') -> true;
% is_constructor_type('Error') -> true;
% is_constructor_type('Some') -> true;
% is_constructor_type('None') -> true;
% is_constructor_type(ok) -> true;
% is_constructor_type(error) -> true;
% is_constructor_type(some) -> true;
% is_constructor_type(none) -> true;
% is_constructor_type(_) -> false.

%% ============================================================================
%% Union Type Constructor Generation
%% ============================================================================

%% Register type constructors in the state so they can be recognized during compilation
register_type_constructors(#type_def{definition = Definition}, State) ->
    case extract_union_variants(Definition) of
        {ok, Variants} ->
            % Extract constructor names and arities
            Constructors = lists:foldl(
                fun(Variant, Acc) ->
                    case extract_constructor_info(Variant) of
                        {ok, Name, Arity} ->
                            maps:put(Name, Arity, Acc);
                        {error, _} ->
                            Acc
                    end
                end,
                State#codegen_state.type_constructors,
                Variants
            ),
            State#codegen_state{type_constructors = Constructors};
        _ ->
            State
    end.

%% Generate constructor functions for union types
%% For example: type Result(T, E) = Ok(T) | Error(E)
%% Should generate: Ok/1 and Error/1 functions
generate_union_type_constructors(#type_def{name = TypeName, definition = Definition}, State) ->
    cure_utils:debug("Processing type definition ~p with definition ~p~n", [TypeName, Definition]),
    case extract_union_variants(Definition) of
        {ok, Variants} ->
            cure_utils:debug("Found union variants: ~p~n", [Variants]),
            case generate_constructor_functions(TypeName, Variants, State, []) of
                {ok, Functions, NewState} ->
                    cure_utils:debug("Generated constructor functions: ~p~n", [Functions]),
                    {ok, Functions, NewState};
                {error, Reason} ->
                    {error, Reason}
            end;
        not_a_union ->
            cure_utils:debug("~p is not a union type~n", [TypeName]),
            {no_constructors, State};
        {error, Reason} ->
            cure_utils:debug("Error extracting union variants: ~p~n", [Reason]),
            {error, Reason}
    end.

%% Extract variants from union type definition
%% Handles various AST formats for union types
extract_union_variants(#union_type{types = Types}) ->
    cure_utils:debug("Found union_type record with types: ~p~n", [Types]),
    {ok, Types};
extract_union_variants(Definition) when is_list(Definition) ->
    % Handle list of union variants
    cure_utils:debug("Found list definition: ~p~n", [Definition]),
    {ok, Definition};
extract_union_variants(Definition) ->
    cure_utils:debug("Checking if definition is union type: ~p~n", [Definition]),
    % Try to detect if this is a union type in other formats
    case is_union_type_definition(Definition) of
        {true, Variants} ->
            cure_utils:debug("Detected union type with variants: ~p~n", [Variants]),
            {ok, Variants};
        false ->
            cure_utils:debug("Not a union type~n"),
            not_a_union
    end.

%% Check if definition represents a union type
%% This handles the case where union types might be represented differently in AST
is_union_type_definition(Definition) ->
    % Look for patterns like: Ok(T) | Error(E) or Lt | Eq | Gt
    case Definition of
        % Pattern for binary union: A | B
        {union_expr, Left, Right, _Location} ->
            Variants = flatten_union_expr({union_expr, Left, Right, _Location}),
            {true, Variants};
        % Direct list of variants
        Variants when is_list(Variants) ->
            case all_are_constructors(Variants) of
                true -> {true, Variants};
                false -> false
            end;
        _ ->
            false
    end.

%% Flatten union expression like A | B | C into [A, B, C]
flatten_union_expr({union_expr, Left, Right, _}) ->
    LeftVariants = flatten_union_expr(Left),
    RightVariants = flatten_union_expr(Right),
    LeftVariants ++ RightVariants;
flatten_union_expr(Variant) ->
    [Variant].

%% Check if all items look like type constructors
all_are_constructors([]) -> true;
all_are_constructors([#primitive_type{} | Rest]) -> all_are_constructors(Rest);
all_are_constructors([#dependent_type{} | Rest]) -> all_are_constructors(Rest);
all_are_constructors([_ | _]) -> false.

%% Generate constructor functions for each variant
generate_constructor_functions(_TypeName, [], State, Acc) ->
    {ok, lists:reverse(Acc), State};
generate_constructor_functions(TypeName, [Variant | RestVariants], State, Acc) ->
    case generate_single_constructor(TypeName, Variant, State) of
        {ok, Function, NewState} ->
            generate_constructor_functions(TypeName, RestVariants, NewState, [Function | Acc]);
        {error, Reason} ->
            {error, Reason}
    end.

%% Generate a single constructor function
generate_single_constructor(_TypeName, Variant, State) ->
    case extract_constructor_info(Variant) of
        {ok, ConstructorName, Arity} ->
            % Create constructor function: ConstructorName(Args...) -> {ConstructorName, Args...}
            Function = create_constructor_function(ConstructorName, Arity, State),
            {ok, Function, State};
        {error, Reason} ->
            {error, Reason}
    end.

%% Extract constructor name and arity from variant
extract_constructor_info(#primitive_type{name = Name}) ->
    % Nullary constructor like Lt, Eq, Gt, None
    {ok, Name, 0};
extract_constructor_info(#dependent_type{
    name = Name, type_params = TypeParams, value_params = ValueParams
}) ->
    % Constructor with arguments like Ok(T), Error(E), Some(T)
    AllParams = TypeParams ++ ValueParams,
    {ok, Name, length(AllParams)};
extract_constructor_info(Variant) ->
    {error, {unsupported_variant, Variant}}.

%% Helper function to generate Erlang record field definitions from record fields
generate_erlang_record_fields(Fields) ->
    [generate_erlang_record_field(Field) || Field <- Fields].

generate_erlang_record_field(#record_field_def{
    name = FieldName, type = _Type, default_value = DefaultValue
}) ->
    % Generate Erlang record field: {record_field, Line, {atom, Line, FieldName}}
    % or {record_field, Line, {atom, Line, FieldName}, DefaultExpr} if default exists
    Line = 0,
    case DefaultValue of
        undefined ->
            {record_field, Line, {atom, Line, FieldName}};
        _ ->
            % Convert default value to Erlang form
            DefaultForm = compile_value_to_erlang_form(
                DefaultValue, {location, Line, 1, undefined}
            ),
            {record_field, Line, {atom, Line, FieldName}, DefaultForm}
    end.

%% Create constructor function as Erlang AST
create_constructor_function(ConstructorName, 0, _State) ->
    % Nullary constructor: ConstructorName() -> {ConstructorName}
    % Use consistent tuple representation for all constructors
    ErlangName = normalize_constructor_name(ConstructorName),
    Body = {tuple, 0, [{atom, 0, ErlangName}]},
    {function, 0, ConstructorName, 0, [
        {clause, 0, [], [], [Body]}
    ]};
create_constructor_function(ConstructorName, Arity, _State) when Arity > 0 ->
    % Constructor with arguments: ConstructorName(Arg1, ..., ArgN) -> {constructor_name, Arg1, ..., ArgN}
    % Generate parameter variables
    Params = [{var, 0, list_to_atom("Arg" ++ integer_to_list(I))} || I <- lists:seq(1, Arity)],
    % Create tuple with normalized constructor name and arguments
    ErlangName = normalize_constructor_name(ConstructorName),
    TupleElements = [{atom, 0, ErlangName} | Params],
    Body = {tuple, 0, TupleElements},

    {function, 0, ConstructorName, Arity, [
        {clause, 0, Params, [], [Body]}
    ]}.
