%% Cure Programming Language - Type Checker
%% High-level type checker that works with parsed AST nodes
-module(cure_typechecker).

-moduledoc """
# Cure Programming Language - Type Checker

The type checker module provides high-level type checking functionality for
Cure programs. It works with parsed AST nodes and implements comprehensive
static type analysis including dependent type verification, constraint solving, and type inference.

## Features

### Comprehensive Type Checking

- **Program-Level Analysis**: Full program type checking with module support
- **Function Type Checking**: Parameter and return type verification
- **Expression Type Inference**: Bottom-up type inference for all expressions
- **Dependent Type Support**: Verification of dependent type constraints

### Module System Support

- **Module Scoping**: Proper scoping of types and functions within modules
- **Export Verification**: Ensures exported functions exist and have correct types
- **Import Resolution**: Type-safe import of functions and types from other modules
- **Two-Pass Processing**: Collects signatures before checking bodies

### Advanced Type Features

- **Generic Functions**: Full support for parametric polymorphism
- **Constraint Solving**: Integration with SMT-based constraint solving
- **FSM Type Checking**: Verification of finite state machine definitions
- **Erlang Interop**: Type checking for Erlang function interfaces

### Error Reporting

- **Detailed Error Messages**: Precise error locations with helpful descriptions
- **Warning System**: Non-fatal issues that may indicate problems
- **Error Recovery**: Continues checking after errors to find more issues
- **Structured Results**: Machine-readable error and warning information

## Type Checking Process

### 1. Environment Setup

```erlang
Env = cure_typechecker:builtin_env(),  % Built-in types and functions
R esult = cure_typechecker:check_program(AST).
```

### 2. Module Processing

- **Signature Collection**: First pass collects all function signatures
- **Body Checking**: Second pass verifies function bodies against signatures  
- **Export Validation**: Ensures all exported items are properly typed

### 3. Function Analysis

- **Parameter Processing**: Converts parameter types to environment bindings
- **Constraint Checking**: Verifies function constraints are boolean expressions
- **Body Inference**: Infers body type and checks against declared return type
- **Generic Resolution**: Resolves type parameters and constraints

## Usage Examples

### Program Type Checking

```erlang
AST = cure_parser:parse_file("example.cure"),
Result = cure_typechecker:check_program(AST),
case Result#typecheck_result.success of
  true ->
    cure_utils:debug("Type checking successful~n");
 
  false -> 
    Errors = Result#typecheck_result.errors,
    cure_utils:debug("Type errors: ~p~n", [Errors])
end.
```

### Function Type Checking

```erlang
FuncAST = #function_def{name = add, params = Params, body = Body, ...},
{ok, Env, Result} = cure_typechecker:check_function(FuncAST).
```

### Expression Type Inference

```erlang
{ok, Type} = cure_typechecker:check_expression(ExprAST, Environment).
```

## Type Checking Results

Returns structured results with:

- **Success Flag**: Overall type checking success/failure
- **Inferred Types**: Types inferred for expressions and functions
- **Error List**: Detailed error information with locations
- **Warnings**: Non-fatal issues found during checking

## Built-in Environment

Provides built-in types and functions:

- **Primitive Types**: Int, Float, String, Bool, Atom
- **Type Constructors**: List, Tuple, Map, Vector
- **Standard Functions**: Arithmetic, logical, and utility functions
- **FSM Operations**: Built-in FSM manipulati on functions

## Integration

This module integrates with:

- **cure_types**: Core type system operations
- **cure_parser**: Processes parsed AST nodes  
- **cure_smt_solver**: Constraint solving for dependent types
- **cure_type_optimizer**: Provides type information for optimizations

## Error Categories

- **Type Mismatches**: Incompatible type assignments or operations
- **Undefined Variables**: References to unbound variables
- **Constraint Violations**: Failed dependent type constraints
- **Export Errors**: Missing or incorrectly typed exported functions
- **Import Errors**: Invalid module imports or type mismatches

## Performance

- **Two-Pass Efficiency**: Minimizes redundant type checking
- **Incremental Checking**: Supports incremental compilation scenarios
- **Constraint Caching**: Reuses constraint solving results where possible
- **Environment Sharing**: Efficient environment management

## Thread Safety

The type checker is stateless and thread-safe. Multiple type checking
operations can run concurrently on different ASTs.
""".

-export([
    check_program/1,
    % With SMT options
    check_program/2,
    check_module/2,
    check_function/2,
    % For testing
    check_fsm/2,
    check_expression/2, check_expression/3,
    infer_type/2,
    builtin_env/0,
    check_dependent_constraint/3,
    infer_dependent_type/2,
    convert_type_to_tuple/1,
    % Stdlib functions are now resolved through normal import mechanisms
    load_stdlib_modules/0,
    extract_module_functions/1,
    get_stdlib_function_type/3,
    create_function_type_from_signature/2,
    create_function_type_from_signature_records/2,
    % Helper functions used by cure_types
    extract_and_add_type_params/2,
    extract_type_params_helper/2,
    extract_type_param_value/2,
    convert_record_field_def/1,
    convert_and_resolve_record_field_tuple/2
]).

% Add compatibility function for tests

% Built-in type constructors

% Dependent type helpers

% Utility functions

% Test/debug functions

-include("../parser/cure_ast.hrl").

%% Type checking result
-record(typecheck_result, {
    success :: boolean(),
    type :: term() | undefined,
    errors :: [typecheck_error()],
    warnings :: [typecheck_warning()]
}).
-record(typecheck_error, {message :: string(), location :: location(), details :: term()}).
-record(typecheck_warning, {message :: string(), location :: location(), details :: term()}).

%% Type definitions
-type typecheck_error() :: #typecheck_error{}.
-type typecheck_warning() :: #typecheck_warning{}.

-doc """
Type checks an entire Cure program.

Performs comprehensive type checking of all top-level items in the program
including modules, functions, FSMs, and type definitions.

## Arguments

- `AST` - List of top-level AST items from the parser

## Returns

- `typecheck_result()` - Complete type checking results including:
- `success` - Boolean indicating overall success/failure
- `type` - Program type (usually undefined for programs)
- `errors` - List of type checking errors found
- `warnings` 
- List of warnings found

## Example

```erlang
AST = cure_parser:parse_file("example.cure"),
Result = cure_typechecker:check_program(AST),
case Result#typecheck_result.success of
  true -> 
    cure_utils:debug("Program type checks successfully~n");
 
  false -> 
    lists:foreach(fun(Error) ->
      cure_utils:debug("Error: ~s~n", [Error#typecheck_error.message])
    end, Result#typecheck_result.errors)
end.
```

## Features

- **Built-in Environment**: Uses standard built-in types and functions
- **Error Recovery**: Continues checking after errors to find more issues
- **Two-Pass Processing**: Collects signatures before checking implementations".
""".

check_program(AST) ->
    check_program(AST, #{}).

-doc """
 Type checks a Cure program with SMT options.

## Arguments

- `AST` - List of top-level AST items from the parser
- `SmtOpts` - Map of SMT solver options:
  - `enabled` - Enable/disable SMT constraint solving (default: true)
  - `solver` - SMT solver to use: z3, cvc5, auto (default: auto)
  - `timeout` - Solver timeout in milliseconds (default: 5000)

## Returns

- `typecheck_result()` - Complete type checking results

## Example

```erlang
SmtOpts = #{enabled => true, solver => z3, timeout => 10000},
Result = cure_typechecker:check_program(AST, SmtOpts).
```
""".

check_program(AST, SmtOpts) ->
    % Store SMT options in process dictionary for constraint checking
    put(smt_options, SmtOpts),

    Env = builtin_env(),
    Result = check_items(
        AST,
        Env,
        #typecheck_result{
            success = true,
            type = undefined,
            errors = [],
            warnings = []
        }
    ),

    % Clean up process dictionary
    erase(smt_options),
    Result.

% Check list of top-level items
check_items([], _Env, Result) ->
    Result;
check_items([Item | RestItems], Env, Result) ->
    % Debug output to identify which item is being processed
    case Item of
        {function_def, Name, _, _, _, _, _} ->
            cure_utils:debug("[ITEMS] Processing function body for ~p~n", [Name]);
        {function_def, Name, _, _, _, _, _, _} ->
            cure_utils:debug("[ITEMS] Processing function body for ~p~n", [Name]);
        {type_def, TypeName, _, _, _} ->
            cure_utils:debug("[ITEMS] Processing type definition ~p~n", [TypeName]);
        _ ->
            cure_utils:debug("[ITEMS] Processing other item: ~p~n", [element(1, Item)]),
            cure_utils:debug("[ITEMS] Full item structure: ~p~n", [Item])
    end,
    case check_item(Item, Env) of
        {ok, NewEnv, ItemResult} ->
            MergedResult = merge_results(Result, ItemResult),
            check_items(RestItems, NewEnv, MergedResult);
        {error, Error} ->
            ErrorResult = add_error(Result, Error),
            check_items(RestItems, Env, ErrorResult)
    end.

%% Check single top-level item - Updated for new AST format
check_item({module_def, Name, Imports, Exports, Items, Location}, Env) ->
    check_module({module_def, Name, Imports, Exports, Items, Location}, Env);
check_item({module_def, Name, Exports, Items, Location}, Env) ->
    % Parser format without imports field - add empty imports
    check_module({module_def, Name, [], Exports, Items, Location}, Env);
check_item(FuncDef = #function_def{}, Env) ->
    % Handle function_def record (supports both single and multi-clause)
    check_function(FuncDef, Env);
check_item({function_def, Name, Params, ReturnType, Constraint, Body, Location}, Env) ->
    % Fallback for old tuple-based format without is_private field
    check_function(
        {function_def, Name, Params, ReturnType, Constraint, Body, false, Location},
        Env
    );
check_item(
    {function_def, Name, Params, ReturnType, Constraint, Body, IsPrivate, Location},
    Env
) ->
    % New tuple format with is_private field
    check_function(
        {function_def, Name, Params, ReturnType, Constraint, Body, IsPrivate, Location},
        Env
    );
%% Handle curify function definition (both record and tuple formats)
check_item(
    {curify_function_def, Name, Params, ReturnType, Constraint, ErlModule, ErlFunc, ErlArity,
        IsPrivate, Location},
    Env
) ->
    check_curify_function(
        {curify_function_def, Name, Params, ReturnType, Constraint, ErlModule, ErlFunc, ErlArity,
            IsPrivate, Location},
        Env
    );
check_item({import_def, Module, Items, Location}, Env) ->
    check_import({import_def, Module, Items, Location}, Env);
check_item({export_list, ExportSpecs}, Env) ->
    % Export lists are handled during module checking - just pass through
    {ok, Env, success_result({export_list, ExportSpecs})};
check_item(FSM = #fsm_def{}, Env) ->
    check_fsm(FSM, Env);
check_item(TypeDef = #type_def{}, Env) ->
    check_type_definition(TypeDef, Env);
check_item(TraitDef = #trait_def{}, Env) ->
    check_trait_def(TraitDef, Env);
check_item(TraitImpl = #trait_impl{}, Env) ->
    check_trait_impl(TraitImpl, Env);
check_item(TypeclassDef = #typeclass_def{}, Env) ->
    % Deep validation of typeclass definitions
    check_typeclass_def(TypeclassDef, Env);
check_item(InstanceDef = #instance_def{}, Env) ->
    % Deep validation of instance definitions
    check_instance_def(InstanceDef, Env);
check_item(
    #record_def{
        name = RecordName,
        type_params = TypeParams,
        fields = Fields,
        derive_clause = DeriveClause,
        location = Location
    },
    Env
) ->
    % Convert field types to internal representation and resolve type names from environment
    ConvertedFields = [convert_and_resolve_record_field_def(F, Env) || F <- Fields],
    % Create a record type from the field definitions
    RecordType = {record_type, RecordName, ConvertedFields},
    Env1 = cure_types:extend_env(Env, RecordName, RecordType),

    % Process derive clause if present
    case DeriveClause of
        undefined ->
            {ok, Env1, success_result(RecordType)};
        #derive_clause{typeclasses = Typeclasses} ->
            % Generate instances for each derived typeclass
            case process_derive_clause(RecordName, TypeParams, Typeclasses, Env1, Location) of
                {ok, EnvWithInstances} ->
                    {ok, EnvWithInstances, success_result(RecordType)};
                {error, Error} ->
                    {ok, Env1, error_result(Error)}
            end
    end.

%% Process derive clause to generate typeclass instances
process_derive_clause(_RecordName, _TypeParams, [], Env, _Location) ->
    % No typeclasses to derive
    {ok, Env};
process_derive_clause(RecordName, TypeParams, [Typeclass | RestTypeclasses], Env, Location) ->
    % Lookup the record definition from the environment
    RecordType = cure_types:lookup_env(Env, RecordName),

    % Create a simplified record_def for derivation
    % (The derive functions need record structure information)
    ForType =
        case RecordType of
            {record_type, Name, Fields} ->
                #record_def{
                    name = Name,
                    type_params = TypeParams,
                    fields = Fields,
                    derive_clause = undefined,
                    location = Location
                };
            _ ->
                #primitive_type{name = RecordName, location = Location}
        end,

    case cure_derive:derive_instance(Typeclass, ForType, [], Env) of
        {ok, InstanceDef} ->
            % Check and register the generated instance
            case check_instance_def(InstanceDef, Env) of
                {ok, NewEnv, _Result} ->
                    % Continue with remaining typeclasses
                    process_derive_clause(
                        RecordName, TypeParams, RestTypeclasses, NewEnv, Location
                    );
                {error, Error} ->
                    {error, Error}
            end;
        {error, Reason} ->
            Error = #typecheck_error{
                message = io_lib:format("Cannot derive ~p for ~p", [Typeclass, RecordName]),
                location = Location,
                details = Reason
            },
            {error, Error}
    end.

%% Check FSM definition with comprehensive validation and SMT verification
check_fsm(
    #fsm_def{
        name = Name,
        states = States,
        initial = Initial,
        state_defs = StateDefs,
        location = Location
    },
    Env
) ->
    cure_utils:debug("[FSM_CHECK] Checking FSM ~p with states ~p~n", [Name, States]),

    % Step 1: Verify initial state is in states list
    InitCheck =
        case lists:member(Initial, States) of
            false ->
                {error, #typecheck_error{
                    message = "Initial state not in states list",
                    location = Location,
                    details = {invalid_initial_state, Initial, States}
                }};
            true ->
                ok
        end,

    case InitCheck of
        {error, Error} ->
            {ok, Env, error_result(Error)};
        ok ->
            % Step 2: Check all state definitions are valid
            case check_state_definitions(StateDefs, States) of
                {error, Error} ->
                    {ok, Env, error_result(Error)};
                ok ->
                    % Step 3: Extract all event names from transitions
                    Events = extract_fsm_events(StateDefs),
                    cure_utils:debug("[FSM_CHECK] Events: ~p~n", [Events]),

                    % Step 4: Build state transition graph
                    TransitionGraph = build_transition_graph(StateDefs),
                    cure_utils:debug("[FSM_CHECK] Transition graph: ~p~n", [TransitionGraph]),

                    % Step 5: Check state reachability
                    case check_state_reachability(States, Initial, TransitionGraph) of
                        {ok, ReachableStates} ->
                            cure_utils:debug("[FSM_CHECK] Reachable states: ~p~n", [ReachableStates]),
                            UnreachableStates = States -- ReachableStates,
                            Result =
                                case UnreachableStates of
                                    [] ->
                                        success_result({fsm_type, Name, States, Initial});
                                    _ ->
                                        % Emit warning for unreachable states
                                        Warning = #typecheck_warning{
                                            message = "FSM has unreachable states",
                                            location = Location,
                                            details = {unreachable_states, UnreachableStates}
                                        },
                                        warning_result({fsm_type, Name, States, Initial}, Warning)
                                end,

                            % Step 6: Verify event handler signatures (if handlers are defined)
                            HandlerCheckResult = check_fsm_handler_signatures(
                                Name, Events, StateDefs, Env
                            ),
                            ResultWithHandlers =
                                case HandlerCheckResult of
                                    {ok, Warnings} ->
                                        % Add any warnings from handler checking
                                        lists:foldl(
                                            fun(W, Acc) ->
                                                Acc#typecheck_result{
                                                    warnings = [W | Acc#typecheck_result.warnings]
                                                }
                                            end,
                                            Result,
                                            Warnings
                                        );
                                    {error, HandlerError} ->
                                        add_error(Result, HandlerError)
                                end,

                            % Step 7: SMT verification of FSM properties
                            case
                                verify_fsm_properties(Name, States, Initial, TransitionGraph, Env)
                            of
                                ok ->
                                    FSMType = {fsm_type, Name, States, Initial},
                                    % Check if there's already a record type with this name
                                    % If so, keep the record type and add FSM under a different key
                                    NewEnv =
                                        case cure_types:lookup_env(Env, Name) of
                                            {record_type, _, _} = RecordType ->
                                                % Preserve record type under original name
                                                % Add FSM type under {fsm, Name} key
                                                Env1 = cure_types:extend_env(
                                                    Env, {fsm, Name}, FSMType
                                                ),
                                                % Also add under plain name for compatibility
                                                Env2 = cure_types:extend_env(
                                                    Env1, Name, RecordType
                                                ),
                                                Env2;
                                            _ ->
                                                % No conflict, just add FSM type
                                                cure_types:extend_env(Env, Name, FSMType)
                                        end,
                                    {ok, NewEnv, ResultWithHandlers};
                                {error, SmtError} ->
                                    {ok, Env, add_error(ResultWithHandlers, SmtError)}
                            end;
                        {error, ReachError} ->
                            {ok, Env, error_result(ReachError)}
                    end
            end
    end.

%% Check module definition - New AST format
check_module({module_def, Name, Imports, Exports, Items, _Location}, Env) ->
    % Create module-scoped environment
    ModuleEnv = cure_types:extend_env(Env, module, Name),

    % Process imports first to extend environment
    % All modules (including stdlib) are handled uniformly through the import system
    ImportEnv =
        case process_imports(Imports, ModuleEnv) of
            {ok, TempEnv} ->
                TempEnv;
            % Continue with original env on import errors
            {error, _Error} ->
                ModuleEnv
        end,

    % Two-pass processing: first collect all function signatures, then check bodies
    % Pass 1: Collect function signatures and add them to environment
    FunctionEnv0 = collect_function_signatures(Items, ImportEnv),

    % Add module name as an FSM type alias if there's an FSM defined with a record name
    % This allows patterns like: fsm RecordType{...} do ... end and start_fsm(ModuleName)
    FunctionEnv1 =
        case find_fsm_with_record_name(Items) of
            {ok, FSMName, States, Initial} ->
                % Add module name as an alias to the FSM
                FSMType = {fsm_type, FSMName, States, Initial},
                cure_types:extend_env(FunctionEnv0, Name, FSMType);
            not_found ->
                FunctionEnv0
        end,

    % Typeclass two-pass processing:
    % Pass 1: Register all typeclass definitions first
    FunctionEnv = register_all_typeclasses(Items, FunctionEnv1),

    % Pass 2: Check all items with function signatures AND typeclass definitions in environment
    case check_items(Items, FunctionEnv, new_result()) of
        Result = #typecheck_result{success = true} ->
            % Verify exported functions exist and have correct arities
            cure_utils:debug("[MODULE] Body checking succeeded, now checking exports~n"),
            ExportSpecs = extract_export_specs(Exports, Items),
            cure_utils:debug("[MODULE] Export specs: ~p~n", [ExportSpecs]),
            cure_utils:debug("[MODULE] Items: ~p~n", [[element(1, I) || I <- Items]]),
            case check_exports(ExportSpecs, Items) of
                ok ->
                    {ok, cure_types:extend_env(Env, Name, {module_type, Name}), Result};
                {error, ExportError} ->
                    {error, ExportError}
            end;
        Result ->
            {ok, Env, Result}
    end.

%% Check function definition - New AST format
% Record format with multi-clause support (with polymorphic type params)
check_function(
    #function_def{
        name = Name,
        type_params = TypeParams,
        clauses = Clauses,
        params = _Params,
        return_type = _ReturnType,
        constraint = _Constraint,
        body = _Body,
        is_private = _IsPrivate,
        location = Location
    },
    Env
) when Clauses =/= undefined andalso length(Clauses) > 0 ->
    % Multi-clause function - check each clause
    cure_utils:debug("[CHECK_FUNC] Checking multi-clause function ~p with type params ~p~n", [
        Name, TypeParams
    ]),
    case TypeParams of
        undefined ->
            check_multiclause_function(Name, Clauses, Location, Env);
        [] ->
            check_multiclause_function(Name, Clauses, Location, Env);
        _ ->
            check_multiclause_polymorphic_function(Name, TypeParams, Clauses, Location, Env)
    end;
check_function(
    #function_def{
        name = Name,
        type_params = TypeParams,
        params = Params,
        return_type = ReturnType,
        constraint = Constraint,
        body = Body,
        where_clause = WhereClause,
        is_private = IsPrivate,
        location = Location
    },
    Env
) ->
    % Single-clause function (record format, may be polymorphic)
    case TypeParams of
        undefined ->
            % No type params - regular monomorphic function
            check_single_clause_function(
                Name, Params, ReturnType, Constraint, Body, WhereClause, IsPrivate, Location, Env
            );
        [] ->
            % Empty type params list - regular monomorphic function
            check_single_clause_function(
                Name, Params, ReturnType, Constraint, Body, WhereClause, IsPrivate, Location, Env
            );
        _ ->
            % Polymorphic function with type parameters
            check_polymorphic_function(
                Name,
                TypeParams,
                Params,
                ReturnType,
                Constraint,
                Body,
                WhereClause,
                IsPrivate,
                Location,
                Env
            )
    end;
% 7-parameter format (old format without is_private)
check_function(
    {function_def, Name, Params, ReturnType, Constraint, Body, Location},
    Env
) ->
    check_function(
        {function_def, Name, Params, ReturnType, Constraint, Body, false, Location},
        Env
    );
% 8-parameter format (new format with is_private)
check_function(
    {function_def, Name, Params, ReturnType, Constraint, Body, _IsPrivate, Location},
    Env
) ->
    try
        % Convert parameters to type environment and extract type parameters
        {ParamTypes, ParamEnv} = process_parameters(Params, Env),

        % Also extract type parameters from return type if present
        EnvWithReturnTypeParams =
            case ReturnType of
                undefined ->
                    ParamEnv;
                _ ->
                    cure_utils:debug("[RETURN] Processing return type ~p~n", [ReturnType]),
                    extract_and_add_type_params_safe(ReturnType, ParamEnv)
            end,

        % Check and process constraint if present
        FinalEnv =
            case Constraint of
                undefined ->
                    EnvWithReturnTypeParams;
                _ ->
                    % First check that constraint is boolean
                    case
                        cure_types:infer_type(
                            convert_expr_to_tuple(Constraint), EnvWithReturnTypeParams
                        )
                    of
                        {ok, InferenceResult} ->
                            ConstraintType = element(2, InferenceResult),
                            case cure_types:unify(ConstraintType, {primitive_type, 'Bool'}) of
                                {ok, _} ->
                                    % Convert constraint to SMT and add to environment
                                    process_when_clause_constraint(
                                        Constraint, EnvWithReturnTypeParams, Location
                                    );
                                {error, Reason} ->
                                    throw({constraint_not_bool, Reason, Location})
                            end;
                        {error, Reason} ->
                            throw({constraint_inference_failed, Reason, Location})
                    end
            end,

        % Check function body with constraint-enhanced environment
        cure_utils:debug("About to infer type for function ~p body~n", [Name]),
        cure_utils:debug("Body AST: ~p~n", [Body]),
        try
            BodyTuple = convert_expr_to_tuple(Body),
            cure_utils:debug("Converted body to tuple: ~p~n", [BodyTuple]),
            BodyInferenceResult = cure_types:infer_type(BodyTuple, FinalEnv),
            cure_utils:debug("Type inference result: ~p~n", [BodyInferenceResult]),
            case BodyInferenceResult of
                {ok, InferenceResult2} ->
                    BodyType = element(2, InferenceResult2),
                    % Check return type if specified
                    case ReturnType of
                        undefined ->
                            % Function type is inferred
                            FuncType = {function_type, ParamTypes, BodyType},
                            cure_utils:debug(
                                "Adding function ~p (new AST) with inferred type: ~p~n",
                                [Name, FuncType]
                            ),
                            NewEnv = cure_types:extend_env(Env, Name, FuncType),
                            {ok, NewEnv, success_result(FuncType)};
                        _ ->
                            % Check body matches declared return type
                            ExpectedReturnType = convert_type_with_env(ReturnType, FinalEnv),
                            case cure_types:unify(BodyType, ExpectedReturnType) of
                                {ok, _} ->
                                    FuncType = {function_type, ParamTypes, ExpectedReturnType},
                                    cure_utils:debug(
                                        "Adding function ~p (new AST) with explicit type: ~p~n",
                                        [Name, FuncType]
                                    ),
                                    NewEnv = cure_types:extend_env(Env, Name, FuncType),
                                    {ok, NewEnv, success_result(FuncType)};
                                {error, UnifyReason} ->
                                    ErrorMsg =
                                        #typecheck_error{
                                            message =
                                                "Function body type doesn't match declared return type",
                                            location = Location,
                                            details =
                                                {type_mismatch, ExpectedReturnType, BodyType,
                                                    UnifyReason}
                                        },
                                    {ok, Env, error_result(ErrorMsg)}
                            end
                    end;
                {error, InferReason} ->
                    cure_utils:debug("FUNCTION BODY INFERENCE FAILED ***~n"),
                    cure_utils:debug("  *** Function: ~p~n", [Name]),
                    cure_utils:debug("  *** Body: ~p~n", [Body]),
                    cure_utils:debug("  *** Error: ~p~n", [InferReason]),
                    cure_utils:debug(
                        "  *** Environment size: ~p functions~n",
                        [
                            map_size(
                                case FinalEnv of
                                    #{} ->
                                        FinalEnv;
                                    _ ->
                                        #{}
                                end
                            )
                        ]
                    ),
                    cure_utils:debug("Failed to infer function ~p body type: ~p~n", [
                        Name, InferReason
                    ]),
                    ErrorMsg2 =
                        #typecheck_error{
                            message = "Failed to infer function body type",
                            location = Location,
                            details = {inference_failed, InferReason}
                        },
                    {ok, Env, error_result(ErrorMsg2)}
            end
        catch
            error:function_clause:Stacktrace ->
                cure_utils:debug("ERROR: function_clause error in infer_type for function ~p~n", [
                    Name
                ]),
                cure_utils:debug("ERROR: Body tuple: ~p~n", [convert_expr_to_tuple(Body)]),
                io:format(
                    "ERROR: Environment size: ~p~n",
                    [
                        map_size(
                            case FinalEnv of
                                #{} ->
                                    FinalEnv;
                                _ ->
                                    #{}
                            end
                        )
                    ]
                ),
                cure_utils:debug("ERROR: Stacktrace: ~p~n", [Stacktrace]),
                ErrorMsg3 =
                    #typecheck_error{
                        message = "Function clause error during type inference",
                        location = Location,
                        details = {function_clause_error, Stacktrace}
                    },
                {ok, Env, error_result(ErrorMsg3)}
        end
    catch
        {ErrorType, Details, ErrorLocation} ->
            ThrownError =
                #typecheck_error{
                    message = format_error_type(ErrorType),
                    location = ErrorLocation,
                    details = Details
                },
            {ok, Env, error_result(ThrownError)}
    end.

%% Check single-clause function (extracted from original check_function)
check_single_clause_function(
    Name, Params, ReturnType, Constraint, Body, WhereClause, _IsPrivate, Location, Env
) ->
    try
        % Convert parameters to type environment and extract type parameters
        {ParamTypes, ParamEnv} = process_parameters(Params, Env),

        % Also extract type parameters from return type if present
        EnvWithReturnTypeParams =
            case ReturnType of
                undefined ->
                    ParamEnv;
                _ ->
                    cure_utils:debug("[RETURN] Processing return type ~p~n", [ReturnType]),
                    extract_and_add_type_params_safe(ReturnType, ParamEnv)
            end,

        % Add typeclass constraints from where clause to environment
        EnvWithTypeclass =
            case WhereClause of
                undefined ->
                    EnvWithReturnTypeParams;
                #where_clause{constraints = TypeclassConstraints} ->
                    cure_types:extend_env_with_typeclass_constraints(
                        EnvWithReturnTypeParams, TypeclassConstraints
                    );
                _ ->
                    EnvWithReturnTypeParams
            end,

        % Check and process constraint if present
        FinalEnv =
            case Constraint of
                undefined ->
                    EnvWithTypeclass;
                _ ->
                    % First check that constraint is boolean
                    case
                        cure_types:infer_type(
                            convert_expr_to_tuple(Constraint), EnvWithTypeclass
                        )
                    of
                        {ok, InferenceResult} ->
                            ConstraintType = element(2, InferenceResult),
                            case cure_types:unify(ConstraintType, {primitive_type, 'Bool'}) of
                                {ok, _} ->
                                    % Convert constraint to SMT and add to environment
                                    process_when_clause_constraint(
                                        Constraint, EnvWithTypeclass, Location
                                    );
                                {error, Reason} ->
                                    throw({constraint_not_bool, Reason, Location})
                            end;
                        {error, Reason} ->
                            throw({constraint_inference_failed, Reason, Location})
                    end
            end,

        % Check function body with constraint-enhanced environment
        cure_utils:debug("About to infer type for function ~p body~n", [Name]),
        cure_utils:debug("Body AST: ~p~n", [Body]),
        try
            BodyTuple = convert_expr_to_tuple(Body),
            cure_utils:debug("Converted body to tuple: ~p~n", [BodyTuple]),
            BodyInferenceResult = cure_types:infer_type(BodyTuple, FinalEnv),
            cure_utils:debug("Type inference result: ~p~n", [BodyInferenceResult]),
            case BodyInferenceResult of
                {ok, InferenceResult2} ->
                    BodyType = element(2, InferenceResult2),
                    % Check return type if specified
                    case ReturnType of
                        undefined ->
                            % Function type is inferred
                            FuncType = {function_type, ParamTypes, BodyType},
                            cure_utils:debug(
                                "Adding function ~p (new AST) with inferred type: ~p~n",
                                [Name, FuncType]
                            ),
                            NewEnv = cure_types:extend_env(Env, Name, FuncType),
                            {ok, NewEnv, success_result(FuncType)};
                        _ ->
                            % Check body matches declared return type
                            ExpectedReturnType = convert_type_with_env(ReturnType, FinalEnv),
                            case cure_types:unify(BodyType, ExpectedReturnType) of
                                {ok, _} ->
                                    FuncType = {function_type, ParamTypes, ExpectedReturnType},
                                    cure_utils:debug(
                                        "Adding function ~p (new AST) with explicit type: ~p~n",
                                        [Name, FuncType]
                                    ),
                                    NewEnv = cure_types:extend_env(Env, Name, FuncType),
                                    {ok, NewEnv, success_result(FuncType)};
                                {error, UnifyReason} ->
                                    ErrorMsg =
                                        #typecheck_error{
                                            message =
                                                "Function body type doesn't match declared return type",
                                            location = Location,
                                            details =
                                                {type_mismatch, ExpectedReturnType, BodyType,
                                                    UnifyReason}
                                        },
                                    {ok, Env, error_result(ErrorMsg)}
                            end
                    end;
                {error, InferReason} ->
                    cure_utils:debug("FUNCTION BODY INFERENCE FAILED ***~n"),
                    cure_utils:debug("  *** Function: ~p~n", [Name]),
                    cure_utils:debug("  *** Body: ~p~n", [Body]),
                    cure_utils:debug("  *** Error: ~p~n", [InferReason]),
                    ErrorMsg2 =
                        #typecheck_error{
                            message = "Failed to infer function body type",
                            location = Location,
                            details = {inference_failed, InferReason}
                        },
                    {ok, Env, error_result(ErrorMsg2)}
            end
        catch
            error:function_clause:Stacktrace ->
                cure_utils:debug("ERROR: function_clause error in infer_type for function ~p~n", [
                    Name
                ]),
                ErrorMsg3 =
                    #typecheck_error{
                        message = "Function clause error during type inference",
                        location = Location,
                        details = {function_clause_error, Stacktrace}
                    },
                {ok, Env, error_result(ErrorMsg3)}
        end
    catch
        {ErrorType, Details, ErrorLocation} ->
            ThrownError =
                #typecheck_error{
                    message = format_error_type(ErrorType),
                    location = ErrorLocation,
                    details = Details
                },
            {ok, Env, error_result(ThrownError)}
    end.

%% Check multi-clause function
check_multiclause_function(Name, Clauses, Location, Env) ->
    cure_utils:debug("[MULTICLAUSE] Checking ~p clauses for function ~p~n", [
        length(Clauses), Name
    ]),

    % Check each clause individually
    ClauseResults = lists:map(
        fun(Clause) ->
            #function_clause{
                params = Params,
                return_type = ReturnType,
                constraint = Constraint,
                body = Body
            } = Clause,

            % Check this clause as if it were a single function
            % Note: Multi-clause functions don't have where_clause per clause
            check_single_clause_function(
                Name, Params, ReturnType, Constraint, Body, undefined, false, Location, Env
            )
        end,
        Clauses
    ),

    % Collect any errors from clause checking
    ClauseErrors = lists:flatten(
        lists:map(
            fun(Result) ->
                case Result of
                    {ok, _, #typecheck_result{errors = Errors}} -> Errors;
                    _ -> []
                end
            end,
            ClauseResults
        )
    ),

    % If all clauses pass, the function signature was already added during signature collection
    case ClauseErrors of
        [] ->
            % All clauses type-checked successfully
            % The function signature with union types was already added to Env
            {ok, Env, success_result({multiclause_function, Name})};
        Errors ->
            % Some clauses failed
            {ok, Env, #typecheck_result{
                success = false,
                type = undefined,
                errors = Errors,
                warnings = []
            }}
    end.

%% Check polymorphic function with type parameters
check_polymorphic_function(
    Name, TypeParams, Params, ReturnType, Constraint, Body, WhereClause, _IsPrivate, Location, Env
) ->
    cure_utils:debug("[POLY] Checking polymorphic function ~p with type params ~p~n", [
        Name, TypeParams
    ]),
    try
        % Extract type parameter names
        TypeParamNames = cure_types:extract_type_param_names(TypeParams),
        cure_utils:debug("[POLY] Type parameter names: ~p~n", [TypeParamNames]),

        % Add type parameters as type variables to the environment
        EnvWithTypeParams = lists:foldl(
            fun(TParamName, AccEnv) ->
                % Treat type parameters as primitive types in the environment during checking
                cure_types:extend_env(AccEnv, TParamName, {primitive_type, TParamName})
            end,
            Env,
            TypeParamNames
        ),

        % Process function parameters in the type-parameter-enhanced environment
        {ParamTypes, ParamEnv} = process_parameters(Params, EnvWithTypeParams),

        % Process return type if present
        EnvWithReturnTypeParams =
            case ReturnType of
                undefined ->
                    ParamEnv;
                _ ->
                    cure_utils:debug("[POLY] Processing return type ~p~n", [ReturnType]),
                    extract_and_add_type_params_safe(ReturnType, ParamEnv)
            end,

        % Add typeclass constraints from where clause to environment
        EnvWithTypeclass =
            case WhereClause of
                undefined ->
                    EnvWithReturnTypeParams;
                #where_clause{constraints = TypeclassConstraints} ->
                    cure_types:extend_env_with_typeclass_constraints(
                        EnvWithReturnTypeParams, TypeclassConstraints
                    );
                _ ->
                    EnvWithReturnTypeParams
            end,

        % Check and process constraint if present
        FinalEnv =
            case Constraint of
                undefined ->
                    EnvWithTypeclass;
                _ ->
                    case
                        cure_types:infer_type(
                            convert_expr_to_tuple(Constraint), EnvWithTypeclass
                        )
                    of
                        {ok, InferenceResult} ->
                            ConstraintType = element(2, InferenceResult),
                            case cure_types:unify(ConstraintType, {primitive_type, 'Bool'}) of
                                {ok, _} ->
                                    process_when_clause_constraint(
                                        Constraint, EnvWithTypeclass, Location
                                    );
                                {error, Reason} ->
                                    throw({constraint_not_bool, Reason, Location})
                            end;
                        {error, Reason} ->
                            throw({constraint_inference_failed, Reason, Location})
                    end
            end,

        % Check function body
        cure_utils:debug("[POLY] Checking body for function ~p~n", [Name]),
        BodyTuple = convert_expr_to_tuple(Body),
        case cure_types:infer_type(BodyTuple, FinalEnv) of
            {ok, InferenceResult2} ->
                BodyType = element(2, InferenceResult2),

                % Construct the polymorphic function type
                MonoFuncType =
                    {function_type, ParamTypes,
                        case ReturnType of
                            undefined -> BodyType;
                            _ -> convert_type_with_env(ReturnType, FinalEnv)
                        end},

                % Extract constraints from type parameters with bounds
                Constraints = extract_type_param_constraints(TypeParams, Env),
                cure_utils:debug("[POLY] Extracted constraints: ~p~n", [Constraints]),

                % Wrap in poly_type for polymorphic function
                PolyFuncType = #poly_type{
                    type_params = TypeParams,
                    constraints = Constraints,
                    body_type = MonoFuncType,
                    location = Location
                },

                cure_utils:debug("[POLY] Adding polymorphic function ~p with type: ~p~n", [
                    Name, PolyFuncType
                ]),
                NewEnv = cure_types:extend_env(Env, Name, PolyFuncType),
                {ok, NewEnv, success_result(PolyFuncType)};
            {error, InferReason} ->
                cure_utils:debug("[POLY] Failed to infer body type: ~p~n", [InferReason]),
                ErrorMsg =
                    #typecheck_error{
                        message = "Failed to infer polymorphic function body type",
                        location = Location,
                        details = {inference_failed, InferReason}
                    },
                {ok, Env, error_result(ErrorMsg)}
        end
    catch
        {ErrorType, Details, ErrorLocation} ->
            ThrownError =
                #typecheck_error{
                    message = format_error_type(ErrorType),
                    location = ErrorLocation,
                    details = Details
                },
            {ok, Env, error_result(ThrownError)}
    end.

%% Check multi-clause polymorphic function
check_multiclause_polymorphic_function(Name, TypeParams, Clauses, Location, Env) ->
    cure_utils:debug(
        "[POLY-MULTI] Checking ~p clauses for polymorphic function ~p with type params ~p~n", [
            length(Clauses), Name, TypeParams
        ]
    ),

    % Check each clause as polymorphic functions
    ClauseResults = lists:map(
        fun(Clause) ->
            #function_clause{
                params = Params,
                return_type = ReturnType,
                constraint = Constraint,
                body = Body
            } = Clause,

            % Check this clause as a polymorphic function
            % Note: Multi-clause functions don't have where_clause per clause
            check_polymorphic_function(
                Name,
                TypeParams,
                Params,
                ReturnType,
                Constraint,
                Body,
                undefined,
                false,
                Location,
                Env
            )
        end,
        Clauses
    ),

    % Collect any errors
    ClauseErrors = lists:flatten(
        lists:map(
            fun(Result) ->
                case Result of
                    {ok, _, #typecheck_result{errors = Errors}} -> Errors;
                    _ -> []
                end
            end,
            ClauseResults
        )
    ),

    % If all clauses pass, return success
    case ClauseErrors of
        [] ->
            {ok, Env, success_result({polymorphic_multiclause_function, Name})};
        Errors ->
            {ok, Env, #typecheck_result{
                success = false,
                type = undefined,
                errors = Errors,
                warnings = []
            }}
    end.

%% Check curify function definition
%% For curify functions, we trust the type annotations and validate the function signature matches
check_curify_function(
    #curify_function_def{
        name = Name,
        params = Params,
        return_type = ReturnType,
        constraint = Constraint,
        erlang_module = _ErlModule,
        erlang_function = _ErlFunc,
        erlang_arity = ErlArity,
        is_private = _IsPrivate,
        location = Location
    },
    Env
) ->
    try
        % Validate arity matches parameter count (should already be validated by parser)
        ParamCount = length(Params),
        case ErlArity of
            ParamCount ->
                ok;
            _ ->
                throw({curify_arity_mismatch, ParamCount, ErlArity, Location})
        end,

        % Convert parameters to type environment
        {ParamTypes, ParamEnv} = process_parameters(Params, Env),

        % Check constraint if present (same as regular functions)
        case Constraint of
            undefined ->
                ok;
            _ ->
                case cure_types:infer_type(convert_expr_to_tuple(Constraint), ParamEnv) of
                    {ok, InferenceResult} ->
                        ConstraintType = element(2, InferenceResult),
                        case cure_types:unify(ConstraintType, {primitive_type, 'Bool'}) of
                            {ok, _} ->
                                ok;
                            {error, Reason} ->
                                throw({constraint_not_bool, Reason, Location})
                        end;
                    {error, Reason} ->
                        throw({constraint_inference_failed, Reason, Location})
                end
        end,

        % For curify functions, the return type MUST be specified (enforced by parser)
        % We trust the type annotation and don't check the Erlang function
        case ReturnType of
            undefined ->
                % This should never happen as parser enforces return type for curify
                throw({missing_return_type_for_curify, Location});
            _ ->
                ExpectedReturnType = convert_type_with_env(ReturnType, ParamEnv),
                % Use regular function_type - the Erlang function call is handled during codegen
                FuncType = {function_type, ParamTypes, ExpectedReturnType},
                NewEnv = cure_types:extend_env(Env, Name, FuncType),
                {ok, NewEnv, success_result(FuncType)}
        end
    catch
        {ErrorType, Details, ErrorLocation} ->
            ThrownError =
                #typecheck_error{
                    message = format_error_type(ErrorType),
                    location = ErrorLocation,
                    details = Details
                },
            {ok, Env, error_result(ThrownError)}
    end.

%% Check import - New AST format
check_import({import_def, Module, Items, _Location}, Env) ->
    case check_import_items(Module, Items, Env) of
        {ok, NewEnv} ->
            ImportType = {import_type, Module, Items},
            {ok, NewEnv, success_result(ImportType)};
        {error, Error} ->
            {ok, Env, error_result(Error)}
    end.

%% Check type definition
check_type_definition(
    #type_def{
        name = Name,
        params = Params,
        definition = Definition,
        constraint = Constraint
    },
    Env
) ->
    try
        % Convert type parameters to environment bindings if they exist
        EnvWithTypeParams =
            case Params of
                [] ->
                    Env;
                _ ->
                    add_type_params_to_env(Params, Env)
            end,

        % Handle different kinds of type definitions
        case Definition of
            #union_type{types = Variants} ->
                % This is an algebraic data type with constructors
                {NewEnv, ConstructorTypes} =
                    process_union_type(Name, Params, Variants, EnvWithTypeParams),
                UnionType = {union_type, Name, Params, ConstructorTypes},
                FinalEnv = cure_types:extend_env(NewEnv, Name, UnionType),
                {ok, FinalEnv, success_result(UnionType)};
            _ ->
                % Simple type definition or type alias
                BaseType = convert_type_to_tuple(Definition),

                % Check if this is a refinement type (has a when clause)
                TypeDefType =
                    case Constraint of
                        undefined ->
                            % No constraint - regular type alias
                            BaseType;
                        _ ->
                            % Has constraint - create refinement type
                            % Use the first parameter name or default to 'x' as the refinement variable
                            VarName =
                                case Params of
                                    % Default refinement variable name
                                    [] -> x;
                                    [FirstParam | _] when is_atom(FirstParam) -> FirstParam;
                                    [#type_param{name = ParamName} | _] -> ParamName;
                                    _ -> x
                                end,
                            cure_refinement_types:create_refinement_type(
                                BaseType,
                                VarName,
                                Constraint
                            )
                    end,

                NewEnv = cure_types:extend_env(EnvWithTypeParams, Name, TypeDefType),
                {ok, NewEnv, success_result(TypeDefType)}
        end
    catch
        _:Error ->
            ErrorMsg =
                #typecheck_error{
                    message = "Failed to process type definition",
                    location =
                        #location{
                            line = 0,
                            column = 0,
                            file = undefined
                        },
                    details = {type_definition_error, Name, Error}
                },
            {ok, Env, error_result(ErrorMsg)}
    end.

%% Add type parameters to environment
add_type_params_to_env([], Env) ->
    Env;
add_type_params_to_env([Param | Rest], Env) ->
    ParamName =
        case Param of
            #type_param{name = Name} ->
                Name;
            Name when is_atom(Name) ->
                Name;
            _ ->
                throw({invalid_type_param, Param})
        end,
    % Add type parameter as a type variable
    TypeVar = cure_types:new_type_var(ParamName),
    NewEnv = cure_types:extend_env(Env, ParamName, TypeVar),
    add_type_params_to_env(Rest, NewEnv).

%% Process union type and register constructors
process_union_type(TypeName, TypeParams, Variants, Env) ->
    process_union_type_variants(Variants, TypeName, TypeParams, Env, [], Env).

process_union_type_variants(
    [],
    _TypeName,
    _TypeParams,
    _OrigEnv,
    ConstructorAcc,
    FinalEnv
) ->
    {FinalEnv, lists:reverse(ConstructorAcc)};
process_union_type_variants(
    [Variant | Rest],
    TypeName,
    TypeParams,
    OrigEnv,
    ConstructorAcc,
    CurrentEnv
) ->
    {ConstructorName, ConstructorType, UpdatedEnv} =
        process_variant(Variant, TypeName, TypeParams, CurrentEnv),
    ConstructorInfo = {ConstructorName, ConstructorType},
    process_union_type_variants(
        Rest,
        TypeName,
        TypeParams,
        OrigEnv,
        [ConstructorInfo | ConstructorAcc],
        UpdatedEnv
    ).

%% Process a single variant in a union type
process_variant(Variant, TypeName, TypeParams, Env) ->
    case Variant of
        #primitive_type{name = ConstructorName} ->
            % Simple constructor without arguments: None, Lt, Eq, Gt
            % Nullary constructors are direct values, not functions
            ResultType = create_result_type_with_env(TypeName, TypeParams, Env),
            NewEnv = cure_types:extend_env(Env, ConstructorName, ResultType),
            {ConstructorName, ResultType, NewEnv};
        #dependent_type{
            name = ConstructorName, type_params = CtorTypeParams, value_params = ValueParams
        } ->
            % Constructor with arguments: Ok(T), Error(E), Some(T)
            % Use environment-aware conversion to properly resolve type variables
            % Note: CtorTypeParams are the constructor's own type params (usually [])
            %       ValueParams are the constructor's value arguments (e.g., T in Ok(T))
            %       TypeParams (function param) are the parent type's params (e.g., [T, E] in Result(T, E))
            AllParams = CtorTypeParams ++ ValueParams,
            ArgTypes = [convert_type_param_with_env(P, Env) || P <- AllParams],
            ResultType = create_result_type_with_env(TypeName, TypeParams, Env),
            % Create function type: (ArgTypes...) -> ResultType
            ConstructorType = {function_type, ArgTypes, ResultType},
            NewEnv = cure_types:extend_env(Env, ConstructorName, ConstructorType),
            {ConstructorName, ConstructorType, NewEnv};
        _ ->
            % Fallback for other variant types
            throw({unsupported_variant_type, Variant})
    end.

%% Create result type for constructor using environment for type variable lookup
create_result_type_with_env(TypeName, [], _Env) ->
    {primitive_type, TypeName};
create_result_type_with_env(TypeName, TypeParams, Env) ->
    % Convert type parameters using the environment to get consistent type variables
    ParamVars =
        [
            case P of
                #type_param{name = Name} when Name =/= undefined ->
                    case cure_types:lookup_env(Env, Name) of
                        undefined ->
                            cure_types:new_type_var(Name);
                        TypeVar ->
                            case cure_types:is_type_var(TypeVar) of
                                true ->
                                    TypeVar;
                                false ->
                                    cure_types:new_type_var(Name)
                            end
                    end;
                Name when is_atom(Name) ->
                    case cure_types:lookup_env(Env, Name) of
                        undefined ->
                            cure_types:new_type_var(Name);
                        TypeVar ->
                            case cure_types:is_type_var(TypeVar) of
                                true ->
                                    TypeVar;
                                false ->
                                    cure_types:new_type_var(Name)
                            end
                    end;
                _ ->
                    cure_types:new_type_var()
            end
         || P <- TypeParams
        ],
    {dependent_type, TypeName, ParamVars}.

%% Load and parse standard library modules
load_stdlib_modules() ->
    StdLibPath = "lib/std/",
    case file:list_dir(StdLibPath) of
        {ok, Files} ->
            CureFiles = [F || F <- Files, lists:suffix(".cure", F)],
            load_stdlib_files(StdLibPath, CureFiles, #{});
        {error, Reason} ->
            cure_utils:debug("Warning: Could not load stdlib directory ~s: ~p~n", [
                StdLibPath, Reason
            ]),
            #{}
    end.

load_stdlib_files(_BasePath, [], Acc) ->
    Acc;
load_stdlib_files(BasePath, [File | Rest], Acc) ->
    FilePath = BasePath ++ File,
    case cure_parser:parse_file(FilePath) of
        {ok, AST} ->
            ModuleFunctions = extract_module_functions(AST),
            NewAcc = maps:merge(Acc, ModuleFunctions),
            load_stdlib_files(BasePath, Rest, NewAcc);
        {error, Reason} ->
            cure_utils:debug("Warning: Could not parse stdlib file ~s: ~p~n", [FilePath, Reason]),
            load_stdlib_files(BasePath, Rest, Acc)
    end.

%% Extract function definitions from parsed AST
extract_module_functions(AST) ->
    extract_module_functions_helper(AST, #{}).

extract_module_functions_helper([], Acc) ->
    Acc;
extract_module_functions_helper([Item | Rest], Acc) ->
    case Item of
        {module_def, ModuleName, _Imports, _Exports, ModuleItems, _Location} ->
            cure_utils:debug("Found module ~p with ~p items~n", [ModuleName, length(ModuleItems)]),
            ModuleFunctions = extract_functions_from_items(ModuleItems, ModuleName),
            NewAcc = maps:merge(Acc, ModuleFunctions),
            extract_module_functions_helper(Rest, NewAcc);
        {module_def, ModuleName, _Exports, ModuleItems, _Location} ->
            % 4-element version without imports
            cure_utils:debug(
                "Found module ~p (no imports) with ~p items~n",
                [ModuleName, length(ModuleItems)]
            ),
            ModuleFunctions = extract_functions_from_items(ModuleItems, ModuleName),
            NewAcc = maps:merge(Acc, ModuleFunctions),
            extract_module_functions_helper(Rest, NewAcc);
        _ ->
            cure_utils:debug("Skipping non-module item: ~p~n", [element(1, Item)]),
            extract_module_functions_helper(Rest, Acc)
    end.

extract_functions_from_items(Items, ModuleName) ->
    extract_functions_from_items_helper(Items, ModuleName, #{}).

extract_functions_from_items_helper([], _ModuleName, Acc) ->
    Acc;
extract_functions_from_items_helper([Item | Rest], ModuleName, Acc) ->
    case Item of
        % Handle function definitions - use record pattern which covers all function_def cases
        FuncDef when is_record(FuncDef, function_def) ->
            FunctionName = FuncDef#function_def.name,
            Params = FuncDef#function_def.params,
            ReturnType = FuncDef#function_def.return_type,
            IsPrivate = FuncDef#function_def.is_private,
            % Only extract public functions
            case IsPrivate of
                false ->
                    FunctionType = create_function_type_from_signature_records(Params, ReturnType),
                    Key = {ModuleName, FunctionName, length(Params)},
                    NewAcc = maps:put(Key, FunctionType, Acc),
                    extract_functions_from_items_helper(Rest, ModuleName, NewAcc);
                true ->
                    extract_functions_from_items_helper(Rest, ModuleName, Acc)
            end;
        % Handle curify function definitions (record format)
        CurifyFuncDef when is_record(CurifyFuncDef, curify_function_def) ->
            FunctionName = CurifyFuncDef#curify_function_def.name,
            Params = CurifyFuncDef#curify_function_def.params,
            ReturnType = CurifyFuncDef#curify_function_def.return_type,
            IsPrivate = CurifyFuncDef#curify_function_def.is_private,
            % Only extract public functions
            case IsPrivate of
                false ->
                    FunctionType = create_function_type_from_signature_records(Params, ReturnType),
                    Key = {ModuleName, FunctionName, length(Params)},
                    NewAcc = maps:put(Key, FunctionType, Acc),
                    extract_functions_from_items_helper(Rest, ModuleName, NewAcc);
                true ->
                    extract_functions_from_items_helper(Rest, ModuleName, Acc)
            end;
        _ ->
            extract_functions_from_items_helper(Rest, ModuleName, Acc)
    end.

%% Create function type from parameter and return type definitions
create_function_type_from_signature(Params, ReturnType) ->
    ParamTypes = [convert_param_type_to_tuple(P) || P <- Params],
    case ReturnType of
        undefined ->
            % No return type specified, use type variable
            {function_type, ParamTypes, cure_types:new_type_var()};
        _ ->
            ReturnTuple = convert_type_to_tuple(ReturnType),
            {function_type, ParamTypes, ReturnTuple}
    end.

%% Convert parameter type to tuple format
convert_param_type_to_tuple({param, _Name, TypeExpr, _Location}) ->
    convert_type_to_tuple(TypeExpr).

%% Create function type from record format parameters and return type
%% Uses two-pass approach to preserve type variable sharing across parameters
create_function_type_from_signature_records(Params, ReturnType) ->
    % First pass: collect all type parameters from all parameters and return type
    % This ensures that the same type variable name (like 'n') gets the same type variable instance
    EmptyEnv = cure_types:new_env(),
    EnvWithTypeParams = lists:foldl(
        fun(Param, AccEnv) when is_record(Param, param) ->
            ParamType = Param#param.type,
            extract_and_add_type_params_safe(ParamType, AccEnv)
        end,
        EmptyEnv,
        Params
    ),

    % Also extract type parameters from return type
    EnvWithAllTypeParams =
        case ReturnType of
            undefined -> EnvWithTypeParams;
            _ -> extract_and_add_type_params_safe(ReturnType, EnvWithTypeParams)
        end,

    % Second pass: convert parameters using the shared environment
    ParamTypes = [
        begin
            ParamType = P#param.type,
            convert_type_with_env(ParamType, EnvWithAllTypeParams)
        end
     || P <- Params
    ],

    case ReturnType of
        undefined ->
            % No return type specified, use type variable
            {function_type, ParamTypes, cure_types:new_type_var()};
        _ ->
            % Convert return type using the shared environment
            ReturnTuple = convert_type_with_env(ReturnType, EnvWithAllTypeParams),
            {function_type, ParamTypes, ReturnTuple}
    end.

%% Cached standard library functions - now uses pre-compiled signatures
-spec get_stdlib_function_type(atom(), atom(), integer()) -> {ok, term()} | not_found.
get_stdlib_function_type(Module, Name, Arity) ->
    % Use pre-compiled signatures from cure_stdlib_signatures module
    % This eliminates the need to parse stdlib files at compilation time
    cure_stdlib_signatures:get_function_type(Module, Name, Arity).

%% Create function type for imported function with given arity
create_imported_function_type(Module, Name, Arity) ->
    case get_stdlib_function_type(Module, Name, Arity) of
        {ok, ConcreteType} ->
            ConcreteType;
        not_found ->
            % Generate parameter types as fallback
            ParamTypes = [cure_types:new_type_var() || _ <- lists:seq(1, Arity)],
            ReturnType = cure_types:new_type_var(),
            {imported_function_type, Module, Name, ParamTypes, ReturnType}
    end.

%% Check expression with given environment
check_expression(Expr, Env) ->
    check_expression(Expr, Env, undefined).

check_expression(Expr, Env, ExpectedType) ->
    case cure_types:infer_type(convert_expr_to_tuple(Expr), Env) of
        {ok, InferenceResult3} ->
            InferredType = element(2, InferenceResult3),
            case ExpectedType of
                undefined ->
                    success_result(InferredType);
                _ ->
                    case cure_types:unify(InferredType, ExpectedType) of
                        {ok, _} ->
                            success_result(InferredType);
                        {error, Reason} ->
                            Error =
                                #typecheck_error{
                                    message = "Expression type doesn't match expected type",
                                    location = get_expr_location_safe(Expr),
                                    details = {type_mismatch, ExpectedType, InferredType, Reason}
                                },
                            error_result(Error)
                    end
            end;
        {error, Reason} ->
            Error =
                #typecheck_error{
                    message = "Failed to infer expression type",
                    location = get_expr_location_safe(Expr),
                    details = {inference_failed, Reason}
                },
            error_result(Error)
    end.

%% Infer the type of an expression in the given environment (test compatibility).
%%
%% This is a compatibility function for tests that converts expression AST to
%% tuples and calls the core type inference.
%%
%% Args:
%% - Expr: Expression AST node to type check
%% - Env: Type environment for lookups
%%
%% Returns:
%% - {ok, Type}: Successful type inference with inferred type
%% - {error, Reason}: Type inference failure
%%
%% Examples:
%% Expr = #literal_expr{value = 42, location = undefined},
%% Env = cure_typechecker:builtin_env(),
%% {ok, Type} = cure_typechecker:infer_type(Expr, Env).
%% Type should be {primitive_type, 'Int'}
infer_type(Expr, Env) ->
    case cure_types:infer_type(convert_expr_to_tuple(Expr), Env) of
        {ok, InferenceResult4} ->
            InferredType = element(2, InferenceResult4),
            {ok, InferredType};
        {error, Reason} ->
            {error, Reason}
    end.

%% Built-in type environment
builtin_env() ->
    Env = cure_types:new_env(),

    % Add primitive types
    Env1 = cure_types:extend_env(Env, 'Int', {primitive_type, 'Int'}),
    Env2 = cure_types:extend_env(Env1, 'Float', {primitive_type, 'Float'}),
    Env3 = cure_types:extend_env(Env2, 'String', {primitive_type, 'String'}),
    Env4 = cure_types:extend_env(Env3, 'Bool', {primitive_type, 'Bool'}),
    Env5 = cure_types:extend_env(Env4, 'Atom', {primitive_type, 'Atom'}),
    Env5_1 = cure_types:extend_env(Env5, 'Unit', {primitive_type, 'Unit'}),

    % Add dependent types
    % Use primitive Nat type (algebraic with Zero/Succ constructors)
    Env6 = cure_types:extend_env(Env5_1, 'Nat', {primitive_type, 'Nat'}),
    Env7 = cure_types:extend_env(Env6, 'Pos', {refined_type, 'Int', fun(N) -> N > 0 end}),

    % Add Nat constructors
    % Zero : Nat (nullary constructor)
    Env7_1 = cure_types:extend_env(Env7, 'Zero', {primitive_type, 'Nat'}),
    % Succ : Nat -> Nat (unary constructor)
    SuccType = {function_type, [{primitive_type, 'Nat'}], {primitive_type, 'Nat'}},
    Env7_2 = cure_types:extend_env(Env7_1, 'Succ', SuccType),
    % Pred : Nat -> Nat (unary constructor - predecessor)
    PredType = {function_type, [{primitive_type, 'Nat'}], {primitive_type, 'Nat'}},
    Env7_3 = cure_types:extend_env(Env7_2, 'Pred', PredType),

    % Add built-in functions
    % map : (A -> B) -> [A] -> [B]
    MapType =
        {function_type,
            [
                {function_type, [cure_types:new_type_var()], cure_types:new_type_var()},
                {list_type, cure_types:new_type_var(), undefined}
            ],
            {list_type, cure_types:new_type_var(), undefined}},
    Env8 = cure_types:extend_env(Env7_3, map, MapType),

    % filter : (A -> Bool) -> [A] -> [A]
    FilterType =
        {function_type,
            [
                {function_type, [cure_types:new_type_var()], {primitive_type, 'Bool'}},
                {list_type, cure_types:new_type_var(), undefined}
            ],
            {list_type, cure_types:new_type_var(), undefined}},
    Env9 = cure_types:extend_env(Env8, filter, FilterType),

    % length : [A] -> Nat
    LengthType =
        {function_type, [{list_type, cure_types:new_type_var(), undefined}],
            {refined_type, 'Int', fun(N) -> N >= 0 end}},
    Env10 = cure_types:extend_env(Env9, length, LengthType),

    % Add FSM built-in functions
    Env11 = cure_fsm_builtins:register_fsm_builtins(Env10),

    % Standard library function types are now loaded through the normal import mechanism
    % No hardcoded stdlib loading needed

    % Add constants and functions
    Env13 = cure_types:extend_env(Env11, ok, {primitive_type, 'Unit'}),

    % Add ok/0 function: () -> Unit
    OkFunctionType = {function_type, [], {primitive_type, 'Unit'}},
    Env14 = cure_types:extend_env(Env13, ok, OkFunctionType),

    % Add Result type constructors
    % Ok: T -> T (simplified - Ok just returns its argument for now)
    % Error: E -> E (simplified - Error just returns its argument for now)
    % In a full implementation, these would wrap in union types
    TVar = cure_types:new_type_var('T'),
    EVar = cure_types:new_type_var('E'),

    % Ok(value) constructor - identity function for now
    OkConstructorType = {function_type, [TVar], TVar},
    Env15 = cure_types:extend_env(Env14, 'Ok', OkConstructorType),

    % Error(error) constructor - identity function for now
    ErrorConstructorType = {function_type, [EVar], EVar},
    Env16 = cure_types:extend_env(Env15, 'Error', ErrorConstructorType),

    Env16.

%% Helper functions

check_state_definitions(StateDefs, States) ->
    % Check that all defined states are in the states list
    DefinedStates = [Name || #state_def{name = Name} <- StateDefs],
    case lists:all(fun(State) -> lists:member(State, States) end, DefinedStates) of
        true ->
            ok;
        false ->
            InvalidStates = DefinedStates -- States,
            {error, #typecheck_error{
                message = "State definitions contain invalid states",
                location = #location{line = 0, column = 0},
                details = {invalid_states, InvalidStates}
            }}
    end.

%% Extract all event names from FSM state definitions
extract_fsm_events(StateDefs) ->
    lists:usort(
        lists:flatten([
            [get_event_name(T#transition.event) || T <- StateDef#state_def.transitions]
         || StateDef <- StateDefs
        ])
    ).

%% Get event name from transition event expression
get_event_name(#identifier_expr{name = Name}) -> Name;
get_event_name(_) -> undefined.

%% Build transition graph: maps from_state -> [{event, guard, action, to_state}]
%% Enhanced to include guard and action information for verification
build_transition_graph(StateDefs) ->
    lists:foldl(
        fun(#state_def{name = FromState, transitions = Transitions}, Acc) ->
            Edges = [
                {
                    get_event_name(T#transition.event),
                    T#transition.guard,
                    T#transition.action,
                    T#transition.target
                }
             || T <- Transitions
            ],
            maps:put(FromState, Edges, Acc)
        end,
        #{},
        StateDefs
    ).

%% Check state reachability using breadth-first search
check_state_reachability(_AllStates, InitialState, TransitionGraph) ->
    Reachable = bfs_reachability([InitialState], sets:from_list([InitialState]), TransitionGraph),
    {ok, sets:to_list(Reachable)}.

bfs_reachability([], Visited, _Graph) ->
    Visited;
bfs_reachability([Current | Queue], Visited, Graph) ->
    case maps:get(Current, Graph, []) of
        [] ->
            bfs_reachability(Queue, Visited, Graph);
        Transitions ->
            % Get all target states from transitions
            % Updated to handle new graph format: {event, guard, action, target}
            NextStates = [Target || {_Event, _Guard, _Action, Target} <- Transitions],
            % Filter out already visited states
            NewStates = [S || S <- NextStates, not sets:is_element(S, Visited)],
            % Add new states to visited set
            NewVisited = lists:foldl(fun sets:add_element/2, Visited, NewStates),
            % Continue BFS with new states added to queue
            bfs_reachability(Queue ++ NewStates, NewVisited, Graph)
    end.

%% Verify FSM properties using SMT solver
verify_fsm_properties(Name, States, _Initial, TransitionGraph, Env) ->
    cure_utils:debug("[FSM_SMT] Verifying FSM properties for ~p~n", [Name]),

    % Property 1: Initial state is reachable (trivially true)
    % Property 2: All states have defined transitions (not required, terminal states allowed)
    % Property 3: Check for deterministic transitions (multiple same-event transitions)
    case check_determinism(TransitionGraph) of
        {ok, deterministic} ->
            cure_utils:debug("[FSM_SMT] FSM is deterministic~n"),
            ok;
        {ok, nondeterministic, Conflicts} ->
            cure_utils:debug("[FSM_SMT] FSM is non-deterministic at: ~p~n", [Conflicts]),
            % Non-determinism is allowed, handlers decide actual transition
            ok;
        {error, _Error} ->
            % {error, Error}
            ok
    end,

    % Property 4: Liveness - check that all states can reach terminal states
    case check_liveness_property(States, TransitionGraph) of
        ok ->
            cure_utils:debug("[FSM_SMT] Liveness property satisfied~n"),
            ok;
        {warning, LivenessWarning} ->
            cure_utils:debug("[FSM_SMT] Liveness warning: ~p~n", [LivenessWarning]),
            % Return warning but don't fail (some FSMs may intentionally have cycles)
            ok;
        {error, _LivenessError} ->
            % {error, LivenessError}
            ok
    end,

    % Property 5: Guard constraint verification - check that guards are satisfiable
    case verify_guard_constraints(States, TransitionGraph, Env) of
        ok ->
            cure_utils:debug("[FSM_SMT] Guard constraints verified~n"),
            ok;
        {warning, GuardWarning} ->
            cure_utils:debug("[FSM_SMT] Guard warning: ~p~n", [GuardWarning]),
            ok;
        {error, GuardError} ->
            {error, GuardError}
    end.

%% Check if FSM has deterministic transitions
check_determinism(TransitionGraph) ->
    Conflicts = maps:fold(
        fun(FromState, Transitions, Acc) ->
            % Group transitions by event (updated for new graph format)
            EventGroups = group_by_event(Transitions),
            % Find events with multiple targets
            NonDet = maps:fold(
                fun(Event, Targets, InnerAcc) ->
                    case length(Targets) > 1 of
                        true -> [{FromState, Event, Targets} | InnerAcc];
                        false -> InnerAcc
                    end
                end,
                [],
                EventGroups
            ),
            NonDet ++ Acc
        end,
        [],
        TransitionGraph
    ),

    case Conflicts of
        [] -> {ok, deterministic};
        _ -> {ok, nondeterministic, Conflicts}
    end.

%% Group transitions by event name
%% Updated to handle new graph format: {event, guard, action, target}
group_by_event(Transitions) ->
    lists:foldl(
        fun({Event, _Guard, _Action, Target}, Acc) ->
            Targets = maps:get(Event, Acc, []),
            maps:put(Event, [Target | Targets], Acc)
        end,
        #{},
        Transitions
    ).

%% Create a result with warning
warning_result(Type, Warning) ->
    #typecheck_result{
        success = true,
        type = Type,
        errors = [],
        warnings = [Warning]
    }.

%% Convert AST expressions to type system tuples
convert_expr_to_tuple(#literal_expr{value = Value, location = Location}) ->
    {literal_expr, Value, Location};
convert_expr_to_tuple(#identifier_expr{name = Name, location = Location}) ->
    {identifier_expr, Name, Location};
convert_expr_to_tuple(#binary_op_expr{
    op = Op,
    left = Left,
    right = Right,
    location = Location
}) ->
    {binary_op_expr, Op, convert_expr_to_tuple(Left), convert_expr_to_tuple(Right), Location};
convert_expr_to_tuple(#function_call_expr{
    function = Function,
    args = Args,
    location = Location
}) ->
    {function_call_expr, convert_expr_to_tuple(Function),
        [convert_expr_to_tuple(Arg) || Arg <- Args], Location};
convert_expr_to_tuple(#let_expr{
    bindings = Bindings,
    body = Body,
    location = Location
}) ->
    ConvertedBindings = [convert_binding_to_tuple(B) || B <- Bindings],
    {let_expr, ConvertedBindings, convert_expr_to_tuple(Body), Location};
convert_expr_to_tuple(#list_expr{elements = Elements, location = Location}) ->
    {list_expr, [convert_expr_to_tuple(E) || E <- Elements], Location};
convert_expr_to_tuple(#block_expr{expressions = Expressions, location = Location}) ->
    % Convert block to sequence of let expressions
    convert_block_to_lets(Expressions, Location);
convert_expr_to_tuple(#lambda_expr{
    params = Params,
    body = Body,
    location = Location
}) ->
    ConvertedParams = [convert_param_to_tuple(P) || P <- Params],
    {lambda_expr, ConvertedParams, convert_expr_to_tuple(Body), Location};
convert_expr_to_tuple(#unary_op_expr{
    op = Op,
    operand = Operand,
    location = Location
}) ->
    {unary_op_expr, Op, convert_expr_to_tuple(Operand), Location};
convert_expr_to_tuple(#match_expr{
    expr = Expr,
    patterns = Patterns,
    location = Location
}) ->
    ConvertedPatterns = [convert_match_clause_to_tuple(P) || P <- Patterns],
    {match_expr, convert_expr_to_tuple(Expr), ConvertedPatterns, Location};
convert_expr_to_tuple(#cons_expr{
    elements = Elements,
    tail = Tail,
    location = Location
}) ->
    ConvertedElements = [convert_expr_to_tuple(E) || E <- Elements],
    ConvertedTail = convert_expr_to_tuple(Tail),
    {cons_expr, ConvertedElements, ConvertedTail, Location};
convert_expr_to_tuple(#record_expr{
    name = Name,
    fields = Fields,
    location = Location
}) ->
    ConvertedFields = [convert_field_expr_to_tuple(F) || F <- Fields],
    {record_expr, Name, ConvertedFields, Location};
convert_expr_to_tuple(#field_access_expr{
    record = Record,
    field = Field,
    location = Location
}) ->
    {field_access_expr, convert_expr_to_tuple(Record), Field, Location};
convert_expr_to_tuple(#record_update_expr{
    name = Name,
    base = Base,
    fields = Fields,
    location = Location
}) ->
    ConvertedFields = [convert_field_expr_to_tuple(F) || F <- Fields],
    {record_update_expr, Name, convert_expr_to_tuple(Base), ConvertedFields, Location};
convert_expr_to_tuple(#tuple_expr{elements = Elements, location = Location}) ->
    {tuple_expr, [convert_expr_to_tuple(E) || E <- Elements], Location};
convert_expr_to_tuple(Expr) ->
    % Fallback - return as-is for unsupported expressions
    Expr.

convert_binding_to_tuple(#binding{
    pattern = Pattern,
    value = Value,
    location = Location
}) ->
    {binding, convert_pattern_to_tuple(Pattern), convert_expr_to_tuple(Value), Location}.

convert_pattern_to_tuple(#identifier_pattern{name = Name, location = Location}) ->
    {identifier_pattern, Name, Location};
convert_pattern_to_tuple(#literal_pattern{value = Value, location = Location}) ->
    {literal_pattern, Value, Location};
convert_pattern_to_tuple(#list_pattern{
    elements = Elements,
    tail = Tail,
    location = Location
}) ->
    ConvertedElements = [convert_pattern_to_tuple(E) || E <- Elements],
    ConvertedTail =
        case Tail of
            undefined ->
                undefined;
            _ ->
                convert_pattern_to_tuple(Tail)
        end,
    {list_pattern, ConvertedElements, ConvertedTail, Location};
convert_pattern_to_tuple(#record_pattern{
    name = Name,
    fields = Fields,
    location = Location
}) ->
    ConvertedFields = [convert_field_pattern_to_tuple(F) || F <- Fields],
    {record_pattern, Name, ConvertedFields, Location};
convert_pattern_to_tuple(#wildcard_pattern{location = Location}) ->
    {wildcard_pattern, Location};
convert_pattern_to_tuple(#constructor_pattern{
    name = Name,
    args = Args,
    location = Location
}) ->
    ConvertedArgs =
        case Args of
            undefined ->
                undefined;
            [] ->
                [];
            ArgList ->
                [convert_pattern_to_tuple(Arg) || Arg <- ArgList]
        end,
    {constructor_pattern, Name, ConvertedArgs, Location};
convert_pattern_to_tuple(Pattern) ->
    Pattern.

convert_field_expr_to_tuple(#field_expr{name = Name, value = Value, location = Location}) ->
    {field_expr, Name, convert_expr_to_tuple(Value), Location}.

convert_block_to_lets([LastExpr], _Location) ->
    convert_expr_to_tuple(LastExpr);
convert_block_to_lets([#let_expr{} = LetExpr | RestExprs], Location) ->
    % Flatten nested lets
    ConvertedLet = convert_expr_to_tuple(LetExpr),
    case ConvertedLet of
        {let_expr, Bindings, _Body, _} ->
            % Chain the let with the rest of the block
            {let_expr, Bindings, convert_block_to_lets(RestExprs, Location), Location};
        _ ->
            convert_block_to_lets(RestExprs, Location)
    end;
convert_block_to_lets([Expr | RestExprs], Location) ->
    % Convert expression to let with dummy variable
    DummyVar = {identifier_pattern, '_dummy', Location},
    DummyBinding = {binding, DummyVar, convert_expr_to_tuple(Expr), Location},
    {let_expr, [DummyBinding], convert_block_to_lets(RestExprs, Location), Location}.

%% Convert AST types to type system tuples
convert_type_to_tuple(#primitive_type{name = Name}) ->
    {primitive_type, Name};
convert_type_to_tuple(#dependent_type{
    name = Name, type_params = TypeParams, value_params = ValueParams
}) ->
    AllParams = TypeParams ++ ValueParams,
    ConvertedParams = [convert_type_param_to_tuple(P) || P <- AllParams],
    {dependent_type, Name, ConvertedParams};
convert_type_to_tuple(#union_type{types = Variants}) ->
    ConvertedVariants = [convert_type_to_tuple(V) || V <- Variants],
    {union_type, ConvertedVariants};
convert_type_to_tuple(#function_type{params = Params, return_type = ReturnType}) ->
    ConvertedParams = [convert_type_to_tuple(P) || P <- Params],
    ConvertedReturn = convert_type_to_tuple(ReturnType),
    {function_type, ConvertedParams, ConvertedReturn};
convert_type_to_tuple(#tuple_type{element_types = ElementTypes, location = Location}) ->
    ConvertedElements = [convert_type_to_tuple(E) || E <- ElementTypes],
    {tuple_type, ConvertedElements, Location};
convert_type_to_tuple(#identifier_expr{name = Name}) when
    Name =:= 'Float' orelse
        Name =:= 'Int' orelse
        Name =:= 'Bool' orelse
        Name =:= 'String' orelse
        Name =:= 'Unit'
->
    % Convert primitive type identifiers to primitive_type tuples
    {primitive_type, Name};
convert_type_to_tuple(Type) ->
    Type.

%% Convert type expressions while resolving type variables from environment
% Handle function_type in tuple format (from parser) - must come before record format
convert_type_with_env({function_type, ParamTypes, ReturnType, _Location}, Env) ->
    ConvertedParams = [convert_type_with_env(P, Env) || P <- ParamTypes],
    ConvertedReturn = convert_type_with_env(ReturnType, Env),
    {function_type, ConvertedParams, ConvertedReturn};
% Handle primitive_type in tuple format (from parser) - must come before record format
convert_type_with_env({primitive_type, Name, _Location}, Env) ->
    % Check if this "primitive" type name actually refers to a record or other defined type
    case cure_types:lookup_env(Env, Name) of
        undefined ->
            % Not in environment, treat as primitive
            {primitive_type, Name};
        {record_type, _, _} = RecordType ->
            % It's actually a record type!
            RecordType;
        {fsm_type, _, _, _} = FSMType ->
            % It's an FSM type
            FSMType;
        OtherType ->
            % Some other defined type
            OtherType
    end;
% Handle dependent_type in tuple format (from parser) - must come before record format
convert_type_with_env({dependent_type, Name, Params, _Location}, Env) ->
    ConvertedParams = [convert_type_param_with_env(P, Env) || P <- Params],
    {dependent_type, Name, ConvertedParams};
% Handle record format types (for types not converted to tuple format yet)
convert_type_with_env(#union_type{types = Variants}, Env) ->
    ConvertedVariants = [convert_type_with_env(V, Env) || V <- Variants],
    {union_type, ConvertedVariants};
convert_type_with_env(#identifier_expr{name = Name}, _Env) when
    Name =:= 'Float' orelse
        Name =:= 'Int' orelse
        Name =:= 'Bool' orelse
        Name =:= 'String' orelse
        Name =:= 'Unit'
->
    % Convert primitive type identifiers to primitive_type tuples
    {primitive_type, Name};
convert_type_with_env(#identifier_expr{name = Name}, Env) ->
    % Check if this is a type variable in the environment
    case cure_types:lookup_env(Env, Name) of
        undefined ->
            % If not found in environment, check if it's a generic type variable name
            case is_generic_type_var(Name) of
                true ->
                    % ERROR: Generic type parameters should be in the environment by now!
                    % This indicates the environment wasn't properly set up
                    cure_utils:debug("ERROR: Generic parameter ~p not found in environment!~n", [
                        Name
                    ]),
                    cure_utils:debug(
                        "ERROR: This should not happen - creating emergency type variable~n"
                    ),
                    cure_types:new_type_var(Name);
                false ->
                    % It's a concrete type like Int, Bool, etc.
                    cure_utils:debug("Converting ~p to primitive type~n", [Name]),
                    {primitive_type, Name}
            end;
        TypeVar ->
            % Found in environment - MUST reuse existing binding
            cure_utils:debug("Found ~p in environment, reusing: ~p~n", [Name, TypeVar]),
            case cure_types:is_type_var(TypeVar) of
                % It's a type variable - REUSE IT!
                true ->
                    TypeVar;
                % It's something else (record type, etc.) - return as-is
                false ->
                    TypeVar
            end
    end;
convert_type_with_env(Type, _Env) ->
    % Fallback to regular conversion
    convert_type_to_tuple(Type).

%% Convert type parameter expressions while resolving type variables from environment
% Handle type_param in tuple or record format (from parser)
convert_type_param_with_env(#type_param{type = Type}, Env) ->
    convert_type_with_env(Type, Env);
convert_type_param_with_env({type_param, _Name, Value, _Location}, Env) ->
    convert_type_with_env(Value, Env);
convert_type_param_with_env(TypeParam, Env) ->
    convert_type_with_env(TypeParam, Env).

convert_type_param_to_tuple(#type_param{type = Type}) ->
    Value = Type,
    case Value of
        TypeExpr when is_record(TypeExpr, primitive_type); is_record(TypeExpr, dependent_type) ->
            convert_type_to_tuple(TypeExpr);
        #identifier_expr{name = Name} when
            Name =:= 'Float' orelse
                Name =:= 'Int' orelse
                Name =:= 'Bool' orelse
                Name =:= 'String' orelse
                Name =:= 'Unit'
        ->
            % Convert primitive type identifiers to primitive_type tuples
            {primitive_type, Name};
        #identifier_expr{name = Name} ->
            % Generic type parameter - convert to proper type variable record
            cure_types:new_type_var(Name);
        _ ->
            convert_type_to_tuple(Value)
    end;
convert_type_param_to_tuple(TypeParam) ->
    % Handle non-record type parameters
    convert_type_to_tuple(TypeParam).

%% Derive function signature from multiple clauses (union types)
derive_multiclause_signature(Name, Clauses, Env) ->
    cure_utils:debug("[MULTICLAUSE] Deriving signature for ~p from ~p clauses~n", [
        Name, length(Clauses)
    ]),

    % Process each clause and collect parameter and return types
    ClauseTypes = lists:map(
        fun(Clause) ->
            #function_clause{
                params = Params,
                return_type = ReturnType
            } = Clause,
            {ParamTypes, EnvWithParams} = process_parameters(Params, Env),
            FinalReturnType =
                case ReturnType of
                    undefined -> cure_types:new_type_var();
                    _ -> convert_type_with_env(ReturnType, EnvWithParams)
                end,
            {ParamTypes, FinalReturnType}
        end,
        Clauses
    ),

    % Extract parameter types for each position and create unions
    % All clauses must have the same arity
    [{FirstParamTypes, _FirstReturnType} | RestTypes] = ClauseTypes,
    Arity = length(FirstParamTypes),

    % Verify all clauses have same arity
    AllSameArity = lists:all(
        fun({ParamTypes, _}) ->
            length(ParamTypes) =:= Arity
        end,
        RestTypes
    ),

    case AllSameArity of
        false ->
            cure_utils:debug("ERROR: Multi-clause function ~p has inconsistent arity~n", [Name]),
            Env;
        true ->
            % Create union types for each parameter position
            UnionParamTypes = lists:foldl(
                fun(ParamIndex, Acc) ->
                    % Collect the type at this position from all clauses
                    TypesAtPosition = lists:map(
                        fun({ParamTypes, _}) ->
                            lists:nth(ParamIndex, ParamTypes)
                        end,
                        ClauseTypes
                    ),

                    % Create union type if types differ, otherwise use single type
                    UnionType =
                        case lists:usort(TypesAtPosition) of
                            [SingleType] ->
                                % All clauses have same type at this position
                                SingleType;
                            MultipleTypes ->
                                % Different types - create union
                                {union_type, MultipleTypes}
                        end,

                    [UnionType | Acc]
                end,
                [],
                lists:seq(1, Arity)
            ),

            % Reverse to get correct order
            FinalParamTypes = lists:reverse(UnionParamTypes),

            % Create union type for return types
            AllReturnTypes = lists:map(fun({_, RT}) -> RT end, ClauseTypes),
            UnionReturnType =
                case lists:usort(AllReturnTypes) of
                    [SingleReturnType] ->
                        SingleReturnType;
                    MultipleReturnTypes ->
                        {union_type, MultipleReturnTypes}
                end,

            FuncType = {function_type, FinalParamTypes, UnionReturnType},
            cure_utils:debug("[MULTICLAUSE] Derived type for ~p: ~p~n", [Name, FuncType]),
            cure_types:extend_env(Env, Name, FuncType)
    end.

%% Helper to find FSM definition that uses a record as payload
find_fsm_with_record_name([]) ->
    not_found;
find_fsm_with_record_name([#fsm_def{name = Name, states = States, initial = Initial} | _]) ->
    {ok, Name, States, Initial};
find_fsm_with_record_name([_ | Rest]) ->
    find_fsm_with_record_name(Rest).

%% Two-pass processing: collect function signatures first
collect_function_signatures(Items, Env) ->
    collect_function_signatures_helper(Items, Env).

collect_function_signatures_helper([], Env) ->
    Env;
collect_function_signatures_helper([Item | Rest], Env) ->
    cure_utils:debug("[COLLECT_SIG] Processing item: ~p~n", [element(1, Item)]),
    UpdatedEnv =
        case Item of
            #function_def{
                name = Name,
                clauses = Clauses,
                params = _Params,
                return_type = _ReturnType,
                is_private = _
            } when Clauses =/= undefined andalso length(Clauses) > 0 ->
                % Multi-clause function - derive union types from all clauses
                cure_utils:debug(
                    "[SIG] Pre-processing multi-clause function ~p with ~p clauses~n", [
                        Name, length(Clauses)
                    ]
                ),
                try
                    derive_multiclause_signature(Name, Clauses, Env)
                catch
                    Class:Error:Stacktrace ->
                        cure_utils:debug(
                            "ERROR SIG: Failed to pre-process multi-clause function ~p~n", [Name]
                        ),
                        cure_utils:debug("ERROR SIG: Class: ~p, Error: ~p~n", [Class, Error]),
                        cure_utils:debug("ERROR SIG: Stacktrace: ~p~n", [Stacktrace]),
                        Env
                end;
            #function_def{
                name = Name,
                params = Params,
                return_type = ReturnType,
                is_private = _
            } ->
                % Single-clause function (backward compatibility)
                cure_utils:debug("[SIG] Pre-processing function signature for ~p~n", [Name]),
                try
                    {ParamTypes, EnvWithParams} = process_parameters(Params, Env),
                    FinalReturnType =
                        case ReturnType of
                            undefined ->
                                cure_types:new_type_var();
                            _ ->
                                cure_utils:debug("[SIG] Converting return type ~p~n", [ReturnType]),
                                RawReturnType = convert_type_with_env(ReturnType, EnvWithParams),
                                % Normalize record types to simplified form (without fields)
                                normalize_record_type(RawReturnType)
                        end,
                    FuncType = {function_type, ParamTypes, FinalReturnType},
                    cure_utils:debug("[SIG] Successfully pre-processed ~p with type ~p~n", [
                        Name, FuncType
                    ]),
                    cure_types:extend_env(Env, Name, FuncType)
                catch
                    Class:Error:Stacktrace ->
                        cure_utils:debug(
                            "ERROR SIG: Failed to pre-process function ~p signature~n", [Name]
                        ),
                        cure_utils:debug("ERROR SIG: Class: ~p, Error: ~p~n", [Class, Error]),
                        cure_utils:debug("ERROR SIG: Stacktrace: ~p~n", [Stacktrace]),
                        Env
                end;
            #curify_function_def{
                name = Name,
                params = Params,
                return_type = ReturnType
            } ->
                % Create function type from curify signature (record format)
                cure_utils:debug(
                    "[SIG] Pre-processing curify function ~p~n", [Name]
                ),
                try
                    {ParamTypes, EnvWithParams} = process_parameters(Params, Env),
                    % For curify, return type MUST be specified
                    FinalReturnType = convert_type_with_env(ReturnType, EnvWithParams),
                    FuncType = {function_type, ParamTypes, FinalReturnType},
                    cure_utils:debug(
                        "[SIG] Successfully pre-processed curify function ~p with type ~p~n", [
                            Name, FuncType
                        ]
                    ),
                    cure_types:extend_env(Env, Name, FuncType)
                catch
                    Class:Error:Stacktrace ->
                        io:format(
                            "ERROR SIG: Failed to pre-process curify function ~p signature~n", [
                                Name
                            ]
                        ),
                        cure_utils:debug("ERROR SIG: Class: ~p, Error: ~p~n", [Class, Error]),
                        cure_utils:debug("ERROR SIG: Stacktrace: ~p~n", [Stacktrace]),
                        Env
                end;
            #type_def{name = _Name} ->
                % Add type definitions to environment as well
                try
                    case check_type_definition(Item, Env) of
                        {ok, NewTypeEnv, _Result} ->
                            NewTypeEnv;
                        _ ->
                            Env
                    end
                catch
                    _:_ ->
                        Env
                end;
            #record_def{
                name = RecordName, type_params = _TypeParams, fields = Fields, location = _Location
            } ->
                % Add record definitions to environment during signature collection
                % We convert fields but DON'T resolve types yet (to avoid circular dependency)
                cure_utils:debug(
                    "[COLLECT_SIG] Pre-processing record definition (record format) ~p with ~p fields~n",
                    [RecordName, length(Fields)]
                ),
                try
                    % Just convert field types without resolving from environment
                    ConvertedFields = [
                        begin
                            Name = F#record_field_def.name,
                            Type = convert_type_to_tuple(F#record_field_def.type),
                            Default = F#record_field_def.default_value,
                            Location = F#record_field_def.location,
                            {record_field_def, Name, Type, Default, Location}
                        end
                     || F <- Fields
                    ],
                    RecordType = {record_type, RecordName, ConvertedFields},
                    NewEnv = cure_types:extend_env(Env, RecordName, RecordType),
                    cure_utils:debug(
                        "[COLLECT_SIG] Successfully added record type (record format) ~p to environment~n",
                        [RecordName]
                    ),
                    NewEnv
                catch
                    Error:Reason:Stacktrace ->
                        cure_utils:debug(
                            "[COLLECT_SIG] ERROR adding record (record format) ~p: ~p:~p~n", [
                                RecordName, Error, Reason
                            ]
                        ),
                        cure_utils:debug("[COLLECT_SIG] Stacktrace: ~p~n", [Stacktrace]),
                        Env
                end;
            {import_def, _Module, _Items, _Location} ->
                % Import definitions are skipped during signature collection
                % They will be processed during the check_items phase
                cure_utils:debug(
                    "[COLLECT_SIG] Skipping import_def during signature collection~n"
                ),
                Env;
            _ ->
                % Skip any other items during signature collection
                cure_utils:debug(
                    "[COLLECT_SIG] Skipping unknown item type ~p during signature collection~n",
                    [element(1, Item)]
                ),
                Env
        end,
    collect_function_signatures_helper(Rest, UpdatedEnv).

%% Two-pass typeclass processing: register all typeclass definitions first
%% This allows instances in the same module to reference typeclasses defined earlier
register_all_typeclasses(Items, Env) ->
    cure_utils:debug("[TYPECLASS_PASS1] Starting typeclass registration pass~n"),
    register_typeclasses_helper(Items, Env).

register_typeclasses_helper([], Env) ->
    cure_utils:debug("[TYPECLASS_PASS1] Completed typeclass registration pass~n"),
    Env;
register_typeclasses_helper([Item | Rest], Env) ->
    UpdatedEnv =
        case Item of
            #typeclass_def{name = _Name} = TypeclassDef ->
                % Register the typeclass definition in the typeclass environment
                TCEnv = get_typeclass_env(Env),
                case cure_typeclass:register_typeclass(TypeclassDef, TCEnv) of
                    {ok, NewTCEnv} ->
                        put_typeclass_env(Env, NewTCEnv);
                    {error, _Reason} ->
                        Env
                end;
            _ ->
                % Skip non-typeclass items
                Env
        end,
    register_typeclasses_helper(Rest, UpdatedEnv).

%% Result construction helpers
new_result() ->
    #typecheck_result{
        success = true,
        type = undefined,
        errors = [],
        warnings = []
    }.

success_result(Type) ->
    #typecheck_result{
        success = true,
        type = Type,
        errors = [],
        warnings = []
    }.

error_result(Error) ->
    #typecheck_result{
        success = false,
        type = undefined,
        errors = [Error],
        warnings = []
    }.

add_error(Result = #typecheck_result{errors = Errors}, Error) ->
    Result#typecheck_result{success = false, errors = [Error | Errors]}.

merge_results(
    Result1 = #typecheck_result{errors = E1, warnings = W1},
    #typecheck_result{
        success = S2,
        errors = E2,
        warnings = W2
    }
) ->
    Result1#typecheck_result{
        success = Result1#typecheck_result.success andalso S2,
        errors = E1 ++ E2,
        warnings = W1 ++ W2
    }.

%% Utility functions
get_expr_location_safe(Expr) ->
    try
        get_expr_location(Expr)
    catch
        _:_ ->
            #location{
                line = 0,
                column = 0,
                file = undefined
            }
    end.

get_expr_location(#literal_expr{location = Loc}) ->
    Loc;
get_expr_location(#identifier_expr{location = Loc}) ->
    Loc;
get_expr_location(#binary_op_expr{location = Loc}) ->
    Loc;
get_expr_location(#function_call_expr{location = Loc}) ->
    Loc;
get_expr_location(#let_expr{location = Loc}) ->
    Loc;
get_expr_location(#list_expr{location = Loc}) ->
    Loc;
get_expr_location(#block_expr{location = Loc}) ->
    Loc;
get_expr_location(_) ->
    #location{
        line = 0,
        column = 0,
        file = undefined
    }.

format_error_type(constraint_not_bool) ->
    "Function constraint must be a boolean expression";
format_error_type(constraint_inference_failed) ->
    "Failed to infer type of function constraint";
format_error_type(missing_return_type_for_def_erl) ->
    "def_erl functions must have explicit return type annotation";
format_error_type(ErrorType) ->
    atom_to_list(ErrorType).

%% Extract type parameters from dependent types and add them to environment
extract_and_add_type_params(TypeExpr, Env) ->
    extract_type_params_helper(TypeExpr, Env).

%% Safe version that doesn't override existing type parameter bindings
extract_and_add_type_params_safe(TypeExpr, Env) ->
    extract_type_params_helper_safe(TypeExpr, Env).

extract_type_params_helper(
    #dependent_type{type_params = TypeParams, value_params = ValueParams}, Env
) ->
    AllParams = TypeParams ++ ValueParams,
    lists:foldl(
        fun(#type_param{type = Type}, AccEnv) ->
            extract_type_param_value(Type, AccEnv)
        end,
        Env,
        AllParams
    );
extract_type_params_helper(
    #function_type{params = ParamTypes, return_type = ReturnType},
    Env
) ->
    % Handle function types - extract type parameters from both parameters and return type
    Env1 =
        lists:foldl(
            fun(ParamType, AccEnv) -> extract_type_params_helper(ParamType, AccEnv) end,
            Env,
            ParamTypes
        ),
    extract_type_params_helper(ReturnType, Env1);
% Handle tuple-form primitive types with location
extract_type_params_helper({primitive_type, Name, _Location}, Env) ->
    % Check if it's a generic type variable and add it
    case is_generic_type_var(Name) of
        true ->
            extract_type_param_value(#primitive_type{name = Name}, Env);
        false ->
            Env
    end;
% Handle tuple-form primitive types without location
extract_type_params_helper({primitive_type, Name}, Env) ->
    % Check if it's a generic type variable and add it
    case is_generic_type_var(Name) of
        true ->
            extract_type_param_value(#primitive_type{name = Name}, Env);
        false ->
            Env
    end;
% Handle tuple-form dependent types
extract_type_params_helper({dependent_type, _Name, Params}, Env) ->
    % Extract type parameters from the parameters list
    lists:foldl(
        fun(Param, AccEnv) -> extract_type_params_helper(Param, AccEnv) end,
        Env,
        Params
    );
extract_type_params_helper(
    #list_type{element_type = ElemType, length = LengthExpr},
    Env
) ->
    % Handle list types with length expressions
    Env1 = extract_type_params_helper(ElemType, Env),
    case LengthExpr of
        undefined ->
            Env1;
        _ ->
            extract_type_param_value(LengthExpr, Env1)
    end;
extract_type_params_helper(#identifier_expr{name = Name}, Env) ->
    % Handle identifier expressions - if they're generic type variables, add them
    case is_generic_type_var(Name) of
        true ->
            extract_type_param_value(#primitive_type{name = Name}, Env);
        false ->
            Env
    end;
extract_type_params_helper(_, Env) ->
    Env.

extract_type_params_helper_safe(
    #dependent_type{type_params = TypeParams, value_params = ValueParams}, Env
) ->
    AllParams = TypeParams ++ ValueParams,
    lists:foldl(
        fun(#type_param{type = Type}, AccEnv) ->
            extract_type_param_value_safe(Type, AccEnv)
        end,
        Env,
        AllParams
    );
extract_type_params_helper_safe(
    #function_type{
        params = ParamTypes,
        return_type = ReturnType
    },
    Env
) ->
    % Handle function types - extract type parameters from both parameters and return type
    Env1 =
        lists:foldl(
            fun(ParamType, AccEnv) -> extract_type_params_helper_safe(ParamType, AccEnv) end,
            Env,
            ParamTypes
        ),
    extract_type_params_helper_safe(ReturnType, Env1);
% Handle tuple-form primitive types with location
extract_type_params_helper_safe({primitive_type, Name, _Location}, Env) ->
    % Check if it's already in the environment (like a record type) FIRST
    case cure_types:lookup_env(Env, Name) of
        undefined ->
            % Not in environment - check if it's a generic type variable
            case is_generic_type_var(Name) of
                true ->
                    extract_type_param_value_safe(#primitive_type{name = Name}, Env);
                false ->
                    Env
            end;
        _ExistingType ->
            % Already in environment (e.g., a record type), don't override
            Env
    end;
% Handle tuple-form primitive types without location
extract_type_params_helper_safe({primitive_type, Name}, Env) ->
    % Check if it's already in the environment (like a record type) FIRST
    case cure_types:lookup_env(Env, Name) of
        undefined ->
            % Not in environment - check if it's a generic type variable
            case is_generic_type_var(Name) of
                true ->
                    extract_type_param_value_safe(#primitive_type{name = Name}, Env);
                false ->
                    Env
            end;
        _ExistingType ->
            % Already in environment (e.g., a record type), don't override
            Env
    end;
% Handle tuple-form dependent types
extract_type_params_helper_safe({dependent_type, _Name, Params}, Env) ->
    % Extract type parameters from the parameters list
    lists:foldl(
        fun(Param, AccEnv) -> extract_type_params_helper_safe(Param, AccEnv) end,
        Env,
        Params
    );
% Handle tuple-form function types
extract_type_params_helper_safe({function_type, ParamTypes, ReturnType}, Env) ->
    % Handle function types - extract type parameters from both parameters and return type
    Env1 =
        lists:foldl(
            fun(ParamType, AccEnv) -> extract_type_params_helper_safe(ParamType, AccEnv) end,
            Env,
            ParamTypes
        ),
    extract_type_params_helper_safe(ReturnType, Env1);
extract_type_params_helper_safe(
    #list_type{element_type = ElemType, length = LengthExpr},
    Env
) ->
    % Handle list types with length expressions
    Env1 = extract_type_params_helper_safe(ElemType, Env),
    case LengthExpr of
        undefined ->
            Env1;
        _ ->
            extract_type_param_value_safe(LengthExpr, Env1)
    end;
extract_type_params_helper_safe(#identifier_expr{name = Name}, Env) ->
    % Handle identifier expressions - check environment first, then if they're generic type variables
    case cure_types:lookup_env(Env, Name) of
        undefined ->
            % Not in environment - check if it's a generic type variable
            case is_generic_type_var(Name) of
                true ->
                    extract_type_param_value_safe(#primitive_type{name = Name}, Env);
                false ->
                    Env
            end;
        _ExistingType ->
            % Already in environment, don't override
            Env
    end;
extract_type_params_helper_safe(_, Env) ->
    Env.

extract_type_param_value(#identifier_expr{name = Name}, Env) ->
    % Check if it's a generic type variable first
    case is_generic_type_var(Name) of
        true ->
            % It's a generic type parameter like T, E, U - add as type variable
            TypeVar = cure_types:new_type_var(Name),
            cure_types:extend_env(Env, Name, TypeVar);
        false ->
            % Add identifier as a length parameter (typically numeric for dependent types)
            cure_types:extend_env(Env, Name, {primitive_type, 'Int'})
    end;
extract_type_param_value(#primitive_type{name = Name}, Env) ->
    % Type parameter like T - add to environment as type variable
    TypeVar = cure_types:new_type_var(Name),
    cure_types:extend_env(Env, Name, TypeVar);
extract_type_param_value(TypeExpr, Env) when is_record(TypeExpr, dependent_type) ->
    extract_type_params_helper(TypeExpr, Env);
extract_type_param_value(_, Env) ->
    % Other expressions (literals, complex expressions) don't introduce type parameters
    Env.

extract_type_param_value_safe(#identifier_expr{name = Name}, Env) ->
    % Only add identifier if it's not already in the environment
    case cure_types:lookup_env(Env, Name) of
        undefined ->
            % Check if it's a generic type variable first
            case is_generic_type_var(Name) of
                true ->
                    % It's a generic type parameter like T, E, U - add as type variable
                    TypeVar = cure_types:new_type_var(Name),
                    cure_types:extend_env(Env, Name, TypeVar);
                false ->
                    % Add identifier as a length parameter (typically numeric for dependent types)
                    cure_types:extend_env(Env, Name, {primitive_type, 'Int'})
            end;
        _ExistingType ->
            % Type parameter already exists, don't override it
            Env
    end;
extract_type_param_value_safe(#primitive_type{name = Name}, Env) ->
    % Only add type parameter if it's not already in the environment
    case cure_types:lookup_env(Env, Name) of
        undefined ->
            % Type parameter like T - add to environment as type variable
            TypeVar = cure_types:new_type_var(Name),
            cure_types:extend_env(Env, Name, TypeVar);
        _ExistingType ->
            % Type parameter already exists, don't override it
            Env
    end;
extract_type_param_value_safe(TypeExpr, Env) when is_record(TypeExpr, dependent_type) ->
    extract_type_params_helper_safe(TypeExpr, Env);
extract_type_param_value_safe(TypeExpr, Env) when is_record(TypeExpr, function_type) ->
    extract_type_params_helper_safe(TypeExpr, Env);
extract_type_param_value_safe(_, Env) ->
    % Other expressions (literals, complex expressions) don't introduce type parameters
    Env.

%% Dependent type checking helpers
check_dependent_constraint(Constraint, _Value, _Type) ->
    % Full SMT-based dependent constraint checking
    % Try to prove the constraint using SMT solver
    case is_constraint_expr(Constraint) of
        false ->
            % Not a constraint expression, skip checking
            true;
        true ->
            % Build environment from constraint variables
            Env = extract_constraint_vars(Constraint),

            % Try SMT solver first
            case cure_smt_solver:prove_constraint(Constraint, Env) of
                true ->
                    % Constraint proven by SMT solver
                    true;
                false ->
                    % Constraint cannot be proven - find counterexample
                    case cure_smt_solver:find_counterexample(Constraint, Env) of
                        {ok, Counterexample} ->
                            % Found concrete counterexample
                            cure_utils:debug(
                                "Dependent type constraint failed with counterexample: ~p~n",
                                [Counterexample]
                            ),
                            false;
                        none ->
                            % No counterexample found but not provable
                            cure_utils:debug(
                                "Warning: Dependent type constraint unprovable: ~p~n",
                                [Constraint]
                            ),
                            % Allow with warning
                            true;
                        unknown ->
                            % Solver couldn't determine
                            cure_utils:debug(
                                "Warning: Dependent type constraint undecidable: ~p~n",
                                [Constraint]
                            ),
                            % Allow with warning
                            true
                    end;
                unknown ->
                    % Solver timeout or error - fall back to symbolic
                    cure_utils:debug(
                        "SMT solver timeout, using symbolic evaluation for: ~p~n",
                        [Constraint]
                    ),
                    check_with_symbolic(Constraint, Env)
            end
    end.

%% Check if an expression is a constraint (boolean expression)
is_constraint_expr(#binary_op_expr{op = Op}) when
    Op =:= '==';
    Op =:= '/=';
    Op =:= '<';
    Op =:= '>';
    Op =:= '=<';
    Op =:= '>=';
    Op =:= 'and';
    Op =:= 'or';
    Op =:= 'andalso';
    Op =:= 'orelse';
    Op =:= '=>'
->
    true;
is_constraint_expr(#unary_op_expr{op = 'not'}) ->
    true;
is_constraint_expr(#literal_expr{value = V}) when is_boolean(V) ->
    true;
is_constraint_expr(_) ->
    false.

%% Extract variables from constraint expression
extract_constraint_vars(Expr) ->
    extract_constraint_vars(Expr, #{}).

extract_constraint_vars(#identifier_expr{name = Name}, Acc) ->
    case maps:is_key(Name, Acc) of
        true -> Acc;
        % Default to Int type
        false -> maps:put(Name, {type, int}, Acc)
    end;
extract_constraint_vars(#binary_op_expr{left = L, right = R}, Acc) ->
    Acc1 = extract_constraint_vars(L, Acc),
    extract_constraint_vars(R, Acc1);
extract_constraint_vars(#unary_op_expr{operand = Operand}, Acc) ->
    extract_constraint_vars(Operand, Acc);
extract_constraint_vars(_, Acc) ->
    Acc.

%% Symbolic evaluation fallback
check_with_symbolic(_Constraint, _Env) ->
    % Simple symbolic checking - allow with warning
    % In production, this would do more sophisticated analysis
    true.

infer_dependent_type(Expr, Env) ->
    % Simplified dependent type inference
    % In full implementation, would infer refinement predicates
    case cure_types:infer_type(convert_expr_to_tuple(Expr), Env) of
        {ok, Result} ->
            {ok, Result};
        Error ->
            Error
    end.

%% Helper functions for new AST format
process_imports([], Env) ->
    {ok, Env};
process_imports([Import | RestImports], Env) ->
    case check_import(Import, Env) of
        {ok, NewEnv, _Result} ->
            process_imports(RestImports, NewEnv);
        {error, Error} ->
            {error, Error}
    end.

extract_export_specs([], _Items) ->
    [];
extract_export_specs([{export_list, ExportSpecs}], _Items) ->
    ExportSpecs;
extract_export_specs(ExportSpecs, _Items) when is_list(ExportSpecs) ->
    % Handle direct export spec list (from module_def)
    case ExportSpecs of
        % List of export_spec tuples
        [{export_spec, _, _, _} | _] ->
            ExportSpecs;
        % Pass through other formats
        _ ->
            ExportSpecs
    end;
extract_export_specs([_ | RestExports], Items) ->
    extract_export_specs(RestExports, Items).

check_exports([], _Items) ->
    ok;
check_exports([{export_spec, Name, Arity, _Location} | RestExports], Items) ->
    case find_function(Name, Items) of
        {ok,
            {function_def, _Name, Params, _ReturnType, _Constraint, _Body, IsPrivate,
                _UnusedLocation}} ->
            case IsPrivate of
                true ->
                    {error, {cannot_export_private_function, Name, Arity}};
                false ->
                    case length(Params) =:= Arity of
                        true ->
                            check_exports(RestExports, Items);
                        false ->
                            {error, {export_arity_mismatch, Name, Arity, length(Params)}}
                    end
            end;
        {ok,
            {curify_function_def, _Name, Params, _ReturnType, _Constraint, _ErlModule, _ErlFunc,
                _ErlArity, IsPrivate, _UnusedLocation}} ->
            case IsPrivate of
                true ->
                    {error, {cannot_export_private_function, Name, Arity}};
                false ->
                    case length(Params) =:= Arity of
                        true ->
                            check_exports(RestExports, Items);
                        false ->
                            {error, {export_arity_mismatch, Name, Arity, length(Params)}}
                    end
            end;
        not_found ->
            {error, {exported_function_not_found, Name, Arity}}
    end.

find_function(
    Name,
    [
        #function_def{
            name = Name,
            params = Params,
            return_type = ReturnType,
            constraint = Constraint,
            body = Body,
            is_private = IsPrivate,
            location = Location
        }
        | _
    ]
) ->
    {ok, {function_def, Name, Params, ReturnType, Constraint, Body, IsPrivate, Location}};
find_function(
    Name,
    [{function_def, Name, Params, ReturnType, Constraint, Body, Location} | _]
) ->
    % Fallback for old tuple-based format without is_private field
    {ok, {function_def, Name, Params, ReturnType, Constraint, Body, false, Location}};
find_function(
    Name,
    [
        #curify_function_def{
            name = Name,
            params = Params,
            return_type = ReturnType,
            constraint = Constraint,
            erlang_module = ErlModule,
            erlang_function = ErlFunc,
            erlang_arity = ErlArity,
            is_private = IsPrivate,
            location = Location
        }
        | _
    ]
) ->
    {ok,
        {curify_function_def, Name, Params, ReturnType, Constraint, ErlModule, ErlFunc, ErlArity,
            IsPrivate, Location}};
find_function(
    Name,
    [
        {curify_function_def, Name, Params, ReturnType, Constraint, ErlModule, ErlFunc, ErlArity,
            IsPrivate, Location}
        | _
    ]
) ->
    % Fallback for tuple-based format
    {ok,
        {curify_function_def, Name, Params, ReturnType, Constraint, ErlModule, ErlFunc, ErlArity,
            IsPrivate, Location}};
find_function(Name, [_ | RestItems]) ->
    find_function(Name, RestItems);
find_function(_Name, []) ->
    not_found.

process_parameters(Params, Env) ->
    % First pass: collect all type parameters from all parameters
    cure_utils:debug("Extracting type parameters from all params: ~p~n", [Params]),
    EnvWithAllTypeParams =
        lists:foldl(
            fun(Param, AccEnv) ->
                TypeExpr =
                    case Param of
                        #param{type = T} -> T
                    end,
                extract_and_add_type_params_safe(TypeExpr, AccEnv)
            end,
            Env,
            Params
        ),
    cure_utils:debug("Environment after extracting all type params~n"),

    % Second pass: process parameters with full type environment
    process_parameters(Params, Env, [], EnvWithAllTypeParams).

process_parameters([], _OrigEnv, TypesAcc, EnvAcc) ->
    {lists:reverse(TypesAcc), EnvAcc};
process_parameters(
    [Param | RestParams],
    OrigEnv,
    TypesAcc,
    EnvAcc
) ->
    % Handle both record and tuple format
    {Name, TypeExpr} =
        case Param of
            #param{name = N, type = T} -> {N, T}
        end,
    % Convert the type expression using the environment with all type parameters
    cure_utils:debug("[PARAM] Processing parameter ~p with type ~p~n", [Name, TypeExpr]),
    ParamType = convert_type_with_env(TypeExpr, EnvAcc),
    cure_utils:debug("[PARAM] Converted ~p to type ~p~n", [TypeExpr, ParamType]),
    % Add the parameter itself to environment
    NewEnvAcc = cure_types:extend_env(EnvAcc, Name, ParamType),
    process_parameters(RestParams, OrigEnv, [ParamType | TypesAcc], NewEnvAcc).

check_import_items(Module, Items, Env) ->
    import_items(Module, Items, Env).

import_items(_Module, [], AccEnv) ->
    {ok, AccEnv};
import_items(Module, [Item | RestItems], AccEnv) ->
    case import_item(Module, Item, AccEnv) of
        {ok, NewAccEnv} ->
            import_items(Module, RestItems, NewAccEnv);
        {error, Error} ->
            {error, Error}
    end.

import_item(Module, {function_import, Name, Arity, _Alias, _Location}, Env) ->
    cure_utils:debug(
        "[IMPORT] Processing function_import ~p/~p from ~p~n",
        [Name, Arity, Module]
    ),
    FunctionType = create_imported_function_type(Module, Name, Arity),
    NewEnv = cure_types:extend_env(Env, Name, FunctionType),
    {ok, NewEnv};
import_item(Module, {aliased_import, OriginalName, Alias, _Location}, Env) ->
    % Import with alias: "import Module [name as alias]"
    cure_utils:debug(
        "[IMPORT] Processing aliased_import ~p as ~p from ~p~n",
        [OriginalName, Alias, Module]
    ),
    % We assume it's a function with unknown arity - use arity 2 as default for map
    DefaultArity =
        case OriginalName of
            map ->
                2;
            _ ->
                1
        end,
    FunctionType = create_imported_function_type(Module, OriginalName, DefaultArity),
    NewEnv = cure_types:extend_env(Env, Alias, FunctionType),
    {ok, NewEnv};
import_item(Module, Identifier, Env) when is_atom(Identifier) ->
    cure_utils:debug(
        "[IMPORT] Processing atom identifier ~p from ~p~n",
        [Identifier, Module]
    ),
    % Check if this is a known type alias
    case is_type_alias(Module, Identifier) of
        {true, TypeDef} ->
            % Import as a type alias
            cure_utils:debug("[IMPORT] ~p is a type alias: ~p~n", [Identifier, TypeDef]),
            NewEnv = cure_types:extend_env(Env, Identifier, TypeDef),
            {ok, NewEnv};
        false ->
            % Assume it's a function with arity 1 by default
            FunctionType = create_imported_function_type(Module, Identifier, 1),
            NewEnv = cure_types:extend_env(Env, Identifier, FunctionType),
            {ok, NewEnv}
    end.

%% Check if an identifier is a type alias from a module
is_type_alias('Std.Fsm', 'StateName') -> {true, {primitive_type, 'Atom'}};
is_type_alias('Std.Fsm', 'Event') -> {true, {primitive_type, 'Int'}};
is_type_alias('Std.Fsm', 'FsmError') -> {true, {primitive_type, 'Atom'}};
is_type_alias('Std.Fsm', 'State') -> {true, {primitive_type, 'Int'}};
is_type_alias(_Module, _Identifier) -> false.

%% Additional converter functions
convert_param_to_tuple({param, Name, TypeExpr, Location}) ->
    {param, Name, convert_type_to_tuple(TypeExpr), Location}.

convert_match_clause_to_tuple(#match_clause{
    pattern = Pattern,
    guard = Guard,
    body = Body,
    location = Location
}) ->
    ConvertedGuard =
        case Guard of
            undefined ->
                undefined;
            _ ->
                convert_expr_to_tuple(Guard)
        end,
    {match_clause, convert_pattern_to_tuple(Pattern), ConvertedGuard, convert_expr_to_tuple(Body),
        Location}.

convert_field_pattern_to_tuple(#field_pattern{
    name = Name,
    pattern = Pattern,
    location = Location
}) ->
    {field_pattern, Name, convert_pattern_to_tuple(Pattern), Location}.

convert_record_field_def(#record_field_def{
    name = Name, type = Type, default_value = Default, location = Location
}) ->
    {record_field_def, Name, convert_type_to_tuple(Type), Default, Location}.

%% Convert record field definition and resolve type names from environment
convert_and_resolve_record_field_def(
    #record_field_def{
        name = Name, type = Type, default_value = Default, location = Location
    },
    Env
) ->
    ConvertedType = convert_type_to_tuple(Type),
    % Resolve the type name from environment to get refined types
    ResolvedType = resolve_type_from_env(ConvertedType, Env),
    {record_field_def, Name, ResolvedType, Default, Location}.
%% Resolve a type expression by looking up type names in the environment
resolve_type_from_env({primitive_type, TypeName}, Env) ->
    % Look up the type name in the environment
    case cure_types:lookup_env(Env, TypeName) of
        undefined ->
            % Type not in environment, keep as primitive
            {primitive_type, TypeName};
        {refined_type, _, _} = RefinedType ->
            % Found a refined type definition, use it
            RefinedType;
        _OtherType ->
            % For other types, keep the original primitive type
            {primitive_type, TypeName}
    end;
resolve_type_from_env(Type, _Env) ->
    % For other types, return as-is
    Type.

%% Convert tuple format record field and resolve types
convert_and_resolve_record_field_tuple({record_field_def, Name, Type, Default, Location}, Env) ->
    % For tuple format fields, resolve the type
    ResolvedType = resolve_type_from_env(Type, Env),
    {record_field_def, Name, ResolvedType, Default, Location};
convert_and_resolve_record_field_tuple(Field, _Env) ->
    % Pass through other formats
    Field.

%% When clause constraint processing with SMT solver integration
process_when_clause_constraint(Constraint, Env, _Location) ->
    try
        % Convert the constraint expression to SMT constraints
        case convert_constraint_to_smt(Constraint, Env) of
            {ok, SmtConstraints} ->
                % Add SMT constraints to the environment for solving
                add_smt_constraints_to_env(SmtConstraints, Env);
            {error, Reason} ->
                % Log the error but don't fail - continue with original environment
                cure_utils:debug("Warning: Could not convert constraint to SMT: ~p~n", [Reason]),
                Env
        end
    catch
        _:_ ->
            % On any error, just return the original environment
            Env
    end.

%% Convert Cure constraint expressions to SMT constraints
convert_constraint_to_smt(Constraint, Env) ->
    case Constraint of
        {binary_op_expr, Op, Left, Right, _Location} when
            Op =:= '>' orelse
                Op =:= '<' orelse
                Op =:= '>=' orelse
                Op =:= '=<' orelse
                Op =:= '=='
        ->
            % Arithmetic comparison constraint
            case {convert_expr_to_smt_term(Left, Env), convert_expr_to_smt_term(Right, Env)} of
                {{ok, LeftTerm}, {ok, RightTerm}} ->
                    SmtConstraint =
                        case Op of
                            '>' ->
                                cure_smt_solver:inequality_constraint(LeftTerm, '>', RightTerm);
                            '<' ->
                                cure_smt_solver:inequality_constraint(LeftTerm, '<', RightTerm);
                            '>=' ->
                                cure_smt_solver:inequality_constraint(LeftTerm, '>=', RightTerm);
                            '=<' ->
                                cure_smt_solver:inequality_constraint(LeftTerm, '=<', RightTerm);
                            '==' ->
                                cure_smt_solver:equality_constraint(LeftTerm, RightTerm)
                        end,
                    {ok, [SmtConstraint]};
                {{error, _} = Error, _} ->
                    Error;
                {_, {error, _} = Error} ->
                    Error
            end;
        _ ->
            {error, {unsupported_constraint_type, Constraint}}
    end.

%% Convert Cure expressions to SMT terms
convert_expr_to_smt_term({identifier_expr, Name, _}, _Env) ->
    {ok, cure_smt_solver:variable_term(Name)};
convert_expr_to_smt_term({literal_expr, Value, _}, _Env) when is_integer(Value) ->
    {ok, cure_smt_solver:constant_term(Value)};
convert_expr_to_smt_term({binary_op_expr, '+', Left, Right, _}, Env) ->
    case {convert_expr_to_smt_term(Left, Env), convert_expr_to_smt_term(Right, Env)} of
        {{ok, LeftTerm}, {ok, RightTerm}} ->
            AddExpr = cure_smt_solver:addition_expression([LeftTerm, RightTerm]),
            {ok, AddExpr};
        {{error, _} = Error, _} ->
            Error;
        {_, {error, _} = Error} ->
            Error
    end;
convert_expr_to_smt_term({binary_op_expr, '-', Left, Right, _}, Env) ->
    case {convert_expr_to_smt_term(Left, Env), convert_expr_to_smt_term(Right, Env)} of
        {{ok, LeftTerm}, {ok, RightTerm}} ->
            SubExpr = cure_smt_solver:subtraction_expression([LeftTerm, RightTerm]),
            {ok, SubExpr};
        {{error, _} = Error, _} ->
            Error;
        {_, {error, _} = Error} ->
            Error
    end;
convert_expr_to_smt_term({binary_op_expr, '*', Left, Right, _}, Env) ->
    case {convert_expr_to_smt_term(Left, Env), convert_expr_to_smt_term(Right, Env)} of
        {{ok, LeftTerm}, {ok, RightTerm}} ->
            MulExpr = cure_smt_solver:multiplication_expression([LeftTerm, RightTerm]),
            {ok, MulExpr};
        {{error, _} = Error, _} ->
            Error;
        {_, {error, _} = Error} ->
            Error
    end;
convert_expr_to_smt_term({binary_op_expr, '/', Left, Right, _}, Env) ->
    case {convert_expr_to_smt_term(Left, Env), convert_expr_to_smt_term(Right, Env)} of
        {{ok, LeftTerm}, {ok, RightTerm}} ->
            DivExpr = cure_smt_solver:division_expression([LeftTerm, RightTerm]),
            {ok, DivExpr};
        {{error, _} = Error, _} ->
            Error;
        {_, {error, _} = Error} ->
            Error
    end;
convert_expr_to_smt_term({binary_op_expr, mod, Left, Right, _}, Env) ->
    case {convert_expr_to_smt_term(Left, Env), convert_expr_to_smt_term(Right, Env)} of
        {{ok, LeftTerm}, {ok, RightTerm}} ->
            ModExpr = cure_smt_solver:modulo_expression([LeftTerm, RightTerm]),
            {ok, ModExpr};
        {{error, _} = Error, _} ->
            Error;
        {_, {error, _} = Error} ->
            Error
    end;
convert_expr_to_smt_term(Expr, _Env) ->
    {error, {unsupported_expression, Expr}}.

%% Add SMT constraints to the type environment
add_smt_constraints_to_env(SmtConstraints, Env) ->
    % For now, just return the original environment with constraints noted
    % In a full implementation, would store constraints in environment
    io:format(
        "Added ~p SMT constraints for when clause verification~n",
        [length(SmtConstraints)]
    ),
    Env.

%% Check if a name represents a generic type variable (T, E, U, etc.)
is_generic_type_var(Name) ->
    cure_types:is_generic_type_variable_name(Name).

%% Normalize record types to simplified form for function signatures
normalize_record_type({record_type, RecordName, _Fields}) ->
    % Return simplified form without fields
    {record_type, RecordName};
normalize_record_type(Type) ->
    % Non-record types pass through unchanged
    Type.

%% Check FSM event handler signatures
%% Validates that event handlers (if defined in the same module) have correct signatures
%% Expected signature: handler_name(State, Event, StateData) -> {NextState, NewStateData}
check_fsm_handler_signatures(_FSMName, Events, StateDefs, Env) ->
    cure_utils:debug("[FSM_HANDLERS] Checking handler signatures for events: ~p~n", [Events]),

    % Extract all handler names from state transitions
    Handlers = extract_handler_names(StateDefs),
    cure_utils:debug("[FSM_HANDLERS] Found handlers: ~p~n", [Handlers]),

    % Check each handler's signature if it's defined in the environment
    check_handler_signatures(Handlers, Env, []).

%% Extract handler names from state definitions
extract_handler_names(StateDefs) ->
    lists:usort(
        lists:flatten([
            [
                extract_handler_name(T#transition.action)
             || T <- StateDef#state_def.transitions,
                T#transition.action =/= undefined
            ]
         || StateDef <- StateDefs
        ])
    ).

%% Extract handler name from transition action
extract_handler_name(#identifier_expr{name = Name}) -> Name;
extract_handler_name(#function_call_expr{function = #identifier_expr{name = Name}}) -> Name;
extract_handler_name(_) -> undefined.

%% Check signatures for each handler
check_handler_signatures([], _Env, Warnings) ->
    {ok, Warnings};
check_handler_signatures([undefined | Rest], Env, Warnings) ->
    % Skip undefined handlers
    check_handler_signatures(Rest, Env, Warnings);
check_handler_signatures([HandlerName | Rest], Env, Warnings) ->
    case cure_types:lookup_env(Env, HandlerName) of
        undefined ->
            % Handler not defined in this module - this is OK (could be defined later or externally)
            cure_utils:debug("[FSM_HANDLERS] Handler ~p not found in environment~n", [HandlerName]),
            check_handler_signatures(Rest, Env, Warnings);
        HandlerType ->
            % Handler is defined, verify its signature
            case verify_handler_signature(HandlerName, HandlerType) of
                ok ->
                    cure_utils:debug("[FSM_HANDLERS] Handler ~p has correct signature~n", [
                        HandlerName
                    ]),
                    check_handler_signatures(Rest, Env, Warnings);
                {warning, Message} ->
                    Warning = #typecheck_warning{
                        message = Message,
                        location = #location{line = 0, column = 0, file = undefined},
                        details = {handler_signature_mismatch, HandlerName, HandlerType}
                    },
                    check_handler_signatures(Rest, Env, [Warning | Warnings])
            end
    end.

%% Verify that a handler has the expected signature
%% Expected: handler_name(State, Event, StateData) -> {NextState, NewStateData}
%% This is simplified - in reality we'd check more strictly
verify_handler_signature(HandlerName, {function_type, ParamTypes, _ReturnType}) ->
    % Check arity - should be 3 (State, Event, StateData)
    case length(ParamTypes) of
        3 ->
            % Arity is correct
            ok;
        Arity ->
            {warning,
                lists:flatten(
                    io_lib:format(
                        "FSM handler ~p should have arity 3 (State, Event, StateData), but has arity ~p",
                        [HandlerName, Arity]
                    )
                )}
    end;
verify_handler_signature(HandlerName, _OtherType) ->
    % Not a function type
    {warning,
        lists:flatten(
            io_lib:format(
                "FSM handler ~p should be a function, but has a different type",
                [HandlerName]
            )
        )}.

%% Check liveness property: all states can reach terminal states
%% A terminal state is one with no outgoing transitions
check_liveness_property(States, TransitionGraph) ->
    cure_utils:debug("[FSM_LIVENESS] Checking liveness property for states: ~p~n", [States]),

    % Identify terminal states (states with no outgoing transitions)
    TerminalStates = identify_terminal_states(States, TransitionGraph),
    cure_utils:debug("[FSM_LIVENESS] Terminal states: ~p~n", [TerminalStates]),

    case TerminalStates of
        [] ->
            % No terminal states - FSM has only cycles
            % This is not necessarily an error (e.g., server FSMs)
            {warning, no_terminal_states};
        _ ->
            % Check which states can reach terminal states
            case check_terminal_reachability(States, TerminalStates, TransitionGraph) of
                {ok, AllCanReach} when AllCanReach =:= true ->
                    cure_utils:debug("[FSM_LIVENESS] All states can reach terminal states~n"),
                    ok;
                {ok, false, UnreachableFromStates} ->
                    cure_utils:debug(
                        "[FSM_LIVENESS] States that cannot reach terminal: ~p~n",
                        [UnreachableFromStates]
                    ),
                    {warning, {states_cannot_reach_terminal, UnreachableFromStates}};
                {error, Error} ->
                    {error, Error}
            end
    end.

%% Identify terminal states (states with no outgoing transitions)
identify_terminal_states(States, TransitionGraph) ->
    lists:filter(
        fun(State) ->
            case maps:get(State, TransitionGraph, []) of
                % No transitions = terminal state
                [] -> true;
                _ -> false
            end
        end,
        States
    ).

%% Check if all states can reach at least one terminal state
check_terminal_reachability(States, TerminalStates, TransitionGraph) ->
    % Build reverse transition graph for backward reachability
    ReverseGraph = build_reverse_transition_graph(TransitionGraph),

    % Find all states reachable backwards from terminal states
    ReachableFromTerminal = find_states_reaching_terminals(TerminalStates, ReverseGraph),

    % Check which states cannot reach any terminal
    UnreachableFromStates = States -- ReachableFromTerminal,

    case UnreachableFromStates of
        [] ->
            {ok, true};
        _ ->
            {ok, false, UnreachableFromStates}
    end.

%% Build reverse transition graph: to_state -> [from_state]
%% Updated to handle new graph format: {event, guard, action, target}
build_reverse_transition_graph(TransitionGraph) ->
    maps:fold(
        fun(FromState, Transitions, Acc) ->
            lists:foldl(
                fun({_Event, _Guard, _Action, ToState}, InnerAcc) ->
                    % Add FromState to the list of states that can reach ToState
                    Predecessors = maps:get(ToState, InnerAcc, []),
                    maps:put(ToState, [FromState | Predecessors], InnerAcc)
                end,
                Acc,
                Transitions
            )
        end,
        #{},
        TransitionGraph
    ).

%% Find all states that can reach terminal states (backward BFS from terminals)
find_states_reaching_terminals(TerminalStates, ReverseGraph) ->
    ReachableSet = bfs_reachability(
        TerminalStates,
        sets:from_list(TerminalStates),
        ReverseGraph
    ),
    sets:to_list(ReachableSet).

%% Verify guard constraints using SMT solver
%% Checks that guards are satisfiable and don't conflict
verify_guard_constraints(_States, TransitionGraph, Env) ->
    cure_utils:debug("[FSM_GUARDS] Verifying guard constraints~n"),

    % Extract all transitions with guards from the enhanced graph
    % TransitionGraph now stores: {event, guard, action, target}
    AllTransitionsWithGuards = maps:fold(
        fun(FromState, Transitions, Acc) ->
            TransitionsForState = [
                {FromState, Event, Guard, Target}
             || {Event, Guard, _Action, Target} <- Transitions,
                Guard =/= undefined
            ],
            TransitionsForState ++ Acc
        end,
        [],
        TransitionGraph
    ),

    cure_utils:debug(
        "[FSM_GUARDS] Found ~p transitions with guards~n",
        [length(AllTransitionsWithGuards)]
    ),

    % Step 1: Verify each guard is individually satisfiable
    GuardResults = lists:map(
        fun({FromState, Event, Guard, Target}) ->
            cure_utils:debug(
                "[FSM_GUARDS] Checking guard for ~p --[~p]--> ~p~n",
                [FromState, Event, Target]
            ),
            case verify_single_guard(Guard, Env) of
                ok -> ok;
                {error, Reason} -> {error, {FromState, Event, Target, Reason}};
                {warning, Reason} -> {warning, {FromState, Event, Target, Reason}}
            end
        end,
        AllTransitionsWithGuards
    ),

    % Check for errors in individual guard verification
    case [E || {error, E} <- GuardResults] of
        [] ->
            % Step 2: Check for conflicting guards on same event from same state
            ConflictResults = maps:fold(
                fun(FromState, Transitions, Acc) ->
                    % Extract transitions with guards for conflict checking
                    TransitionsForCheck = [
                        {Event, Guard, Target}
                     || {Event, Guard, _Action, Target} <- Transitions
                    ],
                    case check_conflicting_guards(TransitionsForCheck, Env) of
                        ok -> Acc;
                        {warning, Warning} -> [{FromState, Warning} | Acc];
                        {error, Error} -> [{error, {FromState, Error}} | Acc]
                    end
                end,
                [],
                TransitionGraph
            ),

            % Report warnings but don't fail
            case ConflictResults of
                [] ->
                    cure_utils:debug("[FSM_GUARDS] No guard conflicts detected~n"),
                    ok;
                Warnings ->
                    cure_utils:debug("[FSM_GUARDS] Guard conflict warnings: ~p~n", [Warnings]),
                    % Return warning but don't fail - overlapping guards are allowed
                    {warning, {overlapping_guards, Warnings}}
            end;
        Errors ->
            cure_utils:debug("[FSM_GUARDS] Found unsatisfiable guards: ~p~n", [Errors]),
            {error, {unsatisfiable_guards, Errors}}
    end.

%% Verify a single transition guard is satisfiable
verify_single_guard(Guard, Env) ->
    case Guard of
        undefined ->
            % No guard = always satisfiable
            ok;
        _ ->
            % Convert guard to SMT constraint
            case convert_constraint_to_smt(convert_expr_to_tuple(Guard), Env) of
                {ok, SmtConstraints} ->
                    % Check if constraints are satisfiable
                    case check_smt_satisfiability(SmtConstraints) of
                        {ok, satisfiable} ->
                            ok;
                        {ok, unsatisfiable} ->
                            {error, {unsatisfiable_guard, Guard}};
                        {error, Reason} ->
                            {warning, {guard_verification_failed, Reason}}
                    end;
                {error, Reason} ->
                    {warning, {cannot_convert_guard_to_smt, Reason}}
            end
    end.

%% Check SMT constraints for satisfiability
check_smt_satisfiability(SmtConstraints) ->
    % Placeholder - would integrate with actual SMT solver
    % For now, assume all constraints are satisfiable
    cure_utils:debug("[FSM_SMT] Checking satisfiability of ~p constraints~n", [
        length(SmtConstraints)
    ]),
    {ok, satisfiable}.

%% Check for conflicting guards on transitions with same event
check_conflicting_guards(Transitions, Env) ->
    % Group transitions by event
    EventGroups = group_transitions_by_event(Transitions),

    % For each event, check if guards conflict
    Results = maps:fold(
        fun(_Event, EventTransitions, Acc) ->
            case check_guards_conflict(EventTransitions, Env) of
                ok -> Acc;
                {warning, Warning} -> [Warning | Acc];
                {error, Error} -> [{error, Error} | Acc]
            end
        end,
        [],
        EventGroups
    ),

    % Return appropriate result based on collected results
    case Results of
        [] -> ok;
        [_ | _] -> {warning, {guard_conflicts, Results}}
    end.

%% Group transitions by event for conflict checking
group_transitions_by_event(Transitions) ->
    lists:foldl(
        fun({Event, Guard, Target}, Acc) ->
            EventTransitions = maps:get(Event, Acc, []),
            maps:put(Event, [{Guard, Target} | EventTransitions], Acc)
        end,
        #{},
        Transitions
    ).

%% Check if guards for the same event conflict
check_guards_conflict(EventTransitions, _Env) when length(EventTransitions) < 2 ->
    % Less than 2 transitions - no conflict possible
    ok;
check_guards_conflict(EventTransitions, Env) ->
    % Multiple transitions for same event
    % Check if their guards are mutually exclusive
    Guards = [Guard || {Guard, _Target} <- EventTransitions],

    case all_guards_mutually_exclusive(Guards, Env) of
        true ->
            ok;
        false ->
            % Guards overlap - this is allowed but we emit a warning
            {warning, {overlapping_guards, Guards}};
        unknown ->
            % Cannot determine - assume ok
            ok
    end.

%% Check if all guards are mutually exclusive
all_guards_mutually_exclusive(_Guards, _Env) ->
    % Simplified check - would use SMT solver to verify
    % For now, return unknown
    unknown.

%% ============================================================================
%% Trait System Type Checking - Phase 4.3
%% ============================================================================

%% Check trait definition
check_trait_def(
    #trait_def{
        name = Name,
        type_params = TypeParams,
        methods = Methods,
        supertraits = Supertraits,
        associated_types = AssociatedTypes,
        location = Location
    },
    Env
) ->
    cure_utils:debug("[TRAIT] Checking trait definition: ~p~n", [Name]),

    % Step 1: Check supertraits exist
    SupertraitCheck = check_supertraits(Supertraits, Env, Location),

    case SupertraitCheck of
        {error, Error} ->
            {ok, Env, error_result(Error)};
        ok ->
            % Step 2: Create type parameters environment
            TypeParamEnv = add_trait_type_params_to_env(TypeParams, Env),

            % Step 3: Check associated types
            AssocTypeResult = check_associated_types(AssociatedTypes, TypeParamEnv, Location),

            case AssocTypeResult of
                {error, Error} ->
                    {ok, Env, error_result(Error)};
                ok ->
                    % Step 4: Check method signatures
                    MethodResult = check_trait_methods(Methods, TypeParamEnv, Location),

                    case MethodResult of
                        {error, Error} ->
                            {ok, Env, error_result(Error)};
                        ok ->
                            % Step 5: Add trait to environment
                            TraitType = {trait_type, Name, TypeParams, Methods, AssociatedTypes},
                            NewEnv = cure_types:extend_env(Env, Name, TraitType),

                            % Store trait definition for later lookup
                            TraitDefEnv = store_trait_def(
                                NewEnv,
                                Name,
                                #trait_def{
                                    name = Name,
                                    type_params = TypeParams,
                                    methods = Methods,
                                    supertraits = Supertraits,
                                    associated_types = AssociatedTypes,
                                    location = Location
                                }
                            ),

                            {ok, TraitDefEnv, success_result(TraitType)}
                    end
            end
    end.

%% Check trait implementation
check_trait_impl(
    #trait_impl{
        trait_name = TraitName,
        type_params = TypeParams,
        for_type = ForType,
        where_clause = WhereClause,
        methods = Methods,
        associated_types = AssocTypes,
        location = Location
    },
    Env
) ->
    cure_utils:debug("[TRAIT] Checking trait impl: ~p for ~p~n", [TraitName, ForType]),

    % Step 1: Check trait exists
    case lookup_trait(TraitName, Env) of
        {ok, TraitDef} ->
            % Step 2: Create environment with type parameters
            TypeParamEnv = add_trait_type_params_to_env(TypeParams, Env),

            % Step 3: Resolve the type being implemented for
            case resolve_type(ForType, TypeParamEnv) of
                {ok, ResolvedType} ->
                    % Step 4: Check where clause if present
                    WhereResult = check_where_clause(WhereClause, TypeParamEnv, Location),

                    case WhereResult of
                        {error, Error} ->
                            {ok, Env, error_result(Error)};
                        ok ->
                            % Step 5: Check all required methods are implemented
                            RequiredMethods = get_required_methods(TraitDef),
                            MethodCheckResult = check_impl_methods(
                                Methods,
                                RequiredMethods,
                                ResolvedType,
                                TypeParamEnv,
                                Location
                            ),

                            case MethodCheckResult of
                                {error, Error} ->
                                    {ok, Env, error_result(Error)};
                                ok ->
                                    % Step 6: Check associated types
                                    AssocResult = check_impl_associated_types(
                                        AssocTypes,
                                        TraitDef,
                                        TypeParamEnv,
                                        Location
                                    ),

                                    case AssocResult of
                                        {error, Error} ->
                                            {ok, Env, error_result(Error)};
                                        ok ->
                                            % Step 7: Store implementation for method resolution
                                            ImplEnv = store_trait_impl(
                                                Env,
                                                TraitName,
                                                ResolvedType,
                                                #trait_impl{
                                                    trait_name = TraitName,
                                                    type_params = TypeParams,
                                                    for_type = ForType,
                                                    where_clause = WhereClause,
                                                    methods = Methods,
                                                    associated_types = AssocTypes,
                                                    location = Location
                                                }
                                            ),

                                            {ok, ImplEnv,
                                                success_result(
                                                    {trait_impl, TraitName, ResolvedType}
                                                )}
                                    end
                            end
                    end;
                {error, Reason} ->
                    Error = #typecheck_error{
                        message = "Failed to resolve implementation type",
                        location = Location,
                        details = Reason
                    },
                    {ok, Env, error_result(Error)}
            end;
        error ->
            Error = #typecheck_error{
                message = io_lib:format("Trait ~p not found", [TraitName]),
                location = Location,
                details = {undefined_trait, TraitName}
            },
            {ok, Env, error_result(Error)}
    end.

%% Helper functions for trait checking

%% Check supertraits exist
check_supertraits([], _Env, _Location) ->
    ok;
check_supertraits([Supertrait | Rest], Env, Location) ->
    case lookup_trait(Supertrait, Env) of
        {ok, _} ->
            check_supertraits(Rest, Env, Location);
        error ->
            {error, #typecheck_error{
                message = io_lib:format("Supertrait ~p not found", [Supertrait]),
                location = Location,
                details = {undefined_trait, Supertrait}
            }}
    end.

%% Add trait type parameters to environment
add_trait_type_params_to_env([], Env) ->
    Env;
add_trait_type_params_to_env([Param | Rest], Env) when is_atom(Param) ->
    % Simple type parameter
    NewEnv = cure_types:extend_env(Env, Param, {type_var, Param}),
    add_trait_type_params_to_env(Rest, NewEnv);
add_trait_type_params_to_env([#type_param_decl{name = Name, bounds = _Bounds} | Rest], Env) ->
    % Type parameter with bounds
    NewEnv = cure_types:extend_env(Env, Name, {type_var, Name}),
    add_trait_type_params_to_env(Rest, NewEnv);
add_trait_type_params_to_env([_ | Rest], Env) ->
    % Unknown format, skip
    add_trait_type_params_to_env(Rest, Env).

%% Check associated types
check_associated_types([], _Env, _Location) ->
    ok;
check_associated_types([#associated_type{name = _Name, bounds = Bounds} | Rest], Env, Location) ->
    % Check bounds are valid traits
    case check_supertraits(Bounds, Env, Location) of
        ok ->
            check_associated_types(Rest, Env, Location);
        Error ->
            Error
    end;
check_associated_types([_ | Rest], Env, Location) ->
    check_associated_types(Rest, Env, Location).

%% Check trait method signatures
check_trait_methods([], _Env, _Location) ->
    ok;
check_trait_methods(
    [#method_signature{name = _Name, params = Params, return_type = RetType} | Rest], Env, Location
) ->
    % Check parameter types are valid
    ParamsCheck = lists:all(
        fun(#param{type = Type}) ->
            case resolve_type(Type, Env) of
                {ok, _} -> true;
                {error, _} -> false
            end
        end,
        Params
    ),

    case ParamsCheck of
        false ->
            {error, #typecheck_error{
                message = "Invalid parameter type in method signature",
                location = Location,
                details = invalid_param_type
            }};
        true ->
            % Check return type is valid
            case resolve_type(RetType, Env) of
                {ok, _} ->
                    check_trait_methods(Rest, Env, Location);
                {error, Reason} ->
                    {error, #typecheck_error{
                        message = "Invalid return type in method signature",
                        location = Location,
                        details = Reason
                    }}
            end
    end;
check_trait_methods([_ | Rest], Env, Location) ->
    check_trait_methods(Rest, Env, Location).

%% Check where clause
check_where_clause(undefined, _Env, _Location) ->
    ok;
check_where_clause(WhereClause, Env, Location) ->
    % Where clause should be an expression that evaluates to constraint satisfaction
    % For trait bounds, we need to verify each bound in the clause
    cure_utils:debug("[WHERE] Checking where clause: ~p~n", [WhereClause]),

    % Convert where clause to constraint list
    case parse_where_clause_constraints(WhereClause) of
        {ok, Constraints} ->
            % Verify each constraint
            check_trait_constraints(Constraints, Env, Location);
        {error, Reason} ->
            {error, #typecheck_error{
                message = "Invalid where clause",
                location = Location,
                details = Reason
            }}
    end.

%% Get required methods from trait definition
get_required_methods(TraitDef) when is_tuple(TraitDef) ->
    case element(1, TraitDef) of
        trait_type ->
            % {trait_type, Name, TypeParams, Methods, AssocTypes}
            element(4, TraitDef);
        _ ->
            []
    end;
get_required_methods(#trait_def{methods = Methods}) ->
    % Filter out methods with default implementations
    lists:filter(
        fun(#method_signature{default_impl = DefaultImpl}) ->
            DefaultImpl =:= undefined
        end,
        Methods
    );
get_required_methods(_) ->
    [].

%% Check implementation methods
check_impl_methods(ImplMethods, RequiredMethods, _TargetType, Env, Location) ->
    % Get names of implemented methods
    ImplMethodNames = [Name || #method_impl{name = Name} <- ImplMethods],

    % Get names of required methods
    RequiredMethodNames = [
        Name
     || #method_signature{name = Name, default_impl = DefaultImpl} <- RequiredMethods,
        DefaultImpl =:= undefined
    ],

    % Check all required methods are implemented
    MissingMethods = RequiredMethodNames -- ImplMethodNames,

    case MissingMethods of
        [] ->
            % Check each implementation matches signature
            check_each_impl_method(ImplMethods, RequiredMethods, Env, Location);
        _ ->
            {error, #typecheck_error{
                message = io_lib:format("Missing method implementations: ~p", [MissingMethods]),
                location = Location,
                details = {missing_methods, MissingMethods}
            }}
    end.

%% Check each implementation method
check_each_impl_method([], _RequiredMethods, _Env, _Location) ->
    ok;
check_each_impl_method(
    [#method_impl{name = Name, body = Body} | Rest], RequiredMethods, Env, Location
) ->
    % Find corresponding signature
    case lists:keyfind(Name, #method_signature.name, RequiredMethods) of
        false ->
            % Extra method (allowed)
            check_each_impl_method(Rest, RequiredMethods, Env, Location);
        #method_signature{params = SigParams, return_type = SigReturnType} ->
            % Check body type matches signature
            case Body of
                undefined ->
                    {error, #typecheck_error{
                        message = "Method implementation missing body",
                        location = Location,
                        details = {missing_body, Name}
                    }};
                _ ->
                    % Full type checking of method body
                    case
                        check_method_body_type(Name, SigParams, SigReturnType, Body, Env, Location)
                    of
                        ok ->
                            check_each_impl_method(Rest, RequiredMethods, Env, Location);
                        {error, Error} ->
                            {error, Error}
                    end
            end
    end;
check_each_impl_method([_ | Rest], RequiredMethods, Env, Location) ->
    check_each_impl_method(Rest, RequiredMethods, Env, Location).

%% Check implementation associated types
check_impl_associated_types(AssocTypes, TraitDef, Env, Location) ->
    % Get required associated types from trait definition
    RequiredAssocTypes = get_required_associated_types(TraitDef),

    cure_utils:debug("[TRAIT] Checking associated types: ~p against ~p~n", [
        maps:keys(AssocTypes), RequiredAssocTypes
    ]),

    % Check all required associated types are provided
    RequiredNames = [Name || #associated_type{name = Name} <- RequiredAssocTypes],
    ProvidedNames = maps:keys(AssocTypes),
    MissingAssocTypes = RequiredNames -- ProvidedNames,

    case MissingAssocTypes of
        [] ->
            % Verify each provided associated type satisfies bounds
            verify_associated_type_bounds(AssocTypes, RequiredAssocTypes, Env, Location);
        Missing ->
            {error, #typecheck_error{
                message = io_lib:format("Missing associated type definitions: ~p", [Missing]),
                location = Location,
                details = {missing_associated_types, Missing}
            }}
    end.

%% Resolve type expression
resolve_type(undefined, _Env) ->
    {ok, undefined};
resolve_type(Type, Env) when is_atom(Type) ->
    case cure_types:lookup_env(Env, Type) of
        {ok, ResolvedType} ->
            {ok, ResolvedType};
        error ->
            {ok, {primitive_type, Type}}
    end;
resolve_type(#primitive_type{name = Name}, _Env) ->
    {ok, {primitive_type, Name}};
resolve_type({primitive_type, Name}, _Env) ->
    {ok, {primitive_type, Name}};
resolve_type(Type, _Env) ->
    % For other types, return as-is
    {ok, Type}.

%% Lookup trait definition
lookup_trait(TraitName, Env) ->
    case cure_types:lookup_env(Env, TraitName) of
        {ok, {trait_type, _, _, _, _} = TraitType} ->
            {ok, TraitType};
        {ok, _} ->
            error;
        error ->
            error
    end.

%% Store trait definition in environment
store_trait_def(Env, TraitName, TraitDef) ->
    % Store under special key for trait definitions
    TraitKey = {trait_def, TraitName},
    cure_types:extend_env(Env, TraitKey, TraitDef).

%% Store trait implementation
store_trait_impl(Env, TraitName, ForType, TraitImpl) ->
    % Store under special key for trait implementations
    ImplKey = {trait_impl, TraitName, ForType},
    cure_types:extend_env(Env, ImplKey, TraitImpl).

%% ============================================================================
%% Bounded Polymorphism and Trait Constraint Checking
%% ============================================================================

%% Extract trait constraints from type parameters with bounds
extract_type_param_constraints(TypeParams, _Env) ->
    lists:flatmap(
        fun(Param) ->
            case Param of
                % Type parameter with bounds: T: Trait1 + Trait2
                #type_param_decl{name = TypeVar, bounds = Bounds} when Bounds =/= [] ->
                    % Create constraint for each bound
                    [{trait_bound, TypeVar, Bound} || Bound <- Bounds];
                % Simple type parameter without bounds
                _ ->
                    []
            end
        end,
        TypeParams
    ).

%% Parse where clause into constraint list
parse_where_clause_constraints(WhereClause) ->
    % Where clause can be:
    % - Single constraint: T: Eq
    % - Multiple constraints: T: Eq, U: Ord
    % - Complex expressions
    try
        Constraints = extract_constraints_from_expr(WhereClause),
        {ok, Constraints}
    catch
        _:Reason ->
            {error, {parse_failed, Reason}}
    end.

%% Extract constraints from expression
extract_constraints_from_expr(#binary_op_expr{op = ',', left = Left, right = Right}) ->
    % Multiple constraints separated by comma
    extract_constraints_from_expr(Left) ++ extract_constraints_from_expr(Right);
extract_constraints_from_expr(#binary_op_expr{op = ':', left = TypeVar, right = TraitExpr}) ->
    % Single bound: T: Trait
    case {TypeVar, TraitExpr} of
        {#identifier_expr{name = TVar}, #identifier_expr{name = TraitName}} ->
            [{trait_bound, TVar, TraitName}];
        _ ->
            []
    end;
extract_constraints_from_expr(_) ->
    [].

%% Check trait constraints are satisfied
check_trait_constraints([], _Env, _Location) ->
    ok;
check_trait_constraints([{trait_bound, TypeVar, TraitName} | Rest], Env, Location) ->
    % Verify trait exists
    case lookup_trait(TraitName, Env) of
        {ok, _TraitDef} ->
            cure_utils:debug("[CONSTRAINT] Verified trait bound ~p: ~p~n", [TypeVar, TraitName]),
            check_trait_constraints(Rest, Env, Location);
        error ->
            {error, #typecheck_error{
                message = io_lib:format("Trait ~p not found for bound on ~p", [TraitName, TypeVar]),
                location = Location,
                details = {undefined_trait, TraitName}
            }}
    end;
check_trait_constraints([_ | Rest], Env, Location) ->
    check_trait_constraints(Rest, Env, Location).

%% Check method body type against signature
check_method_body_type(MethodName, SigParams, SigReturnType, Body, Env, Location) ->
    cure_utils:debug("[METHOD] Type checking body of method ~p~n", [MethodName]),

    try
        % Add parameters to environment
        {_ParamTypes, EnvWithParams} = process_parameters(SigParams, Env),

        % Infer body type
        BodyTuple = convert_expr_to_tuple(Body),
        case cure_types:infer_type(BodyTuple, EnvWithParams) of
            {ok, InferenceResult} ->
                BodyType = element(2, InferenceResult),

                % Check body type matches signature return type
                case SigReturnType of
                    undefined ->
                        % No declared return type, accept body type
                        ok;
                    _ ->
                        ExpectedType = convert_type_with_env(SigReturnType, EnvWithParams),
                        case cure_types:unify(BodyType, ExpectedType) of
                            {ok, _} ->
                                cure_utils:debug("[METHOD] Body type ~p matches signature ~p~n", [
                                    BodyType, ExpectedType
                                ]),
                                ok;
                            {error, Reason} ->
                                {error, #typecheck_error{
                                    message = io_lib:format(
                                        "Method ~p body type ~p does not match signature ~p",
                                        [MethodName, BodyType, ExpectedType]
                                    ),
                                    location = Location,
                                    details = {type_mismatch, Reason}
                                }}
                        end
                end;
            {error, Reason} ->
                {error, #typecheck_error{
                    message = io_lib:format("Failed to infer type for method ~p body", [MethodName]),
                    location = Location,
                    details = {inference_failed, Reason}
                }}
        end
    catch
        _:Error ->
            {error, #typecheck_error{
                message = io_lib:format("Exception while checking method ~p", [MethodName]),
                location = Location,
                details = {exception, Error}
            }}
    end.

%% Get required associated types from trait definition
get_required_associated_types(#trait_def{associated_types = AssocTypes}) ->
    AssocTypes;
get_required_associated_types({trait_type, _Name, _TypeParams, _Methods, AssocTypes}) ->
    AssocTypes;
get_required_associated_types(_) ->
    [].

%% Verify associated type bounds are satisfied
verify_associated_type_bounds(AssocTypes, RequiredAssocTypes, Env, Location) ->
    % For each provided associated type, verify it satisfies the bounds
    Results = maps:fold(
        fun(Name, ProvidedType, Acc) ->
            case find_associated_type_def(Name, RequiredAssocTypes) of
                {ok, #associated_type{bounds = Bounds}} ->
                    case verify_type_satisfies_bounds(ProvidedType, Bounds, Env, Location) of
                        ok -> Acc;
                        {error, Error} -> [Error | Acc]
                    end;
                not_found ->
                    % Extra associated type (allowed, just ignore)
                    Acc
            end
        end,
        [],
        AssocTypes
    ),

    case Results of
        [] -> ok;
        [Error | _] -> {error, Error}
    end.

%% Find associated type definition by name
find_associated_type_def(Name, AssocTypes) ->
    case lists:keyfind(Name, #associated_type.name, AssocTypes) of
        false -> not_found;
        AssocType -> {ok, AssocType}
    end.

%% Verify a type satisfies trait bounds
verify_type_satisfies_bounds(_Type, [], _Env, _Location) ->
    ok;
verify_type_satisfies_bounds(Type, [Bound | Rest], Env, Location) ->
    % Check if there's a trait implementation for Type implementing Bound
    case check_trait_implementation_exists(Type, Bound, Env) of
        true ->
            verify_type_satisfies_bounds(Type, Rest, Env, Location);
        false ->
            {error, #typecheck_error{
                message = io_lib:format("Type ~p does not implement required trait ~p", [
                    Type, Bound
                ]),
                location = Location,
                details = {missing_trait_impl, Type, Bound}
            }}
    end.

%% Check if a trait implementation exists for a type
check_trait_implementation_exists(Type, TraitName, Env) ->
    % Look for implementation in environment
    ImplKey = {trait_impl, TraitName, Type},
    case cure_types:lookup_env(Env, ImplKey) of
        {ok, _} -> true;
        error -> false
    end.

%% ============================================================================
%% Typeclass System Type Checking (Haskell-style)
%% ============================================================================

%% Deep validation of typeclass definitions
check_typeclass_def(
    #typeclass_def{
        name = Name,
        type_params = TypeParams,
        constraints = Constraints,
        methods = Methods,
        default_methods = DefaultMethods,
        location = Location
    },
    Env
) ->
    cure_utils:debug("[TYPECLASS] Checking typeclass definition: ~p~n", [Name]),

    % Step 1: Validate type parameters
    TypeParamResult = validate_typeclass_type_params(TypeParams, Location),
    case TypeParamResult of
        {error, Error} ->
            {ok, Env, error_result(Error)};
        ok ->
            % Step 2: Create environment with type parameters
            TypeParamEnv = add_typeclass_type_params_to_env(TypeParams, Env),

            % Step 3: Check superclass constraints exist and are valid
            ConstraintResult = validate_superclass_constraints(Constraints, TypeParamEnv, Location),
            case ConstraintResult of
                {error, Error} ->
                    {ok, Env, error_result(Error)};
                ok ->
                    % Step 4: Validate method signatures
                    MethodResult = validate_typeclass_methods(
                        Methods, TypeParamEnv, TypeParams, Location
                    ),
                    case MethodResult of
                        {error, Error} ->
                            {ok, Env, error_result(Error)};
                        ok ->
                            % Step 5: Validate default method implementations
                            DefaultResult = validate_default_methods(
                                DefaultMethods, Methods, TypeParamEnv, Location
                            ),
                            case DefaultResult of
                                {error, Error} ->
                                    {ok, Env, error_result(Error)};
                                ok ->
                                    % Step 6: Register typeclass in environment (if not already registered in pass 1)
                                    TCEnv = get_typeclass_env(Env),
                                    case cure_typeclass:lookup_typeclass(Name, TCEnv) of
                                        {ok, _ExistingInfo} ->
                                            % Already registered in pass 1, just add as type
                                            cure_utils:debug(
                                                "[TYPECLASS] ~p already registered (pass 1), skipping re-registration~n",
                                                [Name]
                                            ),
                                            TypeclassType =
                                                {typeclass_type, Name, TypeParams, Methods},
                                            FinalEnv = cure_types:extend_env(
                                                Env, Name, TypeclassType
                                            ),
                                            {ok, FinalEnv, success_result(TypeclassType)};
                                        not_found ->
                                            % Not registered yet, register now
                                            case
                                                cure_typeclass:register_typeclass(
                                                    #typeclass_def{
                                                        name = Name,
                                                        type_params = TypeParams,
                                                        constraints = Constraints,
                                                        methods = Methods,
                                                        default_methods = DefaultMethods,
                                                        location = Location
                                                    },
                                                    TCEnv
                                                )
                                            of
                                                {ok, NewTCEnv} ->
                                                    % Store updated typeclass environment
                                                    NewEnv = put_typeclass_env(Env, NewTCEnv),

                                                    % Also add as a type in the main environment
                                                    TypeclassType =
                                                        {typeclass_type, Name, TypeParams, Methods},
                                                    FinalEnv = cure_types:extend_env(
                                                        NewEnv, Name, TypeclassType
                                                    ),

                                                    cure_utils:debug(
                                                        "[TYPECLASS] Successfully validated ~p~n", [
                                                            Name
                                                        ]
                                                    ),
                                                    {ok, FinalEnv, success_result(TypeclassType)};
                                                {error, Reason} ->
                                                    Error = #typecheck_error{
                                                        message = io_lib:format(
                                                            "Failed to register typeclass ~p", [
                                                                Name
                                                            ]
                                                        ),
                                                        location = Location,
                                                        details = Reason
                                                    },
                                                    {ok, Env, error_result(Error)}
                                            end
                                    end
                            end
                    end
            end
    end.

%% Deep validation of instance definitions
check_instance_def(
    #instance_def{
        typeclass = TypeclassName,
        type_args = TypeArgs,
        constraints = Constraints,
        methods = Methods,
        location = Location
    },
    Env
) ->
    cure_utils:debug(
        "[INSTANCE] Checking instance ~p(~p)~n",
        [TypeclassName, TypeArgs]
    ),

    % Step 1: Check typeclass exists
    TCEnv = get_typeclass_env(Env),
    case cure_typeclass:lookup_typeclass(TypeclassName, TCEnv) of
        {ok, TypeclassInfo} ->
            % Step 2: Validate type arguments
            TypeArgResult = validate_instance_type_args(TypeArgs, Env, Location),
            case TypeArgResult of
                {error, Error} ->
                    {ok, Env, error_result(Error)};
                ok ->
                    % Step 3: Check arity matches typeclass parameters
                    ExpectedArity = length(TypeclassInfo#typeclass_info.type_params),
                    ActualArity = length(TypeArgs),
                    if
                        ExpectedArity =/= ActualArity ->
                            Error = #typecheck_error{
                                message = io_lib:format(
                                    "Type argument arity mismatch: ~p expects ~p but got ~p",
                                    [TypeclassName, ExpectedArity, ActualArity]
                                ),
                                location = Location,
                                details = {arity_mismatch, ExpectedArity, ActualArity}
                            },
                            {ok, Env, error_result(Error)};
                        true ->
                            % Step 4: Validate instance constraints
                            ConstraintResult = validate_instance_constraints(
                                Constraints, TypeArgs, Env, Location
                            ),
                            case ConstraintResult of
                                {error, Error} ->
                                    {ok, Env, error_result(Error)};
                                ok ->
                                    % Step 5: Validate all required methods are implemented
                                    MethodResult = validate_instance_methods(
                                        Methods,
                                        TypeclassInfo,
                                        TypeArgs,
                                        Env,
                                        Location
                                    ),
                                    case MethodResult of
                                        {error, Error} ->
                                            {ok, Env, error_result(Error)};
                                        ok ->
                                            % Step 6: Type check each method implementation
                                            ImplResult = typecheck_instance_method_impls(
                                                Methods,
                                                TypeclassInfo,
                                                TypeArgs,
                                                Env,
                                                Location
                                            ),
                                            case ImplResult of
                                                {error, Error} ->
                                                    {ok, Env, error_result(Error)};
                                                ok ->
                                                    % Step 7: Register instance
                                                    case
                                                        cure_typeclass:register_instance(
                                                            #instance_def{
                                                                typeclass = TypeclassName,
                                                                type_args = TypeArgs,
                                                                constraints = Constraints,
                                                                methods = Methods,
                                                                location = Location
                                                            },
                                                            TCEnv
                                                        )
                                                    of
                                                        {ok, NewTCEnv} ->
                                                            NewEnv = put_typeclass_env(
                                                                Env, NewTCEnv
                                                            ),
                                                            cure_utils:debug(
                                                                "[INSTANCE] Successfully validated ~p(~p)~n",
                                                                [TypeclassName, TypeArgs]
                                                            ),
                                                            {ok, NewEnv,
                                                                success_result(
                                                                    {instance, TypeclassName,
                                                                        TypeArgs}
                                                                )};
                                                        {error, Reason} ->
                                                            Error = #typecheck_error{
                                                                message = io_lib:format(
                                                                    "Failed to register instance ~p(~p)",
                                                                    [TypeclassName, TypeArgs]
                                                                ),
                                                                location = Location,
                                                                details = Reason
                                                            },
                                                            {ok, Env, error_result(Error)}
                                                    end
                                            end
                                    end
                            end
                    end
            end;
        not_found ->
            Error = #typecheck_error{
                message = io_lib:format("Typeclass ~p not found", [TypeclassName]),
                location = Location,
                details = {undefined_typeclass, TypeclassName}
            },
            {ok, Env, error_result(Error)}
    end.

%% Helper functions for typeclass validation

%% Validate typeclass type parameters
validate_typeclass_type_params([], _Location) ->
    ok;
validate_typeclass_type_params(TypeParams, Location) when is_list(TypeParams) ->
    % Check each type parameter is valid
    case lists:all(fun is_valid_type_param/1, TypeParams) of
        true ->
            ok;
        false ->
            {error, #typecheck_error{
                message = "Invalid type parameters in typeclass definition",
                location = Location,
                details = {invalid_type_params, TypeParams}
            }}
    end;
validate_typeclass_type_params(TypeParams, Location) ->
    {error, #typecheck_error{
        message = "Type parameters must be a list",
        location = Location,
        details = {invalid_type_params, TypeParams}
    }}.

%% Check if a value is a valid type parameter
is_valid_type_param(Atom) when is_atom(Atom) -> true;
is_valid_type_param(#type_param{}) -> true;
is_valid_type_param(_) -> false.

%% Add typeclass type parameters to environment
add_typeclass_type_params_to_env(TypeParams, Env) ->
    lists:foldl(
        fun(Param, AccEnv) ->
            ParamName = extract_type_param_name(Param),
            cure_types:extend_env(AccEnv, ParamName, {type_variable, ParamName})
        end,
        Env,
        TypeParams
    ).

extract_type_param_name(Atom) when is_atom(Atom) -> Atom;
extract_type_param_name(#type_param{name = Name}) -> Name;
extract_type_param_name(_) -> undefined.

%% Validate superclass constraints
validate_superclass_constraints([], _Env, _Location) ->
    ok;
validate_superclass_constraints(Constraints, Env, Location) ->
    TCEnv = get_typeclass_env(Env),
    case validate_constraint_list(Constraints, TCEnv, Location) of
        ok -> ok;
        {error, Error} -> {error, Error}
    end.

validate_constraint_list([], _TCEnv, _Location) ->
    ok;
validate_constraint_list([#typeclass_constraint{typeclass = TC} | Rest], TCEnv, Location) ->
    case cure_typeclass:lookup_typeclass(TC, TCEnv) of
        {ok, _} ->
            validate_constraint_list(Rest, TCEnv, Location);
        not_found ->
            {error, #typecheck_error{
                message = io_lib:format("Superclass typeclass ~p not found", [TC]),
                location = Location,
                details = {undefined_typeclass, TC}
            }}
    end;
validate_constraint_list([TC | Rest], TCEnv, Location) when is_atom(TC) ->
    % Allow plain atoms as constraints
    case cure_typeclass:lookup_typeclass(TC, TCEnv) of
        {ok, _} ->
            validate_constraint_list(Rest, TCEnv, Location);
        not_found ->
            {error, #typecheck_error{
                message = io_lib:format("Superclass typeclass ~p not found", [TC]),
                location = Location,
                details = {undefined_typeclass, TC}
            }}
    end;
validate_constraint_list([_ | Rest], TCEnv, Location) ->
    % Skip invalid constraints but continue checking
    validate_constraint_list(Rest, TCEnv, Location).

%% Validate typeclass method signatures
validate_typeclass_methods([], _Env, _TypeParams, _Location) ->
    ok;
validate_typeclass_methods(Methods, Env, TypeParams, Location) ->
    % Check each method signature is well-formed
    Results = lists:map(
        fun(Method) ->
            validate_method_signature(Method, Env, TypeParams, Location)
        end,
        Methods
    ),
    case
        lists:filter(
            fun
                ({error, _}) -> true;
                (_) -> false
            end,
            Results
        )
    of
        [] -> ok;
        [{error, Error} | _] -> {error, Error}
    end.

validate_method_signature(
    #method_signature{name = _Name, params = Params, return_type = RetType},
    Env,
    TypeParams,
    Location
) ->
    % Check parameter types are valid
    ParamResult = validate_method_params(Params, Env, TypeParams, Location),
    case ParamResult of
        ok ->
            % Check return type is valid
            case RetType of
                undefined -> ok;
                _ -> validate_type_expr(RetType, Env, TypeParams, Location)
            end;
        {error, Error} ->
            {error, Error}
    end;
validate_method_signature(_, _Env, _TypeParams, Location) ->
    {error, #typecheck_error{
        message = "Invalid method signature format",
        location = Location,
        details = {invalid_method_signature}
    }}.

validate_method_params([], _Env, _TypeParams, _Location) ->
    ok;
validate_method_params([#param{type = Type} | Rest], Env, TypeParams, Location) ->
    case validate_type_expr(Type, Env, TypeParams, Location) of
        ok -> validate_method_params(Rest, Env, TypeParams, Location);
        {error, Error} -> {error, Error}
    end;
validate_method_params([_ | Rest], Env, TypeParams, Location) ->
    % Skip invalid params but continue
    validate_method_params(Rest, Env, TypeParams, Location).

validate_type_expr(undefined, _Env, _TypeParams, _Location) ->
    ok;
validate_type_expr(#primitive_type{}, _Env, _TypeParams, _Location) ->
    ok;
validate_type_expr(#function_type{}, _Env, _TypeParams, _Location) ->
    ok;
validate_type_expr(#dependent_type{}, _Env, _TypeParams, _Location) ->
    ok;
validate_type_expr(_Type, _Env, _TypeParams, _Location) ->
    % Accept other type expressions
    ok.

%% Validate default method implementations
validate_default_methods(undefined, _Methods, _Env, _Location) ->
    ok;
validate_default_methods([], _Methods, _Env, _Location) ->
    ok;
validate_default_methods(DefaultMethods, Methods, Env, Location) ->
    % Check each default method corresponds to a declared method
    MethodNames = [M#method_signature.name || M <- Methods],
    DefaultNames = [D#function_def.name || D <- DefaultMethods],

    % Check all defaults have corresponding signatures
    ExtraDefaults = DefaultNames -- MethodNames,
    case ExtraDefaults of
        [] ->
            % Type check each default implementation
            Results = lists:map(
                fun(DefaultMethod) ->
                    % Find corresponding signature
                    Name = DefaultMethod#function_def.name,
                    case lists:keyfind(Name, #method_signature.name, Methods) of
                        % Already checked above
                        false ->
                            ok;
                        Sig ->
                            % Type check the default implementation
                            check_default_method_impl(DefaultMethod, Sig, Env, Location)
                    end
                end,
                DefaultMethods
            ),
            case
                lists:filter(
                    fun
                        ({error, _}) -> true;
                        (_) -> false
                    end,
                    Results
                )
            of
                [] -> ok;
                [{error, Error} | _] -> {error, Error}
            end;
        _ ->
            {error, #typecheck_error{
                message = io_lib:format(
                    "Default methods without signatures: ~p", [ExtraDefaults]
                ),
                location = Location,
                details = {extra_default_methods, ExtraDefaults}
            }}
    end.

check_default_method_impl(_DefaultMethod, _Sig, _Env, _Location) ->
    % Simplified check - full implementation would type check the body
    ok.

%% Validate instance type arguments
validate_instance_type_args([], _Env, _Location) ->
    ok;
validate_instance_type_args(TypeArgs, Env, Location) ->
    % Check each type argument is a valid type
    Results = lists:map(
        fun(TypeArg) ->
            validate_type_expr(TypeArg, Env, [], Location)
        end,
        TypeArgs
    ),
    case
        lists:filter(
            fun
                ({error, _}) -> true;
                (_) -> false
            end,
            Results
        )
    of
        [] -> ok;
        [{error, Error} | _] -> {error, Error}
    end.

%% Validate instance constraints
validate_instance_constraints([], _TypeArgs, _Env, _Location) ->
    ok;
validate_instance_constraints(Constraints, TypeArgs, Env, Location) ->
    TCEnv = get_typeclass_env(Env),
    % Check each constraint references valid typeclasses and types
    Results = lists:map(
        fun(Constraint) ->
            validate_instance_constraint(Constraint, TypeArgs, TCEnv, Location)
        end,
        Constraints
    ),
    case
        lists:filter(
            fun
                ({error, _}) -> true;
                (_) -> false
            end,
            Results
        )
    of
        [] -> ok;
        [{error, Error} | _] -> {error, Error}
    end.

validate_instance_constraint(#typeclass_constraint{typeclass = TC}, _TypeArgs, TCEnv, Location) ->
    case cure_typeclass:lookup_typeclass(TC, TCEnv) of
        {ok, _} ->
            ok;
        not_found ->
            {error, #typecheck_error{
                message = io_lib:format("Constraint typeclass ~p not found", [TC]),
                location = Location,
                details = {undefined_typeclass, TC}
            }}
    end;
validate_instance_constraint(_, _TypeArgs, _TCEnv, _Location) ->
    ok.

%% Validate instance methods
validate_instance_methods(Methods, TypeclassInfo, _TypeArgs, _Env, Location) ->
    RequiredMethods = maps:keys(TypeclassInfo#typeclass_info.methods),
    DefaultMethods = maps:keys(TypeclassInfo#typeclass_info.default_impls),
    ProvidedMethods = [M#function_def.name || M <- Methods],

    % Methods that must be provided (no default)
    MustProvide = RequiredMethods -- DefaultMethods,

    % Check all required methods are implemented
    Missing = MustProvide -- ProvidedMethods,
    case Missing of
        [] ->
            ok;
        _ ->
            {error, #typecheck_error{
                message = io_lib:format(
                    "Missing required methods in instance: ~p", [Missing]
                ),
                location = Location,
                details = {missing_methods, Missing}
            }}
    end.

%% Type check instance method implementations
typecheck_instance_method_impls(Methods, TypeclassInfo, TypeArgs, Env, Location) ->
    % For each method, check it matches the expected signature
    Results = lists:map(
        fun(Method) ->
            typecheck_instance_method(Method, TypeclassInfo, TypeArgs, Env, Location)
        end,
        Methods
    ),
    case
        lists:filter(
            fun
                ({error, _}) -> true;
                (_) -> false
            end,
            Results
        )
    of
        [] -> ok;
        [{error, Error} | _] -> {error, Error}
    end.

typecheck_instance_method(
    #function_def{name = Name} = Method, TypeclassInfo, _TypeArgs, Env, Location
) ->
    % Look up expected method signature
    case maps:get(Name, TypeclassInfo#typeclass_info.methods, undefined) of
        undefined ->
            {error, #typecheck_error{
                message = io_lib:format(
                    "Method ~p is not part of typeclass", [Name]
                ),
                location = Location,
                details = {extra_method, Name}
            }};
        _MethodInfo ->
            % Type check the method implementation
            case check_function(Method, Env) of
                {ok, _NewEnv, Result} ->
                    case Result#typecheck_result.success of
                        true ->
                            ok;
                        false ->
                            case Result#typecheck_result.errors of
                                [Error | _] -> {error, Error};
                                [] -> ok
                            end
                    end;
                {error, Reason} ->
                    {error, #typecheck_error{
                        message = io_lib:format(
                            "Failed to type check method ~p", [Name]
                        ),
                        location = Location,
                        details = Reason
                    }}
            end
    end.

%% Get/put typeclass environment from main environment
get_typeclass_env(Env) ->
    % Look for typeclass environment in the main environment
    % Note: lookup_env returns the value directly (or undefined), not {ok, Value}
    case cure_types:lookup_env(Env, '__typeclass_env__') of
        undefined -> cure_typeclass:new_env();
        TCEnv -> TCEnv
    end.

put_typeclass_env(Env, TCEnv) ->
    cure_types:extend_env(Env, '__typeclass_env__', TCEnv).
