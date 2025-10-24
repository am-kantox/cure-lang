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
    check_module/2,
    check_function/2,
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
    create_function_type_from_signature_records/2
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
    Env = builtin_env(),
    check_items(
        AST,
        Env,
        #typecheck_result{
            success = true,
            type = undefined,
            errors = [],
            warnings = []
        }
    ).

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
check_item(
    #record_def{
        name = RecordName, type_params = _TypeParams, fields = Fields, location = _Location
    },
    Env
) ->
    % Convert field types to internal representation and resolve type names from environment
    ConvertedFields = [convert_and_resolve_record_field_def(F, Env) || F <- Fields],
    % Create a record type from the field definitions
    RecordType = {record_type, RecordName, ConvertedFields},
    NewEnv = cure_types:extend_env(Env, RecordName, RecordType),
    {ok, NewEnv, success_result(RecordType)};
check_item({record_def, RecordName, _TypeParams, Fields, _Location}, Env) ->
    % Fallback for tuple format - also resolve type names
    ConvertedFields = [convert_and_resolve_record_field_tuple(F, Env) || F <- Fields],
    RecordType = {record_type, RecordName, ConvertedFields},
    NewEnv = cure_types:extend_env(Env, RecordName, RecordType),
    {ok, NewEnv, success_result(RecordType)}.

%% Check FSM definition
check_fsm(
    #fsm_def{
        name = Name,
        states = States,
        initial = Initial,
        state_defs = StateDefs
    },
    Env
) ->
    % Verify initial state is in states list
    case lists:member(Initial, States) of
        false ->
            Error =
                #typecheck_error{
                    message = "Initial state not in states list",
                    location = #location{line = 0, column = 0},
                    details = {invalid_initial_state, Initial, States}
                },
            {ok, Env, error_result(Error)};
        true ->
            % Check all state definitions
            case check_state_definitions(StateDefs, States) of
                ok ->
                    FSMType = {fsm_type, Name, States, Initial},
                    NewEnv = cure_types:extend_env(Env, Name, FSMType),
                    {ok, NewEnv, success_result(FSMType)};
                {error, Error} ->
                    {ok, Env, error_result(Error)}
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
    FunctionEnv = collect_function_signatures(Items, ImportEnv),

    % Pass 2: Check all items with function signatures in environment
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
% Record format with multi-clause support
check_function(
    #function_def{
        name = Name,
        clauses = Clauses,
        params = Params,
        return_type = ReturnType,
        constraint = Constraint,
        body = Body,
        is_private = IsPrivate,
        location = Location
    },
    Env
) when Clauses =/= undefined andalso length(Clauses) > 0 ->
    % Multi-clause function - check each clause
    cure_utils:debug("[CHECK_FUNC] Checking multi-clause function ~p~n", [Name]),
    check_multiclause_function(Name, Clauses, Location, Env);
check_function(
    #function_def{
        name = Name,
        params = Params,
        return_type = ReturnType,
        constraint = Constraint,
        body = Body,
        is_private = IsPrivate,
        location = Location
    },
    Env
) ->
    % Single-clause function (record format, backward compatible)
    check_single_clause_function(
        Name, Params, ReturnType, Constraint, Body, IsPrivate, Location, Env
    );
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
                    extract_and_add_type_params(ReturnType, ParamEnv)
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
check_single_clause_function(Name, Params, ReturnType, Constraint, Body, _IsPrivate, Location, Env) ->
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
                    extract_and_add_type_params(ReturnType, ParamEnv)
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
            check_single_clause_function(
                Name, Params, ReturnType, Constraint, Body, false, Location, Env
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
        definition = Definition
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
                TypeDefType = convert_type_to_tuple(Definition),
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
        #dependent_type{name = ConstructorName, params = Args} ->
            % Constructor with arguments: Ok(T), Error(E), Some(T)
            % Use environment-aware conversion to properly resolve type variables
            ArgTypes = [convert_type_param_with_env(P, Env) || P <- Args],
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

%% Cached standard library functions
-spec get_stdlib_function_type(atom(), atom(), integer()) -> {ok, term()} | not_found.
get_stdlib_function_type(Module, Name, Arity) ->
    % Lazy loading - load stdlib on first access
    StdlibFunctions =
        case get(stdlib_functions) of
            undefined ->
                Functions = load_stdlib_modules(),
                put(stdlib_functions, Functions),
                Functions;
            Functions ->
                Functions
        end,

    case maps:get({Module, Name, Arity}, StdlibFunctions, undefined) of
        undefined ->
            not_found;
        FunctionType ->
            % Return the function type as-is; instantiation happens at lookup time
            {ok, FunctionType}
    end.

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
    Env6 = cure_types:extend_env(Env5_1, 'Nat', {refined_type, 'Int', fun(N) -> N >= 0 end}),
    Env7 = cure_types:extend_env(Env6, 'Pos', {refined_type, 'Int', fun(N) -> N > 0 end}),

    % Add Nat constructors
    % Zero : Nat (nullary constructor)
    Env7_1 = cure_types:extend_env(Env7, 'Zero', {primitive_type, 'Nat'}),
    % Succ : Nat -> Nat (unary constructor)
    SuccType = {function_type, [{primitive_type, 'Nat'}], {primitive_type, 'Nat'}},
    Env7_2 = cure_types:extend_env(Env7_1, 'Succ', SuccType),

    % Add built-in functions
    % map : (A -> B) -> [A] -> [B]
    MapType =
        {function_type,
            [
                {function_type, [cure_types:new_type_var()], cure_types:new_type_var()},
                {list_type, cure_types:new_type_var(), undefined}
            ],
            {list_type, cure_types:new_type_var(), undefined}},
    Env8 = cure_types:extend_env(Env7_2, map, MapType),

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

    Env14.

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
convert_type_to_tuple(#dependent_type{name = Name, params = Params}) ->
    ConvertedParams = [convert_type_param_to_tuple(P) || P <- Params],
    {dependent_type, Name, ConvertedParams};
convert_type_to_tuple(#union_type{types = Variants}) ->
    ConvertedVariants = [convert_type_to_tuple(V) || V <- Variants],
    {union_type, ConvertedVariants};
convert_type_to_tuple(#function_type{params = Params, return_type = ReturnType}) ->
    ConvertedParams = [convert_type_to_tuple(P) || P <- Params],
    ConvertedReturn = convert_type_to_tuple(ReturnType),
    {function_type, ConvertedParams, ConvertedReturn};
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
convert_type_with_env({primitive_type, Name, _Location}, _Env) ->
    {primitive_type, Name};
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
            % Found in environment - MUST reuse existing type variable
            cure_utils:debug("Found ~p in environment, reusing: ~p~n", [Name, TypeVar]),
            case cure_types:is_type_var(TypeVar) of
                % It's already a proper type_var record - REUSE IT!
                true ->
                    TypeVar;
                % It's something else, treat as primitive
                false ->
                    {primitive_type, Name}
            end
    end;
convert_type_with_env(Type, _Env) ->
    % Fallback to regular conversion
    convert_type_to_tuple(Type).

%% Convert type parameter expressions while resolving type variables from environment
% Handle type_param in tuple format (from parser)
convert_type_param_with_env({type_param, _Name, Value, _Location}, Env) ->
    convert_type_with_env(Value, Env);
convert_type_param_with_env(TypeParam, Env) ->
    convert_type_with_env(TypeParam, Env).

convert_type_param_to_tuple(#type_param{value = Value}) ->
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
    [{FirstParamTypes, FirstReturnType} | RestTypes] = ClauseTypes,
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

%% Two-pass processing: collect function signatures first
collect_function_signatures(Items, Env) ->
    collect_function_signatures_helper(Items, Env).

collect_function_signatures_helper([], Env) ->
    Env;
collect_function_signatures_helper([Item | Rest], Env) ->
    cure_utils:debug("[COLLECT_SIG] Processing item: ~p~n", [element(1, Item)]),
    NewEnv =
        case Item of
            #function_def{
                name = Name,
                clauses = Clauses,
                params = Params,
                return_type = ReturnType,
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
                                convert_type_with_env(ReturnType, EnvWithParams)
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
            _ ->
                % Non-function items don't need pre-processing
                cure_utils:debug("[COLLECT_SIG] Unmatched item type: ~p~n", [Item]),
                Env
        end,
    collect_function_signatures_helper(Rest, NewEnv).

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

extract_type_params_helper(#dependent_type{params = Params}, Env) ->
    lists:foldl(
        fun(#type_param{value = Value}, AccEnv) ->
            extract_type_param_value(Value, AccEnv)
        end,
        Env,
        Params
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

extract_type_params_helper_safe(#dependent_type{params = Params}, Env) ->
    lists:foldl(
        fun(#type_param{value = Value}, AccEnv) ->
            extract_type_param_value_safe(Value, AccEnv)
        end,
        Env,
        Params
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
    % Check if it's a generic type variable and add it
    case is_generic_type_var(Name) of
        true ->
            extract_type_param_value_safe(#primitive_type{name = Name}, Env);
        false ->
            Env
    end;
% Handle tuple-form primitive types without location
extract_type_params_helper_safe({primitive_type, Name}, Env) ->
    % Check if it's a generic type variable and add it
    case is_generic_type_var(Name) of
        true ->
            extract_type_param_value_safe(#primitive_type{name = Name}, Env);
        false ->
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
    % Handle identifier expressions - if they're generic type variables, add them
    case is_generic_type_var(Name) of
        true ->
            extract_type_param_value_safe(#primitive_type{name = Name}, Env);
        false ->
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
check_dependent_constraint(_Constraint, Value, Type) ->
    % Simplified dependent constraint checking
    % In full implementation, would use SMT solver
    case Type of
        {refined_type, _BaseType, Predicate} ->
            try
                Predicate(Value)
            catch
                _:_ ->
                    false
            end;
        _ ->
            true
    end.

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
    % Assume it's a function with arity 1 by default
    FunctionType = create_imported_function_type(Module, Identifier, 1),
    NewEnv = cure_types:extend_env(Env, Identifier, FunctionType),
    {ok, NewEnv}.

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
