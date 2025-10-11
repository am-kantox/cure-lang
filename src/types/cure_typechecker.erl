%% Cure Programming Language - Type Checker
%% High-level type checker that works with parsed AST nodes
-module(cure_typechecker).

-export([
    check_program/1,
    check_module/1, check_module/2,
    check_function/1, check_function/2,
    check_expression/2, check_expression/3,

    % Built-in type constructors
    builtin_env/0,

    % Dependent type helpers
    check_dependent_constraint/3,
    infer_dependent_type/2,

    % Utility functions
    convert_type_to_tuple/1
]).

-include("../parser/cure_ast_simple.hrl").

%% Type checking result
-record(typecheck_result, {
    success :: boolean(),
    type :: term() | undefined,
    errors :: [typecheck_error()],
    warnings :: [typecheck_warning()]
}).

-record(typecheck_error, {
    message :: string(),
    location :: location(),
    details :: term()
}).

-record(typecheck_warning, {
    message :: string(),
    location :: location(),
    details :: term()
}).

%% Type definitions
-type typecheck_error() :: #typecheck_error{}.
-type typecheck_warning() :: #typecheck_warning{}.
-type location() :: term().

%% Check entire program
check_program(AST) ->
    Env = builtin_env(),
    check_items(AST, Env, #typecheck_result{
        success = true,
        type = undefined,
        errors = [],
        warnings = []
    }).

%% Check list of top-level items
check_items([], _Env, Result) ->
    Result;
check_items([Item | RestItems], Env, Result) ->
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
    check_module_new({module_def, Name, Imports, Exports, Items, Location}, Env);
check_item({module_def, Name, Exports, Items, Location}, Env) ->
    % Parser format without imports field - add empty imports
    check_module_new({module_def, Name, [], Exports, Items, Location}, Env);
check_item({function_def, Name, Params, ReturnType, Constraint, Body, Location}, Env) ->
    % Fallback for old tuple-based format without is_private field
    check_function_new({function_def, Name, Params, ReturnType, Constraint, Body, false, Location}, Env);
check_item({function_def, Name, Params, ReturnType, Constraint, Body, IsPrivate, Location}, Env) ->
    % New tuple format with is_private field
    check_function_new({function_def, Name, Params, ReturnType, Constraint, Body, IsPrivate, Location}, Env);
check_item({erlang_function_def, Name, Params, ReturnType, Constraint, ErlangBody, Location}, Env) ->
    check_erlang_function_new(
        {erlang_function_def, Name, Params, ReturnType, Constraint, ErlangBody, Location}, Env
    );
check_item({import_def, Module, Items, Location}, Env) ->
    check_import_new({import_def, Module, Items, Location}, Env);
check_item({export_list, ExportSpecs}, Env) ->
    % Export lists are handled during module checking - just pass through
    {ok, Env, success_result({export_list, ExportSpecs})};
check_item(FSM = #fsm_def{}, Env) ->
    check_fsm(FSM, Env);
check_item(TypeDef = #type_def{}, Env) ->
    check_type_definition(TypeDef, Env).

%% Check module definition
check_module(Module) ->
    check_module(Module, builtin_env()).

check_module(#module_def{name = Name, exports = Exports, items = Items}, Env) ->
    % Create module-scoped environment
    ModuleEnv = cure_types:extend_env(Env, module, Name),

    % Two-pass processing: collect function signatures first, then check bodies
    FunctionEnv = collect_function_signatures(Items, ModuleEnv),

    % Check all items in the module with function signatures available
    case check_items(Items, FunctionEnv, new_result()) of
        Result = #typecheck_result{success = true} ->
            % Verify exported functions exist and have correct arities
            case check_exports(Exports, Items) of
                ok ->
                    {ok, cure_types:extend_env(Env, Name, {module_type, Name}), Result};
                {error, ExportError} ->
                    {error, ExportError}
            end;
        Result ->
            {ok, Env, Result}
    end.

%% Check function definition
check_function(Function) ->
    check_function(Function, builtin_env()).

check_function(
    #function_def{
        name = Name,
        params = Params,
        return_type = ReturnType,
        constraint = Constraint,
        body = Body,
        is_private = _,
        location = Location
    },
    Env
) ->
    try
        % Convert parameters to type environment
        {ParamTypes, ParamEnv} = process_parameters(Params, Env),

        % Also extract type parameters from return type
        EnvWithReturnTypeParams =
            case ReturnType of
                undefined -> ParamEnv;
                _ -> extract_and_add_type_params(ReturnType, ParamEnv)
            end,

        % Check constraint if present
        case Constraint of
            undefined ->
                ok;
            _ ->
                case
                    cure_types:infer_type(
                        convert_expr_to_tuple(Constraint), EnvWithReturnTypeParams
                    )
                of
                    {ok, InferenceResult} ->
                        ConstraintType = element(2, InferenceResult),
                        case cure_types:unify(ConstraintType, {primitive_type, 'Bool'}) of
                            {ok, _} -> ok;
                            {error, Reason} -> throw({constraint_not_bool, Reason, Location})
                        end;
                    {error, Reason} ->
                        throw({constraint_inference_failed, Reason, Location})
                end
        end,

        % Check function body
        case cure_types:infer_type(convert_expr_to_tuple(Body), EnvWithReturnTypeParams) of
            {ok, InferenceResult2} ->
                BodyType = element(2, InferenceResult2),
                % Check return type if specified
                case ReturnType of
                    undefined ->
                        % Function type is inferred
                        FuncType = {function_type, ParamTypes, BodyType},
                        io:format("DEBUG: Adding function ~p to env with inferred type: ~p~n", [
                            Name, FuncType
                        ]),
                        NewEnv = cure_types:extend_env(Env, Name, FuncType),
                        {ok, NewEnv, success_result(FuncType)};
                    _ ->
                        % Check body matches declared return type
                        ExpectedReturnType = convert_type_to_tuple(ReturnType),
                        io:format("DEBUG: Function ~p - body type: ~p, expected: ~p~n", [
                            Name, BodyType, ExpectedReturnType
                        ]),
                        case cure_types:unify(BodyType, ExpectedReturnType) of
                            {ok, _} ->
                                FuncType = {function_type, ParamTypes, ExpectedReturnType},
                                io:format("DEBUG: Adding function ~p to env with type: ~p~n", [
                                    Name, FuncType
                                ]),
                                NewEnv = cure_types:extend_env(Env, Name, FuncType),
                                {ok, NewEnv, success_result(FuncType)};
                            {error, UnifyReason} ->
                                ErrorMsg = #typecheck_error{
                                    message =
                                        "Function body type doesn't match declared return type",
                                    location = Location,
                                    details =
                                        {type_mismatch, ExpectedReturnType, BodyType, UnifyReason}
                                },
                                {ok, Env, error_result(ErrorMsg)}
                        end
                end;
            {error, InferReason} ->
                ErrorMsg2 = #typecheck_error{
                    message = "Failed to infer function body type",
                    location = Location,
                    details = {inference_failed, InferReason}
                },
                {ok, Env, error_result(ErrorMsg2)}
        end
    catch
        throw:{ErrorType, Details, ErrorLocation} ->
            ThrownError = #typecheck_error{
                message = format_error_type(ErrorType),
                location = ErrorLocation,
                details = Details
            },
            {ok, Env, error_result(ThrownError)}
    end.

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
            Error = #typecheck_error{
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
check_module_new({module_def, Name, Imports, Exports, Items, _Location}, Env) ->
    % Create module-scoped environment
    ModuleEnv = cure_types:extend_env(Env, module, Name),

    % Process imports first to extend environment
    ImportEnv =
        case process_imports(Imports, ModuleEnv) of
            {ok, TempEnv} ->
                % Add standard library function types if importing from Std
                case
                    lists:any(
                        fun
                            ({import_def, 'Std', _, _}) -> true;
                            (_) -> false
                        end,
                        Imports
                    )
                of
                    true ->
                        add_std_function_types(TempEnv);
                    false ->
                        TempEnv
                end;
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
            ExportSpecs = extract_export_specs(Exports, Items),
            case check_exports_new(ExportSpecs, Items) of
                ok ->
                    {ok, cure_types:extend_env(Env, Name, {module_type, Name}), Result};
                {error, ExportError} ->
                    {error, ExportError}
            end;
        Result ->
            {ok, Env, Result}
    end.

%% Check function definition - New AST format
% 7-parameter format (old format without is_private)
check_function_new({function_def, Name, Params, ReturnType, Constraint, Body, Location}, Env) ->
    check_function_new({function_def, Name, Params, ReturnType, Constraint, Body, false, Location}, Env);
% 8-parameter format (new format with is_private)
check_function_new({function_def, Name, Params, ReturnType, Constraint, Body, IsPrivate, Location}, Env) ->
    try
        % Convert parameters to type environment and extract type parameters
        {ParamTypes, ParamEnv} = process_parameters_new(Params, Env),

        % Also extract type parameters from return type if present
        EnvWithReturnTypeParams =
            case ReturnType of
                undefined -> ParamEnv;
                _ -> extract_and_add_type_params(ReturnType, ParamEnv)
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
        case cure_types:infer_type(convert_expr_to_tuple(Body), FinalEnv) of
            {ok, InferenceResult2} ->
                BodyType = element(2, InferenceResult2),
                % Check return type if specified
                case ReturnType of
                    undefined ->
                        % Function type is inferred
                        FuncType = {function_type, ParamTypes, BodyType},
                        io:format("DEBUG: Adding function ~p (new AST) with inferred type: ~p~n", [
                            Name, FuncType
                        ]),
                        NewEnv = cure_types:extend_env(Env, Name, FuncType),
                        {ok, NewEnv, success_result(FuncType)};
                    _ ->
                        % Check body matches declared return type
                        ExpectedReturnType = convert_type_to_tuple(ReturnType),
                        case cure_types:unify(BodyType, ExpectedReturnType) of
                            {ok, _} ->
                                FuncType = {function_type, ParamTypes, ExpectedReturnType},
                                io:format(
                                    "DEBUG: Adding function ~p (new AST) with explicit type: ~p~n",
                                    [Name, FuncType]
                                ),
                                NewEnv = cure_types:extend_env(Env, Name, FuncType),
                                {ok, NewEnv, success_result(FuncType)};
                            {error, UnifyReason} ->
                                ErrorMsg = #typecheck_error{
                                    message =
                                        "Function body type doesn't match declared return type",
                                    location = Location,
                                    details =
                                        {type_mismatch, ExpectedReturnType, BodyType, UnifyReason}
                                },
                                {ok, Env, error_result(ErrorMsg)}
                        end
                end;
            {error, InferReason} ->
                io:format("*** DEBUG: FUNCTION BODY INFERENCE FAILED ***~n"),
                io:format("*** Function: ~p~n", [Name]),
                io:format("*** Body: ~p~n", [Body]),
                io:format("*** Error: ~p~n", [InferReason]),
                io:format("*** Environment size: ~p functions~n", [
                    map_size(
                        case FinalEnv of
                            #{} -> FinalEnv;
                            _ -> #{}
                        end
                    )
                ]),
                io:format("DEBUG: Failed to infer function ~p body type: ~p~n", [Name, InferReason]),
                ErrorMsg2 = #typecheck_error{
                    message = "Failed to infer function body type",
                    location = Location,
                    details = {inference_failed, InferReason}
                },
                {ok, Env, error_result(ErrorMsg2)}
        end
    catch
        throw:{ErrorType, Details, ErrorLocation} ->
            ThrownError = #typecheck_error{
                message = format_error_type(ErrorType),
                location = ErrorLocation,
                details = Details
            },
            {ok, Env, error_result(ThrownError)}
    end.

%% Check Erlang function definition (def_erl) - New AST format
%% For def_erl functions, we trust the type annotations and skip body type checking
check_erlang_function_new(
    {erlang_function_def, Name, Params, ReturnType, Constraint, ErlangBody, Location}, Env
) ->
    try
        % Convert parameters to type environment
        {ParamTypes, ParamEnv} = process_parameters_new(Params, Env),

        % Check constraint if present (same as regular functions)
        case Constraint of
            undefined ->
                ok;
            _ ->
                case cure_types:infer_type(convert_expr_to_tuple(Constraint), ParamEnv) of
                    {ok, InferenceResult} ->
                        ConstraintType = element(2, InferenceResult),
                        case cure_types:unify(ConstraintType, {primitive_type, 'Bool'}) of
                            {ok, _} -> ok;
                            {error, Reason} -> throw({constraint_not_bool, Reason, Location})
                        end;
                    {error, Reason} ->
                        throw({constraint_inference_failed, Reason, Location})
                end
        end,

        % For def_erl functions, the return type MUST be specified (enforced by parser)
        % We trust the type annotation and don't check the Erlang body
        case ReturnType of
            undefined ->
                % This should never happen as parser enforces return type for def_erl
                throw({missing_return_type_for_def_erl, Location});
            _ ->
                ExpectedReturnType = convert_type_to_tuple(ReturnType),
                FuncType = {erlang_function_type, ParamTypes, ExpectedReturnType, ErlangBody},
                NewEnv = cure_types:extend_env(Env, Name, FuncType),
                {ok, NewEnv, success_result(FuncType)}
        end
    catch
        throw:{ErrorType, Details, ErrorLocation} ->
            ThrownError = #typecheck_error{
                message = format_error_type(ErrorType),
                location = ErrorLocation,
                details = Details
            },
            {ok, Env, error_result(ThrownError)}
    end.

%% Add basic function types for Std module functions
add_std_function_types(Env) ->
    % Add commonly used Std functions with their types
    % Note: T, U, V are type variables
    TVar = cure_types:new_type_var('T'),
    UVar = cure_types:new_type_var('U'),
    VVar = cure_types:new_type_var('V'),

    % zip_with: (List(T), List(U), (T, U) -> V) -> List(V)
    ZipWithType =
        {function_type,
            [
                {list_type, TVar, undefined},
                {list_type, UVar, undefined},
                {function_type, [TVar, UVar], VVar}
            ],
            {list_type, VVar, undefined}},

    % fold: (List(T), U, (T, U) -> U) -> U
    FoldType =
        {function_type,
            [
                {list_type, TVar, undefined},
                UVar,
                {function_type, [TVar, UVar], UVar}
            ],
            UVar},

    % map: (List(T), (T -> U)) -> List(U)
    MapType =
        {function_type,
            [
                {list_type, TVar, undefined},
                {function_type, [TVar], UVar}
            ],
            {list_type, UVar, undefined}},

    % show: T -> String
    ShowType = {function_type, [TVar], {primitive_type, 'String'}},

    % print: String -> Unit
    PrintType = {function_type, [{primitive_type, 'String'}], {primitive_type, 'Unit'}},

    % Add all function types to environment
    Env1 = cure_types:extend_env(Env, zip_with, ZipWithType),
    Env2 = cure_types:extend_env(Env1, fold, FoldType),
    Env3 = cure_types:extend_env(Env2, map, MapType),
    Env4 = cure_types:extend_env(Env3, show, ShowType),
    Env5 = cure_types:extend_env(Env4, print, PrintType),
    Env5.

%% Check import - New AST format
check_import_new({import_def, Module, Items, _Location}, Env) ->
    case check_import_items_new(Module, Items, Env) of
        {ok, NewEnv} ->
            ImportType = {import_type, Module, Items},
            {ok, NewEnv, success_result(ImportType)};
        {error, Error} ->
            {ok, Env, error_result(Error)}
    end.

%% Check type definition
check_type_definition(#type_def{name = Name, definition = Definition}, Env) ->
    % For now, just add the type to environment
    TypeDefType = convert_type_to_tuple(Definition),
    NewEnv = cure_types:extend_env(Env, Name, TypeDefType),
    {ok, NewEnv, success_result(TypeDefType)}.

%% Create function type for imported function with given arity
create_imported_function_type(Module, Name, Arity) ->
    % Generate parameter types
    ParamTypes = [cure_types:new_type_var() || _ <- lists:seq(1, Arity)],
    ReturnType = cure_types:new_type_var(),
    {imported_function_type, Module, Name, ParamTypes, ReturnType}.

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
                            Error = #typecheck_error{
                                message = "Expression type doesn't match expected type",
                                location = get_expr_location_safe(Expr),
                                details = {type_mismatch, ExpectedType, InferredType, Reason}
                            },
                            error_result(Error)
                    end
            end;
        {error, Reason} ->
            Error = #typecheck_error{
                message = "Failed to infer expression type",
                location = get_expr_location_safe(Expr),
                details = {inference_failed, Reason}
            },
            error_result(Error)
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

    % Add built-in functions
    % map : (A -> B) -> [A] -> [B]
    MapType =
        {function_type,
            [
                {function_type, [cure_types:new_type_var()], cure_types:new_type_var()},
                {list_type, cure_types:new_type_var(), undefined}
            ],
            {list_type, cure_types:new_type_var(), undefined}},
    Env8 = cure_types:extend_env(Env7, map, MapType),

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

    % Add standard library function types
    Env12 = add_std_function_types(Env11),

    % Add constants
    Env13 = cure_types:extend_env(Env12, ok, {primitive_type, 'Unit'}),

    Env13.

%% Helper functions
process_parameters(Params, Env) ->
    process_parameters(Params, Env, [], Env).

process_parameters([], _OrigEnv, TypesAcc, EnvAcc) ->
    {lists:reverse(TypesAcc), EnvAcc};
process_parameters([#param{name = Name, type = TypeExpr} | RestParams], OrigEnv, TypesAcc, EnvAcc) ->
    ParamType = convert_type_to_tuple(TypeExpr),

    % Extract type parameters from dependent types and add them to environment
    % but only add new type parameters, not ones that already exist
    EnvWithTypeParams = extract_and_add_type_params_safe(TypeExpr, EnvAcc),

    % Add the parameter itself to environment
    NewEnvAcc = cure_types:extend_env(EnvWithTypeParams, Name, ParamType),
    process_parameters(RestParams, OrigEnv, [ParamType | TypesAcc], NewEnvAcc).

check_exports([], _Items) ->
    ok;
check_exports([#export_spec{name = Name, arity = Arity} | RestExports], Items) ->
    case find_function(Name, Items) of
        {ok, #function_def{params = Params}} ->
            case length(Params) =:= Arity of
                true -> check_exports(RestExports, Items);
                false -> {error, {export_arity_mismatch, Name, Arity, length(Params)}}
            end;
        not_found ->
            {error, {exported_function_not_found, Name, Arity}}
    end.

find_function(Name, [#function_def{name = Name} = Function | _]) ->
    {ok, Function};
find_function(Name, [_ | RestItems]) ->
    find_function(Name, RestItems);
find_function(_Name, []) ->
    not_found.

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
convert_expr_to_tuple(#binary_op_expr{op = Op, left = Left, right = Right, location = Location}) ->
    {binary_op_expr, Op, convert_expr_to_tuple(Left), convert_expr_to_tuple(Right), Location};
convert_expr_to_tuple(#function_call_expr{function = Function, args = Args, location = Location}) ->
    {function_call_expr, convert_expr_to_tuple(Function),
        [convert_expr_to_tuple(Arg) || Arg <- Args], Location};
convert_expr_to_tuple(#if_expr{
    condition = Condition,
    then_branch = ThenBranch,
    else_branch = ElseBranch,
    location = Location
}) ->
    {if_expr, convert_expr_to_tuple(Condition), convert_expr_to_tuple(ThenBranch),
        convert_expr_to_tuple(ElseBranch), Location};
convert_expr_to_tuple(#let_expr{bindings = Bindings, body = Body, location = Location}) ->
    ConvertedBindings = [convert_binding_to_tuple(B) || B <- Bindings],
    {let_expr, ConvertedBindings, convert_expr_to_tuple(Body), Location};
convert_expr_to_tuple(#list_expr{elements = Elements, location = Location}) ->
    {list_expr, [convert_expr_to_tuple(E) || E <- Elements], Location};
convert_expr_to_tuple(#block_expr{expressions = Expressions, location = Location}) ->
    % Convert block to sequence of let expressions
    convert_block_to_lets(Expressions, Location);
convert_expr_to_tuple(#lambda_expr{params = Params, body = Body, location = Location}) ->
    ConvertedParams = [convert_param_to_tuple(P) || P <- Params],
    {lambda_expr, ConvertedParams, convert_expr_to_tuple(Body), Location};
convert_expr_to_tuple(#unary_op_expr{op = Op, operand = Operand, location = Location}) ->
    {unary_op_expr, Op, convert_expr_to_tuple(Operand), Location};
convert_expr_to_tuple(#match_expr{expr = Expr, patterns = Patterns, location = Location}) ->
    ConvertedPatterns = [convert_match_clause_to_tuple(P) || P <- Patterns],
    {match_expr, convert_expr_to_tuple(Expr), ConvertedPatterns, Location};
convert_expr_to_tuple(#cons_expr{elements = Elements, tail = Tail, location = Location}) ->
    ConvertedElements = [convert_expr_to_tuple(E) || E <- Elements],
    ConvertedTail = convert_expr_to_tuple(Tail),
    {cons_expr, ConvertedElements, ConvertedTail, Location};
convert_expr_to_tuple(Expr) ->
    % Fallback - return as-is for unsupported expressions
    Expr.

convert_binding_to_tuple(#binding{pattern = Pattern, value = Value, location = Location}) ->
    {binding, convert_pattern_to_tuple(Pattern), convert_expr_to_tuple(Value), Location}.

convert_pattern_to_tuple(#identifier_pattern{name = Name, location = Location}) ->
    {identifier_pattern, Name, Location};
convert_pattern_to_tuple(#literal_pattern{value = Value, location = Location}) ->
    {literal_pattern, Value, Location};
convert_pattern_to_tuple(#list_pattern{elements = Elements, tail = Tail, location = Location}) ->
    ConvertedElements = [convert_pattern_to_tuple(E) || E <- Elements],
    ConvertedTail =
        case Tail of
            undefined -> undefined;
            _ -> convert_pattern_to_tuple(Tail)
        end,
    {list_pattern, ConvertedElements, ConvertedTail, Location};
convert_pattern_to_tuple(#record_pattern{name = Name, fields = Fields, location = Location}) ->
    ConvertedFields = [convert_field_pattern_to_tuple(F) || F <- Fields],
    {record_pattern, Name, ConvertedFields, Location};
convert_pattern_to_tuple(#wildcard_pattern{location = Location}) ->
    {wildcard_pattern, Location};
convert_pattern_to_tuple(#constructor_pattern{name = Name, args = Args, location = Location}) ->
    ConvertedArgs =
        case Args of
            undefined -> undefined;
            [] -> [];
            ArgList -> [convert_pattern_to_tuple(Arg) || Arg <- ArgList]
        end,
    {constructor_pattern, Name, ConvertedArgs, Location};
convert_pattern_to_tuple(Pattern) ->
    Pattern.

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
convert_type_to_tuple(#identifier_expr{name = Name}) when
    Name =:= 'Float' orelse Name =:= 'Int' orelse Name =:= 'Bool' orelse
        Name =:= 'String' orelse Name =:= 'Unit'
->
    % Convert primitive type identifiers to primitive_type tuples
    {primitive_type, Name};
convert_type_to_tuple(Type) ->
    Type.

convert_type_param_to_tuple(#type_param{value = Value}) ->
    case Value of
        TypeExpr when
            is_record(TypeExpr, primitive_type);
            is_record(TypeExpr, dependent_type)
        ->
            #type_param{value = convert_type_to_tuple(TypeExpr)};
        #identifier_expr{name = Name} when
            Name =:= 'Float' orelse Name =:= 'Int' orelse Name =:= 'Bool' orelse
                Name =:= 'String' orelse Name =:= 'Unit'
        ->
            % Convert primitive type identifiers to primitive_type tuples
            #type_param{value = {primitive_type, Name}};
        _ ->
            #type_param{value = Value}
    end.

%% Two-pass processing: collect function signatures first
collect_function_signatures(Items, Env) ->
    collect_function_signatures_helper(Items, Env).

collect_function_signatures_helper([], Env) ->
    Env;
collect_function_signatures_helper([Item | Rest], Env) ->
    NewEnv = case Item of
        #function_def{name = Name, params = Params, return_type = ReturnType, is_private = _} ->
            % Create function type from signature
            try
                {ParamTypes, _} = process_parameters_new(Params, Env),
                FinalReturnType = case ReturnType of
                    undefined -> cure_types:new_type_var();
                    _ -> convert_type_to_tuple(ReturnType)
                end,
                FuncType = {function_type, ParamTypes, FinalReturnType},
                cure_types:extend_env(Env, Name, FuncType)
            catch
                _:Error ->
                    io:format("WARNING: Failed to pre-process function ~p signature: ~p~n", [Name, Error]),
                    Env
            end;
        #type_def{name = Name} ->
            % Add type definitions to environment as well
            try
                case check_type_definition(Item, Env) of
                    {ok, NewTypeEnv, _Result} -> NewTypeEnv;
                    _ -> Env
                end
            catch
                _:_ -> Env
            end;
        _ ->
            % Non-function items don't need pre-processing
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
    Result#typecheck_result{
        success = false,
        errors = [Error | Errors]
    }.

merge_results(
    Result1 = #typecheck_result{errors = E1, warnings = W1},
    #typecheck_result{success = S2, errors = E2, warnings = W2}
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
        _:_ -> #location{line = 0, column = 0, file = undefined}
    end.

get_expr_location(#literal_expr{location = Loc}) -> Loc;
get_expr_location(#identifier_expr{location = Loc}) -> Loc;
get_expr_location(#binary_op_expr{location = Loc}) -> Loc;
get_expr_location(#function_call_expr{location = Loc}) -> Loc;
get_expr_location(#if_expr{location = Loc}) -> Loc;
get_expr_location(#let_expr{location = Loc}) -> Loc;
get_expr_location(#list_expr{location = Loc}) -> Loc;
get_expr_location(#block_expr{location = Loc}) -> Loc;
get_expr_location(_) -> #location{line = 0, column = 0, file = undefined}.

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
extract_type_params_helper(#list_type{element_type = ElemType, length = LengthExpr}, Env) ->
    % Handle list types with length expressions
    Env1 = extract_type_params_helper(ElemType, Env),
    case LengthExpr of
        undefined -> Env1;
        _ -> extract_type_param_value(LengthExpr, Env1)
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
extract_type_params_helper_safe(#list_type{element_type = ElemType, length = LengthExpr}, Env) ->
    % Handle list types with length expressions
    Env1 = extract_type_params_helper_safe(ElemType, Env),
    case LengthExpr of
        undefined -> Env1;
        _ -> extract_type_param_value_safe(LengthExpr, Env1)
    end;
extract_type_params_helper_safe(_, Env) ->
    Env.

extract_type_param_value(#identifier_expr{name = Name}, Env) ->
    % Add identifier as a length parameter (typically numeric for dependent types)
    cure_types:extend_env(Env, Name, {primitive_type, 'Int'});
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
            % Add identifier as a length parameter (typically numeric for dependent types)
            cure_types:extend_env(Env, Name, {primitive_type, 'Int'});
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
                _:_ -> false
            end;
        _ ->
            true
    end.

infer_dependent_type(Expr, Env) ->
    % Simplified dependent type inference
    % In full implementation, would infer refinement predicates
    case cure_types:infer_type(convert_expr_to_tuple(Expr), Env) of
        {ok, Result} -> {ok, Result};
        Error -> Error
    end.

%% Helper functions for new AST format
process_imports([], Env) ->
    {ok, Env};
process_imports([Import | RestImports], Env) ->
    case check_import_new(Import, Env) of
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
        [{export_spec, _, _, _} | _] -> ExportSpecs; % List of export_spec tuples
        _ -> ExportSpecs  % Pass through other formats
    end;
extract_export_specs([_ | RestExports], Items) ->
    extract_export_specs(RestExports, Items).

check_exports_new([], _Items) ->
    ok;
check_exports_new([{export_spec, Name, Arity, _Location} | RestExports], Items) ->
    case find_function_new(Name, Items) of
        {ok, {function_def, _Name, Params, _ReturnType, _Constraint, _Body, IsPrivate, _UnusedLocation}} ->
            case IsPrivate of
                true -> 
                    {error, {cannot_export_private_function, Name, Arity}};
                false ->
                    case length(Params) =:= Arity of
                        true -> check_exports_new(RestExports, Items);
                        false -> {error, {export_arity_mismatch, Name, Arity, length(Params)}}
                    end
            end;
        {ok,
            {erlang_function_def, _Name, Params, _ReturnType, _Constraint, _ErlangBody,
                _UnusedLocation}} ->
            case length(Params) =:= Arity of
                true -> check_exports_new(RestExports, Items);
                false -> {error, {export_arity_mismatch, Name, Arity, length(Params)}}
            end;
        not_found ->
            {error, {exported_function_not_found, Name, Arity}}
    end.

find_function_new(Name, [#function_def{name = Name, params = Params, return_type = ReturnType, constraint = Constraint, body = Body, is_private = IsPrivate, location = Location} | _]) ->
    {ok, {function_def, Name, Params, ReturnType, Constraint, Body, IsPrivate, Location}};
find_function_new(Name, [{function_def, Name, Params, ReturnType, Constraint, Body, Location} | _]) ->
    % Fallback for old tuple-based format without is_private field
    {ok, {function_def, Name, Params, ReturnType, Constraint, Body, false, Location}};
find_function_new(Name, [
    {erlang_function_def, Name, Params, ReturnType, Constraint, ErlangBody, Location} | _
]) ->
    {ok, {erlang_function_def, Name, Params, ReturnType, Constraint, ErlangBody, Location}};
find_function_new(Name, [_ | RestItems]) ->
    find_function_new(Name, RestItems);
find_function_new(_Name, []) ->
    not_found.

process_parameters_new(Params, Env) ->
    process_parameters_new(Params, Env, [], Env).

process_parameters_new([], _OrigEnv, TypesAcc, EnvAcc) ->
    {lists:reverse(TypesAcc), EnvAcc};
process_parameters_new(
    [{param, Name, TypeExpr, _Location} | RestParams], OrigEnv, TypesAcc, EnvAcc
) ->
    ParamType = convert_type_to_tuple(TypeExpr),
    % Extract type parameters from dependent types and add them to environment
    EnvWithTypeParams = extract_and_add_type_params(TypeExpr, EnvAcc),
    % Add the parameter itself to environment
    NewEnvAcc = cure_types:extend_env(EnvWithTypeParams, Name, ParamType),
    process_parameters_new(RestParams, OrigEnv, [ParamType | TypesAcc], NewEnvAcc).

check_import_items_new(Module, Items, Env) ->
    import_items_new(Module, Items, Env).

import_items_new(_Module, [], AccEnv) ->
    {ok, AccEnv};
import_items_new(Module, [Item | RestItems], AccEnv) ->
    case import_item_new(Module, Item, AccEnv) of
        {ok, NewAccEnv} ->
            import_items_new(Module, RestItems, NewAccEnv);
        {error, Error} ->
            {error, Error}
    end.

import_item_new(Module, {function_import, Name, Arity, _Location}, Env) ->
    FunctionType = create_imported_function_type(Module, Name, Arity),
    NewEnv = cure_types:extend_env(Env, Name, FunctionType),
    {ok, NewEnv};
import_item_new(Module, Identifier, Env) when is_atom(Identifier) ->
    IdentifierType = {imported_identifier, Module, Identifier},
    NewEnv = cure_types:extend_env(Env, Identifier, IdentifierType),
    {ok, NewEnv}.

%% Additional converter functions
convert_param_to_tuple({param, Name, TypeExpr, Location}) ->
    {param, Name, convert_type_to_tuple(TypeExpr), Location}.

convert_match_clause_to_tuple(#match_clause{
    pattern = Pattern, guard = Guard, body = Body, location = Location
}) ->
    ConvertedGuard =
        case Guard of
            undefined -> undefined;
            _ -> convert_expr_to_tuple(Guard)
        end,
    {match_clause, convert_pattern_to_tuple(Pattern), ConvertedGuard, convert_expr_to_tuple(Body),
        Location}.

convert_field_pattern_to_tuple(#field_pattern{name = Name, pattern = Pattern, location = Location}) ->
    {field_pattern, Name, convert_pattern_to_tuple(Pattern), Location}.

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
                io:format("Warning: Could not convert constraint to SMT: ~p~n", [Reason]),
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
            Op =:= '>' orelse Op =:= '<' orelse Op =:= '>=' orelse Op =:= '=<' orelse Op =:= '=='
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
convert_expr_to_smt_term({binary_op_expr, 'mod', Left, Right, _}, Env) ->
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
    io:format("Added ~p SMT constraints for when clause verification~n", [length(SmtConstraints)]),
    Env.
