%% Cure LSP Type Holes
%% Idris-style type holes with SMT-based inference
-module(cure_lsp_type_holes).

-moduledoc """
# Type Holes - Interactive Type Inference

Provides Idris-style type holes where you can write:
- `?hole` - Named hole (e.g., `?returnType`)
- `_` - Anonymous hole

## Features

1. **Hover on hole** - Shows inferred type
2. **Code action** - "Fill in hole with: List(Int)"
3. **SMT-based inference** - Uses type checker + constraint solving

## Usage Examples

### Return Type Hole
```cure
def double_list(numbers: List(Int)): ? =
    map(numbers, fn(x) -> x * 2 end)
    
% Hover shows: ?returnType :: List(Int)
% Code action: Fill in return type
```

### Parameter Type Hole
```cure
def process(x: _): Int =
    x + 1
    
% Infers: x :: Int
```

### Expression Type Hole
```cure
let result: ? = compute_value()
% Shows inferred type from compute_value
```

## Implementation

Type holes are detected during parsing and marked in the AST.
The LSP provides:
1. Diagnostics (info-level) for each hole
2. Hover information with inferred type
3. Code action to fill in the type
""".

-export([
    % Detection
    find_type_holes/1,
    is_type_hole/1,

    % Inference
    infer_hole_type/3,
    infer_from_context/3,

    % LSP integration
    generate_hole_diagnostics/2,
    generate_hole_code_actions/3,
    generate_hole_hover/3,

    % Utilities
    hole_name/1,
    format_inferred_type/1
]).

-include("../parser/cure_ast.hrl").

%%% ============================================================================
%%% Type Hole Detection
%%% ============================================================================

%% @doc Find all type holes in AST
-spec find_type_holes(term()) -> [{atom(), term(), #location{}}].
find_type_holes(AST) when is_list(AST) ->
    lists:flatmap(fun find_type_holes/1, AST);
find_type_holes(#module_def{items = Items}) ->
    find_type_holes(Items);
find_type_holes(
    #function_def{
        name = Name,
        params = Params,
        return_type = RetType,
        location = Loc
    } = Func
) ->
    Holes = [],

    % Check return type hole
    RetHoles =
        case is_type_hole(RetType) of
            true ->
                HoleName = hole_name(RetType),
                % Use the location from the return type itself, if available
                HoleLoc =
                    case RetType of
                        #primitive_type{location = TypeLoc} when TypeLoc =/= undefined -> TypeLoc;
                        % Fallback to function location
                        _ -> Loc
                    end,
                [{HoleName, {return_type, Func}, HoleLoc}];
            false ->
                []
        end,

    % Check parameter type holes
    ParamHoles =
        case Params of
            undefined ->
                [];
            [] ->
                [];
            _ when is_list(Params) ->
                lists:flatmap(
                    fun(#param{name = ParamName, type = ParamType, location = ParamLoc}) ->
                        case is_type_hole(ParamType) of
                            true ->
                                [{hole_name(ParamType), {param_type, Name, ParamName}, ParamLoc}];
                            false ->
                                []
                        end
                    end,
                    Params
                );
            _ ->
                []
        end,

    RetHoles ++ ParamHoles ++ Holes;
find_type_holes(#let_expr{bindings = Bindings}) ->
    % Check bindings for type holes
    lists:flatmap(
        fun(#binding{pattern = Pattern, value = _Value, location = Loc}) ->
            % For now, we don't track type annotations in bindings
            % This would need enhancement to support let x: ? = ...
            []
        end,
        Bindings
    );
find_type_holes(_) ->
    [].

%% @doc Check if a type expression is a hole
-spec is_type_hole(term()) -> boolean().
is_type_hole(undefined) ->
    false;
is_type_hole(#primitive_type{name = '_'}) ->
    true;
is_type_hole(#identifier_expr{name = Name}) when is_atom(Name) ->
    % Check if name starts with '?'
    NameStr = atom_to_list(Name),
    case NameStr of
        [$? | _] -> true;
        "_" -> true;
        _ -> false
    end;
is_type_hole(_) ->
    false.

%% @doc Extract hole name
hole_name(#primitive_type{name = '_'}) ->
    '_';
hole_name(#identifier_expr{name = Name}) ->
    Name;
hole_name(_) ->
    '_'.

%%% ============================================================================
%%% Type Inference for Holes
%%% ============================================================================

%% @doc Infer type for a hole using type checker and SMT
-spec infer_hole_type(term(), term(), map()) -> {ok, term()} | {error, term()}.
infer_hole_type({return_type, FuncDef}, AST, _State) ->
    % Infer return type from function body
    infer_function_return_type(FuncDef, AST);
infer_hole_type({param_type, _FuncName, ParamName}, AST, State) ->
    % Infer parameter type from usage
    infer_parameter_type(ParamName, AST, State);
infer_hole_type({let_binding, _Pattern}, _AST, _State) ->
    % Infer from right-hand side of let
    {ok, #primitive_type{name = 'Int', location = undefined}}.

%% @doc Infer function return type from body using full type checker
infer_function_return_type(
    #function_def{
        body = Body,
        params = Params,
        return_type = ReturnType,
        clauses = Clauses,
        name = Name,
        location = Location
    } = FuncDef,
    AST
) when Body =/= undefined orelse (Clauses =/= undefined andalso length(Clauses) > 0) ->
    % Build environment with imports from the module
    try
        % Build environment with imports
        case build_module_env(AST) of
            {ok, EnvWithImports} ->
                % For multi-clause functions, check just the first clause to get the inferred type
                % This avoids the issue where check_multiclause_function returns the original env
                case Clauses of
                    undefined ->
                        % Single-clause function with body
                        CheckParams = Params,
                        CheckReturnType =
                            case is_type_hole(ReturnType) of
                                true -> undefined;
                                false -> ReturnType
                            end,
                        CheckBody = Body;
                    [FirstClause | _] ->
                        % Multi-clause function - use first clause
                        CheckParams = FirstClause#function_clause.params,
                        ClauseReturnType = FirstClause#function_clause.return_type,
                        CheckReturnType =
                            case is_type_hole(ClauseReturnType) of
                                true -> undefined;
                                false -> ClauseReturnType
                            end,
                        CheckBody = FirstClause#function_clause.body;
                    _ ->
                        CheckParams = Params,
                        CheckReturnType = undefined,
                        CheckBody = Body
                end,

                % Create a synthetic single-clause function def for type checking
                % We'll need to export it or use an alternative approach
                % For now, let's try using the internal check by calling check_function on a synthetic single-clause function
                SyntheticFuncDef = #function_def{
                    name = Name,
                    type_params = undefined,
                    clauses = undefined,
                    params = CheckParams,
                    return_type = CheckReturnType,
                    constraint = undefined,
                    body = CheckBody,
                    where_clause = undefined,
                    is_private = false,
                    location = Location
                },

                case cure_typechecker:check_function(SyntheticFuncDef, EnvWithImports) of
                    {ok, NewEnv, {typecheck_result, true, ResultType, _Errors, _Warnings}} ->
                        % Look up the function in the environment
                        FunType = cure_types:lookup_env(NewEnv, Name),
                        case FunType of
                            undefined ->
                                % Function not in environment, use ResultType directly
                                RetType = extract_return_type(ResultType),
                                ReturnAstType = convert_type_to_ast_format(RetType),
                                {ok, ReturnAstType};
                            _ ->
                                % Extract return type from function type in environment
                                RetType = extract_return_type(FunType),
                                % Try to resolve type variables by looking at parameter types
                                ResolvedRetType = resolve_type_variables(RetType, FunType),
                                ReturnAstType = convert_type_to_ast_format(ResolvedRetType),
                                {ok, ReturnAstType}
                        end;
                    {ok, _NewEnv, {typecheck_result, false, _ResultType, Errors, _Warnings}} ->
                        {error, {typecheck_failed, Errors}};
                    {error, Reason} = Error ->
                        Error
                end;
            {error, Reason} = Error ->
                Error
        end
    catch
        Class:Exception:_Stacktrace ->
            {error, {exception, Class, Exception}}
    end;
infer_function_return_type(#function_def{clauses = Clauses} = FuncDef, AST) when
    Clauses =/= undefined, length(Clauses) > 0
->
    % Multi-clause function - use the first clause's body
    [FirstClause | _] = Clauses,
    ClauseBody = FirstClause#function_clause.body,
    ClauseParams = FirstClause#function_clause.params,
    % Create a synthetic function_def with the first clause's body and params
    SyntheticFuncDef = FuncDef#function_def{body = ClauseBody, params = ClauseParams},
    infer_function_return_type(SyntheticFuncDef, AST);
infer_function_return_type(_FuncDef, _AST) ->
    % Cannot infer - body and clauses both undefined
    {error, cannot_infer}.

%% @doc Build type environment from module (including imports)
build_module_env(AST) when is_list(AST) ->
    % Check if AST contains a module_def
    case [M || M <- AST, is_record(M, module_def)] of
        [#module_def{items = Items} | _] ->
            % Module items include imports - extract them
            BaseEnv = cure_typechecker:builtin_env(),
            Imports = [Item || Item <- Items, is_record(Item, import_def)],
            case process_imports_for_env(Imports, BaseEnv) of
                {ok, EnvWithImports} ->
                    {ok, EnvWithImports};
                {error, _Reason} ->
                    {ok, BaseEnv}
            end;
        [] ->
            % No module_def, try to find import_def records in list
            BaseEnv = cure_typechecker:builtin_env(),
            Imports = [Item || Item <- AST, is_record(Item, import_def)],
            case process_imports_for_env(Imports, BaseEnv) of
                {ok, EnvWithImports} ->
                    {ok, EnvWithImports};
                {error, _} ->
                    {ok, BaseEnv}
            end
    end;
build_module_env(#module_def{items = Items}) ->
    % Module record passed directly - get imports from items
    BaseEnv = cure_typechecker:builtin_env(),
    Imports = [Item || Item <- Items, is_record(Item, import_def)],
    case process_imports_for_env(Imports, BaseEnv) of
        {ok, EnvWithImports} ->
            {ok, EnvWithImports};
        {error, _} ->
            {ok, BaseEnv}
    end;
build_module_env(_) ->
    {ok, cure_typechecker:builtin_env()}.

%% @doc Extract return type from a function type
extract_return_type({function_type, _Params, Return}) ->
    Return;
extract_return_type({poly_type, _TP, _C, BodyType, _Loc}) ->
    extract_return_type(BodyType);
extract_return_type(Other) ->
    Other.

%% @doc Try to resolve type variables in return type by matching with parameter types
%% Pragmatic heuristic for common cases like map: List(Int) -> List(Int)
resolve_type_variables({dependent_type, 'List', [RetParam]}, {function_type, Params, _Return}) ->
    % For List return types, try to infer the element type from parameters
    case find_list_element_type_in_params(Params) of
        {ok, ElemType} ->
            {dependent_type, 'List', [ElemType]};
        not_found ->
            {dependent_type, 'List', [RetParam]}
    end;
resolve_type_variables(ReturnType, _) ->
    ReturnType.

%% @doc Find concrete element type from List parameters
find_list_element_type_in_params([]) ->
    not_found;
find_list_element_type_in_params([{dependent_type, 'List', [ElemType]} | _Rest]) ->
    % Found a List parameter - check if its element type is concrete
    case is_concrete_type(ElemType) of
        true -> {ok, ElemType};
        false -> not_found
    end;
find_list_element_type_in_params([_ | Rest]) ->
    find_list_element_type_in_params(Rest).

%% @doc Check if a type is concrete (not a type variable)
is_concrete_type({primitive_type, _}) -> true;
% Assume dependent types are concrete
is_concrete_type({dependent_type, _, _}) -> true;
is_concrete_type({type_var, _, _, _}) -> false;
is_concrete_type({type_param, _, Type}) -> is_concrete_type(Type);
is_concrete_type(_) -> false.

%% @doc Process imports to build environment
process_imports_for_env([], Env) ->
    {ok, Env};
process_imports_for_env([Import | Rest], Env) ->
    case process_single_import(Import, Env) of
        {ok, NewEnv} ->
            process_imports_for_env(Rest, NewEnv);
        {error, _} ->
            % Continue with current env if import fails
            process_imports_for_env(Rest, Env)
    end;
process_imports_for_env(undefined, Env) ->
    {ok, Env}.

%% @doc Process a single import definition
process_single_import(#import_def{module = Module, items = Items}, Env) ->
    import_items_to_env(Module, Items, Env);
process_single_import(_, Env) ->
    {ok, Env}.

%% @doc Import items into environment
import_items_to_env(_Module, [], Env) ->
    {ok, Env};
import_items_to_env(Module, [Item | Rest], Env) ->
    case import_single_item(Module, Item, Env) of
        {ok, NewEnv} ->
            import_items_to_env(Module, Rest, NewEnv);
        {error, _} ->
            % Continue even if one item fails
            import_items_to_env(Module, Rest, Env)
    end.

%% @doc Import a single item (function) into environment
import_single_item(Module, #function_import{name = Name, arity = Arity}, Env) ->
    FunctionType = create_imported_function_type(Module, Name, Arity),
    NewEnv = cure_types:extend_env(Env, Name, FunctionType),
    {ok, NewEnv};
import_single_item(Module, FunctionName, Env) when is_atom(FunctionName) ->
    % Atom format - we don't know the arity, so try to get it from the stdlib
    % Try common arities (most stdlib functions are /2)
    % For now, we'll use arity 2 as default (map/2, filter/2, etc.)
    % A better approach would be to query the module for available arities

    % Default arity for stdlib functions like map, filter
    Arity = 2,
    FunctionType = create_imported_function_type(Module, FunctionName, Arity),
    NewEnv = cure_types:extend_env(Env, FunctionName, FunctionType),
    {ok, NewEnv};
import_single_item(_Module, _Item, Env) ->
    % Unknown import format, skip
    {ok, Env}.

%% @doc Create function type for imported function
%% Similar to cure_typechecker:create_imported_function_type but local to LSP
create_imported_function_type(Module, Name, Arity) ->
    case cure_typechecker:get_stdlib_function_type(Module, Name, Arity) of
        {ok, ConcreteType} ->
            ConcreteType;
        not_found ->
            % Generate parameter types as fallback
            ParamTypes = [cure_types:new_type_var() || _ <- lists:seq(1, Arity)],
            ReturnType = cure_types:new_type_var(),
            {imported_function_type, Module, Name, ParamTypes, ReturnType}
    end.

%% @doc Add function parameters to environment
add_params_to_env(Params, Env) ->
    lists:foldl(
        fun(#param{name = Name, type = TypeExpr}, AccEnv) ->
            % Convert type expression to internal type
            ParamType = convert_type_expr(TypeExpr),
            cure_types:extend_env(AccEnv, Name, ParamType)
        end,
        Env,
        Params
    ).

%% @doc Convert type expression from AST to internal format
convert_type_expr(#primitive_type{name = Name}) ->
    {primitive_type, Name};
convert_type_expr(#dependent_type{name = Name, type_params = TypeParams}) ->
    ConvertedParams = [convert_type_param(TP) || TP <- TypeParams],
    {dependent_type, Name, ConvertedParams};
convert_type_expr(_) ->
    cure_types:new_type_var().

%% @doc Convert type parameter
convert_type_param(#type_param{type = Type}) when Type =/= undefined ->
    #type_param{type = convert_type_expr(Type)};
convert_type_param(TP) ->
    TP.

%% @doc Convert internal type to AST format for display
convert_type_to_ast_format({primitive_type, Name}) ->
    #primitive_type{name = Name, location = undefined};
convert_type_to_ast_format({list_type, ElemType, _Length}) ->
    #dependent_type{
        name = 'List',
        type_params = [convert_type_to_ast_format(ElemType)],
        value_params = [],
        location = undefined
    };
convert_type_to_ast_format({dependent_type, Name, Params}) ->
    #dependent_type{
        name = Name,
        type_params = [convert_type_to_ast_format(P) || P <- Params],
        value_params = [],
        location = undefined
    };
convert_type_to_ast_format({function_type, _ParamTypes, ReturnType}) ->
    % For function types, we typically care about the return type in holes
    convert_type_to_ast_format(ReturnType);
convert_type_to_ast_format(_) ->
    #primitive_type{name = '_', location = undefined}.

%% @doc Infer expression type (kept for backwards compatibility but simplified)
infer_expr_type(#literal_expr{value = Val}) when is_integer(Val) ->
    {ok, #primitive_type{name = 'Int', location = undefined}};
infer_expr_type(#literal_expr{value = Val}) when is_float(Val) ->
    {ok, #primitive_type{name = 'Float', location = undefined}};
infer_expr_type(#literal_expr{value = Val}) when is_binary(Val) ->
    {ok, #primitive_type{name = 'String', location = undefined}};
infer_expr_type(#literal_expr{value = Val}) when Val =:= true; Val =:= false ->
    {ok, #primitive_type{name = 'Bool', location = undefined}};
infer_expr_type(_) ->
    {error, cannot_infer}.

%% @doc Infer parameter type from usage
infer_parameter_type(_ParamName, _AST, _State) ->
    % Would analyze how parameter is used in function body
    {ok, #primitive_type{name = 'Int', location = undefined}}.

%% @doc Infer type from surrounding context
-spec infer_from_context(term(), term(), map()) -> {ok, term()} | {error, term()}.
infer_from_context(Hole, AST, State) ->
    infer_hole_type(Hole, AST, State).

%%% ============================================================================
%%% LSP Integration
%%% ============================================================================

%% @doc Generate info-level diagnostics for type holes
-spec generate_hole_diagnostics(binary(), term()) -> [map()].
generate_hole_diagnostics(_Uri, AST) ->
    Holes = find_type_holes(AST),
    lists:map(
        fun({HoleName, Context, Loc}) ->
            HoleNameBin = atom_to_binary(HoleName, utf8),
            Message =
                case infer_hole_type(Context, AST, #{}) of
                    {ok, Type} ->
                        TypeStr = format_inferred_type(Type),
                        iolist_to_binary([
                            <<"Type hole: ">>,
                            HoleNameBin,
                            <<"\nInferred type: ">>,
                            TypeStr,
                            <<"\n\n💡 Click 'Quick Fix' or press Ctrl+. to fill in the type automatically"/utf8>>
                        ]);
                    {error, _} ->
                        iolist_to_binary([
                            <<"Type hole: ">>,
                            HoleNameBin,
                            <<"\nCannot infer type - please provide explicit type annotation">>
                        ])
                end,

            create_hole_diagnostic(Loc, Message)
        end,
        Holes
    ).

create_hole_diagnostic(#location{line = Line, column = Col}, Message) ->
    #{
        <<"range">> => #{
            <<"start">> => #{
                % LSP is 0-indexed
                % Widen the range to cover area around the hole
                <<"line">> => Line - 1,
                <<"character">> => max(0, Col - 1)
            },
            <<"end">> => #{
                <<"line">> => Line - 1,
                % Cover several characters to ensure we catch the _ wherever it is
                <<"character">> => Col + 10
            }
        },
        % Information
        <<"severity">> => 3,
        <<"source">> => <<"cure-holes">>,
        <<"message">> => Message,
        <<"code">> => <<"type-hole">>
    };
create_hole_diagnostic(_, Message) ->
    #{
        <<"range">> => #{
            <<"start">> => #{<<"line">> => 0, <<"character">> => 0},
            <<"end">> => #{<<"line">> => 0, <<"character">> => 0}
        },
        <<"severity">> => 3,
        <<"source">> => <<"cure-holes">>,
        <<"message">> => Message,
        <<"code">> => <<"type-hole">>
    }.

%% @doc Generate code action to fill in hole
-spec generate_hole_code_actions(binary(), map(), term()) -> [map()].
generate_hole_code_actions(Uri, Diagnostic, _AST) ->
    % Helper to get map value with atom or binary key
    GetKey = fun(Key, Map) ->
        case maps:get(Key, Map, undefined) of
            undefined -> maps:get(atom_to_binary(Key, utf8), Map, undefined);
            Val -> Val
        end
    end,

    % Check if diagnostic is for a type hole
    case GetKey(code, Diagnostic) of
        <<"type-hole">> ->
            Range = GetKey(range, Diagnostic),
            Message = GetKey(message, Diagnostic),

            % Extract inferred type from message
            case extract_inferred_type(Message) of
                {ok, TypeStr} ->
                    [create_fill_hole_action(Uri, Range, TypeStr)];
                _ ->
                    []
            end;
        _ ->
            []
    end.

create_fill_hole_action(Uri, Range, TypeStr) ->
    % The diagnostic range is wide, but we only want to replace the _ character
    % Find the _ within the range by assuming it's near the end
    GetKey = fun(Key, Map) ->
        case maps:get(Key, Map, undefined) of
            undefined -> maps:get(atom_to_binary(Key, utf8), Map, undefined);
            Val -> Val
        end
    end,

    StartPos = GetKey(start, Range),
    EndPos = GetKey('end', Range),
    StartLine = GetKey(line, StartPos),
    StartChar = GetKey(character, StartPos),
    EndChar = GetKey(character, EndPos),

    % The diagnostic range was created as (Col-1) to (Col+10) in 0-indexed LSP coordinates
    % where Col is the 1-indexed parser column of the underscore.
    % So StartChar is already the correct 0-indexed position of the underscore.
    % We want to replace exactly one character: the underscore itself.
    ActualRange = #{
        start => #{line => StartLine, character => StartChar},
        'end' => #{line => StartLine, character => StartChar + 1}
    },

    #{
        <<"title">> => iolist_to_binary(["Fill hole with: ", TypeStr]),
        <<"kind">> => <<"quickfix">>,
        % Mark as preferred for auto-apply
        <<"isPreferred">> => true,
        <<"diagnostics">> => [],
        <<"edit">> => #{
            <<"changes">> => #{
                Uri => [
                    #{
                        <<"range">> => ActualRange,
                        <<"newText">> => TypeStr
                    }
                ]
            }
        }
    }.

%% @doc Generate hover information for hole
-spec generate_hole_hover(integer(), integer(), term()) -> map() | undefined.
generate_hole_hover(Line, Character, AST) ->
    Holes = find_type_holes(AST),

    % Find hole at position
    case find_hole_at_position(Holes, Line, Character) of
        {ok, {HoleName, Context, _Loc}} ->
            HoleNameBin = atom_to_binary(HoleName, utf8),
            case infer_hole_type(Context, AST, #{}) of
                {ok, Type} ->
                    TypeStr = format_inferred_type(Type),
                    #{
                        <<"kind">> => <<"markdown">>,
                        <<"value">> => iolist_to_binary([
                            <<"**Type Hole: `">>,
                            HoleNameBin,
                            <<"`**\n\n">>,
                            <<"Inferred type: `">>,
                            TypeStr,
                            <<"`\n\n">>,
                            <<"Use code action to fill in this type.">>
                        ])
                    };
                {error, Reason} ->
                    ReasonBin = atom_to_binary(Reason, utf8),
                    #{
                        <<"kind">> => <<"markdown">>,
                        <<"value">> => iolist_to_binary([
                            <<"**Type Hole: `">>,
                            HoleNameBin,
                            <<"`**\n\n">>,
                            <<"Cannot infer type: ">>,
                            ReasonBin
                        ])
                    }
            end;
        undefined ->
            undefined
    end.

find_hole_at_position(Holes, Line, Character) ->
    Matches = lists:filter(
        fun
            ({_, _, #location{line = L, column = C}}) ->
                L =:= Line + 1 andalso C =< Character + 1 andalso Character + 1 < C + 5;
            (_) ->
                false
        end,
        Holes
    ),

    case Matches of
        [Hole | _] -> {ok, Hole};
        [] -> undefined
    end.

%%% ============================================================================
%%% Utilities
%%% ============================================================================

%% @doc Format inferred type for display
format_inferred_type(#primitive_type{name = Name}) ->
    atom_to_binary(Name, utf8);
format_inferred_type(#dependent_type{name = Name, type_params = TypeParams}) ->
    ParamStrs = lists:map(fun format_inferred_type/1, TypeParams),
    ParamStr = iolist_to_binary(lists:join(", ", ParamStrs)),
    iolist_to_binary([atom_to_binary(Name, utf8), "(", ParamStr, ")"]);
format_inferred_type(#type_param{name = Name}) ->
    atom_to_binary(Name, utf8);
format_inferred_type(_) ->
    <<"_">>.

%% Extract inferred type from diagnostic message
extract_inferred_type(Message) ->
    case binary:split(Message, <<"Inferred type: ">>) of
        [_, TypePart] ->
            % Take first line
            case binary:split(TypePart, <<"\n">>) of
                [TypeStr | _] -> {ok, TypeStr};
                _ -> {ok, TypePart}
            end;
        _ ->
            undefined
    end.
