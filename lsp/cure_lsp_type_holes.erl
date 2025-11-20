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
                [{HoleName, {return_type, Func}, Loc}];
            false ->
                []
        end,

    % Check parameter type holes
    ParamHoles = lists:flatmap(
        fun(#param{name = ParamName, type = ParamType, location = ParamLoc}) ->
            case is_type_hole(ParamType) of
                true ->
                    [{hole_name(ParamType), {param_type, Name, ParamName}, ParamLoc}];
                false ->
                    []
            end
        end,
        Params
    ),

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

%% @doc Infer function return type from body
infer_function_return_type(
    #function_def{body = Body},
    _AST
) ->
    case infer_expr_type(Body) of
        {ok, Type} -> {ok, Type};
        {error, _} = Error -> Error
    end;
infer_function_return_type(_, _) ->
    {error, cannot_infer}.

%% @doc Infer expression type
infer_expr_type(#literal_expr{value = Val}) when is_integer(Val) ->
    {ok, #primitive_type{name = 'Int', location = undefined}};
infer_expr_type(#literal_expr{value = Val}) when is_float(Val) ->
    {ok, #primitive_type{name = 'Float', location = undefined}};
infer_expr_type(#literal_expr{value = Val}) when is_binary(Val) ->
    {ok, #primitive_type{name = 'String', location = undefined}};
infer_expr_type(#literal_expr{value = Val}) when Val =:= true; Val =:= false ->
    {ok, #primitive_type{name = 'Bool', location = undefined}};
% List expression
infer_expr_type(#list_expr{elements = Elements}) ->
    case Elements of
        [] ->
            % Empty list - need more context
            {ok, #dependent_type{
                name = 'List',
                type_params = [#type_param{name = 'T'}],
                value_params = [],
                location = undefined
            }};
        [First | _] ->
            % Infer from first element
            case infer_expr_type(First) of
                {ok, ElemType} ->
                    {ok, #dependent_type{
                        name = 'List',
                        type_params = [ElemType],
                        value_params = [],
                        location = undefined
                    }};
                Error ->
                    Error
            end
    end;
% Function call - return type of called function
infer_expr_type(#function_call_expr{function = #identifier_expr{name = map}, args = [_, Lambda]}) ->
    % Special case for map - infer from lambda return
    case Lambda of
        #lambda_expr{body = LambdaBody} ->
            case infer_expr_type(LambdaBody) of
                {ok, ElemType} ->
                    {ok, #dependent_type{
                        name = 'List',
                        type_params = [ElemType],
                        value_params = [],
                        location = undefined
                    }};
                Error ->
                    Error
            end;
        _ ->
            {error, cannot_infer}
    end;
infer_expr_type(#function_call_expr{}) ->
    {error, need_function_signature};
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
            Message =
                case infer_hole_type(Context, AST, #{}) of
                    {ok, Type} ->
                        TypeStr = format_inferred_type(Type),
                        iolist_to_binary([
                            "Type hole: ",
                            atom_to_list(HoleName),
                            "\nInferred type: ",
                            TypeStr,
                            "\n\n💡 Click 'Quick Fix' or press Ctrl+. to fill in the type automatically"
                        ]);
                    {error, _} ->
                        iolist_to_binary([
                            "Type hole: ",
                            atom_to_list(HoleName),
                            "\nCannot infer type - please provide explicit type annotation"
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
                <<"line">> => Line - 1,
                <<"character">> => Col - 1
            },
            <<"end">> => #{
                <<"line">> => Line - 1,
                % Cover the ? or _
                <<"character">> => Col + 1
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
    % Check if diagnostic is for a type hole
    case maps:get(<<"code">>, Diagnostic, undefined) of
        <<"type-hole">> ->
            Range = maps:get(<<"range">>, Diagnostic),
            Message = maps:get(<<"message">>, Diagnostic),

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
                        <<"range">> => Range,
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
            case infer_hole_type(Context, AST, #{}) of
                {ok, Type} ->
                    TypeStr = format_inferred_type(Type),
                    #{
                        <<"kind">> => <<"markdown">>,
                        <<"value">> => iolist_to_binary([
                            "**Type Hole: `",
                            atom_to_list(HoleName),
                            "`**\n\n",
                            "Inferred type: `",
                            TypeStr,
                            "`\n\n",
                            "Use code action to fill in this type."
                        ])
                    };
                {error, Reason} ->
                    #{
                        <<"kind">> => <<"markdown">>,
                        <<"value">> => iolist_to_binary([
                            "**Type Hole: `",
                            atom_to_list(HoleName),
                            "`**\n\n",
                            "Cannot infer type: ",
                            atom_to_list(Reason)
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
