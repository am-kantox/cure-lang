%% Cure Programming Language - Dependent Type Parser Support
%% Helper functions for parsing dependent type syntax
-module(cure_dependent_parser).

-moduledoc """
# Dependent Type Parser Support

This module provides parser helper functions for dependent type syntax introduced
in Phase 6. It extends the main parser with support for:

- Type-level parameters (both type and value parameters)
- Type-level expressions (arithmetic, comparisons)
- Dependent function types
- Value parameter constraints

## Examples

### Parsing Type-Level Parameters
```cure
type Vector(T, n: Nat) = List(T) when length(this) == n
%        ^  ^^^^^^^^^ value parameter
%        | type parameter
```

### Parsing Dependent Function Types
```cure
def concat<T, m: Nat, n: Nat>(
    v1: Vector(T, m),
    v2: Vector(T, n)
): Vector(T, m + n) = ...
%         ^^^^^^^ type-level expression
```

## Usage

These functions are called by the main parser (`cure_parser.erl`) when
encountering dependent type syntax.
""".

-export([
    % Type parameter parsing
    parse_type_params/1,
    parse_value_param/1,
    is_value_param/1,

    % Type-level expression parsing
    parse_type_level_expr/1,
    is_type_level_op/1,

    % Dependent type utilities
    make_dependent_type/4,
    make_dependent_function_type/5,
    make_type_level_expr/4
]).

-include("cure_ast.hrl").

%% ============================================================================
%% Type Parameter Parsing
%% ============================================================================

%% @doc Check if a parameter declaration is a value parameter
%% Value parameters have type annotations: n: Nat, m: Int, etc.
-spec is_value_param(term()) -> boolean().
is_value_param({param, _Name, Type, _Loc}) when Type =/= undefined ->
    true;
is_value_param(_) ->
    false.

%% @doc Parse type parameters (mix of type and value parameters)
%% Examples:
%%   <T> -> [{type, 'T'}]
%%   <T, n: Nat> -> [{type, 'T'}, {value, n, 'Nat'}]
%%   <T, m: Nat, n: Nat where n > 0> -> [{type, 'T'}, {value, m, 'Nat'}, {value, n, 'Nat', constraint}]
-spec parse_type_params([term()]) -> [#type_param{}].
parse_type_params(Params) ->
    lists:map(fun parse_single_type_param/1, Params).

parse_single_type_param({type_param, Name, undefined, Loc}) ->
    % Type parameter: T, U, etc.
    #type_param{
        name = Name,
        kind = type,
        type = undefined,
        constraint = undefined,
        location = Loc
    };
parse_single_type_param({type_param, Name, Type, Loc}) ->
    % Value parameter: n: Nat, m: Int, etc.
    #type_param{
        name = Name,
        kind = value,
        type = Type,
        constraint = undefined,
        location = Loc
    };
parse_single_type_param({type_param, Name, Type, Constraint, Loc}) ->
    % Constrained value parameter: n: Nat where n > 0
    #type_param{
        name = Name,
        kind = value,
        type = Type,
        constraint = Constraint,
        location = Loc
    }.

%% @doc Parse a value parameter with optional constraint
-spec parse_value_param(term()) -> #value_param{}.
parse_value_param({Name, Type, Constraint, Location}) ->
    #value_param{
        name = Name,
        type = Type,
        constraint = Constraint,
        location = Location
    };
parse_value_param({Name, Type, Location}) ->
    #value_param{
        name = Name,
        type = Type,
        constraint = undefined,
        location = Location
    }.

%% ============================================================================
%% Type-Level Expression Parsing
%% ============================================================================

%% @doc Check if an operator is a type-level operator
-spec is_type_level_op(atom()) -> boolean().
is_type_level_op('+') -> true;
is_type_level_op('-') -> true;
is_type_level_op('*') -> true;
is_type_level_op('/') -> true;
is_type_level_op('==') -> true;
is_type_level_op('<') -> true;
is_type_level_op('<=') -> true;
is_type_level_op('>') -> true;
is_type_level_op('>=') -> true;
is_type_level_op('and') -> true;
is_type_level_op('or') -> true;
is_type_level_op(_) -> false.

%% @doc Parse a type-level expression (e.g., m + n, i < n)
%% Type-level expressions use the same operators as term-level expressions
%% but operate on type-level values (e.g., length parameters)
-spec parse_type_level_expr(term()) -> #type_level_expr{}.
parse_type_level_expr(#binary_op_expr{op = Op, left = Left, right = Right, location = Loc}) when
    is_atom(Op)
->
    case is_type_level_op(Op) of
        true ->
            #type_level_expr{
                op = Op,
                left = parse_type_level_operand(Left),
                right = parse_type_level_operand(Right),
                location = Loc
            };
        false ->
            % Not a type-level operator, return original
            #binary_op_expr{op = Op, left = Left, right = Right, location = Loc}
    end;
parse_type_level_expr(Expr) ->
    Expr.

%% Parse type-level operand (can be identifier, literal, or nested expression)
parse_type_level_operand(#identifier_expr{} = Expr) ->
    Expr;
parse_type_level_operand(#literal_expr{} = Expr) ->
    Expr;
parse_type_level_operand(#binary_op_expr{} = Expr) ->
    parse_type_level_expr(Expr);
parse_type_level_operand(Other) ->
    Other.

%% ============================================================================
%% Dependent Type Construction
%% ============================================================================

%% @doc Create a dependent type record
-spec make_dependent_type(atom(), [term()], [{atom(), term()}], location()) -> #dependent_type{}.
make_dependent_type(Name, TypeParams, ValueParams, Location) ->
    #dependent_type{
        name = Name,
        type_params = TypeParams,
        value_params = ValueParams,
        location = Location
    }.

%% @doc Create a dependent function type record
-spec make_dependent_function_type([#type_param{}], [#param{}], term(), [term()], location()) ->
    #dependent_function_type{}.
make_dependent_function_type(TypeParams, Params, ReturnType, Constraints, Location) ->
    #dependent_function_type{
        type_params = TypeParams,
        params = Params,
        return_type = ReturnType,
        constraints = Constraints,
        location = Location
    }.

%% @doc Create a type-level expression record
-spec make_type_level_expr(atom(), term(), term(), location()) -> #type_level_expr{}.
make_type_level_expr(Op, Left, Right, Location) ->
    #type_level_expr{
        op = Op,
        left = Left,
        right = Right,
        location = Location
    }.

%% ============================================================================
%% Utility Functions
%% ============================================================================

%% @doc Extract type parameters from a mixed list
extract_type_params(Params) ->
    [P || P = #type_param{kind = type} <- Params].

%% @doc Extract value parameters from a mixed list
extract_value_params(Params) ->
    [P || P = #type_param{kind = value} <- Params].

%% @doc Check if a type is a dependent type
is_dependent_type(#dependent_type{}) -> true;
is_dependent_type(_) -> false.

%% @doc Check if a function type is dependent
is_dependent_function_type(#dependent_function_type{}) -> true;
is_dependent_function_type(_) -> false.
