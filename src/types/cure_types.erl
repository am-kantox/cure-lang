%% Cure Programming Language - Type System Core
%% Dependent type system with constraint solving and inference
-module(cure_types).

-moduledoc """
# Cure Programming Language - Type System Core

The core type system module implementing Cure's advanced dependent type system
with constraint solving, type inference, and support for higher-kinded types.
This module provides the foundational type operations that power Cure's static
type checking and dependent type verification.

## Key Features

### Dependent Types
- **Value Dependencies**: Types that depend on runtime values (e.g., `Vector(T, n)`)
- **Constraint Solving**: SMT-based constraint solving for dependent type verification
- **Type-Level Computation**: Evaluation of type expressions with value parameters

### Advanced Type System
- **Higher-Kinded Types**: Support for type constructors and type families
- **Recursive Types**: μ-types with cycle detection and well-formedness checking
- **Union Types**: Discriminated union types with exhaustiveness checking
- **Generic Types**: Full parametric polymorphism with constraint-based inference

### Type Inference Engine
- **Bidirectional Inference**: Combines bottom-up and top-down type inference
- **Constraint Generation**: Generates and solves complex type constraints
- **Alternative Generation**: Provides multiple type possibilities with confidence scores
- **Local Inference**: Context-aware type inference for improved accuracy

### Unification Algorithm
- **Robinson Unification**: Extended Robinson unification for dependent types
- **Occurs Check**: Prevents infinite types with comprehensive cycle detection
- **Constraint Propagation**: Propagates type constraints through unification
- **Substitution Management**: Efficient substitution composition and application

## Core Operations

### Type Variables
```erlang
%% Create new type variables
TVar1 = cure_types:new_type_var(),
TVar2 = cure_types:new_type_var(custom_name).

%% Check type variable properties
true = cure_types:is_type_var(TVar1),
false = cure_types:occurs_check(TVar1, IntType).
```

### Type Unification
```erlang
%% Unify two types
{ok, Substitution} = cure_types:unify(Type1, Type2),
{ok, Sub, Constraints} = cure_types:unify(Type1, Type2, Environment).
```

### Type Inference
```erlang
%% Basic type inference
{ok, InferredType} = cure_types:infer_type(Expression, Environment),

%% Enhanced inference with alternatives
{ok, Result} = cure_types:enhanced_infer_type(Expression, Environment),
Confidence = Result#enhanced_inference_result.confidence,
Alternatives = Result#enhanced_inference_result.alternatives.
```

## Type Environment

The type environment maintains variable bindings and constraints:
- **Hierarchical Scoping**: Supports nested scopes with parent environments
- **Constraint Accumulation**: Collects and manages type constraints
- **Efficient Lookup**: Fast variable resolution with scope traversal

```erlang
%% Environment operations
Env1 = cure_types:new_env(),
Env2 = cure_types:extend_env(Env1, variable_name, VariableType),
{ok, Type} = cure_types:lookup_env(Env2, variable_name).
```

## Constraint Solving

Supports various constraint types:
- **Equality**: `T = U`
- **Subtyping**: `T <: U`
- **Element Membership**: `x elem_of T`
- **Length Constraints**: `length(xs) = n`
- **Logical Constraints**: `implies`, `iff`
- **Variance Constraints**: `covariant`, `contravariant`

## Higher-Kinded Types

```erlang
%% Create type constructors
ListKind = cure_types:create_kind('*', [], '*'),
FunctorKind = cure_types:create_kind('->', [ListKind], ListKind),

%% Type families
Family = cure_types:create_type_family(map, [F, T], Dependencies, Constraints),
Result = cure_types:evaluate_type_family(Family, Arguments).
```

## Performance Characteristics

- **Type Inference**: O(n log n) for most expressions
- **Unification**: O(n) for structural types, O(n²) worst case
- **Constraint Solving**: Depends on constraint complexity, uses SMT solver
- **Memory Usage**: Efficient substitution sharing reduces memory overhead

## Integration

This module integrates with:
- **Type Checker**: Provides core type operations for checking
- **SMT Solver**: Delegates complex constraint solving
- **Type Optimizer**: Provides types for optimization decisions
- **Parser**: Processes type annotations and expressions

## Error Handling

Returns structured errors for:
- **Unification Failures**: Detailed mismatch information
- **Constraint Violations**: Specific constraint failure reasons
- **Infinite Types**: Occurs check violations
- **Kind Errors**: Higher-kinded type mismatches

## Thread Safety

Type variables use a global counter that should be accessed safely in
concurrent environments. The module is otherwise stateless and thread-safe.
""".

-include("../parser/cure_ast_simple.hrl").

-export([
    % Type operations
    new_type_var/0, new_type_var/1,
    is_type_var/1,
    occurs_check/2,

    % Type unification
    unify/2, unify/3,

    % Type environment
    new_env/0,
    extend_env/3,
    lookup_env/2,

    % Type inference
    infer_type/2, infer_type/3,
    infer_dependent_type/2,

    % Enhanced type inference
    enhanced_infer_type/2, enhanced_infer_type/3,
    infer_with_alternatives/3,
    bidirectional_infer/3,
    constraint_propagation/2,
    local_type_inference/3,
    generate_type_alternatives/3,
    generate_list_alternatives/3,
    enhanced_constraint_solving/2,

    % Recursive types
    create_recursive_type/4,
    unfold_recursive_type/1, unfold_recursive_type/2,
    fold_recursive_type/2,
    check_recursive_type_well_formed/1,
    unify_recursive_types/3,
    occurs_check_recursive/2,
    detect_cycles/2,

    % Higher-kinded types
    create_kind/3,
    infer_kind/2,
    check_kind/3,
    unify_kinds/2,
    create_type_constructor/5,
    apply_type_constructor/3,
    create_type_family/4,
    evaluate_type_family/2,
    solve_type_family_equation/3,
    check_constraint_satisfaction/2,
    check_higher_kinded_well_formed/1,
    kind_arity/1,
    is_saturated_type/1,

    % Type checking
    check_type/3, check_type/4,
    is_well_formed_type/1,

    % Pattern matching
    infer_pattern_type/3,

    % Constraint solving
    solve_constraints/1, solve_constraints/2,
    check_dependent_constraint/3,

    % Complex constraint solving
    solve_implication_constraint/3,
    solve_equivalence_constraint/3,
    solve_bounds_constraint/3,
    solve_invariant_constraint/3,
    solve_variance_constraint/4,
    evaluate_type_predicate/2,

    % Utility functions
    substitute/2,
    normalize_type/1,
    type_to_string/1,
    is_generic_type_variable_name/1,

    % DEBUG: Temporary exports for debugging vector param extraction
    extract_vector_params/1,
    extract_param_info/2,
    get_tuple_param_info/1,
    safe_extract_param_value/1
]).

%% Type variable counter for generating unique type variables
-define(TYPE_VAR_COUNTER, cure_type_var_counter).

%% Type definitions
-record(type_var, {
    id :: integer(),
    name :: atom() | undefined,
    constraints :: [term()]
}).

% type_param record is defined in cure_ast_simple.hrl

-record(type_constraint, {
    left :: type_expr(),
    op :: constraint_op(),
    right :: type_expr(),
    location :: location()
}).

-record(type_env, {
    bindings :: #{atom() => type_expr()},
    constraints :: [type_constraint()],
    parent :: type_env() | undefined
}).

-type constraint_op() ::
    '='
    | '<:'
    | '>:'
    | 'elem_of'
    | 'length_eq'
    | 'implies'
    | 'iff'
    | 'bounds'
    | 'invariant'
    | 'covariant'
    | 'contravariant'.
-type type_expr() :: term().
-type location() :: term().
-type type_env() :: #type_env{}.
-type type_var() :: #type_var{}.
-type type_constraint() :: #type_constraint{}.
% Defined in cure_ast_simple.hrl
-type type_param() :: term().

-record(inference_result, {
    type :: type_expr(),
    constraints :: [type_constraint()],
    substitution :: #{type_var() => type_expr()}
}).

%% Enhanced type inference result with additional information
-record(enhanced_inference_result, {
    type :: type_expr(),
    constraints :: [type_constraint()],
    substitution :: #{type_var() => type_expr()},
    % Confidence score 0.0-1.0
    confidence :: float(),
    % Alternative type possibilities
    alternatives :: [type_expr()],
    % Inference steps taken
    justification :: [inference_step()],
    % Additional context
    context_info :: #{atom() => term()}
}).

-record(inference_step, {
    rule :: atom(),
    input :: term(),
    output :: term(),
    location :: location()
}).

-type inference_step() :: #inference_step{}.

%% Recursive type definitions
-record(recursive_type, {
    name :: atom(),
    params :: [type_param()],
    definition :: type_expr(),
    binding_context :: #{atom() => type_expr()},
    location :: location()
}).

-record(mu_type, {
    var :: atom(),
    body :: type_expr(),
    unfold_level :: integer(),
    location :: location()
}).

-record(cycle_detection, {
    visited :: sets:set(atom()),
    stack :: [atom()],
    max_depth :: integer()
}).

% COMMENTED OUT UNUSED TYPES
% -type recursive_type() :: #recursive_type{}.
% -type mu_type() :: #mu_type{}.
% -type cycle_detection() :: #cycle_detection{}.

%% Higher-kinded types definitions
-record(kind, {
    % Base kind or higher-order kind
    constructor :: atom() | kind(),
    % Kind arguments
    args :: [kind()],
    % Result kind
    result :: kind() | atom(),
    arity :: integer(),
    location :: location()
}).

-record(type_constructor, {
    name :: atom(),
    kind :: kind(),
    params :: [type_param()],
    definition :: type_expr() | undefined,
    constraints :: [constraint()],
    location :: location()
}).

-record(higher_kinded_type, {
    constructor :: type_constructor(),
    applied_args :: [type_expr()],
    % Number of args still needed
    remaining_args :: integer(),
    location :: location()
}).

-record(type_family, {
    name :: atom(),
    kind :: kind(),
    equations :: [type_family_equation()],
    location :: location()
}).

-record(type_family_equation, {
    pattern :: [type_expr()],
    result :: type_expr(),
    constraints :: [constraint()],
    location :: location()
}).

-record(constraint, {
    class :: atom(),
    args :: [type_expr()],
    location :: location()
}).

-type kind() :: #kind{}.
-type type_constructor() :: #type_constructor{}.
% COMMENTED OUT UNUSED TYPES
% -type higher_kinded_type() :: #higher_kinded_type{}.
% -type type_family() :: #type_family{}.
-type type_family_equation() :: #type_family_equation{}.
-type constraint() :: #constraint{}.

% Complex dependent type relationship records - UNUSED TYPES COMMENTED OUT
% -record(dependent_relation, {
%     type1 :: type_expr(),
%     type2 :: type_expr(),
%     relation :: dependent_relation_type(),
%     predicate :: fun((term(), term()) -> boolean()) | term(),
%     location :: location()
% }).
%
% -record(type_invariant, {
%     type :: type_expr(),
%     invariant :: fun((type_expr()) -> boolean()) | term(),
%     description :: string(),
%     location :: location()
% }).
%
% -record(variance_constraint, {
%     type_constructor :: atom(),
%     parameter_position :: integer(),
%     variance :: covariant | contravariant | invariant,
%     location :: location()
% }).

% COMMENTED OUT UNUSED TYPE
% -type dependent_relation_type() ::
%     implies
%     | equivalent
%     | bounds
%     | subtype_of
%     | compatible_with
%     | dimension_match
%     | length_preserving.

%% Built-in types
-define(TYPE_INT, {primitive_type, 'Int'}).
-define(TYPE_FLOAT, {primitive_type, 'Float'}).
-define(TYPE_STRING, {primitive_type, 'String'}).
-define(TYPE_BOOL, {primitive_type, 'Bool'}).
-define(TYPE_ATOM, {primitive_type, 'Atom'}).

%% Dependent types
-define(TYPE_NAT, {refined_type, 'Int', fun(N) -> N >= 0 end}).
-define(TYPE_POS, {refined_type, 'Int', fun(N) -> N > 0 end}).

-doc """
Creates a new unique type variable without a specific name.

This is a convenience function that calls new_type_var/1 with undefined name.

## Returns
- `type_var()` - A new unique type variable

## Example
```erlang
TVar = cure_types:new_type_var(),
true = cure_types:is_type_var(TVar).
```

## Note
Uses a process dictionary counter to ensure uniqueness within a process.
For concurrent use, external synchronization may be required.
""".
new_type_var() ->
    new_type_var(undefined).

-doc """
Creates a new unique type variable with an optional name.

## Arguments
- `Name` - Optional name for the type variable (atom() | undefined)

## Returns
- `type_var()` - A new unique type variable with the given name

## Example
```erlang
TVar1 = cure_types:new_type_var(my_var),
TVar2 = cure_types:new_type_var(undefined),
true = TVar1#type_var.name =:= my_var.
```

## Note
The name is primarily for debugging and error reporting. The unique ID
ensures type variable identity regardless of name.
""".
new_type_var(Name) ->
    Counter =
        case get(?TYPE_VAR_COUNTER) of
            undefined -> 0;
            N -> N
        end,
    put(?TYPE_VAR_COUNTER, Counter + 1),
    #type_var{
        id = Counter,
        name = Name,
        constraints = []
    }.

-doc """
Checks if a term is a type variable.

## Arguments
- `Term` - Any term to check

## Returns
- `true` - If the term is a type_var record
- `false` - Otherwise

## Example
```erlang
TVar = cure_types:new_type_var(),
true = cure_types:is_type_var(TVar),
false = cure_types:is_type_var(my_atom).
```
""".
is_type_var(#type_var{}) -> true;
is_type_var(_) -> false.

-doc """
Performs an occurs check to prevent infinite types during unification.

The occurs check ensures that a type variable does not occur within
the type it would be unified with, preventing infinite type structures.

## Arguments
- `TypeVar` - Type variable to check for
- `Type` - Type expression to check within

## Returns
- `true` - If the type variable occurs in the type (would create infinite type)
- `false` - If the unification would be safe

## Example
```erlang
TVar = cure_types:new_type_var(),
ListType = {list_type, TVar},
true = cure_types:occurs_check(TVar, ListType),  % Would create infinite list
false = cure_types:occurs_check(TVar, {primitive_type, 'Int'}).
```

## Note
This is essential for preventing infinite types like `T = List(T)` during unification.
""".
occurs_check(#type_var{id = Id}, Type) ->
    occurs_check_impl(Id, Type).

occurs_check_impl(Id, #type_var{id = Id}) ->
    true;
occurs_check_impl(Id, {function_type, Params, Return}) ->
    lists:any(fun(P) -> occurs_check_impl(Id, P) end, Params) orelse
        occurs_check_impl(Id, Return);
occurs_check_impl(Id, {dependent_type, _, Params}) ->
    lists:any(
        fun(Param) ->
            case Param of
                #type_param{value = V} -> occurs_check_impl(Id, V);
                _ -> occurs_check_impl(Id, Param)
            end
        end,
        Params
    );
occurs_check_impl(Id, {list_type, ElemType, LenExpr}) ->
    occurs_check_impl(Id, ElemType) orelse
        case LenExpr of
            undefined -> false;
            _ -> occurs_check_impl(Id, LenExpr)
        end;
occurs_check_impl(Id, {refined_type, BaseType, _Predicate}) ->
    occurs_check_impl(Id, BaseType);
occurs_check_impl(Id, {gadt_constructor, _, Args, ReturnType}) ->
    lists:any(fun(Arg) -> occurs_check_impl(Id, Arg) end, Args) orelse
        occurs_check_impl(Id, ReturnType);
occurs_check_impl(Id, {proof_type, _, BaseType, _Predicate}) ->
    occurs_check_impl(Id, BaseType);
occurs_check_impl(Id, {liquid_type, _, BaseType, _Constraints, _Context}) ->
    occurs_check_impl(Id, BaseType);
occurs_check_impl(_Id, undefined) ->
    % undefined contains no type variables
    false;
occurs_check_impl(_Id, {literal_expr, _, _}) ->
    % literal expressions contain no type variables
    false;
occurs_check_impl(_Id, {identifier_expr, _, _}) ->
    % identifier expressions contain no type variables (in this context)
    false;
occurs_check_impl(_, _) ->
    false.

-doc """
Creates a new empty type environment.

The type environment maintains variable bindings, constraints, and
supports hierarchical scoping through parent environments.

## Returns
- `type_env()` - A new empty type environment

## Example
```erlang
Env = cure_types:new_env(),
Env2 = cure_types:extend_env(Env, x, {primitive_type, 'Int'}),
{ok, Type} = cure_types:lookup_env(Env2, x).
```

## Features
- **Hierarchical Scoping**: Supports nested environments
- **Constraint Tracking**: Accumulates type constraints
- **Efficient Lookup**: Fast variable resolution
""".
new_env() ->
    #type_env{
        bindings = #{},
        constraints = [],
        parent = undefined
    }.

-doc """
Extends a type environment with a new variable binding.

Supports multiple environment representations for different use cases.

## Arguments
- `Env` - Type environment (type_env(), map(), or list())
- `Var` - Variable name (atom())
- `Type` - Type expression to bind to the variable

## Returns
- Updated environment with the new binding

## Supported Environment Types
- **type_env()**: Full environment with constraints and parent scopes
- **map()**: Simple map for lightweight inference
- **list()**: Association list for basic scoping

## Example
```erlang
Env1 = cure_types:new_env(),
Env2 = cure_types:extend_env(Env1, x, {primitive_type, 'Int'}),
Env3 = cure_types:extend_env(Env2, y, {primitive_type, 'String'}).
```
""".
extend_env(Env = #type_env{bindings = Bindings}, Var, Type) ->
    Env#type_env{bindings = maps:put(Var, Type, Bindings)};
extend_env(#{} = Env, Var, Type) ->
    % Simple map environment for enhanced inference
    maps:put(Var, Type, Env);
extend_env(Env, Var, Type) when is_list(Env) ->
    % Association list environment
    [{Var, Type} | Env].

-doc """
Looks up a variable binding in the type environment.

Searches the current environment and parent environments if available.

## Arguments
- `Env` - Type environment (type_env(), map(), or list())
- `Var` - Variable name to look up (atom())

## Returns
- `Type` - The type bound to the variable if found
- `undefined` - If the variable is not bound in the environment

## Scoping
For type_env() records, searches parent environments if the variable
is not found in the current scope.

## Example
```erlang
Env = cure_types:extend_env(cure_types:new_env(), x, IntType),
IntType = cure_types:lookup_env(Env, x),
undefined = cure_types:lookup_env(Env, unbound_var).
```
""".
lookup_env(#type_env{bindings = Bindings, parent = Parent}, Var) ->
    case maps:get(Var, Bindings, undefined) of
        undefined when Parent =/= undefined ->
            lookup_env(Parent, Var);
        Result ->
            Result
    end;
lookup_env(#{} = Env, Var) ->
    % Simple map environment for enhanced inference
    maps:get(Var, Env, undefined);
lookup_env([], _Var) ->
    % Empty list environment
    undefined;
lookup_env([{Var, Type} | _Rest], Var) ->
    % Found in association list
    Type;
lookup_env([_ | Rest], Var) ->
    % Search rest of association list
    lookup_env(Rest, Var).

-doc """
Unifies two types using the Robinson unification algorithm.

This is a convenience function that calls unify/3 with an empty substitution.

## Arguments
- `Type1` - First type expression to unify
- `Type2` - Second type expression to unify

## Returns
- `{ok, Substitution}` - Successful unification with substitution map
- `{error, Reason}` - Unification failure with detailed error

## Example
```erlang
{ok, Subst} = cure_types:unify(IntType, IntType),
{ok, Subst2} = cure_types:unify(TVar, IntType),
{error, _} = cure_types:unify(IntType, StringType).
```

## Error Cases
- Type mismatch (e.g., Int vs String)
- Occurs check failure (infinite types)
- Constraint violations
""".
unify(Type1, Type2) ->
    unify(Type1, Type2, #{}).

-doc """
Unifies two types with an existing substitution.

Applies the existing substitution to both types before unification
and composes the results.

## Arguments
- `Type1` - First type expression to unify
- `Type2` - Second type expression to unify  
- `Subst` - Existing substitution map to compose with

## Returns
- `{ok, NewSubstitution}` - Combined substitution after unification
- `{error, Reason}` - Unification failure with detailed error

## Example
```erlang
{ok, Subst1} = cure_types:unify(TVar1, IntType),
{ok, Subst2} = cure_types:unify(TVar2, StringType, Subst1),
%% Subst2 now contains bindings for both TVar1 and TVar2
```

## Substitution Composition
The function applies the input substitution to both types before
unification and composes the result with the input substitution.
""".
unify(Type1, Type2, Subst) ->
    unify_impl(
        apply_substitution(Type1, Subst),
        apply_substitution(Type2, Subst),
        Subst
    ).

unify_impl(T, T, Subst) ->
    {ok, Subst};
%% Handle unification with undefined
unify_impl(undefined, _Type, Subst) ->
    % undefined can unify with any type
    {ok, Subst};
unify_impl(_Type, undefined, Subst) ->
    % any type can unify with undefined
    {ok, Subst};
unify_impl(Var = #type_var{id = Id}, Type, Subst) ->
    case occurs_check(Var, Type) of
        true ->
            {error, {occurs_check_failed, Var, Type}};
        false ->
            % Additional check for dependent types containing the variable
            case check_dependent_occurs(Var, Type) of
                true -> {error, {occurs_check_failed, Var, Type}};
                false -> {ok, maps:put(Id, Type, Subst)}
            end
    end;
unify_impl(Type, Var = #type_var{}, Subst) ->
    unify_impl(Var, Type, Subst);
unify_impl({primitive_type, Name1}, {primitive_type, Name2}, Subst) when
    Name1 =:= Name2
->
    {ok, Subst};
unify_impl(
    {function_type, Params1, Return1},
    {function_type, Params2, Return2},
    Subst
) ->
    io:format("DEBUG: Function type unification - Params1: ~p, Params2: ~p~n", [Params1, Params2]),
    case length(Params1) =:= length(Params2) of
        false ->
            {error, {arity_mismatch, length(Params1), length(Params2)}};
        true ->
            case unify_lists(Params1, Params2, Subst) of
                {ok, Subst1} ->
                    io:format("DEBUG: Function parameter unification succeeded~n"),
                    unify_impl(Return1, Return2, Subst1);
                Error ->
                    io:format("DEBUG: Function parameter unification failed: ~p~n", [Error]),
                    Error
            end
    end;
unify_impl({list_type, Elem1, Len1}, {list_type, Elem2, Len2}, Subst) ->
    case unify_impl(Elem1, Elem2, Subst) of
        {ok, Subst1} ->
            unify_lengths(Len1, Len2, Subst1);
        Error ->
            Error
    end;
%% Direct Vector to Vector unification with strict length checking (MUST come before generic dependent_type)
unify_impl(
    {dependent_type, 'Vector', Params1},
    {dependent_type, 'Vector', Params2},
    Subst
) ->
    io:format("DEBUG: Vector unification - Params1: ~p, Params2: ~p~n", [Params1, Params2]),
    case {extract_vector_params(Params1), extract_vector_params(Params2)} of
        {{ok, Elem1, Len1}, {ok, Elem2, Len2}} ->
            io:format("DEBUG: Vector lengths - Len1: ~p, Len2: ~p~n", [Len1, Len2]),
            case unify_impl(Elem1, Elem2, Subst) of
                {ok, Subst1} ->
                    % Strict length checking for Vector types
                    Result = unify_lengths_strict(Len1, Len2, Subst1),
                    io:format("DEBUG: Vector dimension unification result: ~p~n", [Result]),
                    Result;
                Error ->
                    Error
            end;
        {{error, Reason}, _} ->
            io:format("DEBUG: Failed to extract vector params (left): ~p~n", [Reason]),
            {error, {invalid_vector_params_left, Reason}};
        {_, {error, Reason}} ->
            io:format("DEBUG: Failed to extract vector params (right): ~p~n", [Reason]),
            {error, {invalid_vector_params_right, Reason}}
    end;
%% Generic dependent type unification (AFTER specific Vector case)
unify_impl(
    {dependent_type, Name1, Params1},
    {dependent_type, Name2, Params2},
    Subst
) when
    Name1 =:= Name2, length(Params1) =:= length(Params2)
->
    io:format("DEBUG: Generic dependent_type unification called for ~p~n", [Name1]),
    unify_type_params(Params1, Params2, Subst);
%% Bridge unification between list_type and dependent List types
unify_impl(
    {list_type, Elem1, Len1},
    {dependent_type, 'List', Params2},
    Subst
) ->
    case extract_list_params(Params2) of
        {ok, Elem2, Len2} ->
            case unify_impl(Elem1, Elem2, Subst) of
                {ok, Subst1} ->
                    unify_lengths(Len1, Len2, Subst1);
                Error ->
                    Error
            end;
        {error, Reason} ->
            {error, {invalid_list_params, Reason}}
    end;
unify_impl(
    {dependent_type, 'List', Params1},
    {list_type, Elem2, Len2},
    Subst
) ->
    case extract_list_params(Params1) of
        {ok, Elem1, Len1} ->
            case unify_impl(Elem1, Elem2, Subst) of
                {ok, Subst1} ->
                    unify_lengths(Len1, Len2, Subst1);
                Error ->
                    Error
            end;
        {error, Reason} ->
            {error, {invalid_list_params, Reason}}
    end;
%% Bridge unification for Vector types (similar to List)
unify_impl(
    {list_type, Elem1, Len1},
    {dependent_type, 'Vector', Params2},
    Subst
) ->
    case extract_vector_params(Params2) of
        {ok, Elem2, Len2} ->
            case unify_impl(Elem1, Elem2, Subst) of
                {ok, Subst1} ->
                    unify_lengths(Len1, Len2, Subst1);
                Error ->
                    Error
            end;
        {error, Reason} ->
            {error, {invalid_vector_params, Reason}}
    end;
unify_impl(
    {dependent_type, 'Vector', Params1},
    {list_type, Elem2, Len2},
    Subst
) ->
    case extract_vector_params(Params1) of
        {ok, Elem1, Len1} ->
            case unify_impl(Elem1, Elem2, Subst) of
                {ok, Subst1} ->
                    unify_lengths(Len1, Len2, Subst1);
                Error ->
                    Error
            end;
        {error, Reason} ->
            {error, {invalid_vector_params, Reason}}
    end;
%% Support for refined types
unify_impl(
    {refined_type, BaseType1, Predicate1},
    {refined_type, BaseType2, Predicate2},
    Subst
) ->
    case unify_impl(BaseType1, BaseType2, Subst) of
        {ok, Subst1} ->
            % For now, assume compatible predicates if base types unify
            % In full implementation, would check predicate compatibility
            case predicates_compatible(Predicate1, Predicate2) of
                true -> {ok, Subst1};
                false -> {error, {predicate_incompatible, Predicate1, Predicate2}}
            end;
        Error ->
            Error
    end;
%% Allow refined types to unify with their base types
unify_impl({refined_type, BaseType, _Predicate}, Type, Subst) ->
    unify_impl(BaseType, Type, Subst);
unify_impl(Type, {refined_type, BaseType, _Predicate}, Subst) ->
    unify_impl(Type, BaseType, Subst);
%% Support for phantom types - they unify if their base types match
unify_impl({phantom_type, Name1}, {phantom_type, Name2}, Subst) when
    Name1 =:= Name2
->
    {ok, Subst};
%% Support for GADT constructors
unify_impl(
    {gadt_constructor, Name1, Args1, ReturnType1},
    {gadt_constructor, Name2, Args2, ReturnType2},
    Subst
) when
    Name1 =:= Name2, length(Args1) =:= length(Args2)
->
    case unify_lists(Args1, Args2, Subst) of
        {ok, Subst1} ->
            unify_impl(ReturnType1, ReturnType2, Subst1);
        Error ->
            Error
    end;
%% Support for proof types - check base type and predicate compatibility
unify_impl(
    {proof_type, Name1, BaseType1, Predicate1},
    {proof_type, Name2, BaseType2, Predicate2},
    Subst
) when
    Name1 =:= Name2
->
    case unify_impl(BaseType1, BaseType2, Subst) of
        {ok, Subst1} ->
            case predicates_compatible(Predicate1, Predicate2) of
                true -> {ok, Subst1};
                false -> {error, {proof_predicate_incompatible, Predicate1, Predicate2}}
            end;
        Error ->
            Error
    end;
%% Support for liquid types
unify_impl(
    {liquid_type, Name1, BaseType1, Constraints1, _Context1},
    {liquid_type, Name2, BaseType2, Constraints2, _Context2},
    Subst
) when
    Name1 =:= Name2
->
    case unify_impl(BaseType1, BaseType2, Subst) of
        {ok, Subst1} ->
            case constraints_compatible(Constraints1, Constraints2) of
                true -> {ok, Subst1};
                false -> {error, {liquid_constraints_incompatible, Constraints1, Constraints2}}
            end;
        Error ->
            Error
    end;
unify_impl(Type1, Type2, _Subst) ->
    {error, {unification_failed, Type1, Type2}}.

%% Helper functions for unification
unify_lists([], [], Subst) ->
    {ok, Subst};
unify_lists([H1 | T1], [H2 | T2], Subst) ->
    case unify_impl(H1, H2, Subst) of
        {ok, Subst1} -> unify_lists(T1, T2, Subst1);
        Error -> Error
    end.

unify_lengths(undefined, undefined, Subst) ->
    {ok, Subst};
unify_lengths(Len1, Len2, Subst) when Len1 =/= undefined, Len2 =/= undefined ->
    io:format("DEBUG: unify_lengths - Len1: ~p, Len2: ~p~n", [Len1, Len2]),
    case {Len1, Len2} of
        % Handle type variables properly - they should unify with any concrete length
        {TypeVar = #type_var{}, ConcreteLen} ->
            io:format("DEBUG: (regular) Unifying type variable ~p with concrete length ~p~n", [
                TypeVar, ConcreteLen
            ]),
            unify_impl(TypeVar, ConcreteLen, Subst);
        {ConcreteLen, TypeVar = #type_var{}} ->
            io:format("DEBUG: (regular) Unifying concrete length ~p with type variable ~p~n", [
                ConcreteLen, TypeVar
            ]),
            unify_impl(ConcreteLen, TypeVar, Subst);
        _ ->
            % Enhanced length checking with evaluation
            case {evaluate_length_expr(Len1), evaluate_length_expr(Len2)} of
                {{ok, N}, {ok, N}} when is_integer(N) ->
                    % Same evaluated length
                    {ok, Subst};
                {{ok, N1}, {ok, N2}} when is_integer(N1), is_integer(N2), N1 =/= N2 ->
                    % Different evaluated lengths
                    {error, {length_mismatch, N1, N2}};
                _ ->
                    % Fall back to structural comparison
                    case expr_equal(Len1, Len2) of
                        true -> {ok, Subst};
                        false -> {error, {length_mismatch, Len1, Len2}}
                    end
            end
    end;
unify_lengths(_, _, Subst) ->
    {ok, Subst}.

%% Strict length unification for Vector types - no undefined allowed
unify_lengths_strict(Len1, Len2, Subst) ->
    io:format("DEBUG: unify_lengths_strict - Len1: ~p, Len2: ~p~n", [Len1, Len2]),
    case {Len1, Len2} of
        % Handle type variables properly - they should unify with any concrete length
        {TypeVar = #type_var{}, ConcreteLen} ->
            io:format("DEBUG: Unifying type variable ~p with concrete length ~p~n", [
                TypeVar, ConcreteLen
            ]),
            unify_impl(TypeVar, ConcreteLen, Subst);
        {ConcreteLen, TypeVar = #type_var{}} ->
            io:format("DEBUG: Unifying concrete length ~p with type variable ~p~n", [
                ConcreteLen, TypeVar
            ]),
            unify_impl(ConcreteLen, TypeVar, Subst);
        % Handle primitive type variables (e.g., {primitive_type, n})
        {{primitive_type, VarName}, ConcreteLen} when is_atom(VarName) ->
            case is_generic_type_variable_name(VarName) of
                true ->
                    io:format(
                        "DEBUG: Unifying primitive type variable ~p with concrete length ~p~n", [
                            VarName, ConcreteLen
                        ]
                    ),
                    % Convert primitive type variable to proper type var and unify
                    TypeVar = #type_var{id = VarName, name = VarName},
                    unify_impl(TypeVar, ConcreteLen, Subst);
                false ->
                    % Not a type variable, fall through to concrete comparison
                    case {evaluate_length_expr(Len1), evaluate_length_expr(Len2)} of
                        {{ok, N}, {ok, N}} when is_integer(N) ->
                            {ok, Subst};
                        {{ok, N1}, {ok, N2}} when is_integer(N1), is_integer(N2), N1 =/= N2 ->
                            {error, {length_mismatch, N1, N2}};
                        _ ->
                            case expr_equal(Len1, Len2) of
                                true -> {ok, Subst};
                                false -> {error, {vector_dimension_mismatch, Len1, Len2}}
                            end
                    end
            end;
        {ConcreteLen, {primitive_type, VarName}} when is_atom(VarName) ->
            case is_generic_type_variable_name(VarName) of
                true ->
                    io:format(
                        "DEBUG: Unifying concrete length ~p with primitive type variable ~p~n", [
                            ConcreteLen, VarName
                        ]
                    ),
                    % Convert primitive type variable to proper type var and unify
                    TypeVar = #type_var{id = VarName, name = VarName},
                    unify_impl(ConcreteLen, TypeVar, Subst);
                false ->
                    % Not a type variable, fall through to concrete comparison
                    case {evaluate_length_expr(Len1), evaluate_length_expr(Len2)} of
                        {{ok, N}, {ok, N}} when is_integer(N) ->
                            {ok, Subst};
                        {{ok, N1}, {ok, N2}} when is_integer(N1), is_integer(N2), N1 =/= N2 ->
                            {error, {length_mismatch, N1, N2}};
                        _ ->
                            case expr_equal(Len1, Len2) of
                                true -> {ok, Subst};
                                false -> {error, {vector_dimension_mismatch, Len1, Len2}}
                            end
                    end
            end;
        _ ->
            % Both are concrete expressions - evaluate them
            case {evaluate_length_expr(Len1), evaluate_length_expr(Len2)} of
                {{ok, N}, {ok, N}} when is_integer(N) ->
                    % Same evaluated length
                    io:format("DEBUG: Same concrete lengths: ~p~n", [N]),
                    {ok, Subst};
                {{ok, N1}, {ok, N2}} when is_integer(N1), is_integer(N2), N1 =/= N2 ->
                    % Different evaluated lengths
                    io:format("DEBUG: Different concrete lengths: ~p vs ~p~n", [N1, N2]),
                    {error, {length_mismatch, N1, N2}};
                _Other ->
                    % Fall back to structural comparison
                    io:format("DEBUG: Falling back to structural comparison~n"),
                    case expr_equal(Len1, Len2) of
                        true ->
                            {ok, Subst};
                        false ->
                            {error, {vector_dimension_mismatch, Len1, Len2}}
                    end
            end
    end.

unify_type_params([], [], Subst) ->
    {ok, Subst};
unify_type_params(
    [#type_param{value = V1} | T1],
    [#type_param{value = V2} | T2],
    Subst
) ->
    case unify_impl(V1, V2, Subst) of
        {ok, Subst1} -> unify_type_params(T1, T2, Subst1);
        Error -> Error
    end;
% Handle extended type_param format with name field
unify_type_params(
    [Param1 | T1],
    [Param2 | T2],
    Subst
) ->
    % Extract values from various type_param formats
    V1 = extract_type_param_value(Param1),
    V2 = extract_type_param_value(Param2),
    case unify_impl(V1, V2, Subst) of
        {ok, Subst1} -> unify_type_params(T1, T2, Subst1);
        Error -> Error
    end.

%% Expression equality (simplified)
expr_equal(Expr1, Expr2) ->
    % Simplified structural equality - would need full expression comparison
    Expr1 =:= Expr2.

%% Helper functions for dependent type parameter extraction
extract_list_params([]) ->
    {error, missing_params};
extract_list_params([#type_param{name = elem_type, value = ElemType}]) ->
    {ok, ElemType, undefined};
extract_list_params([
    #type_param{name = elem_type, value = ElemType},
    #type_param{name = length, value = Length}
]) ->
    {ok, ElemType, Length};
extract_list_params([
    #type_param{name = length, value = Length},
    #type_param{name = elem_type, value = ElemType}
]) ->
    {ok, ElemType, Length};
extract_list_params([Param1, Param2]) ->
    % Try to extract without checking names as fallback
    Value1 = safe_extract_param_value(Param1),
    Value2 = safe_extract_param_value(Param2),
    {ok, Value1, Value2};
extract_list_params([Param]) ->
    % Single parameter, assume it's element type
    Value = safe_extract_param_value(Param),
    {ok, Value, undefined};
extract_list_params(_) ->
    {error, invalid_list_params}.

extract_vector_params([]) ->
    {error, missing_params};
extract_vector_params([#type_param{name = elem_type, value = ElemType}]) ->
    {ok, ElemType, undefined};
extract_vector_params([
    #type_param{name = elem_type, value = ElemType},
    #type_param{name = length, value = Length}
]) ->
    {ok, ElemType, Length};
extract_vector_params([
    #type_param{name = length, value = Length},
    #type_param{name = elem_type, value = ElemType}
]) ->
    {ok, ElemType, Length};
extract_vector_params([Param1, Param2]) ->
    % Handle compiled tuple format: {type_param, name, bound, value}
    % or old format: {type_param, name, value, bound}
    case extract_param_info(Param1, Param2) of
        {ok, ElemType, Length} ->
            {ok, ElemType, Length};
        {error, _} ->
            % Fallback: assume first is elem_type, second is length
            ElemType = safe_extract_param_value(Param1),
            Length = safe_extract_param_value(Param2),
            {ok, ElemType, Length}
    end;
extract_vector_params([Param]) ->
    % Single parameter, assume it's element type
    Value = safe_extract_param_value(Param),
    {ok, Value, undefined};
extract_vector_params(_) ->
    {error, invalid_vector_params}.

%% Predicate compatibility checking (simplified)
predicates_compatible(Pred1, Pred2) when is_function(Pred1), is_function(Pred2) ->
    % For now, assume all predicates are compatible
    % In full implementation, would analyze predicate relationships
    true;
% Same predicate
predicates_compatible(Pred, Pred) ->
    true;
% Default to compatible for now
predicates_compatible(_, _) ->
    true.

%% Constraint compatibility for liquid types
constraints_compatible(Constraints1, Constraints2) ->
    % For now, simple structural equality
    % In full implementation, would check logical compatibility
    Constraints1 =:= Constraints2.

%% Extract parameter info from tuple format
extract_param_info(Param1, Param2) ->
    case {get_tuple_param_info(Param1), get_tuple_param_info(Param2)} of
        {{elem_type, ElemType}, {length, Length}} ->
            {ok, ElemType, Length};
        {{length, Length}, {elem_type, ElemType}} ->
            {ok, ElemType, Length};
        _ ->
            {error, cannot_extract}
    end.

%% Get parameter name and value from AST record format (covers both record and tuple formats)
get_tuple_param_info(#type_param{name = Name, value = Value}) ->
    {Name, Value};
get_tuple_param_info(_Other) ->
    {unknown, undefined}.

%% Safe parameter value extraction for AST record format
safe_extract_param_value(#type_param{value = undefined}) ->
    % Create a fresh type variable for undefined values
    new_type_var();
safe_extract_param_value(#type_param{value = Value}) ->
    Value;
safe_extract_param_value(Value) ->
    % Handle cases where it's not a type_param record
    Value.

%% Apply substitution to types
apply_substitution(#type_var{id = Id}, Subst) ->
    case maps:get(Id, Subst, undefined) of
        undefined -> #type_var{id = Id};
        Type -> apply_substitution(Type, Subst)
    end;
apply_substitution({function_type, Params, Return}, Subst) ->
    {function_type, [apply_substitution(P, Subst) || P <- Params],
        apply_substitution(Return, Subst)};
apply_substitution({list_type, ElemType, LenExpr}, Subst) ->
    {list_type, apply_substitution(ElemType, Subst),
        case LenExpr of
            undefined -> undefined;
            _ -> apply_substitution_to_expr(LenExpr, Subst)
        end};
apply_substitution({dependent_type, Name, Params}, Subst) ->
    {dependent_type, Name, [apply_substitution_to_param(P, Subst) || P <- Params]};
apply_substitution({refined_type, BaseType, Predicate}, Subst) ->
    {refined_type, apply_substitution(BaseType, Subst), Predicate};
apply_substitution({gadt_constructor, Name, Args, ReturnType}, Subst) ->
    {gadt_constructor, Name, [apply_substitution(Arg, Subst) || Arg <- Args],
        apply_substitution(ReturnType, Subst)};
apply_substitution({proof_type, Name, BaseType, Predicate}, Subst) ->
    {proof_type, Name, apply_substitution(BaseType, Subst), Predicate};
apply_substitution({liquid_type, Name, BaseType, Constraints, Context}, Subst) ->
    {liquid_type, Name, apply_substitution(BaseType, Subst), Constraints, Context};
apply_substitution({phantom_type, Name}, _Subst) ->
    {phantom_type, Name};
apply_substitution(undefined, _Subst) ->
    % undefined remains undefined
    undefined;
apply_substitution(Atom, Subst) when is_atom(Atom) ->
    % Handle atoms as type variable IDs (for type family patterns)
    case maps:get(Atom, Subst, undefined) of
        undefined -> Atom;
        Type -> apply_substitution(Type, Subst)
    end;
apply_substitution(Type, _Subst) ->
    Type.

%% Apply substitution to type parameters (handles types and expressions)
apply_substitution_to_param(Param, Subst) ->
    case Param of
        % Type parameter record
        #type_param{name = Name, value = Value} ->
            #type_param{name = Name, value = apply_substitution_to_param(Value, Subst)};
        % Type expressions
        {primitive_type, _} ->
            apply_substitution(Param, Subst);
        {dependent_type, _, _} ->
            apply_substitution(Param, Subst);
        {function_type, _, _} ->
            apply_substitution(Param, Subst);
        {list_type, _, _} ->
            apply_substitution(Param, Subst);
        #type_var{} ->
            apply_substitution(Param, Subst);
        % Literal expressions - pass through unchanged
        {literal_expr, _, _} ->
            Param;
        {identifier_expr, _, _} ->
            Param;
        {binary_op_expr, _, _, _, _} ->
            Param;
        % Other expressions
        _ when is_atom(Param) -> apply_substitution(Param, Subst);
        _ ->
            Param
    end.

%% Apply substitution to expressions (simplified)
apply_substitution_to_expr(Expr, _Subst) ->
    % In full implementation, would substitute type variables in expressions
    Expr.

%% Type inference entry point
infer_type(Expr, Env) ->
    infer_type(Expr, Env, []).

infer_type(Expr, Env, Constraints) ->
    case infer_expr(Expr, Env) of
        {ok, Type, NewConstraints} ->
            AllConstraints = Constraints ++ NewConstraints,
            case solve_constraints(AllConstraints) of
                {ok, Subst} ->
                    FinalType = apply_substitution(Type, Subst),
                    {ok, #inference_result{
                        type = FinalType,
                        constraints = AllConstraints,
                        substitution = Subst
                    }};
                {error, Reason} ->
                    {error, {constraint_solving_failed, Reason}}
            end;
        {error, Reason} ->
            {error, {type_inference_failed, Reason}}
    end.

%% Type inference for expressions
infer_expr({literal_expr, Value, _Location}, _Env) ->
    Type = infer_literal_type(Value),
    {ok, Type, []};
infer_expr({identifier_expr, Name, Location}, Env) ->
    case lookup_env(Env, Name) of
        undefined ->
            {error, {unbound_variable, Name, Location}};
        Type ->
            {ok, Type, []}
    end;
infer_expr({binary_op_expr, Op, Left, Right, Location}, Env) ->
    case infer_expr(Left, Env) of
        {ok, LeftType, LeftConstraints} ->
            case infer_expr(Right, Env) of
                {ok, RightType, RightConstraints} ->
                    infer_binary_op(
                        Op,
                        LeftType,
                        RightType,
                        Location,
                        LeftConstraints ++ RightConstraints
                    );
                Error ->
                    Error
            end;
        Error ->
            Error
    end;
infer_expr({unary_op_expr, Op, Operand, Location}, Env) ->
    case infer_expr(Operand, Env) of
        {ok, OperandType, OperandConstraints} ->
            infer_unary_op(Op, OperandType, Location, OperandConstraints);
        Error ->
            Error
    end;
infer_expr({function_call_expr, Function, Args, Location}, Env) ->
    % Special debug output for dot_product calls
    case Function of
        {identifier_expr, dot_product, _} ->
            io:format("\n*** DEBUG: DOT_PRODUCT CALL DETECTED ***~n"),
            io:format("DEBUG: Function: ~p~n", [Function]),
            io:format("DEBUG: Args: ~p~n", [Args]);
        _ ->
            ok
    end,
    io:format("DEBUG: Function call inference for ~p with args ~p~n", [Function, Args]),
    case infer_expr(Function, Env) of
        {ok, FuncType, FuncConstraints} ->
            % Special debug for dot_product
            case Function of
                {identifier_expr, dot_product, _} ->
                    io:format("*** DEBUG: dot_product function type: ~p~n", [FuncType]);
                _ ->
                    ok
            end,
            io:format("DEBUG: Function type: ~p~n", [FuncType]),
            case infer_args(Args, Env) of
                {ok, ArgTypes, ArgConstraints} ->
                    % Special debug for dot_product arguments
                    case Function of
                        {identifier_expr, dot_product, _} ->
                            io:format("*** DEBUG: dot_product argument types: ~p~n", [ArgTypes]);
                        _ ->
                            ok
                    end,
                    io:format("DEBUG: Argument types: ~p~n", [ArgTypes]),

                    % Handle curried function application: f(a, b) becomes f(a)(b)
                    infer_curried_application(
                        FuncType, ArgTypes, Location, FuncConstraints ++ ArgConstraints
                    );
                Error ->
                    Error
            end;
        Error ->
            Error
    end;
infer_expr({if_expr, Condition, ThenBranch, ElseBranch, Location}, Env) ->
    case infer_expr(Condition, Env) of
        {ok, CondType, CondConstraints} ->
            BoolConstraint = #type_constraint{
                left = CondType,
                op = '=',
                right = ?TYPE_BOOL,
                location = Location
            },
            case infer_expr(ThenBranch, Env) of
                {ok, ThenType, ThenConstraints} ->
                    case infer_expr(ElseBranch, Env) of
                        {ok, ElseType, ElseConstraints} ->
                            UnifyConstraint = #type_constraint{
                                left = ThenType,
                                op = '=',
                                right = ElseType,
                                location = Location
                            },
                            AllConstraints =
                                CondConstraints ++ ThenConstraints ++
                                    ElseConstraints ++ [BoolConstraint, UnifyConstraint],
                            {ok, ThenType, AllConstraints};
                        Error ->
                            Error
                    end;
                Error ->
                    Error
            end;
        Error ->
            Error
    end;
infer_expr({let_expr, Bindings, Body, _Location}, Env) ->
    infer_let_expr(Bindings, Body, Env, []);
infer_expr({list_expr, Elements, Location}, Env) ->
    case Elements of
        [] ->
            ElemType = new_type_var(),
            LenExpr = {literal_expr, 0, Location},
            {ok, {list_type, ElemType, LenExpr}, []};
        [FirstElem | RestElems] ->
            case infer_expr(FirstElem, Env) of
                {ok, ElemType, FirstConstraints} ->
                    case infer_list_elements(RestElems, ElemType, Env, FirstConstraints) of
                        {ok, FinalConstraints} ->
                            Length = length(Elements),
                            LenExpr = {literal_expr, Length, Location},
                            {ok, {list_type, ElemType, LenExpr}, FinalConstraints};
                        Error ->
                            Error
                    end;
                Error ->
                    Error
            end
    end;
infer_expr({match_expr, MatchExpr, Patterns, _Location}, Env) ->
    case infer_expr(MatchExpr, Env) of
        {ok, MatchType, MatchConstraints} ->
            case infer_match_clauses(Patterns, MatchType, Env) of
                {ok, ResultType, ClauseConstraints} ->
                    {ok, ResultType, MatchConstraints ++ ClauseConstraints};
                Error ->
                    Error
            end;
        Error ->
            Error
    end;
infer_expr({lambda_expr, Params, Body, _Location}, Env) ->
    % Create type variables for parameters
    ParamTypes = [new_type_var() || _ <- Params],

    % Add parameters to environment
    ParamPairs = lists:zip(Params, ParamTypes),
    NewEnv = lists:foldl(
        fun({{param, ParamName, _TypeExpr, _ParamLocation}, ParamType}, AccEnv) ->
            extend_env(AccEnv, ParamName, ParamType)
        end,
        Env,
        ParamPairs
    ),

    % Infer body type
    case infer_expr(Body, NewEnv) of
        {ok, BodyType, BodyConstraints} ->
            % Create curried function type: fn(a, b) -> fn(a) -> fn(b) -> body
            LambdaType = build_curried_function_type(ParamTypes, BodyType),
            {ok, LambdaType, BodyConstraints};
        Error ->
            Error
    end;
infer_expr({cons_expr, Elements, Tail, Location}, Env) ->
    % Type a cons expression [h1, h2, ... | tail]
    case Elements of
        [] ->
            % Empty head list - just return the tail type
            case infer_expr(Tail, Env) of
                {ok, TailType, TailConstraints} ->
                    {ok, TailType, TailConstraints};
                Error ->
                    Error
            end;
        [FirstElem | RestElems] ->
            % Infer type of first element
            case infer_expr(FirstElem, Env) of
                {ok, ElemType, FirstConstraints} ->
                    % Check that all elements have same type
                    case infer_list_elements(RestElems, ElemType, Env, FirstConstraints) of
                        {ok, ElemConstraints} ->
                            % Infer tail type and ensure it's a list of the same element type
                            case infer_expr(Tail, Env) of
                                {ok, TailType, TailConstraints} ->
                                    % Create constraint: tail must be List(ElemType)
                                    ExpectedTailType = {list_type, ElemType, new_type_var()},
                                    TailConstraint = #type_constraint{
                                        left = TailType,
                                        op = '=',
                                        right = ExpectedTailType,
                                        location = Location
                                    },
                                    % Result type is also List(ElemType) with unknown length
                                    ResultType = {list_type, ElemType, new_type_var()},
                                    AllConstraints =
                                        ElemConstraints ++ TailConstraints ++ [TailConstraint],
                                    {ok, ResultType, AllConstraints};
                                Error ->
                                    Error
                            end;
                        Error ->
                            Error
                    end;
                Error ->
                    Error
            end
    end;
infer_expr(Expr, _Env) ->
    {error, {unsupported_expression, Expr}}.

%% Build curried function type from parameter list: [A, B, C] -> Body becomes A -> (B -> (C -> Body))
build_curried_function_type([], BodyType) ->
    BodyType;
build_curried_function_type([ParamType | RestParams], BodyType) ->
    RestFuncType = build_curried_function_type(RestParams, BodyType),
    {function_type, [ParamType], RestFuncType}.

%% Helper functions for type inference
infer_literal_type(N) when is_integer(N) -> ?TYPE_INT;
infer_literal_type(F) when is_float(F) -> ?TYPE_FLOAT;
infer_literal_type(S) when is_list(S) -> ?TYPE_STRING;
infer_literal_type(B) when is_boolean(B) -> ?TYPE_BOOL;
infer_literal_type(A) when is_atom(A) -> ?TYPE_ATOM.

%% Instantiate function type with fresh type variables while preserving sharing
instantiate_function_type({function_type, ParamTypes, ReturnType}) ->
    io:format("DEBUG: Instantiating function type with params: ~p~n", [ParamTypes]),
    % Create a mapping from type variable names to fresh type variables
    TypeVarMap = collect_type_variables(ParamTypes ++ [ReturnType]),
    io:format("DEBUG: Type variable map: ~p~n", [TypeVarMap]),

    % Instantiate parameter types with shared variables
    InstParamTypes = [instantiate_type_with_map(PT, TypeVarMap) || PT <- ParamTypes],
    InstReturnType = instantiate_type_with_map(ReturnType, TypeVarMap),

    io:format("DEBUG: Instantiated params: ~p~n", [InstParamTypes]),
    io:format("DEBUG: Instantiated return: ~p~n", [InstReturnType]),

    {ok, {function_type, InstParamTypes, InstReturnType}, []};
instantiate_function_type(Type) ->
    % Not a function type, return as-is
    {error, {not_function_type, Type}}.

%% Collect all type variables in a list of types and create fresh mappings
collect_type_variables(Types) ->
    collect_type_variables(Types, #{}).

collect_type_variables([], Map) ->
    Map;
collect_type_variables([Type | Rest], Map) ->
    NewMap = collect_type_variables_in_type(Type, Map),
    collect_type_variables(Rest, NewMap).

%% Collect type variables in a single type
collect_type_variables_in_type({dependent_type, _Name, Params}, Map) ->
    lists:foldl(
        fun(Param, AccMap) ->
            case extract_type_param_value(Param) of
                {identifier_expr, VarName, _} ->
                    case maps:is_key(VarName, AccMap) of
                        % Already have a mapping
                        true -> AccMap;
                        false -> maps:put(VarName, new_type_var(), AccMap)
                    end;
                _ ->
                    AccMap
            end
        end,
        Map,
        Params
    );
collect_type_variables_in_type({function_type, ParamTypes, ReturnType}, Map) ->
    Map1 = collect_type_variables(ParamTypes, Map),
    collect_type_variables_in_type(ReturnType, Map1);
collect_type_variables_in_type({list_type, ElemType, _Length}, Map) ->
    collect_type_variables_in_type(ElemType, Map);
collect_type_variables_in_type({primitive_type, Name}, Map) ->
    % Handle primitive types that represent generic type variables
    case is_generic_type_variable_name(Name) of
        true ->
            case maps:is_key(Name, Map) of
                % Already have a mapping
                true -> Map;
                % Create new mapping
                false -> maps:put(Name, new_type_var(), Map)
            end;
        false ->
            % Not a generic type variable, leave as-is
            Map
    end;
collect_type_variables_in_type(_, Map) ->
    Map.

%% Instantiate a type using the type variable map
instantiate_type_with_map({dependent_type, Name, Params}, Map) ->
    InstParams = [instantiate_param_with_map(P, Map) || P <- Params],
    {dependent_type, Name, InstParams};
instantiate_type_with_map({function_type, ParamTypes, ReturnType}, Map) ->
    InstParamTypes = [instantiate_type_with_map(PT, Map) || PT <- ParamTypes],
    InstReturnType = instantiate_type_with_map(ReturnType, Map),
    {function_type, InstParamTypes, InstReturnType};
instantiate_type_with_map({list_type, ElemType, Length}, Map) ->
    {list_type, instantiate_type_with_map(ElemType, Map), Length};
instantiate_type_with_map({primitive_type, Name}, Map) ->
    % Handle primitive types that represent generic type variables
    case is_generic_type_variable_name(Name) of
        true ->
            case maps:get(Name, Map, undefined) of
                % No mapping, keep as-is
                undefined -> {primitive_type, Name};
                % Replace with instantiated type variable
                TypeVar -> TypeVar
            end;
        false ->
            % Not a generic type variable, keep as primitive
            {primitive_type, Name}
    end;
instantiate_type_with_map(Type, _Map) ->
    Type.

%% Instantiate a type parameter using the map
instantiate_param_with_map(Param, Map) ->
    Value = extract_type_param_value(Param),
    case Value of
        {identifier_expr, VarName, _Location} ->
            case maps:get(VarName, Map, undefined) of
                % Keep original if not found
                undefined -> Param;
                TypeVar -> update_param_value(Param, TypeVar)
            end;
        _ ->
            Param
    end.

%% Update the value in a type parameter
update_param_value(#type_param{name = _Name, value = _OldValue} = Param, NewValue) ->
    Param#type_param{value = NewValue};
update_param_value(_Param, NewValue) ->
    % Fallback - create new param structure
    #type_param{name = undefined, value = NewValue}.

%% Check if a name represents a generic type variable (T, E, U, etc.)
is_generic_type_variable_name(Name) ->
    % Check if it's a common generic type variable name pattern
    case atom_to_list(Name) of
        % Single letter: T, E, U, n, etc.
        [C] when (C >= $A andalso C =< $Z) orelse (C >= $a andalso C =< $z) -> true;
        % Type variables like T1, T2, etc.
        "T" ++ _ -> true;
        % Error type variables
        "E" ++ _ -> true;
        % Other generic variables
        "U" ++ _ -> true;
        % Generic A variables
        "A" ++ _ -> true;
        % Generic B variables
        "B" ++ _ -> true;
        % Generic C variables
        "C" ++ _ -> true;
        % Generic F variables (for function types)
        "F" ++ _ -> true;
        % Common lowercase type variables
        "n" ++ _ -> true;
        "m" ++ _ -> true;
        "k" ++ _ -> true;
        _ -> false
    end.

%% Infer curried function application: f(a1, a2, ..., an) becomes f(a1)(a2)...(an)
infer_curried_application(FuncType, [], _Location, Constraints) ->
    % No arguments - return function as-is
    {ok, FuncType, Constraints};
infer_curried_application(FuncType, ArgTypes, Location, Constraints) ->
    % Try to apply all arguments at once first (for multi-parameter functions)
    case apply_all_args_at_once(FuncType, ArgTypes, Location) of
        {ok, ResultType, NewConstraints} ->
            {ok, ResultType, Constraints ++ NewConstraints};
        {error, _Reason} ->
            % Fall back to curried application
            apply_args_curried(FuncType, ArgTypes, Location, Constraints)
    end.

%% Apply all arguments to a multi-parameter function at once
apply_all_args_at_once(FuncType, ArgTypes, Location) ->
    case instantiate_function_type(FuncType) of
        {ok, {function_type, ParamTypes, ReturnType}, InstConstraints} when
            length(ParamTypes) =:= length(ArgTypes)
        ->
            % Multi-parameter function with matching arity - apply all args
            Constraints = lists:zipwith(
                fun(ParamType, ArgType) ->
                    #type_constraint{
                        left = ParamType,
                        op = '=',
                        right = ArgType,
                        location = Location
                    }
                end,
                ParamTypes,
                ArgTypes
            ),
            {ok, ReturnType, InstConstraints ++ Constraints};
        _ ->
            % Not a matching multi-parameter function
            {error, not_matching_multi_param}
    end.

%% Apply arguments one by one (curried style)
apply_args_curried(FuncType, [], _Location, Constraints) ->
    {ok, FuncType, Constraints};
apply_args_curried(FuncType, [ArgType | RestArgs], Location, Constraints) ->
    % Apply function to first argument
    case apply_function_to_arg(FuncType, ArgType, Location) of
        {ok, ResultType, NewConstraints} ->
            % Recursively apply to remaining arguments
            apply_args_curried(
                ResultType, RestArgs, Location, Constraints ++ NewConstraints
            );
        {error, Reason} ->
            {error, Reason}
    end.

%% Apply a function type to a single argument
apply_function_to_arg(FuncType, ArgType, Location) ->
    case instantiate_function_type(FuncType) of
        {ok, {function_type, [ParamType], ReturnType}, InstConstraints} ->
            % Single parameter function - apply directly
            Constraint = #type_constraint{
                left = ParamType,
                op = '=',
                right = ArgType,
                location = Location
            },
            {ok, ReturnType, InstConstraints ++ [Constraint]};
        {ok, {function_type, [ParamType | RestParams], ReturnType}, InstConstraints} when
            RestParams =/= []
        ->
            % Multi-parameter function - apply first param and return curried function
            Constraint = #type_constraint{
                left = ParamType,
                op = '=',
                right = ArgType,
                location = Location
            },
            CurriedType = {function_type, RestParams, ReturnType},
            {ok, CurriedType, InstConstraints ++ [Constraint]};
        {ok, {function_type, [], _ReturnType}, _InstConstraints} ->
            % Zero parameter function - cannot apply argument
            {error, {cannot_apply_to_nullary_function, FuncType, ArgType}};
        {error, _Reason} ->
            % Not a function type - create expected function type and unify
            ReturnType = new_type_var(),
            ExpectedFuncType = {function_type, [ArgType], ReturnType},
            UnifyConstraint = #type_constraint{
                left = FuncType,
                op = '=',
                right = ExpectedFuncType,
                location = Location
            },
            {ok, ReturnType, [UnifyConstraint]}
    end.

infer_binary_op('+', LeftType, RightType, Location, Constraints) ->
    ResultType = new_type_var(),
    NumConstraints = [
        #type_constraint{left = LeftType, op = '=', right = RightType, location = Location},
        #type_constraint{left = LeftType, op = '=', right = ResultType, location = Location}
    ],
    {ok, ResultType, Constraints ++ NumConstraints};
infer_binary_op('-', LeftType, RightType, Location, Constraints) ->
    ResultType = new_type_var(),
    NumConstraints = [
        #type_constraint{left = LeftType, op = '=', right = RightType, location = Location},
        #type_constraint{left = LeftType, op = '=', right = ResultType, location = Location}
    ],
    {ok, ResultType, Constraints ++ NumConstraints};
infer_binary_op('*', LeftType, RightType, Location, Constraints) ->
    ResultType = new_type_var(),
    NumConstraints = [
        #type_constraint{left = LeftType, op = '=', right = RightType, location = Location},
        #type_constraint{left = LeftType, op = '=', right = ResultType, location = Location}
    ],
    {ok, ResultType, Constraints ++ NumConstraints};
infer_binary_op('==', LeftType, RightType, Location, Constraints) ->
    EqualityConstraint = #type_constraint{
        left = LeftType,
        op = '=',
        right = RightType,
        location = Location
    },
    {ok, ?TYPE_BOOL, Constraints ++ [EqualityConstraint]};
infer_binary_op('>', LeftType, RightType, Location, Constraints) ->
    % Allow generic comparison - both operands must be the same type
    ComparisonConstraint = #type_constraint{
        left = LeftType,
        op = '=',
        right = RightType,
        location = Location
    },
    {ok, ?TYPE_BOOL, Constraints ++ [ComparisonConstraint]};
infer_binary_op('<', LeftType, RightType, Location, Constraints) ->
    % Allow generic comparison - both operands must be the same type
    ComparisonConstraint = #type_constraint{
        left = LeftType,
        op = '=',
        right = RightType,
        location = Location
    },
    {ok, ?TYPE_BOOL, Constraints ++ [ComparisonConstraint]};
infer_binary_op('>=', LeftType, RightType, Location, Constraints) ->
    % Allow generic comparison - both operands must be the same type
    ComparisonConstraint = #type_constraint{
        left = LeftType,
        op = '=',
        right = RightType,
        location = Location
    },
    {ok, ?TYPE_BOOL, Constraints ++ [ComparisonConstraint]};
infer_binary_op('=<', LeftType, RightType, Location, Constraints) ->
    % Allow generic comparison - both operands must be the same type
    ComparisonConstraint = #type_constraint{
        left = LeftType,
        op = '=',
        right = RightType,
        location = Location
    },
    {ok, ?TYPE_BOOL, Constraints ++ [ComparisonConstraint]};
infer_binary_op('<=', LeftType, RightType, Location, Constraints) ->
    % Allow generic comparison - both operands must be the same type
    ComparisonConstraint = #type_constraint{
        left = LeftType,
        op = '=',
        right = RightType,
        location = Location
    },
    {ok, ?TYPE_BOOL, Constraints ++ [ComparisonConstraint]};
infer_binary_op('!=', LeftType, RightType, Location, Constraints) ->
    EqualityConstraint = #type_constraint{
        left = LeftType,
        op = '=',
        right = RightType,
        location = Location
    },
    {ok, ?TYPE_BOOL, Constraints ++ [EqualityConstraint]};
infer_binary_op('++', LeftType, RightType, Location, Constraints) ->
    % String concatenation: both operands must be strings, result is string
    StringConstraints = [
        #type_constraint{left = LeftType, op = '=', right = ?TYPE_STRING, location = Location},
        #type_constraint{left = RightType, op = '=', right = ?TYPE_STRING, location = Location}
    ],
    {ok, ?TYPE_STRING, Constraints ++ StringConstraints};
infer_binary_op(Op, _LeftType, _RightType, Location, _Constraints) ->
    {error, {unsupported_binary_operator, Op, Location}}.

%% Type inference for unary operations
infer_unary_op('-', OperandType, Location, Constraints) ->
    % Unary minus: operand must be a numeric type (Int or Float), result has same type
    ResultType = new_type_var(),
    NumericConstraint = #type_constraint{
        left = OperandType,
        op = '=',
        right = ResultType,
        location = Location
    },
    % For now, accept any numeric type - could be more specific later
    {ok, ResultType, Constraints ++ [NumericConstraint]};
infer_unary_op('+', OperandType, Location, Constraints) ->
    % Unary plus: operand must be a numeric type, result has same type
    ResultType = new_type_var(),
    NumericConstraint = #type_constraint{
        left = OperandType,
        op = '=',
        right = ResultType,
        location = Location
    },
    {ok, ResultType, Constraints ++ [NumericConstraint]};
infer_unary_op('not', OperandType, Location, Constraints) ->
    % Logical not: operand must be Bool, result is Bool
    BoolConstraint = #type_constraint{
        left = OperandType,
        op = '=',
        right = ?TYPE_BOOL,
        location = Location
    },
    {ok, ?TYPE_BOOL, Constraints ++ [BoolConstraint]};
infer_unary_op(Op, _OperandType, Location, _Constraints) ->
    {error, {unsupported_unary_operator, Op, Location}}.

infer_args([], _Env) ->
    {ok, [], []};
infer_args([Arg | RestArgs], Env) ->
    case infer_expr(Arg, Env) of
        {ok, ArgType, ArgConstraints} ->
            case infer_args(RestArgs, Env) of
                {ok, RestTypes, RestConstraints} ->
                    {ok, [ArgType | RestTypes], ArgConstraints ++ RestConstraints};
                Error ->
                    Error
            end;
        Error ->
            Error
    end.

infer_let_expr([], Body, Env, Constraints) ->
    case infer_expr(Body, Env) of
        {ok, BodyType, BodyConstraints} ->
            {ok, BodyType, Constraints ++ BodyConstraints};
        Error ->
            Error
    end;
infer_let_expr([{binding, Pattern, Value, _Location} | RestBindings], Body, Env, Constraints) ->
    case infer_expr(Value, Env) of
        {ok, ValueType, ValueConstraints} ->
            case infer_pattern(Pattern) of
                {ok, PatternType, VarName} ->
                    UnifyConstraint = #type_constraint{
                        left = PatternType,
                        op = '=',
                        right = ValueType,
                        location = undefined
                    },
                    NewEnv = extend_env(Env, VarName, ValueType),
                    AllConstraints = Constraints ++ ValueConstraints ++ [UnifyConstraint],
                    infer_let_expr(RestBindings, Body, NewEnv, AllConstraints);
                Error ->
                    Error
            end;
        Error ->
            Error
    end.

infer_pattern({identifier_pattern, Name, _Location}) ->
    PatternType = new_type_var(),
    {ok, PatternType, Name}.

infer_list_elements([], _ElemType, _Env, Constraints) ->
    {ok, Constraints};
infer_list_elements([Elem | RestElems], ElemType, Env, Constraints) ->
    case infer_expr(Elem, Env) of
        {ok, ElemTypeInferred, ElemConstraints} ->
            UnifyConstraint = #type_constraint{
                left = ElemType,
                op = '=',
                right = ElemTypeInferred,
                location = undefined
            },
            NewConstraints = Constraints ++ ElemConstraints ++ [UnifyConstraint],
            infer_list_elements(RestElems, ElemType, Env, NewConstraints);
        Error ->
            Error
    end.

infer_match_clauses([], _MatchType, _Env) ->
    % No patterns - should not happen in valid code
    {error, no_match_patterns};
infer_match_clauses([{match_clause, Pattern, Guard, Body, _Location}], MatchType, Env) ->
    % Single pattern - infer its type and body type
    case infer_pattern_type(Pattern, MatchType, Env) of
        {ok, PatternEnv, PatternConstraints} ->
            % Check guard if present
            GuardConstraints =
                case Guard of
                    undefined ->
                        [];
                    _ ->
                        case infer_expr(Guard, PatternEnv) of
                            {ok, GuardType, GConstraints} ->
                                BoolConstraint = #type_constraint{
                                    left = GuardType,
                                    op = '=',
                                    right = ?TYPE_BOOL,
                                    location = undefined
                                },
                                GConstraints ++ [BoolConstraint];
                            {error, _} ->
                                []
                        end
                end,
            % Infer body type in pattern environment
            case infer_expr(Body, PatternEnv) of
                {ok, BodyType, BodyConstraints} ->
                    AllConstraints = PatternConstraints ++ GuardConstraints ++ BodyConstraints,
                    {ok, BodyType, AllConstraints};
                Error ->
                    Error
            end;
        Error ->
            Error
    end;
infer_match_clauses([FirstClause | RestClauses], MatchType, Env) ->
    % Multiple patterns - all must return the same type
    case infer_match_clauses([FirstClause], MatchType, Env) of
        {ok, FirstType, FirstConstraints} ->
            case infer_match_clauses(RestClauses, MatchType, Env) of
                {ok, RestType, RestConstraints} ->
                    UnifyConstraint = #type_constraint{
                        left = FirstType,
                        op = '=',
                        right = RestType,
                        location = undefined
                    },
                    {ok, FirstType, FirstConstraints ++ RestConstraints ++ [UnifyConstraint]};
                Error ->
                    Error
            end;
        Error ->
            Error
    end.

infer_pattern_type({list_pattern, Elements, Tail, _Location} = Pattern, MatchType, Env) ->
    % For list patterns, create environment with pattern variables and length constraints
    case infer_list_pattern_elements(Elements, Tail, MatchType, Env, []) of
        {ok, PatternEnv, Constraints} ->
            % Add length constraints from SMT solver for dependent types
            LengthConstraints =
                case MatchType of
                    {dependent_type, 'List', [_TypeParam, LengthParam]} ->
                        % Generate SMT constraints for pattern matching on dependent lists
                        cure_smt_solver:infer_pattern_length_constraint(
                            Pattern, extract_length_var(LengthParam)
                        );
                    {list_type, _ElemType, {dependent_length, LengthVar}} ->
                        cure_smt_solver:infer_pattern_length(
                            Pattern, cure_smt_solver:variable_term(LengthVar)
                        );
                    _ ->
                        []
                end,
            SMTConstraints = [convert_smt_to_type_constraint(C) || C <- LengthConstraints],
            {ok, PatternEnv, Constraints ++ SMTConstraints};
        Error ->
            Error
    end;
infer_pattern_type({identifier_pattern, Name, _Location}, MatchType, Env) ->
    % Add identifier to environment with the match type
    NewEnv = extend_env(Env, Name, MatchType),
    {ok, NewEnv, []};
infer_pattern_type({wildcard_pattern, _Location}, _MatchType, Env) ->
    % Wildcard doesn't bind any variables
    {ok, Env, []};
infer_pattern_type({constructor_pattern, ConstructorName, Args, _Location}, _MatchType, Env) ->
    % Handle constructor patterns like Ok(value), Error(err), Some(x), None
    case Args of
        undefined ->
            % Nullary constructor like None
            {ok, Env, []};
        [] ->
            % Nullary constructor like None
            {ok, Env, []};
        ArgPatterns ->
            % Constructor with arguments - need to infer argument types from constructor
            case lookup_env(Env, ConstructorName) of
                undefined ->
                    % Constructor not found in environment - treat as unbound
                    {error, {unbound_constructor, ConstructorName}};
                {function_type, ArgTypes, _ResultType} ->
                    % Constructor is a function - extract argument types
                    infer_constructor_args(ArgPatterns, ArgTypes, Env, []);
                _OtherType ->
                    % Constructor has unexpected type - treat args as generic
                    infer_constructor_args_generic(ArgPatterns, Env, [])
            end
    end;
infer_pattern_type(_Pattern, _MatchType, Env) ->
    % For other patterns, return env unchanged for now
    {ok, Env, []}.

infer_list_pattern_elements([], undefined, _MatchType, Env, Constraints) ->
    {ok, Env, Constraints};
infer_list_pattern_elements([], Tail, MatchType, Env, Constraints) ->
    % Handle tail pattern - preserve dependent type structure for lists
    TailType =
        case MatchType of
            {dependent_type, 'List', [TypeParam, LengthParam]} ->
                % Create new dependent type for tail with reduced length
                NewLengthVar = create_derived_length_var(LengthParam, "tail"),
                {dependent_type, 'List', [
                    TypeParam, #type_param{value = {identifier_expr, NewLengthVar, undefined}}
                ]};
            _ ->
                {list_type, new_type_var(), undefined}
        end,
    case infer_pattern_type(Tail, TailType, Env) of
        {ok, NewEnv, TailConstraints} ->
            {ok, NewEnv, Constraints ++ TailConstraints};
        Error ->
            Error
    end;
infer_list_pattern_elements([Element | RestElements], Tail, MatchType, Env, Constraints) ->
    ElemType =
        case MatchType of
            {dependent_type, 'List', [TypeParam, _]} -> extract_type_param_value(TypeParam);
            _ -> new_type_var()
        end,
    case infer_pattern_type(Element, ElemType, Env) of
        {ok, NewEnv, ElemConstraints} ->
            infer_list_pattern_elements(
                RestElements, Tail, MatchType, NewEnv, Constraints ++ ElemConstraints
            );
        Error ->
            Error
    end.

%% Helper for constructor pattern arguments with known types
infer_constructor_args([], [], Env, Constraints) ->
    {ok, Env, Constraints};
infer_constructor_args([Pattern | RestPatterns], [ArgType | RestArgTypes], Env, Constraints) ->
    case infer_pattern_type(Pattern, ArgType, Env) of
        {ok, NewEnv, PatternConstraints} ->
            infer_constructor_args(
                RestPatterns, RestArgTypes, NewEnv, Constraints ++ PatternConstraints
            );
        Error ->
            Error
    end;
infer_constructor_args(Patterns, ArgTypes, Env, Constraints) when
    length(Patterns) =/= length(ArgTypes)
->
    % Arity mismatch - create generic types for all patterns
    infer_constructor_args_generic(Patterns, Env, Constraints).

%% Helper for constructor pattern arguments with generic types
infer_constructor_args_generic([], Env, Constraints) ->
    {ok, Env, Constraints};
infer_constructor_args_generic([Pattern | RestPatterns], Env, Constraints) ->
    GenericType = new_type_var(),
    case infer_pattern_type(Pattern, GenericType, Env) of
        {ok, NewEnv, PatternConstraints} ->
            infer_constructor_args_generic(RestPatterns, NewEnv, Constraints ++ PatternConstraints);
        Error ->
            Error
    end.

%% Type checking (simplified)
check_type(Expr, ExpectedType, Env) ->
    check_type(Expr, ExpectedType, Env, []).

check_type(undefined, ExpectedType, _Env, _Constraints) ->
    % For undefined expressions, validate type structure and check for dimension consistency
    case is_well_formed_type(ExpectedType) of
        true ->
            case check_dimension_consistency(ExpectedType) of
                ok -> ok;
                Error -> Error
            end;
        false ->
            {error, {malformed_type, ExpectedType}}
    end;
check_type(Expr, ExpectedType, Env, Constraints) ->
    case infer_type(Expr, Env, Constraints) of
        {ok, #inference_result{type = InferredType}} ->
            case unify(InferredType, ExpectedType) of
                {ok, _Subst} -> ok;
                {error, Reason} -> {error, {type_mismatch, ExpectedType, InferredType, Reason}}
            end;
        Error ->
            Error
    end.

%% Constraint solving with SMT solver integration
solve_constraints(Constraints) ->
    solve_constraints(Constraints, #{}).

solve_constraints([], Subst) ->
    {ok, Subst};
solve_constraints(Constraints, Subst) when length(Constraints) > 0 ->
    % Temporarily use simple constraint solving while debugging dependent types
    solve_constraints_simple(Constraints, Subst).

solve_constraints_simple([], Subst) ->
    {ok, Subst};
solve_constraints_simple([Constraint | RestConstraints], Subst) ->
    case solve_constraint(Constraint, Subst) of
        {ok, NewSubst} ->
            solve_constraints_simple(RestConstraints, NewSubst);
        Error ->
            Error
    end.

%% These functions are for future SMT solver integration
-compile(
    {nowarn_unused_function, [
        {solve_type_constraints, 2},
        {partition_constraints, 1},
        {partition_constraints, 3},
        {solve_arithmetic_constraints, 2},
        {convert_to_smt_constraints, 1},
        {convert_type_constraint_to_smt, 1},
        {convert_type_to_smt_term, 1},
        {merge_substitutions, 2}
    ]}
).
solve_type_constraints([], Subst) ->
    {ok, Subst};
solve_type_constraints([Constraint | RestConstraints], Subst) ->
    case solve_constraint(Constraint, Subst) of
        {ok, NewSubst} ->
            solve_type_constraints(RestConstraints, NewSubst);
        Error ->
            Error
    end.

solve_constraint(#type_constraint{left = Left, op = '=', right = Right}, Subst) ->
    io:format("DEBUG: Solving constraint ~p = ~p~n", [Left, Right]),
    Result = unify(Left, Right, Subst),
    io:format("DEBUG: Constraint result: ~p~n", [Result]),
    Result;
solve_constraint(#type_constraint{left = Left, op = 'length_eq', right = Right}, Subst) ->
    % Handle length equality constraints for dependent types
    solve_length_constraint(Left, Right, Subst);
solve_constraint(#type_constraint{left = Left, op = Op, right = Right}, Subst) when
    Op =:= '<:' orelse Op =:= '>:'
->
    % Handle subtyping constraints
    solve_subtype_constraint(Left, Op, Right, Subst);
solve_constraint(#type_constraint{left = Left, op = 'elem_of', right = Right}, Subst) ->
    % Handle element membership constraints
    solve_element_constraint(Left, Right, Subst);
solve_constraint(#type_constraint{left = Left, op = 'implies', right = Right}, Subst) ->
    % Handle implication constraints: Left => Right
    solve_implication_constraint(Left, Right, Subst);
solve_constraint(#type_constraint{left = Left, op = 'iff', right = Right}, Subst) ->
    % Handle equivalence constraints: Left <=> Right
    solve_equivalence_constraint(Left, Right, Subst);
solve_constraint(#type_constraint{left = Left, op = 'bounds', right = Right}, Subst) ->
    % Handle bounds constraints for dependent types
    solve_bounds_constraint(Left, Right, Subst);
solve_constraint(#type_constraint{left = Left, op = 'invariant', right = Right}, Subst) ->
    % Handle type invariant constraints
    solve_invariant_constraint(Left, Right, Subst);
solve_constraint(#type_constraint{left = Left, op = 'covariant', right = Right}, Subst) ->
    % Handle covariance constraints
    solve_variance_constraint(Left, Right, covariant, Subst);
solve_constraint(#type_constraint{left = Left, op = 'contravariant', right = Right}, Subst) ->
    % Handle contravariance constraints
    solve_variance_constraint(Left, Right, contravariant, Subst);
solve_constraint(#type_constraint{op = Op}, _Subst) ->
    % For now, accept arithmetic constraints without solving them
    % This preserves basic dependent type functionality
    if
        Op =:= '>' orelse Op =:= '<' orelse Op =:= '>=' orelse Op =:= '=<' ->
            {ok, #{}};
        true ->
            {error, {unsupported_constraint_op, Op}}
    end.

%% Constraint partitioning and SMT solver integration
partition_constraints(Constraints) ->
    partition_constraints(Constraints, [], []).

partition_constraints([], TypeConstraints, ArithmeticConstraints) ->
    {lists:reverse(TypeConstraints), lists:reverse(ArithmeticConstraints)};
partition_constraints(
    [#type_constraint{op = Op} = C | Rest], TypeConstraints, ArithConstraints
) when
    Op =:= '>' orelse Op =:= '<' orelse Op =:= '>=' orelse Op =:= '=<' orelse Op =:= '/='
->
    % Arithmetic constraints
    partition_constraints(Rest, TypeConstraints, [C | ArithConstraints]);
partition_constraints([C | Rest], TypeConstraints, ArithConstraints) ->
    % Type constraints
    partition_constraints(Rest, [C | TypeConstraints], ArithConstraints).

solve_arithmetic_constraints([], _TypeSubst) ->
    {ok, #{}};
solve_arithmetic_constraints(ArithmeticConstraints, _TypeSubst) ->
    % Convert type constraints to SMT constraints and solve
    case convert_to_smt_constraints(ArithmeticConstraints) of
        {ok, SmtConstraints} ->
            case cure_smt_solver:solve_constraints(SmtConstraints) of
                {sat, Solution} ->
                    {ok, Solution};
                unsat ->
                    {error, unsatisfiable_constraints};
                unknown ->
                    % Continue without solution
                    {ok, #{}}
            end;
        {error, Reason} ->
            {error, {smt_conversion_failed, Reason}}
    end.

convert_to_smt_constraints(TypeConstraints) ->
    try
        SmtConstraints = [convert_type_constraint_to_smt(C) || C <- TypeConstraints],
        {ok, SmtConstraints}
    catch
        throw:Reason -> {error, Reason};
        _:_ -> {error, conversion_failed}
    end.

convert_type_constraint_to_smt(#type_constraint{left = Left, op = Op, right = Right}) ->
    SmtLeft = convert_type_to_smt_term(Left),
    SmtRight = convert_type_to_smt_term(Right),
    cure_smt_solver:arithmetic_constraint(SmtLeft, Op, SmtRight).

convert_type_to_smt_term(#type_var{name = Name}) when Name =/= undefined ->
    cure_smt_solver:variable_term(Name);
convert_type_to_smt_term(#type_var{id = Id}) ->
    cure_smt_solver:variable_term(list_to_atom("T" ++ integer_to_list(Id)));
convert_type_to_smt_term(Value) when is_integer(Value) ->
    cure_smt_solver:constant_term(Value);
convert_type_to_smt_term(Value) when is_atom(Value) ->
    cure_smt_solver:variable_term(Value);
convert_type_to_smt_term(_Other) ->
    throw({unsupported_type_in_smt_constraint, _Other}).

merge_substitutions(Subst1, Subst2) ->
    maps:merge(Subst1, Subst2).

%% Convert SMT constraints back to type constraints
convert_smt_to_type_constraint(SmtConstraint) ->
    case SmtConstraint of
        {smt_constraint, _Type, Left, Op, Right, Location} ->
            #type_constraint{
                left = convert_smt_term_to_type(Left),
                op = Op,
                right = convert_smt_term_to_type(Right),
                location = Location
            };
        _ ->
            #type_constraint{
                left = unknown,
                op = '=',
                right = unknown,
                location = undefined
            }
    end.

convert_smt_term_to_type({smt_term, variable, Name, _}) ->
    #type_var{name = Name};
convert_smt_term_to_type({smt_term, constant, Value, _}) ->
    Value;
convert_smt_term_to_type(_) ->
    unknown.

%% Utility functions
substitute(Type, Subst) ->
    apply_substitution(Type, Subst).

normalize_type(Type) ->
    % Simplified normalization
    Type.

type_to_string(?TYPE_INT) ->
    "Int";
type_to_string(?TYPE_FLOAT) ->
    "Float";
type_to_string(?TYPE_STRING) ->
    "String";
type_to_string(?TYPE_BOOL) ->
    "Bool";
type_to_string(?TYPE_ATOM) ->
    "Atom";
type_to_string(#type_var{id = Id, name = undefined}) ->
    "T" ++ integer_to_list(Id);
type_to_string(#type_var{name = Name}) when Name =/= undefined ->
    atom_to_list(Name);
type_to_string({function_type, Params, Return}) ->
    ParamStrs = [type_to_string(P) || P <- Params],
    "(" ++ string:join(ParamStrs, ", ") ++ ") -> " ++ type_to_string(Return);
type_to_string({list_type, ElemType, undefined}) ->
    "[" ++ type_to_string(ElemType) ++ "]";
type_to_string({list_type, ElemType, _LenExpr}) ->
    % Simplified
    "[" ++ type_to_string(ElemType) ++ "]";
type_to_string({dependent_type, Name, _Params}) ->
    % Simplified
    atom_to_list(Name);
type_to_string(Type) ->
    io_lib:format("~p", [Type]).

%% Helper functions for dependent type pattern matching
extract_length_var(#type_param{value = {identifier_expr, VarName, _}}) ->
    VarName;
extract_length_var(_) ->
    unknown_length.

extract_type_param_value(#type_param{value = Value}) ->
    Value;
% Fallback for other formats
extract_type_param_value(Value) ->
    Value.

create_derived_length_var(#type_param{value = {identifier_expr, BaseVar, _}}, Suffix) ->
    list_to_atom(atom_to_list(BaseVar) ++ "_" ++ Suffix);
create_derived_length_var(_, Suffix) ->
    list_to_atom("derived_" ++ Suffix).

%% Type well-formedness checking
is_well_formed_type({primitive_type, Name}) when
    Name =:= 'Int' orelse Name =:= 'Float' orelse Name =:= 'String' orelse
        Name =:= 'Bool' orelse Name =:= 'Atom' orelse Name =:= 'Nat'
->
    true;
is_well_formed_type(#type_var{}) ->
    true;
is_well_formed_type({function_type, Params, Return}) ->
    lists:all(fun is_well_formed_type/1, Params) andalso is_well_formed_type(Return);
is_well_formed_type({list_type, ElemType, _LengthExpr}) ->
    is_well_formed_type(ElemType);
is_well_formed_type({dependent_type, Name, Params}) when is_atom(Name) ->
    lists:all(fun is_well_formed_type_param/1, Params);
is_well_formed_type({refined_type, BaseType, _Predicate}) ->
    is_well_formed_type(BaseType);
is_well_formed_type({phantom_type, Name}) when is_atom(Name) -> true;
is_well_formed_type({gadt_constructor, Name, Args, ReturnType}) when is_atom(Name) ->
    lists:all(fun is_well_formed_type/1, Args) andalso is_well_formed_type(ReturnType);
is_well_formed_type({proof_type, Name, BaseType, _Predicate}) when is_atom(Name) ->
    is_well_formed_type(BaseType);
is_well_formed_type({liquid_type, Name, BaseType, _Constraints, _Context}) when is_atom(Name) ->
    is_well_formed_type(BaseType);
is_well_formed_type({type_var, Id}) when is_integer(Id) ->
    % Type variable with ID
    true;
is_well_formed_type({type_var, {id, Id}}) when is_integer(Id) ->
    % Type variable with tuple-form ID
    true;
is_well_formed_type(_) ->
    false.

is_well_formed_type_param(#type_param{value = Value}) ->
    is_well_formed_type(Value) orelse is_well_formed_expr(Value) orelse is_type_var(Value);
is_well_formed_type_param(_) ->
    false.

%% Expression well-formedness (simplified)
is_well_formed_expr({literal_expr, Value, _Location}) when
    is_integer(Value) orelse is_float(Value) orelse is_atom(Value) orelse is_list(Value)
->
    true;
is_well_formed_expr({identifier_expr, Name, _Location}) when is_atom(Name) -> true;
is_well_formed_expr({binary_op_expr, Op, Left, Right, _Location}) when
    is_atom(Op)
->
    is_well_formed_expr(Left) andalso is_well_formed_expr(Right);
% Simplified for now
is_well_formed_expr(_) ->
    true.

%% Dependent constraint checking
check_dependent_constraint(Constraint, Value, _Env) ->
    case Constraint of
        Pred when is_function(Pred, 1) ->
            try
                case Pred(Value) of
                    true -> ok;
                    false -> {error, {constraint_violation, Constraint, Value}}
                end
            catch
                _:_ -> {error, {constraint_evaluation_failed, Constraint, Value}}
            end;
        _ ->
            {error, {unsupported_constraint, Constraint}}
    end.

%% Dependent type inference for specific patterns
infer_dependent_type(Expr, Env) ->
    case infer_type(Expr, Env) of
        {ok, Result} ->
            Type = element(2, Result),
            enhance_with_dependent_info(Type, Expr, Env);
        Error ->
            Error
    end.

enhance_with_dependent_info({list_type, ElemType, LenExpr}, {list_expr, Elements, _}, _Env) ->
    ActualLength = length(Elements),
    case LenExpr of
        {literal_expr, ActualLength, _} ->
            % Convert to dependent List type
            {ok,
                {dependent_type, 'List', [
                    #type_param{name = elem_type, value = ElemType},
                    #type_param{name = length, value = {literal_expr, ActualLength, undefined}}
                ]}};
        _ ->
            {ok, {list_type, ElemType, {literal_expr, ActualLength, undefined}}}
    end;
enhance_with_dependent_info(Type, _Expr, _Env) ->
    {ok, Type}.

%% Enhanced constraint solving functions
solve_length_constraint(Left, Right, Subst) ->
    % Try to solve length equations by evaluating expressions
    case {evaluate_length_expr(Left), evaluate_length_expr(Right)} of
        {{ok, N}, {ok, N}} when is_integer(N) ->
            % Same length, constraint satisfied
            {ok, Subst};
        {{ok, N1}, {ok, N2}} when is_integer(N1), is_integer(N2), N1 =/= N2 ->
            {error, {length_mismatch, N1, N2}};
        _ ->
            % Can't evaluate, use unification
            unify(Left, Right, Subst)
    end.

solve_subtype_constraint(Subtype, Op, Supertype, Subst) ->
    case Op of
        '<:' ->
            % Subtype <: Supertype
            check_subtype_relation(Subtype, Supertype, Subst);
        '>:' ->
            % Supertype >: Subtype (reversed)
            check_subtype_relation(Supertype, Subtype, Subst)
    end.

solve_element_constraint(Element, Collection, Subst) ->
    % For now, just ensure types are compatible
    case Collection of
        {list_type, ElemType, _} ->
            unify(Element, ElemType, Subst);
        {dependent_type, 'List', Params} ->
            case extract_list_params(Params) of
                {ok, ElemType, _} ->
                    unify(Element, ElemType, Subst);
                _ ->
                    {ok, Subst}
            end;
        _ ->
            {ok, Subst}
    end.

evaluate_length_expr({literal_expr, N, _}) when is_integer(N) ->
    {ok, N};
evaluate_length_expr({binary_op_expr, '+', Left, Right, _}) ->
    case {evaluate_length_expr(Left), evaluate_length_expr(Right)} of
        {{ok, N1}, {ok, N2}} when is_integer(N1), is_integer(N2) ->
            {ok, N1 + N2};
        _ ->
            {error, cannot_evaluate}
    end;
evaluate_length_expr({binary_op_expr, '-', Left, Right, _}) ->
    case {evaluate_length_expr(Left), evaluate_length_expr(Right)} of
        {{ok, N1}, {ok, N2}} when is_integer(N1), is_integer(N2) ->
            {ok, N1 - N2};
        _ ->
            {error, cannot_evaluate}
    end;
evaluate_length_expr(_) ->
    {error, cannot_evaluate}.

check_subtype_relation(Subtype, Supertype, Subst) ->
    % Simplified subtyping rules
    case {Subtype, Supertype} of
        {Same, Same} ->
            {ok, Subst};
        {{refined_type, BaseType, _}, SuperType} ->
            % Refined type is subtype of its base type
            check_subtype_relation(BaseType, SuperType, Subst);
        {{dependent_type, 'List', Params1}, {dependent_type, 'List', Params2}} ->
            % Covariant in element type if lengths match
            case {extract_list_params(Params1), extract_list_params(Params2)} of
                {{ok, Elem1, Len1}, {ok, Elem2, Len2}} ->
                    case solve_length_constraint(Len1, Len2, Subst) of
                        {ok, Subst1} ->
                            check_subtype_relation(Elem1, Elem2, Subst1);
                        Error ->
                            Error
                    end;
                _ ->
                    {ok, Subst}
            end;
        _ ->
            % Try unification as fallback
            case unify(Subtype, Supertype, Subst) of
                {ok, NewSubst} -> {ok, NewSubst};
                {error, _} -> {error, {subtype_violation, Subtype, Supertype}}
            end
    end.

%% Check dimension consistency for function types involving dependent types
check_dimension_consistency({function_type, Params, _ReturnType}) ->
    case check_vector_operation_validity(Params) of
        ok -> ok;
        Error -> Error
    end;
check_dimension_consistency(_Type) ->
    ok.

check_vector_operation_validity([Param1, Param2]) ->
    case {extract_vector_dimensions(Param1), extract_vector_dimensions(Param2)} of
        {{ok, _ElemType1, Dim1}, {ok, _ElemType2, Dim2}} when
            is_integer(Dim1), is_integer(Dim2), Dim1 =/= Dim2
        ->
            {error, {dimension_mismatch, Dim1, Dim2}};
        {{ok, _, _}, {ok, _, _}} ->
            ok;
        _ ->
            % Strict checking for any Vector types - reject if we can't verify dimensions match
            case is_vector_function_type(Param1, Param2) of
                true ->
                    % For Vector types, we need to be able to verify dimension compatibility
                    case can_verify_vector_dimensions_match(Param1, Param2) of
                        true -> ok;
                        false -> {error, {unverifiable_vector_dimensions, Param1, Param2}}
                    end;
                false ->
                    ok
            end
    end;
check_vector_operation_validity(_Params) ->
    ok.

is_vector_function_type({dependent_type, 'Vector', _}, {dependent_type, 'Vector', _}) -> true;
is_vector_function_type(_, _) -> false.

can_verify_vector_dimensions_match(Vec1, Vec2) ->
    case {extract_vector_dimensions(Vec1), extract_vector_dimensions(Vec2)} of
        {{ok, _, Dim1}, {ok, _, Dim2}} when is_integer(Dim1), is_integer(Dim2) ->
            % Can verify and they match
            Dim1 =:= Dim2;
        {{ok, _, Dim1}, {ok, _, Dim2}} when is_integer(Dim1), is_integer(Dim2) ->
            % Can verify but they don't match
            false;
        _ ->
            % Try to extract and compare length expressions directly
            case {extract_vector_params(Vec1), extract_vector_params(Vec2)} of
                {{ok, _, Len1}, {ok, _, Len2}} ->
                    % Structural comparison
                    expr_equal(Len1, Len2);
                _ ->
                    % Can't verify - assume they don't match for safety
                    false
            end
    end.

extract_vector_dimensions({dependent_type, 'Vector', Params}) ->
    case extract_vector_params(Params) of
        {ok, ElemType, LengthExpr} ->
            case evaluate_length_expr(LengthExpr) of
                {ok, N} when is_integer(N) ->
                    {ok, ElemType, N};
                _ ->
                    {ok, ElemType, unknown}
            end;
        _ ->
            {error, invalid_vector}
    end;
extract_vector_dimensions(_Type) ->
    {error, not_a_vector}.

%% Enhanced occurs checking for dependent types
check_dependent_occurs(#type_var{id = Id}, {dependent_type, _Name, Params}) ->
    lists:any(
        fun(Param) ->
            case Param of
                #type_param{value = Value} ->
                    occurs_check_impl(Id, Value) orelse
                        case Value of
                            % Direct match
                            #type_var{id = Id} -> true;
                            _ -> false
                        end;
                _ ->
                    % Handle raw parameters (no type_param wrapper)
                    occurs_check_impl(Id, Param) orelse
                        case Param of
                            #type_var{id = Id} -> true;
                            _ -> false
                        end
            end
        end,
        Params
    );
check_dependent_occurs(#type_var{id = Id}, {list_type, ElemType, _LenExpr}) ->
    occurs_check_impl(Id, ElemType);
check_dependent_occurs(Var, Type) ->
    % Fallback to standard occurs check if no specific dependent type handling
    occurs_check(Var, Type).

%% ===== COMPLEX DEPENDENT TYPE CONSTRAINT SOLVING =====

%% Solve implication constraints: Left => Right
solve_implication_constraint(Left, Right, Subst) ->
    % For type implication A => B, if A is true/satisfied, then B must be true/satisfied
    case evaluate_type_predicate(Left, Subst) of
        {ok, true} ->
            % Left is satisfied, Right must also be satisfied
            case evaluate_type_predicate(Right, Subst) of
                {ok, true} ->
                    {ok, Subst};
                {ok, false} ->
                    {error, {implication_violated, Left, Right}};
                {error, _} ->
                    % Can't evaluate Right, try to make it true via unification
                    attempt_satisfy_predicate(Right, Subst)
            end;
        {ok, false} ->
            % Left is not satisfied, implication is vacuously true
            {ok, Subst};
        {error, _} ->
            % Can't evaluate Left, treat as conditional constraint
            add_conditional_constraint(Left, Right, implies, Subst)
    end.

%% Solve equivalence constraints: Left <=> Right
solve_equivalence_constraint(Left, Right, Subst) ->
    case {evaluate_type_predicate(Left, Subst), evaluate_type_predicate(Right, Subst)} of
        {{ok, LeftVal}, {ok, RightVal}} ->
            case LeftVal =:= RightVal of
                true -> {ok, Subst};
                false -> {error, {equivalence_violated, Left, Right, LeftVal, RightVal}}
            end;
        _ ->
            % Try to unify Left and Right if possible
            case unify(Left, Right, Subst) of
                {ok, NewSubst} ->
                    {ok, NewSubst};
                {error, _} ->
                    % Can't unify, add as conditional constraint
                    add_conditional_constraint(Left, Right, equivalent, Subst)
            end
    end.

%% Solve bounds constraints for dependent types
solve_bounds_constraint(Type, Bounds, Subst) ->
    case Bounds of
        {bounds, Lower, Upper} ->
            LowerConstraint = #type_constraint{
                left = Lower, op = '<:', right = Type, location = undefined
            },
            UpperConstraint = #type_constraint{
                left = Type, op = '<:', right = Upper, location = undefined
            },
            case solve_constraint(LowerConstraint, Subst) of
                {ok, Subst1} ->
                    solve_constraint(UpperConstraint, Subst1);
                Error ->
                    Error
            end;
        {range, Min, Max} when is_integer(Min), is_integer(Max) ->
            % Handle integer range bounds for dependent types
            case Type of
                {refined_type, BaseType, _} ->
                    check_integer_bounds(BaseType, Min, Max, Subst);
                _ ->
                    check_integer_bounds(Type, Min, Max, Subst)
            end;
        _ ->
            {error, {invalid_bounds_constraint, Bounds}}
    end.

%% Solve type invariant constraints
solve_invariant_constraint(Type, InvariantSpec, Subst) ->
    case InvariantSpec of
        {invariant, Predicate} when is_function(Predicate, 1) ->
            % Apply invariant predicate to the type
            case apply_type_invariant(Type, Predicate, Subst) of
                {ok, true} -> {ok, Subst};
                {ok, false} -> {error, {invariant_violated, Type, InvariantSpec}};
                {error, Reason} -> {error, {invariant_evaluation_failed, Type, Reason}}
            end;
        {structural_invariant, Properties} ->
            % Check structural properties of the type
            check_structural_invariants(Type, Properties, Subst);
        _ ->
            {error, {invalid_invariant_constraint, InvariantSpec}}
    end.

%% Solve variance constraints for type constructors
solve_variance_constraint(TypeConstructor, ParameterType, Variance, Subst) ->
    case validate_variance(TypeConstructor, ParameterType, Variance) of
        ok ->
            {ok, Subst};
        {error, Reason} ->
            {error, {variance_violation, TypeConstructor, ParameterType, Variance, Reason}}
    end.

%% Helper functions for complex constraint solving

evaluate_type_predicate({refined_type, _BaseType, Predicate}, _Subst) when
    is_function(Predicate, 1)
->
    % For refined types, the predicate itself indicates satisfaction
    {ok, true};
evaluate_type_predicate({dependent_type, Name, Params}, Subst) ->
    % Check if dependent type parameters satisfy their constraints
    case Name of
        'Vector' -> evaluate_vector_constraints(Params, Subst);
        'Matrix' -> evaluate_matrix_constraints(Params, Subst);
        'List' -> evaluate_list_constraints(Params, Subst);
        _ -> {error, {unknown_dependent_type, Name}}
    end;
evaluate_type_predicate(Type, _Subst) ->
    % For primitive types, assume they are always satisfied
    case Type of
        {primitive_type, _} -> {ok, true};
        #type_var{} -> {error, cannot_evaluate_type_variable};
        _ -> {error, {unsupported_predicate_type, Type}}
    end.

attempt_satisfy_predicate(Predicate, Subst) ->
    % Try to find a substitution that makes the predicate true
    case Predicate of
        {refined_type, BaseType, Constraint} ->
            % For refined types, check if we can satisfy the constraint
            case solve_refinement_constraint(BaseType, Constraint, Subst) of
                {ok, NewSubst} -> {ok, NewSubst};
                Error -> Error
            end;
        _ ->
            % For other predicates, assume they can be satisfied
            {ok, Subst}
    end.

add_conditional_constraint(_Left, _Right, _Relation, Subst) ->
    % Store conditional constraint for later resolution
    % For now, accept the constraint and continue
    {ok, Subst}.

check_integer_bounds(Type, Min, Max, Subst) when is_integer(Min), is_integer(Max) ->
    case Type of
        % Integers can potentially satisfy bounds
        ?TYPE_INT ->
            {ok, Subst};
        {refined_type, ?TYPE_INT, Predicate} when is_function(Predicate, 1) ->
            % Check if the refinement predicate is compatible with bounds
            case test_bounds_compatibility(Predicate, Min, Max) of
                true -> {ok, Subst};
                false -> {error, {bounds_incompatible_with_refinement, Min, Max}}
            end;
        _ ->
            {error, {bounds_not_applicable, Type, Min, Max}}
    end.

apply_type_invariant(Type, Invariant, _Subst) when is_function(Invariant, 1) ->
    try
        Result = Invariant(Type),
        {ok, Result}
    catch
        _:Reason -> {error, {invariant_application_failed, Reason}}
    end.

check_structural_invariants(Type, Properties, Subst) ->
    case Type of
        {dependent_type, Name, Params} ->
            check_dependent_type_properties(Name, Params, Properties, Subst);
        {function_type, ParamTypes, ReturnType} ->
            check_function_type_properties(ParamTypes, ReturnType, Properties, Subst);
        _ ->
            % No structural invariants for primitive types
            {ok, Subst}
    end.

validate_variance(TypeConstructor, ParameterType, Variance) ->
    case {TypeConstructor, Variance} of
        % List is covariant in its element type
        {{dependent_type, 'List', _}, covariant} -> ok;
        % Function types are contravariant in parameters, covariant in return
        {{function_type, _, _}, contravariant} -> ok;
        {{function_type, _, _}, covariant} -> ok;
        % Vector is invariant in its element type (due to mutability)
        {{dependent_type, 'Vector', _}, invariant} -> ok;
        _ -> {error, {invalid_variance, TypeConstructor, ParameterType, Variance}}
    end.

evaluate_vector_constraints(Params, _Subst) ->
    case extract_vector_params(Params) of
        {ok, _ElemType, LengthExpr} ->
            case evaluate_length_expr(LengthExpr) of
                {ok, N} when is_integer(N), N >= 0 -> {ok, true};
                {ok, N} when is_integer(N), N < 0 -> {ok, false};
                _ -> {error, cannot_evaluate_length}
            end;
        _ ->
            {error, invalid_vector_params}
    end.

evaluate_matrix_constraints(Params, _Subst) ->
    % Matrix constraints: rows > 0, cols > 0
    case length(Params) of
        % Assume [rows, cols, elem_type] format
        N when N >= 3 ->
            case Params of
                [RowsParam, ColsParam, _ElemParam] ->
                    case {extract_integer_param(RowsParam), extract_integer_param(ColsParam)} of
                        {{ok, Rows}, {ok, Cols}} when Rows > 0, Cols > 0 -> {ok, true};
                        {{ok, Rows}, {ok, Cols}} when Rows =< 0; Cols =< 0 -> {ok, false};
                        _ -> {error, cannot_evaluate_matrix_dimensions}
                    end;
                _ ->
                    {error, invalid_matrix_params}
            end;
        _ ->
            {error, insufficient_matrix_params}
    end.

evaluate_list_constraints(Params, _Subst) ->
    case extract_list_params(Params) of
        {ok, _ElemType, LengthExpr} ->
            case evaluate_length_expr(LengthExpr) of
                {ok, N} when is_integer(N), N >= 0 -> {ok, true};
                {ok, N} when is_integer(N), N < 0 -> {ok, false};
                % Unknown length is acceptable for lists
                {error, _} -> {ok, true}
            end;
        % Lists without explicit length are acceptable
        _ ->
            {ok, true}
    end.

solve_refinement_constraint(BaseType, Constraint, Subst) ->
    % Try to solve the refinement constraint by strengthening the base type
    case BaseType of
        #type_var{id = Id} ->
            % Create a refined type with the constraint
            RefinedType = {refined_type, BaseType, Constraint},
            NewSubst = maps:put(Id, RefinedType, Subst),
            {ok, NewSubst};
        _ ->
            % For concrete types, check if constraint is satisfiable
            case Constraint of
                Fun when is_function(Fun, 1) ->
                    % Assume constraint is satisfiable for now
                    {ok, Subst};
                _ ->
                    {ok, Subst}
            end
    end.

check_dependent_type_properties(Name, Params, Properties, Subst) ->
    case {Name, Properties} of
        {'Vector', [{length, positive}]} ->
            case extract_vector_params(Params) of
                {ok, _, LengthExpr} ->
                    case evaluate_length_expr(LengthExpr) of
                        {ok, N} when N > 0 -> {ok, Subst};
                        {ok, N} when N =< 0 -> {error, {property_violation, length, positive, N}};
                        % Can't evaluate, assume satisfied
                        _ -> {ok, Subst}
                    end;
                _ ->
                    {error, invalid_vector_structure}
            end;
        {'List', [{length, non_negative}]} ->
            case extract_list_params(Params) of
                {ok, _, LengthExpr} ->
                    case evaluate_length_expr(LengthExpr) of
                        {ok, N} when N >= 0 -> {ok, Subst};
                        {ok, N} when N < 0 ->
                            {error, {property_violation, length, non_negative, N}};
                        % Can't evaluate, assume satisfied
                        _ ->
                            {ok, Subst}
                    end;
                % Lists without explicit length satisfy this
                _ ->
                    {ok, Subst}
            end;
        % Unknown properties are assumed to be satisfied
        _ ->
            {ok, Subst}
    end.

check_function_type_properties(ParamTypes, _ReturnType, Properties, Subst) ->
    case Properties of
        [{arity, ExpectedArity}] ->
            ActualArity = length(ParamTypes),
            if
                ActualArity =:= ExpectedArity -> {ok, Subst};
                true -> {error, {property_violation, arity, ExpectedArity, ActualArity}}
            end;
        [{pure}] ->
            % For now, assume all functions can be pure
            {ok, Subst};
        % Other properties are assumed satisfied
        _ ->
            {ok, Subst}
    end.

test_bounds_compatibility(Predicate, Min, Max) when is_function(Predicate, 1) ->
    try
        % Test the predicate with values at the bounds
        LowerOk = Predicate(Min),
        UpperOk = Predicate(Max),
        MiddleOk =
            case Min < Max of
                true -> Predicate((Min + Max) div 2);
                false -> true
            end,
        LowerOk andalso UpperOk andalso MiddleOk
    catch
        % If predicate fails, assume incompatible
        _:_ -> false
    end.

extract_integer_param(#type_param{value = {literal_expr, N, _}}) when is_integer(N) ->
    {ok, N};
extract_integer_param(#type_param{value = N}) when is_integer(N) ->
    {ok, N};
extract_integer_param(_) ->
    {error, not_integer}.

%% ===== ENHANCED TYPE INFERENCE =====

%% Enhanced type inference with better algorithms and constraint propagation
enhanced_infer_type(Expr, Env) ->
    enhanced_infer_type(Expr, Env, []).

enhanced_infer_type(Expr, Env, Constraints) ->
    StartTime = erlang:timestamp(),

    % Step 1: Try bidirectional inference first
    case bidirectional_infer(Expr, undefined, Env) of
        {ok, Type, BidirConstraints, Steps} ->
            AllConstraints = Constraints ++ BidirConstraints,

            % Step 2: Apply constraint propagation
            case constraint_propagation(AllConstraints, #{}) of
                {ok, PropagatedConstraints, Subst} ->
                    % Step 3: Solve constraints with enhanced solver
                    case enhanced_constraint_solving(PropagatedConstraints, Subst) of
                        {ok, FinalSubst, Confidence} ->
                            FinalType = apply_substitution(Type, FinalSubst),

                            % Step 4: Generate alternatives if confidence is low
                            Alternatives =
                                case Confidence < 0.8 of
                                    true -> generate_type_alternatives(Expr, FinalType, Env);
                                    false -> []
                                end,

                            EndTime = erlang:timestamp(),
                            Duration = timer:now_diff(EndTime, StartTime),

                            {ok, #enhanced_inference_result{
                                type = FinalType,
                                constraints = PropagatedConstraints,
                                substitution = FinalSubst,
                                confidence = Confidence,
                                alternatives = Alternatives,
                                justification = Steps,
                                context_info = #{duration => Duration, method => bidirectional}
                            }};
                        {error, Reason} ->
                            {error, {enhanced_solving_failed, Reason}}
                    end;
                {error, PropReason} ->
                    {error, {constraint_propagation_failed, PropReason}}
            end;
        {error, _} ->
            % Fall back to traditional inference with enhancements
            enhanced_traditional_inference(Expr, Env, Constraints)
    end.

%% Bidirectional type inference
bidirectional_infer(Expr, ExpectedType, Env) ->
    Steps = [{inference_step, start_bidirectional, {Expr, ExpectedType}, undefined, undefined}],
    bidirectional_infer_impl(Expr, ExpectedType, Env, [], Steps).

bidirectional_infer_impl({literal_expr, Value, Location}, ExpectedType, _Env, Constraints, Steps) ->
    InferredType = infer_literal_type(Value),
    Step = {inference_step, literal_inference, Value, InferredType, Location},

    case ExpectedType of
        undefined ->
            {ok, InferredType, Constraints, [Step | Steps]};
        Expected ->
            % Check if inferred type is compatible with expected
            case unify(InferredType, Expected) of
                {ok, _} ->
                    CompatStep =
                        {inference_step, type_check, {InferredType, Expected}, ok, Location},
                    {ok, Expected, Constraints, [CompatStep, Step | Steps]};
                {error, Reason} ->
                    {error, {type_mismatch_bidirectional, InferredType, Expected, Reason}}
            end
    end;
bidirectional_infer_impl({identifier_expr, Name, Location}, ExpectedType, Env, Constraints, Steps) ->
    case lookup_env(Env, Name) of
        undefined ->
            % Create fresh type variable if not found
            FreshVar = new_type_var(Name),
            _NewEnv = extend_env(Env, Name, FreshVar),
            Step = {inference_step, fresh_variable, Name, FreshVar, Location},

            case ExpectedType of
                undefined ->
                    {ok, FreshVar, Constraints, [Step | Steps]};
                Expected ->
                    % Unify fresh variable with expected type
                    UnifyConstraint = #type_constraint{
                        left = FreshVar, op = '=', right = Expected, location = Location
                    },
                    UnifyStep =
                        {inference_step, unify_expected, {FreshVar, Expected}, UnifyConstraint,
                            Location},
                    {ok, Expected, [UnifyConstraint | Constraints], [UnifyStep, Step | Steps]}
            end;
        VarType ->
            Step = {inference_step, variable_lookup, Name, VarType, Location},

            case ExpectedType of
                undefined ->
                    {ok, VarType, Constraints, [Step | Steps]};
                Expected ->
                    case unify(VarType, Expected) of
                        {ok, _} ->
                            CompatStep =
                                {inference_step, type_check, {VarType, Expected}, ok, Location},
                            {ok, Expected, Constraints, [CompatStep, Step | Steps]};
                        {error, Reason} ->
                            {error, {identifier_type_mismatch, Name, VarType, Expected, Reason}}
                    end
            end
    end;
bidirectional_infer_impl(
    {function_call_expr, Function, Args, Location}, ExpectedType, Env, Constraints, Steps
) ->
    % Enhanced function call inference with better argument handling
    case bidirectional_infer_impl(Function, undefined, Env, Constraints, Steps) of
        {ok, FuncType, FuncConstraints, FuncSteps} ->
            case
                infer_function_call_enhanced(Function, FuncType, Args, ExpectedType, Env, Location)
            of
                {ok, ResultType, CallConstraints, CallSteps} ->
                    AllConstraints = FuncConstraints ++ CallConstraints,
                    AllSteps = CallSteps ++ FuncSteps,
                    {ok, ResultType, AllConstraints, AllSteps};
                Error ->
                    Error
            end;
        Error ->
            Error
    end;
bidirectional_infer_impl(
    {if_expr, Condition, ThenBranch, ElseBranch, Location}, ExpectedType, Env, Constraints, Steps
) ->
    % Enhanced if expression inference
    CondStep = {inference_step, condition_check, Condition, {primitive_type, 'Bool'}, Location},

    case
        bidirectional_infer_impl(Condition, {primitive_type, 'Bool'}, Env, Constraints, [
            CondStep | Steps
        ])
    of
        {ok, _CondType, CondConstraints, CondSteps} ->
            % Infer both branches with the same expected type
            case
                bidirectional_infer_impl(ThenBranch, ExpectedType, Env, CondConstraints, CondSteps)
            of
                {ok, ThenType, ThenConstraints, ThenSteps} ->
                    case
                        bidirectional_infer_impl(
                            ElseBranch, ExpectedType, Env, ThenConstraints, ThenSteps
                        )
                    of
                        {ok, ElseType, ElseConstraints, ElseSteps} ->
                            % Unify branch types or use expected type if available
                            case ExpectedType of
                                undefined ->
                                    % Unify the two branch types
                                    case unify(ThenType, ElseType) of
                                        {ok, _} ->
                                            UnifyStep =
                                                {inference_step, branch_unification,
                                                    {ThenType, ElseType}, ThenType, Location},
                                            {ok, ThenType, ElseConstraints, [UnifyStep | ElseSteps]};
                                        {error, Reason} ->
                                            {error,
                                                {branch_type_mismatch, ThenType, ElseType, Reason}}
                                    end;
                                Expected ->
                                    % Both branches should already match expected type
                                    {ok, Expected, ElseConstraints, ElseSteps}
                            end;
                        Error ->
                            Error
                    end;
                Error ->
                    Error
            end;
        Error ->
            Error
    end;
bidirectional_infer_impl({list_expr, Elements, Location}, ExpectedType, Env, Constraints, Steps) ->
    % Enhanced list inference with element type propagation
    case ExpectedType of
        {list_type, ExpectedElemType, ExpectedLength} ->
            % Propagate expected element type to all elements
            case
                infer_list_elements_bidirectional(
                    Elements, ExpectedElemType, Env, Constraints, Location
                )
            of
                {ok, ElemConstraints, ElemSteps} ->
                    Length = length(Elements),
                    LengthExpr = {literal_expr, Length, Location},

                    % Check length compatibility if specified
                    LengthConstraints =
                        case ExpectedLength of
                            undefined ->
                                ElemConstraints;
                            _ ->
                                LenConstraint = #type_constraint{
                                    left = LengthExpr,
                                    op = '=',
                                    right = ExpectedLength,
                                    location = Location
                                },
                                [LenConstraint | ElemConstraints]
                        end,

                    ListStep =
                        {inference_step, list_construction, {Elements, Length}, ExpectedType,
                            Location},
                    AllSteps = [ListStep | ElemSteps ++ Steps],
                    {ok, ExpectedType, LengthConstraints, AllSteps};
                Error ->
                    Error
            end;
        {dependent_type, 'List', Params} ->
            % Handle dependent list types
            case extract_list_params(Params) of
                {ok, ExpectedElemType, ExpectedLength} ->
                    bidirectional_infer_impl(
                        {list_expr, Elements, Location},
                        {list_type, ExpectedElemType, ExpectedLength},
                        Env,
                        Constraints,
                        Steps
                    );
                Error ->
                    Error
            end;
        undefined ->
            % Infer element type from first element
            case Elements of
                [] ->
                    ElemType = new_type_var(),
                    ListType = {list_type, ElemType, {literal_expr, 0, Location}},
                    EmptyStep = {inference_step, empty_list, [], ListType, Location},
                    {ok, ListType, Constraints, [EmptyStep | Steps]};
                [FirstElem | RestElems] ->
                    case bidirectional_infer_impl(FirstElem, undefined, Env, Constraints, Steps) of
                        {ok, ElemType, ElemConstraints, ElemSteps} ->
                            case
                                infer_list_elements_bidirectional(
                                    RestElems, ElemType, Env, ElemConstraints, Location
                                )
                            of
                                {ok, AllConstraints, AllSteps} ->
                                    Length = length(Elements),
                                    ListType =
                                        {list_type, ElemType, {literal_expr, Length, Location}},
                                    ListStep =
                                        {inference_step, list_construction, {Elements, Length},
                                            ListType, Location},
                                    {ok, ListType, AllConstraints, [
                                        ListStep | AllSteps ++ ElemSteps
                                    ]};
                                Error ->
                                    Error
                            end;
                        Error ->
                            Error
                    end
            end;
        _ ->
            {error, {incompatible_expected_type_for_list, ExpectedType}}
    end;
bidirectional_infer_impl(Expr, ExpectedType, Env, Constraints, Steps) ->
    % Fall back to traditional inference for other expression types
    case infer_expr(Expr, Env) of
        {ok, InferredType, InferConstraints} ->
            FallbackStep = {inference_step, fallback_inference, Expr, InferredType, undefined},
            AllConstraints = Constraints ++ InferConstraints,
            AllSteps = [FallbackStep | Steps],

            case ExpectedType of
                undefined ->
                    {ok, InferredType, AllConstraints, AllSteps};
                Expected ->
                    case unify(InferredType, Expected) of
                        {ok, _} ->
                            CheckStep =
                                {inference_step, type_check, {InferredType, Expected}, ok,
                                    undefined},
                            {ok, Expected, AllConstraints, [CheckStep | AllSteps]};
                        {error, Reason} ->
                            {error,
                                {bidirectional_unification_failed, InferredType, Expected, Reason}}
                    end
            end;
        Error ->
            Error
    end.

%% Enhanced traditional inference with improved algorithms
enhanced_traditional_inference(Expr, Env, Constraints) ->
    case infer_expr(Expr, Env) of
        {ok, Type, InferConstraints} ->
            AllConstraints = Constraints ++ InferConstraints,

            % Apply local type inference improvements
            case local_type_inference(Expr, Type, Env) of
                {ok, ImprovedType, LocalConstraints} ->
                    FinalConstraints = AllConstraints ++ LocalConstraints,

                    case enhanced_constraint_solving(FinalConstraints, #{}) of
                        {ok, Subst, Confidence} ->
                            FinalType = apply_substitution(ImprovedType, Subst),

                            {ok, #enhanced_inference_result{
                                type = FinalType,
                                constraints = FinalConstraints,
                                substitution = Subst,
                                confidence = Confidence,
                                alternatives = [],
                                justification = [
                                    {inference_step, traditional_enhanced, Expr, FinalType,
                                        undefined}
                                ],
                                context_info = #{method => traditional_enhanced}
                            }};
                        {error, Reason} ->
                            {error, {enhanced_solving_failed, Reason}}
                    end;
                {error, Reason} ->
                    {error, {local_inference_failed, Reason}}
            end;
        Error ->
            Error
    end.

%% Constraint propagation with dependency analysis
constraint_propagation(Constraints, InitialSubst) ->
    % Build constraint dependency graph
    DepGraph = build_constraint_dependencies(Constraints),

    % Topological sort for constraint solving order
    case topological_sort_constraints(DepGraph) of
        {ok, SortedConstraints} ->
            % Propagate constraints in dependency order
            propagate_constraints_ordered(SortedConstraints, InitialSubst, []);
        {error, _Reason} ->
            % Fall back to simple propagation if cycle detected
            simple_constraint_propagation(Constraints, InitialSubst)
    end.

simple_constraint_propagation(Constraints, Subst) ->
    % Max 3 iterations
    case propagate_constraints_simple(Constraints, Subst, [], 3) of
        {ok, FinalConstraints, FinalSubst} ->
            {ok, FinalConstraints, FinalSubst};
        {error, Reason} ->
            {error, Reason}
    end.

propagate_constraints_simple(Constraints, Subst, AccConstraints, 0) ->
    % Max iterations reached
    {ok, AccConstraints ++ Constraints, Subst};
propagate_constraints_simple([], Subst, AccConstraints, _Iterations) ->
    {ok, lists:reverse(AccConstraints), Subst};
propagate_constraints_simple([C | Rest], Subst, AccConstraints, Iterations) ->
    case propagate_single_constraint(C, Subst) of
        {ok, NewConstraints, NewSubst} ->
            % Constraint was propagated, continue with new constraints
            AllConstraints = NewConstraints ++ Rest,
            propagate_constraints_simple(AllConstraints, NewSubst, AccConstraints, Iterations - 1);
        {unchanged, FinalSubst} ->
            % Constraint unchanged, add to accumulator
            propagate_constraints_simple(Rest, FinalSubst, [C | AccConstraints], Iterations);
        {error, Reason} ->
            {error, Reason}
    end.

propagate_single_constraint(#type_constraint{left = Left, op = '=', right = Right} = C, Subst) ->
    % Apply current substitution to constraint
    NewLeft = apply_substitution(Left, Subst),
    NewRight = apply_substitution(Right, Subst),

    case {NewLeft, NewRight} of
        {Same, Same} ->
            % Constraint is satisfied, remove it
            {ok, [], Subst};
        {#type_var{id = Id}, Type} when not is_record(Type, type_var) ->
            % Unify type variable with concrete type
            case occurs_check(NewLeft, Type) of
                false ->
                    NewSubst = maps:put(Id, Type, Subst),
                    {ok, [], NewSubst};
                true ->
                    {error, {occurs_check_in_propagation, NewLeft, Type}}
            end;
        {Type, #type_var{id = Id}} when not is_record(Type, type_var) ->
            % Symmetric case
            case occurs_check(NewRight, Type) of
                false ->
                    NewSubst = maps:put(Id, Type, Subst),
                    {ok, [], NewSubst};
                true ->
                    {error, {occurs_check_in_propagation, NewRight, Type}}
            end;
        _ ->
            % Constraint cannot be simplified further
            if
                NewLeft =/= Left orelse NewRight =/= Right ->
                    % Constraint was modified by substitution
                    _UpdatedC = C#type_constraint{left = NewLeft, right = NewRight},
                    {unchanged, Subst};
                true ->
                    {unchanged, Subst}
            end
    end;
propagate_single_constraint(_C, Subst) ->
    % For non-equality constraints, just apply substitution
    {unchanged, Subst}.

%% Enhanced constraint solving with confidence scoring
enhanced_constraint_solving(Constraints, InitialSubst) ->
    case solve_constraints_with_scoring(Constraints, InitialSubst, 0, length(Constraints)) of
        {ok, FinalSubst, SolvedCount} ->
            % Calculate confidence based on solved constraints ratio
            Confidence =
                case length(Constraints) of
                    0 -> 1.0;
                    Total -> float(SolvedCount) / float(Total)
                end,
            {ok, FinalSubst, Confidence};
        Error ->
            Error
    end.

solve_constraints_with_scoring([], Subst, SolvedCount, _Total) ->
    {ok, Subst, SolvedCount};
solve_constraints_with_scoring([C | Rest], Subst, SolvedCount, Total) ->
    case solve_constraint(C, Subst) of
        {ok, NewSubst} ->
            solve_constraints_with_scoring(Rest, NewSubst, SolvedCount + 1, Total);
        {error, _Reason} ->
            % Skip unsolvable constraint but continue with others
            solve_constraints_with_scoring(Rest, Subst, SolvedCount, Total)
    end.

%% Local type inference for specific patterns
local_type_inference(Expr, InferredType, Env) ->
    case Expr of
        {list_expr, Elements, Location} ->
            improve_list_type_inference(Elements, InferredType, Env, Location);
        {function_call_expr, Function, Args, Location} ->
            improve_function_call_inference(Function, Args, InferredType, Env, Location);
        _ ->
            {ok, InferredType, []}
    end.

improve_list_type_inference(Elements, {list_type, ElemType, LenExpr}, Env, _Location) ->
    % Try to infer more specific element type
    case Elements of
        [] ->
            {ok, {list_type, ElemType, LenExpr}, []};
        _ ->
            % Analyze elements for patterns
            case analyze_list_element_patterns(Elements, Env) of
                {ok, MoreSpecificElemType} ->
                    case unify(ElemType, MoreSpecificElemType) of
                        {ok, _} ->
                            ImprovedType = {list_type, MoreSpecificElemType, LenExpr},
                            {ok, ImprovedType, []};
                        {error, _} ->
                            % Keep original type if unification fails
                            {ok, {list_type, ElemType, LenExpr}, []}
                    end;
                {error, _} ->
                    {ok, {list_type, ElemType, LenExpr}, []}
            end
    end;
improve_list_type_inference(_Elements, InferredType, _Env, _Location) ->
    {ok, InferredType, []}.

improve_function_call_inference(_Function, _Args, InferredType, _Env, _Location) ->
    % For now, just return the inferred type
    % Could be enhanced with return type analysis
    {ok, InferredType, []}.

%% Type alternatives generation
generate_type_alternatives(Expr, InferredType, Env) ->
    case Expr of
        {literal_expr, Value, _} ->
            generate_literal_alternatives(Value, InferredType);
        {list_expr, Elements, _} ->
            generate_list_alternatives(Elements, InferredType, Env);
        _ ->
            []
    end.

generate_literal_alternatives(Value, _InferredType) when is_integer(Value) ->
    % Integer could also be Float in some contexts
    [{primitive_type, 'Float'}, {refined_type, {primitive_type, 'Int'}, fun(X) -> X >= 0 end}];
generate_literal_alternatives(_Value, _InferredType) ->
    [].

generate_list_alternatives(Elements, {list_type, ElemType, _}, Env) ->
    % Could be Vector if elements are numeric and length is known
    case {analyze_list_for_vector_potential(Elements, Env), ElemType} of
        {true, NumericType} when
            NumericType =:= {primitive_type, 'Int'};
            NumericType =:= {primitive_type, 'Float'}
        ->
            Length = length(Elements),
            VectorType =
                {dependent_type, 'Vector', [
                    #type_param{name = elem_type, value = NumericType},
                    #type_param{name = length, value = {literal_expr, Length, undefined}}
                ]},
            [VectorType];
        _ ->
            []
    end;
generate_list_alternatives(_Elements, _InferredType, _Env) ->
    [].

%% Inference with alternatives
infer_with_alternatives(Expr, ExpectedType, Env) ->
    case enhanced_infer_type(Expr, Env) of
        {ok, Result} ->
            case Result#enhanced_inference_result.confidence < 0.7 of
                true ->
                    % Try alternative inference strategies
                    Alternatives = try_alternative_strategies(Expr, ExpectedType, Env),
                    UpdatedResult = Result#enhanced_inference_result{alternatives = Alternatives},
                    {ok, UpdatedResult};
                false ->
                    {ok, Result}
            end;
        Error ->
            Error
    end.

try_alternative_strategies(Expr, ExpectedType, Env) ->
    Strategies = [structural_typing, duck_typing, gradual_typing],
    try_strategies(Strategies, Expr, ExpectedType, Env, []).

try_strategies([], _Expr, _ExpectedType, _Env, Acc) ->
    lists:reverse(Acc);
try_strategies([Strategy | Rest], Expr, ExpectedType, Env, Acc) ->
    case apply_strategy(Strategy, Expr, ExpectedType, Env) of
        {ok, AlternativeType} ->
            try_strategies(Rest, Expr, ExpectedType, Env, [AlternativeType | Acc]);
        {error, _} ->
            try_strategies(Rest, Expr, ExpectedType, Env, Acc)
    end.

apply_strategy(structural_typing, Expr, _ExpectedType, Env) ->
    % Try structural typing approach
    case infer_structural_type(Expr, Env) of
        {ok, StructType} -> {ok, StructType};
        Error -> Error
    end;
apply_strategy(duck_typing, Expr, ExpectedType, Env) ->
    % Try duck typing approach
    case infer_duck_type(Expr, ExpectedType, Env) of
        {ok, DuckType} -> {ok, DuckType};
        Error -> Error
    end;
apply_strategy(gradual_typing, Expr, _ExpectedType, Env) ->
    % Try gradual typing with any types
    case infer_gradual_type(Expr, Env) of
        {ok, GradualType} -> {ok, GradualType};
        Error -> Error
    end.

%% Helper functions for enhanced inference

infer_list_elements_bidirectional([], _ExpectedElemType, _Env, Constraints, _Location) ->
    {ok, Constraints, []};
infer_list_elements_bidirectional([Elem | Rest], ExpectedElemType, Env, Constraints, Location) ->
    case bidirectional_infer_impl(Elem, ExpectedElemType, Env, Constraints, []) of
        {ok, _ElemType, ElemConstraints, ElemSteps} ->
            case
                infer_list_elements_bidirectional(
                    Rest, ExpectedElemType, Env, ElemConstraints, Location
                )
            of
                {ok, RestConstraints, RestSteps} ->
                    {ok, RestConstraints, ElemSteps ++ RestSteps};
                Error ->
                    Error
            end;
        Error ->
            Error
    end.

infer_function_call_enhanced(_Function, FuncType, Args, ExpectedType, Env, Location) ->
    % Enhanced function call inference with better argument type propagation
    case extract_function_signature(FuncType) of
        {ok, ParamTypes, ReturnType} ->
            case infer_args_with_expected_types(Args, ParamTypes, Env, Location) of
                {ok, ArgConstraints, ArgSteps} ->
                    % Check if return type matches expected
                    case ExpectedType of
                        undefined ->
                            {ok, ReturnType, ArgConstraints, ArgSteps};
                        Expected ->
                            case unify(ReturnType, Expected) of
                                {ok, _} ->
                                    ReturnStep =
                                        {inference_step, return_type_check, {ReturnType, Expected},
                                            ok, Location},
                                    {ok, Expected, ArgConstraints, [ReturnStep | ArgSteps]};
                                {error, Reason} ->
                                    {error, {return_type_mismatch, ReturnType, Expected, Reason}}
                            end
                    end;
                Error ->
                    Error
            end;
        {error, Reason} ->
            {error, {invalid_function_type, FuncType, Reason}}
    end.

extract_function_signature({function_type, ParamTypes, ReturnType}) ->
    {ok, ParamTypes, ReturnType};
extract_function_signature(_) ->
    {error, not_a_function_type}.

infer_args_with_expected_types(Args, ExpectedTypes, Env, Location) ->
    case length(Args) =:= length(ExpectedTypes) of
        true ->
            infer_args_zip(Args, ExpectedTypes, Env, Location, [], []);
        false ->
            {error, {arity_mismatch, length(Args), length(ExpectedTypes)}}
    end.

infer_args_zip([], [], _Env, _Location, AccConstraints, AccSteps) ->
    {ok, lists:reverse(AccConstraints), lists:reverse(AccSteps)};
infer_args_zip(
    [Arg | RestArgs], [ExpectedType | RestTypes], Env, Location, AccConstraints, AccSteps
) ->
    case bidirectional_infer_impl(Arg, ExpectedType, Env, [], []) of
        {ok, _ArgType, ArgConstraints, ArgSteps} ->
            infer_args_zip(
                RestArgs,
                RestTypes,
                Env,
                Location,
                ArgConstraints ++ AccConstraints,
                ArgSteps ++ AccSteps
            );
        Error ->
            Error
    end.

analyze_list_element_patterns(Elements, Env) ->
    % Analyze elements to find common patterns
    case Elements of
        [] ->
            {error, empty_list};
        [FirstElem | RestElems] ->
            case infer_expr(FirstElem, Env) of
                {ok, FirstType, _} ->
                    check_element_type_consistency(RestElems, FirstType, Env);
                Error ->
                    Error
            end
    end.

check_element_type_consistency([], ConsistentType, _Env) ->
    {ok, ConsistentType};
check_element_type_consistency([Elem | Rest], ConsistentType, Env) ->
    case infer_expr(Elem, Env) of
        {ok, ElemType, _} ->
            case unify(ConsistentType, ElemType) of
                {ok, _} ->
                    check_element_type_consistency(Rest, ConsistentType, Env);
                {error, _} ->
                    % Try to find more general type
                    case find_common_supertype(ConsistentType, ElemType) of
                        {ok, SuperType} ->
                            check_element_type_consistency(Rest, SuperType, Env);
                        {error, _} ->
                            {error, inconsistent_element_types}
                    end
            end;
        Error ->
            Error
    end.

analyze_list_for_vector_potential(Elements, Env) ->
    % Check if all elements are numeric
    lists:all(
        fun(Elem) ->
            case infer_expr(Elem, Env) of
                {ok, Type, _} -> is_numeric_type(Type);
                _ -> false
            end
        end,
        Elements
    ).

is_numeric_type({primitive_type, 'Int'}) -> true;
is_numeric_type({primitive_type, 'Float'}) -> true;
is_numeric_type(_) -> false.

find_common_supertype(Type1, Type2) ->
    % Simple supertype finding
    case {Type1, Type2} of
        {{primitive_type, 'Int'}, {primitive_type, 'Float'}} ->
            {ok, {primitive_type, 'Float'}};
        {{primitive_type, 'Float'}, {primitive_type, 'Int'}} ->
            {ok, {primitive_type, 'Float'}};
        _ ->
            {error, no_common_supertype}
    end.

infer_structural_type(_Expr, _Env) ->
    {error, not_implemented}.

infer_duck_type(_Expr, _ExpectedType, _Env) ->
    {error, not_implemented}.

infer_gradual_type(_Expr, _Env) ->
    {error, not_implemented}.

%% Constraint dependency analysis
build_constraint_dependencies(Constraints) ->
    % Build a simple dependency graph based on type variables
    lists:foldl(
        fun(C, Acc) ->
            Vars = extract_type_vars_from_constraint(C),
            [{C, Vars} | Acc]
        end,
        [],
        Constraints
    ).

extract_type_vars_from_constraint(#type_constraint{left = Left, right = Right}) ->
    LeftVars = extract_type_vars(Left),
    RightVars = extract_type_vars(Right),
    sets:to_list(sets:union(sets:from_list(LeftVars), sets:from_list(RightVars))).

extract_type_vars(#type_var{id = Id}) ->
    [Id];
extract_type_vars({function_type, Params, Return}) ->
    ParamVars = lists:flatmap(fun extract_type_vars/1, Params),
    ReturnVars = extract_type_vars(Return),
    ParamVars ++ ReturnVars;
extract_type_vars({dependent_type, _Name, Params}) ->
    lists:flatmap(fun(#type_param{value = Value}) -> extract_type_vars(Value) end, Params);
extract_type_vars(_) ->
    [].

topological_sort_constraints(DepGraph) ->
    % Simple topological sort (could detect cycles)
    {ok, [C || {C, _Deps} <- DepGraph]}.

propagate_constraints_ordered(Constraints, Subst, AccConstraints) ->
    case Constraints of
        [] ->
            {ok, lists:reverse(AccConstraints), Subst};
        [C | Rest] ->
            case solve_constraint(C, Subst) of
                {ok, NewSubst} ->
                    propagate_constraints_ordered(Rest, NewSubst, AccConstraints);
                {error, _} ->
                    propagate_constraints_ordered(Rest, Subst, [C | AccConstraints])
            end
    end.

%% Helper functions for enhanced inference (using existing implementations above)

%% ===== RECURSIVE TYPES IMPLEMENTATION =====

%% Create a recursive type definition
create_recursive_type(Name, Params, Definition, Location) ->
    % Check that the recursive type is well-formed
    case check_recursive_definition_validity(Name, Definition) of
        {ok, ValidatedDefinition} ->
            #recursive_type{
                name = Name,
                params = Params,
                definition = ValidatedDefinition,
                binding_context = #{},
                location = Location
            };
        {error, Reason} ->
            {error, {invalid_recursive_type, Name, Reason}}
    end.

%% Unfold a recursive type one level
unfold_recursive_type(RecType = #recursive_type{name = _Name, definition = _Def}) ->
    unfold_recursive_type(RecType, 1).

unfold_recursive_type(RecType = #recursive_type{name = Name, definition = Def}, MaxDepth) ->
    case MaxDepth =< 0 of
        true ->
            {error, max_unfold_depth_reached};
        false ->
            % Substitute recursive occurrences in definition
            UnfoldedDef = substitute_recursive_refs(Def, Name, RecType, MaxDepth - 1),
            {ok, UnfoldedDef}
    end;
unfold_recursive_type(#mu_type{var = Var, body = Body, unfold_level = Level}, MaxDepth) ->
    case MaxDepth =< 0 of
        true ->
            {error, max_unfold_depth_reached};
        false ->
            % Substitute μ-variable in body
            UnfoldedBody = substitute_mu_var(Body, Var, #mu_type{
                var = Var, body = Body, unfold_level = Level + 1
            }),
            {ok, UnfoldedBody}
    end;
unfold_recursive_type(Type, _MaxDepth) ->
    % Not a recursive type, return as-is
    {ok, Type}.

%% Fold a type into recursive form
fold_recursive_type(Type, Name) ->
    case extract_recursive_pattern(Type, Name) of
        {ok, Pattern} ->
            #recursive_type{
                name = Name,
                params = [],
                definition = Pattern,
                binding_context = #{},
                location = undefined
            };
        {error, Reason} ->
            {error, Reason}
    end.

%% Check if a recursive type is well-formed
check_recursive_type_well_formed(RecType = #recursive_type{name = Name, definition = Def}) ->
    CycleState = #cycle_detection{
        visited = sets:new(),
        stack = [],
        max_depth = 100
    },

    case detect_cycles(Def, CycleState) of
        {ok, _} ->
            % Check for proper recursion (type must actually be recursive)
            case contains_recursive_ref(Def, Name) of
                true ->
                    % Check productivity (finite unfolding)
                    check_productivity(RecType);
                false ->
                    {error, {not_actually_recursive, Name}}
            end;
        {error, Reason} ->
            {error, Reason}
    end;
check_recursive_type_well_formed(#mu_type{var = Var, body = Body}) ->
    % Check μ-type well-formedness
    case contains_free_var(Body, Var) of
        true -> check_mu_productivity(Var, Body);
        false -> {error, {unused_mu_variable, Var}}
    end;
check_recursive_type_well_formed(_Type) ->
    {error, not_a_recursive_type}.

%% Unify recursive types
unify_recursive_types(RecType1, RecType2, Subst) ->
    case {RecType1, RecType2} of
        {#recursive_type{name = Name}, #recursive_type{name = Name}} ->
            % Same recursive type - structural unification
            unify_recursive_structural(RecType1, RecType2, Subst);
        {#recursive_type{} = R1, #recursive_type{} = R2} ->
            % Different recursive types - try unfolding
            unify_recursive_by_unfolding(R1, R2, Subst, 3);
        {#mu_type{} = M1, #mu_type{} = M2} ->
            % μ-types unification
            unify_mu_types(M1, M2, Subst);
        {#recursive_type{} = R, Type} ->
            % Recursive type with regular type - unfold and unify
            case unfold_recursive_type(R, 2) of
                {ok, UnfoldedR} -> unify(UnfoldedR, Type, Subst);
                {error, Reason} -> {error, {unfold_failed, Reason}}
            end;
        {Type, #recursive_type{} = R} ->
            % Symmetric case
            unify_recursive_types(R, Type, Subst);
        _ ->
            {error, {not_recursive_types, RecType1, RecType2}}
    end.

%% Enhanced occurs check for recursive types
occurs_check_recursive(Var = #type_var{id = Id}, RecType = #recursive_type{definition = Def}) ->
    % Check if variable occurs in the definition
    case occurs_check_in_recursive_def(Id, Def) of
        true ->
            true;
        false ->
            % Also check in unfolded form (limited depth)
            case unfold_recursive_type(RecType, 2) of
                {ok, UnfoldedType} -> occurs_check(Var, UnfoldedType);
                {error, _} -> false
            end
    end;
occurs_check_recursive(Var, #mu_type{var = MuVar, body = Body}) ->
    occurs_check_in_mu_body(Var, MuVar, Body);
occurs_check_recursive(Var, Type) ->
    % Fall back to regular occurs check
    occurs_check(Var, Type).

%% Detect cycles in type definitions
detect_cycles(
    Type, State = #cycle_detection{visited = _Visited, stack = Stack, max_depth = MaxDepth}
) ->
    case length(Stack) >= MaxDepth of
        true -> {error, max_depth_exceeded};
        false -> detect_cycles_impl(Type, State)
    end.

detect_cycles_impl(
    {recursive_type_ref, Name}, State = #cycle_detection{visited = Visited, stack = Stack}
) ->
    case lists:member(Name, Stack) of
        true ->
            {error, {cycle_detected, Name, Stack}};
        false ->
            NewState = State#cycle_detection{
                visited = sets:add_element(Name, Visited),
                stack = [Name | Stack]
            },
            % Continue analysis (would need the actual type definition)
            {ok, NewState}
    end;
detect_cycles_impl(#recursive_type{name = Name, definition = Def}, State) ->
    NewState = State#cycle_detection{stack = [Name | State#cycle_detection.stack]},
    detect_cycles_impl(Def, NewState);
detect_cycles_impl({function_type, Params, Return}, State) ->
    case detect_cycles_in_list(Params, State) of
        {ok, State1} -> detect_cycles_impl(Return, State1);
        Error -> Error
    end;
detect_cycles_impl({dependent_type, _Name, Params}, State) ->
    TypeParams = [V || #type_param{value = V} <- Params],
    detect_cycles_in_list(TypeParams, State);
detect_cycles_impl({list_type, ElemType, LenExpr}, State) ->
    case detect_cycles_impl(ElemType, State) of
        {ok, State1} when LenExpr =/= undefined -> detect_cycles_impl(LenExpr, State1);
        {ok, State1} -> {ok, State1};
        Error -> Error
    end;
detect_cycles_impl(#mu_type{var = _Var, body = Body}, State) ->
    % μ-types create their own scope
    detect_cycles_impl(Body, State);
detect_cycles_impl(_Type, State) ->
    % Base types, type variables, etc.
    {ok, State}.

detect_cycles_in_list([], State) ->
    {ok, State};
detect_cycles_in_list([Type | Rest], State) ->
    case detect_cycles_impl(Type, State) of
        {ok, State1} -> detect_cycles_in_list(Rest, State1);
        Error -> Error
    end.

%% Helper functions for recursive type implementation

check_recursive_definition_validity(Name, Definition) ->
    % Check that the definition is valid for recursion
    case validate_recursive_structure(Definition, Name) of
        ok -> {ok, Definition};
        {error, Reason} -> {error, Reason}
    end.

validate_recursive_structure(Definition, Name) ->
    % Check that recursive references are productive
    case find_recursive_refs(Definition, Name) of
        [] -> {error, no_recursive_references};
        Refs -> check_productivity_of_refs(Refs, Definition)
    end.

find_recursive_refs(Definition, Name) ->
    find_recursive_refs_impl(Definition, Name, []).

find_recursive_refs_impl({recursive_type_ref, Name}, Name, Acc) ->
    [Name | Acc];
find_recursive_refs_impl({function_type, Params, Return}, Name, Acc) ->
    ParamRefs = lists:flatmap(fun(P) -> find_recursive_refs_impl(P, Name, []) end, Params),
    ReturnRefs = find_recursive_refs_impl(Return, Name, []),
    ParamRefs ++ ReturnRefs ++ Acc;
find_recursive_refs_impl({dependent_type, _, Params}, Name, Acc) ->
    lists:flatmap(fun(#type_param{value = V}) -> find_recursive_refs_impl(V, Name, []) end, Params) ++
        Acc;
find_recursive_refs_impl({list_type, ElemType, LenExpr}, Name, Acc) ->
    ElemRefs = find_recursive_refs_impl(ElemType, Name, []),
    LenRefs =
        case LenExpr of
            undefined -> [];
            _ -> find_recursive_refs_impl(LenExpr, Name, [])
        end,
    ElemRefs ++ LenRefs ++ Acc;
% Handle complex constructor types from tests
find_recursive_refs_impl({union_type, Variants}, Name, Acc) ->
    lists:flatmap(fun(V) -> find_recursive_refs_impl(V, Name, []) end, Variants) ++ Acc;
find_recursive_refs_impl({cons_type, Elements}, Name, Acc) ->
    lists:flatmap(fun(E) -> find_recursive_refs_impl(E, Name, []) end, Elements) ++ Acc;
find_recursive_refs_impl({node_type, Elements}, Name, Acc) ->
    lists:flatmap(fun(E) -> find_recursive_refs_impl(E, Name, []) end, Elements) ++ Acc;
find_recursive_refs_impl({succ_type, Elements}, Name, Acc) ->
    lists:flatmap(fun(E) -> find_recursive_refs_impl(E, Name, []) end, Elements) ++ Acc;
find_recursive_refs_impl(_, _, Acc) ->
    Acc.

check_productivity_of_refs(Refs, Definition) ->
    % A recursive type is productive if at least one recursive reference
    % is under a constructor (not immediately recursive)
    case has_constructor_wrapped_ref(Definition, Refs) of
        true -> ok;
        false -> {error, non_productive_recursion}
    end.

has_constructor_wrapped_ref({function_type, _, _}, _Refs) -> true;
has_constructor_wrapped_ref({list_type, _, _}, _Refs) -> true;
has_constructor_wrapped_ref({dependent_type, _, _}, _Refs) -> true;
has_constructor_wrapped_ref({recursive_type_ref, _}, _Refs) -> false;
has_constructor_wrapped_ref(_, _) -> true.

substitute_recursive_refs(Type, RecName, RecType, Depth) ->
    substitute_recursive_refs_impl(Type, RecName, RecType, Depth).

substitute_recursive_refs_impl({recursive_type_ref, RecName}, RecName, RecType, Depth) when
    Depth > 0
->
    % Substitute with unfolded definition
    case unfold_recursive_type(RecType, Depth) of
        {ok, Unfolded} -> Unfolded;
        % Keep original if unfold fails
        {error, _} -> {recursive_type_ref, RecName}
    end;
substitute_recursive_refs_impl({function_type, Params, Return}, RecName, RecType, Depth) ->
    NewParams = [substitute_recursive_refs_impl(P, RecName, RecType, Depth) || P <- Params],
    NewReturn = substitute_recursive_refs_impl(Return, RecName, RecType, Depth),
    {function_type, NewParams, NewReturn};
substitute_recursive_refs_impl({dependent_type, Name, Params}, RecName, RecType, Depth) ->
    NewParams = [
        #type_param{name = N, value = substitute_recursive_refs_impl(V, RecName, RecType, Depth)}
     || #type_param{name = N, value = V} <- Params
    ],
    {dependent_type, Name, NewParams};
substitute_recursive_refs_impl({list_type, ElemType, LenExpr}, RecName, RecType, Depth) ->
    NewElemType = substitute_recursive_refs_impl(ElemType, RecName, RecType, Depth),
    NewLenExpr =
        case LenExpr of
            undefined -> undefined;
            _ -> substitute_recursive_refs_impl(LenExpr, RecName, RecType, Depth)
        end,
    {list_type, NewElemType, NewLenExpr};
substitute_recursive_refs_impl(Type, _RecName, _RecType, _Depth) ->
    Type.

substitute_mu_var(Type, MuVar, Replacement) ->
    substitute_mu_var_impl(Type, MuVar, Replacement).

substitute_mu_var_impl({mu_var, MuVar}, MuVar, Replacement) ->
    Replacement;
substitute_mu_var_impl({function_type, Params, Return}, MuVar, Replacement) ->
    NewParams = [substitute_mu_var_impl(P, MuVar, Replacement) || P <- Params],
    NewReturn = substitute_mu_var_impl(Return, MuVar, Replacement),
    {function_type, NewParams, NewReturn};
substitute_mu_var_impl({dependent_type, Name, Params}, MuVar, Replacement) ->
    NewParams = [
        #type_param{name = N, value = substitute_mu_var_impl(V, MuVar, Replacement)}
     || #type_param{name = N, value = V} <- Params
    ],
    {dependent_type, Name, NewParams};
substitute_mu_var_impl({list_type, ElemType, LenExpr}, MuVar, Replacement) ->
    NewElemType = substitute_mu_var_impl(ElemType, MuVar, Replacement),
    NewLenExpr =
        case LenExpr of
            undefined -> undefined;
            _ -> substitute_mu_var_impl(LenExpr, MuVar, Replacement)
        end,
    {list_type, NewElemType, NewLenExpr};
substitute_mu_var_impl(Type, _MuVar, _Replacement) ->
    Type.

extract_recursive_pattern(Type, Name) ->
    % Try to extract a recursive pattern from a type definition
    case find_recursive_refs(Type, Name) of
        [] -> {error, {no_recursive_pattern, Name}};
        % For now, just return the type
        _Refs -> {ok, Type}
    end.

contains_recursive_ref(Type, Name) ->
    case find_recursive_refs(Type, Name) of
        [] -> false;
        _ -> true
    end.

contains_free_var(Type, Var) ->
    contains_free_var_impl(Type, Var).

contains_free_var_impl({mu_var, Var}, Var) ->
    true;
contains_free_var_impl({function_type, Params, Return}, Var) ->
    lists:any(fun(P) -> contains_free_var_impl(P, Var) end, Params) orelse
        contains_free_var_impl(Return, Var);
contains_free_var_impl({dependent_type, _, Params}, Var) ->
    lists:any(fun(#type_param{value = V}) -> contains_free_var_impl(V, Var) end, Params);
contains_free_var_impl({list_type, ElemType, LenExpr}, Var) ->
    contains_free_var_impl(ElemType, Var) orelse
        (LenExpr =/= undefined andalso contains_free_var_impl(LenExpr, Var));
contains_free_var_impl(_, _) ->
    false.

check_productivity(_RecType = #recursive_type{name = Name, definition = Def}) ->
    % Check that the recursive type is productive (terminates in finite steps)

    % Max depth 5
    case analyze_productivity(Def, Name, 5) of
        productive -> ok;
        {non_productive, Reason} -> {error, {non_productive, Reason}}
    end.

analyze_productivity(_Definition, _Name, MaxDepth) when MaxDepth =< 0 ->
    {non_productive, max_depth_reached};
analyze_productivity({recursive_type_ref, Name}, Name, _MaxDepth) ->
    {non_productive, immediate_recursion};
analyze_productivity({function_type, Params, Return}, Name, MaxDepth) ->
    % Function types are generally productive
    case
        lists:any(fun(P) -> analyze_productivity(P, Name, MaxDepth - 1) =:= productive end, Params)
    of
        true -> productive;
        false -> analyze_productivity(Return, Name, MaxDepth - 1)
    end;
analyze_productivity({list_type, ElemType, _}, Name, MaxDepth) ->
    % List types are productive
    analyze_productivity(ElemType, Name, MaxDepth - 1);
analyze_productivity({dependent_type, _, _}, _Name, _MaxDepth) ->
    % Dependent types are generally productive
    productive;
analyze_productivity(_, _, _) ->
    productive.

check_mu_productivity(Var, Body) ->
    % μ-types are productive if the body contains the variable under constructors
    case has_constructor_above_var(Body, Var) of
        true -> ok;
        false -> {error, {non_productive_mu, Var}}
    end.

has_constructor_above_var({mu_var, Var}, Var) ->
    false;
has_constructor_above_var({function_type, Params, Return}, Var) ->
    lists:any(fun(P) -> has_constructor_above_var(P, Var) end, Params) orelse
        has_constructor_above_var(Return, Var);
has_constructor_above_var({list_type, ElemType, _}, Var) ->
    has_constructor_above_var(ElemType, Var);
has_constructor_above_var({dependent_type, _, Params}, Var) ->
    lists:any(fun(#type_param{value = V}) -> has_constructor_above_var(V, Var) end, Params);
has_constructor_above_var(_, _) ->
    true.

unify_recursive_structural(
    #recursive_type{name = Name, params = Params1},
    #recursive_type{name = Name, params = Params2},
    Subst
) ->
    % Same recursive type - unify parameters
    unify_type_params(Params1, Params2, Subst);
unify_recursive_structural(R1, R2, _Subst) ->
    {error, {different_recursive_types, R1, R2}}.

unify_recursive_by_unfolding(R1, R2, Subst, MaxDepth) when MaxDepth > 0 ->
    case {unfold_recursive_type(R1, 1), unfold_recursive_type(R2, 1)} of
        {{ok, U1}, {ok, U2}} ->
            case unify(U1, U2, Subst) of
                {ok, NewSubst} -> {ok, NewSubst};
                {error, _} -> unify_recursive_by_unfolding(R1, R2, Subst, MaxDepth - 1)
            end;
        _ ->
            {error, unfold_failed}
    end;
unify_recursive_by_unfolding(_R1, _R2, _Subst, _MaxDepth) ->
    {error, max_unfold_attempts_reached}.

unify_mu_types(#mu_type{var = Var1, body = Body1}, #mu_type{var = Var2, body = Body2}, Subst) ->
    % Rename variables to avoid conflicts and unify bodies
    FreshVar = gensym_mu_var(),
    RenamedBody1 = substitute_mu_var(Body1, Var1, {mu_var, FreshVar}),
    RenamedBody2 = substitute_mu_var(Body2, Var2, {mu_var, FreshVar}),
    unify(RenamedBody1, RenamedBody2, Subst).

occurs_check_in_recursive_def(Id, Definition) ->
    occurs_check_in_recursive_def_impl(Id, Definition).

occurs_check_in_recursive_def_impl(Id, #type_var{id = Id}) ->
    true;
occurs_check_in_recursive_def_impl(Id, {function_type, Params, Return}) ->
    lists:any(fun(P) -> occurs_check_in_recursive_def_impl(Id, P) end, Params) orelse
        occurs_check_in_recursive_def_impl(Id, Return);
occurs_check_in_recursive_def_impl(Id, {dependent_type, _, Params}) ->
    lists:any(fun(#type_param{value = V}) -> occurs_check_in_recursive_def_impl(Id, V) end, Params);
occurs_check_in_recursive_def_impl(Id, {list_type, ElemType, LenExpr}) ->
    occurs_check_in_recursive_def_impl(Id, ElemType) orelse
        (LenExpr =/= undefined andalso occurs_check_in_recursive_def_impl(Id, LenExpr));
occurs_check_in_recursive_def_impl(_, _) ->
    false.

occurs_check_in_mu_body(_Var = #type_var{id = Id}, MuVar, Body) ->
    case contains_free_var(Body, MuVar) of
        true -> occurs_check_in_recursive_def_impl(Id, Body);
        false -> false
    end;
occurs_check_in_mu_body(_, _, _) ->
    false.

gensym_mu_var() ->
    Counter =
        case get(mu_var_counter) of
            undefined -> 0;
            N -> N
        end,
    put(mu_var_counter, Counter + 1),
    list_to_atom("mu_" ++ integer_to_list(Counter)).

%% ===== HIGHER-KINDED TYPES IMPLEMENTATION =====

%% Create a kind definition
create_kind(Constructor, Args, Location) ->
    #kind{
        constructor = Constructor,
        args = Args,
        result = determine_result_kind(Constructor, Args),
        arity = length(Args),
        location = Location
    }.

% * kind
determine_result_kind(star, []) -> star;
determine_result_kind(star, _) -> error;
% * -> *
determine_result_kind(arrow, [_, Result]) -> Result;
determine_result_kind(arrow, _) -> error;
determine_result_kind(_, []) -> star;
determine_result_kind(_, Args) -> lists:last(Args).

%% Infer the kind of a type expression
infer_kind(Type, KindEnv) ->
    case Type of
        {primitive_type, _Name} ->
            {ok, #kind{
                constructor = star, args = [], result = star, arity = 0, location = undefined
            }};
        #type_var{} ->
            % Type variables have kind *
            {ok, #kind{
                constructor = star, args = [], result = star, arity = 0, location = undefined
            }};
        {function_type, Params, Return} ->
            % Function types: * -> * -> ... -> *
            case lists:all(fun(P) -> is_base_kind(infer_kind(P, KindEnv)) end, Params) of
                true ->
                    case infer_kind(Return, KindEnv) of
                        {ok, RetKind} when RetKind#kind.constructor =:= star ->
                            {ok, #kind{
                                constructor = star,
                                args = [],
                                result = star,
                                arity = 0,
                                location = undefined
                            }};
                        _ ->
                            {error, invalid_function_return_kind}
                    end;
                false ->
                    {error, invalid_function_param_kinds}
            end;
        {dependent_type, Name, Params} ->
            % Dependent types may have higher kinds
            infer_dependent_type_kind(Name, Params, KindEnv);
        #higher_kinded_type{constructor = Constructor} ->
            {ok, Constructor#type_constructor.kind};
        _ ->
            % Default to * kind for unknown types
            {ok, #kind{
                constructor = star, args = [], result = star, arity = 0, location = undefined
            }}
    end.

%% Check if a type has the expected kind
check_kind(Type, ExpectedKind, KindEnv) ->
    case infer_kind(Type, KindEnv) of
        {ok, InferredKind} ->
            case unify_kinds(InferredKind, ExpectedKind) of
                {ok, _} -> ok;
                {error, Reason} -> {error, {kind_mismatch, ExpectedKind, InferredKind, Reason}}
            end;
        {error, Reason} ->
            {error, {kind_inference_failed, Reason}}
    end.

%% Unify two kinds
unify_kinds(Kind1, Kind2) ->
    case {Kind1, Kind2} of
        {#kind{constructor = C1}, #kind{constructor = C2}} when C1 =:= C2 ->
            case {Kind1#kind.args, Kind2#kind.args} of
                {Args1, Args2} when length(Args1) =:= length(Args2) ->
                    unify_kind_args(Args1, Args2);
                _ ->
                    {error, kind_arity_mismatch}
            end;
        _ ->
            {error, {kind_constructor_mismatch, Kind1, Kind2}}
    end.

unify_kind_args([], []) ->
    {ok, #{}};
unify_kind_args([K1 | Rest1], [K2 | Rest2]) ->
    case unify_kinds(K1, K2) of
        {ok, _} -> unify_kind_args(Rest1, Rest2);
        Error -> Error
    end.

%% Create a type constructor
create_type_constructor(Name, Kind, Params, Definition, Location) ->
    case check_type_constructor_validity(Name, Kind, Params, Definition) of
        ok ->
            #type_constructor{
                name = Name,
                kind = Kind,
                params = Params,
                definition = Definition,
                constraints = [],
                location = Location
            };
        {error, Reason} ->
            {error, {invalid_type_constructor, Name, Reason}}
    end.

%% Apply a type constructor to arguments
apply_type_constructor(TypeConstructor, Args, Location) ->
    case TypeConstructor of
        #type_constructor{kind = _Kind, params = Params} ->
            RequiredArity = length(Params),
            ProvidedArity = length(Args),

            case ProvidedArity =< RequiredArity of
                true ->
                    RemainingArgs = RequiredArity - ProvidedArity,

                    % Check kind compatibility of provided arguments
                    case check_argument_kinds(Args, Params, #{}) of
                        ok ->
                            #higher_kinded_type{
                                constructor = TypeConstructor,
                                applied_args = Args,
                                remaining_args = RemainingArgs,
                                location = Location
                            };
                        {error, Reason} ->
                            {error, {argument_kind_error, Reason}}
                    end;
                false ->
                    {error, {too_many_arguments, ProvidedArity, RequiredArity}}
            end;
        _ ->
            {error, not_a_type_constructor}
    end.

%% Create a type family definition
create_type_family(Name, Kind, Equations, Location) ->
    case check_type_family_validity(Name, Kind, Equations) of
        ok ->
            #type_family{
                name = Name,
                kind = Kind,
                equations = Equations,
                location = Location
            };
        {error, Reason} ->
            {error, {invalid_type_family, Name, Reason}}
    end.

%% Evaluate a type family application
evaluate_type_family(TypeFamily, Args) ->
    case TypeFamily of
        #type_family{equations = Equations} ->
            try_equations(Equations, Args);
        _ ->
            {error, not_a_type_family}
    end.

try_equations([], _Args) ->
    {error, no_matching_equation};
try_equations([Equation | RestEquations], Args) ->
    case match_type_family_pattern(Equation#type_family_equation.pattern, Args) of
        {ok, Substitution} ->
            Result = apply_substitution(Equation#type_family_equation.result, Substitution),
            {ok, Result};
        {error, _} ->
            try_equations(RestEquations, Args)
    end.

%% Solve type family equation
solve_type_family_equation(Equation, Args, KindEnv) ->
    Pattern = Equation#type_family_equation.pattern,
    Result = Equation#type_family_equation.result,

    case match_type_family_pattern(Pattern, Args) of
        {ok, Substitution} ->
            % Check constraints
            case
                check_equation_constraints(
                    Equation#type_family_equation.constraints, Substitution, KindEnv
                )
            of
                ok ->
                    FinalResult = apply_substitution(Result, Substitution),
                    {ok, FinalResult};
                {error, Reason} ->
                    {error, {constraint_violation, Reason}}
            end;
        {error, Reason} ->
            {error, {pattern_match_failed, Reason}}
    end.

%% Check constraint satisfaction
check_constraint_satisfaction(Constraint, KindEnv) ->
    case Constraint of
        #constraint{class = Class, args = Args} ->
            check_type_class_instance(Class, Args, KindEnv);
        _ ->
            {error, invalid_constraint}
    end.

%% Check if higher-kinded type is well-formed
check_higher_kinded_well_formed(HKType) ->
    case HKType of
        #higher_kinded_type{constructor = Constructor, applied_args = Args} ->
            % Check constructor validity
            case check_constructor_well_formed(Constructor) of
                ok ->
                    % Check argument compatibility
                    check_applied_args_valid(Constructor, Args);
                {error, Reason} ->
                    {error, Reason}
            end;
        _ ->
            {error, not_a_higher_kinded_type}
    end.

%% Get the arity of a kind
kind_arity(Kind) ->
    case Kind of
        #kind{arity = Arity} -> Arity;
        _ -> 0
    end.

%% Check if a type is saturated (fully applied)
is_saturated_type(Type) ->
    case Type of
        #higher_kinded_type{remaining_args = 0} -> true;
        #higher_kinded_type{remaining_args = N} when N > 0 -> false;
        % Non-higher-kinded types are considered saturated
        _ -> true
    end.

%% Helper functions for higher-kinded types

infer_dependent_type_kind(Name, Params, _KindEnv) ->
    case {Name, length(Params)} of
        {'List', 1} ->
            {ok, #kind{
                constructor = arrow,
                args = [star_kind(), star_kind()],
                result = star,
                arity = 1,
                location = undefined
            }};
        {'Maybe', 1} ->
            {ok, #kind{
                constructor = arrow,
                args = [star_kind(), star_kind()],
                result = star,
                arity = 1,
                location = undefined
            }};
        {'Vector', 2} ->
            % Vector has kind * -> Nat -> *
            {ok, #kind{
                constructor = arrow,
                args = [star_kind(), nat_kind(), star_kind()],
                result = star,
                arity = 2,
                location = undefined
            }};
        {'Functor', 1} ->
            % Functor has kind (* -> *) -> Constraint
            {ok, #kind{
                constructor = arrow,
                args = [higher_order_kind(), constraint_kind()],
                result = constraint,
                arity = 1,
                location = undefined
            }};
        {'Monad', 1} ->
            % Monad has kind (* -> *) -> Constraint
            {ok, #kind{
                constructor = arrow,
                args = [higher_order_kind(), constraint_kind()],
                result = constraint,
                arity = 1,
                location = undefined
            }};
        _ ->
            % Default to * for unknown types
            {ok, star_kind()}
    end.

star_kind() ->
    #kind{constructor = star, args = [], result = star, arity = 0, location = undefined}.

nat_kind() ->
    #kind{constructor = nat, args = [], result = nat, arity = 0, location = undefined}.

higher_order_kind() ->
    #kind{
        constructor = arrow,
        args = [star_kind(), star_kind()],
        result = star,
        arity = 1,
        location = undefined
    }.

constraint_kind() ->
    #kind{
        constructor = constraint, args = [], result = constraint, arity = 0, location = undefined
    }.

is_base_kind({ok, Kind}) ->
    Kind#kind.constructor =:= star;
is_base_kind(_) ->
    false.

check_type_constructor_validity(_Name, Kind, Params, Definition) ->
    % Check that the number of parameters matches the kind arity
    case {kind_arity(Kind), length(Params)} of
        {Arity, Arity} ->
            % Check that definition is compatible with kind if provided
            case Definition of
                undefined -> ok;
                _ -> check_definition_kind_compatibility(Definition, Kind)
            end;
        {Expected, Got} ->
            {error, {arity_mismatch, Expected, Got}}
    end.

check_definition_kind_compatibility(_Definition, _Kind) ->
    % Simplified - would need full kind checking
    ok.

check_argument_kinds([], _Params, _KindEnv) ->
    % No more arguments to check - this is ok for partial application
    ok;
check_argument_kinds([Arg | RestArgs], [Param | RestParams], KindEnv) ->
    % Extract expected kind from parameter
    ExpectedKind = extract_param_kind(Param),
    case infer_kind(Arg, KindEnv) of
        {ok, ArgKind} ->
            case unify_kinds(ArgKind, ExpectedKind) of
                {ok, _} ->
                    check_argument_kinds(RestArgs, RestParams, KindEnv);
                {error, Reason} ->
                    {error, {argument_kind_mismatch, Arg, ExpectedKind, ArgKind, Reason}}
            end;
        {error, Reason} ->
            {error, {argument_kind_inference_failed, Arg, Reason}}
    end;
check_argument_kinds(Args, [], _KindEnv) ->
    % More arguments than parameters - this is an error
    {error, {too_many_arguments, length(Args), 0}}.

extract_param_kind(_Param) ->
    % Simplified - would extract kind from parameter type annotation
    star_kind().

check_type_family_validity(_Name, _Kind, _Equations) ->
    % Simplified validation - would check equation consistency, coverage, etc.
    ok.

match_type_family_pattern(Pattern, Args) ->
    case length(Pattern) =:= length(Args) of
        true -> match_pattern_args(Pattern, Args, #{});
        false -> {error, arity_mismatch}
    end.

match_pattern_args([], [], Substitution) ->
    {ok, Substitution};
match_pattern_args([PatternArg | RestPattern], [Arg | RestArgs], Subst) ->
    case match_single_pattern(PatternArg, Arg, Subst) of
        {ok, NewSubst} -> match_pattern_args(RestPattern, RestArgs, NewSubst);
        Error -> Error
    end.

match_single_pattern(Pattern, Arg, Subst) ->
    case Pattern of
        #type_var{id = Id} ->
            % Bind type variable
            case maps:get(Id, Subst, undefined) of
                undefined -> {ok, maps:put(Id, Arg, Subst)};
                ExistingBinding when ExistingBinding =:= Arg -> {ok, Subst};
                _ -> {error, variable_binding_conflict}
            end;
        % Handle atoms as type variable IDs (for simplified testing)
        Pattern when is_atom(Pattern) ->
            case maps:get(Pattern, Subst, undefined) of
                undefined -> {ok, maps:put(Pattern, Arg, Subst)};
                ExistingBinding when ExistingBinding =:= Arg -> {ok, Subst};
                _ -> {error, variable_binding_conflict}
            end;
        _ when Pattern =:= Arg ->
            {ok, Subst};
        _ ->
            {error, pattern_mismatch}
    end.

check_equation_constraints([], _Substitution, _KindEnv) ->
    ok;
check_equation_constraints([Constraint | RestConstraints], Substitution, KindEnv) ->
    % Apply substitution to constraint
    SubstConstraint = apply_constraint_substitution(Constraint, Substitution),
    case check_constraint_satisfaction(SubstConstraint, KindEnv) of
        ok -> check_equation_constraints(RestConstraints, Substitution, KindEnv);
        Error -> Error
    end.

apply_constraint_substitution(Constraint, Substitution) ->
    case Constraint of
        #constraint{args = Args} = C ->
            NewArgs = [apply_substitution(Arg, Substitution) || Arg <- Args],
            C#constraint{args = NewArgs};
        _ ->
            Constraint
    end.

check_type_class_instance(_Class, _Args, _KindEnv) ->
    % Simplified - would check if instance exists
    ok.

check_constructor_well_formed(Constructor) ->
    case Constructor of
        #type_constructor{kind = Kind, params = Params} ->
            % Check kind/parameter consistency
            case kind_arity(Kind) =:= length(Params) of
                true -> ok;
                false -> {error, constructor_arity_mismatch}
            end;
        _ ->
            {error, invalid_constructor}
    end.

check_applied_args_valid(Constructor, Args) ->
    case Constructor of
        #type_constructor{params = Params} ->
            RequiredArgs = length(Params),
            ProvidedArgs = length(Args),

            case ProvidedArgs =< RequiredArgs of
                true -> ok;
                false -> {error, {too_many_args, ProvidedArgs, RequiredArgs}}
            end;
        _ ->
            {error, invalid_constructor}
    end.

%% Helper functions for recursive types - using existing extract_type_param_value above

%% Helper functions for enhanced inference use existing implementations above
