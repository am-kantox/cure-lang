-module(cure_typeclass).

%% Typeclass environment management
-export([
    new_env/0,
    register_typeclass/2,
    register_instance/2,
    lookup_typeclass/2,
    lookup_instance/3,
    find_instance/3,
    check_instance_coherence/2,
    resolve_method/4,
    check_constraints/3,
    get_all_instances/2,
    validate_where_constraints/2
]).

-include("../parser/cure_ast.hrl").

%% ============================================================================
%% Type Definitions
%% ============================================================================

%% Typeclass environment storing all typeclass definitions and instances
-record(typeclass_env, {
    classes = #{} :: #{atom() => typeclass_info()},
    instances = #{} :: #{{atom(), [term()]} => instance_info()},
    instance_index = #{} :: #{atom() => [{atom(), [term()]}]},
    derive_rules = #{} :: #{atom() => fun()}
}).

%% Information about a method in a typeclass
-record(method_info, {
    name :: atom(),
    type_signature :: term(),
    constraints = [] :: [typeclass_constraint()],
    has_default = false :: boolean()
}).

%% Information about a typeclass instance
-record(instance_info, {
    typeclass :: atom(),
    type_args = [] :: [term()],
    constraints = [] :: [typeclass_constraint()],
    method_impls = #{} :: #{atom() => #function_def{}},
    source_location :: term()
}).

-type typeclass_env() :: #typeclass_env{}.
-type method_info() :: #method_info{}.
-type instance_info() :: #instance_info{}.

%% ============================================================================
%% Environment Creation
%% ============================================================================

-doc """
Creates a new empty typeclass environment.

## Returns
- `typeclass_env()` - New empty environment

## Example
```erlang
Env = cure_typeclass:new_env().
```
""".
-spec new_env() -> typeclass_env().
new_env() ->
    #typeclass_env{
        classes = #{},
        instances = #{},
        instance_index = #{},
        derive_rules = #{}
    }.

%% ============================================================================
%% Typeclass Registration
%% ============================================================================

-doc """
Registers a typeclass definition in the environment.

## Arguments
- `TypeclassDef` - The typeclass definition AST node
- `Env` - Current typeclass environment

## Returns
- `{ok, NewEnv}` - Updated environment
- `{error, Reason}` - Registration failed

## Example
```erlang
TypeclassDef = #typeclass_def{name = 'Show', ...},
{ok, NewEnv} = cure_typeclass:register_typeclass(TypeclassDef, Env).
```
""".
-spec register_typeclass(#typeclass_def{}, typeclass_env()) ->
    {ok, typeclass_env()} | {error, term()}.
register_typeclass(#typeclass_def{} = TypeclassDef, #typeclass_env{} = Env) ->
    Name = TypeclassDef#typeclass_def.name,
    TypeParams = TypeclassDef#typeclass_def.type_params,
    Constraints = TypeclassDef#typeclass_def.constraints,
    MethodSigs = TypeclassDef#typeclass_def.methods,
    DefaultMethods = TypeclassDef#typeclass_def.default_methods,

    % Check if typeclass already exists
    case maps:is_key(Name, Env#typeclass_env.classes) of
        true ->
            {error, {duplicate_typeclass, Name}};
        false ->
            % Build method info map
            Methods = build_method_info_map(MethodSigs, DefaultMethods),

            % Build default implementations map
            Defaults = build_default_impls_map(DefaultMethods),

            % Create typeclass info
            Info = #typeclass_info{
                name = Name,
                type_params = TypeParams,
                superclasses = Constraints,
                methods = Methods,
                default_impls = Defaults
            },

            % Add to environment
            NewClasses = maps:put(Name, Info, Env#typeclass_env.classes),
            NewEnv = Env#typeclass_env{classes = NewClasses},
            {ok, NewEnv}
    end.

%% Build method info map from method signatures and defaults
build_method_info_map(MethodSigs, DefaultMethods) ->
    DefaultNames = [M#function_def.name || M <- DefaultMethods],
    DefaultSet = sets:from_list(DefaultNames),

    maps:from_list([
        {Sig#method_signature.name, #method_info{
            name = Sig#method_signature.name,
            type_signature = build_method_type(Sig),
            constraints = [],
            has_default = sets:is_element(Sig#method_signature.name, DefaultSet)
        }}
     || Sig <- MethodSigs
    ]).

%% Build method type from signature
build_method_type(#method_signature{params = Params, return_type = RetType}) ->
    ParamTypes = [P#param.type || P <- Params],
    {function_type, ParamTypes, RetType}.

%% Build default implementations map
build_default_impls_map(DefaultMethods) ->
    maps:from_list([{M#function_def.name, M} || M <- DefaultMethods]).

%% ============================================================================
%% Instance Registration
%% ============================================================================

-doc """
Registers a typeclass instance in the environment.

## Arguments
- `InstanceDef` - The instance definition AST node
- `Env` - Current typeclass environment

## Returns
- `{ok, NewEnv}` - Updated environment
- `{error, Reason}` - Registration failed (e.g., overlapping instance)

## Example
```erlang
InstanceDef = #instance_def{typeclass = 'Show', ...},
{ok, NewEnv} = cure_typeclass:register_instance(InstanceDef, Env).
```
""".
-spec register_instance(#instance_def{}, typeclass_env()) ->
    {ok, typeclass_env()} | {error, term()}.
register_instance(#instance_def{} = InstanceDef, #typeclass_env{} = Env) ->
    TypeclassName = InstanceDef#instance_def.typeclass,
    TypeArgs = InstanceDef#instance_def.type_args,
    Constraints = InstanceDef#instance_def.constraints,
    Methods = InstanceDef#instance_def.methods,
    Location = InstanceDef#instance_def.location,

    % Check if typeclass exists
    case maps:get(TypeclassName, Env#typeclass_env.classes, undefined) of
        undefined ->
            {error, {unknown_typeclass, TypeclassName}};
        TypeclassInfo ->
            % Check for overlapping instances
            case check_instance_coherence(InstanceDef, Env) of
                ok ->
                    % Build method implementations map
                    MethodImpls = build_method_impls_map(Methods),

                    % Verify all required methods are implemented
                    case check_required_methods(TypeclassInfo, MethodImpls) of
                        ok ->
                            % Create instance info
                            Info = #instance_info{
                                typeclass = TypeclassName,
                                type_args = TypeArgs,
                                constraints = Constraints,
                                method_impls = MethodImpls,
                                source_location = Location
                            },

                            % Add to environment
                            InstanceKey = {TypeclassName, TypeArgs},
                            NewInstances = maps:put(InstanceKey, Info, Env#typeclass_env.instances),

                            % Update instance index
                            NewIndex = add_to_instance_index(
                                TypeclassName, TypeArgs, Env#typeclass_env.instance_index
                            ),

                            NewEnv = Env#typeclass_env{
                                instances = NewInstances,
                                instance_index = NewIndex
                            },
                            {ok, NewEnv};
                        {error, Reason} ->
                            {error, Reason}
                    end;
                {error, Reason} ->
                    {error, Reason}
            end
    end.

%% Build method implementations map
build_method_impls_map(Methods) ->
    maps:from_list([{M#function_def.name, M} || M <- Methods]).

%% Check that all required methods are implemented
check_required_methods(#typeclass_info{methods = Methods, default_impls = Defaults}, Impls) ->
    RequiredMethods = maps:keys(Methods),
    ImplementedMethods = maps:keys(Impls),
    _DefaultMethods = maps:keys(Defaults),

    % Methods that must be provided (no default)
    MustProvide = [M || M <- RequiredMethods, not maps:is_key(M, Defaults)],

    % Check if all required methods are implemented
    Missing = [M || M <- MustProvide, not lists:member(M, ImplementedMethods)],

    case Missing of
        [] -> ok;
        _ -> {error, {missing_methods, Missing}}
    end.

%% Add instance to index for faster lookup
add_to_instance_index(TypeclassName, TypeArgs, Index) ->
    InstanceKey = {TypeclassName, TypeArgs},
    CurrentList = maps:get(TypeclassName, Index, []),
    maps:put(TypeclassName, [InstanceKey | CurrentList], Index).

%% ============================================================================
%% Instance Lookup
%% ============================================================================

-doc """
Looks up a typeclass by name.

## Arguments
- `Name` - Typeclass name (atom)
- `Env` - Typeclass environment

## Returns
- `{ok, TypeclassInfo}` - Typeclass found
- `not_found` - Typeclass not registered
""".
-spec lookup_typeclass(atom(), typeclass_env()) ->
    {ok, typeclass_info()} | not_found.
lookup_typeclass(Name, #typeclass_env{classes = Classes}) ->
    case maps:get(Name, Classes, undefined) of
        undefined -> not_found;
        Info -> {ok, Info}
    end.

-doc """
Looks up an exact instance by typeclass name and type arguments.

## Arguments
- `TypeclassName` - Name of the typeclass
- `TypeArgs` - List of type arguments
- `Env` - Typeclass environment

## Returns
- `{ok, InstanceInfo}` - Instance found
- `not_found` - No matching instance
""".
-spec lookup_instance(atom(), [term()], typeclass_env()) ->
    {ok, instance_info()} | not_found.
lookup_instance(TypeclassName, TypeArgs, #typeclass_env{instances = Instances}) ->
    Key = {TypeclassName, TypeArgs},
    case maps:get(Key, Instances, undefined) of
        undefined -> not_found;
        Info -> {ok, Info}
    end.

-doc """
Finds an instance by unification (supports type variables).

## Arguments
- `TypeclassName` - Name of the typeclass
- `Type` - Type to find instance for (may contain type variables)
- `Env` - Typeclass environment

## Returns
- `{ok, InstanceInfo, Substitution}` - Instance found with type variable substitution
- `not_found` - No matching instance
- `{ambiguous, [InstanceInfo]}` - Multiple instances could match
""".
-spec find_instance(atom(), term(), typeclass_env()) ->
    {ok, instance_info(), map()} | not_found | {ambiguous, [instance_info()]}.
find_instance(TypeclassName, Type, #typeclass_env{instance_index = Index, instances = Instances}) ->
    % Get all instances for this typeclass
    InstanceKeys = maps:get(TypeclassName, Index, []),

    % Try to unify type with each instance
    Matches = lists:filtermap(
        fun(Key) ->
            Info = maps:get(Key, Instances),
            case try_unify_instance(Type, Info) of
                {ok, Subst} -> {true, {Info, Subst}};
                no_match -> false
            end
        end,
        InstanceKeys
    ),

    case Matches of
        [] -> not_found;
        [{Info, Subst}] -> {ok, Info, Subst};
        Multiple -> {ambiguous, [I || {I, _} <- Multiple]}
    end.

%% Try to unify a type with an instance's type arguments
try_unify_instance(Type, #instance_info{type_args = InstanceTypeArgs}) ->
    % Simplified unification - just check if types match
    % In full implementation, this would do proper unification with type variables
    case InstanceTypeArgs of
        [SingleArg] ->
            if
                Type =:= SingleArg ->
                    {ok, #{}};
                true ->
                    % Try structural matching
                    case {Type, SingleArg} of
                        {Same, Same} -> {ok, #{}};
                        _ -> no_match
                    end
            end;
        _ ->
            no_match
    end.

%% ============================================================================
%% Instance Coherence Checking
%% ============================================================================

-doc """
Checks if a new instance would create overlapping instances.

Ensures the global uniqueness property required for type class coherence.

## Arguments
- `NewInstance` - The instance to check
- `Env` - Current typeclass environment

## Returns
- `ok` - No overlap detected
- `{error, {overlapping_instance, ExistingInstance}}` - Overlap detected
""".
-spec check_instance_coherence(#instance_def{}, typeclass_env()) ->
    ok | {error, term()}.
check_instance_coherence(#instance_def{typeclass = TC, type_args = NewArgs}, Env) ->
    % Get all existing instances for this typeclass
    ExistingKeys = maps:get(TC, Env#typeclass_env.instance_index, []),

    % Check if any existing instance overlaps with new instance
    Overlapping = lists:filter(
        fun({_, ExistingArgs}) ->
            instances_overlap(NewArgs, ExistingArgs)
        end,
        ExistingKeys
    ),

    case Overlapping of
        [] -> ok;
        [First | _] -> {error, {overlapping_instance, First}}
    end.

%% Check if two instance type argument lists overlap
instances_overlap(Args1, Args2) ->
    % Simplified overlap check - in full implementation would check if
    % the instances could unify (considering type variables)
    Args1 =:= Args2.

%% ============================================================================
%% Method Resolution
%% ============================================================================

-doc """
Resolves a method call to its implementation.

## Arguments
- `TypeclassName` - Name of the typeclass
- `MethodName` - Name of the method
- `ReceiverType` - Type of the receiver
- `Env` - Typeclass environment

## Returns
- `{ok, Implementation}` - Method implementation found
- `{error, Reason}` - Resolution failed
""".
-spec resolve_method(atom(), atom(), term(), typeclass_env()) ->
    {ok, term()} | {error, term()}.
resolve_method(TypeclassName, MethodName, ReceiverType, Env) ->
    % Find instance for the receiver type
    case find_instance(TypeclassName, ReceiverType, Env) of
        {ok, InstanceInfo, _Subst} ->
            % Look up method implementation
            case maps:get(MethodName, InstanceInfo#instance_info.method_impls, undefined) of
                undefined ->
                    % Try default implementation
                    case lookup_typeclass(TypeclassName, Env) of
                        {ok, TypeclassInfo} ->
                            case
                                maps:get(
                                    MethodName,
                                    TypeclassInfo#typeclass_info.default_impls,
                                    undefined
                                )
                            of
                                undefined ->
                                    {error, {method_not_implemented, MethodName}};
                                DefaultImpl ->
                                    {ok, DefaultImpl}
                            end;
                        not_found ->
                            {error, {unknown_typeclass, TypeclassName}}
                    end;
                Implementation ->
                    {ok, Implementation}
            end;
        not_found ->
            {error, {no_instance, TypeclassName, ReceiverType}};
        {ambiguous, _} ->
            {error, {ambiguous_instance, TypeclassName, ReceiverType}}
    end.

%% ============================================================================
%% Constraint Checking
%% ============================================================================

-doc """
Checks if typeclass constraints are satisfied.

## Arguments
- `Constraints` - List of typeclass constraints to check
- `TypeEnv` - Type environment (for type variable resolution)
- `TypeclassEnv` - Typeclass environment

## Returns
- `ok` - All constraints satisfied
- `{error, UnsatisfiedConstraints}` - Some constraints not satisfied
- `{pending, PendingConstraints}` - Constraints depend on type variables
""".
-spec check_constraints([typeclass_constraint()], term(), typeclass_env()) ->
    ok | {error, [term()]} | {pending, [term()]}.
check_constraints(Constraints, _TypeEnv, TypeclassEnv) ->
    % Check each constraint
    Results = [check_single_constraint(C, TypeclassEnv) || C <- Constraints],

    % Categorize results
    {_Satisfied, Unsatisfied, Pending} = categorize_constraint_results(Results, Constraints),

    case {Unsatisfied, Pending} of
        {[], []} -> ok;
        {[], _} -> {pending, Pending};
        {_, _} -> {error, Unsatisfied}
    end.

%% Check a single constraint
check_single_constraint(#typeclass_constraint{typeclass = TC, type_args = Args}, Env) ->
    case Args of
        % If all args are concrete types, check for instance
        _ when is_list(Args) ->
            case lists:all(fun is_concrete_type/1, Args) of
                true ->
                    case lookup_instance(TC, Args, Env) of
                        {ok, _} -> satisfied;
                        not_found -> unsatisfied
                    end;
                false ->
                    % Contains type variables, can't check yet
                    pending
            end
    end.

%% Check if a type is concrete (no type variables)
is_concrete_type(#primitive_type{}) -> true;
is_concrete_type(#dependent_type{params = Params}) -> lists:all(fun is_concrete_type/1, Params);
is_concrete_type(_) -> false.

%% Categorize constraint check results
categorize_constraint_results(Results, Constraints) ->
    lists:foldl(
        fun({Result, Constraint}, {Sat, Unsat, Pend}) ->
            case Result of
                satisfied -> {Sat, Unsat, Pend};
                unsatisfied -> {Sat, [Constraint | Unsat], Pend};
                pending -> {Sat, Unsat, [Constraint | Pend]}
            end
        end,
        {[], [], []},
        lists:zip(Results, Constraints)
    ).

%% ============================================================================
%% Query Functions
%% ============================================================================

-doc """
Gets all instances for a given typeclass.

## Arguments
- `TypeclassName` - Name of the typeclass
- `Env` - Typeclass environment

## Returns
- `[InstanceInfo]` - List of all instances for the typeclass
""".
-spec get_all_instances(atom(), typeclass_env()) -> [instance_info()].
get_all_instances(TypeclassName, #typeclass_env{instance_index = Index, instances = Instances}) ->
    InstanceKeys = maps:get(TypeclassName, Index, []),
    [maps:get(Key, Instances) || Key <- InstanceKeys].

%% ============================================================================
%% Where Clause Validation
%% ============================================================================

-doc """
Validates where clause constraints for a function.

Verifies that:
- All referenced typeclasses exist
- Type arguments in constraints are valid
- Arity of constraint matches typeclass definition

## Arguments
- `WhereClause` - The where_clause record or undefined
- `Env` - Typeclass environment

## Returns
- `ok` - All constraints are valid
- `{error, Reason}` - Validation failed

## Example
```erlang
WhereClause = #where_clause{constraints = [...]},
{ok} = cure_typeclass:validate_where_constraints(WhereClause, Env).
```
""".
-spec validate_where_constraints(#where_clause{} | undefined, typeclass_env()) ->
    ok | {error, term()}.
validate_where_constraints(undefined, _Env) ->
    ok;
validate_where_constraints(#where_clause{constraints = Constraints}, Env) ->
    validate_constraints_list(Constraints, Env, []).

%% Validate a list of typeclass constraints
validate_constraints_list([], _Env, _Seen) ->
    ok;
validate_constraints_list([Constraint | Rest], Env, Seen) ->
    case validate_single_constraint(Constraint, Env) of
        ok ->
            % Check for duplicates
            ConstraintKey = constraint_key(Constraint),
            case lists:member(ConstraintKey, Seen) of
                true ->
                    {error, {duplicate_constraint, Constraint}};
                false ->
                    validate_constraints_list(Rest, Env, [ConstraintKey | Seen])
            end;
        {error, Reason} ->
            {error, Reason}
    end.

%% Validate a single typeclass constraint
validate_single_constraint(#typeclass_constraint{typeclass = Name, type_args = TypeArgs}, Env) ->
    % Check if typeclass exists
    case lookup_typeclass(Name, Env) of
        {ok, TypeclassInfo} ->
            % Verify arity matches
            ExpectedArity = length(TypeclassInfo#typeclass_info.type_params),
            ActualArity = length(TypeArgs),

            case ExpectedArity =:= ActualArity of
                true ->
                    % Validate each type argument
                    validate_type_args(TypeArgs);
                false ->
                    {error, {arity_mismatch, Name, ExpectedArity, ActualArity}}
            end;
        {error, not_found} ->
            {error, {unknown_typeclass, Name}}
    end.

%% Validate type arguments in constraints
validate_type_args([]) ->
    ok;
validate_type_args([TypeArg | Rest]) ->
    case is_valid_type_arg(TypeArg) of
        true ->
            validate_type_args(Rest);
        false ->
            {error, {invalid_type_arg, TypeArg}}
    end.

%% Check if a type argument is valid for use in constraints
is_valid_type_arg(#primitive_type{}) ->
    true;
is_valid_type_arg(#dependent_type{}) ->
    true;
is_valid_type_arg(#function_type{}) ->
    true;
is_valid_type_arg(#tuple_type{}) ->
    true;
is_valid_type_arg(#list_type{}) ->
    true;
is_valid_type_arg(#union_type{}) ->
    true;
is_valid_type_arg(_) ->
    false.

%% Create a key for a constraint (for duplicate checking)
constraint_key(#typeclass_constraint{typeclass = Name, type_args = TypeArgs}) ->
    {Name, [type_to_key(T) || T <- TypeArgs]}.

%% Convert type to a key for comparison
type_to_key(#primitive_type{name = Name}) ->
    {primitive, Name};
type_to_key(#dependent_type{name = Name, params = Params}) ->
    {dependent, Name, [type_to_key(P) || P <- Params]};
type_to_key(Type) ->
    Type.
