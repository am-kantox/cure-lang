%% Cure Programming Language - Guard-Based Type Refinement
%% Implements type refinement and flow-sensitive typing based on guard constraints
-module(cure_guard_refinement).

-moduledoc """
# Guard-Based Type Refinement

This module implements Phase 3 of the guard support implementation:
type system integration for guard constraints.

## Features

### Guard Constraint Extraction
Extract constraints from function guards and convert them to refinement type predicates:

```cure
def abs(x: Int): Int when x >= 0 = x
% Refines x's type to: Int when x >= 0
```

### Flow-Sensitive Type Narrowing
Within a function body, parameters have their types refined based on the guard:

```cure
def process(x: Int) when x > 0 = 
    % Here, x has type: Int when x > 0 (i.e., Positive)
    requires_positive(x)
```

### Cross-Clause Type Checking
Verify that all clauses of a multi-clause function have compatible return types:

```cure
def abs(x: Int): Int when x >= 0 = x
def abs(x: Int): Int when x < 0 = -x
% Return type unifies to: Int
```

## Integration

This module integrates with:
- `cure_refinement_types` - For creating refinement type predicates
- `cure_typechecker` - For enhancing function clause type checking
- `cure_guard_optimizer` - For guard simplification and SMT encoding
- `cure_smt_solver` - For constraint verification

## Implementation Approach

1. **Extract Guard Constraints**: Parse guard expressions to identify parameter constraints
2. **Create Refinement Types**: Convert guards to refinement type predicates
3. **Narrow Parameter Types**: Replace parameter types with refined versions in function body scope
4. **Unify Return Types**: Compute union type of all clause return types
5. **Verify Consistency**: Use SMT to check guards are consistent and complete
""".

-include("../parser/cure_ast.hrl").
-include("cure_refinement_types.hrl").

-export([
    % Guard constraint extraction
    extract_guard_constraints/1,
    extract_param_constraints/2,
    identify_constrained_params/1,

    % Type refinement
    refine_param_type/3,
    create_refinement_from_guard/3,
    narrow_param_types_in_body/3,
    create_union_refinement_type/4,
    is_disjunctive_constraint/1,
    extract_disjunctive_branches/1,

    % Cross-clause analysis
    unify_clause_return_types/2,
    check_clause_compatibility/2,
    compute_function_return_type/2,

    % Guard coverage analysis
    check_guard_coverage/2,
    find_uncovered_cases/2,
    detect_unreachable_clauses/1,

    % Flow-sensitive typing
    apply_guard_refinements/3,
    strengthen_environment/3,

    % SMT-based counterexample finding
    find_counterexamples_smt/2,
    build_guard_disjunction/1,
    negate_guard_expression/1,
    negate_comparison_op/1
]).

%% ============================================================================
%% Guard Constraint Extraction
%% ============================================================================

%% @doc Extract all constraints from a guard expression
%% Returns a list of {ParamName, Constraint} tuples
-spec extract_guard_constraints(expr()) -> [{atom(), expr()}].
extract_guard_constraints(undefined) ->
    [];
extract_guard_constraints(Guard) ->
    % Parse guard expression to find parameter constraints
    case Guard of
        #binary_op_expr{op = 'andalso', left = Left, right = Right} ->
            % AND: both constraints apply
            extract_guard_constraints(Left) ++ extract_guard_constraints(Right);
        #binary_op_expr{op = 'orelse', left = Left, right = Right} ->
            % OR: either constraint applies - create union refinement types
            LeftConstraints = extract_guard_constraints(Left),
            RightConstraints = extract_guard_constraints(Right),
            % Collect parameters that appear in either branch
            AllParams = lists:usort([Param || {Param, _} <- LeftConstraints ++ RightConstraints]),
            % For each parameter, create a union constraint combining both branches
            lists:map(
                fun(Param) ->
                    LeftConstraint =
                        case lists:keyfind(Param, 1, LeftConstraints) of
                            {_, LC} ->
                                LC;
                            false ->
                                #literal_expr{
                                    value = false, location = Guard#binary_op_expr.location
                                }
                        end,
                    RightConstraint =
                        case lists:keyfind(Param, 1, RightConstraints) of
                            {_, RC} ->
                                RC;
                            false ->
                                #literal_expr{
                                    value = false, location = Guard#binary_op_expr.location
                                }
                        end,
                    % Create union constraint: {Param, or_constraint(Left, Right)}
                    UnionConstraint = #binary_op_expr{
                        op = 'orelse',
                        left = LeftConstraint,
                        right = RightConstraint,
                        location = Guard#binary_op_expr.location
                    },
                    {Param, UnionConstraint}
                end,
                AllParams
            );
        #binary_op_expr{op = Op, left = Left, right = Right} when
            Op =:= '>';
            Op =:= '<';
            Op =:= '>=';
            Op =:= '=<';
            Op =:= '<=';
            Op =:= '==';
            Op =:= '=:=';
            Op =:= '/=';
            Op =:= '=/='
        ->
            % Comparison: extract parameter if present
            extract_comparison_constraint(Op, Left, Right, Guard);
        _ ->
            % Other guard types (type checks, etc.)
            []
    end.

%% Extract constraints from a comparison expression
extract_comparison_constraint(Op, Left, Right, FullGuard) ->
    % Check if left side is a parameter
    case {Left, Right} of
        {#identifier_expr{name = ParamName}, _} ->
            % x Op value
            [{ParamName, FullGuard}];
        {_, #identifier_expr{name = ParamName}} ->
            % value Op x (flip the constraint)
            FlippedOp = flip_comparison_op(Op),
            FlippedGuard = FullGuard#binary_op_expr{
                op = FlippedOp,
                left = Right,
                right = Left
            },
            [{ParamName, FlippedGuard}];
        {#binary_op_expr{}, #identifier_expr{name = ParamName}} ->
            % expression Op x
            [{ParamName, FullGuard}];
        {#identifier_expr{name = ParamName}, #binary_op_expr{}} ->
            % x Op expression
            [{ParamName, FullGuard}];
        _ ->
            % No direct parameter reference
            []
    end.

%% Flip comparison operators for constraint normalization
flip_comparison_op('>') -> '<';
flip_comparison_op('<') -> '>';
flip_comparison_op('>=') -> '=<';
flip_comparison_op('=<') -> '>=';
flip_comparison_op('<=') -> '>=';
flip_comparison_op('==') -> '==';
flip_comparison_op('=:=') -> '=:=';
flip_comparison_op('/=') -> '/=';
flip_comparison_op('=/=') -> '=/='.

%% @doc Extract constraints for a specific parameter from a guard
-spec extract_param_constraints(atom(), expr()) -> [expr()].
extract_param_constraints(ParamName, Guard) ->
    AllConstraints = extract_guard_constraints(Guard),
    [Constraint || {Param, Constraint} <- AllConstraints, Param =:= ParamName].

%% @doc Identify all parameters that have constraints in a guard
-spec identify_constrained_params(expr()) -> [atom()].
identify_constrained_params(Guard) ->
    Constraints = extract_guard_constraints(Guard),
    lists:usort([Param || {Param, _} <- Constraints]).

%% ============================================================================
%% Type Refinement
%% ============================================================================

%% @doc Refine a parameter's type based on guard constraint
-spec refine_param_type(atom(), type_expr(), expr()) -> type_expr().
refine_param_type(ParamName, BaseType, Guard) ->
    case extract_param_constraints(ParamName, Guard) of
        [] ->
            % No constraints for this parameter
            BaseType;
        Constraints ->
            % Create a refinement type with the constraints
            create_refinement_from_guard(ParamName, BaseType, Constraints)
    end.

%% @doc Create a refinement type from guard constraints
-spec create_refinement_from_guard(atom(), type_expr(), [expr()]) -> type_expr().
create_refinement_from_guard(ParamName, BaseType, Constraints) ->
    % Combine all constraints with AND
    CombinedPredicate = combine_constraints(Constraints),

    % Create refinement type using cure_refinement_types
    cure_refinement_types:create_refinement_type(
        BaseType,
        ParamName,
        CombinedPredicate
    ).

%% Combine multiple constraints with AND
combine_constraints([]) ->
    #literal_expr{value = true, location = #location{line = 0, column = 0, file = undefined}};
combine_constraints([Single]) ->
    Single;
combine_constraints([First | Rest]) ->
    lists:foldl(
        fun(Constraint, Acc) ->
            #binary_op_expr{
                op = 'andalso',
                left = Acc,
                right = Constraint,
                location = #location{line = 0, column = 0, file = undefined}
            }
        end,
        First,
        Rest
    ).

%% @doc Create a union refinement type from disjunctive constraints
%% Handles OR guards by creating a refinement type that accepts either constraint
-spec create_union_refinement_type(type_expr(), atom(), expr(), expr()) -> type_expr().
create_union_refinement_type(BaseType, Var, LeftConstraint, RightConstraint) ->
    % Create union constraint: either LeftConstraint OR RightConstraint
    UnionConstraint = #binary_op_expr{
        op = 'orelse',
        left = LeftConstraint,
        right = RightConstraint,
        location = #location{line = 0, column = 0, file = undefined}
    },
    cure_refinement_types:create_refinement_type(
        BaseType,
        Var,
        UnionConstraint
    ).

%% @doc Check if a constraint is a disjunctive constraint (contains orelse)
-spec is_disjunctive_constraint(expr()) -> boolean().
is_disjunctive_constraint(#binary_op_expr{op = 'orelse'}) ->
    true;
is_disjunctive_constraint(#binary_op_expr{left = Left, right = Right}) ->
    is_disjunctive_constraint(Left) orelse is_disjunctive_constraint(Right);
is_disjunctive_constraint(_) ->
    false.

%% @doc Extract left and right branches from a disjunctive constraint
-spec extract_disjunctive_branches(expr()) -> {expr(), expr()} | error.
extract_disjunctive_branches(#binary_op_expr{op = 'orelse', left = Left, right = Right}) ->
    {Left, Right};
extract_disjunctive_branches(_) ->
    error.

%% @doc Apply type refinements to parameters in function body environment
-spec narrow_param_types_in_body(map(), [#param{}], expr()) -> map().
narrow_param_types_in_body(Env, Params, Guard) ->
    % For each parameter, check if it has constraints in the guard
    lists:foldl(
        fun(Param, AccEnv) ->
            ParamName = Param#param.name,
            ParamType = Param#param.type,

            % Extract base type
            BaseType = convert_param_type_to_base(ParamType),

            % Refine type based on guard
            RefinedType = refine_param_type(ParamName, BaseType, Guard),

            % Update environment with refined type
            case RefinedType of
                BaseType ->
                    % No refinement needed
                    AccEnv;
                _ ->
                    % Replace parameter type with refined version
                    cure_types:extend_env(AccEnv, ParamName, RefinedType)
            end
        end,
        Env,
        Params
    ).

%% Convert parameter type record to base type expression
convert_param_type_to_base(undefined) ->
    {primitive_type, 'Any'};
convert_param_type_to_base(#primitive_type{name = Name}) ->
    {primitive_type, Name};
convert_param_type_to_base({primitive_type, Name}) ->
    {primitive_type, Name};
convert_param_type_to_base(Type) ->
    % Keep other types as-is
    Type.

%% ============================================================================
%% Cross-Clause Analysis
%% ============================================================================

%% @doc Unify return types from all clauses
-spec unify_clause_return_types([#function_clause{}], map()) ->
    {ok, type_expr()} | {error, term()}.
unify_clause_return_types(Clauses, Env) ->
    % Infer return type for each clause
    ReturnTypes = lists:map(
        fun(Clause) ->
            #function_clause{return_type = DeclaredType, body = Body} = Clause,
            case DeclaredType of
                undefined ->
                    % Infer from body
                    case cure_types:infer_type(Body, Env) of
                        {ok, {inferred, InferredType, _}} ->
                            {ok, InferredType};
                        {ok, InferredType} ->
                            {ok, InferredType};
                        Error ->
                            Error
                    end;
                _ ->
                    {ok, DeclaredType}
            end
        end,
        Clauses
    ),

    % Check if all succeeded
    case
        lists:all(
            fun
                ({ok, _}) -> true;
                (_) -> false
            end,
            ReturnTypes
        )
    of
        false ->
            % Some clause failed to infer
            Errors = [E || {error, _} = E <- ReturnTypes],
            {error, {clause_inference_failed, Errors}};
        true ->
            % Unify all return types
            Types = [T || {ok, T} <- ReturnTypes],
            unify_types_list(Types, Env)
    end.

%% Unify a list of types into a single type (union if needed)
unify_types_list([], _Env) ->
    {error, no_types};
unify_types_list([Single], _Env) ->
    {ok, Single};
unify_types_list([First | Rest], Env) ->
    % Try to unify with first type
    case try_unify_all(First, Rest, Env) of
        {ok, UnifiedType} ->
            {ok, UnifiedType};
        {error, _} ->
            % Can't unify - create union type
            AllTypes = [First | Rest],
            {ok, {union_type, lists:usort(AllTypes)}}
    end.

%% Try to unify all types with a base type
try_unify_all(BaseType, Types, Env) ->
    Results = lists:map(
        fun(Type) ->
            cure_types:unify(BaseType, Type, Env)
        end,
        Types
    ),
    case
        lists:all(
            fun
                ({ok, _}) -> true;
                (_) -> false
            end,
            Results
        )
    of
        true ->
            {ok, BaseType};
        false ->
            {error, incompatible_types}
    end.

%% @doc Check if two clauses are compatible (no overlap in guards)
-spec check_clause_compatibility(#function_clause{}, #function_clause{}) ->
    compatible | overlapping | unreachable.
check_clause_compatibility(Clause1, Clause2) ->
    Guard1 = Clause1#function_clause.constraint,
    Guard2 = Clause2#function_clause.constraint,

    case {Guard1, Guard2} of
        {undefined, undefined} ->
            % Both without guards - overlapping
            overlapping;
        {undefined, _} ->
            % First has no guard - second is unreachable if guards overlap
            overlapping;
        {_, undefined} ->
            % Second has no guard - compatible (catch-all)
            compatible;
        _ ->
            % Both have guards - check for overlap using SMT
            check_guard_overlap(Guard1, Guard2)
    end.

%% Check if two guards overlap (can both be true for same inputs)
check_guard_overlap(Guard1, Guard2) ->
    % Use cure_guard_optimizer to check if (Guard1 AND Guard2) is satisfiable
    try
        case cure_guard_optimizer:check_guard_implication(Guard1, Guard2) of
            true ->
                % Guard1 implies Guard2 - Guard2 is unreachable after Guard1
                unreachable;
            false ->
                % Check reverse implication
                case cure_guard_optimizer:check_guard_implication(Guard2, Guard1) of
                    true ->
                        % Guard2 implies Guard1 - they overlap
                        overlapping;
                    false ->
                        % Neither implies the other - check for satisfiability of both
                        % For now, assume compatible
                        compatible
                end;
            _ ->
                % Any other result (error, unknown, etc.) - assume compatible
                compatible
        end
    catch
        _:_ ->
            % On error, conservatively assume compatible
            compatible
    end.

%% @doc Compute final function return type from clauses
-spec compute_function_return_type([#function_clause{}], map()) ->
    {ok, type_expr()} | {error, term()}.
compute_function_return_type(Clauses, Env) ->
    unify_clause_return_types(Clauses, Env).

%% ============================================================================
%% Guard Coverage Analysis
%% ============================================================================
%% @doc Check if guards cover all possible input cases
%% Phase 4: Enhanced with SMT verification
-spec check_guard_coverage([#function_clause{}], map()) ->
    complete | {incomplete, [term()]}.
check_guard_coverage(Clauses, Env) ->
    % Phase 4: Use SMT for comprehensive completeness check
    case cure_guard_smt:verify_guard_completeness(Clauses, Env) of
        {complete, []} ->
            complete;
        {incomplete, Reasons} ->
            % Try to find concrete counterexamples
            Counterexamples = cure_guard_smt:find_uncovered_inputs(Clauses, Env),
            {incomplete, Counterexamples ++ Reasons}
    end.

%% @doc Find input cases not covered by any guard
%% Uses SMT solver to generate concrete counterexamples that fail all guards
-spec find_uncovered_cases([#function_clause{}], map()) -> [term()].
find_uncovered_cases(Clauses, Env) ->
    % Extract all guards from the clauses
    Guards = [
        C#function_clause.constraint
     || C <- Clauses,
        C#function_clause.constraint =/= undefined
    ],

    case Guards of
        [] ->
            % No guards at all - no specific uncovered cases
            [];
        _ ->
            % Use SMT to find inputs that don't match any guard
            find_counterexamples_smt(Guards, Env)
    end.

%% Use SMT solver to find counterexamples
find_counterexamples_smt(Guards, _Env) ->
    try
        % Build a query that negates all guards: ¬(G1 ∨ G2 ∨ ... ∨ Gn)
        % This finds inputs where NO guard is satisfied
        GuardDisjunction = build_guard_disjunction(Guards),
        NegatedGuards = negate_guard_expression(GuardDisjunction),

        % Generate SMT-LIB query for satisfiability of negated guards
        Query = generate_counterexample_query(NegatedGuards),

        % Send to SMT solver
        case cure_guard_smt:generate_counterexample([Guards], _Env) of
            {ok, Counterexamples} when is_list(Counterexamples) ->
                % Successfully found counterexamples
                Counterexamples;
            {ok, _} ->
                % Found but not in expected format
                [];
            {error, _} ->
                % SMT solver couldn't find counterexamples
                [];
            _ ->
                % Unknown result
                []
        end
    catch
        _:Exception ->
            % On any error, return empty list (conservative)
            cure_utils:debug("SMT counterexample search failed: ~p~n", [Exception]),
            []
    end.

%% Build a disjunction of all guards: G1 ∨ G2 ∨ ... ∨ Gn
build_guard_disjunction([]) ->
    #literal_expr{value = false, location = #location{line = 0, column = 0, file = undefined}};
build_guard_disjunction([Single]) ->
    Single;
build_guard_disjunction([First | Rest]) ->
    lists:foldl(
        fun(Guard, Acc) ->
            #binary_op_expr{
                op = 'orelse',
                left = Acc,
                right = Guard,
                location = #location{line = 0, column = 0, file = undefined}
            }
        end,
        First,
        Rest
    ).

%% Negate a guard expression: ¬expr
negate_guard_expression(#literal_expr{value = true, location = Loc}) ->
    #literal_expr{value = false, location = Loc};
negate_guard_expression(#literal_expr{value = false, location = Loc}) ->
    #literal_expr{value = true, location = Loc};
negate_guard_expression(#binary_op_expr{op = 'orelse', left = Left, right = Right, location = Loc}) ->
    % De Morgan's law: ¬(A ∨ B) = (¬A ∧ ¬B)
    #binary_op_expr{
        op = 'andalso',
        left = negate_guard_expression(Left),
        right = negate_guard_expression(Right),
        location = Loc
    };
negate_guard_expression(#binary_op_expr{op = 'andalso', left = Left, right = Right, location = Loc}) ->
    % De Morgan's law: ¬(A ∧ B) = (¬A ∨ ¬B)
    #binary_op_expr{
        op = 'orelse',
        left = negate_guard_expression(Left),
        right = negate_guard_expression(Right),
        location = Loc
    };
negate_guard_expression(#binary_op_expr{op = Op, left = Left, right = Right, location = Loc}) ->
    % Negate comparison operators
    NegOp = negate_comparison_op(Op),
    #binary_op_expr{
        op = NegOp,
        left = Left,
        right = Right,
        location = Loc
    };
negate_guard_expression(Expr) ->
    % For other expressions, wrap in NOT (handled by runtime)
    #unary_op_expr{
        op = 'not',
        operand = Expr,
        location = #location{line = 0, column = 0, file = undefined}
    }.

%% Negate comparison operators
negate_comparison_op('>') -> '=<';
negate_comparison_op('<') -> '>=';
negate_comparison_op('>=') -> '<';
negate_comparison_op('=<') -> '>';
negate_comparison_op('=:=') -> '=/=';
negate_comparison_op('=/=') -> '=:=';
negate_comparison_op('==') -> '/=';
negate_comparison_op('/=') -> '==';
negate_comparison_op(Op) -> Op.

%% Generate SMT query for finding counterexamples
generate_counterexample_query(NegatedGuards) ->
    % This would generate an SMT-LIB 2.0 query
    % For now, return placeholder that cure_guard_smt will handle
    NegatedGuards.

%% @doc Detect unreachable clauses (guards subsumed by earlier guards)
-spec detect_unreachable_clauses([#function_clause{}]) -> [integer()].
detect_unreachable_clauses(Clauses) ->
    % Check each clause against all previous clauses
    {_, Unreachable} = lists:foldl(
        fun(Clause, {PrevClauses, UnreachableAcc}) ->
            ClauseIdx = length(PrevClauses) + 1,
            IsUnreachable = lists:any(
                fun(PrevClause) ->
                    check_clause_compatibility(PrevClause, Clause) =:= unreachable
                end,
                PrevClauses
            ),
            case IsUnreachable of
                true ->
                    {PrevClauses ++ [Clause], UnreachableAcc ++ [ClauseIdx]};
                false ->
                    {PrevClauses ++ [Clause], UnreachableAcc}
            end
        end,
        {[], []},
        Clauses
    ),
    Unreachable.

%% ============================================================================
%% Flow-Sensitive Typing
%% ============================================================================

%% @doc Apply guard refinements to create a refined environment
-spec apply_guard_refinements(map(), [#param{}], expr()) -> map().
apply_guard_refinements(Env, Params, Guard) ->
    narrow_param_types_in_body(Env, Params, Guard).

%% @doc Strengthen environment with additional constraints
-spec strengthen_environment(map(), atom(), expr()) -> map().
strengthen_environment(Env, ParamName, Constraint) ->
    % Look up current type
    case cure_types:lookup_env(Env, ParamName) of
        undefined ->
            Env;
        CurrentType ->
            % Refine with additional constraint
            RefinedType = refine_param_type(ParamName, CurrentType, Constraint),
            cure_types:extend_env(Env, ParamName, RefinedType)
    end.
