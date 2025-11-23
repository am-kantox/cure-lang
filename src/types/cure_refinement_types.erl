%% Cure Programming Language - Refinement Types with SMT Verification
%% Handles refinement types (types with logical constraints) using Z3
-module(cure_refinement_types).

-moduledoc """
# Refinement Types with SMT Verification

This module implements refinement types - types augmented with logical predicates
that are verified at compile-time using the Z3 SMT solver.

## Refinement Types

A refinement type refines a base type with a logical predicate:

```cure
type Positive = Int when x > 0
type NonZero = Int when x != 0
type Percentage = Int when x >= 0 and x =< 100
```

## Subtyping

Refinement subtyping is verified using SMT:

```
Positive <: NonZero   (proven by Z3: x > 0 => x /= 0)
```

## Features

- Extract constraints from refinement type definitions
- Verify subtyping relationships via SMT
- Check function preconditions and postconditions
- Propagate constraints through function calls
- Generate counterexamples for constraint violations

""".

-include("../parser/cure_ast.hrl").
-include("cure_refinement_types.hrl").

-export([
    % Refinement type operations
    create_refinement_type/3,
    extract_constraint/1,
    is_refinement_type/1,
    base_type/1,
    refinement_predicate/1,

    % Subtyping
    check_subtype/3,
    verify_subtype_smt/3,

    % Constraint checking
    check_constraint/3,
    verify_precondition/4,
    verify_postcondition/4,

    % Constraint propagation
    propagate_constraints/3,
    strengthen_type/3,
    weaken_type/2,

    % Utilities
    format_refinement_error/1,
    generate_counterexample/2
]).

%% ============================================================================
%% Type Definitions
%% ============================================================================

-type refinement_type() :: #refinement_type{}.

%% ============================================================================
%% Public API - Refinement Type Operations
%% ============================================================================

%% @doc Create a refinement type from base type and predicate
-spec create_refinement_type(type_expr(), atom(), expr()) -> refinement_type().
create_refinement_type(BaseType, Var, Predicate) ->
    #refinement_type{
        base_type = BaseType,
        variable = Var,
        predicate = Predicate,
        location = #location{line = 0, column = 0, file = undefined}
    }.

%% @doc Extract constraint from a refinement type
-spec extract_constraint(refinement_type()) -> {ok, expr()} | {error, term()}.
extract_constraint(#refinement_type{predicate = Pred}) ->
    {ok, Pred};
extract_constraint(_) ->
    {error, not_refinement_type}.

%% @doc Check if a type is a refinement type
-spec is_refinement_type(term()) -> boolean().
is_refinement_type(#refinement_type{}) -> true;
is_refinement_type(_) -> false.

%% @doc Get the base type of a refinement type
-spec base_type(refinement_type()) -> type_expr().
base_type(#refinement_type{base_type = Base}) -> Base.

%% @doc Get the predicate of a refinement type
-spec refinement_predicate(refinement_type()) -> expr().
refinement_predicate(#refinement_type{predicate = Pred}) -> Pred.

%% ============================================================================
%% Subtyping with SMT Verification
%% ============================================================================

%% @doc Check if Type1 is a subtype of Type2
%% Uses SMT solver to verify: constraint1 => constraint2
-spec check_subtype(term(), term(), map()) -> {ok, boolean()} | {error, term()}.
check_subtype(Type1, Type2, Env) ->
    case {is_refinement_type(Type1), is_refinement_type(Type2)} of
        {true, true} ->
            % Both are refinement types - use SMT
            verify_subtype_smt(Type1, Type2, Env);
        {true, false} ->
            % Type1 refined, Type2 not - check base types
            Base1 = base_type(Type1),
            check_base_subtype(Base1, Type2, Env);
        {false, true} ->
            % Type2 refined, Type1 not - generally false
            % unless Type1 satisfies Type2's constraint
            {ok, false};
        {false, false} ->
            % Neither refined - structural subtyping
            check_structural_subtype(Type1, Type2, Env)
    end.

%% @doc Verify subtyping using SMT solver
%% Proves: ∀x. constraint1(x) => constraint2(x)
-spec verify_subtype_smt(refinement_type(), refinement_type(), map()) ->
    {ok, boolean()} | {error, term()}.
verify_subtype_smt(
    #refinement_type{base_type = Base1, variable = Var1, predicate = Pred1},
    #refinement_type{base_type = Base2, variable = Var2, predicate = Pred2},
    Env
) ->
    % First check base types are compatible
    case check_base_subtype(Base1, Base2, Env) of
        {ok, true} ->
            % Rename Var2 to Var1 for consistency
            NormalizedPred2 = rename_variable(Pred2, Var2, Var1),

            % Use Z3 via SMT process integration
            try
                % Get base type as atom
                BaseTypeAtom = base_type_to_atom(Base1),

                % Generate SMT-LIB query using translator
                Query = cure_smt_translator:generate_refinement_subtype_query(
                    Pred1,
                    NormalizedPred2,
                    Var1,
                    BaseTypeAtom
                ),

                % Send query to Z3
                QueryBinary = iolist_to_binary(Query),
                case z3_query(QueryBinary) of
                    {ok, <<"unsat", _/binary>>} ->
                        % unsat means no counterexample exists, implication holds
                        {ok, true};
                    {ok, <<"sat", _/binary>>} ->
                        % sat means counterexample found, implication does NOT hold
                        {ok, false};
                    {ok, <<"unknown", _/binary>>} ->
                        % Conservative: can't prove it
                        {ok, false};
                    {error, Reason} ->
                        % Z3 error, conservatively return false
                        cure_utils:debug("Z3 error in subtype check: ~p~n", [Reason]),
                        {ok, false}
                end
            catch
                _:_ ->
                    % If anything fails, conservatively return false
                    {ok, false}
            end;
        {ok, false} ->
            {ok, false};
        Error ->
            Error
    end.

%% ============================================================================
%% Constraint Checking
%% ============================================================================

%% @doc Check if a value satisfies a refinement type constraint
-spec check_constraint(expr(), refinement_type(), map()) ->
    {ok, boolean()} | {error, term()}.
check_constraint(ValueExpr, #refinement_type{variable = Var, predicate = Pred}, Env) ->
    % Substitute value into predicate
    SubstitutedPred = substitute_in_expr(Pred, Var, ValueExpr),

    % Use Z3 to check if substituted predicate is satisfiable
    try
        % Generate SMT-LIB query
        Query = cure_smt_translator:generate_constraint_check_query(
            SubstitutedPred,
            SubstitutedPred,
            Env
        ),

        % Send to Z3
        QueryBinary = iolist_to_binary(Query),
        case z3_query(QueryBinary) of
            {ok, <<"sat", _/binary>>} ->
                {ok, true};
            {ok, <<"unsat", _/binary>>} ->
                {ok, false};
            {ok, <<"unknown", _/binary>>} ->
                % Conservative
                {ok, false};
            {error, _Reason} ->
                {ok, false}
        end
    catch
        _:_ ->
            % If conversion fails, conservatively return false
            {ok, false}
    end.

%% @doc Verify function precondition
%% Checks that the argument satisfies the parameter's refinement constraint
-spec verify_precondition(expr(), refinement_type(), map(), location()) ->
    ok | {error, term()}.
verify_precondition(ArgExpr, ParamType, Env, Location) ->
    case check_constraint(ArgExpr, ParamType, Env) of
        {ok, true} ->
            ok;
        {ok, false} ->
            % Generate counterexample
            case generate_counterexample(ArgExpr, ParamType) of
                {ok, CounterEx} ->
                    {error, {precondition_violation, Location, ParamType, CounterEx}};
                _ ->
                    {error, {precondition_violation, Location, ParamType, no_counterexample}}
            end;
        {error, Reason} ->
            {error, {precondition_check_failed, Reason}}
    end.

%% @doc Verify function postcondition
%% Checks that the return value satisfies the return type's refinement constraint
-spec verify_postcondition(expr(), refinement_type(), map(), location()) ->
    ok | {error, term()}.
verify_postcondition(ReturnExpr, ReturnType, Env, Location) ->
    verify_precondition(ReturnExpr, ReturnType, Env, Location).

%% ============================================================================
%% Constraint Propagation
%% ============================================================================

%% @doc Propagate constraints through expressions
%% When we know x: Positive in context, propagate this to uses of x
-spec propagate_constraints(expr(), map(), map()) -> map().
propagate_constraints(Expr, Env, ConstraintMap) ->
    % Walk expression tree and collect constraints
    collect_constraints(Expr, Env, ConstraintMap).

collect_constraints(#identifier_expr{name = Name}, Env, ConstraintMap) ->
    % Look up type and add constraint if it's a refinement type
    case cure_types:lookup_env(Env, Name) of
        RefType when is_record(RefType, refinement_type) ->
            % Extract constraint from refinement type
            Constraint = RefType#refinement_type.predicate,
            maps:put(Name, Constraint, ConstraintMap);
        undefined ->
            ConstraintMap;
        _ ->
            ConstraintMap
    end;
collect_constraints(#binary_op_expr{left = L, right = R}, Env, ConstraintMap) ->
    Map1 = collect_constraints(L, Env, ConstraintMap),
    collect_constraints(R, Env, Map1);
collect_constraints(#function_call_expr{args = Args}, Env, ConstraintMap) ->
    lists:foldl(
        fun(Arg, Acc) -> collect_constraints(Arg, Env, Acc) end,
        ConstraintMap,
        Args
    );
collect_constraints(_, _, ConstraintMap) ->
    ConstraintMap.

%% @doc Strengthen a type with an additional constraint
%% Example: Int -> Int when x > 0 (adding positivity constraint)
-spec strengthen_type(type_expr(), expr(), atom()) -> refinement_type().
strengthen_type(BaseType, AdditionalConstraint, Var) ->
    create_refinement_type(BaseType, Var, AdditionalConstraint).

%% @doc Weaken a refinement type by removing constraints
-spec weaken_type(refinement_type(), [atom()]) -> type_expr().
weaken_type(#refinement_type{base_type = Base}, _ConstraintsToRemove) ->
    % For now, just return base type
    % In full implementation, would selectively remove constraints
    Base.

%% ============================================================================
%% Utilities
%% ============================================================================

%% @doc Format a refinement type error message
-spec format_refinement_error(term()) -> binary().
format_refinement_error({precondition_violation, _Loc, Type, CounterEx}) ->
    iolist_to_binary([
        <<"Refinement type violation\n">>,
        <<"  Required: ">>,
        format_refinement_type(Type),
        <<"\n">>,
        <<"  Counterexample: ">>,
        format_counterexample(CounterEx)
    ]);
format_refinement_error({subtype_check_failed, Type1, Type2}) ->
    iolist_to_binary([
        <<"Subtyping check failed\n">>,
        <<"  ">>,
        format_refinement_type(Type1),
        <<" is not a subtype of ">>,
        format_refinement_type(Type2)
    ]);
format_refinement_error(Other) ->
    iolist_to_binary(io_lib:format("~p", [Other])).

%% @doc Generate a counterexample for constraint violation
-spec generate_counterexample(expr(), refinement_type()) ->
    {ok, map()} | {error, term()}.
generate_counterexample(ValueExpr, #refinement_type{variable = Var, predicate = Pred}) ->
    % Try to find a counterexample using Z3
    try
        % Build a query that asks Z3 to find a value that violates the constraint
        % (assert (not predicate))
        NegatedPred = negate_predicate(Pred),
        SubstitutedPred = substitute_in_expr(NegatedPred, Var, ValueExpr),

        Query = cure_smt_translator:generate_model_query(
            SubstitutedPred,
            SubstitutedPred,
            #{}
        ),

        QueryBinary = iolist_to_binary(Query),
        case z3_query_with_model(QueryBinary) of
            {ok, Model} when map_size(Model) > 0 ->
                {ok, Model};
            {ok, _EmptyModel} ->
                % No model available, return placeholder
                {ok, #{Var => unknown}};
            {error, _Reason} ->
                {ok, #{Var => unknown}}
        end
    catch
        _:_ ->
            % Fallback to placeholder
            {ok, #{Var => unknown}}
    end.

%% @doc Negate a predicate expression for counterexample generation
negate_predicate(#binary_op_expr{op = '>', left = L, right = R} = _Pred) ->
    % x > n becomes x <= n
    #binary_op_expr{op = '<=', left = L, right = R, location = #location{}};
negate_predicate(#binary_op_expr{op = '>=', left = L, right = R} = _Pred) ->
    #binary_op_expr{op = '<', left = L, right = R, location = #location{}};
negate_predicate(#binary_op_expr{op = '<', left = L, right = R} = _Pred) ->
    #binary_op_expr{op = '>=', left = L, right = R, location = #location{}};
negate_predicate(#binary_op_expr{op = '<=', left = L, right = R} = _Pred) ->
    #binary_op_expr{op = '>', left = L, right = R, location = #location{}};
negate_predicate(#binary_op_expr{op = '==', left = L, right = R} = _Pred) ->
    #binary_op_expr{op = '!=', left = L, right = R, location = #location{}};
negate_predicate(#binary_op_expr{op = '!=', left = L, right = R} = _Pred) ->
    #binary_op_expr{op = '==', left = L, right = R, location = #location{}};
negate_predicate(#binary_op_expr{op = 'and', left = L, right = R} = _Pred) ->
    % !(A && B) = !A || !B (De Morgan)
    #binary_op_expr{
        op = 'or',
        left = negate_predicate(L),
        right = negate_predicate(R),
        location = #location{}
    };
negate_predicate(#binary_op_expr{op = 'or', left = L, right = R} = _Pred) ->
    % !(A || B) = !A && !B (De Morgan)
    #binary_op_expr{
        op = 'and',
        left = negate_predicate(L),
        right = negate_predicate(R),
        location = #location{}
    };
negate_predicate(Expr) ->
    % Fallback: wrap in unary not
    #unary_op_expr{op = 'not', operand = Expr, location = #location{}}.

%% ============================================================================
%% Helper Functions
%% ============================================================================

%% Execute a Z3 query and return result
z3_query(QueryBinary) ->
    % Start a Z3 solver with 5 second timeout
    case cure_smt_process:start_solver(z3, 5000) of
        {ok, Pid} ->
            try
                % Execute query
                Result = cure_smt_process:execute_query(Pid, QueryBinary, 5000),
                % Stop solver
                cure_smt_process:stop_solver(Pid),
                % Process result
                case Result of
                    {unsat, _} -> {ok, <<"unsat">>};
                    {sat, _} -> {ok, <<"sat">>};
                    {unknown, _} -> {ok, <<"unknown">>};
                    {error, Reason} -> {error, Reason}
                end
            catch
                _:Error ->
                    cure_smt_process:stop_solver(Pid),
                    {error, Error}
            end;
        {error, Reason} ->
            {error, Reason}
    end.

%% Execute a Z3 query and extract model for counterexample
z3_query_with_model(QueryBinary) ->
    case cure_smt_process:start_solver(z3, 5000) of
        {ok, Pid} ->
            try
                % Execute query with (check-sat) and (get-model)
                Result = cure_smt_process:execute_query(Pid, QueryBinary, 5000),
                Model =
                    case Result of
                        {sat, ModelData} ->
                            % Parse model from Z3 output
                            cure_smt_parser:parse_model(ModelData);
                        _ ->
                            {ok, #{}}
                    end,
                cure_smt_process:stop_solver(Pid),
                Model
            catch
                _:Error ->
                    cure_smt_process:stop_solver(Pid),
                    {error, Error}
            end;
        {error, Reason} ->
            {error, Reason}
    end.

%% Check structural subtyping (non-refined types)
check_structural_subtype(Type1, Type2, _Env) ->
    % Simplified structural subtyping
    case {Type1, Type2} of
        {Same, Same} -> {ok, true};
        _ -> {ok, false}
    end.

%% Check base type compatibility
check_base_subtype(Base1, Base2, _Env) ->
    case {Base1, Base2} of
        {Same, Same} -> {ok, true};
        {#primitive_type{name = N}, #primitive_type{name = N}} -> {ok, true};
        _ -> {ok, false}
    end.

%% Rename variable in expression
rename_variable(Expr, OldVar, NewVar) ->
    rename_var_in_expr(Expr, OldVar, NewVar).

rename_var_in_expr(#identifier_expr{name = OldVar} = Expr, OldVar, NewVar) ->
    Expr#identifier_expr{name = NewVar};
rename_var_in_expr(#binary_op_expr{left = L, right = R} = Expr, OldVar, NewVar) ->
    Expr#binary_op_expr{
        left = rename_var_in_expr(L, OldVar, NewVar),
        right = rename_var_in_expr(R, OldVar, NewVar)
    };
rename_var_in_expr(#unary_op_expr{operand = Op} = Expr, OldVar, NewVar) ->
    Expr#unary_op_expr{operand = rename_var_in_expr(Op, OldVar, NewVar)};
rename_var_in_expr(Expr, _OldVar, _NewVar) ->
    Expr.

%% Substitute value into expression
substitute_in_expr(Expr, Var, Value) ->
    substitute_expr(Expr, Var, Value).

substitute_expr(#identifier_expr{name = Var}, Var, Value) ->
    Value;
substitute_expr(#binary_op_expr{left = L, right = R} = Expr, Var, Value) ->
    Expr#binary_op_expr{
        left = substitute_expr(L, Var, Value),
        right = substitute_expr(R, Var, Value)
    };
substitute_expr(#unary_op_expr{operand = Op} = Expr, Var, Value) ->
    Expr#unary_op_expr{operand = substitute_expr(Op, Var, Value)};
substitute_expr(Expr, _Var, _Value) ->
    Expr.

%% Convert base type to SMT type atom
base_type_to_smt_type(#primitive_type{name = 'Int'}) -> int;
base_type_to_smt_type(#primitive_type{name = 'Bool'}) -> bool;
base_type_to_smt_type(#primitive_type{name = 'Real'}) -> real;
% Default
base_type_to_smt_type(_) -> int.

%% Convert base type to atom for SMT translation
base_type_to_atom(#primitive_type{name = 'Int'}) -> int;
base_type_to_atom(#primitive_type{name = 'Bool'}) -> bool;
base_type_to_atom(#primitive_type{name = 'Real'}) -> real;
base_type_to_atom(#primitive_type{name = 'Float'}) -> real;
% Default
base_type_to_atom(_) -> int.

%% Extract type environment from expression
extract_type_env(_Expr, _Env) ->
    % Simplified - would extract variable types
    #{}.

%% Format refinement type for display
format_refinement_type(#refinement_type{base_type = Base, variable = Var, predicate = Pred}) ->
    BaseName = format_type(Base),
    PredStr = format_expr(Pred),
    iolist_to_binary([BaseName, <<" when ">>, atom_to_binary(Var, utf8), <<" ">>, PredStr]);
format_refinement_type(Type) ->
    iolist_to_binary(io_lib:format("~p", [Type])).

format_type(#primitive_type{name = Name}) ->
    atom_to_binary(Name, utf8);
format_type(Type) ->
    iolist_to_binary(io_lib:format("~p", [Type])).

format_expr(#binary_op_expr{op = Op, left = L, right = R}) ->
    iolist_to_binary([
        format_expr(L),
        <<" ">>,
        atom_to_binary(Op, utf8),
        <<" ">>,
        format_expr(R)
    ]);
format_expr(#identifier_expr{name = Name}) ->
    atom_to_binary(Name, utf8);
format_expr(#literal_expr{value = Val}) ->
    iolist_to_binary(io_lib:format("~p", [Val]));
format_expr(Expr) ->
    iolist_to_binary(io_lib:format("~p", [Expr])).

format_counterexample(Model) when is_map(Model) ->
    Entries = [
        iolist_to_binary([atom_to_binary(K, utf8), <<" = ">>, io_lib:format("~p", [V])])
     || {K, V} <- maps:to_list(Model)
    ],
    iolist_to_binary(lists:join(<<", ">>, Entries));
format_counterexample(Other) ->
    iolist_to_binary(io_lib:format("~p", [Other])).

%% ============================================================================
%% SMT Constraint Conversion
%% ============================================================================

%% Convert Cure AST expression to SMT constraint
expr_to_smt_constraint(#binary_op_expr{op = Op, left = L, right = R}) when
    Op =:= '>' orelse Op =:= '<' orelse Op =:= '>=' orelse Op =:= '=<' orelse
        Op =:= '=' orelse Op =:= '/='
->
    LeftTerm = expr_to_smt_term(L),
    RightTerm = expr_to_smt_term(R),
    cure_smt_solver:arithmetic_constraint(LeftTerm, Op, RightTerm);
expr_to_smt_constraint(#binary_op_expr{op = 'and', left = L, right = R}) ->
    % Build AND constraint
    LC = expr_to_smt_constraint(L),
    RC = expr_to_smt_constraint(R),
    % For now, just return the left constraint (simplified)
    % Full implementation would combine constraints properly
    LC;
expr_to_smt_constraint(#binary_op_expr{op = 'or', left = L, right = _R}) ->
    % Build OR constraint (simplified - just use left)
    expr_to_smt_constraint(L);
expr_to_smt_constraint(_) ->
    % Unknown expression, create trivial true constraint
    cure_smt_solver:equality_constraint(
        cure_smt_solver:constant_term(1),
        cure_smt_solver:constant_term(1)
    ).

%% Convert Cure AST expression to SMT term
expr_to_smt_term(#identifier_expr{name = Name}) ->
    cure_smt_solver:variable_term(Name);
expr_to_smt_term(#literal_expr{value = Val}) ->
    cure_smt_solver:constant_term(Val);
expr_to_smt_term(#binary_op_expr{op = '+', left = L, right = R}) ->
    LeftTerm = expr_to_smt_term(L),
    RightTerm = expr_to_smt_term(R),
    cure_smt_solver:addition_expression([LeftTerm, RightTerm]);
expr_to_smt_term(#binary_op_expr{op = '-', left = L, right = R}) ->
    LeftTerm = expr_to_smt_term(L),
    RightTerm = expr_to_smt_term(R),
    cure_smt_solver:subtraction_expression([LeftTerm, RightTerm]);
expr_to_smt_term(#binary_op_expr{op = '*', left = L, right = R}) ->
    LeftTerm = expr_to_smt_term(L),
    RightTerm = expr_to_smt_term(R),
    cure_smt_solver:multiplication_expression([LeftTerm, RightTerm]);
expr_to_smt_term(#binary_op_expr{op = '/', left = L, right = R}) ->
    LeftTerm = expr_to_smt_term(L),
    RightTerm = expr_to_smt_term(R),
    cure_smt_solver:division_expression([LeftTerm, RightTerm]);
expr_to_smt_term(_) ->
    cure_smt_solver:constant_term(0).
