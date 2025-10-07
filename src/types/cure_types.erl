%% Cure Programming Language - Type System Core
%% Dependent type system with constraint solving and inference
-module(cure_types).

-export([
    % Type operations
    new_type_var/0, new_type_var/1,
    is_type_var/1, occurs_check/2,
    
    % Type unification  
    unify/2, unify/3,
    
    % Type environment
    new_env/0, extend_env/3, lookup_env/2,
    
    % Type inference
    infer_type/2, infer_type/3,
    
    % Type checking
    check_type/3, check_type/4,
    
    % Constraint solving
    solve_constraints/1, solve_constraints/2,
    
    % Utility functions
    substitute/2, normalize_type/1,
    type_to_string/1
]).

%% Type variable counter for generating unique type variables
-define(TYPE_VAR_COUNTER, cure_type_var_counter).

%% Type definitions
-record(type_var, {
    id :: integer(),
    name :: atom() | undefined,
    constraints :: [term()]
}).

-record(type_param, {name, bound = any, value}).

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

-type constraint_op() :: '=' | '<:' | '>:' | 'elem_of' | 'length_eq'.
-type type_expr() :: term().
-type location() :: term().
-type type_env() :: #type_env{}.
-type type_var() :: #type_var{}.
-type type_constraint() :: #type_constraint{}.

-record(inference_result, {
    type :: type_expr(),
    constraints :: [type_constraint()],
    substitution :: #{type_var() => type_expr()}
}).

%% Built-in types
-define(TYPE_INT, {primitive_type, 'Int'}).
-define(TYPE_FLOAT, {primitive_type, 'Float'}).  
-define(TYPE_STRING, {primitive_type, 'String'}).
-define(TYPE_BOOL, {primitive_type, 'Bool'}).
-define(TYPE_ATOM, {primitive_type, 'Atom'}).

%% Dependent types
-define(TYPE_NAT, {refined_type, 'Int', fun(N) -> N >= 0 end}).
-define(TYPE_POS, {refined_type, 'Int', fun(N) -> N > 0 end}).

%% Type variable generation
new_type_var() ->
    new_type_var(undefined).

new_type_var(Name) ->
    Counter = case get(?TYPE_VAR_COUNTER) of
        undefined -> 0;
        N -> N
    end,
    put(?TYPE_VAR_COUNTER, Counter + 1),
    #type_var{
        id = Counter,
        name = Name,
        constraints = []
    }.

is_type_var(#type_var{}) -> true;
is_type_var(_) -> false.

%% Occurs check for infinite types
occurs_check(#type_var{id = Id}, Type) ->
    occurs_check_impl(Id, Type).

occurs_check_impl(Id, #type_var{id = Id}) -> true;
occurs_check_impl(Id, {function_type, Params, Return}) ->
    lists:any(fun(P) -> occurs_check_impl(Id, P) end, Params) orelse
    occurs_check_impl(Id, Return);
occurs_check_impl(Id, {dependent_type, _, Params}) ->
    lists:any(fun(#type_param{value = V}) -> 
        occurs_check_impl(Id, V) 
    end, Params);
occurs_check_impl(Id, {list_type, ElemType, LenExpr}) ->
    occurs_check_impl(Id, ElemType) orelse
    case LenExpr of
        undefined -> false;
        _ -> occurs_check_impl(Id, LenExpr)
    end;
occurs_check_impl(_, _) -> false.

%% Type Environment Operations
new_env() ->
    #type_env{
        bindings = #{},
        constraints = [],
        parent = undefined
    }.

extend_env(Env = #type_env{bindings = Bindings}, Var, Type) ->
    Env#type_env{bindings = maps:put(Var, Type, Bindings)}.

lookup_env(#type_env{bindings = Bindings, parent = Parent}, Var) ->
    case maps:get(Var, Bindings, undefined) of
        undefined when Parent =/= undefined ->
            lookup_env(Parent, Var);
        Result ->
            Result
    end.

%% Type Unification
unify(Type1, Type2) ->
    unify(Type1, Type2, #{}).

unify(Type1, Type2, Subst) ->
    unify_impl(apply_substitution(Type1, Subst), 
               apply_substitution(Type2, Subst), 
               Subst).

unify_impl(T, T, Subst) -> 
    {ok, Subst};

unify_impl(Var = #type_var{id = Id}, Type, Subst) ->
    case occurs_check(Var, Type) of
        true -> {error, {occurs_check_failed, Var, Type}};
        false -> {ok, maps:put(Id, Type, Subst)}
    end;

unify_impl(Type, Var = #type_var{}, Subst) ->
    unify_impl(Var, Type, Subst);

unify_impl({primitive_type, Name1}, {primitive_type, Name2}, Subst) 
    when Name1 =:= Name2 ->
    {ok, Subst};

unify_impl({function_type, Params1, Return1}, 
          {function_type, Params2, Return2}, Subst) ->
    case length(Params1) =:= length(Params2) of
        false -> {error, {arity_mismatch, length(Params1), length(Params2)}};
        true ->
            case unify_lists(Params1, Params2, Subst) of
                {ok, Subst1} ->
                    unify_impl(Return1, Return2, Subst1);
                Error -> Error
            end
    end;

unify_impl({list_type, Elem1, Len1}, {list_type, Elem2, Len2}, Subst) ->
    case unify_impl(Elem1, Elem2, Subst) of
        {ok, Subst1} ->
            unify_lengths(Len1, Len2, Subst1);
        Error -> Error
    end;

unify_impl({dependent_type, Name1, Params1}, 
          {dependent_type, Name2, Params2}, Subst) 
    when Name1 =:= Name2, length(Params1) =:= length(Params2) ->
    unify_type_params(Params1, Params2, Subst);

unify_impl(Type1, Type2, _Subst) ->
    {error, {unification_failed, Type1, Type2}}.

%% Helper functions for unification
unify_lists([], [], Subst) -> {ok, Subst};
unify_lists([H1|T1], [H2|T2], Subst) ->
    case unify_impl(H1, H2, Subst) of
        {ok, Subst1} -> unify_lists(T1, T2, Subst1);
        Error -> Error
    end.

unify_lengths(undefined, undefined, Subst) -> {ok, Subst};
unify_lengths(Len1, Len2, Subst) when Len1 =/= undefined, Len2 =/= undefined ->
    % For now, just check if they're the same expression
    % In a full implementation, we'd need constraint solving here
    case expr_equal(Len1, Len2) of
        true -> {ok, Subst};
        false -> {error, {length_mismatch, Len1, Len2}}
    end;
unify_lengths(_, _, Subst) -> {ok, Subst}.

unify_type_params([], [], Subst) -> {ok, Subst};
unify_type_params([#type_param{value = V1}|T1], 
                 [#type_param{value = V2}|T2], Subst) ->
    case unify_impl(V1, V2, Subst) of
        {ok, Subst1} -> unify_type_params(T1, T2, Subst1);
        Error -> Error
    end.

%% Expression equality (simplified)
expr_equal(Expr1, Expr2) ->
    % Simplified structural equality - would need full expression comparison
    Expr1 =:= Expr2.

%% Apply substitution to types
apply_substitution(#type_var{id = Id}, Subst) ->
    case maps:get(Id, Subst, undefined) of
        undefined -> #type_var{id = Id};
        Type -> apply_substitution(Type, Subst)
    end;

apply_substitution({function_type, Params, Return}, Subst) ->
    {function_type, 
     [apply_substitution(P, Subst) || P <- Params],
     apply_substitution(Return, Subst)};

apply_substitution({list_type, ElemType, LenExpr}, Subst) ->
    {list_type, 
     apply_substitution(ElemType, Subst),
     case LenExpr of
         undefined -> undefined;
         _ -> apply_substitution_to_expr(LenExpr, Subst)
     end};

apply_substitution({dependent_type, Name, Params}, Subst) ->
    {dependent_type, Name,
     [P#type_param{value = apply_substitution(P#type_param.value, Subst)} 
      || P <- Params]};

apply_substitution(Type, _Subst) ->
    Type.

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
                    infer_binary_op(Op, LeftType, RightType, Location, 
                                   LeftConstraints ++ RightConstraints);
                Error -> Error
            end;
        Error -> Error
    end;

infer_expr({function_call_expr, Function, Args, Location}, Env) ->
    case infer_expr(Function, Env) of
        {ok, FuncType, FuncConstraints} ->
            case infer_args(Args, Env) of
                {ok, ArgTypes, ArgConstraints} ->
                    ReturnType = new_type_var(),
                    ExpectedFuncType = {function_type, ArgTypes, ReturnType},
                    UnifyConstraint = #type_constraint{
                        left = FuncType,
                        op = '=',
                        right = ExpectedFuncType,
                        location = Location
                    },
                    AllConstraints = FuncConstraints ++ ArgConstraints ++ [UnifyConstraint],
                    {ok, ReturnType, AllConstraints};
                Error -> Error
            end;
        Error -> Error
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
                            AllConstraints = CondConstraints ++ ThenConstraints ++ 
                                           ElseConstraints ++ [BoolConstraint, UnifyConstraint],
                            {ok, ThenType, AllConstraints};
                        Error -> Error
                    end;
                Error -> Error
            end;
        Error -> Error
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
                        Error -> Error
                    end;
                Error -> Error
            end
    end;

infer_expr({match_expr, MatchExpr, Patterns, Location}, Env) ->
    case infer_expr(MatchExpr, Env) of
        {ok, MatchType, MatchConstraints} ->
            case infer_match_clauses(Patterns, MatchType, Env) of
                {ok, ResultType, ClauseConstraints} ->
                    {ok, ResultType, MatchConstraints ++ ClauseConstraints};
                Error -> Error
            end;
        Error -> Error
    end;

infer_expr(Expr, _Env) ->
    {error, {unsupported_expression, Expr}}.

%% Helper functions for type inference
infer_literal_type(N) when is_integer(N) -> ?TYPE_INT;
infer_literal_type(F) when is_float(F) -> ?TYPE_FLOAT;
infer_literal_type(S) when is_list(S) -> ?TYPE_STRING;
infer_literal_type(B) when is_boolean(B) -> ?TYPE_BOOL;
infer_literal_type(A) when is_atom(A) -> ?TYPE_ATOM.

infer_binary_op('+', LeftType, RightType, Location, Constraints) ->
    NumConstraints = [
        #type_constraint{left = LeftType, op = '=', right = ?TYPE_INT, location = Location},
        #type_constraint{left = RightType, op = '=', right = ?TYPE_INT, location = Location}
    ],
    {ok, ?TYPE_INT, Constraints ++ NumConstraints};

infer_binary_op('-', LeftType, RightType, Location, Constraints) ->
    NumConstraints = [
        #type_constraint{left = LeftType, op = '=', right = ?TYPE_INT, location = Location},
        #type_constraint{left = RightType, op = '=', right = ?TYPE_INT, location = Location}
    ],
    {ok, ?TYPE_INT, Constraints ++ NumConstraints};

infer_binary_op('*', LeftType, RightType, Location, Constraints) ->
    NumConstraints = [
        #type_constraint{left = LeftType, op = '=', right = ?TYPE_INT, location = Location},
        #type_constraint{left = RightType, op = '=', right = ?TYPE_INT, location = Location}
    ],
    {ok, ?TYPE_INT, Constraints ++ NumConstraints};

infer_binary_op('==', LeftType, RightType, Location, Constraints) ->
    EqualityConstraint = #type_constraint{
        left = LeftType,
        op = '=',
        right = RightType,
        location = Location
    },
    {ok, ?TYPE_BOOL, Constraints ++ [EqualityConstraint]};

infer_binary_op('>', LeftType, RightType, Location, Constraints) ->
    NumConstraints = [
        #type_constraint{left = LeftType, op = '=', right = ?TYPE_INT, location = Location},
        #type_constraint{left = RightType, op = '=', right = ?TYPE_INT, location = Location}
    ],
    {ok, ?TYPE_BOOL, Constraints ++ NumConstraints};

infer_binary_op('<', LeftType, RightType, Location, Constraints) ->
    NumConstraints = [
        #type_constraint{left = LeftType, op = '=', right = ?TYPE_INT, location = Location},
        #type_constraint{left = RightType, op = '=', right = ?TYPE_INT, location = Location}
    ],
    {ok, ?TYPE_BOOL, Constraints ++ NumConstraints};

infer_binary_op('>=', LeftType, RightType, Location, Constraints) ->
    NumConstraints = [
        #type_constraint{left = LeftType, op = '=', right = ?TYPE_INT, location = Location},
        #type_constraint{left = RightType, op = '=', right = ?TYPE_INT, location = Location}
    ],
    {ok, ?TYPE_BOOL, Constraints ++ NumConstraints};

infer_binary_op('=<', LeftType, RightType, Location, Constraints) ->
    NumConstraints = [
        #type_constraint{left = LeftType, op = '=', right = ?TYPE_INT, location = Location},
        #type_constraint{left = RightType, op = '=', right = ?TYPE_INT, location = Location}
    ],
    {ok, ?TYPE_BOOL, Constraints ++ NumConstraints};

infer_binary_op(Op, _LeftType, _RightType, Location, _Constraints) ->
    {error, {unsupported_binary_operator, Op, Location}}.

infer_args([], _Env) -> {ok, [], []};
infer_args([Arg | RestArgs], Env) ->
    case infer_expr(Arg, Env) of
        {ok, ArgType, ArgConstraints} ->
            case infer_args(RestArgs, Env) of
                {ok, RestTypes, RestConstraints} ->
                    {ok, [ArgType | RestTypes], ArgConstraints ++ RestConstraints};
                Error -> Error
            end;
        Error -> Error
    end.

infer_let_expr([], Body, Env, Constraints) ->
    case infer_expr(Body, Env) of
        {ok, BodyType, BodyConstraints} ->
            {ok, BodyType, Constraints ++ BodyConstraints};
        Error -> Error
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
                Error -> Error
            end;
        Error -> Error
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
        Error -> Error
    end.

infer_match_clauses([], _MatchType, _Env) ->
    % No patterns - should not happen in valid code
    {error, no_match_patterns};
infer_match_clauses([{match_clause, Pattern, Guard, Body, _Location}], MatchType, Env) ->
    % Single pattern - infer its type and body type
    case infer_pattern_type(Pattern, MatchType, Env) of
        {ok, PatternEnv, PatternConstraints} ->
            % Check guard if present
            GuardConstraints = case Guard of
                undefined -> [];
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
                        {error, _} -> []
                    end
            end,
            % Infer body type in pattern environment
            case infer_expr(Body, PatternEnv) of
                {ok, BodyType, BodyConstraints} ->
                    AllConstraints = PatternConstraints ++ GuardConstraints ++ BodyConstraints,
                    {ok, BodyType, AllConstraints};
                Error -> Error
            end;
        Error -> Error
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
                Error -> Error
            end;
        Error -> Error
    end.

infer_pattern_type({list_pattern, Elements, Tail, _Location} = Pattern, MatchType, Env) ->
    % For list patterns, create environment with pattern variables and length constraints
    case infer_list_pattern_elements(Elements, Tail, MatchType, Env, []) of
        {ok, PatternEnv, Constraints} ->
            % Add length constraints from SMT solver for dependent types
            LengthConstraints = case MatchType of
                {dependent_type, 'List', [TypeParam, LengthParam]} ->
                    % Generate SMT constraints for pattern matching on dependent lists
                    cure_smt_solver:infer_pattern_length_constraint(Pattern, extract_length_var(LengthParam));
                {list_type, _ElemType, {dependent_length, LengthVar}} ->
                    cure_smt_solver:infer_pattern_length(Pattern, cure_smt_solver:variable_term(LengthVar));
                _ -> []
            end,
            SMTConstraints = [convert_smt_to_type_constraint(C) || C <- LengthConstraints],
            {ok, PatternEnv, Constraints ++ SMTConstraints};
        Error -> Error
    end;
infer_pattern_type({identifier_pattern, Name, _Location}, MatchType, Env) ->
    % Add identifier to environment with the match type
    NewEnv = extend_env(Env, Name, MatchType),
    {ok, NewEnv, []};
infer_pattern_type({wildcard_pattern, _Location}, _MatchType, Env) ->
    % Wildcard doesn't bind any variables
    {ok, Env, []};
infer_pattern_type(_Pattern, _MatchType, Env) ->
    % For other patterns, return env unchanged for now
    {ok, Env, []}.

infer_list_pattern_elements([], undefined, _MatchType, Env, Constraints) ->
    {ok, Env, Constraints};
infer_list_pattern_elements([], Tail, MatchType, Env, Constraints) ->
    % Handle tail pattern - preserve dependent type structure for lists
    TailType = case MatchType of
        {dependent_type, 'List', [TypeParam, LengthParam]} ->
            % Create new dependent type for tail with reduced length
            NewLengthVar = create_derived_length_var(LengthParam, "tail"),
            {dependent_type, 'List', [TypeParam, #type_param{value = {identifier_expr, NewLengthVar, undefined}}]};
        _ ->
            {list_type, new_type_var(), undefined}
    end,
    case infer_pattern_type(Tail, TailType, Env) of
        {ok, NewEnv, TailConstraints} ->
            {ok, NewEnv, Constraints ++ TailConstraints};
        Error -> Error
    end;
infer_list_pattern_elements([Element | RestElements], Tail, MatchType, Env, Constraints) ->
    ElemType = case MatchType of
        {dependent_type, 'List', [TypeParam, _]} -> extract_type_param_value(TypeParam);
        _ -> new_type_var()
    end,
    case infer_pattern_type(Element, ElemType, Env) of
        {ok, NewEnv, ElemConstraints} ->
            infer_list_pattern_elements(RestElements, Tail, MatchType, NewEnv, Constraints ++ ElemConstraints);
        Error -> Error
    end.

%% Type checking (simplified)
check_type(Expr, ExpectedType, Env) ->
    check_type(Expr, ExpectedType, Env, []).

check_type(Expr, ExpectedType, Env, Constraints) ->
    case infer_type(Expr, Env, Constraints) of
        {ok, #inference_result{type = InferredType}} ->
            case unify(InferredType, ExpectedType) of
                {ok, _Subst} -> ok;
                {error, Reason} -> {error, {type_mismatch, ExpectedType, InferredType, Reason}}
            end;
        Error -> Error
    end.

%% Constraint solving with SMT solver integration
solve_constraints(Constraints) ->
    solve_constraints(Constraints, #{}).

solve_constraints([], Subst) -> {ok, Subst};
solve_constraints(Constraints, Subst) when length(Constraints) > 0 ->
    % Temporarily use simple constraint solving while debugging dependent types
    solve_constraints_simple(Constraints, Subst).

solve_constraints_simple([], Subst) -> {ok, Subst};
solve_constraints_simple([Constraint | RestConstraints], Subst) ->
    case solve_constraint(Constraint, Subst) of
        {ok, NewSubst} ->
            solve_constraints_simple(RestConstraints, NewSubst);
        Error -> Error
    end.

solve_type_constraints([], Subst) -> {ok, Subst};
solve_type_constraints([Constraint | RestConstraints], Subst) ->
    case solve_constraint(Constraint, Subst) of
        {ok, NewSubst} ->
            solve_type_constraints(RestConstraints, NewSubst);
        Error -> Error
    end.

solve_constraint(#type_constraint{left = Left, op = '=', right = Right}, Subst) ->
    unify(Left, Right, Subst);
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
partition_constraints([#type_constraint{op = Op} = C | Rest], TypeConstraints, ArithConstraints) 
  when Op =:= '>' orelse Op =:= '<' orelse Op =:= '>=' orelse Op =:= '=<' orelse Op =:= '/=' ->
    % Arithmetic constraints
    partition_constraints(Rest, TypeConstraints, [C | ArithConstraints]);
partition_constraints([C | Rest], TypeConstraints, ArithConstraints) ->
    % Type constraints
    partition_constraints(Rest, [C | TypeConstraints], ArithConstraints).

solve_arithmetic_constraints([], _TypeSubst) ->
    {ok, #{}};
solve_arithmetic_constraints(ArithmeticConstraints, TypeSubst) ->
    % Convert type constraints to SMT constraints and solve
    case convert_to_smt_constraints(ArithmeticConstraints) of
        {ok, SmtConstraints} ->
            case cure_smt_solver:solve_constraints(SmtConstraints) of
                {sat, Solution} ->
                    {ok, Solution};
                unsat ->
                    {error, unsatisfiable_constraints};
                unknown ->
                    {ok, #{}}  % Continue without solution
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
        {smt_constraint, Type, Left, Op, Right, Location} ->
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

type_to_string(?TYPE_INT) -> "Int";
type_to_string(?TYPE_FLOAT) -> "Float";
type_to_string(?TYPE_STRING) -> "String";
type_to_string(?TYPE_BOOL) -> "Bool";
type_to_string(?TYPE_ATOM) -> "Atom";
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
    "[" ++ type_to_string(ElemType) ++ "]";  % Simplified
type_to_string({dependent_type, Name, _Params}) ->
    atom_to_list(Name);  % Simplified
type_to_string(Type) ->
    io_lib:format("~p", [Type]).

%% Helper functions for dependent type pattern matching
extract_length_var(#type_param{value = {identifier_expr, VarName, _}}) ->
    VarName;
extract_length_var(_) ->
    unknown_length.

extract_type_param_value(#type_param{value = Value}) ->
    Value;
extract_type_param_value(Value) ->
    Value.

create_derived_length_var(#type_param{value = {identifier_expr, BaseVar, _}}, Suffix) ->
    list_to_atom(atom_to_list(BaseVar) ++ "_" ++ Suffix);
create_derived_length_var(_, Suffix) ->
    list_to_atom("derived_" ++ Suffix).
