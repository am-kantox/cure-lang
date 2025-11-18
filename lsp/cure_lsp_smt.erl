%% LSP SMT Integration - Type Constraint Extraction and Verification
-module(cure_lsp_smt).

-export([
    extract_type_constraints/1,
    extract_function_constraints/1,
    extract_dependent_type_constraints/1,
    verify_refinement_types/1,
    check_exhaustiveness/1,
    generate_counter_example/1,
    suggest_type_annotations/1,

    % Refinement type verification
    verify_refinement_subtyping/3,
    check_refinement_constraint/3,
    verify_function_preconditions/2,
    verify_function_postconditions/2,

    % Incremental verification
    init_verification_state/0,
    verify_document_incremental/2,
    invalidate_cache/2,

    % Diagnostics
    refinement_violation_to_diagnostic/1,
    generate_code_actions/2
]).

-include("../src/parser/cure_ast.hrl").

%% ============================================================================
%% Type Constraint Extraction
%% ============================================================================

%% @doc Extract all type constraints from AST for SMT solving
extract_type_constraints(#module_def{items = Items}) ->
    lists:flatmap(fun extract_item_constraints/1, Items);
extract_type_constraints(_) ->
    [].

extract_item_constraints(#function_def{} = FuncDef) ->
    extract_function_constraints(FuncDef);
extract_item_constraints(#fsm_def{state_defs = StateDefs}) ->
    Transitions = lists:flatmap(
        fun(#state_def{transitions = Trans}) -> Trans end,
        StateDefs
    ),
    lists:flatmap(fun extract_transition_constraints/1, Transitions);
extract_item_constraints(_) ->
    [].

%% @doc Extract constraints from function definition
extract_function_constraints(#function_def{
    name = Name,
    params = Params,
    return_type = RetType,
    body = Body,
    location = _Loc
}) ->
    % Parameter constraints
    ParamConstraints = lists:flatmap(fun extract_param_type_constraints/1, Params),

    % Return type constraints
    RetConstraints =
        case RetType of
            undefined -> [];
            _ -> extract_return_type_constraints(RetType, Body)
        end,

    % Body constraints
    BodyConstraints = extract_expression_constraints(Body),

    % Dependent type constraints
    DepConstraints = extract_dependent_constraints(Name, Params, RetType, Body),

    ParamConstraints ++ RetConstraints ++ BodyConstraints ++ DepConstraints.

extract_param_type_constraints(#param{name = Name, type = Type, location = _Loc}) ->
    case Type of
        undefined ->
            [];
        #dependent_type{name = _TypeName, params = _Params} ->
            % Create SMT constraint for dependent type parameters
            % For now, simplified - actual implementation would extract constraints from params
            [];
        #primitive_type{name = TypeName} ->
            % Basic type constraint
            [
                cure_smt_solver:equality_constraint(
                    cure_smt_solver:variable_term(list_to_atom(atom_to_list(Name) ++ "_type")),
                    cure_smt_solver:constant_term(TypeName)
                )
            ];
        _ ->
            []
    end;
extract_param_type_constraints(_) ->
    [].

extract_return_type_constraints(RetType, Body) ->
    % Match return type with inferred type from body
    InferredType = infer_expression_type(Body),
    case InferredType of
        unknown ->
            [];
        _ ->
            % Generate constraint that declared type equals inferred type
            [type_equality_constraint(RetType, InferredType, return_value)]
    end.

extract_expression_constraints(#let_expr{bindings = Bindings, body = Body}) ->
    BindingConstraints = lists:flatmap(fun extract_binding_constraints/1, Bindings),
    BodyConstraints = extract_expression_constraints(Body),
    BindingConstraints ++ BodyConstraints;
extract_expression_constraints(#match_expr{expr = Expr, patterns = Patterns}) ->
    ExprConstraints = extract_expression_constraints(Expr),
    PatternConstraints = lists:flatmap(fun extract_pattern_constraints/1, Patterns),
    ExhaustivenessConstraints = check_pattern_exhaustiveness(Patterns),
    ExprConstraints ++ PatternConstraints ++ ExhaustivenessConstraints;
extract_expression_constraints(#function_call_expr{function = Func, args = Args}) ->
    FuncConstraints = extract_expression_constraints(Func),
    ArgConstraints = lists:flatmap(fun extract_expression_constraints/1, Args),
    FuncConstraints ++ ArgConstraints;
extract_expression_constraints(#binary_op_expr{op = Op, left = Left, right = Right}) ->
    LeftConstraints = extract_expression_constraints(Left),
    RightConstraints = extract_expression_constraints(Right),
    OpConstraint = binary_op_to_smt_constraint(Op, Left, Right),
    LeftConstraints ++ RightConstraints ++ [OpConstraint];
extract_expression_constraints(#block_expr{expressions = Exprs}) ->
    lists:flatmap(fun extract_expression_constraints/1, Exprs);
extract_expression_constraints(_) ->
    [].

extract_binding_constraints(#binding{pattern = Pattern, value = Value}) ->
    ValueConstraints = extract_expression_constraints(Value),
    % Pattern constraints could be extracted here if needed
    % For now, simplified
    _PatternName =
        case Pattern of
            #identifier_pattern{name = N} -> N;
            _ -> unknown
        end,
    ValueConstraints.

extract_pattern_constraints(#match_clause{pattern = Pattern, guard = Guard, body = Body}) ->
    PatternConstraints = pattern_to_smt_constraints(Pattern),
    GuardConstraints =
        case Guard of
            undefined -> [];
            _ -> guard_to_smt_constraints(Guard)
        end,
    BodyConstraints = extract_expression_constraints(Body),
    PatternConstraints ++ GuardConstraints ++ BodyConstraints.

%% @doc Extract dependent type constraints (length-indexed vectors, etc.)
extract_dependent_type_constraints(#dependent_type{
    name = _TypeName,
    params = Params
}) ->
    % Extract constraints from type parameters
    ParamConstraints = lists:flatmap(fun extract_type_param_constraints/1, Params),
    ParamConstraints;
extract_dependent_type_constraints(_) ->
    [].

extract_type_param_constraints({Name, Constraint}) ->
    case Constraint of
        {gt, Value} ->
            [
                cure_smt_solver:inequality_constraint(
                    cure_smt_solver:variable_term(Name),
                    '>',
                    cure_smt_solver:constant_term(Value)
                )
            ];
        {gte, Value} ->
            [
                cure_smt_solver:inequality_constraint(
                    cure_smt_solver:variable_term(Name),
                    '>=',
                    cure_smt_solver:constant_term(Value)
                )
            ];
        {eq, Value} ->
            [
                cure_smt_solver:equality_constraint(
                    cure_smt_solver:variable_term(Name),
                    cure_smt_solver:constant_term(Value)
                )
            ];
        _ ->
            []
    end;
extract_type_param_constraints(_) ->
    [].

extract_dependent_constraints(_FuncName, Params, _RetType, Body) ->
    % For functions with dependent types, extract constraints on type indices
    % Example: safe_tail(xs: List(T, n)) -> List(T, n-1) where n > 0
    case has_dependent_params(Params) of
        false ->
            [];
        true ->
            % Extract length/size constraints from patterns
            lists:flatmap(
                fun(Param) ->
                    extract_dependent_param_constraints(Param, Body)
                end,
                Params
            )
    end.

has_dependent_params(Params) ->
    lists:any(
        fun(#param{type = Type}) ->
            is_dependent_type(Type)
        end,
        Params
    ).

is_dependent_type(#dependent_type{}) -> true;
is_dependent_type(#list_type{length = L}) when L =/= undefined -> true;
is_dependent_type(_) -> false.

extract_dependent_param_constraints(#param{name = Name, type = Type}, Body) ->
    case Type of
        #list_type{length = LengthVar} when LengthVar =/= undefined ->
            % Extract list length constraints from pattern matching
            extract_list_length_constraints(Name, LengthVar, Body);
        #dependent_type{params = Params} ->
            % Extract dependent type parameter constraints
            lists:flatmap(fun extract_type_param_constraints/1, Params);
        _ ->
            []
    end.

extract_list_length_constraints(ListName, LengthVar, Body) ->
    % Find pattern matching on the list and generate constraints
    case Body of
        #match_expr{expr = #identifier_expr{name = Name}, patterns = Patterns} when
            Name =:= ListName
        ->
            lists:flatmap(
                fun(#match_clause{pattern = Pattern}) ->
                    cure_smt_solver:infer_pattern_length_constraint(Pattern, LengthVar)
                end,
                Patterns
            );
        _ ->
            []
    end.

extract_transition_constraints(_Transition) ->
    % FSM transition constraints
    [].

%% ============================================================================
%% Refinement Type Verification
%% ============================================================================

%% @doc Verify refinement type predicates using SMT
verify_refinement_types(#module_def{items = Items}) ->
    lists:flatmap(fun verify_item_refinements/1, Items);
verify_refinement_types(_) ->
    [].

verify_item_refinements(#function_def{params = Params, body = Body, location = Loc}) ->
    % Check if function body satisfies refinement predicates
    % Simplified - actual refinement checking would analyze dependent type constraints
    Refinements = lists:filtermap(
        fun(#param{name = Name, type = Type}) ->
            case Type of
                #dependent_type{params = _Params} ->
                    % For now, return empty refinement
                    {true, {Name, undefined}};
                _ ->
                    false
            end
        end,
        Params
    ),

    lists:flatmap(
        fun({Name, Refinement}) ->
            verify_refinement_in_body(Name, Refinement, Body, Loc)
        end,
        Refinements
    );
verify_item_refinements(_) ->
    [].

verify_refinement_in_body(VarName, Refinement, Body, Loc) ->
    % Extract all uses of the variable
    Uses = find_variable_uses(VarName, Body),

    % For each use, verify refinement holds
    lists:filtermap(
        fun(Use) ->
            RefConstraint = refinement_to_smt_constraint(Refinement, VarName),
            UseConstraints = extract_expression_constraints(Use),

            case cure_smt_solver:solve_constraints([RefConstraint | UseConstraints]) of
                unsat ->
                    {true, #{
                        location => Loc,
                        severity => error,
                        message => iolist_to_binary(
                            io_lib:format(
                                "Refinement type violated for ~p", [VarName]
                            )
                        )
                    }};
                _ ->
                    false
            end
        end,
        Uses
    ).

find_variable_uses(VarName, Expr) ->
    case Expr of
        #identifier_expr{name = Name} when Name =:= VarName ->
            [Expr];
        #function_call_expr{args = Args} ->
            lists:flatmap(fun(Arg) -> find_variable_uses(VarName, Arg) end, Args);
        #let_expr{body = Body} ->
            find_variable_uses(VarName, Body);
        #match_expr{expr = E, patterns = Patterns} ->
            find_variable_uses(VarName, E) ++
                lists:flatmap(
                    fun(#match_clause{body = B}) ->
                        find_variable_uses(VarName, B)
                    end,
                    Patterns
                );
        #block_expr{expressions = Exprs} ->
            lists:flatmap(fun(E) -> find_variable_uses(VarName, E) end, Exprs);
        _ ->
            []
    end.

%% ============================================================================
%% Pattern Matching Exhaustiveness
%% ============================================================================

%% @doc Check if pattern matching is exhaustive using SMT
check_exhaustiveness(#match_expr{expr = Expr, patterns = Patterns}) ->
    ExprType = infer_expression_type(Expr),
    PatternTypes = [infer_pattern_type(P) || #match_clause{pattern = P} <- Patterns],

    % Create SMT constraint: is there a value of ExprType not covered by patterns?
    TypeConstraint = type_to_smt_constraint(ExprType),
    PatternConstraints = lists:map(fun pattern_type_to_smt_constraint/1, PatternTypes),

    % Negate all pattern constraints (find value NOT matching any pattern)
    NegatedPatterns = lists:map(fun cure_smt_solver:negate_constraint/1, PatternConstraints),

    % If satisfiable, pattern match is not exhaustive
    case cure_smt_solver:solve_constraints([TypeConstraint | NegatedPatterns]) of
        {sat, CounterExample} ->
            {not_exhaustive, CounterExample};
        unsat ->
            exhaustive;
        unknown ->
            unknown
    end;
check_exhaustiveness(_) ->
    unknown.

check_pattern_exhaustiveness(_Patterns) ->
    % Generate exhaustiveness check constraints
    % For now, return empty list (placeholder)
    [].

%% ============================================================================
%% Counter-Example Generation
%% ============================================================================

%% @doc Generate counter-example for failed constraint
generate_counter_example(Constraint) ->
    NegatedConstraint = cure_smt_solver:negate_constraint(Constraint),
    case cure_smt_solver:solve_constraints([NegatedConstraint]) of
        {sat, Solution} ->
            {counter_example, Solution};
        _ ->
            no_counter_example
    end.

%% ============================================================================
%% Type Inference and Annotation Suggestions
%% ============================================================================

%% @doc Suggest type annotations based on usage analysis
suggest_type_annotations(#function_def{params = Params, body = Body}) ->
    lists:filtermap(
        fun(#param{name = Name, type = Type, location = Loc}) ->
            case Type of
                undefined ->
                    InferredType = infer_param_type_from_usage(Name, Body),
                    case InferredType of
                        unknown ->
                            false;
                        _ ->
                            {true, #{
                                location => Loc,
                                param => Name,
                                suggested_type => format_type(InferredType)
                            }}
                    end;
                _ ->
                    false
            end
        end,
        Params
    );
suggest_type_annotations(_) ->
    [].

infer_param_type_from_usage(ParamName, Body) ->
    Uses = find_variable_uses(ParamName, Body),

    % Analyze how the parameter is used
    UsageTypes = lists:map(fun infer_usage_type/1, Uses),

    % Find most specific common type
    case UsageTypes of
        [] -> unknown;
        % Simplified - should find LUB of types
        [Type | _] -> Type
    end.

infer_usage_type(#identifier_expr{}) ->
    unknown;
infer_usage_type(_) ->
    unknown.

%% ============================================================================
%% Helper Functions - SMT Constraint Construction
%% ============================================================================

refinement_to_smt_constraint(Refinement, VarName) ->
    % Convert refinement predicate to SMT constraint
    % Example: x > 0 becomes inequality_constraint(x, '>', 0)
    case Refinement of
        #binary_op_expr{op = Op, left = #identifier_expr{name = N}, right = Right} when
            N =:= VarName
        ->
            RightValue = expression_to_constant(Right),
            cure_smt_solver:inequality_constraint(
                cure_smt_solver:variable_term(VarName),
                Op,
                cure_smt_solver:constant_term(RightValue)
            );
        _ ->
            % Complex refinement - placeholder
            cure_smt_solver:equality_constraint(
                cure_smt_solver:variable_term(VarName),
                cure_smt_solver:constant_term(true)
            )
    end.

binary_op_to_smt_constraint(Op, Left, Right) when Op =:= '+'; Op =:= '-'; Op =:= '*'; Op =:= '/' ->
    % Arithmetic operation constraints
    LeftTerm = expression_to_smt_term(Left),
    RightTerm = expression_to_smt_term(Right),
    cure_smt_solver:arithmetic_constraint(LeftTerm, Op, RightTerm);
binary_op_to_smt_constraint(Op, Left, Right) when
    Op =:= '=:='; Op =:= '=/='; Op =:= '<'; Op =:= '>'; Op =:= '<='; Op =:= '>='
->
    % Comparison constraints
    LeftTerm = expression_to_smt_term(Left),
    RightTerm = expression_to_smt_term(Right),
    cure_smt_solver:inequality_constraint(LeftTerm, Op, RightTerm);
binary_op_to_smt_constraint(_, _, _) ->
    % Unsupported operation
    cure_smt_solver:equality_constraint(
        cure_smt_solver:constant_term(true),
        cure_smt_solver:constant_term(true)
    ).

expression_to_smt_term(#identifier_expr{name = Name}) ->
    cure_smt_solver:variable_term(Name);
expression_to_smt_term(#literal_expr{value = Value}) when is_integer(Value) ->
    cure_smt_solver:constant_term(Value);
expression_to_smt_term(#literal_expr{value = Value}) when is_float(Value) ->
    cure_smt_solver:constant_term(Value);
expression_to_smt_term(#binary_op_expr{op = Op, left = Left, right = Right}) ->
    LeftTerm = expression_to_smt_term(Left),
    RightTerm = expression_to_smt_term(Right),
    case Op of
        '+' -> cure_smt_solver:addition_expression([LeftTerm, RightTerm]);
        '-' -> cure_smt_solver:subtraction_expression([LeftTerm, RightTerm]);
        '*' -> cure_smt_solver:multiplication_expression([LeftTerm, RightTerm]);
        '/' -> cure_smt_solver:division_expression([LeftTerm, RightTerm]);
        'mod' -> cure_smt_solver:modulo_expression([LeftTerm, RightTerm]);
        _ -> cure_smt_solver:constant_term(unknown)
    end;
expression_to_smt_term(_) ->
    cure_smt_solver:constant_term(unknown).

pattern_to_smt_constraints(Pattern) ->
    % Convert pattern to SMT constraints for pattern matching analysis
    case Pattern of
        #list_pattern{} ->
            % List pattern constraints (length, structure)
            LengthVar = cure_smt_solver:variable_term(list_length),
            cure_smt_solver:infer_pattern_length(Pattern, LengthVar);
        #tuple_pattern{elements = Elements} ->
            % Tuple structure constraints
            [
                cure_smt_solver:equality_constraint(
                    cure_smt_solver:variable_term(tuple_size),
                    cure_smt_solver:constant_term(length(Elements))
                )
            ];
        _ ->
            []
    end.

guard_to_smt_constraints(Guard) ->
    % Convert guard expression to SMT constraints
    extract_expression_constraints(Guard).

type_equality_constraint(Type1, Type2, _VarName) ->
    % Create constraint that Type1 and Type2 are equal for variable
    % Used for type unification: assert that Type1 and Type2 are equivalent
    Term1 = cure_smt_solver:constant_term(Type1),
    Term2 = cure_smt_solver:constant_term(Type2),
    cure_smt_solver:equality_constraint(Term1, Term2).

type_to_smt_constraint(Type) ->
    % Convert type to SMT constraint representing all values of that type
    cure_smt_solver:equality_constraint(
        cure_smt_solver:variable_term(type_var),
        cure_smt_solver:constant_term(Type)
    ).

pattern_type_to_smt_constraint(PatternType) ->
    % Convert pattern type to SMT constraint
    type_to_smt_constraint(PatternType).

expression_to_constant(#literal_expr{value = Value}) when
    is_integer(Value); is_float(Value); is_atom(Value)
->
    Value;
expression_to_constant(_) ->
    unknown.

%% ============================================================================
%% Type Inference
%% ============================================================================

infer_expression_type(#literal_expr{value = Value}) when is_integer(Value) ->
    int;
infer_expression_type(#literal_expr{value = Value}) when is_float(Value) ->
    float;
infer_expression_type(#literal_expr{value = Value}) when is_binary(Value) ->
    string;
infer_expression_type(#literal_expr{value = Value}) when is_atom(Value) ->
    atom;
infer_expression_type(#list_expr{}) ->
    list;
infer_expression_type(#tuple_expr{}) ->
    tuple;
infer_expression_type(#function_call_expr{function = Func}) ->
    infer_expression_type(Func);
infer_expression_type(#let_expr{body = Body}) ->
    infer_expression_type(Body);
infer_expression_type(#match_expr{patterns = []}) ->
    unknown;
infer_expression_type(#match_expr{patterns = [#match_clause{body = Body} | _]}) ->
    infer_expression_type(Body);
infer_expression_type(#block_expr{expressions = []}) ->
    unit;
infer_expression_type(#block_expr{expressions = Exprs}) ->
    infer_expression_type(lists:last(Exprs));
infer_expression_type(_) ->
    unknown.

infer_pattern_type(#literal_pattern{value = Value}) when is_integer(Value) ->
    int;
infer_pattern_type(#literal_pattern{value = Value}) when is_atom(Value) ->
    atom;
infer_pattern_type(#list_pattern{}) ->
    list;
infer_pattern_type(#tuple_pattern{}) ->
    tuple;
infer_pattern_type(_) ->
    unknown.

format_type(int) ->
    <<"Int">>;
format_type(float) ->
    <<"Float">>;
format_type(string) ->
    <<"String">>;
format_type(atom) ->
    <<"Atom">>;
format_type(list) ->
    <<"List">>;
format_type(tuple) ->
    <<"Tuple">>;
format_type(unknown) ->
    <<"_">>;
format_type(Type) when is_atom(Type) ->
    atom_to_binary(Type, utf8);
format_type(_) ->
    <<"Unknown">>.

%% ============================================================================
%% Refinement Type Verification (Phase 3 Integration)
%% ============================================================================

%% @doc Verify refinement type subtyping using Z3
verify_refinement_subtyping(Type1, Type2, Env) ->
    cure_refinement_types:check_subtype(Type1, Type2, Env).

%% @doc Check if a value satisfies a refinement constraint
check_refinement_constraint(Value, RefType, Env) ->
    cure_refinement_types:check_constraint(Value, RefType, Env).

%% @doc Verify function preconditions for refinement types
verify_function_preconditions(#function_def{params = Params} = FuncDef, CallSite) ->
    % Extract argument types from call site
    ArgTypes = extract_argument_types(CallSite),

    % Verify each argument against parameter refinement
    Results = lists:zipwith(
        fun(Param, ArgType) ->
            case is_refinement_param(Param) of
                {true, RefType} ->
                    % Check if argument type satisfies parameter refinement
                    case verify_refinement_subtyping(ArgType, RefType, #{}) of
                        {ok, true} -> ok;
                        {ok, false} -> {error, {precondition_violation, Param, ArgType}};
                        Error -> Error
                    end;
                false ->
                    ok
            end
        end,
        Params,
        ArgTypes
    ),

    % Collect errors
    Errors = [E || {error, E} <- Results],
    case Errors of
        [] -> ok;
        _ -> {error, {precondition_violations, Errors}}
    end.

%% @doc Verify function postconditions for refinement types
verify_function_postconditions(#function_def{return_type = RetType, body = Body}, Env) ->
    case is_refinement_return_type(RetType) of
        {true, RefType} ->
            % Infer return type from body
            InferredType = infer_expression_type(Body),

            % Check if inferred type satisfies return refinement
            case verify_refinement_subtyping(InferredType, RefType, Env) of
                {ok, true} -> ok;
                {ok, false} -> {error, {postcondition_violation, RefType, InferredType}};
                Error -> Error
            end;
        false ->
            ok
    end.

is_refinement_param(#param{type = Type}) ->
    % Check if parameter has refinement type
    % Simplified - would check for actual refinement type records
    case Type of
        #dependent_type{} -> {true, Type};
        _ -> false
    end.

is_refinement_return_type(Type) ->
    % Check if return type is a refinement type
    case Type of
        #dependent_type{} -> {true, Type};
        _ -> false
    end.

extract_argument_types(#function_call_expr{args = Args}) ->
    lists:map(fun infer_expression_type/1, Args);
extract_argument_types(_) ->
    [].

%% ============================================================================
%% Incremental SMT Solving (Phase 4)
%% ============================================================================

-type constraint_hash() :: integer().
-type result() :: valid | invalid | unknown.
-type uri() :: binary().
-type constraint() :: term().

-record(verification_state, {
    % Cache of verification results
    cache = #{} :: #{constraint_hash() => result()},
    % Document constraints
    doc_constraints = #{} :: #{uri() => [constraint()]},
    % Verification timestamps
    timestamps = #{} :: #{uri() => integer()},
    % Active solver process (optional, for session persistence)
    solver_pid = undefined :: pid() | undefined
}).

%% @doc Initialize verification state for incremental solving
init_verification_state() ->
    #verification_state{}.

%% @doc Verify document with incremental constraint solving
verify_document_incremental(Uri, #verification_state{} = State) ->
    % Get document timestamp
    Timestamp = erlang:system_time(millisecond),
    LastTimestamp = maps:get(Uri, State#verification_state.timestamps, 0),

    % Check if document has changed
    case Timestamp > LastTimestamp of
        true ->
            % Document changed - re-verify
            case verify_document_with_cache(Uri, State) of
                {ok, Diagnostics, NewState} ->
                    UpdatedState = NewState#verification_state{
                        timestamps = maps:put(
                            Uri, Timestamp, NewState#verification_state.timestamps
                        )
                    },
                    {ok, Diagnostics, UpdatedState};
                Error ->
                    Error
            end;
        false ->
            % Document unchanged - use cached results
            CachedDiagnostics = get_cached_diagnostics(Uri, State),
            {ok, CachedDiagnostics, State}
    end.

%% @doc Verify document using cache for unchanged constraints
verify_document_with_cache(Uri, #verification_state{cache = Cache} = State) ->
    % Extract constraints from document (placeholder)
    Constraints = extract_document_constraints(Uri),

    % Verify constraints, using cache when possible
    {Diagnostics, NewCache} = lists:foldl(
        fun(Constraint, {DiagAcc, CacheAcc}) ->
            Hash = constraint_hash(Constraint),
            case maps:get(Hash, CacheAcc, undefined) of
                undefined ->
                    % Not in cache - verify
                    case verify_constraint(Constraint) of
                        {ok, Result} ->
                            Diag = constraint_result_to_diagnostic(Constraint, Result),
                            {[Diag | DiagAcc], maps:put(Hash, Result, CacheAcc)};
                        _ ->
                            {DiagAcc, CacheAcc}
                    end;
                CachedResult ->
                    % In cache - reuse
                    Diag = constraint_result_to_diagnostic(Constraint, CachedResult),
                    {[Diag | DiagAcc], CacheAcc}
            end
        end,
        {[], Cache},
        Constraints
    ),

    NewState = State#verification_state{cache = NewCache},
    {ok, lists:reverse(Diagnostics), NewState}.

%% @doc Invalidate cache for changed document regions
invalidate_cache(Uri, #verification_state{cache = Cache, doc_constraints = DocCons} = State) ->
    % Remove constraints for this document from cache
    OldConstraints = maps:get(Uri, DocCons, []),
    NewCache = lists:foldl(
        fun(Constraint, CacheAcc) ->
            maps:remove(constraint_hash(Constraint), CacheAcc)
        end,
        Cache,
        OldConstraints
    ),

    State#verification_state{
        cache = NewCache,
        doc_constraints = maps:remove(Uri, DocCons)
    }.

extract_document_constraints(_Uri) ->
    % Placeholder - would extract constraints from parsed document
    [].

verify_constraint(_Constraint) ->
    % Placeholder - would verify using Z3
    {ok, valid}.

constraint_hash(Constraint) ->
    % Simple hash of constraint for caching
    erlang:phash2(Constraint).

get_cached_diagnostics(_Uri, _State) ->
    % Placeholder - would return cached diagnostics
    [].

constraint_result_to_diagnostic(_Constraint, _Result) ->
    % Placeholder - would convert result to LSP diagnostic
    #{}.

%% ============================================================================
%% Rich Diagnostics (Phase 4)
%% ============================================================================

%% @doc Convert refinement type violation to LSP diagnostic
refinement_violation_to_diagnostic({precondition_violation, Location, RefType, CounterEx}) ->
    #{
        range => location_to_range(Location),
        % Error
        severity => 1,
        source => <<"Cure SMT">>,
        message => format_refinement_violation(RefType, CounterEx),
        code => <<"refinement-violation">>,
        relatedInformation => [
            #{
                location => #{uri => <<"file://constraint">>, range => location_to_range(Location)},
                message => <<"Refinement constraint defined here">>
            }
        ]
    };
refinement_violation_to_diagnostic({subtype_check_failed, Type1, Type2}) ->
    #{
        % Error
        severity => 1,
        source => <<"Cure SMT">>,
        message => iolist_to_binary([
            <<"Subtyping failed: ">>,
            cure_refinement_types:format_refinement_error({subtype_check_failed, Type1, Type2})
        ]),
        code => <<"subtype-violation">>
    };
refinement_violation_to_diagnostic(Other) ->
    #{
        severity => 1,
        source => <<"Cure SMT">>,
        message => iolist_to_binary(io_lib:format("Verification failed: ~p", [Other]))
    }.

format_refinement_violation(RefType, CounterEx) ->
    iolist_to_binary([
        <<"Refinement type constraint violated\n">>,
        <<"  Required: ">>,
        cure_refinement_types:format_refinement_error(RefType),
        <<"\n">>,
        <<"  Counterexample: ">>,
        format_counterexample(CounterEx)
    ]).

format_counterexample(CounterEx) when is_map(CounterEx) ->
    Entries = [
        iolist_to_binary([atom_to_binary(K, utf8), <<" = ">>, io_lib:format("~p", [V])])
     || {K, V} <- maps:to_list(CounterEx)
    ],
    iolist_to_binary(lists:join(<<", ">>, Entries));
format_counterexample(Other) ->
    iolist_to_binary(io_lib:format("~p", [Other])).

location_to_range(#location{line = Line, column = Col}) ->
    #{
        start => #{line => max(0, Line - 1), character => max(0, Col - 1)},
        'end' => #{line => max(0, Line - 1), character => max(0, Col + 10)}
    };
location_to_range(_) ->
    #{
        start => #{line => 0, character => 0},
        'end' => #{line => 0, character => 0}
    }.

%% ============================================================================
%% Code Actions (Phase 4)
%% ============================================================================

%% @doc Generate code actions for refinement type violations
generate_code_actions({precondition_violation, Location, RefType, _CounterEx}, Uri) ->
    [
        % Quick fix: Add runtime check
        #{
            title => <<"Add constraint check">>,
            kind => <<"quickfix">>,
            diagnostics => [
                refinement_violation_to_diagnostic({precondition_violation, Location, RefType, #{}})
            ],
            edit => #{
                changes => #{
                    Uri => [
                        #{
                            range => location_to_range(Location),
                            newText => generate_constraint_check(RefType)
                        }
                    ]
                }
            }
        },
        % Quick fix: Strengthen type annotation
        #{
            title => <<"Strengthen type annotation">>,
            kind => <<"quickfix">>,
            edit => #{
                changes => #{
                    Uri => [
                        #{
                            range => location_to_range(Location),
                            newText => generate_refined_type_annotation(RefType)
                        }
                    ]
                }
            }
        }
    ];
generate_code_actions(_, _) ->
    [].

generate_constraint_check(RefType) ->
    % Generate if-check for constraint
    % Simplified - would generate proper Cure syntax
    iolist_to_binary([
        <<"if satisfies_constraint(x) then\n">>,
        <<"  % your code here\n">>,
        <<"else\n">>,
        <<"  error(\"Constraint violation: ">>,
        io_lib:format("~p", [RefType]),
        <<"\")\n">>,
        <<"end">>
    ]).

generate_refined_type_annotation(RefType) ->
    % Generate refined type annotation
    iolist_to_binary([
        <<": ">>,
        cure_refinement_types:format_refinement_error(RefType)
    ]).
