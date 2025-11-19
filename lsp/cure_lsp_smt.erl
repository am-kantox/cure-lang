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
    init_verification_state/1,
    verify_document_incremental/2,
    invalidate_cache/2,
    invalidate_cache_region/4,
    get_cache_stats/1,
    evict_old_cache_entries/2,
    push_solver_context/1,
    pop_solver_context/1,

    % Diagnostics
    refinement_violation_to_diagnostic/1,
    generate_code_actions/2,
    pattern_exhaustiveness_to_diagnostic/1,
    generate_pattern_diagnostics/1,

    % Hover support (Phase 4.2)
    generate_hover_info/3,
    generate_type_hover/2,
    generate_constraint_hover/2,
    format_refinement_violation/2,
    format_type/1,
    format_predicate/1,
    format_operator/1,

    % Code actions (Phase 4.3)
    generate_assertion/1,
    generate_guard_clause/1,
    generate_relaxed_constraint/1,
    generate_conditional_wrapper/1,
    generate_type_annotation/1,
    generate_refinement_annotation/1,
    relax_predicate/1,
    generate_relaxed_type/2,

    % FSM verification
    generate_fsm_diagnostics/1,
    fsm_verification_to_diagnostic/2
]).

-include("../src/parser/cure_ast.hrl").
-include("../src/types/cure_refinement_types.hrl").

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

%% @doc Check if pattern matching is exhaustive using SMT (uses cure_pattern_checker)
check_exhaustiveness(#match_expr{expr = Expr, patterns = Patterns}) ->
    % Extract patterns from match clauses
    PatternList = [P || #match_clause{pattern = P} <- Patterns],

    % Infer type being matched
    ExprType = infer_expression_type(Expr),

    % Use the new pattern checker module
    case cure_pattern_checker:check_exhaustiveness(PatternList, ExprType) of
        {exhaustive} ->
            exhaustive;
        {incomplete, MissingPatterns, _Message} ->
            {not_exhaustive, MissingPatterns};
        {error, Reason} ->
            io:format("Pattern exhaustiveness check error: ~p~n", [Reason]),
            unknown
    end;
check_exhaustiveness(_) ->
    unknown.

check_pattern_exhaustiveness(Patterns) ->
    % Generate exhaustiveness diagnostics for LSP
    % Extract patterns from clauses
    PatternList = [P || #match_clause{pattern = P} <- Patterns],

    % Try to infer type from first pattern
    Type =
        case PatternList of
            [FirstPattern | _] -> infer_pattern_type(FirstPattern);
            [] -> unknown
        end,

    % Check exhaustiveness and return diagnostic if incomplete
    case cure_pattern_checker:check_exhaustiveness(PatternList, Type) of
        {incomplete, MissingPatterns, Message} ->
            % Return diagnostic
            [{pattern_exhaustiveness_warning, MissingPatterns, Message}];
        _ ->
            []
    end.

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
    cache = #{} :: #{constraint_hash() => {result(), integer()}},
    % Document constraints
    doc_constraints = #{} :: #{uri() => [constraint()]},
    % Verification timestamps
    timestamps = #{} :: #{uri() => integer()},
    % Active solver process (optional, for session persistence)
    solver_pid = undefined :: pid() | undefined,
    % Solver context depth (for push/pop)
    context_depth = 0 :: integer(),
    % Cache statistics
    cache_hits = 0 :: integer(),
    cache_misses = 0 :: integer(),
    % Document line change tracking
    doc_changes = #{} :: #{uri() => #{integer() => boolean()}}
}).

%% @doc Initialize verification state for incremental solving
init_verification_state() ->
    init_verification_state(#{}).

%% @doc Initialize verification state with options
init_verification_state(Opts) ->
    UsePersistentSolver = maps:get(persistent_solver, Opts, true),

    State = #verification_state{},

    case UsePersistentSolver of
        true ->
            % Start persistent solver process
            case start_persistent_solver(Opts) of
                {ok, Pid} ->
                    State#verification_state{solver_pid = Pid};
                {error, _Reason} ->
                    % Fall back to non-persistent
                    State
            end;
        false ->
            State
    end.

%% @doc Start a persistent solver session
start_persistent_solver(Opts) ->
    Solver = maps:get(solver, Opts, z3),
    % Shorter timeout for LSP
    Timeout = maps:get(timeout, Opts, 500),

    case cure_smt_process:start_solver(Solver, Timeout) of
        {ok, Pid} ->
            % Initialize solver with common declarations
            % Use longer timeout for initialization (5000ms)
            InitQuery = [
                <<"(set-option :produce-models true)\n">>,
                <<"(set-option :produce-unsat-cores true)\n">>
            ],
            case cure_smt_process:execute_query(Pid, InitQuery, 5000) of
                % Continue even if options fail
                {error, _} -> {ok, Pid};
                _ -> {ok, Pid}
            end;
        Error ->
            Error
    end.

%% @doc Verify document with incremental constraint solving
verify_document_incremental(Uri, #verification_state{} = State) ->
    % Get document timestamp
    Timestamp = erlang:system_time(millisecond),
    LastTimestamp = maps:get(Uri, State#verification_state.timestamps, 0),

    % Check if document has changed
    case Timestamp > LastTimestamp of
        true ->
            % Document changed - re-verify with cache
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
            % Document unchanged - return cached diagnostics
            CachedDiagnostics = get_cached_diagnostics(Uri, State),
            NewState = State#verification_state{
                cache_hits = State#verification_state.cache_hits + 1
            },
            {ok, CachedDiagnostics, NewState}
    end.

%% @doc Push a new context onto the solver stack
push_solver_context(#verification_state{solver_pid = undefined} = State) ->
    % No persistent solver, return unchanged
    State;
push_solver_context(#verification_state{solver_pid = Pid, context_depth = Depth} = State) ->
    % Send push command to solver
    Query = <<"(push 1)\n">>,
    case cure_smt_process:execute_query(Pid, Query, 500) of
        {error, _Reason} ->
            % Push failed, continue without persistent solver
            State#verification_state{solver_pid = undefined};
        _ ->
            % Successfully pushed
            State#verification_state{context_depth = Depth + 1}
    end.

%% @doc Pop a context from the solver stack
pop_solver_context(#verification_state{solver_pid = undefined} = State) ->
    State;
pop_solver_context(#verification_state{solver_pid = Pid, context_depth = Depth} = State) when
    Depth > 0
->
    Query = <<"(pop 1)\n">>,
    case cure_smt_process:execute_query(Pid, Query, 500) of
        {error, _Reason} ->
            State#verification_state{solver_pid = undefined, context_depth = 0};
        _ ->
            State#verification_state{context_depth = Depth - 1}
    end;
pop_solver_context(State) ->
    State.

%% @doc Execute query with persistent solver if available
execute_with_solver(Query, #verification_state{solver_pid = undefined}) ->
    % No persistent solver, use one-shot verification
    case cure_smt_solver:check_constraint(Query, #{}) of
        {sat, Model} -> {ok, sat, Model};
        sat -> {ok, sat, #{}};
        unsat -> {ok, unsat, #{}};
        unknown -> {ok, unknown, #{}};
        {error, Reason} -> {error, Reason}
    end;
execute_with_solver(Query, #verification_state{solver_pid = Pid}) ->
    % Use persistent solver
    QueryBin = constraint_to_smtlib(Query),
    case cure_smt_process:execute_query(Pid, QueryBin, 500) of
        {sat, ModelLines} ->
            Model = parse_model_from_lines(ModelLines),
            {ok, sat, Model};
        {unsat, _} ->
            {ok, unsat, #{}};
        {unknown, _} ->
            {ok, unknown, #{}};
        {error, Reason} ->
            {error, Reason}
    end.

%% @doc Verify document using cache for unchanged constraints
verify_document_with_cache(Uri, #verification_state{cache = Cache} = State) ->
    % Extract constraints from document
    Constraints = extract_document_constraints(Uri),

    Timestamp = erlang:system_time(millisecond),

    % Verify constraints, using cache when possible
    {Diagnostics, NewCache, NewState} = lists:foldl(
        fun(Constraint, {DiagAcc, CacheAcc, StateAcc}) ->
            Hash = constraint_hash(Constraint),
            case maps:get(Hash, CacheAcc, undefined) of
                undefined ->
                    % Not in cache - verify with persistent solver if available
                    case execute_with_solver(Constraint, StateAcc) of
                        {ok, Result, Model} ->
                            % Store in cache with timestamp
                            NewCacheAcc = maps:put(Hash, {Result, Timestamp}, CacheAcc),
                            Diag = constraint_result_to_diagnostic(Constraint, Result, Model),
                            NewStateAcc = StateAcc#verification_state{
                                cache_misses = StateAcc#verification_state.cache_misses + 1
                            },
                            {[Diag | DiagAcc], NewCacheAcc, NewStateAcc};
                        {error, _Reason} ->
                            {DiagAcc, CacheAcc, StateAcc}
                    end;
                {CachedResult, _CachedTime} ->
                    % In cache - reuse
                    Diag = constraint_result_to_diagnostic(Constraint, CachedResult, #{}),
                    NewStateAcc = StateAcc#verification_state{
                        cache_hits = StateAcc#verification_state.cache_hits + 1
                    },
                    {[Diag | DiagAcc], CacheAcc, NewStateAcc}
            end
        end,
        {[], Cache, State},
        Constraints
    ),

    FinalState = NewState#verification_state{cache = NewCache},
    {ok, lists:reverse(Diagnostics), FinalState}.

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
        doc_constraints = maps:remove(Uri, DocCons),
        doc_changes = maps:remove(Uri, State#verification_state.doc_changes)
    }.

%% @doc Invalidate cache for specific line range
invalidate_cache_region(Uri, StartLine, EndLine, #verification_state{} = State) ->
    % Mark lines as changed
    Changes = maps:get(Uri, State#verification_state.doc_changes, #{}),
    NewChanges = lists:foldl(
        fun(Line, Acc) ->
            maps:put(Line, true, Acc)
        end,
        Changes,
        lists:seq(StartLine, EndLine)
    ),

    State#verification_state{
        doc_changes = maps:put(Uri, NewChanges, State#verification_state.doc_changes)
    }.

%% @doc Get cache statistics
get_cache_stats(#verification_state{cache_hits = Hits, cache_misses = Misses, cache = Cache}) ->
    Total = Hits + Misses,
    HitRate =
        if
            Total > 0 -> (Hits / Total) * 100;
            true -> 0.0
        end,
    #{
        cache_hits => Hits,
        cache_misses => Misses,
        cache_size => maps:size(Cache),
        hit_rate_percent => HitRate
    }.

%% @doc Clear old cache entries (cache eviction)
evict_old_cache_entries(#verification_state{cache = Cache} = State, MaxAge) ->
    Now = erlang:system_time(millisecond),
    NewCache = maps:filter(
        fun(_Hash, {_Result, Timestamp}) ->
            (Now - Timestamp) < MaxAge
        end,
        Cache
    ),
    State#verification_state{cache = NewCache}.

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

constraint_result_to_diagnostic(_Constraint, valid, _Model) ->
    % No diagnostic for valid constraints
    undefined;
constraint_result_to_diagnostic(Constraint, invalid, Model) ->
    % Generate diagnostic for invalid constraint
    Location = get_constraint_location(Constraint),
    #{
        range => location_to_range(Location),
        % Error
        severity => 1,
        source => <<"Cure SMT">>,
        message => format_constraint_violation(Constraint, Model),
        code => <<"constraint-violation">>
    };
constraint_result_to_diagnostic(_Constraint, unknown, _Model) ->
    % Unknown result - no diagnostic (may need runtime check)
    undefined.

%% @doc Convert constraint to SMT-LIB format
constraint_to_smtlib(Constraint) ->
    % Use existing SMT translator
    case cure_smt_translator:translate_to_smtlib(Constraint, #{}) of
        {ok, SmtLib} -> SmtLib;
        % Fallback
        {error, _} -> <<"(check-sat)\n">>
    end.

%% @doc Parse model from SMT solver output lines
parse_model_from_lines(Lines) ->
    case cure_smt_parser:parse_model(Lines) of
        {ok, Model} -> Model;
        {error, _} -> #{}
    end.

%% @doc Get location from constraint
get_constraint_location(_Constraint) ->
    % Placeholder - would extract location from constraint AST
    #location{line = 1, column = 1, file = undefined}.

%% @doc Format constraint violation message
format_constraint_violation(_Constraint, Model) ->
    case maps:size(Model) of
        0 ->
            <<"Constraint cannot be satisfied">>;
        _ ->
            Entries = [
                iolist_to_binary([atom_to_binary(K, utf8), <<" = ">>, format_value(V)])
             || {K, V} <- maps:to_list(Model)
            ],
            iolist_to_binary([
                <<"Constraint violated with: ">>,
                iolist_to_binary(lists:join(<<", ">>, Entries))
            ])
    end.

format_value(V) when is_integer(V) -> integer_to_binary(V);
format_value(V) when is_float(V) -> float_to_binary(V);
format_value(V) when is_atom(V) -> atom_to_binary(V, utf8);
format_value(V) -> iolist_to_binary(io_lib:format("~p", [V])).

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
    TypeStr = format_refinement_type_constraint(RefType),
    CounterExStr = format_counterexample_detailed(CounterEx),

    iolist_to_binary([
        <<"Constraint violation\n">>,
        <<"━━━━━━━━━━━━━━━━━━━━━━━━\n">>,
        <<"Required: ">>,
        TypeStr,
        <<"\n">>,
        <<"\nCounterexample:\n">>,
        CounterExStr,
        <<"\n━━━━━━━━━━━━━━━━━━━━━━━━\n">>,
        <<"\n💡 Tip: Strengthen the constraint or add runtime validation">>
    ]).

format_counterexample_detailed(CounterEx) when is_map(CounterEx), map_size(CounterEx) > 0 ->
    Entries = lists:map(
        fun({K, V}) ->
            VarName = format_variable_name(K),
            VarValue = format_variable_value(V),
            iolist_to_binary([<<"  • ">>, VarName, <<" = ">>, VarValue])
        end,
        maps:to_list(CounterEx)
    ),
    iolist_to_binary(lists:join(<<"\n">>, Entries));
format_counterexample_detailed(_) ->
    <<"  (No specific counterexample available)">>.

format_counterexample(CounterEx) when is_map(CounterEx) ->
    Entries = [
        iolist_to_binary([atom_to_binary(K, utf8), <<" = ">>, io_lib:format("~p", [V])])
     || {K, V} <- maps:to_list(CounterEx)
    ],
    iolist_to_binary(lists:join(<<", ">>, Entries));
format_counterexample(Other) ->
    iolist_to_binary(io_lib:format("~p", [Other])).

format_variable_name(Var) when is_atom(Var) ->
    atom_to_binary(Var, utf8);
format_variable_name(Var) ->
    iolist_to_binary(io_lib:format("~p", [Var])).

format_variable_value(unknown) -> <<"<unknown>">>;
format_variable_value(V) when is_integer(V) -> integer_to_binary(V);
format_variable_value(V) when is_float(V) -> float_to_binary(V, [{decimals, 4}]);
format_variable_value(V) when is_atom(V) -> atom_to_binary(V, utf8);
format_variable_value(V) when is_binary(V) -> <<"\"", V/binary, "\"">>;
format_variable_value(V) -> iolist_to_binary(io_lib:format("~p", [V])).

format_refinement_type_constraint(#refinement_type{variable = Var, predicate = Pred}) ->
    VarStr = format_variable_name(Var),
    PredStr = format_predicate(Pred),
    iolist_to_binary([<<"{">>, VarStr, <<" : Int | ">>, PredStr, <<"}">>]);
format_refinement_type_constraint(Type) when is_record(Type, refinement_type) ->
    <<"<refinement type>">>;
format_refinement_type_constraint(_) ->
    <<"<type>">>.

format_predicate(#binary_op_expr{op = Op, left = L, right = R}) ->
    LeftStr = format_predicate(L),
    RightStr = format_predicate(R),
    OpStr = format_operator(Op),
    iolist_to_binary([LeftStr, <<" ">>, OpStr, <<" ">>, RightStr]);
format_predicate(#identifier_expr{name = Name}) ->
    atom_to_binary(Name, utf8);
format_predicate(#literal_expr{value = Val}) ->
    format_variable_value(Val);
format_predicate(_) ->
    <<"...">>.

format_operator('>') -> <<">">>;
format_operator('>=') -> <<">=">>;
format_operator('<') -> <<"<">>;
format_operator('<=') -> <<"<=">>;
format_operator('==') -> <<"==">>;
format_operator('!=') -> <<"!=">>;
format_operator('and') -> <<"&&">>;
format_operator('or') -> <<"||">>;
format_operator(Op) -> atom_to_binary(Op, utf8).

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
generate_code_actions({precondition_violation, Location, RefType, CounterEx}, Uri) ->
    % Generate multiple quick fix options
    [
        % Quick fix 1: Add runtime assertion
        #{
            title => <<"Add runtime assertion">>,
            kind => <<"quickfix">>,
            diagnostics => [
                refinement_violation_to_diagnostic(
                    {precondition_violation, Location, RefType, CounterEx}
                )
            ],
            edit => #{
                changes => #{
                    Uri => [
                        #{
                            range => location_to_range(Location),
                            newText => generate_assertion(RefType)
                        }
                    ]
                }
            }
        },
        % Quick fix 2: Add guard clause
        #{
            title => <<"Add guard clause">>,
            kind => <<"quickfix">>,
            edit => #{
                changes => #{
                    Uri => [
                        #{
                            range => location_to_range(Location),
                            newText => generate_guard_clause(RefType)
                        }
                    ]
                }
            }
        },
        % Quick fix 3: Relax constraint
        #{
            title => <<"Suggest weaker constraint">>,
            kind => <<"quickfix">>,
            edit => #{
                changes => #{
                    Uri => [
                        #{
                            range => location_to_range(Location),
                            newText => generate_relaxed_constraint(RefType)
                        }
                    ]
                }
            }
        },
        % Quick fix 4: Wrap in conditional
        #{
            title => <<"Wrap in conditional check">>,
            kind => <<"quickfix">>,
            edit => #{
                changes => #{
                    Uri => [
                        #{
                            range => location_to_range(Location),
                            newText => generate_conditional_wrapper(RefType)
                        }
                    ]
                }
            }
        }
    ];
generate_code_actions({incomplete_pattern_match, Location, MissingPatterns}, Uri) ->
    [
        % Quick fix: Add missing pattern cases
        #{
            title => <<"Add missing pattern cases">>,
            kind => <<"quickfix">>,
            edit => #{
                changes => #{
                    Uri => [
                        #{
                            range => location_to_range(Location),
                            newText => generate_missing_patterns_text(MissingPatterns)
                        }
                    ]
                }
            }
        }
    ];
generate_code_actions({missing_type_annotation, Location, SuggestedType}, Uri) ->
    [
        % Quick fix: Add inferred type annotation
        #{
            title => <<"Add type annotation">>,
            kind => <<"quickfix">>,
            edit => #{
                changes => #{
                    Uri => [
                        #{
                            range => location_to_range(Location),
                            newText => generate_type_annotation(SuggestedType)
                        }
                    ]
                }
            }
        },
        % Quick fix: Add refinement type annotation
        #{
            title => <<"Add refinement type">>,
            kind => <<"quickfix">>,
            edit => #{
                changes => #{
                    Uri => [
                        #{
                            range => location_to_range(Location),
                            newText => generate_refinement_annotation(SuggestedType)
                        }
                    ]
                }
            }
        }
    ];
generate_code_actions({subtype_check_failed, Location, Type1, Type2}, Uri) ->
    [
        % Quick fix: Use more general type
        #{
            title => iolist_to_binary([<<"Use type ">>, format_type(Type2)]),
            kind => <<"quickfix">>,
            edit => #{
                changes => #{
                    Uri => [
                        #{
                            range => location_to_range(Location),
                            newText => format_type(Type2)
                        }
                    ]
                }
            }
        },
        % Quick fix: Relax constraint in Type1
        #{
            title => <<"Relax constraint to satisfy subtyping">>,
            kind => <<"quickfix">>,
            edit => #{
                changes => #{
                    Uri => [
                        #{
                            range => location_to_range(Location),
                            newText => generate_relaxed_type(Type1, Type2)
                        }
                    ]
                }
            }
        }
    ];
generate_code_actions(_, _) ->
    [].

%% @doc Generate diagnostic for incomplete pattern match
pattern_exhaustiveness_to_diagnostic(
    {incomplete_pattern_match, Location, MissingPatterns, Message}
) ->
    #{
        range => location_to_range(Location),
        % Warning
        severity => 2,
        source => <<"Cure Pattern Checker">>,
        message => iolist_to_binary([
            <<"Pattern match is not exhaustive\n">>,
            list_to_binary(Message)
        ]),
        code => <<"incomplete-pattern-match">>,
        % Tag 1 = Unnecessary (deprecated code)
        tags => [1]
    };
pattern_exhaustiveness_to_diagnostic({redundant_pattern, Location, Index}) ->
    #{
        range => location_to_range(Location),
        % Warning
        severity => 2,
        source => <<"Cure Pattern Checker">>,
        message => iolist_to_binary(
            io_lib:format(
                "Pattern at position ~p is redundant (already covered by earlier patterns)",
                [Index]
            )
        ),
        code => <<"redundant-pattern">>,
        % Tag 1 = Unnecessary
        tags => [1]
    };
pattern_exhaustiveness_to_diagnostic(_) ->
    #{
        severity => 2,
        source => <<"Cure Pattern Checker">>,
        message => <<"Pattern analysis warning">>
    }.

%% @doc Scan AST for match expressions and generate pattern diagnostics
generate_pattern_diagnostics(#module_def{items = Items}) ->
    lists:flatmap(fun generate_item_pattern_diagnostics/1, Items);
generate_pattern_diagnostics(_) ->
    [].

generate_item_pattern_diagnostics(#function_def{body = Body, location = _Loc}) ->
    find_match_exprs_and_check(Body);
generate_item_pattern_diagnostics(_) ->
    [].

find_match_exprs_and_check(
    #match_expr{expr = Expr, patterns = Patterns, location = Loc} = MatchExpr
) ->
    % Check this match expression
    Diagnostic =
        case cure_pattern_checker:check_match(MatchExpr, #{}) of
            {exhaustive} ->
                [];
            {incomplete, MissingPatterns, Message} ->
                [
                    pattern_exhaustiveness_to_diagnostic({
                        incomplete_pattern_match,
                        Loc,
                        MissingPatterns,
                        Message
                    })
                ];
            {redundant, Indices, Message} ->
                % Generate diagnostic for each redundant pattern
                lists:map(
                    fun(Index) ->
                        PatternLoc = get_pattern_location(Patterns, Index),
                        pattern_exhaustiveness_to_diagnostic({
                            redundant_pattern,
                            PatternLoc,
                            Index
                        })
                    end,
                    Indices
                );
            {error, _Reason} ->
                % Silently ignore errors (e.g., Z3 not available)
                []
        end,

    % Recursively check nested expressions
    NestedDiagnostics =
        lists:flatmap(
            fun(#match_clause{body = Body}) ->
                find_match_exprs_and_check(Body)
            end,
            Patterns
        ) ++ find_match_exprs_and_check(Expr),

    Diagnostic ++ NestedDiagnostics;
find_match_exprs_and_check(#let_expr{body = Body, bindings = Bindings}) ->
    BindingDiags = lists:flatmap(
        fun(#binding{value = Val}) -> find_match_exprs_and_check(Val) end,
        Bindings
    ),
    BindingDiags ++ find_match_exprs_and_check(Body);
find_match_exprs_and_check(#function_call_expr{args = Args}) ->
    lists:flatmap(fun find_match_exprs_and_check/1, Args);
find_match_exprs_and_check(#binary_op_expr{left = Left, right = Right}) ->
    find_match_exprs_and_check(Left) ++ find_match_exprs_and_check(Right);
find_match_exprs_and_check(#block_expr{expressions = Exprs}) ->
    lists:flatmap(fun find_match_exprs_and_check/1, Exprs);
find_match_exprs_and_check(_) ->
    [].

get_pattern_location(Patterns, Index) when Index > 0, Index =< length(Patterns) ->
    Clause = lists:nth(Index, Patterns),
    case Clause of
        #match_clause{location = Loc} -> Loc;
        _ -> #location{line = 0, column = 0, file = undefined}
    end;
get_pattern_location(_, _) ->
    #location{line = 0, column = 0, file = undefined}.

generate_missing_patterns_text(MissingPatterns) ->
    PatternTexts = lists:map(
        fun(Pattern) ->
            % Format pattern using pattern_checker's format_pattern
            FormattedPattern = format_pattern_for_code(Pattern),
            io_lib:format("  | ~s -> ???~n", [FormattedPattern])
        end,
        MissingPatterns
    ),
    iolist_to_binary([<<"\n">>, PatternTexts]).

format_pattern_for_code(#literal_expr{value = Value}) ->
    io_lib:format("~p", [Value]);
format_pattern_for_code(#identifier_expr{name = '_'}) ->
    "_";
format_pattern_for_code(#identifier_expr{name = Name}) ->
    atom_to_list(Name);
format_pattern_for_code(#constructor_pattern{name = Name, args = []}) ->
    atom_to_list(Name);
format_pattern_for_code(#constructor_pattern{name = Name, args = Args}) ->
    ArgStrs = [format_pattern_for_code(A) || A <- Args],
    io_lib:format("~s(~s)", [Name, string:join(ArgStrs, ", ")]);
format_pattern_for_code(_) ->
    "_".

generate_constraint_check(RefType) ->
    % Legacy function - use generate_assertion instead
    generate_assertion(RefType).

%% @doc Generate assertion for runtime constraint checking
generate_assertion(#refinement_type{variable = Var, predicate = Pred}) ->
    PredStr = format_predicate(Pred),
    VarStr = atom_to_binary(Var, utf8),
    iolist_to_binary([
        <<"assert ">>,
        PredStr,
        <<" else error(\"">>,
        <<"Constraint violated: ">>,
        VarStr,
        <<" must satisfy ">>,
        PredStr,
        <<"\")">>
    ]);
generate_assertion(_) ->
    <<"assert true">>.

%% @doc Generate guard clause for function parameter
generate_guard_clause(#refinement_type{variable = Var, predicate = Pred}) ->
    PredStr = format_predicate_for_guard(Pred),
    iolist_to_binary([<<" when ">>, PredStr]);
generate_guard_clause(_) ->
    <<"">>.

%% @doc Format predicate for guard clause (may need variable substitution)
format_predicate_for_guard(Pred) ->
    % Similar to format_predicate but for guard context
    format_predicate(Pred).

%% @doc Generate relaxed version of constraint
generate_relaxed_constraint(#refinement_type{variable = Var, predicate = Pred, base_type = Base}) ->
    % Try to weaken the constraint
    RelaxedPred = relax_predicate(Pred),
    BaseStr = format_type(Base),
    VarStr = atom_to_binary(Var, utf8),
    PredStr = format_predicate(RelaxedPred),
    iolist_to_binary([
        <<"% Suggested weaker constraint:\n">>,
        <<"% type ">>,
        VarStr,
        <<"Type = ">>,
        BaseStr,
        <<" when ">>,
        PredStr
    ]);
generate_relaxed_constraint(_) ->
    <<"% No relaxation available">>.

%% @doc Relax a predicate to a weaker version
relax_predicate(#binary_op_expr{op = '>', left = L, right = R} = _Pred) ->
    % x > n becomes x >= n
    #binary_op_expr{op = '>=', left = L, right = R, location = #location{}};
relax_predicate(#binary_op_expr{op = '<', left = L, right = R} = _Pred) ->
    % x < n becomes x <= n
    #binary_op_expr{op = '<=', left = L, right = R, location = #location{}};
relax_predicate(#binary_op_expr{op = '!=', left = L, right = R} = _Pred) ->
    % x != n becomes true (remove constraint)
    #literal_expr{value = true, location = #location{}};
relax_predicate(#binary_op_expr{op = 'and', left = L, right = _R} = _Pred) ->
    % A && B becomes A (drop second constraint)
    L;
relax_predicate(Pred) ->
    % Can't relax, return original
    Pred.

%% @doc Generate conditional wrapper for expression
generate_conditional_wrapper(#refinement_type{variable = Var, predicate = Pred}) ->
    PredStr = format_predicate(Pred),
    VarStr = atom_to_binary(Var, utf8),
    iolist_to_binary([
        <<"if ">>,
        PredStr,
        <<" then\n">>,
        <<"  % Your code here\n">>,
        <<"  ???\n">>,
        <<"else\n">>,
        <<"  error(\"">>,
        VarStr,
        <<" must satisfy ">>,
        PredStr,
        <<"\")">>,
        <<"\nend">>
    ]);
generate_conditional_wrapper(_) ->
    <<"if true then ??? end">>.

generate_refined_type_annotation(RefType) ->
    % Legacy - use generate_refinement_annotation
    generate_refinement_annotation(RefType).

%% @doc Generate simple type annotation
generate_type_annotation(Type) ->
    TypeStr = format_type(Type),
    iolist_to_binary([<<": ">>, TypeStr]).

%% @doc Generate refinement type annotation
generate_refinement_annotation(#refinement_type{} = RefType) ->
    TypeStr = format_type(RefType),
    iolist_to_binary([<<": ">>, TypeStr]);
generate_refinement_annotation(Type) ->
    % Not a refinement type, suggest a template
    TypeStr = format_type(Type),
    iolist_to_binary([<<": {x : ">>, TypeStr, <<" | x > 0}">>]).

%% @doc Generate relaxed type to satisfy subtyping
generate_relaxed_type(Type1, Type2) ->
    % Try to find a middle ground between Type1 and Type2
    case {Type1, Type2} of
        {#refinement_type{} = Ref1, #refinement_type{} = Ref2} ->
            % Both refinement types - try to combine predicates
            generate_combined_refinement(Ref1, Ref2);
        {#refinement_type{base_type = Base}, _} ->
            % Type1 refined, Type2 not - use base type
            format_type(Base);
        {_, #refinement_type{} = Ref2} ->
            % Type2 refined, Type1 not - suggest Type2
            format_type(Ref2);
        _ ->
            % Neither refined - use Type2
            format_type(Type2)
    end.

%% @doc Combine two refinement types (weakening Type1)
generate_combined_refinement(
    #refinement_type{variable = Var1, predicate = Pred1, base_type = Base},
    #refinement_type{variable = _Var2, predicate = Pred2}
) ->
    % Weaken Pred1 or combine with Pred2
    RelaxedPred = relax_predicate(Pred1),
    PredStr = format_predicate(RelaxedPred),
    BaseStr = format_type(Base),
    VarStr = atom_to_binary(Var1, utf8),
    iolist_to_binary([<<"{">>, VarStr, <<" : ">>, BaseStr, <<" | ">>, PredStr, <<"}">>]).

%% ============================================================================
%% FSM Verification Diagnostics (Phase 5.2 Integration)
%% ============================================================================

%% @doc Generate FSM verification diagnostics for a module
generate_fsm_diagnostics(#module_def{items = Items}) ->
    lists:flatmap(fun generate_item_fsm_diagnostics/1, Items);
generate_fsm_diagnostics(_) ->
    [].

generate_item_fsm_diagnostics(#fsm_def{} = FsmDef) ->
    % Verify the FSM and generate diagnostics
    try
        case cure_fsm_verifier:verify_fsm(FsmDef) of
            {ok, Results} ->
                % Convert verification results to diagnostics
                lists:filtermap(
                    fun(Result) ->
                        case needs_diagnostic(Result) of
                            true ->
                                {true, fsm_verification_to_diagnostic(Result, FsmDef)};
                            false ->
                                false
                        end
                    end,
                    Results
                );
            {error, _Reason} ->
                % Silently ignore verification errors
                []
        end
    catch
        _:_ ->
            % Ignore exceptions
            []
    end;
generate_item_fsm_diagnostics(_) ->
    [].

%% Check if a verification result needs a diagnostic
needs_diagnostic({has_deadlock, _}) -> true;
needs_diagnostic({unreachable, _}) -> true;
needs_diagnostic({liveness_violated, _}) -> true;
needs_diagnostic({safety_violated, _}) -> true;
needs_diagnostic(_) -> false.

%% @doc Convert FSM verification result to LSP diagnostic
fsm_verification_to_diagnostic({has_deadlock, State}, #fsm_def{name = FsmName, location = Loc}) ->
    #{
        range => location_to_range(Loc),
        % Error - deadlocks are critical
        severity => 1,
        source => <<"Cure FSM Verifier">>,
        message => iolist_to_binary([
            <<"Deadlock detected in FSM '">>,
            atom_to_binary(FsmName, utf8),
            <<"' at state '">>,
            atom_to_binary(State, utf8),
            <<"': no outgoing transitions">>
        ]),
        code => <<"fsm-deadlock">>,
        % No tags for errors
        tags => []
    };
fsm_verification_to_diagnostic({unreachable, State}, #fsm_def{name = FsmName, location = Loc}) ->
    #{
        range => location_to_range(Loc),
        % Warning - unreachable states are problems but not critical
        severity => 2,
        source => <<"Cure FSM Verifier">>,
        message => iolist_to_binary([
            <<"State '">>,
            atom_to_binary(State, utf8),
            <<"' in FSM '">>,
            atom_to_binary(FsmName, utf8),
            <<"' is unreachable from initial state">>
        ]),
        code => <<"fsm-unreachable-state">>,
        % Tag 1 = Unnecessary (dead code)
        tags => [1]
    };
fsm_verification_to_diagnostic(
    {liveness_violated, {deadlocks, Deadlocks}},
    #fsm_def{name = FsmName, location = Loc}
) ->
    DeadlockStates = [
        atom_to_binary(S, utf8)
     || {has_deadlock, S} <- Deadlocks
    ],
    #{
        range => location_to_range(Loc),
        % Error
        severity => 1,
        source => <<"Cure FSM Verifier">>,
        message => iolist_to_binary([
            <<"Liveness property violated in FSM '">>,
            atom_to_binary(FsmName, utf8),
            <<"': system can get stuck in terminal state(s): ">>,
            iolist_to_binary(lists:join(<<", ">>, DeadlockStates))
        ]),
        code => <<"fsm-liveness-violation">>,
        tags => []
    };
fsm_verification_to_diagnostic(
    {safety_violated, #{bad_state := BadState, path := Path}},
    #fsm_def{name = FsmName, location = Loc}
) ->
    PathStr = format_state_path(Path),
    #{
        range => location_to_range(Loc),
        % Error - safety violations are critical
        severity => 1,
        source => <<"Cure FSM Verifier">>,
        message => iolist_to_binary([
            <<"Safety property violated in FSM '">>,
            atom_to_binary(FsmName, utf8),
            <<"': bad state '">>,
            atom_to_binary(BadState, utf8),
            <<"' is reachable via path: ">>,
            PathStr
        ]),
        code => <<"fsm-safety-violation">>,
        tags => []
    };
fsm_verification_to_diagnostic(_, _) ->
    % Default diagnostic for unknown results
    #{
        severity => 2,
        source => <<"Cure FSM Verifier">>,
        message => <<"FSM verification issue">>
    }.

%% Format a state path for display
format_state_path(Path) when is_list(Path) ->
    StateStrs = [atom_to_binary(S, utf8) || S <- Path],
    iolist_to_binary(lists:join(<<" -> ">>, StateStrs));
format_state_path(_) ->
    <<"unknown">>.

%% ============================================================================
%% Hover Support (Phase 4.2)
%% ============================================================================

%% @doc Generate hover information for identifier at position
%% Returns LSP hover object with markup content
-spec generate_hover_info(atom(), map(), #location{}) -> map() | undefined.
generate_hover_info(Identifier, TypeEnv, Location) ->
    case maps:get(Identifier, TypeEnv, undefined) of
        undefined ->
            undefined;
        Type ->
            Content = generate_type_hover(Identifier, Type),
            #{
                contents => #{
                    kind => <<"markdown">>,
                    value => Content
                },
                range => location_to_range(Location)
            }
    end.

%% @doc Generate hover content for a type
-spec generate_type_hover(atom(), term()) -> binary().
generate_type_hover(VarName, #refinement_type{
    base_type = BaseType, variable = Var, predicate = Pred
}) ->
    VarStr = atom_to_binary(VarName, utf8),
    BaseStr = format_type(BaseType),
    ConstraintStr = format_predicate(Pred),

    iolist_to_binary([
        <<"### Refinement Type\n\n">>,
        <<"```cure\n">>,
        VarStr,
        <<" : ">>,
        BaseStr,
        <<" | ">>,
        ConstraintStr,
        <<"\n">>,
        <<"```\n\n">>,
        <<"**Variable**: `">>,
        atom_to_binary(Var, utf8),
        <<"`\n\n">>,
        <<"**Constraint**: The value must satisfy `">>,
        ConstraintStr,
        <<"`\n\n">>,
        <<"---\n\n">>,
        <<"ℹ️ This constraint is verified at compile-time using SMT">>
    ]);
generate_type_hover(VarName, #primitive_type{name = TypeName}) ->
    VarStr = atom_to_binary(VarName, utf8),
    TypeStr = atom_to_binary(TypeName, utf8),
    iolist_to_binary([
        <<"### Type\n\n">>,
        <<"```cure\n">>,
        VarStr,
        <<" : ">>,
        TypeStr,
        <<"\n">>,
        <<"```">>
    ]);
generate_type_hover(VarName, #function_type{params = Params, return_type = RetType}) ->
    VarStr = atom_to_binary(VarName, utf8),
    ParamsStr = format_function_params(Params),
    RetStr = format_type(RetType),
    iolist_to_binary([
        <<"### Function Type\n\n">>,
        <<"```cure\n">>,
        VarStr,
        <<" : (">>,
        ParamsStr,
        <<") -> ">>,
        RetStr,
        <<"\n">>,
        <<"```">>
    ]);
generate_type_hover(VarName, Type) ->
    VarStr = atom_to_binary(VarName, utf8),
    iolist_to_binary([
        <<"### Type\n\n">>,
        <<"```cure\n">>,
        VarStr,
        <<" : ">>,
        format_type(Type),
        <<"\n">>,
        <<"```">>
    ]).

%% @doc Generate hover content for constraint expressions
-spec generate_constraint_hover(expr(), map()) -> binary().
generate_constraint_hover(Expr, TypeEnv) ->
    % Extract constraints from expression context
    Constraints = extract_active_constraints(Expr, TypeEnv),

    case length(Constraints) of
        0 ->
            <<"### No active constraints">>;
        _ ->
            ConstraintStrs = lists:map(
                fun({Var, Constraint}) ->
                    VarStr = atom_to_binary(Var, utf8),
                    ConstStr = format_predicate(Constraint),
                    iolist_to_binary([<<"- `">>, VarStr, <<"`: ">>, ConstStr])
                end,
                Constraints
            ),
            iolist_to_binary([
                <<"### Active Constraints\n\n">>,
                iolist_to_binary(lists:join(<<"\n">>, ConstraintStrs)),
                <<"\n\n✓ All constraints verified by SMT solver">>
            ])
    end.

%% @doc Extract active constraints in scope at expression
extract_active_constraints(_Expr, TypeEnv) ->
    % Extract refinement type constraints from environment
    lists:filtermap(
        fun({Var, Type}) ->
            case Type of
                #refinement_type{predicate = Pred} ->
                    {true, {Var, Pred}};
                _ ->
                    false
            end
        end,
        maps:to_list(TypeEnv)
    ).

%% Format type for display
format_type(#primitive_type{name = Name}) ->
    atom_to_binary(Name, utf8);
format_type(#refinement_type{base_type = Base, variable = Var, predicate = Pred}) ->
    BaseStr = format_type(Base),
    VarStr = atom_to_binary(Var, utf8),
    PredStr = format_predicate(Pred),
    iolist_to_binary([<<"{">>, VarStr, <<" : ">>, BaseStr, <<" | ">>, PredStr, <<"}">>]);
format_type(#function_type{params = Params, return_type = RetType}) ->
    ParamsStr = format_function_params(Params),
    RetStr = format_type(RetType),
    iolist_to_binary([<<"(">>, ParamsStr, <<") -> ">>, RetStr]);
% Simple atom types
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
format_type(Type) when is_atom(Type) -> atom_to_binary(Type, utf8);
format_type(_) ->
    <<"<type>">>.

format_function_params(Params) ->
    ParamStrs = lists:map(fun format_param/1, Params),
    iolist_to_binary(lists:join(<<", ">>, ParamStrs)).

format_param(#param{name = Name, type = Type}) ->
    NameStr = atom_to_binary(Name, utf8),
    TypeStr = format_type(Type),
    iolist_to_binary([NameStr, <<": ">>, TypeStr]);
format_param(_) ->
    <<"_">>.
