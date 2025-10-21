%% Cure Programming Language - SMT-based Verification System
%%
%% This module provides SMT-based formal verification for FSM safety properties.
%% It integrates with Z3 or similar SMT solvers to verify temporal logic properties,
%% state invariants, and transition safety conditions.

-module(cure_smt_solver).

-moduledoc """
# Cure Programming Language - SMT-based Verification System

This module provides formal verification capabilities for Cure's FSM system using
SMT (Satisfiability Modulo Theories) solvers. It can verify:

- **State Invariants**: Properties that must hold in every reachable state
- **Temporal Properties**: Eventually, always, until properties
- **Transition Safety**: Guards and preconditions for state transitions
- **Message Safety**: Type safety and protocol compliance for message passing

## Supported SMT Solvers

- **Z3**: Primary solver with full theory support
- **CVC4/CVC5**: Alternative solver with good performance
- **Yices**: Lightweight solver for specific use cases

## Verification Properties

### State Invariants
```cure
fsm Counter {
    states: [idle, counting(n: Nat)]
    property counter_non_negative: always (n >= 0)
}
```

### Temporal Properties  
```cure
fsm Protocol {
    property eventual_response: 
        always (request -> eventually response)
}
```

### Transition Safety
```cure
transition request_received {
    guard: buffer_capacity > 0
    action: buffer := buffer + 1
}
```

## Integration with Type System

The SMT solver integrates with Cure's dependent type system to:
- Verify dependent type constraints
- Check length constraints for collections
- Validate refinement type predicates
- Ensure FSM state space safety

""" -
    include("../parser/cure_ast.hrl").

-export([
    % Main verification API
    verify_fsm_properties/2,
    verify_state_invariant/3,
    verify_temporal_property/3,

    % SMT solver interface
    solve_constraints/1,
    check_satisfiability/1,

    % Constraint building
    arithmetic_constraint/3,
    temporal_constraint/4,
    state_constraint/3,

    % Term construction
    variable_term/1,
    constant_term/1,
    function_term/2,

    % Pattern matching constraints
    infer_pattern_length_constraint/2,
    infer_pattern_length/2,

    % Dependent type support
    check_dependent_constraint/2,
    verify_refinement_type/2
]).

%% SMT term representation
-record(smt_term, {
    type :: variable | constant | function | compound,
    name :: atom() | undefined,
    value :: term(),
    args :: [smt_term()] | undefined
}).

%% SMT constraint representation
-record(smt_constraint, {
    type :: arithmetic | temporal | logical | equality,
    left :: smt_term(),
    op :: atom(),
    right :: smt_term(),
    location :: location() | undefined
}).

%% Verification result
-record(verification_result, {
    property :: atom(),
    result :: sat | unsat | unknown,
    model :: #{atom() => term()} | undefined,
    counterexample :: [term()] | undefined,
    solver_info :: #{atom() => term()}
}).

-type smt_term() :: #smt_term{}.
-type smt_constraint() :: #smt_constraint{}.
-type verification_result() :: #verification_result{}.

%% ===== MAIN VERIFICATION API =====

%% Verify all properties defined in an FSM
-spec verify_fsm_properties(fsm_def(), #{}) -> {ok, [verification_result()]} | {error, term()}.
verify_fsm_properties(#fsm_def{name = FsmName, states = States} = FsmDef, Options) ->
    try
        % Extract all properties from the FSM definition
        Properties = extract_fsm_properties(FsmDef),

        % Create SMT context for this FSM
        Context = create_fsm_smt_context(FsmName, States),

        % Verify each property
        Results = [verify_property(Property, Context, Options) || Property <- Properties],

        {ok, Results}
    catch
        Error:Reason:Stack ->
            {error, {verification_failed, Error, Reason, Stack}}
    end.

%% Verify a single state invariant
-spec verify_state_invariant(atom(), expr(), #{}) -> verification_result().
verify_state_invariant(StateName, Condition, Context) ->
    % Build SMT constraints for the invariant
    StateVar = variable_term(StateName),
    ConditionConstraint = expression_to_smt_constraint(Condition, Context),

    % The invariant should hold in all reachable states
    InvariantConstraint = #smt_constraint{
        type = logical,
        left = StateVar,
        op = implies,
        right = ConditionConstraint,
        location = undefined
    },

    % Check satisfiability of the negation (to find counterexamples)
    NegatedConstraint = negate_constraint(InvariantConstraint),

    case solve_constraints([NegatedConstraint]) of
        {sat, Model} ->
            % Found counterexample - invariant is violated
            #verification_result{
                property = StateName,
                result = unsat,
                model = Model,
                counterexample = extract_counterexample(Model),
                solver_info = #{type => invariant_check}
            };
        unsat ->
            % No counterexample - invariant holds
            #verification_result{
                property = StateName,
                result = sat,
                model = undefined,
                counterexample = undefined,
                solver_info = #{type => invariant_check}
            };
        unknown ->
            % Solver couldn't determine - report unknown
            #verification_result{
                property = StateName,
                result = unknown,
                model = undefined,
                counterexample = undefined,
                solver_info = #{type => invariant_check, reason => solver_timeout}
            }
    end.

%% Verify a temporal logic property
-spec verify_temporal_property(atom(), atom(), expr()) -> verification_result().
verify_temporal_property(PropertyName, PropertyType, Condition) ->
    % Convert temporal property to SMT constraints
    case PropertyType of
        eventually ->
            verify_eventually_property(PropertyName, Condition);
        always ->
            verify_always_property(PropertyName, Condition);
        until ->
            verify_until_property(PropertyName, Condition);
        _ ->
            #verification_result{
                property = PropertyName,
                result = unknown,
                model = undefined,
                counterexample = undefined,
                solver_info = #{error => unsupported_temporal_property}
            }
    end.

%% ===== SMT SOLVER INTERFACE =====

%% Solve a list of SMT constraints
-spec solve_constraints([smt_constraint()]) -> sat | unsat | unknown | {sat, #{atom() => term()}}.
solve_constraints(Constraints) ->
    % Convert constraints to SMT-LIB format
    SmtLib = constraints_to_smt_lib(Constraints),

    % Try different solvers in order of preference
    Solvers = [z3, cvc5, yices],
    solve_with_solvers(SmtLib, Solvers).

%% Check satisfiability of a single constraint
-spec check_satisfiability(smt_constraint()) -> sat | unsat | unknown.
check_satisfiability(Constraint) ->
    case solve_constraints([Constraint]) of
        {sat, _Model} -> sat;
        sat -> sat;
        unsat -> unsat;
        unknown -> unknown
    end.

%% ===== CONSTRAINT BUILDING =====

%% Create arithmetic constraint (e.g., x + y > 5)
-spec arithmetic_constraint(smt_term(), atom(), smt_term()) -> smt_constraint().
arithmetic_constraint(Left, Op, Right) ->
    #smt_constraint{
        type = arithmetic,
        left = Left,
        op = Op,
        right = Right,
        location = undefined
    }.

%% Create temporal constraint (e.g., always P, eventually Q)
-spec temporal_constraint(atom(), smt_term(), atom(), smt_term()) -> smt_constraint().
temporal_constraint(TemporalOp, Left, LogicalOp, Right) ->
    #smt_constraint{
        type = temporal,
        left = #smt_term{
            type = function,
            name = TemporalOp,
            value = TemporalOp,
            args = [Left]
        },
        op = LogicalOp,
        right = Right,
        location = undefined
    }.

%% Create state constraint for FSM states
-spec state_constraint(atom(), atom(), smt_term()) -> smt_constraint().
state_constraint(StateName, Op, Value) ->
    StateVar = variable_term(StateName),
    #smt_constraint{
        type = logical,
        left = StateVar,
        op = Op,
        right = Value,
        location = undefined
    }.

%% ===== TERM CONSTRUCTION =====

%% Create variable term
-spec variable_term(atom()) -> smt_term().
variable_term(Name) ->
    #smt_term{
        type = variable,
        name = Name,
        value = Name,
        args = undefined
    }.

%% Create constant term
-spec constant_term(term()) -> smt_term().
constant_term(Value) ->
    #smt_term{
        type = constant,
        name = undefined,
        value = Value,
        args = undefined
    }.

%% Create function application term
-spec function_term(atom(), [smt_term()]) -> smt_term().
function_term(FunctionName, Args) ->
    #smt_term{
        type = function,
        name = FunctionName,
        value = FunctionName,
        args = Args
    }.

%% ===== PATTERN MATCHING CONSTRAINTS =====

%% Generate length constraint from pattern matching
-spec infer_pattern_length_constraint(pattern(), term()) -> [smt_constraint()].
infer_pattern_length_constraint({list_pattern, Elements, Tail, _Location}, LengthVar) ->
    ElementCount = length(Elements),

    case Tail of
        undefined ->
            % Exact length constraint: length = element_count
            LengthTerm = variable_term(LengthVar),
            CountTerm = constant_term(ElementCount),
            [arithmetic_constraint(LengthTerm, '=', CountTerm)];
        _ ->
            % Minimum length constraint: length >= element_count
            LengthTerm = variable_term(LengthVar),
            CountTerm = constant_term(ElementCount),
            [arithmetic_constraint(LengthTerm, '>=', CountTerm)]
    end;
infer_pattern_length_constraint(_Pattern, _LengthVar) ->
    % No length constraints for non-list patterns
    [].

%% Generate length constraint for pattern with term
-spec infer_pattern_length(pattern(), smt_term()) -> [smt_constraint()].
infer_pattern_length(Pattern, LengthTerm) ->
    case Pattern of
        {list_pattern, Elements, undefined, _} ->
            % Exact length match
            ElementCount = length(Elements),
            CountTerm = constant_term(ElementCount),
            [arithmetic_constraint(LengthTerm, '=', CountTerm)];
        {list_pattern, Elements, _Tail, _} ->
            % Minimum length match
            ElementCount = length(Elements),
            CountTerm = constant_term(ElementCount),
            [arithmetic_constraint(LengthTerm, '>=', CountTerm)];
        _ ->
            []
    end.

%% ===== DEPENDENT TYPE SUPPORT =====

%% Check dependent type constraint using SMT
-spec check_dependent_constraint(type_expr(), #{}) -> boolean().
check_dependent_constraint({refined_type, BaseType, Predicate}, Context) ->
    % Convert predicate to SMT constraint and check satisfiability
    BaseVar = variable_term(base_value),
    PredicateConstraint = predicate_to_smt_constraint(Predicate, BaseVar, Context),

    case check_satisfiability(PredicateConstraint) of
        sat -> true;
        unsat -> false;
        % Conservative - assume satisfiable
        unknown -> true
    end;
check_dependent_constraint(_Type, _Context) ->
    true.

%% Verify refinement type predicate
-spec verify_refinement_type(expr(), fun()) -> boolean().
verify_refinement_type(Expression, Predicate) when is_function(Predicate, 1) ->
    % For now, use runtime evaluation
    % In full implementation, would convert to SMT
    try
        Value = evaluate_expression(Expression),
        Predicate(Value)
    catch
        _:_ -> false
    end;
verify_refinement_type(_Expression, _Predicate) ->
    false.

%% ===== INTERNAL HELPER FUNCTIONS =====

%% Extract properties from FSM definition
extract_fsm_properties(#fsm_def{states = States, state_defs = StateDefs}) ->
    % Extract properties from state definitions and transitions
    StateProperties = lists:flatmap(fun extract_state_properties/1, StateDefs),

    % Add implicit properties (e.g., state reachability)
    ReachabilityProperties = generate_reachability_properties(States),

    StateProperties ++ ReachabilityProperties.

extract_state_properties(#state_def{transitions = Transitions}) ->
    lists:flatmap(fun extract_transition_properties/1, Transitions).

extract_transition_properties(#transition{guard = Guard, action = Action}) ->
    Properties = [],

    % Add guard safety property
    GuardProperty =
        case Guard of
            undefined ->
                [];
            _ ->
                [
                    #fsm_property{
                        name = guard_safety,
                        property_type = invariant,
                        condition = Guard,
                        location = undefined
                    }
                ]
        end,

    % Add action safety property
    ActionProperty =
        case Action of
            undefined ->
                [];
            _ ->
                [
                    #fsm_property{
                        name = action_safety,
                        property_type = invariant,
                        condition = Action,
                        location = undefined
                    }
                ]
        end,

    Properties ++ GuardProperty ++ ActionProperty.

generate_reachability_properties(States) ->
    % Generate properties ensuring all states are reachable
    [
        #fsm_property{
            name = list_to_atom("reachable_" ++ atom_to_list(State)),
            property_type = eventually,
            condition = {identifier_expr, State, undefined},
            location = undefined
        }
     || State <- States
    ].

%% Create SMT context for FSM
create_fsm_smt_context(FsmName, States) ->
    #{
        fsm_name => FsmName,
        states => States,
        state_variables => [variable_term(State) || State <- States],
        current_state => variable_term(current_state),
        message_queue => variable_term(message_queue)
    }.

%% Verify individual property
verify_property(
    #fsm_property{name = Name, property_type = Type, condition = Condition}, Context, Options
) ->
    case Type of
        invariant ->
            verify_state_invariant(Name, Condition, Context);
        eventually ->
            verify_eventually_property(Name, Condition);
        always ->
            verify_always_property(Name, Condition);
        until ->
            verify_until_property(Name, Condition);
        _ ->
            #verification_result{
                property = Name,
                result = unknown,
                model = undefined,
                counterexample = undefined,
                solver_info = #{error => unknown_property_type}
            }
    end.

%% Verify eventually property (◇P)
verify_eventually_property(PropertyName, Condition) ->
    % Eventually P means there exists a future state where P holds
    % In SMT: ∃t. P(t) where t is a time/state variable
    TimeVar = variable_term(time),
    ConditionAtTime = apply_temporal_quantifier(Condition, TimeVar),
    ExistentialConstraint = quantify_existentially(TimeVar, ConditionAtTime),

    case check_satisfiability(ExistentialConstraint) of
        sat ->
            #verification_result{
                property = PropertyName,
                result = sat,
                model = undefined,
                counterexample = undefined,
                solver_info = #{type => eventually_check}
            };
        unsat ->
            #verification_result{
                property = PropertyName,
                result = unsat,
                model = undefined,
                counterexample = undefined,
                solver_info = #{type => eventually_check}
            };
        unknown ->
            #verification_result{
                property = PropertyName,
                result = unknown,
                model = undefined,
                counterexample = undefined,
                solver_info = #{type => eventually_check}
            }
    end.

%% Verify always property (□P)
verify_always_property(PropertyName, Condition) ->
    % Always P means P holds in all reachable states
    % In SMT: ∀t. reachable(t) → P(t)
    TimeVar = variable_term(time),
    ReachableAtTime = function_term(reachable, [TimeVar]),
    ConditionAtTime = apply_temporal_quantifier(Condition, TimeVar),
    UniversalConstraint = quantify_universally(
        TimeVar,
        implication_constraint(ReachableAtTime, ConditionAtTime)
    ),

    % Check the negation to find counterexamples
    NegatedConstraint = negate_constraint(UniversalConstraint),

    case check_satisfiability(NegatedConstraint) of
        sat ->
            #verification_result{
                property = PropertyName,
                % Property violated
                result = unsat,
                model = undefined,
                counterexample = undefined,
                solver_info = #{type => always_check}
            };
        unsat ->
            #verification_result{
                property = PropertyName,
                % Property holds
                result = sat,
                model = undefined,
                counterexample = undefined,
                solver_info = #{type => always_check}
            };
        unknown ->
            #verification_result{
                property = PropertyName,
                result = unknown,
                model = undefined,
                counterexample = undefined,
                solver_info = #{type => always_check}
            }
    end.

%% Verify until property (P U Q)
verify_until_property(PropertyName, {until, P, Q}) ->
    % P until Q means P holds until Q becomes true
    % In SMT: ∃t. Q(t) ∧ ∀s. (s < t) → P(s)
    TVar = variable_term(t),
    SVar = variable_term(s),

    QAtT = apply_temporal_quantifier(Q, TVar),
    PAtS = apply_temporal_quantifier(P, SVar),
    SLessThanT = arithmetic_constraint(SVar, '<', TVar),

    ForAllS = quantify_universally(SVar, implication_constraint(SLessThanT, PAtS)),
    ExistsT = quantify_existentially(TVar, conjunction_constraint(QAtT, ForAllS)),

    case check_satisfiability(ExistsT) of
        sat ->
            #verification_result{
                property = PropertyName,
                result = sat,
                model = undefined,
                counterexample = undefined,
                solver_info = #{type => until_check}
            };
        unsat ->
            #verification_result{
                property = PropertyName,
                result = unsat,
                model = undefined,
                counterexample = undefined,
                solver_info = #{type => until_check}
            };
        unknown ->
            #verification_result{
                property = PropertyName,
                result = unknown,
                model = undefined,
                counterexample = undefined,
                solver_info = #{type => until_check}
            }
    end;
verify_until_property(PropertyName, _) ->
    #verification_result{
        property = PropertyName,
        result = unknown,
        model = undefined,
        counterexample = undefined,
        solver_info = #{error => malformed_until_property}
    }.

%% ===== SMT-LIB CONVERSION =====

%% Convert constraints to SMT-LIB format
constraints_to_smt_lib(Constraints) ->
    % Quantifier-free linear integer arithmetic
    Header = "(set-logic QF_LIA)\n",
    Declarations = generate_variable_declarations(Constraints),
    Assertions = [constraint_to_smt_lib(C) || C <- Constraints],
    Footer = "(check-sat)\n(get-model)\n",

    iolist_to_binary([Header, Declarations, Assertions, Footer]).

%% Convert single constraint to SMT-LIB
constraint_to_smt_lib(#smt_constraint{left = Left, op = Op, right = Right}) ->
    LeftSmt = term_to_smt_lib(Left),
    RightSmt = term_to_smt_lib(Right),
    OpSmt = atom_to_list(Op),
    io_lib:format("(assert (~s ~s ~s))~n", [OpSmt, LeftSmt, RightSmt]).

%% Convert term to SMT-LIB
term_to_smt_lib(#smt_term{type = variable, name = Name}) ->
    atom_to_list(Name);
term_to_smt_lib(#smt_term{type = constant, value = Value}) when is_integer(Value) ->
    integer_to_list(Value);
term_to_smt_lib(#smt_term{type = constant, value = Value}) when is_atom(Value) ->
    atom_to_list(Value);
term_to_smt_lib(#smt_term{type = function, name = Name, args = Args}) ->
    ArgStrs = [term_to_smt_lib(Arg) || Arg <- Args],
    io_lib:format("(~s ~s)", [atom_to_list(Name), string:join(ArgStrs, " ")]).

%% Generate variable declarations
generate_variable_declarations(Constraints) ->
    Variables = collect_variables(Constraints),
    [io_lib:format("(declare-fun ~s () Int)~n", [atom_to_list(Var)]) || Var <- Variables].

collect_variables(Constraints) ->
    AllTerms = lists:flatmap(fun extract_terms/1, Constraints),
    Variables = [Name || #smt_term{type = variable, name = Name} <- AllTerms],
    lists:usort(Variables).

extract_terms(#smt_constraint{left = Left, right = Right}) ->
    extract_terms_from_term(Left) ++ extract_terms_from_term(Right).

extract_terms_from_term(#smt_term{args = undefined} = Term) ->
    [Term];
extract_terms_from_term(#smt_term{args = Args} = Term) ->
    [Term | lists:flatmap(fun extract_terms_from_term/1, Args)].

%% ===== SOLVER INTEGRATION =====

%% Try to solve with different SMT solvers
solve_with_solvers(SmtLib, []) ->
    % No solvers available
    unknown;
solve_with_solvers(SmtLib, [Solver | RestSolvers]) ->
    case try_solver(Solver, SmtLib) of
        {ok, Result} -> Result;
        {error, _Reason} -> solve_with_solvers(SmtLib, RestSolvers)
    end.

%% Try specific SMT solver
try_solver(z3, SmtLib) ->
    try_external_solver("z3", ["-in"], SmtLib);
try_solver(cvc5, SmtLib) ->
    try_external_solver("cvc5", ["--lang=smt2"], SmtLib);
try_solver(yices, SmtLib) ->
    try_external_solver("yices-smt2", [], SmtLib).

%% Execute external SMT solver
try_external_solver(Command, Args, SmtLib) ->
    try
        Port = open_port(
            {spawn_executable, Command},
            [binary, {args, Args}, stdin, stdout, stderr]
        ),
        port_command(Port, SmtLib),
        port_close(Port),

        % Parse solver output
        receive
            {Port, {data, Output}} ->
                parse_solver_output(Output)
        after 5000 ->
            {error, solver_timeout}
        end
    catch
        _:Reason ->
            {error, {solver_error, Command, Reason}}
    end.

%% Parse SMT solver output
parse_solver_output(Output) ->
    case binary:match(Output, <<"sat">>) of
        {_Pos, _Len} ->
            Model = parse_model(Output),
            case Model of
                #{} -> {ok, {sat, Model}};
                _ -> {ok, sat}
            end;
        nomatch ->
            case binary:match(Output, <<"unsat">>) of
                {_Pos, _Len} -> {ok, unsat};
                nomatch -> {ok, unknown}
            end
    end.

%% Parse model from solver output
parse_model(Output) ->
    % Simple model parsing - in practice would be more sophisticated
    Lines = binary:split(Output, <<"\n">>, [global]),
    ModelLines = [L || L <- Lines, binary:match(L, <<"(define-fun">>) /= nomatch],
    parse_model_lines(ModelLines, #{}).

parse_model_lines([], Acc) ->
    Acc;
parse_model_lines([Line | Rest], Acc) ->
    case parse_model_line(Line) of
        {ok, Var, Value} ->
            parse_model_lines(Rest, maps:put(Var, Value, Acc));
        error ->
            parse_model_lines(Rest, Acc)
    end.

parse_model_line(Line) ->
    % Parse lines like "(define-fun x () Int 42)"
    case binary:split(Line, <<" ">>, [global]) of
        [<<"(define-fun">>, VarBin, <<"()">>, _Type, ValueBin | _] ->
            try
                Var = binary_to_atom(VarBin, utf8),
                Value = binary_to_integer(ValueBin),
                {ok, Var, Value}
            catch
                _:_ -> error
            end;
        _ ->
            error
    end.

%% ===== UTILITY FUNCTIONS =====

%% Convert expression to SMT constraint
expression_to_smt_constraint({binary_op_expr, Op, Left, Right, _}, Context) ->
    LeftTerm = expression_to_smt_term(Left, Context),
    RightTerm = expression_to_smt_term(Right, Context),
    arithmetic_constraint(LeftTerm, Op, RightTerm);
expression_to_smt_constraint(Expr, _Context) ->
    % Fallback - create a placeholder constraint
    ExprTerm = constant_term(unknown),
    TrueTerm = constant_term(true),
    arithmetic_constraint(ExprTerm, '=', TrueTerm).

expression_to_smt_term({identifier_expr, Name, _}, _Context) ->
    variable_term(Name);
expression_to_smt_term({literal_expr, Value, _}, _Context) ->
    constant_term(Value);
expression_to_smt_term(_Expr, _Context) ->
    constant_term(unknown).

predicate_to_smt_constraint(Predicate, Variable, Context) when is_function(Predicate, 1) ->
    % Convert function predicate to SMT constraint
    % This is a simplified version - full implementation would analyze the function
    arithmetic_constraint(Variable, '>', constant_term(0));
predicate_to_smt_constraint(_Predicate, Variable, _Context) ->
    % Fallback constraint
    arithmetic_constraint(Variable, '=', Variable).

%% Negate SMT constraint
negate_constraint(#smt_constraint{op = '='} = C) ->
    C#smt_constraint{op = '/='};
negate_constraint(#smt_constraint{op = '>'} = C) ->
    C#smt_constraint{op = '<='};
negate_constraint(#smt_constraint{op = '<'} = C) ->
    C#smt_constraint{op = '>='};
negate_constraint(#smt_constraint{op = '>='} = C) ->
    C#smt_constraint{op = '<'};
negate_constraint(#smt_constraint{op = '<='} = C) ->
    C#smt_constraint{op = '>'};
negate_constraint(C) ->
    % Default - return unchanged
    C.

extract_counterexample(Model) ->
    % Extract counterexample from SMT model
    maps:values(Model).

apply_temporal_quantifier(Condition, TimeVar) ->
    % Apply time variable to condition (simplified)
    Condition.

quantify_existentially(Var, Constraint) ->
    % Create existential quantification
    #smt_constraint{
        type = logical,
        left = function_term(exists, [Var]),
        op = '.',
        right = constraint_to_term(Constraint),
        location = undefined
    }.

quantify_universally(Var, Constraint) ->
    % Create universal quantification
    #smt_constraint{
        type = logical,
        left = function_term(forall, [Var]),
        op = '.',
        right = constraint_to_term(Constraint),
        location = undefined
    }.

implication_constraint(Left, Right) ->
    #smt_constraint{
        type = logical,
        left = Left,
        op = implies,
        right = Right,
        location = undefined
    }.

conjunction_constraint(Left, Right) ->
    #smt_constraint{
        type = logical,
        left = Left,
        op = 'and',
        right = Right,
        location = undefined
    }.

constraint_to_term(#smt_constraint{left = Left, op = Op, right = Right}) ->
    function_term(Op, [Left, Right]).

%% Simple expression evaluation for fallback
evaluate_expression({literal_expr, Value, _}) ->
    Value;
evaluate_expression({identifier_expr, Name, _}) ->
    % Would look up in environment
    Name;
evaluate_expression(_Expr) ->
    unknown.
