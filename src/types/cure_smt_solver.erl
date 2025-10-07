%% Cure Programming Language - SMT Solver and Proof Assistant
%% Handles arithmetic constraints and dependent type reasoning
-module(cure_smt_solver).

-export([
    % Core SMT solver interface
    solve_constraints/1, solve_constraints/2,
    check_satisfiable/1,
    prove_constraint/2,
    
    % Constraint construction
    new_constraint/3,
    arithmetic_constraint/3,
    equality_constraint/2,
    implication_constraint/2,
    
    % Pattern matching inference
    infer_pattern_length/2,
    list_pattern_length_constraint/2,
    infer_tail_length_constraint/3,
    
    % Proof assistant
    generate_proof/2,
    check_proof/2,
    
    % Utility functions
    constraint_to_string/1,
    variable_term/1,
    constant_term/1
]).

-include("../parser/cure_ast_simple.hrl").

%% SMT Constraint representation
-record(smt_constraint, {
    type :: equality | inequality | arithmetic | logical,
    left :: smt_term(),
    op :: '=' | '<' | '>' | '<=' | '>=' | '/=' | '+' | '-' | '*' | 'and' | 'or' | 'implies',
    right :: smt_term(),
    location :: location()
}).

-record(smt_term, {
    type :: variable | constant | expression,
    value :: atom() | integer() | float() | smt_expression(),
    location :: location()
}).

-record(smt_expression, {
    op :: '+' | '-' | '*' | '/' | 'mod',
    args :: [smt_term()],
    location :: location()
}).

-record(smt_context, {
    constraints :: [smt_constraint()],
    variables :: #{atom() => smt_term()},
    assumptions :: [smt_constraint()]
}).

-record(proof_term, {
    conclusion :: smt_constraint(),
    premises :: [smt_constraint()],
    rule :: atom(),
    subproofs :: [proof_term()]
}).

-type smt_constraint() :: #smt_constraint{}.
-type smt_term() :: #smt_term{}.
-type smt_expression() :: #smt_expression{}.
-type smt_context() :: #smt_context{}.
-type proof_term() :: #proof_term{}.
-type location() :: term().

%% ============================================================================
%% Public API
%% ============================================================================

%% @doc Solve a list of constraints and return satisfiability
-spec solve_constraints([smt_constraint()]) -> {sat, #{atom() => term()}} | unsat | unknown.
solve_constraints(Constraints) ->
    solve_constraints(Constraints, #{}).

-spec solve_constraints([smt_constraint()], #{atom() => term()}) -> 
    {sat, #{atom() => term()}} | unsat | unknown.
solve_constraints(Constraints, InitialAssignment) ->
    Context = #smt_context{
        constraints = Constraints,
        variables = extract_variables(Constraints),
        assumptions = []
    },
    solve_context(Context, InitialAssignment).

%% @doc Check if a single constraint is satisfiable
-spec check_satisfiable(smt_constraint()) -> boolean().
check_satisfiable(Constraint) ->
    case solve_constraints([Constraint]) of
        {sat, _} -> true;
        _ -> false
    end.

%% @doc Prove that a constraint follows from given assumptions
-spec prove_constraint([smt_constraint()], smt_constraint()) -> 
    {proved, proof_term()} | {disproved, proof_term()} | unknown.
prove_constraint(Assumptions, Goal) ->
    % Try to prove Goal from Assumptions
    Context = #smt_context{
        constraints = [Goal],
        variables = extract_variables([Goal | Assumptions]),
        assumptions = Assumptions
    },
    attempt_proof(Context, Goal).

%% ============================================================================
%% Constraint Construction
%% ============================================================================

%% @doc Create a new constraint
-spec new_constraint(atom(), atom(), smt_term()) -> smt_constraint().
new_constraint(Type, Op, Right) ->
    new_constraint(Type, Op, Right, undefined).

new_constraint(Type, Op, Right, Location) ->
    #smt_constraint{
        type = Type,
        left = undefined,
        op = Op,
        right = Right,
        location = Location
    }.

%% @doc Create arithmetic constraint (e.g., x + 1 = y)
-spec arithmetic_constraint(smt_term(), atom(), smt_term()) -> smt_constraint().
arithmetic_constraint(Left, Op, Right) ->
    #smt_constraint{
        type = arithmetic,
        left = Left,
        op = Op,
        right = Right,
        location = undefined
    }.

%% @doc Create equality constraint (x = y)
-spec equality_constraint(smt_term(), smt_term()) -> smt_constraint().
equality_constraint(Left, Right) ->
    #smt_constraint{
        type = equality,
        left = Left,
        op = '=',
        right = Right,
        location = undefined
    }.

%% @doc Create implication constraint (P -> Q)
-spec implication_constraint(smt_constraint(), smt_constraint()) -> smt_constraint().
implication_constraint(Premise, Conclusion) ->
    #smt_constraint{
        type = logical,
        left = constraint_to_term(Premise),
        op = 'implies',
        right = constraint_to_term(Conclusion),
        location = undefined
    }.

%% ============================================================================
%% Pattern Matching Length Inference
%% ============================================================================

%% @doc Infer length constraints from pattern matching
-spec infer_pattern_length(term(), smt_term()) -> [smt_constraint()].
infer_pattern_length({list_pattern, Elements, Tail, _Location}, ListLengthVar) ->
    ElementCount = length(Elements),
    
    case Tail of
        undefined ->
            % Fixed length pattern [a, b, c] means length = 3
            [equality_constraint(ListLengthVar, constant_term(ElementCount))];
        {wildcard_pattern, _} ->
            % Pattern [a, b | _] means length >= 2
            [inequality_constraint(ListLengthVar, '>=', constant_term(ElementCount))];
        {identifier_pattern, TailVar, _} ->
            % Pattern [a, b | tail] means length = 2 + length(tail)
            TailLengthVar = variable_term(list_to_atom(atom_to_list(TailVar) ++ "_length")),
            [
                arithmetic_constraint(
                    ListLengthVar, 
                    '=',
                    addition_expression([constant_term(ElementCount), TailLengthVar])
                )
            ];
        _ ->
            % Other tail patterns - assume minimum length
            [inequality_constraint(ListLengthVar, '>=', constant_term(ElementCount))]
    end;

%% Handle standard cons pattern [H|T] where H is single element
infer_pattern_length({cons_pattern, _Head, Tail, _Location}, ListLengthVar) ->
    case Tail of
        {identifier_pattern, TailVar, _} ->
            % [x|xs] means list_length = 1 + tail_length
            TailLengthVar = variable_term(list_to_atom(atom_to_list(TailVar) ++ "_length")),
            [
                arithmetic_constraint(
                    ListLengthVar, 
                    '=',
                    addition_expression([constant_term(1), TailLengthVar])
                )
            ];
        _ ->
            % [x|_] means length >= 1
            [inequality_constraint(ListLengthVar, '>=', constant_term(1))]
    end;

%% Handle other pattern types
infer_pattern_length(_, _) ->
    [].

%% @doc Generate length constraints for list pattern matching
-spec list_pattern_length_constraint(term(), atom()) -> smt_constraint().
list_pattern_length_constraint(Pattern, LengthVar) ->
    [Constraint|_] = infer_pattern_length(Pattern, variable_term(LengthVar)),
    Constraint.

%% @doc Infer tail length constraint for safe_tail function
%% When matching [_|xs] -> xs, the tail xs has length n-1 where n is original list length
-spec infer_tail_length_constraint(term(), atom(), atom()) -> [smt_constraint()].
infer_tail_length_constraint({cons_pattern, _, {identifier_pattern, TailVar, _}, _}, 
                           OriginalLengthVar, TailLengthVar) ->
    % [_|xs] -> xs means xs_length = original_length - 1
    TailMinusOne = subtraction_expression([
        variable_term(OriginalLengthVar), 
        constant_term(1)
    ]),
    [
        arithmetic_constraint(
            variable_term(TailLengthVar),
            '=',
            TailMinusOne
        )
    ];
infer_tail_length_constraint({list_pattern, [_], {identifier_pattern, TailVar, _}, _}, 
                               OriginalLengthVar, TailLengthVar) ->
    % [_|tail] -> tail means tail_length = original_length - 1  
    TailMinusOne = subtraction_expression([
        variable_term(OriginalLengthVar), 
        constant_term(1)
    ]),
    [
        arithmetic_constraint(
            variable_term(TailLengthVar),
            '=',
            TailMinusOne
        )
    ];
infer_tail_length_constraint(_, _, _) ->
    [].

%% ============================================================================
%% Core SMT Solving Logic
%% ============================================================================

%% Solve SMT context
solve_context(Context, Assignment) ->
    case simplify_constraints(Context#smt_context.constraints) of
        [] -> {sat, Assignment};
        SimplifiedConstraints ->
            case check_inconsistency(SimplifiedConstraints) of
                true -> unsat;
                false ->
                    case find_unit_constraints(SimplifiedConstraints) of
                        [] -> 
                            % No unit constraints, try case splitting
                            case_split_solve(SimplifiedConstraints, Assignment);
                        UnitConstraints ->
                            % Apply unit constraints and continue
                            NewAssignment = apply_unit_constraints(UnitConstraints, Assignment),
                            RemainingConstraints = propagate_assignments(SimplifiedConstraints, NewAssignment),
                            solve_context(
                                Context#smt_context{constraints = RemainingConstraints},
                                NewAssignment
                            )
                    end
            end
    end.

%% Simplify constraints using basic rules
simplify_constraints(Constraints) ->
    lists:foldl(fun simplify_constraint/2, [], Constraints).

simplify_constraint(Constraint, Acc) ->
    case Constraint of
        #smt_constraint{type = equality, left = Term, op = '=', right = Term} ->
            % x = x is always true, remove it
            Acc;
        #smt_constraint{type = equality, left = Left, op = '=', right = Right} ->
            case {Left, Right} of
                {#smt_term{type = constant, value = V1}, 
                 #smt_term{type = constant, value = V2}} ->
                    case V1 =:= V2 of
                        true -> Acc;  % Remove tautology
                        false -> [false_constraint() | Acc]  % Add contradiction
                    end;
                _ -> [Constraint | Acc]
            end;
        _ -> [Constraint | Acc]
    end.

%% Check for obvious inconsistencies
check_inconsistency(Constraints) ->
    lists:any(fun(C) -> C =:= false_constraint() end, Constraints).

%% Find unit constraints (constraints with single variable)
find_unit_constraints(Constraints) ->
    lists:filter(fun is_unit_constraint/1, Constraints).

%% Apply unit constraints to generate assignments
apply_unit_constraints(UnitConstraints, Assignment) ->
    lists:foldl(fun apply_unit_constraint/2, Assignment, UnitConstraints).

%% Case splitting for DPLL-style solving
case_split_solve(Constraints, Assignment) ->
    case choose_variable(Constraints) of
        undefined -> unknown;  % No more variables to split on
        Var ->
            % Try positive assignment
            PositiveAssignment = Assignment#{Var => true},
            case solve_context(#smt_context{constraints = Constraints}, PositiveAssignment) of
                {sat, Solution} -> {sat, Solution};
                _ ->
                    % Try negative assignment
                    NegativeAssignment = Assignment#{Var => false},
                    solve_context(#smt_context{constraints = Constraints}, NegativeAssignment)
            end
    end.

%% ============================================================================
%% Proof Assistant
%% ============================================================================

%% Attempt to construct a proof
attempt_proof(Context, Goal) ->
    case try_direct_proof(Context#smt_context.assumptions, Goal) of
        {proved, Proof} -> {proved, Proof};
        failed ->
            case try_contradiction_proof(Context#smt_context.assumptions, Goal) of
                {proved, Proof} -> {proved, Proof};
                failed -> unknown
            end
    end.

%% Try direct proof (Goal follows from assumptions)
try_direct_proof(Assumptions, Goal) ->
    case lists:member(Goal, Assumptions) of
        true ->
            {proved, #proof_term{
                conclusion = Goal,
                premises = [Goal],
                rule = assumption,
                subproofs = []
            }};
        false ->
            try_inference_rules(Assumptions, Goal)
    end.

%% Try proof by contradiction
try_contradiction_proof(Assumptions, Goal) ->
    NegatedGoal = negate_constraint(Goal),
    case solve_constraints([NegatedGoal | Assumptions]) of
        unsat ->
            {proved, #proof_term{
                conclusion = Goal,
                premises = Assumptions,
                rule = contradiction,
                subproofs = []
            }};
        _ -> failed
    end.

%% Try various inference rules
try_inference_rules(Assumptions, Goal) ->
    % Try arithmetic inference
    case try_arithmetic_inference(Assumptions, Goal) of
        {proved, Proof} -> {proved, Proof};
        failed -> failed
    end.

%% Try arithmetic inference rules
try_arithmetic_inference(Assumptions, Goal) ->
    case Goal of
        #smt_constraint{type = equality, left = Left, op = '=', right = Right} ->
            try_equality_inference(Assumptions, Left, Right);
        #smt_constraint{type = inequality} ->
            try_inequality_inference(Assumptions, Goal);
        _ -> failed
    end.

try_equality_inference(Assumptions, Left, Right) ->
    % Try to prove Left = Right using arithmetic rules
    case {Left, Right} of
        {#smt_term{type = variable, value = Var}, #smt_term{type = expression}} ->
            % Try to solve for variable in arithmetic expression
            try_solve_arithmetic_equality(Assumptions, Var, Right);
        {#smt_term{type = expression}, #smt_term{type = variable, value = Var}} ->
            try_solve_arithmetic_equality(Assumptions, Var, Left);
        _ -> failed
    end.

try_inequality_inference(Assumptions, Goal) ->
    #smt_constraint{left = Left, op = Op, right = Right} = Goal,
    case evaluate_arithmetic_comparison(Left, Op, Right, Assumptions) of
        true -> 
            {proved, #proof_term{
                conclusion = Goal,
                premises = Assumptions,
                rule = arithmetic_evaluation,
                subproofs = []
            }};
        false -> failed;
        unknown -> failed
    end.

%% ============================================================================
%% Utility Functions
%% ============================================================================

%% Create various term types
variable_term(Name) ->
    #smt_term{type = variable, value = Name, location = undefined}.

constant_term(Value) ->
    #smt_term{type = constant, value = Value, location = undefined}.

addition_expression(Terms) ->
    #smt_term{
        type = expression,
        value = #smt_expression{op = '+', args = Terms, location = undefined},
        location = undefined
    }.

subtraction_expression(Terms) ->
    #smt_term{
        type = expression,
        value = #smt_expression{op = '-', args = Terms, location = undefined},
        location = undefined
    }.

inequality_constraint(Left, Op, Right) ->
    #smt_constraint{
        type = inequality,
        left = Left,
        op = Op,
        right = Right,
        location = undefined
    }.

%% Helper predicates
is_false_constraint() ->
    #smt_constraint{
        type = equality,
        left = constant_term(true),
        op = '=',
        right = constant_term(false),
        location = undefined
    }.

false_constraint() ->
    is_false_constraint().

is_unit_constraint(#smt_constraint{type = equality, left = Left, right = Right}) ->
    % A constraint is unit if it assigns a specific value to a variable
    case {Left, Right} of
        {#smt_term{type = variable}, #smt_term{type = constant}} -> true;
        {#smt_term{type = constant}, #smt_term{type = variable}} -> true;
        _ -> false
    end;
is_unit_constraint(_) ->
    false.

apply_unit_constraint(#smt_constraint{type = equality, left = Left, right = Right}, Assignment) ->
    case {Left, Right} of
        {#smt_term{type = variable, value = Var}, #smt_term{type = constant, value = Val}} ->
            Assignment#{Var => Val};
        {#smt_term{type = constant, value = Val}, #smt_term{type = variable, value = Var}} ->
            Assignment#{Var => Val};
        _ -> Assignment
    end;
apply_unit_constraint(_, Assignment) ->
    Assignment.

choose_variable(Constraints) ->
    % Simple heuristic: choose the first variable that appears in constraints
    Variables = extract_variables(Constraints),
    case maps:keys(Variables) of
        [] -> undefined;
        [Var|_] -> Var
    end.

propagate_assignments(Constraints, Assignment) ->
    [propagate_assignment_in_constraint(C, Assignment) || C <- Constraints].

propagate_assignment_in_constraint(#smt_constraint{left = Left, right = Right} = C, Assignment) ->
    NewLeft = substitute_variables(Left, Assignment),
    NewRight = substitute_variables(Right, Assignment),
    C#smt_constraint{left = NewLeft, right = NewRight}.

substitute_variables(undefined, _Assignment) ->
    undefined;
substitute_variables(#smt_term{type = variable, value = Var} = Term, Assignment) ->
    case maps:get(Var, Assignment, undefined) of
        undefined -> Term;
        Value -> constant_term(Value)
    end;
substitute_variables(#smt_term{type = expression, value = Expr} = Term, Assignment) ->
    NewArgs = [substitute_variables(Arg, Assignment) || Arg <- Expr#smt_expression.args],
    Term#smt_term{value = Expr#smt_expression{args = NewArgs}};
substitute_variables(Term, _Assignment) ->
    Term.

extract_variables(Constraints) ->
    lists:foldl(fun extract_variables_from_constraint/2, #{}, Constraints).

extract_variables_from_constraint(#smt_constraint{left = Left, right = Right}, Acc) ->
    Acc1 = extract_variables_from_term(Left, Acc),
    extract_variables_from_term(Right, Acc1);
extract_variables_from_constraint(_, Acc) ->
    Acc.

extract_variables_from_term(undefined, Acc) ->
    Acc;
extract_variables_from_term(#smt_term{type = variable, value = Name}, Acc) ->
    Acc#{Name => variable};
extract_variables_from_term(#smt_term{type = expression, value = Expr}, Acc) ->
    extract_variables_from_expression(Expr, Acc);
extract_variables_from_term(_, Acc) ->
    Acc.

extract_variables_from_expression(#smt_expression{args = Args}, Acc) ->
    lists:foldl(fun extract_variables_from_term/2, Acc, Args).

constraint_to_term(Constraint) ->
    % Convert constraint to term representation for logical operations
    #smt_term{
        type = expression,
        value = #smt_expression{
            op = constraint_op_to_expression_op(Constraint#smt_constraint.op),
            args = [Constraint#smt_constraint.left, Constraint#smt_constraint.right],
            location = Constraint#smt_constraint.location
        },
        location = Constraint#smt_constraint.location
    }.

constraint_op_to_expression_op(Op) -> Op.

negate_constraint(Constraint) ->
    case Constraint of
        #smt_constraint{op = '='} -> Constraint#smt_constraint{op = '/='};
        #smt_constraint{op = '/='} -> Constraint#smt_constraint{op = '='};
        #smt_constraint{op = '<'} -> Constraint#smt_constraint{op = '>='};
        #smt_constraint{op = '>'} -> Constraint#smt_constraint{op = '=<'};
        #smt_constraint{op = '<='} -> Constraint#smt_constraint{op = '>'};
        #smt_constraint{op = '>='} -> Constraint#smt_constraint{op = '<'};
        _ -> Constraint  % TODO: Handle other constraint types
    end.

%% Convert constraint to human-readable string
constraint_to_string(#smt_constraint{left = Left, op = Op, right = Right}) ->
    LeftStr = term_to_string(Left),
    RightStr = term_to_string(Right),
    OpStr = atom_to_list(Op),
    LeftStr ++ " " ++ OpStr ++ " " ++ RightStr.

term_to_string(#smt_term{type = variable, value = Name}) ->
    atom_to_list(Name);
term_to_string(#smt_term{type = constant, value = Value}) ->
    case Value of
        V when is_integer(V) -> integer_to_list(V);
        V when is_float(V) -> float_to_list(V);
        V when is_atom(V) -> atom_to_list(V);
        _ -> "unknown"
    end;
term_to_string(#smt_term{type = expression, value = Expr}) ->
    expression_to_string(Expr).

expression_to_string(#smt_expression{op = Op, args = Args}) ->
    OpStr = atom_to_list(Op),
    ArgsStrs = [term_to_string(Arg) || Arg <- Args],
    "(" ++ string:join(ArgsStrs, " " ++ OpStr ++ " ") ++ ")".

%% Generate proof term  
generate_proof(_Assumptions, _Goal) ->
    % TODO: Implement proof generation
    undefined.

%% Check proof validity
check_proof(_Proof, _Goal) ->
    % TODO: Implement proof checking
    false.

%% ============================================================================
%% Arithmetic Constraint Solving
%% ============================================================================

%% Try to solve arithmetic equality like m = n - 1
try_solve_arithmetic_equality(Assumptions, Var, Expression) ->
    case Expression of
        #smt_term{type = expression, value = #smt_expression{op = '-', args = [Left, Right]}} ->
            % Handle m = n - 1 pattern
            case {Left, Right} of
                {#smt_term{type = variable, value = SourceVar}, 
                 #smt_term{type = constant, value = Offset}} when is_integer(Offset) ->
                    % Look for constraint on SourceVar in assumptions
                    case find_variable_value(SourceVar, Assumptions) of
                        {found, Value} when is_integer(Value) ->
                            Result = Value - Offset,
                            NewConstraint = equality_constraint(variable_term(Var), constant_term(Result)),
                            {proved, #proof_term{
                                conclusion = NewConstraint,
                                premises = Assumptions,
                                rule = arithmetic_subtraction,
                                subproofs = []
                            }};
                        _ -> failed
                    end;
                _ -> failed
            end;
        #smt_term{type = expression, value = #smt_expression{op = '+', args = [Left, Right]}} ->
            % Handle m = n + 1 pattern
            case {Left, Right} of
                {#smt_term{type = variable, value = SourceVar}, 
                 #smt_term{type = constant, value = Offset}} when is_integer(Offset) ->
                    case find_variable_value(SourceVar, Assumptions) of
                        {found, Value} when is_integer(Value) ->
                            Result = Value + Offset,
                            NewConstraint = equality_constraint(variable_term(Var), constant_term(Result)),
                            {proved, #proof_term{
                                conclusion = NewConstraint,
                                premises = Assumptions,
                                rule = arithmetic_addition,
                                subproofs = []
                            }};
                        _ -> failed
                    end;
                _ -> failed
            end;
        _ -> failed
    end.

%% Find the value of a variable in assumptions
find_variable_value(Var, Assumptions) ->
    find_variable_value_in_list(Var, Assumptions).

find_variable_value_in_list(_Var, []) ->
    not_found;
find_variable_value_in_list(Var, [#smt_constraint{type = equality, left = Left, op = '=', right = Right} | Rest]) ->
    case {Left, Right} of
        {#smt_term{type = variable, value = Var}, #smt_term{type = constant, value = Value}} ->
            {found, Value};
        {#smt_term{type = constant, value = Value}, #smt_term{type = variable, value = Var}} ->
            {found, Value};
        _ -> find_variable_value_in_list(Var, Rest)
    end;
find_variable_value_in_list(Var, [_ | Rest]) ->
    find_variable_value_in_list(Var, Rest).

%% Evaluate arithmetic comparison
evaluate_arithmetic_comparison(Left, Op, Right, Assumptions) ->
    case {evaluate_term(Left, Assumptions), evaluate_term(Right, Assumptions)} of
        {{value, LeftVal}, {value, RightVal}} when is_number(LeftVal), is_number(RightVal) ->
            apply_comparison_operator(LeftVal, Op, RightVal);
        _ -> unknown
    end.

%% Evaluate a term given assumptions
evaluate_term(#smt_term{type = constant, value = Value}, _Assumptions) ->
    {value, Value};
evaluate_term(#smt_term{type = variable, value = Var}, Assumptions) ->
    case find_variable_value(Var, Assumptions) of
        {found, Value} -> {value, Value};
        not_found -> unknown
    end;
evaluate_term(#smt_term{type = expression, value = Expr}, Assumptions) ->
    evaluate_expression(Expr, Assumptions);
evaluate_term(undefined, _Assumptions) ->
    unknown.

%% Evaluate arithmetic expressions
evaluate_expression(#smt_expression{op = Op, args = Args}, Assumptions) ->
    case evaluate_terms(Args, Assumptions) of
        {all_values, Values} ->
            {value, apply_arithmetic_operator(Op, Values)};
        _ -> unknown
    end.

%% Evaluate list of terms
evaluate_terms(Terms, Assumptions) ->
    Results = [evaluate_term(Term, Assumptions) || Term <- Terms],
    case lists:all(fun({Type, _}) -> Type =:= value end, Results) of
        true -> {all_values, [Val || {value, Val} <- Results]};
        false -> partial
    end.

%% Apply arithmetic operator
apply_arithmetic_operator('+', [A, B]) -> A + B;
apply_arithmetic_operator('-', [A, B]) -> A - B;
apply_arithmetic_operator('*', [A, B]) -> A * B;
apply_arithmetic_operator('/', [A, B]) when B =/= 0 -> A / B;
apply_arithmetic_operator(_, _) -> error.

%% Apply comparison operator
apply_comparison_operator(Left, '=', Right) -> Left =:= Right;
apply_comparison_operator(Left, '/=', Right) -> Left =/= Right;
apply_comparison_operator(Left, '<', Right) -> Left < Right;
apply_comparison_operator(Left, '>', Right) -> Left > Right;
apply_comparison_operator(Left, '<=', Right) -> Left =< Right;
apply_comparison_operator(Left, '>=', Right) -> Left >= Right;
apply_comparison_operator(Left, '=<', Right) -> Left =< Right;
apply_comparison_operator(_, _, _) -> unknown.
