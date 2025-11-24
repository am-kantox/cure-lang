%% Cure Programming Language - Guard Refinement Tests
%% Tests for union refinement types and SMT-based counterexample finding
-module(guard_refinement_test).

-include("../src/parser/cure_ast.hrl").
-include("../src/types/cure_refinement_types.hrl").

-export([run/0]).

%% Test runner
run() ->
    io:format("~n=== Guard Refinement Tests ===~n"),

    % Test union refinement types for OR guards
    test_union_refinement_types(),
    test_disjunctive_constraints(),

    % Test SMT-based counterexample finding
    test_counterexample_finding(),
    test_guard_negation(),
    test_guard_disjunction(),

    % Edge cases
    test_nested_or_guards(),
    test_complex_guard_constraints(),

    io:format("~n=== All tests completed ===~n"),
    ok.

%% ============================================================================
%% Union Refinement Type Tests
%% ============================================================================

test_union_refinement_types() ->
    io:format("Testing union refinement types...~n"),

    % Test 1: Create union refinement from OR constraints
    Left = #binary_op_expr{
        op = '>',
        left = #identifier_expr{name = x},
        right = #literal_expr{value = 0},
        location = #location{line = 0, column = 0, file = undefined}
    },
    Right = #binary_op_expr{
        op = '<',
        left = #identifier_expr{name = x},
        right = #literal_expr{value = 0},
        location = #location{line = 0, column = 0, file = undefined}
    },

    UnionType = cure_guard_refinement:create_union_refinement_type(
        {primitive_type, 'Int'},
        x,
        Left,
        Right
    ),

    % Verify it's a refinement type
    true = cure_refinement_types:is_refinement_type(UnionType),
    io:format("  OK: Union refinement type created successfully~n"),

    % Test 2: Verify predicate is disjunctive
    Pred = cure_refinement_types:refinement_predicate(UnionType),
    true = cure_guard_refinement:is_disjunctive_constraint(Pred),
    io:format("  OK: Disjunctive constraint recognized~n"),

    % Test 3: Extract branches
    {LeftBranch, RightBranch} = cure_guard_refinement:extract_disjunctive_branches(Pred),
    true = LeftBranch =/= undefined,
    true = RightBranch =/= undefined,
    io:format("  OK: Disjunctive branches extracted~n").

test_disjunctive_constraints() ->
    io:format("Testing disjunctive constraint detection...~n"),

    % Create OR constraint
    OrConstraint = #binary_op_expr{
        op = 'orelse',
        left = #literal_expr{value = true},
        right = #literal_expr{value = false},
        location = #location{line = 0, column = 0, file = undefined}
    },

    % Should be recognized as disjunctive
    true = cure_guard_refinement:is_disjunctive_constraint(OrConstraint),
    io:format("  OK: OR constraint recognized as disjunctive~n"),

    % Create AND constraint
    AndConstraint = #binary_op_expr{
        op = 'andalso',
        left = #literal_expr{value = true},
        right = #literal_expr{value = false},
        location = #location{line = 0, column = 0, file = undefined}
    },

    % Should NOT be recognized as disjunctive
    false = cure_guard_refinement:is_disjunctive_constraint(AndConstraint),
    io:format("  OK: AND constraint correctly identified as non-disjunctive~n"),

    % Nested disjunctive should also be detected
    NestedOr = #binary_op_expr{
        op = 'andalso',
        left = #binary_op_expr{
            op = 'orelse',
            left = #literal_expr{value = true},
            right = #literal_expr{value = false},
            location = #location{line = 0, column = 0, file = undefined}
        },
        right = #literal_expr{value = true},
        location = #location{line = 0, column = 0, file = undefined}
    },
    true = cure_guard_refinement:is_disjunctive_constraint(NestedOr),
    io:format("  OK: Nested disjunctive constraint detected~n").

%% ============================================================================
%% Guard Negation Tests
%% ============================================================================

test_guard_negation() ->
    io:format("Testing guard expression negation...~n"),

    % Test 1: Negate simple comparison
    Guard1 = #binary_op_expr{
        op = '>',
        left = #identifier_expr{name = x},
        right = #literal_expr{value = 0},
        location = #location{line = 0, column = 0, file = undefined}
    },

    Negated1 = cure_guard_refinement:negate_guard_expression(Guard1),
    % ¬(x > 0) should be x =< 0
    true = (Negated1#binary_op_expr.op =:= '=<'),
    io:format("  OK: Comparison negation: not(x > 0) = (x =< 0)~n"),

    % Test 2: De Morgan's law: ¬(A ∨ B) = (¬A ∧ ¬B)
    Or = #binary_op_expr{
        op = 'orelse',
        left = #literal_expr{value = true},
        right = #literal_expr{value = false},
        location = #location{line = 0, column = 0, file = undefined}
    },

    NegOr = cure_guard_refinement:negate_guard_expression(Or),
    true = (NegOr#binary_op_expr.op =:= 'andalso'),
    io:format("  OK: De Morgan's law: not(A or B) = (not A and not B)~n"),

    % Test 3: De Morgan's law: ¬(A ∧ B) = (¬A ∨ ¬B)
    And = #binary_op_expr{
        op = 'andalso',
        left = #literal_expr{value = true},
        right = #literal_expr{value = false},
        location = #location{line = 0, column = 0, file = undefined}
    },

    NegAnd = cure_guard_refinement:negate_guard_expression(And),
    true = (NegAnd#binary_op_expr.op =:= 'orelse'),
    io:format("  OK: De Morgan's law: not(A and B) = (not A or not B)~n"),

    % Test 4: Double negation
    True = #literal_expr{
        value = true, location = #location{line = 0, column = 0, file = undefined}
    },
    NegTrue = cure_guard_refinement:negate_guard_expression(True),
    false = NegTrue#literal_expr.value,
    io:format("  OK: Boolean negation: not(true) = false~n").

%% ============================================================================
%% Guard Disjunction Tests
%% ============================================================================

test_guard_disjunction() ->
    io:format("Testing guard disjunction building...~n"),

    % Create single guard
    Guard1 = #binary_op_expr{
        op = '>',
        left = #identifier_expr{name = x},
        right = #literal_expr{value = 0},
        location = #location{line = 0, column = 0, file = undefined}
    },

    % Build disjunction of single guard
    Disj1 = cure_guard_refinement:build_guard_disjunction([Guard1]),
    true = (Disj1 =:= Guard1),
    io:format("  OK: Single guard disjunction returns same guard~n"),

    % Create multiple guards
    Guard2 = #binary_op_expr{
        op = '<',
        left = #identifier_expr{name = x},
        right = #literal_expr{value = 0},
        location = #location{line = 0, column = 0, file = undefined}
    },

    % Build disjunction of multiple guards
    Disj2 = cure_guard_refinement:build_guard_disjunction([Guard1, Guard2]),
    true = (Disj2#binary_op_expr.op =:= 'orelse'),
    io:format("  OK: Multiple guard disjunction creates OR expression~n"),

    % Build empty disjunction
    Disj0 = cure_guard_refinement:build_guard_disjunction([]),
    false = Disj0#literal_expr.value,
    io:format("  OK: Empty guard disjunction returns false~n").

%% ============================================================================
%% Counterexample Finding Tests
%% ============================================================================

test_counterexample_finding() ->
    io:format("Testing counterexample finding...~n"),

    % Test with no guards (should return empty)
    Clauses1 = [],
    Result1 = cure_guard_refinement:find_uncovered_cases(Clauses1, #{}),
    true = (Result1 =:= []),
    io:format("  OK: No guards returns empty counterexamples~n"),

    % Test with undefined guards
    Clause2 = #function_clause{
        constraint = undefined,
        body = #identifier_expr{name = x}
    },
    Result2 = cure_guard_refinement:find_uncovered_cases([Clause2], #{}),
    true = (Result2 =:= []),
    io:format("  OK: Undefined guard returns empty counterexamples~n").

%% ============================================================================
%% Edge Case Tests
%% ============================================================================

test_nested_or_guards() ->
    io:format("Testing nested OR guards...~n"),

    % Create nested OR: (x > 0) OR ((y < 0) OR (z == 0))
    Inner = #binary_op_expr{
        op = 'orelse',
        left = #binary_op_expr{
            op = '<',
            left = #identifier_expr{name = y},
            right = #literal_expr{value = 0},
            location = #location{line = 0, column = 0, file = undefined}
        },
        right = #binary_op_expr{
            op = '=:=',
            left = #identifier_expr{name = z},
            right = #literal_expr{value = 0},
            location = #location{line = 0, column = 0, file = undefined}
        },
        location = #location{line = 0, column = 0, file = undefined}
    },

    Outer = #binary_op_expr{
        op = 'orelse',
        left = #binary_op_expr{
            op = '>',
            left = #identifier_expr{name = x},
            right = #literal_expr{value = 0},
            location = #location{line = 0, column = 0, file = undefined}
        },
        right = Inner,
        location = #location{line = 0, column = 0, file = undefined}
    },

    % Extract constraints
    Constraints = cure_guard_refinement:extract_guard_constraints(Outer),
    true = (length(Constraints) > 0),
    io:format("  OK: Nested OR guards parsed: ~p constraint(s)~n", [length(Constraints)]),

    % Negate nested OR
    NegOuter = cure_guard_refinement:negate_guard_expression(Outer),
    true = (NegOuter#binary_op_expr.op =:= 'andalso'),
    io:format("  OK: Nested OR negated correctly~n").

test_complex_guard_constraints() ->
    io:format("Testing complex guard constraints...~n"),

    % Create: (x > 0 AND y < 10) OR (x < 0 AND y > 10)
    Left = #binary_op_expr{
        op = 'andalso',
        left = #binary_op_expr{
            op = '>',
            left = #identifier_expr{name = x},
            right = #literal_expr{value = 0},
            location = #location{line = 0, column = 0, file = undefined}
        },
        right = #binary_op_expr{
            op = '<',
            left = #identifier_expr{name = y},
            right = #literal_expr{value = 10},
            location = #location{line = 0, column = 0, file = undefined}
        },
        location = #location{line = 0, column = 0, file = undefined}
    },

    Right = #binary_op_expr{
        op = 'andalso',
        left = #binary_op_expr{
            op = '<',
            left = #identifier_expr{name = x},
            right = #literal_expr{value = 0},
            location = #location{line = 0, column = 0, file = undefined}
        },
        right = #binary_op_expr{
            op = '>',
            left = #identifier_expr{name = y},
            right = #literal_expr{value = 10},
            location = #location{line = 0, column = 0, file = undefined}
        },
        location = #location{line = 0, column = 0, file = undefined}
    },

    Complex = #binary_op_expr{
        op = 'orelse',
        left = Left,
        right = Right,
        location = #location{line = 0, column = 0, file = undefined}
    },

    % Extract constraints
    Constraints = cure_guard_refinement:extract_guard_constraints(Complex),

    % Should have constraints for both x and y
    XConstraints = [C || {x, C} <- Constraints],
    YConstraints = [C || {y, C} <- Constraints],

    true = (length(XConstraints) > 0),
    true = (length(YConstraints) > 0),
    io:format("  OK: Complex guard constraints extracted correctly~n"),

    % Negate complex constraint
    Negated = cure_guard_refinement:negate_guard_expression(Complex),
    true = (Negated#binary_op_expr.op =:= 'andalso'),
    io:format("  OK: Complex constraint negation applied De Morgan's law~n").
