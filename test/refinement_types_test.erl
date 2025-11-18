%% Test suite for refinement types with SMT verification
-module(refinement_types_test).

-include("../src/parser/cure_ast.hrl").
-include_lib("eunit/include/eunit.hrl").

-define(INT_TYPE, #primitive_type{
    name = 'Int', location = #location{line = 0, column = 0, file = undefined}
}).
-define(BOOL_TYPE, #primitive_type{
    name = 'Bool', location = #location{line = 0, column = 0, file = undefined}
}).

%% ============================================================================
%% Test Runner
%% ============================================================================

run() ->
    eunit:test({module, ?MODULE}, [verbose]).

%% ============================================================================
%% Refinement Type Creation Tests
%% ============================================================================

create_positive_type_test() ->
    % Create: type Positive = Int when x > 0
    Predicate = #binary_op_expr{
        op = '>',
        left = #identifier_expr{name = x, location = loc()},
        right = #literal_expr{value = 0, location = loc()},
        location = loc()
    },
    RefType = cure_refinement_types:create_refinement_type(?INT_TYPE, x, Predicate),

    ?assert(cure_refinement_types:is_refinement_type(RefType)),
    ?assertEqual(?INT_TYPE, cure_refinement_types:base_type(RefType)),
    {ok, ExtractedPred} = cure_refinement_types:extract_constraint(RefType),
    ?assertEqual(Predicate, ExtractedPred).

create_nonzero_type_test() ->
    % Create: type NonZero = Int when x /= 0
    Predicate = #binary_op_expr{
        op = '/=',
        left = #identifier_expr{name = x, location = loc()},
        right = #literal_expr{value = 0, location = loc()},
        location = loc()
    },
    RefType = cure_refinement_types:create_refinement_type(?INT_TYPE, x, Predicate),

    ?assert(cure_refinement_types:is_refinement_type(RefType)),
    {ok, _} = cure_refinement_types:extract_constraint(RefType).

create_percentage_type_test() ->
    % Create: type Percentage = Int when x >= 0 and x <= 100
    LeftConstraint = #binary_op_expr{
        op = '>=',
        left = #identifier_expr{name = x, location = loc()},
        right = #literal_expr{value = 0, location = loc()},
        location = loc()
    },
    RightConstraint = #binary_op_expr{
        op = '=<',
        left = #identifier_expr{name = x, location = loc()},
        right = #literal_expr{value = 100, location = loc()},
        location = loc()
    },
    Predicate = #binary_op_expr{
        op = 'and',
        left = LeftConstraint,
        right = RightConstraint,
        location = loc()
    },
    RefType = cure_refinement_types:create_refinement_type(?INT_TYPE, x, Predicate),

    ?assert(cure_refinement_types:is_refinement_type(RefType)).

%% ============================================================================
%% Subtyping Tests - Core SMT Verification
%% ============================================================================

subtyping_positive_is_nonzero_test() ->
    % Positive <: NonZero (should be provable: x > 0 => x /= 0)
    PositivePred = make_binary_op('>', var(x), int(0)),
    NonZeroPred = make_binary_op('/=', var(x), int(0)),

    Positive = cure_refinement_types:create_refinement_type(?INT_TYPE, x, PositivePred),
    NonZero = cure_refinement_types:create_refinement_type(?INT_TYPE, x, NonZeroPred),

    Env = #{},
    {ok, IsSubtype} = cure_refinement_types:check_subtype(Positive, NonZero, Env),

    % This should be true - Z3 should prove x > 0 => x /= 0
    ?assertEqual(true, IsSubtype).

subtyping_nonzero_not_positive_test() ->
    % NonZero is NOT a subtype of Positive
    % (x /= 0 does not imply x > 0, e.g., x = -1)
    NonZeroPred = make_binary_op('/=', var(x), int(0)),
    PositivePred = make_binary_op('>', var(x), int(0)),

    NonZero = cure_refinement_types:create_refinement_type(?INT_TYPE, x, NonZeroPred),
    Positive = cure_refinement_types:create_refinement_type(?INT_TYPE, x, PositivePred),

    Env = #{},
    {ok, IsSubtype} = cure_refinement_types:check_subtype(NonZero, Positive, Env),

    % Should be false - counterexample: x = -1
    ?assertEqual(false, IsSubtype).

subtyping_percentage_is_nonnegative_test() ->
    % Percentage <: NonNegative
    % (x >= 0 and x <= 100) => (x >= 0)
    PercentagePred = make_binary_op(
        'and',
        make_binary_op('>=', var(x), int(0)),
        make_binary_op('=<', var(x), int(100))
    ),
    NonNegativePred = make_binary_op('>=', var(x), int(0)),

    Percentage = cure_refinement_types:create_refinement_type(?INT_TYPE, x, PercentagePred),
    NonNegative = cure_refinement_types:create_refinement_type(?INT_TYPE, x, NonNegativePred),

    Env = #{},
    {ok, IsSubtype} = cure_refinement_types:check_subtype(Percentage, NonNegative, Env),

    ?assertEqual(true, IsSubtype).

subtyping_reflexive_test() ->
    % Type <: Type (reflexivity)
    Pred = make_binary_op('>', var(x), int(0)),
    RefType = cure_refinement_types:create_refinement_type(?INT_TYPE, x, Pred),

    Env = #{},
    {ok, IsSubtype} = cure_refinement_types:check_subtype(RefType, RefType, Env),

    ?assertEqual(true, IsSubtype).

%% ============================================================================
%% Constraint Checking Tests
%% ============================================================================

check_constraint_positive_value_test() ->
    % Check if 5 satisfies Positive (x > 0)
    Pred = make_binary_op('>', var(x), int(0)),
    Positive = cure_refinement_types:create_refinement_type(?INT_TYPE, x, Pred),

    Value = int(5),
    Env = #{},

    {ok, Satisfies} = cure_refinement_types:check_constraint(Value, Positive, Env),
    ?assertEqual(true, Satisfies).

check_constraint_zero_not_positive_test() ->
    % Check if 0 does NOT satisfy Positive (x > 0)
    Pred = make_binary_op('>', var(x), int(0)),
    Positive = cure_refinement_types:create_refinement_type(?INT_TYPE, x, Pred),

    Value = int(0),
    Env = #{},

    {ok, Satisfies} = cure_refinement_types:check_constraint(Value, Positive, Env),
    ?assertEqual(false, Satisfies).

check_constraint_negative_not_positive_test() ->
    % Check if -5 does NOT satisfy Positive (x > 0)
    Pred = make_binary_op('>', var(x), int(0)),
    Positive = cure_refinement_types:create_refinement_type(?INT_TYPE, x, Pred),

    Value = int(-5),
    Env = #{},

    {ok, Satisfies} = cure_refinement_types:check_constraint(Value, Positive, Env),
    ?assertEqual(false, Satisfies).

check_constraint_percentage_valid_test() ->
    % Check if 50 satisfies Percentage (x >= 0 and x <= 100)
    Pred = make_binary_op(
        'and',
        make_binary_op('>=', var(x), int(0)),
        make_binary_op('=<', var(x), int(100))
    ),
    Percentage = cure_refinement_types:create_refinement_type(?INT_TYPE, x, Pred),

    Value = int(50),
    Env = #{},

    {ok, Satisfies} = cure_refinement_types:check_constraint(Value, Percentage, Env),
    ?assertEqual(true, Satisfies).

check_constraint_percentage_invalid_test() ->
    % Check if 150 does NOT satisfy Percentage (x >= 0 and x <= 100)
    Pred = make_binary_op(
        'and',
        make_binary_op('>=', var(x), int(0)),
        make_binary_op('=<', var(x), int(100))
    ),
    Percentage = cure_refinement_types:create_refinement_type(?INT_TYPE, x, Pred),

    Value = int(150),
    Env = #{},

    {ok, Satisfies} = cure_refinement_types:check_constraint(Value, Percentage, Env),
    ?assertEqual(false, Satisfies).

%% ============================================================================
%% Precondition Verification Tests
%% ============================================================================

verify_precondition_success_test() ->
    % Verify that arg 5 satisfies Positive parameter
    Pred = make_binary_op('>', var(x), int(0)),
    Positive = cure_refinement_types:create_refinement_type(?INT_TYPE, x, Pred),

    Arg = int(5),
    Env = #{},
    Loc = loc(),

    Result = cure_refinement_types:verify_precondition(Arg, Positive, Env, Loc),
    ?assertEqual(ok, Result).

verify_precondition_failure_test() ->
    % Verify that arg 0 does NOT satisfy Positive parameter
    Pred = make_binary_op('>', var(x), int(0)),
    Positive = cure_refinement_types:create_refinement_type(?INT_TYPE, x, Pred),

    Arg = int(0),
    Env = #{},
    Loc = loc(),

    Result = cure_refinement_types:verify_precondition(Arg, Positive, Env, Loc),
    ?assertMatch({error, {precondition_violation, _, _, _}}, Result).

%% ============================================================================
%% Constraint Propagation Tests
%% ============================================================================

propagate_constraints_simple_test() ->
    % When x: Positive, propagate constraint through expression
    Pred = make_binary_op('>', var(x), int(0)),
    Positive = cure_refinement_types:create_refinement_type(?INT_TYPE, x, Pred),

    Env = #{x => Positive},
    Expr = var(x),
    ConstraintMap = #{},

    Result = cure_refinement_types:propagate_constraints(Expr, Env, ConstraintMap),
    ?assert(maps:is_key(x, Result)).

strengthen_type_test() ->
    % Strengthen Int to Positive (Int when x > 0)
    Constraint = make_binary_op('>', var(x), int(0)),
    RefType = cure_refinement_types:strengthen_type(?INT_TYPE, Constraint, x),

    ?assert(cure_refinement_types:is_refinement_type(RefType)),
    ?assertEqual(?INT_TYPE, cure_refinement_types:base_type(RefType)).

weaken_type_test() ->
    % Weaken Positive back to Int
    Pred = make_binary_op('>', var(x), int(0)),
    Positive = cure_refinement_types:create_refinement_type(?INT_TYPE, x, Pred),

    Weakened = cure_refinement_types:weaken_type(Positive, []),
    ?assertEqual(?INT_TYPE, Weakened).

%% ============================================================================
%% Error Formatting Tests
%% ============================================================================

format_error_precondition_test() ->
    Pred = make_binary_op('>', var(x), int(0)),
    Positive = cure_refinement_types:create_refinement_type(?INT_TYPE, x, Pred),

    Error = {precondition_violation, loc(), Positive, #{x => 0}},
    Formatted = cure_refinement_types:format_refinement_error(Error),

    ?assert(is_binary(Formatted)),
    ?assert(byte_size(Formatted) > 0).

format_error_subtype_test() ->
    Pred1 = make_binary_op('>', var(x), int(0)),
    Pred2 = make_binary_op('/=', var(x), int(0)),
    Type1 = cure_refinement_types:create_refinement_type(?INT_TYPE, x, Pred1),
    Type2 = cure_refinement_types:create_refinement_type(?INT_TYPE, x, Pred2),

    Error = {subtype_check_failed, Type1, Type2},
    Formatted = cure_refinement_types:format_refinement_error(Error),

    ?assert(is_binary(Formatted)),
    ?assert(byte_size(Formatted) > 0).

%% ============================================================================
%% Integration Tests - Complex Scenarios
%% ============================================================================

complex_refinement_chain_test() ->
    % Create chain: StrictlyPositive <: Positive <: NonZero
    % StrictlyPositive: x > 10
    % Positive: x > 0
    % NonZero: x /= 0

    StrictlyPosPred = make_binary_op('>', var(x), int(10)),
    PosPred = make_binary_op('>', var(x), int(0)),
    NonZeroPred = make_binary_op('/=', var(x), int(0)),

    StrictlyPositive = cure_refinement_types:create_refinement_type(?INT_TYPE, x, StrictlyPosPred),
    Positive = cure_refinement_types:create_refinement_type(?INT_TYPE, x, PosPred),
    NonZero = cure_refinement_types:create_refinement_type(?INT_TYPE, x, NonZeroPred),

    Env = #{},

    % StrictlyPositive <: Positive
    {ok, IsSubtype1} = cure_refinement_types:check_subtype(StrictlyPositive, Positive, Env),
    ?assertEqual(true, IsSubtype1),

    % Positive <: NonZero
    {ok, IsSubtype2} = cure_refinement_types:check_subtype(Positive, NonZero, Env),
    ?assertEqual(true, IsSubtype2),

    % Transitivity: StrictlyPositive <: NonZero
    {ok, IsSubtype3} = cure_refinement_types:check_subtype(StrictlyPositive, NonZero, Env),
    ?assertEqual(true, IsSubtype3).

bounded_range_subtyping_test() ->
    % SmallRange <: LargeRange
    % SmallRange: x >= 10 and x <= 20
    % LargeRange: x >= 0 and x <= 100

    SmallRangePred = make_binary_op(
        'and',
        make_binary_op('>=', var(x), int(10)),
        make_binary_op('=<', var(x), int(20))
    ),
    LargeRangePred = make_binary_op(
        'and',
        make_binary_op('>=', var(x), int(0)),
        make_binary_op('=<', var(x), int(100))
    ),

    SmallRange = cure_refinement_types:create_refinement_type(?INT_TYPE, x, SmallRangePred),
    LargeRange = cure_refinement_types:create_refinement_type(?INT_TYPE, x, LargeRangePred),

    Env = #{},
    {ok, IsSubtype} = cure_refinement_types:check_subtype(SmallRange, LargeRange, Env),

    ?assertEqual(true, IsSubtype).

%% ============================================================================
%% Helper Functions
%% ============================================================================

loc() ->
    #location{line = 0, column = 0, file = undefined}.

var(Name) ->
    #identifier_expr{name = Name, location = loc()}.

int(Val) ->
    #literal_expr{value = Val, location = loc()}.

make_binary_op(Op, Left, Right) ->
    #binary_op_expr{
        op = Op,
        left = Left,
        right = Right,
        location = loc()
    }.
