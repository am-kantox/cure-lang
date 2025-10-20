%% Comprehensive tests for recursive function type inference with dependent types
-module(recursive_type_tests).

-include("../src/parser/cure_ast.hrl").
-include_lib("eunit/include/eunit.hrl").

%% Include type definitions from types module
-record(type_var, {
    id :: integer(),
    name :: atom() | undefined,
    constraints :: [term()]
}).

-record(type_constraint, {
    left :: term(),
    op :: atom(),
    right :: term(),
    location :: term()
}).

-record(inference_result, {
    type :: term(),
    constraints :: [term()],
    substitution :: map()
}).

-record(recursive_call_context, {
    function_name :: atom(),
    call_depth :: integer(),
    parameter_types :: [term()],
    return_type :: term(),
    dependent_constraints :: [term()],
    type_variable_bindings :: map(),
    location :: term()
}).

-record(recursive_inference_state, {
    call_stack :: [term()],
    fixed_point_iterations :: integer(),
    max_iterations :: integer(),
    convergence_threshold :: float(),
    current_substitution :: map()
}).

%% Helper to create test environment
create_test_env() ->
    BaseEnv = cure_types:new_env(),

    % Add Int type
    Env1 = cure_types:extend_env(BaseEnv, 'Int', {primitive_type, 'Int'}),

    % Add factorial function type: Int -> Int
    FactorialType = {function_type, [{primitive_type, 'Int'}], {primitive_type, 'Int'}},
    Env2 = cure_types:extend_env(Env1, factorial, FactorialType),

    % Add fibonacci function type: Int -> Int
    FibonacciType = {function_type, [{primitive_type, 'Int'}], {primitive_type, 'Int'}},
    Env3 = cure_types:extend_env(Env2, fibonacci, FibonacciType),

    % Add Vector type constructor
    VectorElemParam = #type_param{name = elem_type, value = cure_types:new_type_var()},
    VectorLenParam = #type_param{name = length, value = cure_types:new_type_var()},
    VectorType = {dependent_type, 'Vector', [VectorElemParam, VectorLenParam]},
    Env4 = cure_types:extend_env(Env3, 'Vector', VectorType),

    % Add dot_product function type: Vector(T,n) -> Vector(T,n) -> T
    T = cure_types:new_type_var(elem),
    N = cure_types:new_type_var(len),
    VecParam1 = #type_param{name = elem_type, value = T},
    VecParam2 = #type_param{name = length, value = N},
    VectorTN = {dependent_type, 'Vector', [VecParam1, VecParam2]},

    DotProductType = {function_type, [VectorTN, VectorTN], T},
    Env5 = cure_types:extend_env(Env4, dot_product, DotProductType),

    % Add list_sum function type: List(Int,n) -> Int
    IntType = {primitive_type, 'Int'},
    ListLenParam = #type_param{name = length, value = cure_types:new_type_var()},
    ListIntParam = #type_param{name = elem_type, value = IntType},
    ListIntType = {dependent_type, 'List', [ListIntParam, ListLenParam]},

    ListSumType = {function_type, [ListIntType], IntType},
    cure_types:extend_env(Env5, list_sum, ListSumType).

%% Test basic recursive function call inference
test_factorial_recursive_call_test() ->
    Env = create_test_env(),

    % Create expression: factorial(5)
    Five = {literal_expr, 5, {location, 1, 1, undefined}},
    FactorialCall =
        {function_call_expr, {identifier_expr, factorial, {location, 1, 1, undefined}}, [Five],
            {location, 1, 1, undefined}},

    % Test recursive inference
    Result = cure_types:infer_type(FactorialCall, Env),
    ?assertMatch({ok, _}, Result),

    case Result of
        {ok, InferenceResult} ->
            Type = InferenceResult#inference_result.type,
            ?assertEqual({primitive_type, 'Int'}, Type)
    end.

%% Test recursive fibonacci call
test_fibonacci_recursive_call_test() ->
    Env = create_test_env(),

    % Create expression: fibonacci(10)
    Ten = {literal_expr, 10, {location, 1, 1, undefined}},
    FibCall =
        {function_call_expr, {identifier_expr, fibonacci, {location, 1, 1, undefined}}, [Ten],
            {location, 1, 1, undefined}},

    % Test recursive inference
    Result = cure_types:infer_type(FibCall, Env),
    ?assertMatch({ok, _}, Result),

    case Result of
        {ok, InferenceResult} ->
            Type = InferenceResult#inference_result.type,
            ?assertEqual({primitive_type, 'Int'}, Type)
    end.

%% Test Vector dot product with dependent types
test_vector_dot_product_test() ->
    Env = create_test_env(),

    % Create two vectors: Vector(Int, 3)
    IntType = {primitive_type, 'Int'},
    Three = {literal_expr, 3, {location, 1, 1, undefined}},

    ElemParam = #type_param{name = elem_type, value = IntType},
    LenParam = #type_param{name = length, value = Three},
    VectorInt3 = {dependent_type, 'Vector', [ElemParam, LenParam]},

    % Create dummy vector expressions (for simplicity)
    Vec1 = {identifier_expr, vec1, {location, 1, 1, undefined}},
    Vec2 = {identifier_expr, vec2, {location, 1, 1, undefined}},

    % Add vectors to environment
    Env1 = cure_types:extend_env(Env, vec1, VectorInt3),
    Env2 = cure_types:extend_env(Env1, vec2, VectorInt3),

    % Create expression: dot_product(vec1, vec2)
    DotProdCall =
        {function_call_expr, {identifier_expr, dot_product, {location, 1, 1, undefined}},
            [Vec1, Vec2], {location, 1, 1, undefined}},

    % Test recursive inference with dependent types
    Result = cure_types:infer_type(DotProdCall, Env2),
    ?assertMatch({ok, _}, Result),

    case Result of
        {ok, InferenceResult} ->
            Type = InferenceResult#inference_result.type,
            % Should infer element type (Int) as return type
            ?assertEqual(IntType, Type)
    end.

%% Test recursive state management
test_recursive_state_management_test() ->
    % Test the basic recursive state functions
    InitialState = cure_types:new_recursive_state(),

    ?assertMatch(
        #recursive_inference_state{
            call_stack = [],
            fixed_point_iterations = 0,
            max_iterations = 10,
            convergence_threshold = 0.001,
            current_substitution = #{}
        },
        InitialState
    ),

    % Test pushing a recursive call context
    ParamTypes = [{primitive_type, 'Int'}],
    ReturnType = {primitive_type, 'Int'},
    Location = {location, 1, 1, undefined},

    {ok, UpdatedState} = cure_types:push_recursive_call(
        factorial, ParamTypes, ReturnType, InitialState
    ),

    ?assertEqual(1, length(UpdatedState#recursive_inference_state.call_stack)),

    % Test popping
    {ok, Context, FinalState} = cure_types:pop_recursive_call(UpdatedState),
    ?assertEqual(factorial, Context#recursive_call_context.function_name),
    ?assertEqual([], FinalState#recursive_inference_state.call_stack).

%% Test fixed-point constraint solving
test_fixed_point_constraint_solving_test() ->
    State = cure_types:new_recursive_state(),

    % Create some dummy constraints
    T1 = cure_types:new_type_var(),
    T2 = cure_types:new_type_var(),

    Constraint = #type_constraint{
        left = T1,
        op = '=',
        right = {primitive_type, 'Int'},
        location = undefined
    },

    Constraints = [Constraint],

    % Test fixed-point solving
    Result = cure_types:solve_recursive_constraints_fixed_point(Constraints, State),
    ?assertMatch({ok, _, _}, Result),

    case Result of
        {ok, Subst, _Iterations} ->
            % Should have solved T1 = Int
            ?assert(maps:size(Subst) > 0)
    end.

%% Test convergence checking
test_convergence_checking_test() ->
    State = cure_types:new_recursive_state(),

    % Create two similar substitutions
    T1 = cure_types:new_type_var(),
    T2 = cure_types:new_type_var(),

    % Get type variable IDs
    T1Id = T1#type_var.id,
    T2Id = T2#type_var.id,

    Subst1 = #{T1Id => {primitive_type, 'Int'}},
    % Same binding
    Subst2 = #{T1Id => {primitive_type, 'Int'}},

    % Should converge
    Result1 = cure_types:check_recursive_convergence(Subst1, Subst2, State),
    ?assertMatch({converged, _}, Result1),

    % Create different substitutions
    Subst3 = #{T2Id => {primitive_type, 'String'}},

    % Should not converge
    Result2 = cure_types:check_recursive_convergence(Subst1, Subst3, State),
    ?assertMatch({not_converged, _}, Result2).

%% Test dependent constraint tracking in recursion
test_dependent_constraint_tracking_test() ->
    State = cure_types:new_recursive_state(),
    ParamTypes = [{primitive_type, 'Int'}],
    ReturnType = {primitive_type, 'Int'},

    {ok, StateWithCall} = cure_types:push_recursive_call(factorial, ParamTypes, ReturnType, State),

    % Get the context
    [Context] = StateWithCall#recursive_inference_state.call_stack,

    % Create some dependent type constraints
    T1 = cure_types:new_type_var(),
    VecParam1 = #type_param{name = elem_type, value = T1},
    VecParam2 = #type_param{name = length, value = {literal_expr, 3, undefined}},
    VectorType = {dependent_type, 'Vector', [VecParam1, VecParam2]},

    Constraint = #type_constraint{
        left = T1,
        op = '=',
        right = {primitive_type, 'Int'},
        location = undefined
    },

    Constraints = [Constraint],

    % Test tracking dependent constraints
    Result = cure_types:track_dependent_constraints_in_recursion(
        Constraints, Context, StateWithCall
    ),
    ?assertMatch({ok, _, _}, Result),

    case Result of
        {ok, TrackedConstraints, UpdatedState} ->
            % Should have tracked the constraints
            ?assert(length(TrackedConstraints) > 0),

            % Check the updated context has the constraints
            [UpdatedContext] = UpdatedState#recursive_inference_state.call_stack,
            ?assert(length(UpdatedContext#recursive_call_context.dependent_constraints) > 0)
    end.

%% Test unification with recursive context
test_unification_with_recursive_context_test() ->
    State = cure_types:new_recursive_state(),
    ParamTypes = [{primitive_type, 'Int'}],
    ReturnType = {primitive_type, 'Int'},

    {ok, StateWithCall} = cure_types:push_recursive_call(factorial, ParamTypes, ReturnType, State),
    [Context] = StateWithCall#recursive_inference_state.call_stack,

    % Test unification of two integer types
    Types1 = [{primitive_type, 'Int'}],
    Types2 = [{primitive_type, 'Int'}],

    Result = cure_types:unify_with_recursive_context(Types1, Types2, Context, StateWithCall),
    ?assertMatch({ok, [], _}, Result),

    % Test arity mismatch
    Types3 = [{primitive_type, 'Int'}, {primitive_type, 'String'}],

    Result2 = cure_types:unify_with_recursive_context(Types1, Types3, Context, StateWithCall),
    ?assertMatch({error, {arity_mismatch, 1, 2}}, Result2).

%% Main test suite
recursive_types_test_() ->
    [
        ?_test(test_factorial_recursive_call_test()),
        ?_test(test_fibonacci_recursive_call_test()),
        ?_test(test_vector_dot_product_test()),
        ?_test(test_recursive_state_management_test()),
        ?_test(test_fixed_point_constraint_solving_test()),
        ?_test(test_convergence_checking_test()),
        ?_test(test_dependent_constraint_tracking_test()),
        ?_test(test_unification_with_recursive_context_test())
    ].
