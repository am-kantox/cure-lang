%% Simple verification test for recursive type functions
-module(simple_recursive_test).

-include("../src/parser/cure_ast.hrl").
-include_lib("eunit/include/eunit.hrl").

%% Include record definitions
-record(type_var, {
    id :: integer(),
    name :: atom() | undefined,
    constraints :: [term()]
}).

-record(type_env, {
    bindings :: map(),
    constraints :: [term()],
    parent :: term()
}).

-record(recursive_inference_state, {
    call_stack :: [term()],
    fixed_point_iterations :: integer(),
    max_iterations :: integer(),
    convergence_threshold :: float(),
    current_substitution :: map()
}).

%% Simple test to verify basic recursive functions work
basic_recursive_functions_test() ->
    % Test new_recursive_state/0
    State = cure_types:new_recursive_state(),
    ?assert(is_record(State, recursive_inference_state)),

    % Test new_type_var/0
    TypeVar = cure_types:new_type_var(),
    ?assert(is_record(TypeVar, type_var)),

    % Test basic environment creation
    Env = cure_types:new_env(),
    ?assert(is_record(Env, type_env)),

    % Test pushing and popping recursive calls
    ParamTypes = [{primitive_type, 'Int'}],
    ReturnType = {primitive_type, 'Int'},

    {ok, StateWithCall} = cure_types:push_recursive_call(factorial, ParamTypes, ReturnType, State),
    ?assert(length(StateWithCall#recursive_inference_state.call_stack) =:= 1),

    {ok, _Context, FinalState} = cure_types:pop_recursive_call(StateWithCall),
    ?assert(length(FinalState#recursive_inference_state.call_stack) =:= 0).

%% Run basic test
test() ->
    basic_recursive_functions_test().
