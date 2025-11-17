-module(cure_pipe_optimizer).

-moduledoc """
Optimizations specifically for pipe operator chains.

This module provides compile-time optimizations for pipe operator usage,
focusing on eliminating redundant wrapping/unwrapping and inlining simple
pipe chains when type information proves they cannot fail.
""".

-export([
    optimize_pipe_chain/2,
    can_inline_pipe_chain/2,
    is_error_free_pipe/2,
    new_stats/0,
    update_stats/2,
    format_stats/1
]).

-include("../parser/cure_ast.hrl").

%% ============================================================================
%% Public API
%% ============================================================================

-doc """
Optimize a pipe operator chain based on type information.

This function analyzes a pipe chain and applies optimizations:
1. Eliminate redundant Ok wrapping/unwrapping
2. Inline error-free chains to direct function calls
3. Specialize monomorphic pipe operations

## Arguments
- `PipeExpr` - Binary operation expression with '|>' operator
- `TypeEnv` - Type environment for type inference

## Returns
- `{ok, OptimizedExpr, Stats}` - Optimized expression with statistics
- `{unchanged, PipeExpr, Stats}` - No optimization applied with statistics
""".
optimize_pipe_chain(#binary_op_expr{op = '|>', left = Left, right = Right} = PipeExpr, TypeEnv) ->
    Stats = new_stats(),
    % Check if we can optimize this pipe chain
    case analyze_pipe_chain(PipeExpr, TypeEnv) of
        {error_free, _ChainTypes} ->
            % This chain provably cannot fail - can optimize to direct calls
            case can_inline_to_direct_calls(Left, Right, TypeEnv) of
                {true, DirectCall} ->
                    {ok, DirectCall, update_stats(Stats, inlined)};
                false ->
                    {unchanged, PipeExpr, update_stats(Stats, error_free)}
            end;
        {may_error, _ChainTypes} ->
            % Keep monadic pipe semantics
            {unchanged, PipeExpr, update_stats(Stats, unchanged)};
        unknown ->
            % Cannot determine - keep original
            {unchanged, PipeExpr, update_stats(Stats, unchanged)}
    end;
optimize_pipe_chain(Expr, _TypeEnv) ->
    {unchanged, Expr, new_stats()}.

-doc """
Check if a pipe chain can be inlined to direct function calls.

A pipe chain can be inlined if:
1. All functions in the chain are pure (no side effects)
2. Type information proves no errors can occur
3. The chain is short enough (to avoid code bloat)

## Arguments
- `PipeChain` - Pipe operator chain expression
- `TypeEnv` - Type environment for analysis

## Returns
- `true` - Can be inlined
- `false` - Should keep monadic pipe
""".
can_inline_pipe_chain(PipeChain, TypeEnv) ->
    case analyze_pipe_chain(PipeChain, TypeEnv) of
        {error_free, ChainTypes} ->
            % Check additional constraints
            ChainLength = length(ChainTypes),
            % Don't inline chains longer than 5
            MaxInlineLength = 5,

            case ChainLength =< MaxInlineLength of
                true ->
                    % Check if all functions are pure
                    all_functions_pure(PipeChain);
                false ->
                    false
            end;
        _ ->
            false
    end.

-doc """
Determine if a pipe chain is provably error-free.

A pipe chain is error-free if type analysis proves that:
1. No function in the chain can return Error
2. All type constraints are satisfied
3. No runtime exceptions can occur

## Arguments
- `PipeChain` - Pipe operator chain expression
- `TypeEnv` - Type environment for type checking

## Returns
- `true` - Provably error-free
- `false` - May produce errors
""".
is_error_free_pipe(PipeChain, TypeEnv) ->
    case analyze_pipe_chain(PipeChain, TypeEnv) of
        {error_free, _} -> true;
        _ -> false
    end.

%% ============================================================================
%% Internal Functions
%% ============================================================================

%% Analyze a pipe chain and determine if it can fail
analyze_pipe_chain(#binary_op_expr{op = '|>', left = Left, right = Right}, TypeEnv) ->
    % Analyze the left side
    LeftAnalysis = analyze_pipe_expression(Left, TypeEnv),
    RightAnalysis = analyze_pipe_expression(Right, TypeEnv),

    case {LeftAnalysis, RightAnalysis} of
        {{error_free, LType}, {error_free, RType}} ->
            % Both sides are error-free
            {error_free, [LType, RType]};
        _ ->
            % At least one side may error
            {may_error, [LeftAnalysis, RightAnalysis]}
    end;
analyze_pipe_chain(Expr, _TypeEnv) ->
    % Not a pipe chain
    {may_error, [Expr]}.

%% Analyze a single expression in the pipe chain
analyze_pipe_expression(#literal_expr{}, _TypeEnv) ->
    % Literals never error
    {error_free, literal};
analyze_pipe_expression(#identifier_expr{name = Name}, TypeEnv) ->
    % Look up the function type
    case cure_types:lookup_env(TypeEnv, Name) of
        {function_type, _ParamTypes, ReturnType} ->
            case returns_result_type(ReturnType) of
                true -> {may_error, function_call};
                false -> {error_free, function_call}
            end;
        _ ->
            % Unknown function or variable
            {may_error, unknown}
    end;
analyze_pipe_expression(#function_call_expr{function = Function}, TypeEnv) ->
    % Recursively analyze the function being called
    analyze_pipe_expression(Function, TypeEnv);
analyze_pipe_expression(#binary_op_expr{op = '|>', left = Left, right = Right}, TypeEnv) ->
    % Nested pipe - analyze recursively
    analyze_pipe_chain(#binary_op_expr{op = '|>', left = Left, right = Right}, TypeEnv);
analyze_pipe_expression(#binary_op_expr{}, _TypeEnv) ->
    % Binary operations (arithmetic, etc.) typically don't error
    {error_free, binary_op};
analyze_pipe_expression(_Expr, _TypeEnv) ->
    % Conservative: assume it may error
    {may_error, unknown}.

%% Check if a type is a Result type
returns_result_type({dependent_type, 'Result', _}) -> true;
returns_result_type({primitive_type, 'Result'}) -> true;
returns_result_type(_) -> false.

%% Check if all functions in a pipe chain are pure
all_functions_pure(#binary_op_expr{op = '|>', left = Left, right = Right}) ->
    is_pure_expression(Left) andalso is_pure_expression(Right);
all_functions_pure(_) ->
    false.

%% Check if an expression is pure (no side effects)
is_pure_expression(#literal_expr{}) ->
    true;
is_pure_expression(#identifier_expr{}) ->
    true;
is_pure_expression(#binary_op_expr{op = Op, left = Left, right = Right}) when
    Op =:= '+'; Op =:= '-'; Op =:= '*'; Op =:= '/'
->
    % Arithmetic operators are pure
    is_pure_expression(Left) andalso is_pure_expression(Right);
is_pure_expression(#binary_op_expr{op = '|>', left = Left, right = Right}) ->
    % Pipe chains are pure if both sides are pure
    is_pure_expression(Left) andalso is_pure_expression(Right);
is_pure_expression(#function_call_expr{function = Function, args = Args}) ->
    % Function calls are pure if:
    % 1. The function is known to be pure
    % 2. All arguments are pure
    is_known_pure_function(Function) andalso lists:all(fun is_pure_expression/1, Args);
is_pure_expression(_) ->
    % Conservative: assume impure
    false.

%% Check if a function is known to be pure
is_known_pure_function(#identifier_expr{name = Name}) ->
    % List of known pure functions
    PureFunctions = [
        double,
        increment,
        add,
        multiply,
        square,
        abs,
        max,
        min,
        floor,
        ceiling,
        to_lowercase,
        to_uppercase,
        trim
    ],
    lists:member(Name, PureFunctions);
is_known_pure_function(_) ->
    false.

%% Attempt to inline pipe chain to direct function calls
can_inline_to_direct_calls(Left, Right, TypeEnv) ->
    % For error-free chains like: value |> f |> g
    % Transform to: g(f(value))
    case {Left, Right} of
        {LeftExpr, #identifier_expr{name = RightFunc}} ->
            % Simple case: value |> function
            case is_simple_value(LeftExpr) of
                true ->
                    % Create direct function call
                    DirectCall = #function_call_expr{
                        function = #identifier_expr{
                            name = RightFunc,
                            location = #location{line = 0, column = 0}
                        },
                        args = [LeftExpr],
                        location = #location{line = 0, column = 0}
                    },
                    {true, DirectCall};
                false ->
                    false
            end;
        {#binary_op_expr{op = '|>'} = NestedPipe, #identifier_expr{name = RightFunc}} ->
            % Nested pipe: (a |> b) |> c
            % Try to inline the nested part first
            case
                can_inline_to_direct_calls(
                    NestedPipe#binary_op_expr.left,
                    NestedPipe#binary_op_expr.right,
                    TypeEnv
                )
            of
                {true, InnerCall} ->
                    % Now wrap with outer function
                    DirectCall = #function_call_expr{
                        function = #identifier_expr{
                            name = RightFunc,
                            location = #location{line = 0, column = 0}
                        },
                        args = [InnerCall],
                        location = #location{line = 0, column = 0}
                    },
                    {true, DirectCall};
                false ->
                    false
            end;
        _ ->
            % Too complex to inline
            false
    end.

%% Check if an expression is a simple value (safe to inline)
is_simple_value(#literal_expr{}) ->
    true;
is_simple_value(#identifier_expr{}) ->
    true;
is_simple_value(#function_call_expr{args = Args}) ->
    % Function calls are simple if all args are simple
    lists:all(fun is_simple_value/1, Args);
is_simple_value(_) ->
    false.

%% ============================================================================
%% Optimization Statistics
%% ============================================================================

-doc """
Statistics about pipe operator optimizations applied.
""".
-record(pipe_optimization_stats, {
    total_pipes :: non_neg_integer(),
    inlined_pipes :: non_neg_integer(),
    error_free_pipes :: non_neg_integer(),
    unchanged_pipes :: non_neg_integer()
}).

%% Initialize statistics
new_stats() ->
    #pipe_optimization_stats{
        total_pipes = 0,
        inlined_pipes = 0,
        error_free_pipes = 0,
        unchanged_pipes = 0
    }.

%% Update statistics
update_stats(Stats, inlined) ->
    Stats#pipe_optimization_stats{
        total_pipes = Stats#pipe_optimization_stats.total_pipes + 1,
        inlined_pipes = Stats#pipe_optimization_stats.inlined_pipes + 1
    };
update_stats(Stats, error_free) ->
    Stats#pipe_optimization_stats{
        total_pipes = Stats#pipe_optimization_stats.total_pipes + 1,
        error_free_pipes = Stats#pipe_optimization_stats.error_free_pipes + 1
    };
update_stats(Stats, unchanged) ->
    Stats#pipe_optimization_stats{
        total_pipes = Stats#pipe_optimization_stats.total_pipes + 1,
        unchanged_pipes = Stats#pipe_optimization_stats.unchanged_pipes + 1
    }.

%% Format statistics for display
format_stats(#pipe_optimization_stats{
    total_pipes = Total,
    inlined_pipes = Inlined,
    error_free_pipes = ErrorFree,
    unchanged_pipes = Unchanged
}) ->
    io_lib:format(
        "Pipe Optimizations:~n"
        "  Total pipe operations: ~p~n"
        "  Inlined to direct calls: ~p (~.1f%)~n"
        "  Error-free (optimizable): ~p (~.1f%)~n"
        "  Unchanged (monadic): ~p (~.1f%)~n",
        [
            Total,
            Inlined,
            safe_percentage(Inlined, Total),
            ErrorFree,
            safe_percentage(ErrorFree, Total),
            Unchanged,
            safe_percentage(Unchanged, Total)
        ]
    ).

safe_percentage(_Part, 0) -> 0.0;
safe_percentage(Part, Total) -> (Part / Total) * 100.0.
