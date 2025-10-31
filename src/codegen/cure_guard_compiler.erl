%% Cure Programming Language - Guard Compiler
%% Compiles guard expressions to BEAM bytecode instructions
-module(cure_guard_compiler).

-export([
    compile_guard/2,
    compile_guards/2,
    is_guard_safe/1,
    optimize_guard/1
]).

-include("cure_codegen.hrl").
-include("../parser/cure_ast.hrl").

%% ============================================================================
%% Main Guard Compilation Interface
%% ============================================================================

%% Compile a single guard expression
compile_guard(undefined, State) ->
    % No guard - always true
    {ok,
        [
            #beam_instr{
                op = load_literal,
                args = [true],
                location = undefined
            }
        ],
        State};
compile_guard(Guard, State) ->
    case is_guard_safe(Guard) of
        true ->
            OptimizedGuard = optimize_guard(Guard),
            compile_guard_expr(OptimizedGuard, State);
        false ->
            {error, {unsafe_guard, Guard}}
    end.

%% Compile multiple guards (for complex guard sequences)
compile_guards([], State) ->
    {ok, [], State};
compile_guards(Guards, State) ->
    compile_guards_impl(Guards, [], State).

compile_guards_impl([], Acc, State) ->
    {ok, lists:reverse(Acc), State};
compile_guards_impl([Guard | Rest], Acc, State) ->
    case compile_guard(Guard, State) of
        {ok, Instructions, NewState} ->
            compile_guards_impl(Rest, [Instructions | Acc], NewState);
        {error, Reason} ->
            {error, Reason}
    end.

%% ============================================================================
%% Guard Expression Compilation
%% ============================================================================

%% Compile individual guard expressions
compile_guard_expr(#literal_expr{value = Value, location = Location}, State) ->
    Instruction = #beam_instr{
        op = load_literal,
        args = [Value],
        location = Location
    },
    {ok, [Instruction], State};
compile_guard_expr(#identifier_expr{name = Name, location = Location}, State) ->
    case resolve_variable(Name, State) of
        {ok, VarRef} ->
            Instruction = #beam_instr{
                op = load_var,
                args = [VarRef],
                location = Location
            },
            {ok, [Instruction], State};
        {error, _} ->
            % Try as parameter reference
            Instruction = #beam_instr{
                op = load_param,
                args = [Name],
                location = Location
            },
            {ok, [Instruction], State}
    end;
compile_guard_expr(
    #binary_op_expr{op = Op, left = Left, right = Right, location = Location}, State
) ->
    case is_guard_bif(Op) of
        true ->
            {ok, LeftInstr, State1} = compile_guard_expr(Left, State),
            {ok, RightInstr, State2} = compile_guard_expr(Right, State1),

            GuardInstruction = #beam_instr{
                op = guard_bif,
                args = [Op, 2],
                location = Location
            },

            Instructions = LeftInstr ++ RightInstr ++ [GuardInstruction],
            {ok, Instructions, State2};
        false ->
            {error, {invalid_guard_op, Op}}
    end;
compile_guard_expr(#unary_op_expr{op = Op, operand = Operand, location = Location}, State) ->
    case is_guard_bif(Op) of
        true ->
            {ok, OperandInstr, State1} = compile_guard_expr(Operand, State),

            GuardInstruction = #beam_instr{
                op = guard_bif,
                args = [Op, 1],
                location = Location
            },

            Instructions = OperandInstr ++ [GuardInstruction],
            {ok, Instructions, State1};
        false ->
            {error, {invalid_guard_op, Op}}
    end;
compile_guard_expr(
    #function_call_expr{
        function = #identifier_expr{name = Fun},
        args = Args,
        location = Location
    },
    State
) ->
    case is_guard_bif(Fun) of
        true ->
            {ok, ArgInstructions, State1} = compile_guard_expressions(Args, State),

            GuardInstruction = #beam_instr{
                op = guard_bif,
                args = [Fun, length(Args)],
                location = Location
            },

            Instructions = ArgInstructions ++ [GuardInstruction],
            {ok, Instructions, State1};
        false ->
            {error, {invalid_guard_function, Fun}}
    end;
compile_guard_expr(#tuple_expr{elements = Elements, location = Location}, State) ->
    {ok, ElementInstructions, State1} = compile_guard_expressions(Elements, State),

    TupleInstruction = #beam_instr{
        op = make_tuple,
        args = [length(Elements)],
        location = Location
    },

    Instructions = ElementInstructions ++ [TupleInstruction],
    {ok, Instructions, State1};
compile_guard_expr(#list_expr{elements = Elements, location = Location}, State) ->
    {ok, ElementInstructions, State1} = compile_guard_expressions(Elements, State),

    ListInstruction = #beam_instr{
        op = make_list,
        args = [length(Elements)],
        location = Location
    },

    Instructions = ElementInstructions ++ [ListInstruction],
    {ok, Instructions, State1};
% String pattern matching: "prefix" <> rest
% This compiles to a binary prefix match in guards
compile_guard_expr(
    #binary_op_expr{
        op = '<>',
        left = #literal_expr{value = Prefix, location = LocLeft},
        right = #identifier_expr{name = VarName, location = LocRight},
        location = Location
    },
    State
) when is_binary(Prefix) ->
    % Match string prefix pattern
    % Generates: case String of <<Prefix/binary, Rest/binary>> -> ... end
    PrefixSize = erlang:byte_size(Prefix),

    Instructions = [
        % Load the string to match against (assumes it's on stack or in variable)
        #beam_instr{
            op = load_param,
            args = [VarName],
            location = LocRight
        },
        % Match prefix
        #beam_instr{
            op = match_binary_prefix,
            args = [Prefix, PrefixSize],
            location = Location
        }
    ],
    {ok, Instructions, State};
compile_guard_expr(Expr, _State) ->
    {error, {unsupported_guard_expr, Expr}}.

%% Compile multiple guard expressions
compile_guard_expressions(Expressions, State) ->
    compile_guard_expressions_impl(Expressions, [], State).

compile_guard_expressions_impl([], Acc, State) ->
    {ok, lists:flatten(lists:reverse(Acc)), State};
compile_guard_expressions_impl([Expr | Rest], Acc, State) ->
    case compile_guard_expr(Expr, State) of
        {ok, Instructions, NewState} ->
            compile_guard_expressions_impl(Rest, [Instructions | Acc], NewState);
        {error, Reason} ->
            {error, Reason}
    end.

%% ============================================================================
%% Guard Safety Analysis
%% ============================================================================

%% Check if an expression is safe to use in a guard context
is_guard_safe(undefined) ->
    true;
is_guard_safe(#literal_expr{}) ->
    true;
is_guard_safe(#identifier_expr{}) ->
    true;
is_guard_safe(#binary_op_expr{op = Op, left = Left, right = Right}) ->
    is_guard_bif(Op) andalso is_guard_safe(Left) andalso is_guard_safe(Right);
is_guard_safe(#unary_op_expr{op = Op, operand = Operand}) ->
    is_guard_bif(Op) andalso is_guard_safe(Operand);
is_guard_safe(#function_call_expr{function = #identifier_expr{name = Fun}, args = Args}) ->
    is_guard_bif(Fun) andalso lists:all(fun is_guard_safe/1, Args);
is_guard_safe(#tuple_expr{elements = Elements}) ->
    lists:all(fun is_guard_safe/1, Elements);
is_guard_safe(#list_expr{elements = Elements}) ->
    lists:all(fun is_guard_safe/1, Elements);
is_guard_safe(_) ->
    false.

%% Check if an operator or function is allowed in guards
is_guard_bif('+') -> true;
is_guard_bif('-') -> true;
is_guard_bif('*') -> true;
is_guard_bif('/') -> true;
is_guard_bif('div') -> true;
is_guard_bif('rem') -> true;
is_guard_bif('==') -> true;
is_guard_bif('!=') -> true;
is_guard_bif('=:=') -> true;
is_guard_bif('=/=') -> true;
is_guard_bif('<') -> true;
is_guard_bif('>') -> true;
is_guard_bif('=<') -> true;
is_guard_bif('<=') -> true;
is_guard_bif('>=') -> true;
is_guard_bif('and') -> true;
is_guard_bif('or') -> true;
is_guard_bif('not') -> true;
is_guard_bif('andalso') -> true;
is_guard_bif('orelse') -> true;
is_guard_bif('xor') -> true;
is_guard_bif('band') -> true;
is_guard_bif('bor') -> true;
is_guard_bif('bxor') -> true;
is_guard_bif('bnot') -> true;
is_guard_bif('bsl') -> true;
is_guard_bif('bsr') -> true;
is_guard_bif('abs') -> true;
is_guard_bif('trunc') -> true;
is_guard_bif('round') -> true;
is_guard_bif('size') -> true;
is_guard_bif('length') -> true;
is_guard_bif('string_length') -> true;
% Note: <> is handled specially for pattern matching in compile_guard_expr/2
% but is NOT a valid guard BIF for concatenation
% String byte size
is_guard_bif('byte_size') -> true;
% Binary pattern matching
is_guard_bif('binary_part') -> true;
is_guard_bif('hd') -> true;
is_guard_bif('tl') -> true;
is_guard_bif('element') -> true;
is_guard_bif('is_atom') -> true;
is_guard_bif('is_binary') -> true;
is_guard_bif('is_boolean') -> true;
is_guard_bif('is_float') -> true;
is_guard_bif('is_function') -> true;
is_guard_bif('is_integer') -> true;
is_guard_bif('is_list') -> true;
is_guard_bif('is_number') -> true;
is_guard_bif('is_pid') -> true;
is_guard_bif('is_port') -> true;
is_guard_bif('is_record') -> true;
is_guard_bif('is_reference') -> true;
is_guard_bif('is_tuple') -> true;
is_guard_bif('node') -> true;
is_guard_bif('self') -> true;
is_guard_bif(_) -> false.

%% ============================================================================
%% Guard Optimization
%% ============================================================================

%% Optimize guard expressions
optimize_guard(Guard) ->
    OptimizedGuard = constant_fold_guard(Guard),
    simplify_guard(OptimizedGuard).

%% Constant folding for guard expressions
constant_fold_guard(#binary_op_expr{
    op = Op,
    left = #literal_expr{value = L},
    right = #literal_expr{value = R},
    location = Location
}) ->
    try
        Value =
            case Op of
                '+' -> L + R;
                '-' -> L - R;
                '*' -> L * R;
                '/' when R =/= 0 -> L / R;
                'div' when R =/= 0 -> L div R;
                'rem' when R =/= 0 -> L rem R;
                '==' -> L == R;
                '!=' -> L /= R;
                '=:=' -> L =:= R;
                '=/=' -> L =/= R;
                '<' -> L < R;
                '>' -> L > R;
                '=<' -> L =< R;
                '<=' -> L =< R;
                '>=' -> L >= R;
                'and' -> L and R;
                'or' -> L or R;
                'andalso' -> L andalso R;
                'orelse' -> L orelse R;
                'xor' -> L xor R;
                'band' -> L band R;
                'bor' -> L bor R;
                'bxor' -> L bxor R;
                'bsl' -> L bsl R;
                'bsr' -> L bsr R;
                _ -> throw(no_fold)
            end,
        #literal_expr{value = Value, location = Location}
    catch
        _:_ ->
            % Keep original expression if folding fails
            #binary_op_expr{
                op = Op,
                left = constant_fold_guard(#literal_expr{value = L, location = Location}),
                right = constant_fold_guard(#literal_expr{value = R, location = Location}),
                location = Location
            }
    end;
constant_fold_guard(#unary_op_expr{
    op = Op,
    operand = #literal_expr{value = V},
    location = Location
}) ->
    try
        Value =
            case Op of
                '-' -> -V;
                '+' -> +V;
                'not' -> not V;
                'bnot' -> bnot V;
                'abs' -> abs(V);
                'trunc' -> trunc(V);
                'round' -> round(V);
                _ -> throw(no_fold)
            end,
        #literal_expr{value = Value, location = Location}
    catch
        _:_ ->
            #unary_op_expr{
                op = Op,
                operand = #literal_expr{value = V, location = Location},
                location = Location
            }
    end;
constant_fold_guard(#binary_op_expr{op = Op, left = Left, right = Right, location = Location}) ->
    OptLeft = constant_fold_guard(Left),
    OptRight = constant_fold_guard(Right),
    case {OptLeft, OptRight} of
        {#literal_expr{value = L}, #literal_expr{value = R}} ->
            constant_fold_guard(#binary_op_expr{
                op = Op,
                left = #literal_expr{value = L, location = Location},
                right = #literal_expr{value = R, location = Location},
                location = Location
            });
        _ ->
            #binary_op_expr{op = Op, left = OptLeft, right = OptRight, location = Location}
    end;
constant_fold_guard(#unary_op_expr{op = Op, operand = Operand, location = Location}) ->
    OptOperand = constant_fold_guard(Operand),
    case OptOperand of
        #literal_expr{value = V} ->
            constant_fold_guard(#unary_op_expr{
                op = Op,
                operand = #literal_expr{value = V, location = Location},
                location = Location
            });
        _ ->
            #unary_op_expr{op = Op, operand = OptOperand, location = Location}
    end;
constant_fold_guard(Expr) ->
    Expr.

%% Simplify guard expressions
simplify_guard(#binary_op_expr{
    op = 'andalso',
    left = #literal_expr{value = true},
    right = Right
}) ->
    simplify_guard(Right);
simplify_guard(#binary_op_expr{
    op = 'andalso',
    left = #literal_expr{value = false}
}) ->
    #literal_expr{value = false, location = undefined};
simplify_guard(#binary_op_expr{
    op = 'orelse',
    left = #literal_expr{value = true}
}) ->
    #literal_expr{value = true, location = undefined};
simplify_guard(#binary_op_expr{
    op = 'orelse',
    left = #literal_expr{value = false},
    right = Right
}) ->
    simplify_guard(Right);
simplify_guard(Expr) ->
    Expr.

%% ============================================================================
%% Helper Functions
%% ============================================================================

%% Resolve variable reference in the current scope
resolve_variable(Name, #codegen_state{local_vars = Vars}) ->
    case maps:find(Name, Vars) of
        {ok, VarRef} -> {ok, VarRef};
        error -> {error, undefined_variable}
    end.
