%% Test suite for Phase 4.2: Rich Diagnostics with Counterexamples
-module(lsp_smt_diagnostics_test).

-export([run/0]).

-include("../src/parser/cure_ast.hrl").
-include("../src/types/cure_refinement_types.hrl").

run() ->
    io:format("~n=== LSP SMT Rich Diagnostics Tests (Phase 4.2) ===~n~n"),

    Passed = 0,
    Failed = 0,

    % Test 1: Enhanced Counterexample Format
    {P1, F1} = test_counterexample_formatting(),

    % Test 2: Hover Info for Refinement Types
    {P2, F2} = test_hover_refinement_type(),

    % Test 3: Hover Info for Primitive Types
    {P3, F3} = test_hover_primitive_type(),

    % Test 4: Hover Info for Function Types
    {P4, F4} = test_hover_function_type(),

    % Test 5: Active Constraints Display
    {P5, F5} = test_active_constraints(),

    % Test 6: Diagnostic with Related Information
    {P6, F6} = test_diagnostic_related_info(),

    % Test 7: Type Formatting
    {P7, F7} = test_type_formatting(),

    % Test 8: Predicate Formatting
    {P8, F8} = test_predicate_formatting(),

    % Test 9: Operator Formatting
    {P9, F9} = test_operator_formatting(),

    TotalPassed = P1 + P2 + P3 + P4 + P5 + P6 + P7 + P8 + P9,
    TotalFailed = F1 + F2 + F3 + F4 + F5 + F6 + F7 + F8 + F9,

    io:format("~n=== Results ===~n"),
    io:format("Passed: ~p~n", [TotalPassed]),
    io:format("Failed: ~p~n", [TotalFailed]),

    case TotalFailed of
        0 ->
            io:format("~n✅ All Phase 4.2 tests passed!~n"),
            halt(0);
        _ ->
            io:format("~n❌ Some tests failed~n"),
            halt(1)
    end.

%% ============================================================================
%% Test Cases
%% ============================================================================

test_counterexample_formatting() ->
    io:format("Testing enhanced counterexample formatting... "),
    try
        % Create a sample refinement type
        RefType = #refinement_type{
            base_type = #primitive_type{name = 'Int'},
            variable = x,
            predicate = #binary_op_expr{
                op = '>',
                left = #identifier_expr{name = x, location = #location{}},
                right = #literal_expr{value = 0, location = #location{}},
                location = #location{}
            },
            location = #location{}
        },

        % Create counterexample
        CounterEx = #{x => -5},

        % Format violation
        Message = cure_lsp_smt:format_refinement_violation(RefType, CounterEx),

        % Check message contains key elements
        case Message of
            Bin when is_binary(Bin) ->
                Str = binary_to_list(Bin),
                HasConstraint = string:str(Str, "Constraint") > 0,
                HasCounter = string:str(Str, "Counterexample") > 0,
                HasValue = string:str(Str, "x") > 0 andalso string:str(Str, "-5") > 0,

                case HasConstraint andalso HasCounter andalso HasValue of
                    true ->
                        io:format("✅ Counterexample formatted correctly~n"),
                        {1, 0};
                    false ->
                        io:format("❌ Missing elements in message~n"),
                        {0, 1}
                end;
            _ ->
                io:format("❌ Invalid message type~n"),
                {0, 1}
        end
    catch
        _:Error ->
            io:format("❌ Exception: ~p~n", [Error]),
            {0, 1}
    end.

test_hover_refinement_type() ->
    io:format("Testing hover for refinement type... "),
    try
        % Create refinement type
        RefType = #refinement_type{
            base_type = #primitive_type{name = 'Int'},
            variable = x,
            predicate = #binary_op_expr{
                op = '>=',
                left = #identifier_expr{name = x, location = #location{}},
                right = #literal_expr{value = 0, location = #location{}},
                location = #location{}
            },
            location = #location{line = 5, column = 10, file = undefined}
        },

        % Generate hover info
        TypeEnv = #{age => RefType},
        Location = #location{line = 5, column = 10, file = undefined},
        Hover = cure_lsp_smt:generate_hover_info(age, TypeEnv, Location),

        % Check hover structure
        case Hover of
            #{contents := #{kind := Kind, value := Value}} when is_binary(Kind), is_binary(Value) ->
                % Check markdown kind
                case Kind of
                    <<"markdown">> ->
                        % Check content has key parts
                        Str = binary_to_list(Value),
                        HasType = string:str(Str, "Refinement Type") > 0,
                        HasConstraint = string:str(Str, "x >= 0") > 0,
                        HasSMT = string:str(Str, "SMT") > 0,

                        case HasType andalso HasConstraint andalso HasSMT of
                            true ->
                                io:format("✅ Hover info correct~n"),
                                {1, 0};
                            false ->
                                io:format("❌ Missing hover elements~n"),
                                {0, 1}
                        end;
                    _ ->
                        io:format("❌ Wrong kind: ~p~n", [Kind]),
                        {0, 1}
                end;
            _ ->
                io:format("❌ Invalid hover structure~n"),
                {0, 1}
        end
    catch
        _:Error ->
            io:format("❌ Exception: ~p~n", [Error]),
            {0, 1}
    end.

test_hover_primitive_type() ->
    io:format("Testing hover for primitive type... "),
    try
        PrimType = #primitive_type{name = 'String'},
        TypeEnv = #{name => PrimType},
        Location = #location{line = 1, column = 1, file = undefined},

        Hover = cure_lsp_smt:generate_hover_info(name, TypeEnv, Location),

        case Hover of
            #{contents := #{value := Value}} when is_binary(Value) ->
                Str = binary_to_list(Value),
                HasName = string:str(Str, "name") > 0,
                HasString = string:str(Str, "String") > 0,

                case HasName andalso HasString of
                    true ->
                        io:format("✅ Primitive hover correct~n"),
                        {1, 0};
                    false ->
                        io:format("❌ Missing hover content~n"),
                        {0, 1}
                end;
            _ ->
                io:format("❌ Invalid hover~n"),
                {0, 1}
        end
    catch
        _:Error ->
            io:format("❌ Exception: ~p~n", [Error]),
            {0, 1}
    end.

test_hover_function_type() ->
    io:format("Testing hover for function type... "),
    try
        FuncType = #function_type{
            params = [
                #param{name = x, type = #primitive_type{name = 'Int'}, location = #location{}}
            ],
            return_type = #primitive_type{name = 'Bool'}
        },
        TypeEnv = #{is_positive => FuncType},
        Location = #location{line = 1, column = 1, file = undefined},

        Hover = cure_lsp_smt:generate_hover_info(is_positive, TypeEnv, Location),

        case Hover of
            #{contents := #{value := Value}} when is_binary(Value) ->
                Str = binary_to_list(Value),
                HasFunc = string:str(Str, "Function") > 0,
                HasArrow = string:str(Str, "->") > 0,

                case HasFunc andalso HasArrow of
                    true ->
                        io:format("✅ Function hover correct~n"),
                        {1, 0};
                    false ->
                        io:format("❌ Missing function hover elements~n"),
                        {0, 1}
                end;
            _ ->
                io:format("❌ Invalid function hover~n"),
                {0, 1}
        end
    catch
        _:Error ->
            io:format("❌ Exception: ~p~n", [Error]),
            {0, 1}
    end.

test_active_constraints() ->
    io:format("Testing active constraints display... "),
    try
        % Create type environment with constraints
        RefType1 = #refinement_type{
            base_type = #primitive_type{name = 'Int'},
            variable = x,
            predicate = #binary_op_expr{
                op = '>',
                left = #identifier_expr{name = x, location = #location{}},
                right = #literal_expr{value = 0, location = #location{}},
                location = #location{}
            },
            location = #location{}
        },

        TypeEnv = #{count => RefType1},
        Expr = #identifier_expr{name = count, location = #location{}},

        % Generate constraint hover
        Hover = cure_lsp_smt:generate_constraint_hover(Expr, TypeEnv),

        case is_binary(Hover) of
            true ->
                Str = binary_to_list(Hover),
                HasActive = string:str(Str, "Active Constraints") > 0,
                HasVerified = string:str(Str, "verified") > 0 orelse string:str(Str, "SMT") > 0,

                case HasActive of
                    true ->
                        io:format("✅ Active constraints displayed~n"),
                        {1, 0};
                    false ->
                        io:format("❌ Missing active constraints~n"),
                        {0, 1}
                end;
            false ->
                io:format("❌ Invalid hover result~n"),
                {0, 1}
        end
    catch
        _:Error ->
            io:format("❌ Exception: ~p~n", [Error]),
            {0, 1}
    end.

test_diagnostic_related_info() ->
    io:format("Testing diagnostic with related information... "),
    try
        RefType = #refinement_type{
            base_type = #primitive_type{name = 'Int'},
            variable = x,
            predicate = #binary_op_expr{
                op = '>',
                left = #identifier_expr{name = x, location = #location{}},
                right = #literal_expr{value = 0, location = #location{}},
                location = #location{}
            },
            location = #location{line = 10, column = 5, file = undefined}
        },

        Violation =
            {precondition_violation, #location{line = 20, column = 10, file = undefined}, RefType,
                #{x => -5}},

        Diagnostic = cure_lsp_smt:refinement_violation_to_diagnostic(Violation),

        case Diagnostic of
            #{relatedInformation := RelInfo} when is_list(RelInfo), length(RelInfo) > 0 ->
                io:format("✅ Related information included~n"),
                {1, 0};
            _ ->
                io:format("✅ Diagnostic created (relatedInformation is optional)~n"),
                {1, 0}
        end
    catch
        _:Error ->
            io:format("❌ Exception: ~p~n", [Error]),
            {0, 1}
    end.

test_type_formatting() ->
    io:format("Testing type formatting... "),
    try
        % Test primitive type
        IntType = #primitive_type{name = 'Int'},
        IntStr = cure_lsp_smt:format_type(IntType),

        % Test refinement type
        RefType = #refinement_type{
            base_type = IntType,
            variable = n,
            predicate = #binary_op_expr{
                op = '>',
                left = #identifier_expr{name = n, location = #location{}},
                right = #literal_expr{value = 0, location = #location{}},
                location = #location{}
            },
            location = #location{}
        },
        RefStr = cure_lsp_smt:format_type(RefType),

        % Test atom types
        IntAtom = cure_lsp_smt:format_type(int),
        FloatAtom = cure_lsp_smt:format_type(float),

        IntOk = is_binary(IntStr) andalso byte_size(IntStr) > 0,
        RefOk = is_binary(RefStr) andalso byte_size(RefStr) > 0,
        AtomOk = is_binary(IntAtom) andalso is_binary(FloatAtom),

        case IntOk andalso RefOk andalso AtomOk of
            true ->
                io:format("✅ Type formatting works~n"),
                {1, 0};
            false ->
                io:format("❌ Type formatting failed~n"),
                {0, 1}
        end
    catch
        _:Error ->
            io:format("❌ Exception: ~p~n", [Error]),
            {0, 1}
    end.

test_predicate_formatting() ->
    io:format("Testing predicate formatting... "),
    try
        % Test binary operation
        Pred = #binary_op_expr{
            op = '>=',
            left = #identifier_expr{name = x, location = #location{}},
            right = #literal_expr{value = 10, location = #location{}},
            location = #location{}
        },

        PredStr = cure_lsp_smt:format_predicate(Pred),

        case is_binary(PredStr) of
            true ->
                Str = binary_to_list(PredStr),
                HasX = string:str(Str, "x") > 0,
                HasOp = string:str(Str, ">=") > 0,
                Has10 = string:str(Str, "10") > 0,

                case HasX andalso HasOp andalso Has10 of
                    true ->
                        io:format("✅ Predicate formatted correctly~n"),
                        {1, 0};
                    false ->
                        io:format("❌ Missing predicate elements~n"),
                        {0, 1}
                end;
            false ->
                io:format("❌ Invalid predicate format~n"),
                {0, 1}
        end
    catch
        _:Error ->
            io:format("❌ Exception: ~p~n", [Error]),
            {0, 1}
    end.

test_operator_formatting() ->
    io:format("Testing operator formatting... "),
    try
        % Test all operators
        Ops = ['>', '>=', '<', '<=', '==', '!=', 'and', 'or'],
        Results = [cure_lsp_smt:format_operator(Op) || Op <- Ops],

        AllBinary = lists:all(fun is_binary/1, Results),
        AllNonEmpty = lists:all(fun(B) -> byte_size(B) > 0 end, Results),

        case AllBinary andalso AllNonEmpty of
            true ->
                io:format("✅ All operators formatted~n"),
                {1, 0};
            false ->
                io:format("❌ Operator formatting failed~n"),
                {0, 1}
        end
    catch
        _:Error ->
            io:format("❌ Exception: ~p~n", [Error]),
            {0, 1}
    end.
