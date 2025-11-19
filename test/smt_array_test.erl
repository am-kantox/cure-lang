%% Test suite for SMT Array Theory (Phase 5.1)
-module(smt_array_test).

-export([run/0]).

-include("../src/parser/cure_ast.hrl").

run() ->
    io:format("~n=== SMT Array Theory Tests (Phase 5.1) ===~n~n"),

    % Test 1: All elements positive
    {P1, F1} = test_all_elements_positive(),

    % Test 2: Exists element satisfying
    {P2, F2} = test_exists_element(),

    % Test 3: Sorted ascending
    {P3, F3} = test_sorted_ascending(),

    % Test 4: Sorted descending
    {P4, F4} = test_sorted_descending(),

    % Test 5: Array length constraint
    {P5, F5} = test_length_constraint(),

    % Test 6: Array select operation
    {P6, F6} = test_array_select(),

    % Test 7: Array store operation
    {P7, F7} = test_array_store(),

    % Test 8: Array constant
    {P8, F8} = test_array_const(),

    % Test 9: Query generation
    {P9, F9} = test_query_generation(),

    % Test 10: Array declaration
    {P10, F10} = test_array_declaration(),

    % Test 11: Complex constraint (all positive AND sorted)
    {P11, F11} = test_complex_constraint(),

    % Test 12: Quantifier detection
    {P12, F12} = test_quantifier_detection(),

    TotalPassed = P1 + P2 + P3 + P4 + P5 + P6 + P7 + P8 + P9 + P10 + P11 + P12,
    TotalFailed = F1 + F2 + F3 + F4 + F5 + F6 + F7 + F8 + F9 + F10 + F11 + F12,

    io:format("~n=== Results ===~n"),
    io:format("Passed: ~p~n", [TotalPassed]),
    io:format("Failed: ~p~n", [TotalFailed]),

    case TotalFailed of
        0 ->
            io:format("~n✅ All Phase 5.1 array theory tests passed!~n"),
            halt(0);
        _ ->
            io:format("~n❌ Some tests failed~n"),
            halt(1)
    end.

%% ============================================================================
%% Test Cases
%% ============================================================================

test_all_elements_positive() ->
    io:format("Testing all elements positive constraint... "),
    try
        PropertyFn = fun(_I, V) ->
            #binary_op_expr{
                op = '>',
                left = V,
                right = #literal_expr{value = 0, location = #location{}},
                location = #location{}
            }
        end,

        Constraint = cure_smt_array:all_elements_satisfy(arr, n, PropertyFn),

        % Check it's a forall expression
        case Constraint of
            {forall_expr, [{_IndexVar, int}], _Body} ->
                io:format("✅ All elements constraint generated~n"),
                {1, 0};
            _ ->
                io:format("❌ Wrong constraint type~n"),
                {0, 1}
        end
    catch
        _:Error ->
            io:format("❌ Exception: ~p~n", [Error]),
            {0, 1}
    end.

test_exists_element() ->
    io:format("Testing exists element constraint... "),
    try
        PropertyFn = fun(_I, V) ->
            #binary_op_expr{
                op = '==',
                left = V,
                right = #literal_expr{value = 42, location = #location{}},
                location = #location{}
            }
        end,

        Constraint = cure_smt_array:exists_element_satisfying(arr, n, PropertyFn),

        case Constraint of
            {exists_expr, [{_IndexVar, int}], _Body} ->
                io:format("✅ Exists constraint generated~n"),
                {1, 0};
            _ ->
                io:format("❌ Wrong constraint type~n"),
                {0, 1}
        end
    catch
        _:Error ->
            io:format("❌ Exception: ~p~n", [Error]),
            {0, 1}
    end.

test_sorted_ascending() ->
    io:format("Testing sorted ascending constraint... "),
    try
        Constraint = cure_smt_array:sorted_ascending(arr, n),

        % Should be forall with 2 variables
        case Constraint of
            {forall_expr, Vars, _Body} when length(Vars) == 2 ->
                io:format("✅ Sorted ascending constraint generated~n"),
                {1, 0};
            _ ->
                io:format("❌ Wrong constraint structure~n"),
                {0, 1}
        end
    catch
        _:Error ->
            io:format("❌ Exception: ~p~n", [Error]),
            {0, 1}
    end.

test_sorted_descending() ->
    io:format("Testing sorted descending constraint... "),
    try
        Constraint = cure_smt_array:sorted_descending(arr, n),

        case Constraint of
            {forall_expr, Vars, _Body} when length(Vars) == 2 ->
                io:format("✅ Sorted descending constraint generated~n"),
                {1, 0};
            _ ->
                io:format("❌ Wrong constraint structure~n"),
                {0, 1}
        end
    catch
        _:Error ->
            io:format("❌ Exception: ~p~n", [Error]),
            {0, 1}
    end.

test_length_constraint() ->
    io:format("Testing length constraint... "),
    try
        % Test with integer
        Constraint1 = cure_smt_array:array_length_constraint(n, 10),

        % Test with variable
        Constraint2 = cure_smt_array:array_length_constraint(n, expected_len),

        IsExpr1 = is_record(Constraint1, binary_op_expr),
        IsExpr2 = is_record(Constraint2, binary_op_expr),

        case IsExpr1 andalso IsExpr2 of
            true ->
                io:format("✅ Length constraints generated~n"),
                {1, 0};
            false ->
                io:format("❌ Invalid length constraints~n"),
                {0, 1}
        end
    catch
        _:Error ->
            io:format("❌ Exception: ~p~n", [Error]),
            {0, 1}
    end.

test_array_select() ->
    io:format("Testing array select operation... "),
    try
        % Test with atom index
        Select1 = cure_smt_array:array_select(arr, i),

        % Test with integer index
        Select2 = cure_smt_array:array_select(arr, 5),

        IsCall1 = is_record(Select1, function_call_expr),
        IsCall2 = is_record(Select2, function_call_expr),

        case IsCall1 andalso IsCall2 of
            true ->
                io:format("✅ Array select operations generated~n"),
                {1, 0};
            false ->
                io:format("❌ Invalid select operations~n"),
                {0, 1}
        end
    catch
        _:Error ->
            io:format("❌ Exception: ~p~n", [Error]),
            {0, 1}
    end.

test_array_store() ->
    io:format("Testing array store operation... "),
    try
        Value = #literal_expr{value = 42, location = #location{}},

        % Test with atom index
        Store1 = cure_smt_array:array_store(arr, i, Value),

        % Test with integer index
        Store2 = cure_smt_array:array_store(arr, 3, Value),

        IsCall1 = is_record(Store1, function_call_expr),
        IsCall2 = is_record(Store2, function_call_expr),

        case IsCall1 andalso IsCall2 of
            true ->
                io:format("✅ Array store operations generated~n"),
                {1, 0};
            false ->
                io:format("❌ Invalid store operations~n"),
                {0, 1}
        end
    catch
        _:Error ->
            io:format("❌ Exception: ~p~n", [Error]),
            {0, 1}
    end.

test_array_const() ->
    io:format("Testing array const operation... "),
    try
        Const = cure_smt_array:array_const(0),

        case is_record(Const, function_call_expr) of
            true ->
                io:format("✅ Array const generated~n"),
                {1, 0};
            false ->
                io:format("❌ Invalid const~n"),
                {0, 1}
        end
    catch
        _:Error ->
            io:format("❌ Exception: ~p~n", [Error]),
            {0, 1}
    end.

test_query_generation() ->
    io:format("Testing array query generation... "),
    try
        PropertyFn = fun(_I, V) ->
            #binary_op_expr{
                op = '>',
                left = V,
                right = #literal_expr{value = 0, location = #location{}},
                location = #location{}
            }
        end,

        Constraint = cure_smt_array:all_elements_satisfy(arr, n, PropertyFn),
        Env = #{arr => {array, int, int}, n => {type, int}},

        Query = cure_smt_array:generate_array_query(Constraint, Env),
        QueryBin = iolist_to_binary(Query),
        QueryStr = binary_to_list(QueryBin),

        % Check for key components
        HasLogic = string:str(QueryStr, "set-logic") > 0,
        HasDeclare = string:str(QueryStr, "declare-const") > 0,
        HasAssert = string:str(QueryStr, "assert") > 0,
        HasCheckSat = string:str(QueryStr, "check-sat") > 0,

        case HasLogic andalso HasDeclare andalso HasAssert andalso HasCheckSat of
            true ->
                io:format("✅ Query generated with all components~n"),
                {1, 0};
            false ->
                io:format("❌ Missing query components~n"),
                {0, 1}
        end
    catch
        _:Error ->
            io:format("❌ Exception: ~p~n", [Error]),
            {0, 1}
    end.

test_array_declaration() ->
    io:format("Testing array declaration... "),
    try
        Decl = cure_smt_array:declare_array(arr, int, int),
        DeclBin = iolist_to_binary(Decl),
        DeclStr = binary_to_list(DeclBin),

        HasDeclare = string:str(DeclStr, "declare-const") > 0,
        HasArray = string:str(DeclStr, "Array") > 0,
        HasName = string:str(DeclStr, "arr") > 0,

        case HasDeclare andalso HasArray andalso HasName of
            true ->
                io:format("✅ Array declaration generated~n"),
                {1, 0};
            false ->
                io:format("❌ Invalid declaration~n"),
                {0, 1}
        end
    catch
        _:Error ->
            io:format("❌ Exception: ~p~n", [Error]),
            {0, 1}
    end.

test_complex_constraint() ->
    io:format("Testing complex constraint (all positive AND sorted)... "),
    try
        % All elements positive
        PositiveFn = fun(_I, V) ->
            #binary_op_expr{
                op = '>',
                left = V,
                right = #literal_expr{value = 0, location = #location{}},
                location = #location{}
            }
        end,
        AllPositive = cure_smt_array:all_elements_satisfy(arr, n, PositiveFn),

        % Sorted
        Sorted = cure_smt_array:sorted_ascending(arr, n),

        % Combine with AND
        Combined = #binary_op_expr{
            op = 'and',
            left = AllPositive,
            right = Sorted,
            location = #location{}
        },

        % Generate query
        Env = #{arr => {array, int, int}, n => {type, int}},
        Query = cure_smt_array:generate_array_query(Combined, Env),

        case is_list(Query) orelse is_binary(Query) of
            true ->
                io:format("✅ Complex constraint query generated~n"),
                {1, 0};
            false ->
                io:format("❌ Invalid query~n"),
                {0, 1}
        end
    catch
        _:Error ->
            io:format("❌ Exception: ~p~n", [Error]),
            {0, 1}
    end.

test_quantifier_detection() ->
    io:format("Testing quantifier detection... "),
    try
        % Test forall
        Forall = {forall_expr, [{i, int}], #literal_expr{value = true, location = #location{}}},
        HasForall = cure_smt_array:has_quantifiers(Forall),

        % Test exists
        Exists = {exists_expr, [{i, int}], #literal_expr{value = true, location = #location{}}},
        HasExists = cure_smt_array:has_quantifiers(Exists),

        % Test no quantifier
        Plain = #literal_expr{value = 42, location = #location{}},
        NoQuant = not cure_smt_array:has_quantifiers(Plain),

        case HasForall andalso HasExists andalso NoQuant of
            true ->
                io:format("✅ Quantifier detection works~n"),
                {1, 0};
            false ->
                io:format("❌ Quantifier detection failed~n"),
                {0, 1}
        end
    catch
        _:Error ->
            io:format("❌ Exception: ~p~n", [Error]),
            {0, 1}
    end.
