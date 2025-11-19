%% Phase 2 SMT Translator Extended Tests
%% Tests for quantifiers, extended operators, and advanced features
-module(smt_translator_extended_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

run() ->
    io:format("~n=== SMT Translator Extended Tests (Phase 2) ===~n~n"),

    Tests = [
        fun test_modulo_operator/0,
        fun test_abs_function/0,
        fun test_min_function/0,
        fun test_max_function/0,
        fun test_length_function/0,
        fun test_forall_quantifier/0,
        fun test_exists_quantifier/0,
        fun test_quantifier_with_multiple_vars/0,
        fun test_logic_inference_with_quantifiers/0,
        fun test_nested_quantifiers/0,
        fun test_complex_quantified_formula/0,
        fun test_end_to_end_quantifier/0,
        % New AST record format tests
        fun test_forall_with_ast_record/0,
        fun test_exists_with_ast_record/0,
        fun test_nested_quantifiers_with_records/0
    ],

    Results = lists:map(fun run_test/1, Tests),

    Passed = length([R || R <- Results, R =:= ok]),
    Failed = length(Results) - Passed,

    io:format("~n=== Results ===~n"),
    io:format("Passed: ~p~n", [Passed]),
    io:format("Failed: ~p~n", [Failed]),
    io:format("Total:  ~p~n", [length(Results)]),

    case Failed of
        0 -> io:format("~n✅ All Phase 2 tests passed!~n~n");
        _ -> io:format("~n❌ Some Phase 2 tests failed!~n~n")
    end,

    ok.

run_test(TestFun) ->
    try
        TestFun(),
        ok
    catch
        Class:Reason:Stack ->
            io:format("  ❌ FAILED: ~p:~p~n", [Class, Reason]),
            io:format("     Stack: ~p~n", [Stack]),
            error
    end.

%% ============================================================================
%% Test: Modulo Operator
%% ============================================================================

test_modulo_operator() ->
    io:format("Testing modulo operator... "),

    % x mod 2 == 0 (even number)
    Expr = #binary_op_expr{
        op = 'mod',
        left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
        right = #literal_expr{value = 2, location = #location{line = 1, column = 5}},
        location = #location{line = 1, column = 1}
    },

    Result = cure_smt_translator:translate_expr(Expr),
    ResultStr = lists:flatten(Result),

    case lists:prefix("(mod x 2)", ResultStr) of
        true ->
            io:format("✅ ~s~n", [ResultStr]),
            ok;
        false ->
            io:format("❌ Expected '(mod x 2)', got: ~s~n", [ResultStr]),
            error(unexpected_result)
    end.

%% ============================================================================
%% Test: abs Function
%% ============================================================================

test_abs_function() ->
    io:format("Testing abs function... "),

    % abs(x)
    Expr = #function_call_expr{
        function = #identifier_expr{name = abs, location = #location{line = 1, column = 1}},
        args = [#identifier_expr{name = x, location = #location{line = 1, column = 5}}],
        location = #location{line = 1, column = 1}
    },

    Result = cure_smt_translator:translate_expr(Expr),
    ResultStr = lists:flatten(Result),

    case lists:prefix("(abs x)", ResultStr) of
        true ->
            io:format("✅ ~s~n", [ResultStr]),
            ok;
        false ->
            io:format("❌ Expected '(abs x)', got: ~s~n", [ResultStr]),
            error(unexpected_result)
    end.

%% ============================================================================
%% Test: min Function
%% ============================================================================

test_min_function() ->
    io:format("Testing min function... "),

    % min(x, y)
    Expr = #function_call_expr{
        function = #identifier_expr{name = min, location = #location{line = 1, column = 1}},
        args = [
            #identifier_expr{name = x, location = #location{line = 1, column = 5}},
            #identifier_expr{name = y, location = #location{line = 1, column = 8}}
        ],
        location = #location{line = 1, column = 1}
    },

    Result = cure_smt_translator:translate_expr(Expr),
    ResultStr = lists:flatten(Result),

    % min is translated to ite(x < y, x, y)
    case string:str(ResultStr, "(ite (< x y) x y)") > 0 of
        true ->
            io:format("✅ ~s~n", [ResultStr]),
            ok;
        false ->
            io:format("❌ Expected min to translate to ite, got: ~s~n", [ResultStr]),
            error(unexpected_result)
    end.

%% ============================================================================
%% Test: max Function
%% ============================================================================

test_max_function() ->
    io:format("Testing max function... "),

    % max(x, y)
    Expr = #function_call_expr{
        function = #identifier_expr{name = max, location = #location{line = 1, column = 1}},
        args = [
            #identifier_expr{name = x, location = #location{line = 1, column = 5}},
            #identifier_expr{name = y, location = #location{line = 1, column = 8}}
        ],
        location = #location{line = 1, column = 1}
    },

    Result = cure_smt_translator:translate_expr(Expr),
    ResultStr = lists:flatten(Result),

    % max is translated to ite(x > y, x, y)
    case string:str(ResultStr, "(ite (> x y) x y)") > 0 of
        true ->
            io:format("✅ ~s~n", [ResultStr]),
            ok;
        false ->
            io:format("❌ Expected max to translate to ite, got: ~s~n", [ResultStr]),
            error(unexpected_result)
    end.

%% ============================================================================
%% Test: length Function
%% ============================================================================

test_length_function() ->
    io:format("Testing length function... "),

    % length(xs)
    Expr = #function_call_expr{
        function = #identifier_expr{name = length, location = #location{line = 1, column = 1}},
        args = [#identifier_expr{name = xs, location = #location{line = 1, column = 8}}],
        location = #location{line = 1, column = 1}
    },

    Result = cure_smt_translator:translate_expr(Expr),
    ResultStr = lists:flatten(Result),

    case lists:prefix("(length xs)", ResultStr) of
        true ->
            io:format("✅ ~s~n", [ResultStr]),
            ok;
        false ->
            io:format("❌ Expected '(length xs)', got: ~s~n", [ResultStr]),
            error(unexpected_result)
    end.

%% ============================================================================
%% Test: forall Quantifier
%% ============================================================================

test_forall_quantifier() ->
    io:format("Testing forall quantifier... "),

    % forall x: Int. x >= 0 => x + 1 > 0
    Body = #binary_op_expr{
        op = '=>',
        left = #binary_op_expr{
            op = '>=',
            left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
            right = #literal_expr{value = 0, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        },
        right = #binary_op_expr{
            op = '>',
            left = #binary_op_expr{
                op = '+',
                left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
                right = #literal_expr{value = 1, location = #location{line = 1, column = 1}},
                location = #location{line = 1, column = 1}
            },
            right = #literal_expr{value = 0, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        },
        location = #location{line = 1, column = 1}
    },

    Expr = {forall_expr, [{x, int}], Body},

    Result = cure_smt_translator:translate_expr(Expr, #{x => {type, int}}),
    ResultStr = lists:flatten(Result),

    case string:str(ResultStr, "(forall ((x Int))") > 0 of
        true ->
            io:format("✅ ~s~n", [ResultStr]),
            ok;
        false ->
            io:format("❌ Expected forall quantifier, got: ~s~n", [ResultStr]),
            error(unexpected_result)
    end.

%% ============================================================================
%% Test: exists Quantifier
%% ============================================================================

test_exists_quantifier() ->
    io:format("Testing exists quantifier... "),

    % exists x: Int. x > 0 and x < 10
    Body = #binary_op_expr{
        op = 'and',
        left = #binary_op_expr{
            op = '>',
            left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
            right = #literal_expr{value = 0, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        },
        right = #binary_op_expr{
            op = '<',
            left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
            right = #literal_expr{value = 10, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        },
        location = #location{line = 1, column = 1}
    },

    Expr = {exists_expr, [{x, int}], Body},

    Result = cure_smt_translator:translate_expr(Expr, #{x => {type, int}}),
    ResultStr = lists:flatten(Result),

    case string:str(ResultStr, "(exists ((x Int))") > 0 of
        true ->
            io:format("✅ ~s~n", [ResultStr]),
            ok;
        false ->
            io:format("❌ Expected exists quantifier, got: ~s~n", [ResultStr]),
            error(unexpected_result)
    end.

%% ============================================================================
%% Test: Quantifier with Multiple Variables
%% ============================================================================

test_quantifier_with_multiple_vars() ->
    io:format("Testing quantifier with multiple variables... "),

    % forall x, y: Int. x + y == y + x
    Body = #binary_op_expr{
        op = '==',
        left = #binary_op_expr{
            op = '+',
            left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
            right = #identifier_expr{name = y, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        },
        right = #binary_op_expr{
            op = '+',
            left = #identifier_expr{name = y, location = #location{line = 1, column = 1}},
            right = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        },
        location = #location{line = 1, column = 1}
    },

    Expr = {forall_expr, [{x, int}, {y, int}], Body},

    Result = cure_smt_translator:translate_expr(Expr, #{}),
    ResultStr = lists:flatten(Result),

    HasX = string:str(ResultStr, "(x Int)") > 0,
    HasY = string:str(ResultStr, "(y Int)") > 0,

    case HasX and HasY of
        true ->
            io:format("✅ ~s~n", [ResultStr]),
            ok;
        false ->
            io:format("❌ Expected both variables, got: ~s~n", [ResultStr]),
            error(unexpected_result)
    end.

%% ============================================================================
%% Test: Logic Inference with Quantifiers
%% ============================================================================

test_logic_inference_with_quantifiers() ->
    io:format("Testing logic inference with quantifiers... "),

    % Should infer LIA (not QF_LIA) due to quantifier
    Body = #binary_op_expr{
        op = '>',
        left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
        right = #literal_expr{value = 0, location = #location{line = 1, column = 1}},
        location = #location{line = 1, column = 1}
    },

    Expr = {forall_expr, [{x, int}], Body},

    Logic = cure_smt_translator:infer_logic(Expr),

    case Logic of
        'LIA' ->
            io:format("✅ Inferred LIA~n"),
            ok;
        Other ->
            io:format("❌ Expected LIA, got: ~p~n", [Other]),
            error(unexpected_logic)
    end.

%% ============================================================================
%% Test: Nested Quantifiers
%% ============================================================================

test_nested_quantifiers() ->
    io:format("Testing nested quantifiers... "),

    % forall x. exists y. x + y == 0
    InnerBody = #binary_op_expr{
        op = '==',
        left = #binary_op_expr{
            op = '+',
            left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
            right = #identifier_expr{name = y, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        },
        right = #literal_expr{value = 0, location = #location{line = 1, column = 1}},
        location = #location{line = 1, column = 1}
    },

    ExistsExpr = {exists_expr, [{y, int}], InnerBody},
    ForallExpr = {forall_expr, [{x, int}], ExistsExpr},

    Result = cure_smt_translator:translate_expr(ForallExpr, #{}),
    ResultStr = lists:flatten(Result),

    HasForall = string:str(ResultStr, "(forall") > 0,
    HasExists = string:str(ResultStr, "(exists") > 0,

    case HasForall and HasExists of
        true ->
            io:format("✅ Nested quantifiers translated~n"),
            ok;
        false ->
            io:format("❌ Expected nested quantifiers, got: ~s~n", [ResultStr]),
            error(unexpected_result)
    end.

%% ============================================================================
%% Test: Complex Quantified Formula
%% ============================================================================

test_complex_quantified_formula() ->
    io:format("Testing complex quantified formula... "),

    % forall x: Int. (x > 0 => abs(x) == x)
    AbsCall = #function_call_expr{
        function = #identifier_expr{name = abs, location = #location{line = 1, column = 1}},
        args = [#identifier_expr{name = x, location = #location{line = 1, column = 1}}],
        location = #location{line = 1, column = 1}
    },

    Body = #binary_op_expr{
        op = '=>',
        left = #binary_op_expr{
            op = '>',
            left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
            right = #literal_expr{value = 0, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        },
        right = #binary_op_expr{
            op = '==',
            left = AbsCall,
            right = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        },
        location = #location{line = 1, column = 1}
    },

    Expr = {forall_expr, [{x, int}], Body},

    Result = cure_smt_translator:translate_expr(Expr, #{}),
    ResultStr = lists:flatten(Result),

    HasForall = string:str(ResultStr, "(forall") > 0,
    HasAbs = string:str(ResultStr, "(abs x)") > 0,
    HasImplication = string:str(ResultStr, "(=>") > 0,

    case HasForall and HasAbs and HasImplication of
        true ->
            io:format("✅ Complex formula translated~n"),
            ok;
        false ->
            io:format("❌ Expected complex formula, got: ~s~n", [ResultStr]),
            error(unexpected_result)
    end.

%% ============================================================================
%% Test: End-to-End Quantifier Query
%% ============================================================================

test_end_to_end_quantifier() ->
    io:format("Testing end-to-end quantifier query... "),

    % Test if Z3 can handle a quantified query
    % forall x: Int. x + 0 == x
    Body = #binary_op_expr{
        op = '==',
        left = #binary_op_expr{
            op = '+',
            left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
            right = #literal_expr{value = 0, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        },
        right = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
        location = #location{line = 1, column = 1}
    },

    Expr = {forall_expr, [{x, int}], Body},

    Query = cure_smt_translator:generate_query(Expr, #{}, #{}),
    QueryStr = iolist_to_binary(Query),

    % Check query contains all necessary parts
    HasLogic = binary:match(QueryStr, <<"(set-logic">>) =/= nomatch,
    HasForall = binary:match(QueryStr, <<"(forall">>) =/= nomatch,
    HasCheckSat = binary:match(QueryStr, <<"(check-sat)">>) =/= nomatch,

    case HasLogic and HasForall and HasCheckSat of
        true ->
            io:format("✅ Full query generated~n"),
            ok;
        false ->
            io:format("❌ Query missing components: ~s~n", [QueryStr]),
            error(incomplete_query)
    end.

%% ============================================================================
%% Test: forall with AST Record
%% ============================================================================

test_forall_with_ast_record() ->
    io:format("Testing forall with AST record... "),

    % forall x: Int. x >= 0 => x + 1 > 0 (using #forall_expr{} record)
    Body = #binary_op_expr{
        op = '=>',
        left = #binary_op_expr{
            op = '>=',
            left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
            right = #literal_expr{value = 0, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        },
        right = #binary_op_expr{
            op = '>',
            left = #binary_op_expr{
                op = '+',
                left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
                right = #literal_expr{value = 1, location = #location{line = 1, column = 1}},
                location = #location{line = 1, column = 1}
            },
            right = #literal_expr{value = 0, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        },
        location = #location{line = 1, column = 1}
    },

    % Use new AST record format
    Expr = #forall_expr{
        variables = [{x, int}],
        body = Body,
        location = #location{line = 1, column = 1}
    },

    Result = cure_smt_translator:translate_expr(Expr, #{x => {type, int}}),
    ResultStr = lists:flatten(Result),

    case string:str(ResultStr, "(forall ((x Int))") > 0 of
        true ->
            io:format("✅ ~s~n", [ResultStr]),
            ok;
        false ->
            io:format("❌ Expected forall quantifier, got: ~s~n", [ResultStr]),
            error(unexpected_result)
    end.

%% ============================================================================
%% Test: exists with AST Record
%% ============================================================================

test_exists_with_ast_record() ->
    io:format("Testing exists with AST record... "),

    % exists x: Int. x > 0 and x < 10 (using #exists_expr{} record)
    Body = #binary_op_expr{
        op = 'and',
        left = #binary_op_expr{
            op = '>',
            left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
            right = #literal_expr{value = 0, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        },
        right = #binary_op_expr{
            op = '<',
            left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
            right = #literal_expr{value = 10, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        },
        location = #location{line = 1, column = 1}
    },

    % Use new AST record format
    Expr = #exists_expr{
        variables = [{x, int}],
        body = Body,
        location = #location{line = 1, column = 1}
    },

    Result = cure_smt_translator:translate_expr(Expr, #{x => {type, int}}),
    ResultStr = lists:flatten(Result),

    case string:str(ResultStr, "(exists ((x Int))") > 0 of
        true ->
            io:format("✅ ~s~n", [ResultStr]),
            ok;
        false ->
            io:format("❌ Expected exists quantifier, got: ~s~n", [ResultStr]),
            error(unexpected_result)
    end.

%% ============================================================================
%% Test: Nested Quantifiers with AST Records
%% ============================================================================

test_nested_quantifiers_with_records() ->
    io:format("Testing nested quantifiers with AST records... "),

    % forall x. exists y. x + y == 0
    InnerBody = #binary_op_expr{
        op = '==',
        left = #binary_op_expr{
            op = '+',
            left = #identifier_expr{name = x, location = #location{line = 1, column = 1}},
            right = #identifier_expr{name = y, location = #location{line = 1, column = 1}},
            location = #location{line = 1, column = 1}
        },
        right = #literal_expr{value = 0, location = #location{line = 1, column = 1}},
        location = #location{line = 1, column = 1}
    },

    ExistsExpr = #exists_expr{
        variables = [{y, int}],
        body = InnerBody,
        location = #location{line = 1, column = 1}
    },

    ForallExpr = #forall_expr{
        variables = [{x, int}],
        body = ExistsExpr,
        location = #location{line = 1, column = 1}
    },

    Result = cure_smt_translator:translate_expr(ForallExpr, #{}),
    ResultStr = lists:flatten(Result),

    HasForall = string:str(ResultStr, "(forall") > 0,
    HasExists = string:str(ResultStr, "(exists") > 0,

    case HasForall and HasExists of
        true ->
            io:format("✅ Nested quantifiers with records translated~n"),
            ok;
        false ->
            io:format("❌ Expected nested quantifiers, got: ~s~n", [ResultStr]),
            error(unexpected_result)
    end.
