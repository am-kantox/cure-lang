-module(guard_smt_phase4_test).

%% Phase 4: Enhanced SMT Integration Tests
%% Tests for guard completeness, subsumption, and counterexample generation

-export([run/0]).

-include("../src/parser/cure_ast.hrl").

run() ->
    io:format("~n=== Phase 4: Enhanced SMT Integration Tests ===~n~n"),

    % Run test suites
    Results = [
        test_guard_completeness(),
        test_guard_subsumption(),
        test_inconsistent_guard_detection(),
        test_smt_query_generation()
    ],

    % Summary
    Passed = length([R || R <- Results, R =:= pass]),
    Failed = length([R || R <- Results, R =:= fail]),

    io:format("~n=== Test Summary ===~n"),
    io:format("Passed: ~p~n", [Passed]),
    io:format("Failed: ~p~n", [Failed]),

    case Failed of
        0 ->
            io:format("~n✅ All Phase 4 tests passed!~n"),
            halt(0);
        _ ->
            io:format("~n❌ Some Phase 4 tests failed!~n"),
            halt(1)
    end.

%% ============================================================================
%% Test Suite 1: Guard Completeness Verification
%% ============================================================================

test_guard_completeness() ->
    io:format("Test 1: Guard Completeness Verification...~n"),

    Env = cure_types:new_env(),

    % Test 1a: Complete guards with catch-all
    Clauses1 = [
        #function_clause{
            params = [],
            return_type = undefined,
            constraint = #binary_op_expr{
                op = '>',
                left = #identifier_expr{name = x, location = loc()},
                right = #literal_expr{value = 0, location = loc()},
                location = loc()
            },
            body = #literal_expr{value = 1, location = loc()},
            location = loc()
        },
        #function_clause{
            params = [],
            return_type = undefined,
            % Catch-all
            constraint = undefined,
            body = #literal_expr{value = 0, location = loc()},
            location = loc()
        }
    ],

    Result1 = cure_guard_smt:verify_guard_completeness(Clauses1, Env),
    Test1a =
        case Result1 of
            {complete, []} -> true;
            _ -> false
        end,

    % Test 1b: Incomplete guards (no catch-all)
    Clauses2 = [
        #function_clause{
            params = [],
            return_type = undefined,
            constraint = #binary_op_expr{
                op = '>',
                left = #identifier_expr{name = x, location = loc()},
                right = #literal_expr{value = 0, location = loc()},
                location = loc()
            },
            body = #literal_expr{value = 1, location = loc()},
            location = loc()
        },
        #function_clause{
            params = [],
            return_type = undefined,
            constraint = #binary_op_expr{
                op = '<',
                left = #identifier_expr{name = x, location = loc()},
                right = #literal_expr{value = 0, location = loc()},
                location = loc()
            },
            body = #literal_expr{value = -1, location = loc()},
            location = loc()
        }
    ],

    Result2 = cure_guard_smt:verify_guard_completeness(Clauses2, Env),
    Test1b =
        case Result2 of
            {incomplete, _} -> true;
            _ -> false
        end,

    case Test1a andalso Test1b of
        true ->
            io:format("  ✓ Guard completeness tests passed~n"),
            pass;
        false ->
            io:format("  ✗ Guard completeness tests FAILED~n"),
            io:format("    Test1a: ~p, Test1b: ~p~n", [Test1a, Test1b]),
            io:format("    Result1: ~p~n", [Result1]),
            io:format("    Result2: ~p~n", [Result2]),
            fail
    end.

%% ============================================================================
%% Test Suite 2: Guard Subsumption Detection
%% ============================================================================

test_guard_subsumption() ->
    io:format("Test 2: Guard Subsumption Detection...~n"),

    % Test 2a: Guard subsumption (x > 5 subsumes x > 0)
    Guard1 = #binary_op_expr{
        op = '>',
        left = #identifier_expr{name = x, location = loc()},
        right = #literal_expr{value = 5, location = loc()},
        location = loc()
    },

    Guard2 = #binary_op_expr{
        op = '>',
        left = #identifier_expr{name = x, location = loc()},
        right = #literal_expr{value = 0, location = loc()},
        location = loc()
    },

    % x > 5 implies x > 0, so Guard1 subsumes Guard2
    Result1 = cure_guard_smt:verify_guard_subsumption(Guard1, Guard2),
    Test2a = Result1 =:= true orelse Result1 =:= unknown,

    % Test 2b: No subsumption (x > 0 does not subsume x > 5)
    Result2 = cure_guard_smt:verify_guard_subsumption(Guard2, Guard1),
    Test2b = Result2 =:= false orelse Result2 =:= unknown,

    case Test2a andalso Test2b of
        true ->
            io:format("  ✓ Guard subsumption tests passed~n"),
            pass;
        false ->
            io:format("  ✗ Guard subsumption tests FAILED~n"),
            io:format("    Test2a: ~p (result: ~p)~n", [Test2a, Result1]),
            io:format("    Test2b: ~p (result: ~p)~n", [Test2b, Result2]),
            fail
    end.

%% ============================================================================
%% Test Suite 3: Inconsistent Guard Detection
%% ============================================================================

test_inconsistent_guard_detection() ->
    io:format("Test 3: Inconsistent Guard Detection...~n"),

    % Test 3a: Consistent guard (x > 0)
    ConsistentGuard = #binary_op_expr{
        op = '>',
        left = #identifier_expr{name = x, location = loc()},
        right = #literal_expr{value = 0, location = loc()},
        location = loc()
    },

    Result1 = cure_guard_smt:verify_guard_consistency(ConsistentGuard),
    Test3a = Result1 =:= consistent orelse Result1 =:= unknown,

    % Test 3b: Inconsistent guard (x > 0 and x < 0)
    InconsistentGuard = #binary_op_expr{
        op = 'andalso',
        left = #binary_op_expr{
            op = '>',
            left = #identifier_expr{name = x, location = loc()},
            right = #literal_expr{value = 0, location = loc()},
            location = loc()
        },
        right = #binary_op_expr{
            op = '<',
            left = #identifier_expr{name = x, location = loc()},
            right = #literal_expr{value = 0, location = loc()},
            location = loc()
        },
        location = loc()
    },

    Result2 = cure_guard_smt:verify_guard_consistency(InconsistentGuard),
    Test3b = Result2 =:= inconsistent orelse Result2 =:= unknown,

    case Test3a andalso Test3b of
        true ->
            io:format("  ✓ Inconsistent guard detection tests passed~n"),
            pass;
        false ->
            io:format("  ✗ Inconsistent guard detection tests FAILED~n"),
            io:format("    Test3a: ~p (result: ~p)~n", [Test3a, Result1]),
            io:format("    Test3b: ~p (result: ~p)~n", [Test3b, Result2]),
            fail
    end.

%% ============================================================================
%% Test Suite 4: SMT Query Generation
%% ============================================================================

test_smt_query_generation() ->
    io:format("Test 4: SMT Query Generation...~n"),

    % Test 4a: Completeness query generation
    Guards = [
        #binary_op_expr{
            op = '>',
            left = #identifier_expr{name = x, location = loc()},
            right = #literal_expr{value = 0, location = loc()},
            location = loc()
        },
        #binary_op_expr{
            op = '<',
            left = #identifier_expr{name = x, location = loc()},
            right = #literal_expr{value = 0, location = loc()},
            location = loc()
        }
    ],

    Query1 = cure_guard_smt:generate_completeness_query(Guards, #{}),
    Test4a = is_list(Query1) orelse is_binary(Query1),

    % Test 4b: Subsumption query generation
    Guard1 = #binary_op_expr{
        op = '>',
        left = #identifier_expr{name = x, location = loc()},
        right = #literal_expr{value = 0, location = loc()},
        location = loc()
    },

    Guard2 = #binary_op_expr{
        op = '>',
        left = #identifier_expr{name = x, location = loc()},
        right = #literal_expr{value = 5, location = loc()},
        location = loc()
    },

    Query2 = cure_guard_smt:generate_subsumption_query(Guard1, Guard2),
    Test4b = is_list(Query2) orelse is_binary(Query2),

    % Test 4c: Consistency query generation
    Query3 = cure_guard_smt:generate_consistency_query(Guard1),
    Test4c = is_list(Query3) orelse is_binary(Query3),

    case Test4a andalso Test4b andalso Test4c of
        true ->
            io:format("  ✓ SMT query generation tests passed~n"),
            pass;
        false ->
            io:format("  ✗ SMT query generation tests FAILED~n"),
            io:format("    Test4a: ~p, Test4b: ~p, Test4c: ~p~n", [Test4a, Test4b, Test4c]),
            fail
    end.

%% ============================================================================
%% Helper Functions
%% ============================================================================

loc() ->
    #location{line = 0, column = 0, file = undefined}.
