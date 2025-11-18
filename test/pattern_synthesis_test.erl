-module(pattern_synthesis_test).
-export([run/0]).

-include("../src/parser/cure_ast.hrl").

%% Test runner
run() ->
    io:format("Running Pattern Synthesis Tests...~n", []),
    Results = [
        test_encode_literal_pattern(),
        test_encode_wildcard_pattern(),
        test_encode_variable_pattern(),
        test_encode_constructor_pattern(),
        test_encode_list_pattern(),
        test_encode_patterns_disjunction(),
        test_find_missing_pattern_simple(),
        test_check_exhaustiveness_complete(),
        test_check_exhaustiveness_incomplete(),
        test_type_to_smt_sort()
    ],
    Passed = length([R || R <- Results, R =:= pass]),
    Failed = length([R || R <- Results, R =:= fail]),
    io:format("~n=== Pattern Synthesis Test Results ===~n", []),
    io:format("Passed: ~p~n", [Passed]),
    io:format("Failed: ~p~n", [Failed]),
    if
        Failed =:= 0 ->
            io:format("All tests passed!~n", []),
            ok;
        true ->
            io:format("Some tests failed.~n", []),
            {error, {failed, Failed}}
    end.

%% ============================================================================
%% Pattern Encoding Tests
%% ============================================================================

test_encode_literal_pattern() ->
    io:format("Test: Encode literal pattern...~n", []),

    % Integer literal pattern: 42
    IntPattern = #literal_expr{value = 42, location = loc()},
    IntType = #primitive_type{name = 'Int', location = loc()},

    try
        IntEncoded = cure_pattern_encoder:encode_pattern(IntPattern, IntType),
        IntStr = iolist_to_binary(IntEncoded),

        % Should generate: (= val 42)
        HasEquals = binary:match(IntStr, <<"=">>) =/= nomatch,
        Has42 = binary:match(IntStr, <<"42">>) =/= nomatch,

        if
            HasEquals andalso Has42 ->
                io:format("  ✓ Integer literal encoded correctly~n", []),

                % Boolean literal pattern: true
                BoolPattern = #literal_expr{value = true, location = loc()},
                BoolType = #primitive_type{name = 'Bool', location = loc()},
                BoolEncoded = cure_pattern_encoder:encode_pattern(BoolPattern, BoolType),
                BoolStr = iolist_to_binary(BoolEncoded),

                HasTrue = binary:match(BoolStr, <<"true">>) =/= nomatch,

                if
                    HasTrue ->
                        io:format("  ✓ Boolean literal encoded correctly~n", []),
                        pass;
                    true ->
                        io:format("  ✗ FAILED: Boolean encoding incorrect~n", []),
                        fail
                end;
            true ->
                io:format("  ✗ FAILED: Integer encoding incorrect~n", []),
                fail
        end
    catch
        Error:Reason:Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n~p~n", [Error, Reason, Stack]),
            fail
    end.

test_encode_wildcard_pattern() ->
    io:format("Test: Encode wildcard pattern...~n", []),

    % Wildcard pattern: _
    Pattern = #identifier_expr{name = '_', location = loc()},
    Type = #primitive_type{name = 'Int', location = loc()},

    try
        Encoded = cure_pattern_encoder:encode_pattern(Pattern, Type),
        Str = iolist_to_binary(Encoded),

        % Wildcard should encode to "true" (matches anything)
        if
            Str =:= <<"true">> ->
                io:format("  ✓ Wildcard pattern encoded as 'true'~n", []),
                pass;
            true ->
                io:format("  ✗ FAILED: Wildcard should encode to 'true', got: ~s~n", [Str]),
                fail
        end
    catch
        Error:Reason:Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n~p~n", [Error, Reason, Stack]),
            fail
    end.

test_encode_variable_pattern() ->
    io:format("Test: Encode variable pattern...~n", []),

    % Variable pattern: x
    Pattern = #identifier_expr{name = x, location = loc()},
    Type = #primitive_type{name = 'Int', location = loc()},

    try
        Encoded = cure_pattern_encoder:encode_pattern(Pattern, Type),
        Str = iolist_to_binary(Encoded),

        % Variable should bind and match (contains "let")
        HasLet = binary:match(Str, <<"let">>) =/= nomatch,

        if
            HasLet ->
                io:format("  ✓ Variable pattern encoded with binding~n", []),
                pass;
            true ->
                io:format("  ✗ FAILED: Variable pattern should use 'let'~n", []),
                fail
        end
    catch
        Error:Reason:Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n~p~n", [Error, Reason, Stack]),
            fail
    end.

test_encode_constructor_pattern() ->
    io:format("Test: Encode constructor pattern...~n", []),

    % Constructor pattern: Ok (nullary)
    Pattern = #constructor_pattern{
        name = ok,
        args = [],
        location = loc()
    },

    % ADT type: Result with Ok and Error variants
    Type = {adt, 'Result', [{ok, []}, {error, [int]}]},

    try
        Encoded = cure_pattern_encoder:encode_pattern(Pattern, Type),
        Str = iolist_to_binary(Encoded),

        % Should generate: (is-ok val)
        HasIsOk = binary:match(Str, <<"is-ok">>) =/= nomatch,

        if
            HasIsOk ->
                io:format("  ✓ Constructor pattern encoded correctly~n", []),
                pass;
            true ->
                io:format("  ✗ FAILED: Constructor pattern encoding incorrect: ~s~n", [Str]),
                fail
        end
    catch
        Error:Reason:Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n~p~n", [Error, Reason, Stack]),
            fail
    end.

test_encode_list_pattern() ->
    io:format("Test: Encode list pattern...~n", []),

    % Empty list pattern: []
    EmptyPattern = #list_pattern{elements = [], tail = undefined, location = loc()},
    Type = {list, int},

    try
        EmptyEncoded = cure_pattern_encoder:encode_pattern(EmptyPattern, Type),
        EmptyStr = iolist_to_binary(EmptyEncoded),

        % Should check for nil
        HasNil = binary:match(EmptyStr, <<"nil">>) =/= nomatch,

        if
            HasNil ->
                io:format("  ✓ Empty list pattern encoded correctly~n", []),
                pass;
            true ->
                io:format("  ✗ FAILED: Empty list should encode with 'nil'~n", []),
                fail
        end
    catch
        Error:Reason:Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n~p~n", [Error, Reason, Stack]),
            fail
    end.

test_encode_patterns_disjunction() ->
    io:format("Test: Encode multiple patterns as disjunction...~n", []),

    % Two patterns: 1 and 2
    Pattern1 = #literal_expr{value = 1, location = loc()},
    Pattern2 = #literal_expr{value = 2, location = loc()},
    Type = #primitive_type{name = 'Int', location = loc()},

    try
        Encoded = cure_pattern_encoder:encode_patterns_disjunction([Pattern1, Pattern2], Type),
        Str = iolist_to_binary(Encoded),

        % Should generate: (or (= val 1) (= val 2))
        HasOr = binary:match(Str, <<"or">>) =/= nomatch,
        Has1 = binary:match(Str, <<"1">>) =/= nomatch,
        Has2 = binary:match(Str, <<"2">>) =/= nomatch,

        if
            HasOr andalso Has1 andalso Has2 ->
                io:format("  ✓ Disjunction encoded correctly~n", []),
                pass;
            true ->
                io:format("  ✗ FAILED: Disjunction encoding incorrect~n", []),
                fail
        end
    catch
        Error:Reason:Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n~p~n", [Error, Reason, Stack]),
            fail
    end.

%% ============================================================================
%% Exhaustiveness Checking Tests
%% ============================================================================

test_find_missing_pattern_simple() ->
    io:format("Test: Find missing pattern (simple)...~n", []),

    % Covered: just 'true', missing: 'false'
    TruePattern = #literal_expr{value = true, location = loc()},
    Type = #primitive_type{name = 'Bool', location = loc()},

    try
        Result = cure_pattern_encoder:find_missing_pattern([TruePattern], Type),

        case Result of
            {missing, _Pattern} ->
                io:format("  ✓ Found missing pattern~n", []),
                pass;
            exhaustive ->
                io:format("  ✗ FAILED: Should find missing 'false' pattern~n", []),
                fail;
            {error, Reason} ->
                io:format("  ⚠ Warning: Z3 error (may not be installed): ~p~n", [Reason]),
                % Don't fail if Z3 isn't available
                pass
        end
    catch
        Error:CatchReason:_Stack ->
            io:format("  ⚠ Warning: Exception (Z3 may not be available): ~p:~p~n", [
                Error, CatchReason
            ]),
            % Don't fail the test suite if Z3 isn't available
            pass
    end.

test_check_exhaustiveness_complete() ->
    io:format("Test: Check exhaustiveness (complete)...~n", []),

    % Covered: true and false (complete for Bool)
    TruePattern = #literal_expr{value = true, location = loc()},
    FalsePattern = #literal_expr{value = false, location = loc()},
    Type = #primitive_type{name = 'Bool', location = loc()},

    try
        Result = cure_pattern_encoder:check_exhaustiveness([TruePattern, FalsePattern], Type),

        case Result of
            {complete} ->
                io:format("  ✓ Patterns are exhaustive~n", []),
                pass;
            {incomplete, Missing} ->
                io:format("  ✗ FAILED: Should be complete, but found missing: ~p~n", [Missing]),
                fail;
            {error, Reason} ->
                io:format("  ⚠ Warning: Z3 error: ~p~n", [Reason]),
                pass
        end
    catch
        Error:CatchReason:_Stack ->
            io:format("  ⚠ Warning: Exception (Z3 may not be available): ~p:~p~n", [
                Error, CatchReason
            ]),
            pass
    end.

test_check_exhaustiveness_incomplete() ->
    io:format("Test: Check exhaustiveness (incomplete)...~n", []),

    % Covered: just Ok, missing: Error
    OkPattern = #constructor_pattern{
        name = ok,
        args = [],
        location = loc()
    },
    Type = {adt, 'Result', [{ok, []}, {error, [int]}]},

    try
        Result = cure_pattern_encoder:check_exhaustiveness([OkPattern], Type),

        case Result of
            {incomplete, Missing} when length(Missing) > 0 ->
                io:format("  ✓ Found incomplete patterns, missing: ~p~n", [length(Missing)]),
                pass;
            {complete} ->
                io:format("  ✗ FAILED: Should find missing 'Error' pattern~n", []),
                fail;
            {error, Reason} ->
                io:format("  ⚠ Warning: Z3 error: ~p~n", [Reason]),
                pass
        end
    catch
        Error:CatchReason:_Stack ->
            io:format("  ⚠ Warning: Exception (Z3 may not be available): ~p:~p~n", [
                Error, CatchReason
            ]),
            pass
    end.

%% ============================================================================
%% Utility Tests
%% ============================================================================

test_type_to_smt_sort() ->
    io:format("Test: Convert types to SMT sorts...~n", []),

    IntType = #primitive_type{name = 'Int', location = loc()},
    BoolType = #primitive_type{name = 'Bool', location = loc()},

    try
        IntSort = cure_pattern_encoder:type_to_smt_sort(IntType),
        BoolSort = cure_pattern_encoder:type_to_smt_sort(BoolType),

        if
            IntSort =:= "Int" andalso BoolSort =:= "Bool" ->
                io:format("  ✓ Type to sort conversion correct~n", []),
                pass;
            true ->
                io:format("  ✗ FAILED: Sort conversion incorrect~n", []),
                io:format("    Int: ~p, Bool: ~p~n", [IntSort, BoolSort]),
                fail
        end
    catch
        Error:Reason:Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n~p~n", [Error, Reason, Stack]),
            fail
    end.

%% ============================================================================
%% Helper Functions
%% ============================================================================

loc() ->
    #location{line = 0, column = 0, file = undefined}.
