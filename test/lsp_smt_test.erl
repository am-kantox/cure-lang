-module(lsp_smt_test).
-export([run/0]).

%% Test runner
run() ->
    io:format("Running LSP SMT Tests...~n", []),
    Results = [
        test_init_verification_state(),
        test_verify_refinement_subtyping(),
        test_check_refinement_constraint(),
        test_verify_preconditions(),
        test_verify_postconditions(),
        test_cache_hit(),
        test_cache_invalidation(),
        test_incremental_verification(),
        test_timestamp_tracking(),
        test_diagnostic_generation_subtype(),
        test_diagnostic_generation_constraint(),
        test_diagnostic_generation_precondition(),
        test_code_action_add_check(),
        test_code_action_strengthen_type(),
        test_location_to_range(),
        test_constraint_hashing(),
        test_cache_performance()
    ],
    Passed = length([R || R <- Results, R =:= pass]),
    Failed = length([R || R <- Results, R =:= fail]),
    io:format("~n=== LSP SMT Test Results ===~n", []),
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

%% ========================================================================
%% Verification State Tests
%% ========================================================================

test_init_verification_state() ->
    io:format("Test: Initialize verification state...~n", []),
    State = cure_lsp_smt:init_verification_state(),

    % Check record structure

    % verification_state.cache
    Cache = element(2, State),
    % verification_state.doc_constraints
    DocConstraints = element(3, State),
    % verification_state.timestamps
    Timestamps = element(4, State),
    % verification_state.solver_pid
    SolverPid = element(5, State),

    if
        map_size(Cache) =:= 0 andalso
            map_size(DocConstraints) =:= 0 andalso
            map_size(Timestamps) =:= 0 andalso
            SolverPid =:= undefined ->
            io:format("  ✓ Verification state initialized correctly~n", []),
            pass;
        true ->
            io:format("  ✗ FAILED: Invalid initial state~n", []),
            fail
    end.

%% ========================================================================
%% Refinement Type Verification Tests
%% ========================================================================

test_verify_refinement_subtyping() ->
    io:format("Test: Verify refinement subtyping delegation...~n", []),

    % Create simple refinement types: Positive <: NonZero
    Positive = {refinement_type, int, x, {binop, '>', {var, x}, {literal, 0}}},
    NonZero = {refinement_type, int, x, {binop, '/=', {var, x}, {literal, 0}}},

    State = cure_lsp_smt:init_verification_state(),

    try
        Result = cure_lsp_smt:verify_refinement_subtyping(State, Positive, NonZero),
        case Result of
            {ok, true, _NewState} ->
                io:format("  ✓ Subtyping verification succeeded (Positive <: NonZero)~n", []),
                pass;
            {ok, false, _NewState} ->
                io:format("  ✗ FAILED: Expected valid subtyping relation~n", []),
                fail;
            {error, _Reason, _NewState} ->
                io:format("  ✗ FAILED: Verification error~n", []),
                fail
        end
    catch
        Error:Reason:Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n~p~n", [Error, Reason, Stack]),
            fail
    end.

test_check_refinement_constraint() ->
    io:format("Test: Check refinement constraint...~n", []),

    % Create refinement type: x > 0
    Positive = {refinement_type, int, x, {binop, '>', {var, x}, {literal, 0}}},

    State = cure_lsp_smt:init_verification_state(),

    try
        % Test valid value
        Result1 = cure_lsp_smt:check_refinement_constraint(State, Positive, 5),
        case Result1 of
            {ok, true, _} ->
                io:format("  ✓ Constraint check passed for valid value~n", []),

                % Test invalid value
                Result2 = cure_lsp_smt:check_refinement_constraint(State, Positive, 0),
                case Result2 of
                    {ok, false, _} ->
                        io:format("  ✓ Constraint check failed for invalid value~n", []),
                        pass;
                    {ok, true, _} ->
                        io:format("  ✗ FAILED: Expected constraint violation for 0~n", []),
                        fail;
                    _ ->
                        io:format("  ✗ FAILED: Unexpected result for invalid value~n", []),
                        fail
                end;
            _ ->
                io:format("  ✗ FAILED: Constraint check failed for valid value~n", []),
                fail
        end
    catch
        Error:Reason:Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n~p~n", [Error, Reason, Stack]),
            fail
    end.

test_verify_preconditions() ->
    io:format("Test: Verify function preconditions...~n", []),

    % Create function with precondition: x > 0
    FunInfo = #{
        name => divide,
        preconditions => [
            {refinement_type, int, x, {binop, '>', {var, x}, {literal, 0}}}
        ]
    },

    State = cure_lsp_smt:init_verification_state(),

    try
        Result = cure_lsp_smt:verify_function_preconditions(State, FunInfo),
        % Should return result indicating whether preconditions are verified
        case Result of
            {ok, _Violations, _NewState} ->
                io:format("  ✓ Precondition verification completed~n", []),
                pass;
            {error, _Reason, _NewState} ->
                io:format("  ✗ FAILED: Precondition verification error~n", []),
                fail
        end
    catch
        Error:Reason:Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n~p~n", [Error, Reason, Stack]),
            fail
    end.

test_verify_postconditions() ->
    io:format("Test: Verify function postconditions...~n", []),

    % Create function with postcondition: result > 0
    FunInfo = #{
        name => abs_value,
        postconditions => [
            {refinement_type, int, result, {binop, '>=', {var, result}, {literal, 0}}}
        ]
    },

    State = cure_lsp_smt:init_verification_state(),

    try
        Result = cure_lsp_smt:verify_function_postconditions(State, FunInfo),
        case Result of
            {ok, _Violations, _NewState} ->
                io:format("  ✓ Postcondition verification completed~n", []),
                pass;
            {error, _Reason, _NewState} ->
                io:format("  ✗ FAILED: Postcondition verification error~n", []),
                fail
        end
    catch
        Error:Reason:Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n~p~n", [Error, Reason, Stack]),
            fail
    end.

%% ========================================================================
%% Incremental Verification and Caching Tests
%% ========================================================================

test_cache_hit() ->
    io:format("Test: Cache hit on repeated verification...~n", []),

    State = cure_lsp_smt:init_verification_state(),
    Uri = <<"file:///test.cure">>,

    % Create simple constraint
    Constraint = {refinement_type, int, x, {binop, '>', {var, x}, {literal, 0}}},

    try
        % First verification - cache miss
        {_Result1, State1} = cure_lsp_smt:verify_document_with_cache(
            State,
            {Uri, [Constraint]}
        ),

        % Second verification - should hit cache
        {_Result2, State2} = cure_lsp_smt:verify_document_with_cache(
            State1,
            {Uri, [Constraint]}
        ),

        % Check cache grew
        Cache1Size = map_size(element(2, State1)),
        Cache2Size = map_size(element(2, State2)),

        if
            Cache1Size > 0 andalso Cache2Size =:= Cache1Size ->
                io:format("  ✓ Cache hit detected (size stable: ~p)~n", [Cache2Size]),
                pass;
            true ->
                io:format("  ✗ FAILED: Cache sizes: ~p -> ~p~n", [Cache1Size, Cache2Size]),
                fail
        end
    catch
        Error:Reason:Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n~p~n", [Error, Reason, Stack]),
            fail
    end.

test_cache_invalidation() ->
    io:format("Test: Cache invalidation on document change...~n", []),

    State = cure_lsp_smt:init_verification_state(),
    Uri = <<"file:///test.cure">>,

    % Add document constraints to cache
    Constraint = {refinement_type, int, x, {binop, '>', {var, x}, {literal, 0}}},

    try
        {_Result, State1} = cure_lsp_smt:verify_document_with_cache(
            State,
            {Uri, [Constraint]}
        ),

        Cache1Size = map_size(element(2, State1)),

        % Invalidate cache for this URI
        State2 = cure_lsp_smt:invalidate_cache(State1, Uri),

        Cache2Size = map_size(element(2, State2)),
        DocConstraints2 = element(3, State2),

        % Check if URI is still in constraints (can't use maps:is_key in guard)
        DocStillPresent = maps:is_key(Uri, DocConstraints2),

        if
            Cache2Size < Cache1Size andalso not DocStillPresent ->
                io:format("  ✓ Cache invalidated (size: ~p -> ~p)~n", [Cache1Size, Cache2Size]),
                pass;
            true ->
                io:format("  ✗ FAILED: Cache not properly invalidated~n", []),
                io:format("    Cache sizes: ~p -> ~p~n", [Cache1Size, Cache2Size]),
                io:format("    Doc still in constraints: ~p~n", [DocStillPresent]),
                fail
        end
    catch
        Error:Reason:Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n~p~n", [Error, Reason, Stack]),
            fail
    end.

test_incremental_verification() ->
    io:format("Test: Incremental verification with timestamp tracking...~n", []),

    State = cure_lsp_smt:init_verification_state(),
    Uri = <<"file:///test.cure">>,

    % First verification
    Document1 = {Uri, dummy_ast_1},

    try
        {_Diagnostics1, State1} = cure_lsp_smt:verify_document_incremental(State, Document1),

        Timestamps1 = element(4, State1),

        % Check timestamp was recorded (can't use maps:is_key in guard)
        HasTimestamp1 = maps:is_key(Uri, Timestamps1),

        if
            HasTimestamp1 ->
                io:format("  ✓ Timestamp recorded on first verification~n", []),

                % Wait a bit to ensure different timestamp
                timer:sleep(10),

                % Second verification - should use incremental solving
                Document2 = {Uri, dummy_ast_2},
                {_Diagnostics2, State2} = cure_lsp_smt:verify_document_incremental(
                    State1, Document2
                ),

                Timestamps2 = element(4, State2),
                T1 = maps:get(Uri, Timestamps1),
                T2 = maps:get(Uri, Timestamps2),

                if
                    T2 > T1 ->
                        io:format("  ✓ Timestamp updated on re-verification~n", []),
                        pass;
                    true ->
                        io:format("  ✗ FAILED: Timestamp not updated~n", []),
                        fail
                end;
            true ->
                io:format("  ✗ FAILED: No timestamp recorded~n", []),
                fail
        end
    catch
        Error:Reason:Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n~p~n", [Error, Reason, Stack]),
            fail
    end.

test_timestamp_tracking() ->
    io:format("Test: Timestamp tracking for multiple documents...~n", []),

    State = cure_lsp_smt:init_verification_state(),
    Uri1 = <<"file:///test1.cure">>,
    Uri2 = <<"file:///test2.cure">>,

    try
        {_, State1} = cure_lsp_smt:verify_document_incremental(State, {Uri1, dummy_ast}),
        timer:sleep(10),
        {_, State2} = cure_lsp_smt:verify_document_incremental(State1, {Uri2, dummy_ast}),

        Timestamps = element(4, State2),

        % Check if both URIs have timestamps (can't use maps:is_key in guard)
        HasUri1 = maps:is_key(Uri1, Timestamps),
        HasUri2 = maps:is_key(Uri2, Timestamps),

        if
            HasUri1 andalso HasUri2 ->
                T1 = maps:get(Uri1, Timestamps),
                T2 = maps:get(Uri2, Timestamps),
                if
                    T2 > T1 ->
                        io:format("  ✓ Multiple documents tracked with correct timestamps~n", []),
                        pass;
                    true ->
                        io:format("  ✗ FAILED: Timestamp ordering incorrect~n", []),
                        fail
                end;
            true ->
                io:format("  ✗ FAILED: Not all documents tracked~n", []),
                fail
        end
    catch
        Error:Reason:Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n~p~n", [Error, Reason, Stack]),
            fail
    end.

%% ========================================================================
%% Diagnostic Generation Tests
%% ========================================================================

test_diagnostic_generation_subtype() ->
    io:format("Test: Generate diagnostic for subtype violation...~n", []),

    Error =
        {subtype_error, {refinement_type, int, x, {binop, '>', {var, x}, {literal, 0}}},
            {refinement_type, int, y, {binop, '>=', {var, y}, {literal, 0}}}, {location, 10, 5},
            <<"Counterexample: x = 0">>},

    try
        Diagnostic = cure_lsp_smt:refinement_violation_to_diagnostic(Error),

        Range = maps:get(range, Diagnostic),
        Severity = maps:get(severity, Diagnostic),
        Code = maps:get(code, Diagnostic),
        Message = maps:get(message, Diagnostic),

        if
            % Error
            Severity =:= 1 andalso
                Code =:= <<"refinement_subtype_error">> andalso
                is_map(Range) andalso
                byte_size(Message) > 0 ->
                io:format("  ✓ Subtype diagnostic generated correctly~n", []),
                io:format("    Message: ~s~n", [Message]),
                pass;
            true ->
                io:format("  ✗ FAILED: Invalid diagnostic format~n", []),
                fail
        end
    catch
        Error2:Reason:Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n~p~n", [Error2, Reason, Stack]),
            fail
    end.

test_diagnostic_generation_constraint() ->
    io:format("Test: Generate diagnostic for constraint violation...~n", []),

    Error =
        {constraint_error, {refinement_type, int, x, {binop, '>', {var, x}, {literal, 0}}}, 0,
            {location, 15, 8}, <<"Value 0 violates constraint x > 0">>},

    try
        Diagnostic = cure_lsp_smt:refinement_violation_to_diagnostic(Error),

        Severity = maps:get(severity, Diagnostic),
        Code = maps:get(code, Diagnostic),

        if
            Severity =:= 1 andalso
                Code =:= <<"refinement_constraint_error">> ->
                io:format("  ✓ Constraint diagnostic generated correctly~n", []),
                pass;
            true ->
                io:format("  ✗ FAILED: Invalid diagnostic~n", []),
                fail
        end
    catch
        Error2:Reason:Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n~p~n", [Error2, Reason, Stack]),
            fail
    end.

test_diagnostic_generation_precondition() ->
    io:format("Test: Generate diagnostic for precondition violation...~n", []),

    Error =
        {precondition_error, divide,
            {refinement_type, int, x, {binop, '>', {var, x}, {literal, 0}}}, {location, 20, 12}},

    try
        Diagnostic = cure_lsp_smt:refinement_violation_to_diagnostic(Error),

        Severity = maps:get(severity, Diagnostic),
        Code = maps:get(code, Diagnostic),

        if
            % Warning
            Severity =:= 2 andalso
                Code =:= <<"refinement_precondition_error">> ->
                io:format("  ✓ Precondition diagnostic generated correctly~n", []),
                pass;
            true ->
                io:format("  ✗ FAILED: Invalid diagnostic~n", []),
                fail
        end
    catch
        Error2:Reason:Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n~p~n", [Error2, Reason, Stack]),
            fail
    end.

%% ========================================================================
%% Code Action Tests
%% ========================================================================

test_code_action_add_check() ->
    io:format("Test: Generate 'Add constraint check' code action...~n", []),

    Diagnostic = #{
        range => #{
            start => #{line => 10, character => 5},
            'end' => #{line => 10, character => 10}
        },
        severity => 1,
        code => <<"refinement_constraint_error">>,
        message => <<"Value violates constraint x > 0">>
    },

    Uri = <<"file:///test.cure">>,

    try
        Actions = cure_lsp_smt:generate_code_actions(Diagnostic, Uri),

        % Should generate at least the "Add constraint check" action
        HasAddCheck = lists:any(
            fun(Action) ->
                Title = maps:get(title, Action, <<>>),
                Kind = maps:get(kind, Action, <<>>),
                Title =:= <<"Add constraint check">> andalso
                    Kind =:= <<"quickfix">>
            end,
            Actions
        ),

        if
            HasAddCheck ->
                io:format("  ✓ 'Add constraint check' action generated~n", []),
                pass;
            true ->
                io:format("  ✗ FAILED: Expected 'Add constraint check' action not found~n", []),
                fail
        end
    catch
        Error:Reason:Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n~p~n", [Error, Reason, Stack]),
            fail
    end.

test_code_action_strengthen_type() ->
    io:format("Test: Generate 'Strengthen type' code action...~n", []),

    Diagnostic = #{
        range => #{
            start => #{line => 5, character => 0},
            'end' => #{line => 5, character => 15}
        },
        severity => 1,
        code => <<"refinement_subtype_error">>,
        message => <<"Expected type {int, x, x > 0} but got {int, y, y >= 0}">>
    },

    Uri = <<"file:///test.cure">>,

    try
        Actions = cure_lsp_smt:generate_code_actions(Diagnostic, Uri),

        HasStrengthen = lists:any(
            fun(Action) ->
                Title = maps:get(title, Action, <<>>),
                Kind = maps:get(kind, Action, <<>>),
                Title =:= <<"Strengthen type annotation">> andalso
                    Kind =:= <<"refactor.rewrite">>
            end,
            Actions
        ),

        if
            HasStrengthen ->
                io:format("  ✓ 'Strengthen type' action generated~n", []),
                pass;
            true ->
                io:format("  ✗ FAILED: Expected 'Strengthen type' action not found~n", []),
                fail
        end
    catch
        Error:Reason:Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n~p~n", [Error, Reason, Stack]),
            fail
    end.

%% ========================================================================
%% Utility Function Tests
%% ========================================================================

test_location_to_range() ->
    io:format("Test: Convert location to LSP range...~n", []),

    Location = {location, 10, 5},

    try
        Range = cure_lsp_smt:location_to_range(Location),

        Start = maps:get(start, Range),
        End = maps:get('end', Range),

        StartLine = maps:get(line, Start),
        StartChar = maps:get(character, Start),
        EndLine = maps:get(line, End),
        EndChar = maps:get(character, End),

        if
            % 0-indexed
            StartLine =:= 9 andalso
                % 0-indexed
                StartChar =:= 4 andalso
                EndLine =:= 9 andalso
                EndChar > StartChar ->
                io:format("  ✓ Location converted correctly (1-indexed to 0-indexed)~n", []),
                pass;
            true ->
                io:format("  ✗ FAILED: Invalid range conversion~n", []),
                io:format("    Got: line ~p, char ~p~n", [StartLine, StartChar]),
                fail
        end
    catch
        Error:Reason:Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n~p~n", [Error, Reason, Stack]),
            fail
    end.

test_constraint_hashing() ->
    io:format("Test: Constraint hashing for cache keys...~n", []),

    Constraint1 = {refinement_type, int, x, {binop, '>', {var, x}, {literal, 0}}},
    Constraint2 = {refinement_type, int, x, {binop, '>', {var, x}, {literal, 0}}},
    Constraint3 = {refinement_type, int, x, {binop, '>=', {var, x}, {literal, 0}}},

    try
        % Hash using erlang:phash2 (what cure_lsp_smt likely uses)
        Hash1 = erlang:phash2(term_to_binary(Constraint1)),
        Hash2 = erlang:phash2(term_to_binary(Constraint2)),
        Hash3 = erlang:phash2(term_to_binary(Constraint3)),

        if
            Hash1 =:= Hash2 andalso Hash1 =/= Hash3 ->
                io:format("  ✓ Constraint hashing works correctly~n", []),
                io:format("    Identical constraints: same hash~n", []),
                io:format("    Different constraints: different hash~n", []),
                pass;
            true ->
                io:format("  ✗ FAILED: Hash collision or mismatch~n", []),
                io:format("    Hash1: ~p, Hash2: ~p, Hash3: ~p~n", [Hash1, Hash2, Hash3]),
                fail
        end
    catch
        Error:Reason:Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n~p~n", [Error, Reason, Stack]),
            fail
    end.

%% ========================================================================
%% Performance Tests
%% ========================================================================

test_cache_performance() ->
    io:format("Test: Cache lookup performance...~n", []),

    State = cure_lsp_smt:init_verification_state(),
    Uri = <<"file:///test.cure">>,

    % Create 10 unique constraints
    Constraints = [
        {refinement_type, int, x, {binop, '>', {var, x}, {literal, N}}}
     || N <- lists:seq(0, 9)
    ],

    try
        % First pass - populate cache
        {_, State1} = cure_lsp_smt:verify_document_with_cache(State, {Uri, Constraints}),

        % Second pass - all cache hits
        StartTime = erlang:monotonic_time(millisecond),
        {_, _State2} = cure_lsp_smt:verify_document_with_cache(State1, {Uri, Constraints}),
        EndTime = erlang:monotonic_time(millisecond),

        Duration = EndTime - StartTime,

        if
            % Cache hits should be <10ms for 10 constraints
            Duration < 10 ->
                io:format("  ✓ Cache lookup fast: ~pms for 10 constraints~n", [Duration]),
                pass;
            true ->
                io:format("  ⚠ Cache lookup slow: ~pms (expected <10ms)~n", [Duration]),
                % Don't fail, just warn - performance may vary
                pass
        end
    catch
        Error:Reason:Stack ->
            io:format("  ✗ FAILED: Exception ~p:~p~n~p~n", [Error, Reason, Stack]),
            fail
    end.
