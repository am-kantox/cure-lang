%% Unit Tests for Standard Library Compilation Failure Reporting
%% Tests specifically for:
%% 4. Standard library compilation process correctly reports partial failures when some files fail to compile
-module(stdlib_compilation_failure_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").

%% Run stdlib compilation failure specific tests
run() ->
    cure_utils:debug("Running Stdlib Compilation Failure Tests...~n"),

    test_partial_compilation_failure_formatting(),
    test_individual_compile_failure_formatting(),
    test_beam_to_source_path_conversion(),
    test_missing_files_detection(),
    test_compilation_error_types(),
    test_error_message_aggregation(),

    cure_utils:debug("All stdlib compilation failure tests passed!~n").

%% ============================================================================
%% Test 4: Standard library compilation process correctly reports partial failures
%% ============================================================================

test_partial_compilation_failure_formatting() ->
    cure_utils:debug("Testing partial compilation failure error formatting...~n"),

    % Test 4.1: Single failure formatting
    SingleFailure = [
        {individual_compile_failed, "lib/std/broken.cure", "Parse error at line 5: syntax error"}
    ],

    SingleError = cure_cli:format_error({partial_stdlib_compilation_failed, SingleFailure}),
    ?assert(string:str(SingleError, "Partial standard library compilation failed") > 0),
    ?assert(string:str(SingleError, "lib/std/broken.cure") > 0),
    ?assert(string:str(SingleError, "Parse error at line 5") > 0),

    % Test 4.2: Multiple failures formatting
    MultipleFailures = [
        {individual_compile_failed, "lib/std/broken1.cure", "Type error: undefined variable"},
        {individual_compile_failed, "lib/std/broken2.cure", "Lexical error: unterminated string"},
        {file_read_error, "lib/missing.cure", enoent}
    ],

    MultipleError = cure_cli:format_error({partial_stdlib_compilation_failed, MultipleFailures}),
    ?assert(string:str(MultipleError, "Partial standard library compilation failed") > 0),
    ?assert(string:str(MultipleError, "lib/std/broken1.cure") > 0),
    ?assert(string:str(MultipleError, "lib/std/broken2.cure") > 0),
    ?assert(string:str(MultipleError, "lib/missing.cure") > 0),

    % Test 4.3: Verify semicolon separation in multiple errors
    ?assert(string:str(MultipleError, ";") > 0),

    cure_utils:debug("✓ Partial compilation failure formatting test passed~n").

test_individual_compile_failure_formatting() ->
    cure_utils:debug("Testing individual compile failure error formatting...~n"),

    % Test 5.1: Basic individual compile failure
    IndividualError = cure_cli:format_error(
        {individual_compile_failed, "test.cure", "Compilation failed"}
    ),
    ?assert(string:str(IndividualError, "Individual compilation") > 0),
    ?assert(string:str(IndividualError, "test.cure") > 0),
    ?assert(string:str(IndividualError, "Compilation failed") > 0),

    % Test 5.2: Individual failure with complex error message
    ComplexError = cure_cli:format_error(
        {individual_compile_failed, "lib/std/complex.cure",
            "Type error at line 42: Expected Int but got String\nContext: function definition"}
    ),
    ?assert(string:str(ComplexError, "lib/std/complex.cure") > 0),
    ?assert(string:str(ComplexError, "Type error at line 42") > 0),
    ?assert(string:str(ComplexError, "Expected Int but got String") > 0),

    % Test 5.3: Individual failure with special characters
    SpecialCharError = cure_cli:format_error(
        {individual_compile_failed, "lib/test_with_spaces and symbols!.cure",
            "Error: unexpected token '&' at position 15"}
    ),
    ?assert(string:str(SpecialCharError, "lib/test_with_spaces and symbols!.cure") > 0),
    ?assert(string:str(SpecialCharError, "unexpected token '&'") > 0),

    cure_utils:debug("✓ Individual compile failure formatting test passed~n").

test_beam_to_source_path_conversion() ->
    cure_utils:debug("Testing BEAM to source path conversion...~n"),

    % Test 6.1: Standard library module conversion
    ?assertEqual(
        {ok, "lib/std/core.cure"},
        cure_cli:convert_beam_to_source_path("_build/ebin/Std.Core.beam")
    ),
    ?assertEqual(
        {ok, "lib/std/list.cure"},
        cure_cli:convert_beam_to_source_path("_build/ebin/Std.List.beam")
    ),
    ?assertEqual(
        {ok, "lib/std/string.cure"},
        cure_cli:convert_beam_to_source_path("_build/ebin/Std.String.beam")
    ),
    ?assertEqual(
        {ok, "lib/std/math.cure"},
        cure_cli:convert_beam_to_source_path("_build/ebin/Std.Math.beam")
    ),

    % Test 6.2: Top-level library module conversion
    ?assertEqual(
        {ok, "lib/test.cure"},
        cure_cli:convert_beam_to_source_path("_build/ebin/Test.beam")
    ),
    ?assertEqual(
        {ok, "lib/utils.cure"},
        cure_cli:convert_beam_to_source_path("_build/ebin/Utils.beam")
    ),

    % Test 6.3: Invalid path conversion
    ?assertEqual(error, cure_cli:convert_beam_to_source_path("invalid/path.beam")),
    ?assertEqual(
        error, cure_cli:convert_beam_to_source_path("_build/ebin/Invalid.Module.Name.beam")
    ),
    ?assertEqual(error, cure_cli:convert_beam_to_source_path("not_a_beam_file.txt")),

    % Test 6.4: Edge cases
    ?assertEqual(error, cure_cli:convert_beam_to_source_path("")),
    ?assertEqual(error, cure_cli:convert_beam_to_source_path("_build/ebin/.beam")),

    cure_utils:debug("✓ BEAM to source path conversion test passed~n").

test_missing_files_detection() ->
    cure_utils:debug("Testing missing files detection logic...~n"),

    % Test 7.1: Verify the check_stdlib_compiled function structure
    % This tests the logic without requiring actual files to exist

    % Expected standard library sources
    ExpectedSources = ["lib/std.cure", "lib/test.cure", "lib/std/core.cure", "lib/std/result.cure"],

    % Test the conversion logic for expected BEAM files
    ExpectedBeamFiles = lists:map(
        fun(CureFile) ->
            case string:prefix(CureFile, "lib/std/") of
                nomatch ->
                    BaseName = filename:basename(CureFile, ".cure"),
                    ModuleName = string:titlecase(BaseName),
                    "_build/ebin/" ++ ModuleName ++ ".beam";
                Rest ->
                    BaseName = filename:basename(Rest, ".cure"),
                    ModuleName = string:titlecase(BaseName),
                    "_build/ebin/Std." ++ ModuleName ++ ".beam"
            end
        end,
        ExpectedSources
    ),

    % Verify expected BEAM file names
    ExpectedBeamNames = [
        "_build/ebin/Std.beam",
        "_build/ebin/Test.beam",
        "_build/ebin/Std.Core.beam",
        "_build/ebin/Std.Result.beam"
    ],

    ?assertEqual(ExpectedBeamNames, ExpectedBeamFiles),

    cure_utils:debug("✓ Missing files detection test passed~n").

test_compilation_error_types() ->
    cure_utils:debug("Testing different compilation error types...~n"),

    % Test 8.1: File read errors
    FileReadError = cure_cli:format_error({file_read_error, "missing.cure", enoent}),
    ?assert(string:str(FileReadError, "Could not read file") > 0),
    ?assert(string:str(FileReadError, "missing.cure") > 0),

    % Test 8.2: Stdlib unavailable errors
    StdlibError = cure_cli:format_error({stdlib_unavailable, "Library not compiled"}),
    ?assert(string:str(StdlibError, "Standard library not available") > 0),
    ?assert(string:str(StdlibError, "Library not compiled") > 0),

    % Test 8.3: Stdlib compilation failed errors
    StdlibCompFailedError = cure_cli:format_error(
        {stdlib_compilation_failed, "Make failed with exit code 1"}
    ),
    ?assert(string:str(StdlibCompFailedError, "Standard library compilation failed") > 0),
    ?assert(string:str(StdlibCompFailedError, "Make failed") > 0),

    % Test 8.4: Compilation stage failures
    StageFailedError = cure_cli:format_error(
        {compilation_stage_failed, "Lexical Analysis", "Unexpected character"}
    ),
    ?assert(string:str(StageFailedError, "Lexical Analysis failed") > 0),
    ?assert(string:str(StageFailedError, "Unexpected character") > 0),

    cure_utils:debug("✓ Compilation error types test passed~n").

test_error_message_aggregation() ->
    cure_utils:debug("Testing error message aggregation...~n"),

    % Test 9.1: Multiple error aggregation
    Errors = [
        {individual_compile_failed, "file1.cure", "Error 1"},
        {individual_compile_failed, "file2.cure", "Error 2"},
        {file_read_error, "file3.cure", eacces}
    ],

    AggregatedError = cure_cli:format_error({partial_stdlib_compilation_failed, Errors}),

    % Verify all individual errors are included
    ?assert(string:str(AggregatedError, "file1.cure") > 0),
    ?assert(string:str(AggregatedError, "file2.cure") > 0),
    ?assert(string:str(AggregatedError, "file3.cure") > 0),
    ?assert(string:str(AggregatedError, "Error 1") > 0),
    ?assert(string:str(AggregatedError, "Error 2") > 0),

    % Test 9.2: Empty error list (edge case)
    EmptyError = cure_cli:format_error({partial_stdlib_compilation_failed, []}),
    ?assert(string:str(EmptyError, "Partial standard library compilation failed") > 0),

    % Test 9.3: Single complex error with nested information
    ComplexSingleError = [
        {individual_compile_failed, "complex.cure",
            "Multiple issues:\n  - Line 5: Type error\n  - Line 10: Syntax error"}
    ],

    ComplexFormatted = cure_cli:format_error(
        {partial_stdlib_compilation_failed, ComplexSingleError}
    ),
    ?assert(string:str(ComplexFormatted, "complex.cure") > 0),
    ?assert(string:str(ComplexFormatted, "Multiple issues") > 0),
    ?assert(string:str(ComplexFormatted, "Type error") > 0),
    ?assert(string:str(ComplexFormatted, "Syntax error") > 0),

    cure_utils:debug("✓ Error message aggregation test passed~n").
