%% Unit Tests for Cure Wrapper Script Functionality
%% Tests specifically for:
%% 1. Cure wrapper script correctly executes "make all" for "build" command
%% 2. Cure wrapper script correctly reports missing required BEAM modules
-module(cure_wrapper_script_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").

%% Run wrapper script specific tests
run() ->
    io:format("Running Cure Wrapper Script Tests...~n"),

    test_wrapper_build_command_execution(),
    test_wrapper_missing_beam_module_detection(),
    test_wrapper_required_modules_definition(),
    test_wrapper_error_reporting(),

    io:format("All cure wrapper script tests passed!~n").

%% ============================================================================
%% Test 1: Cure wrapper script correctly executes "make all" for "build" command
%% ============================================================================

test_wrapper_build_command_execution() ->
    io:format("Testing wrapper build command execution logic...~n"),

    % Read the cure wrapper script
    CureScriptPath = "/opt/Proyectos/Ammotion/cure/cure",
    ?assert(filelib:is_regular(CureScriptPath)),

    {ok, ScriptContent} = file:read_file(CureScriptPath),
    ScriptText = binary_to_list(ScriptContent),

    % Test 1.1: Verify build command case exists
    ?assert(string:str(ScriptText, "\"build\")") > 0),

    % Test 1.2: Verify it calls make all command
    ?assert(string:str(ScriptText, "make -C \"${CURE_ROOT}\" all") > 0),

    % Test 1.3: Verify it uses exec to replace the shell process
    ?assert(string:str(ScriptText, "exec make -C \"${CURE_ROOT}\" all") > 0),

    % Test 1.4: Verify it prints informative message
    ?assert(string:str(ScriptText, "Building Cure compiler...") > 0),

    % Test 1.5: Verify the case statement structure is correct
    CasePattern = "case \"${1:-}\" in",
    ?assert(string:str(ScriptText, CasePattern) > 0),

    % Test 1.6: Verify build is one of the handled special cases
    BuildCasePattern = "\"build\")",
    ?assert(string:str(ScriptText, BuildCasePattern) > 0),

    io:format("✓ Wrapper build command execution test passed~n").

%% ============================================================================
%% Test 2: Cure wrapper script correctly reports missing required BEAM modules
%% ============================================================================

test_wrapper_missing_beam_module_detection() ->
    io:format("Testing wrapper missing BEAM module detection...~n"),

    CureScriptPath = "/opt/Proyectos/Ammotion/cure/cure",
    {ok, ScriptContent} = file:read_file(CureScriptPath),
    ScriptText = binary_to_list(ScriptContent),

    % Test 2.1: Verify REQUIRED_MODULES array is defined
    ?assert(string:str(ScriptText, "REQUIRED_MODULES=(") > 0),

    % Test 2.2: Verify each expected required module is listed
    RequiredModules = [
        "cure_cli.beam",
        "cure_lexer.beam",
        "cure_parser.beam",
        "cure_typechecker.beam",
        "cure_codegen.beam"
    ],

    lists:foreach(
        fun(Module) ->
            ?assert(string:str(ScriptText, "\"" ++ Module ++ "\"") > 0)
        end,
        RequiredModules
    ),

    % Test 2.3: Verify MISSING_MODULES array is used
    ?assert(string:str(ScriptText, "MISSING_MODULES=()") > 0),

    % Test 2.4: Verify module file existence check loop
    ?assert(string:str(ScriptText, "for module in \"${REQUIRED_MODULES[@]}\"") > 0),
    ?assert(string:str(ScriptText, "if [[ ! -f \"${CURE_EBIN}/${module}\" ]]") > 0),

    % Test 2.5: Verify missing modules are added to array
    ?assert(string:str(ScriptText, "MISSING_MODULES+=(\"${module}\")") > 0),

    io:format("✓ Wrapper missing BEAM module detection test passed~n").

test_wrapper_required_modules_definition() ->
    io:format("Testing wrapper required modules definition...~n"),

    CureScriptPath = "/opt/Proyectos/Ammotion/cure/cure",
    {ok, ScriptContent} = file:read_file(CureScriptPath),
    ScriptText = binary_to_list(ScriptContent),

    % Test 3.1: Verify exact required modules list structure
    ?assert(string:str(ScriptText, "REQUIRED_MODULES=(") > 0),

    % Test 3.2: Verify proper array closing
    RequiredSectionStart = string:str(ScriptText, "REQUIRED_MODULES=("),
    RequiredSectionText = string:substr(ScriptText, RequiredSectionStart, 500),
    ?assert(string:str(RequiredSectionText, ")") > 0),

    % Test 3.3: Verify modules are properly quoted
    ?assert(string:str(ScriptText, "\"cure_cli.beam\"") > 0),
    ?assert(string:str(ScriptText, "\"cure_lexer.beam\"") > 0),
    ?assert(string:str(ScriptText, "\"cure_parser.beam\"") > 0),
    ?assert(string:str(ScriptText, "\"cure_typechecker.beam\"") > 0),
    ?assert(string:str(ScriptText, "\"cure_codegen.beam\"") > 0),

    io:format("✓ Wrapper required modules definition test passed~n").

test_wrapper_error_reporting() ->
    io:format("Testing wrapper error reporting mechanism...~n"),

    CureScriptPath = "/opt/Proyectos/Ammotion/cure/cure",
    {ok, ScriptContent} = file:read_file(CureScriptPath),
    ScriptText = binary_to_list(ScriptContent),

    % Test 4.1: Verify error reporting condition
    ?assert(string:str(ScriptText, "if [[ ${#MISSING_MODULES[@]} -gt 0 ]]") > 0),

    % Test 4.2: Verify error message is displayed
    ?assert(string:str(ScriptText, "Error: Missing required compiler modules") > 0),

    % Test 4.3: Verify missing modules are printed
    ?assert(string:str(ScriptText, "printf '%s\\n' \"${MISSING_MODULES[@]}\"") > 0),

    % Test 4.4: Verify instructions are provided
    ?assert(string:str(ScriptText, "Run 'make all' to build all required components") > 0),

    % Test 4.5: Verify script exits with error code
    ?assert(string:str(ScriptText, "exit 1") > 0),

    % Test 4.6: Verify error messages go to stderr
    ?assert(string:str(ScriptText, ">&2") > 0),

    io:format("✓ Wrapper error reporting test passed~n").
