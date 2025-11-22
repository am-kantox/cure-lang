%% Cure Programming Language - Function Guards Tests
%% Tests for function-level guards (single and multi-clause)
-module(function_guards_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").

%% Run all function guard tests
run() ->
    cure_utils:debug("Running Function Guards tests...~n"),
    test_single_clause_simple_guard(),
    test_single_clause_complex_guard(),
    test_multi_clause_guards(),
    test_guard_with_arithmetic(),
    test_guard_with_type_checks(),
    test_guard_failure_handling(),
    cure_utils:debug("All function guard tests passed!~n").

%% Test 1: Single clause with simple guard
test_single_clause_simple_guard() ->
    Code =
        "\n"
        "        module TestSimpleGuard do\n"
        "          export [is_positive/1]\n"
        "          \n"
        "          def is_positive(x: Int): Bool when x > 0 = true\n"
        "        end\n"
        "    ",

    case compile_cure_code(Code) of
        {ok, Module} ->
            % Test that function compiles and has correct arity
            ?assert(erlang:function_exported(Module, is_positive, 1)),
            cure_utils:debug("✓ Single clause simple guard compiled~n");
        {error, Reason} ->
            cure_utils:debug("✗ Single clause simple guard compilation failed: ~p~n", [Reason]),
            ?assert(false)
    end.

%% Test 2: Single clause with complex guard (multiple conditions)
test_single_clause_complex_guard() ->
    Code =
        "\n"
        "        module TestComplexGuard do\n"
        "          export [in_range/3]\n"
        "          \n"
        "          def in_range(x: Int, min: Int, max: Int): Bool \n"
        "            when x >= min and x <= max \n"
        "          do\n"
        "            true\n"
        "          end\n"
        "        end\n"
        "    ",

    case compile_cure_code(Code) of
        {ok, Module} ->
            ?assert(erlang:function_exported(Module, in_range, 3)),
            cure_utils:debug("✓ Single clause complex guard compiled~n");
        {error, Reason} ->
            cure_utils:debug("✗ Complex guard compilation failed: ~p~n", [Reason]),
            ?assert(false)
    end.

%% Test 3: Multi-clause function with guards
test_multi_clause_guards() ->
    Code =
        "\n"
        "        module TestMultiClause do\n"
        "          export [abs/1, sign/1]\n"
        "          \n"
        "          def abs(x: Int): Int when x >= 0 = x\n"
        "          def abs(x: Int): Int when x < 0 = -x\n"
        "          \n"
        "          def sign(x: Int): Int when x > 0 = 1\n"
        "          def sign(x: Int): Int when x == 0 = 0\n"
        "          def sign(x: Int): Int when x < 0 = -1\n"
        "        end\n"
        "    ",

    case compile_cure_code(Code) of
        {ok, Module} ->
            % Verify both functions exist
            ?assert(erlang:function_exported(Module, abs, 1)),
            ?assert(erlang:function_exported(Module, sign, 1)),
            cure_utils:debug("✓ Multi-clause guards compiled~n");
        {error, Reason} ->
            cure_utils:debug("✗ Multi-clause guards compilation failed: ~p~n", [Reason]),
            ?assert(false)
    end.

%% Test 4: Guard with arithmetic operations
test_guard_with_arithmetic() ->
    Code =
        "\n"
        "        module TestArithmeticGuard do\n"
        "          export [is_even/1]\n"
        "          \n"
        "          def is_even(n: Int): Bool when n % 2 == 0 = true\n"
        "          def is_even(n: Int): Bool = false\n"
        "        end\n"
        "    ",

    case compile_cure_code(Code) of
        {ok, Module} ->
            ?assert(erlang:function_exported(Module, is_even, 1)),
            cure_utils:debug("✓ Guard with arithmetic compiled~n");
        {error, Reason} ->
            cure_utils:debug("✗ Arithmetic guard compilation failed: ~p~n", [Reason]),
            ?assert(false)
    end.

%% Test 5: Guard with type checks
test_guard_with_type_checks() ->
    Code =
        "\n"
        "        module TestTypeGuard do\n"
        "          export [check_type/1]\n"
        "          \n"
        "          def check_type(x: Any): String when is_integer(x) = \"integer\"\n"
        "          def check_type(x: Any): String = \"other\"\n"
        "        end\n"
        "    ",

    case compile_cure_code(Code) of
        {ok, Module} ->
            ?assert(erlang:function_exported(Module, check_type, 1)),
            cure_utils:debug("✓ Guard with type checks compiled~n");
        {error, Reason} ->
            cure_utils:debug("✗ Type guard compilation failed: ~p~n", [Reason]),
            ?assert(false)
    end.

%% Test 6: Guard failure handling
test_guard_failure_handling() ->
    Code =
        "\n"
        "        module TestGuardFailure do\n"
        "          export [safe_div/2]\n"
        "          \n"
        "          def safe_div(a: Int, b: Int): Int when b != 0 = a / b\n"
        "        end\n"
        "    ",

    case compile_cure_code(Code) of
        {ok, Module} ->
            ?assert(erlang:function_exported(Module, safe_div, 2)),
            cure_utils:debug("✓ Guard failure handling compiled~n");
        {error, Reason} ->
            cure_utils:debug("✗ Guard failure handling compilation failed: ~p~n", [Reason]),
            ?assert(false)
    end.

%% ============================================================================
%% Helper Functions
%% ============================================================================

%% Compile Cure code and return the module name
compile_cure_code(CodeString) ->
    % Write code to temporary file
    TempFile = "/tmp/test_guards_" ++ integer_to_list(erlang:unique_integer([positive])) ++ ".cure",
    ok = file:write_file(TempFile, CodeString),

    try
        % Parse the file
        case cure_parser:parse_file(TempFile) of
            {ok, AST} ->
                compile_ast(AST, TempFile);
            {error, ParseError} ->
                {error, {parse_error, ParseError}}
        end
    after
        % Clean up temp file
        file:delete(TempFile)
    end.

%% Compile AST to BEAM module
compile_ast(#module_def{name = ModuleName} = Module, _Filename) ->
    try
        % Use codegen to compile
        case cure_codegen:compile_module(Module) of
            {ok, BeamModule} ->
                % Generate BEAM code
                case cure_beam_compiler:compile_module_to_beam(BeamModule) of
                    {ok, _BeamCode} ->
                        {ok, ModuleName};
                    {error, BeamError} ->
                        {error, {beam_error, BeamError}}
                end;
            {error, CodegenError} ->
                {error, {codegen_error, CodegenError}}
        end
    catch
        Error:Reason:Stack ->
            {error, {compilation_exception, Error, Reason, Stack}}
    end.
