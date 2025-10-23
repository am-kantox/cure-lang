%% Unit Tests for Cure CLI Automatic Standard Library Import Functionality
%% Tests specifically for:
%% 3. cure_cli module correctly adds automatic standard library imports to source files without explicit imports
-module(cure_cli_stdlib_imports_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").

%% Mock compile_options record (to avoid dependency issues)
-record(compile_options, {
    output_file = undefined,
    output_dir = "_build/ebin",
    debug_info = true,
    warnings = true,
    verbose = false,
    type_check = true,
    optimize = true,
    fsm_runtime = true,
    stdlib_paths = ["_build/lib", "_build/lib/std"]
}).

%% Run CLI stdlib imports specific tests
run() ->
    cure_utils:debug("Running Cure CLI Stdlib Imports Tests...~n"),

    test_automatic_import_addition(),
    test_explicit_module_detection(),
    test_explicit_import_detection(),
    test_import_content_verification(),
    test_source_preservation(),
    test_edge_cases(),

    cure_utils:debug("All cure CLI stdlib imports tests passed!~n").

%% ============================================================================
%% Test 3: cure_cli module correctly adds automatic standard library imports
%% ============================================================================

test_automatic_import_addition() ->
    cure_utils:debug("Testing automatic import addition to plain source...~n"),

    % Create test options
    TestOptions = #compile_options{verbose = false},

    % Test 3.1: Plain function definition should get imports
    PlainSource = "def main() = print(\"Hello World\")",
    EnhancedSource = cure_cli:add_automatic_stdlib_imports(PlainSource, TestOptions),

    % Verify all expected imports are present
    ExpectedImports = [
        "import Std.Core",
        "import Std.Show",
        "import Std.Math",
        "import Std.List",
        "import Std.String"
    ],

    lists:foreach(
        fun(Import) ->
            ?assert(string:str(EnhancedSource, Import) > 0)
        end,
        ExpectedImports
    ),

    % Test 3.2: Verify original source is preserved
    ?assert(string:str(EnhancedSource, PlainSource) > 0),

    % Test 3.3: Verify comment header is added
    ?assert(string:str(EnhancedSource, "# Automatic standard library imports") > 0),

    cure_utils:debug("✓ Automatic import addition test passed~n").

test_explicit_module_detection() ->
    cure_utils:debug("Testing explicit module definition detection...~n"),

    TestOptions = #compile_options{verbose = false},

    % Test 4.1: Module definition at start of line
    ModuleSource1 = "module MyModule\n\ndef main() = print(\"Hello\")",
    Result1 = cure_cli:add_automatic_stdlib_imports(ModuleSource1, TestOptions),
    ?assertEqual(ModuleSource1, Result1),

    % Test 4.2: Module definition with leading whitespace
    ModuleSource2 = "  module  MyModule  \n\ndef main() = print(\"Hello\")",
    Result2 = cure_cli:add_automatic_stdlib_imports(ModuleSource2, TestOptions),
    ?assertEqual(ModuleSource2, Result2),

    % Test 4.3: Module definition with different casing (should still match)
    ModuleSource3 = "Module TestModule\n\ndef test() = 42",
    Result3 = cure_cli:add_automatic_stdlib_imports(ModuleSource3, TestOptions),
    ?assertEqual(ModuleSource3, Result3),

    % Test 4.4: Verify the detection function works directly
    ?assert(cure_cli:has_explicit_module_or_imports("module TestModule")),
    ?assert(cure_cli:has_explicit_module_or_imports("  module  TestModule  ")),

    cure_utils:debug("✓ Explicit module detection test passed~n").

test_explicit_import_detection() ->
    cure_utils:debug("Testing explicit import statement detection...~n"),

    TestOptions = #compile_options{verbose = false},

    % Test 5.1: Import statement at start of line
    ImportSource1 = "import Custom.Module [func1, func2]\n\ndef main() = func1()",
    Result1 = cure_cli:add_automatic_stdlib_imports(ImportSource1, TestOptions),
    ?assertEqual(ImportSource1, Result1),

    % Test 5.2: Import statement with leading whitespace
    ImportSource2 = "  import  Custom.Module  [func1]  \n\ndef main() = func1()",
    Result2 = cure_cli:add_automatic_stdlib_imports(ImportSource2, TestOptions),
    ?assertEqual(ImportSource2, Result2),

    % Test 5.3: Multiple import statements
    ImportSource3 = "import Module1 [func1]\nimport Module2 [func2]\n\ndef main() = func1()",
    Result3 = cure_cli:add_automatic_stdlib_imports(ImportSource3, TestOptions),
    ?assertEqual(ImportSource3, Result3),

    % Test 5.4: Verify the detection function works directly
    ?assert(cure_cli:has_explicit_module_or_imports("import TestModule [test]")),
    ?assert(cure_cli:has_explicit_module_or_imports("  import  TestModule  ")),

    cure_utils:debug("✓ Explicit import detection test passed~n").

test_import_content_verification() ->
    cure_utils:debug("Testing automatic import content verification...~n"),

    TestOptions = #compile_options{verbose = false},
    PlainSource = "def test() = 42",

    EnhancedSource = cure_cli:add_automatic_stdlib_imports(PlainSource, TestOptions),

    % Test 6.1: Verify specific imported functions from Std.Core
    ?assert(
        string:str(EnhancedSource, "import Std.Core [ok, error, some, none, identity, compose]") > 0
    ),

    % Test 6.2: Verify specific imported functions from Std.Show
    ?assert(string:str(EnhancedSource, "import Std.Show [show, print]") > 0),

    % Test 6.3: Verify specific imported functions from Std.Math
    ?assert(string:str(EnhancedSource, "import Std.Math [abs, min, max]") > 0),

    % Test 6.4: Verify specific imported functions from Std.List
    ?assert(string:str(EnhancedSource, "import Std.List [length, head, tail, map, filter]") > 0),

    % Test 6.5: Verify specific imported functions from Std.String (with alias)
    ?assert(string:str(EnhancedSource, "import Std.String [concat as string_concat, trim]") > 0),

    % Test 6.6: Verify empty line separator is added
    Lines = string:split(EnhancedSource, "\n", all),
    ?assert(lists:member("", Lines)),

    cure_utils:debug("✓ Import content verification test passed~n").

test_source_preservation() ->
    cure_utils:debug("Testing original source preservation...~n"),

    TestOptions = #compile_options{verbose = false},

    % Test 7.1: Multi-line source preservation
    MultilineSource =
        "def func1() = 42\n\ndef func2(x) = x * 2\n\ndef main() = print(func1() + func2(5))",
    Enhanced = cure_cli:add_automatic_stdlib_imports(MultilineSource, TestOptions),

    % Original source should be at the end after imports
    ?assert(string:str(Enhanced, MultilineSource) > 0),

    % Test 7.2: Source with comments preservation
    SourceWithComments = "# This is a comment\ndef test() = 42  # inline comment",
    Enhanced2 = cure_cli:add_automatic_stdlib_imports(SourceWithComments, TestOptions),
    ?assert(string:str(Enhanced2, SourceWithComments) > 0),

    % Test 7.3: Source with special characters preservation
    SourceWithSpecial = "def test() = \"Hello\\nWorld!\"",
    Enhanced3 = cure_cli:add_automatic_stdlib_imports(SourceWithSpecial, TestOptions),
    ?assert(string:str(Enhanced3, SourceWithSpecial) > 0),

    cure_utils:debug("✓ Source preservation test passed~n").

test_edge_cases() ->
    cure_utils:debug("Testing edge cases for import addition...~n"),

    TestOptions = #compile_options{verbose = false},

    % Test 8.1: Empty source
    EmptySource = "",
    Enhanced1 = cure_cli:add_automatic_stdlib_imports(EmptySource, TestOptions),
    ?assert(string:str(Enhanced1, "import Std.Core") > 0),

    % Test 8.2: Only whitespace
    WhitespaceSource = "   \n  \n  ",
    Enhanced2 = cure_cli:add_automatic_stdlib_imports(WhitespaceSource, TestOptions),
    ?assert(string:str(Enhanced2, "import Std.Core") > 0),
    ?assert(string:str(Enhanced2, WhitespaceSource) > 0),

    % Test 8.3: Source that looks like module/import but isn't
    FakeModuleSource = "def module_helper() = 42\ndef import_data() = []",
    Enhanced3 = cure_cli:add_automatic_stdlib_imports(FakeModuleSource, TestOptions),
    ?assert(string:str(Enhanced3, "import Std.Core") > 0),
    ?assert(string:str(Enhanced3, FakeModuleSource) > 0),

    % Test 8.4: Module/import in comments should not prevent import addition
    CommentedModuleSource = "# module SomeModule\ndef test() = 42",
    Enhanced4 = cure_cli:add_automatic_stdlib_imports(CommentedModuleSource, TestOptions),
    ?assert(string:str(Enhanced4, "import Std.Core") > 0),

    % Test 8.5: Module/import in strings should not prevent import addition
    StringModuleSource = "def test() = print(\"module MyModule\")",
    Enhanced5 = cure_cli:add_automatic_stdlib_imports(StringModuleSource, TestOptions),
    ?assert(string:str(Enhanced5, "import Std.Core") > 0),

    cure_utils:debug("✓ Edge cases test passed~n").
