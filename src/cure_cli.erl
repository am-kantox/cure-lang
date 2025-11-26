-module(cure_cli).

-moduledoc """
# Cure Programming Language - Command Line Interface

This module provides a comprehensive command-line interface for the Cure programming
language compiler. It handles argument parsing, file compilation, and the complete
compilation pipeline from Cure source code to BEAM bytecode.

## Features

- **Complete CLI Interface**: Argument parsing with support for all compiler options
- **Full Compilation Pipeline**: Lexing → Parsing → Type Checking → Optimization → Code Generation
- **Error Handling**: Comprehensive error reporting with optional debug information
- **Multiple Output Formats**: Support for different output directories and file formats
- **Integration Ready**: Designed for use with build systems and IDEs

## Usage

```bash
cure input.cure                    # Compile with defaults
cure input.cure -o output.beam     # Specify output file
cure input.cure --verbose          # Enable verbose output
cure input.cure --no-optimize      # Disable optimizations
```

## Command Line Options

- `-o, --output FILE` - Output .beam file path
- `-d, --output-dir DIR` - Output directory (default: `_build/ebin`)
- `--verbose` - Enable verbose compilation output
- `--no-debug` - Disable debug information in output
- `--no-warnings` - Suppress compiler warnings
- `--no-type-check` - Skip type checking phase
- `--no-optimize` - Disable type-directed optimizations
- `--no-smt` - Disable SMT constraint solving
- `--smt-solver SOLVER` - Choose SMT solver (z3, cvc5, auto)
- `--smt-timeout MS` - Set SMT solver timeout in milliseconds
- `--emit-ast` - Output AST for debugging (pretty-printed)
- `--emit-typed-ast` - Output typed AST after type checking
- `--emit-ir` - Output intermediate representation before BEAM generation
- `--check` - Type check only, don't compile to BEAM
- `--print-types` - Print inferred types for all functions
- `--no-color` - Disable ANSI color codes in output
- `--wall` - Show all warnings (even minor ones)
- `--Werror` - Treat warnings as errors (fail compilation on warnings)
- `--time` - Show compilation time for each stage
- `--help, -h` - Show help information
- `--version, -v` - Show version information

## Environment Variables

- `CURE_DEBUG=1` - Enable detailed debug output including stack traces

## Error Codes

- `0` - Success
- `1` - Compilation or runtime error
- `2` - Usage error (invalid arguments)

""".

-export([
    % Main entry point for escript
    main/1,
    % Compile a single .cure file
    compile_file/1,
    % Compile with options
    compile_file/2,
    % Wrapper for erl -s invocation (takes list of atoms)
    compile_file_from_shell/1,
    %% Convert compile options to codegen options
    compile_opts_to_codegen_opts/1,
    %% Get module information from AST (simplified, for future use)
    get_module_info/1,
    %% Utility function to check if we have a complete Cure installation
    check_cure_installation/0,
    %% Ensure standard library is available
    ensure_stdlib_available/1,
    % Show help information
    help/0,
    % Show version information
    version/0,
    % Format error messages (exported for testing)
    format_error/1,
    format_compilation_error/1,
    % Helper functions for testing
    add_automatic_stdlib_imports/2,
    has_explicit_module_or_imports/1,
    convert_beam_to_source_path/1
]).

-include("parser/cure_ast.hrl").

%% Version information
-define(CURE_VERSION, "0.7.0").
-define(CURE_DESCRIPTION, "Cure Programming Language Compiler").

%% Exit codes
-define(EXIT_SUCCESS, 0).
-define(EXIT_ERROR, 1).
-define(EXIT_USAGE, 2).

%% Default options
-record(compile_options, {
    % Output .beam file path
    output_file = undefined,
    % Output directory
    output_dir = "_build/ebin",
    % Include debug information
    debug_info = true,
    % Show warnings
    warnings = true,
    % Verbose output
    verbose = false,
    % Enable type checking
    type_check = true,
    % Enable optimizations
    optimize = true,
    % Include FSM runtime
    fsm_runtime = true,
    % Standard library paths to link
    stdlib_paths = ["_build/lib", "_build/lib/std"],
    % SMT solver configuration
    smt_enabled = true,
    % SMT solver to use (z3, cvc5, or auto)
    smt_solver = auto,
    % SMT solver timeout in milliseconds
    smt_timeout = 5000,
    % Emit AST for debugging
    emit_ast = false,
    % Emit typed AST after type checking
    emit_typed_ast = false,
    % Check only mode (type check without compiling)
    check_only = false,
    % Emit IR (intermediate representation) before BEAM generation
    emit_ir = false,
    % Print inferred types for all functions
    print_types = false,
    % Disable ANSI color codes in output
    no_color = false,
    % Show all warnings (even minor ones)
    wall = false,
    % Treat warnings as errors
    werror = false,
    % Show compilation time for each stage
    show_time = false
}).

%% ============================================================================
%% Main Entry Point
%% ============================================================================

-doc """
Main entry point for the Cure compiler when used as an escript.

This function processes command line arguments and orchestrates the entire
compilation process. It handles all user-facing errors and exits with
appropriate status codes.

## Arguments

- `Args` - List of command line arguments as strings

## Exit Codes

- `0` - Successful compilation
- `1` - Compilation error or internal error
- `2` - Usage error (invalid arguments)

## Examples

```erlang
% These calls happen automatically when using the CLI:
main(["input.cure"]).
main(["input.cure", "-o", "output.beam"]).
main(["--help"]).
```

## Error Handling

All exceptions are caught and converted to user-friendly error messages.
When `CURE_DEBUG=1` is set, full stack traces are displayed for debugging.
""".
main(Args) ->
    try
        case parse_args(Args) of
            {help} ->
                help(),
                halt(?EXIT_SUCCESS);
            {version} ->
                version(),
                halt(?EXIT_SUCCESS);
            {compile, Filename, Options} ->
                case compile_file(Filename, Options) of
                    {ok, check_only} ->
                        % Check-only mode succeeded, already printed message
                        halt(?EXIT_SUCCESS);
                    {ok, OutputFile} ->
                        io:format("Successfully compiled ~s -> ~s~n", [Filename, OutputFile]),
                        halt(?EXIT_SUCCESS);
                    {error, Reason} ->
                        io:format("Error: ~s~n", [format_error(Reason)]),
                        halt(?EXIT_ERROR)
                end;
            {error, Message} ->
                io:format("Error: ~s~n", [Message]),
                io:format("Use 'cure --help' for usage information.~n"),
                halt(?EXIT_USAGE)
        end
    catch
        Error:CatchReason:Stack ->
            io:format("Internal error: ~p:~p~n", [Error, CatchReason]),
            case os:getenv("CURE_DEBUG") of
                "1" -> io:format("Stack trace: ~p~n", [Stack]);
                _ -> ok
            end,
            halt(?EXIT_ERROR)
    end.

%% ============================================================================
%% Argument Parsing
%% ============================================================================

%% Parse command line arguments
parse_args([]) ->
    {error, "No input file specified"};
parse_args(["--help" | _]) ->
    {help};
parse_args(["-h" | _]) ->
    {help};
parse_args(["--version" | _]) ->
    {version};
parse_args(["-v" | _]) ->
    {version};
parse_args(Args) ->
    parse_compile_args(Args, #compile_options{}, undefined).

%% Parse compilation arguments
parse_compile_args([], _Options, undefined) ->
    {error, "No input file specified"};
parse_compile_args([], Options, Filename) ->
    {compile, Filename, Options};
parse_compile_args(["-o", OutputFile | Rest], Options, Filename) ->
    NewOptions = Options#compile_options{output_file = OutputFile},
    parse_compile_args(Rest, NewOptions, Filename);
parse_compile_args(["--output", OutputFile | Rest], Options, Filename) ->
    NewOptions = Options#compile_options{output_file = OutputFile},
    parse_compile_args(Rest, NewOptions, Filename);
parse_compile_args(["-d", OutputDir | Rest], Options, Filename) ->
    NewOptions = Options#compile_options{output_dir = OutputDir},
    parse_compile_args(Rest, NewOptions, Filename);
parse_compile_args(["--output-dir", OutputDir | Rest], Options, Filename) ->
    NewOptions = Options#compile_options{output_dir = OutputDir},
    parse_compile_args(Rest, NewOptions, Filename);
parse_compile_args(["--verbose" | Rest], Options, Filename) ->
    NewOptions = Options#compile_options{verbose = true},
    parse_compile_args(Rest, NewOptions, Filename);
parse_compile_args(["--no-debug" | Rest], Options, Filename) ->
    NewOptions = Options#compile_options{debug_info = false},
    parse_compile_args(Rest, NewOptions, Filename);
parse_compile_args(["--no-warnings" | Rest], Options, Filename) ->
    NewOptions = Options#compile_options{warnings = false},
    parse_compile_args(Rest, NewOptions, Filename);
parse_compile_args(["--no-type-check" | Rest], Options, Filename) ->
    NewOptions = Options#compile_options{type_check = false},
    parse_compile_args(Rest, NewOptions, Filename);
parse_compile_args(["--no-optimize" | Rest], Options, Filename) ->
    NewOptions = Options#compile_options{optimize = false},
    parse_compile_args(Rest, NewOptions, Filename);
parse_compile_args(["--no-smt" | Rest], Options, Filename) ->
    NewOptions = Options#compile_options{smt_enabled = false},
    parse_compile_args(Rest, NewOptions, Filename);
parse_compile_args(["--smt-solver", Solver | Rest], Options, Filename) ->
    SolverAtom = list_to_atom(Solver),
    case lists:member(SolverAtom, [z3, cvc5, auto]) of
        true ->
            NewOptions = Options#compile_options{smt_solver = SolverAtom},
            parse_compile_args(Rest, NewOptions, Filename);
        false ->
            {error, io_lib:format("Invalid SMT solver: ~s (must be z3, cvc5, or auto)", [Solver])}
    end;
parse_compile_args(["--smt-timeout", TimeoutStr | Rest], Options, Filename) ->
    try list_to_integer(TimeoutStr) of
        Timeout when Timeout > 0 ->
            NewOptions = Options#compile_options{smt_timeout = Timeout},
            parse_compile_args(Rest, NewOptions, Filename);
        _ ->
            {error, "SMT timeout must be a positive integer"}
    catch
        _:_ ->
            {error, io_lib:format("Invalid SMT timeout value: ~s", [TimeoutStr])}
    end;
parse_compile_args(["--emit-ast" | Rest], Options, Filename) ->
    NewOptions = Options#compile_options{emit_ast = true},
    parse_compile_args(Rest, NewOptions, Filename);
parse_compile_args(["--emit-typed-ast" | Rest], Options, Filename) ->
    NewOptions = Options#compile_options{emit_typed_ast = true},
    parse_compile_args(Rest, NewOptions, Filename);
parse_compile_args(["--check" | Rest], Options, Filename) ->
    NewOptions = Options#compile_options{check_only = true},
    parse_compile_args(Rest, NewOptions, Filename);
parse_compile_args(["--emit-ir" | Rest], Options, Filename) ->
    NewOptions = Options#compile_options{emit_ir = true},
    parse_compile_args(Rest, NewOptions, Filename);
parse_compile_args(["--print-types" | Rest], Options, Filename) ->
    NewOptions = Options#compile_options{print_types = true},
    parse_compile_args(Rest, NewOptions, Filename);
parse_compile_args(["--no-color" | Rest], Options, Filename) ->
    NewOptions = Options#compile_options{no_color = true},
    parse_compile_args(Rest, NewOptions, Filename);
parse_compile_args(["--wall" | Rest], Options, Filename) ->
    NewOptions = Options#compile_options{wall = true},
    parse_compile_args(Rest, NewOptions, Filename);
parse_compile_args(["--Werror" | Rest], Options, Filename) ->
    NewOptions = Options#compile_options{werror = true},
    parse_compile_args(Rest, NewOptions, Filename);
parse_compile_args(["--time" | Rest], Options, Filename) ->
    NewOptions = Options#compile_options{show_time = true},
    parse_compile_args(Rest, NewOptions, Filename);
parse_compile_args([Arg | Rest], Options, undefined) when not (hd(Arg) =:= $-) ->
    % This should be the input filename
    case filename:extension(Arg) of
        ".cure" ->
            parse_compile_args(Rest, Options, Arg);
        _ ->
            {error, io_lib:format("Input file must have .cure extension: ~s", [Arg])}
    end;
parse_compile_args([Arg | _Rest], _Options, _Filename) ->
    {error, io_lib:format("Unknown option: ~s", [Arg])}.

%% ============================================================================
%% Compilation Functions
%% ============================================================================

-doc """
Compile a .cure file with default compilation options.

## Arguments

- `Filename` - Path to the .cure source file to compile

## Returns

- `{ok, OutputFile}` - Successful compilation with output file path
- `{error, Reason}` - Compilation failed with error details

## Examples

```erlang
compile_file("examples/hello.cure").
% => {ok, "_build/ebin/hello.beam"}
```

""".
compile_file(Filename) ->
    % Handle atom filenames from erl -s invocation
    FilenameStr =
        case is_atom(Filename) of
            true -> atom_to_list(Filename);
            false -> Filename
        end,
    compile_file(FilenameStr, #compile_options{}).

-doc """
Compile a .cure file with specified compilation options.

This is the main compilation entry point that supports all compiler
features including type checking, optimizations, and custom output options.

## Arguments

- `Filename` - Path to the .cure source file to compile
- `Options` - Compilation options record with fields:
  - `output_file` - Custom output file path (optional)
  - `output_dir` - Output directory (default: "_build/ebin")
  - `debug_info` - Include debug information (default: true)
  - `warnings` - Show warnings (default: true)  
  - `verbose` - Verbose output (default: false)
  - `type_check` - Enable type checking (default: true)
  - `optimize` - Enable optimizations (default: true)
  - `fsm_runtime` - Include FSM runtime (default: true)

## Returns

- `{ok, OutputFile}` - Successful compilation
- `{error, Reason}` - Compilation error with detailed reason

## Compilation Pipeline

The function executes a complete 5-stage pipeline:

1. **Lexical Analysis** - Tokenize source code
2. **Parsing** - Build Abstract Syntax Tree
3. **Type Checking** - Verify types and constraints (optional)
4. **Optimization** - Type-directed optimizations (optional)
5. **Code Generation** - Generate BEAM bytecode

## Examples

```erlang
% Compile with verbose output
Options = #compile_options{verbose = true},
compile_file("src/math.cure", Options).

% Compile without optimizations  
Options = #compile_options{optimize = false},
compile_file("debug.cure", Options).

% Custom output file
Options = #compile_options{output_file = "custom.beam"},
compile_file("input.cure", Options).
```

""".
compile_file(Filename, Options) ->
    % Handle atom filenames from erl -s invocation
    FilenameStr =
        case is_atom(Filename) of
            true -> atom_to_list(Filename);
            false -> Filename
        end,
    case filelib:is_regular(FilenameStr) of
        false ->
            {error, {file_not_found, FilenameStr}};
        true ->
            compile_file_impl(FilenameStr, Options)
    end.

%% Wrapper for invocation via erl -s (takes list of atoms)
compile_file_from_shell([FilenameAtom]) when is_atom(FilenameAtom) ->
    compile_file(atom_to_list(FilenameAtom), #compile_options{});
compile_file_from_shell(Args) ->
    io:format("Error: Invalid arguments to compile_file_from_shell: ~p~n", [Args]),
    halt(1).

%% Implementation of file compilation
compile_file_impl(Filename, Options) ->
    % Check if we're compiling a standard library file to avoid circular dependency
    IsStdlibFile = string:prefix(Filename, "lib/") =/= nomatch,

    case IsStdlibFile of
        true ->
            % Skip standard library check for stdlib files to avoid circular dependency
            if
                Options#compile_options.verbose ->
                    cure_utils:debug("Compiling standard library file ~s...~n", [Filename]);
                true ->
                    ok
            end,

            try
                % Step 1: Read source file
                case file:read_file(Filename) of
                    {ok, SourceBinary} ->
                        Source = binary_to_list(SourceBinary),
                        compile_source(Filename, Source, Options);
                    {error, FileError} ->
                        {error, {file_read_error, Filename, FileError}}
                end
            catch
                Error:Reason:_Stack ->
                    {error, {compilation_failed, Error, Reason}}
            end;
        false ->
            % For non-stdlib files, check if we need stdlib
            % Skip stdlib check for analysis-only modes (check, emit-ast, emit-typed-ast)
            AnalysisOnly =
                Options#compile_options.check_only orelse
                    Options#compile_options.emit_ast orelse
                    Options#compile_options.emit_typed_ast,

            case AnalysisOnly of
                true ->
                    % Skip stdlib for analysis-only modes
                    if
                        Options#compile_options.verbose ->
                            cure_utils:debug("Analyzing ~s (stdlib check skipped)...~n", [Filename]);
                        true ->
                            ok
                    end,

                    try
                        case file:read_file(Filename) of
                            {ok, SourceBinary} ->
                                Source = binary_to_list(SourceBinary),
                                compile_source(Filename, Source, Options);
                            {error, FileError} ->
                                {error, {file_read_error, Filename, FileError}}
                        end
                    catch
                        Error:Reason:_Stack ->
                            {error, {compilation_failed, Error, Reason}}
                    end;
                false ->
                    % Need stdlib for full compilation
                    case ensure_stdlib_available(Options) of
                        ok ->
                            if
                                Options#compile_options.verbose ->
                                    cure_utils:debug("Compiling ~s...~n", [Filename]);
                                true ->
                                    ok
                            end,

                            try
                                % Step 1: Read source file
                                case file:read_file(Filename) of
                                    {ok, SourceBinary} ->
                                        Source = binary_to_list(SourceBinary),
                                        compile_source(Filename, Source, Options);
                                    {error, FileError} ->
                                        {error, {file_read_error, Filename, FileError}}
                                end
                            catch
                                Error:Reason:_Stack ->
                                    {error, {compilation_failed, Error, Reason}}
                            end;
                        {error, StdlibError} ->
                            {error, {stdlib_unavailable, StdlibError}}
                    end
            end
    end.

%% Compile source code through the full pipeline
compile_source(Filename, Source, Options) ->
    % Add automatic standard library imports if not compiling stdlib itself
    IsStdlibFile = string:prefix(Filename, "lib/") =/= nomatch,
    EnhancedSource =
        case IsStdlibFile of
            % Don't add auto-imports to stdlib files
            true -> Source;
            false -> add_automatic_stdlib_imports(Source, Options)
        end,

    Pipeline = [
        {"Lexical Analysis", fun(Src) -> cure_lexer:tokenize(list_to_binary(Src)) end},
        {"Parsing", fun(Tokens) ->
            case cure_parser:parse(Tokens) of
                {ok, AST} = Result ->
                    % Emit AST if requested
                    case Options#compile_options.emit_ast of
                        true ->
                            io:format("~n=== Abstract Syntax Tree ===~n~n"),
                            io:format("~p~n", [AST]),
                            io:format("~n============================~n~n");
                        false ->
                            ok
                    end,
                    Result;
                Error ->
                    Error
            end
        end},
        {"Type Checking", fun(AST) ->
            case Options#compile_options.type_check of
                true ->
                    case type_check_ast(AST, Options) of
                        {ok, TypedAST} = Result ->
                            % Emit typed AST if requested
                            case Options#compile_options.emit_typed_ast of
                                true ->
                                    io:format("~n=== Typed Abstract Syntax Tree ===~n~n"),
                                    io:format("~p~n", [TypedAST]),
                                    io:format("~n===================================~n~n");
                                false ->
                                    ok
                            end,
                            % Print types if requested
                            case Options#compile_options.print_types of
                                true ->
                                    print_inferred_types(TypedAST);
                                false ->
                                    ok
                            end,
                            % If check-only mode, stop here
                            case Options#compile_options.check_only of
                                true ->
                                    {check_only_success, TypedAST};
                                false ->
                                    Result
                            end;
                        Error ->
                            Error
                    end;
                false ->
                    % If check-only but type checking disabled, that's an error
                    case Options#compile_options.check_only of
                        true ->
                            {error, "Cannot use --check with --no-type-check"};
                        false ->
                            {ok, AST}
                    end
            end
        end},
        {"Type-directed Optimization", fun(AST) ->
            case Options#compile_options.optimize of
                true -> optimize_ast(AST, Options);
                false -> {ok, AST}
            end
        end},
        {"Code Generation", fun(AST) ->
            if
                Options#compile_options.verbose ->
                    cure_utils:debug(" ★★★  AST structure: ~p~n", [AST]);
                true ->
                    ok
            end,

            % Use the actual code generator
            CodegenOpts = compile_opts_to_codegen_opts(Options),
            case cure_codegen:compile_program(AST, CodegenOpts) of
                {ok, CompiledModules} ->
                    % Take the first module and generate BEAM file
                    case CompiledModules of
                        [Module | _] ->
                            % Emit IR if requested
                            case Options#compile_options.emit_ir of
                                true ->
                                    io:format(
                                        "~n=== Intermediate Representation (Erlang Forms) ===~n~n"
                                    ),
                                    io:format("Module: ~p~n", [Module]),
                                    io:format(
                                        "~n================================================~n~n"
                                    );
                                false ->
                                    ok
                            end,

                            % Generate BEAM binary in memory
                            case cure_codegen:convert_to_erlang_forms(Module) of
                                {ok, Forms} ->
                                    case
                                        compile:forms(Forms, [binary, return_errors, no_auto_import])
                                    of
                                        {ok, ModuleName, Binary} ->
                                            {ok, {ModuleName, Binary}};
                                        {error, Errors, _Warnings} ->
                                            {error, {beam_generation_failed, Errors}}
                                    end;
                                {error, FormError} ->
                                    {error, {form_conversion_failed, FormError}}
                            end;
                        [] ->
                            {error, no_modules_compiled}
                    end;
                {error, CodegenError} ->
                    {error, {codegen_failed, CodegenError}}
            end
        end}
    ],

    case run_pipeline(Pipeline, EnhancedSource, Options) of
        {check_only_success, _TypedAST} ->
            % Check-only mode succeeded
            io:format("Type checking completed successfully.~n"),
            {ok, check_only};
        {ok, {ModuleName, BeamBinary}} ->
            write_output(Filename, {ModuleName, BeamBinary}, Options);
        {ok, BeamBinary} when is_binary(BeamBinary) ->
            % Fallback for old format
            write_output(Filename, BeamBinary, Options);
        {error, Stage, Reason} ->
            if
                Options#compile_options.verbose ->
                    cure_utils:debug("Compilation failed at ~s: ~p~n", [Stage, Reason]);
                true ->
                    ok
            end,
            {error, {compilation_stage_failed, Stage, Reason}}
    end.

%% Run the compilation pipeline
run_pipeline([], Result, _Options) ->
    {ok, Result};
run_pipeline([{StageName, StageFunc} | RestStages], Input, Options) ->
    % Start timer if --time option is enabled
    StartTime =
        case Options#compile_options.show_time of
            true -> erlang:monotonic_time(millisecond);
            false -> undefined
        end,

    if
        Options#compile_options.verbose ->
            cure_utils:debug("  ~s...~n", [StageName]);
        true ->
            ok
    end,

    StageResult = StageFunc(Input),

    % Print timing if --time option is enabled
    case {Options#compile_options.show_time, StartTime} of
        {true, StartMs} when is_integer(StartMs) ->
            EndTime = erlang:monotonic_time(millisecond),
            Duration = EndTime - StartMs,
            io:format("  [~s] completed in ~w ms~n", [StageName, Duration]);
        _ ->
            ok
    end,

    case StageResult of
        {check_only_success, AST} ->
            % Check-only mode: stop pipeline and return success
            {check_only_success, AST};
        {ok, Output} ->
            run_pipeline(RestStages, Output, Options);
        {error, Reason} ->
            {error, StageName, Reason};
        % Handle cases where stage function returns result directly
        Output ->
            run_pipeline(RestStages, Output, Options)
    end.

%% Type check AST with SMT options
type_check_ast(AST, Options) ->
    % Extract SMT options from compile options
    SmtOpts = #{
        enabled => Options#compile_options.smt_enabled,
        solver => Options#compile_options.smt_solver,
        timeout => Options#compile_options.smt_timeout
    },

    try
        % Pass SMT options to type checker
        case cure_typechecker:check_program(AST, SmtOpts) of
            {error, Reason} ->
                cure_utils:debug("Type checking error: ~p~n", [Reason]),
                {error, Reason};
            Result ->
                check_type_result(Result, AST)
        end
    catch
        Class:Error:Stack ->
            % If type checking fails with exception, provide more detailed error
            cure_utils:debug("Error: Type checking failed with exception ~p:~p~n", [Class, Error]),
            case os:getenv("CURE_DEBUG") of
                "1" -> cure_utils:debug("Stack trace: ~p~n", [Stack]);
                _ -> ok
            end,
            {error, type_check_exception}
    end.

%% Type check AST (legacy - without options)
type_check_ast(AST) ->
    type_check_ast(AST, #compile_options{}).

%% Print inferred types for all functions in AST
print_inferred_types(AST) when is_list(AST) ->
    io:format("~n=== Inferred Types ===~n~n"),
    lists:foreach(fun print_item_types/1, AST),
    io:format("~n======================~n~n"),
    ok;
print_inferred_types(_) ->
    ok.

print_item_types(#module_def{name = ModuleName, items = Items}) ->
    io:format("Module ~s:~n", [ModuleName]),
    lists:foreach(fun print_item_types/1, Items);
print_item_types(#function_def{name = Name, params = Params, return_type = RetType}) ->
    ParamTypes = [format_param_type(P) || P <- Params],
    RetTypeStr = format_type(RetType),
    io:format("  ~s(~s) -> ~s~n", [Name, string:join(ParamTypes, ", "), RetTypeStr]);
print_item_types(_) ->
    ok.

format_param_type(#param{name = Name, type = Type}) ->
    lists:flatten(io_lib:format("~s: ~s", [Name, format_type(Type)]));
format_param_type(_) ->
    "<unknown>".

format_type(undefined) -> "<inferred>";
format_type({primitive_type, T, _}) -> atom_to_list(T);
format_type({type_constructor, Name, _Args, _}) -> atom_to_list(Name);
format_type(_) -> "<complex type>".

%% Check type checking result and determine success/failure
check_type_result(Result, AST) ->
    cure_utils:debug("Type check result structure: ~p~n", [Result]),
    case Result of
        % Handle typecheck_result record
        {typecheck_result, Success, _Type, Errors, Warnings} ->
            % Note: We capture Warnings here but --Werror handling is done at compilation level
            % since we don't have access to Options in this function
            case Success of
                true ->
                    case Errors of
                        [] ->
                            % Check if there are warnings (for --Werror support at higher level)
                            case Warnings of
                                [] ->
                                    {ok, AST};
                                _ ->
                                    % Return ok, --Werror will be handled at compile_source level
                                    {ok, AST}
                            end;
                        ErrorList ->
                            cure_utils:debug("Type checking failed with errors: ~p~n", [ErrorList]),
                            {error, {type_check_failed, ErrorList}}
                    end;
                false ->
                    cure_utils:debug("Type checking failed with errors: ~p~n", [Errors]),
                    {error, {type_check_failed, Errors}}
            end;
        % Handle legacy success result formats
        {success_result, _} ->
            {ok, AST};
        % Handle typecheck_result tuple format based on position
        _ when is_tuple(Result) andalso tuple_size(Result) =:= 5 ->
            % Assume this is a typecheck_result record tuple

            % success field
            Success = element(2, Result),
            % errors field
            Errors = element(4, Result),
            case Success of
                true ->
                    case Errors of
                        [] ->
                            {ok, AST};
                        ErrorList ->
                            cure_utils:debug("Type checking failed with errors: ~p~n", [ErrorList]),
                            {error, {type_check_failed, ErrorList}}
                    end;
                false ->
                    cure_utils:debug("Type checking failed with errors: ~p~n", [Errors]),
                    {error, {type_check_failed, Errors}}
            end;
        % Handle other tuple formats
        _ when is_tuple(Result) ->
            cure_utils:debug("Warning: Unknown type check result format: ~p~n", [Result]),
            cure_utils:debug("Assuming type checking failed~n"),
            {error, unknown_type_check_format};
        _ ->
            cure_utils:debug("Warning: Type check result is not a tuple: ~p~n", [Result]),
            {error, invalid_type_check_result}
    end.

%% Optimize AST using type-directed optimizations
optimize_ast(AST, Options) ->
    try
        if
            Options#compile_options.verbose ->
                io:format("  Running type-directed optimizations...~n");
            true ->
                ok
        end,

        % Call the type optimizer with default configuration
        case cure_type_optimizer:optimize_program(AST) of
            {ok, OptimizedAST, Report} ->
                if
                    Options#compile_options.verbose ->
                        io:format("  Optimization completed successfully~n"),
                        io:format("  Optimization report: ~p~n", [Report]);
                    true ->
                        ok
                end,
                {ok, OptimizedAST};
            {error, Reason} ->
                io:format("  Optimization error: ~p~n", [Reason]),
                % Fall back to unoptimized AST if optimization fails
                io:format("  Warning: Optimization failed, continuing with unoptimized AST~n"),
                {ok, AST}
        end
    catch
        Class:Error:Stack ->
            % If optimization fails with exception, continue with unoptimized AST
            io:format("  Error: Optimization failed with exception ~p:~p~n", [Class, Error]),
            case os:getenv("CURE_DEBUG") of
                "1" -> io:format("  Stack trace: ~p~n", [Stack]);
                _ -> ok
            end,
            io:format("  Warning: Optimization failed, continuing with unoptimized AST~n"),
            {ok, AST}
    end.

-doc """
Convert CLI compilation options to code generation options.

This function transforms the user-facing compilation options into
the internal format expected by the code generation modules.

## Arguments

- `Options` - Compilation options record

## Returns

- List of `{Key, Value}` tuples for the code generator

## Option Mapping

- `debug_info` → `{debug_info, true}`
- `optimize` → `{optimize, 1}` 
- `warnings` → `{warnings, true}`
- `fsm_runtime` → `{fsm_integration, true}`

""".
compile_opts_to_codegen_opts(Options) ->
    CodegenOpts = [],

    CodegenOpts1 =
        case Options#compile_options.debug_info of
            true -> [{debug_info, true} | CodegenOpts];
            false -> CodegenOpts
        end,

    CodegenOpts2 =
        case Options#compile_options.optimize of
            true -> [{optimize, 1} | CodegenOpts1];
            false -> CodegenOpts1
        end,

    CodegenOpts3 =
        case Options#compile_options.warnings of
            true -> [{warnings, true} | CodegenOpts2];
            false -> CodegenOpts2
        end,

    CodegenOpts4 =
        case Options#compile_options.fsm_runtime of
            true -> [{fsm_integration, true} | CodegenOpts3];
            false -> CodegenOpts3
        end,

    CodegenOpts4.

%% Write output file
write_output(InputFilename, BeamData, Options) ->
    {OutputFile, BeamBinary} =
        case BeamData of
            {ModuleName, Binary} ->
                % Use module name for BEAM filename
                {atom_to_list(ModuleName) ++ ".beam", Binary};
            Binary when is_binary(Binary) ->
                % Fallback to input filename
                {determine_output_filename(InputFilename, Options), Binary}
        end,

    OutputDir = Options#compile_options.output_dir,

    % Ensure output directory exists
    case filelib:ensure_dir(filename:join(OutputDir, "dummy")) of
        ok ->
            FullOutputPath = filename:join(OutputDir, OutputFile),
            case file:write_file(FullOutputPath, BeamBinary) of
                ok ->
                    {ok, FullOutputPath};
                {error, Reason} ->
                    {error, {file_write_error, FullOutputPath, Reason}}
            end;
        {error, Reason} ->
            {error, {directory_create_error, OutputDir, Reason}}
    end.

%% Determine output filename
determine_output_filename(InputFilename, Options) ->
    case Options#compile_options.output_file of
        undefined ->
            % Generate output filename from input filename
            BaseName = filename:basename(InputFilename, ".cure"),
            BaseName ++ ".beam";
        OutputFile ->
            filename:basename(OutputFile)
    end.

%% ============================================================================
%% Help and Information Functions
%% ============================================================================

-doc """
Display comprehensive help information for the Cure compiler.

Outputs usage instructions, command-line options, examples, and
environment variables to assist users in using the compiler effectively.

## Output Format

- **Usage**: Basic command syntax
- **Arguments**: Required input file specification
- **Options**: All available command-line flags with descriptions
- **Examples**: Common usage patterns
- **Environment**: Relevant environment variables

""".
help() ->
    io:format("~s v~s~n", [?CURE_DESCRIPTION, ?CURE_VERSION]),
    io:format("~n"),
    io:format("USAGE:~n"),
    io:format("    cure [OPTIONS] <input-file>~n"),
    io:format("~n"),
    io:format("ARGUMENTS:~n"),
    io:format("    <input-file>    Input .cure source file to compile~n"),
    io:format("~n"),
    io:format("OPTIONS:~n"),
    io:format("    -h, --help           Show this help message~n"),
    io:format("    -v, --version        Show version information~n"),
    io:format("    -o, --output <file>  Output .beam file path~n"),
    io:format("    -d, --output-dir <dir>  Output directory (default: _build/ebin)~n"),
    io:format("    --verbose            Enable verbose output~n"),
    io:format("    --no-debug           Disable debug information~n"),
    io:format("    --no-warnings        Disable warnings~n"),
    io:format("    --no-type-check      Skip type checking~n"),
    io:format("    --no-optimize        Disable optimizations~n"),
    io:format("    --no-smt             Disable SMT constraint solving~n"),
    io:format("    --smt-solver <solver>  Choose SMT solver: z3 (default), cvc5, auto~n"),
    io:format("    --smt-timeout <ms>   Set SMT timeout in milliseconds (default: 5000)~n"),
    io:format("    --emit-ast           Output AST for debugging (pretty-printed)~n"),
    io:format("    --emit-typed-ast     Output typed AST after type checking~n"),
    io:format("    --emit-ir            Output IR before BEAM generation~n"),
    io:format("    --check              Type check only, don't compile to BEAM~n"),
    io:format("    --print-types        Print inferred types for all functions~n"),
    io:format("    --no-color           Disable ANSI color codes in output~n"),
    io:format("    --wall               Show all warnings (even minor ones)~n"),
    io:format("    --Werror             Treat warnings as errors~n"),
    io:format("    --time               Show compilation time for each stage~n"),
    io:format("~n"),
    io:format("EXAMPLES:~n"),
    io:format("    cure examples/simple.cure~n"),
    io:format("    cure examples/fsm_demo.cure -o fsm_demo.beam~n"),
    io:format("    cure examples/fsm_demo.cure --no-smt --smt-timeout 10000~n"),
    io:format("    cure src/my_module.cure --verbose -d build/~n"),
    io:format("~n"),
    io:format("ENVIRONMENT VARIABLES:~n"),
    io:format("    CURE_DEBUG=1         Enable debug stack traces~n").

-doc """
Display version and system information for the Cure compiler.

Shows the current Cure compiler version, Erlang/OTP version,
and a brief description of the Cure programming language.

## Output Information

- **Cure Version**: Current compiler version (from `?CURE_VERSION`)
- **Erlang/OTP Version**: Version of the runtime platform
- **Description**: Brief overview of Cure language features

## Example Output

```
Cure Programming Language Compiler v0.1.0

Built with Erlang/OTP 25

Cure is a dependently-typed functional programming language
for the BEAM virtual machine with built-in finite state machines.
```

""".
version() ->
    io:format("~s v~s~n", [?CURE_DESCRIPTION, ?CURE_VERSION]),
    io:format("~n"),
    io:format("Built with Erlang/OTP ~s~n", [erlang:system_info(otp_release)]),
    io:format("~n"),
    io:format("Cure is a dependently-typed functional programming language~n"),
    io:format("for the BEAM virtual machine with built-in finite state machines.~n").

%% ============================================================================
%% Error Formatting
%% ============================================================================

%% Format error messages for user display
format_error({file_not_found, Filename}) ->
    io_lib:format("File not found: ~s", [Filename]);
format_error({file_read_error, Filename, Reason}) ->
    io_lib:format("Could not read file ~s: ~p", [Filename, Reason]);
format_error({file_write_error, Filename, Reason}) ->
    io_lib:format("Could not write file ~s: ~p", [Filename, Reason]);
format_error({directory_create_error, Dir, Reason}) ->
    io_lib:format("Could not create directory ~s: ~p", [Dir, Reason]);
format_error({stdlib_unavailable, Reason}) ->
    io_lib:format("Standard library not available: ~s", [format_error(Reason)]);
format_error({stdlib_compilation_failed, Output}) ->
    io_lib:format("Standard library compilation failed: ~s", [Output]);
format_error({partial_stdlib_compilation_failed, Failures}) ->
    ErrorStrings = [format_error(Error) || Error <- Failures],
    io_lib:format("Partial standard library compilation failed: ~s", [
        string:join(ErrorStrings, "; ")
    ]);
format_error({individual_compile_failed, SourceFile, Output}) ->
    io_lib:format("Individual compilation of ~s failed: ~s", [SourceFile, Output]);
format_error({compilation_stage_failed, Stage, Reason}) ->
    io_lib:format("~s failed: ~s", [Stage, format_compilation_error(Reason)]);
format_error({compilation_failed, Error, Reason}) ->
    io_lib:format("Compilation failed: ~p:~p", [Error, Reason]);
format_error(Reason) when is_list(Reason) ->
    Reason;
format_error(Reason) ->
    io_lib:format("~p", [Reason]).

%% Format compilation-specific errors
format_compilation_error({lexer_error, Line, Message}) ->
    io_lib:format("Lexical error at line ~w: ~s", [Line, Message]);
format_compilation_error({parser_error, Line, Message}) ->
    io_lib:format("Parse error at line ~w: ~s", [Line, Message]);
format_compilation_error({type_error, Message}) ->
    io_lib:format("Type error: ~s", [Message]);
format_compilation_error({type_errors, Errors}) ->
    ErrorStrings = [format_compilation_error(Error) || Error <- Errors],
    string:join(ErrorStrings, "; ");
format_compilation_error(Reason) ->
    io_lib:format("~p", [Reason]).

%% ============================================================================
%% Module Information Functions
%% ============================================================================

-doc """
Extract module information from an Abstract Syntax Tree.

Extracts comprehensive metadata from compiled modules including:
- Module name
- Exported functions with arities
- Imported modules
- Type definitions
- FSM definitions
- Function count

## Arguments

- `AST` - Abstract Syntax Tree from the parser (list of items or single module_def)

## Returns

- Map with module information:
  - `name` - Module name (atom or 'unknown')
  - `exports` - List of exported function specs with name/arity
  - `imports` - List of imported module names
  - `functions` - List of function names defined in module
  - `types` - List of type definition names
  - `fsms` - List of FSM definition names
  - `function_count` - Total number of functions
  - `type_count` - Total number of types
  - `fsm_count` - Total number of FSMs
  - `type` - Module type ('module' or 'unknown')

## Example

```erlang
AST = cure_parser:parse_file("MyModule.cure"),
Info = get_module_info(AST),
% => #{name => 'MyModule', exports => [{hello, 1}], ...}
```

""".
get_module_info(AST) when is_list(AST) ->
    % AST is a list of top-level items
    extract_info_from_items(AST);
get_module_info(#module_def{name = Name, exports = Exports, items = Items}) ->
    % Single module definition
    Info = extract_info_from_items(Items),
    Info#{
        name => Name,
        exports => extract_export_specs(Exports),
        type => module
    };
get_module_info(AST) when is_tuple(AST) ->
    % Generic tuple - try to extract what we can
    #{
        name => unknown,
        exports => [],
        imports => [],
        functions => [],
        types => [],
        fsms => [],
        function_count => 0,
        type_count => 0,
        fsm_count => 0,
        type => module
    };
get_module_info(_) ->
    #{
        name => undefined,
        exports => [],
        imports => [],
        functions => [],
        types => [],
        fsms => [],
        function_count => 0,
        type_count => 0,
        fsm_count => 0,
        type => unknown
    }.

%% Extract information from list of module items
extract_info_from_items(Items) when is_list(Items) ->
    lists:foldl(fun extract_item_info/2, initial_info(), Items).

%% Initial info map
initial_info() ->
    #{
        name => unknown,
        exports => [],
        imports => [],
        functions => [],
        types => [],
        fsms => [],
        function_count => 0,
        type_count => 0,
        fsm_count => 0,
        type => module
    }.

%% Extract information from a single item
extract_item_info(#module_def{name = Name, exports = Exports, items = SubItems}, Info) ->
    SubInfo = extract_info_from_items(SubItems),
    Info#{
        name => Name,
        exports => extract_export_specs(Exports),
        imports => SubInfo#{imports => []},
        functions => SubInfo#{functions => []},
        types => SubInfo#{types => []},
        fsms => SubInfo#{fsms => []},
        function_count => SubInfo#{function_count => 0},
        type_count => SubInfo#{type_count => 0},
        fsm_count => SubInfo#{fsm_count => 0}
    };
extract_item_info(#function_def{name = Name}, Info) ->
    Functions = maps:get(functions, Info, []),
    FunctionCount = maps:get(function_count, Info, 0),
    Info#{
        functions => [Name | Functions],
        function_count => FunctionCount + 1
    };
extract_item_info(#curify_function_def{name = Name}, Info) ->
    Functions = maps:get(functions, Info, []),
    FunctionCount = maps:get(function_count, Info, 0),
    Info#{
        functions => [Name | Functions],
        function_count => FunctionCount + 1
    };
extract_item_info(#type_def{name = Name}, Info) ->
    Types = maps:get(types, Info, []),
    TypeCount = maps:get(type_count, Info, 0),
    Info#{
        types => [Name | Types],
        type_count => TypeCount + 1
    };
extract_item_info(#record_def{name = Name}, Info) ->
    Types = maps:get(types, Info, []),
    TypeCount = maps:get(type_count, Info, 0),
    Info#{
        types => [Name | Types],
        type_count => TypeCount + 1
    };
extract_item_info(#fsm_def{name = Name}, Info) ->
    FSMs = maps:get(fsms, Info, []),
    FSMCount = maps:get(fsm_count, Info, 0),
    Info#{
        fsms => [Name | FSMs],
        fsm_count => FSMCount + 1
    };
extract_item_info(#import_def{module = Module}, Info) ->
    Imports = maps:get(imports, Info, []),
    Info#{imports => [Module | Imports]};
extract_item_info(_, Info) ->
    % Unknown item type, ignore
    Info.

%% Extract export specifications as {Name, Arity} tuples
extract_export_specs(Exports) when is_list(Exports) ->
    lists:filtermap(
        fun
            (#export_spec{name = Name, arity = Arity}) when is_integer(Arity) ->
                {true, {Name, Arity}};
            (#export_spec{name = Name, arity = undefined}) ->
                % Type export without arity
                {true, {Name, type}};
            (_) ->
                false
        end,
        Exports
    );
extract_export_specs(_) ->
    [].

-doc """
Verify that all required Cure compiler modules are available.

This function checks for the presence of core compiler modules
to ensure the Cure installation is complete and functional.

## Required Modules

- `cure_lexer` - Tokenization engine
- `cure_parser` - AST generation
- `cure_typechecker` - Type checking system
- `cure_codegen` - Code generation

## Returns

- `ok` - All required modules are present
- `{error, {missing_modules, List}}` - Some modules are missing

## Side Effects

Prints warning messages if modules are missing, including
instructions to run `make all` to build the complete compiler.

## Usage

This function is called internally to validate the compiler
state before attempting compilation operations.

""".
check_cure_installation() ->
    RequiredModules = [cure_lexer, cure_parser, cure_typechecker, cure_codegen],
    Missing = lists:filter(
        fun(Module) ->
            case code:which(Module) of
                non_existing -> true;
                _ -> false
            end
        end,
        RequiredModules
    ),

    case Missing of
        [] ->
            ok;
        MissingModules ->
            cure_utils:debug("Warning: Missing Cure compiler modules: ~p~n", [MissingModules]),
            cure_utils:debug("Make sure to run 'make all' to build the complete compiler~n"),
            {error, {missing_modules, MissingModules}}
    end.

-doc """
Ensure that the Cure standard library is available and compiled.

This function checks if the standard library BEAM files exist,
and if not, attempts to compile them automatically.

## Arguments

- `Options` - Compilation options including verbosity settings

## Returns

- `ok` - Standard library is available
- `{error, Reason}` - Standard library compilation failed

## Side Effects

- May invoke `make stdlib` to compile missing standard library
- Prints progress messages if verbose mode is enabled

""".
ensure_stdlib_available(Options) ->
    StdlibPaths = Options#compile_options.stdlib_paths,

    case check_stdlib_compiled(StdlibPaths) of
        ok ->
            if
                Options#compile_options.verbose ->
                    cure_utils:debug("Standard library already compiled~n");
                true ->
                    ok
            end,
            ok;
        {missing, _MissingFiles} ->
            if
                Options#compile_options.verbose ->
                    cure_utils:debug("Compiling Cure standard library...~n");
                true ->
                    ok
            end,
            compile_stdlib()
    end.

%% Check if standard library files are compiled
check_stdlib_compiled(_StdlibPaths) ->
    % Get only the working .cure files in the standard library
    % Only check for files that actually exist to avoid unnecessary rebuilds
    AllStdlibSources = [
        "lib/std.cure",
        "lib/std/core.cure",
        "lib/std/io.cure",
        "lib/std/list.cure",
        "lib/std/math.cure",
        "lib/std/result.cure",
        "lib/std/show.cure",
        "lib/std/vector.cure"
    ],
    % Filter to only check files that exist in the source tree
    StdlibSources = lists:filter(fun(F) -> filelib:is_regular(F) end, AllStdlibSources),

    % Convert to expected BEAM file paths
    ExpectedBeamFiles = lists:map(
        fun(CureFile) ->
            % Convert lib/std/module.cure -> _build/ebin/Std.Module.beam
            % Convert lib/module.cure -> _build/ebin/Module.beam
            case string:prefix(CureFile, "lib/std/") of
                nomatch ->
                    % lib/module.cure -> _build/ebin/Module.beam
                    BaseName = filename:basename(CureFile, ".cure"),
                    ModuleName = string:titlecase(BaseName),
                    "_build/ebin/" ++ ModuleName ++ ".beam";
                Rest ->
                    % lib/std/module.cure -> _build/ebin/Std.Module.beam
                    BaseName = filename:basename(Rest, ".cure"),
                    ModuleName = string:titlecase(BaseName),
                    "_build/ebin/Std." ++ ModuleName ++ ".beam"
            end
        end,
        StdlibSources
    ),

    % Check which BEAM files are missing
    Missing = lists:filter(
        fun(BeamFile) -> not filelib:is_regular(BeamFile) end,
        ExpectedBeamFiles
    ),

    case Missing of
        [] -> ok;
        MissingFiles -> {missing, MissingFiles}
    end.

%% Compile standard library using make
compile_stdlib() ->
    cure_utils:debug("Compiling Cure standard library...~n"),
    case os:cmd("make -C . stdlib 2>&1") of
        _Output ->
            case check_stdlib_compiled(["_build/lib", "_build/lib/std"]) of
                ok ->
                    cure_utils:debug("Standard library compilation completed successfully~n"),
                    ok;
                {missing, MissingFiles} ->
                    io:format(
                        "Standard library compilation completed but some files are missing:~n"
                    ),
                    lists:foreach(
                        fun(File) -> cure_utils:debug("  Missing: ~s~n", [File]) end,
                        MissingFiles
                    ),
                    % Try to compile individual missing files
                    case compile_missing_stdlib_files(MissingFiles) of
                        ok -> ok;
                        {error, _} = Error -> Error
                    end
            end
    end.

%% Compile individual missing standard library files
compile_missing_stdlib_files(MissingBeamFiles) ->
    cure_utils:debug("Attempting to compile missing standard library files individually...~n"),

    % Convert BEAM file paths back to source file paths
    SourceFiles = lists:filtermap(
        fun(BeamFile) ->
            case convert_beam_to_source_path(BeamFile) of
                {ok, SourcePath} ->
                    case filelib:is_regular(SourcePath) of
                        true -> {true, SourcePath};
                        false -> false
                    end;
                error ->
                    false
            end
        end,
        MissingBeamFiles
    ),

    % Compile each source file individually using direct compilation to avoid recursion
    Results = lists:map(
        fun(SourceFile) ->
            cure_utils:debug("  Compiling ~s...~n", [SourceFile]),
            % Call compile_file directly instead of using ./cure to avoid infinite recursion
            % Use minimal options since this is stdlib compilation
            StdlibOpts = #compile_options{
                output_dir = "_build/ebin",
                debug_info = true,
                warnings = false,
                verbose = false,
                % Skip type checking for stdlib to avoid circular deps
                type_check = false,
                optimize = false,
                fsm_runtime = false,
                stdlib_paths = []
            },
            case compile_file(SourceFile, StdlibOpts) of
                {ok, OutputFile} ->
                    cure_utils:debug("    Successfully compiled ~s~n", [OutputFile]),
                    ok;
                {error, Reason} ->
                    {error, {individual_compile_failed, SourceFile, Reason}}
            end
        end,
        SourceFiles
    ),

    % Check if all compilations succeeded
    case lists:all(fun(Result) -> Result =:= ok end, Results) of
        true ->
            ok;
        false ->
            Failures = [R || R <- Results, R =/= ok],
            {error, {partial_stdlib_compilation_failed, Failures}}
    end.

%% Convert BEAM file path back to source file path
convert_beam_to_source_path(BeamFile) ->
    case string:prefix(BeamFile, "_build/ebin/") of
        nomatch ->
            error;
        ModuleWithExt ->
            ModuleName = filename:basename(ModuleWithExt, ".beam"),
            case string:split(ModuleName, ".", trailing) of
                ["Std", SubModule] ->
                    SourcePath = "lib/std/" ++ string:lowercase(SubModule) ++ ".cure",
                    {ok, SourcePath};
                [SingleModule] ->
                    SourcePath = "lib/" ++ string:lowercase(SingleModule) ++ ".cure",
                    {ok, SourcePath};
                _ ->
                    error
            end
    end.

%% Add automatic standard library imports to user source code
add_automatic_stdlib_imports(Source, Options) ->
    case Options#compile_options.verbose of
        true -> cure_utils:debug("Adding automatic standard library imports...~n");
        false -> ok
    end,

    % Check if the source already has explicit imports or is a module definition
    case has_explicit_module_or_imports(Source) of
        true ->
            % If there are explicit imports/module def, don't add automatic ones
            Source;
        false ->
            % Add automatic imports for basic functionality
            AutoImports = [
                "# Automatic standard library imports",
                "import Std.Core [ok, error, some, none, identity, compose]",
                "import Std.Show [show, print]",
                "import Std.Math [abs, min, max]",
                "import Std.List [length, head, tail, map, filter]",
                "import Std.String [concat as string_concat, trim]",
                % Empty line separator
                "",
                Source
            ],
            string:join(AutoImports, "\n")
    end.

%% Check if source code already has explicit module definition or imports
has_explicit_module_or_imports(Source) ->
    Lines = string:split(Source, "\n", all),
    lists:any(
        fun(Line) ->
            TrimmedLine = string:trim(Line),
            string:prefix(TrimmedLine, "module ") =/= nomatch orelse
                string:prefix(TrimmedLine, "import ") =/= nomatch
        end,
        Lines
    ).
