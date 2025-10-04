%% Cure Programming Language - Command Line Interface
%% Provides a unified CLI for compiling .cure files to BEAM bytecode
-module(cure_cli).

-export([
    main/1,           % Main entry point for escript
    compile_file/1,   % Compile a single .cure file
    compile_file/2,   % Compile with options
    compile_opts_to_codegen_opts/1,  %% Convert compile options to codegen options
    get_module_info/1, %% Get module information from AST (simplified, for future use)
    check_cure_installation/0, %% Utility function to check if we have a complete Cure installation
    help/0,           % Show help information
    version/0         % Show version information
]).

-include("parser/cure_ast_simple.hrl").

%% Version information
-define(CURE_VERSION, "0.1.0").
-define(CURE_DESCRIPTION, "Cure Programming Language Compiler").

%% Exit codes
-define(EXIT_SUCCESS, 0).
-define(EXIT_ERROR, 1).
-define(EXIT_USAGE, 2).

%% Default options
-record(compile_options, {
    output_file = undefined,      % Output .beam file path
    output_dir = "_build/ebin",   % Output directory
    debug_info = true,            % Include debug information
    warnings = true,              % Show warnings
    verbose = false,              % Verbose output
    type_check = true,            % Enable type checking
    optimize = true,              % Enable optimizations
    fsm_runtime = true            % Include FSM runtime
}).

%% ============================================================================
%% Main Entry Point
%% ============================================================================

%% Main entry point for escript usage
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

parse_args(["--help"|_]) ->
    {help};

parse_args(["-h"|_]) ->
    {help};

parse_args(["--version"|_]) ->
    {version};

parse_args(["-v"|_]) ->
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

%% Compile a .cure file with default options
compile_file(Filename) ->
    compile_file(Filename, #compile_options{}).

%% Compile a .cure file with specified options
compile_file(Filename, Options) ->
    case filelib:is_regular(Filename) of
        false ->
            {error, {file_not_found, Filename}};
        true ->
            compile_file_impl(Filename, Options)
    end.

%% Implementation of file compilation
compile_file_impl(Filename, Options) ->
    if Options#compile_options.verbose ->
        io:format("Compiling ~s...~n", [Filename]);
    true -> ok
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
    end.

%% Compile source code through the full pipeline
compile_source(Filename, Source, Options) ->
    Pipeline = [
        {"Lexical Analysis", fun(Src) -> cure_lexer:tokenize(list_to_binary(Src)) end},
        {"Parsing", fun(Tokens) -> cure_parser:parse(Tokens) end},
        {"Type Checking", fun(AST) -> 
            case Options#compile_options.type_check of
                true -> type_check_ast(AST);
                false -> {ok, AST}
            end
        end},
        {"Code Generation", fun(AST) -> 
            if Options#compile_options.verbose ->
                io:format("    AST structure: ~p~n", [AST]);
            true -> ok
            end,
            
            % Use the actual code generator
            CodegenOpts = compile_opts_to_codegen_opts(Options),
            case cure_codegen:compile_program(AST, CodegenOpts) of
                {ok, CompiledModules} ->
                    % Take the first module and generate BEAM file
                    case CompiledModules of
                        [Module | _] ->
                            % Generate BEAM binary in memory
                            case cure_codegen:convert_to_erlang_forms(Module) of
                                {ok, Forms} ->
                                    case compile:forms(Forms, [binary, return_errors]) of
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
    
    case run_pipeline(Pipeline, Source, Options) of
        {ok, {ModuleName, BeamBinary}} ->
            write_output(Filename, {ModuleName, BeamBinary}, Options);
        {ok, BeamBinary} when is_binary(BeamBinary) ->
            % Fallback for old format
            write_output(Filename, BeamBinary, Options);
        {error, Stage, Reason} ->
            if Options#compile_options.verbose ->
                io:format("Compilation failed at ~s: ~p~n", [Stage, Reason]);
            true -> ok
            end,
            {error, {compilation_stage_failed, Stage, Reason}}
    end.

%% Run the compilation pipeline
run_pipeline([], Result, _Options) ->
    {ok, Result};

run_pipeline([{StageName, StageFunc} | RestStages], Input, Options) ->
    if Options#compile_options.verbose ->
        io:format("  ~s...~n", [StageName]);
    true -> ok
    end,
    
    case StageFunc(Input) of
        {ok, Output} ->
            run_pipeline(RestStages, Output, Options);
        {error, Reason} ->
            {error, StageName, Reason};
        % Handle cases where stage function returns result directly
        Output ->
            run_pipeline(RestStages, Output, Options)
    end.

%% Type check AST (simplified version)
type_check_ast(AST) ->
    try
        TypeEnv = cure_typechecker:builtin_env(),
        case AST of
            [FirstItem | _] when is_record(FirstItem, module_def) ->
                % Single module case - check the first (and should be only) module
                case cure_typechecker:check_module(FirstItem, TypeEnv) of
                    {ok, _NewEnv, _Result} ->
                        io:format("Type checking successful~n"),
                        {ok, AST};
                    {error, Reason} -> 
                        io:format("Type checking error: ~p~n", [Reason]),
                        {error, Reason}
                end;
            Items when is_list(Items) ->
                % Multiple top-level items - check them as a program
                case cure_typechecker:check_program(Items) of
                    Result when is_tuple(Result) ->
                        % Check if it looks like a success result
                        case element(1, Result) of
                            success_result -> 
                                io:format("Type checking successful~n"),
                                {ok, AST};
                            _ ->
                                % Try to extract error information
                                case tuple_size(Result) >= 2 of
                                    true ->
                                        case element(2, Result) of
                                            true -> 
                                                io:format("Type checking successful~n"),
                                                {ok, AST};
                                            false ->
                                                io:format("Type checking failed~n"),
                                                {error, type_check_failed}
                                        end;
                                    false ->
                                        io:format("Type checking failed (unknown format)~n"),
                                        {error, type_check_failed}
                                end
                        end;
                    {error, Reason} -> 
                        io:format("Type checking error: ~p~n", [Reason]),
                        {error, Reason}
                end;
            SingleItem ->
                % Single non-module item - check as program with single item
                case cure_typechecker:check_program([SingleItem]) of
                    Result when is_tuple(Result) ->
                        % Check if it looks like a success result
                        case element(1, Result) of
                            success_result -> 
                                io:format("Type checking successful~n"),
                                {ok, AST};
                            _ ->
                                % Try to extract error information
                                case tuple_size(Result) >= 2 of
                                    true ->
                                        case element(2, Result) of
                                            true -> 
                                                io:format("Type checking successful~n"),
                                                {ok, AST};
                                            false ->
                                                io:format("Type checking failed~n"),
                                                {error, type_check_failed}
                                        end;
                                    false ->
                                        io:format("Type checking failed (unknown format)~n"),
                                        {error, type_check_failed}
                                end
                        end;
                    {error, Reason} -> 
                        io:format("Type checking error: ~p~n", [Reason]),
                        {error, Reason}
                end
        end
    catch
        Class:Error:Stack ->
            % If type checking fails with exception, provide more detailed error
            io:format("Warning: Type checking failed with exception ~p:~p~n", [Class, Error]),
            case os:getenv("CURE_DEBUG") of
                "1" -> io:format("Stack trace: ~p~n", [Stack]);
                _ -> ok
            end,
            io:format("Proceeding without type information~n"),
            {ok, AST}
    end.

%% Convert compile options to codegen options
compile_opts_to_codegen_opts(Options) ->
    CodegenOpts = [],
    
    CodegenOpts1 = case Options#compile_options.debug_info of
        true -> [{debug_info, true} | CodegenOpts];
        false -> CodegenOpts
    end,
    
    CodegenOpts2 = case Options#compile_options.optimize of
        true -> [{optimize, 1} | CodegenOpts1];
        false -> CodegenOpts1
    end,
    
    CodegenOpts3 = case Options#compile_options.warnings of
        true -> [{warnings, true} | CodegenOpts2];
        false -> CodegenOpts2
    end,
    
    CodegenOpts4 = case Options#compile_options.fsm_runtime of
        true -> [{fsm_integration, true} | CodegenOpts3];
        false -> CodegenOpts3
    end,
    
    CodegenOpts4.

%% Write output file
write_output(InputFilename, BeamData, Options) ->
    {OutputFile, BeamBinary} = case BeamData of
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

%% Display help information
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
    io:format("~n"),
    io:format("EXAMPLES:~n"),
    io:format("    cure examples/simple.cure~n"),
    io:format("    cure examples/fsm_demo.cure -o fsm_demo.beam~n"),
    io:format("    cure src/my_module.cure --verbose -d build/~n"),
    io:format("~n"),
    io:format("ENVIRONMENT VARIABLES:~n"),
    io:format("    CURE_DEBUG=1         Enable debug stack traces~n").

%% Display version information
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

%% Get module information from AST (simplified, for future use)
get_module_info(AST) when is_tuple(AST) ->
    % For now, just return a generic structure
    % TODO: Extract actual module info when AST types are available
    #{
        name => unknown,
        exports => [],
        type => module
    };

get_module_info(_) ->
    #{
        name => undefined,
        exports => [],
        type => unknown
    }.

%% Utility function to check if we have a complete Cure installation
check_cure_installation() ->
    RequiredModules = [cure_lexer, cure_parser, cure_typechecker, cure_codegen],
    Missing = lists:filter(fun(Module) ->
        case code:which(Module) of
            non_existing -> true;
            _ -> false
        end
    end, RequiredModules),
    
    case Missing of
        [] -> ok;
        MissingModules ->
            io:format("Warning: Missing Cure compiler modules: ~p~n", [MissingModules]),
            io:format("Make sure to run 'make all' to build the complete compiler~n"),
            {error, {missing_modules, MissingModules}}
    end.

