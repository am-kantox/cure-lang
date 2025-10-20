%% Enhanced compilation wrapper with better error reporting
-module(cure_compile_wrapper).

-export([
    compile_source_file/1,
    compile_source_file/2,
    format_error/1,
    get_error_suggestions/1
]).

-include("../parser/cure_ast.hrl").

%% Compile a Cure source file with enhanced error reporting
compile_source_file(SourceFile) ->
    compile_source_file(SourceFile, []).

compile_source_file(SourceFile, Options) ->
    try
        io:format("Compiling ~s...~n", [SourceFile]),

        % Step 1: Lexical analysis
        case cure_lexer:tokenize_file(SourceFile) of
            {ok, Tokens} ->
                io:format("✓ Lexical analysis: ~p tokens~n", [length(Tokens)]),

                % Step 2: Parsing
                case cure_parser:parse(Tokens) of
                    {ok, AST} ->
                        io:format("✓ Parsing: AST generated~n"),

                        % Step 3: Module structure creation
                        case create_module_ast(AST, SourceFile) of
                            {ok, ModuleAST} ->
                                io:format("✓ Module structure: Created~n"),
                                cure_utils:debug("Created ModuleAST: ~p~n", [ModuleAST]),

                                % Step 4: Code generation
                                cure_utils:debug("ModuleAST format: ~p~n", [ModuleAST]),
                                case cure_codegen:compile_module(ModuleAST, Options) of
                                    {ok, Module} ->
                                        io:format("✓ Code generation: Success~n"),

                                        % Step 5: BEAM generation
                                        ModuleName = maps:get(name, Module),
                                        BeamFile = atom_to_list(ModuleName) ++ ".beam",
                                        case cure_codegen:generate_beam_file(Module, BeamFile) of
                                            {ok, {LoadedName, Path}} ->
                                                io:format("✓ BEAM generation: ~s~n", [Path]),
                                                {ok, {LoadedName, Path}};
                                            {error, BeamError} ->
                                                {error,
                                                    {beam_generation_failed, BeamError,
                                                        get_beam_error_suggestions(BeamError)}}
                                        end;
                                    {error, CodegenError} ->
                                        {error,
                                            {code_generation_failed, CodegenError,
                                                get_codegen_error_suggestions(CodegenError)}}
                                end;
                            {error, ModuleError} ->
                                {error,
                                    {module_structure_failed, ModuleError,
                                        get_module_error_suggestions(ModuleError)}}
                        end;
                    {error, ParseError} ->
                        {error,
                            {parsing_failed, ParseError, get_parse_error_suggestions(ParseError)}}
                end;
            {error, LexError} ->
                {error, {lexical_analysis_failed, LexError, get_lex_error_suggestions(LexError)}}
        end
    catch
        Error:Reason:Stack ->
            {error,
                {compilation_exception, Error, Reason, Stack,
                    get_exception_suggestions(Error, Reason)}}
    end.

%% Create proper module AST from parsed items
create_module_ast(AST, SourceFile) ->
    try
        case AST of
            % Case 1: Parsed module structure (already correct format)
            [{module_def, Name, Exports, Items, Location}] ->
                % This is the format from parser: {module_def, Name, ExportList, Items, Location}
                % Convert to codegen format: {module_def, Name, Imports, Exports, Items, Location}
                ConvertedExports = convert_parsed_exports(Exports),
                {ok, {module_def, Name, [], ConvertedExports, Items, Location}};
            % Case 2: List of functions (bare functions without module wrapper)
            Items when is_list(Items) ->
                % Check if first item is a module_def (different arity)
                case Items of
                    [{module_def, Name, Exports, ModuleItems, Location}] ->
                        % Handle parsed module with different arity
                        ConvertedExports = convert_parsed_exports(Exports),
                        {ok, {module_def, Name, [], ConvertedExports, ModuleItems, Location}};
                    _ ->
                        % Regular list of items - create wrapper module
                        ExportSpecs = extract_exports(Items),
                        ModuleName = get_module_name_from_file(SourceFile),
                        ModuleAST =
                            {module_def, ModuleName, [],
                                {export_list, ExportSpecs, {location, 1, 1, undefined}}, Items,
                                {location, 1, 1, undefined}},
                        {ok, ModuleAST}
                end;
            % Case 3: Single item
            Item ->
                ExportSpecs = extract_exports([Item]),
                ModuleName = get_module_name_from_file(SourceFile),
                ModuleAST =
                    {module_def, ModuleName, [],
                        {export_list, ExportSpecs, {location, 1, 1, undefined}}, [Item],
                        {location, 1, 1, undefined}},
                {ok, ModuleAST}
        end
    catch
        _:CreateReason ->
            {error, {invalid_ast_structure, AST, CreateReason}}
    end.

%% Convert parsed export format to codegen expected format
convert_parsed_exports(Exports) when is_list(Exports) ->
    % Parser returns list of export_spec records directly
    {export_list, Exports, {location, 1, 1, undefined}};
convert_parsed_exports(Exports) ->
    % Already in correct format
    Exports.

%% Extract module name from file path
get_module_name_from_file(FilePath) ->
    BaseName = filename:basename(FilePath, ".cure"),
    list_to_atom(BaseName).

%% Extract exports from function definitions
extract_exports(Items) ->
    extract_exports(Items, []).

extract_exports([], Acc) ->
    lists:reverse(Acc);
extract_exports([{function_def, Name, Params, _RetType, _Constraint, _Body, Location} | Rest], Acc) ->
    Arity = length(Params),
    Export = {export_spec, Name, Arity, Location},
    extract_exports(Rest, [Export | Acc]);
extract_exports([_ | Rest], Acc) ->
    extract_exports(Rest, Acc).

%% Error formatting functions
format_error({lexical_analysis_failed, Error, Suggestions}) ->
    io_lib:format("Lexical Analysis Error: ~p~n~s", [Error, format_suggestions(Suggestions)]);
format_error({parsing_failed, Error, Suggestions}) ->
    io_lib:format("Parsing Error: ~p~n~s", [Error, format_suggestions(Suggestions)]);
format_error({module_structure_failed, Error, Suggestions}) ->
    io_lib:format("Module Structure Error: ~p~n~s", [Error, format_suggestions(Suggestions)]);
format_error({code_generation_failed, Error, Suggestions}) ->
    io_lib:format("Code Generation Error: ~p~n~s", [Error, format_suggestions(Suggestions)]);
format_error({beam_generation_failed, Error, Suggestions}) ->
    io_lib:format("BEAM Generation Error: ~p~n~s", [Error, format_suggestions(Suggestions)]);
format_error({compilation_exception, Error, Reason, _Stack, Suggestions}) ->
    io_lib:format("Compilation Exception: ~p:~p~n~s", [
        Error, Reason, format_suggestions(Suggestions)
    ]);
format_error(Error) ->
    io_lib:format("Unknown Error: ~p", [Error]).

format_suggestions(Suggestions) when is_list(Suggestions), length(Suggestions) > 0 ->
    % Ensure all suggestions are strings
    StringSuggestions = [lists:flatten(io_lib:format("~s", [S])) || S <- Suggestions],
    SuggestionText = string:join(StringSuggestions, "\n  - "),
    io_lib:format("Suggestions:~n  - ~s", [SuggestionText]);
format_suggestions(_) ->
    "".

%% Error suggestion functions
get_lex_error_suggestions({unexpected_character, Char}) ->
    [
        io_lib:format(
            "Unexpected character '~c' (~p). Check for typos or unsupported operators.", [
                Char, Char
            ]
        ),
        "Make sure you're using supported operators like 'and'/'or' instead of '&&'/'||'"
    ];
get_lex_error_suggestions(_) ->
    ["Check source file for invalid characters or syntax"].

get_parse_error_suggestions({unexpected_token, Token}) ->
    [
        io_lib:format("Unexpected token: ~p. Check syntax around this token.", [Token]),
        "Make sure all expressions are properly terminated",
        "Check that all 'do'/'end' blocks are balanced"
    ];
get_parse_error_suggestions(_) ->
    ["Check syntax and ensure proper nesting of expressions"].

get_module_error_suggestions({invalid_ast_structure, _AST, _Reason}) ->
    [
        "The parsed AST doesn't match expected module structure",
        "Make sure your source file contains proper function definitions",
        "If using module syntax, ensure 'module Name do ... end' structure"
    ];
get_module_error_suggestions(_) ->
    ["Check module definition and structure"].

get_codegen_error_suggestions({unsupported_module_item, Item}) ->
    [
        io_lib:format("Unsupported module item: ~p", [element(1, Item)]),
        "This might be a nested module definition",
        "Try using simpler function definitions without nested modules",
        "Check that all language constructs are supported"
    ];
get_codegen_error_suggestions({not_a_module, _}) ->
    [
        "Expected a module AST but got something else",
        "Make sure the parser is returning a proper module structure"
    ];
get_codegen_error_suggestions({function_compilation_failed, Name, Reason}) ->
    [
        io_lib:format("Function '~p' failed to compile: ~p", [Name, Reason]),
        "Check function syntax and type annotations",
        "Ensure all expressions in the function body are valid"
    ];
get_codegen_error_suggestions(_) ->
    ["Code generation failed - check language construct support"].

get_beam_error_suggestions({form_conversion_failed, _Reason, _Stack}) ->
    [
        "Failed to convert internal representation to Erlang forms",
        "This might be due to unsupported language features",
        "Try using simpler constructs"
    ];
get_beam_error_suggestions(_) ->
    ["BEAM file generation failed"].

get_exception_suggestions(error, {badmatch, _}) ->
    [
        "Pattern match failure - check that functions return expected values",
        "This might indicate an internal compiler error"
    ];
get_exception_suggestions(_, _) ->
    ["Unexpected exception during compilation"].

%% Get comprehensive error suggestions
get_error_suggestions(Error) ->
    case Error of
        {lexical_analysis_failed, LexError, _} -> get_lex_error_suggestions(LexError);
        {parsing_failed, ParseError, _} -> get_parse_error_suggestions(ParseError);
        {module_structure_failed, ModError, _} -> get_module_error_suggestions(ModError);
        {code_generation_failed, CodegenError, _} -> get_codegen_error_suggestions(CodegenError);
        {beam_generation_failed, BeamError, _} -> get_beam_error_suggestions(BeamError);
        _ -> ["Unknown error type"]
    end.
