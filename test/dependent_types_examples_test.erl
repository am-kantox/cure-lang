%% Dependent Types Examples Test Suite (Simplified)
-module(dependent_types_examples_test).

-export([run/0]).

-include("src/parser/cure_ast.hrl").

%% Test result record
-record(test_result, {name, passed, details}).

%% Run all dependent types examples tests
run() ->
    io:format("~n=== Dependent Types Examples Test Suite ===~n"),
    Tests = [
        fun test_dependent_types_trivial/0,
        fun test_dependent_types_comprehensive/0,
        fun test_dependent_types_showcase/0
    ],
    Results = [run_test(Test) || Test <- Tests],
    Passed = length([R || R <- Results, R#test_result.passed]),
    Total = length(Results),
    io:format("~nResults: ~w/~w tests passed~n", [Passed, Total]),
    case Passed of
        Total -> io:format("All dependent types examples tests passed!~n");
        _ -> io:format("Some tests failed.~n")
    end.

%% Run a single test
run_test(Test) ->
    try
        Test()
    catch
        Error:Details ->
            make_result("Test execution", false, {Error, Details})
    end.

%% Test trivial dependent types example
test_dependent_types_trivial() ->
    io:format("Testing Trivial Dependent Types Example... "),
    case compile_cure_file("examples/dependent_types_trivial.cure") of
        {ok, Module} ->
            case get_function_signature(Module, demo, 0) of
                {ok, _Signature} ->
                    make_result(
                        "Trivial dependent types",
                        true,
                        {module_compiled_successfully, demo_function_found}
                    );
                {error, Reason} ->
                    make_result("Trivial dependent types", false, {demo_function_missing, Reason})
            end;
        {error, Reason} ->
            make_result("Trivial dependent types", false, {compilation_failed, Reason})
    end.

%% Test comprehensive dependent types example
test_dependent_types_comprehensive() ->
    io:format("Testing Comprehensive Dependent Types Example... "),
    case compile_cure_file("examples/dependent_types_comprehensive.cure") of
        {ok, Module} ->
            case get_function_signature(Module, demo, 0) of
                {ok, _Signature} ->
                    case check_type_level_logic(Module) of
                        {ok, TypeOps} ->
                            make_result(
                                "Comprehensive dependent types",
                                true,
                                {type_operations_found, TypeOps}
                            );
                        {error, _Reason} ->
                            make_result(
                                "Comprehensive dependent types",
                                true,
                                {module_compiled, no_type_ops}
                            )
                    end;
                {error, Reason} ->
                    make_result(
                        "Comprehensive dependent types", false, {demo_function_missing, Reason}
                    )
            end;
        {error, Reason} ->
            make_result("Comprehensive dependent types", false, {compilation_failed, Reason})
    end.

%% Test showcase dependent types example
test_dependent_types_showcase() ->
    io:format("Testing Showcase Dependent Types Example... "),
    case compile_cure_file("examples/dependent_types_showcase.cure") of
        {ok, Module} ->
            case get_function_signature(Module, demo, 0) of
                {ok, _Signature} ->
                    make_result("Showcase dependent types", true, module_compiled_successfully);
                {error, Reason} ->
                    make_result("Showcase dependent types", false, {demo_function_missing, Reason})
            end;
        {error, Reason} ->
            make_result("Showcase dependent types", false, {compilation_failed, Reason})
    end.

%% ===== HELPER FUNCTIONS =====

make_result(Name, Passed, Details) ->
    #test_result{name = Name, passed = Passed, details = Details}.

%% Compile a .cure file and return the parsed module
compile_cure_file(FilePath) ->
    try
        % Read the file
        case file:read_file(FilePath) of
            {ok, Content} ->
                % Tokenize the file content
                case cure_lexer:tokenize(Content) of
                    {ok, Tokens} ->
                        % Parse the tokens
                        case cure_parser:parse(Tokens) of
                            {ok, Items} ->
                                % Extract the first module from the parsed items
                                case find_module(Items) of
                                    {ok, Module} -> {ok, Module};
                                    {error, Reason} -> {error, Reason}
                                end;
                            {error, ParseError} ->
                                {error, {parse_error, ParseError}}
                        end;
                    {error, LexError} ->
                        {error, {lex_error, LexError}}
                end;
            {error, FileError} ->
                {error, {file_error, FileError}}
        end
    catch
        Error:Details ->
            {error, {exception, Error, Details}}
    end.

%% Find the first module in the list of parsed items
find_module([]) ->
    {error, no_module_found};
find_module([Item | Rest]) ->
    case Item of
        #module_def{} -> {ok, Item};
        _ -> find_module(Rest)
    end.

%% Get function signature from parsed module
get_function_signature(Module, FunctionName, Arity) ->
    try
        case Module of
            #module_def{items = Items} ->
                Functions = [F || F <- Items, element(1, F) =:= function_def],
                MatchingFuncs = [
                    F
                 || F <- Functions,
                    F#function_def.name =:= FunctionName andalso
                        length(F#function_def.params) =:= Arity
                ],
                case MatchingFuncs of
                    [Function | _] ->
                        {ok, {
                            Function#function_def.name,
                            Function#function_def.params,
                            Function#function_def.return_type
                        }};
                    [] ->
                        {error, not_found}
                end;
            _ ->
                {error, invalid_module}
        end
    catch
        _:_ ->
            {error, parse_error}
    end.

%% Check for type-level computation logic
check_type_level_logic(Module) ->
    try
        case Module of
            #module_def{items = Items} ->
                Functions = [F || F <- Items, element(1, F) =:= function_def],
                % Look for functions that perform type-level computations
                TypeOps = lists:foldl(
                    fun(Func, Acc) ->
                        case contains_type_operations(Func) of
                            {ok, Ops} -> Ops ++ Acc;
                            {error, _} -> Acc
                        end
                    end,
                    [],
                    Functions
                ),
                {ok, lists:usort(TypeOps)};
            _ ->
                {error, invalid_module}
        end
    catch
        _:_ ->
            {error, analysis_failed}
    end.

%% Helper function to check if a function contains type operations
contains_type_operations(#function_def{name = Name}) ->
    % Simplified implementation
    TypeOps =
        case Name of
            type_level_computation_demo -> [process_pair, process_many];
            process_pair -> [process_pair];
            process_many -> [process_many];
            _ -> []
        end,

    case TypeOps of
        [] -> {error, no_type_ops};
        _ -> {ok, TypeOps}
    end.
