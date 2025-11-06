#!/usr/bin/env escript
%% Generate pre-compiled type signatures from Cure standard library
%% This eliminates the need to parse stdlib files during compilation

-mode(compile).

%% We can't include headers in escript, so we pattern match on tuples

main([]) ->
    io:format("Generating type signatures from standard library...~n"),
    
    % Add paths to compiled modules
    code:add_path("_build/ebin"),
    
    % Load stdlib modules
    StdLibPath = "lib/std/",
    case file:list_dir(StdLibPath) of
        {ok, Files} ->
            CureFiles = [F || F <- Files, lists:suffix(".cure", F)],
            io:format("Found ~p stdlib files~n", [length(CureFiles)]),
            
            % Parse all stdlib files and extract signatures
            Signatures = collect_signatures(StdLibPath, CureFiles),
            io:format("Collected ~p function signatures~n", [maps:size(Signatures)]),
            
            % Generate Erlang module
            generate_signatures_module(Signatures),
            io:format("Generated src/types/cure_stdlib_signatures.erl~n"),
            io:format("Done!~n");
        {error, Reason} ->
            io:format("Error: Could not read stdlib directory: ~p~n", [Reason]),
            halt(1)
    end;
    
main(_) ->
    io:format("Usage: escript generate_type_signatures.escript~n"),
    halt(1).

%% Collect signatures from all stdlib files
collect_signatures(BasePath, Files) ->
    collect_signatures(BasePath, Files, #{}).

collect_signatures(_BasePath, [], Acc) ->
    Acc;
collect_signatures(BasePath, [File | Rest], Acc) ->
    FilePath = BasePath ++ File,
    io:format("  Processing ~s...~n", [File]),
    case cure_parser:parse_file(FilePath) of
        {ok, AST} ->
            ModuleFunctions = extract_module_functions(AST),
            NewAcc = maps:merge(Acc, ModuleFunctions),
            collect_signatures(BasePath, Rest, NewAcc);
        {error, Reason} ->
            io:format("  Warning: Could not parse ~s: ~p~n", [FilePath, Reason]),
            collect_signatures(BasePath, Rest, Acc)
    end.

%% Extract function signatures from AST
extract_module_functions(AST) ->
    extract_module_functions_helper(AST, #{}).

extract_module_functions_helper([], Acc) ->
    Acc;
extract_module_functions_helper([Item | Rest], Acc) ->
    case Item of
        {module_def, ModuleName, _Imports, _Exports, ModuleItems, _Location} ->
            ModuleFunctions = extract_functions_from_items(ModuleItems, ModuleName),
            NewAcc = maps:merge(Acc, ModuleFunctions),
            extract_module_functions_helper(Rest, NewAcc);
        {module_def, ModuleName, _Exports, ModuleItems, _Location} ->
            ModuleFunctions = extract_functions_from_items(ModuleItems, ModuleName),
            NewAcc = maps:merge(Acc, ModuleFunctions),
            extract_module_functions_helper(Rest, NewAcc);
        _ ->
            extract_module_functions_helper(Rest, Acc)
    end.

extract_functions_from_items(Items, ModuleName) ->
    extract_functions_from_items_helper(Items, ModuleName, #{}).

extract_functions_from_items_helper([], _ModuleName, Acc) ->
    Acc;
extract_functions_from_items_helper([Item | Rest], ModuleName, Acc) ->
    try
        case Item of
            % Match function_def record as tuple
            {function_def, Name, Params, _Body, ReturnType, _Constraint, _WhereClause, _Clauses, IsPrivate, _Location} 
                    when is_list(Params) ->
                case IsPrivate of
                    false ->
                        FunctionType = create_function_type_from_signature(Params, ReturnType),
                        Key = {ModuleName, Name, length(Params)},
                        NewAcc = maps:put(Key, FunctionType, Acc),
                        extract_functions_from_items_helper(Rest, ModuleName, NewAcc);
                    _ ->
                        extract_functions_from_items_helper(Rest, ModuleName, Acc)
                end;
            % Match curify_function_def record as tuple  
            {curify_function_def, Name, Params, ReturnType, _ErlModule, _ErlFunc, _ErlArity, IsPrivate, _Location}
                    when is_list(Params) ->
                case IsPrivate of
                    false ->
                        FunctionType = create_function_type_from_signature(Params, ReturnType),
                        Key = {ModuleName, Name, length(Params)},
                        NewAcc = maps:put(Key, FunctionType, Acc),
                        extract_functions_from_items_helper(Rest, ModuleName, NewAcc);
                    _ ->
                        extract_functions_from_items_helper(Rest, ModuleName, Acc)
                end;
            _ ->
                extract_functions_from_items_helper(Rest, ModuleName, Acc)
        end
    catch
        _:_ ->
            % Skip items that cause errors
            extract_functions_from_items_helper(Rest, ModuleName, Acc)
    end.

%% Create function type from parameters and return type
create_function_type_from_signature(Params, ReturnType) ->
    ParamTypes = [convert_param_type(P) || P <- Params],
    case ReturnType of
        undefined ->
            {function_type, ParamTypes, {type_var, '_'}};
        _ ->
            ReturnTypeConverted = convert_type(ReturnType),
            {function_type, ParamTypes, ReturnTypeConverted}
    end.

%% Convert parameter type to internal representation
convert_param_type({param, _Name, Type, _Location}) ->
    convert_type(Type);
convert_param_type(_) ->
    {type_var, '_'}.

%% Convert type expression to internal representation
convert_type(undefined) ->
    {type_var, '_'};
convert_type({primitive_type, Name}) when is_atom(Name) ->
    {primitive_type, Name};
convert_type({list_type, ElemType, _Length}) ->
    {list_type, convert_type(ElemType), undefined};
convert_type({function_type, ParamTypes, ReturnType}) when is_list(ParamTypes) ->
    {function_type, [convert_type(P) || P <- ParamTypes], convert_type(ReturnType)};
convert_type({tuple_type, ElemTypes}) when is_list(ElemTypes) ->
    {tuple_type, [convert_type(E) || E <- ElemTypes]};
convert_type({dependent_type, Name, Params}) when is_atom(Name), is_list(Params) ->
    {dependent_type, Name, [convert_type(P) || P <- Params]};
convert_type(_Other) ->
    {type_var, '_'}.

%% Generate Erlang module with signatures
generate_signatures_module(Signatures) ->
    ModuleName = "cure_stdlib_signatures",
    OutputPath = "src/types/" ++ ModuleName ++ ".erl",
    
    % Generate module header
    Header = [
        "%% GENERATED FILE - DO NOT EDIT\n",
        "%% Generated by scripts/generate_type_signatures.escript\n",
        "%% Contains pre-compiled type signatures for Cure standard library\n",
        "\n",
        "-module(", ModuleName, ").\n",
        "-export([get_function_type/3, all_signatures/0]).\n",
        "\n",
        "%% Get function type signature for a stdlib function\n",
        "-spec get_function_type(atom(), atom(), integer()) -> {ok, term()} | not_found.\n"
    ],
    
    % Generate function clauses
    SortedKeys = lists:sort(maps:keys(Signatures)),
    FunctionClauses = lists:map(
        fun(Key = {Module, Name, Arity}) ->
            Type = maps:get(Key, Signatures),
            TypeStr = format_type(Type),
            io_lib:format("get_function_type(~p, ~p, ~p) ->\n    {ok, ~s};\n",
                         [Module, Name, Arity, TypeStr])
        end,
        SortedKeys
    ),
    
    % Catch-all clause
    CatchAll = "get_function_type(_, _, _) ->\n    not_found.\n\n",
    
    % Generate all_signatures/0 for debugging
    AllSigs = [
        "%% Return all signatures (for debugging)\n",
        "all_signatures() ->\n",
        "    #{",
        string:join([
            io_lib:format("\n        {~p, ~p, ~p} => ~s",
                         [M, N, A, format_type(maps:get({M,N,A}, Signatures))])
            || {M, N, A} <- SortedKeys
        ], ","),
        "\n    }.\n"
    ],
    
    % Write file
    Content = lists:flatten([Header, FunctionClauses, CatchAll, AllSigs]),
    file:write_file(OutputPath, Content).

%% Format type for Erlang source code
format_type({primitive_type, Name}) ->
    io_lib:format("{primitive_type, ~p}", [Name]);
format_type({type_var, Name}) ->
    io_lib:format("{type_var, ~p}", [Name]);
format_type({list_type, ElemType, undefined}) ->
    io_lib:format("{list_type, ~s, undefined}", [format_type(ElemType)]);
format_type({list_type, ElemType, Length}) ->
    io_lib:format("{list_type, ~s, ~p}", [format_type(ElemType), Length]);
format_type({function_type, ParamTypes, ReturnType}) ->
    ParamsStr = string:join([format_type(P) || P <- ParamTypes], ", "),
    io_lib:format("{function_type, [~s], ~s}", [ParamsStr, format_type(ReturnType)]);
format_type({tuple_type, ElemTypes}) ->
    ElemsStr = string:join([format_type(E) || E <- ElemTypes], ", "),
    io_lib:format("{tuple_type, [~s]}", [ElemsStr]);
format_type({dependent_type, Name, Params}) ->
    ParamsStr = string:join([format_type(P) || P <- Params], ", "),
    io_lib:format("{dependent_type, ~p, [~s]}", [Name, ParamsStr]);
format_type(Other) ->
    io_lib:format("~p", [Other]).
