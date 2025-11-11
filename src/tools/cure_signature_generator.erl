%% Generate pre-compiled type signatures from Cure standard library
-module(cure_signature_generator).
-export([generate/0]).

-include("../parser/cure_ast.hrl").

generate() ->
    io:format("Generating type signatures from standard library...~n"),

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
            io:format("Done!~n"),
            ok;
        {error, Reason} ->
            io:format("Error: Could not read stdlib directory: ~p~n", [Reason]),
            {error, Reason}
    end.

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
        #module_def{name = ModuleName, items = ModuleItems} ->
            % Record format (most common from parser)
            ModuleFunctions = extract_functions_from_items(ModuleItems, ModuleName),
            NewAcc = maps:merge(Acc, ModuleFunctions),
            extract_module_functions_helper(Rest, NewAcc);
        {module_def, ModuleName, _Imports, _Exports, ModuleItems, _Location} ->
            ModuleFunctions = extract_functions_from_items(ModuleItems, ModuleName),
            NewAcc = maps:merge(Acc, ModuleFunctions),
            extract_module_functions_helper(Rest, NewAcc);
        {module_def, ModuleName, _Exports, ModuleItems, _Location} ->
            % 4-element version without imports
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
            #function_def{
                name = Name, params = Params, return_type = ReturnType, is_private = IsPrivate
            } when
                Params =/= undefined, is_list(Params)
            ->
                case IsPrivate of
                    false ->
                        FunctionType = create_function_type_from_signature(Params, ReturnType),
                        Key = {ModuleName, Name, length(Params)},
                        NewAcc = maps:put(Key, FunctionType, Acc),
                        extract_functions_from_items_helper(Rest, ModuleName, NewAcc);
                    _ ->
                        extract_functions_from_items_helper(Rest, ModuleName, Acc)
                end;
            #curify_function_def{
                name = Name, params = Params, return_type = ReturnType, is_private = IsPrivate
            } when
                is_list(Params)
            ->
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
    %% Debug output
    %% io:format("  Params: ~p~n", [Params]),
    %% io:format("  ParamTypes: ~p~n", [ParamTypes]),
    case ReturnType of
        undefined ->
            {function_type, ParamTypes, {type_var, '_'}};
        _ ->
            ReturnTypeConverted = convert_type(ReturnType),
            %% io:format("  ReturnType: ~p~n  Converted: ~p~n", [ReturnType, ReturnTypeConverted]),
            {function_type, ParamTypes, ReturnTypeConverted}
    end.

%% Convert parameter type to internal representation
convert_param_type(#param{type = Type}) ->
    convert_type(Type);
convert_param_type(_) ->
    {type_var, '_'}.

%% Convert type expression to internal representation
convert_type(undefined) ->
    {type_var, '_'};
convert_type(#primitive_type{name = Name}) ->
    {primitive_type, Name};
convert_type({primitive_type, Name, _Location}) when is_atom(Name) ->
    %% Handle 3-tuple format with location (from parser)
    convert_type({primitive_type, Name});
convert_type({primitive_type, Name}) when is_atom(Name) ->
    %% Handle 2-tuple format without location
    {primitive_type, Name};
convert_type({list_type, ElemType, _Length}) ->
    {list_type, convert_type(ElemType), undefined};
convert_type({function_type, ParamTypes, ReturnType, _Location}) when is_list(ParamTypes) ->
    %% Handle 4-tuple format with location (from parser)
    {function_type, [convert_type(P) || P <- ParamTypes], convert_type(ReturnType)};
convert_type({function_type, ParamTypes, ReturnType}) when is_list(ParamTypes) ->
    %% Handle 3-tuple format without location
    {function_type, [convert_type(P) || P <- ParamTypes], convert_type(ReturnType)};
convert_type({tuple_type, ElemTypes}) when is_list(ElemTypes) ->
    {tuple_type, [convert_type(E) || E <- ElemTypes]};
convert_type(#dependent_type{name = Name, params = Params}) when is_list(Params) ->
    %% Handle dependent type records - preserve type parameters
    {dependent_type, Name, [convert_type_param(P) || P <- Params]};
convert_type({dependent_type, Name, Params}) when is_atom(Name), is_list(Params) ->
    {dependent_type, Name, [convert_type_param(P) || P <- Params]};
convert_type(_Other) ->
    {type_var, '_'}.

%% Convert type parameter (used in dependent types)
convert_type_param(#type_param{name = Name, value = Value}) ->
    %% For dependent types like Vector(T, n), we need to preserve the parameter structure
    %% Create a tuple representation that the type system can work with
    {type_param, Name, convert_type_param_value(Value)};
convert_type_param(Other) ->
    %% If it's not a type_param record, try to convert it as a type
    convert_type(Other).

%% Convert type parameter value
convert_type_param_value(#primitive_type{name = Name, location = _Loc}) ->
    %% Check if this is a type variable (T, U, etc.) or a value variable (n, m, etc.)
    %% Type variables are typically uppercase, value variables are lowercase
    case is_type_variable_name(Name) of
        true ->
            %% Type parameter like T, U - convert to type_var
            %% Create tuple that will be formatted as record syntax in output
            {type_var_record, Name};
        false ->
            %% Value parameter like n, m - keep as identifier expression
            {identifier_expr, Name, undefined}
    end;
convert_type_param_value({primitive_type, Name, _Loc}) ->
    %% Handle tuple format
    case is_type_variable_name(Name) of
        true ->
            {type_var_record, Name};
        false ->
            {identifier_expr, Name, undefined}
    end;
convert_type_param_value({primitive_type, Name}) ->
    %% Handle simple tuple format without location
    case is_type_variable_name(Name) of
        true ->
            {type_var_record, Name};
        false ->
            {identifier_expr, Name, undefined}
    end;
convert_type_param_value(#identifier_expr{name = Name}) ->
    %% Type parameter referring to a value like n or m
    {identifier_expr, Name, undefined};
convert_type_param_value({identifier_expr, Name, _Loc}) ->
    %% Type parameter value expression
    {identifier_expr, Name, undefined};
convert_type_param_value(Other) ->
    %% Other type expressions - recursively convert
    convert_type(Other).

%% Check if a name is a type variable (uppercase) vs value variable (lowercase)
is_type_variable_name(Name) when is_atom(Name) ->
    NameStr = atom_to_list(Name),
    case NameStr of
        [First | _] when First >= $A, First =< $Z -> true;
        _ -> false
    end;
is_type_variable_name(_) ->
    false.

%% Generate Erlang module with signatures
generate_signatures_module(Signatures) ->
    ModuleName = "cure_stdlib_signatures",
    OutputPath = "src/types/" ++ ModuleName ++ ".erl",

    % Generate module header
    Header = [
        "%% GENERATED FILE - DO NOT EDIT\n",
        "%% Generated by cure_signature_generator:generate/0\n",
        "%% Contains pre-compiled type signatures for Cure standard library\n",
        "\n",
        "-module(",
        ModuleName,
        ").\n",
        "-export([get_function_type/3, all_signatures/0]).\n",
        "\n",
        "%% Include AST record definitions for type_var and type_param\n",
        "-include(\"../parser/cure_ast.hrl\").\n",
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
            io_lib:format(
                "get_function_type(~p, ~p, ~p) ->\n    {ok, ~s};\n",
                [Module, Name, Arity, TypeStr]
            )
        end,
        SortedKeys
    ),

    % Catch-all clause
    CatchAll = "get_function_type(_, _, _) ->\n    not_found.\n\n",

    % Generate all_signatures/0 for debugging - simplified to avoid compilation issues
    AllSigs = [
        "%% Return all signatures (for debugging)\n",
        "all_signatures() ->\n",
        "    %% List of {Module, Function, Arity} tuples\n",
        "    [",
        string:join(
            [
                io_lib:format("\n        {~p, ~p, ~p}", [M, N, A])
             || {M, N, A} <- SortedKeys
            ],
            ","
        ),
        "\n    ].\n"
    ],

    % Write file
    Content = lists:flatten([Header, FunctionClauses, CatchAll, AllSigs]),
    file:write_file(OutputPath, Content).

%% Format type for Erlang source code
format_type({primitive_type, Name}) ->
    io_lib:format("{primitive_type, ~p}", [Name]);
format_type({type_var, Name}) ->
    io_lib:format("{type_var, ~p}", [Name]);
format_type({type_var_record, Name}) ->
    %% Format as tuple for dependent type parameters (avoids needing record defs)
    io_lib:format("{type_var, ~p, ~p, []}", [Name, Name]);
format_type({type_param, Name, Value}) ->
    %% Format type_param tuple for dependent types
    io_lib:format("{type_param, ~p, ~s}", [Name, format_type(Value)]);
format_type({identifier_expr, Name, _Loc}) ->
    %% Format identifier expressions used in dependent types
    io_lib:format("{identifier_expr, ~p, undefined}", [Name]);
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
