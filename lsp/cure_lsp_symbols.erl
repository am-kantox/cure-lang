-module(cure_lsp_symbols).
-export([new/0, add_module/3, get_symbol/2, find_references/2, get_completions/2]).
-export([get_module_exports/2, get_functions/2]).

-include("../src/parser/cure_ast.hrl").

-record(symbol_table, {
    % ModuleName -> ModuleInfo
    modules = #{} :: map(),
    % {Module, Function, Arity} -> FunctionInfo
    functions = #{} :: map(),
    % {Module, TypeName} -> TypeInfo
    types = #{} :: map(),
    % {Module, FSMName} -> FSMInfo
    fsms = #{} :: map(),
    % Symbol -> [Location]
    references = #{} :: map()
}).

-record(module_info, {
    name :: atom(),
    uri :: binary(),
    exports = [] :: list(),
    functions = [] :: list(),
    types = [] :: list(),
    fsms = [] :: list()
}).

-record(function_info, {
    module :: atom(),
    name :: atom(),
    arity :: integer(),
    line :: integer(),
    type_sig :: term(),
    doc :: binary()
}).

-record(fsm_info, {
    module :: atom(),
    name :: atom(),
    states :: list(),
    line :: integer(),
    doc :: binary()
}).

%% Create new symbol table
new() ->
    #symbol_table{}.

%% Add module to symbol table
add_module(SymbolTable, Uri, #module_def{name = ModName, exports = Exports, items = Items}) ->
    % Separate functions and FSMs from items
    Functions = [F || F <- Items, is_record(F, function_def)],
    FSMs = [F || F <- Items, is_record(F, fsm_def)],

    ModInfo = #module_info{
        name = ModName,
        uri = Uri,
        exports = Exports,
        functions = Functions,
        fsms = FSMs
    },

    % Add module
    NewModules = maps:put(ModName, ModInfo, SymbolTable#symbol_table.modules),

    % Add functions
    FuncMap = lists:foldl(
        fun(FuncDef, Acc) ->
            add_function_to_map(ModName, FuncDef, Uri, Acc)
        end,
        SymbolTable#symbol_table.functions,
        Functions
    ),

    % Add FSMs
    FsmMap = lists:foldl(
        fun(FsmDef, Acc) ->
            add_fsm_to_map(ModName, FsmDef, Uri, Acc)
        end,
        SymbolTable#symbol_table.fsms,
        FSMs
    ),

    SymbolTable#symbol_table{
        modules = NewModules,
        functions = FuncMap,
        fsms = FsmMap
    };
add_module(SymbolTable, _Uri, _AST) ->
    SymbolTable.

add_function_to_map(
    Module, #function_def{name = Name, params = Params, location = Location}, _Uri, Map
) ->
    Arity = length(Params),
    Line =
        case Location of
            #location{line = L} -> L;
            _ -> 0
        end,
    Key = {Module, Name, Arity},
    FuncInfo = #function_info{
        module = Module,
        name = Name,
        arity = Arity,
        line = Line,
        type_sig = undefined,
        doc = <<>>
    },
    maps:put(Key, FuncInfo, Map);
add_function_to_map(_Module, _, _Uri, Map) ->
    Map.

add_fsm_to_map(Module, #fsm_def{name = Name, states = States, location = Location}, _Uri, Map) ->
    Line =
        case Location of
            #location{line = L} -> L;
            _ -> 0
        end,
    % Extract state names from state_def records
    StateNames =
        case States of
            List when is_list(List) ->
                [S || S <- List, is_atom(S)];
            _ ->
                []
        end,
    Key = {Module, Name},
    FsmInfo = #fsm_info{
        module = Module,
        name = Name,
        states = StateNames,
        line = Line,
        doc = <<>>
    },
    maps:put(Key, FsmInfo, Map);
add_fsm_to_map(_Module, _, _Uri, Map) ->
    Map.

%% Get symbol information
get_symbol(
    #symbol_table{functions = Functions}, {module, Module, function, Name, Arity}
) ->
    case maps:get({Module, Name, Arity}, Functions, undefined) of
        undefined -> {error, not_found};
        FuncInfo -> {ok, {function, FuncInfo}}
    end;
get_symbol(#symbol_table{fsms = FSMs}, {module, Module, fsm, Name}) ->
    case maps:get({Module, Name}, FSMs, undefined) of
        undefined -> {error, not_found};
        FsmInfo -> {ok, {fsm, FsmInfo}}
    end;
get_symbol(#symbol_table{modules = Modules}, {module, ModName}) ->
    case maps:get(ModName, Modules, undefined) of
        undefined -> {error, not_found};
        ModInfo -> {ok, {module, ModInfo}}
    end;
get_symbol(_, _) ->
    {error, invalid_symbol}.

%% Find all references to a symbol
find_references(#symbol_table{references = Refs}, Symbol) ->
    maps:get(Symbol, Refs, []).

%% Get completion suggestions
get_completions(#symbol_table{functions = Functions, fsms = FSMs, modules = Modules}, Prefix) ->
    PrefixBin = ensure_binary(Prefix),

    % Function completions
    FuncCompletions = maps:fold(
        fun({_Mod, Name, Arity}, FuncInfo, Acc) ->
            NameBin = atom_to_binary(Name, utf8),
            case binary:match(NameBin, PrefixBin) of
                nomatch -> Acc;
                _ -> [make_function_completion(Name, Arity, FuncInfo) | Acc]
            end
        end,
        [],
        Functions
    ),

    % FSM completions
    FsmCompletions = maps:fold(
        fun({_Mod, Name}, FsmInfo, Acc) ->
            NameBin = atom_to_binary(Name, utf8),
            case binary:match(NameBin, PrefixBin) of
                nomatch -> Acc;
                _ -> [make_fsm_completion(Name, FsmInfo) | Acc]
            end
        end,
        [],
        FSMs
    ),

    % Module completions
    ModCompletions = maps:fold(
        fun(Name, ModInfo, Acc) ->
            NameBin = atom_to_binary(Name, utf8),
            case binary:match(NameBin, PrefixBin) of
                nomatch -> Acc;
                _ -> [make_module_completion(Name, ModInfo) | Acc]
            end
        end,
        [],
        Modules
    ),

    FuncCompletions ++ FsmCompletions ++ ModCompletions.

%% Get module exports
get_module_exports(#symbol_table{modules = Modules}, ModuleName) ->
    case maps:get(ModuleName, Modules, undefined) of
        undefined -> [];
        #module_info{exports = Exports} -> Exports
    end.

%% Get all functions in a module
get_functions(#symbol_table{functions = Functions}, ModuleName) ->
    maps:fold(
        fun({Mod, Name, Arity}, FuncInfo, Acc) ->
            case Mod of
                ModuleName -> [{Name, Arity, FuncInfo} | Acc];
                _ -> Acc
            end
        end,
        [],
        Functions
    ).

%% Helper functions
ensure_binary(Atom) when is_atom(Atom) ->
    atom_to_binary(Atom, utf8);
ensure_binary(List) when is_list(List) ->
    list_to_binary(List);
ensure_binary(Bin) when is_binary(Bin) ->
    Bin.

make_function_completion(Name, Arity, #function_info{doc = Doc}) ->
    #{
        label => iolist_to_binary(io_lib:format("~s/~p", [Name, Arity])),
        % Function
        kind => 3,
        detail => iolist_to_binary(io_lib:format("function ~s/~p", [Name, Arity])),
        documentation => Doc,
        insertText => atom_to_binary(Name, utf8)
    }.

make_fsm_completion(Name, #fsm_info{states = States, doc = Doc}) ->
    #{
        label => atom_to_binary(Name, utf8),
        % Class (closest to FSM)
        kind => 7,
        detail => iolist_to_binary(io_lib:format("fsm ~s with states: ~p", [Name, States])),
        documentation => Doc,
        insertText => atom_to_binary(Name, utf8)
    }.

make_module_completion(Name, #module_info{}) ->
    #{
        label => atom_to_binary(Name, utf8),
        % Module
        kind => 9,
        detail => iolist_to_binary(io_lib:format("module ~s", [Name])),
        insertText => atom_to_binary(Name, utf8)
    }.
