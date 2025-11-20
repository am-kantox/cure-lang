-module(cure_lsp_symbols).
-export([new/0, add_module/3, get_symbol/2, find_references/2, get_completions/2]).
-export([get_module_exports/2, get_functions/2, get_traits/2, get_typeclasses/2]).

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
    % {Module, TraitName} -> TraitInfo
    traits = #{} :: map(),
    % {Module, TypeclassName} -> TypeclassInfo
    typeclasses = #{} :: map(),
    % {Module, TraitName, ForType} -> TraitImplInfo
    trait_impls = #{} :: map(),
    % {Module, TypeclassName, ForType} -> InstanceInfo
    instances = #{} :: map(),
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

-record(trait_info, {
    module :: atom(),
    name :: atom(),
    type_params :: list(),
    methods :: list(),
    line :: integer(),
    doc :: binary()
}).

-record(trait_impl_info, {
    module :: atom(),
    trait_name :: atom(),
    for_type :: term(),
    methods :: list(),
    line :: integer(),
    doc :: binary()
}).

-record(instance_info, {
    module :: atom(),
    typeclass :: atom(),
    type_args :: list(),
    methods :: list(),
    line :: integer(),
    doc :: binary()
}).

-record(lsp_typeclass_info, {
    module :: atom(),
    name :: atom(),
    type_params :: list(),
    methods :: list(),
    line :: integer(),
    doc :: binary()
}).

%% Create new symbol table
new() ->
    #symbol_table{}.

%% Add module to symbol table
add_module(SymbolTable, Uri, #module_def{name = ModName, exports = Exports, items = Items}) ->
    % Separate items by type
    Functions = [F || F <- Items, is_record(F, function_def)],
    FSMs = [F || F <- Items, is_record(F, fsm_def)],
    Traits = [T || T <- Items, is_record(T, trait_def)],
    Typeclasses = [TC || TC <- Items, is_record(TC, typeclass_def)],
    TraitImpls = [TI || TI <- Items, is_record(TI, trait_impl)],
    Instances = [I || I <- Items, is_record(I, instance_def)],

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

    % Add traits
    TraitMap = lists:foldl(
        fun(TraitDef, Acc) ->
            add_trait_to_map(ModName, TraitDef, Uri, Acc)
        end,
        SymbolTable#symbol_table.traits,
        Traits
    ),

    % Add typeclasses
    TypeclassMap = lists:foldl(
        fun(TypeclassDef, Acc) ->
            add_typeclass_to_map(ModName, TypeclassDef, Uri, Acc)
        end,
        SymbolTable#symbol_table.typeclasses,
        Typeclasses
    ),

    % Add trait implementations
    TraitImplMap = lists:foldl(
        fun(TraitImpl, Acc) ->
            add_trait_impl_to_map(ModName, TraitImpl, Uri, Acc)
        end,
        SymbolTable#symbol_table.trait_impls,
        TraitImpls
    ),

    % Add typeclass instances
    InstanceMap = lists:foldl(
        fun(Instance, Acc) ->
            add_instance_to_map(ModName, Instance, Uri, Acc)
        end,
        SymbolTable#symbol_table.instances,
        Instances
    ),

    SymbolTable#symbol_table{
        modules = NewModules,
        functions = FuncMap,
        fsms = FsmMap,
        traits = TraitMap,
        typeclasses = TypeclassMap,
        trait_impls = TraitImplMap,
        instances = InstanceMap
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

add_trait_to_map(
    Module,
    #trait_def{name = Name, type_params = TypeParams, methods = Methods, location = Location},
    _Uri,
    Map
) ->
    Line =
        case Location of
            #location{line = L} -> L;
            _ -> 0
        end,
    Key = {Module, Name},
    TraitInfo = #trait_info{
        module = Module,
        name = Name,
        type_params = TypeParams,
        methods = Methods,
        line = Line,
        doc = <<>>
    },
    maps:put(Key, TraitInfo, Map);
add_trait_to_map(_Module, _, _Uri, Map) ->
    Map.

add_typeclass_to_map(
    Module,
    #typeclass_def{name = Name, type_params = TypeParams, methods = Methods, location = Location},
    _Uri,
    Map
) ->
    Line =
        case Location of
            #location{line = L} -> L;
            _ -> 0
        end,
    Key = {Module, Name},
    TypeclassInfo = #lsp_typeclass_info{
        module = Module,
        name = Name,
        type_params = TypeParams,
        methods = Methods,
        line = Line,
        doc = <<>>
    },
    maps:put(Key, TypeclassInfo, Map);
add_typeclass_to_map(_Module, _, _Uri, Map) ->
    Map.

add_trait_impl_to_map(
    Module,
    #trait_impl{trait_name = TraitName, for_type = ForType, methods = Methods, location = Location},
    _Uri,
    Map
) ->
    Line =
        case Location of
            #location{line = L} -> L;
            _ -> 0
        end,
    Key = {Module, TraitName, ForType},
    TraitImplInfo = #trait_impl_info{
        module = Module,
        trait_name = TraitName,
        for_type = ForType,
        methods = Methods,
        line = Line,
        doc = <<>>
    },
    maps:put(Key, TraitImplInfo, Map);
add_trait_impl_to_map(_Module, _, _Uri, Map) ->
    Map.

add_instance_to_map(
    Module,
    #instance_def{
        typeclass = Typeclass, type_args = TypeArgs, methods = Methods, location = Location
    },
    _Uri,
    Map
) ->
    Line =
        case Location of
            #location{line = L} -> L;
            _ -> 0
        end,
    Key = {Module, Typeclass, TypeArgs},
    InstanceInfo = #instance_info{
        module = Module,
        typeclass = Typeclass,
        type_args = TypeArgs,
        methods = Methods,
        line = Line,
        doc = <<>>
    },
    maps:put(Key, InstanceInfo, Map);
add_instance_to_map(_Module, _, _Uri, Map) ->
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
get_symbol(#symbol_table{traits = Traits}, {module, Module, trait, Name}) ->
    case maps:get({Module, Name}, Traits, undefined) of
        undefined -> {error, not_found};
        TraitInfo -> {ok, {trait, TraitInfo}}
    end;
get_symbol(#symbol_table{typeclasses = Typeclasses}, {module, Module, typeclass, Name}) ->
    case maps:get({Module, Name}, Typeclasses, undefined) of
        undefined -> {error, not_found};
        TypeclassInfo -> {ok, {typeclass, TypeclassInfo}}
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
get_completions(
    #symbol_table{
        functions = Functions,
        fsms = FSMs,
        modules = Modules,
        traits = Traits,
        typeclasses = Typeclasses
    },
    Prefix
) ->
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

    % Trait completions
    TraitCompletions = maps:fold(
        fun({_Mod, Name}, TraitInfo, Acc) ->
            NameBin = atom_to_binary(Name, utf8),
            case binary:match(NameBin, PrefixBin) of
                nomatch -> Acc;
                _ -> [make_trait_completion(Name, TraitInfo) | Acc]
            end
        end,
        [],
        Traits
    ),

    % Typeclass completions
    TypeclassCompletions = maps:fold(
        fun({_Mod, Name}, TypeclassInfo, Acc) ->
            NameBin = atom_to_binary(Name, utf8),
            case binary:match(NameBin, PrefixBin) of
                nomatch -> Acc;
                _ -> [make_typeclass_completion(Name, TypeclassInfo) | Acc]
            end
        end,
        [],
        Typeclasses
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

    FuncCompletions ++ FsmCompletions ++ TraitCompletions ++ TypeclassCompletions ++ ModCompletions.

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

%% Get all traits in a module
get_traits(#symbol_table{traits = Traits}, ModuleName) ->
    maps:fold(
        fun({Mod, Name}, TraitInfo, Acc) ->
            case Mod of
                ModuleName -> [{Name, TraitInfo} | Acc];
                _ -> Acc
            end
        end,
        [],
        Traits
    ).

%% Get all typeclasses in a module
get_typeclasses(#symbol_table{typeclasses = Typeclasses}, ModuleName) ->
    maps:fold(
        fun({Mod, Name}, TypeclassInfo, Acc) ->
            case Mod of
                ModuleName -> [{Name, TypeclassInfo} | Acc];
                _ -> Acc
            end
        end,
        [],
        Typeclasses
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

make_trait_completion(Name, #trait_info{type_params = TypeParams, methods = Methods, doc = Doc}) ->
    MethodCount = length(Methods),
    TypeParamsStr = format_type_params_list(TypeParams),
    #{
        label => atom_to_binary(Name, utf8),
        % Interface
        kind => 8,
        detail => iolist_to_binary(
            io_lib:format("trait ~s~s (~p methods)", [Name, TypeParamsStr, MethodCount])
        ),
        documentation => Doc,
        insertText => atom_to_binary(Name, utf8)
    }.

make_typeclass_completion(Name, #lsp_typeclass_info{
    type_params = TypeParams, methods = Methods, doc = Doc
}) ->
    MethodCount = length(Methods),
    TypeParamsStr = format_type_params_list(TypeParams),
    #{
        label => atom_to_binary(Name, utf8),
        % Interface
        kind => 8,
        detail => iolist_to_binary(
            io_lib:format("typeclass ~s~s (~p methods)", [Name, TypeParamsStr, MethodCount])
        ),
        documentation => Doc,
        insertText => atom_to_binary(Name, utf8)
    }.

format_type_params_list([]) ->
    <<"">>;
format_type_params_list(TypeParams) when is_list(TypeParams) ->
    ParamStrs = [atom_to_binary(TP, utf8) || TP <- TypeParams, is_atom(TP)],
    case ParamStrs of
        [] -> <<"">>;
        _ -> iolist_to_binary([<<"(">>, lists:join(<<", ">>, ParamStrs), <<")">>])
    end;
format_type_params_list(_) ->
    <<"">>.
