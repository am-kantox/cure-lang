-module(cure_typeclass_codegen).

%% Typeclass code generation for the Cure BEAM compiler
-export([
    compile_typeclass/2,
    compile_instance/2,
    process_derive_clause/3,
    generate_instance_function/4,
    generate_instance_registration/4
]).

-include("../parser/cure_ast.hrl").
-include("cure_codegen.hrl").

%% ============================================================================
%% Typeclass Compilation
%% ============================================================================

-doc """
Compiles a typeclass definition to BEAM code.

Typeclasses compile to Erlang behaviour modules with:
- behaviour_info/1 callback specification
- Default method implementations
- Method signature documentation

## Arguments
- `TypeclassDef` - Typeclass AST node
- `State` - Codegen state

## Returns
- `{ok, CompiledModule, NewState}` - Compiled typeclass module
- `{error, Reason}` - Compilation error
""".
-spec compile_typeclass(#typeclass_def{}, term()) ->
    {ok, term(), term()} | {error, term()}.
compile_typeclass(
    #typeclass_def{name = Name, methods = Methods, default_methods = DefaultMethods}, State
) ->
    % Typeclass compiles to a behaviour module with behaviour_info/1
    % and optional default method implementations

    % Extract method signatures for behaviour_info
    % Methods are #method_signature{} records
    MethodSpecs = [
        {Method#method_signature.name, length(Method#method_signature.params)}
     || Method <- Methods
    ],

    % Generate behaviour_info function as Erlang abstract form
    BehaviourInfoFunction = generate_behaviour_info_function(MethodSpecs),

    % Default methods come from the default_methods field as #function_def{} records
    % not from methods field (which contains #method_signature{} records)
    DefaultImpls =
        case DefaultMethods of
            undefined -> [];
            _ -> DefaultMethods
        end,

    % Compile default methods to actual BEAM functions
    case compile_default_methods(DefaultImpls, State) of
        {ok, CompiledDefaults, NewState} ->
            % Return typeclass as a compilable module structure
            TypeclassModule = #{
                name => Name,
                methods => MethodSpecs,
                behaviour_info_function => BehaviourInfoFunction,
                default_functions => CompiledDefaults
            },
            {ok, {typeclass, TypeclassModule}, NewState};
        {error, Reason} ->
            {error, {typeclass_compilation_failed, Name, Reason}}
    end.

%% ============================================================================
%% Instance Compilation
%% ============================================================================

-doc """
Compiles an instance definition to BEAM code.

Instances compile to regular Erlang functions with specialized naming:
- `show_Int/1` for Show(Int).show
- `eq_Point/2` for Eq(Point).==
- `compare_Person/2` for Ord(Person).compare

## Arguments
- `InstanceDef` - Instance AST node
- `State` - Codegen state

## Returns
- `{ok, CompiledFunctions, NewState}` - List of compiled functions
- `{error, Reason}` - Compilation error
""".
-spec compile_instance(#instance_def{}, term()) ->
    {ok, [term()], term()} | {error, term()}.
compile_instance(
    #instance_def{
        typeclass = TypeclassName,
        type_args = TypeArgs,
        methods = Methods
    },
    State
) ->
    % Extract the primary type (first type argument)
    PrimaryType = extract_primary_type(TypeArgs),

    % Compile each method with mangled name, threading state through
    case compile_instance_methods(TypeclassName, PrimaryType, Methods, State, []) of
        {ok, CompiledMethods, NewState} ->
            % Generate registration code and update state
            case
                generate_instance_registration(
                    TypeclassName, PrimaryType, CompiledMethods, NewState
                )
            of
                {ok, RegistrationInfo, UpdatedState} ->
                    % Return compiled methods and updated state with registration info
                    {ok, CompiledMethods, UpdatedState};
                {error, Reason} ->
                    % Log registration failure but continue (non-fatal)
                    cure_utils:debug("Instance registration failed for ~p(~p): ~p~n", [
                        TypeclassName, PrimaryType, Reason
                    ]),
                    {ok, CompiledMethods, NewState}
            end;
        {error, Reason} ->
            {error, Reason}
    end.

%% Compile instance methods with proper state threading
compile_instance_methods(_TypeclassName, _PrimaryType, [], State, Acc) ->
    {ok, lists:reverse(Acc), State};
compile_instance_methods(TypeclassName, PrimaryType, [Method | Rest], State, Acc) ->
    case compile_instance_method(TypeclassName, PrimaryType, Method, State) of
        {ok, CompiledFunc, NewState} ->
            % Properly thread the updated state through
            compile_instance_methods(TypeclassName, PrimaryType, Rest, NewState, [
                CompiledFunc | Acc
            ]);
        {error, Reason} ->
            {error, {instance_method_failed, Method#function_def.name, Reason}}
    end.

%% ============================================================================
%% Derive Clause Processing
%% ============================================================================

-doc """
Processes a derive clause and generates instances.

Called during record definition compilation to automatically generate
typeclass instances using the derive mechanism.

## Arguments
- `DeriveClause` - Derive clause AST node
- `RecordDef` - Record definition being derived for
- `State` - Codegen state

## Returns
- `{ok, GeneratedInstances, NewState}` - List of generated instance functions
- `{error, Reason}` - Derivation error
""".
-spec process_derive_clause(#derive_clause{}, #record_def{}, term()) ->
    {ok, [term()], term()} | {error, term()}.
process_derive_clause(
    #derive_clause{typeclasses = Typeclasses},
    RecordDef,
    State
) ->
    % For each typeclass in the derive list, generate an instance
    Results = lists:map(
        fun(TypeclassName) ->
            case cure_derive:derive_instance(TypeclassName, RecordDef, [], undefined) of
                {ok, InstanceDef} ->
                    % Compile the generated instance
                    compile_instance(InstanceDef, State);
                {error, Reason} ->
                    {error, {derive_failed, TypeclassName, Reason}}
            end
        end,
        Typeclasses
    ),

    % Collect all successfully generated functions
    case lists:partition(fun({Tag, _, _}) -> Tag =:= ok end, Results) of
        {OkResults, []} ->
            AllFunctions = lists:flatten([Funcs || {ok, Funcs, _} <- OkResults]),
            {ok, AllFunctions, State};
        {_, Errors} ->
            {error, {derive_compilation_failed, Errors}}
    end;
process_derive_clause(undefined, _RecordDef, State) ->
    % No derive clause - nothing to do
    {ok, [], State}.

%% ============================================================================
%% Helper Functions
%% ============================================================================

%% Generate behaviour_info/1 callback function
generate_behaviour_info_function(MethodSpecs) ->
    % Generate proper Erlang abstract form for behaviour_info/1
    Line = 1,
    MethodList = lists:map(
        fun({Name, Arity}) ->
            {tuple, Line, [{atom, Line, Name}, {integer, Line, Arity}]}
        end,
        MethodSpecs
    ),

    % Build the list of callbacks
    CallbacksList = lists:foldr(
        fun(Tuple, Acc) -> {cons, Line, Tuple, Acc} end,
        {nil, Line},
        MethodList
    ),

    {function, Line, behaviour_info, 1, [
        {clause, Line, [{atom, Line, callbacks}], [], [CallbacksList]},
        {clause, Line, [{var, Line, '_'}], [], [{atom, Line, undefined}]}
    ]}.

%% Compile default method implementations
compile_default_methods([], State) ->
    {ok, [], State};
compile_default_methods(Methods, State) ->
    % Compile each default method as a regular function
    Results = lists:map(
        fun(Method) ->
            % Use the main codegen module to compile the function
            case cure_codegen:compile_function_impl(Method, State) of
                {ok, CompiledFunc, NewState} ->
                    {ok, CompiledFunc, NewState};
                {error, Reason} ->
                    {error, {default_method_failed, Method#function_def.name, Reason}}
            end
        end,
        Methods
    ),

    % Check for errors
    case lists:partition(fun({Tag, _, _}) -> Tag =:= ok end, Results) of
        {OkResults, []} ->
            CompiledFuncs = [Func || {ok, Func, _} <- OkResults],
            % Take the state from the last successful compilation
            FinalState =
                case OkResults of
                    [] -> State;
                    _ -> element(3, lists:last(OkResults))
                end,
            {ok, CompiledFuncs, FinalState};
        {_, Errors} ->
            {error, {default_methods_failed, Errors}}
    end.

%% Extract primary type from type arguments
extract_primary_type([]) ->
    'Unknown';
extract_primary_type([#primitive_type{name = Name} | _]) ->
    Name;
extract_primary_type([#dependent_type{name = Name} | _]) ->
    Name;
extract_primary_type([_ | Rest]) ->
    extract_primary_type(Rest).

%% Compile a single instance method with name mangling
compile_instance_method(TypeclassName, TypeName, Method, State) ->
    % Generate mangled name: typeclass_type_method
    % e.g., Show_Int_show, Eq_Point_eq
    MethodName = Method#function_def.name,
    MangledName = mangle_instance_method_name(TypeclassName, TypeName, MethodName),

    % Create a new function with the mangled name
    MangledMethod = Method#function_def{name = MangledName},

    % Compile the method to actual BEAM code
    case cure_codegen:compile_function_impl(MangledMethod, State) of
        {ok, CompiledFunc, NewState} ->
            % Return the compiled function with metadata and new state
            % CompiledFunc is typically {function, FuncMap}
            InstanceFunction =
                case CompiledFunc of
                    {function, FuncMap} when is_map(FuncMap) ->
                        {function,
                            maps:merge(FuncMap, #{
                                original_name => MethodName,
                                mangled_name => MangledName,
                                typeclass => TypeclassName,
                                type => TypeName,
                                is_instance_method => true
                            })};
                    Other ->
                        Other
                end,
            {ok, InstanceFunction, NewState};
        {error, Reason} ->
            {error, {instance_method_compilation_failed, MangledName, Reason}}
    end.

%% Mangle instance method name for uniqueness
mangle_instance_method_name(TypeclassName, TypeName, MethodName) ->
    % Convert to list format for name construction
    TCStr = atom_to_list(TypeclassName),
    TypeStr = atom_to_list(TypeName),
    MethodStr = atom_to_list(MethodName),

    % Create mangled name: TC_Type_method
    MangledStr = TCStr ++ "_" ++ TypeStr ++ "_" ++ MethodStr,
    list_to_atom(MangledStr).

%% ============================================================================
%% Instance Function Generation
%% ============================================================================

-doc """
Generates a callable function for a typeclass method dispatch.

Creates wrapper functions that dispatch to the correct instance:
```erlang
show(X) when is_integer(X) -> show_Int(X);
show(X) when is_float(X) -> show_Float(X);
show(X) when is_list(X) -> show_List(X).
```

## Arguments
- `TypeclassName` - Name of the typeclass
- `MethodName` - Name of the method
- `Instances` - List of registered instances
- `State` - Codegen state

## Returns
- `{ok, DispatchFunction}` - Generated dispatch function
- `{error, Reason}` - Generation error
""".
-spec generate_instance_function(atom(), atom(), [term()], term()) ->
    {ok, term()} | {error, term()}.
generate_instance_function(TypeclassName, MethodName, Instances, _State) ->
    % Generate function clauses for each instance
    Clauses = lists:map(
        fun(#{type := TypeName, arity := Arity}) ->
            generate_dispatch_clause(TypeclassName, TypeName, MethodName, Arity)
        end,
        Instances
    ),

    % Add a catch-all clause that throws an error
    CatchAllClause = generate_catchall_clause(TypeclassName, MethodName),

    AllClauses = Clauses ++ [CatchAllClause],

    DispatchFunction = #{
        name => MethodName,
        typeclass => TypeclassName,
        clauses => AllClauses
    },

    {ok, DispatchFunction}.

%% Generate a dispatch clause for a specific type
generate_dispatch_clause(TypeclassName, TypeName, MethodName, Arity) ->
    % Generate pattern for the type
    Pattern = generate_type_pattern(TypeName, Arity),

    % Generate guard if needed
    Guard = generate_type_guard(TypeName, Arity),

    % Generate call to mangled instance method
    MangledName = mangle_instance_method_name(TypeclassName, TypeName, MethodName),
    Body = {call, {atom, MangledName}, generate_var_list(Arity)},

    #{
        pattern => Pattern,
        guard => Guard,
        body => Body
    }.

%% Generate catch-all clause for unknown types
generate_catchall_clause(TypeclassName, MethodName) ->
    #{
        pattern => [{var, '_'}],
        guard => [],
        body =>
            {error,
                {tuple, [
                    {atom, no_instance},
                    {atom, TypeclassName},
                    {atom, MethodName}
                ]}}
    }.

%% Generate type pattern for dispatch
generate_type_pattern('Int', 1) ->
    [{var, 'X'}];
generate_type_pattern('Float', 1) ->
    [{var, 'X'}];
generate_type_pattern('String', 1) ->
    [{var, 'X'}];
generate_type_pattern(_Type, Arity) ->
    generate_var_list(Arity).

%% Generate type guard for dispatch
generate_type_guard('Int', 1) ->
    [{call, {atom, is_integer}, [{var, 'X'}]}];
generate_type_guard('Float', 1) ->
    [{call, {atom, is_float}, [{var, 'X'}]}];
generate_type_guard('String', 1) ->
    [{call, {atom, is_list}, [{var, 'X'}]}];
generate_type_guard(_Type, _Arity) ->
    [].

%% Generate list of variables for function calls
generate_var_list(0) ->
    [];
generate_var_list(N) ->
    [
        {var, list_to_atom("X" ++ integer_to_list(I))}
     || I <- lists:seq(1, N)
    ].

%% ============================================================================
%% Instance Registration Code Generation
%% ============================================================================

-doc """
Generates instance registration code for automatic registration on module load.

This creates an -on_load attribute and registration function that automatically
registers the instance with cure_instance_registry when the module is loaded.

## Arguments
- `TypeclassName` - Name of the typeclass (e.g., 'Show', 'Eq')
- `TypeName` - Name of the type (e.g., 'Int', 'List')
- `CompiledMethods` - List of compiled method functions
- `State` - Codegen state

## Returns
- Registration code structure with on_load hook
""".
-spec generate_instance_registration(atom(), atom(), [term()], term()) ->
    {ok, term(), term()} | {error, term()}.
generate_instance_registration(TypeclassName, TypeName, CompiledMethods, State) ->
    try
        % Extract method names and arities from compiled methods
        MethodMap = build_method_map(TypeclassName, TypeName, CompiledMethods),

        % Generate the registration function
        Line = 1,
        ModuleName = get_current_module_name(),

        % Build the method map as an Erlang term
        MethodMapExpr = generate_method_map_expr(MethodMap, Line),

        % Build the type expression
        TypeExpr = generate_type_expr(TypeName, Line),

        % Generate the registration function body:
        % register_instance() ->
        %     cure_instance_registry:register_instance(
        %         'TypeclassName',
        %         {primitive_type, 'TypeName'},
        %         #{method1 => {module, function, arity}, ...}
        %     ).
        RegistrationBody = {
            call,
            {remote, Line, {atom, Line, cure_instance_registry}, {atom, Line, register_instance}},
            [
                {atom, Line, TypeclassName},
                TypeExpr,
                MethodMapExpr
            ]
        },

        RegistrationFunction = {
            function,
            Line,
            register_instance,
            0,
            [{clause, Line, [], [], [RegistrationBody]}]
        },

        % Generate -on_load attribute
        OnLoadAttr = {
            attribute,
            Line,
            on_load,
            {register_instance, 0}
        },

        % Update state with instance registry information
        RegistrationInfo = #{
            type => instance_registration,
            on_load_attr => OnLoadAttr,
            registration_function => RegistrationFunction,
            typeclass => TypeclassName,
            type_name => TypeName,
            module => ModuleName
        },

        % Update instance_registry in state
        CurrentRegistry = maps:get(instance_registry, State, #{}),
        UpdatedRegistry = update_instance_registry(
            CurrentRegistry, TypeclassName, TypeName, ModuleName
        ),
        UpdatedState = State#codegen_state{instance_registry = UpdatedRegistry},

        {ok, RegistrationInfo, UpdatedState}
    catch
        Class:Error:Stack ->
            cure_utils:debug("Instance registration error for ~p(~p): ~p:~p~n", [
                TypeclassName, TypeName, Class, Error
            ]),
            case os:getenv("CURE_DEBUG") of
                "1" -> cure_utils:debug("Stack: ~p~n", [Stack]);
                _ -> ok
            end,
            {error, {registration_failed, TypeclassName, TypeName, Error}}
    end.

%% Build method map from compiled methods
build_method_map(_TypeclassName, _TypeName, CompiledMethods) ->
    lists:foldl(
        fun(CompiledMethod, Acc) ->
            case CompiledMethod of
                {function, #{original_name := OrigName, mangled_name := MangledName}} ->
                    % Get the arity from the mangled function
                    % For now, assume arity 1 for most methods
                    Arity = 1,
                    ModuleName = get_current_module_name(),
                    maps:put(OrigName, {ModuleName, MangledName, Arity}, Acc);
                _ ->
                    % Skip non-function entries
                    Acc
            end
        end,
        #{},
        CompiledMethods
    ).

%% Generate method map expression as Erlang abstract form
generate_method_map_expr(MethodMap, Line) ->
    % Generate map literal: #{method1 => {module, func, arity}, ...}
    Assocs = maps:fold(
        fun(MethodName, {Module, Function, Arity}, Acc) ->
            Key = {atom, Line, MethodName},
            Value =
                {tuple, Line, [
                    {atom, Line, Module},
                    {atom, Line, Function},
                    {integer, Line, Arity}
                ]},
            [{map_field_assoc, Line, Key, Value} | Acc]
        end,
        [],
        MethodMap
    ),
    {map, Line, Assocs}.

%% Generate type expression as Erlang abstract form
generate_type_expr(TypeName, Line) ->
    % For now, generate simple primitive type: {primitive_type, 'TypeName'}
    {tuple, Line, [
        {atom, Line, primitive_type},
        {atom, Line, TypeName}
    ]}.

%% Update instance registry with new instance entry
update_instance_registry(CurrentRegistry, TypeclassName, TypeName, ModuleName) ->
    % Ensure typeclass key exists in registry
    TypeclassMap = maps:get(TypeclassName, CurrentRegistry, #{}),
    % Add type entry mapping to module
    UpdatedTypeMap = maps:put(TypeName, {module, ModuleName}, TypeclassMap),
    % Update registry
    maps:put(TypeclassName, UpdatedTypeMap, CurrentRegistry).

%% Get current module name from state or use placeholder
get_current_module_name() ->
    % This should be extracted from the codegen state
    % For now, use a placeholder that will be replaced during actual compilation
    'cure_generated_module'.
