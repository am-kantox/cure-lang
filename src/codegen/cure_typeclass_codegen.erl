-module(cure_typeclass_codegen).

%% Typeclass code generation for the Cure BEAM compiler
-export([
    compile_typeclass/2,
    compile_instance/2,
    process_derive_clause/3,
    generate_instance_function/4
]).

-include("../parser/cure_ast.hrl").

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
compile_typeclass(#typeclass_def{name = Name, methods = Methods}, State) ->
    % Typeclass compiles to a behaviour module
    % For now, we'll compile it as documentation/metadata
    % Full implementation would generate a module with behaviour_info/1

    % Extract method signatures for behaviour_info
    MethodSpecs = [
        {Method#function_def.name, length(Method#function_def.params)}
     || Method <- Methods
    ],

    % Generate behaviour_info function
    BehaviourInfo = generate_behaviour_info(MethodSpecs),

    % Generate default implementations if any
    DefaultImpls = [
        Method
     || Method <- Methods, Method#function_def.body =/= undefined
    ],

    CompiledDefaults = compile_default_methods(DefaultImpls, State),

    % Return metadata about the typeclass
    TypeclassMetadata = #{
        name => Name,
        methods => MethodSpecs,
        behaviour_info => BehaviourInfo,
        defaults => CompiledDefaults
    },

    {ok, {typeclass, TypeclassMetadata}, State}.

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

    % Compile each method with mangled name
    CompiledMethods = lists:map(
        fun(Method) ->
            compile_instance_method(TypeclassName, PrimaryType, Method, State)
        end,
        Methods
    ),

    % Check for errors
    case lists:partition(fun({Tag, _}) -> Tag =:= ok end, CompiledMethods) of
        {OkResults, []} ->
            Functions = [Func || {ok, Func} <- OkResults],
            {ok, Functions, State};
        {_, Errors} ->
            {error, {instance_compilation_failed, Errors}}
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

%% Generate behaviour_info/1 callback for typeclass
generate_behaviour_info(MethodSpecs) ->
    % In Erlang, behaviour_info(callbacks) returns [{FunctionName, Arity}]
    {function, behaviour_info, 1, [
        {clause,
            [
                {atom, callbacks}
            ],
            [], [
                {list, [
                    {tuple, [{atom, Name}, {integer, Arity}]}
                 || {Name, Arity} <- MethodSpecs
                ]}
            ]},
        {clause,
            [
                {var, '_'}
            ],
            [], [
                {atom, undefined}
            ]}
    ]}.

%% Compile default method implementations
compile_default_methods(Methods, State) ->
    % Default methods need to be compiled as regular functions
    % For now, return metadata
    [
        #{
            name => Method#function_def.name,
            params => Method#function_def.params,
            has_default => true
        }
     || Method <- Methods
    ].

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

    % For now, return function metadata
    % Full implementation would call cure_codegen:compile_function_impl
    {ok, #{
        original_name => MethodName,
        mangled_name => MangledName,
        typeclass => TypeclassName,
        type => TypeName,
        arity => length(Method#function_def.params),
        method => MangledMethod
    }}.

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
