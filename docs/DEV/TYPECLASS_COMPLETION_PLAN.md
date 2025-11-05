# Typeclass System Completion Plan

## Overview

This document outlines the implementation plan for the three remaining features needed to complete Cure's typeclass system:

1. **Higher-Kinded Type Checking** - Type system support for type constructors (F(A))
2. **Instance Dispatch Runtime** - Runtime resolution and caching of typeclass instances
3. **Module-Level Where Clauses** - Support for helper functions with typeclass constraints

## Current State

✅ **Complete:**
- Lexer support for `$` operators (`<$`, `$>`, `<*>`, `*>`, `<*`, `>>=`, `>>`)
- Parser support for operator function definitions (`def (op)(params)`)
- Typeclass and instance AST definitions
- Basic typeclass codegen (compiles to BEAM behaviour modules)
- Instance codegen (compiles to mangled function names)

⏳ **In Progress:**
- Higher-kinded type checking
- Instance dispatch
- Module-level where clauses

---

## Part 1: Higher-Kinded Type Checking

### Goal
Enable the type system to handle type constructors (types that take types as parameters), essential for Functor, Applicative, and Monad typeclasses.

### Current Implementation Status

The type system already has basic infrastructure:
- `#kind{}` record defined (line 370-379, cure_types.erl)
- `#type_constructor{}` record defined (line 381-388)
- `#higher_kinded_type{}` record defined (line 390-396)
- Exported functions: `create_kind/3`, `infer_kind/2`, `check_kind/3`, `unify_kinds/2`, etc.

**However**, these functions are not yet fully implemented for typeclass usage.

### Implementation Tasks

#### 1.1 Extend Kind System

**File: `src/types/cure_types.erl`**

Add kind representations for typeclass type constructors:

```erlang
%% Kind constructors
-define(KIND_TYPE, {kind, '*', [], '*', 0, undefined}).
-define(KIND_TYPE_TO_TYPE, {kind, '->', [?KIND_TYPE], ?KIND_TYPE, 1, undefined}).
-define(KIND_TYPE_TO_TYPE_TO_TYPE, {kind, '->', [?KIND_TYPE, ?KIND_TYPE], ?KIND_TYPE, 2, undefined}).
```

#### 1.2 Implement Kind Inference for Type Constructors

Extend `infer_kind/2` to handle:
- Simple types: `Int :: *`, `String :: *`
- Type constructors: `List :: * -> *`, `Map :: * -> * -> *`
- Higher-order: `Functor :: (* -> *) -> *`

```erlang
infer_kind({primitive_type, _Name}, _Env) ->
    {ok, ?KIND_TYPE};
infer_kind({dependent_type, Name, Params}, Env) ->
    % Look up constructor kind in environment
    case lookup_type_constructor(Name, Env) of
        {ok, #type_constructor{kind = Kind}} ->
            % Check if fully applied
            Expected = kind_arity(Kind),
            Actual = length(Params),
            if 
                Actual =:= Expected -> {ok, result_kind(Kind)};
                Actual < Expected -> {ok, partial_application_kind(Kind, Actual)};
                true -> {error, {too_many_type_args, Name, Expected, Actual}}
            end;
        not_found ->
            % Infer from usage
            infer_constructor_kind(Name, length(Params), Env)
    end.
```

#### 1.3 Add Kind Checking to Typeclass Definitions

When parsing a typeclass like `class Functor(F)`, verify that `F` has kind `* -> *`:

**File: `src/types/cure_typechecker.erl`**

```erlang
check_typeclass_def(#typeclass_def{name = Name, type_params = TypeParams, methods = Methods} = Def, Env) ->
    % Step 1: Infer kinds for type parameters
    TypeParamKinds = infer_typeclass_param_kinds(TypeParams, Methods, Env),
    
    % Step 2: Add type constructor to environment
    TypeConstructor = #type_constructor{
        name = Name,
        kind = build_typeclass_kind(TypeParamKinds),
        params = TypeParams,
        definition = undefined,
        constraints = Def#typeclass_def.constraints,
        location = Def#typeclass_def.location
    },
    EnvWithTC = add_type_constructor(TypeConstructor, Env),
    
    % Step 3: Check method signatures with HKT support
    check_typeclass_methods(Methods, TypeParams, TypeParamKinds, EnvWithTC).
```

#### 1.4 Kind Unification for Instance Resolution

When checking `instance Functor(List)`, verify kinds match:

```erlang
check_instance_kinds(InstanceDef, TypeclassInfo, Env) ->
    #instance_def{typeclass = TC, type_args = TypeArgs} = InstanceDef,
    
    % Get typeclass kind requirements
    TCKind = TypeclassInfo#typeclass_info.kind,
    
    % Infer kinds of type arguments
    TypeArgKinds = [infer_kind(Arg, Env) || Arg <- TypeArgs],
    
    % Unify with expected kinds
    case unify_kinds(TCKind, TypeArgKinds) of
        {ok, _Subst} -> ok;
        {error, Reason} -> {error, {kind_mismatch, TC, Reason}}
    end.
```

### Testing Strategy

Create test file: `test/typeclass_hkt_test.erl`

```erlang
test_functor_kind() ->
    % Functor(F) where F :: * -> *
    Env = cure_types:new_env(),
    {ok, FunctorKind} = cure_types:infer_kind({typeclass_type, 'Functor', [?KIND_TYPE_TO_TYPE]}, Env),
    ?assertEqual(?KIND_TYPE_TO_TYPE, FunctorKind).

test_list_functor_instance() ->
    % instance Functor(List)
    % List :: * -> * matches Functor requirement
    Env = cure_types:new_env(),
    ListKind = cure_types:infer_kind({type_constructor, 'List', [?KIND_TYPE]}, Env),
    ?assertEqual({ok, ?KIND_TYPE_TO_TYPE}, ListKind).
```

---

## Part 2: Instance Dispatch Runtime

### Goal
Implement efficient runtime resolution of typeclass instances with caching for performance.

### Architecture

```
Call Site                Instance Registry           Compiled Code
---------               ------------------          --------------
show(x)   --lookup-->   {Show, Int} -> show_Int_show
  |                          |                |
  v                          v                v
[cache]  <--register--  [instances map]   [BEAM functions]
```

### Implementation Tasks

#### 2.1 Instance Registry Module

**File: `src/runtime/cure_instance_registry.erl`**

```erlang
-module(cure_instance_registry).
-behaviour(gen_server).

%% API
-export([
    start_link/0,
    register_instance/3,
    lookup_instance/2,
    get_method/3,
    clear_cache/0
]).

%% Internal state
-record(state, {
    instances = #{} :: #{{atom(), [term()]} => instance_entry()},
    cache = #{} :: #{cache_key() => compiled_method()},
    index = #{} :: #{atom() => [instance_key()]}
}).

-record(instance_entry, {
    typeclass :: atom(),
    type_args :: [term()],
    methods :: #{atom() => compiled_method()},
    constraints :: [term()],
    priority :: integer()  % For overlapping instance resolution
}).

-type cache_key() :: {atom(), atom(), term()}.  % {Typeclass, Method, Type}
-type instance_key() :: {atom(), [term()]}.
-type compiled_method() :: {module(), atom(), arity()}.  % {Mod, Fun, Arity}
```

#### 2.2 Instance Registration at Module Load

**File: `src/codegen/cure_typeclass_codegen.erl`**

Extend compilation to generate registration calls:

```erlang
compile_instance(#instance_def{} = InstanceDef, State) ->
    % ... existing compilation ...
    
    % Generate module initialization function
    InitFunction = generate_instance_registration(InstanceDef, CompiledMethods),
    
    {ok, {instance, #{
        methods => CompiledMethods,
        init_function => InitFunction
    }}, NewState}.

generate_instance_registration(#instance_def{typeclass = TC, type_args = Args}, Methods) ->
    % Generate function that registers instance on module load:
    % -on_load(register_instance/0).
    % register_instance() ->
    %     cure_instance_registry:register_instance(
    %         'Show', 
    %         ['Int'],
    %         #{show => {?MODULE, show_Int_show, 1}}
    %     ).
    
    MethodMap = maps:from_list([
        {MethodName, {module_name, MangledName, Arity}}
        || {MethodName, MangledName, Arity} <- Methods
    ]),
    
    {on_load_function, register_instance, [
        {call, {remote, cure_instance_registry, register_instance}, [
            {atom, TC},
            {list, [{atom, A} || A <- Args]},
            {map, MethodMap}
        ]}
    ]}.
```

#### 2.3 Dispatch Function Generation

Create wrapper functions for method dispatch:

**File: `src/runtime/cure_typeclass_dispatch.erl`**

```erlang
-module(cure_typeclass_dispatch).
-export([dispatch/4, dispatch_cached/4]).

%% Dispatch typeclass method call
dispatch(Typeclass, Method, Receiver, Args) ->
    % Get receiver type at runtime
    ReceiverType = infer_runtime_type(Receiver),
    
    % Look up instance
    case cure_instance_registry:get_method(Typeclass, Method, ReceiverType) of
        {ok, {Mod, Fun, _Arity}} ->
            apply(Mod, Fun, [Receiver | Args]);
        {error, no_instance} ->
            error({no_instance, Typeclass, ReceiverType});
        {error, ambiguous} ->
            error({ambiguous_instance, Typeclass, ReceiverType})
    end.

%% Cached dispatch (for hot paths)
dispatch_cached(Typeclass, Method, Receiver, Args) ->
    ReceiverType = infer_runtime_type(Receiver),
    CacheKey = {Typeclass, Method, ReceiverType},
    
    case persistent_term:get(CacheKey, undefined) of
        undefined ->
            {Mod, Fun, Arity} = resolve_and_cache(Typeclass, Method, ReceiverType),
            persistent_term:put(CacheKey, {Mod, Fun, Arity}),
            apply(Mod, Fun, [Receiver | Args]);
        {Mod, Fun, _Arity} ->
            apply(Mod, Fun, [Receiver | Args])
    end.

%% Infer runtime type from Erlang value
infer_runtime_type(V) when is_integer(V) -> {primitive_type, 'Int'};
infer_runtime_type(V) when is_float(V) -> {primitive_type, 'Float'};
infer_runtime_type(V) when is_list(V) -> 
    case io_lib:printable_list(V) of
        true -> {primitive_type, 'String'};
        false -> {dependent_type, 'List', [infer_runtime_type(hd(V))]}
    end;
infer_runtime_type(V) when is_tuple(V) ->
    case element(1, V) of
        RecordName when is_atom(RecordName) ->
            {record_type, RecordName};
        _ ->
            {tuple_type, [infer_runtime_type(E) || E <- tuple_to_list(V)]}
    end.
```

#### 2.4 Overlapping Instance Resolution

Implement priority-based resolution for overlapping instances:

```erlang
resolve_instance(Typeclass, Type, Instances) ->
    % Filter matching instances
    Matches = [I || I <- Instances, instance_matches(I, Type)],
    
    case Matches of
        [] -> {error, no_instance};
        [Single] -> {ok, Single};
        Multiple ->
            % Sort by specificity (most specific first)
            Sorted = lists:sort(fun compare_instance_specificity/2, Multiple),
            case Sorted of
                [Most | _] -> {ok, Most};
                [] -> {error, no_instance}
            end
    end.

compare_instance_specificity(I1, I2) ->
    % More specific instances have higher priority:
    % 1. Concrete types > type variables
    % 2. More constraints > fewer constraints
    % 3. Explicit declaration order
    
    S1 = instance_specificity_score(I1),
    S2 = instance_specificity_score(I2),
    S1 > S2.
```

### Testing Strategy

Test file: `test/instance_dispatch_test.erl`

```erlang
test_basic_dispatch() ->
    % Register Show(Int) instance
    cure_instance_registry:register_instance('Show', ['Int'], #{
        show => {test_module, show_int, 1}
    }),
    
    % Dispatch show(42)
    Result = cure_typeclass_dispatch:dispatch('Show', show, 42, []),
    ?assertEqual("42", Result).

test_cached_dispatch() ->
    % First call caches
    R1 = cure_typeclass_dispatch:dispatch_cached('Show', show, 42, []),
    
    % Second call uses cache
    R2 = cure_typeclass_dispatch:dispatch_cached('Show', show, 99, []),
    
    ?assertEqual("42", R1),
    ?assertEqual("99", R2).
```

---

## Part 3: Module-Level Where Clauses

### Goal
Support helper functions with typeclass constraints at module level, enabling code like:

```haskell
-- Currently commented out in typeclass.cure
def sequence(xs: List(M(A))): M(List(A)) where Monad(M) = ...
```

### Implementation Tasks

#### 3.1 Parser Extension

**File: `src/parser/cure_parser.erl`**

Add support for module-level function definitions with where clauses:

```erlang
parse_module_level_function(State) ->
    % def function_name(params): return_type where Constraint = body
    
    {NameToken, State1} = expect(identifier, State),
    Name = get_token_value(NameToken),
    
    State2 = expect('(', State1),
    {Params, State3} = parse_param_list(State2),
    State4 = expect(')', State3),
    
    {ReturnType, State5} = parse_type_annotation(State4),
    
    % Check for where clause
    {WhereClause, State6} = 
        case current_token(State5) of
            {where, _, _} ->
                State5a = advance(State5),
                parse_where_clause(State5a);
            _ ->
                {undefined, State5}
        end,
    
    State7 = expect('=', State6),
    {Body, State8} = parse_expression(State7),
    
    FunctionDef = #function_def{
        name = Name,
        params = Params,
        return_type = ReturnType,
        where_clause = WhereClause,
        body = Body,
        location = get_location(NameToken)
    },
    
    {FunctionDef, State8}.

parse_where_clause(State) ->
    % Parse: where Monad(M), Show(A)
    {Constraints, StateN} = parse_constraint_list(State),
    {#where_clause{constraints = Constraints}, StateN}.
```

#### 3.2 Type Checking with Constraint Propagation

**File: `src/types/cure_typechecker.erl`**

```erlang
check_function_with_where_clause(#function_def{where_clause = Where} = FuncDef, Env) ->
    case Where of
        undefined ->
            % No constraints, check normally
            check_function_def(FuncDef, Env);
        #where_clause{constraints = Constraints} ->
            % Add constraints to environment
            EnvWithConstraints = add_typeclass_constraints(Constraints, Env),
            
            % Check function body with constraints available
            case check_function_def(FuncDef, EnvWithConstraints) of
                ok ->
                    % Verify all constraints are satisfiable
                    verify_constraints_satisfiable(Constraints, EnvWithConstraints);
                Error ->
                    Error
            end
    end.

verify_constraints_satisfiable(Constraints, Env) ->
    % For each constraint like Monad(M):
    % 1. Check that M is a type variable or type constructor
    % 2. Verify Monad typeclass exists
    % 3. Don't require concrete instance (polymorphic)
    
    lists:foldl(
        fun(#typeclass_constraint{typeclass = TC, type_args = Args}, ok) ->
            case cure_typeclass:lookup_typeclass(TC, Env) of
                {ok, _Info} ->
                    % Check kind compatibility
                    check_constraint_kinds(TC, Args, Env);
                not_found ->
                    {error, {unknown_typeclass, TC}}
            end;
           (_, Error) ->
            Error
        end,
        ok,
        Constraints
    ).
```

#### 3.3 Codegen for Constrained Functions

**File: `src/codegen/cure_codegen.erl`**

Functions with where clauses compile to functions that take "dictionary" parameters:

```erlang
compile_constrained_function(#function_def{where_clause = Where} = Func, State) ->
    #where_clause{constraints = Constraints} = Where,
    
    % Generate dictionary parameters for each constraint
    % where Monad(M) => add parameter: monad_M_dict
    DictParams = generate_constraint_dictionaries(Constraints),
    
    % Transform function body to use dictionaries
    TransformedBody = transform_constrained_calls(Func#function_def.body, DictParams),
    
    % Compile with additional dictionary parameters
    TransformedFunc = Func#function_def{
        params = Func#function_def.params ++ DictParams,
        body = TransformedBody
    },
    
    compile_function_impl(TransformedFunc, State).

generate_constraint_dictionaries(Constraints) ->
    [begin
        DictName = constraint_dict_name(TC, TypeArgs),
        #param{
            name = DictName,
            type = {typeclass_dict, TC, TypeArgs},
            location = Loc
        }
    end || #typeclass_constraint{typeclass = TC, type_args = TypeArgs, location = Loc} <- Constraints].

constraint_dict_name(Typeclass, [TypeArg | _]) ->
    TCStr = string:lowercase(atom_to_list(Typeclass)),
    TypeStr = type_to_dict_string(TypeArg),
    list_to_atom(TCStr ++ "_" ++ TypeStr ++ "_dict").
```

#### 3.4 Dictionary Passing at Call Sites

When calling a constrained function, pass appropriate dictionaries:

```erlang
compile_constrained_call(FuncName, Args, Constraints, Env, State) ->
    % Look up dictionaries for constraints
    Dicts = [resolve_dictionary(C, Env) || C <- Constraints],
    
    % Compile call with dictionary arguments
    AllArgs = Args ++ Dicts,
    compile_function_call(FuncName, AllArgs, State).

resolve_dictionary(#typeclass_constraint{typeclass = TC, type_args = TypeArgs}, Env) ->
    % Look up instance for (TC, TypeArgs)
    case cure_typeclass:lookup_instance(TC, TypeArgs, Env) of
        {ok, InstanceInfo} ->
            % Generate dictionary literal
            generate_instance_dictionary(TC, InstanceInfo);
        not_found ->
            % Look in constraint environment (polymorphic call)
            lookup_constraint_dict(TC, TypeArgs, Env)
    end.
```

### Testing Strategy

Test file: `test/where_clause_test.erl`

```erlang
test_simple_where_clause() ->
    % def twice(x: M(A)): M(A) where Monad(M) = bind(x, fn(a) => return(a))
    
    Code = <<"
        module test_where.
        
        def twice(x: M(A)): M(A) where Monad(M) =
            bind(x, fn(a) => return(a))
        end
    ">>,
    
    {ok, AST} = cure_parser:parse(Code),
    ?assertMatch(#module{functions = [#function_def{where_clause = #where_clause{}}]}, AST).

test_sequence_function() ->
    % def sequence(xs: List(M(A))): M(List(A)) where Monad(M)
    
    Code = <<"
        module test_sequence.
        
        def sequence(xs: List(M(A))): M(List(A)) where Monad(M) =
            match xs do
                [] => return([])
                [x | rest] =>
                    bind(x, fn(a) =>
                        bind(sequence(rest), fn(as) =>
                            return([a | as])
                        ))
                    )
            end
        end
    ">>,
    
    {ok, Compiled} = cure_compiler:compile_string(Code),
    ?assert(is_binary(Compiled)).
```

---

## Integration Plan

### Phase 1: Higher-Kinded Types (Week 1)
1. Implement kind system extensions
2. Add kind checking to typeclass definitions
3. Write tests for Functor, Applicative, Monad kinds
4. Update parser to validate kind compatibility

### Phase 2: Instance Dispatch (Week 2)
1. Implement instance registry gen_server
2. Add instance registration to codegen
3. Implement dispatch functions
4. Add caching with persistent_term
5. Test with Show, Eq, Ord instances

### Phase 3: Where Clauses (Week 3)
1. Extend parser for where clause syntax
2. Implement constraint propagation in type checker
3. Add dictionary passing to codegen
4. Enable module-level helper functions in typeclass.cure
5. Test with sequence, mapM, etc.

### Phase 4: Integration & Testing (Week 4)
1. Uncomment helper functions in lib/typeclass_spec/typeclass.cure
2. Write comprehensive integration tests
3. Performance benchmarking
4. Documentation updates
5. Example programs demonstrating all features

---

## Success Criteria

✅ **Higher-Kinded Types:**
- [ ] Functor(List), Functor(Maybe), Functor(Either) compile
- [ ] Kind errors detected for invalid instances (e.g., Functor(Int))
- [ ] Type inference works with higher-kinded type variables

✅ **Instance Dispatch:**
- [ ] Runtime method resolution works for all typeclasses
- [ ] Caching improves performance by >10x on hot paths
- [ ] Overlapping instance resolution is deterministic
- [ ] Instance registration happens automatically on module load

✅ **Where Clauses:**
- [ ] Module-level functions with constraints parse correctly
- [ ] Dictionary passing is invisible to user code
- [ ] Helper functions (sequence, mapM, etc.) work polymorphically
- [ ] Type checking validates constraint satisfaction

---

## Performance Targets

- Instance lookup: < 100ns (cached), < 1μs (uncached)
- Kind checking: < 10μs per typeclass definition
- Dictionary passing overhead: < 5% compared to direct calls
- Compilation time: < 10% increase for files using typeclasses

---

## Next Steps

1. Review this plan with the team
2. Set up tracking issues for each phase
3. Begin implementation of Phase 1 (Higher-Kinded Types)
4. Write failing tests before implementation
5. Iterate with code reviews after each phase

---

## References

- [Haskell Type Classes](https://wiki.haskell.org/Typeclassopedia)
- [Scala Implicits Resolution](https://docs.scala-lang.org/tour/implicit-parameters.html)
- [Rust Trait Objects](https://doc.rust-lang.org/book/ch17-02-trait-objects.html)
- [GHC Typeclass Implementation](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/type_classes.html)
