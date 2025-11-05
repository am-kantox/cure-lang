-module(types_hkt_test).
-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").

%% Test suite for Higher-Kinded Types (HKT) in Cure's type system
%%
%% Tests:
%% 1. Kind inference for primitive types and type constructors
%% 2. Kind checking for typeclass definitions
%% 3. Instance kind verification
%% 4. Kind unification

%% ============================================================================
%% Basic Kind Inference Tests
%% ============================================================================

kind_inference_primitive_type_test() ->
    % Primitive types like Int, String have kind *
    Env = cure_types:new_env(),

    % Int :: *
    {ok, IntKind} = cure_types:infer_kind({primitive_type, 'Int'}, Env),
    ?assertEqual({kind, star, [], star, 0, undefined}, IntKind),

    % String :: *
    {ok, StringKind} = cure_types:infer_kind({primitive_type, 'String'}, Env),
    ?assertEqual({kind, star, [], star, 0, undefined}, StringKind),

    % Bool :: *
    {ok, BoolKind} = cure_types:infer_kind({primitive_type, 'Bool'}, Env),
    ?assertEqual({kind, star, [], star, 0, undefined}, BoolKind).

kind_inference_list_constructor_test() ->
    % List is a type constructor: List :: * -> *
    Env = cure_types:new_env(),

    % Register List as a type constructor
    ListConstructor = #type_constructor{
        name = 'List',
        kind =
            {kind, '->', [{kind, star, [], star, 0, undefined}],
                {kind, star, [], star, 0, undefined}, 1, undefined},
        params = ['T'],
        definition = undefined,
        constraints = [],
        location = undefined
    },
    EnvWithList = cure_types:add_type_constructor(ListConstructor, Env),

    % List :: * -> *
    {ok, ListKind} = cure_types:infer_kind({type_constructor, 'List'}, EnvWithList),
    ?assertMatch({kind, '->', _, _, 1, _}, ListKind).

kind_inference_fully_applied_list_test() ->
    % List(Int) has kind * (fully applied)
    Env = cure_types:new_env(),

    % Register List constructor
    ListConstructor = #type_constructor{
        name = 'List',
        kind =
            {kind, '->', [{kind, star, [], star, 0, undefined}],
                {kind, star, [], star, 0, undefined}, 1, undefined},
        params = ['T'],
        definition = undefined,
        constraints = [],
        location = undefined
    },
    EnvWithList = cure_types:add_type_constructor(ListConstructor, Env),

    % List(Int) :: *
    {ok, AppliedKind} = cure_types:infer_kind(
        {dependent_type, 'List', [#type_param{value = {primitive_type, 'Int'}}]},
        EnvWithList
    ),
    ?assertEqual({kind, star, [], star, 0, undefined}, AppliedKind).

kind_inference_maybe_constructor_test() ->
    % Maybe :: * -> *
    Env = cure_types:new_env(),

    MaybeConstructor = #type_constructor{
        name = 'Maybe',
        kind =
            {kind, '->', [{kind, star, [], star, 0, undefined}],
                {kind, star, [], star, 0, undefined}, 1, undefined},
        params = ['T'],
        definition = undefined,
        constraints = [],
        location = undefined
    },
    EnvWithMaybe = cure_types:add_type_constructor(MaybeConstructor, Env),

    {ok, MaybeKind} = cure_types:infer_kind({type_constructor, 'Maybe'}, EnvWithMaybe),
    ?assertMatch({kind, '->', _, _, 1, _}, MaybeKind).

kind_inference_map_constructor_test() ->
    % Map :: * -> * -> *
    Env = cure_types:new_env(),

    KindStar = {kind, star, [], star, 0, undefined},
    MapConstructor = #type_constructor{
        name = 'Map',
        kind = {kind, '->', [KindStar, KindStar], KindStar, 2, undefined},
        params = ['K', 'V'],
        definition = undefined,
        constraints = [],
        location = undefined
    },
    EnvWithMap = cure_types:add_type_constructor(MapConstructor, Env),

    {ok, MapKind} = cure_types:infer_kind({type_constructor, 'Map'}, EnvWithMap),
    ?assertMatch({kind, '->', _, _, 2, _}, MapKind).

%% ============================================================================
%% Kind Checking for Typeclasses
%% ============================================================================

typeclass_functor_kind_test() ->
    % class Functor(F) where F :: * -> *
    Env = cure_types:new_env(),

    FunctorDef = #typeclass_def{
        name = 'Functor',
        type_params = ['F'],
        constraints = [],
        methods = [
            #method_signature{
                name = map,
                params = [
                    #param{name = f, type = {function_type, ['A'], 'B'}, location = undefined},
                    #param{
                        name = fa,
                        type = {dependent_type, 'F', [#type_param{value = {primitive_type, 'A'}}]},
                        location = undefined
                    }
                ],
                return_type = {dependent_type, 'F', [#type_param{value = {primitive_type, 'B'}}]},
                location = undefined
            }
        ],
        default_methods = [],
        location = undefined
    },

    % Check typeclass definition and infer F :: * -> *
    {ok, TypeclassInfo, _EnvWithTC} = cure_types:check_typeclass_def(FunctorDef, Env),

    ?assertEqual('Functor', TypeclassInfo#typeclass_info.name),
    ?assertMatch({kind, '->', _, _, 1, _}, TypeclassInfo#typeclass_info.kind).

typeclass_monad_kind_test() ->
    % class Monad(M) where M :: * -> *
    Env = cure_types:new_env(),

    MonadDef = #typeclass_def{
        name = 'Monad',
        type_params = ['M'],
        constraints = [],
        methods = [
            #method_signature{
                name = return,
                params = [#param{name = a, type = 'A', location = undefined}],
                return_type = {dependent_type, 'M', [#type_param{value = {primitive_type, 'A'}}]},
                location = undefined
            },
            #method_signature{
                name = bind,
                params = [
                    #param{
                        name = ma,
                        type = {dependent_type, 'M', [#type_param{value = {primitive_type, 'A'}}]},
                        location = undefined
                    },
                    #param{
                        name = f,
                        type =
                            {function_type, ['A'],
                                {dependent_type, 'M', [#type_param{value = {primitive_type, 'B'}}]}},
                        location = undefined
                    }
                ],
                return_type = {dependent_type, 'M', [#type_param{value = {primitive_type, 'B'}}]},
                location = undefined
            }
        ],
        default_methods = [],
        location = undefined
    },

    {ok, TypeclassInfo, _EnvWithTC} = cure_types:check_typeclass_def(MonadDef, Env),

    ?assertEqual('Monad', TypeclassInfo#typeclass_info.name),
    ?assertMatch({kind, '->', _, _, 1, _}, TypeclassInfo#typeclass_info.kind).

%% ============================================================================
%% Instance Kind Checking
%% ============================================================================

instance_functor_list_valid_test() ->
    % instance Functor(List) - Valid: List :: * -> * matches Functor requirement
    Env = cure_types:new_env(),

    % Register List constructor
    KindStar = {kind, star, [], star, 0, undefined},
    ListConstructor = #type_constructor{
        name = 'List',
        kind = {kind, '->', [KindStar], KindStar, 1, undefined},
        params = ['T'],
        definition = undefined,
        constraints = [],
        location = undefined
    },
    EnvWithList = cure_types:add_type_constructor(ListConstructor, Env),

    % Register Functor typeclass
    FunctorInfo = #typeclass_info{
        name = 'Functor',
        type_params = ['F'],
        superclasses = [],
        methods = #{},
        default_impls = #{},
        kind = {kind, '->', [KindStar], KindStar, 1, undefined}
    },
    EnvWithFunctor = cure_types:add_typeclass_info(FunctorInfo, EnvWithList),

    % instance Functor(List)
    InstanceDef = #instance_def{
        typeclass = 'Functor',
        type_args = [{type_constructor, 'List'}],
        constraints = [],
        methods = [],
        location = undefined
    },

    % Should succeed - kinds match
    ?assertEqual(ok, cure_types:check_instance_kinds(InstanceDef, FunctorInfo, EnvWithFunctor)).

instance_functor_int_invalid_test() ->
    % instance Functor(Int) - Invalid: Int :: *, but Functor requires * -> *
    Env = cure_types:new_env(),

    KindStar = {kind, star, [], star, 0, undefined},

    % Register Functor typeclass
    FunctorInfo = #typeclass_info{
        name = 'Functor',
        type_params = ['F'],
        superclasses = [],
        methods = #{},
        default_impls = #{},
        kind = {kind, '->', [KindStar], KindStar, 1, undefined}
    },
    EnvWithFunctor = cure_types:add_typeclass_info(FunctorInfo, Env),

    % instance Functor(Int) - should fail
    InstanceDef = #instance_def{
        typeclass = 'Functor',
        type_args = [{primitive_type, 'Int'}],
        constraints = [],
        methods = [],
        location = undefined
    },

    % Should fail - Int has kind * but Functor needs * -> *
    ?assertMatch(
        {error, {kind_mismatch, 'Functor', _}},
        cure_types:check_instance_kinds(InstanceDef, FunctorInfo, EnvWithFunctor)
    ).

instance_functor_maybe_valid_test() ->
    % instance Functor(Maybe) - Valid: Maybe :: * -> *
    Env = cure_types:new_env(),

    KindStar = {kind, star, [], star, 0, undefined},

    % Register Maybe constructor
    MaybeConstructor = #type_constructor{
        name = 'Maybe',
        kind = {kind, '->', [KindStar], KindStar, 1, undefined},
        params = ['T'],
        definition = undefined,
        constraints = [],
        location = undefined
    },
    EnvWithMaybe = cure_types:add_type_constructor(MaybeConstructor, Env),

    % Register Functor typeclass
    FunctorInfo = #typeclass_info{
        name = 'Functor',
        type_params = ['F'],
        superclasses = [],
        methods = #{},
        default_impls = #{},
        kind = {kind, '->', [KindStar], KindStar, 1, undefined}
    },
    EnvWithFunctor = cure_types:add_typeclass_info(FunctorInfo, EnvWithMaybe),

    % instance Functor(Maybe)
    InstanceDef = #instance_def{
        typeclass = 'Functor',
        type_args = [{type_constructor, 'Maybe'}],
        constraints = [],
        methods = [],
        location = undefined
    },

    ?assertEqual(ok, cure_types:check_instance_kinds(InstanceDef, FunctorInfo, EnvWithFunctor)).

%% ============================================================================
%% Kind Unification Tests
%% ============================================================================

kind_unification_equal_test() ->
    % * unifies with *
    Kind1 = {kind, star, [], star, 0, undefined},
    Kind2 = {kind, star, [], star, 0, undefined},

    {ok, _Subst} = cure_types:unify_kinds(Kind1, Kind2).

kind_unification_constructor_test() ->
    % (* -> *) unifies with (* -> *)
    KindStar = {kind, star, [], star, 0, undefined},
    Kind1 = {kind, '->', [KindStar], KindStar, 1, undefined},
    Kind2 = {kind, '->', [KindStar], KindStar, 1, undefined},

    {ok, _Subst} = cure_types:unify_kinds(Kind1, Kind2).

kind_unification_mismatch_test() ->
    % * does NOT unify with (* -> *)
    Kind1 = {kind, star, [], star, 0, undefined},
    Kind2 =
        {kind, '->', [{kind, star, [], star, 0, undefined}], {kind, star, [], star, 0, undefined},
            1, undefined},

    ?assertMatch({error, _}, cure_types:unify_kinds(Kind1, Kind2)).

%% ============================================================================
%% Helper Function Tests
%% ============================================================================

kind_arity_test() ->
    KindStar = {kind, star, [], star, 0, undefined},
    ?assertEqual(0, cure_types:kind_arity(KindStar)),

    Kind1 = {kind, '->', [KindStar], KindStar, 1, undefined},
    ?assertEqual(1, cure_types:kind_arity(Kind1)),

    Kind2 = {kind, '->', [KindStar, KindStar], KindStar, 2, undefined},
    ?assertEqual(2, cure_types:kind_arity(Kind2)).

result_kind_test() ->
    KindStar = {kind, star, [], star, 0, undefined},

    % * -> * results in *
    Kind1 = {kind, '->', [KindStar], KindStar, 1, undefined},
    ?assertEqual(KindStar, cure_types:result_kind(Kind1)),

    % * itself results in *
    ?assertEqual(KindStar, cure_types:result_kind(KindStar)).

%% ============================================================================
%% Integration Tests with Typeclass Environment
%% ============================================================================

full_functor_list_integration_test() ->
    % Complete test: Define Functor, register List, create instance
    Env = cure_types:new_env(),

    % 1. Register List type constructor
    KindStar = {kind, star, [], star, 0, undefined},
    ListConstructor = #type_constructor{
        name = 'List',
        kind = {kind, '->', [KindStar], KindStar, 1, undefined},
        params = ['T'],
        definition = undefined,
        constraints = [],
        location = undefined
    },
    Env1 = cure_types:add_type_constructor(ListConstructor, Env),

    % 2. Define Functor typeclass
    FunctorDef = #typeclass_def{
        name = 'Functor',
        type_params = ['F'],
        constraints = [],
        methods = [
            #method_signature{
                name = map,
                params = [
                    #param{name = f, type = {function_type, ['A'], 'B'}, location = undefined},
                    #param{
                        name = fa,
                        type = {dependent_type, 'F', [#type_param{value = {primitive_type, 'A'}}]},
                        location = undefined
                    }
                ],
                return_type = {dependent_type, 'F', [#type_param{value = {primitive_type, 'B'}}]},
                location = undefined
            }
        ],
        default_methods = [],
        location = undefined
    },

    {ok, FunctorInfo, Env2} = cure_types:check_typeclass_def(FunctorDef, Env1),

    % 3. Create instance Functor(List)
    InstanceDef = #instance_def{
        typeclass = 'Functor',
        type_args = [{type_constructor, 'List'}],
        constraints = [],
        methods = [],
        location = undefined
    },

    % 4. Verify instance kinds
    ?assertEqual(ok, cure_types:check_instance_kinds(InstanceDef, FunctorInfo, Env2)),

    % 5. Register instance
    {ok, _Env3} = cure_typeclass:register_instance(
        InstanceDef,
        cure_typeclass:new_env()
    ).
