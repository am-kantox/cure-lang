%% Record Type Inference Tests
%% Comprehensive tests for record type inference, type checking, and type safety

-module(record_type_inference_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").

%% Test runner
run() ->
    cure_utils:debug("~n=== Record Type Inference Test Suite ===~n"),

    Tests = [
        {test_simple_record_type_inference, "Simple Record Type Inference"},
        {test_parametric_record_types, "Parametric Record Types"},
        {test_record_field_type_checking, "Record Field Type Checking"},
        {test_record_construction_type_safety, "Record Construction Type Safety"},
        {test_record_pattern_type_inference, "Record Pattern Type Inference"},
        {test_nested_record_types, "Nested Record Types"},
        {test_record_type_polymorphism, "Record Type Polymorphism"},
        {test_record_type_constraints, "Record Type Constraints"},
        {test_record_type_unification, "Record Type Unification"},
        {test_record_type_errors, "Record Type Errors"}
    ],

    Results = lists:map(
        fun({TestFun, TestName}) ->
            cure_utils:debug("Testing ~s... ", [TestName]),
            try
                case apply(?MODULE, TestFun, []) of
                    ok ->
                        cure_utils:debug("PASSED~n"),
                        {TestName, passed};
                    {error, Reason} ->
                        cure_utils:debug("FAILED: ~p~n", [Reason]),
                        {TestName, {failed, Reason}}
                end
            catch
                Error:ErrReason:Stacktrace ->
                    cure_utils:debug("ERROR: ~p:~p~n", [Error, ErrReason]),
                    cure_utils:debug("Stacktrace: ~p~n", [Stacktrace]),
                    {TestName, {error, {Error, ErrReason}}}
            end
        end,
        Tests
    ),

    Passed = length([R || {_, passed} = R <- Results]),
    Total = length(Results),

    cure_utils:debug("~nResults: ~p/~p tests passed~n", [Passed, Total]),

    case Passed of
        Total ->
            cure_utils:debug("All record type inference tests passed!~n"),
            ok;
        _ ->
            cure_utils:debug("Some tests failed.~n"),
            {failed, Results}
    end.

%% ===== SIMPLE RECORD TYPE INFERENCE =====

test_simple_record_type_inference() ->
    Code = <<
        "record Person { name: String, age: Int }\n"
        "        \n"
        "        def alice(): Person =\n"
        "          Person{name: \"Alice\", age: 25}\n"
        "        \n"
        "        def get_name(p: Person): String =\n"
        "          case p of\n"
        "            Person{name: n} -> n\n"
        "          end\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(3, length(AST)),
    [RecordDef, AliceFunc, GetNameFunc] = AST,

    % Check record definition has correct field types
    ?assertMatch(#record_def{name = 'Person'}, RecordDef),
    #record_def{fields = Fields} = RecordDef,
    ?assertEqual(2, length(Fields)),

    [NameField, AgeField] = Fields,
    ?assertMatch(
        #record_field_def{
            name = name,
            type = #primitive_type{name = 'String'}
        },
        NameField
    ),

    ?assertMatch(
        #record_field_def{
            name = age,
            type = #primitive_type{name = 'Int'}
        },
        AgeField
    ),

    % Check function return types match record type
    ?assertMatch(
        #function_def{
            name = alice,
            return_type = #primitive_type{name = 'Person'}
        },
        AliceFunc
    ),

    ?assertMatch(
        #function_def{
            name = get_name,
            return_type = #primitive_type{name = 'String'}
        },
        GetNameFunc
    ),

    ok.

%% ===== PARAMETRIC RECORD TYPES =====

test_parametric_record_types() ->
    Code = <<
        "record Option(T) { value: T, is_some: Bool }\n"
        "        record Pair(A, B) { first: A, second: B }\n"
        "        \n"
        "        def some_int(x: Int): Option(Int) =\n"
        "          Option{value: x, is_some: true}\n"
        "        \n"
        "        def make_pair(a: String, b: Float): Pair(String, Float) =\n"
        "          Pair{first: a, second: b}\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(4, length(AST)),
    [OptionDef, PairDef, SomeIntFunc, MakePairFunc] = AST,

    % Check parametric record definitions
    ?assertMatch(
        #record_def{
            name = 'Option',
            type_params = ['T']
        },
        OptionDef
    ),

    ?assertMatch(
        #record_def{
            name = 'Pair',
            type_params = ['A', 'B']
        },
        PairDef
    ),

    % Check that functions use correct parametric types
    ?assertMatch(#function_def{name = some_int}, SomeIntFunc),
    ?assertMatch(#function_def{name = make_pair}, MakePairFunc),

    ok.

%% ===== RECORD FIELD TYPE CHECKING =====

test_record_field_type_checking() ->
    % This test verifies that field types are correctly parsed and structured
    Code = <<
        "record Complex { \n"
        "          id: Int, \n"
        "          name: String, \n"
        "          active: Bool,\n"
        "          score: Float,\n"
        "          tags: List(String),\n"
        "          metadata: Option(String)\n"
        "        }\n"
        "        \n"
        "        def create_complex(): Complex =\n"
        "          Complex{\n"
        "            id: 42,\n"
        "            name: \"test\",\n"
        "            active: true,\n"
        "            score: 3.14,\n"
        "            tags: [\"important\", \"test\"],\n"
        "            metadata: Some(\"extra info\")\n"
        "          }\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(2, length(AST)),
    [RecordDef, CreateFunc] = AST,

    % Check record definition has all fields with correct types
    ?assertMatch(#record_def{name = 'Complex'}, RecordDef),
    #record_def{fields = Fields} = RecordDef,
    ?assertEqual(6, length(Fields)),

    % Verify each field type
    [IdField, NameField, ActiveField, ScoreField, TagsField, MetadataField] = Fields,

    ?assertMatch(
        #record_field_def{
            name = id,
            type = #primitive_type{name = 'Int'}
        },
        IdField
    ),

    ?assertMatch(
        #record_field_def{
            name = name,
            type = #primitive_type{name = 'String'}
        },
        NameField
    ),

    ?assertMatch(
        #record_field_def{
            name = active,
            type = #primitive_type{name = 'Bool'}
        },
        ActiveField
    ),

    ?assertMatch(
        #record_field_def{
            name = score,
            type = #primitive_type{name = 'Float'}
        },
        ScoreField
    ),

    % Complex types like List(String) and Option(String) should be parsed correctly
    ?assertMatch(#record_field_def{name = tags}, TagsField),
    ?assertMatch(#record_field_def{name = metadata}, MetadataField),

    ok.

%% ===== RECORD CONSTRUCTION TYPE SAFETY =====

test_record_construction_type_safety() ->
    Code = <<
        "record User { id: Int, email: String }\n"
        "        \n"
        "        def valid_user(): User =\n"
        "          User{id: 123, email: \"user@example.com\"}\n"
        "        \n"
        "        def construct_with_variables(): User =\n"
        "          let user_id = 456\n"
        "          let user_email = \"another@example.com\"\n"
        "          User{id: user_id, email: user_email}\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(3, length(AST)),
    [UserDef, ValidUserFunc, ConstructFunc] = AST,

    % Check record construction expressions
    ?assertMatch(#record_def{name = 'User'}, UserDef),

    % Check that both functions return User type
    ?assertMatch(
        #function_def{
            name = valid_user,
            return_type = #primitive_type{name = 'User'}
        },
        ValidUserFunc
    ),

    ?assertMatch(
        #function_def{
            name = construct_with_variables,
            return_type = #primitive_type{name = 'User'}
        },
        ConstructFunc
    ),

    % Check record construction expressions in function bodies
    ValidUserBody = ValidUserFunc#function_def.body,
    ?assertMatch(#record_expr{name = 'User'}, ValidUserBody),

    ConstructBody = ConstructFunc#function_def.body,
    ?assertMatch(#let_expr{}, ConstructBody),

    ok.

%% ===== RECORD PATTERN TYPE INFERENCE =====

test_record_pattern_type_inference() ->
    Code = <<
        "record Point { x: Float, y: Float }\n"
        "        record Rectangle { top_left: Point, bottom_right: Point }\n"
        "        \n"
        "        def area(rect: Rectangle): Float =\n"
        "          case rect of\n"
        "            Rectangle{top_left: Point{x: x1, y: y1}, bottom_right: Point{x: x2, y: y2}} ->\n"
        "              (x2 - x1) * (y2 - y1)\n"
        "            _ -> 0.0\n"
        "          end\n"
        "        \n"
        "        def center_x(rect: Rectangle): Float =\n"
        "          match rect do\n"
        "            Rectangle{top_left: Point{x: x1}, bottom_right: Point{x: x2}} ->\n"
        "              (x1 + x2) / 2.0\n"
        "          end\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(4, length(AST)),
    [PointDef, RectDef, AreaFunc, CenterXFunc] = AST,

    % Check record definitions
    ?assertMatch(#record_def{name = 'Point'}, PointDef),
    ?assertMatch(#record_def{name = 'Rectangle'}, RectDef),

    % Check functions with complex nested patterns
    ?assertMatch(#function_def{name = area}, AreaFunc),
    ?assertMatch(#function_def{name = center_x}, CenterXFunc),

    % Check that pattern matching expressions are structured correctly
    AreaBody = AreaFunc#function_def.body,
    ?assertMatch(#match_expr{}, AreaBody),

    CenterXBody = CenterXFunc#function_def.body,
    ?assertMatch(#match_expr{}, CenterXBody),

    ok.

%% ===== NESTED RECORD TYPES =====

test_nested_record_types() ->
    Code = <<
        "record Address { street: String, city: String, country: String }\n"
        "        record Contact { email: String, phone: String }\n"
        "        record Person { name: String, address: Address, contact: Contact }\n"
        "        \n"
        "        def get_email(person: Person): String =\n"
        "          case person of\n"
        "            Person{contact: Contact{email: e}} -> e\n"
        "            _ -> \"no-email\"\n"
        "          end\n"
        "        \n"
        "        def lives_in_city(person: Person, target_city: String): Bool =\n"
        "          match person do\n"
        "            Person{address: Address{city: c}} when c == target_city -> true\n"
        "            _ -> false\n"
        "          end\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(5, length(AST)),
    [AddressDef, ContactDef, PersonDef, GetEmailFunc, LivesInCityFunc] = AST,

    % Check nested record structure
    ?assertMatch(#record_def{name = 'Address'}, AddressDef),
    ?assertMatch(#record_def{name = 'Contact'}, ContactDef),
    ?assertMatch(#record_def{name = 'Person'}, PersonDef),

    % Check that Person record has Address and Contact field types
    #record_def{fields = PersonFields} = PersonDef,
    ?assertEqual(3, length(PersonFields)),

    [NameField, AddressField, ContactField] = PersonFields,
    ?assertMatch(
        #record_field_def{
            name = name,
            type = #primitive_type{name = 'String'}
        },
        NameField
    ),

    ?assertMatch(
        #record_field_def{
            name = address,
            type = #primitive_type{name = 'Address'}
        },
        AddressField
    ),

    ?assertMatch(
        #record_field_def{
            name = contact,
            type = #primitive_type{name = 'Contact'}
        },
        ContactField
    ),

    ok.

%% ===== RECORD TYPE POLYMORPHISM =====

test_record_type_polymorphism() ->
    Code = <<
        "record Container(T) { value: T, count: Int }\n"
        "        \n"
        "        def int_container(x: Int): Container(Int) =\n"
        "          Container{value: x, count: 1}\n"
        "        \n"
        "        def string_container(s: String): Container(String) =\n"
        "          Container{value: s, count: 1}\n"
        "        \n"
        "        def get_value(container: Container(T)): T =\n"
        "          case container of\n"
        "            Container{value: v} -> v\n"
        "          end\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(4, length(AST)),
    [ContainerDef, IntContainerFunc, StringContainerFunc, GetValueFunc] = AST,

    % Check parametric record definition
    ?assertMatch(
        #record_def{
            name = 'Container',
            type_params = ['T']
        },
        ContainerDef
    ),

    % Check that functions use correct instantiated types
    ?assertMatch(#function_def{name = int_container}, IntContainerFunc),
    ?assertMatch(#function_def{name = string_container}, StringContainerFunc),
    ?assertMatch(#function_def{name = get_value}, GetValueFunc),

    ok.

%% ===== RECORD TYPE CONSTRAINTS =====

test_record_type_constraints() ->
    Code = <<
        "record ValidatedEmail { email: String } where email =~ /^[\\w.-]+@[\\w.-]+\\.[a-zA-Z]{2,}$/\n"
        "        record BoundedNumber(T) { value: T } where T: Numeric\n"
        "        \n"
        "        def create_email(email_str: String): ValidatedEmail =\n"
        "          ValidatedEmail{email: email_str}\n"
        "        \n"
        "        def create_bounded_int(x: Int): BoundedNumber(Int) =\n"
        "          BoundedNumber{value: x}\n"
        "        "
    >>,

    % Note: This test is primarily for parsing constraints, actual constraint checking
    % would be implemented in the type checker
    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    % Check that we can parse records with constraints
    ?assertEqual(4, length(AST)),
    [EmailDef, NumberDef, CreateEmailFunc, CreateBoundedFunc] = AST,

    ?assertMatch(#record_def{name = 'ValidatedEmail'}, EmailDef),
    ?assertMatch(#record_def{name = 'BoundedNumber'}, NumberDef),
    ?assertMatch(#function_def{name = create_email}, CreateEmailFunc),
    ?assertMatch(#function_def{name = create_bounded_int}, CreateBoundedFunc),

    ok.

%% ===== RECORD TYPE UNIFICATION =====

test_record_type_unification() ->
    Code = <<
        "record Coord { x: Float, y: Float }\n"
        "        \n"
        "        def process_coord(coord: Coord): Float =\n"
        "          let Coord{x: x_val, y: y_val} = coord\n"
        "          x_val + y_val\n"
        "        \n"
        "        def update_coord(coord: Coord, new_x: Float): Coord =\n"
        "          case coord of\n"
        "            Coord{y: y_val} -> Coord{x: new_x, y: y_val}\n"
        "          end\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(3, length(AST)),
    [CoordDef, ProcessFunc, UpdateFunc] = AST,

    % Check record definition
    ?assertMatch(#record_def{name = 'Coord'}, CoordDef),

    % Check functions that demonstrate type unification
    ?assertMatch(#function_def{name = process_coord}, ProcessFunc),
    ?assertMatch(#function_def{name = update_coord}, UpdateFunc),

    % Check that let bindings with record patterns work
    ProcessBody = ProcessFunc#function_def.body,
    ?assertMatch(#let_expr{}, ProcessBody),

    % Check that case expressions with record patterns work
    UpdateBody = UpdateFunc#function_def.body,
    ?assertMatch(#match_expr{}, UpdateBody),

    ok.

%% ===== RECORD TYPE ERRORS =====

test_record_type_errors() ->
    % Test cases that should be detected as type errors (this test mainly checks parsing)
    Code = <<
        "record TypedRecord { id: Int, name: String }\n"
        "        \n"
        "        def potential_type_error(): TypedRecord =\n"
        "          % This would be a type error if type checking were fully implemented\n"
        "          TypedRecord{id: \"not an int\", name: 42}\n"
        "        \n"
        "        def missing_field_error(): TypedRecord =\n"
        "          % This would be a type error - missing required field\n"
        "          TypedRecord{id: 1}\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    % The code should parse successfully even with type errors
    % (actual type error detection would be in the type checker, not parser)
    ?assertEqual(3, length(AST)),
    [RecordDef, ErrorFunc1, ErrorFunc2] = AST,

    ?assertMatch(#record_def{name = 'TypedRecord'}, RecordDef),
    ?assertMatch(#function_def{name = potential_type_error}, ErrorFunc1),
    ?assertMatch(#function_def{name = missing_field_error}, ErrorFunc2),

    % Check that record construction expressions are parsed even with wrong types
    ErrorBody1 = ErrorFunc1#function_def.body,
    ?assertMatch(#record_expr{name = 'TypedRecord'}, ErrorBody1),

    ErrorBody2 = ErrorFunc2#function_def.body,
    ?assertMatch(#record_expr{name = 'TypedRecord'}, ErrorBody2),

    ok.
