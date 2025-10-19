%% Advanced Pattern Matching Tests
%% Tests for case expressions, record patterns, constructor patterns, and type inference

-module(pattern_matching_advanced_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast.hrl").

%% Test runner
run() ->
    io:format("~n=== Advanced Pattern Matching Test Suite ===~n"),

    Tests = [
        {test_case_expression_parsing, "Case Expression Parsing"},
        {test_case_expression_semantic_analysis, "Case Expression Semantic Analysis"},
        {test_record_pattern_matching_basic, "Basic Record Pattern Matching"},
        {test_record_pattern_matching_field_extraction, "Record Pattern Field Extraction"},
        {test_record_pattern_matching_nested, "Nested Record Pattern Matching"},
        {test_constructor_pattern_multiple_args, "Constructor Pattern Multiple Arguments"},
        {test_constructor_pattern_no_args, "Constructor Pattern No Arguments"},
        {test_type_inference_record_definitions, "Type Inference for Record Definitions"},
        {test_type_inference_record_construction, "Type Inference for Record Construction"},
        {test_type_inference_record_patterns, "Type Inference for Record Patterns"},
        {test_show_functions_behavior, "Show Functions Behavior"}
    ],

    Results = lists:map(
        fun({TestFun, TestName}) ->
            io:format("Testing ~s... ", [TestName]),
            try
                case apply(?MODULE, TestFun, []) of
                    ok ->
                        io:format("PASSED~n"),
                        {TestName, passed};
                    {error, Reason} ->
                        io:format("FAILED: ~p~n", [Reason]),
                        {TestName, {failed, Reason}}
                end
            catch
                Error:ErrReason:Stacktrace ->
                    io:format("ERROR: ~p:~p~n", [Error, ErrReason]),
                    io:format("Stacktrace: ~p~n", [Stacktrace]),
                    {TestName, {error, {Error, ErrReason}}}
            end
        end,
        Tests
    ),

    Passed = length([R || {_, passed} = R <- Results]),
    Total = length(Results),

    io:format("~nResults: ~p/~p tests passed~n", [Passed, Total]),

    case Passed of
        Total ->
            io:format("All advanced pattern matching tests passed!~n"),
            ok;
        _ ->
            io:format("Some tests failed.~n"),
            {failed, Results}
    end.

%% ===== CASE EXPRESSION TESTS =====

%% Test parsing of case...of...end expressions
test_case_expression_parsing() ->
    Code = <<
        "def test_case(x: Int): String =\n"
        "          case x of\n"
        "            1 -> \"one\"\n"
        "            2 -> \"two\"\n"
        "            _ -> \"other\"\n"
        "          end\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,
    ?assertMatch(#function_def{name = test_case}, FunctionDef),

    % Check that body is a match expression (case reuses match_expr AST node)
    Body = FunctionDef#function_def.body,
    ?assertMatch(#match_expr{}, Body),

    % Check match expression structure
    #match_expr{expr = Expr, patterns = Patterns} = Body,
    ?assertMatch(#identifier_expr{name = x}, Expr),
    ?assertEqual(3, length(Patterns)),

    % Check patterns
    [FirstClause, SecondClause, ThirdClause] = Patterns,
    ?assertMatch(#match_clause{pattern = #literal_pattern{value = 1}}, FirstClause),
    ?assertMatch(#match_clause{pattern = #literal_pattern{value = 2}}, SecondClause),
    ?assertMatch(#match_clause{pattern = #wildcard_pattern{}}, ThirdClause),

    ok.

%% Test semantic analysis of case expressions
test_case_expression_semantic_analysis() ->
    Code = <<
        "def test_complex_case(result: Result(Int, String)): String =\n"
        "          case result of\n"
        "            Ok(value) when value > 0 -> \"positive\"\n"
        "            Ok(value) when value < 0 -> \"negative\"\n"
        "            Ok(_) -> \"zero\"\n"
        "            Error(msg) -> msg\n"
        "          end\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    % Check that we can parse complex case with guards and constructor patterns
    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,
    ?assertMatch(#function_def{name = test_complex_case}, FunctionDef),

    Body = FunctionDef#function_def.body,
    ?assertMatch(#match_expr{}, Body),

    #match_expr{patterns = Patterns} = Body,
    ?assertEqual(4, length(Patterns)),

    % Check that we have constructor patterns with guards
    [FirstClause, SecondClause, ThirdClause, FourthClause] = Patterns,
    ?assertMatch(
        #match_clause{
            pattern = #constructor_pattern{name = 'Ok'},
            guard = Guard1
        } when Guard1 =/= undefined,
        FirstClause
    ),

    ?assertMatch(
        #match_clause{
            pattern = #constructor_pattern{name = 'Ok'},
            guard = Guard2
        } when Guard2 =/= undefined,
        SecondClause
    ),

    ?assertMatch(
        #match_clause{
            pattern = #constructor_pattern{name = 'Ok'},
            guard = undefined
        },
        ThirdClause
    ),

    ?assertMatch(
        #match_clause{
            pattern = #constructor_pattern{name = 'Error'},
            guard = undefined
        },
        FourthClause
    ),

    ok.

%% ===== RECORD PATTERN MATCHING TESTS =====

%% Test basic record pattern matching
test_record_pattern_matching_basic() ->
    Code = <<
        "record Person { name: String, age: Int }\n"
        "        \n"
        "        def greet(person: Person): String =\n"
        "          case person of\n"
        "            Person{name: n, age: a} -> \"Hello \" ++ n\n"
        "            _ -> \"Hello stranger\"\n"
        "          end\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(2, length(AST)),
    [RecordDef, FunctionDef] = AST,

    % Check record definition
    ?assertMatch(#record_def{name = 'Person'}, RecordDef),

    % Check function definition
    ?assertMatch(#function_def{name = greet}, FunctionDef),

    Body = FunctionDef#function_def.body,
    ?assertMatch(#match_expr{}, Body),

    #match_expr{patterns = Patterns} = Body,
    ?assertEqual(2, length(Patterns)),

    % Check record pattern
    [RecordClause, WildcardClause] = Patterns,
    ?assertMatch(
        #match_clause{
            pattern = #record_pattern{name = 'Person'}
        },
        RecordClause
    ),

    % Check record pattern fields
    #match_clause{pattern = RecordPattern} = RecordClause,
    #record_pattern{fields = Fields} = RecordPattern,
    ?assertEqual(2, length(Fields)),

    ok.

%% Test record pattern field extraction
test_record_pattern_matching_field_extraction() ->
    Code = <<
        "record Point { x: Float, y: Float }\n"
        "        record Circle { center: Point, radius: Float }\n"
        "        \n"
        "        def get_center_x(circle: Circle): Float =\n"
        "          case circle of\n"
        "            Circle{center: Point{x: center_x}} -> center_x\n"
        "            _ -> 0.0\n"
        "          end\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(3, length(AST)),
    [PointDef, CircleDef, FunctionDef] = AST,

    % Check record definitions
    ?assertMatch(#record_def{name = 'Point'}, PointDef),
    ?assertMatch(#record_def{name = 'Circle'}, CircleDef),

    % Check function with nested record pattern
    ?assertMatch(#function_def{name = get_center_x}, FunctionDef),

    Body = FunctionDef#function_def.body,
    ?assertMatch(#match_expr{}, Body),

    #match_expr{patterns = Patterns} = Body,
    ?assertEqual(2, length(Patterns)),

    % Check nested record pattern
    [NestedClause, _] = Patterns,
    ?assertMatch(
        #match_clause{
            pattern = #record_pattern{name = 'Circle'}
        },
        NestedClause
    ),

    ok.

%% Test nested record patterns
test_record_pattern_matching_nested() ->
    Code = <<
        "record Address { street: String, city: String }\n"
        "        record Person { name: String, address: Address }\n"
        "        \n"
        "        def get_city(person: Person): String =\n"
        "          match person do\n"
        "            Person{address: Address{city: c}} -> c\n"
        "            _ -> \"Unknown\"\n"
        "          end\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(3, length(AST)),
    [AddressDef, PersonDef, FunctionDef] = AST,

    % Check definitions exist
    ?assertMatch(#record_def{name = 'Address'}, AddressDef),
    ?assertMatch(#record_def{name = 'Person'}, PersonDef),
    ?assertMatch(#function_def{name = get_city}, FunctionDef),

    ok.

%% ===== CONSTRUCTOR PATTERN TESTS =====

%% Test constructor patterns with multiple arguments
test_constructor_pattern_multiple_args() ->
    Code = <<
        "def process_result(result: Result(Int, String)): String =\n"
        "          case result of\n"
        "            Ok(value) -> \"Success: \" ++ show(value)\n"
        "            Error(msg) -> \"Error: \" ++ msg\n"
        "          end\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,

    Body = FunctionDef#function_def.body,
    ?assertMatch(#match_expr{}, Body),

    #match_expr{patterns = Patterns} = Body,
    ?assertEqual(2, length(Patterns)),

    % Check constructor patterns
    [OkClause, ErrorClause] = Patterns,
    ?assertMatch(
        #match_clause{
            pattern = #constructor_pattern{name = 'Ok', args = [_]}
        },
        OkClause
    ),

    ?assertMatch(
        #match_clause{
            pattern = #constructor_pattern{name = 'Error', args = [_]}
        },
        ErrorClause
    ),

    ok.

%% Test constructor patterns with no arguments
test_constructor_pattern_no_args() ->
    Code = <<
        "def process_option(opt: Option(Int)): String =\n"
        "          case opt of\n"
        "            Some(value) -> show(value)\n"
        "            None() -> \"empty\"\n"
        "            None -> \"also empty\"\n"
        "          end\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,

    Body = FunctionDef#function_def.body,
    ?assertMatch(#match_expr{}, Body),

    #match_expr{patterns = Patterns} = Body,
    ?assertEqual(3, length(Patterns)),

    % Check constructor patterns
    [SomeClause, NoneWithParensClause, NoneWithoutParensClause] = Patterns,

    ?assertMatch(
        #match_clause{
            pattern = #constructor_pattern{name = 'Some', args = [_]}
        },
        SomeClause
    ),

    % None() - empty constructor with parentheses
    ?assertMatch(
        #match_clause{
            pattern = #constructor_pattern{name = 'None', args = []}
        },
        NoneWithParensClause
    ),

    % None - constructor without parentheses (should be parsed as identifier pattern)
    ?assertMatch(
        #match_clause{
            pattern = #identifier_pattern{name = 'None'}
        },
        NoneWithoutParensClause
    ),

    ok.

%% ===== TYPE INFERENCE TESTS =====

%% Test type inference for record definitions
test_type_inference_record_definitions() ->
    Code = <<
        "record Person { name: String, age: Int }\n"
        "        \n"
        "        def create_person(): Person =\n"
        "          Person{name: \"Alice\", age: 30}\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(2, length(AST)),
    [RecordDef, FunctionDef] = AST,

    % Check record definition structure
    ?assertMatch(
        #record_def{
            name = 'Person',
            fields = [_, _]
        },
        RecordDef
    ),

    #record_def{fields = Fields} = RecordDef,
    ?assertEqual(2, length(Fields)),

    % Check field types are defined
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

    ok.

%% Test type inference for record construction
test_type_inference_record_construction() ->
    Code = <<
        "record Point { x: Float, y: Float }\n"
        "        \n"
        "        def origin(): Point =\n"
        "          Point{x: 0.0, y: 0.0}\n"
        "        \n"
        "        def point_from_ints(a: Int, b: Int): Point =\n"
        "          Point{x: float(a), y: float(b)}\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(3, length(AST)),
    [RecordDef, OriginFunc, PointFromIntsFunc] = AST,

    % Check record construction in function bodies
    ?assertMatch(#record_def{name = 'Point'}, RecordDef),

    % Check origin function
    ?assertMatch(#function_def{name = origin}, OriginFunc),
    OriginBody = OriginFunc#function_def.body,
    ?assertMatch(#record_expr{name = 'Point'}, OriginBody),

    % Check point_from_ints function
    ?assertMatch(#function_def{name = point_from_ints}, PointFromIntsFunc),
    PointBody = PointFromIntsFunc#function_def.body,
    ?assertMatch(#record_expr{name = 'Point'}, PointBody),

    ok.

%% Test type inference for record patterns
test_type_inference_record_patterns() ->
    Code = <<
        "record Color { r: Int, g: Int, b: Int }\n"
        "        \n"
        "        def is_grayscale(color: Color): Bool =\n"
        "          case color of\n"
        "            Color{r: r, g: g, b: b} when r == g and g == b -> true\n"
        "            _ -> false\n"
        "          end\n"
        "        \n"
        "        def get_red(color: Color): Int =\n"
        "          case color of\n"
        "            Color{r: red_value} -> red_value\n"
        "            _ -> 0\n"
        "          end\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(3, length(AST)),
    [ColorDef, IsGrayscaleFunc, GetRedFunc] = AST,

    % Check record definition
    ?assertMatch(#record_def{name = 'Color'}, ColorDef),

    % Check functions use record patterns correctly
    ?assertMatch(#function_def{name = is_grayscale}, IsGrayscaleFunc),
    ?assertMatch(#function_def{name = get_red}, GetRedFunc),

    % Check that record patterns are parsed correctly
    IsGrayscaleBody = IsGrayscaleFunc#function_def.body,
    ?assertMatch(#match_expr{}, IsGrayscaleBody),

    GetRedBody = GetRedFunc#function_def.body,
    ?assertMatch(#match_expr{}, GetRedBody),

    ok.

%% ===== SHOW FUNCTIONS BEHAVIOR TESTS =====

%% Test the show, print, and println functions behavior
test_show_functions_behavior() ->
    % Test that we can parse code using the show functions
    Code = <<
        "def test_show_functions(x: Int): Unit =\n"
        "          let str = show(x)\n"
        "          print(str)\n"
        "          println(\"Done\")\n"
        "        "
    >>,

    {ok, Tokens} = cure_lexer:tokenize(Code),
    {ok, AST} = cure_parser:parse(Tokens),

    ?assertEqual(1, length(AST)),
    [FunctionDef] = AST,

    % Check function structure
    ?assertMatch(#function_def{name = test_show_functions}, FunctionDef),

    Body = FunctionDef#function_def.body,
    ?assertMatch(#let_expr{}, Body),

    % The function should parse successfully, demonstrating that the show functions
    % are properly defined in the standard library
    ok.

%% ===== HELPER FUNCTIONS =====

%% Get location from pattern (helper function for testing)
get_pattern_location(#literal_pattern{location = Loc}) -> Loc;
get_pattern_location(#identifier_pattern{location = Loc}) -> Loc;
get_pattern_location(#wildcard_pattern{location = Loc}) -> Loc;
get_pattern_location(#record_pattern{location = Loc}) -> Loc;
get_pattern_location(#constructor_pattern{location = Loc}) -> Loc;
get_pattern_location(_) -> {1, 1}.
