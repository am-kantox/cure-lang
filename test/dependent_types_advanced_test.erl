%% Dependent Type System Advanced Tests - Complex Constraints and Refinement Types
-module(dependent_types_advanced_test).

-export([run/0]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/parser/cure_ast_simple.hrl").

%% Type checking result record (from cure_typechecker.erl)
-record(typecheck_result, {
    success :: boolean(),
    type :: term() | undefined,
    errors :: [term()],
    warnings :: [term()]
}).

%% Run all dependent type system tests
run() ->
    io:format("Running Dependent Types Advanced tests...~n"),
    test_length_indexed_lists(),
    test_refinement_types(),
    test_dependent_function_types(),
    test_type_constraints_validation(),
    test_dependent_record_types(),
    test_bounded_integers(),
    test_capacity_constrained_collections(),
    test_state_dependent_operations(),
    test_proof_carrying_code(),
    test_dependent_type_inference(),
    io:format("All dependent type system advanced tests passed!~n").

%% Test length-indexed lists (Vector types)
test_length_indexed_lists() ->
    % Test Vector(T, n) where n is the length
    VectorType3Int = create_vector_type('Int', 3),
    VectorType5String = create_vector_type('String', 5),
    VectorTypeDynamic = create_vector_type('Int', 'N'),  % Parametric length
    
    % Test creating a vector with correct length
    Vector3Elements = create_vector_expression([
        create_literal_int(1),
        create_literal_int(2),
        create_literal_int(3)
    ]),
    
    % Should type-check successfully
    Env = cure_typechecker:builtin_env(),
    Result1 = cure_typechecker:check_expression_with_expected_type(
        Vector3Elements, VectorType3Int, Env),
    ?assertMatch(#typecheck_result{success = true}, Result1),
    
    % Test creating a vector with incorrect length
    Vector2Elements = create_vector_expression([
        create_literal_int(1),
        create_literal_int(2)
    ]),
    
    % Should fail type-check (length mismatch: 2 ≠ 3)
    Result2 = cure_typechecker:check_expression_with_expected_type(
        Vector2Elements, VectorType3Int, Env),
    ?assertMatch(#typecheck_result{success = false}, Result2),
    ?assert(lists:any(fun(Error) ->
        case Error of
            {length_mismatch, Expected, Actual} -> 
                Expected == 3 andalso Actual == 2;
            _ -> false
        end
    end, Result2#typecheck_result.errors)),
    
    % Test vector concatenation type checking
    ConcatExpr = create_vector_concat_expression(Vector3Elements, Vector2Elements),
    ExpectedConcatType = create_vector_type('Int', 5),  % 3 + 2 = 5
    
    Result3 = cure_typechecker:infer_expression_type(ConcatExpr, Env),
    ?assertMatch(#typecheck_result{success = true}, Result3),
    ?assertEqual(ExpectedConcatType, Result3#typecheck_result.type),
    
    % Test parametric vector operations
    ParametricVectorFun = create_parametric_vector_function(),
    Result4 = cure_typechecker:check_function(ParametricVectorFun),
    ?assertMatch({ok, _Env, #typecheck_result{success = true}}, Result4),
    
    io:format("✓ Length-indexed lists test passed~n").

%% Test refinement types (types with predicates)
test_refinement_types() ->
    % Test {x: Int | x > 0} (positive integers)
    PositiveIntType = create_refinement_type('Int', 
        create_predicate_greater_than(create_identifier('x'), create_literal_int(0))),
    
    % Test {x: Int | x >= 0 && x <= 100} (bounded integers)
    BoundedIntType = create_refinement_type('Int',
        create_and_predicate(
            create_predicate_greater_equal(create_identifier('x'), create_literal_int(0)),
            create_predicate_less_equal(create_identifier('x'), create_literal_int(100))
        )),
    
    % Test {s: String | len(s) >= 3} (non-empty strings with minimum length)
    NonEmptyStringType = create_refinement_type('String',
        create_predicate_greater_equal(
            create_function_call(len, [create_identifier('s')]),
            create_literal_int(3)
        )),
    
    Env = cure_typechecker:builtin_env(),
    
    % Test positive literal assignment
    PositiveLiteral = create_literal_int(42),
    Result1 = cure_typechecker:check_expression_with_expected_type(
        PositiveLiteral, PositiveIntType, Env),
    ?assertMatch(#typecheck_result{success = true}, Result1),
    
    % Test negative literal assignment (should fail)
    NegativeLiteral = create_literal_int(-5),
    Result2 = cure_typechecker:check_expression_with_expected_type(
        NegativeLiteral, PositiveIntType, Env),
    ?assertMatch(#typecheck_result{success = false}, Result2),
    ?assert(lists:any(fun(Error) ->
        case Error of
            {refinement_violation, _Predicate, _Value} -> true;
            _ -> false
        end
    end, Result2#typecheck_result.errors)),
    
    % Test bounded integer (valid case)
    BoundedLiteral = create_literal_int(50),
    Result3 = cure_typechecker:check_expression_with_expected_type(
        BoundedLiteral, BoundedIntType, Env),
    ?assertMatch(#typecheck_result{success = true}, Result3),
    
    % Test bounded integer (out of bounds)
    OutOfBoundsLiteral = create_literal_int(150),
    Result4 = cure_typechecker:check_expression_with_expected_type(
        OutOfBoundsLiteral, BoundedIntType, Env),
    ?assertMatch(#typecheck_result{success = false}, Result4),
    
    % Test string length refinement
    ValidString = create_literal_string("Hello"),  % Length = 5 >= 3
    Result5 = cure_typechecker:check_expression_with_expected_type(
        ValidString, NonEmptyStringType, Env),
    ?assertMatch(#typecheck_result{success = true}, Result5),
    
    InvalidString = create_literal_string("Hi"),  % Length = 2 < 3
    Result6 = cure_typechecker:check_expression_with_expected_type(
        InvalidString, NonEmptyStringType, Env),
    ?assertMatch(#typecheck_result{success = false}, Result6),
    
    io:format("✓ Refinement types test passed~n").

%% Test dependent function types
test_dependent_function_types() ->
    % Test function: take(list: List(T), n: Nat) -> List(T, min(len(list), n))
    TakeFunction = #function_def{
        name = take,
        params = [
            #param{
                name = list,
                type = create_dependent_list_type('T'),
                location = create_location(1, 1)
            },
            #param{
                name = n,
                type = #primitive_type{name = 'Nat', location = create_location(1, 2)},
                location = create_location(1, 2)
            }
        ],
        return_type = create_dependent_type('List', [
            create_type_param('T'),
            create_function_call(min, [
                create_function_call(len, [create_identifier('list')]),
                create_identifier('n')
            ])
        ]),
        constraint = undefined,
        body = create_take_implementation(),
        location = create_location(1, 1)
    },
    
    % Test function: replicate(n: Nat, x: T) -> List(T, n)
    ReplicateFunction = #function_def{
        name = replicate,
        params = [
            #param{
                name = n,
                type = #primitive_type{name = 'Nat', location = create_location(3, 1)},
                location = create_location(3, 1)
            },
            #param{
                name = x,
                type = create_type_variable('T'),
                location = create_location(3, 2)
            }
        ],
        return_type = create_vector_type('T', create_identifier('n')),
        constraint = undefined,
        body = create_replicate_implementation(),
        location = create_location(3, 1)
    },
    
    % Test type checking of dependent functions
    Result1 = cure_typechecker:check_function(TakeFunction),
    ?assertMatch({ok, _Env, #typecheck_result{success = true}}, Result1),
    
    Result2 = cure_typechecker:check_function(ReplicateFunction),
    ?assertMatch({ok, _Env, #typecheck_result{success = true}}, Result2),
    
    % Test calling dependent functions
    Env = cure_typechecker:builtin_env(),
    
    % take([1,2,3,4,5], 3) should return List(Int, 3)
    TakeCall = #function_call_expr{
        function = create_identifier('take'),
        args = [
            create_list_literal([1, 2, 3, 4, 5]),
            create_literal_int(3)
        ],
        location = create_location(5, 1)
    },
    
    Result3 = cure_typechecker:infer_expression_type(TakeCall, Env),
    ?assertMatch(#typecheck_result{success = true}, Result3),
    ExpectedTakeResultType = create_vector_type('Int', 3),
    ?assertEqual(ExpectedTakeResultType, Result3#typecheck_result.type),
    
    % replicate(4, "hello") should return List(String, 4)
    ReplicateCall = #function_call_expr{
        function = create_identifier('replicate'),
        args = [
            create_literal_int(4),
            create_literal_string("hello")
        ],
        location = create_location(6, 1)
    },
    
    Result4 = cure_typechecker:infer_expression_type(ReplicateCall, Env),
    ?assertMatch(#typecheck_result{success = true}, Result4),
    ExpectedReplicateResultType = create_vector_type('String', 4),
    ?assertEqual(ExpectedReplicateResultType, Result4#typecheck_result.type),
    
    io:format("✓ Dependent function types test passed~n").

%% Test type constraint validation
test_type_constraints_validation() ->
    % Test function with complex type constraints
    ConstrainedFunction = #function_def{
        name = safe_divide,
        params = [
            #param{
                name = numerator,
                type = #primitive_type{name = 'Float', location = create_location(1, 1)},
                location = create_location(1, 1)
            },
            #param{
                name = denominator,
                type = create_refinement_type('Float', 
                    create_predicate_not_equal(create_identifier('x'), create_literal_float(0.0))),
                location = create_location(1, 2)
            }
        ],
        return_type = #primitive_type{name = 'Float', location = create_location(1, 3)},
        constraint = create_constraint_expression(
            create_predicate_not_equal(
                create_identifier('denominator'), 
                create_literal_float(0.0)
            )
        ),
        body = #binary_op_expr{
            op = '/',
            left = create_identifier('numerator'),
            right = create_identifier('denominator'),
            location = create_location(2, 1)
        },
        location = create_location(1, 1)
    },
    
    % Should pass type checking with constraint
    Result1 = cure_typechecker:check_function(ConstrainedFunction),
    ?assertMatch({ok, _Env, #typecheck_result{success = true}}, Result1),
    
    % Test calling with valid arguments
    Env = cure_typechecker:builtin_env(),
    ValidCall = #function_call_expr{
        function = create_identifier('safe_divide'),
        args = [
            create_literal_float(10.0),
            create_literal_float(2.0)  % Non-zero, satisfies constraint
        ],
        location = create_location(4, 1)
    },
    
    Result2 = cure_typechecker:check_expression(ValidCall, Env),
    ?assertMatch(#typecheck_result{success = true}, Result2),
    
    % Test calling with invalid arguments (should be caught at compile time)
    InvalidCall = #function_call_expr{
        function = create_identifier('safe_divide'),
        args = [
            create_literal_float(10.0),
            create_literal_float(0.0)  % Zero, violates constraint
        ],
        location = create_location(5, 1)
    },
    
    Result3 = cure_typechecker:check_expression(InvalidCall, Env),
    ?assertMatch(#typecheck_result{success = false}, Result3),
    ?assert(lists:any(fun(Error) ->
        case Error of
            {constraint_violation, _} -> true;
            _ -> false
        end
    end, Result3#typecheck_result.errors)),
    
    io:format("✓ Type constraints validation test passed~n").

%% Test dependent record types
test_dependent_record_types() ->
    % Test Buffer record with capacity and current size
    BufferType = create_dependent_record_type('Buffer', [
        {capacity, create_refinement_type('Nat', 
            create_predicate_greater_than(create_identifier('x'), create_literal_int(0)))},
        {data, create_vector_type('T', create_identifier('size'))},
        {size, create_refinement_type('Nat',
            create_and_predicate(
                create_predicate_greater_equal(create_identifier('x'), create_literal_int(0)),
                create_predicate_less_equal(create_identifier('x'), create_identifier('capacity'))
            ))}
    ]),
    
    % Test creating a valid buffer
    ValidBuffer = create_record_expression('Buffer', [
        {capacity, create_literal_int(10)},
        {data, create_vector_expression([
            create_literal_string("a"),
            create_literal_string("b"),
            create_literal_string("c")
        ])},
        {size, create_literal_int(3)}
    ]),
    
    Env = cure_typechecker:builtin_env(),
    Result1 = cure_typechecker:check_expression_with_expected_type(
        ValidBuffer, BufferType, Env),
    ?assertMatch(#typecheck_result{success = true}, Result1),
    
    % Test creating invalid buffer (size > capacity)
    InvalidBuffer = create_record_expression('Buffer', [
        {capacity, create_literal_int(5)},
        {data, create_vector_expression([
            create_literal_string("a"),
            create_literal_string("b"),
            create_literal_string("c"),
            create_literal_string("d"),
            create_literal_string("e"),
            create_literal_string("f"),
            create_literal_string("g")
        ])},
        {size, create_literal_int(7)}  % 7 > 5 (capacity)
    ]),
    
    Result2 = cure_typechecker:check_expression_with_expected_type(
        InvalidBuffer, BufferType, Env),
    ?assertMatch(#typecheck_result{success = false}, Result2),
    
    % Test buffer operations
    BufferPushFunction = create_buffer_push_function(),
    Result3 = cure_typechecker:check_function(BufferPushFunction),
    ?assertMatch({ok, _Env, #typecheck_result{success = true}}, Result3),
    
    io:format("✓ Dependent record types test passed~n").

%% Test bounded integers with range constraints
test_bounded_integers() ->
    % Test different bounded integer types
    ByteType = create_bounded_integer_type(0, 255),
    PercentType = create_bounded_integer_type(0, 100),
    TemperatureType = create_bounded_integer_type(-273, 10000),  % Celsius
    
    Env = cure_typechecker:builtin_env(),
    
    % Test valid byte values
    ValidByte = create_literal_int(128),
    Result1 = cure_typechecker:check_expression_with_expected_type(
        ValidByte, ByteType, Env),
    ?assertMatch(#typecheck_result{success = true}, Result1),
    
    % Test invalid byte value (out of range)
    InvalidByte = create_literal_int(300),
    Result2 = cure_typechecker:check_expression_with_expected_type(
        InvalidByte, ByteType, Env),
    ?assertMatch(#typecheck_result{success = false}, Result2),
    
    % Test arithmetic on bounded integers
    ByteAddition = #binary_op_expr{
        op = '+',
        left = create_literal_int(100),  % Byte value
        right = create_literal_int(50),  % Byte value
        location = create_location(1, 1)
    },
    
    % Result should be checked for overflow
    Result3 = cure_typechecker:check_expression_with_expected_type(
        ByteAddition, ByteType, Env),
    ?assertMatch(#typecheck_result{success = true}, Result3),  % 100 + 50 = 150, within byte range
    
    ByteOverflow = #binary_op_expr{
        op = '+',
        left = create_literal_int(200),  % Byte value
        right = create_literal_int(100),  % Byte value
        location = create_location(2, 1)
    },
    
    Result4 = cure_typechecker:check_expression_with_expected_type(
        ByteOverflow, ByteType, Env),
    ?assertMatch(#typecheck_result{success = false}, Result4),  % 200 + 100 = 300, overflow
    
    io:format("✓ Bounded integers test passed~n").

%% Test capacity-constrained collections
test_capacity_constrained_collections() ->
    % Test BoundedList(T, MaxCapacity) type
    BoundedList10 = create_bounded_list_type('String', 10),
    BoundedList5 = create_bounded_list_type('Int', 5),
    
    Env = cure_typechecker:builtin_env(),
    
    % Test creating bounded list within capacity
    SmallList = create_list_literal(["a", "b", "c"]),  % 3 elements, under capacity
    Result1 = cure_typechecker:check_expression_with_expected_type(
        SmallList, BoundedList10, Env),
    ?assertMatch(#typecheck_result{success = true}, Result1),
    
    % Test creating bounded list exceeding capacity
    LargeList = create_list_literal([1, 2, 3, 4, 5, 6, 7]),  % 7 elements, exceeds capacity of 5
    Result2 = cure_typechecker:check_expression_with_expected_type(
        LargeList, BoundedList5, Env),
    ?assertMatch(#typecheck_result{success = false}, Result2),
    ?assert(lists:any(fun(Error) ->
        case Error of
            {capacity_exceeded, _MaxCapacity, _ActualSize} -> true;
            _ -> false
        end
    end, Result2#typecheck_result.errors)),
    
    % Test bounded list operations
    BoundedListAppendFunction = create_bounded_list_append_function(),
    Result3 = cure_typechecker:check_function(BoundedListAppendFunction),
    ?assertMatch({ok, _Env, #typecheck_result{success = true}}, Result3),
    
    io:format("✓ Capacity-constrained collections test passed~n").

%% Test state-dependent operations
test_state_dependent_operations() ->
    % Test File operations with state (Open/Closed)
    FileStateType = create_union_type([
        create_tagged_type('Open', create_primitive_type('FileHandle')),
        create_tagged_type('Closed', create_primitive_type('Unit'))
    ]),
    
    % Function: read(file: File(Open)) -> String
    ReadFunction = #function_def{
        name = read_file,
        params = [
            #param{
                name = file,
                type = create_tagged_type('Open', create_primitive_type('FileHandle')),
                location = create_location(1, 1)
            }
        ],
        return_type = #primitive_type{name = 'String', location = create_location(1, 2)},
        constraint = undefined,
        body = create_file_read_implementation(),
        location = create_location(1, 1)
    },
    
    % Function: close(file: File(Open)) -> File(Closed)
    CloseFunction = #function_def{
        name = close_file,
        params = [
            #param{
                name = file,
                type = create_tagged_type('Open', create_primitive_type('FileHandle')),
                location = create_location(3, 1)
            }
        ],
        return_type = create_tagged_type('Closed', create_primitive_type('Unit')),
        constraint = undefined,
        body = create_file_close_implementation(),
        location = create_location(3, 1)
    },
    
    Result1 = cure_typechecker:check_function(ReadFunction),
    ?assertMatch({ok, _Env, #typecheck_result{success = true}}, Result1),
    
    Result2 = cure_typechecker:check_function(CloseFunction),
    ?assertMatch({ok, _Env, #typecheck_result{success = true}}, Result2),
    
    Env = cure_typechecker:builtin_env(),
    
    % Test valid operation (reading from open file)
    OpenFile = create_tagged_value('Open', create_literal_string("file_handle_123")),
    ValidReadCall = #function_call_expr{
        function = create_identifier('read_file'),
        args = [OpenFile],
        location = create_location(5, 1)
    },
    
    Result3 = cure_typechecker:check_expression(ValidReadCall, Env),
    ?assertMatch(#typecheck_result{success = true}, Result3),
    
    % Test invalid operation (reading from closed file)
    ClosedFile = create_tagged_value('Closed', create_unit_literal()),
    InvalidReadCall = #function_call_expr{
        function = create_identifier('read_file'),
        args = [ClosedFile],
        location = create_location(6, 1)
    },
    
    Result4 = cure_typechecker:check_expression(InvalidReadCall, Env),
    ?assertMatch(#typecheck_result{success = false}, Result4),
    ?assert(lists:any(fun(Error) ->
        case Error of
            {state_mismatch, _Expected, _Actual} -> true;
            _ -> false
        end
    end, Result4#typecheck_result.errors)),
    
    io:format("✓ State-dependent operations test passed~n").

%% Test proof-carrying code patterns
test_proof_carrying_code() ->
    % Test function that requires proof of non-emptiness
    SafeHeadFunction = #function_def{
        name = safe_head,
        params = [
            #param{
                name = list,
                type = create_refinement_type(
                    create_list_type('T'),
                    create_predicate_greater_than(
                        create_function_call(length, [create_identifier('list')]),
                        create_literal_int(0)
                    )
                ),
                location = create_location(1, 1)
            }
        ],
        return_type = create_type_variable('T'),
        constraint = undefined,
        body = create_safe_head_implementation(),
        location = create_location(1, 1)
    },
    
    Result1 = cure_typechecker:check_function(SafeHeadFunction),
    ?assertMatch({ok, _Env, #typecheck_result{success = true}}, Result1),
    
    Env = cure_typechecker:builtin_env(),
    
    % Test with provably non-empty list
    NonEmptyList = create_list_literal([1, 2, 3]),
    ValidCall = #function_call_expr{
        function = create_identifier('safe_head'),
        args = [NonEmptyList],
        location = create_location(3, 1)
    },
    
    Result2 = cure_typechecker:check_expression(ValidCall, Env),
    ?assertMatch(#typecheck_result{success = true}, Result2),
    
    % Test with potentially empty list (should require runtime check or proof)
    PotentiallyEmptyList = create_identifier('unknown_list'),
    UncertainCall = #function_call_expr{
        function = create_identifier('safe_head'),
        args = [PotentiallyEmptyList],
        location = create_location(4, 1)
    },
    
    Result3 = cure_typechecker:check_expression(UncertainCall, Env),
    ?assertMatch(#typecheck_result{success = false}, Result3),
    ?assert(lists:any(fun(Error) ->
        case Error of
            {insufficient_proof, _Property} -> true;
            _ -> false
        end
    end, Result3#typecheck_result.errors)),
    
    io:format("✓ Proof-carrying code test passed~n").

%% Test dependent type inference
test_dependent_type_inference() ->
    % Test that the type system can infer dependent types
    Env = cure_typechecker:builtin_env(),
    
    % Simple list literal should infer List(Int, 3)
    ListLiteral = create_list_literal([1, 2, 3]),
    Result1 = cure_typechecker:infer_expression_type(ListLiteral, Env),
    ?assertMatch(#typecheck_result{success = true}, Result1),
    ExpectedType = create_vector_type('Int', 3),
    ?assertEqual(ExpectedType, Result1#typecheck_result.type),
    
    % Concatenation should infer combined length
    List1 = create_list_literal([1, 2]),
    List2 = create_list_literal([3, 4, 5]),
    ConcatExpr = create_concat_expression(List1, List2),
    
    Result2 = cure_typechecker:infer_expression_type(ConcatExpr, Env),
    ?assertMatch(#typecheck_result{success = true}, Result2),
    ExpectedConcatType = create_vector_type('Int', 5),
    ?assertEqual(ExpectedConcatType, Result2#typecheck_result.type),
    
    % Test arithmetic inference with bounded integers
    BoundedValue1 = create_literal_int(50),  % Within byte range
    BoundedValue2 = create_literal_int(30),  % Within byte range
    AdditionExpr = #binary_op_expr{
        op = '+',
        left = BoundedValue1,
        right = BoundedValue2,
        location = create_location(1, 1)
    },
    
    % Should infer that result is 80, which fits in byte range
    Result3 = cure_typechecker:infer_expression_type(AdditionExpr, Env),
    ?assertMatch(#typecheck_result{success = true}, Result3),
    
    io:format("✓ Dependent type inference test passed~n").

%% ============================================================================
%% Helper Functions for Creating AST Nodes and Type Expressions
%% ============================================================================

create_location(Line, Column) ->
    #location{line = Line, column = Column, file = "test"}.

create_literal_int(Value) ->
    #literal_expr{value = Value, location = create_location(1, 1)}.

create_literal_float(Value) ->
    #literal_expr{value = Value, location = create_location(1, 1)}.

create_literal_string(Value) ->
    #literal_expr{value = Value, location = create_location(1, 1)}.

create_unit_literal() ->
    #literal_expr{value = unit, location = create_location(1, 1)}.

create_identifier(Name) ->
    #identifier_expr{name = Name, location = create_location(1, 1)}.

create_vector_type(ElementType, Length) ->
    #dependent_type{
        name = 'Vector',
        params = [
            #type_param{value = #primitive_type{name = ElementType, location = create_location(1, 1)}},
            #type_param{value = Length}
        ],
        location = create_location(1, 1)
    }.

create_dependent_list_type(ElementType) ->
    #dependent_type{
        name = 'List',
        params = [#type_param{value = #primitive_type{name = ElementType, location = create_location(1, 1)}}],
        location = create_location(1, 1)
    }.

create_refinement_type(BaseType, Predicate) ->
    #dependent_type{
        name = 'Refined',
        params = [
            #type_param{value = #primitive_type{name = BaseType, location = create_location(1, 1)}},
            #type_param{value = Predicate}
        ],
        location = create_location(1, 1)
    }.

create_predicate_greater_than(Left, Right) ->
    #binary_op_expr{op = '>', left = Left, right = Right, location = create_location(1, 1)}.

create_predicate_greater_equal(Left, Right) ->
    #binary_op_expr{op = '>=', left = Left, right = Right, location = create_location(1, 1)}.

create_predicate_less_equal(Left, Right) ->
    #binary_op_expr{op = '=<', left = Left, right = Right, location = create_location(1, 1)}.

create_predicate_not_equal(Left, Right) ->
    #binary_op_expr{op = '/=', left = Left, right = Right, location = create_location(1, 1)}.

create_and_predicate(Left, Right) ->
    #binary_op_expr{op = 'and', left = Left, right = Right, location = create_location(1, 1)}.

create_function_call(Name, Args) ->
    #function_call_expr{
        function = create_identifier(Name),
        args = Args,
        location = create_location(1, 1)
    }.

create_vector_expression(Elements) ->
    #list_expr{elements = Elements, location = create_location(1, 1)}.

create_vector_concat_expression(Left, Right) ->
    #function_call_expr{
        function = create_identifier('concat'),
        args = [Left, Right],
        location = create_location(1, 1)
    }.

create_list_literal(Values) ->
    Elements = [create_literal_int(V) || V <- Values, is_integer(V)] ++
               [create_literal_string(V) || V <- Values, is_list(V)],
    #list_expr{elements = Elements, location = create_location(1, 1)}.

create_type_variable(Name) ->
    #primitive_type{name = Name, location = create_location(1, 1)}.

create_constraint_expression(Predicate) ->
    Predicate.

create_dependent_record_type(Name, Fields) ->
    FieldSpecs = [create_field_spec(FieldName, FieldType) || {FieldName, FieldType} <- Fields],
    #dependent_type{
        name = Name,
        params = FieldSpecs,
        location = create_location(1, 1)
    }.

create_field_spec(Name, Type) ->
    #field_expr{name = Name, value = Type, location = create_location(1, 1)}.

create_record_expression(Name, Fields) ->
    FieldExprs = [#field_expr{name = FName, value = FValue, location = create_location(1, 1)} 
                  || {FName, FValue} <- Fields],
    #record_expr{name = Name, fields = FieldExprs, location = create_location(1, 1)}.

create_bounded_integer_type(Min, Max) ->
    create_refinement_type('Int',
        create_and_predicate(
            create_predicate_greater_equal(create_identifier('x'), create_literal_int(Min)),
            create_predicate_less_equal(create_identifier('x'), create_literal_int(Max))
        )).

create_bounded_list_type(ElementType, MaxCapacity) ->
    #dependent_type{
        name = 'BoundedList',
        params = [
            #type_param{value = #primitive_type{name = ElementType, location = create_location(1, 1)}},
            #type_param{value = create_literal_int(MaxCapacity)}
        ],
        location = create_location(1, 1)
    }.

create_union_type(Types) ->
    #union_type{types = Types, location = create_location(1, 1)}.

create_tagged_type(Tag, InnerType) ->
    #dependent_type{
        name = 'Tagged',
        params = [
            #type_param{value = create_identifier(Tag)},
            #type_param{value = InnerType}
        ],
        location = create_location(1, 1)
    }.

create_primitive_type(Name) ->
    #primitive_type{name = Name, location = create_location(1, 1)}.

create_list_type(ElementType) ->
    #list_type{
        element_type = #primitive_type{name = ElementType, location = create_location(1, 1)},
        length = undefined,
        location = create_location(1, 1)
    }.

create_tagged_value(Tag, Value) ->
    #tuple_expr{
        elements = [create_identifier(Tag), Value],
        location = create_location(1, 1)
    }.

create_concat_expression(Left, Right) ->
    create_function_call('++', [Left, Right]).

%% Placeholder implementations for complex functions
create_parametric_vector_function() ->
    #function_def{
        name = vector_map,
        params = [
            #param{name = f, type = create_function_type(['T'], 'U'), location = create_location(1, 1)},
            #param{name = vec, type = create_vector_type('T', 'N'), location = create_location(1, 2)}
        ],
        return_type = create_vector_type('U', 'N'),
        constraint = undefined,
        body = create_identifier('not_implemented'),
        location = create_location(1, 1)
    }.

create_function_type(ParamTypes, ReturnType) ->
    #function_type{
        params = [#primitive_type{name = PT, location = create_location(1, 1)} || PT <- ParamTypes],
        return_type = #primitive_type{name = ReturnType, location = create_location(1, 1)},
        location = create_location(1, 1)
    }.

create_take_implementation() ->
    create_identifier('not_implemented').

create_replicate_implementation() ->
    create_identifier('not_implemented').

create_buffer_push_function() ->
    #function_def{
        name = buffer_push,
        params = [
            #param{name = buffer, type = create_identifier('Buffer'), location = create_location(1, 1)},
            #param{name = item, type = create_type_variable('T'), location = create_location(1, 2)}
        ],
        return_type = create_identifier('Buffer'),
        constraint = undefined,
        body = create_identifier('not_implemented'),
        location = create_location(1, 1)
    }.

create_bounded_list_append_function() ->
    #function_def{
        name = bounded_append,
        params = [
            #param{name = list, type = create_bounded_list_type('T', 'N'), location = create_location(1, 1)},
            #param{name = item, type = create_type_variable('T'), location = create_location(1, 2)}
        ],
        return_type = create_bounded_list_type('T', 'N'),
        constraint = undefined,
        body = create_identifier('not_implemented'),
        location = create_location(1, 1)
    }.

create_file_read_implementation() ->
    create_identifier('not_implemented').

create_file_close_implementation() ->
    create_identifier('not_implemented').

create_safe_head_implementation() ->
    create_identifier('not_implemented').