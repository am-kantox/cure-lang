%% Test module for NamedValue(T) primitive type
-module(namedvalue_test).

-include("../src/parser/cure_ast.hrl").

-export([run/0]).

run() ->
    io:format("~n=== NamedValue Type Tests ===~n"),
    
    % Test 1: NamedValue type parsing
    test_namedvalue_parsing(),
    
    % Test 2: NamedValue type unification
    test_namedvalue_unification(),
    
    % Test 3: NamedValue as tuple equivalence
    test_namedvalue_tuple_equivalence(),
    
    io:format("~n=== All NamedValue Tests Passed ===~n"),
    ok.

%% Test 1: NamedValue type parsing
test_namedvalue_parsing() ->
    io:format("~nTest 1: NamedValue type parsing...~n"),
    
    % Parse "type Person = NamedValue(String)"
    Code = <<"type Person = NamedValue(String)">>,
    
    case cure_lexer:tokenize(Code) of
        {ok, Tokens} when is_list(Tokens) ->
            io:format("  Tokens: ~p~n", [Tokens]),
            
            case cure_parser:parse(Tokens) of
                {ok, AST} ->
                    io:format("  Parsed AST successfully~n"),
                    io:format("  AST: ~200p~n", [AST]),
                    io:format("  ✓ NamedValue parsing test passed~n");
                {error, Reason} ->
                    io:format("  ✗ Parse error: ~p~n", [Reason]),
                    throw({parse_error, Reason})
            end;
        {error, Reason} ->
            io:format("  ✗ Tokenization error: ~p~n", [Reason]),
            throw({tokenize_error, Reason})
    end.

%% Test 2: NamedValue type unification
test_namedvalue_unification() ->
    io:format("~nTest 2: NamedValue type unification...~n"),
    
    % Create NamedValue(Int) and NamedValue(Int) - should unify
    Location = #location{line = 1, column = 1, file = <<"test">>},
    
    IntType = #primitive_type{name = 'Int', location = Location},
    IntParam = #type_param{
        name = undefined,
        value = IntType,
        location = Location
    },
    
    NamedValue1 = #dependent_type{
        name = 'NamedValue',
        params = [IntParam],
        location = Location
    },
    
    NamedValue2 = #dependent_type{
        name = 'NamedValue',
        params = [IntParam],
        location = Location
    },
    
    case cure_types:unify(NamedValue1, NamedValue2) of
        {ok, _Subst} ->
            io:format("  ✓ NamedValue(Int) unifies with NamedValue(Int)~n");
        {error, Reason} ->
            io:format("  ✗ Unification failed: ~p~n", [Reason]),
            throw({unification_error, Reason})
    end,
    
    % Create NamedValue(Int) and NamedValue(String) - should not unify
    StringType = #primitive_type{name = 'String', location = Location},
    StringParam = #type_param{
        name = undefined,
        value = StringType,
        location = Location
    },
    
    NamedValueString = #dependent_type{
        name = 'NamedValue',
        params = [StringParam],
        location = Location
    },
    
    case cure_types:unify(NamedValue1, NamedValueString) of
        {error, _} ->
            io:format("  ✓ NamedValue(Int) does not unify with NamedValue(String)~n");
        {ok, _} ->
            io:format("  ✗ Should not unify different NamedValue types~n"),
            throw(unexpected_unification)
    end.

%% Test 3: NamedValue as tuple equivalence
test_namedvalue_tuple_equivalence() ->
    io:format("~nTest 3: NamedValue as tuple equivalence...~n"),
    
    % Create NamedValue(Int)
    Location = #location{line = 1, column = 1, file = <<"test">>},
    
    IntType = #primitive_type{name = 'Int', location = Location},
    IntParam = #type_param{
        name = undefined,
        value = IntType,
        location = Location
    },
    
    NamedValueInt = #dependent_type{
        name = 'NamedValue',
        params = [IntParam],
        location = Location
    },
    
    % Create tuple type {Atom, Int}
    AtomType = #primitive_type{name = 'Atom', location = Location},
    
    TupleType = #tuple_type{
        element_types = [AtomType, IntType],
        location = Location
    },
    
    % These should unify since NamedValue(T) is equivalent to {Atom, T}
    case cure_types:unify(NamedValueInt, TupleType) of
        {ok, _Subst1} ->
            io:format("  ✓ NamedValue(Int) unifies with {Atom, Int}~n");
        {error, Reason1} ->
            io:format("  ✗ Unification failed: ~p~n", [Reason1]),
            throw({tuple_unification_error, Reason1})
    end,
    
    % Test reverse direction
    case cure_types:unify(TupleType, NamedValueInt) of
        {ok, _Subst2} ->
            io:format("  ✓ {Atom, Int} unifies with NamedValue(Int)~n");
        {error, Reason2} ->
            io:format("  ✗ Reverse unification failed: ~p~n", [Reason2]),
            throw({reverse_tuple_unification_error, Reason2})
    end.
