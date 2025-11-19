%% Cure Programming Language - SMT Array Theory Support
%% Enables list/vector constraints using SMT array theory
-module(cure_smt_array).

-moduledoc """
# SMT Array Theory for Lists and Vectors

This module provides SMT array theory support for reasoning about lists and vectors
with constraints like:
- All elements satisfy a property (forall i. arr[i] > 0)
- Sorted sequences (forall i j. i < j => arr[i] <= arr[j])
- Length-indexed vectors (length(arr) == n)

## SMT-LIB Array Theory

Arrays in SMT-LIB are maps from indices to values:
```smt
(declare-const arr (Array Int Int))  ; Array from Int to Int
(assert (= (select arr 0) 42))        ; arr[0] = 42
(assert (= (store arr 1 10) arr2))    ; arr2 = arr with arr2[1] = 10
```

## Usage

```erlang
% Check if all elements are positive
Constraint = all_elements_satisfy(arr, n, 
    fun(i, v) -> #binary_op_expr{op = '>', left = v, right = lit(0)} end),
Query = generate_array_query(Constraint, #{arr => {array, int, int}, n => {type, int}}).
```
""".

-export([
    % Array constraint builders
    all_elements_satisfy/3,
    exists_element_satisfying/3,
    sorted_ascending/2,
    sorted_descending/2,
    array_length_constraint/2,

    % Array operations
    array_select/2,
    array_store/3,
    array_const/1,

    % Query generation
    generate_array_query/2,
    generate_array_query/3,

    % Type support
    declare_array/3,

    % Helper functions
    has_quantifiers/1
]).

-include("../parser/cure_ast.hrl").

%% ============================================================================
%% Array Constraint Builders
%% ============================================================================

%% @doc Generate constraint that all elements in array satisfy a property
%% forall i. 0 <= i < length => property(arr[i])
-spec all_elements_satisfy(atom(), atom(), fun((atom(), expr()) -> expr())) -> expr().
all_elements_satisfy(ArrayVar, LengthVar, PropertyFn) ->
    % Create index variable
    IndexVar = list_to_atom(atom_to_list(ArrayVar) ++ "_i"),

    % Create array access: arr[i]
    ArrayAccess = array_select(ArrayVar, IndexVar),

    % Generate property for arr[i]
    Property = PropertyFn(IndexVar, ArrayAccess),

    % Build: forall i. (0 <= i < length) => property(arr[i])
    IndexInBounds = #binary_op_expr{
        op = 'and',
        left = #binary_op_expr{
            op = '>=',
            left = #identifier_expr{name = IndexVar, location = #location{}},
            right = #literal_expr{value = 0, location = #location{}},
            location = #location{}
        },
        right = #binary_op_expr{
            op = '<',
            left = #identifier_expr{name = IndexVar, location = #location{}},
            right = #identifier_expr{name = LengthVar, location = #location{}},
            location = #location{}
        },
        location = #location{}
    },

    Implication = #binary_op_expr{
        op = '=>',
        left = IndexInBounds,
        right = Property,
        location = #location{}
    },

    % Wrap in forall quantifier
    {forall_expr, [{IndexVar, int}], Implication}.

%% @doc Generate constraint that at least one element satisfies a property
%% exists i. 0 <= i < length /\ property(arr[i])
-spec exists_element_satisfying(atom(), atom(), fun((atom(), expr()) -> expr())) -> expr().
exists_element_satisfying(ArrayVar, LengthVar, PropertyFn) ->
    IndexVar = list_to_atom(atom_to_list(ArrayVar) ++ "_i"),
    ArrayAccess = array_select(ArrayVar, IndexVar),
    Property = PropertyFn(IndexVar, ArrayAccess),

    IndexInBounds = #binary_op_expr{
        op = 'and',
        left = #binary_op_expr{
            op = '>=',
            left = #identifier_expr{name = IndexVar, location = #location{}},
            right = #literal_expr{value = 0, location = #location{}},
            location = #location{}
        },
        right = #binary_op_expr{
            op = '<',
            left = #identifier_expr{name = IndexVar, location = #location{}},
            right = #identifier_expr{name = LengthVar, location = #location{}},
            location = #location{}
        },
        location = #location{}
    },

    Conjunction = #binary_op_expr{
        op = 'and',
        left = IndexInBounds,
        right = Property,
        location = #location{}
    },

    {exists_expr, [{IndexVar, int}], Conjunction}.

%% @doc Generate sorted ascending constraint
%% forall i j. 0 <= i < j < length => arr[i] <= arr[j]
-spec sorted_ascending(atom(), atom()) -> expr().
sorted_ascending(ArrayVar, LengthVar) ->
    IVar = list_to_atom(atom_to_list(ArrayVar) ++ "_i"),
    JVar = list_to_atom(atom_to_list(ArrayVar) ++ "_j"),

    % Build: 0 <= i < j < length
    IBounds = #binary_op_expr{
        op = 'and',
        left = #binary_op_expr{
            op = '>=',
            left = #identifier_expr{name = IVar, location = #location{}},
            right = #literal_expr{value = 0, location = #location{}},
            location = #location{}
        },
        right = #binary_op_expr{
            op = '<',
            left = #identifier_expr{name = IVar, location = #location{}},
            right = #identifier_expr{name = JVar, location = #location{}},
            location = #location{}
        },
        location = #location{}
    },

    JBound = #binary_op_expr{
        op = '<',
        left = #identifier_expr{name = JVar, location = #location{}},
        right = #identifier_expr{name = LengthVar, location = #location{}},
        location = #location{}
    },

    Bounds = #binary_op_expr{
        op = 'and',
        left = IBounds,
        right = JBound,
        location = #location{}
    },

    % Build: arr[i] <= arr[j]
    SortedProperty = #binary_op_expr{
        op = '=<',
        left = array_select(ArrayVar, IVar),
        right = array_select(ArrayVar, JVar),
        location = #location{}
    },

    Implication = #binary_op_expr{
        op = '=>',
        left = Bounds,
        right = SortedProperty,
        location = #location{}
    },

    {forall_expr, [{IVar, int}, {JVar, int}], Implication}.

%% @doc Generate sorted descending constraint
-spec sorted_descending(atom(), atom()) -> expr().
sorted_descending(ArrayVar, LengthVar) ->
    % Similar to sorted_ascending but with >= instead of <=
    IVar = list_to_atom(atom_to_list(ArrayVar) ++ "_i"),
    JVar = list_to_atom(atom_to_list(ArrayVar) ++ "_j"),

    IBounds = #binary_op_expr{
        op = 'and',
        left = #binary_op_expr{
            op = '>=',
            left = #identifier_expr{name = IVar, location = #location{}},
            right = #literal_expr{value = 0, location = #location{}},
            location = #location{}
        },
        right = #binary_op_expr{
            op = '<',
            left = #identifier_expr{name = IVar, location = #location{}},
            right = #identifier_expr{name = JVar, location = #location{}},
            location = #location{}
        },
        location = #location{}
    },

    JBound = #binary_op_expr{
        op = '<',
        left = #identifier_expr{name = JVar, location = #location{}},
        right = #identifier_expr{name = LengthVar, location = #location{}},
        location = #location{}
    },

    Bounds = #binary_op_expr{
        op = 'and',
        left = IBounds,
        right = JBound,
        location = #location{}
    },

    SortedProperty = #binary_op_expr{
        op = '>=',
        left = array_select(ArrayVar, IVar),
        right = array_select(ArrayVar, JVar),
        location = #location{}
    },

    Implication = #binary_op_expr{
        op = '=>',
        left = Bounds,
        right = SortedProperty,
        location = #location{}
    },

    {forall_expr, [{IVar, int}, {JVar, int}], Implication}.

%% @doc Generate array length constraint
-spec array_length_constraint(atom(), integer() | atom()) -> expr().
array_length_constraint(LengthVar, ExpectedLength) when is_integer(ExpectedLength) ->
    #binary_op_expr{
        op = '==',
        left = #identifier_expr{name = LengthVar, location = #location{}},
        right = #literal_expr{value = ExpectedLength, location = #location{}},
        location = #location{}
    };
array_length_constraint(LengthVar, ExpectedVar) when is_atom(ExpectedVar) ->
    #binary_op_expr{
        op = '==',
        left = #identifier_expr{name = LengthVar, location = #location{}},
        right = #identifier_expr{name = ExpectedVar, location = #location{}},
        location = #location{}
    }.

%% ============================================================================
%% Array Operations
%% ============================================================================

%% @doc Generate array select (indexing) expression: arr[i]
-spec array_select(atom(), atom() | integer()) -> expr().
array_select(ArrayVar, Index) when is_atom(Index) ->
    #function_call_expr{
        function = #identifier_expr{name = select, location = #location{}},
        args = [
            #identifier_expr{name = ArrayVar, location = #location{}},
            #identifier_expr{name = Index, location = #location{}}
        ],
        location = #location{}
    };
array_select(ArrayVar, Index) when is_integer(Index) ->
    #function_call_expr{
        function = #identifier_expr{name = select, location = #location{}},
        args = [
            #identifier_expr{name = ArrayVar, location = #location{}},
            #literal_expr{value = Index, location = #location{}}
        ],
        location = #location{}
    }.

%% @doc Generate array store (update) expression: store(arr, i, v)
-spec array_store(atom(), atom() | integer(), expr()) -> expr().
array_store(ArrayVar, Index, Value) when is_atom(Index) ->
    #function_call_expr{
        function = #identifier_expr{name = store, location = #location{}},
        args = [
            #identifier_expr{name = ArrayVar, location = #location{}},
            #identifier_expr{name = Index, location = #location{}},
            Value
        ],
        location = #location{}
    };
array_store(ArrayVar, Index, Value) when is_integer(Index) ->
    #function_call_expr{
        function = #identifier_expr{name = store, location = #location{}},
        args = [
            #identifier_expr{name = ArrayVar, location = #location{}},
            #literal_expr{value = Index, location = #location{}},
            Value
        ],
        location = #location{}
    }.

%% @doc Generate constant array expression: ((as const (Array Int Int)) value)
-spec array_const(integer()) -> expr().
array_const(Value) ->
    #function_call_expr{
        function = #identifier_expr{name = const, location = #location{}},
        args = [#literal_expr{value = Value, location = #location{}}],
        location = #location{}
    }.

%% ============================================================================
%% Query Generation
%% ============================================================================

%% @doc Generate SMT-LIB query with array theory
-spec generate_array_query(expr(), map()) -> iolist().
generate_array_query(Constraint, Env) ->
    generate_array_query(Constraint, Env, #{}).

-spec generate_array_query(expr(), map(), map()) -> iolist().
generate_array_query(Constraint, Env, Opts) ->
    % Use QF_AUFLIA logic (Quantifier-Free Arrays, Uninterpreted Functions, Linear Integer Arithmetic)
    % Or just AUFLIA if we have quantifiers
    Logic =
        case has_quantifiers(Constraint) of
            true -> 'AUFLIA';
            false -> 'QF_AUFLIA'
        end,

    % Collect variables from environment (not from constraint, since quantified vars are local)
    Vars = maps:keys(Env),

    % Generate declarations (arrays and regular variables)
    Declarations = lists:map(
        fun(V) ->
            case maps:get(V, Env, undefined) of
                {array, IndexType, ElemType} ->
                    declare_array(V, IndexType, ElemType);
                _ ->
                    cure_smt_translator:declare_variable(V, Env)
            end
        end,
        Vars
    ),

    % Translate constraint with array support
    Assertion = ["(assert ", translate_array_expr(Constraint, Env), ")\n"],

    % Assemble query
    [
        "(set-logic ",
        atom_to_list(Logic),
        ")\n",
        Declarations,
        Assertion,
        "(check-sat)\n",
        case maps:get(get_model, Opts, true) of
            true -> "(get-model)\n";
            false -> ""
        end
    ].

%% @doc Declare an array variable in SMT-LIB
-spec declare_array(atom(), atom(), atom()) -> iolist().
declare_array(Name, IndexType, ElemType) ->
    IndexSmt = map_type_to_smt(IndexType),
    ElemSmt = map_type_to_smt(ElemType),
    ["(declare-const ", atom_to_list(Name), " (Array ", IndexSmt, " ", ElemSmt, "))\n"].

%% ============================================================================
%% Array Expression Translation
%% ============================================================================

%% @doc Translate expressions with array operations
-spec translate_array_expr(expr(), map()) -> iolist().
% Quantified expressions
translate_array_expr({forall_expr, Vars, Body}, Env) ->
    VarDecls = lists:map(
        fun({V, Type}) ->
            ["(", atom_to_list(V), " ", map_type_to_smt(Type), ")"]
        end,
        Vars
    ),
    ["(forall (", lists:join(" ", VarDecls), ") ", translate_array_expr(Body, Env), ")"];
translate_array_expr({exists_expr, Vars, Body}, Env) ->
    VarDecls = lists:map(
        fun({V, Type}) ->
            ["(", atom_to_list(V), " ", map_type_to_smt(Type), ")"]
        end,
        Vars
    ),
    ["(exists (", lists:join(" ", VarDecls), ") ", translate_array_expr(Body, Env), ")"];
% Array operations
translate_array_expr(
    #function_call_expr{function = #identifier_expr{name = select}, args = [Arr, Idx]}, Env
) ->
    ["(select ", translate_array_expr(Arr, Env), " ", translate_array_expr(Idx, Env), ")"];
translate_array_expr(
    #function_call_expr{function = #identifier_expr{name = store}, args = [Arr, Idx, Val]}, Env
) ->
    [
        "(store ",
        translate_array_expr(Arr, Env),
        " ",
        translate_array_expr(Idx, Env),
        " ",
        translate_array_expr(Val, Env),
        ")"
    ];
translate_array_expr(
    #function_call_expr{function = #identifier_expr{name = const}, args = [Val]}, Env
) ->
    ["((as const (Array Int Int)) ", translate_array_expr(Val, Env), ")"];
% Delegate to standard translator for other expressions
translate_array_expr(Expr, Env) ->
    cure_smt_translator:translate_expr(Expr, Env).

%% ============================================================================
%% Helper Functions
%% ============================================================================

has_quantifiers({forall_expr, _, _}) ->
    true;
has_quantifiers({exists_expr, _, _}) ->
    true;
has_quantifiers(#binary_op_expr{left = L, right = R}) ->
    has_quantifiers(L) orelse has_quantifiers(R);
has_quantifiers(#unary_op_expr{operand = Op}) ->
    has_quantifiers(Op);
has_quantifiers(_) ->
    false.

map_type_to_smt(int) -> "Int";
map_type_to_smt(nat) -> "Int";
map_type_to_smt(real) -> "Real";
map_type_to_smt(bool) -> "Bool";
map_type_to_smt(_) -> "Int".
