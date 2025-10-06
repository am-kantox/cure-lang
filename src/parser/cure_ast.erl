%% Cure Programming Language - AST Definitions
%% Abstract Syntax Tree node definitions
-module(cure_ast).

-export([
    new_module/4,
    new_function/5,
    new_type_def/3,
    new_fsm/4,
    new_expr/3
]).

%% AST Node Types

%% Program is a list of top-level items
-type program() :: [item()].

%% Top-level items
-type item() :: 
    module_def() | 
    function_def() | 
    erlang_function_def() |
    type_def() | 
    fsm_def() | 
    import_def().

%% Module definition
-record(module_def, {
    name :: atom(),
    exports :: [export_spec()],
    items :: [item()],
    location :: location()
}).
-type module_def() :: #module_def{}.

%% Function definition
-record(function_def, {
    name :: atom(),
    params :: [param()],
    return_type :: type_expr() | undefined,
    constraint :: expr() | undefined,
    body :: expr(),
    location :: location()
}).
-type function_def() :: #function_def{}.

%% Erlang function definition (for Erlang interop)
-record(erlang_function_def, {
    name :: atom(),
    params :: [param()],
    return_type :: type_expr(),
    constraint :: expr() | undefined,
    erlang_body :: string(),  % Raw Erlang code as string
    location :: location()
}).
-type erlang_function_def() :: #erlang_function_def{}.

%% Type definition
-record(type_def, {
    name :: atom(),
    params :: [atom()],
    definition :: type_expr(),
    location :: location()
}).
-type type_def() :: #type_def{}.

%% FSM definition
-record(fsm_def, {
    name :: atom(),
    states :: [atom()],
    initial :: atom(),
    state_defs :: [state_def()],
    location :: location()
}).
-type fsm_def() :: #fsm_def{}.

%% State definition within FSM
-record(state_def, {
    name :: atom(),
    transitions :: [transition()],
    location :: location()
}).
-type state_def() :: #state_def{}.

%% State transition
-record(transition, {
    event :: expr(),
    guard :: expr() | undefined,
    target :: atom(),
    action :: expr() | undefined,
    location :: location()
}).
-type transition() :: #transition{}.

%% Import definition
-record(import_def, {
    module :: atom(),
    items :: [atom()] | all,
    location :: location()
}).
-type import_def() :: #import_def{}.

%% Export specification
-record(export_spec, {
    name :: atom(),
    arity :: integer(),
    location :: location()
}).
-type export_spec() :: #export_spec{}.

%% Function parameter
-record(param, {
    name :: atom(),
    type :: type_expr(),
    location :: location()
}).
-type param() :: #param{}.

%% Expressions
-type expr() :: 
    literal_expr() |
    identifier_expr() |
    function_call_expr() |
    match_expr() |
    if_expr() |
    let_expr() |
    binary_op_expr() |
    unary_op_expr() |
    list_expr() |
    tuple_expr() |
    record_expr() |
    lambda_expr().

%% Literal expressions
-record(literal_expr, {
    value :: term(),
    location :: location()
}).
-type literal_expr() :: #literal_expr{}.

%% Identifier expressions
-record(identifier_expr, {
    name :: atom(),
    location :: location()
}).
-type identifier_expr() :: #identifier_expr{}.

%% Function call expressions
-record(function_call_expr, {
    function :: expr(),
    args :: [expr()],
    location :: location()
}).
-type function_call_expr() :: #function_call_expr{}.

%% Match expressions
-record(match_expr, {
    expr :: expr(),
    patterns :: [match_clause()],
    location :: location()
}).
-type match_expr() :: #match_expr{}.

-record(match_clause, {
    pattern :: pattern(),
    guard :: expr() | undefined,
    body :: expr(),
    location :: location()
}).
-type match_clause() :: #match_clause{}.

%% If expressions
-record(if_expr, {
    condition :: expr(),
    then_branch :: expr(),
    else_branch :: expr(),
    location :: location()
}).
-type if_expr() :: #if_expr{}.

%% Let expressions
-record(let_expr, {
    bindings :: [binding()],
    body :: expr(),
    location :: location()
}).
-type let_expr() :: #let_expr{}.

-record(binding, {
    pattern :: pattern(),
    value :: expr(),
    location :: location()
}).
-type binding() :: #binding{}.

%% Binary operations
-record(binary_op_expr, {
    op :: atom(),
    left :: expr(),
    right :: expr(),
    location :: location()
}).
-type binary_op_expr() :: #binary_op_expr{}.

%% Unary operations
-record(unary_op_expr, {
    op :: atom(),
    operand :: expr(),
    location :: location()
}).
-type unary_op_expr() :: #unary_op_expr{}.

%% List expressions
-record(list_expr, {
    elements :: [expr()],
    location :: location()
}).
-type list_expr() :: #list_expr{}.

%% Tuple expressions
-record(tuple_expr, {
    elements :: [expr()],
    location :: location()
}).
-type tuple_expr() :: #tuple_expr{}.

%% Record expressions
-record(record_expr, {
    name :: atom(),
    fields :: [field_expr()],
    location :: location()
}).
-type record_expr() :: #record_expr{}.

-record(field_expr, {
    name :: atom(),
    value :: expr(),
    location :: location()
}).
-type field_expr() :: #field_expr{}.

%% Lambda expressions
-record(lambda_expr, {
    params :: [param()],
    body :: expr(),
    location :: location()
}).
-type lambda_expr() :: #lambda_expr{}.

%% Type expressions
-type type_expr() :: 
    primitive_type() |
    dependent_type() |
    function_type() |
    union_type() |
    list_type() |
    tuple_type().

%% Primitive types
-record(primitive_type, {
    name :: atom(),
    location :: location()
}).
-type primitive_type() :: #primitive_type{}.

%% Dependent types
-record(dependent_type, {
    name :: atom(),
    params :: [type_param()],
    location :: location()
}).
-type dependent_type() :: #dependent_type{}.

-record(type_param, {
    name :: atom() | undefined,  % Named parameter
    value :: type_expr() | expr(),  % Type or value parameter
    location :: location()
}).
-type type_param() :: #type_param{}.

%% Function types
-record(function_type, {
    params :: [type_expr()],
    return_type :: type_expr(),
    location :: location()
}).
-type function_type() :: #function_type{}.

%% Union types
-record(union_type, {
    types :: [type_expr()],
    location :: location()
}).
-type union_type() :: #union_type{}.

%% List types
-record(list_type, {
    element_type :: type_expr(),
    length :: expr() | undefined,  % For dependent typing
    location :: location()
}).
-type list_type() :: #list_type{}.

%% Tuple types
-record(tuple_type, {
    element_types :: [type_expr()],
    location :: location()
}).
-type tuple_type() :: #tuple_type{}.

%% Patterns for pattern matching
-type pattern() :: 
    wildcard_pattern() |
    literal_pattern() |
    identifier_pattern() |
    list_pattern() |
    tuple_pattern() |
    record_pattern().

-record(wildcard_pattern, {
    location :: location()
}).
-type wildcard_pattern() :: #wildcard_pattern{}.

-record(literal_pattern, {
    value :: term(),
    location :: location()
}).
-type literal_pattern() :: #literal_pattern{}.

-record(identifier_pattern, {
    name :: atom(),
    location :: location()
}).
-type identifier_pattern() :: #identifier_pattern{}.

-record(list_pattern, {
    elements :: [pattern()],
    tail :: pattern() | undefined,
    location :: location()
}).
-type list_pattern() :: #list_pattern{}.

-record(tuple_pattern, {
    elements :: [pattern()],
    location :: location()
}).
-type tuple_pattern() :: #tuple_pattern{}.

-record(record_pattern, {
    name :: atom(),
    fields :: [field_pattern()],
    location :: location()
}).
-type record_pattern() :: #record_pattern{}.

-record(field_pattern, {
    name :: atom(),
    pattern :: pattern(),
    location :: location()
}).
-type field_pattern() :: #field_pattern{}.

%% Source location information
-record(location, {
    line :: integer(),
    column :: integer(),
    file :: string() | undefined
}).
-type location() :: #location{}.

%% Export all type definitions
-export_type([
    program/0, item/0,
    module_def/0, function_def/0, erlang_function_def/0, type_def/0, fsm_def/0, import_def/0,
    state_def/0, transition/0,
    export_spec/0, param/0,
    expr/0, literal_expr/0, identifier_expr/0, function_call_expr/0,
    match_expr/0, match_clause/0, if_expr/0, let_expr/0, binding/0,
    binary_op_expr/0, unary_op_expr/0, list_expr/0, tuple_expr/0,
    record_expr/0, field_expr/0, lambda_expr/0,
    type_expr/0, primitive_type/0, dependent_type/0, type_param/0,
    function_type/0, union_type/0, list_type/0, tuple_type/0,
    pattern/0, wildcard_pattern/0, literal_pattern/0, identifier_pattern/0,
    list_pattern/0, tuple_pattern/0, record_pattern/0, field_pattern/0,
    location/0
]).

%% Helper functions for creating AST nodes

%% Create a module definition
-spec new_module(atom(), [export_spec()], [item()], location()) -> module_def().
new_module(Name, Exports, Items, Location) ->
    #module_def{
        name = Name,
        exports = Exports,
        items = Items,
        location = Location
    }.

%% Create a function definition
-spec new_function(atom(), [param()], type_expr() | undefined, 
                  expr() | undefined, expr()) -> function_def().
new_function(Name, Params, ReturnType, Constraint, Body) ->
    #function_def{
        name = Name,
        params = Params,
        return_type = ReturnType,
        constraint = Constraint,
        body = Body,
        location = #location{line = 0, column = 0}  % TODO: proper location
    }.

%% Create a type definition
-spec new_type_def(atom(), [atom()], type_expr()) -> type_def().
new_type_def(Name, Params, Definition) ->
    #type_def{
        name = Name,
        params = Params,
        definition = Definition,
        location = #location{line = 0, column = 0}  % TODO: proper location
    }.

%% Create an FSM definition
-spec new_fsm(atom(), [atom()], atom(), [state_def()]) -> fsm_def().
new_fsm(Name, States, Initial, StateDefs) ->
    #fsm_def{
        name = Name,
        states = States,
        initial = Initial,
        state_defs = StateDefs,
        location = #location{line = 0, column = 0}  % TODO: proper location
    }.

%% Create an expression with location
-spec new_expr(atom(), term(), location()) -> expr().
new_expr(literal, Value, Location) ->
    #literal_expr{value = Value, location = Location};
new_expr(identifier, Name, Location) ->
    #identifier_expr{name = Name, location = Location};
new_expr(Type, Data, Location) ->
    error({unknown_expr_type, Type, Data, Location}).