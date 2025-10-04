%% Cure Programming Language - AST Header File
%% Record definitions for Abstract Syntax Tree nodes

%% Token record (from lexer)
-record(token, {
    type,
    value,
    line,
    column
}).

%% Source location information
-record(location, {
    line,
    column,
    file
}).

%% Module definition
-record(module_def, {
    name,
    exports,
    items,
    location
}).

%% Function definition
-record(function_def, {
    name,
    params,
    return_type,
    constraint,
    body,
    location
}).

%% Type definition
-record(type_def, {
    name :: atom(),
    params :: [atom()],
    definition :: type_expr(),
    location :: location()
}).

%% FSM definition
-record(fsm_def, {
    name :: atom(),
    states :: [atom()],
    initial :: atom(),
    state_defs :: [state_def()],
    location :: location()
}).

%% State definition within FSM
-record(state_def, {
    name :: atom(),
    transitions :: [transition()],
    location :: location()
}).

%% State transition
-record(transition, {
    event :: expr(),
    guard :: expr() | undefined,
    target :: atom(),
    action :: expr() | undefined,
    location :: location()
}).

%% Import definition
-record(import_def, {
    module :: atom(),
    items :: [atom()] | all,
    location :: location()
}).

%% Export specification
-record(export_spec, {
    name :: atom(),
    arity :: integer(),
    location :: location()
}).

%% Function parameter
-record(param, {
    name :: atom(),
    type :: type_expr(),
    location :: location()
}).

%% Literal expressions
-record(literal_expr, {
    value :: term(),
    location :: location()
}).

%% Identifier expressions
-record(identifier_expr, {
    name :: atom(),
    location :: location()
}).

%% Function call expressions
-record(function_call_expr, {
    function :: expr(),
    args :: [expr()],
    location :: location()
}).

%% Match expressions
-record(match_expr, {
    expr :: expr(),
    patterns :: [match_clause()],
    location :: location()
}).

-record(match_clause, {
    pattern :: pattern(),
    guard :: expr() | undefined,
    body :: expr(),
    location :: location()
}).

%% If expressions
-record(if_expr, {
    condition :: expr(),
    then_branch :: expr(),
    else_branch :: expr(),
    location :: location()
}).

%% Let expressions
-record(let_expr, {
    bindings :: [binding()],
    body :: expr(),
    location :: location()
}).

-record(binding, {
    pattern :: pattern(),
    value :: expr(),
    location :: location()
}).

%% Binary operations
-record(binary_op_expr, {
    op :: atom(),
    left :: expr(),
    right :: expr(),
    location :: location()
}).

%% Unary operations
-record(unary_op_expr, {
    op :: atom(),
    operand :: expr(),
    location :: location()
}).

%% List expressions
-record(list_expr, {
    elements :: [expr()],
    location :: location()
}).

%% Tuple expressions
-record(tuple_expr, {
    elements :: [expr()],
    location :: location()
}).

%% Record expressions
-record(record_expr, {
    name :: atom(),
    fields :: [field_expr()],
    location :: location()
}).

-record(field_expr, {
    name :: atom(),
    value :: expr(),
    location :: location()
}).

%% Lambda expressions
-record(lambda_expr, {
    params :: [param()],
    body :: expr(),
    location :: location()
}).

%% Primitive types
-record(primitive_type, {
    name :: atom(),
    location :: location()
}).

%% Dependent types
-record(dependent_type, {
    name :: atom(),
    params :: [type_param()],
    location :: location()
}).

-record(type_param, {
    name :: atom() | undefined,  % Named parameter
    value :: type_expr() | expr(),  % Type or value parameter
    location :: location()
}).

%% Function types
-record(function_type, {
    params :: [type_expr()],
    return_type :: type_expr(),
    location :: location()
}).

%% Union types
-record(union_type, {
    types :: [type_expr()],
    location :: location()
}).

%% List types
-record(list_type, {
    element_type :: type_expr(),
    length :: expr() | undefined,  % For dependent typing
    location :: location()
}).

%% Tuple types
-record(tuple_type, {
    element_types :: [type_expr()],
    location :: location()
}).

%% Wildcard pattern
-record(wildcard_pattern, {
    location :: location()
}).

%% Literal pattern
-record(literal_pattern, {
    value :: term(),
    location :: location()
}).

%% Identifier pattern
-record(identifier_pattern, {
    name :: atom(),
    location :: location()
}).

%% List pattern
-record(list_pattern, {
    elements :: [pattern()],
    tail :: pattern() | undefined,
    location :: location()
}).

%% Tuple pattern
-record(tuple_pattern, {
    elements :: [pattern()],
    location :: location()
}).

%% Record pattern
-record(record_pattern, {
    name :: atom(),
    fields :: [field_pattern()],
    location :: location()
}).

-record(field_pattern, {
    name :: atom(),
    pattern :: pattern(),
    location :: location()
}).