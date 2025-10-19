%% Cure Programming Language - AST Header File (Simplified)
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
    is_private,  % true for defp, false for def
    location
}).

%% Erlang function definition (for Erlang interop)
-record(erlang_function_def, {
    name,
    params,
    return_type,
    constraint,
    erlang_body,  % Raw Erlang code as string
    location
}).

%% Type definition
-record(type_def, {
    name,
    params,
    definition,
    constraint,
    location
}).

%% Record definition
-record(record_def, {
    name,
    type_params,  % optional type parameters [param1, param2, ...]
    fields,
    location
}).

%% Record field definition
-record(record_field_def, {
    name,
    type,
    default_value,  % optional
    location
}).

%% FSM definition
-record(fsm_def, {
    name,
    states,
    initial,
    state_defs,
    location
}).

%% State definition within FSM
-record(state_def, {
    name,
    transitions,
    location
}).

%% State transition
-record(transition, {
    event,
    guard,
    target,
    action,
    location
}).

%% Import definition
-record(import_def, {
    module,
    items,
    location
}).

%% Function import specification (name/arity)
-record(function_import, {
    name,
    arity,
    alias,  % Optional alias name
    location
}).

%% Export specification
-record(export_spec, {
    name,
    arity,
    location
}).

%% Function parameter
-record(param, {
    name,
    type,
    location
}).

%% Literal expressions
-record(literal_expr, {
    value,
    location
}).

%% Identifier expressions
-record(identifier_expr, {
    name,
    location
}).

%% Function call expressions
-record(function_call_expr, {
    function,
    args,
    location
}).

%% Match expressions
-record(match_expr, {
    expr,
    patterns,
    location
}).

-record(match_clause, {
    pattern,
    guard,
    body,
    location
}).

%% If expressions
-record(if_expr, {
    condition,
    then_branch,
    else_branch,
    location
}).

%% Let expressions
-record(let_expr, {
    bindings,
    body,
    location
}).

%% Block expressions (sequential expressions)
-record(block_expr, {
    expressions,
    location
}).

-record(binding, {
    pattern,
    value,
    location
}).

%% Binary operations
-record(binary_op_expr, {
    op,
    left,
    right,
    location
}).

%% Unary operations
-record(unary_op_expr, {
    op,
    operand,
    location
}).

%% List expressions
-record(list_expr, {
    elements,
    location
}).

%% Cons expressions [head | tail]
-record(cons_expr, {
    elements,  % List of head elements
    tail,      % Tail expression
    location
}).

%% Type annotation expressions (expr as Type)
-record(type_annotation_expr, {
    expr,      % Expression being annotated
    type,      % Type annotation
    location
}).

%% Tuple expressions
-record(tuple_expr, {
    elements,
    location
}).

%% Record expressions
-record(record_expr, {
    name,
    fields,
    location
}).

-record(field_expr, {
    name,
    value,
    location
}).

%% Lambda expressions
-record(lambda_expr, {
    params,
    body,
    location
}).

%% String interpolation expressions
-record(string_interpolation_expr, {
    parts,   % List of {string_part, String} | {expr, Expression}
    location
}).

%% Primitive types
-record(primitive_type, {
    name,
    location
}).

%% Dependent types
-record(dependent_type, {
    name,
    params,
    location
}).

-record(type_param, {
    name,
    value,
    location
}).

%% Function types
-record(function_type, {
    params,
    return_type,
    location
}).

%% Union types
-record(union_type, {
    types,
    location
}).

%% List types
-record(list_type, {
    element_type,
    length,
    location
}).

%% Tuple types
-record(tuple_type, {
    element_types,
    location
}).

%% Patterns
-record(wildcard_pattern, {
    location
}).

-record(literal_pattern, {
    value,
    location
}).

-record(identifier_pattern, {
    name,
    location
}).

-record(list_pattern, {
    elements,
    tail,
    location
}).

-record(tuple_pattern, {
    elements,
    location
}).

-record(record_pattern, {
    name,
    fields,
    location
}).

-record(field_pattern, {
    name,
    pattern,
    location
}).

%% Constructor pattern (for Result, Option, etc.)
-record(constructor_pattern, {
    name,    % Ok, Error, Some, None, ok, error, etc.
    args,    % Arguments to the constructor (list or undefined)
    location
}).

%% Type definitions for use throughout the AST
-type location() :: #location{}.
-type expr() :: #literal_expr{} |
               #identifier_expr{} |
               #function_call_expr{} |
               #match_expr{} |
               #if_expr{} |
               #let_expr{} |
               #binary_op_expr{} |
               #unary_op_expr{} |
               #list_expr{} |
               #tuple_expr{} |
               #record_expr{} |
               #lambda_expr{}.

-type pattern() :: #wildcard_pattern{} |
                  #literal_pattern{} |
                  #identifier_pattern{} |
                  #list_pattern{} |
                  #tuple_pattern{} |
                  #record_pattern{} |
                  #constructor_pattern{}.

-type type_expr() :: #primitive_type{} |
                    #dependent_type{} |
                    #function_type{} |
                    #union_type{} |
                    #list_type{} |
                    #tuple_type{}.

-type match_clause() :: #match_clause{}.
-type binding() :: #binding{}.
-type field_expr() :: #field_expr{}.
-type field_pattern() :: #field_pattern{}.
-type param() :: #param{} | atom().  % Record param or simple atom
-type type_param() :: #type_param{}.
-type state_def() :: #state_def{}.
-type transition() :: #transition{}.

