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

%% Function clause (for multi-clause functions)
-record(function_clause, {
    params,          % Parameters with types for this clause
    return_type,     % Return type for this specific clause (optional)
    constraint,      % Guard/constraint for this clause (optional)
    body,            % Function body for this clause
    location         % Source location
}).

%% Function definition
%% Supports both single-clause (backward compatible) and multi-clause functions
-record(function_def, {
    name,
    clauses,         % List of #function_clause{} records (new multi-clause support)
    params,          % DEPRECATED: kept for backward compatibility, use clauses instead
    return_type,     % Union of all clause return types (derived)
    constraint,      % DEPRECATED: kept for backward compatibility
    body,            % DEPRECATED: kept for backward compatibility
    is_private,      % determined by export list, not by keyword
    location
}).

%% Curify function definition (wraps Erlang functions)
-record(curify_function_def, {
    name,
    params,
    return_type,
    constraint,
    erlang_module,   % Atom: Erlang module name
    erlang_function, % Atom: Erlang function name
    erlang_arity,    % Integer: Erlang function arity
    is_private,      % Boolean: determined by export list
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
    timeout,     % Optional timeout
    location
}).

%% FSM spawn expression
-record(fsm_spawn_expr, {
    fsm_name,
    init_args,
    init_state,
    location
}).

%% FSM message send expression
-record(fsm_send_expr, {
    target,      % FSM or Pid to send to
    message,     % Message to send
    location
}).

%% FSM receive expression for handling messages
-record(fsm_receive_expr, {
    patterns,    % List of message patterns to match
    timeout,     % Optional timeout
    location
}).

%% FSM state expression for current state access
-record(fsm_state_expr, {
    location
}).

%% Safety property assertion for FSM verification
-record(fsm_property, {
    name,
    property_type,  % invariant | eventually | always | until
    condition,
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

%% FSM types
-record(fsm_type, {
    name,           % FSM name
    states,         % List of valid states
    message_types,  % List of message types
    location
}).

%% Process type (for FSM instances)
-record(process_type, {
    fsm_type,      % The FSM type this process implements
    current_state, % Current state (for refinement types)
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
               #let_expr{} |
               #binary_op_expr{} |
               #unary_op_expr{} |
               #list_expr{} |
               #tuple_expr{} |
               #record_expr{} |
               #lambda_expr{} |
               #fsm_spawn_expr{} |
               #fsm_send_expr{} |
               #fsm_receive_expr{} |
               #fsm_state_expr{}.

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
                    #tuple_type{} |
                    #fsm_type{} |
                    #process_type{}.

-type match_clause() :: #match_clause{}.
-type binding() :: #binding{}.
-type field_expr() :: #field_expr{}.
-type field_pattern() :: #field_pattern{}.
-type param() :: #param{} | atom().  % Record param or simple atom
-type type_param() :: #type_param{}.
-type state_def() :: #state_def{}.
-type transition() :: #transition{}.

