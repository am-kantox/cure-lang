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
    type_params,     % List of type parameter atoms (e.g., ['T', 'U']) for polymorphic functions
    clauses,         % List of #function_clause{} records (new multi-clause support)
    params,          % DEPRECATED: kept for backward compatibility, use clauses instead
    return_type,     % Union of all clause return types (derived)
    constraint,      % DEPRECATED: kept for backward compatibility
    body,            % DEPRECATED: kept for backward compatibility
    where_clause,    % Optional #where_clause{} for typeclass constraints on type parameters
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
    type_params,     % List of type parameter atoms for polymorphic types (e.g., ['T'])
    params,          % Constructor parameters
    definition,
    constraint,
    location
}).

%% Record definition
-record(record_def, {
    name,
    type_params,    % optional type parameters [param1, param2, ...]
    fields,
    derive_clause,  % optional #derive_clause{} for automatic instance derivation
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

%% Vector expressions ‹elem1, elem2, ...›
-record(vector_expr, {
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

%% Field access expressions (record.field)
-record(field_access_expr, {
    record,    % Expression evaluating to a record
    field,     % Atom: field name
    location
}).

%% Record update expressions (Record{old | field: value})
-record(record_update_expr, {
    name,      % Record type name
    base,      % Expression for the base record
    fields,    % List of #field_expr{} records
    location
}).

%% String interpolation expressions
-record(string_interpolation_expr, {
    parts,   % List of {string_part, String} | {expr, Expression}
    location
}).

%% Qualified method call (e.g., Trait::method) - Phase 4: Traits
-record(qualified_call_expr, {
    trait_name,      % Optional trait name for disambiguation
    type_args,       % Optional explicit type arguments
    method_name,     % Method name
    receiver,        % Optional receiver expression (for method syntax)
    args,            % Method arguments
    location         % Source location
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

%% Type parameter declaration (for explicit bounds/constraints)
-record(type_param_decl, {
    name,            % Atom: type parameter name (e.g., 'T')
    bounds,          % List of type bounds/constraints (e.g., ['Eq', 'Ord'])
    kind,            % Optional: kind annotation for higher-kinded types
    location
}).

%% Polymorphic type (forall quantification)
-record(poly_type, {
    type_params,     % List of type parameter atoms or #type_param_decl{}
    constraints,     % List of type constraints (for bounded polymorphism)
    body_type,       % The actual type expression
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
               #vector_expr{} |
               #tuple_expr{} |
               #record_expr{} |
               #field_access_expr{} |
               #record_update_expr{} |
               #lambda_expr{} |
               #fsm_spawn_expr{} |
               #fsm_send_expr{} |
               #fsm_receive_expr{} |
               #fsm_state_expr{} |
               #qualified_call_expr{}.  % Phase 4: Trait method calls

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

%% ============================================================================
%% Trait System (Ad-hoc Polymorphism) - Phase 4
%% ============================================================================

%% Trait definition - defines a set of methods that types can implement
%% Similar to type classes in Haskell or traits in Rust
-record(trait_def, {
    name,            % Atom: trait name (e.g., 'Eq', 'Show', 'Ord')
    type_params,     % List of type parameters [atom()] (e.g., ['Self'])
    methods,         % List of #method_signature{} records
    supertraits,     % List of trait names this trait extends (e.g., ['Eq'] for Ord)
    associated_types,% List of #associated_type{} for associated types
    location         % Source location
}).

%% Method signature within a trait
-record(method_signature, {
    name,            % Atom: method name
    type_params,     % Optional additional type parameters for this method
    params,          % List of #param{} - method parameters
    return_type,     % Return type expression
    default_impl,    % Optional default implementation (expr())
    location         % Source location
}).

%% Associated type declaration in trait
-record(associated_type, {
    name,            % Atom: associated type name
    bounds,          % List of trait bounds (optional)
    default,         % Optional default type
    location         % Source location
}).

%% Trait implementation for a specific type
-record(trait_impl, {
    trait_name,      % Atom: name of trait being implemented
    type_params,     % Type parameters for polymorphic implementations
    for_type,        % Type expression this trait is being implemented for
    where_clause,    % Optional where clause for bounds (list of constraints)
    methods,         % List of #method_impl{} - method implementations
    associated_types,% Map of associated type name -> concrete type
    location         % Source location
}).

%% Method implementation within a trait impl
-record(method_impl, {
    name,            % Atom: method name
    params,          % List of #param{}
    return_type,     % Return type (optional, can be inferred from trait)
    body,            % Method body (expr())
    location         % Source location
}).

%% Trait bound/constraint on a type parameter
%% Used in function signatures and trait definitions
-record(trait_bound, {
    type_param,      % Atom: type parameter being constrained
    trait_name,      % Atom: trait that must be implemented
    location         % Source location
}).

%% Where clause for complex trait bounds
-record(where_clause, {
    constraints,     % List of #trait_bound{} or #type_equality{}
    location         % Source location
}).

%% Type equality constraint (e.g., T::Item = U)
-record(type_equality, {
    left,            % Type expression or associated type projection
    right,           % Type expression
    location         % Source location
}).

%% ============================================================================
%% Type Classes (Haskell-style) - Alias for Traits with Different Syntax
%% ============================================================================

%% Typeclass definition - Haskell-style type classes
%% This is an alias/alternative syntax for traits
-record(typeclass_def, {
    name,              % Atom: typeclass name (e.g., 'Show', 'Eq', 'Ord')
    type_params,       % List of type parameter atoms or #type_param_decl{}
    constraints,       % List of superclass constraints (e.g., ['Eq'] for Ord)
    methods,           % List of #method_signature{} records
    default_methods,   % List of #function_def{} with default implementations
    location           % Source location
}).

%% Instance definition - implements a typeclass for a specific type
-record(instance_def, {
    typeclass,         % Atom: typeclass name being implemented
    type_args,         % List of type expressions (e.g., [Int] or [List(T)])
    constraints,       % Context constraints (e.g., [Show(T)] for Show(List(T)))
    methods,           % List of #function_def{} with implementations
    location           % Source location
}).

%% Derive clause - automatic instance derivation
-record(derive_clause, {
    typeclass,         % Atom: first typeclass (for compatibility)
    typeclasses,       % List of atom(): all typeclasses to derive
    for_type,          % Type expression (inferred from record)
    constraints,       % When clause constraints (optional)
    location           % Source location
}).

%% Typeclass constraint (used in function signatures)
%% e.g., "where Show(T), Eq(T)"
-record(typeclass_constraint, {
    typeclass,         % Atom: typeclass name
    type_args,         % List of type expressions
    location           % Source location
}).

%% Typeclass info - runtime representation of a typeclass
-record(typeclass_info, {
    name :: atom(),
    type_params = [] :: [atom()],
    superclasses = [] :: [#typeclass_constraint{}],
    methods = #{} :: #{atom() => term()},
    default_impls = #{} :: #{atom() => #function_def{}},
    kind :: term()  % Kind of the typeclass (e.g., * -> * for Functor)
}).

-type typeclass_info() :: #typeclass_info{}.
-type typeclass_constraint() :: #typeclass_constraint{}.

%% ============================================================================
%% Higher-Kinded Types Support
%% ============================================================================

%% Kind - represents the "type of a type"
-record(kind, {
    constructor :: atom() | term(),  % Base kind or higher-order kind
    args :: [term()],                % Kind arguments
    result :: term() | atom(),       % Result kind
    arity :: integer(),
    location :: term()
}).

%% Type constructor - represents types that take type parameters
-record(type_constructor, {
    name :: atom(),
    kind :: term(),
    params :: [term()],
    definition :: term() | undefined,
    constraints :: [term()],
    location :: term()
}).

-type kind() :: #kind{}.
-type type_constructor() :: #type_constructor{}.

