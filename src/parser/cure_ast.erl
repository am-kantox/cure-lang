-moduledoc """
# Cure Programming Language - AST Definitions

This module defines the Abstract Syntax Tree (AST) node types and structure for
the Cure programming language. It provides comprehensive type definitions and
helper functions for creating and manipulating AST nodes throughout the compilation
pipeline.

## Overview

The Cure AST represents the complete syntactic structure of Cure programs including:
- **Programs**: Collections of top-level items
- **Modules**: Module definitions with exports and items
- **Functions**: Function definitions with parameters, return types, and bodies
- **Types**: User-defined types, primitives, and complex type expressions
- **FSMs**: Finite state machine definitions with states and transitions
- **Expressions**: All forms of expressions (literals, function calls, control flow)
- **Patterns**: Pattern matching constructs
- **Location Information**: Source position tracking for error reporting

## AST Structure

### Top-Level Items
Programs consist of top-level items:
- `module_def()` - Module definitions
- `function_def()` - Regular function definitions
- `erlang_function_def()` - Erlang interop functions
- `type_def()` - User-defined type definitions
- `fsm_def()` - Finite state machine definitions
- `import_def()` - Import statements

### Expression Types
Expressions represent computations and values:
- `literal_expr()` - Literals (numbers, strings, atoms)
- `identifier_expr()` - Variable and function names
- `function_call_expr()` - Function calls with arguments
- `binary_op_expr()` - Binary operations (+, -, *, etc.)
- `unary_op_expr()` - Unary operations (-, not)
- `match_expr()` - Pattern matching expressions
- `if_expr()` - Conditional expressions
- `let_expr()` - Let bindings
- `list_expr()` - List literals
- `tuple_expr()` - Tuple literals
- `record_expr()` - Record construction
- `lambda_expr()` - Anonymous functions

### Type System
Type expressions represent Cure's type system:
- `primitive_type()` - Built-in types (Int, String, Bool, etc.)
- `dependent_type()` - Parameterized types with dependencies
- `function_type()` - Function type signatures
- `union_type()` - Union types (T | U)
- `list_type()` - List types
- `tuple_type()` - Tuple types
- `type_param()` - Type parameters for generics

### Pattern Matching
Patterns for destructuring and matching:
- `wildcard_pattern()` - Wildcard patterns (_)
- `literal_pattern()` - Literal value patterns
- `identifier_pattern()` - Variable binding patterns
- `list_pattern()` - List destructuring patterns
- `tuple_pattern()` - Tuple destructuring patterns
- `record_pattern()` - Record field patterns
- `constructor_pattern()` - Constructor patterns (Ok(x), Error(e))

### FSM Support
First-class finite state machine support:
- `fsm_def()` - FSM type definitions
- `state_def()` - Individual state definitions
- `transition()` - State transitions with events, guards, and actions

## Location Tracking

All AST nodes include location information for:
- **Error Reporting**: Precise source locations for compilation errors
- **Debugging**: Source mapping for runtime errors
- **IDE Support**: Language server integration
- **Documentation**: API documentation generation

## Usage Example

```erlang
%% Create a simple function definition
Params = [#param{name = x, type = int_type(), location = Location}],
Body = #literal_expr{value = 42, location = Location},
Function = cure_ast:new_function(identity, Params, int_type(), undefined, Body).

%% Create an FSM definition
States = [idle, running, stopped],
Initial = idle,
StateDefs = [IdleState, RunningState, StoppedState],
FSM = cure_ast:new_fsm(state_machine, States, Initial, StateDefs).
```

## Design Principles

### Immutability
AST nodes are immutable records that can be safely shared and transformed
without side effects.

### Composability
Complex AST structures are built by composing simpler nodes, enabling
modular construction and transformation.

### Location Preservation
Every AST node maintains source location information to support high-quality
error messages and debugging.

### Type Safety
Erlang type specifications ensure AST node integrity and enable static
analysis tools to verify AST manipulation code.

## Integration

This module integrates with:
- **Parser**: Produces AST nodes from token streams
- **Type Checker**: Analyzes and annotates AST with type information
- **Compiler**: Transforms AST through various compilation phases
- **Error Reporter**: Uses location information for error messages

## Performance Considerations

- **Memory Efficient**: Records are lightweight with minimal overhead
- **Copy-on-Write**: Erlang's immutable data structures optimize memory usage
- **Pattern Matching**: Efficient pattern matching on AST node types
- **Location Sharing**: Location records can be shared between related nodes
"""

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
    module_def()
    | function_def()
    | erlang_function_def()
    | type_def()
    | fsm_def()
    | import_def().

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
    % Raw Erlang code as string
    erlang_body :: string(),
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
    literal_expr()
    | identifier_expr()
    | function_call_expr()
    | match_expr()
    | if_expr()
    | let_expr()
    | binary_op_expr()
    | unary_op_expr()
    | list_expr()
    | tuple_expr()
    | record_expr()
    | lambda_expr().

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
    primitive_type()
    | dependent_type()
    | function_type()
    | union_type()
    | list_type()
    | tuple_type().

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
    % Named parameter
    name :: atom() | undefined,
    % Type or value parameter
    value :: type_expr() | expr(),
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
    % For dependent typing
    length :: expr() | undefined,
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
    wildcard_pattern()
    | literal_pattern()
    | identifier_pattern()
    | list_pattern()
    | tuple_pattern()
    | record_pattern().

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
    program/0,
    item/0,
    module_def/0,
    function_def/0,
    erlang_function_def/0,
    type_def/0,
    fsm_def/0,
    import_def/0,
    state_def/0,
    transition/0,
    export_spec/0,
    param/0,
    expr/0,
    literal_expr/0,
    identifier_expr/0,
    function_call_expr/0,
    match_expr/0,
    match_clause/0,
    if_expr/0,
    let_expr/0,
    binding/0,
    binary_op_expr/0,
    unary_op_expr/0,
    list_expr/0,
    tuple_expr/0,
    record_expr/0,
    field_expr/0,
    lambda_expr/0,
    type_expr/0,
    primitive_type/0,
    dependent_type/0,
    type_param/0,
    function_type/0,
    union_type/0,
    list_type/0,
    tuple_type/0,
    pattern/0,
    wildcard_pattern/0,
    literal_pattern/0,
    identifier_pattern/0,
    list_pattern/0,
    tuple_pattern/0,
    record_pattern/0,
    field_pattern/0,
    location/0
]).

%% Helper functions for creating AST nodes

-doc """
Creates a new module definition AST node.

## Arguments
- `Name` - Module name (atom)
- `Exports` - List of export specifications
- `Items` - List of top-level items in the module
- `Location` - Source location information

## Returns
- `module_def()` - Module definition AST node

## Example
```erlang
Exports = [#export_spec{name = hello, arity = 1, location = Loc}],
Items = [FunctionDef],
Module = cure_ast:new_module('MyModule', Exports, Items, Location).
```
"""
-spec new_module(atom(), [export_spec()], [item()], location()) -> module_def().
new_module(Name, Exports, Items, Location) ->
    #module_def{
        name = Name,
        exports = Exports,
        items = Items,
        location = Location
    }.

-doc """
Creates a new function definition AST node.

## Arguments
- `Name` - Function name (atom)
- `Params` - List of function parameters
- `ReturnType` - Return type expression (undefined if not specified)
- `Constraint` - Optional constraint expression for the function
- `Body` - Function body expression

## Returns
- `function_def()` - Function definition AST node

## Example
```erlang
Params = [#param{name = x, type = IntType, location = Loc}],
Body = #literal_expr{value = 42, location = Loc},
Function = cure_ast:new_function(identity, Params, IntType, undefined, Body).
```

## Note
This helper function uses a default location. For proper location tracking,
construct the record directly with accurate location information.
"""
-spec new_function(
    atom(),
    [param()],
    type_expr() | undefined,
    expr() | undefined,
    expr()
) -> function_def().
new_function(Name, Params, ReturnType, Constraint, Body) ->
    #function_def{
        name = Name,
        params = Params,
        return_type = ReturnType,
        constraint = Constraint,
        body = Body,
        % TODO: proper location
        location = #location{line = 0, column = 0}
    }.

-doc """
Creates a new type definition AST node.

## Arguments
- `Name` - Type name (atom)
- `Params` - List of type parameter names
- `Definition` - Type expression defining the type

## Returns
- `type_def()` - Type definition AST node

## Example
```erlang
Params = [t],
Definition = #union_type{types = [IntType, StringType], location = Loc},
TypeDef = cure_ast:new_type_def('Maybe', Params, Definition).
```

## Note
This helper function uses a default location. For proper location tracking,
construct the record directly with accurate location information.
"""
-spec new_type_def(atom(), [atom()], type_expr()) -> type_def().
new_type_def(Name, Params, Definition) ->
    #type_def{
        name = Name,
        params = Params,
        definition = Definition,
        % TODO: proper location
        location = #location{line = 0, column = 0}
    }.

-doc """
Creates a new FSM definition AST node.

## Arguments
- `Name` - FSM name (atom)
- `States` - List of state names
- `Initial` - Initial state name
- `StateDefs` - List of state definitions with transitions

## Returns
- `fsm_def()` - FSM definition AST node

## Example
```erlang
States = [idle, running, stopped],
StateDefs = [IdleState, RunningState, StoppedState],
FSM = cure_ast:new_fsm(counter, States, idle, StateDefs).
```

## Note
This helper function uses a default location. For proper location tracking,
construct the record directly with accurate location information.
"""
-spec new_fsm(atom(), [atom()], atom(), [state_def()]) -> fsm_def().
new_fsm(Name, States, Initial, StateDefs) ->
    #fsm_def{
        name = Name,
        states = States,
        initial = Initial,
        state_defs = StateDefs,
        % TODO: proper location
        location = #location{line = 0, column = 0}
    }.

-doc """
Creates a new expression AST node with location information.

## Arguments
- `Type` - Expression type (literal, identifier, etc.)
- `Data` - Expression data appropriate for the type
- `Location` - Source location information

## Returns
- `expr()` - Expression AST node
- `error({unknown_expr_type, Type, Data, Location})` - Unknown expression type

## Supported Types
- `literal` - Creates a literal expression from the value
- `identifier` - Creates an identifier expression from the name

## Example
```erlang
Literal = cure_ast:new_expr(literal, 42, Location),
Identifier = cure_ast:new_expr(identifier, variable_name, Location).
```

## Note
This is a limited helper function that only supports basic expression types.
For complex expressions, construct the records directly.
"""
-spec new_expr(atom(), term(), location()) -> expr().
new_expr(literal, Value, Location) ->
    #literal_expr{value = Value, location = Location};
new_expr(identifier, Name, Location) ->
    #identifier_expr{name = Name, location = Location};
new_expr(Type, Data, Location) ->
    error({unknown_expr_type, Type, Data, Location}).
