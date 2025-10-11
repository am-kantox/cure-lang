%% Cure Standard Library - Main Module (Temporary Erlang Implementation)
%% This re-exports functions from various standard library modules
-module('Std').

-moduledoc """
# Cure Standard Library - Main Module

This module serves as the primary entry point for Cure's standard library,
re-exporting functions from specialized modules like Std.List. It provides
a unified interface for importing standard library functionality into
Cure programs.

## Architecture

This is a temporary Erlang implementation that bridges the gap while the
full Cure standard library is being developed. The actual standard library
is implemented in lib/std/ as pure Cure code, but this module provides
runtime compatibility for compiled programs.

### Re-export Pattern
Functions are re-exported by delegation to their actual implementation
modules, maintaining a clean namespace while allowing specialized
implementation in dedicated modules.

## Available Functions

### List Processing
All list functions are delegated to 'Std.List' module:
- `map/2` - Transform list elements
- `filter/2` - Select list elements based on predicate
- `fold/3`, `foldl/3`, `foldr/3` - Reduce lists to single values
- `zip_with/3` - Combine two lists with a function
- `head/1`, `tail/1` - List access functions
- `length/1`, `reverse/1` - List utilities
- `find/2` - Search for elements

### Type Constructors
Placeholder functions for Cure type system compatibility:
- `'List'/1` - List type constructor
- `'Result'/2` - Result type constructor

## Usage in Cure

```cure
import Std [map, filter, List, Result]

// Use imported functions
let doubled = map(numbers, fn x -> x * 2 end)
let evens = filter(numbers, fn x -> x % 2 == 0 end)
```

## Implementation Status

- **Current**: Erlang re-export module for compatibility
- **Future**: Direct Cure implementation in lib/std.cure
- **Migration**: Gradual transition to pure Cure implementation

## Dependencies

This module depends on:
- `'Std.List'` - List processing implementation
- Future: Additional Std.* modules for other domains

## Error Handling

All error handling is delegated to the underlying implementation modules.
Refer to specific module documentation for error semantics.
""".

%% Re-export list functions from Std.List
-export([
    % List functions
    zip_with/3,
    fold/3,
    map/2,
    filter/2,
    head/1,
    tail/1,
    length/1,
    reverse/1,
    find/2,
    foldl/3,
    foldr/3,

    % Types (for import compatibility) - these are just dummy functions
    % In real Cure, these would be type constructors
    'List'/1,
    'Result'/2
]).

%% Re-export list functions by delegating to Std.List
zip_with(List1, List2, Fun) ->
    'Std.List':zip_with(List1, List2, Fun).

fold(List, Acc, Fun) ->
    'Std.List':fold(List, Acc, Fun).

map(Fun, List) ->
    'Std.List':map(Fun, List).

filter(Pred, List) ->
    'Std.List':filter(Pred, List).

head(List) ->
    'Std.List':head(List).

tail(List) ->
    'Std.List':tail(List).

length(List) ->
    'Std.List':length(List).

reverse(List) ->
    'Std.List':reverse(List).

find(Pred, List) ->
    'Std.List':find(Pred, List).

foldl(Fun, Acc, List) ->
    'Std.List':foldl(Fun, Acc, List).

foldr(Fun, Acc, List) ->
    'Std.List':foldr(Fun, Acc, List).

%% Type constructor dummies (these don't do anything at runtime)
'List'(_ElementType) ->
    list.

'Result'(_OkType, _ErrorType) ->
    result.
