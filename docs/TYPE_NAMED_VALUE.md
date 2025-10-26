# NamedValue(T) Type

## Overview

`NamedValue(T)` is a primitive dependent type in Cure that represents a tuple `{Atom, T}` where the first element is an atom (the "name") and the second element is a value of type `T`.

This type is designed for use in data structures like `Map` where key-value pairs need to be represented with named keys.

## Definition

```cure
type NamedValue(T) = {Atom, T}
```

## Syntax

```cure
# Type definition
type Person = NamedValue(String)

# Usage
person: NamedValue(String) = {:john, "John Doe"}
```

## Implementation

### Lexer
- Added `Atom` as a recognized primitive type keyword in `cure_lexer.erl`

### Parser
- Added `Atom` primitive type parsing in `cure_parser.erl`
- `NamedValue(T)` is parsed as a parameterized `dependent_type` with name `'NamedValue'` and one type parameter

### Type System  
- Added `?TYPE_NAMEDVALUE(T)` macro in `cure_types.erl` that expands to `{tuple_type, [{primitive_type, 'Atom'}, T], undefined}`
- Implemented unification rules:
  - `NamedValue(T1)` unifies with `NamedValue(T2)` iff `T1` unifies with `T2`
  - `NamedValue(T)` should unify with tuple type `{Atom, T}` (bridge unification - partially implemented)
- Added `type_to_string` support for pretty-printing `NamedValue(T)` types

### AST
- Uses existing `#dependent_type{}` record with:
  - `name = 'NamedValue'`
  - `params = [#type_param{value = T}]` where `T` is the type parameter

## Status

### Working
✅ Lexing and tokenization of `Atom` and `NamedValue`  
✅ Parsing `NamedValue(T)` as a dependent type  
✅ Unification between `NamedValue(T1)` and `NamedValue(T2)`  
✅ Type parameter extraction  
✅ Type-to-string conversion  

### TODO
❌ Complete bridge unification between `NamedValue(T)` and `{Atom, T}` tuple types
  - Basic pattern is implemented but needs runtime verification
  - May need special handling in the pattern matching order

## Usage Examples

### Basic Usage
```cure
module Example

# Type definition
type Config = NamedValue(String)

# Function using NamedValue
def getConfig(key: Atom): Config = {key, "default_value"}
```

### With Map (Future)
```cure
# When Map is implemented, NamedValue will be used for entries
type Map(K, V) = List(NamedValue(V))  # Simplified representation
```

## Implementation Files

- `/opt/Proyectos/Ammotion/cure/src/lexer/cure_lexer.erl` - Keyword recognition
- `/opt/Proyectos/Ammotion/cure/src/parser/cure_parser.erl` - Type parsing
- `/opt/Proyectos/Ammotion/cure/src/types/cure_types.erl` - Type system and unification
- `/opt/Proyectos/Ammotion/cure/test/namedvalue_test.erl` - Test suite

## Related Types

- `Atom` - Primitive type for atoms
- `{T, U}` - Tuple types
- `Map(K, V)` - (Future) Map type that will use `NamedValue` for entries
