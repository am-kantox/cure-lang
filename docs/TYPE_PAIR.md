# Pair(KT, VT) Type

## Overview

`Pair(KT, VT)` is a primitive dependent type in Cure that represents a tuple `{KT, VT}` where the first element is the key type and the second element is the value type.

This type is designed for use in data structures like `Map` where key-value pairs need to be represented.

## Definition

```cure
type Pair(KT, VT) = {KT, VT}
```

## Syntax

```cure
# Type definition
type Entry = Pair(String, Int)

# Usage
entry: Pair(String, Int) = {"age", 25}
```

## Implementation

### Lexer
- Added `Atom` as a recognized primitive type keyword in `cure_lexer.erl`

### Parser
- `Pair(KT, VT)` is parsed as a parameterized `dependent_type` with name `'Pair'` and two type parameters

### Type System  
- Added `?TYPE_PAIR(KT, VT)` macro in `cure_types.erl` that expands to `{tuple_type, [KT, VT], undefined}`
- Implemented unification rules:
  - `Pair(KT1, VT1)` unifies with `Pair(KT2, VT2)` iff `KT1` unifies with `KT2` and `VT1` unifies with `VT2`
  - `Pair(KT, VT)` unifies with tuple type `{KT, VT}` (bridge unification - fully implemented)
- Added `type_to_string` support for pretty-printing `Pair(KT, VT)` types

### AST
- Uses existing `#dependent_type{}` record with:
  - `name = 'Pair'`
  - `params = [#type_param{value = KT}, #type_param{value = VT}]` where `KT` is the key type and `VT` is the value type

## Status

### Working
✅ Parsing `Pair(KT, VT)` as a dependent type  
✅ Unification between `Pair(KT1, VT1)` and `Pair(KT2, VT2)`  
✅ Bridge unification between `Pair(KT, VT)` and `{KT, VT}` tuple types
✅ Type parameter extraction  
✅ Type-to-string conversion

## Usage Examples

### Basic Usage
```cure
module Example

# Type definition
type Entry = Pair(String, Int)

# Function using Pair
def createEntry(key: String, value: Int): Entry = {key, value}
```

### With Map (Future)
```cure
# When Map is implemented, Pair will be used for entries
type Map(K, V) = List(Pair(K, V))  # Simplified representation
```

## Implementation Files

- `/opt/Proyectos/Ammotion/cure/src/parser/cure_parser.erl` - Type parsing
- `/opt/Proyectos/Ammotion/cure/src/types/cure_types.erl` - Type system and unification
- `/opt/Proyectos/Ammotion/cure/test/pair_test.erl` - Test suite

## Related Types

- `{T, U}` - Tuple types
- `Map(K, V)` - (Future) Map type that will use `Pair` for entries
