# Typeclass Specifications

This directory contains **specification files** for Cure's typeclass system using future syntax. These files use syntax extensions that are not yet supported by the current parser.

## Purpose

These files serve as:
1. **Documentation** - Showing the intended syntax and structure of typeclasses
2. **Specifications** - Defining the future standard library typeclass interface
3. **Reference** - Examples for future typeclass implementations
4. **Design Documents** - Guiding implementation of parser extensions

## Files

- `typeclass.cure` - Core typeclass definitions (Show, Eq, Ord, Functor, Applicative, Monad)
- `eq.cure` - Eq instances for built-in types  
- `show.cure` - Show instances for built-in types
- `functor.cure` - Functor instances for containers

## Why Not in lib/std?

These files use syntax features not yet implemented:
1. **Export list syntax** - `export [Typeclass1, Typeclass2]` (parser expects `do`)
2. **Operator symbols** - Dollar sign operators like `<$`, `$>` (lexer doesn't support `$`)
3. **Advanced where clauses** - Multiple constraints like `where Eq(T), Show(T)`
4. **Higher-kinded types** - `Functor(F)` where F is a type constructor

The standard library compilation process (`make stdlib`) compiles all `.cure` files in `lib/std/` to BEAM bytecode. Until the parser is extended to support these features, keeping these files separate prevents build failures.

## Implementation Status

### Completed ✅
- **Parser support** - Basic typeclass/instance syntax parses correctly
- **Type system** - Typeclass registration and resolution works 
- **Derivation** - Automatic instance derivation implemented
- **Codegen** - Full BEAM code generation implemented
  - Typeclasses compile to behaviour modules with `behaviour_info/1`
  - Instances compile to mangled Erlang functions  
  - Default methods compile to actual BEAM code
  - Proper state threading throughout compilation

### In Progress ⏳  
- **Parser extensions** - Support for operator symbols and advanced syntax
- **Runtime** - Instance dispatch and method calls
- **Standard library** - Implementing Show, Eq, Ord using working syntax

## Next Steps

1. **Parser Extensions**: Add support for `$` in operators and export list syntax
2. **Simplified Typeclasses**: Create working versions using current syntax
3. **Runtime Integration**: Complete instance method dispatch
4. **Migration**: Once syntax is supported, move files to `lib/std/`

See `docs/TYPECLASS_IMPLEMENTATION_STATUS.md` for complete implementation details.
