# Typeclass Specifications

This directory contains **specification files** for Cure's typeclass system. These files define the structure and instances of typeclasses but are **not meant to be compiled** as regular Cure modules.

## Purpose

These files serve as:
1. **Documentation** - Showing how typeclasses are defined and used
2. **Specifications** - Defining the standard library typeclass interface
3. **Reference** - Examples for implementing custom typeclasses

## Files

- `typeclass.cure` - Core typeclass definitions (Show, Eq, Ord, Functor, Applicative, Monad)
- `instances/show.cure` - Show instances for built-in types
- `instances/eq.cure` - Eq instances for built-in types
- `instances/functor.cure` - Functor instances for containers

## Why Not in lib/std?

The standard library compilation process (`make stdlib`) attempts to compile all `.cure` files in `lib/std/` to BEAM bytecode. However, typeclass definitions and instances require special compiler support that is still being integrated. Moving these files here prevents compilation failures while preserving the specifications for future use.

## Future Work

Once the typeclass system is fully integrated with the BEAM code generator, these files can be moved back to `lib/std/` and will compile to proper BEAM modules that can be imported and used in Cure programs.

## Current Status

- ✅ **Parser support** - Typeclasses parse correctly
- ✅ **Type system** - Typeclass registration and resolution works
- ✅ **Derivation** - Automatic instance derivation implemented
- ⏳ **Codegen** - Full BEAM code generation in progress
- ⏳ **Runtime** - Instance dispatch and method calls being implemented

See `docs/TYPECLASS_IMPLEMENTATION_STATUS.md` for complete details.
