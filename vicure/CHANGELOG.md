# Vicure Changelog

## [2025-01-05] - Modern Cure Support

### Added

#### Syntax Highlighting
- **Typeclass Keywords**: `typeclass`, `class` for Haskell-style type classes
- **Trait Keywords**: `trait`, `impl` for Rust-style traits
- **Instance Keywords**: `instance` for typeclass instances
- **Derive Keyword**: `derive` for automatic instance derivation
- **Curify Keyword**: `curify` for wrapping Erlang functions
- **Where Keyword**: `where` for typeclass constraints
- **For Keyword**: `for` in trait implementations

#### Pattern Matching
- Typeclass names after `typeclass`, `trait`, and `class` keywords
- Instance/implementation names after `instance` and `impl` keywords
- Function definitions with `curify` keyword
- Proper highlighting for generic type constraints

#### Color Scheme Integration
- Typeclasses/Traits use `Structure` highlight group (similar to interfaces)
- Instance/impl keywords use `Special` highlight group for emphasis
- Maintains consistency with existing Cure syntax

### Modified

#### Indentation Rules
- Added automatic indentation for `typeclass...end` blocks
- Added automatic indentation for `trait...end` blocks
- Added automatic indentation for `instance...end` blocks
- Added automatic indentation for `impl...end` blocks
- Added support for `curify` function definitions

#### Documentation
- Updated `NEOVIM_PLUGIN.md` with modern features
- Added comprehensive examples showing:
  - Record definitions with fields
  - Typeclass definitions with methods
  - Instance implementations
  - Generic functions with `where` clauses
  - Curify declarations for Erlang interop
- Updated feature list to include all modern constructs

### Test Files
- Added `test_syntax.cure` - comprehensive test file demonstrating:
  - Record definitions
  - Typeclass and trait definitions
  - Instance and impl blocks
  - Generic functions with constraints
  - FSM definitions
  - Curify declarations
  - Pattern matching
  - String interpolation
  - All operators and keywords

## [Previous] - Initial Release

### Added
- Basic syntax highlighting for Cure language
- Keywords: `def`, `module`, `fsm`, `state`, `match`, `when`, etc.
- Operators: `->`, `|>`, `::`, arithmetic and comparison
- String literals with interpolation support
- Numeric literals (integers and floats)
- Comments with TODO/FIXME highlighting
- Atoms (`:symbol` and `'quoted'`)
- Type annotations and constructors
- FSM-specific constructs

### Features
- Automatic indentation for blocks
- Filetype detection for `.cure` files
- Compatible with standard Vim color schemes
