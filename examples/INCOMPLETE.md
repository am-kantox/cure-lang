# Incomplete Language Features

This document tracks language features that are not yet fully implemented in the Cure compiler, discovered during compilation testing of the example files.

## Compilation Failures

### Pattern Matching Example (`pattern_matching.cure`)

**Status**: ❌ Failed - Lexical Analysis  
**Error**: `{{unexpected_character,38},52,20}` - Character 38 (`&`) at line 52, column 20

**Issues Identified**:
1. **Logical `&&` Operator**: The `&&` (logical AND) operator is not recognized by the lexer
2. **All advanced pattern matching features** are blocked by this lexical issue

### Monadic Pipes Example (`monadic_pipes.cure`) 

**Status**: ❌ Failed - Lexical Analysis  
**Error**: `{{unexpected_character,38},87,34}` - Same `&&` operator issue

### Dependent Types Example (`dependent_types.cure`)

**Status**: ❌ Failed - Lexical Analysis  
**Error**: `{{unexpected_character,38},117,21}` - Same `&&` operator issue

### Finite State Machines Example (`finite_state_machines.cure`)

**Status**: ❌ Failed - Lexical Analysis  
**Error**: `{{unexpected_character,38},511,21}` - Same `&&` operator issue

**Root Cause**: All complex examples fail due to the `&&` logical operator not being implemented in the lexer.

## Language Features Status

### ✅ Working Features (confirmed through testing)
- **Basic module definitions** with `export [function/arity]`
- **Simple function definitions** with typed parameters: `def name(param: Type): ReturnType = expr`
- **Primitive types**: `Int`, `Float`, `String` literals
- **List literals**: `[1, 2, 3, 4, 5]`
- **Tuple literals**: `{10, 20}`, `{"hello", 123, 3.14}`
- **Let bindings**: `let var = expr`
- **Function calls**: `function(args)`
- **Basic arithmetic**: `+`, `-`, `*` operators
- **Built-in functions**: `print/1`
- **Comments**: `# comment text`
- **Block expressions**: Multiple expressions with proper scoping
- **Lexical analysis and parsing** for supported features
- **Type checking** for basic type system
- **Unary operators**: `-5` (negation)

### ❌ Missing/Broken Features
- **Logical operators**: `&&`, `||` (logical AND/OR)
- **If-then-else expressions**: `if condition then expr1 else expr2`
- **Pattern matching**: `match expr do ... end`
- **Guard clauses**: `when condition`
- **Record definitions**: `record Name do ... end`
- **Union types**: `type Name = A | B`
- **Private functions**: `defp name() = ...`
- **Complex type annotations**: Dependent types, refinement types
- **String interpolation**: `"text #{expr}"`
- **Pipe operators**: `|>`
- **FSM definitions**: `fsm Name do ... end`
- **Process definitions**: `process name() do ... end`

### ❓ Unknown Status (needs testing)
- **Case expressions**: `case expr of ... end`
- **Comparison operators**: `==`, `!=`, `<=`, `>=`
- **String concatenation**: `++`
- **List operations**: `::` (cons), pattern matching `[head | tail]`
- **Import statements**: `import Module [...]`
- **Type definitions**: Basic `type` declarations
- **Lambda expressions**: `fn(x) -> expr end`
- **Match expressions**: Alternative to case

## Recommended Approach

1. **Start with minimal working examples** using only confirmed working features
2. **Incrementally add features** one at a time to identify what works
3. **Create simplified versions** that demonstrate core concepts within current limitations
4. **Update this document** as more features are tested

## Testing Priority

1. ✅ Basic logical operators (`and`, `or` instead of `&&`, `||`)
2. ✅ Simple if-then-else expressions
3. ✅ Basic pattern matching
4. ✅ Simple type definitions
5. ⏳ Record definitions
6. ⏳ Function composition
7. ⏳ FSM basic syntax

## Simplified Examples Created

### ✅ Working Examples (compile successfully)
- `examples/simplified/minimal_working.cure` - Absolute minimal example
- `examples/simplified/basic_pattern_matching_simple.cure` - Simple function calls and arithmetic
- `examples/simplified/basic_function_composition.cure` - Manual function composition
- `examples/simplified/basic_types_demo.cure` - Basic types and collections

### ⚠️ Partially Working (parse/typecheck but code generation issues)
- Some examples pass lexical analysis and parsing but fail during BEAM code generation
- This indicates the core language features work but there are backend compilation issues

### 📅 Next Steps
1. **Investigate code generation issues** - Functions compile but BEAM generation fails
2. **Test more operators** - Comparison operators (`>`, `<`, `==`)
3. **Test simple pattern matching** - Basic `match` expressions
4. **Add lexical support for `&&`, `||`** - Would unlock most advanced examples
