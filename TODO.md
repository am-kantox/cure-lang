# Cure Programming Language - TODO List

**Last Updated**: October 31, 2025

This document tracks missing features, planned improvements, and known issues in the Cure programming language implementation.

---

## 🔴 Critical Missing Features

### 1. Pipe Operator `|>` Implementation
**Status**: Parser recognizes it, but needs proper implementation

**Current State**:
- Parser has `|>` defined in `get_operator_info` with precedence 1
- Codegen treats it as "monadic pipe" with special `monadic_pipe_call` instruction
- Implementation appears to wrap results in `Ok()` automatically

**Issues**:
- Not clear if it works as a simple function composition pipe
- Documentation shows it being used in examples but unclear if it's fully working
- May be conflating simple pipe with monadic/error-handling pipe

**Required Work**:
- [ ] Verify current `|>` operator behavior with tests
- [ ] Decide: simple pipe (`x |> f` = `f(x)`) vs monadic pipe (auto-wrapping)
- [ ] Implement simple left-to-right function composition if not working
- [ ] Add comprehensive tests for pipe operator
- [ ] Document pipe operator behavior clearly
- [ ] Add examples showing pipe operator usage

**Files to modify**:
- `src/parser/cure_parser.erl` (line 2859: pipe operator parsing)
- `src/codegen/cure_codegen.erl` (lines 1505-1548: monadic pipe implementation)
- Add tests in `test/pipe_operator_test.erl`

---

## 🟠 High Priority Language Features

### 2. Type Classes and Traits System
**Status**: Planned but not implemented

**Current State**:
- Type system has `{typeclass_constraint, ClassName, TypeArgs}` representation
- Parser does **not** recognize `typeclass` or `instance` keywords
- `Std.Show` exists as a module but not as a trait/typeclass
- No polymorphic `show/1` function - each type needs its own implementation

**Required Work**:
- [ ] Add `typeclass` and `instance` keywords to lexer
- [ ] Implement typeclass definition parsing
- [ ] Implement instance declaration parsing
- [ ] Add typeclass constraint checking to type system
- [ ] Implement method resolution for typeclass instances
- [ ] Create core typeclasses:
  - `Show(T)` - string conversion
  - `Eq(T)` - equality comparison
  - `Ord(T)` - ordering comparison
  - `Functor(F)` - map operation
  - `Monad(M)` - bind operation
- [ ] Implement automatic deriving for common types
- [ ] Add typeclass constraint syntax in function signatures

**Example Implementation**:
```cure
typeclass Show(T) where
  def show(x: T): String
end

instance Show(Int) where
  def show(x: Int): String = int_to_string(x)
end

instance Show(Bool) where
  def show(x: Bool): String =
    match x do
      true -> "true"
      false -> "false"
    end
end

# Generic function using typeclass constraint
def debug_print(x: T): Int where Show(T) =
  println(show(x))
  0
```

**Files to modify**:
- `src/lexer/cure_lexer.erl` - Add typeclass/instance keywords
- `src/parser/cure_parser.erl` - Parse typeclass definitions
- `src/types/cure_typechecker.erl` - Typeclass constraint checking
- `src/codegen/cure_codegen.erl` - Method dispatch codegen
- Create `test/typeclass_test.erl`

---

### 3. Control Flow - `if-then-else` Expressions
**Status**: **NOT IMPLEMENTED** despite appearing in documentation

**Current State**:
- Documentation shows `if-then-else` syntax in multiple places
- Parser does **not** support `if-then-else`
- All conditionals must use `match` expressions
- Comments in code suggest `if` was intentionally removed or never implemented

**Required Work**:
Option A: Implement `if-then-else`
- [ ] Add `if`, `then`, `else` as keywords to lexer
- [ ] Add parser support for if expressions
- [ ] Add codegen support for if expressions
- [ ] Update all documentation to show working syntax

Option B: Keep `match`-only (RECOMMENDED)
- [ ] Explicitly document that `if-then-else` is not supported
- [ ] Provide clear migration patterns from if to match
- [ ] Update all docs that incorrectly show if-then-else
- [ ] Add linter warning if future code tries to use if

**Decision needed**: Choose Option A or B and implement consistently

---

### 4. Advanced FSM Syntax - Guards and Actions
**Status**: Planned but not implemented

**Current State**:
- FSM uses simple arrow syntax: `State1 --> |event| State2`
- Old-style syntax with `state Name do ... end` is parsed but may not work
- No support for guards in transitions
- No support for actions on transitions

**Planned Syntax**:
```cure
fsm Counter(max: Int) do
  states: [Zero, Counting(n: Int) where 0 < n <= max]
  initial: Zero
  
  state Zero do
    event(:increment) -> Counting(1)
  end
  
  state Counting(n) do
    event(:increment) when n < max -> Counting(n + 1)
    event(:decrement) when n > 1 -> Counting(n - 1)
    event(:decrement) when n == 1 -> Zero
    event(:reset) -> Zero
  end
end
```

**Required Work**:
- [ ] Decide on final FSM syntax (arrow-only vs state-do-end)
- [ ] Implement guard expressions in FSM transitions
- [ ] Implement action expressions on state changes
- [ ] Add compile-time exhaustiveness checking for FSM events
- [ ] Support dependent types in FSM state parameters
- [ ] Generate better error messages for FSM misuse
- [ ] Add FSM verification tests

**Files to modify**:
- `src/parser/cure_parser.erl` (lines 899-1100: FSM parsing)
- `src/fsm/cure_fsm_runtime.erl` - Runtime support for guards
- `src/codegen/cure_action_compiler.erl` - Action compilation
- `src/codegen/cure_guard_compiler.erl` - Guard compilation

---

### 5. String Interpolation
**Status**: AST exists, implementation unclear

**Current State**:
- `#string_interpolation_expr{}` exists in AST
- Parser may not fully support it
- Codegen has `compile_string_interpolation` function

**Required Work**:
- [ ] Verify if string interpolation works
- [ ] Add syntax: `"Hello, #{name}!"` or similar
- [ ] Test with all expression types inside interpolation
- [ ] Document string interpolation syntax
- [ ] Add comprehensive tests

---

## 🟡 Medium Priority Features

### 6. List Operations - Restore Commented Functions
**Status**: Functions exist but commented out

**Current State**:
In `lib/std/list.cure`, these functions are commented:
- `nth/3` - Get element at index with default
- `take/2` - Take first n elements
- `drop/2` - Drop first n elements

**Issue**: The `drop` function used `if-then-else` which doesn't exist

**Required Work**:
- [ ] Rewrite `nth`, `take`, `drop` using `match` instead of `if`
- [ ] Uncomment and test these functions
- [ ] Add to export list
- [ ] Add tests for these functions

**Example fix for `drop`**:
```cure
def drop(list: List(T), n: Int): List(T) =
  match n do
    x when x <= 0 -> list
    _ ->
      match list do
        [] -> []
        [_ | t] -> drop(t, n - 1)
      end
  end
```

---

### 7. Refinement Type Syntax
**Status**: Internal representation exists, user syntax unclear

**Current State**:
- Type system has `{refined_type, BaseType, Predicate}` tuples
- Documentation shows `{x: BaseType | Predicate(x)}` syntax
- Parser likely doesn't support this syntax

**Required Work**:
- [ ] Implement parsing for refinement type syntax
- [ ] Add syntax for inline refinements: `def f(x: Int where x > 0): Int`
- [ ] Add syntax for type aliases: `type Pos = {x: Int | x > 0}`
- [ ] Connect refinement predicates to SMT solver
- [ ] Generate runtime checks when SMT can't prove
- [ ] Add comprehensive tests

---

### 8. Lambda Expressions
**Status**: Exists but needs verification

**Current State**:
- `#lambda_expr{}` exists in AST
- Syntax: `fn(x) -> x * 2 end`
- Codegen has `compile_lambda_expr`

**Required Work**:
- [ ] Verify lambdas work correctly
- [ ] Test lambda closures (capturing variables)
- [ ] Test nested lambdas
- [ ] Test lambdas with multiple parameters
- [ ] Add type inference for lambda parameters
- [ ] Document lambda syntax and limitations

---

### 9. Record Field Access and Update
**Status**: Implemented but no examples

**Current State**:
- Parser supports `record.field` syntax (field access)
- Parser supports `Record{base | field: value}` syntax (update)
- Codegen implementations exist
- **No example files** demonstrating these features

**Required Work**:
- [ ] Create example file demonstrating field access
- [ ] Create example file demonstrating record update
- [ ] Test chained field access: `record.field1.field2`
- [ ] Test updating multiple fields
- [ ] Add to standard library if useful
- [ ] Document in language spec

**Example to create**:
```cure
# examples/07_record_operations.cure
record Point do
  x: Float
  y: Float
end

def demo_field_access(): Float =
  let p = Point{x: 3.0, y: 4.0}
  p.x  # Direct field access

def demo_record_update(): Point =
  let p1 = Point{x: 1.0, y: 2.0}
  Point{p1 | x: 5.0}  # Update x field
```

---

### 10. Modulo Operator `%`
**Status**: Parser recognizes it, needs verification

**Current State**:
- `%` appears in operator precedence (line 2855)
- Used in examples (FizzBuzz in pattern_guards.cure)
- May be compiled to `rem` in Erlang

**Required Work**:
- [ ] Verify `%` operator works
- [ ] Test with negative numbers
- [ ] Document behavior (truncated vs floored division)
- [ ] Ensure consistency with Erlang `rem`

---

### 11. Tuple Pattern Matching
**Status**: Exists but needs verification

**Current State**:
- `parse_tuple_pattern/1` exists in parser
- Tuple expressions work: `{1, 2, 3}`
- Pattern matching on tuples used in examples

**Required Work**:
- [ ] Verify tuple patterns work in all contexts
- [ ] Test nested tuple patterns
- [ ] Test tuple patterns with guards
- [ ] Document tuple syntax completely

---

## 🟢 Low Priority / Nice to Have

### 12. Standard Library Completeness

**Missing Modules**:
- [ ] `Std.Concurrent` - Concurrency primitives
- [ ] `Std.Json` - JSON parsing/serialization
- [ ] `Std.Http` - HTTP client/server
- [ ] `Std.Crypto` - Cryptographic functions
- [ ] `Std.Test` - Testing framework
- [ ] `Std.File` - File I/O operations
- [ ] `Std.Process` - Process management

**Incomplete Modules**:
- [ ] `Std.Math` - Needs implementations for most functions
- [ ] `Std.String` - Many functions need implementation
- [ ] `Std.Result` - Currently simplified to Int-based

---

### 13. CLI Integration

**Missing CLI Options**:
- [ ] `--smt-solver [z3|cvc5]` - Choose SMT solver
- [ ] `--smt-timeout <ms>` - Set SMT timeout
- [ ] `--no-smt` - Disable SMT solving
- [ ] `--emit-ast` - Output AST for debugging
- [ ] `--emit-typed-ast` - Output typed AST
- [ ] `--format` - Format Cure source files
- [ ] `--check` - Type check without compiling
- [ ] `--explain <error-code>` - Explain error codes

**Required Work**:
- [ ] Add CLI flag parsing for SMT options
- [ ] Wire SMT solver into compilation pipeline
- [ ] Add flags for intermediate output (AST, typed AST, etc.)
- [ ] Create formatter for Cure source code
- [ ] Implement check-only mode

**Files to modify**:
- `src/cure_cli.erl` - Add new CLI options

---

### 14. Effect System
**Status**: Not implemented

**Potential Syntax**:
```cure
def read_file(path: String): String ! IO =
  # Function that performs IO
  
def pure_computation(x: Int): Int ! Pure =
  # Pure function, no effects
```

**Required Work**:
- [ ] Design effect system
- [ ] Add effect tracking to type system
- [ ] Implement effect inference
- [ ] Add effect annotations to stdlib
- [ ] Document effect system

---

### 15. Macro System
**Status**: Not implemented

**Required Work**:
- [ ] Design macro syntax
- [ ] Implement macro expansion phase
- [ ] Add hygiene system
- [ ] Create macro utilities
- [ ] Document macro system

---

### 16. Package Manager
**Status**: Not implemented

**Required Work**:
- [ ] Design package format
- [ ] Create package registry
- [ ] Implement dependency resolution
- [ ] Add versioning support
- [ ] Create `cure install`, `cure publish` commands

---

## 📋 Documentation Tasks

### 17. Documentation Inconsistencies Fixed

**Recently Updated** (October 31, 2025):
- ✅ Updated all `if-then-else` to `match` expressions
- ✅ Updated string concatenation from `++` to `<>`
- ✅ Updated FSM syntax to arrow-based transitions
- ✅ Removed references to non-existent example files
- ✅ Fixed function signature syntax (`:` for return types)
- ✅ Added "Last Updated" dates to all docs

**Still Needed**:
- [ ] Create comprehensive CONTRIBUTING.md
- [ ] Add architecture diagrams
- [ ] Create video tutorials
- [ ] Write blog posts about features
- [ ] Create interactive tutorials

---

## 🧪 Testing Gaps

### 18. Test Coverage Improvements

**Missing Test Categories**:
- [ ] Pipe operator comprehensive tests
- [ ] Lambda expression tests
- [ ] Record field access/update tests
- [ ] String interpolation tests
- [ ] Modulo operator tests
- [ ] Negative number handling tests
- [ ] Unicode string handling tests
- [ ] Large file compilation tests (>10K lines)
- [ ] Concurrent compilation tests
- [ ] Memory leak tests

**Required Work**:
- [ ] Create test files for each missing category
- [ ] Add property-based testing
- [ ] Add fuzzing tests
- [ ] Add benchmark suite
- [ ] Create regression test suite

---

## 🐛 Known Issues

### 19. Type System Issues

**Current Issues**:
- [ ] Currying in `fold/3` and `zip_with/3` is non-standard
  - Current: `fn(x) -> fn(acc) -> x + acc end end`
  - Expected: `fn(x, acc) -> x + acc end`
- [ ] Type inference may not work for all expressions
- [ ] Dependent type verification may be incomplete
- [ ] SMT solver integration not exposed in compilation pipeline

---

### 20. Parser Issues

**Known Limitations**:
- [ ] Error recovery could be improved
- [ ] Some error messages are unclear
- [ ] Parser performance for large files
- [ ] Backtracking in record update parsing

---

### 21. Codegen Issues

**Known Issues**:
- [ ] Generated code may not be optimized
- [ ] Debug info generation incomplete
- [ ] Some BEAM instructions may be suboptimal

---

## 🚀 Performance Optimizations

### 22. Compiler Performance

**Optimization Opportunities**:
- [ ] Parallel compilation of independent modules
- [ ] Incremental compilation (only recompile changed)
- [ ] Caching of type checking results
- [ ] Faster parser implementation
- [ ] Optimize type inference algorithm

---

### 23. Runtime Performance

**Optimization Opportunities**:
- [ ] Tail call optimization verification
- [ ] Better inlining heuristics
- [ ] Specialization of hot functions
- [ ] Pattern matching compilation optimization

---

## 🔧 Tooling

### 24. Development Tools

**Missing Tools**:
- [ ] Language Server Protocol (LSP) implementation
- [ ] Syntax highlighting for popular editors
- [ ] Debugger integration
- [ ] REPL (Read-Eval-Print Loop)
- [ ] Code formatter
- [ ] Linter
- [ ] Documentation generator
- [ ] Profiler

---

## 🏗️ Infrastructure

### 25. Build System Improvements

**Required Work**:
- [ ] Proper dependency tracking
- [ ] Parallel builds
- [ ] Build caching
- [ ] Cross-compilation support
- [ ] Release packaging

---

### 26. CI/CD

**Required Work**:
- [ ] GitHub Actions workflows
- [ ] Automated testing on multiple platforms
- [ ] Automated documentation deployment
- [ ] Release automation
- [ ] Performance benchmarking in CI

---

## 📊 Priority Matrix

### Must Have (Before 1.0)
1. ✅ Basic compilation pipeline - **DONE**
2. ✅ FSM support - **DONE** 
3. ✅ Module system - **DONE**
4. 🔴 Pipe operator - **IN PROGRESS**
5. 🔴 Type classes/traits - **CRITICAL**
6. 🟠 Control flow decision (if vs match only) - **NEEDED**

### Should Have (1.x releases)
1. Lambda expressions verification
2. Record operations examples
3. CLI SMT integration
4. Refinement type syntax
5. Complete standard library
6. LSP implementation

### Nice to Have (2.x releases)
1. Effect system
2. Macro system
3. Package manager
4. Visual FSM tools
5. REPL
6. Advanced optimizations

---

## 📝 Contributing

When working on items from this TODO list:

1. **Check current status** - Item may be partially implemented
2. **Write tests first** - Ensure feature is testable
3. **Update documentation** - Keep docs in sync with code
4. **Add examples** - Show feature usage
5. **Update this TODO** - Mark items as complete or in progress

---

## 🏁 Completion Tracking

**Implemented Features**: ~85%
- ✅ Lexer, Parser, Type System
- ✅ FSM Runtime
- ✅ Code Generation
- ✅ Module System
- ✅ Standard Library (basic)
- ✅ CLI (basic)

**Missing Critical Features**: ~15%
- 🔴 Pipe operator (partial)
- 🔴 Type classes/traits
- 🔴 Some control flow features

**Overall Status**: **Production Ready for Core Features**, **Beta for Advanced Features**

---

*Last Updated: October 31, 2025*
*Next Review: When starting new feature development*
