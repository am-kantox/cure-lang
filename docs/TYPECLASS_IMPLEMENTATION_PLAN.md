# Type Classes and Traits System - Implementation Plan

**Status**: In Progress  
**Started**: November 4, 2025  
**Estimated Duration**: 8 weeks

## Overview

This document tracks the implementation of the Type Classes and Traits system for Cure, as outlined in TODO.md section 2. This is a critical feature for 1.0 release.

---

## Phase 1: Lexer & Parser Foundation (Week 1)

### 1.1 Lexer Updates
- [ ] Add keywords: `typeclass`, `instance`, `where` (already exists), `derive`
- [ ] Update `keywords()` map in `src/lexer/cure_lexer.erl`
- [ ] Note: `trait` and `impl` already exist (lines 310-311)

### 1.2 AST Extensions
- [ ] Add `typeclass_def` record to `src/parser/cure_ast.hrl`
- [ ] Add `method_signature` record
- [ ] Add `instance_def` record
- [ ] Add `derive_clause` record
- [ ] Update type exports

### 1.3 Parser Implementation
- [ ] Implement `parse_typeclass_def/1` in `src/parser/cure_parser.erl`
- [ ] Implement `parse_instance_def/1`
- [ ] Implement `parse_derive_clause/1`
- [ ] Implement `parse_function_constraints/1` for `where` clauses
- [ ] Update module item parsing to handle typeclasses and instances

### 1.4 Testing
- [ ] Create `test/typeclass_parser_test.erl`
- [ ] Test parsing typeclass definitions
- [ ] Test parsing instance definitions
- [ ] Test parsing derive clauses
- [ ] Test parsing constrained function signatures

---

## Phase 2: Type System Core (Week 2-3)

### 2.1 Typeclass Environment
- [ ] Create `src/types/cure_typeclass.erl`
- [ ] Implement `typeclass_env` record and infrastructure
- [ ] Implement `new_typeclass_env/0`
- [ ] Implement `register_typeclass/2`
- [ ] Implement `register_instance/2`
- [ ] Implement `lookup_instance/3`
- [ ] Implement `check_instance_coherence/2`
- [ ] Implement `resolve_method/3`

### 2.2 Constraint Resolution
- [ ] Extend `src/types/cure_typechecker.erl` with constraint checking
- [ ] Implement `check_typeclass_constraints/3`
- [ ] Implement `resolve_qualified_call/3`
- [ ] Update type checking to propagate constraints

### 2.3 Instance Search & Overlapping Checks
- [ ] Implement `find_instance/3`
- [ ] Implement `check_overlapping_instances/2`
- [ ] Implement instance unification
- [ ] Handle instance context constraints

### 2.4 Testing
- [ ] Create `test/typeclass_resolution_test.erl`
- [ ] Test constraint resolution
- [ ] Test instance lookup
- [ ] Test overlapping instance detection
- [ ] Test coherence checking

---

## Phase 3: Core Typeclasses (Week 4)

### 3.1 Create Standard Typeclasses
- [ ] Create `lib/std/typeclass.cure`
- [ ] Define `Eq` typeclass
- [ ] Define `Ord` typeclass
- [ ] Define `Show` typeclass
- [ ] Define `Functor` typeclass
- [ ] Define `Applicative` typeclass
- [ ] Define `Monad` typeclass

### 3.2 Built-in Instances
- [ ] Create `lib/std/instances/show.cure`
  - [ ] `Show(Int)` instance
  - [ ] `Show(Bool)` instance
  - [ ] `Show(String)` instance
  - [ ] `Show(List(T))` instance
- [ ] Create `lib/std/instances/eq.cure`
  - [ ] `Eq(Int)` instance
  - [ ] `Eq(Bool)` instance
  - [ ] `Eq(List(T))` instance
- [ ] Create `lib/std/instances/functor.cure`
  - [ ] `Functor(List)` instance
  - [ ] `Functor(Option)` instance

### 3.3 Testing
- [ ] Test all Show instances
- [ ] Test all Eq instances
- [ ] Test Functor instances
- [ ] Test constrained polymorphic functions

---

## Phase 4: Codegen Integration (Week 5)

### 4.1 Method Dispatch
- [ ] Extend `src/codegen/cure_codegen.erl`
- [ ] Implement `compile_qualified_call/3`
- [ ] Implement `compile_instance_def/2`
- [ ] Implement monomorphization for known instances
- [ ] Generate instance modules

### 4.2 Dictionary Passing
- [ ] Implement dictionary passing for polymorphic code
- [ ] Generate dictionary structures
- [ ] Handle dictionary parameters in function calls
- [ ] Optimize dictionary passing when possible

### 4.3 Testing
- [ ] Create `test/typeclass_codegen_test.erl`
- [ ] Test method dispatch codegen
- [ ] Test instance compilation
- [ ] Test dictionary passing
- [ ] Test monomorphization

---

## Phase 5: Automatic Derivation (Week 6)

### 5.1 Derive Mechanism
- [ ] Create `src/types/cure_derive.erl`
- [ ] Implement `derive_instance/4`
- [ ] Implement `derive_show/3` for records
- [ ] Implement `derive_eq/3` for records
- [ ] Implement `derive_ord/3` for records
- [ ] Implement `derive_functor/3` for type constructors

### 5.2 Integration
- [ ] Hook derive mechanism into typechecker
- [ ] Process derive clauses during compilation
- [ ] Generate derived instances

### 5.3 Testing
- [ ] Create `test/typeclass_derive_test.erl`
- [ ] Test derive Show
- [ ] Test derive Eq
- [ ] Test derive Ord
- [ ] Test derive Functor

---

## Phase 6: Comprehensive Testing (Week 7)

### 6.1 Integration Tests
- [ ] Create comprehensive test suite
- [ ] Test end-to-end typeclass usage
- [ ] Test error cases
- [ ] Test edge cases (recursive instances, etc.)

### 6.2 Example Programs
- [ ] Create `examples/08_typeclasses.cure`
- [ ] Create `examples/09_custom_typeclasses.cure`
- [ ] Create `examples/10_functor_monad.cure`

### 6.3 Performance Testing
- [ ] Benchmark method dispatch overhead
- [ ] Benchmark dictionary passing
- [ ] Compare with direct calls

---

## Phase 7: Documentation & Polish (Week 8)

### 7.1 Documentation
- [ ] Update `docs/TYPE_SYSTEM.md` with typeclass section
- [ ] Create `docs/TYPECLASSES.md` comprehensive guide
- [ ] Update `docs/CURE_SYNTAX_GUIDE.md`
- [ ] Update `docs/FEATURE_REFERENCE.md`
- [ ] Update `README.md` with typeclass examples

### 7.2 Error Messages
- [ ] Implement clear "no instance found" errors
- [ ] Implement "overlapping instance" errors
- [ ] Implement "missing method" errors
- [ ] Implement "unsatisfied constraint" errors
- [ ] Add helpful suggestions in error messages

### 7.3 Final Polish
- [ ] Code review and cleanup
- [ ] Performance optimization
- [ ] Final integration testing
- [ ] Update TODO.md to mark feature complete

---

## AST Design

### New Records

```erlang
%% Typeclass definition
-record(typeclass_def, {
    name,              % Atom: typeclass name
    type_params,       % List of type parameters
    constraints,       % Superclass constraints
    methods,           % List of #method_signature{}
    default_methods,   % List of #function_def{} with defaults
    location
}).

%% Method signature in typeclass
-record(method_signature, {
    name,              % Atom: method name
    params,            % List of #param{}
    return_type,       % Type expression
    constraints,       % Additional constraints
    location
}).

%% Instance definition
-record(instance_def, {
    typeclass,         % Atom: typeclass name
    type_args,         % Type expressions being instantiated
    constraints,       % Context constraints
    methods,           % List of #function_def{} implementations
    location
}).

%% Derive clause
-record(derive_clause, {
    typeclass,         % Atom: typeclass to derive
    for_type,          % Type expression
    constraints,       % When clause constraints
    location
}).
```

---

## Key Design Decisions

1. **Syntax**: Use `typeclass`/`instance` (Haskell-style), keep `trait`/`impl` as aliases
2. **Method Resolution**: Compile-time monomorphization with dictionary-passing fallback
3. **Instance Coherence**: Enforce globally unique instances (no orphan instances)
4. **Derivation**: Support automatic derivation for structural types
5. **Integration**: Typeclass constraints compile to additional function parameters

---

## Example Usage

### Defining a Typeclass

```cure
typeclass Show(T) where
  def show(x: T): String
end
```

### Implementing an Instance

```cure
instance Show(Int) where
  def show(x: Int): String = int_to_string(x)
end
```

### Using Constraints

```cure
def debug_print(x: T): Int where Show(T) =
  println(show(x))
  0
```

### Automatic Derivation

```cure
record Person do
  name: String
  age: Int
end

derive Show for Person
```

---

## Progress Tracking

- **Phase 1**: ✅ **COMPLETE** (November 4, 2025)
  - ✅ Added `typeclass`, `instance`, `derive` keywords to lexer
  - ✅ Added AST records for typeclasses, instances, derive clauses, and constraints
  - ✅ Implemented parsing functions for all typeclass constructs
  - ✅ Updated module and top-level item parsing
  - ✅ Parser compiles successfully
  - ⚠️ Integration tests pending (blocked on existing parser token format issues)
- **Phase 2**: ✅ **COMPLETE** (November 4, 2025)
  - ✅ Created `cure_typeclass.erl` module with full environment management
  - ✅ Implemented typeclass registration and lookup
  - ✅ Implemented instance registration with coherence checking
  - ✅ Implemented method resolution
  - ✅ Implemented constraint checking infrastructure
  - ✅ All resolution tests passing
- **Phase 3**: ✅ **COMPLETE** (November 4, 2025)
  - ✅ Created `lib/std/typeclass.cure` with core typeclass definitions
  - ✅ Defined Show, Eq, Ord, Functor, Applicative, Monad typeclasses
  - ✅ Created Show instances for all built-in types
  - ✅ Created Eq instances for all built-in types
  - ✅ Created Functor instances for List, Option, Result
  - ✅ Created comprehensive example program (`examples/08_typeclasses.cure`)
  - ✅ Included helper functions for polymorphic programming
- **Phase 4**: Not started
- **Phase 5**: Not started
- **Phase 6**: Not started
- **Phase 7**: Not started

---

## Notes

- This feature is marked as **CRITICAL** in TODO.md
- Required for 1.0 release
- Builds on existing dependent type system infrastructure
- Will integrate with existing modules in `lib/std/`

---

*Last Updated: November 4, 2025*
