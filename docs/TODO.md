# Cure Language TODO List

This document lists all features, functions, and components that are not yet fully implemented in the Cure programming language compiler and runtime.

**Generated**: 2025-10-28  
**Source**: Automated scan of codebase for TODO, FIXME, Placeholder, stub markers

---

## Table of Contents

1. [Parser & AST](#parser--ast)
2. [Type System & Checker](#type-system--checker)
3. [Type Optimizer & Monomorphization](#type-optimizer--monomorphization)
4. [Code Generation](#code-generation)
5. [LSP (Language Server Protocol)](#lsp-language-server-protocol)
6. [SMT Solver](#smt-solver)
7. [CLI & Tooling](#cli--tooling)
8. [Runtime & Standard Library](#runtime--standard-library)
9. [Testing](#testing)
10. [Documentation](#documentation)

---

## Parser & AST

### Location Tracking

**File**: `src/parser/cure_parser.erl`

- **Line 1557**: Import statement location tracking
  ```erlang
  % TODO: proper location
  Location = #location{line = 0, column = 0, file = undefined},
  ```
  - Currently using placeholder location for import statements
  - Need to extract actual location from tokens

- **Line 1982**: Where clause parsing
  ```erlang
  % TODO: Implement proper where clause parsing with trait bounds
  ```
  - Where clauses are parsed as expressions
  - Need proper trait bound parsing for generic constraints

**File**: `src/parser/cure_ast.erl`

- **Lines 610, 642, 676**: Default location placeholders in helper functions
  ```erlang
  % TODO: proper location
  location = #location{line = 0, column = 0}
  ```
  - `new_function/5`: Line 610
  - `new_type_def/3`: Line 642
  - `new_fsm/4`: Line 676
  - These helper functions should accept location parameters

**Priority**: Medium  
**Impact**: Error messages and debugging information less precise

---

## Type System & Checker

### Polymorphism

**File**: `src/types/cure_typechecker.erl`

- **Line 993**: ✅ **COMPLETED** - Bounded polymorphism
  - Implemented `extract_type_param_constraints/2` to extract trait bounds from type parameters
  - Polymorphic functions now properly handle constraints like `T: Eq`
  - Constraints are stored in poly_type records and validated

### Trait System

**File**: `src/types/cure_typechecker.erl`

- **Line 3763**: ✅ **COMPLETED** - Where clause checking
  - Implemented `parse_where_clause_constraints/1` to parse where clauses
  - Implemented `check_trait_constraints/3` to verify trait bounds
  - Where clauses in trait implementations are now fully validated

- **Line 3827**: ✅ **COMPLETED** - Method body type checking
  - Implemented `check_method_body_type/6` with full type inference
  - Method implementations now type-checked against signatures
  - Body types verified to match declared return types

- **Line 3844**: ✅ **COMPLETED** - Associated type checking
  - Implemented `verify_associated_type_bounds/4` for bound verification
  - Associated types validated to satisfy trait requirements
  - Missing associated types properly reported

**Priority**: ~~High~~ → **COMPLETED** ✅  
**Impact**: Trait system now complete with full validation

### SMT & Constraint Checking

**File**: `src/types/cure_typechecker.erl`

- **Line 3443**: SMT satisfiability checking
  ```erlang
  % Placeholder - would integrate with actual SMT solver
  % For now, assume all constraints are satisfiable
  {ok, satisfiable}.
  ```
  - FSM guard satisfiability always returns true
  - Need real SMT solver integration

**File**: `src/types/cure_smt_solver.erl`

- **Line 849**: Constraint negation
  ```erlang
  % TODO: Handle other constraint types
  _ -> Constraint
  ```
  - Only handles basic comparison operators
  - Need support for logical, arithmetic, and custom constraints

**Priority**: Medium  
**Impact**: May miss unsatisfiable guards in FSMs

---

## Type Optimizer & Monomorphization

### Dead Code Analysis

**File**: `src/types/cure_type_optimizer.erl`

- **Lines 714-721**: ✅ **COMPLETED** - Type-based dead code analysis
  - Implemented `find_unreachable_functions_by_type/2` with call site analysis
  - Implemented `find_unreachable_patterns_by_types/2` for pattern analysis
  - Implemented `find_redundant_type_checks/2` for redundant check detection
  - Functions now use type information to identify dead code
  - Protected exported functions and entry points from elimination

### AST Transformations

**File**: `src/types/cure_type_optimizer.erl`

- **Line 722**: ✅ **COMPLETED** - Monomorphization transformation
  - Implemented `transform_ast_for_monomorphization/2` with full AST traversal
  - Implemented `transform_item_for_mono/2` for module-level transformation
  - Implemented `transform_function_calls/2` for call site rewriting
  - Now properly transforms polymorphic function calls

- **Line 724**: ✅ **COMPLETED** - Inlining transformation
  - Implemented `transform_ast_for_inlining/2` with inline decision map
  - Implemented `inline_in_expression/3` for expression-level inlining
  - Implemented `substitute_in_expression/4` for parameter substitution
  - Function calls now inlined when beneficial

- **Line 726**: ✅ **COMPLETED** - Dead function filtering
  - Implemented `filter_dead_functions/2` with module filtering
  - Implemented `filter_dead_from_item/2` for item-level filtering
  - Dead functions now properly removed from AST

- **Line 728**: ✅ **COMPLETED** - Cleanup after DCE
  - Implemented `cleanup_after_dead_code_removal/2`
  - Implemented `remove_unreachable_patterns/2`
  - Implemented `remove_redundant_checks/2`
  - Post-elimination cleanup now performed

### Reporting

**File**: `src/types/cure_type_optimizer.erl`

- **Line 1321**: Optimization reporting
  ```erlang
  % TODO: Implement comprehensive reporting
  ```
  - Returns placeholder statistics
  - Should track actual optimizations applied

### Instantiation Analysis

**File**: `src/types/cure_type_optimizer.erl`

- **Line 1401**: Concrete instantiation finding
  ```erlang
  % TODO: Implement based on call site analysis
  []
  ```
  - Returns empty list
  - Should analyze call sites to find concrete type instantiations

### Performance Optimization Stubs

**File**: `src/types/cure_type_optimizer.erl`

- **Lines 5420-5424**: AST transformation stubs
  ```erlang
  %% Simple stub implementations for AST transformations
  apply_single_specialization(AST, _Specialization) -> AST.
  apply_single_hot_path_optimization(AST, _Optimization) -> AST.
  apply_single_memory_layout(AST, _MemoryLayout) -> AST.
  apply_single_performance_optimization(AST, _PerfOpt) -> AST.
  ```
  - No actual transformations performed
  - Adaptive optimization system incomplete

**Priority**: ~~High~~ → **MOSTLY COMPLETED** ✅  
**Impact**: Core optimization passes now functional, advanced optimizations remain TODO

---

## Code Generation

### Type Parameter Handling

**File**: `src/codegen/cure_beam_compiler.erl`

- **Lines 408-409**: Type parameter substitution
  ```erlang
  % Type parameters are compile-time only, substitute with a placeholder
  % Use 0 as placeholder for type params
  ```
  - Type parameters replaced with constant 0
  - Should be eliminated during monomorphization, not at codegen

### Guard Compilation

**File**: `src/codegen/cure_beam_compiler.erl`

- **Lines 548-552**: Guard check compilation
  ```erlang
  % For now, we'll assume guard checks always pass at runtime
  % In a full implementation, this would generate proper guard validation
  ```
  - Guard checks always succeed
  - Should generate actual validation code

**Priority**: Medium  
**Impact**: Runtime behavior may not match type system guarantees

---

## LSP (Language Server Protocol)

### Type Inference for Hints

**File**: `lsp/cure_lsp_enhanced.erl`

- **Line 427**: Parameter type inference
  ```erlang
  % Placeholder for type inference
  unknown.
  ```
  - Cannot infer parameter types
  - Should use type checker to determine types

- **Line 431**: Return type inference
  ```erlang
  % Placeholder for return type inference
  unknown.
  ```
  - Cannot infer return types
  - Should use type checker for inference

### Type Checking Integration

**File**: `lsp/cure_lsp_analyzer.erl`

- **Line 528**: Type checking diagnostics
  ```erlang
  % Placeholder for type checking integration
  % Would call cure_typechecker:check(AST) and convert errors to diagnostics
  ```
  - Type errors not reported in LSP
  - Should integrate with typechecker for real-time feedback

**Priority**: Medium  
**Impact**: Limited IDE support, no type hints or error reporting

---

## SMT Solver

### Constraint Type Support

**File**: `src/types/cure_smt_solver.erl`

- **Line 849**: Extended constraint negation
  ```erlang
  % TODO: Handle other constraint types
  ```
  - Only basic comparisons supported
  - Need logical operators, quantifiers, custom constraints

**Priority**: Low  
**Impact**: Dependent type checking limited

---

## CLI & Tooling

### Module Information Extraction

**File**: `src/cure_cli.erl`

- **Line 862**: AST metadata extraction
  ```erlang
  % TODO: Extract actual module info when AST types are available
  ```
  - Returns placeholder module info
  - Should extract name, exports, imports from AST

**Priority**: Low  
**Impact**: Limited tooling support for module inspection

---

## Runtime & Standard Library

### Monadic Pipe Documentation

**File**: `src/runtime/cure_std.erl`

- **Line 87**: Module documentation truncated
  ```
  ...(truncated)
  ```
  - Complete pipe semantics documentation needed

**Priority**: Low  
**Impact**: Documentation completeness

---

## Testing

### Standard Library Tests

**File**: `test/std_string_test.erl`

Multiple test placeholders throughout (lines 34, 36, 38, 40, 55, 57, 69, etc.)

### I/O Tests

**File**: `test/std_io_test.erl`

Multiple test placeholders (lines 132, 138, 144, 153, 159, 165)

### Monomorphization Tests

**File**: `test/monomorphization_test.erl`

- **Line 970**: Additional test cases needed

### Pattern Compilation Tests

**File**: `test/pattern_compilation_test.erl`

- **Lines 82, 159**: Pattern matching edge cases

**Priority**: Medium  
**Impact**: Incomplete test coverage

---

## Documentation

### Completed Features

**File**: `docs/completed/type_directed_optimization_summary.md`

- **Line 185**: Documentation placeholder

### Status Documents

**File**: `docs/POLYMORPHISM_STATUS.md`

- **Lines 6, 112, 220**: Status tracking items

**File**: `docs/FSM_STATUS.md`

- **Line 30**: FSM implementation status

### Feature Documentation

**File**: `docs/FSM_GUARD_VERIFICATION.md`

- **Line 53**: Guard verification documentation

**File**: `docs/FSM_API_DESIGN.md`

- **Lines 146, 153**: API design considerations

**File**: `docs/FSM_TYPE_CHECKING_SUMMARY.md`

- **Lines 75, 80**: Type checking completeness

**File**: `docs/STD_SUMMARY.md`

- **Lines 276, 280**: Standard library documentation

**File**: `docs/LSP_FEATURES.md`

- **Line 59**: LSP feature documentation

**Priority**: Low  
**Impact**: Documentation gaps

---

## Examples & Library Code

### Pattern Matching Examples

**File**: `examples/pattern_matching.cure`

- **Line 24**: Pattern matching examples

### Monadic Pipes

**File**: `examples/monadic_pipes.cure`

- **Lines 187, 217, 338**: Monadic pipe examples and edge cases

### FSM Standard Library

**File**: `lib/std/fsm.cure`

- **Lines 44, 46, 52, 57, 62**: FSM utility functions

**Priority**: Low  
**Impact**: Example completeness

---

## Makefile & Build System

**File**: `Makefile`

- **Lines 179, 184, 207**: Build system TODOs

**Priority**: Low  
**Impact**: Build process improvements

---

## Summary by Priority

### High Priority

~~1. **Trait System Completion**~~ ✅ **COMPLETED**
   - ✅ Method body type checking
   - ✅ Associated type validation
   - ✅ Where clause verification
   
~~2. **Monomorphization Pipeline**~~ ✅ **COMPLETED**
   - ✅ AST transformation for specializations
   - ✅ Dead code elimination implementation
   - ✅ Inlining transformation

~~3. **Bounded Polymorphism**~~ ✅ **COMPLETED**
   - ✅ Constraint checking for type bounds
   - ✅ Trait bound satisfaction

**All high-priority items have been completed!** 🎉

### Medium Priority

1. **Location Tracking**
   - Accurate source locations for all AST nodes
   - Better error messages

2. **LSP Integration**
   - Type inference for hints
   - Real-time type checking
   - Diagnostic reporting

3. **Guard Compilation**
   - Proper guard validation code generation
   - SMT solver integration for guard analysis

4. **Test Coverage**
   - Complete standard library tests
   - Monomorphization test cases
   - Pattern matching edge cases

### Low Priority

1. **Documentation**
   - Complete all pending documentation
   - Update status documents

2. **Module Metadata**
   - Extract full module information from AST
   
3. **Build System**
   - Makefile improvements

4. **Examples**
   - Complete example programs

---

## Notes

- Many optimizations are stubbed out and return input unchanged
- Type system features are mostly complete; trait system needs work
- Code generation handles most cases but guard checking is simplified
- LSP support exists but lacks type checker integration
- Test infrastructure is in place but many tests are placeholders

**Total Items**: ~70 TODOs across ~20 files

## Priority Breakdown

### High Priority (3 areas):

1. Trait system completion (method body checking, associated types, where clauses)
2. Monomorphization pipeline (AST transformations, DCE, inlining)
3. Bounded polymorphism (constraint checking)

### Medium Priority (4 areas):

1. Location tracking for better error messages
2. LSP integration for IDE support
3. Guard compilation improvements
4. Test coverage expansion

### Low Priority (4 areas):

1. Documentation completion
2. Module metadata extraction
3. Build system improvements
4. Example programs

**Last Updated**: 2025-10-28
