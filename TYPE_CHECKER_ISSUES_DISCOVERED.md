# Type Checker Issues Discovered

## Overview

While implementing FSM standard library integration and fixing the `turnstile.cure` example, several fundamental type checker limitations were discovered that prevent the example from compiling.

## Issue 1: Empty List Literals in Function Arguments

**Problem**: When an empty list `[]` is used as an argument in a nested function call where the outer functions return `Any`, the type checker fails with unification errors.

**Example**:
```cure
let cast1 = fsm_cast(:main_turnstile, pair(:push, []))
```

**Error**:
```
{unification_failed, {primitive_type,'Atom'}, {list_type, ...}}
```

**Workaround**: Extract the empty list to a separate binding:
```cure
let empty_list = []
let event = pair(:push, empty_list)
let cast1 = fsm_cast(:main_turnstile, event)
```

This workaround helps but doesn't fully resolve all issues.

## Issue 2: Wildcard Pattern `_` Typed as Atom

**Problem**: The wildcard pattern `_` in let bindings is being typed as `Atom` instead of being polymorphic/accepting any type.

**Example**:
```cure
let _ = fsm_cast(:main_turnstile, pair(:push, []))
```

**Error**:
```
{binding_constraint_failed, '_', {unification_failed, {primitive_type,'Atom'}, {tuple_type, ...}}}
```

**Expected**: The wildcard should accept any type, similar to how it works in Erlang/Elixir.

## Issue 3: Generic Type Variables in Return Types

**Problem**: Functions with generic type variables in return types (e.g., `{A, B}`) cause unification failures when the return value is bound in a let expression.

**Example** (from `pair.cure`):
```cure
def pair(first: A, second: B): {A, B} =
  {first, second}
```

**Error** when used:
```
{unification_failed, {primitive_type,'Atom'}, {tuple_type, [{primitive_type,'A'}, {primitive_type,'B'}], ...}}
```

**Workaround**: Change return type to `Any`:
```cure
def pair(first: Any, second: Any): Any =
  {first, second}
```

## Issue 4: Statement Type Inference with `Any` Returns

**Problem**: When a function returning `Any` is called as a statement (not bound to a variable), the type checker creates a dummy binding with type `Atom`, leading to unification failures when the actual return involves tuples or lists.

**Location**: In `cure_typechecker.erl`, lines 1979-1982:
```erlang
convert_block_to_lets([Expr | RestExprs], Location) ->
    % Convert expression to let with dummy variable
    DummyVar = {identifier_pattern, '_dummy', Location},
    DummyBinding = {binding, DummyVar, convert_expr_to_tuple(Expr), Location},
    {let_expr, [DummyBinding], convert_block_to_lets(RestExprs, Location), Location}.
```

The `_dummy` pattern is typed as `Atom`, but the expression may return other types.

## Issue 5: Record Type Unification with Atom

**Problem**: In handler functions that return records wrapped in result types, the type checker tries to unify `Atom` with record types.

**Example**:
```cure
def push(from: Atom, evt: Any, payload: TurnstilePayload): Any =
  match from do
    :Locked -> ok(pair(:Locked, new_payload))
    ...
  end
```

**Error**:
```
{unification_failed, {primitive_type,'Atom'}, {record_type,'TurnstilePayload'}}
```

## Root Cause Analysis

The fundamental issue appears to be in how the type inference engine handles:

1. **Type Variable Instantiation**: Generic type variables (`A`, `B`) are not being properly instantiated to concrete types during unification
2. **Any Type Handling**: The `Any` type doesn't properly subsume other types during unification
3. **Pattern Type Inference**: Wildcard and dummy patterns are given concrete types (`Atom`) instead of being polymorphic
4. **Nested Expression Type Propagation**: Type constraints from outer expressions incorrectly propagate to inner expressions

## Required Fixes

### High Priority

1. **Fix Wildcard Pattern Typing**: Make `_` and `_dummy` patterns polymorphic, accepting any type
2. **Improve Any Type Unification**: Ensure `Any` can unify with any concrete type without errors
3. **Fix Generic Type Variable Handling**: Properly instantiate type variables during function application

### Medium Priority

4. **Better Error Messages**: Current errors don't clearly indicate the source of type mismatches
5. **Statement Typing**: Review how statements (unbound expressions) are typed

## Workarounds for Users

Until these issues are fixed:

1. Extract complex expressions to separate bindings
2. Use `Any` return types instead of generic types
3. Bind statement results to named variables instead of using wildcards
4. Avoid nested function calls with complex type signatures

## Files Involved

- `src/types/cure_typechecker.erl` - Main type checker logic
- `src/types/cure_types.erl` - Type system and unification
- `lib/std/pair.cure` - Demonstrates generic type issues
- `examples/turnstile.cure` - Real-world example that fails

## Next Steps

1. Fix wildcard pattern typing to be polymorphic
2. Improve `Any` type handling in unification
3. Add test cases for these scenarios
4. Update turnstile example once fixes are in place
