# Pattern Compilation Tests

This document describes the unit tests for pattern compilation to Erlang forms in the Cure compiler.

## Test File: `test/pattern_compilation_test.erl`

### Overview

The pattern compilation tests verify that Cure patterns are correctly compiled to Erlang abstract syntax forms. These tests cover both currently implemented patterns and provide expectations for patterns that are not yet implemented.

### Test Coverage

#### 1. Binary Pattern Compilation (`test_binary_pattern_compilation/0`)

**Status: Not yet implemented in AST**

Tests for binary pattern compilation including:
- Simple binary patterns: `<<X>>`
- Sized binary patterns: `<<X:8>>`
- Typed binary patterns: `<<X:8/integer>>`
- Multiple element patterns: `<<X:8, Y:16>>`
- Literal binary patterns: `<<"hello">>`
- Rest patterns: `<<Head:8, Rest/binary>>`

**Expected Erlang forms:**
```erlang
% <<X>> -> {bin, Line, [{bin_element, Line, {var, Line, x}, default, default}]}
% <<X:8>> -> {bin, Line, [{bin_element, Line, {var, Line, x}, {integer, Line, 8}, default}]}
% <<X:8/integer>> -> {bin, Line, [{bin_element, Line, {var, Line, x}, {integer, Line, 8}, [integer]}]}
```

**Current behavior:** Structural verification only (patterns not implemented in AST)

#### 2. Map Pattern Compilation (`test_map_pattern_compilation/0`)

**Status: Not yet implemented in AST**

Tests for map pattern compilation including:
- Empty map patterns: `#{}`
- Exact match patterns: `#{key := value}`
- Multiple field patterns: `#{a := X, b := Y}`
- Variable key patterns: `#{Key := Value}`
- Nested map patterns: `#{outer := #{inner := X}}`

**Expected Erlang forms:**
```erlang
% #{} -> {map, Line, []}
% #{key := value} -> {map, Line, [{map_field_exact, Line, {atom, Line, key}, {var, Line, value}}]}
```

**Current behavior:** Structural verification only (patterns not implemented in AST)

#### 3. Record Pattern Compilation (`test_record_pattern_compilation/0`)

**Status: Implemented in AST, not in codegen**

Tests for record pattern compilation including:
- Record patterns with all fields: `#person{name = Name, age = Age}`
- Record patterns with wildcard fields: `#person{name = Name, _ = _}`
- Empty record patterns: `#person{}`
- Nested record patterns: `#company{ceo = #person{name = CEO}}`

**Expected Erlang forms:**
```erlang
% #person{name = Name, age = Age} -> 
% {record, Line, person, [{record_field, Line, {atom, Line, name}, {var, Line, 'Name'}},
%                         {record_field, Line, {atom, Line, age}, {var, Line, 'Age'}}]}
```

**Current behavior:** Falls back to wildcard pattern `{var, Line, '_'}`

#### 4. Wildcard Pattern Compilation (`test_wildcard_pattern_compilation/0`)

**Status: Fully implemented**

Tests for wildcard pattern compilation including:
- Simple wildcard patterns: `_`
- Wildcards in tuples: `{1, _, x}`
- Wildcards in lists: `[_, rest]`
- Multiple independent wildcards: `{_, _}`

**Erlang forms:**
```erlang
% _ -> {var, Line, '_'}
```

**Current behavior:** ✅ All tests pass

#### 5. Complex Nested Pattern Compilation (`test_complex_nested_patterns/0`)

**Status: Fully implemented**

Tests for complex nested patterns including:
- Tuple containing lists: `{status, [head | tail]}`
- List of tuples: `[{ok, value1}, {error, reason}]`
- Nested tuples: `{{inner1, inner2}, outer}`
- Mixed patterns with wildcards: `{_, [_, value | _]}`
- Deep nesting: `[{{a, b}, [c | d]}, e]`
- Empty nested structures: `{[], {}}`

**Current behavior:** ✅ All tests pass

### Test Execution

Run the tests with:
```bash
cd /opt/Proyectos/Ammotion/cure
erlc -o _build/ebin -I . test/pattern_compilation_test.erl
erl -pa _build/ebin -s pattern_compilation_test run -s init stop
```

### Implementation Status Summary

| Pattern Type | AST Definition | Codegen Implementation | Test Status |
|--------------|---------------|----------------------|-------------|
| Literal | ✅ | ✅ | ✅ Pass |
| Wildcard | ✅ | ✅ | ✅ Pass |
| Identifier | ✅ | ✅ | ✅ Pass |
| List | ✅ | ✅ | ✅ Pass |
| Tuple | ✅ | ✅ | ✅ Pass |
| Record | ✅ | ❌ (fallback) | ⚠️ Fallback verified |
| Binary | ❌ | ❌ | 📋 Structure verified |
| Map | ❌ | ❌ | 📋 Structure verified |

### Future Implementation

To fully implement the missing patterns:

1. **Binary Patterns**: Add `binary_pattern` and `binary_element` records to `cure_ast.hrl`
2. **Map Patterns**: Add `map_pattern` and `map_field_exact` records to `cure_ast.hrl`
3. **Record Pattern Codegen**: Implement record pattern handling in `convert_pattern_to_erlang_form/2`

The test suite provides comprehensive expectations for these implementations and will validate the behavior once implemented.