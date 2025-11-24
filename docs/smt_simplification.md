# SMT Constraint Simplification

## Overview

The `cure_smt_solver:simplify_constraint/2` function implements comprehensive constraint simplification using a two-phase approach:

1. **Local algebraic simplifications** - Fast, deterministic optimizations requiring no external solver
2. **SMT-based simplifications** - Advanced optimizations using Z3's simplify command (when available)

## Implementation Location

- **Module**: `src/smt/cure_smt_solver.erl`
- **Function**: `simplify_constraint/2` (lines 150-180)
- **Helper Functions**: Lines 447-641

## Supported Simplifications

### 1. Arithmetic Identities

| Pattern | Simplification | Example |
|---------|---------------|---------|
| `x + 0` | `x` | Identity element for addition |
| `0 + x` | `x` | Commutative identity |
| `x * 1` | `x` | Identity element for multiplication |
| `1 * x` | `x` | Commutative identity |
| `x * 0` | `0` | Zero property |
| `0 * x` | `0` | Commutative zero |
| `x - 0` | `x` | Subtraction identity |

### 2. Boolean Identities

| Pattern | Simplification | Example |
|---------|---------------|---------|
| `x and true` | `x` | Conjunction identity |
| `true and x` | `x` | Commutative identity |
| `x and false` | `false` | Annihilator element |
| `false and x` | `false` | Commutative annihilator |
| `x or true` | `true` | Disjunction annihilator |
| `true or x` | `true` | Commutative annihilator |
| `x or false` | `x` | Disjunction identity |
| `false or x` | `x` | Commutative identity |

### 3. Constant Folding

All operations with constant operands are evaluated at compile time:

```erlang
2 + 3          => 5
10 - 3         => 7
4 * 5          => 20
true and false => false
5 > 3          => true
```

### 4. Comparison Simplifications

For pure expressions (no side effects):

| Pattern | Simplification | Notes |
|---------|---------------|-------|
| `x == x` | `true` | Reflexivity of equality |
| `x /= x` | `false` | Negation of reflexivity |
| `x < x` | `false` | Irreflexivity of strict ordering |
| `x > x` | `false` | Irreflexivity of strict ordering |
| `x =< x` | `true` | Reflexivity of weak ordering |
| `x >= x` | `true` | Reflexivity of weak ordering |

### 5. Double Negation Elimination

| Pattern | Simplification | Type |
|---------|---------------|------|
| `not (not x)` | `x` | Boolean negation |
| `-(-x)` | `x` | Numeric negation |
| `not true` | `false` | Constant negation |
| `not false` | `true` | Constant negation |
| `-N` | `-N` | Constant folding |

## Algorithm Details

### Local Simplification Algorithm

The implementation uses a fixed-point iteration strategy:

```erlang
simplify_local(Constraint, Env) ->
    case simplify_once(Constraint, Env) of
        Constraint -> Constraint;    % No change, done
        Simplified -> simplify_local(Simplified, Env)  % Changed, iterate
    end.
```

This ensures that nested simplifications are fully reduced. For example:
- `((x + 0) * 1) - 0` → `(x * 1) - 0` → `x - 0` → `x`

### SMT-Based Simplification

When Z3 is available, the implementation:

1. Generates an SMT-LIB query with variable declarations
2. Uses Z3's `(simplify ...)` command
3. Parses the simplified result back to AST

Currently, the SMT-based simplification provides infrastructure for advanced optimizations but falls back to local simplification if parsing fails.

## Performance Characteristics

- **Local simplifications**: O(n) per pass, where n = expression tree size
- **Fixed-point iteration**: Typically 1-3 passes for most expressions
- **SMT simplification**: ~2-10ms overhead for Z3 process (when used)

## Use Cases

### 1. Guard Optimization

Simplify type guards to eliminate redundant checks:

```erlang
% Before: (n > 0) and true
% After:  (n > 0)
```

### 2. Dependent Type Constraints

Reduce complex type constraints at compile time:

```erlang
% Vector(T, n+0) simplifies to Vector(T, n)
% This enables better type checking and error messages
```

### 3. Dead Code Elimination

Identify always-true or always-false conditions:

```erlang
if x >= x then ... else ...  
% Condition simplifies to 'true', else branch is dead code
```

## Testing

### Test Suite

- **Location**: `test/smt_simplify_test.erl`
- **Tests**: 5 test categories, 20+ individual test cases
- **Coverage**: All simplification rules

Run tests:
```bash
make test
# Or specifically:
erl -pa _build/ebin -noshell -s smt_simplify_test run -s init stop
```

### Example Script

- **Location**: `examples/smt_simplify_example.erl`
- **Purpose**: Interactive demonstration of simplification capabilities

Run example:
```bash
cd examples
./smt_simplify_example.erl
```

## API Usage

### Basic Usage

```erlang
% Create a constraint: x + 0
X = #identifier_expr{name = x, location = ...},
Zero = #literal_expr{value = 0, location = ...},
Constraint = #binary_op_expr{op = '+', left = X, right = Zero, location = ...},

% Simplify
Simplified = cure_smt_solver:simplify_constraint(Constraint, #{}).
% Result: X
```

### With Type Environment

```erlang
% Environment mapping variables to types
Env = #{x => {type, int}, n => {type, nat}},
Simplified = cure_smt_solver:simplify_constraint(Constraint, Env).
```

## Future Enhancements

### Potential Improvements

1. **Full S-expression Parser**
   - Parse Z3's simplified output back to AST
   - Enable more sophisticated SMT-based simplifications

2. **Additional Algebraic Rules**
   - Distributive laws: `x * (y + z)` → `(x * y) + (x * z)`
   - Associative transformations
   - De Morgan's laws for boolean expressions

3. **Context-Aware Simplifications**
   - Use type information for more aggressive simplification
   - Incorporate known facts from the environment

4. **Caching**
   - Cache simplification results for common patterns
   - Memoization for expensive SMT queries

## References

- **Main Implementation**: `src/smt/cure_smt_solver.erl:447-641`
- **SMT Translator**: `src/smt/cure_smt_translator.erl`
- **Related Modules**: 
  - `cure_guard_optimizer.erl` - Uses simplification for guard optimization
  - `cure_type_optimizer.erl` - Uses simplification in type-directed optimizations

## Implementation Notes

### Pure Expression Check

The implementation includes a helper `is_pure_expr/1` that determines if an expression has no side effects. This is crucial for safely applying reflexive simplifications like `x == x` → `true`, since the simplification is only valid if evaluating `x` twice produces the same result.

### Zero Multiplication Handling

When simplifying `x * 0` to `0`, the implementation preserves the expression structure by creating a new binary operation with zero literals on both sides. This maintains type information and location data for error reporting.

### Location Preservation

All simplifications preserve the `location` field from the original expression, ensuring that error messages and debugging information remain accurate after optimization.
