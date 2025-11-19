# Cure LSP with SMT Verification - User Guide

**Version**: 0.1.0  
**Last Updated**: 2025-11-19

---

## Table of Contents

1. [Overview](#overview)
2. [Getting Started](#getting-started)
3. [Features](#features)
4. [Configuration](#configuration)
5. [Using SMT Verification](#using-smt-verification)
6. [Quick Fixes](#quick-fixes)
7. [Performance Tuning](#performance-tuning)
8. [Troubleshooting](#troubleshooting)
9. [Advanced Usage](#advanced-usage)

---

## Overview

Cure's Language Server Protocol (LSP) integration provides real-time SMT-based verification for:

- **Refinement types**: Verify constraints like `x > 0` at compile time
- **Dependent types**: Length-indexed vectors, bounded integers
- **Pattern exhaustiveness**: Prove all cases are covered
- **FSM verification**: Check state machine invariants

### Key Benefits

✅ **Real-time feedback** - See errors as you type, no compilation needed  
✅ **Concrete counterexamples** - "x = -5 violates x > 0" instead of generic errors  
✅ **Automated fixes** - One-click quick fixes for common issues  
✅ **Performance optimized** - <100ms for cached checks, <500ms for new code  

---

## Getting Started

### Prerequisites

1. **Z3 SMT Solver** (required)
   ```bash
   # Ubuntu/Debian
   sudo apt install z3
   
   # macOS
   brew install z3
   
   # Or download from: https://github.com/Z3Prover/z3/releases
   ```

2. **Verify Z3 installation**
   ```bash
   z3 --version
   # Should output: Z3 version 4.x.x
   ```

### IDE Setup

#### Visual Studio Code

1. Install the **Cure Language Support** extension (when available)
2. The LSP server will start automatically when you open a `.cure` file
3. SMT verification runs in the background

#### Neovim/Vim

```lua
-- Add to your LSP config
require('lspconfig').cure_ls.setup{
  cmd = {'cure-lsp-server'},
  filetypes = {'cure'},
  settings = {
    cure = {
      smt = {
        enabled = true,
        solver = 'z3',
        timeout = 500  -- ms
      }
    }
  }
}
```

#### Emacs

```elisp
(use-package lsp-mode
  :hook (cure-mode . lsp)
  :custom
  (lsp-cure-smt-enabled t)
  (lsp-cure-smt-timeout 500))
```

---

## Features

### 1. Refinement Type Checking

**Define constrained types:**

```cure
type Positive = Int when x > 0
type Percentage = Int when x >= 0 and x <= 100
type NonEmptyList(T) = List(T) when length(xs) > 0
```

**Get instant feedback:**

```cure
def divide(a: Int, b: Positive): Int = a / b  ✅

def bad_divide(a: Int, b: Int): Int = 
    divide(a, b)  // ❌ Error: b may not be positive
    // Counterexample: b = -5 violates b > 0
```

### 2. Hover Information

Hover over any variable to see its refinement type:

```cure
def process(n: Positive) = 
    let x = n + 1  // Hover shows: x: Int when x > 1
```

**Hover display:**
```markdown
```cure
x: Int when x > 1
```

**Refinement Type**

This variable has a refined type with the constraint:
- `x > 1`

The SMT solver will verify this constraint is satisfied.
```

### 3. Pattern Exhaustiveness

**Automatic checking:**

```cure
match n with
| 0 -> "zero"
| n when n > 0 -> "positive"
end

// ❌ Error: Pattern match is not exhaustive
// Missing case: n when n < 0
```

**With quick fix:**
```cure
match n with
| 0 -> "zero"
| n when n > 0 -> "positive"
| n when n < 0 -> "negative"  // Quick fix adds this
end
```

### 4. Quick Fixes

When SMT finds an issue, you get actionable fixes:

#### Add Guard Clause
```cure
// Before
def divide(a: Int, b: Int): Int = a / b

// Quick fix: Add guard clause
def divide(a: Int, b: Int) when b /= 0: Int = a / b
```

#### Add Assertion
```cure
def divide(a: Int, b: Int): Int =
    assert b /= 0  // Quick fix adds this
    a / b
```

#### Relax Constraint
```cure
// Error: Cannot prove n > 10 implies n > 5
// Quick fix: Relax n > 10 to n >= 10
```

#### Type Conversion
```cure
// Error: Expected Int, got Float
// Quick fix: Add to_int(value)
```

---

## Configuration

### Timeout Settings

Configure timeouts based on your workflow:

```erlang
% In your LSP config
#{
    timeouts => #{
        lsp => 500,        % Interactive editing (default)
        compile => 5000,   % Full compilation
        test => 10000      % Running tests
    }
}
```

### Cache Settings

```erlang
#{
    cache => #{
        enabled => true,
        max_size => 1000,      % Max cached queries
        ttl_seconds => 3600    % Cache lifetime
    }
}
```

### Solver Selection

```erlang
#{
    solver => z3,              % Currently only Z3 supported
    solver_path => "/usr/bin/z3"  % Custom path if needed
}
```

---

## Using SMT Verification

### Writing Verifiable Code

**✅ Good: Simple constraints**
```cure
type Positive = Int when x > 0
type Even = Int when x mod 2 == 0
```

**✅ Good: Composite constraints**
```cure
type PositiveEven = Int when x > 0 and x mod 2 == 0
```

**⚠️ Careful: Complex constraints**
```cure
// May be slow
type Prime = Int when is_prime(x)  // Non-linear
```

**❌ Avoid: Undecidable constraints**
```cure
// SMT may timeout
type Halting = Int when terminates(f, x)
```

### Constraint Complexity Guidelines

| Complexity | SMT Time | Example |
|------------|----------|---------|
| Simple comparison | <10ms | `x > 0`, `x <= 100` |
| Linear arithmetic | <50ms | `x + y > z`, `2*x < y` |
| Quantifiers (bounded) | <200ms | `forall i. 0 <= i < n => arr[i] > 0` |
| Non-linear | <500ms | `x * y > z` (may timeout) |

### Best Practices

1. **Keep constraints simple** - SMT works best with linear arithmetic
2. **Use type aliases** - Define once, use everywhere
3. **Combine with guards** - Runtime checks complement SMT verification
4. **Test edge cases** - SMT proves properties, but test actual values

---

## Quick Fixes

### Available Quick Fixes

#### 1. Refinement Violations

**Problem**: Constraint not satisfied

**Available fixes**:
- Add guard clause: `when x > 0`
- Add assertion: `assert x > 0`
- Relax constraint: `x > 0` → `x >= 0`

#### 2. Non-Exhaustive Patterns

**Problem**: Missing pattern cases

**Available fixes**:
- Add missing case (SMT provides counterexample)
- Add wildcard: `_ -> error("unhandled")`

#### 3. Type Mismatches

**Problem**: Type doesn't match

**Available fixes**:
- Add type annotation: `: Positive`
- Add type conversion: `to_int()`, `to_float()`

#### 4. Undefined Variables

**Problem**: Variable not in scope

**Available fixes**:
- Add as parameter
- Define with `let`

---

## Performance Tuning

### Understanding Performance

**Cache hit** (instant): <10ms  
**Small edit** (incremental): <100ms  
**New constraint** (full solve): <500ms  
**Complex constraint**: May timeout at 500ms  

### Optimization Strategies

#### 1. Structure Code for Caching

```cure
// Good: Stable constraints
type UserId = Int when x > 0

def process_user(id: UserId) = ...  // Cached after first check

// Bad: Dynamic constraints
type DynamicRange(n) = Int when x >= 0 and x < n  // Re-verified each time
```

#### 2. Use Batch Processing

```cure
// SMT batches constraints from same context
def process_many(xs: List(Positive)) =  // All checked together
    xs.map(fn x -> x + 1)
```

#### 3. Simplify Constraints

```cure
// Faster
type Positive = Int when x > 0

// Slower (quantifier)
type AllPositive = List(Int) when 
    forall i. 0 <= i < length(xs) => xs[i] > 0
```

### Monitoring Performance

Check LSP statistics:

```erlang
cure_lsp_performance:get_stats().
% => #{
%     queued => 45,
%     processed => 120,
%     avg_verify_time_ms => 85,
%     cache_hit_rate => 0.82
% }
```

---

## Troubleshooting

### Common Issues

#### Z3 Not Found

**Error**: `Z3 solver not found`

**Solution**:
1. Install Z3: `sudo apt install z3` or `brew install z3`
2. Verify: `z3 --version`
3. Set path in config if in non-standard location

#### Verification Timeout

**Error**: `SMT verification timed out`

**Solutions**:
1. Simplify the constraint
2. Increase timeout in settings
3. Split complex constraints into simpler ones
4. Use runtime checks instead: `assert x > 0`

#### High Memory Usage

**Symptom**: LSP using >1GB RAM

**Solutions**:
1. Restart LSP server
2. Reduce cache size in config
3. Disable SMT for large files: `// @smt-disable`

#### Slow Response Time

**Symptom**: Lag when typing

**Solutions**:
1. Check cache hit rate (should be >80%)
2. Increase batch timeout
3. Disable SMT temporarily: Toggle in IDE

### Debug Mode

Enable verbose logging:

```bash
CURE_LSP_LOG_LEVEL=debug cure-lsp-server
```

Check logs:
```bash
tail -f ~/.cure/lsp.log
```

---

## Advanced Usage

### Disabling SMT for Specific Code

```cure
// @smt-disable
def unsafe_operation(x: Int) =
    // SMT verification skipped here
    x / 0  // Would normally error
```

### Custom Solver Flags

```erlang
#{
    solver_args => [
        "timeout=1000",
        "smt.mbqi=false"
    ]
}
```

### Incremental Verification

LSP automatically uses incremental solving:
- Persistent Z3 process (avoids 50ms startup)
- Push/pop scopes for edits
- Hash-based cache invalidation

### Background Verification

Large files verified in background:
```erlang
cure_lsp_performance:verify_async(Uri, AST, lsp).
```

Results arrive asynchronously without blocking editor.

---

## Resources

- **SMT-LIB Standard**: http://smtlib.cs.uiowa.edu/
- **Z3 Guide**: https://microsoft.github.io/z3guide/
- **Refinement Types**: https://ucsd-progsys.github.io/liquidhaskell/
- **Cure Documentation**: https://cure-lang.org/docs

---

## FAQ

**Q: Does SMT verification guarantee no runtime errors?**  
A: SMT proves properties about types, but runtime checks are still needed for:
- External input validation
- Resource limits (memory, disk)
- Concurrent behavior

**Q: Can I use CVC5 instead of Z3?**  
A: Not yet. Z3 is currently the only supported solver.

**Q: Does SMT work with separate compilation?**  
A: Yes! Constraint verification is modular and works across module boundaries.

**Q: What happens if SMT times out?**  
A: The constraint is treated as "unknown" - no error, but no proof either. Use runtime checks as fallback.

**Q: Can SMT verify recursive functions?**  
A: Limited support. Simple recursion works, but complex recursion may timeout. Use termination measures explicitly.

---

**Happy verifying! 🎉**

For issues or questions: https://github.com/cure-lang/cure/issues
