# Cure SMT Troubleshooting Guide

**Version**: 0.1.0  
**Last Updated**: 2025-11-19

---

## Quick Diagnostics

Run these commands to check your setup:

```bash
# Check Z3 installation
z3 --version

# Check Cure compiler
cure --version

# Test SMT integration
cd /path/to/cure
make test

# Check LSP server
cure-lsp-server --version
```

---

## Common Issues

### 1. Z3 Solver Not Found

**Symptoms**:
- Error: `Z3 solver not found`
- Error: `Failed to start SMT solver`
- LSP diagnostics not working

**Diagnosis**:
```bash
which z3
# If empty, Z3 is not installed or not in PATH
```

**Solutions**:

#### Ubuntu/Debian
```bash
sudo apt update
sudo apt install z3
```

#### macOS
```bash
brew install z3
```

#### Manual Installation
```bash
# Download from GitHub
wget https://github.com/Z3Prover/z3/releases/download/z3-4.12.2/z3-4.12.2-x64-glibc-2.31.zip
unzip z3-4.12.2-x64-glibc-2.31.zip
sudo cp z3-4.12.2-x64-glibc-2.31/bin/z3 /usr/local/bin/
```

#### Custom Path
If Z3 is in a non-standard location:
```erlang
% In LSP config
#{
    solver_path => "/custom/path/to/z3"
}
```

---

### 2. SMT Verification Timeout

**Symptoms**:
- Error: `SMT verification timed out`
- Slow editor response
- Diagnostics take >1 second

**Diagnosis**:
```erlang
% Check current timeout
cure_lsp_smt:get_cache_stats().
% Look at avg_verify_time_ms
```

**Solutions**:

#### 1. Increase Timeout
```erlang
% For complex constraints
cure_lsp_performance:set_timeout(lsp, 1000).  % 1 second
```

#### 2. Simplify Constraints
```cure
% Before (slow)
type Complex = Int when 
    x > 0 and x < 100 and x mod 2 == 0 and is_prime(x)

% After (faster)
type Simple = Int when x > 0 and x < 100
```

#### 3. Split Complex Types
```cure
% Instead of one complex type
type PositiveEvenPrime = Int when x > 0 and x mod 2 == 0 and is_prime(x)

% Use composition
type Positive = Int when x > 0
type Even = Int when x mod 2 == 0
% Check is_prime at runtime
```

#### 4. Use Runtime Checks
```cure
def process(n: Int) =
    assert is_prime(n)  % Runtime check instead of type
    ...
```

---

### 3. High Memory Usage

**Symptoms**:
- LSP using >1GB RAM
- System becomes slow
- Out of memory errors

**Diagnosis**:
```bash
# Check LSP memory
ps aux | grep cure-lsp-server
```

**Solutions**:

#### 1. Clear Cache
```erlang
cure_lsp_smt:clear_cache(State).
```

#### 2. Reduce Cache Size
```erlang
% In config
#{
    cache => #{
        max_size => 500,  % Default: 1000
        ttl_seconds => 1800  % Default: 3600
    }
}
```

#### 3. Restart LSP Server
Most IDEs have a "Restart LSP" command:
- **VS Code**: Cmd+Shift+P → "Reload Window"
- **Neovim**: `:LspRestart`
- **Emacs**: `M-x lsp-restart-workspace`

#### 4. Disable SMT for Large Files
```cure
// @smt-disable
module LargeModule
```

---

### 4. Incorrect Diagnostics

**Symptoms**:
- False positives (errors that shouldn't be there)
- False negatives (missing errors)
- Outdated diagnostics

**Solutions**:

#### 1. Refresh Diagnostics
Save the file or trigger manual verification.

#### 2. Check Cache Validity
```erlang
% Invalidate cache for a document
cure_lsp_smt:invalidate_cache_document(Uri, State).
```

#### 3. Check Z3 Version
```bash
z3 --version
# Should be 4.8.0 or newer
```

Older Z3 versions may give incorrect results. Upgrade if needed.

#### 4. Report Bug
If diagnostics are consistently wrong:
1. Create minimal reproduction
2. File issue: https://github.com/cure-lang/cure/issues
3. Include Z3 version and example code

---

### 5. LSP Server Crashes

**Symptoms**:
- LSP suddenly stops responding
- IDE shows "LSP connection lost"
- No diagnostics after crash

**Diagnosis**:
```bash
# Check LSP logs
tail -f ~/.cure/lsp.log

# Look for crash reason
grep -i "error\|crash\|exception" ~/.cure/lsp.log
```

**Solutions**:

#### 1. Enable Debug Mode
```bash
CURE_LSP_LOG_LEVEL=debug cure-lsp-server
```

#### 2. Check for Known Issues
```bash
# Check if it's a known bug
cure-lsp-server --check-known-issues
```

#### 3. Reduce Concurrent Verification
```erlang
% Limit background tasks
#{
    max_concurrent => 2  % Default: 4
}
```

#### 4. Disable Problematic Features
```erlang
#{
    features => #{
        hover => true,
        code_actions => true,
        diagnostics => false  % Disable if causing crashes
    }
}
```

---

### 6. Slow Editor Performance

**Symptoms**:
- Lag when typing
- Delayed diagnostics
- Editor feels sluggish

**Diagnosis**:
```erlang
cure_lsp_performance:get_stats().
% Check:
% - cache_hit_rate (should be >0.8)
% - avg_verify_time_ms (should be <100ms)
% - queue_size (should be <10)
```

**Solutions**:

#### 1. Check Cache Hit Rate
```erlang
Stats = cure_lsp_performance:get_stats(),
HitRate = maps:get(cache_hit_rate, Stats).
% If <0.8, increase cache size
```

#### 2. Adjust Batch Timing
```erlang
% Process batches more frequently
cure_lsp_performance:start_link(#{
    batch_timeout_ms => 25  % Default: 50
}).
```

#### 3. Disable Real-time Verification
Use on-save verification instead:
```erlang
#{
    verify_on_change => false,
    verify_on_save => true
}
```

#### 4. Profile Slow Code
```bash
# Find slow constraints
CURE_LSP_PROFILE=true cure-lsp-server
```

---

### 7. Pattern Exhaustiveness False Positives

**Symptoms**:
- "Non-exhaustive pattern" error when all cases covered
- Suggested missing case doesn't make sense

**Example**:
```cure
match (x, y) with
| (true, true) -> "both"
| (true, false) -> "x only"
| (false, true) -> "y only"
| (false, false) -> "neither"
end
% Error: Non-exhaustive (but it is!)
```

**Solutions**:

#### 1. Check SMT Logic
Some patterns require specific SMT logics:
```erlang
% Ensure correct logic is used
#{
    smt_logic => 'QF_LIA'  % For booleans and integers
}
```

#### 2. Add Redundant Pattern
```cure
% Add explicit wildcard to satisfy checker
match (x, y) with
| (true, true) -> "both"
| (true, false) -> "x only"
| (false, true) -> "y only"
| (false, false) -> "neither"
| _ -> error("impossible")  % Redundant but helps SMT
end
```

#### 3. Disable for Specific Match
```cure
// @exhaustiveness-disable
match complex_value with
...
end
```

---

### 8. Counterexample Not Helpful

**Symptoms**:
- Counterexample shows `<unknown>`
- Values don't make sense
- Can't reproduce issue manually

**Example**:
```cure
// Error: Constraint violated
// Counterexample: x = <unknown>
```

**Solutions**:

#### 1. Simplify Constraint
Complex constraints may not produce good counterexamples:
```cure
% Instead of
type Complex = Int when f(g(h(x))) > 0

% Use
type Simple = Int when x > threshold
```

#### 2. Add Intermediate Variables
```cure
def process(x: Int) =
    let step1 = f(x)
    let step2 = g(step1)
    let step3 = h(step2)
    assert step3 > 0
    ...
```

#### 3. Enable Model Generation
```erlang
#{
    solver_options => #{
        produce_models => true
    }
}
```

---

### 9. Quick Fixes Not Appearing

**Symptoms**:
- Error shown but no quick fixes offered
- "No code actions available"

**Solutions**:

#### 1. Check Code Action Support
```erlang
% Verify code actions are enabled
#{
    features => #{
        code_actions => true
    }
}
```

#### 2. Check Diagnostic Code
Quick fixes only work for specific error codes:
- `refinement-violation`
- `non-exhaustive-pattern`
- `type-mismatch`
- `undefined-var`

#### 3. Cursor Position
Ensure cursor is on the error (red squiggle).

#### 4. Restart LSP
Sometimes code actions cache gets stale.

---

### 10. Integration with Build System

**Symptoms**:
- LSP works but compilation fails
- Different errors in IDE vs command line

**Solutions**:

#### 1. Sync Configurations
Ensure LSP and compiler use same settings:
```erlang
% In both .cure-lsp.config and rebar.config
#{
    smt => #{
        enabled => true,
        timeout => 500
    }
}
```

#### 2. Check Include Paths
```erlang
% LSP needs same include paths as compiler
#{
    include_dirs => [
        "src",
        "include",
        "deps/*/include"
    ]
}
```

#### 3. Run Full Build
```bash
# Clean build to ensure consistency
make clean && make all
```

---

## Performance Benchmarks

### Expected Performance

| Operation | Target | Acceptable | Slow |
|-----------|--------|------------|------|
| Cache hit | <10ms | <50ms | >100ms |
| Simple constraint | <50ms | <100ms | >200ms |
| Complex constraint | <200ms | <500ms | >1000ms |
| Full document | <500ms | <1s | >2s |
| Startup | <100ms | <200ms | >500ms |

### Measuring Performance

```erlang
% Get detailed stats
Stats = cure_lsp_performance:get_stats(),
io:format("Cache hit rate: ~p~n", [maps:get(cache_hit_rate, Stats)]),
io:format("Avg verify time: ~pms~n", [maps:get(avg_verify_time_ms, Stats)]),
io:format("Queue size: ~p~n", [maps:get(queue_size, Stats)]).
```

### Optimization Checklist

- [ ] Z3 version 4.8.0 or newer
- [ ] Cache hit rate >80%
- [ ] Average verification <100ms
- [ ] Queue size typically <5
- [ ] Memory usage <500MB
- [ ] No timeout errors

---

## Debug Workflows

### Workflow 1: Trace Specific Error

```bash
# 1. Enable debug logging
export CURE_LSP_LOG_LEVEL=debug
export CURE_LSP_TRACE_FILE=~/cure-trace.log

# 2. Reproduce issue

# 3. Check trace
grep "refinement-violation" ~/cure-trace.log

# 4. Extract SMT query
grep "SMT Query" ~/cure-trace.log -A 20
```

### Workflow 2: Profile Slow Constraint

```bash
# 1. Enable profiling
export CURE_LSP_PROFILE=true

# 2. Open slow file in IDE

# 3. Check profile
cat ~/.cure/profile.log | sort -k3 -n
# Column 3 is verification time
```

### Workflow 3: Test SMT Query Manually

```bash
# 1. Extract query from logs
grep "SMT Query" ~/.cure/lsp.log -A 30 > query.smt2

# 2. Run Z3 directly
z3 query.smt2

# 3. Check output
# sat = constraint satisfiable
# unsat = constraint violated
# unknown = timeout or undecidable
```

---

## Getting Help

### Before Filing an Issue

1. **Check logs**: `~/.cure/lsp.log`
2. **Verify Z3**: `z3 --version`
3. **Try minimal example**: Reproduce with smallest code
4. **Check known issues**: https://github.com/cure-lang/cure/issues

### What to Include in Bug Report

```markdown
**Cure Version**: `cure --version`
**Z3 Version**: `z3 --version`
**OS**: Ubuntu 22.04 / macOS 13 / etc.
**IDE**: VS Code 1.85 / Neovim 0.9 / etc.

**Expected**: [what should happen]
**Actual**: [what actually happens]

**Minimal Example**:
```cure
type Positive = Int when x > 0
def test(n: Int) = divide(1, n)  % Error here
```

**Logs**:
[attach relevant log section]
```

### Community Resources

- **GitHub Issues**: https://github.com/cure-lang/cure/issues
- **Discussions**: https://github.com/cure-lang/cure/discussions
- **Discord**: [invite link]
- **Stack Overflow**: Tag `cure-lang`

---

## Advanced Debugging

### Attach to Running LSP

```bash
# Find LSP process
ps aux | grep cure-lsp-server

# Attach debugger
gdb -p <pid>

# Or use Erlang debugger
erl -name debug@localhost -setcookie cure
# In Erlang shell:
> net_adm:ping('cure-lsp@localhost').
> debugger:start().
```

### Enable SMT Solver Tracing

```erlang
% In config
#{
    solver_options => #{
        trace => true,
        trace_file => "/tmp/z3-trace.log"
    }
}
```

### Dump AST for Debugging

```erlang
% In Cure code
// @dump-ast
def problematic_function(x) = ...
```

This generates `function_name.ast.txt` with full AST.

---

**Still stuck? File an issue with details! 🐛**
