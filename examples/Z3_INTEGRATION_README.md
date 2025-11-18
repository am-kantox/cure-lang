# Z3 SMT Integration Example

This directory contains `z3_integration_demo.cure`, a comprehensive example demonstrating all Z3 SMT solver features in the Cure programming language.

## Overview

The Z3 integration provides compile-time verification and real-time LSP diagnostics for:

1. **Pattern Exhaustiveness Checking** - Ensures all cases are covered
2. **Guard Optimization** - Simplifies and optimizes boolean expressions
3. **FSM Verification** - Detects deadlocks, unreachable states, and temporal properties
4. **Refinement Types** - Verifies type constraints at compile time

## Features Demonstrated

### 1. Pattern Exhaustiveness (Phase 5.1)

```cure
def classify_bool(x: Bool): String =
  match x do
    true -> "Yes"
    false -> "No"
  end
  # ✅ Z3 verifies: All Bool cases covered
```

**What Z3 Does:**
- Encodes patterns as SMT constraints
- Searches for missing cases using Z3's model finder
- Synthesizes counter-examples for incomplete matches
- Reports via LSP in real-time

**Try It:**
- Uncomment the `bad_classify` function to see LSP error for missing pattern

### 2. Guard Optimization (Phase 5.3)

```cure
def redundant_check(x: Int): Bool =
  # Before: true && x > 10 && x > 0
  # After Z3 optimization: x > 10
  # (because x > 10 implies x > 0)
  ...
```

**What Z3 Does:**
- Algebraic simplification: `true AND X → X`
- Redundancy elimination using implication checking
- Cost-based reordering (cheap checks first)
- Multi-pass convergence

**Optimizations Applied:**
- Identity laws
- Idempotency (`X AND X → X`)
- Double negation elimination
- Constant folding

### 3. FSM Verification (Phase 5.2)

#### Traffic Light FSM

```cure
fsm TrafficData{cycles: 0} do
  Red --> |timer| Green
  Green --> |timer| Yellow  
  Yellow --> |timer| Red
end
```

**Z3 Verification:**
- ✅ All states reachable from Red
- ✅ No deadlocks (every state has exits)
- ✅ Cyclic behavior (returns to Red)

#### Protocol FSM with Error Handling

```cure
fsm ProtocolData{retries: 0} do
  Disconnected --> |connect| Connecting
  Connecting --> |success| Connected
  Connecting --> |failure| Error
  Connected --> |disconnect| Disconnected
  Error --> |retry| Connecting
  Error --> |give_up| Disconnected
end
```

**Z3 Verification:**
- ✅ All states reachable
- ✅ Error recovery paths exist
- ✅ No deadlocks

**Try It:**
- Uncomment the `DeadlockData` FSM to see LSP diagnostics for:
  - Deadlocked states (no outgoing transitions)
  - Unreachable states

### 4. Guard Patterns

```cure
def classify_number(n: Int): String =
  match n do
    x when x > 0 -> "Positive"
    x when x < 0 -> "Negative"
    0 -> "Zero"
  end
  # ✅ Z3 verifies: All Int values covered
```

**What Z3 Does:**
- Encodes guards as SMT formulas
- Checks union of all guards covers the type
- Finds gaps in coverage
- Suggests missing guards

## Compilation

### Standard Compilation

```bash
cure compile examples/z3_integration_demo.cure
```

### With Verification Enabled

```bash
cure compile --verify examples/z3_integration_demo.cure
```

**Compiler Output:**
```
Compiling z3_integration_demo.cure...

Pattern Verification:
  ✓ classify_bool: exhaustive
  ✓ classify_option: exhaustive
  ✓ classify_number: exhaustive (with guards)

FSM Verification:
  ✓ TrafficData FSM: All states reachable, no deadlocks
  ✓ ProtocolData FSM: All states reachable, error recovery available

Guard Optimization:
  ✓ redundant_check: Simplified (3 guards → 1 guard)
  ✓ complex_guard: Optimized (redundant checks removed)

Compilation successful!
Generated: z3_integration_demo.beam
```

## LSP Integration

### Setup

1. Start the Cure LSP server:
```bash
cure-lsp --port 7777
```

2. Configure your IDE to use the Cure LSP server

3. Open `z3_integration_demo.cure`

### Real-Time Diagnostics

The LSP server provides instant feedback:

#### Pattern Errors

Uncomment `bad_classify`:
```cure
def bad_classify(x: Bool): String =
  match x do
    true -> "Yes"
    # Missing: false
  end
```

**LSP Diagnostic:**
```
Error [line 30]: Incomplete pattern match
  Missing pattern: false
  Severity: Error (1)
  Source: cure-pattern-checker
```

#### FSM Deadlock

Uncomment the problematic FSM:
```cure
fsm DeadlockData{count: 0} do
  Start --> |begin| Active
  Active --> |finish| Done
  # Done has no outgoing transitions
end
```

**LSP Diagnostics:**
```
Error [line 117]: State 'Done' has a deadlock
  Message: No outgoing transitions
  Severity: Error (1)
  Source: cure-fsm-verifier
```

#### Unreachable States

```cure
fsm BadFsm{x: 0} do
  A --> |event| B
  # C is never reached
end
```

**LSP Diagnostic:**
```
Warning [line X]: Unreachable state 'C'
  Message: No path from initial state
  Severity: Warning (2)
  Source: cure-fsm-verifier
```

## Running the Example

```bash
# Compile
make all

# Run the demonstration
erl -pa _build/ebin -pa _build/lib/std -eval 'Z3Demo:main(), init:stop().'
```

**Expected Output:**
```
=== Z3 SMT Integration Demo ===

1. Pattern Exhaustiveness
  ✅ Bool patterns exhaustive
  ✅ Option patterns exhaustive

2. Guard Optimization
  ✅ Guards optimized by Z3

3. FSM Verification - Traffic Light
  ✅ Traffic FSM verified:
    - All states reachable
    - No deadlocks
    - Cyclic behavior
  State transitions: Red → Green → Yellow → Red

4. FSM Verification - Protocol
  ✅ Protocol FSM verified:
    - All states reachable
    - Error recovery available
    - No deadlocks

5. Pattern Guards
  ✅ Guard patterns exhaustive

=== All Z3 Features Demonstrated ===

Compile-time verification provided:
  ✓ Pattern exhaustiveness
  ✓ Guard optimization
  ✓ FSM deadlock detection
  ✓ FSM reachability
  ✓ FSM liveness properties

LSP provides real-time diagnostics for:
  • Missing pattern cases
  • Unreachable FSM states
  • FSM deadlocks
  • Guard redundancy
```

## How It Works

### Compilation Pipeline

```
┌─────────────────┐
│  Cure Source    │
│  (.cure file)   │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  Parser (AST)   │
└────────┬────────┘
         │
         ▼
┌─────────────────────────────────────────┐
│         Z3 Verification                 │
│  ┌──────────────┐  ┌────────────────┐  │
│  │  Pattern     │  │  Guard         │  │
│  │  Checker     │  │  Optimizer     │  │
│  └──────────────┘  └────────────────┘  │
│  ┌──────────────┐  ┌────────────────┐  │
│  │  FSM         │  │  Refinement    │  │
│  │  Verifier    │  │  Types         │  │
│  └──────────────┘  └────────────────┘  │
└─────────┬───────────────────────────────┘
          │
          ▼
   ┌──────────────┐
   │  SMT-LIB     │
   │  Queries     │
   └──────┬───────┘
          │
          ▼
   ┌──────────────┐
   │  Z3 Solver   │
   └──────┬───────┘
          │
          ▼
   ┌──────────────┐
   │  Diagnostics │
   │  & Results   │
   └──────────────┘
```

### LSP Flow

```
┌─────────────┐       ┌─────────────┐
│    IDE      │◄─────►│  LSP Server │
│  (Editor)   │ JSON  │  (Cure)     │
└─────────────┘  RPC  └──────┬──────┘
                              │
                              ▼
                      ┌───────────────┐
                      │  Z3 Verifiers │
                      │  - Pattern    │
                      │  - FSM        │
                      │  - Guards     │
                      └───────┬───────┘
                              │
                              ▼
                      ┌───────────────┐
                      │  Diagnostics  │
                      │  (Real-time)  │
                      └───────────────┘
```

## Test Statistics

From the comprehensive test suite:

| Feature | Tests | Status |
|---------|-------|--------|
| Pattern Exhaustiveness | 13/13 | ✅ 100% |
| FSM Verification | 8/8 | ✅ 100% |
| Guard Optimization | 9/9 | ✅ 100% |
| Refinement Types | 21/21 | ✅ 100% |
| LSP Integration | 6/6 | ✅ 100% |
| Comprehensive Tests | 6/6 | ✅ 100% |
| **Total** | **63/63** | **✅ 100%** |

## Performance

From benchmarks on this example:

- **Pattern checking**: ~29ms for complex patterns
- **Guard optimization**: <1ms for typical guards
- **FSM verification**: <50ms for typical FSMs
- **All operations**: Well under 1 second

## Additional Resources

- [Z3 Integration Complete Documentation](../docs/Z3_INTEGRATION_COMPLETE.md)
- [Phase 3-5 Roadmap](../docs/Z3_PHASE_3_5_ROADMAP.md)
- [Cure Language Specification](../README.md)
- [Z3 Theorem Prover](https://github.com/Z3Prover/z3)

## Troubleshooting

### Z3 Not Found

```bash
# Install Z3
sudo apt install z3  # Ubuntu/Debian
brew install z3       # macOS
```

### LSP Not Reporting Diagnostics

1. Check LSP server is running: `ps aux | grep cure-lsp`
2. Verify IDE LSP client is configured correctly
3. Check LSP logs: `~/.cure/lsp.log`

### Compilation Errors

```bash
# Rebuild with verbose output
make clean && make all VERBOSE=1
```

## Contributing

To add more Z3 verification examples:

1. Create a new function demonstrating the feature
2. Add comments explaining what Z3 verifies
3. Include both working and intentionally broken examples
4. Update this README with the new feature

## License

See the main Cure repository license.
