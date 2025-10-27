# FSM Guard Verification Enhancements

## Overview

Enhanced the Cure FSM type checker to include comprehensive guard verification functionality. The TransitionGraph data structure was upgraded to store guard and action information from StateDefs, enabling full verification of transition guards using SMT solver integration.

## Changes Made

### 1. Enhanced TransitionGraph Structure

**Previous Format:**
```erlang
TransitionGraph :: #{state() => [{event(), target_state()}]}
```

**New Format:**
```erlang
TransitionGraph :: #{state() => [{event(), guard(), action(), target_state()}]}
```

The enhanced format now includes:
- `guard` - The guard expression from transitions (undefined if no guard)
- `action` - The action to execute on transition (undefined if no action)

### 2. Updated Core Functions

All functions that work with the TransitionGraph were updated to handle the new 4-tuple format:

#### `build_transition_graph/1`
- **Location:** `cure_typechecker.erl:1440-1456`
- **Change:** Now extracts and stores guard and action information from `#transition` records
- **Format:** Builds edges as `{Event, Guard, Action, Target}` tuples

#### `bfs_reachability/3`
- **Location:** `cure_typechecker.erl:1463-1479`
- **Change:** Pattern matches on 4-tuple format `{_Event, _Guard, _Action, Target}`
- **Purpose:** Maintains correct state reachability analysis

#### `group_by_event/1`
- **Location:** `cure_typechecker.erl:1555-1565`
- **Change:** Extracts events while ignoring guard/action data
- **Purpose:** Groups transitions by event name for determinism checking

#### `build_reverse_transition_graph/1`
- **Location:** `cure_typechecker.erl:3009-3026`
- **Change:** Handles 4-tuple format in reverse graph construction
- **Purpose:** Enables backward reachability for liveness checking

### 3. Guard Verification Implementation

#### `verify_guard_constraints/3`
- **Location:** `cure_typechecker.erl:3037-3112`
- **Previous:** Placeholder implementation with TODO comment
- **Current:** Full implementation with two-step verification:

**Step 1: Individual Guard Satisfiability**
```erlang
% Extract all transitions with guards
AllTransitionsWithGuards = maps:fold(
    fun(FromState, Transitions, Acc) ->\
        TransitionsForState = [
            {FromState, Event, Guard, Target}
         || {Event, Guard, _Action, Target} <- Transitions,
            Guard =/= undefined
        ],
        TransitionsForState ++ Acc
    end,
    [],
    TransitionGraph
)
```

Each guard is verified using `verify_single_guard/2` which:
1. Converts the guard to SMT constraints
2. Checks satisfiability using the SMT solver
3. Returns `ok`, `{error, Reason}`, or `{warning, Reason}`

**Step 2: Guard Conflict Detection**
```erlang
ConflictResults = maps:fold(
    fun(FromState, Transitions, Acc) ->\n        % Extract transitions for conflict checking
        TransitionsForCheck = [
            {Event, Guard, Target}
         || {Event, Guard, _Action, Target} <- Transitions
        ],
        case check_conflicting_guards(TransitionsForCheck, Env) of
            ok -> Acc;
            {warning, Warning} -> [{FromState, Warning} | Acc];
            {error, Error} -> [{error, {FromState, Error}} | Acc]
        end
    end,
    [],
    TransitionGraph
)
```

Checks for overlapping guards on the same event from the same state.

### 4. Helper Functions

#### `verify_single_guard/2`
- **Location:** `cure_typechecker.erl:3114-3136`
- Converts guard expressions to SMT constraints
- Verifies satisfiability using `check_smt_satisfiability/1`
- Returns appropriate result or warning

#### `check_conflicting_guards/2`
- **Location:** `cure_typechecker.erl:3147-3169`
- Groups transitions by event using `group_transitions_by_event/1`
- Checks each event's transitions for guard conflicts
- Returns `ok` or `{warning, {guard_conflicts, Results}}`

#### `group_transitions_by_event/1`
- **Location:** `cure_typechecker.erl:3171-3179`
- Groups transitions by event name
- Preserves guard and target information for conflict analysis

#### `check_guards_conflict/2`
- **Location:** `cure_typechecker.erl:3181-3199`
- Verifies guards for the same event are mutually exclusive
- Uses `all_guards_mutually_exclusive/2` for verification
- Returns `ok`, `{warning, ...}`, or `unknown`

### 5. SMT Solver Integration

Enhanced `cure_smt_solver` module to export `inequality_constraint/3`:

```erlang
-export([
    % ... existing exports ...
    inequality_constraint/3,  % NEW EXPORT
    % ... more exports ...
]).

inequality_constraint(Left, Op, Right) ->\n    #smt_constraint{\n        type = inequality,
        left = Left,
        op = Op,
        right = Right,
        location = undefined
    }.
```

This function creates inequality constraints for guard conditions like `x > 0`, `n >= 5`, etc.

## Usage Example

```cure
fsm DemoFSM {
    states [idle, active]
    initial idle
    
    state idle {
        -- Transition with guard: only activate when x > 0
        on start when x > 0 -> active
    }
    
    state active {
        -- Unconditional transition back
        on stop -> idle
    }
}
```

The type checker now:
1. ✓ Extracts guard `x > 0` from the transition
2. ✓ Verifies the guard is satisfiable (not contradictory)
3. ✓ Checks for conflicting guards on the same event
4. ✓ Provides detailed error messages if guards are unsatisfiable
5. ✓ Warns about overlapping guards (non-determinism)

## Testing

A demo test file is available at `test/fsm_guard_verification_demo.erl` demonstrating:
- FSM creation with guarded transitions
- Type checking with guard verification
- Successful verification output

To run:
```bash
cd /opt/Proyectos/Ammotion/cure
erlc -I src/parser -I src/types -o _build/ebin test/fsm_guard_verification_demo.erl
erl -pa _build/ebin -noshell -s fsm_guard_verification_demo run -s init stop
```

Expected output:
```
=== FSM Guard Verification Demo ===

Checking FSM with guard verification...
✓ FSM type checking PASSED
  - Guards verified successfully
  - Warnings: 0
  - No warnings

=== Demo Complete ===
```

## Benefits

1. **Early Error Detection:** Catches unsatisfiable guards at compile time
2. **Non-determinism Warnings:** Identifies potential runtime issues with overlapping guards
3. **SMT Integration:** Leverages formal methods for rigorous verification
4. **Comprehensive Analysis:** Verifies both individual guards and their interactions
5. **Detailed Reporting:** Provides clear error messages with state and transition context

## Future Enhancements

1. **Advanced SMT Solving:** Integrate external SMT solvers (Z3, CVC4) for complex constraints
2. **Guard Minimization:** Suggest simplified equivalent guards
3. **Coverage Analysis:** Verify that guards cover all possible input cases
4. **Performance Optimization:** Cache guard verification results for repeated patterns
5. **Guard Inference:** Automatically infer missing guards from FSM properties

## Related Files

- `src/types/cure_typechecker.erl` - Main type checker with FSM verification
- `src/types/cure_smt_solver.erl` - SMT constraint solving
- `src/parser/cure_ast.hrl` - AST definitions including `#transition{}` record
- `test/fsm_guard_verification_demo.erl` - Demonstration test
