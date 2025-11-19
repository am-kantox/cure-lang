# Known Issue: 07_fsm_verification.cure

## Status
**NOT COMPILING** - Type inference issue

## Problem
The example `07_fsm_verification.cure` demonstrates multiple FSM definitions and verification concepts but currently fails to compile due to a type inference limitation.

## Error
```
Type Checking failed: {type_check_failed,
    [{typecheck_error,"Failed to infer function body type",
         {location,114,3,undefined},
         {inference_failed,
             {type_inference_failed,
                 {unbound_variable,counter_fsm,
                     {location,135,14,undefined}}}}}]}
```

## Root Cause
The Cure type checker has difficulty with:
1. **Multiple FSM definitions in one module** - Defining 4 different FSMs (`CounterState`, `LightState`, `WorkflowState`, `DoorState`) in a single module
2. **Complex let bindings in long functions** - The main function is 170+ lines with multiple FSM spawns and state queries
3. **Variable scoping in large functions** - Type inference loses track of `let` bindings in complex control flow

## Workaround Options

### Option 1: Split into Multiple Modules
Create separate modules for each FSM:
- `CounterFSM.cure` - Deadlock detection example
- `TrafficLightFSM.cure` - Reachability analysis
- `WorkflowFSM.cure` - Liveness properties
- `DoorLockFSM.cure` - Safety properties

### Option 2: Simplify the Main Function
Break the large `main/0` function into smaller helper functions:
```cure
def main(): Int =
  demo_deadlock_detection()
  demo_reachability()
  demo_liveness()
  demo_safety()
  0

def demo_deadlock_detection(): Int = ...
def demo_reachability(): Int = ...
# etc
```

### Option 3: Use Single FSM Example
Reduce to just one FSM demonstration per file (similar to `06_fsm_traffic_light.cure`).

## Working Examples
These FSM examples DO compile and work correctly:
- ✅ `06_fsm_traffic_light.cure` - Basic FSM with single definition
- ✅ `06_fsm_traffic_light_enhanced.cure` - Enhanced FSM with multiple states and events

## Future Fix
This issue will be resolved when the Cure type checker is enhanced to:
1. Support multiple FSM definitions per module
2. Handle longer function bodies with complex let bindings
3. Improve variable scoping analysis in type inference

## How to Use This Example
For now, use this file as **documentation and reference** for FSM verification concepts rather than a runnable example. The concepts demonstrated are:
- Deadlock detection
- Reachability analysis  
- Liveness properties
- Safety properties

Refer to the working examples (`06_fsm_traffic_light.cure` and `06_fsm_traffic_light_enhanced.cure`) for compilable FSM code.
