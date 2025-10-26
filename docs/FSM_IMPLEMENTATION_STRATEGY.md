# FSM Implementation Strategy

This document describes the implementation strategy for Cure's FSM system with Mermaid-style syntax, gen_server runtime, and SMT verification.

## Overview

The FSM implementation consists of several layers:

1. **Parser** - Parse `fsm RecordType{...} do ... end` blocks
2. **Type Checker** - Validate FSM definitions with SMT verification
3. **Code Generator** - Compile to Erlang/BEAM code
4. **Runtime** - Gen_server-based FSM execution
5. **Standard Library** - Cure-level FSM API

## Architecture

```
┌─────────────────────┐
│  Cure Source Code   │
│  (turnstile.cure)   │
└──────────┬──────────┘
           │
           ▼
┌─────────────────────┐
│   Lexer & Parser    │ ← Parse FSM syntax
│  (cure_parser.erl)  │
└──────────┬──────────┘
           │
           ▼
┌─────────────────────┐
│     AST Nodes       │
│  #fsm_def{}, etc.   │
└──────────┬──────────┘
           │
           ▼
┌─────────────────────┐
│   Type Checker &    │ ← SMT verification
│  SMT Verification   │
│(cure_typechecker)   │
└──────────┬──────────┘
           │
           ▼
┌─────────────────────┐
│   Code Generator    │ ← Generate Erlang
│ (cure_codegen.erl)  │
└──────────┬──────────┘
           │
           ▼
┌─────────────────────┐
│  Erlang BEAM Code   │
│  + FSM Definition   │
└──────────┬──────────┘
           │
           ▼
┌─────────────────────┐
│   Runtime System    │
│ (cure_fsm_runtime)  │ ← Gen_server processes
│ (cure_fsm_cure_api) │
└─────────────────────┘
```

## 1. Parser Implementation

### FSM Syntax

```cure
module Turnstile do
  record TurnstilePayload do
    coins_inserted: Int
    people_passed: Int
  end
  
  fsm TurnstilePayload{coins_inserted: 0, people_passed: 0} do
    Locked --> |coin| Unlocked
    Locked --> |push| Locked
    Unlocked --> |push| Locked
  end
  
  def coin(from: StateName, event: Event, payload: TurnstilePayload): Result(State, FsmError) =
    Ok({:Unlocked, updated_payload})
end
```

### Parser Changes

File: `src/parser/cure_parser.erl`

Add parsing for:

1. **FSM Declaration**: `fsm RecordType{field: value, ...} do ... end`
   - Parse record type name and initial payload
   - Parse transition list

2. **Transition Syntax**: `State --> |event| TargetState`
   - Left side: State name (atom)
   - Middle: Event name between pipes (|event|)
   - Right side: Target state name (atom)

3. **AST Generation**:
   ```erlang
   #fsm_def{
       name = TurnstilePayload,  % Record type name
       initial_payload = #{coins_inserted => 0, people_passed => 0},
       states = [Locked, Unlocked],  % Extract from transitions
       initial = Locked,  % First state in transition list
       state_defs = [
           #state_def{
               name = Locked,
               transitions = [
                   #transition{event = coin, target = Unlocked, ...},
                   #transition{event = push, target = Locked, ...}
               ]
           },
           ...
       ]
   }
   ```

### Implementation Steps

1. Add `parse_fsm_definition/1` function
2. Add `parse_fsm_transition/1` for Mermaid syntax
3. Extract initial state (first in transition list)
4. Build state_defs from transition list
5. Store initial_payload from record literal

## 2. Type Checking with SMT Verification

### Type Checking Tasks

File: `src/types/cure_typechecker.erl`

1. **Payload Type Validation**
   - Verify record type exists
   - Check initial payload matches record fields
   - Validate field types

2. **State Validation**
   - Extract all state names from transitions
   - Verify states are atoms
   - Check for unreachable states

3. **Handler Signature Verification**
   - For each event in transitions, find corresponding handler function
   - Verify signature: `(StateName, Event, Payload) -> Result(State, FsmError)`
   - Check that handler returns correct types

4. **Transition Validation**
   - Verify all transitions reference valid states
   - Check for non-determinism (same from-state and event with different targets)
   - Validate this is intentional

### SMT Verification

File: `src/verification/cure_smt_solver.erl`

Add `verify_fsm_safety/1` function that checks:

1. **Reachability Analysis**
   - All states are reachable from initial state
   - Warn about unreachable states

2. **Deadlock Detection**
   - Check for states with no outgoing transitions
   - Verify intentional terminal states

3. **Handler Safety**
   - Verify handlers always return valid states
   - Check payload type consistency

4. **State Invariants** (if annotated)
   - Verify invariant properties hold in all reachable states

### Implementation

```erlang
check_fsm_definition(FsmDef, Env) ->
    % 1. Validate payload record type
    case validate_payload_type(FsmDef, Env) of
        {ok, PayloadType} ->
            % 2. Validate transitions and handlers
            case validate_transitions(FsmDef, PayloadType, Env) of
                {ok, ValidatedTransitions} ->
                    % 3. SMT verification
                    case cure_smt_solver:verify_fsm_safety(FsmDef) of
                        {ok, Warnings} ->
                            {ok, FsmDef, Warnings};
                        {error, Reason} ->
                            {error, {fsm_verification_failed, Reason}}
                    end;
                {error, Reason} ->
                    {error, Reason}
            end;
        {error, Reason} ->
            {error, Reason}
    end.
```

## 3. Code Generation

### Generated Code Structure

For each FSM definition, generate:

1. **FSM Definition Function**: `'__fsm_definition__'/0`
   - Returns #fsm_definition{} record
   - Includes initial state and payload
   - Maps transitions to handler functions

2. **Transition Table**:
   ```erlang
   transitions => #{
       {Locked, coin} => {Unlocked, undefined, fun coin/3},
       {Locked, push} => {Locked, undefined, fun push/3},
       ...
   }
   ```

3. **Handler Wrappers**:
   - Wrap Cure handler functions to match expected signature
   - Convert between Cure types and Erlang types

### Example Generated Code

```erlang
-module('Elixir.Turnstile').
-export(['__fsm_definition__'/0, coin/3, push/3]).

'__fsm_definition__'() ->
    #fsm_definition{
        name = 'Turnstile',
        states = ['Locked', 'Unlocked'],
        initial_state = 'Locked',
        initial_payload = #{coins_inserted => 0, people_passed => 0},
        transitions => #{
            {'Locked', coin} => {'Unlocked', undefined, fun coin/3},
            {'Locked', push} => {'Locked', undefined, fun push/3},
            {'Unlocked', push} => {'Locked', undefined, fun push/3}
        },
        timeouts => #{}
    }.

% Handler wrapper for coin event
coin(FromState, {EventName, EventPayload}, CurrentPayload) ->
    % Call the Cure-generated handler
    case 'coin__cure__'(FromState, {EventName, EventPayload}, CurrentPayload) of
        {ok, {NextState, NewPayload}} ->
            {NextState, undefined, NewPayload};  % Runtime format
        {error, Reason} ->
            error({fsm_handler_error, Reason})
    end.
```

### Code Generator Changes

File: `src/codegen/cure_codegen.erl`

1. Add `generate_fsm_definition/2` function
2. Generate `__fsm_definition__/0` export
3. Generate transition table with handler references
4. Generate handler wrappers

## 4. Runtime Integration

### FSM Runtime Modifications

File: `src/fsm/cure_fsm_runtime.erl`

**Already implemented**, but needs small adjustments:

1. Support `initial_payload` in `#fsm_definition{}`
2. Modify transition handler execution to:
   - Pass `(FromState, Event, CurrentPayload)` to handler
   - Expect `Result(State, FsmError)` return value
   - Extract `{NextState, NewPayload}` from `Ok({state, payload})`

### Handler Execution Flow

```erlang
handle_fsm_event(EventName, EventPayload, State) ->
    CurrentState = State#fsm_state.current_state,
    CurrentPayload = State#fsm_state.data,
    
    % Find transition
    case find_transition(CurrentState, EventName, State#fsm_state.transitions) of
        {ok, {_TargetState, _Guard, HandlerFun}} ->
            % Call handler
            Event = {EventName, EventPayload},
            case HandlerFun(CurrentState, Event, CurrentPayload) of
                {ok, {NextState, NewPayload}} ->
                    % Transition successful
                    State#fsm_state{
                        current_state = NextState,
                        data = NewPayload
                    };
                {error, Reason} ->
                    % Handler rejected transition
                    % Stay in current state
                    State
            end;
        {error, no_transition} ->
            % No transition found
            State
    end.
```

## 5. Standard Library Implementation

### Cure Wrapper

File: `lib/std/fsm.cure`

The functions are implemented as FFI calls to `cure_fsm_cure_api.erl`:

```cure
module Std.Fsm do
  export [start_fsm/1, fsm_cast/2, fsm_advertise/2, fsm_state/1]
  
  def start_fsm(module: Module): Pid =
    @ffi("cure_fsm_cure_api", "start_fsm", [module])
  
  def fsm_cast(target: Pid | FsmName, event: Event): None =
    @ffi("cure_fsm_cure_api", "fsm_cast", [target, event])
    
  def fsm_advertise(pid: Pid, name: FsmName): None =
    @ffi("cure_fsm_cure_api", "fsm_advertise", [pid, name])
    
  def fsm_state(target: Pid | FsmName): Result(State, FsmError) =
    @ffi("cure_fsm_cure_api", "fsm_state", [target])
end
```

## 6. Compilation Pipeline

### Full Pipeline

```
1. Lexer: cure_lexer.erl
   └─> Tokens

2. Parser: cure_parser.erl
   └─> AST with #fsm_def{}

3. Type Checker: cure_typechecker.erl
   ├─> Validate FSM definition
   ├─> Verify handler signatures
   └─> SMT verification via cure_smt_solver.erl

4. Code Generator: cure_codegen.erl
   ├─> Generate __fsm_definition__/0
   ├─> Generate transition table
   └─> Generate handler wrappers

5. BEAM Compiler: cure_beam_compiler.erl
   └─> Compile to .beam file

6. Runtime: cure_fsm_runtime.erl + cure_fsm_cure_api.erl
   └─> Execute FSM as gen_server
```

## 7. Testing Strategy

### Unit Tests

1. **Parser Tests**: `test/parser/fsm_parser_test.erl`
   - Test Mermaid-style transition parsing
   - Test initial payload extraction
   - Test error handling

2. **Type Checker Tests**: `test/types/fsm_typechecker_test.erl`
   - Test handler signature validation
   - Test payload type checking
   - Test SMT verification integration

3. **Codegen Tests**: `test/codegen/fsm_codegen_test.erl`
   - Test __fsm_definition__/0 generation
   - Test handler wrapper generation
   - Test transition table generation

4. **Runtime Tests**: `test/fsm/fsm_runtime_test.erl`
   - Test FSM lifecycle (start, stop)
   - Test event processing
   - Test state transitions
   - Test handler execution

### Integration Test

Compile and run `examples/turnstile.cure`:

```bash
make all
./cure compile examples/turnstile.cure
./cure run Turnstile.main
```

Expected output:
```
=== Turnstile FSM Demo ===
Initial state: Locked
...
Final State:
Coins inserted: 3
People passed: 1
Denied attempts: 1
```

## 8. Implementation Order

1. ✅ Update FSM runtime header with initial_payload field
2. ✅ Create cure_fsm_cure_api.erl wrapper
3. ⏳ Implement FSM parser (cure_parser.erl)
4. ⏳ Implement FSM type checking (cure_typechecker.erl)
5. ⏳ Implement SMT verification (cure_smt_solver.erl)
6. ⏳ Implement code generation (cure_codegen.erl)
7. ⏳ Update Std.Fsm with FFI calls
8. ⏳ Test with turnstile example
9. ⏳ Write comprehensive tests

## Next Steps

The immediate next task is to implement the FSM parser to recognize and parse the Mermaid-style syntax. This involves:

1. Adding lexer tokens for `-->` and `|`
2. Implementing `parse_fsm_definition/1` in cure_parser.erl
3. Generating proper AST nodes
4. Testing with simple examples
