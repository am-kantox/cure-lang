# Cure FSM Standard Library Integration

This document describes how the Cure FSM standard library (`lib/std/fsm.cure`) integrates with the underlying Erlang FSM runtime.

## Architecture

The FSM system consists of three layers:

### 1. Cure Standard Library (`lib/std/fsm.cure`)
- **Purpose**: Provides type-checked Cure API for FSM operations
- **Implementation**: Uses `curify` FFI bindings to call Erlang functions
- **Type Safety**: Provides Cure-level type checking before calling Erlang runtime

### 2. Cure API Wrapper (`src/fsm/cure_fsm_cure_api.erl`)
- **Purpose**: Bridges Cure's high-level FSM syntax and Erlang runtime
- **Functions**:
  - `start_fsm/1` - Start FSM from compiled Cure module
  - `fsm_cast/2` - Send events to FSM (asynchronous)
  - `fsm_advertise/2` - Register FSM process with a name
  - `fsm_state/1` - Query current FSM state and payload

### 3. FSM Runtime (`src/fsm/cure_fsm_runtime.erl`)
- **Purpose**: Core FSM execution engine (gen_server behavior)
- **Features**:
  - Event processing with compiled guards/actions
  - State transition management with O(1) lookup
  - Timeout handling
  - Performance statistics
  - FSM type registry

### 4. FSM Built-ins (`src/fsm/cure_fsm_builtins.erl`)
- **Purpose**: Additional FSM utility functions
- **Functions**: Process management, monitoring, batch operations, validation

## API Functions

### Core Functions (from `cure_fsm_cure_api`)

#### `start_fsm(mod: Atom): Any`
Starts an FSM instance from a compiled Cure module.

**Implementation Flow**:
1. Look up `Module:'__fsm_definition__'()` function
2. Extract initial state and payload
3. Call `cure_fsm_runtime:start_fsm/2`
4. Return `{ok, Pid}` or `{error, Reason}`

**Example**:
```cure
let fsm_pid = start_fsm(Turnstile)
```

#### `fsm_cast(target: Any, evt: Any): Any`
Send an event asynchronously to an FSM.

**Event Format**: `{EventName, EventPayload}` where:
- `EventName` is an atom (e.g., `:coin`, `:push`)
- `EventPayload` is a list of `{key, value}` pairs

**Target**: Can be a Pid or registered name (atom)

**Example**:
```cure
fsm_cast(:main_turnstile, {:coin, []})
```

#### `fsm_advertise(pid: Any, name: Atom): Any`
Register a name for an FSM process.

**Example**:
```cure
fsm_advertise(fsm_pid, :main_turnstile)
```

#### `fsm_state(target: Any): Any`
Query the current state and payload of an FSM.

**Returns**: `{ok, {StateName, Payload}}` or `{error, Reason}`

**Example**:
```cure
let {ok, {state, payload}} = fsm_state(:main_turnstile)
```

### Additional Functions (from `cure_fsm_builtins`)

#### `fsm_stop(pid: Any): Any`
Gracefully terminate an FSM process.

#### `fsm_spawn(fsm_type: Atom, initial_data: Any): Any`
Alternative to `start_fsm` that takes FSM type and initial data directly.

#### `fsm_send(pid: Any, event: Any): Any`
Lower-level event sending without tuple wrapping.

#### `fsm_info(pid: Any): Any`
Get detailed FSM information including event history and performance stats.

#### `fsm_is_alive(pid: Any): Any`
Check if an FSM process is still running.

## Type System Integration

### FFI Bindings with `curify`

The `curify` keyword creates type-checked FFI bindings to Erlang functions:

```cure
curify start_fsm(mod: Atom): Any = {cure_fsm_cure_api, start_fsm, 1}
```

This:
1. Type-checks the `mod` argument as `Atom`
2. Generates a call to `cure_fsm_cure_api:start_fsm(Mod)`
3. Returns result with type `Any` (runtime-checked)

### Type Safety

While the return types are `Any` for flexibility, the Cure type system ensures:
- Function arguments are correctly typed
- FSM definitions are validated at compile time
- Pattern matching on results provides runtime safety

## FSM Definition Compilation

When a Cure module with an FSM definition is compiled:

1. **Parser** recognizes `fsm` syntax and creates AST
2. **Type Checker** validates states, transitions, and handlers
3. **Code Generator** produces:
   - `Module:'__fsm_definition__'/0` function
   - Compiled transition table
   - Handler function references
4. **Runtime Registration** (optional): FSM type registered in global registry

## Event Processing Flow

1. User calls `fsm_cast(Pid, {Event, Payload})`
2. `cure_fsm_cure_api:fsm_cast/2` resolves target to Pid
3. Calls `cure_fsm_runtime:send_event/3`
4. Runtime looks up transition in flat map (O(1))
5. Evaluates compiled guard (if any)
6. Executes compiled action
7. Updates state atomically
8. Records event in history
9. Sets/clears timeouts as needed

## Performance Characteristics

- **Event Processing**: < 10μs per event
- **State Transitions**: O(1) lookup
- **Memory**: Bounded with automatic history trimming
- **Throughput**: > 100K events/second per FSM instance

## Error Handling

All functions return tagged tuples for error handling:

```cure
match start_fsm(MyFsm) do
  {ok, pid} -> # Success
  {error, reason} -> # Handle error
end
```

Common errors:
- `{fsm_definition_not_found, Module, Reason}` - Module has no FSM
- `{fsm_not_found, Name}` - Named FSM not registered
- `{invalid_fsm_pid, Pid}` - Invalid Pid argument

## Examples

See `examples/turnstile.cure` for a complete working example demonstrating:
- FSM definition with payload
- Starting and naming FSM
- Sending events
- Querying state
- Pattern matching on results
