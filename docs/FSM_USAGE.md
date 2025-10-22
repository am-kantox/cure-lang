# Cure FSM Usage Guide

This document provides comprehensive guidance on using Finite State Machines (FSMs) in the Cure programming language, both from Cure code and from the Erlang shell.

## Table of Contents

1. [Introduction](#introduction)
2. [FSM Concepts](#fsm-concepts)
3. [Defining FSMs in Cure](#defining-fsms-in-cure)
4. [Working with Payloads](#working-with-payloads)
5. [Guards and Actions](#guards-and-actions)
6. [Using FSMs from Cure Code](#using-fsms-from-cure-code)
7. [Using FSMs from Erlang Shell](#using-fsms-from-erlang-shell)
8. [Advanced Features](#advanced-features)
9. [Examples](#examples)

## Introduction

Cure provides first-class support for Finite State Machines (FSMs) as a core language feature. FSMs in Cure are:

- **Type-safe**: States and transitions are checked at compile time
- **Efficient**: O(1) state transition lookup with compiled guards and actions
- **Payload-aware**: Each FSM carries mutable payload data through transitions
- **Actor-based**: Built on BEAM processes with full OTP integration

## FSM Concepts

### Core Components

1. **States**: Named states the FSM can be in (e.g., `Idle`, `Running`, `Stopped`)
2. **Events**: Triggers that cause state transitions (e.g., `start`, `stop`, `timeout`)
3. **Transitions**: Rules that define how events move the FSM between states
4. **Guards**: Conditions that must be true for a transition to occur
5. **Actions**: Functions executed during transitions that can modify data and payload
6. **Payload**: Mutable data carried by the FSM across transitions

### FSM State Model

Each FSM instance maintains:

- **Current State**: The active state name
- **State Data**: Long-lived data specific to the FSM instance
- **Payload**: Short-lived data that actions can read and modify during transitions
- **Event History**: Recent transitions for debugging
- **Timeouts**: Automatic timeout-based transitions

## Defining FSMs in Cure

### Basic FSM Definition

```cure
fsm TrafficLight {
    states: [Green, Yellow, Red]
    initial: Green
    
    state Green {
        on timer -> Yellow
    }
    
    state Yellow {
        on timer -> Red
    }
    
    state Red {
        on timer -> Green
    }
}
```

### FSM with Guards

Guards are conditions that must be true for a transition to execute:

```cure
fsm Counter {
    states: [Zero, Positive, Negative]
    initial: Zero
    
    state Zero {
        on increment when data.value < 100 -> Positive
        on decrement -> Negative
    }
    
    state Positive {
        on increment when data.value < 100 -> Positive
        on decrement when data.value > 1 -> Positive
        on decrement when data.value == 1 -> Zero
    }
    
    state Negative {
        on increment -> Zero
        on decrement when data.value > -100 -> Negative
    }
}
```

### FSM with Actions

Actions are functions executed during transitions that can modify state data and payload:

```cure
fsm BankAccount {
    states: [Active, Frozen, Closed]
    initial: Active
    
    state Active {
        on deposit {
            action: |state, event| {
                let amount = event.amount;
                let new_balance = state.data.balance + amount;
                
                // Update state data
                state.data.balance = new_balance;
                
                // Update payload with transaction info
                payload.last_transaction = #{
                    type => deposit,
                    amount => amount,
                    timestamp => now()
                };
                
                {state.data, payload}
            }
        } -> Active
        
        on freeze -> Frozen
        on close -> Closed
    }
    
    state Frozen {
        on unfreeze -> Active
        on close -> Closed
    }
    
    state Closed {
        // Terminal state - no transitions out
    }
}
```

## Working with Payloads

Payloads are mutable data structures that can be modified by action functions during transitions. They are separate from state data and are designed for short-lived information that changes frequently.

### Payload Operations

Within action functions, you have access to payload operations:

```cure
action: |state, event| {
    // Load current payload
    let current_payload = payload;
    
    // Set entire payload
    payload = #{counter => 1, timestamp => now()};
    
    // Update specific field
    payload.counter = payload.counter + 1;
    
    // Get payload field
    let count = payload.counter;
    
    // Return both state data and modified payload
    {state.data, payload}
}
```

### Payload vs State Data

**Use State Data for:**
- Long-lived information (user ID, account balance, configuration)
- Data that defines the FSM's identity
- Information that should persist across many transitions

**Use Payload for:**
- Transaction-specific information
- Temporary context during a sequence of transitions
- Data that actions need to communicate across transitions
- Event processing metadata (timestamps, counters, flags)

## Guards and Actions

### Guard Expressions

Guards are boolean expressions that can access:
- `state.current_state`: Current state name
- `state.data`: State data (read-only in guards)
- `event.data`: Event-specific data
- `payload`: Current payload (read-only in guards)

```cure
// Simple guard
when data.balance > 100

// Complex guard with multiple conditions
when data.balance > 0 and event.amount <= data.daily_limit and payload.transaction_count < 10

// Guard with type checks
when is_integer(event.amount) and event.amount > 0
```

### Action Functions

Actions can:
- Read state data, event data, and payload
- Modify state data
- Modify payload
- Call built-in functions
- Return new state data and payload

```cure
action: |state, event| {
    // Access event data
    let amount = event.amount;
    let user_id = event.user_id;
    
    // Modify state data
    state.data.balance = state.data.balance - amount;
    state.data.transaction_count = state.data.transaction_count + 1;
    
    // Modify payload
    payload.last_amount = amount;
    payload.last_user = user_id;
    payload.timestamp = now();
    
    // Log action (built-in function)
    log_info("Withdrawal: #{amount} by #{user_id}");
    
    // Return updated data and payload
    {state.data, payload}
}
```

## Using FSMs from Cure Code

### Spawning an FSM

```cure
// Create FSM with initial data
let fsm = spawn_fsm(TrafficLight, #{timer_duration => 30});

// Spawn with initial state override (if supported)
let fsm2 = spawn_fsm_with_state(Counter, #{value => 0}, Zero);
```

### Sending Events

```cure
// Send event without data
fsm_send(fsm, timer);

// Send event with data
fsm_send(fsm, increment, #{amount => 5});

// Send batch events for performance
let events = [start, {process, #{id => 1}}, {process, #{id => 2}}, stop];
fsm_send_batch(fsm, events);
```

### Querying FSM State

```cure
// Get current state
let current_state = fsm_state(fsm);

// Get full FSM info
let info = fsm_info(fsm);
// info contains: fsm_type, current_state, data, event_history

// Check if FSM is alive
if fsm_is_alive(fsm) {
    // FSM is running
}
```

### FSM Lifecycle

```cure
// Stop an FSM
fsm_stop(fsm);

// Monitor FSM for termination
let monitor_ref = fsm_monitor(fsm);

// Link to FSM (bidirectional crash propagation)
fsm_link(fsm);
```

### Timeouts

```cure
// Set a timeout
fsm_set_timeout(fsm, 5000, timeout_expired);

// Clear a timeout
fsm_clear_timeout(fsm);
```

## Using FSMs from Erlang Shell

When testing or debugging, you can interact with Cure FSMs directly from the Erlang shell.

### Starting the Shell

```bash
cd /opt/Proyectos/Ammotion/cure
make shell
```

### Registering an FSM Type

```erlang
% Define a simple FSM
cure_fsm_runtime:register_fsm_type(
    simple_counter,
    ['Zero', 'Positive'],
    'Zero',
    [
        {'Zero', increment, 'Positive', undefined, fun(State, _Event) ->
            Data = State#fsm_state.data,
            Payload = State#fsm_state.payload,
            NewData = maps:put(count, maps:get(count, Data, 0) + 1, Data),
            NewPayload = maps:put(last_op, increment, Payload),
            {NewData, NewPayload}
        end},
        {'Positive', decrement, 'Zero', undefined, fun(State, _Event) ->
            Data = State#fsm_state.data,
            Payload = State#fsm_state.payload,
            NewData = maps:put(count, 0, Data),
            NewPayload = maps:put(last_op, decrement, Payload),
            {NewData, NewPayload}
        end}
    ]
).
```

### Working with FSM Instances

```erlang
% Start an FSM
{ok, FSM} = cure_fsm_runtime:start_fsm(simple_counter, #{count => 0}).

% Check current state
{ok, State} = cure_fsm_runtime:get_state(FSM).
% State => 'Zero'

% Send events
cure_fsm_runtime:send_event(FSM, increment).
timer:sleep(10).  % Allow async processing

{ok, State2} = cure_fsm_runtime:get_state(FSM).
% State2 => 'Positive'

% Get full FSM info (includes payload)
{ok, Info} = cure_fsm_runtime:get_fsm_info(FSM).
% Info => #{
%   fsm_type => simple_counter,
%   current_state => 'Positive',
%   data => #{count => 1},
%   event_history => [...]
% }

% Stop the FSM
cure_fsm_runtime:stop_fsm(FSM).
```

### Advanced Shell Usage

```erlang
% Register FSM with compiled definition
CompiledFSM = #fsm_definition{
    name = traffic_light,
    states = ['Green', 'Yellow', 'Red'],
    initial_state = 'Green',
    transitions = #{
        {'Green', timer} => {'Yellow', undefined, undefined},
        {'Yellow', timer} => {'Red', undefined, undefined},
        {'Red', timer} => {'Green', undefined, undefined}
    },
    timeouts = #{}
},
cure_fsm_runtime:register_fsm_type(traffic_light, CompiledFSM).

% Spawn with options
{ok, FSM2} = cure_fsm_runtime:start_fsm(traffic_light, #{}, []).

% Send batch events
Events = [timer, timer, timer],
cure_fsm_runtime:send_batch_events(FSM2, Events).

% Get performance stats
{ok, Stats} = cure_fsm_runtime:get_performance_stats(FSM2).
% Stats => #fsm_perf_stats{
%   events_processed => 3,
%   avg_event_time => 2.5,
%   max_event_time => 5.0,
%   ...
% }

% List all registered FSM types
Types = cure_fsm_runtime:get_registered_fsm_types().
```

### Using Payload from Shell

```erlang
% Define action that modifies payload
ActionFun = fun(State, Event) ->
    Data = State#fsm_state.data,
    Payload = State#fsm_state.payload,
    
    % Initialize payload if undefined
    CurrentPayload = case Payload of
        undefined -> #{};
        P -> P
    end,
    
    % Update payload with event count
    Count = maps:get(event_count, CurrentPayload, 0),
    NewPayload = maps:put(event_count, Count + 1, CurrentPayload),
    NewPayload2 = maps:put(last_event_time, erlang:system_time(microsecond), NewPayload),
    
    % Return both data and payload
    {Data, NewPayload2}
end.

% Register FSM with payload-modifying action
cure_fsm_runtime:register_fsm_type(
    payload_fsm,
    ['StateA', 'StateB'],
    'StateA',
    [
        {'StateA', ping, 'StateB', undefined, ActionFun},
        {'StateB', pong, 'StateA', undefined, ActionFun}
    ]
).

% Test payload modification
{ok, FSM} = cure_fsm_runtime:start_fsm(payload_fsm, #{}).
cure_fsm_runtime:send_event(FSM, ping).
timer:sleep(10).
{ok, Info} = cure_fsm_runtime:get_fsm_info(FSM).
% Check that payload is being tracked (you'll need to add payload to get_fsm_info return)
```

## Advanced Features

### State Timeouts

Define automatic transitions after a timeout:

```cure
fsm AutoShutdown {
    states: [Running, ShuttingDown, Off]
    initial: Running
    
    state Running {
        on stop -> ShuttingDown
        timeout 60000 -> ShuttingDown  % Auto-shutdown after 60 seconds
    }
    
    state ShuttingDown {
        on cleanup_complete -> Off
        timeout 10000 -> Off  % Force shutdown after 10 seconds
    }
    
    state Off {
        % Terminal state
    }
}
```

### Nested FSMs

FSMs can spawn and manage other FSMs:

```cure
action: |state, event| {
    // Spawn a child FSM
    let child_fsm = spawn_fsm(Worker, #{task => event.task});
    
    // Store child reference in state data
    state.data.children = [child_fsm | state.data.children];
    
    // Track in payload for immediate use
    payload.last_spawned = child_fsm;
    
    {state.data, payload}
}
```

### FSM Communication

FSMs can send messages to each other:

```cure
// Send message to another FSM
fsm_send_message(target_fsm, #{type => request, data => payload});

// Receive messages (if FSM has receive capability)
match fsm_receive(timeout: 5000) {
    #{type: request, data: Data} -> handle_request(Data),
    #{type: response} -> handle_response(),
    timeout -> handle_timeout()
}
```

### Performance Monitoring

```cure
// Get performance statistics
let stats = fsm_get_performance_stats(fsm);
// stats contains:
// - events_processed: Total events
// - avg_event_time: Average processing time
// - max_event_time: Maximum processing time
// - memory_usage: Current memory
// - last_updated: Last update timestamp
```

## Examples

### Example 1: Simple Counter with Payload Tracking

```erlang
% From Erlang shell
cure_fsm_runtime:register_fsm_type(
    counter_with_history,
    ['Zero', 'Positive', 'Negative'],
    'Zero',
    [
        {'Zero', increment, 'Positive', undefined, fun(S, _E) ->
            D = S#fsm_state.data,
            P = maps:put(operations, [increment | maps:get(operations, S#fsm_state.payload, [])], S#fsm_state.payload),
            {maps:put(value, 1, D), P}
        end},
        {'Zero', decrement, 'Negative', undefined, fun(S, _E) ->
            D = S#fsm_state.data,
            P = maps:put(operations, [decrement | maps:get(operations, S#fsm_state.payload, [])], S#fsm_state.payload),
            {maps:put(value, -1, D), P}
        end},
        {'Positive', increment, 'Positive', undefined, fun(S, _E) ->
            D = S#fsm_state.data,
            P = maps:put(operations, [increment | maps:get(operations, S#fsm_state.payload, [])], S#fsm_state.payload),
            {maps:put(value, maps:get(value, D) + 1, D), P}
        end},
        {'Positive', reset, 'Zero', undefined, fun(S, _E) ->
            D = maps:put(value, 0, S#fsm_state.data),
            P = maps:put(operations, [], #{reset_count => maps:get(reset_count, S#fsm_state.payload, 0) + 1}),
            {D, P}
        end},
        {'Negative', increment, 'Zero', undefined, fun(S, _E) ->
            D = maps:put(value, 0, S#fsm_state.data),
            P = maps:put(operations, [], S#fsm_state.payload),
            {D, P}
        end}
    ]
).

{ok, C} = cure_fsm_runtime:start_fsm(counter_with_history, #{value => 0}).
cure_fsm_runtime:send_event(C, increment).
cure_fsm_runtime:send_event(C, increment).
cure_fsm_runtime:send_event(C, increment).
timer:sleep(50).
{ok, State} = cure_fsm_runtime:get_state(C).
% State => 'Positive'
```

### Example 2: Traffic Light with Timing

```erlang
cure_fsm_runtime:register_fsm_type(
    timed_traffic_light,
    ['Green', 'Yellow', 'Red'],
    'Green',
    [
        {'Green', timer, 'Yellow', undefined, fun(S, _E) ->
            P = maps:put(green_time, erlang:system_time(millisecond), S#fsm_state.payload),
            {S#fsm_state.data, P}
        end},
        {'Yellow', timer, 'Red', undefined, fun(S, _E) ->
            P = maps:put(yellow_time, erlang:system_time(millisecond), S#fsm_state.payload),
            {S#fsm_state.data, P}
        end},
        {'Red', timer, 'Green', undefined, fun(S, _E) ->
            P = maps:put(red_time, erlang:system_time(millisecond), S#fsm_state.payload),
            P2 = maps:put(cycle_count, maps:get(cycle_count, P, 0) + 1, P),
            {S#fsm_state.data, P2}
        end}
    ]
).

{ok, TL} = cure_fsm_runtime:start_fsm(timed_traffic_light, #{}).
cure_fsm_runtime:send_event(TL, timer).
timer:sleep(10).
{ok, 'Yellow'} = cure_fsm_runtime:get_state(TL).
```

### Example 3: State Machine with Guards

```erlang
GuardFun = fun(State, EventData) ->
    Count = maps:get(count, State#fsm_state.data, 0),
    Count < 5
end.

cure_fsm_runtime:register_fsm_type(
    limited_counter,
    ['Idle', 'Counting', 'Full'],
    'Idle',
    [
        {'Idle', start, 'Counting', undefined, fun(S, _) ->
            {maps:put(count, 0, S#fsm_state.data), S#fsm_state.payload}
        end},
        {'Counting', increment, 'Counting', GuardFun, fun(S, _) ->
            D = S#fsm_state.data,
            {maps:put(count, maps:get(count, D) + 1, D), S#fsm_state.payload}
        end},
        {'Counting', increment, 'Full', fun(State, _) -> 
            maps:get(count, State#fsm_state.data, 0) >= 5
        end, fun(S, _) ->
            {maps:put(count, 5, S#fsm_state.data), S#fsm_state.payload}
        end},
        {'Full', reset, 'Idle', undefined, fun(S, _) ->
            {maps:put(count, 0, S#fsm_state.data), S#fsm_state.payload}
        end}
    ]
).
```

## Best Practices

1. **Keep States Simple**: Each state should represent a clear, distinct mode of operation
2. **Use Guards Wisely**: Guards should be fast, pure functions without side effects
3. **Manage Payload Lifecycle**: Clear payload data when transitioning to states that don't need it
4. **Separate Concerns**: Use state data for identity, payload for transaction context
5. **Test Transitions**: Test all state transitions, especially edge cases with guards
6. **Monitor Performance**: Use performance stats to identify bottlenecks
7. **Use Batch Events**: For high-throughput scenarios, batch events for better performance
8. **Handle Timeouts**: Always have timeout transitions for long-running states
9. **Document States**: Clearly document what each state means and when transitions occur
10. **Leverage Types**: Use Cure's type system to catch FSM errors at compile time

## Troubleshooting

### FSM Not Transitioning

- Check that the event name matches exactly
- Verify guard conditions are being met
- Check event history with `fsm_info/1`
- Ensure the FSM process is alive with `fsm_is_alive/1`

### Payload Not Updating

- Verify action function returns `{data, payload}` tuple
- Check that payload is being initialized properly
- Make sure you're calling the right update operations

### Performance Issues

- Use `get_performance_stats/1` to identify slow transitions
- Consider batch event processing for high throughput
- Profile guard and action functions
- Check event history size (automatically trimmed at 100 events)

### Memory Leaks

- Event history is automatically trimmed (last 50 of 100)
- Clear large payload data when not needed
- Monitor FSM memory usage

## Reference

### FSM Runtime Functions

- `register_fsm_type/2`: Register FSM type definition
- `start_fsm/2`, `start_fsm/3`: Create FSM instance
- `stop_fsm/1`: Stop FSM instance
- `send_event/2`, `send_event/3`: Send event to FSM
- `send_batch_events/2`: Send multiple events
- `get_state/1`: Get current state
- `get_fsm_info/1`: Get complete FSM information
- `get_performance_stats/1`: Get performance metrics
- `set_timeout/3`: Set state timeout
- `clear_timeout/1`: Clear timeout
- `lookup_fsm_definition/1`: Look up FSM type
- `get_registered_fsm_types/0`: List all registered types

### Payload Operations (in Actions)

- `payload`: Read current payload
- `payload.field`: Get payload field
- `payload = value`: Set entire payload
- `payload.field = value`: Update payload field

### Built-in Action Functions

- `log_debug/1`, `log_info/1`, `log_warning/1`, `log_error/1`: Logging
- `now/0`: Get current timestamp
- `maps:get/2`, `maps:put/3`: Map operations
- `length/1`, `size/1`: Collection operations
- Standard arithmetic and boolean operators

---

For more information, see the main Cure documentation and the FSM runtime source code in `src/fsm/cure_fsm_runtime.erl`.
