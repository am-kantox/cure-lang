# Enhanced Traffic Light FSM - Quick Reference

## File Locations

```
examples/06_fsm_traffic_light_enhanced.cure  - Cure source code
test/traffic_light_enhanced_test.erl          - Erlang test implementation
examples/README_TRAFFIC_LIGHT_ENHANCED.md     - Complete documentation
docs/TRAFFIC_LIGHT_ENHANCED_SUMMARY.md        - Implementation summary
```

## Quick Start

```bash
# Build and run
make clean && make all
erlc -o _build/ebin -I src test/traffic_light_enhanced_test.erl
erl -pa _build/ebin -noshell -s traffic_light_enhanced_test run -s init stop
```

## FSM States

```
Red ---------> Green ---------> Yellow ---------> Red
 |              |                 |                 |
 |              |                 |                 |
 +---> Maintenance <--------------+                 |
 |              |                                   |
 +---> FlashingRed <-------------------------------+
```

## Events

| Event | Symbol | Purpose |
|-------|--------|---------|
| Timer | ⏱️ | Normal cycle progression |
| Emergency | 🚨 | Immediate safety stop |
| Pedestrian | 🚶 | Priority crossing |
| Maintenance | 🔧 | Service mode |
| Resume | ▶️ | Exit service |
| Error | ⚠️ | System failure |
| Reset | 🔄 | Recover from error |

## API Cheat Sheet

```erlang
%% Start FSM
{ok, Pid} = cure_fsm_runtime:start_fsm(FSMType, InitialData),

%% Register FSM
ok = cure_fsm_cure_api:fsm_advertise(Pid, Name),

%% Send event
ok = cure_fsm_cure_api:fsm_cast(Name, Event, Data),

%% Batch events
ok = cure_fsm_cure_api:fsm_send_batch(Name, [Event1, Event2, ...]),

%% Query state
{ok, {StateName, Payload}} = cure_fsm_cure_api:fsm_state(Name),

%% Get info
{ok, Info} = cure_fsm_cure_api:fsm_info(Name),

%% Get history
{ok, History} = cure_fsm_cure_api:fsm_history(Name),

%% Lookup
Pid = cure_fsm_cure_api:fsm_whereis(Name).
```

## Statistics Tracked

```erlang
#{
    cycles_completed => Int,      % Complete cycles
    timer_events => Int,          % Timer transitions
    emergency_stops => Int,       % Emergency activations
    total_transitions => Int,     % All transitions
    red_duration => Int,         % Red time (seconds)
    green_duration => Int,       % Green time (seconds)
    yellow_duration => Int,      % Yellow time (seconds)
    pedestrian_crossings => Int, % Pedestrian events
    errors_detected => Int       % System errors
}
```

## Test Phases

1. ✅ **Lifecycle** - spawn, register, lookup
2. ✅ **Normal Cycle** - Red→Green→Yellow→Red
3. ✅ **Batch Processing** - 6 events at once
4. ✅ **Emergency** - immediate Red transition
5. ✅ **Pedestrian** - priority Green
6. ✅ **Maintenance** - service mode
7. ✅ **Error Recovery** - FlashingRed→Red
8. ✅ **Monitoring** - info, history, stats

## Performance

- **Latency**: ~155μs per event
- **Throughput**: ~6,500 events/sec
- **Batch speedup**: 2.3x
- **Memory**: Bounded to ≤100 events

## Example Transitions

```cure
# Normal cycle
Red --> |timer| Green {
    timer_events = timer_events + 1
    total_transitions = total_transitions + 1
    red_duration = red_duration + 30
}

# Emergency stop
Green --> |emergency| Red {
    emergency_stops = emergency_stops + 1
    total_transitions = total_transitions + 1
}

# Error handling
Yellow --> |error| FlashingRed {
    errors_detected = errors_detected + 1
    total_transitions = total_transitions + 1
}
```

## Erlang Action Pattern

```erlang
Action = fun(State, _EventData) ->
    Data = State#fsm_state.data,
    NewData = Data#{
        counter => maps:get(counter, Data) + 1
    },
    {NewData, State#fsm_state.payload}
end
```

## Common Patterns

### Initialize FSM
```erlang
InitData = #{field1 => Value1, field2 => Value2},
{ok, Pid} = cure_fsm_runtime:start_fsm(my_fsm, InitData).
```

### Register and Use
```erlang
ok = cure_fsm_cure_api:fsm_advertise(Pid, my_fsm),
ok = cure_fsm_cure_api:fsm_cast(my_fsm, event_name, []).
```

### Batch Events
```erlang
Events = [event1, event2, event3],
ok = cure_fsm_cure_api:fsm_send_batch(my_fsm, Events).
```

### Query State
```erlang
{ok, {CurrentState, Payload}} = cure_fsm_cure_api:fsm_state(my_fsm),
io:format("State: ~p, Payload: ~p~n", [CurrentState, Payload]).
```

## Troubleshooting

### FSM not found
```erlang
%% Check if registered
Pid = cure_fsm_cure_api:fsm_whereis(Name),
case Pid of
    undefined -> io:format("Not registered~n");
    _ -> io:format("Found: ~p~n", [Pid])
end.
```

### Event not processing
```erlang
%% Check current state
{ok, {State, _}} = cure_fsm_cure_api:fsm_state(Name),
io:format("Current state: ~p~n", [State]).

%% Check event history
{ok, History} = cure_fsm_cure_api:fsm_history(Name),
io:format("Recent events: ~p~n", [lists:sublist(History, 5)]).
```

### Performance issues
```erlang
%% Use batch processing for multiple events
Events = lists:duplicate(100, timer),
cure_fsm_cure_api:fsm_send_batch(Name, Events).
```

## Testing Template

```erlang
%% Define FSM
FSMDef = #fsm_definition{
    name = my_fsm,
    states = ['State1', 'State2'],
    initial_state = 'State1',
    transitions = #{
        {'State1', event} => {'State2', undefined, Action}
    },
    timeouts = #{}
},

%% Register type
ok = cure_fsm_runtime:register_fsm_type(my_fsm, FSMDef),

%% Start instance
{ok, Pid} = cure_fsm_runtime:start_fsm(my_fsm, #{}),

%% Test transition
cure_fsm_runtime:send_event(Pid, event),
timer:sleep(10),
{ok, 'State2'} = cure_fsm_runtime:get_state(Pid).
```

## Resources

- **Full README**: `examples/README_TRAFFIC_LIGHT_ENHANCED.md`
- **Summary**: `docs/TRAFFIC_LIGHT_ENHANCED_SUMMARY.md`
- **Test Code**: `test/traffic_light_enhanced_test.erl`
- **Runtime Docs**: `src/fsm/cure_fsm_runtime.erl` (moduledoc)
- **API Docs**: `src/fsm/cure_fsm_cure_api.erl` (moduledoc)

---

**Quick Reference** | Cure FSM System | v1.0
