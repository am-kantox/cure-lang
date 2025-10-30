#!/bin/bash
# Run the traffic light FSM example
set -e

echo "=== Compiling 06_fsm_traffic_light.cure ==="
./cure examples/06_fsm_traffic_light.cure

echo ""
echo "=== Running traffic light FSM example ==="
erl -pa _build/ebin -pa _build/lib -noshell -eval "
code:load_file('TrafficLightFSM'),
'TrafficLightFSM':register_fsms(),
timer:sleep(50),
Result = 'TrafficLightFSM':main(),
io:format(\"~n=== Execution completed with code: ~p ===~n\", [Result]),
timer:sleep(200),
init:stop()." 2>&1

echo ""
echo "=== Done ==="
