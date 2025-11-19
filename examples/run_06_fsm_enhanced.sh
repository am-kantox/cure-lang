#!/bin/bash
# Run the enhanced traffic light FSM example
set -e

echo "=== Compiling 06_fsm_traffic_light_enhanced.cure ==="
./cure examples/06_fsm_traffic_light_enhanced.cure

echo ""
echo "=== Running enhanced traffic light FSM example ==="
erl -pa _build/ebin -noshell -eval "
'TrafficLightEnhanced':register_fsms(),
'TrafficLightEnhanced':main().
" -s init stop 2>&1

echo ""
echo "=== Done ==="
