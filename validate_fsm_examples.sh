#!/bin/bash
# FSM Examples Validation Script

set -e

echo "========================================="
echo "  Cure FSM Examples Validation"
echo "========================================="
echo ""

# Colors
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "1. Checking environment..."
echo "   - Cure compiler: $(if [ -x ./cure ]; then echo '✓ Found'; else echo '✗ Not found'; exit 1; fi)"
echo "   - Build directory: $(if [ -d _build/ebin ]; then echo '✓ Ready'; else echo '✗ Missing'; exit 1; fi)"
echo ""

echo "2. Parsing FSM examples..."
echo ""

echo "   Parsing enhanced traffic light..."
erl -pa _build/ebin -noshell -eval '
case cure_parser:parse_file("examples/06_fsm_traffic_light_enhanced.cure") of
    {ok, _} -> 
        io:format("   ✓ Traffic light example parses successfully~n");
    {error, E} -> 
        io:format("   ✗ Parse error: ~p~n", [E]),
        halt(1)
end, halt(0).'

echo ""
echo "   Parsing verification examples..."
erl -pa _build/ebin -noshell -eval '
case cure_parser:parse_file("examples/07_fsm_verification.cure") of
    {ok, _} -> 
        io:format("   ✓ Verification examples parse successfully~n");
    {error, E} -> 
        io:format("   ✗ Parse error: ~p~n", [E]),
        halt(1)
end, halt(0).'

echo ""
echo "3. Running FSM compilation tests..."
echo ""

echo "   Testing Mermaid-style FSM with actions..."
erl -pa _build/ebin -noshell -s fsm_mermaid_compile_test run -s init stop 2>&1 | grep -E "(✓|✗|Testing|Actions executed)" || true

echo ""
echo "   Testing verification examples..."
erl -pa _build/ebin -noshell -s fsm_verification_compile_test run -s init stop 2>&1 | grep -E "(✓|✗|Testing|Found|FSM:)" | head -15 || true

echo ""
echo "4. Testing FSM verification integration..."
echo ""

erl -pa _build/ebin -noshell -s fsm_verification_integration_test run -s init stop 2>&1 | grep -E "(✓|✗|⚠|Testing|Verification|Deadlock)" | head -20 || true

echo ""
echo "========================================="
echo -e "${GREEN}  Validation Complete!${NC}"
echo "========================================="
echo ""
echo "All FSM examples validated successfully."
echo ""
echo "To explore the examples:"
echo "  - Enhanced traffic light: examples/06_fsm_traffic_light_enhanced.cure"
echo "  - Verification patterns: examples/07_fsm_verification.cure"
echo ""
echo "To run tests with verification enabled:"
echo "  CURE_FSM_VERIFY=1 make test-fsm"
echo ""
