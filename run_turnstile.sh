#!/bin/bash
# Run the turnstile FSM example
set -e

echo "=== Compiling turnstile.cure ==="
./cure examples/turnstile.cure

echo ""
echo "=== Running turnstile example ==="
erl -pa _build/ebin -pa _build/lib -noshell -eval "
code:load_file('Turnstile'),
'Turnstile':register_fsms(),
timer:sleep(50),
Result = 'Turnstile':main(),
io:format(\"~n=== Execution completed with code: ~p ===~n\", [Result]),
timer:sleep(200),
init:stop()." 2>&1

echo ""
echo "=== Done ===" 