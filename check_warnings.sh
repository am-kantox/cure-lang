#!/bin/bash

echo "=== Compiling all Erlang files and checking for warnings ==="

# Compile sources
echo "--- Source files ---"
find src -name "*.erl" -exec erlc +debug_info -I include -I src/parser -I src/fsm -I src/types -o _build/ebin {} \;

echo "--- Test files ---"
find test -name "*.erl" -exec erlc +debug_info -I include -I src/parser -I src/fsm -I src/types -o _build/ebin {} \;

echo "=== Compilation complete ==="