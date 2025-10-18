#!/bin/bash

# Simple script to compile and run Cure programs
# Usage: ./run_cure.sh filename.cure [main_function]
#
# The script will:
# 1. Compile the .cure file using the Cure compiler
# 2. Extract the module name from the compiled BEAM file
# 3. Run the specified function (defaults to 'main')

if [ $# -eq 0 ]; then
    echo "Usage: $0 <filename.cure> [main_function]"
    echo "  filename.cure: The Cure source file to compile and run"
    echo "  main_function: Function to call (defaults to 'main')"
    echo ""
    echo "Examples:"
    echo "  $0 examples/simple_demo.cure"
    echo "  $0 examples/simple_demo.cure main"
    echo "  $0 lib/examples/list_tuple_demo.cure test_lists"
    exit 1
fi

CURE_FILE="$1"
MAIN_FUNCTION="${2:-main}"  # Default to 'main' if no function specified

# Validate input file
if [ ! -f "$CURE_FILE" ]; then
    echo "❌ Error: File '$CURE_FILE' not found"
    exit 1
fi

# Check if cure compiler exists
if [ ! -x "./cure" ]; then
    echo "❌ Error: Cure compiler './cure' not found or not executable"
    echo "   Please run 'make compiler' first"
    exit 1
fi

echo "🚀 Compiling and running Cure program: $CURE_FILE"
echo "📋 Target function: $MAIN_FUNCTION"
echo "================================================"

# Step 1: Compile the .cure file
echo "⚙️  Compiling $CURE_FILE..."
if ! ./cure "$CURE_FILE" --verbose; then
    echo "❌ Compilation failed!"
    exit 1
fi

# Step 2: Find the generated BEAM file and extract module name
# The compiler generates BEAM files in _build/ebin/
# We need to determine the module name from the source file or compilation output
# Look for the most recently modified BEAM file
BEAM_FILE=$(find _build/ebin -name "*.beam" -newer "$CURE_FILE" 2>/dev/null | head -1)

# If no newer BEAM file found, try to extract module name from compilation output
if [ -z "$BEAM_FILE" ]; then
    # Try to find any BEAM file that might have been generated
    # The Cure compiler should have told us which BEAM file it generated
    # Let's look at the most recent BEAM files
    BEAM_FILE=$(ls -t _build/ebin/*.beam 2>/dev/null | head -1)
    
    if [ -z "$BEAM_FILE" ]; then
        echo "❌ No BEAM file found in _build/ebin/"
        echo "   This might indicate compilation didn't generate a BEAM file"
        exit 1
    fi
    
    echo "⚠️  Using most recent BEAM file (compilation might have reused existing file)"
fi

# Extract module name from BEAM file path
MODULE_NAME=$(basename "$BEAM_FILE" .beam)
echo "📦 Found compiled module: $MODULE_NAME"

# Better approach: Try to extract module name from the source file
# Parse the .cure file to find the module definition
SOURCE_MODULE_NAME=$(grep -E '^module\s+\w+\s+do' "$CURE_FILE" | sed -E 's/^module\s+(\w+)\s+do.*/\1/' | head -1)

if [ -n "$SOURCE_MODULE_NAME" ] && [ "$SOURCE_MODULE_NAME" != "$MODULE_NAME" ]; then
    echo "🔍 Detected module name from source: $SOURCE_MODULE_NAME"
    # Check if the source-based module BEAM file exists
    SOURCE_BEAM="_build/ebin/${SOURCE_MODULE_NAME}.beam"
    if [ -f "$SOURCE_BEAM" ]; then
        MODULE_NAME="$SOURCE_MODULE_NAME"
        echo "📦 Using source-detected module: $MODULE_NAME"
    fi
fi

# Step 3: Execute the function
echo "🎯 Executing ${MODULE_NAME}:${MAIN_FUNCTION}()..."
echo "--------------------"

# Run the function and capture both output and return value
# cd /opt/Proyectos/Ammotion/cure && erl -pa _build/ebin -pa _build/lib/std -pa _build -noshell -eval ""
erl -pa _build/ebin -pa _build/lib -pa _build/lib/std -pa _build -noshell -eval "
try
    Result = '$MODULE_NAME':'$MAIN_FUNCTION'(),
    io:format(\"~n📊 Function result: ~p~n\", [Result]),
    io:format(\"✅ Program completed successfully~n\"),
    halt(0)
catch
    error:Reason:Stack ->
        io:format(\"~n❌ Runtime error: ~p~n\", [Reason]),
        io:format(\"   Stack trace: ~p~n\", [Stack]),
        halt(1);
    exit:Reason ->
        io:format(\"~n❌ Exit error: ~p~n\", [Reason]),
        halt(1);
    throw:Reason ->
        io:format(\"~n❌ Throw error: ~p~n\", [Reason]),
        halt(1)
end" -s init stop
