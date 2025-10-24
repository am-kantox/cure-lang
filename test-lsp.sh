#!/bin/bash
# Test script for Cure LSP server

cd "$(dirname "$0")"

echo "Testing Cure LSP Server..."
echo "=========================="
echo

# Check if LSP is built
if [ ! -f "./cure-lsp" ]; then
    echo "Error: cure-lsp not found. Run 'make lsp' first."
    exit 1
fi

# Test 1: Version check
echo "Test 1: Version check"
./cure-lsp --version
echo

# Test 2: Symbol extraction
echo "Test 2: Symbol extraction from vector_test.cure"
erl -pa _build/ebin -pa _build/lsp -noshell -eval \
  "{ok, Text} = file:read_file(\"examples/vector_test.cure\"), \
   Symbols = cure_lsp_analyzer:extract_symbols(Text), \
   io:format(\"Found ~p symbols~n\", [length(Symbols)]), \
   lists:foreach(fun(S) -> io:format(\"  - ~s~n\", [maps:get(name, S)]) end, Symbols)." \
  -s init stop
echo

# Test 3: Diagnostics (should be empty for valid file)
echo "Test 3: Diagnostics for vector_test.cure"
erl -pa _build/ebin -pa _build/lsp -noshell -eval \
  "{ok, Text} = file:read_file(\"examples/vector_test.cure\"), \
   Diags = cure_lsp_analyzer:analyze(Text), \
   case Diags of \
     [] -> io:format(\"✓ No diagnostics (file is valid)~n\"); \
     _ -> io:format(\"✗ Found ~p diagnostics~n\", [length(Diags)]) \
   end." \
  -s init stop
echo

echo "=========================="
echo "LSP Tests Complete!"
echo
echo "To test in NeoVim:"
echo "1. Add the config from lsp/NEOVIM_SETUP.md to your init.lua"
echo "2. Run: nvim examples/vector_test.cure"
echo "3. Check: :LspInfo"
