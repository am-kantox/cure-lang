#!/bin/bash

# Test script to verify LSP updates diagnostics on document changes

echo "Testing LSP diagnostic updates..."
echo "=================================="
echo ""

# Start LSP server in background (simulated - you'll need to start it manually in your editor)
# For now, just verify the functions are callable

cd /home/am/Proyectos/Ammotion/cure

echo "Test 1: Verify cure_lsp_analyzer can handle code changes"
echo "----------------------------------------------------------"

# Test with broken code
erl -pa _build/ebin -pa _build/lsp -noshell -eval '
Code1 = <<"module Test do\n  def foo( x y) = 42\nend">>,
io:format("Analyzing broken code...~n"),
Diag1 = cure_lsp_analyzer:analyze(Code1),
io:format("Diagnostics: ~p~n~n", [length(Diag1)]),

Code2 = <<"module Test do\n  def foo(x, y) = 42\nend">>,
io:format("Analyzing fixed code...~n"),
Diag2 = cure_lsp_analyzer:analyze(Code2),
io:format("Diagnostics: ~p~n~n", [length(Diag2)]),

case {length(Diag1) > 0, length(Diag2) =:= 0} of
    {true, true} ->
        io:format("✓ Analyzer correctly detects and clears errors~n");
    {false, _} ->
        io:format("✗ Analyzer did not detect the syntax error~n");
    {_, false} ->
        io:format("✗ Analyzer still reports errors on valid code~n")
end,
halt().'

echo ""
echo "Test 2: Check that analyzer handles type errors"
echo "------------------------------------------------"

erl -pa _build/ebin -pa _build/lsp -noshell -eval '
Code3 = <<"module Test do\n  def foo(): Int = \"string\"\nend">>,
io:format("Analyzing type error code...~n"),
Diag3 = cure_lsp_analyzer:analyze(Code3),
io:format("Diagnostics count: ~p~n", [length(Diag3)]),
lists:foreach(fun(D) ->
    Msg = maps:get(<<"message">>, D, <<"no message">>),
    io:format("  - ~s~n", [Msg])
end, Diag3),

Code4 = <<"module Test do\n  def foo(): Int = 42\nend">>,
io:format("~nAnalyzing fixed type...~n"),
Diag4 = cure_lsp_analyzer:analyze(Code4),
io:format("Diagnostics count: ~p~n", [length(Diag4)]),

case {length(Diag3) > 0, length(Diag4) =:= 0} of
    {true, true} ->
        io:format("~n✓ Analyzer correctly handles type error transitions~n");
    {false, _} ->
        io:format("~n✗ Analyzer did not detect the type error~n");
    {_, false} ->
        io:format("~n✗ Analyzer still reports errors after type fix~n")
end,
halt().'

echo ""
echo "=================================="
echo "LSP diagnostic update tests complete"
echo ""
echo "To test in your editor:"
echo "1. Open a .cure file with an error"
echo "2. Watch stderr output: tail -f /tmp/cure-lsp.log"
echo "3. Fix the error and save"
echo "4. Verify diagnostics update in the editor"
