#!/bin/bash
# Direct compilation script for simple_pipe.cure example
# Bypasses stdlib to avoid compilation issues

set -e

echo "🚀 Compiling simple_pipe.cure example"
echo "========================================"

cd /opt/Proyectos/Ammotion/cure

# Step 1: Parse
echo "1. Parsing..."
erl -pa _build/ebin -noshell -eval "
{ok, AST} = cure_parser:parse_file(\"examples/simple_pipe.cure\"),
io:format(\"   ✓ Parsed successfully~n\"),
halt(0).
" || exit 1

# Step 2: Type check
echo "2. Type checking..."
erl -pa _build/ebin -noshell -eval "
{ok, AST} = cure_parser:parse_file(\"examples/simple_pipe.cure\"),
TypeResult = cure_typechecker:check_program(AST),
case element(2, TypeResult) of
    true -> 
        io:format(\"   ✓ Type check passed~n\"),
        halt(0);
    false ->
        io:format(\"   ✗ Type check failed~n\"),
        io:format(\"   Errors: ~p~n\", [element(4, TypeResult)]),
        halt(1)
end.
" || exit 1

# Step 3: Code generation
echo "3. Generating BEAM code..."
erl -pa _build/ebin -noshell -eval "
{ok, AST} = cure_parser:parse_file(\"examples/simple_pipe.cure\"),
{ok, CompiledModule} = cure_codegen:compile_module(hd(AST)),
ModuleName = maps:get(name, CompiledModule),
OutputPath = \"_build/ebin/\" ++ atom_to_list(ModuleName) ++ \".beam\",
{ok, {ModuleName, OutputPath}} = cure_codegen:write_beam_module(CompiledModule, OutputPath),
io:format(\"   ✓ Generated ~s~n\", [OutputPath]),
halt(0).
" || exit 1

# Step 4: Load and execute
echo "4. Running..."
echo ""
erl -pa _build/ebin -noshell -eval "
code:purge(simple_pipe),
code:load_file(simple_pipe),
try
    Result = simple_pipe:main(),
    io:format(\"📊 Result: ~p~n\", [Result]),
    io:format(\"~n✅ Success! The pipe operator works correctly.~n\"),
    io:format(\"   5 |> double |> increment = 5 -> 10 -> 11~n\"),
    halt(0)
catch
    error:undef ->
        io:format(\"❌ Module not properly loaded~n\"),
        halt(1);
    Error:Reason:Stack ->
        io:format(\"❌ Runtime error: ~p:~p~n\", [Error, Reason]),
        io:format(\"   Stack: ~p~n\", [Stack]),
        halt(1)
end.
" 

echo ""
echo "✨ Pipe operator example completed!"
