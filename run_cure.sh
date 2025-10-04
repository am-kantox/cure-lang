#!/bin/bash

# Simple script to compile and run Cure programs
# Usage: ./run_cure.sh filename.cure

if [ $# -eq 0 ]; then
    echo "Usage: $0 <filename.cure>"
    exit 1
fi

CURE_FILE="$1"

if [ ! -f "$CURE_FILE" ]; then
    echo "Error: File $CURE_FILE not found"
    exit 1
fi

echo "🚀 Compiling and running Cure program: $CURE_FILE"
echo "================================================"

# Run Erlang with proper evaluation structure
erl -pa _build/ebin -pa _build/ebin/lexer -pa _build/ebin/parser -pa _build/ebin/types -pa _build/ebin/codegen -pa _build/ebin/fsm -pa _build/ebin/runtime -noshell -eval "
begin
    {ok, Tokens} = cure_lexer:tokenize_file(\"$CURE_FILE\"),
    io:format(\"📝 Tokenization: SUCCESS (~p tokens)~n\", [length(Tokens)]),
    {ok, AST} = cure_parser:parse(Tokens),
    io:format(\"🔍 Parsing: SUCCESS~n\"),
    {ok, CompiledModules} = cure_codegen:compile_program(AST, []),
    io:format(\"⚙️  Compilation: SUCCESS (~p modules)~n\", [length(CompiledModules)]),
    io:format(\"🎯 Execution Output:~n--------------------~n\"),
    case cure_runtime:run_program(CompiledModules) of
        {ok, _Result, _State} ->
            io:format(\"~n✅ Program completed successfully~n\"),
            halt(0);
        {error, Error} ->
            io:format(\"~n❌ Runtime error: ~p~n\", [Error]),
            halt(1);
        Other ->
            io:format(\"~n❌ Unexpected result: ~p~n\", [Other]),
            halt(1)
    end
end"
