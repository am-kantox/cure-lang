-module(debug_gen).
-export([disassemble_beam/1]).

disassemble_beam(BeamFile) ->
    case beam_disasm:file(BeamFile) of
        {beam_file, Module, Exports, Attributes, CompileInfo, Code} ->
            io:format("Module: ~p~n", [Module]),
            io:format("Exports: ~p~n", [Exports]),
            io:format("Code:~n"),
            [io:format("  ~p~n", [Function]) || Function <- Code];
        Error ->
            io:format("Error: ~p~n", [Error])
    end.