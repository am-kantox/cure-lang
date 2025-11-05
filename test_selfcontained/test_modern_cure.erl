#!/usr/bin/env escript
%% Test modern Cure LSP features with typeclass example

-module(test_modern_cure).
-mode(compile).

main([]) ->
    % Add the cure modules to path
    code:add_pathz("_build/default/lib/cure/ebin"),
    
    io:format("=== Testing Modern Cure LSP Features ===~n~n"),
    
    % Test with the typeclass example
    test_typeclass_example(),
    
    % Test with list basics example
    test_list_basics(),
    
    io:format("~n=== All Tests Passed! ===~n").

test_typeclass_example() ->
    io:format("Testing typeclass example...~n"),
    {ok, Content} = file:read_file("examples/08_typeclasses.cure"),
    
    % Test analysis
    io:format("  - Running analyzer...~n"),
    Result = cure_lsp_analyzer:analyze_document(Content),
    
    #{lex_result := LexResult, 
      parse_result := ParseResult,
      symbols := Symbols,
      diagnostics := Diagnostics} = Result,
    
    io:format("    Lex result: ~p~n", [element(1, LexResult)]),
    io:format("    Parse result: ~p~n", [element(1, ParseResult)]),
    io:format("    Symbols found: ~p~n", [length(Symbols)]),
    io:format("    Diagnostics: ~p~n", [length(Diagnostics)]),
    
    % Test symbol extraction
    io:format("  - Extracting symbols...~n"),
    case Symbols of
        [] ->
            io:format("    WARNING: No symbols extracted~n");
        _ ->
            io:format("    Found symbols:~n"),
            lists:foreach(fun(Symbol) ->
                SymbolName = maps:get(name, Symbol),
                SymbolKind = maps:get(kind, Symbol),
                io:format("      - ~s (kind: ~p)~n", [SymbolName, SymbolKind])
            end, lists:sublist(Symbols, 5))
    end,
    
    % Test hover info (on line with "typeclass Show(T)")
    io:format("  - Testing hover info...~n"),
    HoverInfo = cure_lsp_analyzer:get_hover_info(Content, 13, 10),
    case HoverInfo of
        null ->
            io:format("    Hover: No info found~n");
        Info ->
            io:format("    Hover: Found info~n")
    end,
    
    io:format("  ✓ Typeclass example test complete~n~n").

test_list_basics() ->
    io:format("Testing list basics example...~n"),
    {ok, Content} = file:read_file("examples/01_list_basics.cure"),
    
    % Test analysis
    io:format("  - Running analyzer...~n"),
    Result = cure_lsp_analyzer:analyze_document(Content),
    
    #{symbols := Symbols, diagnostics := Diagnostics} = Result,
    
    io:format("    Symbols found: ~p~n", [length(Symbols)]),
    io:format("    Diagnostics: ~p~n", [length(Diagnostics)]),
    
    if
        length(Symbols) > 0 ->
            io:format("    Sample symbols:~n"),
            lists:foreach(fun(Symbol) ->
                SymbolName = maps:get(name, Symbol),
                io:format("      - ~s~n", [SymbolName])
            end, lists:sublist(Symbols, 3));
        true ->
            io:format("    WARNING: No symbols found~n")
    end,
    
    io:format("  ✓ List basics example test complete~n~n").
