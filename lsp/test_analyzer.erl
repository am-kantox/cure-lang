-module(test_analyzer).
-export([run/0]).

run() ->
    io:format("~n=== Testing Cure LSP Analyzer ===~n~n"),

    % Read test file
    {ok, TestCode} = file:read_file("lsp/test_example.cure"),

    % Test 1: Basic analysis
    io:format("Test 1: Basic analysis~n"),
    Diagnostics = cure_lsp_analyzer:analyze(TestCode),
    io:format("  Diagnostics: ~p~n", [Diagnostics]),

    % Test 2: Extract symbols
    io:format("~nTest 2: Extract symbols~n"),
    Symbols = cure_lsp_analyzer:extract_symbols(TestCode),
    io:format("  Symbols found: ~p~n", [length(Symbols)]),
    lists:foreach(
        fun(Sym) ->
            Name = maps:get(name, Sym),
            Kind = maps:get(kind, Sym),
            io:format("    - ~s (kind: ~p)~n", [Name, Kind])
        end,
        Symbols
    ),

    % Test 3: Full document analysis
    io:format("~nTest 3: Full document analysis~n"),
    Analysis = cure_lsp_analyzer:analyze_document(TestCode),
    io:format("  Lex result: ~p~n", [element(1, maps:get(lex_result, Analysis))]),
    io:format("  Parse result: ~p~n", [element(1, maps:get(parse_result, Analysis))]),
    io:format("  Symbols count: ~p~n", [length(maps:get(symbols, Analysis))]),

    % Test 4: Symbol table
    io:format("~nTest 4: Symbol table~n"),
    SymbolTable = cure_lsp_symbols:new(),
    case maps:get(parse_result, Analysis) of
        {ok, AST} ->
            UpdatedSymbols = cure_lsp_symbols:add_module(
                SymbolTable,
                <<"file:///test_example.cure">>,
                AST
            ),
            io:format("  Symbol table updated successfully~n"),

            % Test completions
            Completions = cure_lsp_symbols:get_completions(UpdatedSymbols, <<"gre">>),
            io:format("  Completions for 'gre': ~p~n", [length(Completions)]),
            lists:foreach(
                fun(Comp) ->
                    Label = maps:get(label, Comp),
                    io:format("    - ~s~n", [Label])
                end,
                Completions
            );
        _ ->
            io:format("  Failed to parse AST~n")
    end,

    % Test 5: Hover info (at function definition)
    io:format("~nTest 5: Hover info at line 4 (main function)~n"),
    HoverInfo = cure_lsp_analyzer:get_hover_info(TestCode, 3, 5),
    case HoverInfo of
        null ->
            io:format("  No hover info found~n");
        _ ->
            Contents = maps:get(contents, HoverInfo),
            Value = maps:get(value, Contents),
            io:format("  Hover info: ~s~n", [Value])
    end,

    % Test 6: Definition lookup
    io:format("~nTest 6: Definition lookup at line 4~n"),
    DefResult = cure_lsp_analyzer:get_definition(TestCode, 3, 5),
    case DefResult of
        null ->
            io:format("  No definition found~n");
        _ ->
            io:format("  Definition found: ~p~n", [DefResult])
    end,

    io:format("~n=== All tests completed ===~n"),
    ok.
