#!/usr/bin/env escript
%% Test script to check LSP type hole inference

main([]) ->
    main(["examples/type_holes_demo.cure"]);
main([FilePath]) ->
    io:format("Testing LSP type hole inference for: ~s~n", [FilePath]),

    % Compile the modules we need
    code:add_patha("_build/ebin"),
    code:add_patha("_build/default/lib/cure/ebin"),

    % Parse the file
    case cure_parser:parse_file(FilePath) of
        {ok, AST} ->
            io:format("~nParsed AST successfully~n"),

            % Find type holes
            Holes = cure_lsp_type_holes:find_type_holes(AST),
            io:format("~nFound ~p type holes:~n", [length(Holes)]),
            lists:foreach(
                fun({HoleName, Context, Loc}) ->
                    io:format("  - ~p at ~p~n", [HoleName, Loc]),

                    % Try to infer type
                    io:format("    Attempting type inference...~n"),
                    case cure_lsp_type_holes:infer_hole_type(Context, AST, #{}) of
                        {ok, Type} ->
                            TypeStr = cure_lsp_type_holes:format_inferred_type(Type),
                            io:format("    ✓ Inferred type: ~s~n", [TypeStr]);
                        {error, Reason} ->
                            io:format("    ✗ Failed: ~p~n", [Reason])
                    end
                end,
                Holes
            ),

            % Generate diagnostics
            io:format("~nGenerating diagnostics...~n"),
            Diagnostics = cure_lsp_type_holes:generate_hole_diagnostics(<<"/test">>, AST),
            io:format("Generated ~p diagnostics~n", [length(Diagnostics)]),

            ok;
        {error, Reason} ->
            io:format("Failed to parse file: ~p~n", [Reason]),
            halt(1)
    end.
