#!/usr/bin/env escript
%% Test code action extraction

main([]) ->
    % Add paths
    code:add_patha("_build/default/lib/cure/ebin"),

    % Test message
    Message =
        <<"Type hole: _\nInferred type: List(Int)\n\n💡 Click 'Quick Fix' or press Ctrl+. to fill in the type automatically"/utf8>>,

    % Extract inferred type
    Result = cure_lsp_type_holes:extract_inferred_type(Message),

    io:format("Message: ~s~n", [Message]),
    io:format("Extracted type: ~p~n", [Result]),

    case Result of
        {ok, TypeStr} ->
            io:format("✓ Successfully extracted: ~s~n", [TypeStr]);
        _ ->
            io:format("✗ Failed to extract type~n")
    end.
