#!/usr/bin/env escript

main(_) ->
    % Add paths
    code:add_pathz("_build/ebin"),
    code:add_pathz("_build/lsp"),
    code:add_pathz("_build/lib"),

    % Test code with a type hole
    Code =
        <<"\n"
        "module Test do\n"
        "  export [create_person/0]\n"
        "  \n"
        "  record Person do\n"
        "    name: String\n"
        "    age: Int\n"
        "  end\n"
        "  \n"
        "  def create_person(): _ =\n"
        "    Person{name: \"Alice\", age: 30}\n"
        "end\n">>,

    io:format("Testing type hole detection...~n"),

    % Parse
    case cure_lexer:tokenize(Code) of
        {ok, Tokens} ->
            io:format("Tokenization successful~n"),
            case cure_parser:parse(Tokens) of
                {ok, AST} ->
                    io:format("Parsing successful~n"),
                    io:format("AST: ~p~n~n", [AST]),

                    % Test type hole detection
                    io:format("Finding type holes...~n"),
                    Holes = cure_lsp_type_holes:find_type_holes(AST),
                    io:format("Found ~p holes~n", [length(Holes)]),
                    lists:foreach(
                        fun({Name, Context, Loc}) ->
                            io:format("  Hole: ~p, Context: ~p, Location: ~p~n", [
                                Name, Context, Loc
                            ])
                        end,
                        Holes
                    ),

                    % Test diagnostic generation
                    io:format("~nGenerating diagnostics...~n"),
                    Uri = <<"file:///test.cure">>,
                    Diagnostics = cure_lsp_type_holes:generate_hole_diagnostics(Uri, AST),
                    io:format("Generated ~p diagnostics~n", [length(Diagnostics)]),
                    lists:foreach(
                        fun(Diag) ->
                            io:format("  Diagnostic: ~p~n", [Diag])
                        end,
                        Diagnostics
                    );
                {error, ParseError} ->
                    io:format("Parse error: ~p~n", [ParseError])
            end;
        {error, LexError} ->
            io:format("Lex error: ~p~n", [LexError])
    end.
