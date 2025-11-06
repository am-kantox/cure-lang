#!/usr/bin/env escript
%% Detailed profiling of Cure compiler using fprof

-mode(compile).

main([Filename]) ->
    io:format("~n=== Detailed Compiler Profiling ===~n~n"),
    
    % Ensure compiler modules are loaded
    code:add_path("_build/ebin"),
    
    % Read file content
    {ok, Content} = file:read_file(Filename),
    
    % Profile lexing
    io:format("Profiling Lexer...~n"),
    {LexTime, {ok, Tokens}} = timer:tc(fun() ->
        cure_lexer:tokenize(Content)
    end),
    io:format("  Lexer time: ~.3f ms~n~n", [LexTime / 1000]),
    
    % Profile parsing
    io:format("Profiling Parser...~n"),
    {ParseTime, {ok, AST}} = timer:tc(fun() ->
        cure_parser:parse(Tokens)
    end),
    io:format("  Parser time: ~.3f ms~n~n", [ParseTime / 1000]),
    
    % Profile type checking with detailed fprof
    io:format("Profiling Type Checker (detailed with fprof)...~n"),
    fprof:trace(start),
    {TypeTime, TypeResult} = timer:tc(fun() ->
        cure_typechecker:check_program(AST)
    end),
    fprof:trace(stop),
    
    io:format("  Type Checker time: ~.3f ms~n", [TypeTime / 1000]),
    
    % Analyze profiling data
    fprof:profile(),
    fprof:analyse([{dest, "typechecker_profile.txt"}, {totals, true}, {sort, acc}]),
    
    io:format("~nDetailed profile saved to typechecker_profile.txt~n"),
    io:format("~nTop functions by accumulated time (run: grep -E '^[^ ]' typechecker_profile.txt | head -20)~n~n"),
    
    % Show top functions
    os:cmd("grep -E '^[^ ]|CNT.*ACC' typechecker_profile.txt | head -30"),
    
    % Continue with codegen
    {TypedAST, Success} = case TypeResult of
        {typecheck_result, true, _, _, _} -> {AST, true};
        {typecheck_result, false, _, Errors, _} ->
            io:format("  Type errors: ~p~n", [Errors]),
            {AST, false};
        _ -> {AST, false}
    end,
    
    case Success of
        true ->
            io:format("~nProfiling Code Generator...~n"),
            {CodegenTime, _} = timer:tc(fun() ->
                cure_codegen:compile_program(TypedAST)
            end),
            io:format("  Codegen time: ~.3f ms~n~n", [CodegenTime / 1000]),
            
            TotalTime = LexTime + ParseTime + TypeTime + CodegenTime,
            io:format("=== Summary ===~n"),
            io:format("Total: ~.3f ms~n", [TotalTime / 1000]),
            halt(0);
        false ->
            io:format("~nType checking failed, skipping codegen~n"),
            halt(1)
    end;
    
main(_) ->
    io:format("Usage: escript profile_detailed.erl <file.cure>~n"),
    halt(1).
