#!/usr/bin/env escript
%% Profile Cure compiler performance

-module(profile_compile).

main([Filename]) ->
    % Start profiling
    io:format("~n=== Starting Cure Compiler Profiling ===~n~n"),
    
    % Ensure compiler modules are loaded
    code:add_path("_build/ebin"),
    
    % Profile lexer
    io:format("Phase 1: Lexing...~n"),
    {LexTime, LexResult} = timer:tc(fun() ->
        {ok, Content} = file:read_file(Filename),
        cure_lexer:tokenize(Content)
    end),
    io:format("  Time: ~.3f ms~n", [LexTime / 1000]),
    
    Tokens = case LexResult of
        {ok, T} -> T;
        {error, E} -> 
            io:format("  ERROR: ~p~n", [E]),
            halt(1)
    end,
    
    % Profile parser
    io:format("~nPhase 2: Parsing...~n"),
    {ParseTime, ParseResult} = timer:tc(fun() ->
        cure_parser:parse(Tokens)
    end),
    io:format("  Time: ~.3f ms~n", [ParseTime / 1000]),
    
    AST = case ParseResult of
        {ok, A} -> A;
        {error, E2} -> 
            io:format("  ERROR: ~p~n", [E2]),
            halt(1)
    end,
    
    % Profile type checking
    io:format("~nPhase 3: Type Checking...~n"),
    {TypeTime, TypeResult} = timer:tc(fun() ->
        cure_typechecker:check_program(AST)
    end),
    io:format("  Time: ~.3f ms~n", [TypeTime / 1000]),
    
    TypedAST = case TypeResult of
        {typecheck_result, true, _, _, _} -> AST;  % Use original AST if success
        {typecheck_result, false, _, Errors, _} ->
            io:format("  ERROR: ~p~n", [Errors]),
            halt(1);
        {error, E3} -> 
            io:format("  ERROR: ~p~n", [E3]),
            halt(1)
    end,
    
    % Profile code generation
    io:format("~nPhase 4: Code Generation...~n"),
    {CodegenTime, CodegenResult} = timer:tc(fun() ->
        cure_codegen:compile_program(TypedAST)
    end),
    io:format("  Time: ~.3f ms~n", [CodegenTime / 1000]),
    
    case CodegenResult of
        {ok, _Modules} -> ok;
        {error, E4} -> 
            io:format("  ERROR: ~p~n", [E4]),
            halt(1)
    end,
    
    % Summary
    TotalTime = LexTime + ParseTime + TypeTime + CodegenTime,
    io:format("~n=== Summary ===~n"),
    io:format("Total Time: ~.3f ms~n", [TotalTime / 1000]),
    io:format("~nBreakdown:~n"),
    io:format("  Lexer:      ~6.3f ms (~.1f%)~n", [LexTime / 1000, (LexTime / TotalTime) * 100]),
    io:format("  Parser:     ~6.3f ms (~.1f%)~n", [ParseTime / 1000, (ParseTime / TotalTime) * 100]),
    io:format("  Type Check: ~6.3f ms (~.1f%)~n", [TypeTime / 1000, (TypeTime / TotalTime) * 100]),
    io:format("  Codegen:    ~6.3f ms (~.1f%)~n", [CodegenTime / 1000, (CodegenTime / TotalTime) * 100]),
    io:format("~n"),
    
    halt(0);
    
main(_) ->
    io:format("Usage: escript profile_compile.erl <file.cure>~n"),
    halt(1).
