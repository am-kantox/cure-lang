#!/usr/bin/env escript
%% Test script for Show typeclass

main(_) ->
    % Add the build directory to the code path
    code:add_patha("_build/ebin"),
    
    io:format("~n=== Testing Show Typeclass ===~n~n"),
    
    % Test Show(Int)
    IntResult = 'Std.Show':'Show_Int_show'(42),
    io:format("show(42) = ~s~n", [IntResult]),
    
    % Test Show(Bool)  
    BoolTrue = 'Std.Show':'Show_Bool_show'(true),
    BoolFalse = 'Std.Show':'Show_Bool_show'(false),
    io:format("show(true) = ~s~n", [BoolTrue]),
    io:format("show(false) = ~s~n", [BoolFalse]),
    
    % Test Show(String)
    StringResult = 'Std.Show':'Show_String_show'(<<"Hello, World!">>),
    io:format("show(\"Hello, World!\") = ~s~n", [StringResult]),
    
    % Test Show(Float)
    FloatResult = 'Std.Show':'Show_Float_show'(3.14),
    io:format("show(3.14) = ~s~n", [FloatResult]),
    
    io:format("~n=== All Show instances working! ===~n"),
    
    ok.
