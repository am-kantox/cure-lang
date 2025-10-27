-module(debug_turnstile_ast).
-export([test/0]).

test() ->
    io:format("=== Debugging turnstile AST ===~n"),
    case cure_parser:parse_file("examples/turnstile.cure") of
        {ok, AST} ->
            io:format("Parsed successfully~n~n"),
            % Find the module
            [ModuleDef | _] = AST,
            {module_def, ModuleName, _Imports, _Exports, Items, _Loc} = ModuleDef,
            io:format("Module: ~p~n", [ModuleName]),

            % Find the coin function
            CoinFunc = lists:keyfind(coin, 2, [I || I <- Items, element(1, I) =:= function_def]),
            case CoinFunc of
                false ->
                    io:format("coin function not found!~n");
                {function_def, Name, Params, RetType, _Constraint, Body, _IsPrivate, _Loc2} ->
                    io:format("~nFunction: ~p~n", [Name]),
                    io:format("Params: ~p~n", [Params]),
                    io:format("Return type: ~p~n", [RetType]),
                    io:format("~nBody structure:~n"),
                    print_expr(Body, 0)
            end;
        {error, Reason} ->
            io:format("Parse error: ~p~n", [Reason])
    end.

print_expr(Expr, Indent) ->
    Prefix = lists:duplicate(Indent, " "),
    case Expr of
        {let_expr, Bindings, LetBody, _Loc} ->
            io:format("~slet_expr with ~p bindings~n", [Prefix, length(Bindings)]),
            lists:foreach(fun(B) -> print_binding(B, Indent + 2) end, Bindings),
            io:format("~s  body:~n", [Prefix]),
            print_expr(LetBody, Indent + 4);
        {record_expr, RecName, Fields, _Loc} ->
            io:format("~srecord_expr: ~p with ~p fields~n", [Prefix, RecName, length(Fields)]),
            lists:foreach(fun(F) -> print_field(F, Indent + 2) end, Fields);
        {match_expr, MatchE, Patterns, _Loc} ->
            io:format("~smatch_expr~n", [Prefix]),
            io:format("~s  matching on:~n", [Prefix]),
            print_expr(MatchE, Indent + 4),
            io:format("~s  patterns: ~p~n", [Prefix, length(Patterns)]);
        {identifier_expr, Name, _Loc} ->
            io:format("~sidentifier: ~p~n", [Prefix, Name]);
        {field_access_expr, Record, Field, _Loc} ->
            io:format("~sfield_access: .~p on:~n", [Prefix, Field]),
            print_expr(Record, Indent + 2);
        {binary_op_expr, Op, _Left, _Right, _Loc} ->
            io:format("~sbinary_op: ~p~n", [Prefix, Op]);
        Other ->
            io:format("~s~p~n", [Prefix, element(1, Other)])
    end.

print_binding({binding, Pattern, Value, _Loc}, Indent) ->
    Prefix = lists:duplicate(Indent, " "),
    io:format("~sbinding: ", [Prefix]),
    print_pattern(Pattern),
    io:format(" =~n"),
    print_expr(Value, Indent + 2).

print_pattern({identifier_pattern, Name, _Loc}) ->
    io:format("~p", [Name]);
print_pattern(Other) ->
    io:format("~p", [element(1, Other)]).

print_field({field_expr, Name, Value, _Loc}, Indent) ->
    Prefix = lists:duplicate(Indent, " "),
    io:format("~sfield ~p:~n", [Prefix, Name]),
    print_expr(Value, Indent + 2).
