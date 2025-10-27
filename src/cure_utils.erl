-module(cure_utils).

-export([debug/1, debug/2]).

-spec debug(Format) -> ok when Format :: io:format().
debug(Format) ->
    debug(Format, []).

-spec debug(Format, Data) -> ok when
    Format :: io:format(),
    Data :: [term()].
-ifdef(debug).

debug(Format, Data) when is_list(Format) ->
    io:format(Format, Data);
debug(Format, Data) ->
    io:format("~p ~p~n", [Format, Data]).

-else.

debug(_, _) ->
    ok.

-endif.
