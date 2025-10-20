-module(cure_utils).

-export([debug/1, debug/2]).

-spec debug(Format) -> ok when Format :: io:format().
debug(Format) ->
  debug(Format, []).

-ifdef(debug).

-spec debug(Format, Data) -> ok
  when Format :: io:format(),
       Data :: [term()].
debug(Format, Data) when is_list(Format) ->
  io:format("DEBUG: " ++ Format, Data).

-else.

-spec debug(Format, Data) -> ok
  when Format :: io:format(),
       Data :: [term()].
debug(Format, _Data) when is_list(Format) ->
  ok.

-endif.
