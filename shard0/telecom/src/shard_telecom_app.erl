-module(shard_telecom_app).
-behaviour(application).

-export([start/2, stop/1]).

start(_Type, _Args) ->
    shard_telecom_sup:start_link().

stop(_State) ->
    ok.
