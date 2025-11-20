-module(cure_mcp_user).
-export([start/0]).

%% Minimal user interface for MCP server
%% This prevents Erlang from creating the default terminal-based user_drv
%% and allows clean stdio communication

start() ->
    % Do nothing - we handle I/O directly in cure_mcp_server
    ok.
