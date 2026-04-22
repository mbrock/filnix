#!/usr/bin/env escript
%%! -sname libei_ping_client

-mode(compile).

main([CookieString, TargetNodeString, ServerString]) ->
    true = erlang:set_cookie(node(), list_to_atom(CookieString)),
    TargetNode = list_to_atom(TargetNodeString),
    Server = list_to_atom(ServerString),
    {Server, TargetNode} ! {ping, self()},
    receive
        {pong, CNodeName} ->
            io:format("libei-ping-demo: received pong from ~p~n", [CNodeName]),
            ok;
        Other ->
            io:format(standard_error, "libei-ping-demo: unexpected reply ~p~n", [Other]),
            halt(1)
    after 5000 ->
        io:format(standard_error, "libei-ping-demo: timed out waiting for pong from ~s~n", [TargetNodeString]),
        halt(1)
    end.
