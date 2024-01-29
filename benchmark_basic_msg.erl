-module(benchmark_basic_msg).
-export([start/0]).

-define(REPEAT, 10000000).

start() ->
    basic_test(?REPEAT),
    ok.

basic_test(N) ->
    % Get the start time
    StartTime = erlang:monotonic_time(),

    % Start the receiver process
    ReceiverPid = spawn(fun() -> receiver(N, StartTime) end),

    % Start the sender process and send N messages to the receiver
    _SenderPid = spawn(fun() -> sender(ReceiverPid, N) end),
    io:format("Sender is going to send ~p messages~n", [N]).

sender(ReceiverPid, N) when N > 0 ->
    % Send a message to the receiver
    Data = <<"Hello">>,
    ReceiverPid ! {self(), Data},
    sender(ReceiverPid, N - 1);
sender(_, _) ->
    ok.

receiver(N, _Start) ->
    receive_messages(N, 0, _Start).

receive_messages(0, TotalBytes, _Start) ->
    % All messages received
    % Get the end time
    EndTime = erlang:monotonic_time(),

    % Calculate the time difference
    % TimeTaken = timer:now_diff(EndTime, StartTime) / 1000,  % Convert to microseconds
    TimeTaken = (EndTime - _Start) / 1000000,  % Convert to microseconds

    io:format("Received all messages totaling ~p bytes~n", [TotalBytes]),
    io:format("Time taken to send and receive ~p microseconds~n", [TimeTaken]);
receive_messages(N, TotalBytes, _Start) ->
    % Receive a message
    receive
        {_, Data} ->
            % Add the size of the received message to the total
            MessageSize = size(Data),
            receive_messages(N - 1, TotalBytes + MessageSize, _Start)
    end.

