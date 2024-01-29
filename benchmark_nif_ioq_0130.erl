-module(benchmark_nif_ioq_0130).
-export([start/0]).

-define(REPEAT, 10000000).

start() ->
    basic_test(?REPEAT),
    ioq_test(),
    ok.

basic_test(N) ->
    % Start the receiver process
    ReceiverPid = spawn(fun() -> receiver(N) end),

    % Get the start time
    StartTime = erlang:monotonic_time(),

    % Start the sender process and send N messages to the receiver
    sender(ReceiverPid, N),

    % Get the end time
    EndTime = erlang:monotonic_time(),

    % Calculate the time difference
    % TimeTaken = timer:now_diff(EndTime, StartTime) / 1000,  % Convert to microseconds
    TimeTaken = (EndTime - StartTime) / 1000,  % Convert to microseconds

    io:format("Time taken to send and receive ~p messages: ~p microseconds~n", [N, TimeTaken]).

sender(ReceiverPid, N) when N > 0 ->
    % Send a message to the receiver
    Data = <<"Hello">>,
    ReceiverPid ! {self(), Data},
    sender(ReceiverPid, N - 1);
sender(_, _) ->
    ok.

receiver(N) ->
    receive_messages(N, 0).

receive_messages(0, TotalBytes) ->
    % All messages received
    io:format("Received all messages totaling ~p bytes~n", [TotalBytes]);

receive_messages(N, TotalBytes) ->
    % Receive a message
    receive
        {_, Data} ->
            % Add the size of the received message to the total
            MessageSize = size(Data),
            receive_messages(N - 1, TotalBytes + MessageSize)
    end.



% ioq send, receive
ioq_test() ->
    % Start the receiver process
    ReceiverPid = spawn(fun() -> ioq_receiver() end),
    
    % Start the sender process and pass the receiver's pid to it
    spawn(fun() -> ioq_sender(ReceiverPid) end).

ioq_sender(ReceiverPid) ->
    % Send data to the receiver process
    Data = "Hello, Erlang!",
    ReceiverPid ! {self(), Data},  % Send a message to the receiver process
    io:format("IO queue: Sender sent data: ~p~n", [Data]).

ioq_receiver() ->
    receive
        {SenderPid, Data} ->
            io:format("IO queue: Receiver received data (~p) from ~p~n", [Data, SenderPid])
    end.

% Example usage:
% data_transfer:start().
