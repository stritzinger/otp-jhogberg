-module(benchmark_basic_new).
-export([start/0]).

-define(REPEAT, 1000).

start() ->
    basic_test(),
    ok.

basic_test() ->
    % Get the start time
    StartTime = erlang:monotonic_time(),

    % Start the receiver process
    ReceiverPid = spawn(fun() -> basic_receiver(StartTime) end),

    % Start the sender process and send N messages to the receiver
    _SenderPid = spawn(fun() -> basic_sender_start(ReceiverPid) end),

    % io:format("Sender is going to send ~p messages.~n", [N]).
    ok.

basic_sender_start(ReceiverPid) ->
    io:format("Sender is going to send msg: start~n"),
    ReceiverPid ! {start, self()},

    io:format("Sender is going to send msg: data~n"),
    basic_sender(ReceiverPid, ?REPEAT).

basic_sender(ReceiverPid, N) when N > 0 ->
    _Data = <<"Hello">>,
    ReceiverPid ! {data, self(), _Data},
    basic_sender(ReceiverPid, N-1);
basic_sender(ReceiverPid, 0) ->
    io:format("Sender is going to send msg: stop~n"),
    ReceiverPid ! {stop, self()},
    ok.


basic_receiver(_StartTime) ->
    receive
        {start, SenderPid} ->
            io:format("Receiver: Received message: start from ~p~n", [SenderPid]),
            basic_receive_messages(0, _StartTime)
    end.

basic_receiver_end(TotalBytes, _StartTime) ->
    % Get the end time
    EndTime = erlang:monotonic_time(),

    % TimeTaken = timer:now_diff(EndTime, _StartTime) / 1000,  % Convert to microseconds
    TimeTaken = erlang:convert_time_unit(EndTime - _StartTime, native, microsecond),
    io:format("Received all messages totaling ~p bytes~n", [TotalBytes]),
    io:format("Time taken to send and receive ~p microseconds~n", [TimeTaken]),
    ok.

basic_receive_messages(TotalBytes, _StartTime) ->
    % Receive a message
    receive
        {data, _SenderPid, _Data} ->
            io:format("Receiver: Received message: data <<~s>> from ~p~n", [_Data, _SenderPid]),
            MessageSize = byte_size(_Data),
            basic_receive_messages(TotalBytes + MessageSize, _StartTime);
        {stop, SenderPid} ->
            io:format("Receiver: Received message:stop from ~p~n", [SenderPid]),
            _ = basic_receiver_end(TotalBytes, _StartTime)
    end.


