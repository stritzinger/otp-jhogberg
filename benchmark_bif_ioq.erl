-module(benchmark_bif_ioq).
-export([start/0]).

-define(BYTESSENT, 1000).
-define(REPEAT, 10).
-define(MS, 0).
-define(DATA, <<0:?REPEAT/unit:8>>).

start() ->
    ioq_test(),
    ok.

ioq_test() ->
    % Start the receiver process
    ReceiverPid = spawn(fun() -> ioq_receiver_start(erlang:monotonic_time()) end),

    % Start the sender process and send N messages to the receiver
    _SenderPid = spawn(fun() -> ioq_sender_start(ReceiverPid) end),
    ok.

ioq_sender_start(ReceiverPid) ->
    io:format("Sender is creating io queue~n"),
    Queue = erlang:create_io_queue(),
    io:format("Sender: Sends msg: start~n"),
    ReceiverPid ! {start, self()},
    ioq_sender_data(ReceiverPid, Queue).

ioq_sender_data(ReceiverPid, Queue) ->
    QueueBytes = erlang:write_io_queue(Queue, [?DATA]),
    TotalBytes = QueueBytes,
    io:format("Sender: Sends msg: data~n"),
    ReceiverPid ! {data, self(), Queue},
    ioq_write(ReceiverPid, Queue, QueueBytes, TotalBytes).

ioq_write(ReceiverPid, _Queue, _QueueBytes, ?BYTESSENT) ->
    io:format("Sender: Completed date sending via IO Queue~n"),
    ioq_sender_stop(ReceiverPid);
ioq_write(ReceiverPid, Queue, QueueBytes0,TotalBytes0) when TotalBytes0 < ?BYTESSENT ->
    TotalBytes = TotalBytes0 + byte_size(?DATA),
    ExpectBytes = QueueBytes0 + byte_size(?DATA),
    case erlang:write_io_queue(Queue, [?DATA]) of
        ExpectBytes ->
            io:format("Sender: Writes data again into Queue~n"),
            ioq_write(ReceiverPid, Queue, ExpectBytes, TotalBytes);
        QueueBytes ->
            io:format("Sender: Sends msg: data one more time~n"),
            ReceiverPid ! {data, self(), Queue},
            ioq_write(ReceiverPid, Queue, QueueBytes, TotalBytes)
    end.

ioq_sender_stop(ReceiverPid) ->
    io:format("Sender: Sends msg: stop~n"),
    ReceiverPid ! {stop, self()},
    ok.


ioq_receiver_start(StartTime) ->
    receive
        {start, SenderPid} ->
            io:format("Receiver: Received message: start from ~p~n", [SenderPid]),
	    SenderPid,
	    ioq_receiver(StartTime, 0, 0)
    end.

ioq_receiver(StartTime, TotalBytes, TotalDataMsgCount) ->
    receive
        {data, SenderPid, Queue} ->
            timer:sleep(?MS),
            io:format("Receiver: Received message: data from ~p~n", [SenderPid]),
	    SenderPid,
            ReceiveBytes = erlang:empty_io_queue(Queue),
	    ioq_receiver(StartTime, TotalBytes + ReceiveBytes, data_msg_stats(TotalDataMsgCount));
        {stop, SenderPid} ->
            io:format("Receiver: Received message: stop from ~p~n", [SenderPid]),
	    SenderPid,
	    _ = ioq_receiver_end(TotalBytes, StartTime, TotalDataMsgCount)
    end.

ioq_receiver_end(TotalBytes, StartTime, TotalDataMsgCount) ->
    EndTime = erlang:monotonic_time(),
    TimeTaken = erlang:convert_time_unit(EndTime - StartTime, native, microsecond),
 
    % All messages received
    io:format("Receiver: Sleep ~p ms every time it receives data message~n", [?MS]),
    io:format("Receiver: Received data messages totaling ~p times~n", [TotalDataMsgCount]),
    io:format("Receiver: Read Data from Queue totaling ~p bytes~n", [TotalBytes]),
    io:format("----------------------------------------------------------~n"),
    io:format("----- Time taken to send and receive ~p microseconds------~n", [TimeTaken]),
    ok.

data_msg_stats(TotalDataMsgCount) ->
    TotalDataMsgCount + 1.
