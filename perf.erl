-module(perf).
-export([f/0]).

f() ->
  R = fun rand:uniform/1,
  RR = fun(N) -> [rand:uniform(1000) || _ <- lists:seq(0, N)] end,
  Ranges = [{R(500) + 500, R(500) + 500} || _ <- lists:seq(1, 1000)],
  Times = lists:map(
    fun({A, B}) ->
      {T, _} = timer:tc(
        fun() ->
          lists:subtract(RR(A), RR(B))
        end
      ), T
    end, Ranges),
  Sum = lists:foldl(fun(T, Acc) -> T + Acc end, 0, Times),
  io:format("AVG ~p~n", [Sum / length(Times)]).

