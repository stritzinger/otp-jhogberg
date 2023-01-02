-module(t).
-export([t/0, e/0, id/1]).

e() ->
    Letter = id(255),
    <<1:1, K/bits>> = <<1:1, Letter/utf8>>,
    case K of
        <<A/utf8>> -> {yay, A};
        _ -> erlang:display(boo)
    end.

t() ->
    {ok, Bin} = file:read_file("./lib/stdlib/test/unicode_util_SUITE_data/NormalizationTest.txt"),
    N = id(0),
    <<N:1, UnalignedBin/bits>> = <<N:1, Bin/bits>>,
    {Aligned, _} = timer:tc(fun() -> benchmark(Bin, 100) end),
    {Unaligned, _} = timer:tc(fun() -> benchmark(UnalignedBin, 100) end),
    {aligned, Aligned, unaligned, Unaligned}.

id(I) -> I.

benchmark(_, 0) ->
    ok;
benchmark(Bin, N) ->
    [A || <<A/utf8>> <= Bin],
    benchmark(Bin, N - 1).
