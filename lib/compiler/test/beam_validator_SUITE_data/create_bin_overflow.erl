-module(create_bin_overflow).
-compile([export_all,nowarn_export_all]).

t() ->
    Bin = id(<<"Some arbitrary but very long content", 0:4096>>),

    WordBits = erlang:system_info(wordsize) * 8,

    %% The debug emulator crashes more reliably when the result buffer is too
    %% large to be allocated on the heap.
    Size = id((1 bsl (WordBits - 5)) - (bit_size(Bin) div 32) + 17),
    <<544:WordBits>> = <<(Size * 32 + bit_size(Bin)):WordBits>>, %Assertion.

    Other = id(<<0>>),

    <<0,
      Bin/bits,

      %% We need to do this 32 times (59 -> 64 bits) to force an overflow of
      %% the size calc.
      %%
      %% Binary construction will fail because Bin is smaller than the
      %% requested size, but we won't raise the exception until we've written
      %% the previous segment into an undersized buffer.
      Other:Size/bits,
      Other:Size/bits,
      Other:Size/bits,
      Other:Size/bits,

      Other:Size/bits,
      Other:Size/bits,
      Other:Size/bits,
      Other:Size/bits,

      Other:Size/bits,
      Other:Size/bits,
      Other:Size/bits,
      Other:Size/bits,

      Other:Size/bits,
      Other:Size/bits,
      Other:Size/bits,
      Other:Size/bits,

      Other:Size/bits,
      Other:Size/bits,
      Other:Size/bits,
      Other:Size/bits,

      Other:Size/bits,
      Other:Size/bits,
      Other:Size/bits,
      Other:Size/bits,

      Other:Size/bits,
      Other:Size/bits,
      Other:Size/bits,
      Other:Size/bits,

      Other:Size/bits,
      Other:Size/bits,
      Other:Size/bits,
      Other:Size/bits>>.

id(I) -> I.
