-module(unions).
-compile([export_all, nowarn_export_all]).

-spec foo(any()) -> nominal(foo, 1 | 2 | 3).
foo(X) -> X.

-spec bar(any()) -> nominal(bar, 1 | 2 | 3).
bar(X) -> X.

-spec qux(nominal(foo, 1 | 2 | 3)) -> ok.
qux(X) -> X.

-spec baz(nominal(bar, 1 | 2 | 3)) -> ok.
baz(X) -> X.

trivial(X) ->
    %% Should work fine
    qux(foo(X)),
    baz(bar(X)),
    qux(1),
    baz(1),
    %% Should not work!
    baz(union_foo(X)).

union_foo(X) ->
    case X of 
       1 -> foo(X);
       _ -> 4
    end.
