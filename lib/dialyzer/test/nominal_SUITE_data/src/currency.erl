-module(currency).
-compile([export_all]).

-type euro() :: nominal(euro, float()).
-spec euro_ctor(float()) -> euro().
euro_ctor(X) -> X.

-type kr() :: nominal(kr, integer()).

-type dollar() :: nominal(dollar, float()).
-spec dollar_ctor(float()) -> dollar().
dollar_ctor(X) -> X.

-type money() :: nominal(money, euro()|kr()|dollar()).

-type rate() :: nominal(rate, float()).
-spec rate_ctor(float()) -> rate().
rate_ctor(X) -> X.

-type transaction() :: nominal(transaction, {integer(), number(), number()}).
-spec transaction_ctor(integer(), money(), euro()|kr()) -> transaction().
transaction_ctor(X, Y, Z) -> {X, Y, Z}.

-spec euroToKr(rate(), euro()) -> kr().
euroToKr(Rate, Amount) -> trunc(Rate * Amount).

-spec krToEuro(rate(), kr()) -> euro().
krToEuro(Rate, Amount) -> float(Rate * Amount).

-spec euroToDollar(rate(), euro()) -> dollar().
euroToDollar(Rate, Amount) -> Rate * Amount.

t1() ->
    krToEuro(3.0, 7).

t2() ->
    euroToKr(rate_ctor(3.0), dollar_ctor(3.5)).

t3() ->
    transaction_ctor(305, 3.0, dollar_ctor(204.0)).

-spec t4(kr()) -> nominal(kr, 10 | 20 | 30) | nominal(euro, float()) | atom().
t4(X) -> 5.

-spec t5(nominal(kr, 21 | 22) | nominal(kr, 24)) -> nominal(kr, 84| 88).
t5(X) -> X * 4.