-module(meterfeet).
-export([t1/0, t2/0, t3/0]).


-type meter() :: nominal(meter, integer()).
-type feet() :: nominal(feet, integer()).

-spec id1(meter() | integer()) -> integer().
id1(X) -> 
    X + 7.

-spec id2(meter()) -> integer().
id2(X) -> 
    X * 10.

-spec feet_ctor(integer()) -> feet().
feet_ctor(X) -> X.

-spec meter_ctor(integer()) -> meter().
meter_ctor(X) -> X.

t1() -> 
    id1(feet_ctor(42)).

t2() -> 
    id2(feet_ctor(42)).


t3() ->
    feet_ctor(meter_ctor(42)).
