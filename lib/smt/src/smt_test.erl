-module(smt_test).

-export([run/0]).

-spec run() -> term().
run() ->
    smt:load(),
    Options = #{log_file => "smt-log.txt"},
    S = smt:new(Options),
    Declarations = [
        {datatype, 'MyType', [
            {integer_term, [{integer_value, 'Int'}]}
        ]}
    ],
    smt:declare(Declarations, S).
