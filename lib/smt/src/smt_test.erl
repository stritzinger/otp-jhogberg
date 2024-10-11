-module(smt_test).

-export([run/0]).
-export([run/1]).

-spec run() -> term().
run() ->
    smt:load(),
    Options = #{log_file => "smt-log.txt"},
    S = smt:new(Options),
    Declarations = [
        {constant, a, 'Int'},
        {uninterpreted_function, f, ['Int', 'Bool'], 'Int'}
    ],
    {ok, S1} = smt:declare(Declarations, S),
    io:format("Declarations ~p~n", [S1]),
    {ExprId1, S2} = smt:expression({'Int', 4}, S1),
    {ExprId2, S3} = smt:expression({'Bool', true}, S2),
    {ExprId3, S4} = smt:expression({numeric_lt, a, ExprId1}, S3),
    {ExprId4, S5} = smt:expression({numeric_lt, {f, [a, ExprId2]}, {'Int', 100}}, S4),
    {ok, S6} = smt:assert(ExprId3, S5),
    {ok, S7} = smt:assert(ExprId4, S6),
    io:format("Final context ~p~n", [S7]),
    {Res, _Context} = smt:check(S7),
    Res.

run(Filename) ->
    parse(Filename).

parse(Filename) ->
    {ok, Binary} = file:read_file(Filename),
    case smtlib2_scanner:string(binary_to_list(Binary)) of
        {ok, Tokens, _EndLine} ->
            io:format("Tokens ~p\n",[Tokens]),
             % checking the work of the Yecc
            case smtlib2_parser:parse(Tokens) of
                {ok, Res} ->
                    io:format("Parser Result ~p \n", [Res]),
                    smt(Res);
                Else ->
                    io:format("Parser failed: ~p\n On tokens : ~p\n", [Else, Tokens])
            end,
            ok;
        ErrorInfo ->
            io:format("Scanner failed: ~p\n On File ~p\n", [ErrorInfo, Filename])
    end.

smt(Expressions) ->
    smt:load(),
    S = smt:new(),
    rec_execute(Expressions, S).

 rec_execute([], _) -> ok;
 rec_execute([E|Expressions], S) ->
    S1 = case execute(E, S) of
        {ok, NewS} -> NewS;
        {Res, S} -> io:format("~p~n",[Res])
    end,
     rec_execute(Expressions, S1).

execute({constant, Name, Type} = D, S) ->
    smt:declare(D, S);
execute({uninterpreted_function, _Name, _Args, _Ret} = D, S) ->
    smt:declare(D, S);
execute({assert, Expr}, S) ->
    {Id, S1} = smt:expression(Expr, S),
    smt:assert(Id, S1);
execute({'check-sat'}, S) ->
    smt:check(S);
execute({'get-model'}, S) ->
    % not available
    {ok, S}.
