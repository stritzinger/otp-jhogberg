-module(t).

-export([t1/0, t2/0, t3/0, test/1]).

t1() -> test(#{a=>a}).
t2() -> test(#{a=>{2}}).
t3() -> test(#{a=>{3}}).

test(#{a:={X}}) -> X+1.

    TypeB = {c,map,
               {[],
                {c,atom,[gurka],unknown},
                any},
               unknown},
    
    TypeC = {c,map,
               {[{{c,atom,[friarelli],unknown},
                  mandatory,
                  {c,atom,[gaffel],unknown}}],
                {c,map,{[],any,any},unknown},
                {c,atom,[tomat],unknown}},
               unknown},
    
    LHS_Sup = erl_types:t_sup(TypeA, erl_types:t_sup(TypeB, TypeC)),
    RHS_Sup = erl_types:t_sup(erl_types:t_sup(TypeA, TypeB), TypeC),
    
    LHS_Sup = RHS_Sup. %% Crash!
