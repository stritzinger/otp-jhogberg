%%
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2022-2022. All Rights Reserved.
%%
%% Licensed under the Apache License, Version 2.0 (the "License");
%% you may not use this file except in compliance with the License.
%% You may obtain a copy of the License at
%%
%%     http://www.apache.org/licenses/LICENSE-2.0
%%
%% Unless required by applicable law or agreed to in writing, software
%% distributed under the License is distributed on an "AS IS" BASIS,
%% WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
%% See the License for the specific language governing permissions and
%% limitations under the License.
%%
%% %CopyrightEnd%
%%
%% This pass makes optimizations based on the inferred lifetimes of values,
%% for example allowing destructive record and map updates when we know that
%% the previous value cannot be reached in any way.
%%

-module(beam_ssa_lifetimes).
-export([module/2]).

-include("beam_ssa.hrl").

-record(func_info,
        { in = ordsets:new(),
          out = ordsets:new(),
          mutability }).

-record(mutability, { candidates = gb_sets:new(),
                      consumed = gb_sets:new(),
                      blacklist = gb_sets:new() }).

-import(lists, [flatten/1]).

-record(scan_st,
        { wl = wl_new() :: worklist(),
          committed = #{} :: #{ beam_ssa:b_local() => [boolean()] },
          updates = #{} :: #{ beam_ssa:b_local() => [boolean()] } }).

-spec module(beam_ssa:b_module(), [compile:option()]) ->
                    {'ok',beam_ssa:b_module()}.

module(#b_module{body=Fs0,exports=Exports}=Module, _Opts) ->
    Fdb = build_func_db(Module),
    Fs = if
        Fdb =:= #{} ->
            %% Very hacky :(
            Fs0;
        Fdb =/= #{} ->
            FuncMap = init_function_map(Fs0, #{}),
            St0 = init_scan_st(Exports),
            {Fdb1, _St} = scan_next(FuncMap, Fdb, St0),
            plan(Fs0, Fdb1)
    end,
    {ok, Module#b_module{body=Fs}}.

init_function_map([#b_function{anno=Anno}=F | Fs], FuncMap) ->
    {_,Name,Arity} = maps:get(func_info, Anno),
    FuncId = #b_local{name=#b_literal{val=Name},arity=Arity},
    init_function_map(Fs, FuncMap#{ FuncId => F });
init_function_map([], FuncMap) ->
    FuncMap.

init_scan_st(Exports) ->
    %% Start out as if all the roots have been called with immutable arguments.
    Roots = [#b_local{name=#b_literal{val=Name},arity=Arity} ||
                {Name, Arity} <- Exports],
    #scan_st{ committed=#{},
               updates=init_scan_st_1(Roots, #{}),
               wl=wl_defer_list(Roots, wl_new()) }.

init_scan_st_1([#b_local{arity=Arity}=Id | Exports], Updates0) ->
    Updates = Updates0#{ Id => lists:duplicate(Arity, false) },
    init_scan_st_1(Exports, Updates);
init_scan_st_1([], Updates) ->
    Updates.

scan_commit_args(Id, #scan_st{updates=Us,committed=Committed0}=State0) ->
    Mutability = map_get(Id, Us),
    Committed = Committed0#{ Id => Mutability },
    State = State0#scan_st{committed=Committed},
    {Mutability, State}.

scan_update_calls([#b_set{op=make_fun,args=[#b_local{}=Callee | _]} | Calls],
                  Mutability, St0) ->
    %% Assume that all parameters are immutable.
    ArgMutability = lists:duplicate(Callee#b_local.arity, false),
    St = scan_update_args(Callee, ArgMutability, St0),
    scan_update_calls(Calls, Mutability, St);
scan_update_calls([#b_set{op=call,args=[#b_local{}=Callee | Args]} | Calls],
                  Mutability, St0) ->
    %% The arguments were consumed by this call, so we don't need to check the
    %% candidate set.
    #mutability{consumed=Consumed} = Mutability,
    ArgMutability = [gb_sets:is_element(Arg, Consumed) || Arg <- Args],
    St = scan_update_args(Callee, ArgMutability, St0),
    scan_update_calls(Calls, Mutability, St);
scan_update_calls([], _Mutability, St) ->
    St.

scan_update_args(Callee, Mutability, #scan_st{committed=Committed}=State) ->
    case Committed of
        #{ Callee := Current } ->
            case parallel_and(Current, Mutability) of
                Current ->
                    %% We've already processed this function with these
                    %% arguments, so there's no need to visit it again.
                    State;
                Widened ->
                    scan_update_args_1(Callee, Widened, State)
            end;
        #{} ->
            scan_update_args_1(Callee, Mutability, State)
    end.

scan_update_args_1(Callee, Mutability, #scan_st{updates=Us0,wl=Wl0}=State) ->
    Us = case Us0 of
             #{ Callee := Current } ->
                 Us0#{ Callee => parallel_and(Current, Mutability) };
             #{} ->
                 Us0#{ Callee => Mutability }
         end,
    State#scan_st{updates=Us,wl=wl_add(Callee, Wl0)}.

parallel_and([A | As], [B | Bs]) ->
    [(A and B) | parallel_and(As, Bs)];
parallel_and([], []) ->
    [].

%%
%% During the inter-function pass, we track candidates variables on a per-block
%% basis and queue up calls, forwarding call information once we hit a return
%% terminator and can conclusively tell whether the term is observable or not.
%%
%% During the intra-function pass, we walk forward once to find sources, and if
%% there were any, we walk backwards and add destructive-update hints when
%% appropriate.
%%

scan_next(FuncMap, Fdb0, St0) ->
    case wl_next(St0#scan_st.wl) of
        {ok, FuncId} ->
            {St, Fdb} = scan_function(FuncId, FuncMap, Fdb0, St0),
            scan_next(FuncMap, Fdb, St);
        empty ->
            %% No more work to do, assert that we don't have any outstanding
            %% updates.
            #scan_st{updates=Same,committed=Same} = St0, %Assertion.
            {Fdb0, St0}
    end.

scan_function(Id, FuncMap, Fdb0, St0) ->
    case scan_function_1(Id, FuncMap, Fdb0, St0) of
        {false, false, State, Fdb} ->
            %% No added work and the types are identical. Pop ourselves from
            %% the work list and move on to the next function.
            Wl = wl_pop(Id, State#scan_st.wl),
            {State#scan_st{wl=Wl}, Fdb};
        {false, true, State, Fdb} ->
            %% We've added some work and our return type is unchanged. Keep
            %% following the work list without popping ourselves; we're very
            %% likely to need to return here later and can avoid a lot of
            %% redundant work by keeping our place in line.
            {State, Fdb};
        {true, WlChanged, State, Fdb} ->
            %% Our return type has changed so all of our (previously analyzed)
            %% callers need to be analyzed again.
            %%
            %% If our worklist is unchanged we'll pop ourselves since our
            %% callers will add us back if we need to analyzed again, and
            %% it's wasteful to stay in the worklist when we don't.
            Wl0 = case WlChanged of
                    true -> State#scan_st.wl;
                    false -> wl_pop(Id, State#scan_st.wl)
                end,

            #func_info{in=Cs0} = map_get(Id, Fdb),
            Updates = State#scan_st.updates,
            Callers = [C || C <- Cs0, is_map_key(C, Updates)],
            Wl = wl_defer_list(Callers, Wl0),

            {State#scan_st{wl=Wl}, Fdb}
    end.

scan_function_1(Id, FuncMap, Fdb0, #scan_st{wl=Wl0}=St0) ->
    #b_function{bs=Blocks,args=Args} = map_get(Id, FuncMap),
    Linear = beam_ssa:linearize(Blocks),

    {ArgMutability, St1} = scan_commit_args(Id, St0),
    %% FIXME: fugly.
    Candidates0 = [Arg || {Arg, true} <- lists:zip(Args, ArgMutability)],
    Candidates = gb_sets:from_list(Candidates0),

    Incoming = {#mutability{candidates=Candidates}, gb_sets:new()},
    Ls = #{ 0 => {incoming, Incoming} },
    {MutRet, St} = scan_bs(Linear, Fdb0, true, Ls, St1),

    #{ Id := #func_info{mutability={MutRet0, ArgMutability0}}=Entry } = Fdb0,
    WlChanged = wl_changed(Wl0, St#scan_st.wl),
    if
        MutRet =/= MutRet0; ArgMutability =/= ArgMutability0 ->
            Fdb = Fdb0#{ Id => Entry#func_info{mutability={MutRet,ArgMutability}} },

            {true, WlChanged, St, Fdb};
        MutRet =:= MutRet0, ArgMutability =:= ArgMutability0->
            {false, WlChanged, St, Fdb0}
    end.

scan_bs([{?EXCEPTION_BLOCK, _} | Bs], Fdb, MutRet, Ls, St) ->
    %% Nothing of interest happens here, skip it.
    scan_bs(Bs, Fdb, MutRet, Ls, St);
scan_bs([{L, #b_blk{is=Is,last=Last}} | Bs], Fdb, MutRet0, Ls0, St0) ->
    case Ls0 of
        #{ L := Incoming } ->
            {incoming, {Mutability0, Calls0}} = Incoming, %Assertion.
            {Mutability, Calls} = scan_is(Is, Fdb, Mutability0, Calls0,
                                          Ls0, St0),
            {MutRet, Ls1, St} = scan_update_successors(Last, Mutability, Calls,
                                                       MutRet0, Ls0, St0),
            Ls = Ls1#{ L := {outgoing, {Mutability, Calls}} },
            scan_bs(Bs, Fdb, MutRet and MutRet0, Ls, St);
        #{} ->
            %% Unreachable.
            scan_bs(Bs, Fdb, MutRet0, Ls0, St0)
    end;
scan_bs([], _Fdb, MutRet, _Ls0, St) ->
    {MutRet, St}.

scan_is([#b_set{op=phi,dst=Dst,args=Args} | Is],
         Fdb, Mutability0, Calls, Ls, St) ->
    Mutability = phi(Dst, Args, Ls, Mutability0),
    scan_is(Is, Fdb, Mutability, Calls, Ls, St);
scan_is([#b_set{op=call,dst=Dst,args=[#b_local{}=Callee | Args]}=I | Is], Fdb,
         Mutability0, Calls, Ls, St) ->
    Mutability = scan_is_call(Callee, Dst, Args, Fdb, Mutability0),
    scan_is(Is, Fdb, Mutability, gb_sets:add(I, Calls), Ls, St);
scan_is([#b_set{op=make_fun,args=[#b_local{}=_Callee | Args]}=I | Is], Fdb,
         Mutability0, Calls, Ls, St) ->
    Mutability = store(Args, Mutability0),
    scan_is(Is, Fdb, Mutability, gb_sets:add(I, Calls), Ls, St);
scan_is([#b_set{op=put_tuple,dst=Dst,args=Args} | Is],
         Fdb, Mutability0, Calls, Ls, St) ->
    Mutability = store(Args, Mutability0),
    scan_is(Is, Fdb, nominate(Dst, Mutability), Calls, Ls, St);
scan_is([#b_set{op=update_record,
                 dst=Dst,
                 args=[_Hint, _Size, Source | Updates]} | Is],
         Fdb, Mutability0, Calls, Ls, St) ->
    Mutability1 = store(Updates, Mutability0),
    Mutability = consume([Source], Mutability1),
    scan_is(Is, Fdb, nominate(Dst, Mutability), Calls, Ls, St);
scan_is([#b_set{op={succeeded,_}} | Is], Fdb, Mutability, Calls, Ls, St) ->
    scan_is(Is, Fdb, Mutability, Calls, Ls, St);
scan_is([#b_set{op=get_tuple_element,args=[Tuple, _Index]} | Is],
         Fdb, Mutability0, Calls, Ls, St) ->
    Mutability = observe(Tuple, Mutability0),
    scan_is(Is, Fdb, Mutability, Calls, Ls, St);
scan_is([#b_set{args=Args} | Is], Fdb, Mutability, Calls, Ls, St) ->
    scan_is(Is, Fdb, store(Args, Mutability), Calls, Ls, St);
scan_is([], _Fdb, Mutability, Calls, _Ls, _St) ->
    {Mutability, Calls}.

scan_is_call(Callee, Dst, Args, Fdb, Mutability0) ->
    #{ Callee := #func_info{mutability={MutabilityReturn, _}} } = Fdb,
    case MutabilityReturn of
        true -> nominate(Dst, consume(Args, Mutability0));
        false -> consume(Args, Mutability0)
    end.

scan_update_successors(#b_ret{arg=Arg}, Mutability0, Calls, MutRet0, Ls, St0) ->
    %% Note that we have to consume the return value _BEFORE_ updating calls
    %% as we'd otherwise risk returning an alias.
    #mutability{consumed=Consumed} = Mutability = consume([Arg], Mutability0),
    St = scan_update_calls(gb_sets:to_list(Calls), Mutability, St0),
    MutRet = MutRet0 and gb_sets:is_element(Arg, Consumed),
    {MutRet, Ls, St};
scan_update_successors(Last, Mutability, Calls, MutRet, Ls0, St) ->
    Ls = update_successors(Last, {Mutability, Calls}, Ls0),
    {MutRet, Ls, St}.

%%%
%%% FIXME: Explain how the optimization pass works.
%%%

-record(plan_st,
        { candidates = gb_sets:new(),
          blacklist = gb_sets:new() }).

plan([#b_function{anno=Anno,args=Args,bs=Bs}=F0 | Fs], Fdb) ->
    {_,Name,Arity} = maps:get(func_info, Anno),
    FuncId = #b_local{name=#b_literal{val=Name},arity=Arity},

    #{ FuncId := #func_info{mutability={_, ArgMutability}} } = Fdb,

    Candidates0 = [Arg || {Arg, true} <- lists:zip(Args, ArgMutability)],
    Candidates = gb_sets:from_list(Candidates0),

    Incoming = {#mutability{candidates=Candidates}, gb_sets:new()},
    Ls = #{ 0 => {incoming, Incoming} },
    Linear0 = beam_ssa:linearize(Bs),
    St = plan_bs(Linear0, Fdb, Ls, #plan_st{}),
    #plan_st{candidates=CandFoo,blacklist=Blacklist} = St,

    Linear = opt_bs(Linear0, gb_sets:subtract(CandFoo,Blacklist)),
    [F0#b_function{bs=maps:from_list(Linear)} | plan(Fs, Fdb)];
plan([], _Fdb) ->
    [].

plan_bs([{?EXCEPTION_BLOCK, _} | Bs], Fdb, Ls, St) ->
    %% Nothing of interest happens here, skip it.
    plan_bs(Bs, Fdb, Ls, St);
plan_bs([{L, #b_blk{is=Is,last=Last}} | Bs], Fdb, Ls0, St0) ->
    case Ls0 of
        #{ L := Incoming } ->
            {incoming, {Mutability0, Mutations0}} = Incoming, %Assertion.

            {Mutability, Mutations} = plan_is(Is, Fdb, Ls0,
                                              Mutability0, Mutations0),
            {Ls1, St} = plan_update_successors(Last, Mutability, Mutations,
                                              Ls0, St0),
            Ls = Ls1#{ L := {outgoing, {Mutability, Mutations}} },
            plan_bs(Bs, Fdb, Ls, St);
        #{} ->
            %% Unreachable.
            plan_bs(Bs, Fdb, Ls0, St0)
    end;
plan_bs([], _Fdb, _Ls0, St) ->
    St.

plan_is([#b_set{op=phi,dst=Dst,args=Args} | Is],
        Fdb, Ls, Mutability0, Mutations) ->
    Mutability = phi(Dst, Args, Ls, Mutability0),
    plan_is(Is, Fdb, Ls, Mutability, Mutations);
plan_is([#b_set{op=call,dst=Dst,args=[#b_local{}=Callee | Args]} | Is],
        Fdb, Ls, Mutability0, Mutations) ->
    Mutability = plan_is_call(Callee, Dst, Args, Fdb, Mutability0),
    plan_is(Is, Fdb, Ls, Mutability, Mutations);
plan_is([#b_set{op=put_tuple,dst=Dst,args=Args} | Is],
        Fdb, Ls, Mutability0, Mutations) ->
    Mutability = store(Args, Mutability0),
    plan_is(Is, Fdb, Ls, nominate(Dst, Mutability), Mutations);
plan_is([#b_set{op=update_record,
                args=[_Hint, _Size, Source | Updates]}=I | Is],
        Fdb, Ls, Mutability0, Mutations0) ->
    %% FIXME: This DOES NOT create a candidate when the `reuse` hint is used.
    %% modify the ssa_type pass so that it creates a `none` hint by default,
    %% which can then be turned into `reuse` in this pass if we determine that
    %% the result is observed (blacklisted).
    Mutability1 = store(Updates, Mutability0),
    {Mutability, Mutations} = plan_mutate(I, Source, Mutability1, Mutations0),
    plan_is(Is, Fdb, Ls, Mutability, Mutations);
plan_is([#b_set{op={succeeded,_}} | Is],
        Fdb, Ls, Mutability, Mutations) ->
    plan_is(Is, Fdb, Ls, Mutability, Mutations);
plan_is([#b_set{op=get_tuple_element,args=[Tuple, _Index]} | Is],
         Fdb, Ls, Mutability0, Mutations) ->
    Mutability = observe(Tuple, Mutability0),
    plan_is(Is, Fdb, Ls, Mutability, Mutations);
plan_is([#b_set{args=Args} | Is],
        Fdb, Ls, Mutability, Mutations) ->
    plan_is(Is, Fdb, Ls, store(Args, Mutability), Mutations);
plan_is([], _Fdb, _Ls, Mutability, Mutations) ->
    {Mutability, Mutations}.

plan_mutate(#b_set{dst=Dst}, Source, Mutability0, Mutations0) ->
    #mutability{candidates=Candidates} = Mutability0,
    Mutability = nominate(Dst, Mutability0),
    case gb_sets:is_element(Source, Candidates) of
        true ->
            Mutations = gb_sets:add({Source, Dst}, Mutations0),
            {consume([Source], Mutability), Mutations};
        false ->
            {Mutability, Mutations0}
    end.

plan_is_call(Callee, Dst, Args, Fdb, Mutability0) ->
    #{ Callee := #func_info{mutability={MutabilityReturn,_}} } = Fdb,
    case MutabilityReturn of
        true -> nominate(Dst, consume(Args, Mutability0));
        false -> consume(Args, Mutability0)
    end.

plan_update_successors(#b_ret{arg=Arg}, Mutability0, Mutations, Ls, St0) ->
    #mutability{consumed=Consumed,
                blacklist=Fhqwhgads} = consume([Arg], Mutability0),
    St = gb_sets:fold(fun({Source, Dst}, Acc) ->
                              #plan_st{candidates=Candidates0,
                                       blacklist=Blacklist0} = Acc,
                              case {gb_sets:is_element(Source, Consumed),
                                    gb_sets:is_element(Source, Fhqwhgads)} of
                                  {true, false} ->
                                      Candidates = gb_sets:add(Dst, Candidates0),
                                      Acc#plan_st{candidates=Candidates};
                                  {_, _} ->
                                      Blacklist = gb_sets:add(Dst, Blacklist0),
                                      Acc#plan_st{blacklist=Blacklist}
                              end
                      end, St0, Mutations),
    {Ls, St};
plan_update_successors(Last, Mutability, Mutations, Ls0, St) ->
    Ls = update_successors(Last, {Mutability, Mutations}, Ls0),
    {Ls, St}.

block_merge({LHSMutability, LHSAcc}, {RHSMutability, RHSAcc}) ->
    #mutability{candidates=LHSCandidates,
                consumed=LHSConsumed,
                blacklist=LHSBlacklist} = LHSMutability,
    #mutability{candidates=RHSCandidates,
                consumed=RHSConsumed,
                blacklist=RHSBlacklist} = RHSMutability,

    Candidates = gb_sets:intersection(LHSCandidates, RHSCandidates),

    %% FIXME: This is _very_ hacky. Both Consumed and Blacklist are spread to
    %% all blocks to support code like the following:
    %%
    %%  A = case ... of
    %%          true -> A0#aoeu{snth=gurka};
    %%          false -> A0
    %%      end,
    %%  A#aoeu{zvwm=gaffel}.
    %%
    %% If A0 is a valid candidate, then it's okay to destructively update it in
    %% the `true` branch, and okay to destructively update it afterwards since
    %% the result of both branches is a candidate.
    %%
    %% By marking A0 as consumed after _both_ branches we can be certain that
    %% any later use rolls it back in whatever branch actually consumed it, and
    %% by blacklisting if it's blacklisted in_any_ branch -- for example if the
    %% `false` branch stored `A0` in a tuple or similar -- we can be certain
    %% that `A#aoeu{zvwm=gaffel}` won't screw anything else up.
    Consumed = gb_sets:union(LHSConsumed, RHSConsumed),
    Blacklist = gb_sets:union(LHSBlacklist, RHSBlacklist),

    Mutability = #mutability{candidates=Candidates,consumed=Consumed,
                             blacklist=Blacklist},
    Acc = gb_sets:union(LHSAcc, RHSAcc),

    {Mutability, Acc}.

%%
%% FIXME: Optimize, explain this?
%%

opt_bs([{L, #b_blk{is=Is}=Blk} | Bs], Mutations) ->
    [{L, Blk#b_blk{is=opt_is(Is, Mutations)}} | opt_bs(Bs, Mutations)];
opt_bs([], _Mutations) ->
    [].

opt_is([#b_set{op=update_record,dst=Dst,args=[_Hint | Args]}=I0 | Is],
       Mutations) ->
    I = case gb_sets:is_element(Dst, Mutations) of
            true -> I0#b_set{args=[#b_literal{val=destructive} | Args]};
            false -> I0
        end,
    [I | opt_is(Is, Mutations)];
opt_is([#b_set{}=I | Is], Mutations) ->
    [I | opt_is(Is, Mutations)];
opt_is([], _Mutations) ->
    [].

%%
%% FIXME: Common code... Explain things better here?
%%

%% FIXME: Terminology.
nominate(#b_var{}=Arg, #mutability{candidates=Candidates0}=Mut0) ->
    Candidates = gb_sets:add_element(Arg, Candidates0),
    Mut0#mutability{candidates=Candidates}.

%% FIXME: Terminology.
%%
%% Consuming a variable means that we've mutated it, so it's no longer a valid
%% candidate. If we reach the end of the function without observing it, we know
%% that the mutation is safe.
consume(Args0, Mut0) ->
    #mutability{candidates=Candidates0,consumed=Consumed0}=Mut0,

    Args = gb_sets:from_list(Args0),
    Consumed = gb_sets:union(gb_sets:subtract(Consumed0, Args),
                             gb_sets:intersection(Candidates0, Args)),
    Candidates = gb_sets:subtract(Candidates0, Args),

    Mut0#mutability{candidates=Candidates,consumed=Consumed}.

%% FIXME: Terminology.
%%
%% Storing a candidate means we need to back out of any destructive updates.
store(Args, Mut0) ->
    #mutability{candidates=Candidates0,
                consumed=Consumed0,
                blacklist=Blacklist0}=Mut0,

    Stored = gb_sets:from_list(Args),
    Candidates = gb_sets:subtract(Candidates0, Stored),
    Consumed = gb_sets:subtract(Consumed0, Stored),

    %% FIXME: This will run like molasses, but makes bootstrapping easier.
    Blacklist = gb_sets:union(Blacklist0, Stored),

    Mut0#mutability{candidates=Candidates,
                    consumed=Consumed,
                    blacklist=Blacklist}.

%% FIXME: Terminology.
%%
%% Observing a candidate before it's been consumed is fine, but we'll need to
%% back out if we observe it after that point.
observe(Arg, Mut0) ->
    #mutability{consumed=Consumed0,
                blacklist=Blacklist0}=Mut0,

    {Consumed, Blacklist} = case gb_sets:is_element(Arg, Consumed0) of
                                true ->
                                    {gb_sets:del_element(Arg, Consumed0),
                                     gb_sets:add_element(Arg, Blacklist0)};
                                false ->
                                    {Consumed0, Blacklist0}
                            end,

    Mut0#mutability{consumed=Consumed,blacklist=Blacklist}.

phi(Var, Phis, Ls, Mutability0) ->
    %% All arguments are consumed so that they cannot be reused later on
    %% separately from `Var`.
    Mutability = consume([Arg || {#b_var{}=Arg, _From} <- Phis],
                         Mutability0),
    case phi_all_candidates_1(Phis, Ls) of
        true -> nominate(Var, Mutability);
        false -> Mutability
    end.

phi_all_candidates_1([{Arg, From} | Args], Ls) ->
    case Ls of
        #{ From := Outgoing } ->
            {outgoing, {Mutability, _Acc}} = Outgoing, %Assertion.
            #mutability{candidates=Candidates}=Mutability,
            case gb_sets:is_element(Arg, Candidates) of
                true -> phi_all_candidates_1(Args, Ls);
                false -> false
            end;
        #{} ->
            phi_all_candidates_1(Args, Ls)
    end;
phi_all_candidates_1([], _Ls) ->
    true.

%% FIXME: untangle this from the inter pass, and think of a better name than
%% "State" ...
update_successors(#b_br{bool=#b_var{},succ=Succ,fail=Fail},
                  State, Ls0) ->
    Ls = update_successor(Succ, State, Ls0),
    update_successor(Fail, State, Ls);
update_successors(#b_br{bool=#b_literal{val=true},succ=Succ},
                  State, Ls) ->
    update_successor(Succ, State, Ls);
update_successors(#b_switch{fail=Fail,list=List},
                  State, Ls0) ->
    Ls = update_successor(Fail, State, Ls0),
    update_successors_1([L || {_, L} <- List], State, Ls).

update_successors_1([S | Successors], State, Ls0) ->
    Ls = update_successor(S, State, Ls0),
    update_successors_1(Successors, State, Ls);
update_successors_1([], _State, Ls) ->
    Ls.

update_successor(?EXCEPTION_BLOCK, _State, Ls) ->
    %% We KNOW that no variables are used in the ?EXCEPTION_BLOCK,
    %% so there is no need to update observability information. That
    %% can be a huge timesaver for huge functions.
    Ls;
update_successor(S, State, Ls) ->
    case Ls of
        #{ S := {outgoing, _} } ->
            %% We're in a receive loop or similar; the target block will not be
            %% revisited.
            Ls;
        #{ S := {incoming, State0} } ->
            Ls#{ S := {incoming, block_merge(State0, State)} };
        #{} ->
            Ls#{ S => {incoming, State} }
    end.

%%
%% FIXME: The following has been crudely lifted from other passes for
%% convenience.
%% 

-record(worklist,
        { counter = 0 :: integer(),
          elements = gb_trees:empty() :: gb_trees:tree(integer(), term()),
          indexes = #{} :: #{ term() => integer() } }).

-type worklist() :: #worklist{}.

wl_new() -> #worklist{}.

%% Adds an element to the worklist, or moves it to the front if it's already
%% present.
wl_add(Element, #worklist{counter=Counter,elements=Es,indexes=Is}) ->
    case Is of
        #{ Element := Index } ->
            wl_add_1(Element, Counter, gb_trees:delete(Index, Es), Is);
        #{} ->
            wl_add_1(Element, Counter, Es, Is)
    end.

wl_add_1(Element, Counter0, Es0, Is0) ->
    Counter = Counter0 + 1,
    Es = gb_trees:insert(Counter, Element, Es0),
    Is = Is0#{ Element => Counter },
    #worklist{counter=Counter,elements=Es,indexes=Is}.

%% All mutations bump the counter, so we can check for changes without a deep
%% comparison.
wl_changed(#worklist{counter=Same}, #worklist{counter=Same}) -> false;
wl_changed(#worklist{}, #worklist{}) -> true.

%% Adds the given elements to the back of the worklist, skipping the elements
%% that are already present. This lets us append elements arbitrarily after the
%% current front without changing the work order.
wl_defer_list(Elements, #worklist{counter=Counter,elements=Es,indexes=Is}) ->
    wl_defer_list_1(Elements, Counter, Es, Is).

wl_defer_list_1([Element | Elements], Counter0, Es0, Is0) ->
    case Is0 of
        #{ Element := _ } ->
            wl_defer_list_1(Elements, Counter0, Es0, Is0);
        #{} ->
            Counter = Counter0 + 1,
            Es = gb_trees:insert(-Counter, Element, Es0),
            Is = Is0#{ Element => -Counter },
            wl_defer_list_1(Elements, Counter, Es, Is)
    end;
wl_defer_list_1([], Counter, Es, Is) ->
    #worklist{counter=Counter,elements=Es,indexes=Is}.

wl_next(#worklist{indexes=Is}) when Is =:= #{} ->
    empty;
wl_next(#worklist{elements=Es,indexes=Is}) when Is =/= #{} ->
    {_Key, Element} = gb_trees:largest(Es),
    {ok, Element}.

%% Removes the front of the worklist.
wl_pop(Element, #worklist{counter=Counter0,elements=Es0,indexes=Is0}=Wl) ->
    Counter = Counter0 + 1,
    {_Key, Element, Es} = gb_trees:take_largest(Es0), %Assertion.
    Is = maps:remove(Element, Is0),
    Wl#worklist{counter=Counter,elements=Es,indexes=Is}.

%% Builds a function information map with basic information about incoming and
%% outgoing local calls, as well as whether the function is exported.
build_func_db(#b_module{body=Fs,attributes=Attr,exports=Exports0}) ->
    Exports = fdb_exports(Attr, Exports0),
    try
        fdb_fs(Fs, Exports, #{})
    catch
        %% All module-level optimizations are invalid when a NIF can override a
        %% function, so we have to bail out.
        throw:load_nif -> #{}
    end.

fdb_exports([{on_load, L} | Attrs], Exports) ->
    %% Functions marked with on_load must be treated as exported to prevent
    %% them from being optimized away when unused.
    fdb_exports(Attrs, flatten(L) ++ Exports);
fdb_exports([_Attr | Attrs], Exports) ->
    fdb_exports(Attrs, Exports);
fdb_exports([], Exports) ->
    gb_sets:from_list(Exports).

fdb_fs([#b_function{bs=Bs,args=Args}=F | Fs], Exports, FuncDb0) ->
    Id = get_func_id(F),

    Mutability = {true, [true || _ <- Args]},

    FuncDb1 = case FuncDb0 of
                  %% We may have an entry already if someone's called us.
                  #{ Id := Info } ->
                      FuncDb0#{ Id := Info#func_info{ mutability=Mutability }};
                  #{} ->
                      FuncDb0#{ Id => #func_info{ mutability=Mutability }}
              end,

    RPO = beam_ssa:rpo(Bs),
    FuncDb = beam_ssa:fold_blocks(fun(_L, #b_blk{is=Is}, FuncDb) ->
                                       fdb_is(Is, Id, FuncDb)
                               end, RPO, FuncDb1, Bs),

    fdb_fs(Fs, Exports, FuncDb);
fdb_fs([], _Exports, FuncDb) ->
    FuncDb.

fdb_is([#b_set{op=call,
               args=[#b_local{}=Callee | _]} | Is],
       Caller, FuncDb) ->
    fdb_is(Is, Caller, fdb_update(Caller, Callee, FuncDb));
fdb_is([#b_set{op=call,
               args=[#b_remote{mod=#b_literal{val=erlang},
                               name=#b_literal{val=load_nif}},
                     _Path, _LoadInfo]} | _Is], _Caller, _FuncDb) ->
    throw(load_nif);
fdb_is([#b_set{op=MakeFun,
               args=[#b_local{}=Callee | _]} | Is],
       Caller, FuncDb) when MakeFun =:= make_fun;
                            MakeFun =:= old_make_fun ->
    %% The make_fun instruction's type depends on the return type of the
    %% function in question, so we treat this as a function call.
    fdb_is(Is, Caller, fdb_update(Caller, Callee, FuncDb));
fdb_is([_ | Is], Caller, FuncDb) ->
    fdb_is(Is, Caller, FuncDb);
fdb_is([], _Caller, FuncDb) ->
    FuncDb.

fdb_update(Caller, Callee, FuncDb) ->
    CallerVertex = maps:get(Caller, FuncDb, #func_info{}),
    CalleeVertex = maps:get(Callee, FuncDb, #func_info{}),

    Calls = ordsets:add_element(Callee, CallerVertex#func_info.out),
    CalledBy = ordsets:add_element(Caller, CalleeVertex#func_info.in),

    FuncDb#{ Caller => CallerVertex#func_info{out=Calls},
             Callee => CalleeVertex#func_info{in=CalledBy} }.

get_func_id(F) ->
    {_Mod, Name, Arity} = beam_ssa:get_anno(func_info, F),
    #b_local{name=#b_literal{val=Name}, arity=Arity}.
