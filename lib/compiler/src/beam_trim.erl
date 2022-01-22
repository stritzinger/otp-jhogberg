%%
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2007-2021. All Rights Reserved.
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

-module(beam_trim).
-export([module/2]).

-import(lists, [any/2,reverse/1,reverse/2,sort/1]).

-include("beam_asm.hrl").

-record(st,
        {safe :: sets:set(beam_asm:label()) %Safe labels.
        }).

-spec module(beam_utils:module_code(), [compile:option()]) ->
          {'ok',beam_utils:module_code()}.

module({Mod,Exp,Attr,Fs0,Lc}, _Opts) ->
    Fs = [function(F) || F <- Fs0],
    {ok,{Mod,Exp,Attr,Fs,Lc}}.

function({function,Name,Arity,CLabel,Is0}) ->
    try
        St = #st{safe=safe_labels(Is0, [])},
        Usage = none,
        Is = trim(Is0, Usage, St, []),
        {function,Name,Arity,CLabel,Is}
    catch
        Class:Error:Stack ->
            io:fwrite("Function: ~w/~w\n", [Name,Arity]),
            erlang:raise(Class, Error, Stack)
    end.

trim([{init_yregs,_}=I|Is], none, St, Acc) ->
    case usage(Is) of
        none ->
            trim(Is, none, St, [I|Acc]);
        Us ->
            trim([I|Is], Us, St, Acc)
    end;
trim([{init_yregs,{list,Kills0}}=I|Is0], [U|Us], St, Acc) ->
    Kills = [{kill,Y} || Y <- Kills0],
    try
        %% Find out the size and layout of the stack frame.
        %% Example of a layout:
        %%
        %%    [{kill,{y,0}},{dead,{y,1},{live,{y,2}},{kill,{y,3}}]
        %%
        %% That means that y0 and y3 are to be killed, that y1
        %% has been killed previously, and that y2 is live.
        {FrameSize, Layout} = frame_layout(Is0, Kills, U, St),

        %% Calculate all recipes that are not worse in terms
        %% of estimated execution time. The recipes are ordered
        %% in descending order from how much they trim.
        IsNotRecursive = is_not_recursive(Is0),
        Recipes = trim_recipes(Layout, U, IsNotRecursive),

        %% Try the recipes in order. A recipe may not work out because
        %% a register that was previously killed may be
        %% resurrected. If that happens, the next recipe, which trims
        %% less, will be tried.
        try_remap(Recipes, Is0, FrameSize)
    of
        {Is,TrimInstr} ->
            %% One of the recipes was applied.
            trim(Is, none, St, reverse(TrimInstr)++Acc)
    catch
        not_possible ->
            %% No recipe worked out. Use the original init_yregs/1
            %% instruction.
            trim(Is0, Us, St, [I|Acc])
    end;
trim([I|Is], [_|Us], St, Acc) ->
    trim(Is, Us, St, [I|Acc]);
trim([I|Is], none, St, Acc) ->
    trim(Is, none, St, [I|Acc]);
trim([I|Is], [], St, Acc) ->
    trim(Is, none, St, [I|Acc]);
trim([], _, _, Acc) ->
    reverse(Acc).

%% is_not_recursive([Instruction]) -> true|false.
%%  Test whether the next call or apply instruction may
%%  do a recursive call. Return `true` if the call is
%%  definitely not recursive, and `false` otherwise.
is_not_recursive([{call_ext,_,Ext}|_]) ->
    case Ext of
        {extfunc,M,F,A} ->
            erl_bifs:is_pure(M, F, A);
        _ ->
            false
    end;
is_not_recursive([{block,_}|Is]) -> is_not_recursive(Is);
is_not_recursive([{line,_}|Is]) -> is_not_recursive(Is);
is_not_recursive(_) -> false.

%% trim_recipes([{kill,R}|{live,R}|{dead,R}]) -> [Recipe].
%%      Recipe = {Kills,NumberToTrim,Moves}
%%      Kills = [{kill,Y}]
%%      Moves = [{move,SrcY,DstY}]
%%
%%  Calculate how to best trim the stack and kill the correct
%%  Y registers. Return a list of possible recipes. The best
%%  recipe (the one that trims the most) is first in the list.

trim_recipes(Layout, {Read, Written}, IsNotRecursive) ->
    UsedRegs = ordsets:union(Read, Written),

    Recipes0 = construct_recipes(Layout, 0, [], []),
    Recipes = filter_recipes(Recipes0, UsedRegs),
    NumOrigKills = length([I || {kill,_}=I <- Layout]),
    IsTooExpensive = is_too_expensive_fun(IsNotRecursive),
    [R || R <- Recipes,
          not is_too_expensive(R, NumOrigKills, IsTooExpensive)].

construct_recipes([{kill,{y,Trim0}}|Ks], Trim0, Moves, Acc) ->
    Trim = Trim0 + 1,
    Recipe = {Ks,Trim,Moves},
    construct_recipes(Ks, Trim, Moves, [Recipe|Acc]);
construct_recipes([{dead,{y,Trim0}}|Ks], Trim0, Moves, Acc) ->
    Trim = Trim0 + 1,
    Recipe = {Ks,Trim,Moves},
    construct_recipes(Ks, Trim, Moves, [Recipe|Acc]);
construct_recipes([{live,{y,Trim0}=Src}|Ks0], Trim0, Moves0, Acc) ->
    case take_last_dead(Ks0) of
        none ->
            %% No more recipes are possible.
            Acc;
        {Dst, Ks} ->
            Trim = Trim0 + 1,
            Moves = [{move,Src,Dst} | Moves0],
            Recipe = {Ks,Trim,Moves},
            construct_recipes(Ks, Trim, Moves, [Recipe | Acc])
    end;
construct_recipes([], _, _, Acc) ->
    Acc.

%% FIXME: Don't create bad recipes to begin with, and try to make that a bit
%% less messy than this hack.
filter_recipes([{_Ks, Trim, Moves}=Recipe | Rs], UsedRegs) ->
    Moved = ordsets:from_list([Src || {move,Src,_} <- Moves]),
    Illegal = ordsets:from_list([Dst || {move,_,Dst} <- Moves]),
    Eliminated = [{y,N} || N <- lists:seq(0, Trim - 1)],
    %% All eliminated registers that are also in the used set must be moved.
    UsedEliminated = ordsets:intersection(Eliminated, UsedRegs),
    case {ordsets:is_subset(UsedEliminated, Moved),
          ordsets:is_disjoint(Illegal, UsedRegs)} of
        {true, true} ->
            UsedEliminated = Moved,                        %Assertion.
            [Recipe | filter_recipes(Rs, UsedRegs)];
        _ ->
            filter_recipes(Rs, UsedRegs)
    end;
filter_recipes([], _) ->
    [].

take_last_dead(L) ->
    take_last_dead_1(reverse(L)).

take_last_dead_1([{kill,Reg}|Is]) ->
    {Reg,reverse(Is)};
take_last_dead_1([{dead,Reg}|Is]) ->
    {Reg,reverse(Is)};
take_last_dead_1(_) ->
    none.

%% Is trimming too expensive?
is_too_expensive({Ks,_,Moves}, NumOrigKills, IsTooExpensive) ->
    NumKills = num_kills(Ks, 0),
    NumMoves = length(Moves),
    IsTooExpensive(NumKills, NumMoves, NumOrigKills).

num_kills([{kill,_}|T], Acc) ->
    num_kills(T, Acc+1);
num_kills([_|T], Acc) ->
    num_kills(T, Acc);
num_kills([], Acc) -> Acc.

is_too_expensive_fun(true) ->
    %% This call is not recursive (because it is a call to a BIF).
    %% Here we should avoid trimming if the trimming sequence is
    %% likely to be more expensive than the original sequence.
    fun(NumKills, NumMoves, NumOrigKills) ->
            Penalty =
                if
                    %% Slightly penalize the use of any `move`
                    %% instruction to avoid replacing two `kill`
                    %% instructions with a `move` and a `trim`.
                    NumMoves =/= 0 -> 1;
                    true -> 0
                end,
            1 + Penalty + NumKills + NumMoves > NumOrigKills
    end;
is_too_expensive_fun(false) ->
    %% This call **may** be recursive. In a recursive function that
    %% builds up a huge stack, having unused stack slots will be very
    %% expensive. Therefore, we want to be biased towards trimming.
    %% We will do that by not counting the `trim` instruction in
    %% the formula below.
    fun(NumKills, NumMoves, NumOrigKills) ->
            NumKills + NumMoves > NumOrigKills
    end.

%% try_remap([Recipe], [Instruction], FrameSize) ->
%%           {[Instruction],[TrimInstruction]}.
%%  Try to renumber Y registers in the instruction stream. The
%%  first recipe that works will be used.
%%
%%  This function will issue a `not_possible` exception if none
%%  of the recipes were possible to apply.

try_remap([R|Rs], Is0, FrameSize) ->
    {TrimInstr, Moved, Trim} = expand_recipe(R, FrameSize),
    try remap(Is0, Moved, Trim) of
        Is -> {Is, TrimInstr}
    catch
        throw:not_possible ->
            try_remap(Rs, Is0, FrameSize)
    end;
try_remap([], _, _) ->
    throw(not_possible).

expand_recipe({Layout,Trim,Moves}, FrameSize) ->
    Is = reverse(Moves, [{trim,Trim,FrameSize-Trim}]),
    Moved = maps:from_list([{Src,Dst-Trim} || {move,{y,Src},{y,Dst}} <- Moves]),
    case [Y || {kill,Y} <- Layout] of
        [] ->
            {Is, Moved, Trim};
        [_|_]=Yregs ->
            {[{init_yregs,{list,Yregs}}|Is], Moved, Trim}
    end.

remap([{'%',Comment}=I|Is], Moved, Trim) ->
    case Comment of
        {var_info,Var0,Type} ->
            Var = remap_arg(Var0, Moved, Trim),
            [{'%',{var_info, Var, Type}} | remap(Is, Moved, Trim)];
        _ ->
            [I | remap(Is, Moved, Trim)]
    end;
remap([{apply,_}=I|Is], Moved, Trim) ->
    [I | remap(Is, Moved, Trim)];
remap([{bif,Name,Fail,Ss,D}|Is], Moved, Trim) ->
    I = {bif,Name,Fail,
         [remap_arg(S, Moved, Trim) || S <- Ss],
         remap_arg(D, Moved, Trim)},
    [I | remap(Is, Moved, Trim)];
remap([{block,Bl0}|Is], Moved, Trim) ->
    Bl = remap_block(Bl0, Moved, Trim),
    [{block,Bl} | remap(Is, Moved, Trim)];
remap([{bs_get_tail,Src,Dst,Live}|Is], Moved, Trim) ->
    I = {bs_get_tail,
         remap_arg(Src, Moved, Trim),
         remap_arg(Dst, Moved, Trim),Live},
    [I | remap(Is, Moved, Trim)];
remap([{bs_start_match4,Fail,Live,Src,Dst}|Is], Moved, Trim) ->
    I = {bs_start_match4,Fail,Live,
         remap_arg(Src, Moved, Trim),
         remap_arg(Dst, Moved, Trim)},
    [I | remap(Is, Moved, Trim)];
remap([{bs_set_position,Src1,Src2}|Is], Moved, Trim) ->
    I = {bs_set_position,
         remap_arg(Src1, Moved, Trim),
         remap_arg(Src2, Moved, Trim)},
    [I | remap(Is, Moved, Trim)];
remap([{call_fun,_}=I|Is], Moved, Trim) ->
    [I | remap(Is, Moved, Trim)];
remap([{call,_,_}=I|Is], Moved, Trim) ->
    [I | remap(Is, Moved, Trim)];
remap([{call_ext,_,_}=I|Is], Moved, Trim) ->
    [I | remap(Is, Moved, Trim)];
remap([{deallocate,N}|Is], Moved, Trim) ->
    I = {deallocate, N - Trim},
    [I | remap(Is, Moved, Trim)];
remap([{gc_bif,Name,Fail,Live,Ss,D}|Is], Moved, Trim) ->
    I = {gc_bif,Name,Fail,Live,
         [remap_arg(S, Moved, Trim) || S <- Ss],
         remap_arg(D, Moved, Trim)},
    [I | remap(Is, Moved, Trim)];
remap([{get_map_elements,Fail,M,{list,L0}}|Is], Moved, Trim) ->
    L = [remap_arg(E, Moved, Trim) || E <- L0],
    I = {get_map_elements,Fail,remap_arg(M, Moved, Trim),{list,L}},
    [I | remap(Is, Moved, Trim)];
remap([{init_yregs,{list,Yregs0}}|Is], Moved, Trim) ->
    Yregs = sort([remap_arg(Y, Moved, Trim) || Y <- Yregs0]),
    I = {init_yregs,{list,Yregs}},
    [I | remap(Is, Moved, Trim)];
remap([{line,_}=I|Is], Moved, Trim) ->
    [I | remap(Is, Moved, Trim)];
remap([{make_fun2,_,_,_,_}=I|T], Moved, Trim) ->
    [I | remap(T, Moved, Trim)];
remap([{make_fun3,F,Index,OldUniq,Dst0,{list,Env0}}|T], Moved, Trim) ->
    Env = [remap_arg(E, Moved, Trim) || E <- Env0],
    Dst = remap_arg(Dst0, Moved, Trim),
    I = {make_fun3,F,Index,OldUniq,Dst,{list,Env}},
    [I | remap(T, Moved, Trim)];
remap([{recv_marker_clear,Ref}|Is], Moved, Trim) ->
    I = {recv_marker_clear,remap_arg(Ref, Moved, Trim)},
    [I | remap(Is, Moved, Trim)];
remap([{recv_marker_reserve,Mark}|Is], Moved, Trim) ->
    I = {recv_marker_reserve,remap_arg(Mark, Moved, Trim)},
    [I | remap(Is, Moved, Trim)];
remap([{swap,Reg1,Reg2}|Is], Moved, Trim) ->
    I = {swap,remap_arg(Reg1, Moved, Trim),remap_arg(Reg2, Moved, Trim)},
    [I | remap(Is, Moved, Trim)];
remap([{test,Name,Fail,Ss}|Is], Moved, Trim) ->
    I = {test,Name,Fail,[remap_arg(S, Moved, Trim) || S <- Ss]},
    [I | remap(Is, Moved, Trim)];
remap([{test,Name,Fail,Live,Ss0,Dst0}|Is], Moved, Trim) ->
    Ss = [remap_arg(S, Moved, Trim) || S <- Ss0],
    Dst = remap_arg(Dst0, Moved, Trim),
    I = {test,Name,Fail,Live,Ss,Dst},
    [I | remap(Is, Moved, Trim)];
remap([return|_]=Is, _Moved, _Trim) ->
    Is.

remap_block([{set,Ds0,Ss0,Info}|Is], Moved, Trim) ->
    Ds = [remap_arg(D, Moved, Trim) || D <- Ds0],
    Ss = [remap_arg(S, Moved, Trim) || S <- Ss0],
    [{set,Ds,Ss,Info} | remap_block(Is, Moved, Trim)];
remap_block([], _Moved, _Trim) ->
    [].

remap_arg({y,Y}, _Moved, Trim) when Y >= Trim ->
    {y, Y - Trim};
remap_arg({y,Y}, Moved, Trim) when Y < Trim ->
    {y, map_get(Y, Moved)};
remap_arg(#tr{r={y,Y}}=T, _Moved, Trim) when Y >= Trim ->
    T#tr{r={y,Y - Trim}};
remap_arg(#tr{r={y,Y}}=T, Moved, Trim) when Y < Trim ->
    T#tr{r={y, map_get(Y, Moved)}};
remap_arg(Any, _Moved, _Trim) ->
    Any.

%% safe_labels([Instruction], Accumulator) -> gb_set()
%%  Build a gb_set of safe labels. The code at a safe
%%  label does not depend on the values in a specific
%%  Y register, only that all Y registers are initialized
%%  so that it safe to scan the stack when an exception
%%  is generated.
%%
%%  In other words, code at a safe label will continue
%%  to work if Y registers have been renumbered and
%%  the size of the stack frame has changed.

safe_labels([{label,L}|Is], Acc) ->
    case is_safe_label(Is) of
        true -> safe_labels(Is, [L|Acc]);
        false -> safe_labels(Is, Acc)
    end;
safe_labels([_|Is], Acc) ->
    safe_labels(Is, Acc);
safe_labels([], Acc) -> sets:from_list(Acc, [{version, 2}]).

is_safe_label([{'%',_}|Is]) ->
    is_safe_label(Is);
is_safe_label([{line,_}|Is]) ->
    is_safe_label(Is);
is_safe_label([{badmatch,{Tag,_}}|_]) ->
    Tag =/= y;
is_safe_label([{case_end,{Tag,_}}|_]) ->
    Tag =/= y;
is_safe_label([{try_case_end,{Tag,_}}|_]) ->
    Tag =/= y;
is_safe_label([if_end|_]) ->
    true;
is_safe_label([{block,Bl}|Is]) ->
    is_safe_label_block(Bl) andalso is_safe_label(Is);
is_safe_label([{call_ext,_,{extfunc,M,F,A}}|_]) ->
    erl_bifs:is_exit_bif(M, F, A);
is_safe_label(_) -> false.

is_safe_label_block([{set,Ds,Ss,_}|Is]) ->
    IsYreg = fun(#tr{r={y,_}}) -> true;
                ({y,_}) -> true;
                (_) -> false
             end,
    %% This instruction is safe if the instruction
    %% neither reads or writes Y registers.
    not (any(IsYreg, Ss) orelse any(IsYreg, Ds)) andalso
        is_safe_label_block(Is);
is_safe_label_block([]) -> true.

%% frame_layout([Instruction], [{kill,_}], St) ->
%%      [{kill,Reg} | {live,Reg} | {dead,Reg}]
%%  Figure out the layout of the stack frame.

frame_layout(Is, Kills, Usage, #st{safe=Safe}) ->
    N = frame_size(Is, Safe),

    {Read, _Written} = Usage,

    Regs = frame_layout_1(Kills, 0, N),

    Dead = ordsets:subtract(Regs, Read),
    Live = ordsets:subtract(Read, Dead),
    Layout = frame_layout_2(Kills, Dead, Live, 0),

    {N, Layout}.

%% Returns a list of all non-killed registers in the stack frame.
frame_layout_1([{kill,{y,Y}} | Ks], Y, N) ->
    frame_layout_1(Ks, Y + 1, N);
frame_layout_1(Ks, Y, N) when Y < N ->
    [{y,Y} | frame_layout_1(Ks, Y + 1, N)];
frame_layout_1([], Y, Y) ->
    [].

%% Adds 'live' and 'dead' annotations for all registers in the frame, keeping
%% 'kill' annotations and ignoring trailing 'live' ones.
frame_layout_2([], [], _Live, _Y) ->
    [];
frame_layout_2([{kill,{y,Y}}=I | Ks], Dead, Live, Y) ->
    [I | frame_layout_2(Ks, Dead, Live, Y + 1)];
frame_layout_2(Ks, [{y,Y}=R | Dead], Live, Y) ->
    [{dead, R} | frame_layout_2(Ks, Dead, Live, Y + 1)];
frame_layout_2(Ks, Dead, [{y,Y}=R | Live], Y) ->
    [{live, R} | frame_layout_2(Ks, Dead, Live, Y + 1)].

%% frame_size([Instruction], SafeLabels) -> FrameSize
%%  Find out the frame size by looking at the code that follows.
%%
%%  Implicitly, also check that the instructions are a straight
%%  sequence of code that ends in a return. Any branches are
%%  to safe labels (i.e., the code at those labels don't depend
%%  on the contents of any Y register).

frame_size([{'%',_}|Is], Safe) ->
    frame_size(Is, Safe);
frame_size([{block,_}|Is], Safe) ->
    frame_size(Is, Safe);
frame_size([{call_fun,_}|Is], Safe) ->
    frame_size(Is, Safe);
frame_size([{call,_,_}|Is], Safe) ->
    frame_size(Is, Safe);
frame_size([{call_ext,_,_}|Is], Safe) ->
    frame_size(Is, Safe);
frame_size([{apply,_}|Is], Safe) ->
    frame_size(Is, Safe);
frame_size([{bif,_,{f,L},_,_}|Is], Safe) ->
    frame_size_branch(L, Is, Safe);
frame_size([{gc_bif,_,{f,L},_,_,_}|Is], Safe) ->
    frame_size_branch(L, Is, Safe);
frame_size([{test,_,{f,L},_}|Is], Safe) ->
    frame_size_branch(L, Is, Safe);
frame_size([{test,_,{f,L},_,_,_}|Is], Safe) ->
    frame_size_branch(L, Is, Safe);
frame_size([{init_yregs,_}|Is], Safe) ->
    frame_size(Is, Safe);
frame_size([{make_fun2,_,_,_,_}|Is], Safe) ->
    frame_size(Is, Safe);
frame_size([{make_fun3,_,_,_,_,_}|Is], Safe) ->
    frame_size(Is, Safe);
frame_size([{recv_marker_clear,_}|Is], Safe) ->
    frame_size(Is, Safe);
frame_size([{recv_marker_reserve,_}|Is], Safe) ->
    frame_size(Is, Safe);
frame_size([{get_map_elements,{f,L},_,_}|Is], Safe) ->
    frame_size_branch(L, Is, Safe);
frame_size([{deallocate,N}|_], _) ->
    N;
frame_size([{line,_}|Is], Safe) ->
    frame_size(Is, Safe);
frame_size([{bs_start_match4,Fail,_,_,_}|Is], Safe) ->
    case Fail of
        {f,L} -> frame_size_branch(L, Is, Safe);
        _ -> frame_size(Is, Safe)
    end;
frame_size([{bs_set_position,_,_}|Is], Safe) ->
    frame_size(Is, Safe);
frame_size([{bs_get_tail,_,_,_}|Is], Safe) ->
    frame_size(Is, Safe);
frame_size([{swap,_,_}|Is], Safe) ->
    frame_size(Is, Safe);
frame_size(_, _) -> throw(not_possible).

frame_size_branch(0, Is, Safe) ->
    frame_size(Is, Safe);
frame_size_branch(L, Is, Safe) ->
    case sets:is_element(L, Safe) of
        false -> throw(not_possible);
        true -> frame_size(Is, Safe)
    end.

usage(Is) ->
    usage(Is, []).

usage([{label,_}|_], Acc) ->
    do_usage(Acc);
usage([I|Is], Acc) ->
    usage(Is, [I|Acc]);
usage([], Acc) ->
    do_usage(Acc).

do_usage(Is0) ->
    case Is0 of
        [return,{deallocate,_N}|Is] ->
            do_usage(Is, {[], []}, []);
        _ ->
            none
    end.

do_usage([{'%',_}|Is], Usage, Acc) ->
    do_usage(Is, Usage, [Usage|Acc]);
do_usage([{apply,_}|Is], Usage, Acc) ->
    do_usage(Is, Usage, [Usage|Acc]);
do_usage([{block,Blk}|Is], Usage0, Acc) ->
    Usage = do_usage_blk(Blk, Usage0),
    do_usage(Is, Usage, [Usage|Acc]);
do_usage([{bs_get_tail,Src,Dst,_}|Is], {Read0, Written0}, Acc) ->
    Written = ordsets:union(yregs([Dst]), Written0),
    Read1 = ordsets:del_element(Dst, Read0),
    Read = ordsets:union(Read1, yregs([Src])),
    Usage = {Read, Written},
    do_usage(Is, Usage, [Usage|Acc]);
do_usage([{bs_get_position,Src,Dst,_Live}|Is], {Read0, Written0}, Acc) ->
    Written = ordsets:union(yregs([Dst]), Written0),
    Read1 = ordsets:del_element(Dst, Read0),
    Read = ordsets:union(Read1, yregs([Src])),
    Usage = {Read, Written},
    do_usage(Is, Usage, [Usage|Acc]);
do_usage([{bs_set_position,Src1,Src2}|Is], {Read0, Written}, Acc) ->
    Read = ordsets:union(Read0, yregs([Src1,Src2])),
    Usage = {Read, Written},
    do_usage(Is, Usage, [Usage|Acc]);
do_usage([{bs_start_match4,_Fail,_Live,Src,Dst}|Is], {Read0, Written0}, Acc) ->
    Written = ordsets:union(yregs([Dst]), Written0),
    Read1 = ordsets:del_element(Dst, Read0),
    Read = ordsets:union(Read1, yregs([Src])),
    Usage = {Read, Written},
    do_usage(Is, Usage, [Usage|Acc]);
do_usage([{call,_,_}|Is], Usage, Acc) ->
    do_usage(Is, Usage, [Usage|Acc]);
do_usage([{call_ext,_,_}|Is], Usage, Acc) ->
    do_usage(Is, Usage, [Usage|Acc]);
do_usage([{call_fun,_}|Is], Usage, Acc) ->
    do_usage(Is, Usage, [Usage|Acc]);
do_usage([{bif,_,{f,_},Ss,Dst}|Is], {Read0, Written0}, Acc) ->
    Written = ordsets:union(yregs([Dst]), Written0),
    Read1 = ordsets:del_element(Dst, Read0),
    Read = ordsets:union(Read1, yregs(Ss)),
    Usage = {Read, Written},
    do_usage(Is, Usage, [Usage|Acc]);
do_usage([{gc_bif,_,{f,_},_,Ss,Dst}|Is], {Read0, Written0}, Acc) ->
    Written = ordsets:union(yregs([Dst]), Written0),
    Read1 = ordsets:del_element(Dst, Read0),
    Read = ordsets:union(Read1, yregs(Ss)),
    Usage = {Read, Written},
    do_usage(Is, Usage, [Usage|Acc]);
do_usage([{get_map_elements,{f,_},S,{list,List}}|Is], {Read0, Written0}, Acc) ->
    {Ss,Ds0} = beam_utils:split_even(List),
    Ds = ordsets:from_list(yregs(Ds0)),
    Written = ordsets:union(Written0, Ds),
    Read1 = ordsets:subtract(Read0, yregs(Ds)),
    Read = ordsets:union(Read1, yregs([S|Ss])),
    Usage = {Read, Written},
    do_usage(Is, Usage, [Usage|Acc]);
do_usage([{init_yregs,{list,Ds}}|Is], {Read0, Written0}, Acc) ->
    Read = ordsets:subtract(Read0, Ds),
    Written = ordsets:union(Written0, Ds),
    Usage = {Read, Written},
    do_usage(Is, Usage, [Usage|Acc]);
do_usage([{make_fun3,_,_,_,Dst,{list,Ss}}|Is], {Read0, Written0}, Acc) ->
    Written = ordsets:union(yregs([Dst]), Written0),
    Read1 = ordsets:del_element(Dst, Read0),
    Read = ordsets:union(Read1, yregs(Ss)),
    Usage = {Read, Written},
    do_usage(Is, Usage, [Usage|Acc]);
do_usage([{line,_}|Is], Usage, Acc) ->
    do_usage(Is, Usage, [Usage|Acc]);
do_usage([{recv_marker_clear,Src}|Is], {Read0, Written}, Acc) ->
    Read = ordsets:union(Read0, yregs([Src])),
    Usage = {Read, Written},
    do_usage(Is, Usage, [Usage|Acc]);
do_usage([{recv_marker_reserve,Src}|Is], {Read0, Written}, Acc) ->
    Read = ordsets:union(Read0, yregs([Src])),
    Usage = {Read, Written},
    do_usage(Is, Usage, [Usage|Acc]);
do_usage([{swap,R1,R2}|Is], {Read0, Written0}, Acc) ->
    Read = ordsets:union(Read0, yregs([R1,R2])),
    Written = ordsets:union(Written0, yregs([R1,R2])),
    Usage = {Read, Written},
    do_usage(Is, Usage, [Usage|Acc]);
do_usage([{test,_,{f,_},Ss}|Is], {Read0, Written}, Acc) ->
    Read = ordsets:union(Read0, yregs(Ss)),
    Usage = {Read, Written},
    do_usage(Is, Usage, [Usage|Acc]);
do_usage([{test,_,{f,_},_,Ss,Dst}|Is], {Read0, Written0}, Acc) ->
    Written = ordsets:union(yregs([Dst]), Written0),
    Read1 = ordsets:del_element(Dst, Read0),
    Read = ordsets:union(Read1, yregs(Ss)),
    Usage = {Read, Written},
    do_usage(Is, Usage, [Usage|Acc]);
do_usage([_I|_], _, _) ->
    %% io:format("~p\n", [I]),
    none;
do_usage([], _Usage, Acc) ->
    Acc;
do_usage(_, _, _) ->
    none.

do_usage_blk([{set,Ds,Ss,_}|Is], Usage0) ->
    {Read0, Written0} = do_usage_blk(Is, Usage0),
    Dsts = ordsets:from_list(yregs(Ds)),
    Written = ordsets:union(Written0, Dsts),
    Read1 = ordsets:subtract(Read0, Dsts),
    Read = ordsets:union(Read1, yregs(Ss)),
    {Read, Written};
do_usage_blk([], Usage) ->
    Usage.

yregs(Rs) ->
    ordsets:from_list(yregs_1(Rs)).

yregs_1([{y,_}=Y|Rs]) ->
    [Y|yregs_1(Rs)];
yregs_1([#tr{r={y,_}=Y}|Rs]) ->
    [Y|yregs_1(Rs)];
yregs_1([_|Rs]) ->
    yregs_1(Rs);
yregs_1([]) -> [].
