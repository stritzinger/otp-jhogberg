%%
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2023-2023. All Rights Reserved.
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

%%
%% FIXME: this is tailored to Z3 at the moment, but the idea is to support
%% several simultaneous solvers in the future (e.g. for quorum or covering each
%% other's gaps).
%% 
%% We therefore assign our own identifiers to each expression, as different
%% solvers have different interfaces and what might require one primitive in
%% one solver may require several in another.
%%
%% As an aside, I've also largely ignored error checking in here, relying on
%% the underlying solver to slap us whenever anything goes wrong. Making us
%% independently able to find errors is too much work to justify doing so at
%% this stage -- we don't even know if this will fly yet -- but we'll want to
%% do so later on because the scaffolding required for error checking can also
%% be used for disambiguating functions and macros based on sorts.
%%

-module(smt).
-export([new/0,
         new/1,

         expression/2,
         declare/2,

         simplify/2,

         assert/2,
         push/1,
         pop/2,

         check/1,
         check/2,

         close/1]).

-export([load/0]).

-import(lists, [foldl/3, mapfoldl/3, zip/2]).

-define(DEBUG, false).

-record(smt, {context :: term(),
              fence :: non_neg_integer(),
              counter :: pos_integer(),
              expressions :: map(),
              macros :: map(),
              sorts :: map(),
              stack :: [{Counter :: pos_integer(),
                         Expressions :: map(),
                         Macros :: map(),
                         Sorts :: map()}] }).

-spec load() -> ok.
load() ->
    %% HACK: Put this in application startup instead, and get rid of this silly
    %% guard against multiple calls.
    case persistent_term:get('$smt_loaded', false) of
        true ->
            ok;
        false ->
            ok = z3_nif:load(),
            persistent_term:put('$smt_loaded', true),
            ok
    end.

-spec new() -> term().
new() ->
    new(#{}).

-spec new(_Options) -> term().
new(Options) ->
    Context = z3_nif:new(Options),

    State0 = #smt{ context = Context,
                   fence = 0,
                   counter = 1,
                   expressions = #{},
                   macros = #{},
                   sorts = #{},
                   stack = [] },

    Builtins = [{'Bool', fun z3_nif:boolean_sort/2},
                {'Int', fun z3_nif:integer_sort/2},
                %% FIXME: Use the actual float type later on, this is just a
                %% hack to force sort conflicts.
                {'Float', fun z3_nif:real_sort/2},
                {'String', fun z3_nif:string_sort/2}],

    State = foldl(fun({Name, Fun}, Acc0) ->
                          {SortId, Acc} = sub_sort(Name, Acc0),
                          ok = Fun(Acc#smt.context, SortId),
                          Acc
                  end, State0, Builtins),

    Fence = z3_nif:fence(State#smt.context),
    State#smt{fence=Fence}.

-spec enter_fence(#smt{}) -> #smt{}.
-spec exit_fence(Result, #smt{}) -> {Result, #smt{}}.

-if(?DEBUG).
enter_fence(#smt{context=Context,fence=Fence}=State) ->
    Fence = z3_nif:fence(Context),              %Assertion.
    State.
exit_fence(Result, #smt{context=Context}=State) ->
    {Result, State#smt{fence=z3_nif:fence(Context)}}.
-else.
enter_fence(State) ->
    State.
exit_fence(Result, State) ->
    {Result, State}.
-endif.

-spec expression(_Expr, #smt{}) -> {term(), #smt{}}.
expression(Expr, State0) ->
    {Id, State} = translate(Expr, enter_fence(State0)),
    %% Tag the expression with our context reference so that it cannot be used
    %% by mistake in other contexts.
    case ?DEBUG of
        true -> exit_fence({State#smt.context, Id}, State);
        false -> exit_fence(Id, State)
    end.

-spec declare(term(), #smt{}) -> {ok, #smt{}}.
declare(Exprs, State0) when is_list(Exprs) ->
    State = foldl(fun declare_1/2, enter_fence(State0), Exprs),
    exit_fence(ok, State);
declare(Expr, State0) ->
    exit_fence(ok, declare_1(Expr, enter_fence(State0))).

-spec simplify(_Expr, #smt{}) -> {term(), #smt{}}.
simplify(Expr, State0) ->
    {Id, State1} = translate(Expr, enter_fence(State0)),
    {ExprId, State} = new_id(State1),
    ok = z3_nif:simplify(State#smt.context, ExprId, Id),
    exit_fence(ExprId, State).

-spec assert(_Id, #smt{}) -> {ok, #smt{}}.
assert(Id, State0) when not ?DEBUG, is_integer(Id) ->
    State = enter_fence(State0),
    ok = z3_nif:assert(State#smt.context, Id),
    exit_fence(ok, State);
assert({Ref, Id}, #smt{context=Ref}=State0) when ?DEBUG ->
    State = enter_fence(State0),
    ok = z3_nif:assert(State#smt.context, Id),
    exit_fence(ok, State).

-spec push(#smt{}) -> {ok, #smt{}}.
push(State0) ->
    State1 = enter_fence(State0),

    #smt{counter=Counter,
         expressions=Exprs,
         macros=Macros,
         sorts=Sorts,
         stack=Stack} = State1,
    State = State1#smt{stack=[{Counter, Exprs, Macros, Sorts} | Stack]},

    ok = z3_nif:push(State#smt.context),
    exit_fence(ok, State).

-spec pop(_Frames, #smt{}) -> {ok, #smt{}}.
pop(Frames, State0) ->
    State1 = enter_fence(State0),

    {FromId, Exprs, Macros, Sorts, Stack} = pop_1(Frames, State1#smt.stack),
    State = State1#smt{expressions=Exprs,
                       macros=Macros,
                       sorts=Sorts,
                       stack=Stack},

    ok = z3_nif:pop(State#smt.context, Frames, FromId),
    exit_fence(ok, State).

pop_1(1, [{Counter, Exprs, Macros, Sorts} | Stack]) ->
    {Counter, Exprs, Macros, Sorts, Stack};
pop_1(N, [_ | Stack]) when N > 1 ->
    pop_1(N - 1, Stack).

-spec check(#smt{}) -> {term(), #smt{}}.
check(State) ->
    check(State, []).

-spec check(#smt{}, list()) -> {term(), #smt{}}.
check(State0, Assumptions) ->
    #smt{context=Context} = State = enter_fence(State0),
    As = case ?DEBUG of
             true -> [begin {Context, Id} = A, Id end || A <- Assumptions];
             false -> Assumptions
         end,
    Res = z3_nif:check(Context, As),
    exit_fence(Res, State).

-spec close(#smt{}) -> {term(), #smt{}}.
close(State0) ->
    #smt{context=Context} = State = enter_fence(State0),
    Res = z3_nif:close(Context),
    exit_fence(Res, State#smt{context=closed}).

%%
%%
%%

declare_1({constant, Name, Sort}=Declaration, State0) ->
    {SymbolId, State1} = symbol(Name, State0),
    {SortId, State2} = sort(Sort, State1),
    {create, {FuncId, State}} = sub_expr(Name, State2),
    z3_return(z3_nif:constant(State#smt.context, FuncId, SymbolId, SortId),
              Declaration),
    State;
declare_1({datatype, Name, Constructors}, State) ->
    datatype(Name, Constructors, State);
declare_1({linear_order, Name, Sort, Index}=Declaration, State0) ->
    {SortId, State1} = sort(Sort, State0),
    {create, {FuncId, State}} = sub_expr(Name, State1),
    z3_return(z3_nif:linear_order(State#smt.context, FuncId, SortId, Index),
              Declaration),
    State;
declare_1({literal, Name, Expr}, State0) ->
    {ExprId, #smt{expressions=Exprs}=State} = translate(Expr, State0),
    case Exprs of
        #{ Name := Other } ->
            ExprId = Other,                     %Assertion.
            State;
        #{} ->
            State#smt{expressions=Exprs#{ Name => ExprId }}
    end;
declare_1({macro, Name, Parameters, RangeSort, Expr}, State0) ->
    {_RangeSortId, State} = sort(RangeSort, State0),
    macro(Name, Parameters, Expr, State);
declare_1({interpreted_functions, Funs}, State) ->
    interpreted_functions(Funs, State);
declare_1({uninterpreted_function, Name, Domains, Range}=Declaration, State0) ->
    {SymbolId, State1} = symbol(Name, State0),
    {DomainIds, State2} = mapfoldl(fun sort/2, State1, Domains),
    {RangeId, State3} = sort(Range, State2),
    {create, {FuncId, State}} = sub_expr(Name, State3),
    z3_return(z3_nif:uninterpreted_function(State#smt.context,
                                            FuncId,
                                            SymbolId,
                                            DomainIds,
                                            RangeId),
              Declaration),
    State;
declare_1({uninterpreted_sort, Name}=Declaration, State0) ->
    {SymbolId, State1} = symbol(Name, State0),
    {SortId, State} = sub_sort(Name, State1),
    z3_return(z3_nif:uninterpreted_sort(State#smt.context, SortId, SymbolId),
              Declaration),
    State.

datatype(Name, Constructors, State0) ->
    {SymbolId, State1} = symbol(Name, State0),

    %% Forward-declare our own sort so that it can be used within itself. Note
    %% that this reference cannot be used after the datatype has been created,
    %% and that we'll need to override it later on.
    {FwSortId, State} = sub_sort(Name, State1),
    z3_return(z3_nif:datatype_sort(State#smt.context, FwSortId, SymbolId),
              {Name, Constructors}),

    datatype_1(Constructors, Name, SymbolId, [], State).

datatype_1([{Name, Fields0} | Cs], SortName, SymbolId, CsIds, State0) ->
    {Fields, State1} = mapfoldl(fun({FName, Sort}, Acc0) ->
                                        {FNameId, Acc1} = symbol(FName, Acc0),
                                        {SortId, Acc} = sort(Sort, Acc1),
                                        {{FNameId, SortId}, Acc}
                                end, State0, Fields0),
    {NameId, State2} = symbol(Name, State1),
    {RecognizerId, State3} = symbol(State2),
    {ConstructorId, State4} = new_id(State3),

    z3_return(z3_nif:constructor(State4#smt.context,
                                 ConstructorId,
                                 NameId,
                                 RecognizerId,
                                 Fields),
              SortName),

    %% We have to define all constructors and declare the datatype before we
    %% can assign accessors etc.
    State5 = datatype_1(Cs,
                        SortName,
                        SymbolId,
                        [ConstructorId | CsIds],
                        State4),

    {AccessorIds, State6} = mapfoldl(fun({FieldName, _Sort}, Acc) ->
                                             {create, Res} = sub_expr(FieldName,
                                                                      Acc),
                                             Res
                                     end, State5, Fields0),
    {create, {TesterFuncId, State7}} = sub_expr({is, Name}, State6),
    {create, {ConstructorFuncId, State}} = sub_expr(Name, State7),

    z3_return(z3_nif:query_constructor(State#smt.context,
                                       ConstructorId,
                                       ConstructorFuncId,
                                       TesterFuncId,
                                       AccessorIds),
              SortName),

    State;
datatype_1([], SortName, SymbolId, ConstructorIds, State0) ->
    %% Overwrite the forward reference with the actual sort.
    {SortId, State} = override_sort(SortName, State0),
    z3_return(z3_nif:datatype(State#smt.context,
                              SortId, 
                              SymbolId,
                              ConstructorIds),
              SortName),
    State.

macro(Name, Arguments, Expr, #smt{macros=Macros0}=State) ->
    case Macros0 of
        #{ Name := _ } ->
            error({already_exists, Expr});
        #{} ->
            Macros = Macros0#{ Name => {Arguments, Expr} },
            State#smt{macros=Macros}
    end.

interpreted_functions([{Name, Parameters, Range, Body} | Funs], State0) ->
    #smt{context=Context} = State0,

    {NameId, State1} = symbol(Name, State0),
    {RangeId, State2} = sort(Range, State1),
    {DomainIds, State3} = mapfoldl(fun({_ArgName, Domain}, Acc) ->
                                           sort(Domain, Acc)
                                   end, State2, Parameters),
    {create, {FuncId, State4}} = sub_expr(Name, State3),

    z3_return(z3_nif:declare_interpreted_function(Context,
                                                  FuncId,
                                                  NameId,
                                                  DomainIds,
                                                  RangeId),
              Name),

    %% Ensure that all other functions are declared so that we can refer to
    %% them in the body.
    %%
    %% Note that we stash away the expression map to ensure that nothing in the
    %% body escapes to the outside (including the arguments!).
    #smt{expressions=Expr0} = State5 = interpreted_functions(Funs, State4),

    {ArgIds, State6} =
        mapfoldl(fun({ArgName, Domain}, Acc0) ->
                         Acc = declare_1({constant, ArgName, Domain}, Acc0),
                         translate(ArgName, Acc)
                 end, State5, Parameters),

    {BodyId, State} = translate(Body, State6),
    z3_return(z3_nif:define_interpreted_function(Context,
                                                 FuncId,
                                                 ArgIds,
                                                 BodyId),
              Name),

    State#smt{expressions=Expr0};
interpreted_functions([], State) ->
    State.


%%
%% Sort translation.
%%

sort(Sort, State) ->
    case State#smt.sorts of
        #{ Sort := Id } -> {Id, State};
        #{} -> sort_1(Sort, State)
    end.

sort_1({array, Domains, Range}=Sort, State0) ->
    {DomainIds, State1} = mapfoldl(fun sort/2, State0, Domains),
    {RangeId, State2} = sort(Range, State1),
    {SortId, State} = sub_sort(Sort, State2),
    z3_return(z3_nif:array_sort(State#smt.context, SortId, DomainIds, RangeId),
              Sort),
    {SortId, State};
sort_1({sequence, Basis}=Sort, State0) ->
    {BasisId, State1} = sort(Basis, State0),
    {SortId, State} = sub_sort(Sort, State1),
    z3_return(z3_nif:sequence_sort(State#smt.context, SortId, BasisId),
              Sort),
    {SortId, State}.

sub_sort(Sort, #smt{counter=Counter0,sorts=Sorts0}=State) ->
    case Sorts0 of
        #{ Sort := _ } ->
            error({already_exists, Sort});
        #{} ->
            Sorts = Sorts0#{ Sort => Counter0 },
            Counter = Counter0 + 1,
            {Counter0, State#smt{counter=Counter,sorts=Sorts}}
    end.

override_sort(Sort, #smt{counter=Counter0,sorts=Sorts0}=State) ->
    Sorts = Sorts0#{ Sort := Counter0 },        %Assertion.
    Counter = Counter0 + 1,
    {Counter0, State#smt{counter=Counter,sorts=Sorts}}.

%%
%% Expression translation
%%

translate(Id, State) when not ?DEBUG, is_integer(Id) ->
    {Id, State};
translate({Ref, Id}, #smt{context=Ref}=State) when ?DEBUG ->
    {Id, State};
translate(Expr, State) ->
    case State#smt.expressions of
        #{ Expr := Id } -> {Id, State};
        #{} -> translate_1(Expr, State)
    end.

translate_1({'Bool', Literal}=Expr, State0) ->
    true = is_boolean(Literal),                 %Assertion.
    case sub_expr(Expr, State0) of
        {create, {Id, State}=Res} ->
            z3_return(z3_nif:make_boolean(State#smt.context,
                                          Id,
                                          Literal), Expr),
            Res;
        {exists, Res} ->
            Res
    end;
translate_1({'String', Literal}=Expr, State0) ->
    case sub_expr(Expr, State0) of
        {create, {Id, State}=Res} ->
            z3_return(z3_nif:make_string(State#smt.context, 
                                         Id,
                                         iolist_to_binary(Literal)), Expr),
            Res;
        {exists, Res} ->
            Res
    end;
translate_1({'Int', Literal}=Expr, State0) ->
    true = is_integer(Literal),                 %Assertion.
    {SortId, State1} = sort('Int', State0),
    case sub_expr(Expr, State1) of
        {create, {Id, State}=Res} ->
            case z3_nif:make_integer(State#smt.context, Id, SortId, Literal) of
                conversion_needed ->
                    %% Z3 expects null-termination.
                    Binary = <<(integer_to_binary(Literal, 10))/bits, 0>>,
                    z3_return(z3_nif:make_integer(State#smt.context,
                                                  Id,
                                                  SortId,
                                                  Binary),
                              Expr);
                ok ->
                    ok
            end,
            Res;
        {exists, Res} ->
            Res
    end;
translate_1({'and', [One]}, State) ->
    translate(One, State);
translate_1({'and', _}=Expr, State) ->
    translate_unary_vararg(fun z3_nif:conjugation/3, Expr, State);
translate_1({'or', [One]}, State) ->
    translate(One, State);
translate_1({'or', _}=Expr, State) ->
    translate_unary_vararg(fun z3_nif:disjunction/3, Expr, State);
translate_1({same, [_One]}, State) ->
    translate({'Bool', true}, State);
translate_1({same, _}=Expr, State) ->
    translate_unary_vararg(fun z3_nif:same/3, Expr, State);
translate_1({distinct, [_One]}, State) ->
    translate({'Bool', false}, State);
translate_1({distinct, _}=Expr, State) ->
    translate_unary_vararg(fun z3_nif:distinct/3, Expr, State);
translate_1({one_of, [LHS, RHS]}, State) ->
    translate({'xor', LHS, RHS}, State);
translate_1({one_of, [One]}, State) ->
    translate(One, State);
translate_1({one_of, _}=Expr, State) ->
    translate_unary_vararg(fun z3_nif:one_of/3, Expr, State);
translate_1({'xor', _, _}=Expr, State) ->
    translate_binary(fun z3_nif:exclusive_or/4, Expr, State);
translate_1({iff, _, _}=Expr, State) ->
    translate_binary(fun z3_nif:iff/4, Expr, State);
translate_1({implies, _, _}=Expr, State) ->
    translate_binary(fun z3_nif:implies/4, Expr, State);
translate_1({ite, If, Then, Else}=Expr, State0) ->
    {IfId, State1} = translate(If, State0),
    {ThenId, State2} = translate(Then, State1),
    {ElseId, State3} = translate(Else, State2),
    case sub_expr({ite, IfId, ThenId, ElseId}, State3) of
        {create, {Id, State}=Res} ->
            z3_return(z3_nif:if_then_else(State#smt.context,
                                          Id,
                                          IfId,
                                          ThenId,
                                          ElseId),
                      Expr),
            Res;
        {exists, Res} ->
            Res
    end;
translate_1({'not', SubExpr}=Expr, State0) ->
    {SubExprId, State1} = translate(SubExpr, State0),
    case sub_expr({'not', SubExprId}, State1) of
        {create, {Id, State}=Res} ->
            z3_return(z3_nif:negate(State#smt.context, Id, SubExprId),
                      Expr),
            Res;
        {exists, Res} ->
            Res
    end;
translate_1({match, Value, Matches}, State) ->
    %% FIXME: We need an exhaustiveness check here, lest we create a malformed
    %% expression that has the last pattern as a catch-all clause.
    Expanded = expand_match(Matches, Value),
    translate(Expanded, State);
translate_1({array_select, Array, Indexes}=Expr, State0) ->
    {ArrayId, State1} = translate(Array, State0),
    {IndexIds, State2} = mapfoldl(fun translate/2, State1, Indexes),
    case sub_expr({array_select, ArrayId, IndexIds}, State2) of
        {create, {Id, State}=Res} ->
            z3_return(z3_nif:array_select(State#smt.context,
                                          Id,
                                          ArrayId,
                                          IndexIds),
                      Expr),
            Res;
        {exists, Res} ->
            Res
    end;
translate_1({array_store, Array, Indexes, Value}=Expr, State0) ->
    {ArrayId, State1} = translate(Array, State0),
    {IndexIds, State2} = mapfoldl(fun translate/2, State1, Indexes),
    {ValueId, State3} = translate(Value, State2),
    case sub_expr({array_store, ArrayId, IndexIds, ValueId}, State3) of
        {create, {Id, State}=Res} ->
            z3_return(z3_nif:array_store(State#smt.context,
                                         Id,
                                         ArrayId,
                                         IndexIds,
                                         ValueId),
                      Expr),
            Res;
        {exists, Res} ->
            Res
    end;
translate_1({sequence_concat, Sequences}=Expr, State0) ->
    {SeqIds, State1} = mapfoldl(fun translate/2, State0, Sequences),
    case sub_expr({sequence_concat, SeqIds}, State1) of
        {create, {Id, State}=Res} ->
            z3_return(z3_nif:sequence_concat(State#smt.context, Id, SeqIds),
                      Expr),
            Res;
        {exists, Res} ->
            Res
    end;
translate_1({sequence_unit, Item}=Expr, State0) ->
    {ItemId, State1} = translate(Item, State0),
    case sub_expr({sequence_unit, ItemId}, State1) of
        {create, {Id, State}=Res} ->
            z3_return(z3_nif:sequence_unit(State#smt.context, Id, ItemId),
                      Expr),
            Res;
        {exists, Res} ->
            Res
    end;
translate_1({sequence_empty, Sort}=Expr, State0) ->
    {SortId, State1} = sort({sequence, Sort}, State0),
    case sub_expr({sequence_empty, SortId}, State1) of
        {create, {Id, State}=Res} ->
            z3_return(z3_nif:sequence_empty(State#smt.context, Id, SortId),
                      Expr),
            Res;
        {exists, Res} ->
            Res
    end;
translate_1({sequence_length, Sequence}=Expr, State0) ->
    {SeqId, State1} = translate(Sequence, State0),
    case sub_expr({sequence_length, SeqId}, State1) of
        {create, {Id, State}=Res} ->
            z3_return(z3_nif:sequence_length(State#smt.context, Id, SeqId),
                      Expr),
            Res;
        {exists, Res} ->
            Res
    end;
translate_1({update_field, Accessor, Record, Value}=Expr, State0) ->
    {AccessorId, State1} = translate(Accessor, State0),
    {RecordId, State2} = translate(Record, State1),
    {ValueId, State3} = translate(Value, State2),
    case sub_expr({update_field, AccessorId, RecordId, ValueId}, State3) of
        {create, {Id, State}=Res} ->
            z3_return(z3_nif:update_field(State#smt.context,
                                          Id,
                                          AccessorId,
                                          RecordId,
                                          ValueId),
                      Expr),
            Res;
        {exists, Res} ->
            Res
    end;
translate_1({numeric_addition, _}=Expr, State) ->
    translate_unary_vararg(fun z3_nif:numeric_addition/3, Expr, State);
translate_1({numeric_division, _, _}=Expr, State) ->
    translate_binary(fun z3_nif:numeric_division/4, Expr, State);
translate_1({numeric_modulus, _, _}=Expr, State) ->
    translate_binary(fun z3_nif:numeric_modulus/4, Expr, State);
translate_1({numeric_multiplication, _}=Expr, State) ->
    translate_unary_vararg(fun z3_nif:numeric_multiplication/3, Expr, State);
translate_1({numeric_remainder, _, _}=Expr, State) ->
    translate_binary(fun z3_nif:numeric_remainder/4, Expr, State);
translate_1({numeric_subtraction, _}=Expr, State) ->
    translate_unary_vararg(fun z3_nif:numeric_subtraction/3, Expr, State);
translate_1({numeric_lt, _, _}=Expr, State) ->
    translate_binary(fun z3_nif:numeric_lt/4, Expr, State);
translate_1({numeric_le, _, _}=Expr, State) ->
    translate_binary(fun z3_nif:numeric_le/4, Expr, State);
translate_1({numeric_gt, _, _}=Expr, State) ->
    translate_binary(fun z3_nif:numeric_gt/4, Expr, State);
translate_1({numeric_ge, _, _}=Expr, State) ->
    translate_binary(fun z3_nif:numeric_ge/4, Expr, State);
translate_1({string_lt, _, _}=Expr, State) ->
    translate_binary(fun z3_nif:string_lt/4, Expr, State);
translate_1({string_le, _, _}=Expr, State) ->
    translate_binary(fun z3_nif:string_le/4, Expr, State);
translate_1({Function, Arguments}=Expr, State0) when is_list(Arguments) ->
    case State0#smt.macros of
        #{ Function := Macro } ->
            translate(expand_macro(Macro, Arguments), State0);
        #{} ->
            {ArgIds, State1} = mapfoldl(fun translate/2, State0, Arguments),
            {FuncId, State2} = translate(Function, State1),
            case sub_expr({FuncId, ArgIds}, State2) of
                {create, {Id, State}=Res} ->
                    z3_return(z3_nif:application(State#smt.context,
                                                 Id,
                                                 FuncId,
                                                 ArgIds), Expr),
                    Res;
                {exists, Res} ->
                    Res
            end
    end;
translate_1(Expr, _State) ->
    error({unknown_literal, Expr}).

%% For simplicity, we're expanding macros syntactically rather than using the
%% solver's expression substitution functionality. This is a wee bit slower but
%% much easier to reason about.
expand_macro({Parameters, Expr}, Arguments) ->
    Mapping = maps:from_list(zip(Parameters, Arguments)),
    expand_macro_1(Expr, Mapping).

expand_macro_1(Tuple, Mapping) when is_tuple(Tuple) ->
    expand_macro_tuple(Tuple, tuple_size(Tuple), Mapping);
expand_macro_1(Args, Mapping) when is_list(Args) ->
    [expand_macro_1(Arg, Mapping) || Arg <- Args];
expand_macro_1(Literal, Mapping) ->
    case Mapping of
        #{ Literal := Replacement } -> Replacement;
        #{} -> Literal
    end.

expand_macro_tuple(Tuple, Index, Mapping) when Index >= 1 ->
    Expanded = expand_macro_1(element(Index, Tuple), Mapping),
    expand_macro_tuple(setelement(Index, Tuple, Expanded), Index - 1, Mapping);
expand_macro_tuple(Tuple, 0, _Mapping) ->
    Tuple.

expand_match([{_Constructor, Body}], _Value) ->
    Body;
expand_match([{Constructor, Body} | Matches], Value) ->
    Inner = expand_match(Matches, Value),
    {ite, {{is,Constructor}, [Value]}, Body, Inner}.

translate_unary_vararg(F, {Op, SubExprs0}=Expr, State0) ->
    {SubExprIds, State1} = mapfoldl(fun(SubExpr, Acc) ->
                                            translate(SubExpr, Acc)
                                    end, State0, SubExprs0),
    case sub_expr({Op, SubExprIds}, State1) of
        {create, {Id, State}=Res} ->
            z3_return(F(State#smt.context, Id, SubExprIds), Expr),
            Res;
        {exists, Res} ->
            Res
    end.

translate_binary(F, {Op, LHS, RHS}=Expr, State0) ->
    {LHSId, State1} = translate(LHS, State0),
    {RHSId, State2} = translate(RHS, State1),
    case sub_expr({Op, LHSId, RHSId}, State2) of
        {create, {Id, State}=Res} ->
            z3_return(F(State#smt.context, Id, LHSId, RHSId), Expr),
            Res;
        {exists, Res} ->
            Res
    end.

sub_expr(Expr, #smt{counter=Counter0,expressions=Exprs0}=State) ->
    case Exprs0 of
        #{ Expr := Id } ->
            {exists, {Id, State}};
        #{} ->
            Exprs = Exprs0#{ Expr => Counter0 },
            Counter = Counter0 + 1,
            {create, {Counter0, State#smt{counter=Counter,expressions=Exprs}}}
    end.

symbol(State) ->
    symbol([], State).

symbol(Name, #smt{context=Context,counter=Counter0}=State) ->
    Counter = Counter0 + 1,
    ok = z3_nif:symbol(Context, Counter0, Name),
    {Counter0, State#smt{counter=Counter}}.

new_id(#smt{counter=Counter0}=State) ->
    Counter = Counter0 + 1,
    {Counter0, State#smt{counter=Counter}}.

z3_return(ok, _Expr) -> ok;
z3_return(error, Expr) -> error(Expr).
