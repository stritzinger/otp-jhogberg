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
%% USAGE:
%%
%% $ erlc +cons $FILE_GOES_HERE
%%
%% To print the reachability of basic blocks:
%%    $ erlc +cons_block_results $FILE_GOES_HERE
%%

%%
%% This pass translates our SSA into a form understandable by conventional SMT
%% solvers such as Z3 or CVC5, letting us ask them questions about our code.
%%
%% The point of this exercise is to increase confidence in our compiler,
%% similar in spirit to CompCert and CakeML but taking an altogether different
%% approach. Rather than proving that the code which applies optimizations
%% always does the right thing, we're trying to see whether it's viable to use
%% a constraint solver to prove the safety of individual transformations.
%%
%% The translation is intended to be as close to reality as possible, covering
%% all aspects of the code including control flow and side effects, letting us
%% ask difficult questions like whether reordering the control flow in a given
%% manner will change the semantic meaning of the code; we are not, as with the
%% old value-space pass (beam_ssa_type), limited to merely asking about the
%% possible values of individual variables.
%%
%% For every (SSA) variable, we create an expression that represents its
%% associated operation, describing it in as much detail as we feel like
%% providing. We can provide a total definition if we want the solver to
%% understand it fully, but we're free to provide a partial one (up to the
%% point where anything goes) if there's little point in doing more.
%%
%% For example, it's very useful for the solver to completely understand how
%% tuples work, so we'll define those in full, but we can't say anything about
%% remote function calls as the callee may change entirely between calls due to
%% code upgrades, so they're better left as uninterpreted functions
%% ("undefined," can return anything).
%%
%% Control flow is modeled by having an expression per basic block that returns
%% whether it's reachable, referring to the preceding blocks and whether the
%% condition(s) in which they branch to the current block holds.
%%
%% Side-effects are represented through variables that hold the current state
%% of the universe, with impure operations consuming and/or producing them.
%% This is not particularly fast, but makes it easy to determine whether
%% changes to control flow retain the meaning of the original code (or at the
%% very least express it).
%%
%% More details and background can be found in the paper "Modeling Erlang
%% Compiler IR as SMT Formulas" presented at ICFP '24 Erlang Workshop.
%% https://doi.org/10.1145/3677995.3678193
%%

-module(beam_ssa_constraints).
-export([module/2]).

-include("beam_ssa.hrl").

-import(lists, [all/2, foldl/3, mapfoldl/3, usort/1]).

-define(IF(__Cond__, __True__, __False__),
        case __Cond__ of
            true -> __True__;
            false -> __False__
        end).

-record(st, { smt,
              vars = #{} :: #{ Var :: #b_var{} => {Sort :: atom(),
                                                   Expr :: term()} },
              opaques = #{} :: #{ Value :: term() => Expr :: term() },
              functions = sets:new([{version,2}]) :: sets:set()
            }).

declarations() ->
    [%% Terms are represented as a nested recursive datatype, with the parts we
     %% don't care about hidden within an Opaque field for better performance.
     {uninterpreted_sort, 'Opaque'},
     {datatype, 'Term',
      [{integer_term, [{integer_value, 'Int'}]},
       {float_term, [{float_value, 'Float'}]},
       {atom_term, [{atom_value, 'String'}]},
       {reference_term, [{reference_value, 'Opaque'}]},
       {lambda_term, [{lambda_module, 'String'},
                      {lambda_function, 'String'},
                      {lambda_arity, 'Int'},
                      {lambda_free, 'Int'},
                      {lambda_elements, {array, ['Int'], 'Term'}}]},
       {pid_term, [{pid_value, 'Opaque'}]},
       {port_term, [{port_value, 'Opaque'}]},
       {tuple_term, [{tuple_arity, 'Int'},
                     {tuple_elements, {array, ['Int'], 'Term'}}]},
       {map_term, [{map_size, 'Int'},
                   {map_opaque, 'Opaque'}]},
       {nil_term, []},
       {cons_term, [{head_value, 'Term'},
                    {tail_value, 'Term'}]},

       %% For some inexplicable reason, performance nosedives when we represent
       %% a bitstring as an array of its bits (even when bitstrings are
       %% completely absent). As we have very little interest in understanding
       %% the contents of bitstrings at the moment, we'll simply declare them
       %% opaque for now.
       %%
       %% (Ideally I'd like to have a bit-vector of the same size as the
       %% bitstring, but that's not possible at the moment.)
       {bitstring_term, [{bitstring_size,'Int'},
                         {bitstring_opaque, 'Opaque'}]}
      ]},

     %% Unit array for lambda and tuple elements. Explicitly created terms
     %% (e.g. put_tuple) MUST define every one of their elements.
     {constant, term_array_unit, {array, ['Int'], 'Term'}},

     %% Helper function for filling in the opaque fields of literals, following
     %% the literal index.
     {uninterpreted_function, opaque, ['Int'], 'Opaque'},

     %% Free variables for function arguments.
     {uninterpreted_function, argument, ['Int'], 'Term'},

     %% We model side-effects by using explicit variables representing the
     %% current state of the universe. Every impure operation reads from the
     %% universe, and every side-effecting operation returns a new universe
     %% based on the old one.
     %%
     %% This is not particularly fast in long functions, but makes it easier to
     %% reason about side effects.
     {uninterpreted_sort, 'Universe'},
     {constant, genesis, 'Universe'},
     {uninterpreted_function, tick, ['Universe'], 'Universe'},

     {datatype, 'Pure',
      [{defined, [{value, 'Term'}]},
       {undefined, []}]},

     {datatype, 'Impure',
      [{return, [{result, 'Term'}, {universe, 'Universe'}]},
       {raise, [{exception, 'Universe'}]}]},

     %%
     %% This marks the end of the data types, what follows are definitions of
     %% all the operations we currently care about.
     %%
     %% Operations that aren't defined below are declared on the fly to keep
     %% things simple.
     %%
     %% --

     %%
     %% Term ordering.
     %%
     %% We're currently basing this entirely on the Z3 linear-order extension
     %% for convenience, other solvers will have to settle for using an
     %% uninterpreted function w/ quantifiers for now.
     %%
     {linear_order, term_compare_le, 'Term', 0},

     {macro, term_order, [term], 'Int',
      {match, term,
       [{integer_term, {'Int', 0}},
        {float_term, {'Int', 0}},
        {atom_term, {'Int', 1}},
        {reference_term, {'Int', 2}},
        {lambda_term, {'Int', 3}},
        {port_term, {'Int', 4}},
        {pid_term, {'Int', 5}},
        {tuple_term, {'Int', 6}},
        {map_term, {'Int', 7}},
        {nil_term, {'Int', 8}},
        {cons_term, {'Int', 9}},
        {bitstring_term, {'Int', 10}}]}},

     %% Our term order is linear but does not distinguish between integers and
     %% floats, comparing them as if they have been losslessly converted to
     %% some other kind of number with infinite precision. Thus, the float
     %% `1.0` and the integer `1` order equal despite being distinct terms, and
     %% the same applies to nested terms where `{1.0}` compares greater than
     %% `{0}`.
     %%
     %% This prevents us from using a linear order function directly, as we'd
     %% imply sameness where there is none. Instead, we pass all terms through
     %% a coercion function that represents this aspect of our comparison
     %% rules.
     {uninterpreted_function, term_compare_coerce_u, ['Term'], 'Term'},
     {macro, term_compare_coerce, [term], 'Bool',
      {ite, {'or', [{{is,integer_term}, [term]},
                    {{is,float_term}, [term]},
                    {{is,lambda_term}, [term]},
                    {{is,tuple_term}, [term]},
                    {{is,map_term}, [term]},
                    {{is,cons_term}, [term]}]},
       {term_compare_coerce_u, [term]},
       term}},

     {macro, {bif, 'Bool', '=<'}, [lhs, rhs], 'Bool',
      {term_compare_le, [{term_compare_coerce, [lhs]},
                         {term_compare_coerce, [rhs]}]}},
     {macro, {bif, 'Bool', '<'}, [lhs, rhs], 'Bool',
      {'and', [{{bif, 'Bool', '=<'}, [lhs, rhs]},
               {'not', {{bif, 'Bool', '=<'}, [rhs, lhs]}}]}},
     {macro, {bif, 'Bool', '>'}, [lhs, rhs], 'Bool',
      {'not', {{bif, 'Bool', '=<'}, [lhs, rhs]}}},
     {macro, {bif, 'Bool', '>='}, [lhs, rhs], 'Bool',
      {'not', {{bif, 'Bool', '<'}, [lhs, rhs]}}},
     {macro, {bif, 'Bool', '=='}, [lhs, rhs], 'Bool',
      {'and', [{{bif, 'Bool', '=<'}, [lhs, rhs]},
               {{bif, 'Bool', '=<'}, [rhs, lhs]}]}},
     {macro, {bif, 'Bool', '/='}, [lhs, rhs], 'Bool',
      {'not', {{bif, 'Bool', '=='}, [lhs, rhs]}}},
     {macro, {bif, 'Bool', '=:='}, [lhs, rhs], 'Bool',
      {same, [lhs, rhs]}},
     {macro, {bif, 'Bool', '=/='}, [lhs, rhs], 'Bool',
      {distinct, [lhs, rhs]}},

     %%
     %% Boolean operations
     %%
     {literal, atom_true, {atom_term, [{'String', <<"true">>}]}},
     {literal, atom_false, {atom_term, [{'String', <<"false">>}]}},

     {macro, {bif, 'Bool', 'and'}, [lhs, rhs], 'Bool',
      {'and', [lhs, rhs]}},

     {macro, {bif, 'Pure', 'and'}, [lhs, rhs], 'Pure',
      {ite, {'and', [{'or', [{same, [lhs, atom_true]},
                             {same, [lhs, atom_false]}]},
                     {'or', [{same, [rhs, atom_true]},
                             {same, [rhs, atom_false]}]}]},
       {defined, [{ite, {same, [lhs, rhs]}, lhs, atom_false}]},
       {undefined, []}}},

     {macro, {bif, 'Bool', 'or'}, [lhs, rhs], 'Bool',
      {'or', [lhs, rhs]}},

     {macro, {bif, 'Pure', 'or'}, [lhs, rhs], 'Pure',
      {ite, {'and', [{'or', [{same, [lhs, atom_true]},
                             {same, [lhs, atom_false]}]},
                     {'or', [{same, [rhs, atom_true]},
                             {same, [rhs, atom_false]}]}]},
       {defined, [{ite, {'or', [{same, [lhs, atom_true]},
                                {same, [rhs, atom_true]}]},
                   atom_true, atom_false}]},
       {undefined, []}}},

     {macro, {bif, 'Bool', 'xor'}, [lhs, rhs], 'Bool',
      {'xor', lhs, rhs}},

     {macro, {bif, 'Pure', 'xor'}, [lhs, rhs], 'Pure',
      {ite, {'and', [{'or',[{same, [lhs, atom_true]},
                            {same, [lhs, atom_false]}]},
                     {'or',[{same, [rhs, atom_true]},
                            {same, [rhs, atom_false]}]}]},
       {defined, [{ite, {distinct, [lhs, rhs]},
                   atom_true, atom_false}]},
       {undefined, []}}},

     {macro, {bif, 'Bool', 'not'}, [term], 'Bool',
      {'not', term}},

     {macro, {bif, 'Pure', 'not'}, [term], 'Pure',
      {ite, {'or', [{same, [term, atom_true]}, {same, [term, atom_false]}]},
       {defined, [{ite, {same, [term, atom_true]}, atom_false, atom_true}]},
       {undefined, []}}},

     %%
     %% Type tests
     %%
     {macro, {bif, 'Bool', is_atom}, [term], 'Bool',
      {{is,atom_term}, [term]}},

     {macro, {bif, 'Bool', is_boolean}, [term], 'Bool',
      {'or', [{same, [term, atom_true]},
              {same, [term, atom_false]}]}},

     {macro, {bif, 'Bool', is_bitstring}, [term], 'Bool',
      {{is,bitstring_term}, [term]}},

     {macro, {bif, 'Bool', is_binary}, [term], 'Bool',
      {'and',
       [{{is,bitstring_term}, [term]},
        {same, [{'Int', 0},
                {numeric_modulus,
                 {bitstring_size, [term]},
                 {'Int', 8}}]}]}},

     {macro, {bif, 'Bool', is_tuple}, [term], 'Bool',
      {{is,tuple_term}, [term]}},

     {macro, {bif, 'Bool', is_map}, [term], 'Bool',
      {{is,map_term}, [term]}},

     {macro, {bif, 'Bool', is_integer}, [term], 'Bool',
      {{is,integer_term}, [term]}},

     {macro, {bif, 'Bool', is_function}, [term], 'Bool',
      {{is,lambda_term}, [term]}},

     {macro, {bif, 'Pure', is_function_arity}, [term, arity], 'Pure',
      {ite, {'and', [{{is,integer_term}, [arity]},
                     {numeric_ge, {integer_value, [arity]}, {'Int', 0}}]},
       {defined,
        [{ite,
          {'and', [{{is,lambda_term}, [term]},
                   {same, [{lambda_arity, [term]},
                           {integer_value, [arity]}]}]},
          atom_true,
          atom_false}]},
       {undefined, []}}},

     {macro, {bif, 'Bool', is_float}, [term], 'Bool',
      {{is,float_term}, [term]}},

     {macro, {bif, 'Bool', is_list}, [term], 'Bool',
      {'or',[{{is,cons_term}, [term]},
             {{is,nil_term}, [term]}]}},

     {macro, {bif, 'Bool', is_number}, [term], 'Bool',
      {'or',[{{is,integer_term}, [term]},
             {{is,float_term}, [term]}]}},

     {macro, {bif, 'Bool', is_pid}, [term], 'Bool',
      {{is,pid_term}, [term]}},

     {macro, {bif, 'Bool', is_port}, [term], 'Bool',
      {{is,port_term}, [term]}},

     {macro, {bif, 'Bool', is_reference}, [term], 'Bool',
      {{is,reference_term}, [term]}},

     %%
     %% List operations
     %%
     {macro, {bif, 'Pure', hd}, [term], 'Pure',
      {ite, {{is,cons_term}, [term]},
       {defined, [{head_value, [term]}]},
       {undefined, []}}},

     {macro, {bif, 'Pure', tl}, [term], 'Pure',
      {ite, {{is,cons_term}, [term]},
       {defined, [{tail_value, [term]}]},
       {undefined, []}}},

     {uninterpreted_function, {bif, length_u}, ['Term'], 'Int'},
     {macro, {bif, 'Pure', length}, [term], 'Pure',
      {ite, {{bif, 'Bool', is_list}, [term]},
       {defined, [{integer_term, [{{bif, length_u}, [term]}]}]},
       {undefined, []}}},

     %%
     %% Tuple operations
     %%
     {macro, tuple_element, [tuple, index], 'Term',
      {array_select, {tuple_elements, [tuple]}, [index]}},

     {macro, {bif, 'Pure', tuple_size}, [tuple], 'Pure',
      {ite, {{is,tuple_term}, [tuple]},
       {defined, [{integer_term, [{tuple_arity, [tuple]}]}]},
       {undefined, []}}},

     {macro, {bif, 'Pure', element}, [index, tuple], 'Pure',
      {ite, {'and',[{{is,integer_term}, [index]},
                    {{is,tuple_term}, [tuple]},
                    {numeric_le,
                     {integer_value, [index]},
                     {tuple_arity, [tuple]}},
                    {numeric_ge,
                     {integer_value, [index]},
                     {'Int', 1}}]},
       {defined, [{tuple_element, [tuple, {integer_value, [index]}]}]},
       {undefined, []}}},

     {macro, {erlang, setelement, 3}, [index, tuple, value], 'Pure',
      {ite, {'and',[{{is,integer_term}, [index]},
                    {{is,tuple_term}, [tuple]},
                    {numeric_le,
                     {integer_value, [index]},
                     {tuple_arity, [tuple]}},
                    {numeric_ge,
                     {integer_value, [index]},
                     {'Int', 1}}]},
       {defined,
        [{update_field,
          tuple_elements,
          tuple,
          {array_store,
           {tuple_elements, [tuple]},
           [{integer_value, [index]}],
           value}}]},
       {undefined, []}}},

     %%
     %% Map operations
     %%
     {uninterpreted_function, has_map_element, ['Term', 'Term'], 'Bool'},
     {uninterpreted_function, map_element, ['Term', 'Term'], 'Term'},

     {macro, {bif, 'Pure', 'map_get'}, [key, map], 'Pure',
      {ite, {'and', [{{is,map_term}, [map]}, {has_map_element, [key, map]}]},
       {defined, [{map_element, [key, map]}]},
       {undefined, []}}},

     {macro, {bif, 'Pure', 'is_map_key'}, [key, map], 'Pure',
      {ite, {{is,map_term}, [map]},
       {defined, [{ite, {has_map_element, [key, map]}, atom_true, atom_false}]},
       {undefined, []}}},

     {macro, {bif, 'Pure', 'map_size'}, [map], 'Pure',
      {ite, {{is,map_term}, [map]},
       {defined, [{integer_term, [{map_size, [map]}]}]},
       {undefined, []}}},

     {uninterpreted_function, put_map_exact,
      ['Term', {sequence, 'Term'}], 'Pure'},
     {uninterpreted_function, put_map_assoc,
      ['Term', {sequence, 'Term'}], 'Term'},

     %%
     %% Bitstring operations, the ones not listed here are stubbed on the fly.
     %%
     {uninterpreted_function, bs_create_bin, [{sequence, 'Term'}], 'Pure'},
     {uninterpreted_function, bs_match, [{sequence, 'Term'}], 'Pure'},

     %%
     %% Float operations. These are just stubbed so we can sanity-check solver
     %% performance on already-optimized code.
     %%

     {uninterpreted_function, {float, convert}, ['Term'], 'Pure'},
     {uninterpreted_function, {float, put}, ['Term'], 'Term'},
     {uninterpreted_function, {float, get}, ['Term'], 'Term'},
     {uninterpreted_function, {float, negate}, ['Term'], 'Term'},
     {uninterpreted_function, {float, '-'}, ['Term', 'Term'], 'Pure'},
     {uninterpreted_function, {float, '+'}, ['Term', 'Term'], 'Pure'},
     {uninterpreted_function, {float, '/'}, ['Term', 'Term'], 'Pure'},
     {uninterpreted_function, {float, '*'}, ['Term', 'Term'], 'Pure'},

     %%
     %% Misc other operations that we want to be able to reason about.
     %%
     {macro, {bif, 'Term', max}, [lhs, rhs], 'Term',
      {ite, {{bif, 'Bool', '>='}, [lhs, rhs]}, lhs, rhs}},

     {macro, {bif, 'Term', min}, [lhs, rhs], 'Term',
      {ite, {{bif, 'Bool', '=<'}, [lhs, rhs]}, lhs, rhs}},

     {uninterpreted_function, {bif, 'Term', self}, [], 'Term'},
     {uninterpreted_function, {bif, 'Term', node}, [], 'Term'},

     %% Stubs for pure BIFs that we don't wish to define yet. We skip stubbing
     %% pure BIFs on the fly to avoid collisions with the ones we've defined
     %% (we don't yet support asking the SMT context whether a function is
     %% defined or not), so all of them must be listed here.
     {uninterpreted_function, {bif, 'Pure', 'float'}, ['Term'], 'Pure'},
     {uninterpreted_function, {bif, 'Pure', '+'}, ['Term', 'Term'], 'Pure'},
     {uninterpreted_function, {bif, 'Pure', '-'}, ['Term', 'Term'], 'Pure'},
     {uninterpreted_function, {bif, 'Pure', negate}, ['Term'], 'Pure'},
     {uninterpreted_function, {bif, 'Pure', '*'}, ['Term', 'Term'], 'Pure'},
     {uninterpreted_function, {bif, 'Pure', '/'}, ['Term', 'Term'], 'Pure'},
     {uninterpreted_function, {bif, 'Pure', 'div'}, ['Term', 'Term'], 'Pure'},
     {uninterpreted_function, {bif, 'Pure', 'rem'}, ['Term', 'Term'], 'Pure'},
     {uninterpreted_function, {bif, 'Pure', 'abs'}, ['Term'], 'Pure'},
     {uninterpreted_function, {bif, 'Pure', 'band'}, ['Term', 'Term'], 'Pure'},
     {uninterpreted_function, {bif, 'Pure', 'bor'}, ['Term', 'Term'], 'Pure'},
     {uninterpreted_function, {bif, 'Pure', 'bxor'}, ['Term', 'Term'], 'Pure'},
     {uninterpreted_function, {bif, 'Pure', 'bsl'}, ['Term', 'Term'], 'Pure'},
     {uninterpreted_function, {bif, 'Pure', 'bsr'}, ['Term', 'Term'], 'Pure'},
     {uninterpreted_function, {bif, 'Pure', 'bnot'}, ['Term'], 'Pure'},
     {uninterpreted_function, {bif, 'Pure', 'bit_size'}, ['Term'], 'Pure'},
     {uninterpreted_function, {bif, 'Pure', 'byte_size'}, ['Term'], 'Pure'},
     {uninterpreted_function, {bif, 'Pure', 'ceil'}, ['Term'], 'Pure'},
     {uninterpreted_function, {bif, 'Pure', 'floor'}, ['Term'], 'Pure'},
     {uninterpreted_function, {bif, 'Pure', 'round'}, ['Term'], 'Pure'},
     {uninterpreted_function, {bif, 'Pure', 'trunc'}, ['Term'], 'Pure'}
    ].

-spec module(Module, Options) -> Result when
      Module :: beam_ssa:b_module(),
      Options :: [compile:option()],
      Result :: {ok, beam_ssa:b_module(), list()}.

module(#b_module{body=Fs0,name=Name}=Module, Opts0) ->
    Opts = proplists:expand([{cons_block_results,
                              [cons, cons_debug, cons_block_results]},
                             {cons_debug,
                              [cons, cons_debug]}],
                            Opts0),

    case proplists:get_bool(cons, Opts) of
        true ->
            smt:load(),

            io:format("... compiling ~p\n", [Name]),
            {WithSetup, WithoutSetup} =
                timer:tc(fun() ->
                                 lists:sum([function(F, Opts) || F <- Fs0])
                         end),
            io:format("\twhole module took ~p us (~p with setup)\n",
                    [WithoutSetup, WithSetup]);
        false ->
            ok
    end,

    {ok, Module, []}.

function(#b_function{anno=Anno,args=Args,bs=Blocks}, Opts) ->
    #{ func_info := MFA } = Anno,

    ?IF(proplists:get_bool(cons_debug, Opts),
        io:format("Starting ~p\n", [MFA]),
        ok),
    {Total, Internal} =
        timer:tc(fun() ->
                         RPO = beam_ssa:rpo(Blocks) -- [?EXCEPTION_BLOCK],
                         Order = beam_ssa:number(RPO),

                         Options =
                             ?IF(proplists:get_bool(cons_log, Opts),
                                 begin
                                     {M, F, A} = MFA,
                                     LogFile = io_lib:format("~w@~w@~w.smt",
                                                             [M, F, A]),
                                     #{ log_file => LogFile }
                                 end,
                                 #{}),

                         St0 = init_state(Options, Args),
                         {#st{smt=Ctx}, BlkExprs} = bs(RPO, Blocks, Order, St0),

                         smoke_test(RPO, Opts, Blocks,
                                    BlkExprs, Ctx, 0)
                 end),
    ?IF(proplists:get_bool(cons_debug, Opts),
        io:format("\t~p done in ~p us (~.2f% setup overhead)\n",
                  [MFA, Internal, (Total / Internal * 100) - 100]),
        ok),

    Internal.

smoke_test([Target | Lbls], Opts, Blocks, BlkExprs, Ctx0, Elapsed) ->
    #{Target := Expr } = BlkExprs,
    {CheckId, Ctx1} = smt:simplify(Expr, Ctx0),

    ?IF(proplists:get_bool(cons_block_results, Opts),
        io:format("\t~p is ... ", [Target]), ok),
    {Time, {_Res, Ctx}} = timer:tc(fun() -> smt:check(Ctx1, [CheckId]) end),
    ?IF(Time > 100000 andalso proplists:get_bool(cons_debug, Opts),
        io:format("\t~p was slow, took ~p us, ~p\n", [Target, Time, _Res]),
        ?IF(proplists:get_bool(cons_block_results, Opts),
            io:format("~p (~p us)\n", [_Res, Time]), ok)),

    smoke_test(Lbls, Opts, Blocks, BlkExprs, Ctx, Elapsed + Time);
smoke_test([], _Opts, _Blocks, _BlkExprs, Ctx, Elapsed) ->
    _ = smt:close(Ctx),
    Elapsed.

init_state(Options, Args) ->
    {ok, Ctx} = smt:declare(declarations(), smt:new(Options)),
    foldl(fun(Arg, St0) ->
                  Expr = {argument, [{'Int', Arg#b_var.name}]},
                  {_, St} = define(Arg, 'Term', Expr, St0),
                  St
          end, #st{smt=Ctx}, Args).

bs([0=Lbl | Lbls], Blocks, Order, St0) ->
    #{ Lbl := #b_blk{is=Is,last=Last} } = Blocks,

    {Universe, St1} = define({universe, Lbl}, 'Universe', genesis, St0),

    {Implications, St2} = is(Is, Lbl, Universe, #{}, St1, []),
    {Flow, St3} = terminator(Last, Lbl, St2, #{}),

    {Expr, St} = simplify({'and', [{'Bool', true} | Implications]}, St3),

    bs_1(Lbls, Blocks, Order, Flow, St, #{ Lbl => Expr }).

bs_1([?EXCEPTION_BLOCK | Lbls], Blocks, Order, Flow, St, BlkExprs) ->
    bs_1(Lbls, Blocks, Order, Flow, St, BlkExprs);
bs_1([Lbl | Lbls], Blocks, Order, Flow0, St0, BlkExprs) ->
    #{ Lbl := #b_blk{is=Is,last=Last} } = Blocks,

    {Preds, PreCs} = preconditions(Lbl, Flow0, BlkExprs),

    {Universe, St1} = universe(Preds, Lbl, BlkExprs, St0),

    {Implications, St2} = is(Is, Lbl, Universe, BlkExprs, St1, []),
    {Flow, St3} = terminator(Last, Lbl, St2, Flow0),

    {Expr, St} = simplify({'and', [{one_of, PreCs} | Implications]}, St3),

    bs_1(Lbls, Blocks, Order, Flow, St, BlkExprs#{ Lbl => Expr });
bs_1([], _Blocks, _Order, _Flow, St, BlkExprs) ->
    {St, BlkExprs}.

define(Label, Sort, Expr0, #st{smt=Ctx0,vars=Vars}=St) ->
    {Expr, Ctx} = smt:expression(Expr0, Ctx0),
    {Expr, St#st{smt=Ctx,vars=Vars#{ Label => {Sort, Expr} }}}.

expression(Expr0, #st{smt=Ctx0}=St) ->
    {Expr, Ctx} = smt:expression(Expr0, Ctx0),
    {Expr, St#st{smt=Ctx}}.

simplify(Expr0, #st{smt=Ctx0}=St) ->
    {Expr, Ctx} = smt:simplify(Expr0, Ctx0),
    {Expr, St#st{smt=Ctx}}.

universe(Preds, Lbl, BlkExprs, St) ->
    Phi = universe_1(Preds, BlkExprs, St),
    define({universe, Lbl}, 'Universe', Phi, St).

universe_1([Pred], _BlkExprs, St) ->
    #{ {universe, Pred} := {'Universe', Expr} } = St#st.vars,
    Expr;
universe_1([Pred | Preds], BlkExprs, St) ->
    #{ {universe, Pred} := {'Universe', Expr} } = St#st.vars,
    Inner = universe_1(Preds, BlkExprs, St),
    #{ Pred := Cond } = BlkExprs,
    {ite, Cond, Expr, Inner}.

preconditions(Lbl, Flow, BlkExprs) ->
    #{ Lbl := Branches } = Flow,
    maps:fold(fun(From, unconditional, {Preds, Acc0}) ->
                      #{ From := Expr } = BlkExprs,
                      {[From | Preds], [Expr | Acc0]};
                 (From, Conditions, {Preds, Acc}) ->
                      #{ From := Expr } = BlkExprs,
                      Cond = {'and', [Expr, {one_of, Conditions}]},
                      {[From | Preds], [Cond | Acc]}
              end, {[], []}, Branches).

terminator(#b_br{bool=#b_var{}=Bool0,succ=Succ,fail=Fail},
           Lbl, St, Flow0) ->
    case St#st.vars of
        #{ Bool0 := {'Bool', {'Bool', True}} } ->
            true = True,                        %Assertion.
            {branch_cs(Lbl, Succ, Flow0), St};
        #{ Bool0 := {'Bool', Expr} } ->
            Flow = branch_cs(Lbl, Succ, Expr, Flow0),
            {branch_cs(Lbl, Fail, {'not', Expr}, Flow), St};
        #{} ->
            %% We're branching on a term that's statically known to be a
            %% boolean atom. This is fairly rare but we need to handle it.
            {True, St} = literal_expr(true, St), %Assertion.
            {Bool, St} = term_expr(Bool0, St), %Assertion.
            Expr = {same, [Bool, True]},
            Flow = branch_cs(Lbl, Succ, Expr, Flow0),
            {branch_cs(Lbl, Fail, {'not', Expr}, Flow), St}
    end;
terminator(#b_br{bool=#b_literal{},succ=Succ}, Lbl, St, Flow0) ->
    {branch_cs(Lbl, Succ, Flow0), St};
terminator(#b_switch{arg=#b_var{}=Arg,fail=Fail,list=List},
           Lbl, St0, Flow0) ->
    {[_|_]=Values, Targets} = switch_group(List, [], []), %Assertion.
    {Test, Extracted, Marshal, St} = switch_exprs(Values, Arg, St0),

    Flow = foldl(fun({To, Vs}, Acc) ->
                         switch_target(Lbl, To, Vs, Test, Extracted,
                                       Marshal, Acc)
                 end, Flow0, Targets),

    {switch_fallback(Lbl, Fail, Values, Test, Extracted, Marshal, Flow), St};
terminator(#b_ret{}, _Lbl, St, Flow) ->
    {Flow, St}.

%% Group the values on a per-target basis so we won't create multiple branch
%% conditions per target if multiple values switch to the same target.
switch_group([{#b_literal{val=Value}, To} | List], Values, Branches) ->
    switch_group(List, [Value | Values], [{To, Value} | Branches]);
switch_group([], Values, Branches) ->
    {Values, sofs:to_external(sofs:rel2fam(sofs:relation(Branches)))}.

switch_exprs([Head | _], Arg, St0) ->
    {Expr, St0} = term_expr(Arg, St0),        %Assertion.
    {Constructor, Extract, Marshal} =
        if
            is_atom(Head) ->
                {atom_term, atom_value,
                 fun(V) -> {'String', atom_to_binary(V)} end};
            is_integer(Head) ->
                {integer_term, integer_value,
                 fun(V) -> {'Int', V} end};
            is_float(Head) ->
                {float_term, float_value,
                 fun(V) -> {'Float', V} end}
        end,
    {Test, St1} = expression({{is,Constructor}, [Expr]}, St0),
    {Extracted, St} = expression({Extract, [Expr]}, St1),
    {Test, Extracted, Marshal, St}.

switch_target(Lbl, To, Values, Test, Extracted, Marshal, Flow) ->
    {Ranges, Singletons} = switch_compact_1(Values, Extracted, Marshal),
    SingletonEqs = [{same, [Extracted, Value]} || Value <- Singletons],
    branch_cs(Lbl, To, {'and', [Test, {one_of, Ranges ++ SingletonEqs}]}, Flow).

switch_fallback(Lbl, To, Values, Test, Extracted, Marshal, Flow) ->
    {Ranges, Singletons} = switch_compact_1(Values, Extracted, Marshal),
    NotSingleton = {'distinct', [Extracted | Singletons]},
    Expr = case Ranges of
               [_|_] -> {'and', [NotSingleton, {'not', {'or', Ranges}}]};
               [] -> NotSingleton
           end,
    branch_cs(Lbl, To, {'or', [{'not', Test}, Expr]}, Flow).

switch_compact_1([Head | _]=Values, Extracted, Marshal) when is_integer(Head) ->
    %% It's very common for switches over integers to have continuous ranges
    %% here and there, try to coalesce them if possible.
    [First | Rest] = usort(Values),

    {Ranges0, Singletons0} =
        switch_compact_integers(Rest, First, First, [], []),

    Ranges = [{'and', [{numeric_ge, Extracted, Marshal(Start)},
                       {numeric_le, Extracted, Marshal(End)}]}
              || {Start, End} <- Ranges0],
    Singletons = [Marshal(Singleton) || Singleton <- Singletons0],

    {Ranges, Singletons};
switch_compact_1(All, _Extracted, Marshal) ->
    {[], [Marshal(Value) || Value <- All]}.

switch_compact_integers([Value | Values], Start, End, Ranges, Singletons) ->
    case Value =:= (End + 1) of
        true ->
            switch_compact_integers(Values, Start, Value, Ranges, Singletons);
        false when Start =:= End ->
            switch_compact_integers(Values, Value, Value,
                                    Ranges, [Start | Singletons]);
        false ->
            switch_compact_integers(Values, Value, Value,
                                    [{Start, End} | Ranges], Singletons)
    end;
switch_compact_integers([], Same, Same, Ranges, Singletons) ->
    {Ranges, [Same | Singletons]};
switch_compact_integers([], Start, End, Ranges, Singletons) ->
    {[{Start, End} | Ranges], Singletons}.

branch_cs(_From, ?EXCEPTION_BLOCK, _Cond, Flow) ->
    Flow;
branch_cs(From, To, Cond, Flow) ->
    case Flow of
        #{ To := PreCs0 } ->
            PreCs = case PreCs0 of
                        #{ From := Conds } -> PreCs0#{ From => [Cond | Conds] };
                        #{} -> PreCs0#{ From => [Cond] }
                    end,
            Flow#{ To := PreCs };
        #{} ->
            Flow#{ To => #{ From => [Cond] }}
    end.

branch_cs(_From, ?EXCEPTION_BLOCK, Flow) ->
    Flow;
branch_cs(From, To, Flow) ->
    case Flow of
        #{ To := PreCs0 } ->
            PreCs = case PreCs0 of
                        #{ From := _ } -> error({invalid_branch, From, To});
                        #{} -> PreCs0#{ From => unconditional }
                    end,
            Flow#{ To := PreCs };
        #{} ->
            Flow#{ To => #{ From => unconditional }}
    end.

is([#b_set{op=phi,dst=Dst,args=Args} | Is],
   Lbl, Universe, BlkExprs, St0, Imps) ->
    {Sort, Expr, St1} = phi(Args, BlkExprs, St0),
    {_, St} = define(Dst, Sort, Expr, St1),
    is(Is, Lbl, Universe, BlkExprs, St, Imps);
is([#b_set{op=Op,dst=Dst,args=Args},
    #b_set{op={succeeded,_},dst=SuccDst,args=[Dst]}],
   Lbl, Universe, BlkExprs, St0, Imps0) ->
    {Sort, Expr0, Imps1, St1} = instruction(Op, Universe, Args, St0),
    true = all(fun({implies, _, _}) -> true end, Imps1), %Assertion.

    {Expr, St2} = define(Dst, Sort, Expr0, St1),
    {Imps, St} = mapfoldl(fun expression/2, St2, Imps1),
    is_1(Sort, Expr, {checked, SuccDst}, [], Lbl, Universe, BlkExprs, St,
         Imps ++ Imps0);
is([#b_set{op=Op,dst=Dst,args=Args} | Is],
   Lbl, Universe, BlkExprs, St0, Imps0) ->
    {Sort, Expr0, Imps1, St1} = instruction(Op, Universe, Args, St0),
    true = all(fun({implies, _, _}) -> true end, Imps1), %Assertion.

    {Expr, St2} = define(Dst, Sort, Expr0, St1),
    {Imps, St} = mapfoldl(fun expression/2, St2, Imps1),
    is_1(Sort, Expr, unchecked, Is, Lbl, Universe, BlkExprs, St,
         Imps ++ Imps0);
is([], _Lbl, _Universe, _BlkExprs, St, Imps) ->
    {Imps, St}.

is_1('Impure', Expr, Spec, Is, Lbl, _Universe0, BlkExprs, St0, Imps) ->
    {Universe, St1} = define({universe, Lbl},
                             'Universe',
                             {universe, [Expr]},
                             St0),
    case Spec of
        {checked, SuccDst} ->
            {_, St} = define(SuccDst, 'Bool', {{is,return}, [Expr]},St1),
            is(Is, Lbl, Universe, BlkExprs, St, Imps);
        unchecked ->
            {Succeeded, St} = expression({{is,return}, [Expr]}, St1),
            is(Is, Lbl, Universe, BlkExprs, St, [Succeeded | Imps])
    end;
is_1('Pure', Expr, Spec, Is, Lbl, Universe, BlkExprs, St0, Imps) ->
    case Spec of
        {checked, SuccDst} ->
            {_, St} = define(SuccDst, 'Bool', {{is,defined}, [Expr]}, St0),
            is(Is, Lbl, Universe, BlkExprs, St, Imps);
        unchecked ->
            {Succeeded, St} = expression({{is,defined}, [Expr]}, St0),
            is(Is, Lbl, Universe, BlkExprs, St, [Succeeded | Imps])
    end;
is_1(_Sort, _Expr, Spec, Is, Lbl, Universe, BlkExprs, St0, Imps) ->
    case Spec of
        {checked, SuccDst} ->
            %% Bluntly assume that this operation cannot fail.
            {_, St} = define(SuccDst, 'Bool', {'Bool', true}, St0),
            is(Is, Lbl, Universe, BlkExprs, St, Imps);
        unchecked ->
            is(Is, Lbl, Universe, BlkExprs, St0, Imps)
    end.

phi([{#b_var{}=Arg, _From} | _]=Phis, BlkExprs, St) ->
    %% Try to retain the sort of phis when possible to avoid conversions to
    %% 'Term': it's relatively common for them to be 'Bool' in branchy control
    %% flow.
    #{ Arg := {Sort, _} } = St#st.vars,
    phi_1(Phis, Sort, BlkExprs, St);
phi([{#b_literal{val=Lit}, _From} | _]=Phis, BlkExprs, St) ->
    Sort = if
               is_boolean(Lit) -> 'Bool';
               is_integer(Lit) -> 'Int';
               true -> 'Term'
           end,
    phi_1(Phis, Sort, BlkExprs, St).

phi_1([{Val, _From}], Sort0, _BlkExprs, St0) ->
    Sort = phi_sort(Val, Sort0, St0),
    {Expr, St} = sort_expr(Val, Sort, St0),
    {Sort, Expr, St};
phi_1([{Val0, From} | Phis], Sort0, BlkExprs, St0) ->
    {Sort, Inner, St1} = phi_1(Phis, phi_sort(Val0, Sort0, St0), BlkExprs, St0),
    {Val, St} = sort_expr(Val0, Sort, St1),
    #{ From := Cond } = BlkExprs,
    {Sort, {ite, Cond, Val, Inner}, St}.

phi_sort(Val, Sort, St) ->
    case St#st.vars of
        #{ Val := {Sort, _} } ->
            Sort;
        #{ Val := _ } ->
            'Term';
        #{} ->
            #b_literal{val=Lit} = Val,          %Assertion.
            if
                is_boolean(Lit), Sort =:= 'Bool' -> Sort;
                is_integer(Lit), Sort =:= 'Int' -> Sort;
                true -> 'Term'
            end
    end.

%% Returns the purity, range, and expression of an instruction, together with
%% a list of implications that are relevant to the result (if any).
%%
%% The latter is currently only used by (and very important for) comparison
%% operators, where they tie in the Erlang term order. Doing the same with
%% quantifiers is more elegant but turned out too expensive in practice.
instruction(bs_create_bin, _Universe, Args, St0) ->
    {Expr, St} = term_varargs(Args, St0),
    {'Pure', {bs_create_bin, [Expr]}, [], St};
instruction(bs_match, _Universe, Args, St0) ->
    {Expr, St} = term_varargs(Args, St0),
    {'Pure', {bs_match, [Expr]}, [], St};
instruction(match_fail, Universe, _Args, St) ->
    {'Impure', {raise, [{tick, [Universe]}]}, [], St};
instruction(get_map_element, _Universe, [Map0, Key0], St0) ->
    %% Note the reversed argument order.
    {Key, St1} = term_expr(Key0, St0),
    {Map, St} = term_expr(Map0, St1),
    {'Pure', {{bif, 'Pure', map_get}, [Key, Map]}, [], St};
instruction(has_map_field, _Universe, [Map0, Key0], St0) ->
    %% Note the reversed argument order.
    {Key, St1} = term_expr(Key0, St0),
    {Map, St} = term_expr(Map0, St1),
    {'Bool', {has_map_element, [Key, Map]}, [], St};
instruction(get_tuple_element, _Universe,
            [Tuple0, #b_literal{val=Index}], St0) ->
    {Tuple, St} = term_expr(Tuple0, St0),
    {'Term', {tuple_element, [Tuple, {'Int', Index + 1}]}, [], St};
instruction(get_hd, _Universe, [Arg0], St0) ->
    {Arg, St} = term_expr(Arg0, St0),
    {'Term', {head_value, [Arg]}, [], St};
instruction(get_tl, _Universe, [Arg0], St0) ->
    {Arg, St} = term_expr(Arg0, St0),
    {'Term', {tail_value, [Arg]}, [], St};
instruction(put_list, _Universe, [LHS0, RHS0], St0) ->
    {LHS, St1} = term_expr(LHS0, St0),
    {RHS, St} = term_expr(RHS0, St1),
    {'Term', {cons_term, [LHS, RHS]}, [], St};
instruction(put_tuple, _Universe, Args, St0) ->
    {N, Elements, St} = term_array(Args, St0),
    {'Term', {tuple_term, [{'Int', N}, Elements]}, [], St};
instruction(put_map, _Universe, [Update, Map0 | Args0], St0) ->
    {Sort, Op} = case Update of
                     #b_literal{val=assoc} -> {'Term', put_map_assoc};
                     #b_literal{val=exact} -> {'Pure', put_map_exact}
                 end,
    {Map, St1} = term_expr(Map0, St0),
    {Args, St} = term_varargs(Args0, St1),
    {Sort, {Op, [Map, Args]}, [], St};
instruction(call, _Universe, [#b_remote{mod=#b_literal{val=erlang},
                                        name=#b_literal{val=setelement},
                                        arity=3} | Args0], St0) ->
    %% TODO: break this out into a separate function for known calls.
    %%
    %% Note that we can represent some calls as pure: as long as they don't
    %% side-effect and cannot fail due to any reason other than bad arguments
    %% (including their module being unloaded), we can safely treat them as
    %% pure.
    {Args, St} = term_exprs(Args0, St0),
    {'Pure', {{erlang, setelement, 3}, Args}, [], St};
instruction(make_fun, _Universe, [Callee | Args], St0) ->
    #b_local{name=#b_literal{val=Function},arity=Arity} = Callee,
    {N, Elements, St} = term_array(Args, St0),
    NumFree = N - Arity,
    {'Term',
     {lambda_term,
      [{'String', <<"">>}, %% HACK
       {'String', atom_to_binary(Function)},
       {'Int', Arity - NumFree},
       {'Int', NumFree},
       Elements]},
     [],
     St};
instruction(is_nonempty_list, _Universe, [Arg0], St0) ->
    {Arg, St} = term_expr(Arg0, St0),
    {'Bool', {{is,cons_term}, [Arg]}, [], St};
instruction(is_tagged_tuple, _Universe, [Arg0, Size0, Tag0], St0) ->
    #b_literal{val=Size} = Size0,               %Assertion.
    true = is_integer(Size) andalso Size >= 1,  %Assertion.
    #b_literal{} = Tag0,                        %Assertion.

    {Arg, St1} = term_expr(Arg0, St0),
    {Tag, St} = term_expr(Tag0, St1),

    Expr = {'and',
            [{{is,tuple_term}, [Arg]},
             {same, [{tuple_arity, [Arg]}, {'Int', Size}]},
             {same, [{tuple_element, [Arg, {'Int', 1}]}, Tag]}]},

    {'Bool', Expr, [], St};
instruction(update_record, _Universe, [_Hint, _Size, Tuple0 | Args], St0) ->
    {Tuple, St1} = term_expr(Tuple0, St0),
    {Expr, St} = update_tuple_elements(Args, Tuple, St1),
    {'Term', Expr, [], St};
instruction(update_tuple, _Universe, [Tuple0 | Args], St0) ->
    {Tuple, St1} = term_expr(Tuple0, St0),
    {Expr, St} = update_tuple(Args, Tuple, St1),
    {'Pure', Expr, [], St};
instruction({float, Op}, _Universe, [Arg0], St0)
  when Op =:= negate;
       Op =:= get;
       Op =:= put ->
    {Arg, St} = term_expr(Arg0, St0),
    {'Term', {{float, Op}, [Arg]}, [], St};
instruction({float, convert}=Op, _Universe, [Arg0], St0) ->
    {Arg, St} = term_expr(Arg0, St0),
    {'Pure', {Op, [Arg]}, [], St};
instruction({float, _}=Op, _Universe, Args0, St0) ->
    {Args, St} = term_exprs(Args0, St0),
    {'Pure', {Op, Args}, [], St};
instruction({bif,'-'}, _Universe, [Arg0], St0) ->
    {Arg, St} = term_expr(Arg0, St0),
    {'Pure', {{bif, 'Pure', negate}, [Arg]}, [], St};
instruction({bif,SafeOp}, _Universe, Args0, St0)
  when SafeOp =:= self;
       SafeOp =:= min;
       SafeOp =:= max;
       SafeOp =:= node, length(Args0) =:= 0 ->
    {Args, St} = term_exprs(Args0, St0),
    {'Term', {{bif, 'Term', SafeOp}, Args}, [], St};
instruction({bif,BoolOp}, _Universe, [#b_var{}=LHS, #b_var{}=RHS]=Args0, St0)
  when BoolOp =:= 'and';
       BoolOp =:= 'or';
       BoolOp =:= 'xor' ->
    case St0#st.vars of
        #{ LHS := {'Bool', LExpr}, RHS := {'Bool', RExpr} } ->
            {'Bool', {{bif, 'Bool', BoolOp}, [LExpr, RExpr]}, [], St0};
        #{} ->
            {Args, St} = term_exprs(Args0, St0),
            {'Pure', {{bif, 'Pure', BoolOp}, Args}, [], St}
    end;
instruction({bif,'not'}, _Universe, [#b_var{}=Arg0], St0) ->
    case St0#st.vars of
        #{ Arg0 := {'Bool', Expr} } ->
            {'Bool', {{bif, 'Bool', 'not'}, [Expr]}, [], St0};
        #{} ->
            {Arg, St} = term_expr(Arg0, St0),
            {'Pure', {{bif, 'Pure', 'not'}, [Arg]}, [], St}
    end;
instruction({bif,CompOp}, _Universe, 
            [LHS, RHS]=Args0, St0)
  when CompOp =:= '=:=';
       CompOp =:= '=/=' ->
    case St0#st.vars of
        #{ LHS := {'Bool', Expr} } when ((CompOp =:= '=/=') xor
                                         RHS#b_literal.val) ->
            {'Bool', Expr, [], St0};
        #{ LHS := {'Bool', Expr} } when ((CompOp =:= '=:=') xor
                                         RHS#b_literal.val) ->
            {'Bool', {'not', Expr}, [], St0};
        #{} ->
            {Args, St} = term_exprs(Args0, St0),
            {'Bool', {{bif, 'Bool', CompOp}, Args}, [], St}
    end;
instruction({bif,RelOp}, _Universe, Args0, St0)
  when RelOp =:= '==';
       RelOp =:= '/=';
       RelOp =:= '=<';
       RelOp =:= '<';
       RelOp =:= '>=';
       RelOp =:= '>' ->
    {Args, St} = term_exprs(Args0, St0),
    [LHS, RHS] = Args,
    {'Bool', {{bif, 'Bool', RelOp}, Args},
     [{implies,
       {numeric_lt, {term_order, [LHS]}, {term_order, [RHS]}},
       {{bif, 'Bool', '<'}, [LHS, RHS]}},
      {implies,
       {{bif, 'Bool', '=<'}, [LHS, RHS]},
       {numeric_le, {term_order, [LHS]}, {term_order, [RHS]}}},
      %% FIXME: Encode the weird Int <-> Float comparison rules somehow, so
      %% that we can help the solver understand e.g. `5 < 6.0`
      {implies,
       {'and', [{{is,integer_term}, [LHS]},
                {{is,integer_term}, [RHS]}]},
       {'and', [{same, [{numeric_le,
                         {integer_value, [LHS]},
                         {integer_value, [RHS]}},
                        {{bif, 'Bool', '=<'}, [LHS, RHS]}]},
                {same, [{numeric_le,
                         {integer_value, [RHS]},
                         {integer_value, [LHS]}},
                        {{bif, 'Bool', '=<'}, [RHS, LHS]}]}
               ]}}],
     St};
instruction({bif,is_function}, _Universe, [_, _]=Args0, St0) ->
    %% We don't yet disambiguate macros/functions based on arity, sorts, etc,
    %% so this has to be handled here as it overloads is_function/1.
    {Args, St} = term_exprs(Args0, St0),
    {'Pure', {{bif, 'Pure', is_function_arity}, Args}, [], St};
instruction({bif,Bif}, Universe, Args0, St0) ->
    Arity = length(Args0),
    case (erl_internal:guard_bif(Bif, Arity) orelse
          erl_internal:bool_op(Bif, Arity) orelse
          erl_internal:arith_op(Bif, Arity) orelse
          erl_internal:new_type_test(Bif, Arity)) of
        true ->
            Range = case erl_internal:new_type_test(Bif, Arity) of
                        true -> 'Bool';
                        false -> 'Pure'
                    end,
            {Args, St} = term_exprs(Args0, St0),
            {Range, {{bif, Range, Bif}, Args}, [], St};
        false ->
            generic_impure('Impure', {bif, Bif}, Universe, Args0, St0)
    end;
instruction(call, Universe, [Callee | Args], St) ->
    generic_impure('Impure', {call, Callee}, Universe, Args, St);
instruction(new_try_tag, Universe, Args, St) ->
    generic_impure('Impure', new_try_tag, Universe, Args, St);
instruction(kill_try_tag, Universe, Args, St) ->
    generic_impure('Term', kill_try_tag, Universe, Args, St);
instruction(catch_end, Universe, Args, St) ->
    generic_impure('Term', catch_end, Universe, Args, St);
instruction(landingpad, Universe, Args, St) ->
    generic_impure('Term', landingpad, Universe, Args, St);
instruction(extract, Universe, Args, St) ->
    generic_impure('Term', extract, Universe, Args, St);
instruction(raw_raise, Universe, Args, St) ->
    generic_impure('Term', raw_raise, Universe, Args, St);
instruction(resume, Universe, Args, St) ->
    generic_impure('Term', resume, Universe, Args, St);
instruction(build_stacktrace, Universe, Args, St) ->
    generic_impure('Impure', build_stacktrace, Universe, Args, St);
instruction(nif_start, Universe, Args, St) ->
    generic_impure('Term', nif_start, Universe, Args, St);
instruction(peek_message, Universe, Args, St) ->
    generic_impure('Term', peek_message, Universe, Args, St);
instruction(remove_message, Universe, Args, St) ->
    generic_impure('Term', remove_message, Universe, Args, St);
instruction(recv_next, Universe, Args, St) ->
    generic_impure('Term', recv_next, Universe, Args, St);
instruction(wait_timeout, Universe, Args, St) ->
    generic_impure('Term', wait_timeout, Universe, Args, St);
instruction(recv_marker_reserve, Universe, [], St) ->
    generic_impure('Impure', recv_marker_reserve, Universe, [], St);
instruction(recv_marker_bind, Universe, Args, St) ->
    generic_impure('Impure', recv_marker_bind, Universe, Args, St);
instruction(recv_marker_clear, Universe, Args, St) ->
    generic_impure('Impure', recv_marker_clear, Universe, Args, St);
instruction(bs_init_writable, _Universe, Args, St) ->
    generic_pure('Term', bs_init_writable, Args, St);
instruction(bs_start_match, _Universe, Args, St) ->
    generic_pure('Pure', bs_start_match, Args, St);
instruction(bs_get_tail, _Universe, Args, St) ->
    generic_pure('Term', bs_get_tail, Args, St);
instruction(bs_test_tail, _Universe, Args, St) ->
    generic_pure('Pure', bs_test_tail, Args, St);
instruction(bs_ensure, _Universe, Args, St) ->
    generic_pure('Pure', bs_ensure, Args, St);
instruction(bs_extract, _Universe, Args, St) ->
    generic_pure('Term', bs_extract, Args, St).

update_tuple(Updates, Tuple, St0) ->
    case update_tuple_min_size(Updates, 0) of
        MinSize when MinSize >= 1 ->
            {Updated, St} = update_tuple_elements(Updates, Tuple, St0),

            Expr = {ite,
                    {'and', [{{is,tuple_term}, [Tuple]},
                             {numeric_ge,
                              {tuple_arity, [Tuple]},
                              {'Int', MinSize}}]},
                    {defined, [Updated]},
                    {undefined, []}},

            {Expr, St};
        _ ->
            {{undefined, []}, St0}
    end.

update_tuple_min_size([], MinSize) ->
    MinSize;
update_tuple_min_size([Index0, _Value | Updates], MinSize) ->
    case Index0 of
        #b_literal{val=Index} when is_integer(Index), Index >= 1 ->
            update_tuple_min_size(Updates, max(Index, MinSize));
        _ ->
            0
    end.

update_tuple_elements(Updates, Tuple, St0) ->
    {Elements, St} =
        update_tuple_elements_1(Updates, {tuple_elements, [Tuple]}, St0),
    {{update_field, tuple_elements, Tuple, Elements}, St}.

update_tuple_elements_1([], Elements, St) ->
    {Elements, St};
update_tuple_elements_1([#b_literal{val=Index}, Value0 | Updates],
                        Elements, St0) ->
    {Inner, St1} = update_tuple_elements_1(Updates, Elements, St0),
    {Value, St} = term_expr(Value0, St1),

    {{array_store, Inner, [{'Int', Index}], Value}, St}.

generic_impure(Range, Op, Universe, Args0, St0) ->
    Name = {Op, length(Args0)},
    {Args, St} = term_exprs(Args0, St0),
    Sorts = ['Universe' | ['Term' || _ <- Args]],
    generic_instruction(Range, Name, [Universe | Args], Sorts, St).

generic_pure(Range, Op, Args0, St0) ->
    Name = {Op, length(Args0)},
    {Args, St} = term_exprs(Args0, St0),
    Sorts = ['Term' || _ <- Args],
    generic_instruction(Range, Name, Args, Sorts, St).

generic_instruction(Range, Name, Args, Sorts, St) ->
    #st{functions=Functions0,smt=Ctx0} = St,
    case sets:is_element(Name, Functions0) of
        true ->
            {Range, {Name, Args}, [], St};
        false ->
            Functions = sets:add_element(Name, Functions0),
            {ok, Ctx} = smt:declare({uninterpreted_function,
                                     Name,
                                     Sorts,
                                     Range}, Ctx0),
            {Range, {Name, Args}, [], St#st{functions=Functions,smt=Ctx}}
    end.

term_array(Args, St0) ->
    {N, Elements, St} =
        foldl(fun(Arg, {Index, Inner, Acc0}) ->
                      {Expr, Acc} = term_expr(Arg, Acc0),
                      Store = {array_store, Inner, [{'Int', Index}], Expr},
                      {Index + 1, Store, Acc}
              end, {1, term_array_unit, St0}, Args),
    {N - 1, Elements, St}.

term_varargs([], St) ->
    {{sequence_empty, 'Term'}, St};
term_varargs(Args0, St0) ->
    {Args, St} = mapfoldl(fun term_expr/2, St0, Args0),
    {{sequence_concat, [{sequence_unit, Arg} || Arg <- Args]}, St}.

term_exprs(Args, St) ->
    mapfoldl(fun term_expr/2, St, Args).

term_expr(#b_var{}=Arg, St) ->
    #{ Arg := Def } = St#st.vars,               %Assertion.
    case Def of
        {'Bool', Expr} ->
            {{ite, Expr, atom_true, atom_false}, St};
        {'Int', Expr} ->
            {{integer_term, [Expr]}, St};
        {'Impure', Expr} ->
            {{result, [Expr]}, St};
        {'Pure', Expr} ->
            {{value, [Expr]}, St};
        {'Term', Expr} ->
            {Expr, St};
        _ ->
            error({no_term_conversion, Arg, Def})
    end;
term_expr(#b_literal{val=Value}, St) ->
    literal_expr(Value, St).

literal_expr(Value, St0) when is_bitstring(Value) ->
    {Opaque, St} = opaque_expr(Value, St0),
    {{bitstring_term, [{'Int', bit_size(Value)}, Opaque]}, St};
literal_expr([Head | Tail], St0) ->
    {HeadExpr, St1} = literal_expr(Head, St0),
    {TailExpr, St} = literal_expr(Tail, St1),
    {{cons_term, [HeadExpr, TailExpr]}, St};
literal_expr(Value, St0) when is_map(Value) ->
    {Opaque, St} = opaque_expr(Value, St0),
    {{map_term, [{'Int', map_size(Value)}, Opaque]}, St};
literal_expr(Value, St0) when is_pid(Value) ->
    {Opaque, St} = opaque_expr(Value, St0),
    {{pid_term, [Opaque]}, St};
literal_expr(Value, St0) when is_port(Value) ->
    {Opaque, St} = opaque_expr(Value, St0),
    {{port_term, [Opaque]}, St};
literal_expr(Value, St0) when is_reference(Value) ->
    {Opaque, St} = opaque_expr(Value, St0),
    {{reference_term, [Opaque]}, St};
literal_expr(Value, St0) when is_tuple(Value) ->
    {_, Elements, St} =
        foldl(fun(Arg, {Index, Inner, Acc0}) ->
                      {Expr, Acc} = literal_expr(Arg, Acc0),
                      Store = {array_store, Inner, [{'Int', Index}], Expr},
                      {Index + 1, Store, Acc}
              end, {1, term_array_unit, St0}, tuple_to_list(Value)),
    {{tuple_term, [{'Int', tuple_size(Value)}, Elements]}, St};
literal_expr(Value, St) ->
    {literal_expr_1(Value), St}.

literal_expr_1(true) ->
    atom_true;
literal_expr_1(false) ->
    atom_false;
literal_expr_1(Value) when is_function(Value) ->
    {type, external} = erlang:fun_info(Value, type), %Assertion.
    {module, Module} = erlang:fun_info(Value, module),
    {name, Function} = erlang:fun_info(Value, name),
    {arity, Arity} = erlang:fun_info(Value, arity),

    {lambda_term,
     [{'String', atom_to_binary(Module)},
      {'String', atom_to_binary(Function)},
      {'Int', Arity},
      {'Int', 0},
      term_array_unit]};
literal_expr_1(Value) when is_atom(Value) ->
    {atom_term, [{'String', atom_to_binary(Value)}]};
literal_expr_1(Value) when is_integer(Value) ->
    {integer_term, [{'Int', Value}]};
literal_expr_1(Value) when is_float(Value) ->
    %% HACK HACK HACK
    {integer_term, [{'Int', trunc(Value)}]};
literal_expr_1([]) ->
    {nil_term, []}.

opaque_expr(Value, #st{opaques=Opaques}=St) ->
    case Opaques of
        #{ Value := Existing } ->
            {Existing, St};
        #{} ->
            Expr = {opaque, [{'Int', map_size(Opaques)}]},
            {Expr, St#st{opaques=Opaques#{ Value => Expr }}}
    end.

sort_expr(Arg, 'Term', St) ->
    term_expr(Arg, St);
sort_expr(#b_var{}=Arg, Sort, St) ->
    #{ Arg := {Sort, Expr} } = St#st.vars,
    {Expr, St};
sort_expr(#b_literal{val=Val}, Sort, St) ->
    true = Sort =:= 'Bool' orelse Sort =:= 'Int',
    {{Sort, Val}, St}.
