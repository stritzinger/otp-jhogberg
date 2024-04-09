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

-feature(maybe_expr, enable).
-module(z3_nif).

-export([new/1,
         close/1,
         fence/1,

         simplify/3,
         symbol/3,

         assert/2,
         check/1, check/2,
         push/1, pop/3,

         uninterpreted_sort/3,

         make_boolean/3,
         boolean_sort/2,
         one_of/3,
         same/3,
         distinct/3,
         iff/4,
         implies/4,
         negate/3,
         exclusive_or/4,
         conjugation/3,
         disjunction/3,
         if_then_else/5,

         application/4,
         constant/4,
         declare_interpreted_function/5,
         define_interpreted_function/4,
         uninterpreted_function/5,
         linear_order/4,

         constructor/5,
         datatype/4,
         datatype_sort/3,
         query_constructor/5,
         update_field/5,

         array_sort/4,
         array_select/4,
         array_store/5,

         sequence_sort/3,
         sequence_concat/3,
         sequence_empty/3,
         sequence_unit/3,
         sequence_length/3,

         make_string/3,
         string_sort/2,
         string_lt/4,
         string_le/4,

         integer_sort/2,
         real_sort/2,
         make_integer/4,
         make_real/4,
         numeric_addition/3,
         numeric_multiplication/3,
         numeric_subtraction/3,
         numeric_unary_minus/3,
         numeric_division/4,
         numeric_modulus/4,
         numeric_remainder/4,
         numeric_power/4,
         numeric_lt/4,
         numeric_le/4,
         numeric_gt/4,
         numeric_ge/4
        ]).

-export([load/0]).

-spec load() -> term().
load() ->
    %% FIXME: lifted from ASN.1, this needs to be cleaned up and hoisted to the
    %% user as we plan to support several solvers under a common interface, and
    %% this logic will most likely be the exact same for all of them.
    LibBaseName = atom_to_list(?MODULE),
    PrivDir = code:priv_dir(smt),
    LibName = case erlang:system_info(build_type) of
                  opt ->
                      LibBaseName;
                  Type ->
                      LibTypeName = LibBaseName ++ "." ++ atom_to_list(Type),
                      case (filelib:wildcard(
                              filename:join(
                                [PrivDir,
                                 "lib",
                                 LibTypeName ++ "*"])) /= []) orelse
                          (filelib:wildcard(
                             filename:join(
                               [PrivDir,
                                "lib",
                                erlang:system_info(system_architecture),
                                LibTypeName ++ "*"])) /= []) of
                          true ->LibTypeName;
                          false ->LibBaseName
                      end
              end,
    Lib = filename:join([PrivDir, "lib", LibName]),

    maybe
        {error, {load_failed, _}} = Error ?= erlang:load_nif(Lib, 0),

        ArchLibDir = filename:join([PrivDir, "lib",
                                    erlang:system_info(system_architecture)]),
        Candidate = filelib:wildcard(filename:join([ArchLibDir,LibName ++ "*"])),
        case Candidate of
            [] ->
                Error;
            _ ->
                ArchLib = filename:join([ArchLibDir, LibName]),
                erlang:load_nif(ArchLib, 0)
        end
    else
        Other ->Other
    end.

-spec check(_Context) -> term().
check(Context) ->
    check(Context, []).

-spec fence(_Context) -> term().
fence(_Context) ->
    erlang:nif_error(undef).

-spec new(_Options) -> term().
new(_Options) ->
    erlang:nif_error(undef).

-spec close(_Options) -> term().
close(_Options) ->
    erlang:nif_error(undef).

-spec simplify(_Context, _Id, _Expression) -> term().
simplify(_Context, _Id, _Expression) ->
    erlang:nif_error(undef).

-spec symbol(_Context, _Id, _Name) -> term().
symbol(_Context, _Id, _Name) ->
    erlang:nif_error(undef).

%% Solver stuff.
-spec assert(_Context, _Expression) -> term().
assert(_Context, _Expression) ->
    erlang:nif_error(undef).

-spec check(_Context, _Assumptions) -> term().
check(_Context, _Assumptions) ->
    erlang:nif_error(undef).

-spec push(_Context) -> term().
push(_Context) ->
    erlang:nif_error(undef).

-spec pop(_Context, _Frames, _FromId) -> term().
pop(_Context, _Frames, _FromId) ->
    erlang:nif_error(undef).

%% Constants
-spec make_boolean(_Context, _Id, _Value) -> term().
make_boolean(_Context, _Id, _Value) ->
    erlang:nif_error(undef).

-spec make_integer(_Context, _Id, _Sort, _Value) -> term().
make_integer(_Context, _Id, _Sort, _Value) ->
    erlang:nif_error(undef).

-spec make_string(_Context, _Id, _Value) -> term().
make_string(_Context, _Id, _Value) ->
    erlang:nif_error(undef).

-spec make_real(_Context, _Id, _Numerator, _Denominator) -> term().
make_real(_Context, _Id, _Numerator, _Denominator) ->
    erlang:nif_error(undef).

%% Logical operations
-spec one_of(_Context, _Id, _Exprs) -> term().
one_of(_Context, _Id, _Exprs) ->
    erlang:nif_error(undef).

-spec same(_Context, _Id, _Exprs) -> term().
same(_Context, _Id, _Exprs) ->
    erlang:nif_error(undef).

-spec distinct(_Context, _Id, _Exprs) -> term().
distinct(_Context, _Id, _Exprs) ->
    erlang:nif_error(undef).

-spec iff(_Context, _Id, _LHS, _RHS) -> term().
iff(_Context, _Id, _LHS, _RHS) ->
    erlang:nif_error(undef).

-spec implies(_Context, _Id, _LHS, _RHS) -> term().
implies(_Context, _Id, _LHS, _RHS) ->
    erlang:nif_error(undef).

-spec negate(_Context, _Id, _Expr) -> term().
negate(_Context, _Id, _Expr) ->
    erlang:nif_error(undef).

-spec exclusive_or(_Context, _Id, _LHS, _RHS) -> term().
exclusive_or(_Context, _Id, _LHS, _RHS) ->
    erlang:nif_error(undef).

-spec conjugation(_Context, _Id, _Exprs) -> term().
conjugation(_Context, _Id, _Exprs) ->
    erlang:nif_error(undef).

-spec disjunction(_Context, _Id, _Exprs) -> term().
disjunction(_Context, _Id, _Exprs) ->
    erlang:nif_error(undef).

-spec if_then_else(_Context, _Id, _If, _Then, _Else) -> term().
if_then_else(_Context, _Id, _If, _Then, _Else) ->
    erlang:nif_error(undef).


%% Functions
-spec uninterpreted_function(_Context, _Id, _Symbol, _Domain, _Range) -> term().
uninterpreted_function(_Context, _Id, _Symbol, _Domain, _Range) ->
    erlang:nif_error(undef).

-spec declare_interpreted_function(_Context, _Id, _Symbol, _Domain, _Range) -> term().
declare_interpreted_function(_Context, _Id, _Symbol, _Domain, _Range) ->
    erlang:nif_error(undef).

-spec define_interpreted_function(_Context, _Function, _Arguments, _Body) -> term().
define_interpreted_function(_Context, _Function, _Arguments, _Body) ->
    erlang:nif_error(undef).

-spec constant(_Context, _Id, _Symbol, _Sort) -> term().
constant(_Context, _Id, _Symbol, _Sort) ->
    erlang:nif_error(undef).

-spec application(_Context, _Id, _Function, _Arguments) -> term().
application(_Context, _Id, _Function, _Arguments) ->
    erlang:nif_error(undef).

-spec linear_order(_Context, _Id, _Sort, _Index) -> term().
linear_order(_Context, _Id, _Sort, _Index) ->
    erlang:nif_error(undef).

%% Datatypes
-spec constructor(_Context, _Id, _Name, _Recognizer, _Fields) -> term().
constructor(_Context, _Id, _Name, _Recognizer, _Fields) ->
    erlang:nif_error(undef).

-spec datatype(_Context, _Id, _Name, _Constructors) -> term().
datatype(_Context, _Id, _Name, _Constructors) ->
    erlang:nif_error(undef).

-spec datatype_sort(_Context, _Id, _Name) -> term().
datatype_sort(_Context, _Id, _Name) ->
    erlang:nif_error(undef).

-spec query_constructor(_Context,
                        _Constructor_Func_Id,
                        _Tester_Func_Id,
                        _Accessor_Ids,
                        _Constructor) -> term().
query_constructor(_Context,
                  _Constructor_Func_Id,
                  _Tester_Func_Id,
                  _Accessor_Ids,
                  _Constructor) ->
    erlang:nif_error(undef).

-spec update_field(_Context, _Id, _Accessor, _Record, _Value) -> term().
update_field(_Context, _Id, _Accessor, _Record, _Value) ->
    erlang:nif_error(undef).

%% Integer/Real operations


-spec numeric_addition(_Context, _Id, _Exprs) -> term().
numeric_addition(_Context, _Id, _Exprs) ->
    erlang:nif_error(undef).

-spec numeric_multiplication(_Context, _Id, _Exprs) -> term().
numeric_multiplication(_Context, _Id, _Exprs) ->
    erlang:nif_error(undef).

-spec numeric_subtraction(_Context, _Id, _Exprs) -> term().
numeric_subtraction(_Context, _Id, _Exprs) ->
    erlang:nif_error(undef).

-spec numeric_unary_minus(_Context, _Id, _Expr) -> term().
numeric_unary_minus(_Context, _Id, _Expr) ->
    erlang:nif_error(undef).

-spec numeric_division(_Context, _Id, _LHS, _RHS) -> term().
numeric_division(_Context, _Id, _LHS, _RHS) ->
    erlang:nif_error(undef).

-spec numeric_modulus(_Context, _Id, _LHS, _RHS) -> term().
numeric_modulus(_Context, _Id, _LHS, _RHS) ->
    erlang:nif_error(undef).

-spec numeric_remainder(_Context, _Id, _LHS, _RHS) -> term().
numeric_remainder(_Context, _Id, _LHS, _RHS) ->
    erlang:nif_error(undef).

-spec numeric_power(_Context, _Id, _LHS, _RHS) -> term().
numeric_power(_Context, _Id, _LHS, _RHS) ->
    erlang:nif_error(undef).

-spec numeric_lt(_Context, _Id, _LHS, _RHS) -> term().
numeric_lt(_Context, _Id, _LHS, _RHS) ->
    erlang:nif_error(undef).

-spec numeric_le(_Context, _Id, _LHS, _RHS) -> term().
numeric_le(_Context, _Id, _LHS, _RHS) ->
    erlang:nif_error(undef).

-spec numeric_gt(_Context, _Id, _LHS, _RHS) -> term().
numeric_gt(_Context, _Id, _LHS, _RHS) ->
    erlang:nif_error(undef).

-spec numeric_ge(_Context, _Id, _LHS, _RHS) -> term().
numeric_ge(_Context, _Id, _LHS, _RHS) ->
    erlang:nif_error(undef).

%% Array operations
-spec array_sort(_Context, _Id, _Domain, _Range) -> term().
array_sort(_Context, _Id, _Domain, _Range) ->
    erlang:nif_error(undef).
-spec array_select(_Context, _Id, _Array, _Indexes) -> term().
array_select(_Context, _Id, _Array, _Indexes) ->
    erlang:nif_error(undef).
-spec array_store(_Context, _Id, _Array, _Indexes, _Value) -> term().
array_store(_Context, _Id, _Array, _Indexes, _Value) ->
    erlang:nif_error(undef).

%% Sequence operations
-spec sequence_sort(_Context, _Id, _Sort) -> term().
sequence_sort(_Context, _Id, _Sort) ->
    erlang:nif_error(undef).

-spec sequence_concat(_Context, _Id, _Exprs) -> term().
sequence_concat(_Context, _Id, _Exprs) ->
    erlang:nif_error(undef).

-spec sequence_empty(_Context, _Id, _Sort) -> term().
sequence_empty(_Context, _Id, _Sort) ->
    erlang:nif_error(undef).

-spec sequence_unit(_Context, _Id, _Expr) -> term().
sequence_unit(_Context, _Id, _Expr) ->
    erlang:nif_error(undef).

-spec sequence_length(_Context, _Id, _Expr) -> term().
sequence_length(_Context, _Id, _Expr) ->
    erlang:nif_error(undef).

-spec string_lt(_Context, _Id, _LHS, _RHS) -> term().
string_lt(_Context, _Id, _LHS, _RHS) ->
    erlang:nif_error(undef).

-spec string_le(_Context, _Id, _LHS, _RHS) -> term().
string_le(_Context, _Id, _LHS, _RHS) ->
    erlang:nif_error(undef).

%% Sorts
-spec boolean_sort(_Context, _Id) ->term().
boolean_sort(_Context, _Id) ->
    erlang:nif_error(undef).

-spec integer_sort(_Context, _Id) ->term().
integer_sort(_Context, _Id) ->
    erlang:nif_error(undef).

-spec real_sort(_Context, _Id) ->term().
real_sort(_Context, _Id) ->
    erlang:nif_error(undef).

-spec string_sort(_Context, _Id) ->term().
string_sort(_Context, _Id) ->
    erlang:nif_error(undef).

-spec uninterpreted_sort(_Context, _Id, _Symbol) ->term().
uninterpreted_sort(_Context, _Id, _Symbol) ->
    erlang:nif_error(undef).
