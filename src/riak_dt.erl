%% -------------------------------------------------------------------
%%
%% riak_dt.erl: behaviour for convergent data types
%%
%% Copyright (c) 2007-2012 Basho Technologies, Inc.  All Rights Reserved.
%%
%% This file is provided to you under the Apache License,
%% Version 2.0 (the "License"); you may not use this file
%% except in compliance with the License.  You may obtain
%% a copy of the License at
%%
%%   http://www.apache.org/licenses/LICENSE-2.0
%%
%% Unless required by applicable law or agreed to in writing,
%% software distributed under the License is distributed on an
%% "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
%% KIND, either express or implied.  See the License for the
%% specific language governing permissions and limitations
%% under the License.
%%
%% -------------------------------------------------------------------

-module(riak_dt).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

-export([to_binary/1, from_binary/1, dict_to_orddict/1]).
-export_type([actor/0, dot/0, crdt/0, context/0]).
-export([is_riak_dt/1]).

-include("riak_dt.hrl").
-include("riak_dt_tags.hrl").

-type crdt() :: term().
-type operation() :: term().
-type actor() :: term().
-type value() :: term().
-type error() :: term().
-type dot() :: {actor(), pos_integer()}.
-type context() :: riak_dt_vclock:vclock() | undefined.

-callback new() -> crdt().
-callback value(crdt()) -> term().
-callback value(term(), crdt()) -> value().
-callback update(operation(), actor(), crdt()) -> {ok, crdt()} | {error, error()}.
-callback update(operation(), actor(), crdt(), context()) -> {ok, crdt()} | {error, error()}.
%% @doc When nested in a Map, some CRDTs need the logical clock of the
%% top level Map to make context operations. This callback provides
%% the clock and the crdt, and if relevant, returns to crdt with the
%% given clock as it's own.
-callback parent_clock(riak_dt_vclock:vclock(), crdt()) ->
     crdt().
-callback merge(crdt(), crdt()) -> crdt().
-callback equal(crdt(), crdt()) -> boolean().
-callback to_binary(crdt()) -> binary().
-callback to_binary(TargetVers :: pos_integer(), crdt()) ->
     {ok, binary()} | ?UNSUPPORTED_VERSION.
-callback from_binary(binary()) -> {ok, crdt()} |
                                   ?INVALID_BINARY |
                                   ?UNSUPPORTED_VERSION.

-callback stats(crdt()) -> [{atom(), number()}].
-callback stat(atom(), crdt()) -> number() | undefined.
-callback is_operation(term()) -> boolean().

-callback to_version(pos_integer(), crdt()) -> crdt().

-define(RIAK_DT_CRDTS, [riak_dt_disable_flag, riak_dt_emcntr,
    riak_dt_enable_flag, riak_dt_gcounter, riak_dt_gset, riak_dt_lwwreg,
    riak_dt_map, riak_dt_od_flag, riak_dt_oe_flag, riak_dt_orset,
    riak_dt_orswot, riak_dt_pncounter, riak_dt_vclock, riak_dt_mvreg]).

-ifdef(EQC).
% Extra callbacks for any crdt_statem_eqc tests

-callback gen_op() -> eqc_gen:gen(operation()).

-endif.

-spec to_binary(crdt()) -> binary().
to_binary(Term) ->
    Opts = case application:get_env(riak_dt, binary_compression, 1) of
               true -> [compressed];
               N when N >= 0, N =< 9 -> [{compressed, N}];
               _ -> []
           end,
    term_to_binary(Term, Opts).

-spec from_binary(binary()) -> crdt().
from_binary(Binary) ->
    binary_to_term(Binary).


%% @private turns a dict into a sorted list of [{key, value}]
-spec dict_to_orddict(riak_dt_dict()) -> orddict:orddict().
dict_to_orddict(Dict) ->
    lists:sort(dict:to_list(Dict)).

%%  @doc checks that a given atom is a riak_dt CRDT.
-spec is_riak_dt(term()) -> boolean().
is_riak_dt(Term) ->
    is_atom(Term) andalso lists:member(Term, ?RIAK_DT_CRDTS).

-ifdef(TEST).
is_riak_dt_test() ->
    ?assertEqual(true, is_riak_dt(riak_dt_pncounter)),
    ?assertEqual(false, is_riak_dt(whatever)).

-endif.