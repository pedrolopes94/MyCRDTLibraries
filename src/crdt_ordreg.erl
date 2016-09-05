%% @author pedrolopes

%% @doc A state- and op-based Ordered State Register CRDT.
%% As the data structure is operation-based, to issue an operation, 
%% one should firstly call 'generate_downstream/3' to get the downstream version of the 
%% operation and then call 'update/2'.
%%
%% As the structure is also a state-based CRDT, it has as well a 'merge/2' function used
%% to perform a merge of two Register states.
%% @end

-module(crdt_ordreg).
-behaviour(riak_dt).

-export([new/0, value/1, value/2, merge/2, equal/2]).
-export([parent_clock/2]).
-export([update/2, update/3, update/4]).
-export([stats/1, stat/2]).
-export([generate_downstream/3]).
-export([to_binary/1, to_binary/2]).
-export([from_binary/1]).
-export([to_version/2]).
-export([is_operation/1]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

-export_type([ordreg/0, ordreg_op/0]).

-opaque ordreg() :: {riak_dt_vclock:vclock(), term()}.

-type ordreg_op() :: {assign, {term(), actor()}}  | {assign, term()}.

-type actor() :: riak_dt:actor() | {riak_dt:actor(), riak_dt_vclock:vclock()}.

-spec new() -> ordreg().
new() ->
	{riak_dt_vclock:fresh(), <<>>}.

-spec parent_clock(riak_dt_vclock:vclock(), ordreg()) -> ordreg().
parent_clock(_Clock, Reg) ->
    Reg.

-spec value(ordreg()) -> term().
value({_Clock, Value}) ->
	Value.
-spec value(term(), ordreg()) -> [term()].
value(_, OrdReg) ->
	value(OrdReg).

-spec update(ordreg_op(), ordreg()) -> {ok, ordreg()}.
update({assign, {Value, Actor}}, OrdReg) ->
	update({assign, Value}, Actor, OrdReg).

%% @doc The assign operation may receve a tuple consisting of an actor
%%		and a clock, which corresponds to the clock of the source replica.
%%		We are receiving a whole clock instead of a Dot because we want only
%%		to assign the new value if no concurrent assigns occurred between the replicas.
%%		And the only way to verify that is by comparing clocks.
%%		If concurrent assigns occurred, we want the bigger element (in natural order)
%%		between the current value and the value to assign.
-spec update(ordreg_op(), actor(), ordreg()) -> {ok, ordreg()}.
update({assign, Value}, {_Actor, Clk}, {Clock, CurrValue}) when is_list(Clk)->
	NewClock = riak_dt_vclock:merge([Clk, Clock]),
	case riak_dt_vclock:descends(Clk, Clock) orelse riak_dt_vclock:descends(Clock, Clk) of
		true ->
			{ok, {NewClock, Value}};
		false ->
			GreaterValue = max(Value, CurrValue),
			{ok, {NewClock, GreaterValue}}
	end;
			
update({assign, Value}, Actor, {Clock, _CurrValue}) ->
	NewClock = riak_dt_vclock:increment(Actor, Clock),
	{ok, {NewClock, Value}}.

update(Op, Actor, Reg, _Ctx) ->
    update(Op, Actor, Reg).

-spec merge(ordreg(), ordreg()) -> {ok, ordreg()}.
merge({Clock, Value}, {Clock, Value}) ->
	{ok, {Clock, Value}};
merge({LHClock, LHValue}, {RHClock, RHValue}) ->
	NewClock = riak_dt_vclock:merge([LHClock, RHClock]),
	GreaterValue = max(LHValue, RHValue),
	{ok, {NewClock, GreaterValue}}.

-spec equal(ordreg(), ordreg()) -> boolean().
equal({Clock, Value}, {Clock, Value}) ->
	true;
equal(_,_) ->
	false.

-spec stats(ordreg()) -> [{atom(), number() | undefined}].
stats(OrdReg) ->
	[{value_size, stat(value_size, OrdReg)}].

-spec stat(atom(), ordreg()) -> number() | undefined.
stat(value_size, {_Clock, Value}) ->
	erlang:external_size(Value);
stat(_, _) -> undefined.

-spec generate_downstream(ordreg_op(), actor(), ordreg()) -> {ok, ordreg_op()}.
generate_downstream({assign, Value}, Actor, {Clock, _CurrValue}) ->
	NewClock = riak_dt_vclock:increment(Actor, Clock),
	{ok, {assign, {Value, {Actor, NewClock}}}}.

-include("riak_dt_tags.hrl").
-define(TAG, ?DT_ORDREG_TAG).
-define(V1_VERS, 1).

-spec to_binary(ordreg()) -> binary().
to_binary(OrdReg) ->
    <<?TAG:8/integer, ?V1_VERS:8/integer, (riak_dt:to_binary(OrdReg))/binary>>.

-spec to_binary(Vers :: pos_integer(), ordreg()) -> {ok, binary()} | ?UNSUPPORTED_VERSION.
to_binary(1, OrdReg) ->
    {ok, to_binary(OrdReg)};
to_binary(Vers, _OrdReg) ->
    ?UNSUPPORTED_VERSION(Vers).

-spec from_binary(binary()) -> {ok, ordreg()} | ?UNSUPPORTED_VERSION | ?INVALID_BINARY.
from_binary(<<?TAG:8/integer, ?V1_VERS:8/integer, Bin/binary>>) ->
    {ok, riak_dt:from_binary(Bin)};
from_binary(<<?TAG:8/integer, Vers:8/integer, _Bin/binary>>) ->
    ?UNSUPPORTED_VERSION(Vers);
from_binary(_B) ->
    ?INVALID_BINARY.

-spec to_version(pos_integer(), ordreg()) -> ordreg().
to_version(_Version, OrdReg) ->
    OrdReg.

-spec is_operation(term()) -> boolean().
is_operation(Operation) ->
    case Operation of
        {assign, _} ->
            true;
        _ ->
            false
    end.

%% ===================================================================
%% EUnit tests
%% ===================================================================
-ifdef(TEST).
new_test() ->
    ?assertEqual({[], <<>>}, new()).

value_test() ->
	Reg1 = new(),
    Reg2 = {[{x,1}], "A"},
    ?assertEqual(<<>>, value(Reg1)),
	?assertEqual("A", value(Reg2)).

update_assign_test() ->
    Reg1 = new(),
	{ok, Assign1} = generate_downstream({assign, "B"}, actor1, Reg1),
    {ok, Reg2} = update(Assign1, Reg1),
	{ok, Assign2} = generate_downstream({assign, "A"}, actor1, Reg2),
	{ok, Reg3} = update(Assign2, Reg2),
	{ok, Assign3} = generate_downstream({assign, "C"}, actor2, Reg3),
	{ok, Reg4} = update(Assign3, Reg3),
    ?assertEqual({[{actor1, 1}], "B"}, Reg2),
	?assertEqual({[{actor1, 2}], "A"}, Reg3),
	?assertEqual({[{actor1, 2}, {actor2, 1}], "C"}, Reg4).

merge_test() ->
	Reg1 = new(),
	{ok, Assign1} = generate_downstream({assign, "p"}, actor1, Reg1),
	{ok, Reg2} = update(Assign1, Reg1),
	{ok, Assign2} = generate_downstream({assign, "m"}, actor2, Reg1),
	{ok, Reg3} = update(Assign2, Reg1),
	{ok, Merge} = merge(Reg2, Reg3),
	?assertEqual({[{actor1, 1}, {actor2, 1}], "p"}, Merge).

equal_test() ->
    Reg1 = new(),
	{ok, Assign1} = generate_downstream({assign, "obj1"}, actor1, Reg1),
	{ok, Reg2} = update(Assign1, Reg1),
	{ok, Assign2} = generate_downstream({assign, "obj2"}, actor1, Reg2),
	{ok, Reg3} = update(Assign2, Reg2),
	{ok, Assign3} = generate_downstream({assign, obj2}, actor1, Reg2),
	{ok, Reg4} = update(Assign3, Reg2),
    ?assert(equal(Reg1, Reg1)),
    ?assertNot(equal(Reg3, Reg4)).

stat_test() ->
    Reg1 = new(),
	{ok, Assign1} = generate_downstream({assign, <<"abcd">>}, actor1, Reg1),
	{ok, Reg2} = update(Assign1, Reg1),
	?assertEqual([{value_size, 11}], stats(Reg1)),
    ?assertEqual([{value_size, 15}], stats(Reg2)),
    ?assertEqual(15, stat(value_size, Reg2)),
    ?assertEqual(undefined, stat(actor_count, Reg2)).
-endif.