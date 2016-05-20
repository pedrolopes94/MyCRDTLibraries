%% @author Pedro Lopes
-module(pncounter).
-export([new/0, update/3, value/1, compare/2, merge/2]).
-include_lib("eunit/include/eunit.hrl").

%% The next module functions work with replicas as ordered maps.
%% Each entry of those maps is a pair {K, V} where K is a key and V is a value.
%% Each key is unique and represents the identifier of a source replica; it has also a value
%% that will hold its P value and N value.
%% For example, let R be a replica as an ordered map. R will have the following format:
%% R = [{ID0, {P0,N0}}, {ID1, {P1,N1}}, ..., {ID(n-1), {P(n-1),N(n-1)}}],
%% where IDi is the identifier of the source replica;
%% Pi is the current value for the corresponding increment G-Counter;
%% Ni is the current value for the corresponding decrement G-Counter;
%% and n equals the number of replicas.


%% new/0 function: returns an empty PN-Counter.
new() -> orddict:new().

%% update/3 function: increments (inc) or decrements (dec) a G-Counter of an actor (ID).
%% This function hides two sub-functions: the increment and decrement. Depending on the value
%% of the first parameter, a function of type increment or decrement is executed.
%% More formally, the increment function can be written this way: Counter[ID] := {P + 1, N}
%% The decrement function can be written this way: Counter[ID] := {P, N + 1}
update(inc, Counter, ID) ->
	update({inc, 1}, Counter, ID);
update(dec, Counter, ID) ->
	update({dec, 1}, Counter, ID);

update({inc, Value}, Counter, ID) ->
	case orddict:is_key(ID, Counter) of
		true ->	lists:reverse(update_op({fun increment/2, Value}, Counter, ID, []));
		false -> orddict:store(ID, increment({0,0}, Value), Counter)
	end;
update({dec, Value}, Counter, ID) ->
	case orddict:is_key(ID, Counter) of
		true -> lists:reverse(update_op({fun decrement/2, Value}, Counter, ID, []));
		false -> orddict:store(ID, decrement({0,0}, Value), Counter)
	end.

update_op(_, [], _, Final) -> Final;
update_op({Op, Value}, [{OldID, {P, N}} | T], ID, Final) when OldID == ID ->
	lists:reverse(T) ++ [{OldID, Op({P, N}, Value)} | Final];
update_op({Op, Value}, [H | T], ID, Final) ->
	update_op({Op, Value}, T, ID, [H | Final]).

increment({P, _N}, Value) -> {P + Value, _N}.
decrement({_P, N}, Value) -> {_P, N + Value}.

%% value/1 function: returns the difference between two G-Counters (P and N).
value(Counter) ->
	lists:sum([Pvalue - Nvalue || {_, {Pvalue, Nvalue}} <- Counter]).

%% ________ Alternative version of Value function ________
%% value(Counter) ->
%% 	get_value(Counter, 0, 0).
%%
%% get_value([], PSum, NSum) -> PSum - NSum;
%% get_value([{_, {P, N}} | T], PSum, NSum) -> 
%%	get_value(T, PSum + P, NSum + N).


%% compare/2 function: returns true if all values from P and N of PN-Counter X
%% are less than or equal to values from P and N of PN-Counter Y, respectively; returns false otherwise.
compare(CounterX, CounterY) ->
	try compare_counters(CounterX, CounterY) of
		true -> true
	catch
		false -> false
	end.

compare_counters([], []) -> true;
compare_counters([{X_ID, {X_P, X_N}} | X_T], [{Y_ID, {Y_P, Y_N}} | Y_T])
  when X_P =< Y_P,  X_N =< Y_N, X_ID == Y_ID ->
	compare_counters(X_T, Y_T);
compare_counters(_, _) -> throw(false). %%	The function must stop when the requirements don't apply.

%% merge/2 function: returns Z, a new PN-Counter with counters with merged values from PN-Counters X and Y.
%% This function merges each P and N from X and Y (respectively). For each actor,
%% the maximum value between X and Y is calculated, and saves that value in the new PN-Counter.
merge(CounterX, CounterY) ->
	orddict:merge(fun calculate_max/3, CounterX, CounterY).

calculate_max(_, {X_P, X_N}, {Y_P, Y_N}) ->
	{max(X_P, Y_P), max(X_N, Y_N)}.

%% ________ Alternative version of Merge function ________ (tested only once)
%% merge(CounterX, CounterY) ->
%% 	lists:reverse(merge_lists(CounterX, CounterY, [])).
%%
%% merge_lists([], [], Res) -> Res;
%% merge_lists([], Remains, Res) ->
%% 	lists:reverse(Remains) ++ Res;
%% merge_lists(Remains, [], Res) ->
%% 	lists:reverse(Remains) ++ Res;
%% merge_lists([{X_ID, {X_P, X_N}} = Entry | X_T], [{_, {Y_P, Y_N}} | Y_T] = CounterY, Res) ->
%% 	case orddict:is_key(X_ID, CounterY) of
%% 		true ->	P_max = max(X_P, Y_P),
%% 				N_max = max(X_N, Y_N),
%% 				merge_lists(X_T, Y_T, [{X_ID, {P_max, N_max}} | Res]);
%% 		false -> merge_lists(X_T, CounterY, [Entry | Res])
%% 	end.
%% merge_lists([_ | T1], [_ | T2], Res) ->
%% 	merge_lists(T1, T2, Res).


%% ________ EUnit Tests ________
new_test() ->
	?assertEqual([], new()).

increment_test() ->
	S0 = new(),
	S1 = update(inc, S0, id1),
	S2 = update(inc, S1, id2),
	S3 = update(inc, S2, id1),
	?assertEqual([{id1, {2,0}}, {id2, {1,0}}], S3).

increment_value_test() ->
	S0 = new(),
	S1 = update({inc, 5}, S0, id2),
	S2 = update({inc, 5}, S1, id1),
	S3 = update({inc, 2}, S2, id1),
	?assertEqual([{id1, {7,0}}, {id2, {5,0}}], S3).

decrement_test() ->
	S0 = new(),
	S1 = update(dec, S0, id2),
	S2 = update(dec, S1, id1),
	S3 = update(dec, S2, id2),
	?assertEqual([{id1, {0,1}}, {id2, {0,2}}], S3).

decrement_value_test() ->
	S0 = new(),
	S1 = update({dec, 10}, S0, id1),
	S2 = update({dec, 7}, S1, id2),
	S3 = update({dec, 3}, S2, id1),
	?assertEqual([{id1, {0,13}}, {id2, {0,7}}], S3).

update_mixed_test() ->
	C0 = new(),
	S0 = update({inc, 20}, C0, id1),
	S1 = update({dec, 12}, S0, id1),
	S2 = update({inc, 10}, S1, id2),
	S3 = update({dec, 3}, S2, id3),
	S4 = update(inc, S3, id4),
	S5 = update(inc, S4, id1),
	S6 = update(dec, S5, id2),
	S7 = update(dec, S6, id3),
	?assertEqual([{id1, {20,12}}, {id2, {10,0}}, {id3, {0,3}}, {id4, {1,0}}], S4),
	?assertEqual([{id1, {21,12}}, {id2, {10,1}}, {id3, {0,4}}, {id4, {1,0}}], S7).

value_test() ->
	C1 = new(),
	S0 = update({inc, 30}, C1, id1),
	S1 = update({dec, 10}, S0, id1),
	S2 = update({inc, 23}, S1, id2),
	S3 = update({dec, 45}, S2, id2),
	S4 = update({inc, 10}, S3, id3),
	?assertEqual(0, value(C1)),
	?assertEqual(-2, value(S3)),
	?assertEqual(8, value(S4)).

compare_test() ->
	C1 = new(),
	S0 = update(inc, C1, id1),
	S1 = update({inc, 6}, S0, id2),
	S2 = update({dec, 6}, S1, id2),
	S3 = update({inc, 3}, S2, id1),
	S4 = update({dec, 5}, S3, id1),
	?assert(compare(C1, C1)),
	?assert(compare(S2, S4)),
	?assertNot(compare(S4, S2)),
	?assertNot(compare(C1, S2)).

merge_test() ->
	C1 = new(),
	S0 = update({inc, 20}, C1, id1),
	S1 = update({dec, 15}, S0, id1),
	S2 = update(inc, S1, id1),
	C2 = new(),
	T0 = update({inc, 30}, C2, id2),
	T1 = update({dec, 8}, T0, id2),
	?assertEqual([], merge(C1, C2)),
	?assertEqual([{id1, {21, 15}}], merge(S1, S2)),
	?assertEqual([{id1, {20, 15}}, {id2, {30,8}}], merge(S1, T1)).

full_test() ->
	C1 = new(),
	C2 = update({inc, 3}, C1, id1),
	C3 = update({dec, 2}, C2, id2),
	C4 = new(),
	C5 = update({dec, 2}, C4, id1),
	C6 = update({inc, 5}, C5, id2),
	S0 = update(inc, C3, id2),
	S1 = update(dec, C6, id2),
	S2 = merge(S0, S1),
	?assertEqual([{id1, {3,2}}, {id2, {5,2}}], S2),
	?assertNot(compare(C1, C2)),
	?assertEqual(4, value(S2)).