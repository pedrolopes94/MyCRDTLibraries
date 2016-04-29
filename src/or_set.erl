%% @author Pedro Lopes
%% @doc @todo Add description to or_set.
-module(or_set).
-export([new/0, update/3, value/2, lookup/2, merge/2]).
-include_lib("eunit/include/eunit.hrl").

%% The idea is to represent an OR-Set with an ordered map.
%% Each element of the ordered map has a pair {K, V} where K is a key and V is a value.
%% Each key is unique and represents an element; its value is a list of unique tags of the element.
%% If S is the of those pairs, then:
%% S = [{E1, [E1Tag1, E1Tag2, ...]}, {E2, [E2Tag1, E2Tag2, ...]}, ...],
%% where Ei is an element;
%% and EiTagj is an unique tag of element Ei.


%% new/0 function: returns an empty set of elements.
new() -> orddict:new().

%% update/2 function: adds or removes an element of the set.
update(add, Element, Set) ->
	add_element(Element, Set);
update(remove, Element, Set) ->
	remove_element(Element, Set).

add_element(Element, Set) ->
	Tag = crypto:strong_rand_bytes(20),
	case lookup(Element, Set) of
		true -> orddict:append(Element, Tag, Set);
		false -> orddict:store(Element, [Tag], Set)
	end.

remove_element(Element, Set) ->
	R = orddict:filter(fun (Key, _Value) -> Key =:= Element end, Set),
	orddict:erase(Element, Set),
	R.

%% value/2 function: returns an element with its associated list of tags, if the element exists.
%% If the element doesn't exist, an empty set is returned.
value(Element, Set) ->
	case orddict:find(Element, Set) of
		{ok, Tags} -> {Element, Tags};
		error -> {Element, orddict:new()}
	end.

%% lookup/2 function: checks if an element belongs to a set.
lookup(Element, Set) -> orddict:is_key(Element, Set).

%% merge/2 function: merges two OR-Sets
merge(Set1, Set2) ->
	orddict:merge(fun merge_tags/3, Set1, Set2).

merge_tags(_, Tag1, Tag2) ->
	lists:append(Tag1, Tag2).


%% ________ EUnit Tests ________
new_test() ->
	?assertEqual([], new()).

add_element_test() ->
	S1 = new(),
	S2 = update(add, obj1, S1),
	S3 = update(add, obj2, S2),
	S4 = update(add, obj1, S3),
	?assertEqual([{obj1, [0,2]}, {obj2, [1]}], S4).