%% A collection of functional predicates.
%
% This is mostly following Naish 1995
%
% Type signatures are given in comments, prefixed with ::
%
% Aleksandar Dimitrov

:- module(functionalPredicates,
	[filter/3
	, converse/4
	, compose/4
	, map/3
	, increment/3
	, foldr/4]).

% filter/3
% returns elements in list for which P succeeds
%
% :: (a -> Boolean) -> [a] -> [a]
filter(_, []      , []).
filter(P, [A0|As0], As) :-
	(call(P, A0) ->
		As = [A0|As1]
	;
		As = As1
	),
	filter(P, As0, As1).

% foldr/4
% folds lists through functions (left-to-right)
% NOTE that this only supports uncurried results for F
%
% :: (a -> b -> b) -> b -> [a] -> b
foldr(_, B, []    , B).
foldr(F, B, [A|As], R) :- 
	foldr(F, B, As, R1),
	call(F, A, R1, R).

% map/3
% maps a list through a given predicate to another list
% NOTE that this only supports uncurried results for F
%
% :: (a -> b) -> [a] -> [b]
map(_, []      , []    ).
map(F, [A0|As0], [A|As]) :-
	call(F, A0, A),
	map(F, As0, As).

% compose/4
% functional composition
%
% :: (b -> c) -> (a -> b) -> a -> c
compose(F, G, X, FGX) :-
	call(G, X, GX),
	call(F, GX, FGX).

% converse/4
% reverse the order of an application
%
% :: (a -> a -> b) -> a -> a -> b
converse(F, X, Y, FYX) :-
	call(F, Y, X, FYX).

% increment/3
% Increment a number
% 
% :: (Number a) => a -> a -> a
increment(_, X, Y) :-
	plus(1, X, Y).
