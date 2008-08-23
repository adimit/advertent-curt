% or.pl
% takes a formula and gives back a list of possible formulas
% after eliminating disjunction
% Aleksandar Dimitrov

module(or,[disjunk/2]).

term(Sym,Args,Term) :-
	(
		is_list(Args), !, Term =.. [Sym|Args]
	;
		Term =.. [Sym|[Args]]
	)
	.

disjunk(X,[X]) :- (var(X); atom(X)) , ! .

disjunk(or(A,B),Formulas) :-
	disjunk(A,FA)
	, disjunk(B,FB)
	, !
	, append(FA,FB,Formulas)
	.

disjunk(Formula,Result) :-
	Formula =.. [Sym|Args]
	, maplist(disjunk,Args,DArgs)
	, args(DArgs,PDArgs)
	, !
	, maplist(term(Sym),PDArgs,Result)
	.


% args/2
% takes a list of lists and returns all permutations of each list's elements
args([],[[]]).

args([X],X).

args([X,Y],Perms) :- 
	args(X,Y,Perms)
	.

args([Xs,Ys|Zs],Perms) :-
	args(Xs,Ys,P)
	, args([P|Zs],Perms)
	.

% args/3 
% helper for args/2 - two lists (both of which may be nested)
% and returs all permutations on both lists
args([],_,[]).

args(As,Bs,Lists) :- 
	As = [X|Xs]
	, args(Xs,Bs,More)
	, maplist(pairs(X),Bs,New)
	, append(New,More,Lists)
	.

pairs(X,Y,R) :-
	(
		(
			is_list(X),
			(
				is_list(Y), append(X,Y,R)
			;
				append(X,[Y],R)
			)
		;
			is_list(Y), append([X],Y,R)
		)
	;
		R = [X,Y]
	)
	.
