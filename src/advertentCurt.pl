%% Advertent Curt. Here to answer your questions.
% Aleksandar Dimitrov
% based on Helpful Curt

:- module(curt,[curt/0,infix/0,prefix/0]).

:- use_module(callInference,[callTP/3,
                             callTPandMB/6]).

:- use_module(readLine,[readLine/1]).

:- use_module(comsemPredicates,[infix/0,
                                prefix/0,
                                memberList/2,
                                compose/3,
				selectFromList/3,
				printRepresentations/1]).

:- use_module(or,[disjunk/2]).

:- use_module(kellerStorage,[kellerStorage/2]).

:- use_module(modelChecker2,[satisfy/4]).

:- use_module(backgroundKnowledge,[backgroundKnowledge/2]).

:- use_module(elimEquivReadings,[elimEquivReadings/2]).

:- use_module(curtPredicates,[curtHelp/0,
                              curtOutput/1,
                              updateReadings/1,
                              updateModels/1,
                              updateHistory/1,
                              clearHistory/0,
                              list2string/2,
                              selectReadings/3]).


/*========================================================================
   Dynamic Predicates
========================================================================*/

:- dynamic history/1, readings/1, models/1, epistemic/1, doxastic/1.

history([]).
readings([]).
models([]).
epistemic([]).
doxastic([]).

% domain size for model builders
domainSize(15).

/*========================================================================
   Start Curt
========================================================================*/

curt:- 
   curtTalk(run).


/*========================================================================
   Control
========================================================================*/

curtTalk(quit).

curtTalk(run):-
   readLine(Input),
   curtUpdate(Input,CurtsMoves,State), 
   curtOutput(CurtsMoves),
   curtTalk(State).


/*========================================================================
   Update Curt's Information State
========================================================================*/

curtUpdate([],[clarify],run):- !.

curtUpdate([bye],[bye],quit):- !,
   %updateReadings([]),
   %updateModels([]),
   clearHistory.

curtUpdate([new],[],run):- !,
   updateReadings([]),
   updateModels([]),
   clearHistory.

curtUpdate([help],[],run):- !,
   curtHelp.

curtUpdate([infix],[],run):- !,
   infix.

curtUpdate([prefix],[],run):- !,
   prefix.

curtUpdate([select,X],[],run):-
   number(X),
   readings(R1),
   selectReadings(X,R1,R2), !,
   updateReadings(R2),
   models(M1), !,
   selectReadings(X,M1,M2),
   updateModels(M2).

curtUpdate([summary],[],run):-
   readings(Readings),
   elimEquivReadings(Readings,Unique),
   updateReadings(Unique),
   updateModels([]).

curtUpdate([knowledge],[],run):-
   readings(R),
   findall(K,(memberList(F,R),backgroundKnowledge(F,K)),L),
   printRepresentations(L).

curtUpdate([readings],[],run):- !,
   readings(R),
   printRepresentations(R).

curtUpdate([models],[],run):- !,
   models(M),
   printRepresentations(M).

curtUpdate([history],[],run):- !,
   history(H),
   printRepresentations(H).

curtUpdate(Input,Moves,run) :-
	kellerStorage(Input,Rs)
	, !
	, maplist(disjunk,Rs,Nested)
	, flatten(Nested,Readings)
	, updateHistory(Input)
	, interpretReadings(Readings,Model)
	,
	(
		\+ Model = []
		, updateModels(Model), !
		, Moves = [accept]
	;
		Moves = [reject]
	)
	.

curtUpdate(_,[noparse],run).

noEmpties([],[]).
noEmpties([[]|Xs],L) :- !, noEmpties(Xs,L).
noEmpties([X|Xs],[X|L]) :- noEmpties(Xs,L).

interpretReadings(Readings,Model) :-
	models(Old) , !
	, interpretReadings(Old,Readings,M)
	, noEmpties(M,Model)
	.

interpretReadings([],Readings,Model) :-
	maplist(curt:interpret([]),Readings,M)
	, noEmpties(M,Model)
	.


interpretReadings([(_Index,World)|Worlds],Readings,NewWorlds) :-
	maplist(curt:interpret(World),Readings,W1)
	,
	(
		\+ Worlds = []
		, interpretReadings(Worlds,Readings,Ws)
		, append(W1,Ws,NewWorlds)
	;
		Worlds = []
		, NewWorlds = W1
	)
	.

% Interpret one old reading (may be the empty list) wrt to one new reading
% and gives back an index/world pair
interpret(Old,New,World) :-
	(
		beAdvertent(Old,New), !
		, World = (_,Old)
	;
		getKnowledge(Old,New,BK,Reading)
		,
		(
			check(and(BK,New),'consistency',BBModel), !
			,
			(
				check(and(BK,not(New)),'informativity',_), !
				, BBModel = model(D,F)
				, World = (_,world(D,F,Reading))
			;
				format('~nFound uninformative reading. Dropping reading.',[])
				, World = (_,Old)
			)
		;
			format('~nFound inconsistency. Dropping world.',[])
			, World = []
		)
	)
	.

getKnowledge([],New,BackgroundKnowledge,New) :- 
	backgroundKnowledge(New,BackgroundKnowledge).

getKnowledge(world(_D,_F,Old),New,and(BackgroundKnowledge,Old),and(Old,New)) :- 
	backgroundKnowledge(and(Old,New),BackgroundKnowledge).

beAdvertent(world(_D,_F,Background),knowledge(X,P)) :-
	(
		P = que(_,[],Q)
		, !
		, backgroundKnowledge(and(Q,Background),BK2)
		,
		(
			\+ check(and(and(Background,BK2),not(Q)),'yes/ interrogative: informativity',_)
			, !
			, backgroundKnowledge(Q,BK)
			, check(and(Q,BK),'preparing world: consistency', model(D,F))
		;
			\+ check(and(and(Background,BK2),Q),'/no interrogative: informativity',_)
			, backgroundKnowledge(Q,BK)
			, check(and(not(Q),BK),'preparing world: consistency', model(D,F))
		)
		, World = (X,world(D,F,Q))
		, addEpistemic(World)
	;
		P = que(_Y,_Domain,_Body)
		, !
		, fail
	;
		backgroundKnowledge(and(P,Background),BK2)
		, \+ check(and(and(Background,BK2),not(P)),'embedded proposition: informativity',_)
		, backgroundKnowledge(P,BK)
		, check(and(P,BK),'preparing world: consistency', model(D,F))
		, World = (X,world(D,F,Q))
		, addEpistemic(World)
	)
	.

check(Formula,Job,Model) :-
	domainSize(DomainSize)
	, callTPandMB(not(Formula),Formula,DomainSize,Proof,Model,Engine)
	, format('~nMessage (~p checking): ~p found a result.',[Job,Engine])
	, \+ Proof=proof, Model=model([_|_],_)
	.

addEpistemic(World) :-
	retract(epistemic(Model))
	, append(Model,[World],New)
	, assert(epistemic(New))
	.

addDoxastic(World) :-
	retract(doxastic(Model))
	, append(Model,[World],New)
	, assert(doxastic(New))
	.

/*========================================================================
   Combine New Utterances with History
   TODO: add a call to the summary command
========================================================================*/

combine(New,New):-
   readings([]).

combine(Readings,Updated):-
   readings([Old|_]),
   findall(and(Old,New),memberList(New,Readings),Updated).


/*========================================================================
    Answer Questions
========================================================================*/

answerQuestion(que(X,R,S),Models,Moves):-
   (
      Models=[Model|_],
      satisfy(some(X,and(R,S)),Model,[],Result), 
      \+ Result=undef,
      !,     
      findall(A,satisfy(and(R,S),Model,[g(X,A)],pos),Answers),
      realiseAnswer(Answers,que(X,R,S),Model,String),
      Moves=[sensible_question,answer(String)]
   ;
      Moves=[unknown_answer]
   ).


/*========================================================================
    Realise all answers
========================================================================*/

realiseAnswer([],_,_,'none').

realiseAnswer([Value],Q,Model,String):-
   realiseString(Q,Value,Model,String).

realiseAnswer([Value1,Value2|Values],Q,Model,String):-
   realiseString(Q,Value1,Model,String1),
   realiseAnswer([Value2|Values],Q,Model,String2),
   list2string([String1,and,String2],String).


/*========================================================================
    Realise a single answer
========================================================================*/

realiseString(que(X,R,S),Value,Model,String):-
   kellerStorage:lexEntry(pn,[symbol:Symbol,syntax:Answer|_]),
   satisfy(eq(Y,Symbol),Model,[g(Y,Value)],pos), !,
   checkAnswer(some(X,and(eq(X,Symbol),and(R,S))),Proof),
   (
      Proof=proof, !,
      list2string(Answer,String)
   ;
      list2string([maybe|Answer],String)
   ).

realiseString(que(X,R,S),Value,Model,String):-
   kellerStorage:lexEntry(noun,[symbol:Symbol,syntax:Answer|_]), 
   compose(Formula,Symbol,[X]),
   satisfy(Formula,Model,[g(X,Value)],pos), !,
   checkAnswer(some(X,and(Formula,and(R,S))),Proof),
   (
      Proof=proof, !,
      list2string([a|Answer],String)
   ;
      list2string([maybe,a|Answer],String)
   ).

realiseString(_,Value,_,Value).


/*========================================================================
   Answer Checking
========================================================================*/

checkAnswer(Answer,Proof):-
   readings([F|_]),
   backgroundKnowledge(F,BK),
   callTP(imp(and(F,BK),Answer),Proof,Engine),
   format('~nMessage (answer checking): ~p found result "~p".',[Engine,Proof]).


/*========================================================================
   Info
========================================================================*/

info:-
   format('~n> ---------------------------------------------------------- <',[]),
   format('~n> helpfulCurt.pl, by Patrick Blackburn and Johan Bos         <',[]),
   format('~n>                                                            <',[]),
   format('~n> ?- curt.                - start a dialogue with Curt       <',[]),
   format('~n>                                                            <',[]),
   format('~n> Type "help" to get more information about features         <',[]),
   format('~n> ---------------------------------------------------------- <',[]),
   format('~n~n',[]).



/*========================================================================
   Display info at start
========================================================================*/

:- info.

 
