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
	kellerStorage(Input,Readings)
	, !
	, updateHistory(Input)
	, interpretReadings(Readings,Model)
	, (
		\+ Model = []
		, updateModels(Model), !
		, Moves = [accept]
	;
		Moves = [reject]).

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
	maplist(curt:interpret((_,[])),Readings,M)
	, noEmpties(M,Model)
	.

interpretReadings([World|Worlds],Readings,NewWorlds) :-
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
interpret((Index,Old),New,World) :-
	(
		beAdvertent((Index,Old),New), !
		, World = (Index,Old)
	;
		getKnowledge(Old,New,BK,Reading) , (
			check(and(BK,New),'consistency',BBModel), !  , (
				check(and(BK,not(New)),'informativity',_), !
				, BBModel = model(D,F)
				, World = (Index,world(D,F,Reading))
			;
				format('~nFound uninformative reading. Dropping reading.',[])
				, World = (Index,Old)
			)
		;
			format('~nFound inconsistency. Dropping world.',[])
			, World = [])) .

getKnowledge([],New,BackgroundKnowledge,New) :- 
	backgroundKnowledge(New,BackgroundKnowledge).

getKnowledge(world(_D,_F,Old),New,and(BackgroundKnowledge,Old),and(Old,New)) :- 
	backgroundKnowledge(and(Old,New),BackgroundKnowledge).

getEpistemicBG(X,I,world(D,F,R)) :-
	epistemic(E), !
	, delete(E,(X,I,world(D,F,R)),Rest)
	, \+ Rest = E
	, retract(epistemic(_)), !
	, assert(epistemic(Rest))
	.

getDoxasticBG(X,I,world(D,F,R)) :-
	doxastic(E), !
	, delete(E,(X,I,world(D,F,R)),Rest)
	, \+ Rest = E
	, retract(doxastic(_)), !
	, assert(doxastic(Rest))
	.

%beAdvertent((Index,world(D,F,R)),que([],[],B)) :-
	%fail
	%.

checkPartitions(Reading,[X|Xs],F) :-
	(
		backgroundKnowledge(and(Reading,X),BK)
		, \+ check(and(and(Reading,BK),X),'~npartition checking: informativity',_), !
		, checkPartitions(Reading,Xs,F)
	;
		format('~nfound result: ~p', X)
		, F = X
	)
	.

beAdvertent((_Index,world(_D,F,R)),que(X,Domain,Body),Answer) :-
	findBuddies(F,Buddies)
	, maplist(or:formulate(X,and(Domain,Body)),Buddies, Formulae)
	, partition(Formulae,Parted)
	, checkPartitions(R,Parted,Answer)
	.

beAdvertent((Index,world(D,F,R)),que(X,Domain,Body)) :-
	beAdvertent((Index,world(D,F,R)),que(X,Domain,Body),_).

beAdvertent((Index,world(_,_,Background)),knowledge(X,que(_,alt,Q))) :-
	!, (
		getEpistemicBG(X,_,world(_,_,EBG))
		, !
		, BG = and(Q,EBG)
		, NBG = and(not(Q),EBG)
	;
		BG = Q
		, NBG = not(Q)
	)
	, backgroundKnowledge(and(BG,Background),BK2)
	, (
		\+ check(and(and(Background,BK2),not(BG)),'yes/ interrogative: informativity',_)
		, !
		, backgroundKnowledge(BG,BK)
		, check(and(BG,BK),'preparing world: consistency', model(D2,F2))
		, World = (X,Index,world(D2,F2,BG))
	;
		\+ check(and(and(Background,BK2),BG),'/no interrogative: informativity',_)
		, backgroundKnowledge(NBG,BK)
		, check(and(NBG,BK),'preparing world: consistency', model(D2,F2))
		, World = (X,Index,world(D2,F2,NBG))
	)
	, addEpistemic(World)
	.

beAdvertent((Index,world(D,F,Background)),knowledge(X,que(Y,Domain,Body))) :-
	! , beAdvertent((Index,world(D,F,Background)),que(Y,Domain,Body),Answer)
	, (
		getEpistemicBG(Y,_,world(_,_,EBG))
		, !
		, Q = and(Answer,EBG)
	;
		Q = Answer
	)
	, backgroundKnowledge(Q,BK)
	, check(and(Q,BK),'preparing world: consistency', model(D2,F2))
	, World = (X, Index,world(D2,F2,Q))
	, addEpistemic(World)
	.

beAdvertent((Index,world(_,_,Background)),knowledge(X,P)) :-
	(
		getEpistemicBG(X,_,world(_,_,EBG))
		, !
		, Q = and(P,EBG)
	;
		Q = P
	)
	, backgroundKnowledge(and(Q,Background),BK2)
	, \+ check(and(and(Background,BK2),not(Q)),'embedded proposition: informativity',_)
	, backgroundKnowledge(Q,BK)
	, check(and(Q,BK),'preparing world: consistency', model(D2,F2))
	, World = (X,Index,world(D2,F2,Q))
	, addEpistemic(World)
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
findBuddies([f(0,A,_)|Fs],[A|More]) :-
	!, findBuddies(Fs,More)
	.

findBuddies([],[]).

findBuddies([f(_,_,_)|Fs],Buddies) :-
	!, findBuddies(Fs,Buddies).

partition([L],[L, not(L)]).

partition([F1,F2],Ls):-
	partition([F1],Fs)
	, maplist(partition(F2),Fs,L)
	, !
	, flatten(L,Ls)
	.
partition([F1|Fs],Ls) :-
	partition(Fs,PF)
	, maplist(partition(F1),PF,L)
	, flatten(L,Ls)
	.

partition(T1,X,[and(X,T1), and(X,not(T1))]).

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

realiseString(que(X,R,S),Value,world(D,F,Reading),String):-
   kellerStorage:lexEntry(pn,[symbol:Symbol,syntax:Answer|_]),
   satisfy(eq(Y,Symbol),model(D,F),[g(Y,Value)],pos), !,
   (
      \+ checkAnswer(some(X,and(eq(X,Symbol),and(R,S))),Reading), !
      , list2string(Answer,String)
   ;
      list2string([maybe|Answer],String)
   ).

realiseString(que(X,R,S),Value,world(D,F,Reading),String):-
   kellerStorage:lexEntry(noun,[symbol:Symbol,syntax:Answer|_]), 
   compose(Formula,Symbol,[X]),
   satisfy(Formula,model(D,F),[g(X,Value)],pos), !,
   (
      \+ checkAnswer(some(X,and(Formula,and(R,S))),Reading), !
      , list2string([a|Answer],String)
   ;
      list2string([maybe,a|Answer],String)
   ).

realiseString(_,Value,_,Value).


/*========================================================================
   Answer Checking
========================================================================*/

checkAnswer(Answer,F):-
   backgroundKnowledge(F,BK),
   check(not(imp(and(F,BK),Answer)),'answer deduction: consistency checking',_)
   .


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

 
