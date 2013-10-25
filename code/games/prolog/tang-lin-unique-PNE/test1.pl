/*
  Prolog code used to generate results in:

  Pingzhong Tang and Fangzhen Lin
  Discovering theorems in game theory: two-person games with unique pure Nash equilibrium payoffs
  Artificial Intelligence 175.14–15 (2011), pp. 2010–2020

  See file LICENSE for usage conditions/restrictions.
*/

:-[library(lists)].
:- style_check(-singleton).
:- style_check(-discontiguous).
run(M,N) :- 
    length(M,M1), length(N,N1),
    string_concat('model-', M1,Out1), 
    string_concat(Out1, 'x',Out2), 
    string_concat(Out2, N1,Out3), 
    string_to_atom(Out3,Outfile),
    open(Outfile,write,OF,[type(binary),alias(outfile)]), 
    generate_product_set(M,N,S),
    generate_game(S,Out),
    write(outfile,Out),
    nl(outfile),
    fail.
run(M,N):-
	close(outfile). 
/* run([a,b],[1,2],TA). */


/*
run(M,N,Out) :-
	generate_product_set(M,N,S),
	generate_preference(S,[],Out). [[[[1, a], [2, a], [3, a]], [[1, b], [2, b], [3, b]], [[1, c], [2, c], [3, c]]], [[[1, a], [1, b], [1, c]], [[2, a], [2, b], [2, c]], [[3, a], [3, b], [3|...]]]]
*/

/* generate the product set of the action sorts */ 
generate_product_set(M,N,S) :-
	findall([A,B],member_of2(A,B,M,N),S).

member_of2(A,B,C,D) :-
	member(A,C),
	member(B,D).
/* set operations */ 
one_non_empty_subset(Xs,Ys) :-
    possible_subset(Xs,Ys),
    Xs \== [].

possible_subset([],[]).
possible_subset(Xs,[_|Ys]) :- 
    possible_subset(Xs,Ys).
possible_subset([Y|Xs],[Y|Ys]) :- 
    possible_subset(Xs,Ys).

conc([],List,List).
conc([X|L1],L2,[X|List]) :-
	conc(L1,L2,List).
/* insert X to the last the Last1 and return this list as List2 */
insert_last(X,List1,List2):-
	conc(List1,[X],List2).
	
/* generate_preference, given the product set, return the hierachical structure preference */
generate_preference([],X,X). 
/* the first argument is the input set, the second is the middle input, and X is final output */
generate_preference(S,M,Out) :-
	one_non_empty_subset(Sub,S),
	delete_subset(S,Sub,S1),
	insert_last(Sub,M,M1),
	generate_preference(S1,M1,Out).


generate_game(S,[P1,P2]):-
	generate_preference(S,[],P1),
	generate_preference(S,[],P2).

/* episode for generating the strict preference game */

generate_first_dimension(M,N,S,P1):-
	nth1(1,M,X),
	nth1(1,N,Y),
	delete_item([X,Y],S,S1),
	permutation(S1,S2),
	conc([[X,Y]],S2,P1).
generate_second_dimension(M,N,S,P2):-
	permutation(S,P2).
generate_strict_model(M,N,[P1,P2]):-
	generate_product_set(M,N,S),
	generate_first_dimension(M,N,S,P1),
	generate_second_dimension(M,N,S,P2).
	
/* delete_subset: delete a non-empty subset from the original list, if the second argument is not the subset of the first argument, then list the differences */

delete_subset(S,[],S).
delete_subset([],_,[]).
delete_subset([X|Set1],Set2,D) :-
	member(X,Set2),!,                       /* cut */
	delete_subset(Set1,Set2,D).
delete_subset([X|Set1],Set2,[X|D]):-
	delete_subset(Set1,Set2,D).

/* delete a item from a list */
delete_item(X,[X|Tail],Tail).
delete_item(X,[Y|Tail],[Y|Tail1]):-
	delete_item(X,Tail,Tail1).

/* //////////////////////////////////////////////////////////////////////////////////////////////////////////// */
/* to test the satisfication relationship of atomic formular p1 and p2. */

:-op(500,xfy,/\).
:-op(500,xfy,\/).
:-op(900,fy,~).
:-op(1050,xfx,->).
:-op(500,xfx,<->).
:-op(400,xfx,#). /* exist */
:-op(400,xfx,$). /* forall */
:-op(400,xfx,@). /* nash equilibra */

/* set operation */

/* test the membership version 3, test whether A is the element of the elements of List and return the number of element it belongs to: Y. Eg: 
member_of3(A,[[[2, b]], [[2, a]], [[1, b]], [[1, a]]],1,Y).*/

member_of3(A,[Head|Tail],X,X):-
    member(A,Head).
member_of3(A,[Head|Tail],X,Y):-
    Z is X+1,
    member_of3(A,Tail,Z,Y).

/* satisfication relationship of atomic formular under model M 
satisfy(p2(1, a, 1, b),[1,2],[a,b],[[[2, b], [2, a], [1, b], [1, a]], [[2, b], [2, a], [1, b], [1, a]]]).
*/

/* !!!!!!be careful of this version of satisfication !!!!!!!!!!!!!!! the models are different!!!!!*/

satisfy(p1(A1,B1,A2,B2),M,N,[Head|Tail]):- /* head is the preference of p1 and tail is that of p2 */ 
    nth1(X1,Head,[A1,B1]),
    nth1(X2,Head,[A2,B2]),
    X2>=X1.
satisfy(p2(A1,B1,A2,B2),M,N,[Head|[Tail|Tail1]]):- /* head is the preference of p1 and tail is that of p2 */ 
    nth1(X1,Tail,[A1,B1]),
    nth1(X2,Tail,[A2,B2]),
    X2>=X1.
    

/* and */
satisfy(A/\B,M,N,Mo):-
    satisfy(A,M,N,Mo),satisfy(B,M,N,Mo).

/* or */
satisfy(A\/B,M,N,Mo):-
    satisfy(A,M,N,Mo).
satisfy(A\/B,M,N,Mo):-
    satisfy(B,M,N,Mo).

/* not */
satisfy(~A,M,N,Mo):-
    \+ (satisfy(A,M,N,Mo)).

/* imply */
satisfy(A->B,M,N,Mo):-
    satisfy((~(A))\/B,M,N,Mo).

/* equivalent */
satisfy(A<->B,M,N,Mo):-
    satisfy(A->B,M,N,Mo),
    satisfy(B->A,M,N,Mo).

/* exist, I implement this operator in a strange way [X1,X2,...]#p1(X1,X2,...), the intuitive meaning is very obvious */ 

satisfy(X#A,M,N,Mo):-
    object(X,M,N),
    satisfy(A,M,N,Mo),
    	!.


/*test whether X is the object of the model <M,N,Mo> */
object([],M,N).
object([Head|[]],M,N):-
    member(Head,M).
object([Head|[]],M,N):-
    member(Head,N).
object([Head|[Head1|Tail1]],M,N):-
    member(Head,M),
    member(Head1,N),
    object(Tail1,M,N).
    
/* forall */

satisfy(X$A,M,N,Mo):-
    	\+ (object(X,M,N),
   	satisfy(X#(~(A)),M,N,Mo)).
/*
satisfy(X$A,M,N,Mo):-
	object(X,M,N).
*/	
/* ne */    
satisfy(X@Y,M,N,Mo):-
    member(X,M),
    member(Y,N),
    satisfy(~(([U,V])#((p1(U,Y,X,Y)/\(~(p1(X,Y,U,Y))))\/(p2(X,V,X,Y)/\(~(p2(X,Y,X,V)))))),M,N,Mo). 

/* W2
[X1,Y1,X2,Y2]$(((X1@Y1)/\(X2@Y2))->((p1(X1,Y1,X2,Y2)/\p1(X2,Y2,X1,Y1))/\(p2(X1,Y1,X2,Y2)/\p2(X2,Y2,X1,Y1))))
 

satisfy([X1,Y1,X2,Y2]$(((X1@Y1)/\(X2@Y2))->((p1(X1,Y1,X2,Y2)/\p1(X2,Y2,X1,Y1))/\(p2(X1,Y1,X2,Y2)/\p2(X2,Y2,X1,Y1)))),[1,2],[a,b],[[[[2, b]], [[2, a]], [[1, b]], [[1, a]]], [[[2, b]], [[2, a]], [[1, b]], [[1, a]]]]).

satisfy([X1,Y1,X2,Y2]$(((X1@Y1)/\(X2@Y2))->((p1(X1,Y1,X2,Y2)/\p1(X2,Y2,X1,Y1))/\(p2(X1,Y1,X2,Y2)/\p2(X2,Y2,X1,Y1)))),[1,2],[a,b],[[[[A1, A2]], [[A3, A4]], [[A5, A6]], [[A7, A8]]],[[[A9,A10]], [[A11,A12]], [[A13,A14]], [[A15,A16]]]])/\object([A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16],[1,2],[a,b]).
*/


/* ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////  */

    
    


/* 
first step: for all the models that generated by generate_game, check whether they can be satisfied by ~(W2),keep those that can be satisfied and assert them into the database
*/

check1(M,N):-
	/*
	generate_product_set(M,N,S),
	generate_game(S,Model),
	*/
	generate_strict_model(M,N,Model), 
	filter(Model,~([X1,Y1,X2,Y2]$(((X1@Y1)/\(X2@Y2))->((p1(X1,Y1,X2,Y2)/\p1(X2,Y2,X1,Y1))/\(p2(X1,Y1,X2,Y2)/\p2(X2,Y2,X1,Y1))))),M,N),/* Formular here is ~(W2) */
	assert(model(Model)),
	fail.
check1(M,N):- !.

/* Succeed when Model is satisfied by the Formular */
filter(Model,Formular,M,N):-
	satisfy(Formular,M,N,Model).
/*
test(X,Y,p1(S)/\p2(T)):-
	member(S,X),
	member(T,Y).
*/
/* this partition provides a non-order partition of the first argument */
partition([],X,X).
partition(List,Middle,Set):-
	one_non_empty_subset(Sub,List),
	delete_subset(List,Sub,List1),
	union([Sub],Middle,Mid),
	sort(Mid,Middle1),
	partition(List1,Middle1,Set).	
/* ///////////////////////////////////////////////////////////////////////// */
/* construct the formular based on L1,L2 */
/* set operation */
/* delete_n: delete the nth element of the list */
delete_n(N,List1,List2):-
	conc(L1,[X|L2],List1),
	length(L1,M),
	N is M+1,
	conc(L1,L2,List2).

/* insert_n: insert the element to the nth place of the list */
insert_n(N,X,List1,List2):-
	conc(L1,L2,List1),
	length(L1,L),
	N is L+1,
	conc(L1,[X|L2],List2).

/* replace the equal value in the parameters list */
replace(List,[],List).
replace(List,[[Head|[]]|Tail],List1):-
	replace(List,Tail,List1).
replace(List,[[Head|Tail1]|Tail],List1):-
	Tail1 \== [],
	deal_with(List,[Head|Tail1],Temp),
	replace(Temp,Tail,List1).

deal_with(List,[Head|[]],List).
deal_with(List,[Head|[Head1|Tail]],List1):-
	nth1(Index,[1,2,3,4,5,6,7,8],Head1),
	nth1(Index1,[1,2,3,4,5,6,7,8],Head),
	nth1(Index1,List,Element),
	delete_n(Index,List,List2),
	insert_n(Index,Element,List2,List3),
	deal_with(List3,[Head|Tail],List1).

/* the following test predicate generate all the formulas */

test(Listx,Listy,F):-
	/* abolish(partx,1), */
	assert(partx([])),
	partition([1,2,3,4],[],X),
	\+ partx(X),
	assert(partx(X)),
	replace(Listx,X,Listx1),
	abolish(party,1),
	assert(party([])),
	partition([1,2,3,4],[],Y),
	\+ party(Y),
	assert(party(Y)),
	replace(Listy,Y,Listy1),
	construct(Listx1,Listy1,F).

/* ////////////////////////////////////////////// */

	
/* check2([1,2],[a,b],[X1,X2,X3,X4],[Y1,Y2,Y3,Y4]). */	
check2(M,N,Listx,Listy):-
	length(M,M1), length(N,N1),
	string_concat('game-', M1,Out1), 
	string_concat(Out1, 'x',Out2), 
	string_concat(Out2, N1,Out3), 
	string_to_atom(Out3,Outfile),
    	open(Outfile,write,OF,[alias(outfile)]),
	check1(M,N), /* all the models are filtered and are asserted into the database 			*/
	generate_all_models(M,N),
	test(Listx,Listy,F), 
	\+ (model(Mo),satisfy(F,M,N,Mo)),
	/* mod(X),satisfy(F,M,N,X), */
	satisfied_by_some(F,M,N),
	\+ (model(Mo),satisfy(F,M,N,Mo)), 
	satisfied_by_some(F,M,N),
	write(outfile,F),
	nl(outfile), 
	fail.
check2(M,N,Listx,Listy):-
	close(outfile).	
	
/* 	first, generate all the model and insert into database;
	second,generate a formular and test whether it can be satisfied by all the models in the database,if it can not, then assert it into database;
	third,delete those models that can not be satisfied by not( W2);
	finally,check the formulars remaining with the models remaining.
*/
/* check3([1,2],[a,b],[X1,X2,X3,X4],[Y1,Y2,Y3,Y4]). */
check3(M,N,Listx,Listy):-
	length(M,M1), length(N,N1),
	string_concat('game-', M1,Out1), 
	string_concat(Out1, 'x',Out2), 
	string_concat(Out2, N1,Out3), 
	string_to_atom(Out3,Outfile),
    	open(Outfile,write,OF,[alias(outfile)]),
	generate_all_models(M,N),
	keep_useful(M,N,Listx,Listy),
	delete_model(M,N),
	retract(formular(F)),
	\+ (model(X),satisfy(F,M,N,X)),
	write(outfile,F),
	nl(outfile),
	fail.
check3(M,N,Listx,Listy):- 
	close(outfile).
	
/* generate all models and assert into database */	
generate_all_models(M,N):-
	/*
	generate_product_set(M,N,S),
	generate_game(S,Model),
	*/
	generate_strict_model(M,N,Model),
	assert(mod(Model)),
	fail.
generate_all_models(M,N):- !.

keep_useful(M,N,Listx,Listy):-
	/* test(Listx,Listy,F), */
	construct(Listx,Listy,F),
	assert(formular(F)),
	\+ (mod(X),satisfy(F,M,N,X)),
	retract(formular(T)),
	fail.
keep_useful(M,N,Listx,Listy):- !.

delete_model(M,N):-
	retract(mod(X)),
	satisfy(~([X1,Y1,X2,Y2]$(((X1@Y1)/\(X2@Y2))->((p1(X1,Y1,X2,Y2)/\p1(X2,Y2,X1,Y1))/\(p2(X1,Y1,X2,Y2)/\p2(X2,Y2,X1,Y1))))),M,N,X),
	assert(model(X)),
	fail.
delete_model(M,N):-
	!.

/* /////////////////////////////////////////////////////////////////////////// */
/* check4 */
/* /////////////////////////////////////////////////////////////////////////// */
/* hierachical formular generator for testing formulas */
/* the framework */
/* ordered partition to reduce duplication */
generate_sub_partition(List1,List2,List1,List4):-
	one_non_empty_subset([Head|[Tail|[]]],List2),
	length([Head|[Tail|[]]],2),
	length(Head,1),
	length(Tail,1),
	delete_subset(List2,[Head|[Tail|[]]],List),
	flatten([Head|[Tail|[]]],Sub),
	union([Sub],List,Temp),
	sort(Temp,List4).
generate_sub_partition(List1,List2,List1,List4):-
	one_non_empty_subset([Head|[Tail|[]]],List2),
	length([Head|[Tail|[]]],2),
	length(Head,1),
	length(Tail,Y),
	Y>1,
	nth1(M,List2,Head),
	nth1(N,List2,Tail),
	M>N,
	delete_subset(List2,[Head|[Tail|[]]],List),
	flatten([Head|[Tail|[]]],Sub),
	union([Sub],List,Temp),
	sort(Temp,List4).
generate_sub_partition(List1,List2,List1,List4):-
	one_non_empty_subset([Head|[Tail|[]]],List2),
	length([Head|[Tail|[]]],2),
	length(Head,X),
	length(Tail,1),
	X>1,
	nth1(M,List2,Head),
	nth1(N,List2,Tail),
	N>M,
	delete_subset(List2,[Head|[Tail|[]]],List),
	flatten([Head|[Tail|[]]],Sub),
	union([Sub],List,Temp),
	sort(Temp,List4).
generate_sub_partition(List1,List2,List3,List2):-
	one_non_empty_subset([Head|[Tail|[]]],List1),
	length([Head|[Tail|[]]],2),
	length(Head,1),
	length(Tail,1),
	delete_subset(List1,[Head|[Tail|[]]],List),
	flatten([Head|[Tail|[]]],Sub),
	union([Sub],List,Temp),
	sort(Temp,List3).
generate_sub_partition(List1,List2,List3,List2):-
	one_non_empty_subset([Head|[Tail|[]]],List1),
	length([Head|[Tail|[]]],2),
	length(Head,1),
	length(Tail,Y),
	Y>1,
	nth1(M,List1,Head),
	nth1(N,List1,Tail),
	M>N,
	delete_subset(List1,[Head|[Tail|[]]],List),
	flatten([Head|[Tail|[]]],Sub),
	union([Sub],List,Temp),
	sort(Temp,List3).
generate_sub_partition(List1,List2,List3,List2):-
	one_non_empty_subset([Head|[Tail|[]]],List1),
	length([Head|[Tail|[]]],2),
	length(Head,X),
	length(Tail,1),
	X>1,
	nth1(M,List1,Head),
	nth1(N,List1,Tail),
	N>M,
	delete_subset(List1,[Head|[Tail|[]]],List),
	flatten([Head|[Tail|[]]],Sub),
	union([Sub],List,Temp),
	sort(Temp,List3).

/* the follow is the version of generate_sub_partition with 8 parameters */
generate_sub_partition(List1,List2,List3,List4,List5,List6,List3,List4):-
	generate_sub_partition(List1,List2,List5,List6).
generate_sub_partition(List1,List2,List3,List4,List1,List2,List5,List6):-
	generate_sub_partition(List3,List4,List5,List6).
/* like level_generator */
generator(M,N,Listx1,Listx2,Listy1,Listy2,List1,List2,List3,List4):-
	generate_sub_partition(List1,List2,List3,List4,List5,List6,List7,List8),	
	partition_formular(Listx1,Listx2,Listy1,Listy2,List5,List6,List7,List8,Formular),
	satisfied_some(M,N,Formular),
	generator(M,N,Listx1,Listx2,Listy1,Listy2,List5,List6,List7,List8).
generator(M,N,Listx1,Listx2,Listy1,Listy2,List1,List2,List3,List4):-
	\+ (generate_sub_partition(List1,List2,List3,List4,List5,List6,List7,List8),	
	partition_formular(Listx1,Listx2,Listy1,Listy2,List5,List6,List7,List8,Formular),
	satisfied_some(M,N,Formular)),
	sort_element(List1,L1),
	sort_element(List2,L2),
	sort_element(List3,L3),
	sort_element(List4,L4),
	\+ (part(L1,L2,L3,L4)),
	/* 
	partition_formular(Listx1,Listx2,Listy1,Listy2,List1,List2,List3,List4,Formular1), 
	*/
	assert(part(L1,L2,L3,L4)),
	write(outfile,part(L1,L2,L3,L4)),
	nl(outfile).

/* sort the element of the list */
sort_element([Head|Tail],[Head1|Tail1]):-
	sort(Head,Head1),
	sort_element(Tail,Tail1).
sort_element([],[]):- !. 	

/* partition_formular/3, convert partition to the corresponding formular */
partition_formular(Listx,Listy,List1,List2,Formular):-
	replace(Listx,List1,Listx1),
	replace(Listy,List2,Listy1),
	construct(Listx1,Listy1,Formular).
partition_formular(Listx1,Listx2,Listy1,Listy2,List1,List2,List3,List4,Formular):-
	replace(Listx1,List1,Listx11),
	replace(Listx2,List2,Listx22),
	replace(Listy1,List3,Listy11),
	replace(Listy2,List4,Listy22),
	construct(Listx11,Listx22,Listy11,Listy22,Formular).
satisfied_some(M,N,Formular):-
	\+ (model(Mo),satisfy(Formular,M,N,Mo)).
/* the main procedure */
/*  check4([1,2],[a,b],[X1,X2,X3,X4],[X5,X6,X7,X8],[Y1,Y2,Y3,Y4],[Y5,Y6,Y7,Y8]). */
check4(M,N,Listx1,Listx2,Listy1,Listy2):-
	length(M,M1), length(N,N1),
	string_concat('game-', M1,Out1), 
	string_concat(Out1, 'x',Out2), 
	string_concat(Out2, N1,Out3), 
	string_to_atom(Out3,Outfile),
    	open(Outfile,write,OF,[alias(outfile)]),
	check1(M,N),
	generate_all_models(M,N), 
	assert(part([],[],[],[])),
/* all the models are filtered and are asserted into the database */
	generator(M,N,Listx1,Listx2,Listy1,Listy2,[[1],[2],[3],[4]],[[1],[2],[3],[4]],[[1],[2],[3],[4]],[[1],[2],[3],[4]]),
	fail.

check4(M,N,Listx1,Listx2,Listy1,Listy2):-
	close(outfile).
/*
check5(M,N):-
	length(M,M1), length(N,N1),
	string_concat('game-', M1,Out1), 
	string_concat(Out1, 'x',Out2), 
	string_concat(Out2, N1,Out3), 
	string_to_atom(Out3,Outfile),
    	open(Outfile,write,OF,[alias(outfile)]),
	check4(M,N,[X1,X2,X3,X4],[X5,X6,X7,X8],[Y1,Y2,Y3,Y4],[Y5,Y6,Y7,Y8]), 
	part(L1,L2,L3,L4),
	write(outfile,part(L1,L2,L3,L4)),
	nl(outfile),
	fail.
check5(M,N):-
	close(outfile).
*/

/* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  */
/* new way to generate formulas and test them; then assert into database;
   so the formulas in the database are all satisfied by the requirement.
   find the most special formular and delete its parents, write that formular and
   do it recursively
*/

/* step 0 */
construct(Listx,Listy,[X1,Y1,X2,Y2,X3,Y3,X4,Y4]$(p1(X1,Y1,X2,Y2)/\p2(X3,Y3,X4,Y4))):-
	nth1(1,Listx,X1),
	nth1(2,Listx,X2),
	nth1(3,Listx,X3),
	nth1(4,Listx,X4),
	nth1(1,Listy,Y1),
	nth1(2,Listy,Y2),
	nth1(3,Listy,Y3),
	nth1(4,Listy,Y4).


/* step 1, generate all the partition of [1,2,3,4], and assert them into database */
generate_part :-
	assert(partition_4([])),
	/* assert(part_1([],[])), */
	partition([1,2,3,4],[],X),
	\+ (partition_4(X)),
	assert(partition_4(X)),
	fail.
generate_part :-
	retract(partition_4([])),
	!.

/* step 2, generate the formulas and assert them into database, before this, check 1 &generate_all_models */
/*  t2([1,2,3],[a,b],[X1,X2,X3,X4],[Y1,Y2,Y3,Y4]). */
generate_for1(Lx,Ly) :-
	partition_4(Lx),	
	partition_4(Ly).
	
generate_for2(Lx,Ly,Listx,Listy,F):-
	replace(Listx,Lx,Listx1),
	replace(Listy,Ly,Listy1),
	construct(Listx1,Listy1,F).

satisfied_by_some(F,M,N):-
	mod(X),
	satisfy(F,M,N,X),
	!.
/* assert those sufficient conditions into database as part_1(X,Y) */
t2(M,N,Listx,Listy):-
	generate_part,
	check1(M,N),
	generate_all_models(M,N),
	generate_for1(Lx,Ly),
	generate_for2(Lx,Ly,Listx,Listy,F),
	\+ (model(Mo),satisfy(F,M,N,Mo)), 
	satisfied_by_some(F,M,N), 
	assert(part_1(Lx,Ly)),
	fail.
t2(M,N,Listx,Listy):-
	!.

/* step 3, get rid of the redundancy by delete all the parents from the database */
/* step 3.1, count the number of equivalence subsets of Lx, and Ly */
count_subset1([],0):-
	!.
count_subset1([Head|Tail],M):-
	count_subset1(Tail,N),
	M is N+1.

count_subset(L1,L2,O):-
	count_subset1(L1,M),
	count_subset1(L2,N),
	O is M+N.

/* step 3.2, find the most special list, i.e, the list with the least number of subsets */
find_special(Listx,Listy):-
	X is 8,
	assert(temp(X)),
	assert(part_2([],[])),
	part_1(Lx,Ly),
	count_subset(Lx,Ly,M),
	temp(N),
	M<N,
	retract(temp(N)),
	retract(part_2(L1,L2)),
	assert(temp(M)),
	assert(part_2(Lx,Ly)),
	fail.
find_special(Listx,Listy):-
	retract(temp(N)),
	retract(part_2(Listx,Listy)),
	!.

/* step 3.3, is_parent1: the first argument is the parent (more general one) of the second argument */
is_parent1(List,List):-
	!.
is_parent1([],List):-
	!.
is_parent1([Head|Tail],Parent):-
	member(Elem,Parent),
	subset(Head,Elem),
	is_parent1(Tail,Parent).

is_parent(Listx,Listy,Lx,Ly):-
	is_parent1(Listx,Lx),
	is_parent1(Listy,Ly).

/* step 3.4, delete the most special element and all its parents, and write that formular, then do the above recursively */
delete_parent(Listx,Listy):-
	part_1(Lx,Ly),
	is_parent(Lx,Ly,Listx,Listy),	
	retract(part_1(Lx,Ly)),
	fail.
delete_parent(Listx,Listy):-
	\+ (part_3(Listx,Listy)),
	write(outfile,[Listx,Listy]),
	assert(part_3(Listx,Listy)),
	nl(outfile).

/* procedure_1([1,2],[a,b],[X1,X2,X3,X4],[Y1,Y2,Y3,Y4]). */
procedure_1(M,N,Listx,Listy):-
	length(M,M1), length(N,N1),
	string_concat('game-', M1,Out1), 
	string_concat(Out1, 'x',Out2), 
	string_concat(Out2, N1,Out3), 
	string_to_atom(Out3,Outfile),
    	open(Outfile,write,OF,[alias(outfile)]),
	t2(M,N,Listx,Listy),
	assert(part_3([],[])),
	part_1(X,Y),
	find_special(Lx,Ly),
	delete_parent(Lx,Ly),
	fail.
procedure_1(M,N,Listx,Listy):-
	close(outfile).

check5:-
	procedure_1([1,2],[a,b],[X1,X2,X3,X4],[Y1,Y2,Y3,Y4]).
/* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% */
/* the following are for the four literals cases */

construct(Listx,Listxx,Listy,Listyy,[X1,Y1,X2,Y2,X3,Y3,X4,Y4,X5,Y5,X6,Y6,X7,Y7,X8,Y8]$(((~p1(X1,Y1,X2,Y2))\/p(X3,Y3,X4,Y4))/\(p1(X5,Y5,X6,Y6)\/(~p2(X7,Y7,X8,Y8))))):-
	nth1(1,Listx,X1),
	nth1(2,Listx,X2),
	nth1(3,Listx,X3),
	nth1(4,Listx,X4),
	nth1(1,Listxx,X5),
	nth1(2,Listxx,X6),
	nth1(3,Listxx,X7),
	nth1(4,Listxx,X8),
	nth1(1,Listy,Y1),
	nth1(2,Listy,Y2),
	nth1(3,Listy,Y3),
	nth1(4,Listy,Y4),
	nth1(1,Listyy,Y5),
	nth1(2,Listyy,Y6),
	nth1(3,Listyy,Y7),
	nth1(4,Listyy,Y8).

generate_for1(Lx,Ly,Lx1,Ly1) :-
	partition_4(Lx),	
	partition_4(Ly),
	partition_4(Lx1),
	partition_4(Ly1).
	
generate_for2(Lx,Ly,Lx1,Ly1,Listx,Listy,Listxx,Listyy,F):-
	replace(Listx,Lx,Listx1),
	replace(Listy,Ly,Listy1),
	replace(Listxx,Lx1,Listx2),
	replace(Listyy,Ly1,Listy2),
	construct(Listx1,Listx2,Listy1,Listy2,F).
/* assert those sufficient conditions into database as part_1(X,Y) */
t2(M,N,Listx,Listxx,Listy,Listyy):-
	generate_part,
	retract(partition_4([])),
	check1(M,N),
	generate_all_models(M,N),
	generate_for1(Lx,Ly,Lx1,Ly1),
	generate_for2(Lx,Ly,Listx,Listy,F1),
	generate_for2(Lx1,Ly1,Listxx,Listyy,F2),
	satisfied_by_some(~(F1),M,N),
	satisfied_by_some(~(F2),M,N),
	generate_for2(Lx,Ly,Lx1,Ly1,Listx,Listy,Listxx,Listyy,F),
	satisfied_by_some(F,M,N), 
	\+ (model(Mo),satisfy(F,M,N,Mo)), 
	assert(part_1(Lx,Ly,Lx1,Ly1)),
	fail.
t2(M,N,Listx,Listxx,Listy,Listyy):-
	!.


count_subset(L1,L2,L3,L4,O):-
	count_subset1(L1,M),
	count_subset1(L2,N),
	count_subset1(L3,P),
	count_subset1(L4,Q),
	O is M+N+P+Q.

is_parent(Listx,Listy,Listxx,Listyy,Lx,Ly,Lx1,Ly1):-
	is_parent1(Listx,Lx),
	is_parent1(Listy,Ly),
	is_parent1(Listxx,Lx1),
	is_parent1(Listyy,Ly1).

delete_parent(Listx,Listy,Listxx,Listyy):-
	part_1(Lx,Ly,Lx1,Ly1),
	is_parent(Lx,Ly,Lx1,Ly1,Listx,Listy,Listxx,Listyy),	
	retract(part_1(Lx,Ly,Lx1,Ly1)),
	fail.
delete_parent(Listx,Listy,Listxx,Listyy):-
	\+ (part_3(Listx,Listy,Listxx,Listyy)),
	write(outfile,[Listx,Listy,Listxx,Listyy]),
	assert(part_3(Listx,Listy,Listxx,Listyy)),
	nl(outfile).

find_special(Listx,Listy,Listxx,Listyy):-
	X is 16,
	assert(temp(X)),
	assert(part_2([],[],[],[])),
	part_1(Lx,Ly,Lx1,Ly1),
	count_subset(Lx,Ly,Lx1,Ly1,M),
	temp(N),
	M<N,
	retract(temp(N)),
	retract(part_2(L1,L2,L3,L4)),
	assert(temp(M)),
	assert(part_2(Lx,Ly,Lx1,Ly1)),
	fail.
find_special(Listx,Listy,Listxx,Listyy):-
	retract(temp(N)),
	retract(part_2(Listx,Listy,Listxx,Listyy)),
	!.
procedure_2(M,N,Listx,Listy,Listxx,Listyy):-
	length(M,M1), length(N,N1),
	string_concat('game-', M1,Out1), 
	string_concat(Out1, 'x',Out2), 
	string_concat(Out2, N1,Out3), 
	string_to_atom(Out3,Outfile),
    	open(Outfile,write,OF,[alias(outfile)]),
	t2(M,N,Listx,Listxx,Listy,Listyy),
	assert(part_3([],[],[],[])),
	part_1(X,Y,S,T),
	find_special(Lx,Ly,Lx1,Ly1),
	delete_parent(Lx,Ly,Lx1,Ly1),
	fail.
procedure_2(M,N,Listx,Listy,Listxx,Listyy):-
	close(outfile).
check6 :-
	procedure_2([1,2],[a,b],[X1,X2,X3,X4],[Y1,Y2,Y3,Y4],[X5,X6,X7,X8],[Y5,Y6,Y7,Y8]).

/* output the game corresponding to the formular */
output_game(M,N,Lx,Ly,Listx,Listy):-
	length(M,M1), length(N,N1),
	string_concat('games-', M1,Out1), 
	string_concat(Out1, 'x',Out2), 
	string_concat(Out2, N1,Out3), 
	string_to_atom(Out3,Outfile),
    	open(Outfile,write,OF,[alias(outfile)]),
	generate_all_models(M,N),
	generate_for2(Lx,Ly,Listx,Listy,F),
	write(outfile,[Lx,Ly]),
	nl(outfile),	
	nl(outfile),
	mod(Mo),
	satisfy(F,M,N,Mo),
	write(outfile,Mo),
	nl(outfile),
	fail.
output_game(M,N,Lx,Ly,Listx,Listy):-
	close(outfile).

check7(Lx,Ly):-
	output_game([1,2],[a,b],Lx,Ly,[X1,X2,X3,X4],[Y1,Y2,Y3,Y4]).

/* check the guess */
test_condition(M,N):-
	length(M,M1), length(N,N1),
	string_concat('games-', M1,Out1), 
	string_concat(Out1, 'x',Out2), 
	string_concat(Out2, N1,Out3), 
	string_to_atom(Out3,Outfile),
    	open(Outfile,write,OF,[alias(outfile)]),
	/*
	generate_all_models(M,N),
	*/
	sc_game(M,N),
	mod(Mo),
	filter(Mo,[X1,Y1,X2,Y2]$(((X1@Y1)/\(X2@Y2))->((p1(X1,Y1,X2,Y2)/\p1(X2,Y2,X1,Y1))/\(p2(X1,Y1,X2,Y2)/\p2(X2,Y2,X1,Y1)))),M,N), /* at most one N.E */
	filter(Mo,~(([X]#([X1,Y]$(p1(X,Y,X1,Y))))\/([Y1]#([X2,Y2]$(p2(X2,Y1,X2,Y2))))),M,N), /* not trivial */
	generate_for2([[1, 3], [2, 4]], [[1, 2, 3, 4]],[[1, 2, 3, 4]], [[1, 3], [2, 4]],[X1,X2,X3,X4],[Y1,Y2,Y3,Y4],[X5,X6,X7,X8],[Y5,Y6,Y7,Y8],F),  
	filter(Mo,~(F),M,N), /* not sc */
	/*
	filter(Mo,~([X,Y]$(~(X@Y))),M,N), /* at least one N.E */
	*/
	/*
	generate_for2([[1, 2], [3, 4]], [[1, 4], [2, 3]],[X1,X2,X3,X4],[Y1,Y2,Y3,Y4],F1), /* condition 4 */
	generate_for2([[1, 4], [2, 3]], [[1], [2, 3, 4]],[X1,X2,X3,X4],[Y1,Y2,Y3,Y4],F2), /* condition 6 */
	filter(Mo,(F1)\/(F2),M,N),
	*/
	\+ (sc(Model),
	equivalent(Mo,Model,M,N)
	),
	write(outfile,Mo),
	nl(outfile),
	fail.
test_condition(M,N):-
	close(outfile),
	!.

check8 :-
	test_condition([1,2,3],[a,b,c]).
	
/* the episode whether two games are equivalent */
/*
equivalent_p1(G1,G2,M,N):-
	\+ (member(X1,M),
	member(X2,M),
	member(Y,N),
	satisfy(p1(X1,Y,X2,Y),M,N,G1),
	satisfy(~p1(X1,Y,X2,Y),M,N,G2)).

equivalent_p2(G1,G2,M,N):-
	\+ (member(Y1,N),
	member(Y2,N),
	member(X,N),
	satisfy(p2(X,Y1,X,Y2),M,N,G1),
	satisfy(~p2(X,Y1,X1,Y2),M,N,G2)).

equivalent(G1,G2,M,N):-
	equivalent_p1(G1,G2,M,N),
	equivalent_p1(G2,G1,M,N),
	equivalent_p2(G1,G2,M,N),
	equivalent_p2(G2,G1,M,N).
*/
/* find all strictly competitive games */
sc_game(M,N):-
	generate_all_models(M,N),
	mod(Mo),	
	generate_for2([[1, 3], [2, 4]], [[1, 2, 3, 4]],[[1, 2, 3, 4]], [[1, 3], [2, 4]],[X1,X2,X3,X4],[Y1,Y2,Y3,Y4],[X5,X6,X7,X8],[Y5,Y6,Y7,Y8],F),
	filter(Mo,F,M,N),
	assert(sc(Mo)),
	fail.
sc_game(M,N):-
	!.

/* remember to change the form in construct/4 */
/* [[1, 4], [2, 3]],[[1, 4],[ 2, 3]], [[1, 4],[ 2, 3]], [[1, 4], [2, 3]] */
/* [[1, 3], [2, 4]], [[1, 2, 3, 4]],[[1, 2, 3, 4]], [[1, 3], [2, 4]]    */	

/* generate partial games */	
/* for player one, generate preference according to fixed y */
/* generate the partial preference for player one */
generate_partial1(M,[],X,X):- !.
generate_partial1(M,[Head|Tail],X,Y):-
	findall([A,Head],member(A,M),S),
	insert_last(S,X,X1),
	generate_partial1(M,Tail,X1,Y).	

permute([],G,G):- !.
permute([Head|Tail],G,G1):-
	permutation(Head,S),
	insert_last(S,G,X),
	permute(Tail,X,G1).

generate_partial_p1(M,N,G):-
	generate_partial1(M,N,[],P),
	permute(P,[],G).

generate_partial2([],N,X,X):-!.
generate_partial2([Head|Tail],N,X,Y):-
	findall([Head,A],member(A,N),S),
	insert_last(S,X,X1),
	generate_partial2(Tail,N,X1,Y).

generate_partial_p2(M,N,G):-
	generate_partial2(M,N,[],P),
	permute(P,[],G).

generate_partial(M,N,[G1,G2]):-
	generate_partial_p1(M,N,G1),
	generate_partial_p2(M,N,G2).

/* ne notation for partial game */
find_candidate([],Temp,Temp):-!.
find_candidate([Head|Tail],Temp,Bag):-
	nth1(1,Head,X),
	insert_last(X,Temp,Temp1),
	find_candidate(Tail,Temp1,Bag).
has_ne([P1,P2]):-
	find_candidate(P1,[],Bag1),
	find_candidate(P2,[],Bag2),
	intersection(Bag1,Bag2,Set),
	Set \== [].
/* dominant notion for partial game */
dominant_p1([Head|[]]):-!.
dominant_p1([Head|[Head1|Tail]]):-
	nth1(1,Head,L1),
	nth1(1,L1,X),
	nth1(1,Head1,L2),
	nth1(1,L2,X),
	dominant_p1([Head1|Tail]).

dominant_p2([Head|[]]):-!.
dominant_p2([Head|[Head1|Tail]]):-
	nth1(1,Head,L1),
	nth1(2,L1,X),
	nth1(1,Head1,L2),
	nth1(2,L2,X),
	dominant_p2([Head1|Tail]).
not_dominant([P1,P2]):-
	\+(dominant_p1(P1)),
	\+(dominant_p2(p2)).
	


/* verify the new version of equivalent */
	
/* step one */
/* generate the game class, with the maximum row elements given in player one and maximum column element given in player two */
/* Fix each y, give the maximun position in x, for player one */
generate_class_p1(M,[],X,X):- !.
generate_class_p1(M,[Head|Tail],X,Y):-
	member(A,M),
	insert_last([A,Head],X,X1),
	generate_class_p1(M,Tail,X1,Y).

/* for player two */
generate_class_p2([],N,X,X):- !.
generate_class_p2([Head|Tail],N,X,Y):-
	member(A,N),
	insert_last([Head,A],X,X1),
	generate_class_p2(Tail,N,X1,Y).

/* both game */
generate_class(M,N,[G1,G2]):-
	generate_class_p1(M,N,[],G1),
	generate_class_p2(M,N,[],G2).

/* step two */
/* at most one ne, no ne, exactly one ne */
at_most_one_ne([Head,Tail]):-
	intersection(Head,Tail,[]),
	!.
at_most_one_ne([Head,Tail]):-
	intersection(Head,Tail,[X|[]]).

no_ne([Head,Tail]):-
	intersection(Head,Tail,[]).

exact_one_ne([Head,Tail]):-
	intersection(Head,Tail,[X|[]]),
	[X|[]] \==[].

exist_ne(List):-
	\+ (no_ne(List)).	
/* step three, non-independent */

independent_p1([[Head|[Head1|Tail1]],Tail]):-
	nth1(1,Head,X),
	nth1(1,Head1,X),
	independent_p1([[Head1|Tail1],Tail]).
independent_p1([[Head|[]],Tail]):-
	!.

independent_p2([Head,[Head1|[Head2|Tail]]]):-	
	nth1(2,Head1,X),
	nth1(2,Head2,X),
	independent_p2([Head,[Head2|Tail]]).
independent_p2([Head,[Head1|[]]]):-
	!.

non_independent(Game):-
	\+ (independent_p1(Game)),
	\+ (independent_p2(Game)).	

/* step 4, not equivalent to a strictly  competitive game */
/* conversion for player one, from class to partial game */
/* 4.1 generate the possible partial game for the class */
class_partial_p1([Head|Tail],Temp,P,M,N):-
	nth1(2,Head,Y),
	findall([X,Y],member(X,M),S),
	delete(S,Head,S1),
	permutation(S1,S2),
	append([Head],S2,S3),
	insert_last(S3,Temp,Temp1),
	class_partial_p1(Tail,Temp1,P,M,N).
class_partial_p1([],P,P,M,N):-
	!.
/* for player two */
class_partial_p2([Head|Tail],Temp,P,M,N):-
	nth1(1,Head,X),
	findall([X,Y],member(Y,N),S),
	delete(S,Head,S1),
	permutation(S1,S2),
	append([Head],S2,S3),
	insert_last(S3,Temp,Temp1),
	class_partial_p2(Tail,Temp1,P,M,N).
class_partial_p2([],P,P,M,N):-
	!.

class_partial([Head,Tail],[G1,G2],M,N):-
	class_partial_p1(Head,[],G1,M,N),
	class_partial_p2(Tail,[],G2,M,N).

/* 4.2. generate the graph from the partial game */
/* player one's partial preference */
partial_graph_p1([],Relation,Relation):-
	!.
partial_graph_p1([Head|Tail],Relation,Graph):-
	findall([A,B],(nth1(X,Head,A),nth1(1,Head,B),X>1),Gr),
	union(Relation,Gr,Relation1),
	partial_graph_p1(Tail,Relation1,Graph).
/* player two's partial preference */
partial_graph_p2([],Relation,Relation):-
	!.
partial_graph_p2([Head|Tail],Relation,Graph):-
	findall([A,B],(nth1(X,Head,A),nth1(1,Head,B),X>1),Gr),
	union(Relation,Gr,Relation1),
	partial_graph_p2(Tail,Relation1,Graph).

partial_graph([Head,Tail],Graph):-
	partial_graph_p1(Head,[],Graph1),
	partial_graph_p2(Tail,[],Graph2),
	union(Graph1,Graph2,Graph).
/* check loop */
graph_database([]):-
	!.
graph_database([Head|Tail]):-
	assert(edge(Head)),
	graph_database(Tail).
/*		
connect(A,B,1):-
	edge([A,B]),
	!.

connect(A,B,Y):-
	edge([A,C]),
	X is Y-1,
	connect(C,B,X).

exist_loop(M,N):-
	member(X,M),
	member(Y,N),
	connect([X,Y],[X,Y],9).

no_loop(M,N):-
	\+ (member(X,M),
	member(Y,N),
	member(L,[2,3,4,5,6,7,8,9]),
	connect([X,Y],[X,Y],L)).
*/
/*
bfs([]):-
	!.
bfs(List):-
	\+ (member(X,List),
	mark(X),
	assert(mark(X))),
	findall(B,(edge([A,B]),member(A,List)),List1)),
	bfs(List1).
*/	
/* another try visit*/	
visit(V):-
	retract(mark(V,C)),
	assert(mark(V,g)),
	edge([V,U]),
	mark(U,g),
	!.
visit(V):-
	retract(mark(V,C)),
	assert(mark(V,g)),
	edge([V,U]),
	mark(U,w),
	visit(U),
	!.
visit(V):-
	retract(mark(V,C)),
	assert(mark(V,b)),	
	fail.	
	
/* detect cycle */
find_node(M,N,List):-
	findall([A,B],(member(A,M),member(B,N)),List).

mark_white([]):- !.
mark_white([Head|Tail]):-
	assert(mark(Head,w)),
	mark_white(Tail).

cycle(M,N):-
	find_node(M,N,List),
	mark_white(List),
	member(V,List),
	mark(V,w),
	visit(V),
	!.	
no_cycle(M,N):-
	\+ (cycle(M,N)).

has_cycle(Class,M,N):-
	abolish(edge,1),
	abolish(mark,2),
	class_partial(Class,Partial,M,N),
	partial_graph(Partial,Graph),
	graph_database(Graph),
	cycle(M,N),
	!.
has_cycle_partial(Partial,M,N):-
	abolish(edge,1),
	abolish(mark,2),
	partial_graph(Partial,Graph),
	graph_database(Graph),
	cycle(M,N),
	!.
/* the follow is to deal with the supermodular case */

/* step 1, redo-satisfy for partial game */
satisfy_redo(p1(X1,Y,X2,Y),M,N,[P1,P2]):-
	member(List,P1),
	nth1(N1,List,[X1,Y]),
	nth1(N2,List,[X2,Y]),
	N2>=N1.
satisfy_redo(p2(X,Y1,X,Y2),M,N,[P1,P2]):-
	member(List,P2),
	nth1(N1,List,[X,Y1]),
	nth1(N2,List,[X,Y2]),
	N2>=N1. 
/*
satisfy_redo(join(X,Y,Z),M,N,List):-
	join(X,Y,Z).
satisfy_redo(meet(X,Y,Z),M,N,List):-
	meet(X,Y,Z).
satisfy_redo(lattice(X,Y),M,N,List):-
	lattice(X,Y).	
*/
satisfy_redo(great1(X,Y),M,N,List):-
	great1(X,Y).
satisfy_redo(great2(X,Y),M,N,List):-
	great2(X,Y).
/* and */
satisfy_redo(A/\B,M,N,Mo):-
    satisfy_redo(A,M,N,Mo),satisfy_redo(B,M,N,Mo).

/* or */
satisfy_redo(A\/B,M,N,Mo):-
    satisfy_redo(A,M,N,Mo).
satisfy_redo(A\/B,M,N,Mo):-
    satisfy_redo(B,M,N,Mo).

/* not */
satisfy_redo(~(A),M,N,Mo):-
    \+ (satisfy_redo(A,M,N,Mo)).

/* imply */
satisfy_redo(A->B,M,N,Mo):-
    satisfy_redo((~(A))\/B,M,N,Mo).

/* equivalent */
satisfy_redo(A<->B,M,N,Mo):-
    satisfy_redo(A->B,M,N,Mo),
    satisfy_redo(B->A,M,N,Mo).

/* exist, I implement this operator in a strange way [X1,X2,...]#p1(X1,X2,...), the intuitive meaning is very obvious */ 

satisfy_redo(X#A,M,N,Mo):-
    object(X,M,N),
    satisfy_redo(A,M,N,Mo),
    	!.

/* forall */

satisfy_redo(X$A,M,N,Mo):-
    	\+ (object(X,M,N),
   	satisfy_redo(X#(~(A)),M,N,Mo)).

/*step 2, generate the lattice pairs */
/*
lattice(a,b).
lattice(a,c).
lattice(b,c).
lattice(1,2).
lattice(1,3).
lattice(2,3).
*/
lattice1(X,Y,A,B):-
	nth1(M,A,X),
	nth1(N,A,Y),
	M<N.
lattice1(X,Y,A,B):-
	nth1(M,B,X),
	nth1(N,B,Y),
	M<N.
generate_lattice(A,B):-
	lattice1(X,Y,A,B),
	assert(lattice(X,Y)),
	fail.
generate_lattice(A,B):-
	!.
	

join(X,Y,X):-
	lattice(X,Y).
/*
join(X,Y,Z):-
	lattice(Z,X),
	lattice(Z,Y).
*/
meet(X,Y,Y):-
	lattice(X,Y).
/*
meet(X,Y,Z):-
	lattice(X,Z),
	lattice(Y,Z).
*/
supermodular(M,N,Partial,A,B):-
	abolish(lattice,2),
	generate_lattice(A,B),
/*
	satisfy_redo([X,Y,Z,Y,Join,Y,Meet,Y]$((join(X,Z,Join)/\meet(X,Z,Meet))->(p1(X,Y,Meet,Y)->p1(Join,Y,Z,Y))),M,N,Partial),
	satisfy_redo([X,Y,Z,Y,Join,Y,Meet,Y]$((join(X,Z,Join)/\meet(X,Z,Meet))->(p1(Z,Y,Join,Y)->p1(Meet,Y,X,Y))),M,N,Partial),
*/
	satisfy_redo([X,Y1,Z,Y2]$((lattice(X,Z)/\lattice(Y1,Y2))->(p1(X,Y2,Z,Y2)->p1(X,Y1,Z,Y1))),M,N,Partial),
	satisfy_redo([X,Y1,Z,Y2]$((lattice(X,Z)/\lattice(Y1,Y2))->(p1(Z,Y1,X,Y1)->p1(Z,Y2,X,Y2))),M,N,Partial),
/*
	satisfy_redo([X,Y1,X,Y2,X,Join,X,Meet]$((join(Y1,Y2,Join)/\meet(Y1,Y2,Meet))->(p2(X,Y1,X,Meet)->p2(X,Join,X,Y2))),M,N,Partial),
	satisfy_redo([X,Y1,X,Y2,X,Join,X,Meet]$((join(Y1,Y2,Join)/\meet(Y1,Y2,Meet))->(p2(X,Y2,X,Join)->p2(X,Meet,X,Y1))),M,N,Partial),
*/
	satisfy_redo([X,Y1,Z,Y2]$((lattice(X,Z)/\lattice(Y1,Y2))->(p2(Z,Y1,Z,Y2)->p2(X,Y1,X,Y2))),M,N,Partial),
	satisfy_redo([X,Y1,Z,Y2]$((lattice(X,Z)/\lattice(Y1,Y2))->(p2(X,Y2,X,Y1)->p2(Z,Y2,Z,Y1))),M,N,Partial).
% //////////////////////////////////
% rewrite the part of satisfaction
% fact 
great1(1,2).
great1(1,3).
great1(2,3).
great2(a,b).
great2(a,c).
great2(b,c).
% generate new types of formulas


construct_new1([X1,Y1,X2,Y2]$((great1(X1,X2)/\great2(Y1,Y2))->(p1(X3,Y3,X4,Y3)->p1(X5,Y4,X6,Y4)))):-
	member(X3,[X1,X2]),
	member(X4,[X1,X2]),
	member(X5,[X1,X2]),
	member(X6,[X1,X2]),
	member(Y3,[Y1,Y2]),
	member(Y4,[Y1,Y2]).

construct_new2([X1,Y1,X2,Y2]$((great1(X1,X2)/\great2(Y1,Y2))->(p2(X3,Y3,X3,Y4)->p1(X4,Y5,X4,Y6)))):-
	member(X3,[X1,X2]),
	member(X4,[X1,X2]),
	member(Y3,[Y1,Y2]),
	member(Y4,[Y1,Y2]),
	member(Y5,[Y1,Y2]),
	member(Y6,[Y1,Y2]).
construct_new((F1)/\(F2)):-
	construct_new1(F1),
	construct_new2(F2).
test_construct:-
	open('no-of-for',write,OF,[alias(outfile)]),
	construct_new(F),
	write(outfile,F),
	nl(outfile),	
	fail.
test_construct:-
	close(outfile),	
	!.
%find conditions that is similar to supermodular
%generate all the partial models
generate_all_partial_models(M,N):-
	generate_partial(M,N,Partial),
	assert(part_model(Partial)),
	fail.
generate_all_partial_models(M,N):-
	!.
generate_none_partial(M,N):-
	generate_partial(M,N,Partial),
	\+ (has_ne(Partial)),
	assert(part_mod(Partial)),
	fail.
generate_none_partial(M,N):-
	!.
similar_supermodular(M,N):-
	open('similar',write,OF,[alias(outfile)]),
%	generate_all_partial_models(M,N),
	generate_none_partial(M,N),
	construct_new(F),
	\+ (part_mod(Mo),satisfy_redo(F,M,N,Mo)),
	write(outfile,F),
	nl(outfile),
	fail.

similar_supermodular(M,N):-
	close(outfile),
	!.	

simi:-
	similar_supermodular([1,2,3],[a,b,c]).


% //////////////////////
interesting_game(M,N):-
	open('interesting',write,OF,[alias(outfile)]),
	generate_partial(M,N,Partial),
%	has_ne(Partial),
%	not_dominant(Partial),
%	has_cycle_partial(Partial,M,N),

%	\+ (permutation([1,2,3],A),
%	permutation([a,b,c],B),
%	supermodular(M,N,Partial,A,B)),

	supermodular(M,N,Partial,[1,2,3],[a,b,c]),
	\+ (has_ne(Partial)),
	write(outfile, Partial),
	nl(outfile),
	fail.
interesting_game(M,N):-
	close(outfile),
	!.
interesting:-
	interesting_game([1,2,3],[a,b,c]).
has_cycle_class(M,N,Class):-
	class_partial(Class,Partial,M,N),
	has_cycle_partial(Partial,M,N),
	!.
	
interest_game(M,N):-
	open('interest',write,OF,[alias(outfile)]),
	generate_class(M,N,Class),
%	exist_ne(Class),
%	has_cycle_class(M,N,Class),
	\+ (class_partial(Class,Partial,M,N),
	permutation([1,2,3],A),
	permutation([a,b,c],B),
	supermodular(M,N,Partial,A,B)),
	write(outfile, Class),
	nl(outfile),
	fail.
interest_game(M,N):-
	close(outfile),
	!.
interest:-
	interest_game([1,2,3],[a,b,c]).
check9(M,N):-
	length(M,M1), length(N,N1),
	string_concat('games-', M1,Out1), 
	string_concat(Out1, 'x',Out2), 
	string_concat(Out2, N1,Out3), 
	string_to_atom(Out3,Outfile),
    	open(Outfile,write,OF,[alias(outfile)]),
	generate_class(M,N,Class),
%	at_most_one_ne(Class),

	exact_one_ne(Class),

/*
	\+ (at_most_one_ne(class)),
*/
%	non_independent(Class),

	\+ (
	class_partial(Class,Partial,M,N),
	abolish(edge,1),
	abolish(mark,2),
	partial_graph(Partial,Graph),
	graph_database(Graph),
	no_cycle(M,N)),

	write(outfile,Class),
	nl(outfile),
	fail.
check9(M,N):-
	close(outfile),
	!.

check10 :-
	check9([1,2,3],[a,b,c]).
		
/* partial_graph([[[[3,a],[2,a],[1,a]],[[1,b],[2,b],[3,b]],[[2,c],[1,c],[3,c]]],[[[1,c],[1,b],[1,a]],[[2,a],[2,b],[2,c]],[[3,a],[3,b],[3,c]]]],G),
assert(edge([1,2])),assert(edge([2,3])),assert(edge([3,4])),assert(edge([4,1])),connect(2,4,3).
*/	
/* output those that are zero-sum and no N.E */	
new_zero(M,N):-
	length(M,M1), length(N,N1),
	string_concat('games-', M1,Out1), 
	string_concat(Out1, 'x',Out2), 
	string_concat(Out2, N1,Out3), 
	string_to_atom(Out3,Outfile),
    	open(Outfile,write,OF,[alias(outfile)]),
	generate_strict_model(M,N,Model),
	generate_for2([[1, 3], [2, 4]], [[1, 2, 3, 4]],[[1, 2, 3, 4]], [[1, 3], [2, 4]],[X1,X2,X3,X4],[Y1,Y2,Y3,Y4],[X5,X6,X7,X8],[Y5,Y6,Y7,Y8],F),
	filter(Model,F,M,N),
	filter(Model,~([X,Y]#(X@Y)),M,N),
	write(outfile,Model),
	nl(outfile),
	fail.
new_zero(M,N):-
	close(outfile),
	!.
