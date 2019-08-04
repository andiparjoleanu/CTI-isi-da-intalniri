
/*cod preluat din cartea(bibliografie[1]):
BALCAN Maria Florina, HRISTEA Florentina, 
Aspecte ale Cautarii si Reprezentarii Cunostintelor in Inteligenta Artificiala,
Editura Universitatii din Bucuresti, 2004, 
pg 216
*/

%predicat care inchide pe rand toate stream-urile deschise
close_all :- current_stream(_,_,S),close(S),fail;true.

%predicat care elimina toate predicatele salvate in baza de cunostinte
curata_bc:-current_predicate(P), abolish(P,[force(true)]), fail;true.

:-use_module(library(sockets)).
:-use_module(library(lists)).

:-use_module(library(file_systems)).
:-use_module(library(system)).

:-op(900, fy, '!').

:-op(100, xfx, ')').

:-dynamic fapt/3.

:-dynamic interogat/1.

:-dynamic scop/1.

:-dynamic interogabil/3.

:-dynamic regula/3.

:-dynamic solutie/4.

:-dynamic constrangeri/1.

:-dynamic reconsultare/1.

:-dynamic nr/1.
%-----------------------------------------------------------------------------------------------------------------------
%simulare caracter tab

tab(N) :- N > 0, write(' '), N1 is N - 1, tab(N1).
tab(0).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
tab(Stream,N):-N>0,write(Stream,' '),N1 is N-1, tab(Stream,N1).
tab(_,0).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%-----------------------------------------------------------------------------------------------------------------------
%predicat pentru negarea unui alt predicat

'!' P :- P, !, fail.
'!' _.

%-----------------------------------------------------------------------------------------------------------------------

_')'_.

%-----------------------------------------------------------------------------------------------------------------------
%afisare lista cu spatii

scrie_lista([]) :- nl.

scrie_lista([H|T]) :-
write(H), tab(1),
scrie_lista(T).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%aici 3
scrie_lista(Stream, []) :- nl(Stream), flush_output(Stream).

scrie_lista(Stream, [H | T]) :-
	write(Stream, H), tab(Stream, 1),
	scrie_lista(Stream, T).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

scrie_lista_terminator(Stream, [], Chr) :- write(Stream, Chr).

scrie_lista_terminator(Stream, [H | T], Chr) :-
	write(Stream, H), tab(Stream, 1),
	scrie_lista_terminator(Stream, T, Chr).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%aici 3

scrie_lista_butoane(Stream, L) :- append(['('], T, L), append(T1, [')'], T), write(Stream, '('), 
	scrie_continut_butoane(Stream, T1), write(Stream, ')'), nl(Stream), flush_output(Stream).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

scrie_continut_butoane(Stream, [H]) :- write(Stream, H), !.
scrie_continut_butoane(Stream, [H | T]) :-
	write(Stream, H), write(Stream, ';'),
	scrie_continut_butoane(Stream, T).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%-----------------------------------------------------------------------------------------------------------------------
%afisare lista fara spatii

scrie_lista_fara_spatii([]).

scrie_lista_fara_spatii([H | T]) :-
write(H), 
scrie_lista_fara_spatii(T).

scrie_lista_fara_spatii(_, []).

scrie_lista_fara_spatii(Stream, [H | T]) :-
write(Stream, H), 
scrie_lista_fara_spatii(Stream, T).

%-----------------------------------------------------------------------------------------------------------------------
%afiseaza faptele din baza de cunostinte

afiseaza_fapte :-
write('Fapte existente ? baza de cunostinte:'),
nl, nl, write(' (Atribut,valoare) '), nl, nl,
listeaza_fapte, nl.

%-----------------------------------------------------------------------------------------------------------------------

afiseaza_fapte(Stream) :-
listeaza_fapte(Stream).

%-----------------------------------------------------------------------------------------------------------------------
%afiseaza faptele din baza de cunostinte

listeaza_fapte :-  
fapt(av(Atr,Val), FC, _), 
write('('), write(Atr), write(','),
write(Val), write(')'),
write(','), write(' certitudine '),
FC1 is integer(FC), write(FC1),
nl, fail.

listeaza_fapte.

%-----------------------------------------------------------------------------------------------------------------------

listeaza_fapte(Stream) :-  
fapt(av(Atr,Val), FC, _), 
write(Stream, '('), write(Stream, Atr), write(Stream, ','),
write(Stream, Val), write(Stream, ')'),
write(Stream, ','), write(Stream, ' certitudine '),
FC1 is integer(FC), write(Stream, FC1),
write(Stream, '$'), fail.

listeaza_fapte(_).

%-----------------------------------------------------------------------------------------------------------------------
%converteste indicativele regulilor din numere float in int

lista_float_int([], []).
lista_float_int([Regula | Reguli], [Regula1 | Reguli1]):-
(Regula \== utiliz,
Regula1 is integer(Regula);
Regula == utiliz, Regula1 = Regula),
lista_float_int(Reguli, Reguli1).

%-----------------------------------------------------------------------------------------------------------------------
%programul efectiv

pornire :-
retractall(interogat(_)),      %atribut dat de utlizator
retractall(fapt(_, _, _)),     %memoreaza un fapt cunoscut(de le utilizator sau dedus)
repeat,
write('Introduceti una din urmatoarele optiuni: '),
nl, nl,
write(' (Incarca Consulta Reinitiaza  Afisare_fapte  Cum   Iesire) '),
nl, nl, write('|: '), 
citeste_linie([H|T]),           %argumente in "linia de comanda"
executa([H|T]), 
H == iesire.
                         
/*
fapt(av(anotimp, vara), 80, [utiliz])
                     av = atribut-valoare, fc, istoric

Ex: in_romania -> istoric = [3, 4]
*/

%-----------------------------------------------------------------------------------------------------------------------
%executa actiunea corespunzatoare uneia dintre optiunile afisate de predicatul pornire

executa([incarca]) :- 
incarca, !, nl,
write('Fisierul dorit a fost incarcat'), nl.

executa([consulta]) :- 
scopuri_princ, !.

%sterge toate atributele si faptele din baza de cunostinte
executa([reinitiaza]) :- 
retractall(interogat(_)),
retractall(fapt(_, _, _)), !.

%afiseaza faptele din baza de cunostinte
executa([afisare_fapte]) :-
afiseaza_fapte,!.


executa([cum|L]) :- cum(L), !.


executa([iesire]) :- !.

executa([_|_]) :-
write('Comanda incorecta! '), nl.

%-----------------------------------------------------------------------------------------------------------------------
%cauta solutia atributului scop, definit in fisier

scopuri_princ :-
scop(Atr), determina(Atr), afiseaza_scop(Atr), salveaza_solutii_in_director(Atr), fail.

scopuri_princ.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
scopuri_princ(Stream) :-
scop(Atr), determina(Stream,Atr), afiseaza_scop(Stream,Atr), salveaza_solutii_in_director(Atr), fail.

scopuri_princ(_) :- reconsultare(0).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%-----------------------------------------------------------------------------------------------------------------------
salveaza_solutii_in_director(Atr) :-
	atom_concat('demonstr_sistem(', Atr, Num1),
	atom_concat(Num1, ')', Denumire),
	(directory_exists(Denumire) -> 
		file_members_of_directory(Denumire, Set),
		sterge_toate_fisierele(Set); 
		make_directory(Denumire)), !, 
	fapt(av(Atr, Val), _, _),
    atom_concat('demonstratie##', Val, Den_fis),
    atom_concat(Den_fis, '##.txt', Denumire_fisier),
    atom_concat(Denumire, '/', Denumire1),
    atom_concat(Denumire1, Denumire_fisier, Cale_abs),
    telling(Input_curent),
    tell(Cale_abs), 
    cum(av(Atr, Val)),
    told,
    tell(Input_curent).

salveaza_solutii_in_director.
    
   
%-----------------------------------------------------------------------------------------------------------------------
sterge_toate_fisierele([-(_, Cale) | T]) :-
	delete_file(Cale),
	sterge_toate_fisierele(T).

sterge_toate_fisierele([]).

%-----------------------------------------------------------------------------------------------------------------------
%memoreaza in baza de cunostinte o valoare pentru atributul scop

determina(Atr) :-
realizare_scop(av(Atr,_), _, [scop(Atr)]), !.

determina(_).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
determina(Stream,Atr) :-
realizare_scop(Stream,av(Atr,_),_,[scop(Atr)]), reconsultare(0), !.

determina(_,_) :- reconsultare(0).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%-----------------------------------------------------------------------------------------------------------------------
%se apeleaza dupa gasirea unei solutii

afiseaza_scop(Atr) :-
setof(str(FC, av(Atr, Val)), R^(fapt(av(Atr, Val), FC, R), FC >= 20), L), !,
afiseaza_scopuri(L), nl, nl, write('Doriti sa afisati detalii despre solutii? (da nu)'), nl, 
repeat, read(Rasp), member(Rasp, [da, nu]), nl, !, nl, (Rasp = da -> afiseaza_detalii_solutii(L); true).

afiseaza_scop(_) :- write('Ne pare rau, nu s-au gasit solutii'), nl, nl.

%ATENTIE write(Stream, 's(\'NU ESITE SOLUTIE\')')

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

afiseaza_scop(Stream, Atr) :-
setof(str(FC, av(Atr, Val)), R^(fapt(av(Atr, Val), FC, R), FC >= 20), L), !,
afiseaza_scopuri(Stream, L), format(Stream, 's(~p)', [gata]), nl(Stream), flush_output(Stream).

afiseaza_scop(Stream, _) :- format(Stream, 's(~p)', [nu]), nl(Stream), flush_output(Stream).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%-----------------------------------------------------------------------------------------------------------------------

afiseaza_scopuri([]).
afiseaza_scopuri([H | T]) :- afiseaza_scopuri(T),  nl, H =.. [_, FC, A], scrie_scop(A, FC), !.

afiseaza_scopuri(_, []).
afiseaza_scopuri(Stream, [H | T]) :- afiseaza_scopuri(Stream, T),  nl(Stream), H =.. [_, FC, A], scrie_scop(Stream, A, FC), !.


%------------------------------------------------------------------------------------------------------------------------
afiseaza_detalii_solutii([str(_, av(_, Val)) | T]) :-
	afiseaza_detalii_solutii(T),
	solutie(Val, Descriere, proprietati(ListaProp), Cale),
	format('{ ~p }\n', [Val]),
	format('text descriere { ~p }\n', [Descriere]),
	write('proprietati solutie {'), nl,
	afisare_proprietati(ListaProp),
	write('}'), nl,
	format('imagine { ~p }\n', [Cale]), nl,
	afisare_delimitator(40), nl, nl.

afiseaza_detalii_solutii([]).

%-----------------------------------------------------------------------------------------------------------------------

afisare_proprietati([]).

afisare_proprietati([av(Atr, Val) | T]) :-
	(number(Val) -> Val1 is integer(Val); Val1 = Val), format('{~p#[~p]}\n', [Atr, Val1]),
	afisare_proprietati(T).

%-----------------------------------------------------------------------------------------------------------------------

afisare_delimitator(N) :-
	N > 0,
    write('/'),
    N1 is N - 1,
    afisare_delimitator(N1).

afisare_delimitator(0).

%-----------------------------------------------------------------------------------------------------------------------
%se afiseaza scopul si solutia

scrie_scop(av(Atr, Val), FC) :-
transformare(av(Atr, Val), X),
scrie_lista_fara_spatii(X),
write(' '),
write('(fc='),
FC1 is integer(FC), write(FC1), write(')').

/*
scrie_scop(Stream, av(Atr, Val), FC) :-
transformare(av(Atr, Val), X),
write(Stream, 's('),
scrie_lista_fara_spatii(Stream, X),
write(Stream, ' '),
write(Stream, '(fc='),
FC1 is integer(FC), write(Stream, FC1), write(Stream, '))'), nl(Stream).
*/


scrie_scop(Stream, av(_, Val), FC) :-
write(Stream, 's('),
solutie(Val, Descriere, proprietati(Prop), URL),
write(Stream, Val),
write(Stream, '$'),
FC1 is integer(FC),
write(Stream, FC1),
write(Stream, '$'),
atom_chars(Descriere, L),
sterge_linie_noua(L, L1),
atom_chars(Desc1, L1),
write(Stream, Desc1),
write(Stream, '$'),
scrie_proprietati(Stream, Prop),
write(Stream, '$'),
write(Stream, URL),
write(Stream, ')'), nl(Stream).


%-----------------------------------------------------------------------------------------------------------------------

sterge_linie_noua([], []) :- !.
sterge_linie_noua([H | T], L1) :- sterge_linie_noua(T, L2), (H \= '\n' -> L1 = [H | L2]; L1 = L2). 

%-----------------------------------------------------------------------------------------------------------------------
scrie_proprietati(Stream, L) :-
	write(Stream, '['),
	scrie_prop(Stream, L),
	write(Stream, ']').
%-----------------------------------------------------------------------------------------------------------------------

scrie_prop(Stream, [av(Atr, Val)]) :- !,
	format(Stream, '~p#~p', [Atr, Val]).

scrie_prop(Stream, [av(Atr, Val) | T]) :-
	format(Stream, '~p#~p%', [Atr, Val]),
	scrie_prop(Stream, T).

%-----------------------------------------------------------------------------------------------------------------------
%trateaza o premisa a unei reguli

realizare_scop(av(Atr, 'nu conteaza'), FC, _) :- 
fapt(av(Atr, 'nu conteaza'), FC, _), !.

realizare_scop('!' av(Atr, 'nu conteaza'), FC, _) :- 
fapt(av(Atr, 'nu conteaza'), FC, _), !.

%daca premisa este un atribut boolean cu valoare negativa, se trateaza premisa cu opusul factorului de certitudine 

realizare_scop('!' Scop, Not_FC, Istorie) :-
realizare_scop(Scop, FC, Istorie),
Not_FC is - FC, !.

%testeaza daca premisa a fost memorata ca fapt

realizare_scop(Scop, FC, _) :-
fapt(Scop, FC, _), !.

%incearca sa declanseze interogarea asociata atributului din premisa

realizare_scop(Scop, FC, Istorie) :-
pot_interoga(Scop, Istorie), !,
realizare_scop(Scop, FC, Istorie).

%cauta o regula pentru care concluzia contine atributul scop 

realizare_scop(Scop, FC_curent, Istorie) :-
fg(Scop, FC_curent, Istorie).

%------------------------------------------------------------------------------------------------------------------------
/*
daca Atr nu este un atribut interogat, preiau interogarea corespunzatoare, apelez interogarea si marchez 
atributul ca interogat
*/

pot_interoga(av(Atr, _), Istorie) :-
! interogat(av(Atr, _)),                           
interogabil(Atr, Optiuni, Mesaj),
interogheaza(Atr, Mesaj, Optiuni, Istorie), nl,
asserta( interogat(av(Atr,_))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
pot_interoga(Stream, av(Atr,_), Istorie) :-
'!' interogat(av(Atr, _)),
interogabil(Atr, Optiuni, Mesaj),
interogheaza(Stream, Atr, Mesaj, Optiuni, Istorie), nl, 
asserta( interogat(av(Atr,_))).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
realizare_scop(_, av(Atr, 'nu conteaza'), FC, _) :- 
fapt(av(Atr, 'nu conteaza'), FC, _), !.

realizare_scop(_, '!' av(Atr, 'nu conteaza'), FC, _) :- 
fapt(av(Atr, 'nu conteaza'), FC, _), !.

realizare_scop(Stream, '!' Scop,Not_FC,Istorie) :-
realizare_scop(Stream,Scop,FC,Istorie),
Not_FC is - FC, !.

realizare_scop(_,Scop,FC,_) :-
fapt(Scop,FC,_), !.

realizare_scop(Stream,Scop,FC,Istorie) :-
(reconsultare(1) -> (!, fail);
(pot_interoga(Stream,Scop,Istorie),
!, realizare_scop(Stream, Scop, FC, Istorie))).

realizare_scop(Stream,Scop,FC_curent,Istorie) :-
(reconsultare(1) -> (!, fail);
fg(Stream,Scop,FC_curent,Istorie)).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%-----------------------------------------------------------------------------------------------------------------------
/*
preia din baza de cunostinte regula care contine scopul, o demonstreaza, determina FC conform premiselor, 
se calculeaza FC-ul real in functie de FC-ul concluziei si FC-ul obtinut din premise
*/

fg(Scop, FC_curent, Istorie) :-
regula(N, premise(Lista), concluzie(Scop, FC)),
demonstreaza(N, Lista, FC_premise, Istorie),
ajusteaza(FC, FC_premise, FC_nou),
actualizeaza(Scop, FC_nou, FC_curent, N),
FC_curent == 100, !.

fg(Scop, FC, _) :- fapt(Scop, FC, _).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
fg(Stream,Scop,FC_curent,Istorie) :-
regula(N, premise(Lista), concluzie(Scop,FC)),
demonstreaza(Stream,N,Lista,FC_premise,Istorie),
ajusteaza(FC,FC_premise,FC_nou),
actualizeaza(Scop,FC_nou,FC_curent,N),
FC_curent == 100, !.

fg(_,Scop,FC,_) :- fapt(Scop,FC,_).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%------------------------------------------------------------------------------------------------------------------------
%se incepe demonstratia unei reguli cu factorul de certitudine 100. In istoric, se adauga indicativul regulii

demonstreaza(N, ListaPremise, Val_finala, Istorie) :-
dem(ListaPremise, 100, Val_finala, [N | Istorie]), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
demonstreaza(Stream,N,ListaPremise,Val_finala,Istorie) :-
dem(Stream,ListaPremise,100,Val_finala,[N|Istorie]),!.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%------------------------------------------------------------------------------------------------------------------------ 
/*
se trateaza pe rand toate premisele. Factorul de certitudine rezultat este valoarea minima dintre factorii de 
certitudine ai premiselor
*/

dem([], Val_finala, Val_finala, _).

dem([H | T], Val_actuala, Val_finala, Istorie) :-
realizare_scop(H, FC, Istorie),
Val_interm is min(Val_actuala, FC),
Val_interm >= 20,
dem(T, Val_interm, Val_finala, Istorie).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
dem(_,[],Val_finala,Val_finala,_).

dem(Stream,[H|T], Val_actuala, Val_finala, Istorie) :-
realizare_scop(Stream, H, FC, Istorie),
Val_interm is min(Val_actuala, FC),
Val_interm >= 20,
dem(Stream,T,Val_interm,Val_finala,Istorie).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 

%------------------------------------------------------------------------------------------------------------------------
%declanseaza o interogare pentru utilizator

/*
daca atributul are valori booleene, nu se mai afiseaza lista de optiuni si se asteapta raspunsul utilizatorului
care trebuie sa fie da sau nu. Raspunsul utilizatorului poate avea si forma: "valoare (fc=X)"
*/

interogheaza(Atr, Mesaj, Optiuni, Istorie) :-
	Optiuni = [da, nu],
	!, write(Mesaj), nl,
	constrangeri(L),
	(member(Atr, L) ->
		append(Optiuni, ['\'nu conteaza\'', '\'nu stiu\''], Optiuni1);
		Optiuni1 = Optiuni),
	citeste_opt(X, Optiuni1, Istorie),
	det_val_fc(X, Val, FC),
	asserta(fapt(av(Atr, Val), FC, [utiliz])).

/*
in cazul in care atributul are valori multiple, se asteapta raspunsul utilizatorului si apoi se memoreaza atributul
ca fapt in baza de cunostinte. Raspunsul utilizatorului poate avea si forma: "valoare (fc=X)"
*/

interogheaza(Atr, Mesaj, Optiuni, Istorie) :-
	write(Mesaj), nl,
	constrangeri(L),
	(member(Atr, L) ->
		append(Optiuni, ['\'nu conteaza\'', '\'nu stiu\''], Optiuni1);
		Optiuni1 = Optiuni),		
	citeste_opt(VLista, Optiuni1, Istorie),
	assert_fapt(Atr, VLista).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
       
interogheaza(Stream, Atr, Mesaj, Optiuni, Istorie) :- 
	Optiuni = [da, nu],
	!,write(Stream, i(Mesaj)), nl(Stream), flush_output(Stream),
	write('\n Intrebare atr boolean\n'),
	constrangeri(L),
	(member(Atr, L) -> 
		(append(Optiuni, ['\'nu conteaza\'', '\'nu stiu\''], Optiuni1), 
			write(Stream,'(da;nu;\'nu conteaza\';\'nu stiu\')'));
		Optiuni1 = Optiuni,
			write(Stream, '(da;nu)')),
	nl(Stream), flush_output(Stream),
	de_la_utiliz(Stream, X, Istorie, Optiuni1),
	(reconsultare(1) -> 
		(!, fail); 
		(det_val_fc(X, Val, FC),
		asserta( fapt(av(Atr, Val), FC, [utiliz])))).
	

%aici 1
interogheaza(Stream,Atr,Mesaj,Optiuni,Istorie) :- 
	write('\n Intrebare atr val multiple\n'),
	write(Stream, i(Mesaj)), nl(Stream), flush_output(Stream),
	constrangeri(L),
	(member(Atr, L) ->
		append(Optiuni, ['\'nu conteaza\'', '\'nu stiu\''], Optiuni1);
		Optiuni1 = Optiuni),
	citeste_opt(Stream, VLista, Optiuni1, Istorie),
	(reconsultare(1) ->
		(!, fail); 
		assert_fapt(Atr, VLista)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%------------------------------------------------------------------------------------------------------------------------
%predicatele afiseaza pasii prin care s-a realizat demonstrarea unei concluzii

cum([]) :- write('Scop? '), nl,
write('|:'), citeste_linie(Linie), nl,
transformare(Scop, Linie), cum(Scop).

cum(L) :- 
transformare(Scop, L), nl, cum(Scop).

cum(! Scop) :- 
fapt(Scop, FC, Reguli),
lista_float_int(Reguli, Reguli1),
FC < -20,
transformare(! Scop, PG),
append(PG, [' a fost derivat cu ajutorul regulilor: '], LL1),
scrie_lista_fara_spatii(LL1), scrie_lista(Reguli1), nl, afis_reguli(Reguli), fail.

cum(Scop) :-
	fapt(Scop, FC, Reguli),
	lista_float_int(Reguli, Reguli1),
	FC > 20, transformare(Scop, PG),
	append(PG, [' a fost derivat cu ajutorul regulilor: '], LL1),
	scrie_lista_fara_spatii(LL1), scrie_lista(Reguli1), nl, afis_reguli(Reguli),
	fail.

cum(_).

cum(Stream, Scop) :-
	fapt(Scop, FC, Reguli),
	lista_float_int(Reguli, Reguli1),
	FC > 20, transformare(Scop, PG),
	append(PG, [' a fost derivat cu ajutorul regulilor: '], LL1),
	scrie_lista_fara_spatii(Stream, LL1), scrie_lista_terminator(Stream, Reguli1, '$'), write(Stream, '$'), afis_reguli(Stream, Reguli),
	fail.

cum(_, _).

%------------------------------------------------------------------------------------------------------------------------
%afiseaza regulile din baza de cunostinte pentru indicativele din lista primita ca parametru

afis_reguli([]).

afis_reguli([N | X]) :-
	afis_regula(N),
	premisele(N),
	afis_reguli(X).

afis_reguli(_, []).

afis_reguli(Stream, [N | X]) :-
	afis_regula(Stream, N),
	premisele(Stream, N),
	afis_reguli(Stream, X).

%------------------------------------------------------------------------------------------------------------------------
%afiseaza structua unei reguli din fisier

afis_regula(N) :-
	regula(N, premise(Lista_premise), concluzie(Scop, FC)), 
	NN is integer(N),
	scrie_lista_fara_spatii(['r @ ', NN]), nl,
	length(Lista_premise, Len),
	(Len =:= 1 -> 
		(scrie_lista(['  Conditia este'])); 
		(scrie_lista(['  Conditiile sunt']))
	),
	scrie_lista_premise(Lista_premise),
	scrie_lista(['  Concluzia este']),
	transformare(Scop, Scop_tr),
	append(['   '], Scop_tr, L1),
	FC1 is integer(FC), append(L1, [' (fc=', FC1, ')'], LL),
	scrie_lista_fara_spatii(LL), nl, nl.



afis_regula(Stream, N) :-
	regula(N, premise(Lista_premise), concluzie(Scop, FC)), 
	NN is integer(N),
	scrie_lista_fara_spatii(Stream, ['r @ ', NN]), write(Stream, '$'),
	length(Lista_premise, Len),
	(Len =:= 1 -> 
		(scrie_lista_terminator(Stream, ['  Conditia este'], '$')); 
		(scrie_lista_terminator(Stream, ['  Conditiile sunt'], '$'))
	),
	scrie_lista_premise(Stream, Lista_premise),
	scrie_lista_terminator(Stream, ['  Concluzia este'], '$'),
	transformare(Scop, Scop_tr),
	append(['   '], Scop_tr, L1),
	FC1 is integer(FC), append(L1, [' (fc=', FC1, ')'], LL),
	scrie_lista_fara_spatii(Stream, LL), write(Stream, '$'), write(Stream, '$').

%------------------------------------------------------------------------------------------------------------------------
%scrie premisele unei reguli, asa cum se regasesc in fisierul de intrare

scrie_lista_premise([]).

scrie_lista_premise([H | T]) :-
	transformare(H, H_tr),
	tab(5), scrie_lista_fara_spatii(H_tr), nl,
	scrie_lista_premise(T).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
scrie_lista_premise(_,[]).

scrie_lista_premise(Stream,[H | T]) :-
	transformare(H, H_tr),
	tab(Stream, 5), scrie_lista_fara_spatii(Stream,H_tr), write(Stream, '$'),
	scrie_lista_premise(Stream, T).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%------------------------------------------------------------------------------------------------------------------------
%intervine la afisarea solutiei sau la afisarea regulilor care intervin in analiza

%daca atributul este boolean si are valoarea adevarat:

transformare(av(A, da), ['<', A, '>']) :- !.

%daca atributul este boolean si are valoarea fals:

transformare('!' av(A, da), ['!', '<', A, '>']) :- !.

transformare(av(A, nu), ['!', '<', A, '>']) :- !.

%daca atributul are valori multiple:

transformare(av(A, V), ['<', A, '>', ' ',  V]) :- !.

transformare(av(A, V), ['<', A, '>',  V]).

%------------------------------------------------------------------------------------------------------------------------
%preia premisele regulii si apeleaza cum_premise cu lista de premise

premisele(N) :-
	regula(N, premise(Lista_premise), _),
	!, cum_premise(Lista_premise).

premisele(Stream, N) :-
	regula(N, premise(Lista_premise), _),
	!, cum_premise(Stream, Lista_premise).

%------------------------------------------------------------------------------------------------------------------------
%afiseaza cum a fost obtinuta valoarea fiecarei premise

cum_premise([]).

cum_premise([Scop|X]) :-
	cum(Scop),
	cum_premise(X).

cum_premise(_, []).

cum_premise(Stream, [Scop|X]) :-
	cum(Stream, Scop),
	cum_premise(Stream, X).

%------------------------------------------------------------------------------------------------------------------------
%se afiseaza optiunile pentru interogarea curenta, apoi se asteapta raspunsul utilizatorului

citeste_opt(X, Opt_init, Istorie) :-
	atribuie_indicativ(Opt_init, Optiuni),
	afiseaza_optiuni(Optiuni),
	de_la_utiliz(X, Istorie, Optiuni).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%aici 2
citeste_opt(Stream,X,Optiuni,Istorie) :-
	append(['('],Optiuni,Opt1),
	append(Opt1,[')'],Opt),
	scrie_lista_butoane(Stream,Opt),
	de_la_utiliz(Stream,X,Istorie,Optiuni).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%------------------------------------------------------------------------------------------------------------------------

afiseaza_optiuni([]).

afiseaza_optiuni([A')'B | T]) :-
	format('~p) ~p\n', [A, B]),
    afiseaza_optiuni(T).

%------------------------------------------------------------------------------------------------------------------------

atribuie_indicativ(Opt_init, Op) :-
	atr_ind(Opt_init, Op, 'a').

atr_ind([], [], _).
atr_ind([Op | T1], [Val')'Op | T2], Val) :- atom_codes(Val, [Cod]), Cod1 is Cod + 1, atom_codes(Val1, [Cod1]), atr_ind(T1, T2, Val1).

%------------------------------------------------------------------------------------------------------------------------
%citeste optiunea introdusa de utilizator si valideaza raspunsul

de_la_utiliz(X, Istorie, Lista_opt) :-
	repeat, write(': '), citeste_linie(Y),
	proceseaza_raspuns(Y, X, Istorie, Lista_opt).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%aici 4
de_la_utiliz(Stream,X,Istorie,Lista_opt) :-
	repeat,write('astept raspuns\n'), citeste_linie(Stream,X), 
	format('Am citit ~p din optiunile',[X]), write(Lista_opt), nl,
	proceseaza_raspunsul(Stream, X, Istorie, Lista_opt), write('gata de la utiliz\n').
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%------------------------------------------------------------------------------------------------------------------------
%daca se introduce atomul de_ce, se afiseaza pasii parcursi de program in analiza scopului curent

proceseaza_raspunsul(Stream, [de_ce], Istorie, _) :- write(Stream, 'd('), afis_istorie(Stream, Istorie), write(Stream, ')'), nl(Stream), flush_output(Stream), !, fail.



proceseaza_raspunsul(_, [X], _, Lista_opt):-
	member(X,Lista_opt).

proceseaza_raspunsul(_, [X, '(', fc, '=', FC, ')'], _, Lista_opt):-
	member(X, Lista_opt), float(FC).

proceseaza_raspunsul(_, [reinitiaza], _, _) :- retractall(reconsultare(_)), asserta(reconsultare(1)).

%testeaza daca textul introdus corespunde cu una dintre optiuni
proceseaza_raspuns([de_ce], _, Istorie, _) :- nl, afis_istorie(Istorie), !, fail.

proceseaza_raspuns([X], [Y], _, Lista_opt) :-
	member(X')'Y, Lista_opt).

proceseaza_raspuns([Y], [Y], _, Lista_opt) :-
	member(_')'Y, Lista_opt).

%testeaza daca textul introdus corespunde cu una dintre optiuni si daca factorul de certitudine este un numar real

proceseaza_raspuns([X, '(', fc, '=', FC, ')'], [Y, '(', fc, '=', FC, ')'], _, Lista_opt) :-
	member(X')'Y, Lista_opt), float(FC).


proceseaza_raspuns(Rasp, Rasp, _, Lista_opt) :-
	Rasp = [Y, '(', fc, '=', FC, ')'],
	member(_')'Y, Lista_opt), float(FC).

%------------------------------------------------------------------------------------------------------------------------
%se adauga in baza de cunostinte ca fapt optiunea aleasa de utilizator 

assert_fapt(Atr, [Val, '(', fc, '=', FC, ')']) :-
!, asserta(fapt(av(Atr, Val), FC, [utiliz])).

assert_fapt(Atr, [Val]) :-
asserta(fapt(av(Atr, Val), 100, [utiliz])).

%------------------------------------------------------------------------------------------------------------------------
/*
se determina factorul de certitudine in functie de raspunsul utilizatorului

daca raspunsul este negativ si cuprinde un factor de certitudine, in baza de cunostinte atributul 
se va memora ca raspuns pozitiv cu un factor de certitudine negativ (- FC) 

altfel, factorul de certitudine va fi cel specificat de utilizator
*/

det_val_fc([nu], da, -100).

det_val_fc([nu, FC], da, NFC) :- NFC is - FC.

det_val_fc([nu, '(', fc, '=', FC, ')'], da, NFC) :- NFC is - FC.

det_val_fc([Val, FC], Val, FC).

det_val_fc([Val, '(', fc, '=', FC, ')'], Val, FC).

det_val_fc([Val], Val, 100).

%------------------------------------------------------------------------------------------------------------------------
%afiseaza regulile care au determinat declansarea unei interogari
        
afis_istorie([]) :- nl.

afis_istorie([scop(X) | T]) :-
scrie_lista([scop, '@', X]), !,
afis_istorie(T).

afis_istorie([N | T]) :-
afis_regula(N), !, afis_istorie(T).

%------------------------------------------------------------------------------------------------------------------------

afis_istorie(Stream, []) :- write(Stream, '$').

afis_istorie(Stream, [scop(X) | T]) :-
scrie_lista_terminator(Stream, [scop, '@', X], '$'), !,
afis_istorie(Stream, T).

afis_istorie(Stream, [N | T]) :-
afis_regula(Stream, N), !, afis_istorie(Stream, T).

%------------------------------------------------------------------------------------------------------------------------
/*
daca scop exista ca fapt in baza de cunostinte, se calculeaza pentru scop un factor de certitudine in functie
de valoarea existenta in baza de cunostinte si valoarea obtinuta in urma operatiei de ajustare a factorului de 
certitudine din premise. Se inlocuieste in faptul corespunzator din baza de cunostinte valoarea factorului
de certitudine si se adauga in istoric indicativul regulii demonstrate
*/

actualizeaza(Scop, FC_nou, FC, RegulaN) :-
fapt(Scop, FC_vechi, _),
combina(FC_nou, FC_vechi, FC),
retract(fapt(Scop, FC_vechi, Reguli_vechi)),
asserta(fapt(Scop, FC, [RegulaN | Reguli_vechi])), !.

/*
scop se adauga in baza de cunostinte daca nu a mai fost adaugat pana acum. Istoricul este reprezentat de regula care
a fost demonstrata
*/

actualizeaza(Scop, FC, FC, RegulaN) :-
asserta(fapt(Scop, FC, [RegulaN])).

%-----------------------------------------------------------------------------------------------------------------------
/*
factorul de certitudine real este determinat de factorul de certitudine specificat in concluzia regulii si 
factorul de certitudine obtinut prin demonstrarea premiselor 
*/

ajusteaza(FC1, FC2, FC) :-
X is FC1 * FC2 / 100,
FC is round(X).

%------------------------------------------------------------------------------------------------------------------------
/*

*/

combina(FC1, FC2, FC) :-
FC1 >= 0, FC2 >= 0,
X is FC2 * (100 - FC1) / 100 + FC1,
FC is round(X).

combina(FC1, FC2, FC) :-
FC1 < 0, FC2 < 0,
X is - (- FC1 - FC2 * (100 + FC1) / 100),
FC is round(X).

combina(FC1, FC2, FC) :-
(FC1 < 0; FC2 < 0),
(FC1 > 0; FC2 > 0),
FCM1 is abs(FC1), FCM2 is abs(FC2),
MFC is min(FCM1, FCM2),
X is 100 * (FC1 + FC2) / (100 - MFC),
FC is round(X).

%-----------------------------------------------------------------------------------------------------------------------
%incarca fisierul cu reguli

incarca :-
	write('Introduceti numele fisierului care doriti sa fie incarcat: '), 
	nl, write('|:'), read(F), 
	write('Introduceti numele fisierului cu constrangeri: '), 
	nl, read(C), 
	write('Introduceti numele fisierului care contine descrierea solutiilor posibile: '), 
	nl, read(R), 
	file_exists(F), file_exists(C), file_exists(R), !, incarca(F, C, R).

%daca fisierul nu exista, se executa urmatoarea regula
incarca :- write('S-a produs o eroare la identificarea fisierelor! '), nl, fail.

%-----------------------------------------------------------------------------------------------------------------------
%sterge din baza de cunostinte scopul, toate  atributele, faptele, regulile si incarca regulile din fisierul nou

incarca(F, C, R) :-
retractall(interogat(_)), retractall(fapt(_, _, _)),
retractall(scop(_)), retractall(interogabil(_, _, _)),
retractall(regula(_, _, _)), retractall(solutie(_, _, _, _)),
retractall(constrangeri(_)),
open(R, read, StreamR), incarca_solutii(StreamR), close(StreamR), open(C, read, StreamC), incarca_constrangeri(StreamC), close(StreamC), 
open(F, read, StreamF), incarca_reguli(StreamF), close(StreamF), !.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
incarca(F) :-
retractall(interogat(_)),retractall(fapt(_,_,_)),
retractall(scop(_)),retractall(interogabil(_,_,_)),
retractall(regula(_,_,_)),
open(F,read,StreamR),incarca_reguli(StreamR),close(StreamR),!.

%-----------------------------------------------------------------------------------------------------------------------
%citeste fiecare regula si interpreteaza cuvintele regasite in aceasta

incarca_reguli :-
repeat, citeste_propozitie(L),
proceseaza(L), L == [end_of_file], nl.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
incarca_reguli(StreamR) :-

repeat,citeste_propozitie(StreamR, L),
proceseaza(L),L == [end_of_file],nl.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%-----------------------------------------------------------------------------------------------------------------------

incarca_constrangeri(Stream) :-
    assert(constrangeri([])),
	repeat,
		read(Stream, X),
		(X == end_of_file;
		 (retract(constrangeri(L)),
		  L1 = [X | L],
		  assert(constrangeri(L1)),
		  fail)
		).

%-----------------------------------------------------------------------------------------------------------------------

incarca_solutii(Stream) :-
repeat, citeste_solutie(Stream, L),
proceseaza(L), L == [end_of_file], nl.

%-----------------------------------------------------------------------------------------------------------------------
%interpreteaza cuvintele unei reguli

proceseaza([end_of_file]) :- !.

proceseaza(L) :-
trad(R, L, []), assertz(R), !.

/*
De exemplu, pentru propozitia:
scopul este loc_concediu.

L va fi [scopul, este, loc_concediu]
Astfel, la apelul trad(scop(X), [scopul, este, X | T], T), vom avea:
X = loc_concediu
T = []

Se adauga in baza de cunostinte scop(loc_concediu)
*/

%-----------------------------------------------------------------------------------------------------------------------

%trad(scop(X), [scopul, este, X | T], T).
trad(scop(X)) --> [scop, '@', X].

%trad(interogabil(Atr, M, P), L, T) :- L = [i, '@', Atr | B], afiseaza(Atr, P, B, G), lista_optiuni(M, G, T).
trad(interogabil(Atr, M, P)) --> 
[i, '@', Atr], afiseaza(Atr, P), lista_optiuni(M).

%trad(regula(N, premise(Daca), concluzie(Atunci, F)), L, T) :- identificator(N, L, L1), daca(Daca, L1, L2), atunci(Atunci, F, L2, T).
trad(regula(N, premise(Daca), concluzie(Atunci, F))) --> identificator(N), daca(Daca), atunci(Atunci, F).

trad(solutie(Nume_solutie, Descriere, proprietati(Prop), URL_imagine)) --> preia_nume_solutie(Nume_solutie), preia_descriere(Descriere),
	preia_proprietati(Prop), preia_url(URL_imagine).

trad('Eroare la parsare'-L, L, _).

%-----------------------------------------------------------------------------------------------------------------------

preia_nume_solutie(Nume_solutie) --> ['{', Nume_solutie, '}'].

preia_descriere(Descriere) --> [text, descriere, '{', Descriere, '}'].

preia_proprietati(Prop) --> [proprietati, solutie, '{'], lista_proprietati(Prop).

lista_proprietati([], ['}' | T], T).
lista_proprietati([av(Atr, Val) | T]) --> ['{', Atr, '#', '[', Val, ']', '}'], lista_proprietati(T). 

preia_url(URL_imagine) --> [imagine, '{', URL_imagine, '}'].

%-----------------------------------------------------------------------------------------------------------------------

%lista_optiuni(M, [optiunile, sunt | R], T) :- lista_de_optiuni(M, R, T).
lista_optiuni(M) --> [optiunile, sunt], lista_de_optiuni(M).

%lista_de_optiuni([Element], [Element| T], T).
lista_de_optiuni([Element]) -->  [Element].

%lista_de_optiuni([Element | Y], [Element, ',' | R], T) :- lista_de_optiuni(Y, R, T).
lista_de_optiuni([Element |T]) --> [Element], [','], lista_de_optiuni(T).

%afiseaza(_, P, [textul, este, P | T], T).
afiseaza(_, P) -->  [textul, este, P].

%afiseaza(P, P, T, T).
afiseaza(P, P) -->  [].

%identificator(N, [r, '@', N | T], T).
identificator(N) --> [r, '@', N].

%daca(Daca, [conditiile, sunt | R], T) :- lista_premise(Daca, R, T).
daca(Daca) --> [conditiile, sunt], lista_premise(Daca).

%daca(Daca, [conditia, este | R], T) :- lista_premise(Daca, R, T).
daca(Daca) --> [conditia, este], lista_premise(Daca).

%lista_premise([Daca], L, T) :- propoz(Daca, L, [concluzia, este | T]).
lista_premise([Daca]) --> propoz(Daca), [concluzia, este].

%lista_premise([Prima | Celelalte], L, T) :- propoz(Prima, L, X), lista_premise(Celelalte, X, T).
lista_premise([Prima | Celalalte]) --> propoz(Prima), lista_premise(Celalalte).

%atunci(Atunci, FC, L, T) :- propoz(Atunci, L, ['(', fc, '=', FC, ')' | T]).
atunci(Atunci, FC) --> propoz(Atunci), ['(', fc, '='], [FC], [')'].

%atunci(Atunci, 100, L, T) :- propoz(Atunci, L, T).
atunci(Atunci, 100) --> propoz(Atunci).

%propoz('!' av(Atr, da), ['!', '<', Atr, '>' | T], T).
propoz('!' av(Atr, da)) --> ['!', '<', Atr, '>'].

%propoz(av(Atr, Val), ['<', Atr, '>', Val | T], T).
propoz(av(Atr, Val)) --> ['<', Atr, '>', Val].

%propoz(av(Atr, da), ['<', Atr, '>' | T], T).
propoz(av(Atr, da)) --> ['<', Atr, '>'].

%-----------------------------------------------------------------------------------------------------------------------      

citeste_linie([Cuv | Lista_cuv]) :-
get_code(Car),
citeste_cuvant(Car, Cuv, Car1), 
rest_cuvinte_linie(Car1, Lista_cuv).
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%stream%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
citeste_linie(Stream,[Cuv|Lista_cuv]) :-
get_code(Stream,Car),
citeste_cuvant(Stream,Car, Cuv, Car1), 
rest_cuvinte_linie(Stream,Car1, Lista_cuv).
 
      
% -1 este codul ASCII pt EOF

rest_cuvinte_linie(_,-1, []):-!.
    
rest_cuvinte_linie(_,Car,[]) :-(Car==13;Car==10), !.

rest_cuvinte_linie(Stream,Car,[Cuv1|Lista_cuv]) :-
citeste_cuvant(Stream,Car,Cuv1,Car1),      
rest_cuvinte_linie(Stream,Car1,Lista_cuv).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%-----------------------------------------------------------------------------------------------------------------------      
% -1 este codul ASCII pt EOF

rest_cuvinte_linie(-1, []) :- !.
    
rest_cuvinte_linie(Car, []) :- (Car == 13; Car == 10), !.

rest_cuvinte_linie(Car, [Cuv1 | Lista_cuv]) :-
citeste_cuvant(Car, Cuv1, Car1),      
rest_cuvinte_linie(Car1, Lista_cuv).

%-----------------------------------------------------------------------------------------------------------------------
%citeste o propozitie din fisier. Se citeste recursiv cate un cuvant folosind predicatul citeste_cuvant

citeste_propozitie([Cuv | Lista_cuv]) :-
get_code(Car), citeste_cuvant(Car, Cuv, Car1), 
rest_cuvinte_propozitie(Car1, Lista_cuv).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

citeste_propozitie(Stream, [Cuv|Lista_cuv]) :-
get_code(Stream, Car),citeste_cuvant(Stream, Car, Cuv, Car1), 
rest_cuvinte_propozitie(Stream, Car1, Lista_cuv).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
     

%-----------------------------------------------------------------------------------------------------------------------
%citeste o solutie din fisier.

citeste_solutie([Cuv | Lista_cuv]) :-
get_code(Car), citeste_cuvant(Car, Cuv, Car1), 
rest_cuvinte_solutie(Car1, Lista_cuv), !.

citeste_solutie(Stream, [Cuv | Lista_cuv]) :-
get_code(Stream, Car), citeste_cuvant(Stream, Car, Cuv, Car1), 
rest_cuvinte_solutie(Stream, Car1, Lista_cuv), !.
 
%-----------------------------------------------------------------------------------------------------------------------
%returneaza lista cuvintelor din solutia curenta. Cand se intalneste end_of_file sau un sir de '/', lista se initializeaza cu []

rest_cuvinte_solutie(-1, []) :- !.
    
rest_cuvinte_solutie(47, ['/']) :- citeste_pana_la_ultimul_separator(39), !.

/*
se apeleaza recursiv rest_cuvinte_solutie, care citeste din fisier in functie de caracterul returnat la
apelul lui citeste_cuvant
*/

rest_cuvinte_solutie(Car, L) :-
citeste_cuvant(Car, Cuv1, Car1),      
rest_cuvinte_solutie(Car1, Lista_cuv),
(Lista_cuv = ['/'] -> L = []; append([Cuv1], Lista_cuv, L)).



rest_cuvinte_solutie(_, -1, []) :- !.
    
rest_cuvinte_solutie(Stream, 47, ['/']) :- citeste_pana_la_ultimul_separator(Stream, 39), !.

rest_cuvinte_solutie(Stream, Car, L) :-
citeste_cuvant(Stream, Car, Cuv1, Car1),      
rest_cuvinte_solutie(Stream, Car1, Lista_cuv),
(Lista_cuv = ['/'] -> L = []; append([Cuv1], Lista_cuv, L)).

%-----------------------------------------------------------------------------------------------------------------------

citeste_pana_la_ultimul_separator(Nr) :- Nr > 0, get_code(47), Nr1 is Nr - 1, !, citeste_pana_la_ultimul_separator(Nr1).

citeste_pana_la_ultimul_separator(0).

citeste_pana_la_ultimul_separator(Stream, Nr) :- Nr > 0, get_code(Stream, 47), Nr1 is Nr - 1, !, citeste_pana_la_ultimul_separator(Stream, Nr1).

citeste_pana_la_ultimul_separator(_, 0).

%-----------------------------------------------------------------------------------------------------------------------
%returneaza lista cuvintelor din propozitia curenta. Cand se intalneste end_of_file sau ., lista se initializeaza cu []

rest_cuvinte_propozitie(-1, []):-!.
    
rest_cuvinte_propozitie(Car, []) :- Car == 46, !.

/*
se apeleaza recursiv rest_cuvinte propozitie, care citeste din fisier in functie de caracterul returnat la
apelul lui citeste_cuvant
*/

rest_cuvinte_propozitie(Car, [Cuv1|Lista_cuv]) :-
citeste_cuvant(Car, Cuv1, Car1),      
rest_cuvinte_propozitie(Car1,Lista_cuv).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
rest_cuvinte_propozitie(_,-1, []):-!.
    
rest_cuvinte_propozitie(_,Car,[]) :-Car==46, !.

rest_cuvinte_propozitie(Stream,Car,[Cuv1|Lista_cuv]) :-
citeste_cuvant(Stream,Car,Cuv1,Car1),      
rest_cuvinte_propozitie(Stream,Car1,Lista_cuv).


citeste_cuvant(_,-1,end_of_file,-1):-!.

citeste_cuvant(Stream,Caracter,Cuvant,Caracter1) :-   
caracter_cuvant(Caracter),!, 
name(Cuvant, [Caracter]),get_code(Stream,Caracter1).

citeste_cuvant(Stream,Caracter, Numar, Caracter1) :-
caracter_numar(Caracter),!,
citeste_tot_numarul(Stream,Caracter, Numar, Caracter1).
 

citeste_tot_numarul(Stream,Caracter,Numar,Caracter1):-
determina_lista(Stream,Lista1,Caracter1),
append([Caracter],Lista1,Lista),
transforma_lista_numar(Lista,Numar).


determina_lista(Stream,Lista,Caracter1):-
get_code(Stream,Caracter), 
(caracter_numar(Caracter),
determina_lista(Stream,Lista1,Caracter1),
append([Caracter],Lista1,Lista); 
\+(caracter_numar(Caracter)),
Lista=[],Caracter1=Caracter).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%-----------------------------------------------------------------------------------------------------------------------
%citeste_cuvant determina cum va fi citita secventa de caractere care urmeaza in consola

%daca suntem la final de fisier, nu ne intereseaza caracterul cu care s-a incheiat secventa curenta

citeste_cuvant(-1, end_of_file, -1):-!.

/*
daca se intalneste un caracter special, se returneaza caracterul ca atom si codul ascii al caracterului
care urmeaza in fisier
*/

citeste_cuvant(Caracter, Cuvant, Caracter1) :-   
caracter_cuvant(Caracter), !, 
name(Cuvant, [Caracter]), get_code(Caracter1).


%daca se intalneste o cifra, se citesc caractere pana la aparitia unui caracter care nu e cifra

citeste_cuvant(Caracter, Numar, Caracter1) :-
caracter_numar(Caracter), !,
citeste_tot_numarul(Caracter, Numar, Caracter1).

% 39 este codul ASCII pt '

/*
daca se citeste un atom cuprins intre apostrofuri,
se ignora tipul caracterelor din care este format, iar lista de caractere citite
se termina la a doua aparitie a caracterului '
*/

citeste_cuvant(Caracter, Cuvant, Caracter1) :-
Caracter == 39, !,
pana_la_urmatorul_apostrof(Lista_caractere),
L=[Caracter | Lista_caractere],
name(Cuvant, L), get_code(Caracter1).


/*
daca primul caracter din secventa "poate fi in interiorul unui cuvant",
se considera ca urmeaza un cuvant si se citesc caractere pana la aparitia unui caracter
special. Se preiau codurile ASCII ale caracterelor intr-o lista si dupa intalnirea
caracterului special, se transforma lista de coduri in atom
*/

citeste_cuvant(Caracter, Cuvant, Caracter1) :-          
caractere_in_interiorul_unui_cuvant(Caracter), !,              
((Caracter > 64, Caracter < 91), !,
Caracter_modificat is Caracter + 32;
Caracter_modificat is Caracter),                              
citeste_intreg_cuvantul(Caractere, Caracter1),
name(Cuvant, [Caracter_modificat | Caractere]).

%se ignora orice alt tip de caracter intalnit

citeste_cuvant(_, Cuvant, Caracter1) :-                
get_code(Caracter),       
citeste_cuvant(Caracter, Cuvant, Caracter1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
citeste_cuvant(Stream,Caracter,Cuvant,Caracter1) :-
Caracter==39,!,
pana_la_urmatorul_apostrof(Stream,Lista_caractere),
L=[Caracter|Lista_caractere],
name(Cuvant, L),get_code(Stream,Caracter1).
        

pana_la_urmatorul_apostrof(Stream,Lista_caractere):-
get_code(Stream,Caracter),
(Caracter == 39,Lista_caractere=[Caracter];
Caracter\==39,
pana_la_urmatorul_apostrof(Stream,Lista_caractere1),
Lista_caractere=[Caracter|Lista_caractere1]).


citeste_cuvant(Stream,Caracter,Cuvant,Caracter1) :-          
caractere_in_interiorul_unui_cuvant(Caracter),!,              
((Caracter>64,Caracter<91),!,
Caracter_modificat is Caracter+32;
Caracter_modificat is Caracter),                              
citeste_intreg_cuvantul(Stream,Caractere,Caracter1),
name(Cuvant,[Caracter_modificat|Caractere]).
        

citeste_intreg_cuvantul(Stream,Lista_Caractere,Caracter1) :-
get_code(Stream,Caracter),
(caractere_in_interiorul_unui_cuvant(Caracter),
((Caracter>64,Caracter<91),!, 
Caracter_modificat is Caracter+32;
Caracter_modificat is Caracter),
citeste_intreg_cuvantul(Stream,Lista_Caractere1, Caracter1),
Lista_Caractere=[Caracter_modificat|Lista_Caractere1]; \+(caractere_in_interiorul_unui_cuvant(Caracter)),
Lista_Caractere=[], Caracter1=Caracter).


citeste_cuvant(Stream,_,Cuvant,Caracter1) :-                
get_code(Stream,Caracter),       
citeste_cuvant(Stream,Caracter,Cuvant,Caracter1).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 


%-----------------------------------------------------------------------------------------------------------------------
/*
se citesc caractere numerice, se adauga caracterul initial la lista caracterelor si se transforma lista
in numar
*/

citeste_tot_numarul(Caracter, Numar, Caracter1):-
determina_lista(Lista1, Caracter1),
append([Caracter], Lista1, Lista),
transforma_lista_numar(Lista, Numar).

%-----------------------------------------------------------------------------------------------------------------------
%se citesc caractere pana cand se intalneste un caracter care nu e cifra

determina_lista(Lista, Caracter1):-
get_code(Caracter), 
(caracter_numar(Caracter),
determina_lista(Lista1, Caracter1),
append([Caracter], Lista1, Lista); 
\+(caracter_numar(Caracter)),
Lista = [], Caracter1 = Caracter).
 
%-----------------------------------------------------------------------------------------------------------------------
%predicat care transforma o lista de cifre intr-un numar

transforma_lista_numar([], 0).

transforma_lista_numar([H | T], N):-
transforma_lista_numar(T, NN), 
lungime(T, L), Aux is exp(10, L),
HH is H - 48, N is HH * Aux + NN.

%-----------------------------------------------------------------------------------------------------------------------
%predicat care calculeaza lungimea unei liste

lungime([], 0).

lungime([_ | T], L):-
lungime(T, L1),
L is L1 + 1.

%-----------------------------------------------------------------------------------------------------------------------
%predicat care citeste caractere pana la aparitia caracterului '

pana_la_urmatorul_apostrof(Lista_caractere):-
get_code(Caracter),
(Caracter == 39, Lista_caractere = [Caracter];
Caracter \== 39,
pana_la_urmatorul_apostrof(Lista_caractere1),
Lista_caractere = [Caracter | Lista_caractere1]).
        
%-----------------------------------------------------------------------------------------------------------------------
/*
se citesc caractere pana cand se intalneste un caracter "care nu poate fi in interiorul unui cuvant",
se salveaza caracterele valide in Lista_Caractere, iar caracterul care a intrerupt citirea se memoreaza in variabila Caracter1
*/

citeste_intreg_cuvantul(Lista_Caractere, Caracter1) :-
get_code(Caracter),
(caractere_in_interiorul_unui_cuvant(Caracter),
((Caracter > 64, Caracter < 91),!, 
Caracter_modificat is Caracter + 32;
Caracter_modificat is Caracter),
citeste_intreg_cuvantul(Lista_Caractere1, Caracter1),
Lista_Caractere = [Caracter_modificat | Lista_Caractere1]; \+ (caractere_in_interiorul_unui_cuvant(Caracter)),
Lista_Caractere = [], Caracter1 = Caracter).

%-----------------------------------------------------------------------------------------------------------------------
%predicatul determina daca caracterul citit este un caracter special

caracter_cuvant(C) :- member(C, [44, 59, 58, 63, 46, 40, 41, 64, 33, 60, 61, 62, 123, 125, 91, 93, 35, 47]).

/*
am specificat codurile ASCII pentru , ; : ? . ( ) @ ! < = > { } [ ] # /
RESTUL CARACTERELOR ALFANUMERICE VOR FI IGNORATE -> TREBUIE ADAUGATE
*/

%-----------------------------------------------------------------------------------------------------------------------
%predicatul determina daca caracterul citit este alfanumeric, '-' sau '_'

caractere_in_interiorul_unui_cuvant(C):-
C > 64, C < 91; C > 47, C < 58;
C == 45; C == 95; C > 96, C < 123.

%-----------------------------------------------------------------------------------------------------------------------
%predicatul determina daca caracterul citit este numar

caracter_numar(C) :- C < 58, C >= 48.

inceput:-format('Salutare\n',[]),	flush_output,

				prolog_flag(argv, [PortSocket|_]), %preiau numarul portului, dat ca argument cu -a
				%portul este atom, nu constanta numerica, asa ca trebuie sa il convertim la numar
				atom_chars(PortSocket,LCifre),
				number_chars(Port,LCifre),%transforma lista de cifre in numarul din 
				socket_client_open(localhost: Port, Stream, [type(text)]),
				proceseaza_text_primit(Stream,0).
				
				
proceseaza_text_primit(Stream,C):-
				write(inainte_de_citire),
				read(Stream,CevaCitit),
				write(dupa_citire),
				write(CevaCitit),nl,
				proceseaza_termen_citit(Stream,CevaCitit,C).
				
proceseaza_termen_citit(Stream,salut,C):-
				write(Stream,'salut, bre!\n'),
				flush_output(Stream),
				C1 is C+1,
				proceseaza_text_primit(Stream,C1).
				
proceseaza_termen_citit(Stream,'I hate you!',C):-
				write(Stream,'I hate you too!!'),
				flush_output(Stream),
				C1 is C+1,
				proceseaza_text_primit(Stream,C1).
				

proceseaza_termen_citit(Stream,director(D),C):- %pentru a seta directorul curent
				format(Stream,'Locatia curenta de lucru s-a deplasat la adresa ~p.',[D]),
				format('Locatia curenta de lucru s-a deplasat la adresa ~p',[D]),				
				X=current_directory(_,D),
				write(X),
				call(X),
				nl(Stream),
				flush_output(Stream),
				C1 is C+1,
				proceseaza_text_primit(Stream,C1).				
				
				
proceseaza_termen_citit(Stream, incarca(X, Y, Z),C):-
				write(Stream,'Se incearca incarcarea fisierului\n'),
				flush_output(Stream),
				incarca(X, Y, Z),
				C1 is C+1,
				proceseaza_text_primit(Stream,C1).
				
proceseaza_termen_citit(Stream, comanda(consulta),C):-
				write(Stream,'Se incepe consultarea\n'),
				flush_output(Stream),
				retractall(reconsultare(_)), 
				asserta(reconsultare(0)), 
				scopuri_princ(Stream),
				C1 is C+1,
				proceseaza_text_primit(Stream,C1).

proceseaza_termen_citit(Stream, comanda(reinitiaza),C):-
				executa([reinitiaza]),
				C1 is C+1,
				proceseaza_text_primit(Stream,C1).

proceseaza_termen_citit(Stream, comanda(afiseaza_fapte),C):-
				write(Stream, 'f('),
				afiseaza_fapte(Stream),
				write(Stream, ')'),
				nl(Stream),
				flush_output(Stream),
				C1 is C+1,
				proceseaza_text_primit(Stream,C1).

proceseaza_termen_citit(Stream, cum(X), C) :-
				write(Stream, 'w('),
				cum(Stream, av(student_cti, X)),
				write(Stream, ')'),
				nl(Stream),
				flush_output(Stream),
				C1 is C+1,
				proceseaza_text_primit(Stream, C1).
				
proceseaza_termen_citit(Stream, X, _):- % cand vrem sa-i spunem "Pa"
				(X == end_of_file ; X == exit),
				write(gata),nl,
				close(Stream).
				
			
proceseaza_termen_citit(Stream, Altceva,C):- %cand ii trimitem sistemului expert o comanda pe care n-o pricepe
				write(Stream,'ce vrei, neica, de la mine?! '),write(Stream,Altceva),nl(Stream),
				flush_output(Stream),
				C1 is C+1,
				proceseaza_text_primit(Stream,C1).

