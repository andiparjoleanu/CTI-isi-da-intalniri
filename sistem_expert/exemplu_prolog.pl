:-use_module(library(sockets)).


inceput:-format('Salutare\n',[]),	flush_output,
				prolog_flag(argv, [PortSocket|_]), %preiau numarul portului, dat ca argument cu -a
				%portul este atom, nu constanta numerica, asa ca trebuie sa il convertim la numar
				atom_chars(PortSocket,LCifre),
				number_chars(Port,LCifre),%transforma lista de cifre in numarul din 
				socket_client_open(localhost: Port, Stream, [type(text)]),
				proceseaza_text_primit(Stream,0).
				
				
proceseaza_text_primit(Stream,C):-
				read(Stream,CevaCitit),
				proceseaza_termen_citit(Stream,CevaCitit,C).
				
proceseaza_termen_citit(Stream,salut,C):-
				write(Stream,'salut, bre!\n'),
				flush_output(Stream),
				C1 is C+1,
				proceseaza_text_primit(Stream,C1).
				
proceseaza_termen_citit(Stream,'ce mai faci?',C):-
				write(Stream,'ma plictisesc...\n'),
				flush_output(Stream),
				C1 is C+1,
				proceseaza_text_primit(Stream,C1).
				
proceseaza_termen_citit(Stream, X + Y,C):-
				Rez is X+Y,
				write(Stream,Rez),nl(Stream),
				flush_output(Stream),
				C1 is C+1,
				proceseaza_text_primit(Stream,C1).
				
oras(bucuresti, mare).				
oras(pitesti, mic).				
proceseaza_termen_citit(Stream, oras(X),C):-
				oras(X,Tip),
				format(Stream,'~p este un oras ~p\n',[X,Tip]),
				flush_output(Stream),
				C1 is C+1,
				proceseaza_text_primit(Stream,C1).
				
proceseaza_termen_citit(Stream, X, _):-
				(X == end_of_file ; X == exit),
				close(Stream).
				
			
proceseaza_termen_citit(Stream, Altceva,C):-
				write(Stream,'nu inteleg ce vrei sa spui: '),write(Stream,Altceva),nl(Stream),
				flush_output(Stream),
				C1 is C+1,
				proceseaza_text_primit(Stream,C1).