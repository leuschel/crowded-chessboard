:- use_module(library(clpfd)).
:- use_module(library(lists)).

% Prolog Solution to crowded chessboard

/*
 Crowded Chessboard Problem from problem 306:
  Dudeney, H. E. Amusements in Mathematics. New York: Dover, pp. 88-89 and 96, 1970.

  Optimal number of bishops: 2*n - 2
 http://mathworld.wolfram.com/BishopsProblem.html
 http://www.gutenberg.org/files/16713/16713-h/16713-h.htm#CHESSBOARD_PROBLEMS
*/

solve(N,Knights,Sol) :-
   statistics(walltime,[Start,_]),
   length(Sol,N),
   maplist(pieces(N),Sol),
   append(Sol,AllPieces),
   (N=4 -> Bishops=5 ; Bishops is 2*N-2),
   Empty is N*N - 2*N - Bishops - Knights,
   format('Starting solving ~w*~w board for ~w queens/rooks, ~w bishops, ~w knights (start: ~w ms)~n',[N,N,N,Bishops,Knights,Start]),
   global_cardinality(AllPieces,[0-Empty, 1-N, 2-N, 3-Bishops,4-Knights]),
   maplist(exactly_one(1),Sol), % one queen on every row
   maplist(exactly_one(2),Sol), % one rook on every row
   transpose(Sol,TSol),
   %print(t(TSol)),nl,
   maplist(exactly_one(1),TSol), % one queen on every col
   maplist(exactly_one(2),TSol), % one rook on every col
   findall(diag(D,Sol),diagonal(Sol,D),Diagonals),
   %print(diag(Diagonals)),nl,
   maplist(at_most_one(1,Sol),Diagonals), % check queens do not attack each other on diagonals
   maplist(at_most_one(3,Sol),Diagonals), % ditto for bishops
   % now check Knights
   knights_ok(Sol),
   labeling([ffc],AllPieces),
   statistics(walltime,[_,Delta]),
   print(walltime(Delta)),nl,
   prboard(Sol).
   %nl, print(diagonals(Diagonals)),nl.
solve(_N,_Knights,_Sol) :-
   statistics(walltime,[_,Delta]),
   print(walltime_for_failure(Delta)),nl,fail.

% 0 = empty, 1 = queen, 2=rook, 3=bishop, 4=knight

pieces(N,L) :- length(L,N), clpfd:domain(L,0,4).

exactly_one(Piece,List) :- count(Piece,List,'#=',1).
at_most_one(Piece,Sol,diag(D,Sol)) :- at_most_one(Piece,D).
at_most_one(Piece,List) :- count(Piece,List,'#<',2).

% a predicate to check whether knights are not attacking each other
knights_ok([_]).
knights_ok([L1,L2|TL]) :-
   knights_ok2(1,L1,L2,TL),
   knights_ok([L2|TL]).

knights_ok2(_,[],_,_).
knights_ok2(Index,[Knight|KT],L2,TL) :-
   I1 is Index+1, Im1 is Index-1,
   I2 is Index+2, Im2 is Index-2,
   check_knight(I2,L2,Knight),
   check_knight(Im2,L2,Knight),
   (TL = [L3|_]
      -> check_knight(I1,L3,Knight),check_knight(Im1,L3,Knight)
      ;  true),
   knights_ok2(I1,KT,L2,TL).

check_knight(Index,Line,K1) :-
    (nth1(Index,Line,K2) -> not_two_knights(K1,K2) ; true).

not_two_knights(K1,K2) :- (K1 #= 4) #=> (K2 #\= 4).

% compute the diagonals on the chessboard
diagonal([L1|TL],[D1|TD]) :-
   % first the diagonals starting from the top row
   nth1(Index,L1,D1),
   (diagonalp1(Index,1,TL,TD) ;
    diagonalp1(Index,-1,TL,TD)).
diagonal([_|TL],D) :-
   % now the diagonals starting on the first or last square of lower rows
   diagonal2(TL,D).

diagonal2([_|TL],D) :- diagonal2(TL,D).
diagonal2([L1|TL],[D1|TD]) :-
    L1 = [D1|_],
    diagonalp1(1,1,TL,TD).
diagonal2([L1|TL],[D1|TD]) :-
    last(L1,D1), length(L1,N),
    diagonalp1(N,-1,TL,TD).

diagonalp1(_Index,_,[],[]).
diagonalp1(Index,Offset,[L1|TL],D) :-
    I1 is Index+Offset,
    (nth1(I1,L1,D1)
       -> D = [D1|TD], diagonalp1(I1,Offset,TL,TD)
       ;  D = []).

% printing utilities

prboard(B) :- nl,maplist(prrow,B).
prrow(L) :- maplist(pr,L),nl, length(L,N), length(L2,N), maplist(pr,L2),nl.

pr(V) :- var(V),!, write('---|').
pr(0) :- write('   |').
pr(1) :- write(' Q |').
pr(2) :- write(' R |').
pr(3) :- write(' B |').
pr(4) :- write(' K |').

/*
| ?- solve(4,3,R).
walltime(0)

 R | B | Q | B |
---|---|---|---|
 Q | R | K | B |
---|---|---|---|
 B | K | R | Q |
---|---|---|---|
 K | Q | B | R |
---|---|---|---|
R = [[2,3,1,3],[1,2,4,3],[3,4,2,1],[4,1,3,2]] ? 
*/

% solve(5,5,R). takes 0.24 seconds
/*

 R |   | K | B | Q |
---|---|---|---|---|
 B | Q |   | K | R |
---|---|---|---|---|
 B | R | K | Q | B |
---|---|---|---|---|
 Q | K | R | K | B |
---|---|---|---|---|
 B | B | Q | R | B |
---|---|---|---|---|

solve(6,0,R).
4.8 seconds

solve(7,0,R).
walltime(13910)

solve(8,0,R) runs for very long; even if we set 13 bishops and remove knights from domain and from checking
*/


/*
21.6 minutes :
?- solve(7,0,R).
Starting solving 7*7 board for 7 queens/rooks, 12 bishops, 0 knights (start: 30150 ms)
walltime(1296470)

   |   |   | Q | B | B | R |
---|---|---|---|---|---|---|
 B | Q | R |   |   |   |   |
---|---|---|---|---|---|---|
 B | R |   |   |   |   | Q |
---|---|---|---|---|---|---|
 B |   |   | R | Q |   | B |
---|---|---|---|---|---|---|
 R |   | Q |   |   |   | B |
---|---|---|---|---|---|---|
 Q |   |   |   |   | R | B |
---|---|---|---|---|---|---|
 B | B | B |   | R | Q | B |
---|---|---|---|---|---|---|
R = [[0,0,0,1,3,3,2],[3,1,2,0,0,0,0],[3,2,0,0,0,0,1],[3,0,0,2,1,0,3],[2,0,1,0,0,0|...],[1,0,0,0,0|...],[3,3,3,0|...]] ? 


*/