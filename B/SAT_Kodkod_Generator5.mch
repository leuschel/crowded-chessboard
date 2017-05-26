MACHINE SAT_Generator
/*
 Crowded Chessboard Problem from problem 306:
  Dudeney, H. E. Amusements in Mathematics. New York: Dover, pp. 88-89 and 96, 1970.

For n=6 with 9 knights: 1.6 - 3.58 secs  (4.26 secs without sym break)

*/

DEFINITIONS
      SET_PREF_MAX_INITIALISATIONS == 1;
      EXTERNAL_PREDICATE_KODKOD(T1,T2) == INTEGER*T1*T2*BOOL;
      KODKOD(ID,Ids,WaitIds,BoolExpr)==BoolExpr=TRUE;
      EXTERNAL_PREDICATE_KODKOD_SOLVE(T1,T2) == INTEGER*T1*T2;
      KODKOD_SOLVE(ID,Ids,WaitIds)==(1=1);
	  EXTERNAL_PREDICATE_LEQ_SYM_BREAK(X)==X*X;
	  LEQ_SYM_BREAK(x,y)==(1=1);

      "LibraryIO.def";      
      "LibrarySTRINGS.def";
      Idx == (1..n)*(1..n);
      arrpos(i,j) == (i-1)*n+j; // converting two dimensional coordinates to one dimensional
      
      /* printing constraints for an encoding board: Idx --> PIECES */
      pdiff == {piece,i,j,i2,j2,s| piece:PIECES & (i,j) : Idx & (i2,j2):attack(piece)(i,j) &
                  s = FORMAT_TO_STRING("(board(~w)=~w => board(~w)/=~w) ",
                          [INT_TO_STRING(arrpos(i,j)),TO_STRING(piece),
                           INT_TO_STRING(arrpos(i2,j2)),TO_STRING(piece)])};
      prdiff == {x|x:ran(pdiff) & printf("~w &~n",x)};
      
      /* printing constraints for an encoding boardNR : PIECES */
      pdiff2 == {piece,i,j,i2,j2,s| piece:PIECES & (i,j) : Idx & (i2,j2):attack(piece)(i,j) &
                  s = FORMAT_TO_STRING("(board~w=~w => board~w/=~w) ",
                          [INT_TO_STRING(arrpos(i,j)),TO_STRING(piece),
                           INT_TO_STRING(arrpos(i2,j2)),TO_STRING(piece)])};
      prdiff2 == {x|x:ran(pdiff2) & printf("~w &~n",x)};
      prbrd2 == {x|x:1..(n**2) & printf("board~w, ",x)};
      
      /* printing constraints for an encoding boardNrPiece : BOOL */
      pdiff3 == {piece,i,j,i2,j2,s| piece:PIECES & (i,j) : Idx & (i2,j2):attack(piece)(i,j) &
                  s = FORMAT_TO_STRING("(board~w~w=TRUE => board~w~w=FALSE) ",
                          [INT_TO_STRING(arrpos(i,j)),TO_STRING(piece),
                           INT_TO_STRING(arrpos(i2,j2)),TO_STRING(piece)])};
      prdiff3 == {x|x:ran(pdiff3) & printf("~w &~n",x)};
      prbrd3 == {x|x:1..(n**2) & printf("board~wQueen, ",x) & printf("board~wRook, ",x) & printf("board~wBishop, ",x) & printf("board~wKnight, ",x) };
      pratmost3 == {x|x:1..(n**2) & printf("~nAT_MOST_ONE(board~wQueen,",x) & printf("board~wRook,",x) & printf("board~wBishop,",x) & printf("board~wKnight) &",x) };
      
      AT_MOST_ONE(Q,R,B,K) == (Q=TRUE => (R=FALSE & B=FALSE & K=FALSE)) & (R=TRUE => (B=FALSE & K=FALSE)) & (B=TRUE => K=FALSE);
      
      
      ANIMATION_FUNCTION_DEFAULT == ( {r,c,i|r:1..n & c:1..n & i=board((r-1)*n+c) }  );
      ANIMATION_FUNCTION == ( {r,c,i|r:1..n & c:1..n & i=15 & (r+c)mod 2 = 0 & Empty=board((r-1)*n+c) }  );
      ANIMATION_IMG1 == "ChessPieces/Chess_qll45.gif";
      ANIMATION_IMG2 == "ChessPieces/Chess_rll45.gif";
      ANIMATION_IMG3 == "ChessPieces/Chess_bll45.gif";
      ANIMATION_IMG4 == "ChessPieces/Chess_nll45.gif";
      ANIMATION_IMG5 == "ChessPieces/Chess_emptyl45.gif";
      ANIMATION_IMG11 == "ChessPieces/Chess_qld45.gif";
      ANIMATION_IMG12 == "ChessPieces/Chess_rld45.gif";
      ANIMATION_IMG13 == "ChessPieces/Chess_bld45.gif";
      ANIMATION_IMG15 == "ChessPieces/Chess_emptyd45.gif";
      
      SET_PREF_KODKOD == FALSE;
      SET_PREF_KODKOD_ONLY_FULL == FALSE;
      SET_PREF_KODKOD_MAX_NR_SOLS == 1;
      SET_PREF_KODKOD_SAT_SOLVER == "glucose";
      SET_PREF_KODKOD_SYMMETRY == 20;
      
      SET_PREF_TRACE_INFO == FALSE;
      SET_PREF_TIME_OUT == 145000;

      NBSHP == 8;  
      NKGHT == 5; 
SETS
  PIECES = {Queen, Rook, Bishop, Knight,Empty}
ABSTRACT_CONSTANTS
   dist
CONSTANTS
   n, same_row_or_col, same_diagonal, knight_move, attack, board
PROPERTIES
  n=5
  &
  /* computing distance between two indices: */
  dist = %(i,j).(i:INTEGER & j:INTEGER| IF i>=j THEN i-j ELSE j-i END)
  &
  
  /* auxiliary functions to compute attacking positions : */
  same_row_or_col = %(i,j).(i:1..n & j:1..n | {i2,j2|i2:1..n & j2:1..n & (i,j) /= (i2,j2) & (i=i2 or j=j2)})
  &
  same_diagonal = %(i,j).(i:1..n & j:1..n | {i2,j2|i2:1..n & j2:1..n & (i,j) /= (i2,j2) & (i2-i=j2-j or i-i2=j2-j)})
  &
  knight_move = %(i,j).(i:1..n & j:1..n | {i2,j2|i2:1..n & j2:1..n & i/=i2 & j/=j2 & dist(i,i2)+dist(j,j2)=3})
  &
  attack = {Rook |-> same_row_or_col,
            Bishop |-> same_diagonal,
            Queen |-> %p.(p:(1..n)*(1..n)| same_row_or_col(p) \/ same_diagonal(p)),
            Knight |-> knight_move,
            Empty |-> ((1..n)*(1..n))*{{}}
            }
  
 &
  board : INTEGER <-> PIECES
  
  &
  KODKOD(1,board,n,bool(board : (1..(n*n)) --> PIECES))
  &
  
  KODKOD(1,board,n,bool(
   card({p| p:dom(board) & board(p)=Queen}) = n &
   card({p| p:dom(board) & board(p)=Rook}) = n &
   card({p| p:dom(board) & board(p)=Bishop}) = NBSHP &
   card({p| p:dom(board) & board(p)=Knight}) = NKGHT &
   card({p| p:dom(board) & board(p)=Empty}) = (n*n - 2*n - NBSHP - NKGHT) ))
  
  
  &
  !(piece,i,j,i2,j2).( piece:PIECES & (i,j) : Idx & (i2,j2):attack(piece)(i,j)
                       & LEQ_SYM_BREAK((i,j),(i2,j2)) // optional symmetry breaking
     => KODKOD(1,board,(attack,i,j,i2,j2),bool(board(arrpos(i,j))=piece => board(arrpos(i2,j2))/=piece)))

   &
   KODKOD_SOLVE(1,(board,n),(n,attack))
ASSERTIONS
   board : (1..(n*n)) --> PIECES;
  
   card({p| p:dom(board) & board(p)=Queen}) = n;
   card({p| p:dom(board) & board(p)=Rook}) = n;
   card({p| p:dom(board) & board(p)=Bishop}) = NBSHP;
   card({p| p:dom(board) & board(p)=Knight}) = NKGHT;
   card({p| p:dom(board) & board(p)=Empty}) = (n*n - 2*n - NBSHP - NKGHT);

  !(piece,i,j,i2,j2).( piece:PIECES & (i,j) : Idx & (i2,j2):attack(piece)(i,j)
     => (board(arrpos(i,j))=piece => board(arrpos(i2,j2))/=piece))
END

