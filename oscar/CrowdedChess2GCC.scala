/*******************************************************************************
 * OscaR is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
 * (at your option) any later version.
 *   
 * OscaR is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License  for more details.
 *   
 * You should have received a copy of the GNU Lesser General Public License along with OscaR.
 * If not, see http://www.gnu.org/licenses/lgpl-3.0.en.html
 ******************************************************************************/

package oscar.examples.evaluation

import oscar.cp._

/**
 Crowded Chessboard Problem from problem 306:
  Dudeney, H. E. Amusements in Mathematics. New York: Dover, pp. 88-89 and 96, 1970.

  Optimal number of bishops: 2*n - 2
 http://mathworld.wolfram.com/BishopsProblem.html
 http://www.gutenberg.org/files/16713/16713-h/16713-h.htm#CHESSBOARD_PROBLEMS
*/

/**
 * Crowded Chess Model: Normal model, where board is a 2 dimensional model
 */

object CrowdedChessGCC extends CPModel with App {

  // Size of board
  val n = 5
  
  // The chess pieces
  val b = 1 // Bishops
  val q = 2 // Queens
  val r = 3 // Rooks
  val k = 4 // Knights
  
  // The board values
  val Pieces = Set(0, b , q , r , k)

  // Number of Bishops (nb) and Knights (nk)
  val nb = n*2-2
  val nk = 5
  
  // Create board
  val board = Array.fill(n, n)(CPIntVar(Pieces))
  val board_t = board.transpose;
  
  for(i <- 0 until n){
    // Queens Rows and Columns
    add(gcc(board(i), Array((q,CPIntVar(0 to 1)))))
    add(gcc(board_t(i), Array((q,CPIntVar(0 to 1)))))
    
    // Rooks Rows and Columns
    add(gcc(board(i), Array((r,CPIntVar(0 to 1)))))
    add(gcc(board_t(i), Array((r,CPIntVar(0 to 1)))))
  }
  
  for(i <- 0 until n; j <- 0 until n){
   
    // Knight Movements
    // This creates the allowed movements for a Knight, e.g. it creates the "L" shape
    val kMove = for(m<- Seq(-2, -1, 1, 2); u <- Seq(-2, -1, 1, 2); if ( (m.abs!=u.abs) && (i+m>=0) && (i+m<n) && (j+u>=0) && (j+u<n)))
      yield board(i+m)(j+u);
     
     // This adds the knights constraint: "if a knight is placed, no other knight can be in its "L" shape"
     kMove.foreach { t => add(board(i)(j).isEq(k) ==> (t.isDiff(k))) } // the forall test from VDM
     
     // This could be used instead of line above, if Knight gets values like 95
     //if(!s.isEmpty)
     //add((board(i)(j)isEq(k))==>(sum(s).isLeEq(90)))
     
   // Queens Diagonals
   val qDiag1 = for(m<- 0 until n; if ((m-i+j>=0) && (m-i+j < n) ) ) yield board(m)(m-i+j);
   if(!qDiag1.isEmpty)
     add(gcc(qDiag1, Array((q,CPIntVar(0 to 1))))) // add Diagonal constraint
   
   val qDiag2 = for(m<- 0 until n; if ((i+j-m>=0) && (i+j-m < n) ) ) yield board(m)(i+j-m);
   if(!qDiag2.isEmpty)
     add(gcc(qDiag2, Array((q,CPIntVar(0 to 1))))) // add Diagonal constraint
       
   // Bishop Diagonals
   val bDiag1 = for(m<- 0 until n; if ((m-i+j>=0) && (m-i+j < n) ) ) yield board(m)(m-i+j);
   if(!bDiag1.isEmpty)
     add(gcc(bDiag1, Array((b,CPIntVar(0 to 1))))) // add Diagonal constraint
   
   val bDiag2 = for(m<- 0 until n; if ((i+j-m>=0) && (i+j-m < n) ) ) yield board(m)(i+j-m);
   if(!bDiag2.isEmpty)
     add(gcc(bDiag2, Array((b,CPIntVar(0 to 1)))))  // add Diagonal constraint
     
  }
  
  // Add global cardinality constraint to force the number of each piece
  add(gcc(board.flatten.toArray, Array((b,CPIntVar(nb))))) // Bishops (nb)
  add(gcc(board.flatten.toArray, Array((q,CPIntVar(n))))) // Queens (n)
  add(gcc(board.flatten.toArray, Array((r,CPIntVar(n))))) // Rooks (n)
  add(gcc(board.flatten.toArray, Array((k,CPIntVar(nk))))) // Knights (nk)
  add(gcc(board.flatten.toArray, Array((0,CPIntVar(n*n-2*n-nb-nk))))) // Empty places (n*n-nb-2*n-nk)
    
  // Search heuristic
  //  NOTE: binaryStatic could also be used
  search(binaryFirstFail(board.flatten.toSeq))
  
  onSolution {
    println("****************************")
    for(i <- 0 until n) { 
         println(board(i).map(j=>"%3d".format(j.value)).mkString(""))
       }
  }
  
  // Execution, search for one solution
  val stats = start(nSols = 1)
  println(stats)
}
