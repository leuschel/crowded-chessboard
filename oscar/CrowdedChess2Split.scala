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
 * Crowded Chess 2: Max bishops, Queens and Rooks, while max Knights are from a table
 * 
 * Note: Current order is bishops(200)->rooks(100)->queens(100)->knights(100)->solution
 * 
 */

object CrowdedChess2Split extends CPModel with App {
	
  def alldifferent_except_0(cp: CPSolver, y: Array[CPIntVar]) = {
  for(i <- 0 until y.length; j <- 0 until i) {
    cp.add( ((y(i).isDiff(0)) && (y(j).isDiff(0))) ==> (y(i).isDiff(y(j))))
  }
}
  
	// The sets used for storing intermediate conflicts
  // Each set stores the coordinates, e.g. (x,y) position
	val Qset = scala.collection.mutable.Set[(Int, Int)]() // Queens
	val Rset = scala.collection.mutable.Set[(Int, Int)]() // Rooks
	val Bset = scala.collection.mutable.Set[(Int, Int)]() // Bishops
	
	// Note Knights do not have a conflict set, because they are found at last
			
	// Size of board
	val n = 5;
	
	// The number of each piece
	val nQ = n; // Queens
	val nB = n*2-2; // Bishops
	val nK = 5; // Knights
	val nR = n; // Rooks
	
	// Chess Pieces
	val b = 1; // Bishop
	val q = 2; // Queens
	val r = 3; // Rooks
	val k = 4; // Knights
	
  // Function used to find Knights, Input value defines the number of solutions to be found
	def knights(w: Int)  = new CPModel {

		val Pieces = Set(0, k)

		// Create the board
		val board = Array.fill(n, n)(CPIntVar(Pieces))
		val board_t = board.transpose;

    // Add occupied Rooks positions
		for(i<-Rset){
			add(board(i._1)(i._2)!==k)
		}

		// Add occucpied Bishops positions
		for(i<-Bset){
			add(board(i._1)(i._2)!==k)
		}

		// Add occupied Queens positions
		for(i<-Qset){
			add(board(i._1)(i._2)!==k)
		}

		for(i <- 0 until n; j <- 0 until n){

		  // Add the Knights movement
			val kMove = for(m<- Seq(-2, -1, 1, 2); u <- Seq(-2, -1, 1, 2); 
					if ( (m.abs!=u.abs) && (i+m>=0) && (i+m<n) && (j+u>=0) && (j+u<n)))
				yield board(i+m)(j+u);

			// Add the constraint based on the L shape captured above
			kMove.foreach { t => add(board(i)(j).isEq(k) ==> (t.isDiff(k))) } // the forall test from VDM
		}

		add(gcc(board.flatten.toArray, Array((k,CPIntVar(nK)))))

		// Search heuristic
		search(binaryFirstFail(board.flatten.toSeq))
		
		onSolution {
			println("************Knights Solution****************")
			
			for(i <- 0 until n) { 
				println(board(i).map(j=>"%3d".format(j.value)).mkString(""))
			}

			val t1 = System.currentTimeMillis()
			val t3 = (t1-t0)
			println("Elapsed time: " + t3)
			
			// Hold forever
			while(true){}

		}
		// Execution, search for one solution
		val stats = start(nSols = w)
		println(stats)

	}

	 // Function used to find Queens, Input value defines the number of solutions to be found
	def queens(w: Int)  = new CPModel {

  val Pieces = Set(0, q)

  // Create the board
	val board = Array.fill(n, n)(CPIntVar(Pieces))
	val board_t = board.transpose;

  // Add occupied Rooks positions
	for(i<-Rset){
		add(board(i._1)(i._2)!==q)
	}

	// Add occupied Bishops positions
	for(i<-Bset){
		add(board(i._1)(i._2)!==q)
	}

	// Add constriants for rows and colums
	for(i <- 0 until n){
		add(gcc(board(i), Array((q,CPIntVar(0 to 1))))) // alldifferent rows
		add(gcc(board_t(i), Array((q,CPIntVar(0 to 1))))) // alldifferent rows
	}

	// Add diagonal constraints
	for(i <- 0 until n; j <- 0 until n){
		val qDiag1 = for(m<- 0 until n; if ((m-i+j>=0) && (m-i+j < n) ) ) yield board(m)(m-i+j);
		if(!qDiag1.isEmpty)
		  add(gcc(qDiag1, Array((q,CPIntVar(0 to 1)))))

		val qDiag2 = for(m<- 0 until n; if ((i+j-m>=0) && (i+j-m < n) ) ) yield board(m)(i+j-m);
		if(!qDiag2.isEmpty)
		  add(gcc(qDiag2, Array((q,CPIntVar(0 to 1)))))
		}

		// Global Cardinalicy Constraint (GCC) to number of queens to be found
		add(gcc(board.flatten.toArray, Array((q,CPIntVar(nQ)))))

		search {
			binaryFirstFail(board.flatten.toSeq)
		} 
		onSolution {
		  // We land here upon each solution
			println("*********Queens Solution***************")
			for(i <- 0 until n) { 
				println(board(i).map(j=>"%3d".format(j.value)).mkString(""))
			}

			// Add all the occupied queens positions
			for(i<-0 until n; j <- 0 until n){
				if(board(i)(j).value.toInt!=0){
					Qset += ((i, j))
				}
			}
			
			// Search for 100 knights solution pr. queens solution
			knights(100)
			// Clear the queens occupied postions before finding a new solution
			Qset.clear();
		}

		// Execution, search for one solution
		val stats = start(nSols = w)
		println(stats)

	}

	 // Function used to find Bishops, Input value defines the number of solutions to be found
	def bishop(w: Int)  = new CPModel {
    val Pieces = Set(0, b)

	  // Define board
	  val board = Array.fill(n, n)(CPIntVar(Pieces))
	  val board_t = board.transpose;
	
     // Note: Bishops get called first, so no conflicts set constraints are added. 
  
    // Add diagonals
	  for(i <- 0 until n; j <- 0 until n){
		  val bDiag1 = for(m<- 0 until n; if ((m-i+j>=0) && (m-i+j < n) ) ) yield board(m)(m-i+j);
		  if(!bDiag1.isEmpty)
		    add(gcc(bDiag1, Array((b,CPIntVar(0 to 1)))))

		  val bDiag2 = for(m<- 0 until n; if ((i+j-m>=0) && (i+j-m < n) ) ) yield board(m)(i+j-m);
		  if(!bDiag2.isEmpty) 
		    add(gcc(bDiag2, Array((b,CPIntVar(0 to 1)))))
	}
	
	// GCC constraint for number of bishops
	add(gcc(board.flatten.toArray, Array((b,CPIntVar(nB)))))

	search {
		binaryFirstFail(board.flatten.toSeq)
	} 
	onSolution {
		println("*********Bishops Solution***************")
		for(i <- 0 until n) { 
			println(board(i).map(j=>"%3d".format(j.value)).mkString(""))
		}

		// Add occupied positions of current Bishop solution 
		for(i<-0 until n; j <- 0 until n){
			if(board(i)(j).value.toInt!=0){
				Bset += ((i, j))
			}
		}
		
		// For each bishops solution run 100 solutions for rooks at max
		rooks(100);
		
		// Clear set after each solution
		Bset.clear();
  }
		// Execution, search for one solution
		val stats = start(nSols = w)
		println(stats)
	}

	// Function used to find Rooks, Input value defines the number of solutions to be found
	def rooks(w: Int) = new CPModel {
    val Pieces = Set(0, r)

		// Create board
		val board = Array.fill(n, n)(CPIntVar(Pieces))
		val board_t = board.transpose;

    // Add the Bishops occupied positions
		for(i<-Bset){
			add(board(i._1)(i._2)!==r)
		}

		// For rooks rows and columns are different
		for(i <- 0 until n){
			add(gcc(board(i), Array((r,CPIntVar(0 to 1))))) // alldiffernt rows
			add(gcc(board_t(i), Array((r,CPIntVar(0 to 1))))) // alldifferent columns
		}

		// GCC on number of Rooks to be placed
		add(gcc(board.flatten.toArray, Array((r,CPIntVar(nR)))))

		search {
			binaryFirstFail(board.flatten.toSeq)
		} 
		onSolution {
			println("*********Rooks Solution***************")
			for(i <- 0 until n) { 
				println(board(i).map(j=>"%3d".format(j.value)).mkString(""))
			}
			
			// Add occupied position of rooks for current solution
			for(i<-0 until n; j <- 0 until n){
				if(board(i)(j).value.toInt!=0){
					Rset += ((i, j))
				}
			}
			// Run 100 solution for queens pr. solution for rook
			queens(100);
			
			// Clear rook occupied position for current solution
			Rset.clear();
		}

		// Execution, search for one solution
		val stats = start(nSols = w)
				println(stats)
	}


	/**** This is system start-up ****/
	val t0 = System.currentTimeMillis()
	// Run for 200 solution of bishop
	bishop(200);
	
	println("No solution")
}
