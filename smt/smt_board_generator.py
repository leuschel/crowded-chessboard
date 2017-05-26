#! /usr/local/bin/python3

# generates the SMT encoding based on the sat encoding, i.e. boolean variables and integer arithmetic for cardinality constraints
import sys

if len(sys.argv) < 2:
    print('command line argument for board size missing')
    sys.exit(1)

n = int(sys.argv[1])
if n not in range(5,17):
    print('command line argument for board size should be between 6 and 16')
    sys.exit(1)

num_queens = n
num_rooks = n
num_bishops = 2*n-2
if n == 5:
    num_knights = 5
elif n == 6:
    num_knights = 9
elif n == 7:
    num_knights = 11
elif n == 8:
    num_knights = 21
elif n == 9:
    num_knights = 29
elif n == 10:
    num_knights = 37
elif n == 11:
    num_knights = 47
elif n == 12:
    num_knights = 57
elif n == 13:
    num_knights = 69
elif n == 14:
    num_knights = 81
elif n == 15:
    num_knights = 94
elif n == 16:
    num_knights = 109

print("(declare-datatypes (T1 T2) ((Pair (mk-pair (first T1) (second T2)))))")
print("(define-fun on_board ((x (Pair Int Int))) Bool (and (<= 1 (first x) " + str(n) + ") (<= 1 (second x) " + str(n) + ")))")
print("(define-fun not_same_row ((x (Pair Int Int)) (y (Pair Int Int))) Bool (not (= (first x) (first y))))")
print("(define-fun not_same_col ((x (Pair Int Int)) (y (Pair Int Int))) Bool (not (= (second x) (second y))))")
print("(define-fun not_same_diagonal ((x (Pair Int Int)) (y (Pair Int Int))) Bool (and (not (= (- (first x) (first y)) (- (second x) (second y)))) (not (= (- 0 (- (first x) (first y))) (- (second x) (second y))))))")
print("(declare-fun board ((Pair Int Int)) Int)")
print("(assert (forall ((x (Pair Int Int))) (<= -1 (board x) 3)))")
print("(assert (forall ((x (Pair Int Int))) (=> (not (on_board x)) (= (board x) -1))))")
print("(define-fun not_reachable_knight ((x (Pair Int Int)) (y (Pair Int Int))) Bool (and (or (not (= 2   (- (first x)  (first y)))) (not (= 1 (- (second x) (second y))))) (or (not (= -2  (- (first x)  (first y)))) (not (= 1   (- (second x) (second y))))) (or (not (= 2   (- (first x)  (first y)))) (not (= -1  (- (second x) (second y)))))         (or (not (= -2  (- (first x)  (first y))))             (not (= -1  (- (second x) (second y))))) (or (not (= 1 (- (first x) (first y)))) (not (= 2 (- (second x) (second y))))) (or (not (= -1  (- (first x)  (first y)))) (not (= 2 (- (second x) (second y))))) (or (not (= 1 (- (first x) (first y)))) (not (= -2  (- (second x) (second y))))) (or (not (= -1  (- (first x)  (first y)))) (not (= -2  (- (second x) (second y)))))))")
print("(assert (forall ((x (Pair Int Int)) (y (Pair Int Int))) (=> (and (= (board x) 0) (= (board y) 0) (not (= x y))) (and (not_same_col x y) (not_same_row x y) (not_same_diagonal x y)))))")
print("(assert (forall ((x (Pair Int Int)) (y (Pair Int Int))) (=> (and (= (board x) 1) (= (board y) 1) (not (= x y))) (and (not_same_col x y) (not_same_row x y)))))")
print("(assert (forall ((x (Pair Int Int)) (y (Pair Int Int))) (=> (and (= (board x) 2) (= (board y) 2) (not (= x y))) (not_same_diagonal x y))))")
print("(assert (forall ((x (Pair Int Int)) (y (Pair Int Int))) (=> (and (= (board x) 3) (= (board y) 3) (not (= x y))) (not_reachable_knight x y))))")

def cardinality_constraint(kind,card):
    print("(assert (exists (")
    for x in range(1,card+1):
        print("(v" + str(x) + "(Pair Int Int))")
    print(") (and (distinct")
    for x in range(1,card+1):
        print(" v" + str(x))
    print(")")
    for x in range(1,card+1):
        print("(= (board v" + str(x) + ")" + str(kind) + ")")
    print(")))")

cardinality_constraint(0,num_queens)
cardinality_constraint(1,num_rooks)
cardinality_constraint(2,num_bishops)
cardinality_constraint(3,num_knights)

print("(check-sat)")
print("(get-model)")
