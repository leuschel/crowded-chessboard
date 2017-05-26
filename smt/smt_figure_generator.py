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
#print("(define-fun not_same_col ((x (Pair Int Int)) (y (Pair Int Int))) Bool (not (= (second x) (second y))))")
print("(define-fun not_same_diagonal ((x (Pair Int Int)) (y (Pair Int Int))) Bool (and (not (= (- (first x) (first y)) (- (second x) (second y)))) (not (= (- 0 (- (first x) (first y))) (- (second x) (second y))))))")
print("(define-fun not_reachable_knight ((x (Pair Int Int)) (y (Pair Int Int))) Bool (and (or (not (= 2   (- (first x)  (first y)))) (not (= 1 (- (second x) (second y))))) (or (not (= -2  (- (first x)  (first y)))) (not (= 1   (- (second x) (second y))))) (or (not (= 2   (- (first x)  (first y)))) (not (= -1  (- (second x) (second y)))))         (or (not (= -2  (- (first x)  (first y))))             (not (= -1  (- (second x) (second y))))) (or (not (= 1 (- (first x) (first y)))) (not (= 2 (- (second x) (second y))))) (or (not (= -1  (- (first x)  (first y)))) (not (= 2 (- (second x) (second y))))) (or (not (= 1 (- (first x) (first y)))) (not (= -2  (- (second x) (second y))))) (or (not (= -1  (- (first x)  (first y)))) (not (= -2  (- (second x) (second y)))))))")

# queen constraints
for x in range(1,num_queens+1):
    print("(declare-fun q" + str(x) + "() (Pair Int Int))")
    print("(assert (= (first q" + str(x) + ") " + str(x) + "))")
    print("(assert (on_board q" + str(x) + "))")
    
print("(assert (distinct ")
for x in range(1,num_queens+1):
    print("(second q" + str(x) + ")")
print("))")

for x in range(1,num_queens):
    for y in range(x+1,num_queens+1):
        print("(assert (not_same_diagonal q" + str(x) + " q" + str(y) + "))")
        
# rook constraints
for x in range(1,num_rooks+1):
    print("(declare-fun r" + str(x) + "() (Pair Int Int))")
    print("(assert (= (first r" + str(x) + ") " + str(x) + "))")
    print("(assert (on_board r" + str(x) + "))")
    
print("(assert (distinct ")
for x in range(1,num_rooks+1):
    print("(second r" + str(x) + ")")
print("))")

# bishop constraints
for x in range(1,num_bishops+1):
    print("(declare-fun b" + str(x) + "() (Pair Int Int))")
    print("(assert (on_board b" + str(x) + "))")
    
for x in range(1,num_bishops):
    for y in range(x+1,num_bishops+1):
        print("(assert (not_same_diagonal b" + str(x) + " b" + str(y) + "))")
        
# knight constraints
for x in range(1,num_knights+1):
    print("(declare-fun k" + str(x) + "() (Pair Int Int))")
    print("(assert (on_board k" + str(x) + "))")
    
for x in range(1,num_knights):
    for y in range(x+1,num_knights+1):
        print("(assert (not_reachable_knight k" + str(x) + " k" + str(y) + "))")
        
# figures do not share positions
print("(assert (distinct")
for x in range(1,num_queens+1):
    print(" q" + str(x)) 
for x in range(1,num_rooks+1):
    print(" r" + str(x)) 
for x in range(1,num_bishops+1):
    print(" b" + str(x)) 
for x in range(1,num_knights+1):
    print(" k" + str(x)) 
print("))")

print("(check-sat)")
print("(get-model)")

