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

def var_name(kind,x,y):
    return kind + "_" + str(x) + "_" + str(y)

def make_vars(kind):
    for numx in range(1,n+1):
        for numy in range(1,n+1):
            print("(declare-fun " + var_name(kind,numx,numy) + "() Bool)")

def not_used_by(x,y):
    for numx in range(1,n+1):
        for numy in range(1,n+1):
            print("(assert (=> " + var_name(x,numx,numy) + " (not " + var_name(y,numx,numy) + ")))")

def does_not_share_rows(kind):
    for numx in range(1,n+1):
        for numy in range(1,n+1):
            for row in {x for x in range(1,n+1) if x != numx}:
                print("(assert (=> " + var_name(kind,numx,numy) + " (not " + var_name(kind,row,numy) + ")))")

def does_not_share_cols(kind):
    for numx in range(1,n+1):
        for numy in range(1,n+1):
            for col in {x for x in range(1,n+1) if x != numy}:
                print("(assert (=> " + var_name(kind,numx,numy) + " (not " + var_name(kind,numx,col) + ")))")

def does_not_share_diagonals(kind):
    for numx in range(1,n+1):
        for numy in range(1,n+1):
            for (dx, dy) in {(x,y) for x in range(numx+1,n+1) for y in range(numy+1,n+1) if numx-x == numy-y}:
                print("(assert (=> " + var_name(kind,numx,numy) + " (not " + var_name(kind,dx,dy) + ")))")

    for numx in range(1,n+1):
        for numy in range(1,n+1):
            for (dx, dy) in {(x,y) for x in range(1,n+1) for y in range(1,n+1) if -(numx-x) == numy-y if numx != x if numy != y}:
                print("(assert (=> " + var_name(kind,numx,numy) + " (not " + var_name(kind,dx,dy) + ")))")

def cardinality_constraint(kind,card):
    print("(assert (= " + str(card) + " (+")
    for numx in range(1,n+1):
        for numy in range(1,n+1):
            print("(if " + var_name(kind,numx,numy) + " 1 0)")
    print(")))")


kinds = ["queen","rook","bishop","knight"]
pairs = {(x,y) for x in kinds for y in kinds if x != y}

for kind in kinds:
    make_vars(kind)

for (kinda,kindb) in pairs:
    not_used_by(kinda,kindb)

for kind in ["queen", "rook"]:
    does_not_share_cols(kind)
    does_not_share_rows(kind)

for kind in ["queen", "bishop"]:
    does_not_share_diagonals(kind)

# encode knights movement
for numx in range(1,n+1):
    for numy in range(1,n+1):
        for (otherx,othery) in {(numx+1,numy+2),(numx-1,numy+2),(numx+1,numy-2),(numx-1,numy-2),(numx+2,numy+1),(numx+2,numy-1),(numx-2,numy+1),(numx-2,numy-1)}:
            if otherx > 0 and otherx < n+1 and othery > 0 and othery < n+1:
                print("(assert (=> " + var_name("knight",numx,numy) + " (not " + var_name("knight",otherx,othery) + ")))")

cardinality_constraint("queen",num_queens)
cardinality_constraint("rook",num_rooks)
cardinality_constraint("bishop",num_bishops)
cardinality_constraint("knight",num_knights)

print("(check-sat)")
print("(get-model)")
