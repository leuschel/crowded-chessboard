#! /usr/local/bin/python3

import sys

cnfvars = {}
nextvar = 1
tempcounter = 0

def var_name(kind,x,y):
    return kind + "_" + str(x) + "_" + str(y)

def get_var(key):
    global cnfvars
    global nextvar
    if not key in cnfvars:
        cnfvars[key] = str(nextvar)
        nextvar += 1
    return cnfvars[key]

def get_temp_var():
    global tempcounter
    tempcounter += 1
    return "temp" + str(tempcounter)

def setup_vars(kind,n):
    for numx in range(1,n+1):
        for numy in range(1,n+1):
            get_var(var_name(kind,numx,numy))

def not_used_by(x,y,n):
    new_string = []
    for numx in range(1,n+1):
        for numy in range(1,n+1):
            new_string += ["-" + get_var(var_name(x,numx,numy)) + " -" + get_var(var_name(y,numx,numy)) + " 0"]
    return new_string

def does_not_share_rows(kind,n):
    new_string = []
    for numx in range(1,n+1):
        for numy in range(1,n+1):
            for row in {x for x in range(1,n+1) if x != numx}:
                new_string += ["-" + get_var(var_name(kind,numx,numy)) + " -" + get_var(var_name(kind,row,numy)) + " 0"]
    return new_string

def does_not_share_cols(kind,n):
    new_string = []
    for numx in range(1,n+1):
        for numy in range(1,n+1):
            for col in {x for x in range(1,n+1) if x != numy}:
                new_string += ["-" + get_var(var_name(kind,numx,numy)) + " -" + get_var(var_name(kind,numx,col)) + " 0"]
    return new_string

def does_not_share_diagonals(kind,n):
    new_string = []
    for numx in range(1,n+1):
        for numy in range(1,n+1):
            for (dx, dy) in {(x,y) for x in range(numx+1,n+1) for y in range(numy+1,n+1) if numx-x == numy-y}:
                new_string += ["-" + get_var(var_name(kind,numx,numy)) + " -" + get_var(var_name(kind,dx,dy)) + " 0"]

    for numx in range(1,n+1):
        for numy in range(1,n+1):
            for (dx, dy) in {(x,y) for x in range(1,n+1) for y in range(1,n+1) if -(numx-x) == numy-y if numx != x if numy != y}:
                new_string += ["-" + get_var(var_name(kind,numx,numy)) + " -" + get_var(var_name(kind,dx,dy)) + " 0"]
    return new_string

def HA_sum(a,b):
    c = get_temp_var()
    new_string = []
    new_string += ["-" + get_var(a) + " -" + get_var(b) + " -" + get_var(c) + " 0"]
    new_string += [get_var(a) + " " + get_var(b) + " -" + get_var(c) + " 0"]
    new_string += [get_var(a) + " -" + get_var(b) + " " + get_var(c) + " 0"]
    new_string += ["-" + get_var(a) + " " + get_var(b) + " " + get_var(c) + " 0"]
    return new_string, c

def HA_carry(a,b):
    c = get_temp_var()
    new_string = []
    new_string += ["-" + get_var(a) + " -" + get_var(b) + " " + get_var(c) + " 0"]
    new_string += [get_var(a) + " -" + get_var(c) + " 0"]
    new_string += [get_var(b) + " -" + get_var(c) + " 0"]
    return new_string, c

def FA_sum(a,b,c):
    x = get_temp_var()
    new_string = []

    new_string += [get_var(a) + " " + get_var(b) + " " + get_var(c) + " -" + get_var(x) + " 0"]
    new_string += [get_var(a) + " -" + get_var(b) + " -" + get_var(c) + " -" + get_var(x) + " 0"]
    new_string += ["-" + get_var(a) + " " + get_var(b) + " -" + get_var(c) + " -" + get_var(x) + " 0"]
    new_string += ["-" + get_var(a) + " -" + get_var(b) + " " + get_var(c) + " -" + get_var(x) + " 0"]

    new_string += ["-" + get_var(a) + " -" + get_var(b) + " -" + get_var(c) + " " + get_var(x) + " 0"]
    new_string += ["-" + get_var(a) + " " + get_var(b) + " " + get_var(c) + " " + get_var(x) + " 0"]
    new_string += ["" + get_var(a) + " -" + get_var(b) + " " + get_var(c) + " " + get_var(x) + " 0"]
    new_string += ["" + get_var(a) + " " + get_var(b) + " -" + get_var(c) + " " + get_var(x) + " 0"]

    return new_string, x

def FA_carry(a,b,c):
    x = get_temp_var()
    new_string = []

    new_string += ["-" + get_var(b) + " -" + get_var(c) + " " + get_var(x) + " 0"]
    new_string += ["-" + get_var(a) + " -" + get_var(c) + " " + get_var(x) + " 0"]
    new_string += ["-" + get_var(a) + " -" + get_var(b) + " " + get_var(x) + " 0"]

    new_string += [get_var(b) + " " + get_var(c) + " -" + get_var(x) + " 0"]
    new_string += [get_var(a) + " " + get_var(c) + " -" + get_var(x) + " 0"]
    new_string += [get_var(a) + " " + get_var(b) + " -" + get_var(x) + " 0"]

    return new_string, x

def card_constraints_totalizer(kind,card,n):
    inputs = []
    for numx in range(1,n+1):
        for numy in range(1,n+1):
            inputs.append(var_name(kind,numx,numy))
    output_vars, new_constraints = card_constraints_totalizer_aux(inputs)
    for x in range(len(output_vars)):
        if x < card:
            new_constraints += ([get_var(output_vars[x]) + " 0"])
        else:
            new_constraints += (["-" + get_var(output_vars[x]) + " 0"])
    return new_constraints

def card_constraints_totalizer_aux(inputs):
    if len(inputs) == 1:
        return inputs, []
    else:
        left = inputs[:len(inputs)//2]
        right = inputs[len(inputs)//2:]
        left_vars, left_constraints = card_constraints_totalizer_aux(left)
        right_vars, right_constraints = card_constraints_totalizer_aux(right)
        constraints = left_constraints
        constraints.extend(right_constraints)
        outputs = []
        for i in range(len(inputs)):
            outputs.append(get_temp_var())
        c1_vars = {(a,b,r) for a in range(len(left_vars)+1) for b in range(len(right_vars)+1) for r in range(1,len(outputs)+1) if r == a+b}
        c2_vars = {(a+1,b+1,r+1) for a in range(len(left_vars)+1) for b in range(len(right_vars)+1) for r in range(len(outputs)) if r == a+b}
        constraints.extend([totalizer_c1(x,left_vars,right_vars,outputs) for x in c1_vars])
        constraints.extend([totalizer_c2(x,left_vars,right_vars,outputs) for x in c2_vars])
        return outputs, constraints

def totalizer_c1(var_tuple,left_vars,right_vars,outputs):
    (a,b,r) = var_tuple
    if a == 0 and b == 0:
        return get_var(outputs[r-1]) + " 0"
    if a == 0:
        return "-" + get_var(right_vars[b-1]) + " " + get_var(outputs[r-1]) + " 0"
    if b == 0:
        return "-" + get_var(left_vars[a-1]) + " " + get_var(outputs[r-1]) + " 0"
    return "-" + get_var(left_vars[a-1]) + " -" + get_var(right_vars[b-1]) + " " + get_var(outputs[r-1]) + " 0"

def totalizer_c2(var_tuple,left_vars,right_vars,outputs):
    (a,b,r) = var_tuple
    if a > len(left_vars) and b > len(right_vars):
        return "-" + get_var(outputs[r-1]) + " 0"
    if a > len(left_vars):
        return get_var(right_vars[b-1]) + " -" + get_var(outputs[r-1]) + " 0"
    if b > len(right_vars):
        return get_var(left_vars[a-1]) + " -" + get_var(outputs[r-1]) + " 0"
    return get_var(left_vars[a-1]) + " " + get_var(right_vars[b-1]) + " -" + get_var(outputs[r-1]) + " 0"

def card_constraints_adder(kind,card,n):
    new_string = []
    buckets = {0: []}
    for numx in range(1,n+1):
        for numy in range(1,n+1):
            buckets[0].append(var_name(kind,numx,numy))
    #import pdb; pdb.set_trace()
    cur_level = 0
    while(cur_level in buckets):
        while len(buckets[cur_level]) > 1:
            if not cur_level+1 in buckets:
                buckets[cur_level+1] = []

            # use full adder if at least three variables
            if len(buckets[cur_level]) > 2:
                var1 = buckets[cur_level].pop()
                var2 = buckets[cur_level].pop()
                var3 = buckets[cur_level].pop()

                s, r = FA_sum(var1,var2,var3)
                new_string += s
                buckets[cur_level].append(r)

                s, r = FA_carry(var1,var2,var3)
                new_string += s
                buckets[cur_level+1].append(r)

            else:
                # half adder for the remaining two
                var1 = buckets[cur_level].pop()
                var2 = buckets[cur_level].pop()

                s, r = HA_sum(var1,var2)
                new_string += s
                buckets[cur_level].append(r)

                s, r = HA_carry(var1,var2)
                new_string += s
                buckets[cur_level+1].append(r)
        cur_level += 1

    binary = [int(x) for x in bin(card)[2:]]
    binary.reverse()
    for i in buckets:
        if i in range(0,len(binary)):
            if binary[i]:
                new_string += [get_var(buckets[i][0]) + " 0"]
            else:
                new_string += ["-" + get_var(buckets[i][0]) + " 0"]
        else:
            new_string += ["-" + get_var(buckets[i][0]) + " 0"]
    return new_string


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

kinds = ["queen","rook","bishop","knight"]
pairs = {(x,y) for x in kinds for y in kinds if x != y}

output = []
num_clauses = 0

for kind in kinds:
    setup_vars(kind,n)

for (kinda,kindb) in pairs:
    s = not_used_by(kinda,kindb,n)
    output += s

for kind in ["queen", "rook"]:
    s = does_not_share_cols(kind,n)
    output += s
    s = does_not_share_rows(kind,n)
    output += s

for kind in ["queen", "bishop"]:
    s = does_not_share_diagonals(kind,n)
    output += s

# encode knights movement
for numx in range(1,n+1):
    for numy in range(1,n+1):
        for (otherx,othery) in {(numx+1,numy+2),(numx-1,numy+2),(numx+1,numy-2),(numx-1,numy-2),(numx+2,numy+1),(numx+2,numy-1),(numx-2,numy+1),(numx-2,numy-1)}:
            if otherx in range(1,n+1) and othery in range(1,n+1):
                output += ["-" + get_var(var_name("knight",numx,numy)) + " -" + get_var(var_name("knight",otherx,othery)) + " 0"]

s = card_constraints_adder("queen",num_queens,n)
output += s

s = card_constraints_adder("rook",num_rooks,n)
output += s

s = card_constraints_adder("bishop",num_bishops,n)
output += s

s = card_constraints_adder("knight",num_knights,n)
output += s

print("c crowded chess board")
for k in cnfvars:
    print("c " + str(k) + " is " + cnfvars[k])
print("p cnf " + str(len(cnfvars)) + " " + str(len(output)))
print("\n".join(output))
