#!/usr/bin/env python3

import sys
import numpy as np

clauses = [None]
permanent_assignment = set()
temporary_assignment = set()
culprit = 0

def load_cnf(filename):
    global clauses
    num_vars = 0
    num_clauses = 0
    with open(filename) as f:
        for line in f:
            line = line.strip()
            if line[0] == "c":
                continue
            if line[0] == "p":
                num_vars = int(line.split()[2])
                num_clauses = int(line.split()[3])
                continue
            clauses.append(list(map(int, line.split()[:-1])))
    if len(clauses) - 1 != num_clauses:
        print("WARNING: declared (%d) and actual (%d) number of clauses differ!" % (len(clauses) - 1, num_clauses))
    return num_vars

def load_grat(filename):
    return np.ascontiguousarray(np.fromfile(filename, dtype=np.int32)[::-1])

def load_rup(filename):
    rup = []
    with open(filename) as f:
        for line in f:
            rup.append(list(map(int, line.split()[:-1])))
    return rup

def is_unit(clause_id):
    global culprit
    unit_literal = 0
    assignment = permanent_assignment | temporary_assignment
    for lit in clauses[clause_id]:
        if lit in assignment:
            print("ERROR %d NOT UNIT BECAUSE SATISFIED" % clause_id)
            print("Satisfying literal: %d" % lit)
            culprit = clause_id
            return 0
        if -lit not in assignment:
            if unit_literal == 0:
                unit_literal = lit
            else:
                print("ERROR %d NOT UNIT BECAUSE TWO UNDEC" % clause_id)
                print("Undecided literals: %d %d (possibly more)" % (lit, unit_literal))
                culprit = clause_id
                return 0
    if unit_literal == 0:
        print(assignment)
        print([lit for lit in clauses[clause_id]])
        print("ERROR %d NOT UNIT, BUT CONFLICT" % (clause_id))
        culprit = clause_id
    return unit_literal

def is_empty(clause_id):
    global culprit
    assignment = permanent_assignment | temporary_assignment
    for lit in clauses[clause_id]:
        if lit in assignment:
            print("ERROR %d NOT EMPTY BECAUSE SATISFIED" % clause_id)
            print("Satisfying literal: %d" % lit)
            culprit = clause_id
            return False
        if -lit not in assignment:
            print("ERROR %d NOT EMPTY" % clause_id)
            print("Undecided literal: %d (possibly more)" % (lit))
            culprit = clause_id
            return False
    return True


def diagnose(rup, grat):
    global permanent_assignment, temporary_assignment
    next_rup_clause = 0
    grat_head = 0
    conflict_reached = False
    bug = False
    while not bug and grat_head < len(grat):
        if grat[grat_head] == 1:
            grat_head += 1
            while grat[grat_head] != 0:
                unit_literal = is_unit(grat[grat_head])
                if unit_literal == 0:
                    print("Failed while trying to claim a clause unit")
                    bug = True
                    break
                else:
                    permanent_assignment.add(unit_literal)
                grat_head += 1
        elif grat[grat_head] == 3:
            for lit in rup[next_rup_clause]:
                temporary_assignment.add(-lit)
            grat_head += 1
            current_id = grat[grat_head]
            grat_head += 1
            while grat[grat_head] != 0:
                unit_literal = is_unit(grat[grat_head])
                if unit_literal == 0:
                    print("Failed while trying to claim a clause unit to prove %d RUP" % current_id)
                    bug = True
                    break
                else:
                    temporary_assignment.add(unit_literal)
                grat_head += 1
            if not bug:
                grat_head += 1
                if grat[grat_head] == 0:
                    print("Conflict clause for lemma %d is 0, should be a positive id" % current_id)
                    bug = True
                elif not is_empty(grat[grat_head]):
                    print("Invalid conflict for candidate RUP clause %d" % current_id)
                    bug = True
                else:
                    temporary_assignment = set()
                    clauses.append(rup[next_rup_clause])
                    next_rup_clause += 1
        elif grat[grat_head] == 5:
            grat_head += 1
            if grat[grat_head] == 0:
                print("Final conflict clause is 0, should be a positive id")
                bug = True
            elif not is_empty(grat[grat_head]):
                print("Claimed conflict is not a conflict")
                bug = True
        grat_head += 1
    if not bug:
        print("OK")
    else:
        print("Proof check failed")
        if culprit != 0:
            print("Permanent assignment: " + " ".join(map(str, permanent_assignment)))
            print("Temporary assignment: " + " ".join(map(str, temporary_assignment)))
            print("Culprit: " + " ".join(map(str, clauses[culprit])))
        else:
            print("Syntax error detected")


def main(cnf_filename, rup_filename, grat_filename):
    global permanent_assignment, temporary_assignment
    num_vars = load_cnf(cnf_filename)
    #permanent_assignment = [0] * (num_vars + 1)
    #temporary_assignment = [0] * (num_vars + 1)
    rup = load_rup(rup_filename)
    grat = load_grat(grat_filename)
    diagnose(rup, grat)

if __name__ == "__main__":
    if len(sys.argv) == 2:
        main(sys.argv[1] + ".qrp.cnf", sys.argv[1] + ".qrp.rup", sys.argv[1] + ".qrp.grat")
    else:
        main(sys.argv[1], sys.argv[2], sys.argv[3]);
