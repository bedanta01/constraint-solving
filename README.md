# constraint-solving
Satisfiability and sat-solvers

# DPLL algorithm implementation:
Uses dimacs input format:

c this is a comment
p cnf 4 5
1 -2 -3 4 0
-1 2 -3 0
-3 4 0
1 3 4 0
-1 2 -4 0

To run the code:

g++ --std=c++11 -o dpll_object DPLL.cpp
dpll_object < input.dimacs
