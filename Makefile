
PROBCLI=probcli


sat-bench:
	echo "Everything as SAT"
	python sat/sat_generator.py 6 > sat/crowded_sat.cnf
	time z3 sat/crowded_sat.cnf
	#time minisat sat/crowded_sat.cnf
smt-bench:
	echo "Everything as SMTLIB, piece --> board position"
	python smt/smt_figure_generator.py 6 > smt/crowded_figure.smt2 && time z3 smt/crowded_figure.smt2
smt-bench2:
	echo "Everything as SMTLIB, board position --> piece"
	python smt/smt_board_generator.py 6 > smt/crowded_figure.smt2 && time z3 smt/crowded_figure.smt2
smt-bench3:
	echo "Cardinality using SMTLIB, rest is SAT"
	python smt/smt_sat_generator.py 6 > smt/crowded_figure.smt2 && time z3 smt/crowded_figure.smt2

prob-bench-elegant:
	echo "Solving n=4 with 5 bishops and 3 Knights using ProB's default solver"
	time $(PROBCLI) B/Crowded_Elegant4.mch -init -silent
	echo "Solving n=5 with 8 bishops and 5 Knights using ProB's default solver"
	time $(PROBCLI) B/Crowded_Elegant5.mch -init -silent
	echo "Solving n=6 with 10 bishops and 7 Knights using ProB's default solver"
	time $(PROBCLI) B/Crowded_Elegant6.mch -init -silent
prob-bench:
	echo "Solving n=6 with 5 Knights using ProB+Kodkod and Glucose"
	time $(PROBCLI) B/SAT_Kodkod_Generator5.mch -init -silent
	echo "Solving n=6 with 9 Knights using ProB+Kodkod and Glucose"
	time $(PROBCLI) B/SAT_Kodkod_Generator6.mch -init -silent
	echo "Solving n=7 with 11 Knights using ProB+Kodkod and Glucose"
	time $(PROBCLI) B/SAT_Kodkod_Generator7.mch -init -silent 
	echo "Solving n=8 with 21 Knights using ProB+Kodkod and Glucose"
	time $(PROBCLI) B/SAT_Kodkod_Generator.mch -init -silent
	echo "Solving n=8 with 22 Knights using ProB+Kodkod and Glucose (UNSAT)"
	time $(PROBCLI) B/SAT_Kodkod_Generator8Unsat.mch -init -silent -expcterr setup_constants_fails
	echo "Solving n=9 with 29 Knights using ProB+Kodkod and Glucose"
	time $(PROBCLI) B/SAT_Kodkod_Generator9.mch -init -silent

