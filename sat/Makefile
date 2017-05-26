sattest: crowded_sat.cnf
	minisat crowded_sat.cnf model.cnf
	cat model.cnf

crowded_sat.cnf: sat_generator.py
	./sat_generator.py 8 > crowded_sat.cnf

board8:
	./sat_generator.py 8 > crowded_sat.cnf
	minisat crowded_sat.cnf model.cnf
board9:
	./sat_generator.py 9 > crowded_sat.cnf
	minisat crowded_sat.cnf model.cnf
board10:
	./sat_generator.py 10 > crowded_sat.cnf
	minisat crowded_sat.cnf model.cnf
board11:
	./sat_generator.py 11 > crowded_sat.cnf
	minisat crowded_sat.cnf model.cnf
board12:
	./sat_generator.py 12 > crowded_sat.cnf
	minisat crowded_sat.cnf model.cnf
board13:
	./sat_generator.py 13 > crowded_sat.cnf
	minisat crowded_sat.cnf model.cnf
board14:
	./sat_generator.py 14 > crowded_sat.cnf
	minisat crowded_sat.cnf model.cnf
board15:
	./sat_generator.py 15 > crowded_sat.cnf
	minisat crowded_sat.cnf model.cnf
board16:
	./sat_generator.py 16 > crowded_sat.cnf
	minisat crowded_sat.cnf model.cnf

SAT4JPATH=/Applications/Development/SAT/sat4j-core-v20130525
sat4jtest: crowded_sat.cnf
	java -jar $(SAT4JPATH)/org.sat4j.core.jar crowded_sat.cnf
