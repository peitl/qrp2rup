qrp2rup: qrp2rup.cc proof_translator.o clause_writer.o io.o
	g++ -std=c++11 qrp2rup.cc proof_translator.o clause_writer.o io.o -Wall -O3 -o qrp2rup

proof_translator.o: proof_translator.cc proof_translator.hh sorted_query_oracle.hh 
	g++ -std=c++11 -Wall -O3 -c -o proof_translator.o proof_translator.cc

io.o: io.cc proof_translator.hh types.hh
	g++ -std=c++11 io.cc -Wall -O3 -c -o io.o

clause_writer.o: clause_writer.cc clause_writer.hh types.hh
	g++ -std=c++11 clause_writer.cc -Wall -O3 -c -o clause_writer.o

clean:
	rm -v proof_translator.o clause_writer.o io.o
