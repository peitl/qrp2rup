qrp2rup: qrp2rup.cc ProofTranslator
	g++ -std=c++11 qrp2rup.cc proof_translator.o -Wall -O3 -o qrp2rup

ProofTranslator: proof_translator.cc clause_writer.hh proof_translator.hh rfao_node.hh sorted_query_oracle.hh types.hh 
	g++ -std=c++11 proof_translator.cc -Wall -O3 -c -o proof_translator.o
