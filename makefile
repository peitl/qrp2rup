CXX = g++
CXXFLAGS = -std=c++11 -Wall -O3

ifeq ($(debug), 1)
	CXXFLAGS += -g
endif

SRCS = grat_manager.cc clause_writer.cc cnf_circuit.cc io.cc proof_translator.cc qrp2rup.cc
OBJS = $(SRCS:.cc=.o)
EXE = qrp2rup

$(EXE): $(OBJS)
	$(CXX) $(CXXFLAGS) $^ -o $@

qrp2rup.o: qrp2rup.cc proof_translator.o cnf_circuit.o clause_writer.o io.o grat_manager.o

proof_translator.o: proof_translator.cc proof_translator.hh sorted_query_oracle.hh defaults.hh

io.o: io.cc proof_translator.hh types.hh

cnf_circuit.o: cnf_circuit.cc cnf_circuit.hh circuit.hh

clause_writer.o: clause_writer.cc clause_writer.hh types.hh

grat_manager.o: grat_manager.cc grat_manager.hh defaults.hh

clean:
	rm -v $(OBJS) $(EXE)
