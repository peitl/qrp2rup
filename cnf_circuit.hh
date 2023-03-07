#ifndef _CNF_CIRCUIT_H_
#define _CNF_CIRCUIT_H_

#include "circuit.hh"
#include <ostream>
#include <fstream>
#include <iostream>
#include <string>

using std::vector;
using std::ofstream;
using std::string;

class CNFCircuit : public Circuit {
	public:
	ClauseCNT num_clauses; 
	ofstream ofs;

	CNFCircuit(const string& filename) : num_clauses(0), ofs(ofstream(filename)) {};

	virtual void or_gate(NewVar output, vector<NewLit>::const_iterator begin,
										vector<NewLit>::const_iterator end);
	virtual void and_gate(NewVar output, vector<NewLit>::const_iterator begin,
										vector<NewLit>::const_iterator end);
	virtual void or_gate(NewVar output, vector<NewLit>::const_reverse_iterator begin,
										vector<NewLit>::const_reverse_iterator end);
	virtual void and_gate(NewVar output, vector<NewLit>::const_reverse_iterator begin,
										vector<NewLit>::const_reverse_iterator end);
	virtual void or_gate(NewVar output, const vector<NewLit>& inputs);
	virtual void and_gate(NewVar output, const vector<NewLit>& inputs);

	virtual void equiv_gate(NewVar output, OldVar input1, NewVar input2);
	virtual void ite_gate(NewVar output, OldLit query, NewVar val_false, NewVar val_true);

	virtual void close_circuit(NewVar max_var);
};

#endif
