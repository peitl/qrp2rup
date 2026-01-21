#ifndef _CNF_CIRCUIT_H_
#define _CNF_CIRCUIT_H_

#include "circuit.hh"
#include <fstream>
#include <string>

using std::vector;
using std::ofstream;
using std::string;

class CNFCircuit : public Circuit {
	public:
	ofstream ofs;

	CNFCircuit(const string& filename) : ofs(ofstream(filename)) {
		// print a fake prefix to the cnf--later rewrite when values are known
		ofs << "p cnf ____________________ ____________________\n";
	};

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

	virtual void bincls(NewLit a, NewLit b);
	virtual void tercls(NewLit a, NewLit b, NewLit c);

	virtual void close_circuit();
	virtual void close_circuit(NewVar max_var);
};

#endif
