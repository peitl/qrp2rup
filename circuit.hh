#ifndef _CIRCUIT_H_
#define _CIRCUIT_

#include "types.hh"
#include <vector>

using std::vector;

class Circuit {
	virtual void or_gate(NewVar output, vector<NewLit>::const_iterator begin,
										vector<NewLit>::const_iterator end) = 0;
	virtual void and_gate(NewVar output, vector<NewLit>::const_iterator begin,
										vector<NewLit>::const_iterator end) = 0;
	virtual void or_gate(NewVar output, vector<NewLit>::const_reverse_iterator begin,
										vector<NewLit>::const_reverse_iterator end) = 0;
	virtual void and_gate(NewVar output, vector<NewLit>::const_reverse_iterator begin,
										vector<NewLit>::const_reverse_iterator end) = 0;
	virtual void or_gate(NewVar output, const vector<NewLit>& inputs) = 0;
	virtual void and_gate(NewVar output, const vector<NewLit>& inputs) = 0;

	// virtual void or_gate(NewVar output, vector<OldLit>::const_iterator begin,
	// 									vector<OldLit>::const_iterator end) = 0;
	// virtual void and_gate(NewVar output, vector<OldLit>::const_iterator begin,
	// 									vector<OldLit>::const_iterator end) = 0;
	// virtual void or_gate(NewVar output, vector<OldLit>::const_reverse_iterator begin,
	// 									vector<OldLit>::const_reverse_iterator end) = 0;
	// virtual void and_gate(NewVar output, vector<OldLit>::const_reverse_iterator begin,
	// 									vector<OldLit>::const_reverse_iterator end) = 0;
	// virtual void or_gate(NewVar output, const vector<OldLit>& inputs) = 0;
	// virtual void and_gate(NewVar output, const vector<OldLit>& inputs) = 0;

	virtual void equiv_gate(NewVar output, OldVar input1, NewVar input2) = 0;
	virtual void ite_gate(NewVar output, OldLit query, NewVar val_false, NewVar val_true) = 0;
};

#endif
