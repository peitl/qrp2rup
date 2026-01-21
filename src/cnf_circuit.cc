#include "cnf_circuit.hh"
#include <iomanip>

void CNFCircuit::or_gate(NewVar output, vector<NewLit>::const_iterator begin,
										vector<NewLit>::const_iterator end) {
    for (std::vector<NewLit>::const_iterator it = begin; it != end; it++) {
        ofs << -*it << " " << output << " 0\n";
    }
    for (std::vector<NewLit>::const_iterator it = begin; it != end; it++) {
        ofs << *it << " ";
    }
    ofs << -output << " 0\n";

    num_clauses += end - begin + 1;
}

void CNFCircuit::and_gate(NewVar output, vector<NewLit>::const_iterator begin,
										 vector<NewLit>::const_iterator end) {
    for (std::vector<NewLit>::const_iterator it = begin; it != end; it++) {
        ofs << *it << " " << -output << " 0\n";
    }
    for (typename std::vector<NewLit>::const_iterator it = begin; it != end; it++) {
        ofs << -*it << " ";
    }
    ofs << output << " 0\n";

    num_clauses += end - begin + 1;
}

void CNFCircuit::or_gate(NewVar output, vector<NewLit>::const_reverse_iterator begin,
										vector<NewLit>::const_reverse_iterator end) {
    for (std::vector<NewLit>::const_reverse_iterator it = begin; it != end; it++) {
        ofs << -*it << " " << output << " 0\n";
    }
    for (std::vector<NewLit>::const_reverse_iterator it = begin; it != end; it++) {
        ofs << *it << " ";
    }
    ofs << -output << " 0\n";

    num_clauses += end - begin + 1;
}

void CNFCircuit::and_gate(NewVar output, vector<NewLit>::const_reverse_iterator begin,
										 vector<NewLit>::const_reverse_iterator end) {
    for (std::vector<NewLit>::const_reverse_iterator it = begin; it != end; it++) {
        ofs << *it << " " << -output << " 0\n";
    }
    for (typename std::vector<NewLit>::const_reverse_iterator it = begin; it != end; it++) {
        ofs << -*it << " ";
    }
    ofs << output << " 0\n";

    num_clauses += end - begin + 1;
}

void CNFCircuit::or_gate(NewVar output, const vector<NewLit>& inputs) {
	or_gate(output, inputs.begin(), inputs.end());
}

void CNFCircuit::and_gate(NewVar output, const vector<NewLit>& inputs) {
	and_gate(output, inputs.begin(), inputs.end());
}

// output = (input1 == input2)
void CNFCircuit::equiv_gate(NewVar output, OldVar input1, NewVar input2) {
	ofs << -output << " " << -input1 << " " <<   input2 << " 0\n";
	ofs << -output << " " <<  input1 << " " <<  -input2 << " 0\n";
	ofs <<  output << " " <<  input1 << " " <<   input2 << " 0\n";
	ofs <<  output << " " << -input1 << " " <<  -input2 << " 0\n";
	num_clauses += 4;
}

// if (query) {output = val_true} else {output = val_false}
void CNFCircuit::ite_gate(NewVar output, OldLit query, NewVar val_false, NewVar val_true) {
	ofs <<  query << " " << -val_false << " " <<   output << " 0\n";
	ofs <<  query << " " <<  val_false << " " <<  -output << " 0\n";
	ofs << -query << " " << -val_true  << " " <<   output << " 0\n";
	ofs << -query << " " <<  val_true  << " " <<  -output << " 0\n";
	num_clauses += 4;
}

void CNFCircuit::bincls(NewLit a, NewLit b) {
	ofs << a << " " << b << " 0" << std::endl;
}

void CNFCircuit::tercls(NewLit a, NewLit b, NewLit c) {
	ofs << a << " " << b << " " << c << " 0" << std::endl;
}

void CNFCircuit::close_circuit() {
	// to be called when something went wrong
	ofs.close();
}

void CNFCircuit::close_circuit(NewVar max_var) {
	// seek to the beginning of cnf and update the problem line
	ofs.seekp(6);
	ofs << std::setw(41) << std::left <<
		std::to_string(max_var) + " " + std::to_string(num_clauses) << "\n";

	ofs.close();
}
