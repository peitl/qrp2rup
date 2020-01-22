#ifndef _PROOF_TRANSLATOR_H_
#define _PROOF_TRANSLATOR_H_

#include <cstdlib>
#include <string.h>

#include <string>
#include <fstream>
#include <sstream>
#include <iomanip>
#include <limits>

#include <stack>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <algorithm>
#include <tuple>

// STRUCTS AND CLASSES
// --------------------------------------

#include "types.hh"
#include "rfao_node.hh"
#include "clause_writer.hh"
#include "sorted_query_oracle.hh"

using std::stack;
using std::vector;
using std::array;
using std::unordered_set;
using std::unordered_map;

class ProofTranslator {
public:
	ClauseWriter cert;
	ClauseWriter rup;
	vector<GRAT_ClauseID> grat_proof;

	string gratfile;
	string qrpfile;
	string qdimacs;
	
	unordered_map<OldVar, qdata> var_data;
	unordered_map<QRP_ClauseID, vector<OldVar>> clause_database;

	//unordered_map<OldVar, vector<RFAO_node>> countermodel;
	
	/* this contains the ids of clauses that were replaced by 'g' variables,
	 * and thus it makes no sense to print DRAT deletion information for them. */
	unordered_set<QRP_ClauseID> no_delete;

	unordered_map<ClauseVarPair, NewVar> phase;
	unordered_map<VarPhasePair, NewVar> eflit;
	unordered_map<PivotPhasesTuple, NewVar> phase_cache;
	unordered_map<QRP_ClauseID, vector<OldVar>> merged_vars_in;

	// points to the first of the pair of defining clauses for phase in case pivot is false
	unordered_map<PivotPhasePair, GRAT_ClauseID> phase_def;

	// points to the first of the four defining clauses
	unordered_map<NewVar, GRAT_ClauseID> eflit_def; 

	// points to the E-clause that connects eflit to its eflit_left predecessor,
	// the other E-clause has ID + 2
	unordered_map<PivotEflitPair, GRAT_ClauseID> eflit_shortcut; 

	// assuming existential primary type by default, i.e. a false formula
	uint8_t primary_type = 1;
	bool delinfo;
	bool verbose_output;
	bool proof_is_qrp;
	NewVar CONST_TRUE = 0, CONST_FALSE = 0;
	QRP_ClauseID spare_QRP_IDs[2];
	ClauseCNT num_cnf_clauses = 0;
	uint64_t num_reductions;
	uint64_t num_merges;
	size_t last_orig_clause_seen;
	vector<vector<OldLit>> matrix;
	vector<bool> tautological;
	vector<OldVar> clause_tseitin_variables = {};

	/* *** GRAT stuff ***
	 *
	 * instead of the RFAO arrays, we now only keep track of two clause ids, which
	 * encode the current derived equivalence between a variable and its partial
	 * circuit.
	 *
	 * prop holds these two clauses, and in fact whenever prop has an entry for var,
	 * then the two clauses whose ids it holds are
	 *
	 * (var, -countermodel_out_var[var]) and (-var, countermodel_out_var[var])
	 *
	 * *** */
	unordered_map<OldVar, array<GRAT_ClauseID, 2>> prop;
	unordered_map<QRP_ClauseID, GRAT_ClauseID> get_grat_id;
	unordered_map<OldVar, NewVar> countermodel_out_var;
	GRAT_ClauseID conflict_clause;

	NewVar max_var = 0;
	inline NewVar get_fresh_variable() { return ++max_var; }
	inline void discard_last_variable() { --max_var; }

	ProofTranslator(const string& qrpfile, const string& qdimacs, bool verbose_output = false) :
		cert(ClauseWriter(qrpfile + ".cert")),
		rup(ClauseWriter(qrpfile + ".rup")),
		gratfile(qrpfile + ".grat"),
		qrpfile(qrpfile),
		qdimacs(qdimacs),
		delinfo(false),
		verbose_output(verbose_output) {}

	vector<vector<OldLit>> read_qdimacs();

	inline void write_grat_proof();
	inline void display_grat_proof_human_readable();

	/* Warning: the following functions all assume that the underlying qrp ifstream is in a valid
	 * state at the right position in order to extract the right information */

	// skips all comment lines, returns the problem line (p qrp ...)
	inline bool skip_comments(std::ifstream& qrp);

	inline size_t parse_num_vars(const string& problem_line);

	// returns a stream position at the and of the prefix (= beginning of the matrix)
	inline std::streampos read_prefix(std::ifstream& qrp);

	// parses the DAG structure of the proof into parents_of, returns the id of the empty clause
	inline QRP_ClauseID parse_DAG_structure_QRP(std::ifstream& qrp,
			unordered_map<QRP_ClauseID, vector<QRP_ClauseID>>& parents_of);

	inline QRP_ClauseID parse_DAG_structure_Qute(std::ifstream& qrp,
			unordered_map<QRP_ClauseID, vector<QRP_ClauseID>>& parents_of);

	inline bool is_SAT_proof(string& result_line);

	inline unordered_map<QRP_ClauseID, QRP_ClauseID> find_core(
			QRP_ClauseID empty_constraint,
			unordered_map<QRP_ClauseID, vector<QRP_ClauseID>>& parents_of);

	// reads the literals of a new proof line and the IDs of parent proof lines;
	// returns a reference to the read clause
	QRP_ClauseID read_proof_line(const char * line,
			QRP_ClauseID& parent_left,
			vector<QRP_ClauseID>& parents_right); 

	// combines the matrix of qdiamcs with certificate into combined
	void combine(string qdimacs, string certificate, string combined);

	// proof checking
	
	inline void sort_and_remove_duplicate_literals(vector<OldLit>& clause);
	
	bool record_axiom(QRP_ClauseID current_id);

	int translate_resolution_step(QRP_ClauseID parent_left,
			QRP_ClauseID parent_right,
			QRP_ClauseID resolvent);

	size_t split_by_depth(vector<OldVar>& clause, uint32_t depth);

	vector<OldLit> resolve(const vector<OldLit>& c1, const vector<OldLit>& c2);

	int32_t check_resolution(vector<OldLit>& c1, vector<OldLit>& c2, vector<OldLit>& resolvent,
			vector<OldLit>& merged_lits,
			vector<OldLit>& reduced_lits);

	int32_t check_reduction(vector<OldLit>& premise, vector<OldLit>& conclusion,
			vector<OldLit>& reduced_lits);

	void split_reduction_step(QRP_ClauseID id, vector<OldLit>& reduced_lits,
			vector<OldLit>& reduced_simple,
			vector<OldLit>& reduced_merged);

	vector<NewVar> shadow(QRP_ClauseID id);

	inline void forget(QRP_ClauseID clause_id);

	// phase functions and co.
	NewVar get_phase(QRP_ClauseID id, OldLit lit);
	void copy_phases(QRP_ClauseID src, QRP_ClauseID dest);
	NewVar make_eflit(OldVar var, NewVar phase_var);
	NewVar get_eflit(OldLit lit, NewVar phi);
	NewVar update_phase(OldLit pivot, NewVar phase_left, NewVar phase_right);

	void push_to_array(OldVar var, NewVar entry, bool term);
	// shortcut for above, where "bool term" is hidden in the sign of entry
	void push_to_array(OldVar var, NewLit entry);

	// verify the QRP proof, extract the countermodel, and create the RUP and GRAT proof
	bool translate();

};






inline void ProofTranslator::write_grat_proof() {
	std::ofstream grat(gratfile, std::ios::binary);
	for (auto rit = grat_proof.rbegin(); rit != grat_proof.rend(); ++rit) {
		if (*rit < 0)
			*rit = num_cnf_clauses + cert.num_clauses - *rit;
		grat.write((char*)&(*rit), 4);
	}
	grat.close();
}

inline void ProofTranslator::display_grat_proof_human_readable() {
	size_t i = 0;
	while (i < grat_proof.size()) {
		if (grat_proof[i] == 3) {
			std::cout << "RUP " << grat_proof[++i] << ":";
			while (grat_proof[++i] != 0) {
				std::cout << " " << grat_proof[i];
			}
			std::cout << " CFLT: " << grat_proof[++i] << std::endl;
			++i;
		} else if (grat_proof[i] == 1) {
			std::cout << "UNIT:";
			while (grat_proof[++i] != 0) {
				std::cout << " " << grat_proof[i];
			}
			std::cout << std::endl;
			++i;
		} else if (grat_proof[i] == 2) {
			std::cout << "DEL:";
			while (grat_proof[++i] != 0) {
				std::cout << " " << grat_proof[i];
			}
			std::cout << std::endl;
			++i;
		} else if (grat_proof[i] == 5) {
			std::cout << "CONFLICT: " << grat_proof[++i] << std::endl;
			++i;
		} else {
			while (grat_proof[i++] != 0) {}
		}
	}
}

// skips all comments, then checks whether the input is a QRP, or a Qute-style proof
inline bool ProofTranslator::skip_comments(std::ifstream& qrp) {
	string line;
	while (qrp.peek() == 'c') {
		std::getline(qrp, line);
	}
	if (qrp.peek() == 'p') {
		std::getline(qrp, line);
		// QRP
		return true;
	} else if (qrp.peek() == 'a' || qrp.peek() == 'e') {
		return false;
	} else {
		// handle syntax error (throw exception?)
		return false;
	}
}

inline size_t ProofTranslator::parse_num_vars(const string& problem_line) {
	size_t max_var;
	std::istringstream iss(problem_line);
	iss.ignore(6);
	iss >> max_var;
	return max_var;
}

inline std::streampos ProofTranslator::read_prefix(std::ifstream& qrp) {
	std::streampos matrix_begin = qrp.tellg();
	string line;
	char last_qtype = 'x';
	char qtype = 'y';
	uint32_t last_qdepth = 0;
	
	while (true) {

		matrix_begin = qrp.tellg();
		qtype = qrp.peek();
		if (qtype != 'a' && qtype != 'e')
			break;

		if (qtype != last_qtype) {
			last_qtype = qtype;
			++last_qdepth;
		}

		OldVar var;
		std::getline(qrp, line);
		std::istringstream iss(line);
		iss.ignore(2);

		while (iss >> var) {
			if (var == 0)
				break;
			if (var > max_var)
				max_var = var;
			var_data[var] = {last_qdepth, qtype == 'e'};
		}
	}
	return matrix_begin;
}

inline QRP_ClauseID ProofTranslator::parse_DAG_structure_Qute(std::ifstream& qrp,
		unordered_map<QRP_ClauseID, vector<QRP_ClauseID>>& parents_of) {

	string line;
	QRP_ClauseID empty_constraint_id = 0;
	int empty_constraint_type;
	while (std::getline(qrp, line)) {

		char * tmp_line;

		QRP_ClauseID id = strtoul(line.c_str(), &tmp_line, 10);
		parents_of[id] = {};

		// skip Qute clause/term flag
		int constraint_type = strtol(tmp_line, &tmp_line, 10);

		long int first_literal_in_constraint = strtol(tmp_line, &tmp_line, 10);
		if (first_literal_in_constraint == 0) {
			// empty clause
			empty_constraint_id = id;
			empty_constraint_type = constraint_type;
			break;
		} else {
			tmp_line = strstr(tmp_line, " 0 ");
			if (tmp_line == NULL) {
				std::cerr << "Syntax error in step with the id " << id << std::endl;
				return 0;
			}
			tmp_line += 3;
		}

		QRP_ClauseID parent = 0;
		while ((parent = strtoul(tmp_line, &tmp_line, 10)) != 0) {
			parents_of[id].push_back(parent);
		}
	}

	primary_type = (empty_constraint_type == 0);

	return empty_constraint_id;
}

inline QRP_ClauseID ProofTranslator::parse_DAG_structure_QRP(std::ifstream& qrp,
		unordered_map<QRP_ClauseID, vector<QRP_ClauseID>>& parents_of) {

	string line;
	QRP_ClauseID empty_constraint_id = 0;
	while (std::tolower(qrp.peek()) != 'r') {
		std::getline(qrp, line);
		char * tmp_line;

		QRP_ClauseID id = strtoul(line.c_str(), &tmp_line, 10);
		parents_of[id] = {};

		long int first_literal_in_constraint = strtol(tmp_line, &tmp_line, 10);
		if (first_literal_in_constraint == 0) {
			// empty clause
			empty_constraint_id = id;
		} else {
			tmp_line = strstr(tmp_line, " 0 ");
			if (tmp_line == NULL) {
				std::cerr << "Syntax error in step with the id " << id << std::endl;
				return 0;
			}
			tmp_line += 3;
		}

		QRP_ClauseID parent = 0;
		while ((parent = strtoul(tmp_line, &tmp_line, 10)) != 0) {
			parents_of[id].push_back(parent);
		}
	}

	return empty_constraint_id;
}

inline bool ProofTranslator::is_SAT_proof(string& result_line) {
	std::transform(result_line.begin(), result_line.end(), result_line.begin(), tolower);
	if (result_line == "r sat") {
		return true;
	}
	// TODO: check whether result_line == "r unsat" ?
	return false;
}

inline unordered_map<QRP_ClauseID, QRP_ClauseID> ProofTranslator::find_core(
		QRP_ClauseID empty_constraint_id,
		unordered_map<QRP_ClauseID, vector<QRP_ClauseID>>& parents_of) {

	unordered_map<QRP_ClauseID, QRP_ClauseID> last_use_of;

	stack<QRP_ClauseID, vector<QRP_ClauseID>> core_clauses;
	core_clauses.push(empty_constraint_id);
	last_use_of[empty_constraint_id] = 0;
	while (!core_clauses.empty()) {
		QRP_ClauseID current_id = core_clauses.top();
		core_clauses.pop();
		auto pit = parents_of.find(current_id);
		if (pit != parents_of.end()) {
			for (auto parent: pit->second) {
				if (parent) {
					auto it = last_use_of.find(parent);
					if (it != last_use_of.end()) {
						if (current_id > it->second) {
							it->second = current_id;
						}
					} else {
						last_use_of.insert({parent, current_id});
						core_clauses.push(parent);
					}
				}
			}
		}
	}

	parents_of.clear();

	return last_use_of;
}

void ProofTranslator::sort_and_remove_duplicate_literals(vector<OldLit>& clause) {
	// sort and remove duplicate literals
	sort(clause.begin(), clause.end(), compare_lits);
	clause.resize(
			std::distance(
				clause.begin(),
				std::unique(
					clause.begin(),
					clause.end())
				)
			);
}

template<typename T>
inline
void negate(std::vector<T>& clause) {
	for (size_t i = 0; i < clause.size(); i++)
		clause[i] = -clause[i];
}

inline void ProofTranslator::copy_phases(QRP_ClauseID src, QRP_ClauseID dest) {
	vector<OldLit>& src_clause = clause_database[src];
	for (OldLit lit : src_clause) {
		OldVar var = abs(lit);
		ClauseVarPair dest_key = {dest, var};
		unordered_map<ClauseVarPair, NewVar>::iterator it = phase.find({src, var});
		if (it != phase.end() && phase.find(dest_key) == phase.end()) {
			phase.insert({dest_key, it->second});
			merged_vars_in[dest].push_back(var);
		}
	}
};

inline void ProofTranslator::forget(QRP_ClauseID clause_id) {
	for (OldVar var : merged_vars_in[clause_id]) {
		phase.erase({clause_id, var});
	}
	merged_vars_in.erase(clause_id);
	clause_database.erase(clause_id);
	get_grat_id.erase(clause_id);
}

#endif
