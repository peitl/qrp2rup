#ifndef _PROOF_TRANSLATOR_H_
#define _PROOF_TRANSLATOR_H_

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
using std::unordered_set;
using std::unordered_map;

class ProofTranslator {
public:
	ClauseWriter cert;
	ClauseWriter rup;

	string gratfile;
	string qrpfile;
	string qdimacs;
	
	unordered_map<OldVar, qdata> var_data;
	unordered_map<QRP_ClauseID, vector<OldVar>> clause_database;

	unordered_map<OldVar, vector<RFAO_node>> countermodel;

	unordered_map<ClauseVarPair, NewVar> phase;
	unordered_map<VarPhasePair, NewVar> eflit;
	unordered_map<PivotPhasesTuple, NewVar> phase_cache;

	unordered_map<PivotPhasePair, GRAT_ClauseID> phase_def; // points to the first of the pair of defining clauses for phase in case pivot is false
	unordered_map<NewVar, GRAT_ClauseID> eflit_def; // points to the first of the four defining clauses
	unordered_map<PivotEflitPair, GRAT_ClauseID> eflit_shortcut; // points to the E-clause that connects eflit to its eflit_left predecessor, the other E-clause has ID + 2

	// TODO: add something to remember the clauses that propagate phase and eflit definitions

	// assuming existential primary type by default, i.e. a false formula
	uint8_t primary_type = 1;
	bool delinfo;
	bool verbose_output;
	NewVar CONST_TRUE = 0, CONST_FALSE = 0;
	ClauseCNT num_cnf_clauses = 0;

	NewVar max_var;
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

	// reads the literals of a new proof line and the IDs of parent proof lines; returns a reference to the read clause
	vector<vector<OldLit>> read_qdimacs();
	vector<OldLit>& read_proof_line(const char * line, QRP_ClauseID& id, QRP_ClauseID& p1, QRP_ClauseID& p2); 
	void combine(string qdimacs, string certificate, string combined);

	// proof checking
	size_t split_by_depth(vector<OldVar>& clause, uint32_t depth);
	int32_t check_resolution(vector<OldLit>& c1, vector<OldLit>& c2, vector<OldLit>& resolvent, vector<OldLit>& merged_lits, vector<OldLit>& reduced_lits);
	int32_t check_reduction(vector<OldLit>& premise, vector<OldLit>& conclusion, vector<OldLit>& reduced_lits);
	void split_reduction_step(QRP_ClauseID id, vector<OldLit>& reduced_lits, vector<OldLit>& reduced_simple, vector<OldLit>& reduced_merged);
	vector<NewVar> shadow(QRP_ClauseID id);

	// phase functions and co.
	NewVar get_phase(QRP_ClauseID id, OldLit lit);
	void copy_phases(QRP_ClauseID src, QRP_ClauseID dest);
	NewVar make_eflit(OldVar var, NewVar phase_var);
	NewVar get_eflit(OldLit lit, NewVar phi);
	NewVar update_phase(OldLit pivot, NewVar phase_left, NewVar phase_right);

	void push_to_array(OldVar var, NewVar entry, bool term);
	void push_to_array(OldVar var, NewLit entry); // shortcut for above, where "bool term" is hidden in the sign of entry

	// verify the QRP proof, extract the countermodel, and create the RUP and GRAT proof
	bool translate();

};

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
		}
	}
};

#endif
