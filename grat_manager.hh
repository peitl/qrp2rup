#ifndef _GRAT_MANAGER_H_
#define _GRAT_MANAGER_H_

#include "types.hh"
#include <vector>

using std::vector;
using std::string;

class GRATManager {
	public:
	vector<GRAT_ClauseID> grat_proof;
	size_t max_capacity;
	uint32_t auxiliary_files = 0;
	const string gratfile;

	GRATManager(string gratfile, size_t max_capacity) : max_capacity(max_capacity), gratfile(gratfile) {};

	void open_proof();

	void unit_clause(GRAT_ClauseID clause);
	void unit_clauses(const vector<GRAT_ClauseID>& clauses);

	void delete_clauses(const vector<GRAT_ClauseID>& clauses);

	void open_rup_lemma(GRAT_ClauseID lemma);
	// specifies a clause that becomes unit during checking
	void unit(GRAT_ClauseID clause);
	// specifies a sequence of clauses that become unit during checking
	void unit_sequence(const vector<GRAT_ClauseID>& clauses);
	// specifies a sequence of clauses that become unit in reverse order during checking
	void rev_unit_sequence(const vector<GRAT_ClauseID>& clauses);
	void close_rup_lemma(GRAT_ClauseID conflict);

	void conflict_clause(GRAT_ClauseID clause);

	void ensure_space_for(size_t new_items);
	void read_buffer();
	void dump_buffer();
	void write_buffer_backwards(std::ofstream& grat, ClauseCNT total_cnf_clauses);
	void write_grat_proof(ClauseCNT total_cnf_clauses);
	void display_grat_proof_human_readable();
};

#endif
