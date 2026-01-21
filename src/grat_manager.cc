#include "grat_manager.hh"
#include <iostream>
#include <fstream>
#include <string>

void GRATManager::open_proof() {
	grat_proof.push_back(6);
	grat_proof.push_back(0);
}

void GRATManager::unit_clause(GRAT_ClauseID clause) {
	grat_proof.push_back(1);
	grat_proof.push_back(clause);
	grat_proof.push_back(0);
}

void GRATManager::unit_clauses(const vector<GRAT_ClauseID>& clauses) {
	grat_proof.push_back(1);
	grat_proof.insert(grat_proof.end(), clauses.begin(), clauses.end());
	grat_proof.push_back(0);
}

void GRATManager::delete_clauses(const vector<GRAT_ClauseID>& clauses) {
	grat_proof.push_back(2);
	grat_proof.insert(grat_proof.end(), clauses.begin(), clauses.end());
	grat_proof.push_back(0);
}

void GRATManager::open_rup_lemma(GRAT_ClauseID lemma) {
	grat_proof.push_back(3);
	grat_proof.push_back(lemma);
}

void GRATManager::unit(GRAT_ClauseID lemma) {
	grat_proof.push_back(lemma);
}

void GRATManager::unit_sequence(const vector<GRAT_ClauseID>& clauses) {
	grat_proof.insert(grat_proof.end(), clauses.begin(), clauses.end());
}

void GRATManager::rev_unit_sequence(const vector<GRAT_ClauseID>& clauses) {
	grat_proof.insert(grat_proof.end(), clauses.rbegin(), clauses.rend());
}

void GRATManager::close_rup_lemma(GRAT_ClauseID conflict) {
	grat_proof.push_back(0);
	grat_proof.push_back(conflict);
}

void GRATManager::conflict_clause(GRAT_ClauseID clause) {
	grat_proof.push_back(5);
	grat_proof.push_back(clause);
}

void GRATManager::dump_buffer() {
	std::ofstream aux_grat(gratfile + std::to_string(auxiliary_files), std::ios::binary);
	aux_grat.write((char*)&(*grat_proof.begin()), sizeof(GRAT_ClauseID) * grat_proof.size());
	aux_grat.close();
	++auxiliary_files;
	grat_proof.clear();
}

void GRATManager::read_buffer() {
	--auxiliary_files;
	std::ifstream aux_grat(gratfile + std::to_string(auxiliary_files), std::ios::binary);
	aux_grat.seekg(0, std::ios::end);
    size_t size = aux_grat.tellg();
    aux_grat.seekg(0, std::ios::beg);
	grat_proof.resize(size / sizeof(GRAT_ClauseID));
	aux_grat.read((char*)&(*grat_proof.begin()), size);
	aux_grat.close();
}

void GRATManager::write_buffer_backwards(std::ofstream& grat, ClauseCNT total_cnf_clauses) {
	for (auto rit = grat_proof.rbegin(); rit != grat_proof.rend(); ++rit) {
		if (*rit < 0)
			*rit = total_cnf_clauses - *rit;
		grat.write((char*)&(*rit), sizeof(GRAT_ClauseID));
	}
}

void GRATManager::write_grat_proof(ClauseCNT total_cnf_clauses) {
	std::ofstream grat(gratfile, std::ios::binary);
	write_buffer_backwards(grat, total_cnf_clauses);
	while (auxiliary_files > 0) {
		read_buffer();	
		remove((gratfile + std::to_string(auxiliary_files)).c_str());
		write_buffer_backwards(grat, total_cnf_clauses);
	}
	grat.close();
}

// WARNING: this will display only the part of the proof currently in the buffer
// the intended use is for debugging, so for small proofs only, anyway
void GRATManager::display_grat_proof_human_readable() {
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
