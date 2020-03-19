#include "grat_manager.hh"
#include <iostream>
#include <fstream>
#include <string>

void GRATManager::open_proof() {
	grat_proof.push_back(6);
	grat_proof.push_back(0);
}

void GRATManager::unit_clause(GRAT_ClauseID clause) {
	ensure_space_for(3);
	grat_proof.push_back(1);
	grat_proof.push_back(clause);
	grat_proof.push_back(0);
}

void GRATManager::unit_clauses(const vector<GRAT_ClauseID>& clauses) {
	ensure_space_for(2 + clauses.size());
	grat_proof.push_back(1);
	grat_proof.insert(grat_proof.end(), clauses.begin(), clauses.end());
	grat_proof.push_back(0);
}

void GRATManager::delete_clauses(const vector<GRAT_ClauseID>& clauses) {
	ensure_space_for(2 + clauses.size());
	grat_proof.push_back(2);
	grat_proof.insert(grat_proof.end(), clauses.begin(), clauses.end());
	grat_proof.push_back(0);
}

void GRATManager::open_rup_lemma(GRAT_ClauseID lemma) {
	ensure_space_for(2);
	grat_proof.push_back(3);
	grat_proof.push_back(lemma);
}

void GRATManager::unit(GRAT_ClauseID lemma) {
	ensure_space_for(1);
	grat_proof.push_back(lemma);
}

void GRATManager::unit_sequence(const vector<GRAT_ClauseID>& clauses) {
	ensure_space_for(clauses.size());
	grat_proof.insert(grat_proof.end(), clauses.begin(), clauses.end());
}

void GRATManager::rev_unit_sequence(const vector<GRAT_ClauseID>& clauses) {
	ensure_space_for(clauses.size());
	grat_proof.insert(grat_proof.end(), clauses.rbegin(), clauses.rend());
}

void GRATManager::close_rup_lemma(GRAT_ClauseID conflict) {
	ensure_space_for(2);
	grat_proof.push_back(0);
	grat_proof.push_back(conflict);
}

void GRATManager::conflict_clause(GRAT_ClauseID clause) {
	ensure_space_for(2);
	grat_proof.push_back(5);
	grat_proof.push_back(clause);
}

void GRATManager::ensure_space_for(size_t new_items) {
	if (grat_proof.size() + new_items > capacity) {
		if (capacity < max_capacity) {
			capacity *= 10;
			grat_proof.resize(capacity);
		} else {
			dump_buffer();
		}
	}
}

void GRATManager::dump_buffer() {
	std::ofstream aux_grat(gratfile + std::to_string(auxiliary_files), std::ios::binary);
	//std::copy(grat_proof.begin(), grat_proof.end(), std::ostreambuf_iterator<char>(aux_grat));
	aux_grat.write((char*)&(*grat_proof.begin()), 4 * grat_proof.size());
	aux_grat.close();
	++auxiliary_files;
	grat_proof.clear();
}

void GRATManager::read_buffer() {
	--auxiliary_files;
	std::ifstream aux_grat(gratfile + std::to_string(auxiliary_files), std::ios::binary);
	//std::copy(grat_proof.begin(), grat_proof.end(), std::ostreambuf_iterator<char>(aux_grat));
	aux_grat.seekg(0, std::ios::end);
    size_t size = aux_grat.tellg();
    aux_grat.seekg(0, std::ios::beg);
	aux_grat.read((char*)&(*grat_proof.begin()), size);
	aux_grat.close();
	grat_proof.clear();
}

void GRATManager::write_buffer_backwards(std::ofstream& grat, ClauseCNT total_cnf_clauses) {
	for (auto rit = grat_proof.rbegin(); rit != grat_proof.rend(); ++rit) {
		if (*rit < 0)
			*rit = total_cnf_clauses - *rit;
		grat.write((char*)&(*rit), 4);
	}
}

void GRATManager::write_grat_proof(ClauseCNT total_cnf_clauses) {
	std::ofstream grat(gratfile, std::ios::binary);
	write_buffer_backwards(grat, total_cnf_clauses);
	while (auxiliary_files > 0) {
		--auxiliary_files;
		read_buffer();	
		remove((gratfile + std::to_string(auxiliary_files)).c_str());
		write_buffer_backwards(grat, total_cnf_clauses);
	}
	grat.close();
}

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
