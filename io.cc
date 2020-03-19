#include "proof_translator.hh"

using std::ifstream;

// skips all comments, then checks whether the input is a QRP, or a Qute-style proof
bool ProofTranslator::skip_comments(std::ifstream& qrp) {
	string line;
	while (qrp.peek() == 'c') {
		std::getline(qrp, line);
		if (extract_core)
			core_writer << line << std::endl;
	}
	if (qrp.peek() == 'p') {
		std::getline(qrp, line);
		if (extract_core)
			core_writer << line << std::endl;
		// QRP
		return true;
	} else if (qrp.peek() == 'a' || qrp.peek() == 'e') {
		return false;
	} else {
		// TODO: handle syntax error (throw exception?)
		return false;
	}
}

size_t ProofTranslator::parse_num_vars(const string& problem_line) {
	size_t max_var;
	std::istringstream iss(problem_line);
	iss.ignore(6);
	iss >> max_var;
	return max_var;
}

std::streampos ProofTranslator::read_prefix(std::ifstream& qrp) {
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
		if (extract_core)
			core_writer << line << std::endl;
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

QRP_ClauseID ProofTranslator::parse_DAG_structure_Qute(std::ifstream& qrp,
		unordered_map<QRP_ClauseID, vector<QRP_ClauseID>>& parents_of) {

	string line;
	QRP_ClauseID empty_constraint_id = 0;
	int empty_constraint_type = 0;
	while (empty_constraint_id == 0 && std::getline(qrp, line)) {

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

QRP_ClauseID ProofTranslator::parse_DAG_structure_QRP(std::ifstream& qrp,
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

bool ProofTranslator::is_SAT_proof(string& result_line) {
	std::transform(result_line.begin(), result_line.end(), result_line.begin(), tolower);
	if (result_line == "r sat") {
		return true;
	}
	// TODO: check whether result_line == "r unsat" ?
	return false;
}

unordered_map<QRP_ClauseID, QRP_ClauseID> ProofTranslator::find_core(
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

vector<vector<OldLit>> ProofTranslator::read_qdimacs() {
	vector<vector<OldLit>> matrix;
	string line;
	ifstream qbf(qdimacs);

	// discard everything that is not clauses
	while (std::getline(qbf, line) && (line[0] == 'c' || line[0] == 'p' || line[0] == 'a' || line[0] == 'e')) {}
	do {
		if (!std::all_of(line.begin(), line.end(), isspace)) {
			matrix.push_back({});
			int32_t lit;
			std::istringstream iss(line);
			while(iss >> lit) {
				if (lit != 0) {
					matrix.back().push_back(lit);
				}
				else {
					break;
				}
			}
		}
	} while (std::getline(qbf, line));		 
	return matrix;
}

QRP_ClauseID ProofTranslator::read_proof_line(const char * line,
		QRP_ClauseID& parent_left,
		vector<QRP_ClauseID>& parents_right) {

	char * tmp;
	QRP_ClauseID id = strtoul(line, &tmp, 10);
	clause_database[id] = {};

	if (!proof_is_qrp) {
		// skip Qute clause/term flag
		strtoul(tmp, &tmp, 10);
	}

	OldLit lit;
	while ((lit = strtol(tmp, &tmp, 10)) != 0) {
		clause_database[id].push_back(lit);
	}

	parent_left = strtoul(tmp, &tmp, 10);

	QRP_ClauseID parent_right;
	if (parent_left) {
		while ((parent_right = strtoul(tmp, &tmp, 10)) != 0) {
			parents_right.push_back(parent_right);
		}
	}
	return id;
}

void ProofTranslator::combine(string qdimacs, string certificate, string combined) {
	ifstream qbf(qdimacs);
	ifstream cert(certificate);
	//ClauseWriter comb(combined);
	CNFCircuit comb(combined);

	string line;
	ClauseCNT num_clauses = 0;

	do {
		std::getline(qbf, line);
	} while (line[0] == 'c');

	do {
		std::getline(cert, line);
	} while (line[0] == 'c');

	{
		std::istringstream iss(line);
		iss.ignore(6);
		iss >> num_clauses;
		iss >> num_clauses;
	}
	
	//comb << "p cnf " << max_var << " " << num_clauses << "\n";
	comb.ofs << "p cnf ____________________ ____________________\n";

	do {
		std::getline(qbf, line);
	} while (line[0] == 'a' || line[0] == 'e');

	vector<int32_t> clause;
	vector<int32_t> top_level_clause;

	size_t tseitin_idx = 0;
	do {
		if (!std::all_of(line.begin(), line.end(), isspace)) {
			if (primary_type == 0) {
				std::istringstream iss(line);
				int32_t lit;
				while (iss >> lit) {
					if (lit != 0)
						clause.push_back(lit);
					else
						break;
				}
				int32_t c = clause_tseitin_variables[tseitin_idx++];
				comb.or_gate(c, clause);
				top_level_clause.push_back(-c);
				clause.clear();
			} else {
				comb.ofs << line << "\n";
				num_clauses++;
			}
		}
	} while (std::getline(qbf, line));

	if (primary_type == 0) {
		// TODO: make this more elegant
		//comb.write_clause(top_level_clause);
		for (OldLit lit : top_level_clause) {
			comb.ofs << lit << " ";
		}
		comb.ofs << " 0\n";
	}

	while (std::getline(cert, line)) {
		comb.ofs << line << "\n";
	}

	comb.ofs.seekp(6);
	comb.ofs << std::setw(41) << std::left << std::to_string(max_var) + " " + std::to_string(num_clauses + comb.num_clauses) << "\n";

}
