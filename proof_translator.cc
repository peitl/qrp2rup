#include "proof_translator.hh"
#include "sorted_query_oracle.hh"
#include "defaults.hh"
#include <climits>
#include <iomanip>
#include <limits>

using std::ifstream;

bool ProofTranslator::translate() {

	clock_t start = clock();

	ifstream qrp(qrpfile);

	/*if (extract_core)
		core_writer.open(qrpfile + ".core");*/

	/* TODO: Implement various modes; the advantage is that with some assumptions
	 * on the proof structure, we can avoid memory overhead and even produce slightly
	 * smaller RUP proofs in some cases. */
	// bool implicit_immediate_reductions = false;
	// bool implicit_resolution_reductions = false;

	// read up to the preamble line, discard any comments and determine proof format
	proof_is_qrp = skip_comments(qrp);

	if (verbosity >= 1) {
		std::cout << "--- qrp2rup     ------------------" << std::endl;
		std::cout << std::endl;
		if (proof_is_qrp)
			std::cout << "QRP format detected." << std::endl;
		else
			std::cout << "Qute format detected." << std::endl;
	}

	// parse the preamble line, extract number of variables
	// seems to be unnecessary
	// size_t qbf_num_vars = parse_num_vars(problem_line);

	// read the prefix and store quantifier types and depths of variables into var_data
	std::streampos matrix_begin = read_prefix(qrp);

	// BEGIN FIRST PASS ---------------------------------
	
	unordered_map<QRP_ClauseID, vector<QRP_ClauseID>> parents_of;

	if (verbosity >= 1)
		std::cout << "Parsing the DAG structure of the proof..." << std::flush;

	clock_t begin = clock();

	QRP_ClauseID empty_constraint_id = 0;
	vector<QRP_ClauseID> empty_constraint_ids;
	if (proof_is_qrp) {
		empty_constraint_id = parse_DAG_structure_QRP(qrp, parents_of);
		string result_line;
		std::getline(qrp, result_line);
		if (is_SAT_proof(result_line))
			primary_type = 1; // universal is primary
		empty_constraint_ids.push_back(empty_constraint_id);
	} else {
		// this version also sets primary_type
		empty_constraint_ids = parse_DAG_structure_Qute(qrp, parents_of);
	}

	if (empty_constraint_ids.empty()) {
		std::cerr << "FAIL" << std::endl;
		cert->close_circuit();
		rup.ofs.close();
		/*if (extract_core)
			core_writer.close();*/
		return false;
	}

	statistics.num_empty_constraints = empty_constraint_ids.size();
	if (extract_core) {
		for (QRP_ClauseID eid : empty_constraint_ids) {
			core_writers.push_back({});
			core_writers.back().open(qrpfile + ".core." + std::to_string(eid));
			for (const string& pline : prefix_lines) {
				core_writers.back() << pline << std::endl;
			}
		}
	}

	// the last empty constraint, but possibly not the only one (for enumeration proofs)
	empty_constraint_id = empty_constraint_ids.back();
	constraint_type.resize(empty_constraint_id+1, 0);

	clock_t end = clock();

	if (verbosity >= 1) {
		std::cout << " done (" << std::fixed << std::showpoint << std::setprecision(2) <<double(end-begin) / CLOCKS_PER_SEC << "s)" << std::endl;
		std::cout << std::endl;
	}

	// used for intermediate learned constraints, every constraint must formally have an id
	spare_QRP_IDs[0] = empty_constraint_id + 1;
	spare_QRP_IDs[1] = empty_constraint_id + 2;

	// load the formula from the QDIMACS file, it's necessary in every case
	matrix = read_qdimacs(); // sets have_formula accordingly
	if (have_formula) {
		num_cnf_clauses = matrix.size();

		if (primary_type == 1) {
			// recalculate num_cnf_clauses
			for (auto& c : matrix) {
				num_cnf_clauses += c.size();
				clause_tseitin_variables.push_back(get_fresh_variable());
			}
			// top level clause
			++num_cnf_clauses;
		} else {
			// in the unsat case, we need to sort the clauses of the matrix and remove duplicates
			// for efficient comparisons 
			// however, careful, because in the sat case, they must not be sorted!
			for (auto& c : matrix) {
				sort(c.begin(), c.end(), compare_lits);
				c.resize(std::distance(c.begin(), std::unique(c.begin(), c.end())));
			}
		}
	}

	last_use_of = find_core(empty_constraint_ids, parents_of);
	
	// END FIRST PASS	---------------------------------
	qrp.clear();
	qrp.seekg(matrix_begin);

	// read and translate the actual proof
	begin = clock();

	// define an auxiliary variable that holds the value 1
	//CONST_TRUE = get_fresh_variable();
	CONST_TRUE = INT_MAX;
	CONST_FALSE = -CONST_TRUE;
	cert->CONST_TRUE = CONST_TRUE;
	cert->CONST_FALSE = CONST_FALSE;
	//cert.and_gate(CONST_TRUE, {});
	//std::cout << "CONST_TRUE = " << CONST_TRUE << std::endl;

	//grat_proof = {6, 0};
	gman.open_proof();
	conflict_clause = 0;
	//gman.unit_clause(num_cnf_clauses + cert.num_clauses); // declare CONST_TRUE unit

	if (have_formula && primary_type == 1) {
		// the following can happen:
		// Suppose the true QBF F has a tautological clause C that is discarded in
		// preprocessing by the QBF solver. Later, the solver comes up with an initial term T that
		// doesn't hit C, which is OK, because C is no longer in the matrix, but T will not be
		// verified correctly. Therefore we first derive unit clauses that say that every
		// tautological clause is always satisfied.
		GRAT_ClauseID current_clause = 1;
		tautological.resize(matrix.size(), false);
		for (size_t clause_idx = 0; clause_idx < matrix.size(); ++clause_idx) {
			vector<OldLit>& clause = matrix[clause_idx];
			unordered_set<OldLit> clause_as_set(clause.begin(), clause.end());
			size_t i = 0;
			for (i = 0; i < clause.size(); ++i) {
				if (clause_as_set.count(-clause[i])) {
					tautological[clause_idx] = true;
					break;
				}
			}
		
			if (tautological[clause_idx]) {
				size_t j = i + 1;
				while (clause[j] != -clause[i]) {
					++j;
				}
				rup.write_clause<OldLit>({clause_tseitin_variables[clause_idx]});
				gman.open_rup_lemma(-rup.num_clauses);
				gman.unit(current_clause + i);
				gman.close_rup_lemma(current_clause + j);

				gman.unit_clause(-rup.num_clauses);
			}
			current_clause += clause.size() + 1;
		}
	}

	last_orig_clause_seen = 0;

	string line;
	QRP_ClauseID temporary_parent_left = 0, temporary_resolvent = 0;

	size_t last_threshold = 1;
	size_t threshold = 1;

	while (std::getline(qrp, line)) {
		// not sure what to do about this in the case of multiple cores
		/*if (line[0] == 'r') {
			if (extract_core)
				core_writer << line << std::endl;
			continue;
		}*/

		QRP_ClauseID parent_left;
		vector<QRP_ClauseID> parents_right;
		bool ctype;
		QRP_ClauseID current_id = read_proof_line(line.c_str(), parent_left, parents_right, ctype);
		constraint_type[current_id] = ctype;

		++statistics.num_proof_lines;

		if (last_use_of.find(current_id) == last_use_of.end()) {
			clause_database.erase(current_id);
			continue;
		}

		++statistics.num_core_proof_lines;

		if (extract_core) {
			for (size_t i : sinks_of[current_id]) {
				core_writers[i] << line << std::endl;
			}
		}

		if (ctype == 1) {
			negate(clause_database[current_id]);
		}

		sort_and_remove_duplicate_literals(clause_database[current_id]);

		if (parent_left == 0) {
			// input clause / initial term
			record_axiom(current_id);
			if (!have_formula) {
				/* we don't have a separate formula file (probably because using QCIR)
				 * so we have to log axioms. We do it like this:
				 * 	 set last_use_of to 0, so that the constraint doesn't get deleted
				 * 	 push the id to a list of axioms
				 */
				last_use_of[current_id] = 0;
				axioms.push_back(current_id);
			}

		} else {
			if (parents_right.empty()) {
				// reduction step
				if (translate_resolution_step(parent_left, 0, current_id) != 0) {
					std::cout << "the failed step was a reduction step" << std::endl;
				}
			} else {
				size_t i = 0;
				int spare_QRP_ID_idx = 0;
				temporary_parent_left = parent_left;
				while (i < parents_right.size() - 1) {
					temporary_resolvent = spare_QRP_IDs[spare_QRP_ID_idx];
					spare_QRP_ID_idx = 1 - spare_QRP_ID_idx;
					// compute resolution of temporary_parent_left and parents_right[i]
					// into clause_database[temporary_resolvent]
					
					clause_database[temporary_resolvent] = resolve(
							clause_database[temporary_parent_left],
							clause_database[parents_right[i]],
							constraint_type[parents_right[i]]
							);
					
					int result = translate_resolution_step(temporary_parent_left, parents_right[i], temporary_resolvent);
					if (temporary_parent_left != parent_left) {
						forget(temporary_parent_left);
					}

					// TODO: implement proper exception handling
					if (result != 0) {
						std::cout << "intermediate resolution failed" << std::endl;
						std::cout << "learned clause id: " << current_id << std::endl;
						std::cout << "parent_right: " << parents_right[i] <<
							" (" << (i+2) << ordinal_suffix(i+2) <<
							" in that derivation)" << std::endl;
						return result;
					}

					++i;
					temporary_parent_left = temporary_resolvent;
				}

				int result = translate_resolution_step(temporary_parent_left, parents_right.back(), current_id);
				// TODO: implement proper exception handling
				if (result != 0) {
					std::cout << "intermediate resolution failed" << std::endl;
					std::cout << "learned clause id: " << current_id << std::endl;
					std::cout << "parent_right: " << parents_right[i] <<
						" (" << (i+2) << ordinal_suffix(i+2) <<
						" in that derivation)" << std::endl;
					return result;
				}

				if (temporary_parent_left != parent_left) {
					forget(temporary_parent_left);
				}

				vector<GRAT_ClauseID> to_delete;

				unordered_map<QRP_ClauseID, QRP_ClauseID>::iterator it = last_use_of.find(parent_left);
				if (it->second == current_id) {
					last_use_of.erase(it);
					if (delinfo) {
						if (!no_delete.erase(parent_left)) {
							to_delete.push_back(get_grat_id[parent_left]);
						}
					}
					forget(parent_left);
				}
				for (QRP_ClauseID parent_right : parents_right) {
					it = last_use_of.find(parent_right);
					if (it->second == current_id) {
						last_use_of.erase(it);
						if (delinfo) {
							if (!no_delete.erase(parent_right)) {
								to_delete.push_back(get_grat_id[parent_right]);							
							}
						}
						forget(parent_right);
					}
				}
			}
		}

		if (clause_database[current_id].size() <= delinfo) {
			no_delete.insert(current_id);
		}

		if (gman.grat_proof.size() > gman.max_capacity) {
			gman.dump_buffer();
		}

		if (verbosity >= 2) {
			if (statistics.num_core_proof_lines >= threshold) {
				std::cout << "INFO: " << statistics.num_core_proof_lines << " core proof lines processed.";
				std::cout << " The GRAT proof buffer now has " << gman.grat_proof.size() << " entries." << std::endl;
				size_t new_threshold = threshold + last_threshold;
				last_threshold = threshold;
				threshold = new_threshold;
			}
		}
	}

	gman.conflict_clause(conflict_clause);

	gman.write_grat_proof(num_cnf_clauses + cert->num_clauses);

	if (verbosity >= 2) {
		gman.display_grat_proof_human_readable();
	}

	// now encode the countermodels into CNF
	// TODO: implement different types of encoding (quadratic one-sided, multi-gates)
	// now handled by the circuit class, legacy code is stored in circuit.hh 

	cert->close_circuit(max_var);
	rup.ofs.close();
	for (ofstream& core_writer : core_writers)
		core_writer.close();

	if (have_formula) {
		combine(qdimacs, qrpfile + ".cert", qrpfile + ".cnf");
	} else {
		combine_internal(qrpfile + ".cert", qrpfile + ".cnf");
	}

	if (verbosity >= 1)
		print_statistics();

	end = clock();
	double t = ((double) end - begin) / CLOCKS_PER_SEC;

	if (verbosity >= 1) {
		std::cout << "---  TIME STATS ------------------" << std::endl;
		std::cout << std::endl;
		std::cout << "Proof translated in " << std::fixed << std::showpoint << std::setprecision(2) << t << " seconds" << std::endl;
		std::cout << "Total time: " << std::fixed << std::showpoint << std::setprecision(2) << ((double)clock() - start) / CLOCKS_PER_SEC << " seconds" << std::endl;
		std::cout << std::endl;
	}

	if (verbosity >= 0) {
		std::cout << "OK"  << std::endl;
	}

	return true;
}




int ProofTranslator::translate_resolution_step(QRP_ClauseID parent_left,
											QRP_ClauseID parent_right,
											QRP_ClauseID resolvent) {

	++statistics.num_core_resolutions;

	vector<OldLit> merged_lits;
	vector<OldLit> reduced_lits;
	vector<OldLit> reduced_simple;
	vector<OldVar> reduced_merged;
	vector<NewVar> auxg; // holds intermediate g-variables for merged reduction steps
	merged_vars_in[resolvent] = {};

	OldLit pivot = 0;
	if (parent_right != 0) {
		// resolvent
		pivot = check_resolution(clause_database[parent_left],
								 clause_database[parent_right],
								 clause_database[resolvent], merged_lits, reduced_lits,
								 constraint_type[parent_right]);
		if (pivot == 0) {
			std::cout << "Failed resolution step with id " << resolvent << std::endl;
			return -1;
		}

		// first update phases, then handle reductions
		// merged_lits contains a single literal for every merged variables,
		// namely one that appears in parent_left
		for (size_t i = 0; i < merged_lits.size(); ++i) {
			OldLit lit = merged_lits[i];
			OldVar var = abs(lit);
			merged_vars_in[resolvent].push_back(var);

			NewVar phase_left = get_phase(parent_left, lit);
			NewVar phase_right = get_phase(parent_right, -lit);

			PivotPhasesTuple cache_key = {pivot, phase_left, phase_right};

			NewVar var_phase;
			unordered_map<PivotPhasesTuple, NewVar>::iterator ppit = phase_cache.find(cache_key);
			if (phase_left == phase_right) {
				// var is in fact not being merged: remove it from merged_lits
				var_phase = phase_left;						
				merged_lits[i] = merged_lits.back();
				merged_lits.pop_back();
				--i;
			} else if (ppit != phase_cache.end()) {
				var_phase = ppit->second;
			} else {
				var_phase = update_phase(pivot, phase_left, phase_right);
			}
			phase.insert({{resolvent, var}, var_phase});
			if (verbosity >= 3)
				std::cout << "Phase of " << var << " in " << resolvent << " is " << var_phase << std::endl;

			NewVar var_eflit;
			unordered_map<VarPhasePair, NewVar>::iterator vpit = eflit.find({var, var_phase});
			if (vpit != eflit.end()) {
				var_eflit = vpit->second;
			} else {
				var_eflit = make_eflit(var, var_phase);
				eflit.insert({{var, var_phase}, var_eflit});
				// print E-clauses because effective literal was updated
				NewVar eflit_left = get_eflit(lit, phase_left);
				NewVar eflit_right = get_eflit(-lit, phase_right);

				// ##############################################################
				// shortcuts to falsify left parent
				// ##############################################################
				// the sequence of propagations is:
				//	 pivot^0		+  phase_left^f				 =>  var_phase^f  [ phase_def[var_phase]   ]
				//	 eflit_left^1	+  phase_left^f				 =>  var^f		  [ eflit_def[eflit_left]  ] (only if phase_left is non-trivial)
				//	 var_eflit^0	+  var_phase^f	  + var^f	 =>  0			  [ eflit_def[var_eflit]   ]
				//
				//	 pivot^1		+  phase_right^f			 =>  var_phase^f  [ phase_def[var_phase]   ]
				//	 eflit_right^1	+  phase_right^f			 =>  var^f		  [ eflit_def[eflit_right] ] (only if phase_right is non-trivial)
				//	 var_eflit^0	+  var_phase^f	  + var^f	 =>  0			  [ eflit_def[var_eflit]   ]
				// ##############################################################
				
				// TODO: rewrite sequences such as this one into vector.insert(end, initializer_list)
				
				// if phase_left (phase_right) is non-trivial, we need to make a RUP-style case distinction
				if (phase_left != CONST_TRUE) {
					gman.open_rup_lemma(-(rup.num_clauses+1)); // referencing a not yet written lemma
					if (phase_left != CONST_FALSE) {
						rup.write_clause<NewLit>({var_eflit, pivot, -eflit_left, phase_left});
						gman.unit(phase_def[{pivot, var_phase}] + 1);
						gman.unit(eflit_def[eflit_left] + 0);
					} else {
						rup.write_clause<NewLit>({var_eflit, pivot, -eflit_left});
						gman.unit(phase_def[{pivot, var_phase}] + 0);
						// eflit_left has no def, so nothing to prop
					}
					gman.close_rup_lemma(eflit_def[var_eflit] + 2);
				}

				if (phase_left != CONST_FALSE) {
					rup.write_clause<NewLit>({var_eflit, pivot, -eflit_left});
					gman.open_rup_lemma(-rup.num_clauses);
					if (phase_left != CONST_TRUE) {
						gman.unit(-(rup.num_clauses - 1));
						gman.unit(eflit_def[eflit_left] + 1);
					}
					gman.unit(phase_def[{pivot, var_phase}] + 0);
					gman.close_rup_lemma(eflit_def[var_eflit] + 3);
				}					

				eflit_shortcut[{pivot, var_eflit}] = rup.num_clauses;

				// shortcuts to falsify right parent
				if (phase_right != CONST_TRUE) {
					gman.open_rup_lemma(-(rup.num_clauses+1)); // referencing a not yet written lemma
					if (phase_right != CONST_FALSE) {
						rup.write_clause<NewLit>({var_eflit, -pivot, -eflit_right, phase_right});
						gman.unit(phase_def[{-pivot, var_phase}] + 1);
						gman.unit(eflit_def[eflit_right] + 0);
					} else {
						rup.write_clause<NewLit>({var_eflit, -pivot, -eflit_right});
						gman.unit(phase_def[{-pivot, var_phase}] + 0);
						// eflit_right has no def so nothing to prop
					}
					gman.close_rup_lemma(eflit_def[var_eflit] + 2);
				}

				if (phase_right != CONST_FALSE) {
					rup.write_clause<NewLit>({var_eflit, -pivot, -eflit_right});
					gman.open_rup_lemma(-rup.num_clauses);
					if (phase_right != CONST_TRUE) {
						gman.unit(-(rup.num_clauses - 1));
						gman.unit(eflit_def[eflit_right] + 1);
					}
					gman.unit(phase_def[{-pivot, var_phase}] + 0);
					gman.close_rup_lemma(eflit_def[var_eflit] + 3);
				}

				eflit_shortcut[{-pivot, var_eflit}] = rup.num_clauses;
			}
			if (verbosity >= 3)
				std::cout << "Phase of " << var << " in " << resolvent << " is " << var_phase << std::endl;
		}
		// carry over phases of already merged literals that are not being merged now
		copy_phases(parent_left, resolvent);
		copy_phases(parent_right, resolvent);
	} else {
		check_reduction(clause_database[parent_left], clause_database[resolvent], reduced_lits, constraint_type[resolvent]);
		copy_phases(parent_left, resolvent);
	}

	split_reduction_step(resolvent, reduced_lits, reduced_simple, reduced_merged);
	// TODO: avoid the computation of the shadow clause if not necessary
	vector<NewVar> shadcls = shadow(resolvent);

	// compute the propagation sequence for newly merged literals
	// the "left" ("right") sequence is what propagates when the left (right) pivot and the new merged literals are falsified
	vector<GRAT_ClauseID> merge_propagation_sequence_left;
	vector<GRAT_ClauseID> merge_propagation_sequence_right;
	for (NewLit merged_lit : merged_lits) {

		++statistics.num_core_variable_merges;

		NewVar merged_eflit = get_eflit(merged_lit, get_phase(resolvent, merged_lit));
		merge_propagation_sequence_left.push_back(-eflit_shortcut[{pivot, merged_eflit}]);
		merge_propagation_sequence_right.push_back(-eflit_shortcut[{-pivot, merged_eflit}]);
	}

	if (!merged_lits.empty()) {
		++statistics.num_core_merge_steps;
	}

	/* if there are any reduced literals, create the corresponding g_i variables
	 * and update the countermodel circuits, else just print the shadow clause. */
	if (!reduced_lits.empty()) {

		++statistics.num_core_reduction_steps;

		// initialize all g-variables
		NewVar g = get_fresh_variable();
		cert->or_gate(g, shadcls);

		// the current clause is at the end of the certificate at the moment
		GRAT_ClauseID current_grat_id = cert->num_clauses + num_cnf_clauses;
		get_grat_id[resolvent] = current_grat_id;

		if (shadcls.empty()) {
			conflict_clause = current_grat_id;
		}

		// avoid creation of new variable when shadow clause is unit or empty, but that complicates things
		/*if (shadcls.size() > 0) {
			if (shadcls.size() > 1) {
				g = get_fresh_variable();
				num_cert_clauses += define_variable_clause(cnf, g, shadcls);
			} else {
				has_unit_conclusion = true;
				g = shadcls[0];
			}
		} else {
			has_empty_conclusion = true;
		}*/

		auxg.push_back(g);

		// create intermediate g-variables for every reduced merged variable
		// also compute how falsifying later gvars propagates earlier gvars
		vector<GRAT_ClauseID> gvar_downwards_propagation_sequence;
		vector<GRAT_ClauseID> gvar_downwards_shortcut_sequence;
		vector<GRAT_ClauseID> gvar_eflit_falsification_sequence;
		vector<GRAT_ClauseID> gvar_definition_conflict_clause;
		
		for (OldVar var : reduced_merged) {

			NewVar last_aux = auxg.back();
			auxg.push_back(get_fresh_variable());
			// define next_g = last_g | eflit(var, phase(id, var))
			cert->or_gate(auxg.back(), {last_aux, get_eflit(var, get_phase(resolvent, var))});
			gvar_downwards_propagation_sequence.push_back(cert->num_clauses + num_cnf_clauses - 2);
			gvar_eflit_falsification_sequence.push_back(cert->num_clauses + num_cnf_clauses - 1);
			gvar_definition_conflict_clause.push_back(cert->num_clauses + num_cnf_clauses);
			if (gvar_downwards_propagation_sequence.size() > 1) {
				// the downwards shortcut clause from -g_k to -g, k > 1
				rup.write_clause<NewLit>({auxg.back(), -g});

				gman.open_rup_lemma(-rup.num_clauses);
				gman.unit(gvar_downwards_propagation_sequence.back());
				gman.close_rup_lemma(gvar_downwards_shortcut_sequence.back());
				
				gvar_downwards_shortcut_sequence.push_back(-rup.num_clauses);
			} else {
				gvar_downwards_shortcut_sequence.push_back(gvar_downwards_propagation_sequence.back());
			}
		}

		// setting (-g) propagates the negation of the current clause via the 2-clauses
		vector<GRAT_ClauseID> g_def_propagation_sequence;

		for (GRAT_ClauseID g_binclause_id = current_grat_id - shadcls.size(); g_binclause_id < current_grat_id; ++g_binclause_id) {
			g_def_propagation_sequence.push_back(g_binclause_id);
		}

		// handle the simple part of the reduction step
		// compute the countermodel and the propagation sequence
		vector<GRAT_ClauseID> reduction_propagation_sequence;

		for (OldLit lit : reduced_simple) {

			++statistics.num_core_literal_reductions;
			++statistics.num_core_simple_literal_reductions;

			OldVar var = abs(lit);

			if (prop_pos.find(var) == prop_pos.end()) {
				prop_pos[var] = {};
				rfao_array_length[var] = 0;
			}
			if (prop_neg.find(var) == prop_neg.end()) {
				prop_neg[var] = {};
			}

			++rfao_array_length[var];

			/* out_var is the variable representing the yet unknown partial
			 * countermodel circuit for var (by default var)
			 *
			 * since all the previous (g) unit clauses are in the proof,
			 * the value of var is equivalent to out_var via the prop clauses */ 
			NewVar out_var = var;
			auto found = countermodel_out_var.find(var);
			if (found != countermodel_out_var.end()){
				out_var = found->second;
			}

			/* new_out will be the new out_var, representing the smaller
			 * unknown circuit */
			NewVar new_out = get_fresh_variable();

			if (lit < 0) {
				// first pack the pertinent prop sequence if it is too long
				if (prop_pos[var].size() >= PROP_PACKING_THRESHOLD)
					pack_prop_sequence(var, true);

				cert->or_gate(out_var, {-g, new_out});
				reduction_propagation_sequence.push_back(cert->num_clauses + num_cnf_clauses - 2);
				reduction_propagation_sequence.insert(reduction_propagation_sequence.end(),
						prop_pos[var].rbegin(),
						prop_pos[var].rend());

				/*auto prop_clause = prop.find(var);
				if (prop_clause != prop.end()) {
					reduction_propagation_sequence.push_back(prop_clause->second[0]);
				}*/
			} else {
				// first pack the pertinent prop sequence if it is too long
				if (prop_neg[var].size() >= PROP_PACKING_THRESHOLD)
					pack_prop_sequence(var, false);

				cert->and_gate(out_var, {g, new_out});
				reduction_propagation_sequence.push_back(cert->num_clauses + num_cnf_clauses - 2);
				reduction_propagation_sequence.insert(reduction_propagation_sequence.end(),
						prop_neg[var].rbegin(),
						prop_neg[var].rend());
				/*auto prop_clause = prop.find(var);
				if (prop_clause != prop.end()) {
					reduction_propagation_sequence.push_back(prop_clause->second[1]);
				}*/
			}
			countermodel_out_var[var] = new_out;
		} 

		// gvar = resolvent after reducing everything simple
		NewVar gvar = auxg.back();
		auxg.pop_back();
		gvar_downwards_shortcut_sequence.pop_back();

		if (!merged_lits.empty()) {
			// here gvar is guaranteed to be non-zero, because there were merges, but
			// we have not reduced them yet (gvar = clause after reducing simple literals)

			rup.write_clause<NewLit>({pivot, gvar});

			gman.open_rup_lemma(-rup.num_clauses);
			gman.rev_unit_sequence(gvar_downwards_propagation_sequence);
			gman.rev_unit_sequence(gvar_eflit_falsification_sequence);
			gman.unit_sequence(g_def_propagation_sequence);
			gman.unit_sequence(reduction_propagation_sequence);
			gman.unit_sequence(merge_propagation_sequence_left);
			gman.close_rup_lemma(get_grat_id[parent_left]);
			//grat_proof.insert(grat_proof.end(), gvar_downwards_propagation_sequence.rbegin(), gvar_downwards_propagation_sequence.rend());
			//grat_proof.insert(grat_proof.end(), gvar_eflit_falsification_sequence.rbegin(), gvar_eflit_falsification_sequence.rend());
			//grat_proof.insert(grat_proof.end(), g_def_propagation_sequence.begin(), g_def_propagation_sequence.end());
			//grat_proof.insert(grat_proof.end(), reduction_propagation_sequence.begin(), reduction_propagation_sequence.end());
			//grat_proof.insert(grat_proof.end(), merge_propagation_sequence_left.begin(), merge_propagation_sequence_left.end());
			//grat_proof.push_back(0);
			//grat_proof.push_back(get_grat_id[parent_left]);

			rup.write_clause<NewLit>({gvar});

			gman.open_rup_lemma(-rup.num_clauses);
			gman.unit(-(rup.num_clauses - 1));
			gman.rev_unit_sequence(gvar_downwards_propagation_sequence);
			gman.rev_unit_sequence(gvar_eflit_falsification_sequence);
			gman.unit_sequence(g_def_propagation_sequence);
			gman.unit_sequence(reduction_propagation_sequence);
			gman.unit_sequence(merge_propagation_sequence_right);
			gman.close_rup_lemma(get_grat_id[parent_right]);

			gman.unit_clause(-rup.num_clauses);

		} else {
			// no merges in this resolultion step
			rup.write_clause<NewLit>({gvar});

			gman.open_rup_lemma(-rup.num_clauses);
			gman.rev_unit_sequence(gvar_downwards_propagation_sequence);
			gman.rev_unit_sequence(gvar_eflit_falsification_sequence);
			gman.unit_sequence(g_def_propagation_sequence);
			gman.unit_sequence(reduction_propagation_sequence);

			// if this is a resolution step with reduction, additionally one of the parents propagates
			if (parent_right) {
				gman.unit(get_grat_id[parent_right]);
			}

			gman.close_rup_lemma(get_grat_id[parent_left]);

			// mark the newly added clause as unit
			gman.unit_clause(-rup.num_clauses);
		}

		gvar_downwards_propagation_sequence.clear();
		gvar_eflit_falsification_sequence.clear();

		// handle the part with reduced merged literals
		for (vector<OldVar>::reverse_iterator rit = reduced_merged.rbegin(); rit != reduced_merged.rend(); rit++) {

			++statistics.num_core_literal_reductions;
			++statistics.num_core_merged_literal_reductions;

			OldVar var = *rit;

			if (prop_pos.find(var) == prop_pos.end()) {
				prop_pos[var] = {};
				rfao_array_length[var] = 0;
			}
			if (prop_neg.find(var) == prop_neg.end()) {
				prop_neg[var] = {};
			}

			rfao_array_length[var] += 2;

			NewVar var_phase = get_phase(resolvent, var);
			gvar = auxg.back();
			auxg.pop_back();

			NewVar out_var = var;
			auto found = countermodel_out_var.find(var);
			if (found != countermodel_out_var.end()){
				out_var = found->second;
			}
			
			// create the f' variables and push both entries to the countermodel
			NewVar f1 = get_fresh_variable();
			NewVar f2 = get_fresh_variable();
			// TODO: cache the outcome of the following definitions based on the phase variable
			// challenge: we need to know which clauses propagate f1 and f2 for the GRAT proof
			cert->or_gate(f1, {g, -var_phase});
			cert->or_gate(f2, {g, var_phase});

			// new_out := f1 & ( -f2 | ... )
			NewVar new_out1 = get_fresh_variable();
			NewVar new_out2 = get_fresh_variable();
			cert->and_gate(out_var, {f1, new_out1});
			cert->or_gate(new_out1, {-f2, new_out2});

			//auto prop_clause = prop.find(var);
			
			// first pack prop sequences if they are too long
			if (prop_pos[var].size() >= PROP_PACKING_THRESHOLD)
				pack_prop_sequence(var, true);
			if (prop_neg[var].size() >= PROP_PACKING_THRESHOLD)
				pack_prop_sequence(var, false);

			rup.write_clause<NewLit>({gvar, -var_phase});

			gman.open_rup_lemma(-rup.num_clauses);
			//grat_proof.insert(grat_proof.end(), gvar_downwards_propagation_sequence.rbegin(), gvar_downwards_propagation_sequence.rend());
			if (!gvar_downwards_shortcut_sequence.empty()) {
				gman.unit(gvar_downwards_shortcut_sequence.back()); // g := false
			}
			gman.unit(cert->num_clauses + num_cnf_clauses - 9); // f1 := false
			gman.unit(cert->num_clauses + num_cnf_clauses - 5); // out_var := false
			gman.rev_unit_sequence(prop_neg[var]);
			/*if (prop_clause != prop.end()) {
				grat_proof.push_back(prop_clause->second[1]);
			}*/
			gman.unit(eflit_def[get_eflit(var, var_phase)] + 1);
			gman.close_rup_lemma(gvar_definition_conflict_clause.back());

			rup.write_clause<NewLit>({gvar});

			gman.open_rup_lemma(-rup.num_clauses);
			gman.unit(-(rup.num_clauses - 1));
			//grat_proof.insert(grat_proof.end(), gvar_downwards_propagation_sequence.rbegin(), gvar_downwards_propagation_sequence.rend());
			if (!gvar_downwards_shortcut_sequence.empty()) {
				gman.unit(gvar_downwards_shortcut_sequence.back()); // g := false
				gvar_downwards_shortcut_sequence.pop_back();
			}
			gman.unit(cert->num_clauses + num_cnf_clauses - 6);  // f2 := false
			gman.unit(cert->num_clauses + num_cnf_clauses - 2);  // new_out1 := true
			gman.unit(cert->num_clauses + num_cnf_clauses - 10); // f1 := true
			gman.unit(cert->num_clauses + num_cnf_clauses - 3);  // out_var := true
			gman.rev_unit_sequence(prop_pos[var]);
			/*if (prop_clause != prop.end()) {
				grat_proof.push_back(prop_clause->second[0]);
			}*/
			gman.unit(eflit_def[get_eflit(var, var_phase)] + 0);
			gman.close_rup_lemma(gvar_definition_conflict_clause.back());

			gman.unit_clause(-rup.num_clauses);

			countermodel_out_var[var] = new_out2;
			
			gvar_definition_conflict_clause.pop_back();

		}
		
		/* add the clauses that short-circuit the RFAO array to the last partial circuit
		 *
		 * for a given var = abs(lit), we have that
		 *	 ( "|" is logical or, "{}" designates a falsified literal )
		 *
		 * if lit > 0:
		 *	 current_id		: -old_out | new_out
		 *	 current_id + 1 : old_out | {-g} | -new_out
		 * if lit < 0:
		 *	 current_id		: old_out | -new_out
		 *	 current_id + 1 : -old_out | {-g} | new_out
		 *
		 * and regardless (prop_clause[x] propagates 1-x into var)
		 *
		 *			 SHOULDN'T THIS BE CHANGED THOUGH?
		 * 
		 * prop_clause[0] = var | -old_out
		 * prop_clause[1] = -var | old_out
		 *
		 * the new prop_clause will be the resolvent of the old prop_clause and the
		 * appropriate definition. This is formalized below.
		 *
		 */
		GRAT_ClauseID running_grat_id = cert->num_clauses + num_cnf_clauses - 3*reduced_simple.size() - 12*reduced_merged.size() + 2;
		for (int32_t lit : reduced_simple) {
			int32_t var = abs(lit);
			GRAT_ClauseID delta = (lit > 0);

			prop_pos[var].push_back(running_grat_id + delta);
			prop_neg[var].push_back(running_grat_id + 1 - delta);

			running_grat_id += 3;
		}

		running_grat_id = cert->num_clauses + num_cnf_clauses - 12*reduced_merged.size();

		// update prop clauses for reduced merged literals
		for (vector<OldVar>::reverse_iterator rit = reduced_merged.rbegin(); rit != reduced_merged.rend(); rit++) {
			OldVar var = *rit;
			//auto prop_clause = prop.find(var);

			gman.unit_clauses({running_grat_id + 1,
							   running_grat_id + 4});

			prop_pos[var].push_back(running_grat_id + 9);
			prop_pos[var].push_back(running_grat_id + 11);

			prop_neg[var].push_back(running_grat_id + 8);
			prop_neg[var].push_back(running_grat_id + 12);

			running_grat_id += 12;
		}

		reduced_lits.clear();
		reduced_simple.clear();
		reduced_merged.clear();
		/* if a clause has been replaced by a g variable, mark that it's deletion
		 * information should not be forwarded to the rup proof */
		if (delinfo)
			no_delete.insert(resolvent);
	} else {
		/* okay, weird shit going on, apparently it can happen that DepQBF
		 * performs dummy reductions and the reduced clause is then equal
		 * to the premise. Therefore, we have to check if this is truly a
		 * resolution step, in which case we proceed as usual, or whether
		 * this is a fake reduction, in which case we re-route the GRAT id. */
		if (parent_right > 0) {
			// if the shadow clause is empty and there were no reductions,
			// we know that there were no merges and both premises are unit
			if (shadcls.empty()) {
				gman.unit_clause(get_grat_id[parent_left]);
				conflict_clause = get_grat_id[parent_right];
				no_delete.insert(parent_left);
				no_delete.insert(parent_right);
			} else {
				// if there were merged literals, we need to distinguish cases
				// based on the pivot in order to propagate everything
				if (!merged_lits.empty()) {
					rup.ofs << pivot << " "; rup.write_clause(shadcls);

					gman.open_rup_lemma(-rup.num_clauses);
					gman.unit_sequence(merge_propagation_sequence_left);
					gman.close_rup_lemma(get_grat_id[parent_left]);

					rup.write_clause(shadcls);

					gman.open_rup_lemma(-rup.num_clauses);
					gman.unit(-(rup.num_clauses - 1));
					gman.unit_sequence(merge_propagation_sequence_right);
					gman.close_rup_lemma(get_grat_id[parent_right]);

				} else {
					rup.write_clause(shadcls);

					gman.open_rup_lemma(-rup.num_clauses);
					gman.unit(get_grat_id[parent_right]);
					gman.close_rup_lemma(get_grat_id[parent_left]);
				}
				get_grat_id[resolvent] = -rup.num_clauses;
			}
		} else {
			get_grat_id[resolvent] = get_grat_id[parent_left];
			last_use_of[parent_left] = last_use_of[resolvent];
			if (shadcls.empty()) {
				conflict_clause = get_grat_id[parent_left];
			}
		}

		if (shadcls.size() <= delinfo) {
			no_delete.insert(resolvent);
		}
	}

	merged_lits.clear();
	shadcls.clear();

	// clear the phases of reduced literals
	for (OldLit lit : reduced_lits) {
		if (lit > 0) {
			phase.erase({resolvent, lit});
		}
	}

	return 0;
}

void ProofTranslator::pack_prop_sequence(OldVar var, bool pos) {

	NewVar out_var = countermodel_out_var[var];

	if (pos) {
		rup.write_clause<NewLit>({var, -out_var});
		gman.open_rup_lemma(-rup.num_clauses);
		// TODO: this insertion is not very neat, because it's not a full vector, same in the else branch
		gman.grat_proof.insert(gman.grat_proof.end(), prop_pos[var].begin(), prop_pos[var].end() - 1);
		gman.close_rup_lemma(prop_pos[var].back());

		prop_pos[var].clear();
		prop_pos[var].push_back(-rup.num_clauses);
	} else {
		rup.write_clause<NewLit>({-var, out_var});
		gman.open_rup_lemma(-rup.num_clauses);
		gman.grat_proof.insert(gman.grat_proof.end(), prop_neg[var].begin(), prop_neg[var].end() - 1);
		gman.close_rup_lemma(prop_neg[var].back());

		prop_neg[var].clear();
		prop_neg[var].push_back(-rup.num_clauses);
	}
}

bool ProofTranslator::record_axiom(QRP_ClauseID current_id) {

	++statistics.num_core_axioms;

	if (!have_formula) {
		// can't compare with the matrix, but we should check for auxiliary Tseitin variables
		// and record a GRAT ID
		get_grat_id[current_id] = statistics.num_core_axioms;
		for (OldLit lit : clause_database[current_id]) {
			OldVar var = abs(lit);
			if (var > max_var) {
				max_var = var;
			}
		}
		return true;
	}

	if (primary_type == 1) {
		// initial term, careful, it's already negated
		rup.write_clause(clause_database[current_id]);
		get_grat_id[current_id] = -rup.num_clauses;

		gman.open_rup_lemma(-rup.num_clauses);
		//memset(initial_term_chi, 0, qbf_num_vars+1);
		unordered_set<OldLit> initial_term(clause_database[current_id].begin(),
										   clause_database[current_id].end());
		GRAT_ClauseID current_clause = 0;
		for (size_t clause_idx = 0; clause_idx < matrix.size(); ++clause_idx) {
			vector<OldLit>& clause = matrix[clause_idx];
			if (!tautological[clause_idx]) {
				size_t current_lit = 1;
				for (auto lit : clause) {
					// initial_term is negated, so check for presence of -lit
					if (initial_term.count(-lit)) {
						gman.unit(current_clause + current_lit);
						break;
					} else {
						++current_lit;
					}
				}
				if (current_lit > clause.size()) {
					// TODO: implement some incomplete heuristic in order to attempt to recover the satisfying assignment
					if (verbosity > 1) {
						std::cout << "WARNING: Non-hitting initial term with the id " << current_id << std::endl;
						std::cout << "Unsatisfied clause no. " << clause_idx << " is:" << std::endl;
						for (auto lit : clause) {
							std::cout << lit << " ";
						}
						std::cout << std::endl;
					}
				}
			}
			current_clause += clause.size() + 1;
		}
		gman.close_rup_lemma(num_cnf_clauses);

		// On January 25th 2020, Qute did not record the existential reduction it performed
		// on an initial term in case when further resolutions followed immediately. This
		// led to some proofs being reported invalid since a literal that should have been
		// removed right after model generation remained, and later clashed resulting in
		// an invalid merge. Therefore, we perform a safety reduction here, and in case
		// the reduction is in fact recorded later in the proof, the GRAT id will simply be
		// rerouted.
		
		QRP_ClauseID reduct_id = spare_QRP_IDs[0];

		// resolving with an empty constraint is in fact reduction
		clause_database[reduct_id] = resolve(clause_database[current_id], {}, constraint_type[current_id]);

		translate_resolution_step(current_id, 0, reduct_id);

		clause_database[current_id] = clause_database[reduct_id];
		get_grat_id[current_id] = get_grat_id[reduct_id];
		clause_database.erase(reduct_id);
		get_grat_id.erase(reduct_id);
	} else {
		// input clause
		
		/* TODO: figure out how to test for input clause properly
		 * the problems are:
		 *
		 *	 we assume the clauses come in the same order in the QRP as in the QDIMACS
		 */

		while (last_orig_clause_seen < matrix.size() && !setequal(clause_database[current_id], matrix[last_orig_clause_seen])) {
			++last_orig_clause_seen;
		}
		// because clauses in the proof are 1-indexed, not 0-indexed like in the variable matrix;
		// additionally we advance the variable last_orig_clause_seen for the following search
		++last_orig_clause_seen;

		if (last_orig_clause_seen > matrix.size()) {
			// error, input clause is invalid
			std::cout << "ERROR: Input clause with the id " << current_id << " does not occur in the matrix" << std::endl;
			return false;
		}

		get_grat_id[current_id] = last_orig_clause_seen;
		if (clause_database[current_id].empty()) {
			conflict_clause = last_orig_clause_seen;
		}
	}

	return true;
}







/* Organize the clause by splitting it on the given depth.
 * Returns the index l, such that the literals with depth at most depth
 * have indices <l, the ones with strictly greater depth have indices >=l.
 */
size_t ProofTranslator::split_by_depth(vector<OldVar>& clause, uint32_t depth) {
	size_t l = 0, u = clause.size();
	while (l < u) {
		int32_t lit = clause[l];
		qdata varq = var_data[abs(lit)];
		if (varq.depth > depth) {
			clause[l] = clause[--u];
			clause[u] = lit;
		} else {
			l++;
		}
	}
	return l;
}

/* Verify that the resolvent of c1 and c2 is indeed a resolvent, and collect
 * merged literals from c1 into merged_lits and literals reduced after resolution
 * into reduced_lits. Returns the pivot literal that occurs in c1 if the
 * resolution is OK, otherwise 0.
 *
 * Implementation notes: the clauses c1, c2, resolvent are supposed to be sorted
 * and no translation into unordered_set takes place. 
 */
int32_t ProofTranslator::check_resolution(vector<OldLit>& c1, vector<OldLit>& c2, vector<OldLit>& resolvent, vector<OldLit>& merged_lits, vector<OldLit>& reduced_lits, int primary_type) {
	int32_t pivot = 0;
	uint32_t max_primary_depth = 0;
	int32_t rightmost_primary = 0;
	for (int32_t lit : resolvent) {
		int32_t var = abs(lit);
		// TODO the if-condition is hacky: it assumes that unknown variables are primary
		// relies on the assumption that unknown variables are auxiliary Tseitin variables
		if (var_data.find(var) == var_data.end()) {
			rightmost_primary = var;
			max_primary_depth = UINT_MAX;
		} else if (var_data[var].type == primary_type && var_data[var].depth > max_primary_depth) {
			rightmost_primary = var;
			max_primary_depth = var_data[var].depth;
		}
	}
	uint32_t min_merged_depth = std::numeric_limits<uint32_t>::max();
	// careful! Queries are no longer in sorted order, if we use compare_lits,
	// must use compare_lits_weak, which only compares variables
	// queries come in increasing order of variables, but not necessarily literals
	SortedQueryOracle oracle_c2(c2, compare_lits_weak);
	SortedQueryOracle oracle_res(resolvent, compare_lits_weak);
	for (int32_t lit : c1) {
		int32_t var = abs(lit);
		bool is_primary = (var_data.find(var) == var_data.end()) || (var_data[var].type == primary_type);
		if (oracle_c2.has(-lit)) {
			if (is_primary) {
				if (pivot != 0 && lit != pivot) {
					std::cout << lit << ": duplicate pivot (already have " << pivot << ")\n";
					return 0;
				} else {
					pivot = lit;
				}
			} else {
				/* this step depends on the fact that in the ordering of the literals,
				 * literals on one variable come directly one after the other (are an interval).
				 * If this is violated, a variable may be pushed more than once, which should
				 * theoretically still be OK thanks to phase caching, but better not do it. */
				if (merged_lits.empty() || abs(merged_lits.back()) != var) {
					if (var_data[var].depth < min_merged_depth)
						min_merged_depth = var_data[var].depth;
					merged_lits.push_back(lit);
					//if (verbosity >= 3)
					//	std::cout << lit << " is merged!\n";
				}
			}
		}
		if (!oracle_res.has(lit)) {
			if (is_primary) {
				if (lit != pivot) {
					std::cout << lit << ": primary reduction in c1\n";
					return 0;
				}
			} else {
				if (var_data[var].depth <= max_primary_depth) {
					std::cout << "non-tailing reduction in c1: " << lit << " reduced in the presence of " << rightmost_primary << " (claimed pivot " << pivot << ")\n";
					return 0;
				}
				reduced_lits.push_back(lit);
			}
		}
	}

	if (pivot == 0) {
		std::cout << "no pivot\n";
		return 0;
	}

	uint32_t pivot_depth = UINT_MAX;
	if (var_data.find(abs(pivot)) != var_data.end()) {
		pivot_depth = var_data[abs(pivot)].depth;
	}

	if (min_merged_depth < pivot_depth) {
		std::cout << "illegal merge" << std::endl;
		std::cout << "pivot: " << pivot << std::endl;
		std::cout << "illegally merged variables: ";
		for (OldLit lit : merged_lits)
			if (var_data[abs(lit)].depth < var_data[abs(pivot)].depth)
				std::cout << lit << " ";
		std::cout << std::endl;
		return 0;
	}
	//if (verbosity >= 3 && !merged_lits.empty())
	//	std::cout << "pivot for these merges: " << pivot << std::endl;

	/* Since reduced_lits was populated in sorted order, we can use has_literal on it,
	 * to determine if a given literal was already collected for reduction if it's
	 * contained in both c1 and c2. */
	SortedQueryOracle oracle_reduced(reduced_lits, compare_lits_weak);
	oracle_res.rewind();
	//print_clause(std::cout, reduced_lits);
	for (int32_t lit: c2) {
		if (!oracle_reduced.has(lit)) {
			//std::cout << "reduced_lits does not have " << lit << std::endl;
			if (!oracle_res.has(lit)) {
				//std::cout << "resolvent does not have " << lit << std::endl;
				int32_t var = abs(lit);
				/*if (var_data.find(var) == var_data.end()) {
					std::cerr << std::endl << var << " is aux";
				} else if (var_data[var].type == primary_type) { 
					std::cerr << std::endl << var << " is pri";
				} else {
					std::cerr << std::endl << var << " is sec, but " << pivot << " is pivot";
				}*/
				if ((var_data.find(var) == var_data.end()) || (var_data[var].type == primary_type)) {
					if (lit != -pivot) {
						std::cout << lit << ": primary reduction in c2\n";
						return 0;
					}
				} else {
					if (var_data[var].depth < max_primary_depth) {
						std::cout << std::endl << lit << ": non-tailing reduction in c2\n";
						return 0;
					}
					reduced_lits.push_back(lit);
				}
			}
		}
	}
	SortedQueryOracle oracle_c1(c1, compare_lits_weak);
	oracle_c2.rewind();
	for (int32_t lit: resolvent) {
		if (!oracle_c1.has(lit) && !oracle_c2.has(lit)) {
			std::cout << "introduction of literals into resolvent\n";
			return 0;
		}
	}
	return pivot;
}

// naively computes a sorted resolvent of c1 and c2, discarding all clashing primaries
// and merging all clashing secondaries: the result needs to be checked for validity
vector<OldLit> ProofTranslator::resolve(const vector<OldLit>& c1, const vector<OldLit>& c2, int primary_type) {
	vector<OldLit> resolvent;
	size_t i1 = 0, i2 = 0;

	uint32_t max_primary_depth = 0;
	while (i1 < c1.size() || i2 < c2.size()) {
		if (i1 == c1.size()) {
			OldVar var = abs(c2[i2]);
			if (var_data.find(var) == var_data.end()) {
				max_primary_depth = UINT_MAX;
			} else if (var_data[var].type == primary_type && max_primary_depth < var_data[var].depth) {
				max_primary_depth = var_data[var].depth;
			}
			++i2;
		} else if (i2 == c2.size()) {
			OldVar var = abs(c1[i1]);
			if (var_data.find(var) == var_data.end()) {
				max_primary_depth = UINT_MAX;
			} else if (var_data[var].type == primary_type && max_primary_depth < var_data[var].depth) {
				max_primary_depth = var_data[var].depth;
			}
			++i1;
		} else {
			OldLit lit1 = c1[i1];
			OldVar var1 = abs(lit1);
			OldLit lit2 = c2[i2];
			OldVar var2 = abs(lit2);
			if (var1 == var2) {
				if (lit1 == lit2) {
					if (var_data.find(var1) == var_data.end()) {
						max_primary_depth = UINT_MAX;
					} else if (var_data[var1].type == primary_type && max_primary_depth < var_data[var1].depth) {
						max_primary_depth = var_data[var1].depth;
					}
					++i1;
					++i2;
				} else {
					// even if this is a primary, it's the pivot, so it won't appear in the resolvent
					++i1;
					++i2;
				}
			} else if (var1 < var2) {
				if (var_data.find(var1) == var_data.end()) {
					max_primary_depth = UINT_MAX;
				} else if (var_data[var1].type == primary_type && max_primary_depth < var_data[var1].depth) {
					max_primary_depth = var_data[var1].depth;
				}
				++i1;
			} else {
				if (var_data.find(var2) == var_data.end()) {
					max_primary_depth = UINT_MAX;
				} else if (var_data[var2].type == primary_type && max_primary_depth < var_data[var2].depth) {
					max_primary_depth = var_data[var2].depth;
				}
				++i2;
			}
		}
	}

	i1 = i2 = 0;

	while (i1 < c1.size() || i2 < c2.size()) {
		if (i1 == c1.size()) {
			OldLit lit = c2[i2];
			OldVar var = abs(lit);
			if (var_data.find(var) == var_data.end() || var_data[var].type == primary_type || var_data[var].depth < max_primary_depth)
				resolvent.push_back(lit);
			++i2;
		} else if (i2 == c2.size()) {
			OldLit lit = c1[i1];
			OldVar var = abs(lit);
			if (var_data.find(var) == var_data.end() || var_data[var].type == primary_type || var_data[var].depth < max_primary_depth)
				resolvent.push_back(lit);
			++i1;
		} else {
			OldLit lit1 = c1[i1];
			OldVar var1 = abs(lit1);
			OldLit lit2 = c2[i2];
			OldVar var2 = abs(lit2);
			if (var1 == var2) {
				if (lit1 == lit2) {
					if (var_data.find(var1) == var_data.end() || var_data[var1].type == primary_type || var_data[var1].depth < max_primary_depth)
						resolvent.push_back(lit1);
					++i1;
					++i2;
				} else {
					if (var_data.find(var1) == var_data.end() || var_data[var1].type == primary_type) {
						++i1;
						++i2;
					} else {
						if (lit1 < lit2) {
							// according to compare_lits, the negative literal comes first
							if (var_data[var1].depth < max_primary_depth) {
								// only push secondary clashing literals
								resolvent.push_back(lit1);
							}
							++i1;
						} else {
							if (var_data[var2].depth < max_primary_depth) {
								// only push secondary clashing literals
								resolvent.push_back(lit2);
							}
							++i2;
						}
					}
				}
			} else if (var1 < var2) {
				if (var_data.find(var1) == var_data.end() || var_data[var1].type == primary_type || var_data[var1].depth < max_primary_depth)
					resolvent.push_back(lit1);
				++i1;
			} else {
				if (var_data.find(var2) == var_data.end() || var_data[var2].type == primary_type || var_data[var2].depth < max_primary_depth)
					resolvent.push_back(lit2);
				++i2;
			}

		}
	}
	/* for (OldLit l : resolvent) {
		std::cout << l << " ";
	}
	std::cout << std::endl; */
	return resolvent;
}

/* Check that the given reduction step is sound, returns 1 on success, otherwise
 * the following error codes:
 *	 0: reduction on primary literal
 *	-1: reduction on non-tailing secondary literal
 *	-2: introduction of literal not from premise
 */
int32_t ProofTranslator::check_reduction(vector<OldLit>& premise, vector<OldLit>& conclusion, vector<OldLit>& reduced_lits, int primary_type) {
	uint32_t max_primary_depth = 0;
	for (int32_t lit : conclusion) {
		int32_t var = abs(lit);
		if (var_data[var].type == primary_type && var_data[var].depth > max_primary_depth) {
			max_primary_depth = var_data[var].depth;
		}
	}
	for (int32_t lit : premise) {
		int32_t var = abs(lit);
		if (!has_literal(conclusion, lit)) {
			if (var_data[var].type == primary_type) {
				return 0;
			} else if (var_data[var].depth <= max_primary_depth) {
				return 1;
			}
			reduced_lits.push_back(lit);
		}
	}
	for (int32_t lit : conclusion) {
		if (!has_literal(premise, lit)) {
			return -2;
		}
	}
	return 1;
}

/* Splits the reduced literals into those that are not merged and those that are merged.
 * For the merged ones, it is assumed that always both literals are reduced at once,
 * therefore the positive literal is present, and only the positive literal is recorded. */
void ProofTranslator::split_reduction_step(QRP_ClauseID id, vector<OldLit>& reduced_lits, vector<OldLit>& reduced_simple, vector<OldLit>& reduced_merged) {
	for (int32_t lit : reduced_lits) {
		if (std::abs(get_phase(id, lit)) != CONST_TRUE) {
			if (lit > 0) {
				reduced_merged.push_back(lit);
			}
		} else {
			reduced_simple.push_back(lit);
		}
	}
}

vector<NewVar> ProofTranslator::shadow(QRP_ClauseID id) {
	if (verbosity >= 3 && !merged_vars_in[id].empty()) {
		std::cout << "Shadow clause for step " << id << ":";
	}
	vector<NewVar> shadcls;
	for (int32_t lit : clause_database[id]) {
		int64_t ef_lit = get_eflit(lit, get_phase(id, lit));
		if (ef_lit == lit || lit > 0) {
			shadcls.push_back(ef_lit);
			if (verbosity >= 3 && !merged_vars_in[id].empty()) {
				std::cout << " " << ef_lit << "(" << lit << ")";
			}
		}
	}
	if (verbosity >= 3 && !merged_vars_in[id].empty())
		std::cout << std::endl;
	
	return shadcls;
}






// #################################
// PHASE FUNCTIONS AND CO
// #################################

NewVar ProofTranslator::get_phase(QRP_ClauseID id, OldLit lit) {
	unordered_map<ClauseVarPair, NewVar>::iterator it = phase.find({id, abs(lit)});
	if (it != phase.end()) {
		return it->second;
	}
	return lit > 0 ? CONST_TRUE : CONST_FALSE;
}

NewVar ProofTranslator::get_eflit(OldLit lit, NewVar phi) {
	OldVar var = abs(lit);
	unordered_map<VarPhasePair, NewVar>::iterator it = eflit.find({var, phi});
	if (it != eflit.end()) {
		return it->second;
	}
	return lit;
}

NewVar ProofTranslator::update_phase(OldLit pivot, NewVar phase_left, NewVar phase_right) {
	// pivot is the literal as it appears in the left parent
	// always phase_left != phase_right
	NewVar phi = get_fresh_variable();
	if (phase_left == CONST_TRUE) {
		phase_def[{pivot, phi}] = num_cnf_clauses + cert->num_clauses + 1;
		phase_def[{-pivot, phi}] = num_cnf_clauses + cert->num_clauses + 2;
		cert->bincls(pivot, phi);
		if (phase_right == CONST_FALSE) {
			cert->bincls(-pivot, -phi);
			cert->num_clauses += 2;
		} else {
			cert->tercls(-pivot, -phase_right,  phi);
			cert->tercls(-pivot,  phase_right, -phi);
			cert->num_clauses += 3;
		}
	} else if (phase_left == CONST_FALSE) {
		phase_def[{pivot, phi}] = num_cnf_clauses + cert->num_clauses + 1;
		phase_def[{-pivot, phi}] = num_cnf_clauses + cert->num_clauses + 2;
		cert->bincls(pivot, -phi);
		if (phase_right == CONST_TRUE) {
			cert->bincls(-pivot, phi);
			cert->num_clauses += 2;
		} else {
			cert->tercls(-pivot, -phase_right,  phi);
			cert->tercls(-pivot,  phase_right, -phi);
			cert->num_clauses += 3;
		}
	} else {
		phase_def[{pivot, phi}] = num_cnf_clauses + cert->num_clauses + 1;
		phase_def[{-pivot, phi}] = num_cnf_clauses + cert->num_clauses + 3;
		cert->tercls(pivot, -phase_left,  phi);
		cert->tercls(pivot,  phase_left, -phi);
		if (phase_right == CONST_TRUE) {
			cert->bincls(-pivot, phi);
			cert->num_clauses += 3;
		} else if (phase_right == CONST_FALSE) {
			cert->bincls(-pivot, -phi);
			cert->num_clauses += 3;
		} else {
			cert->tercls(-pivot, -phase_right,  phi);
			cert->tercls(-pivot,  phase_right, -phi);
			cert->num_clauses += 4;
		}
	}
	/*phase_def[{pivot, phi}] = num_cnf_clauses + cert.num_clauses + 1;
	phase_def[{-pivot, phi}] = num_cnf_clauses + cert.num_clauses + 3;
	//cert.write_clause<NewLit>({ pivot, -phase_left ,  phi});
	//cert.write_clause<NewLit>({ pivot,	phase_left , -phi});
	//cert.write_clause<NewLit>({-pivot, -phase_right,  phi});
	//cert.write_clause<NewLit>({-pivot,	phase_right, -phi});
	cert.ite_gate(phi, pivot, phase_left, phase_right);*/
	phase_cache.insert({{pivot, phase_left, phase_right}, phi});
	/* if (phase_left == -phase_right) {
		phase_cache.insert({{-pivot, phase_left, phase_right}, -phi});
	} */
	return phi;
}

NewVar ProofTranslator::make_eflit(OldVar var, NewVar phase_var) {
	int64_t new_eflit = get_fresh_variable();
	eflit_def[new_eflit] = num_cnf_clauses + cert->num_clauses + 1;
	cert->equiv_gate(new_eflit, var, phase_var);
	//cert.write_clause<NewLit>({-new_eflit, -var,  phase_var});
	//cert.write_clause<NewLit>({-new_eflit,	var, -phase_var});
	//cert.write_clause<NewLit>({ new_eflit,	var,  phase_var});
	//cert.write_clause<NewLit>({ new_eflit, -var, -phase_var});
	return new_eflit;
}


// #################
//		  IO
// #################


