#include "proof_translator.hh"

#include <cstdlib>
#include <string.h>

using std::ifstream;

bool ProofTranslator::translate() {

    ifstream qrp(qrpfile);

    string line;


    /* TODO: Implement various modes; the advantage is that with some assumptions
     * on the proof structure, we can avoid memory overhead and even produce slightly
     * smaller RUP proofs in some cases. */
    // bool implicit_immediate_reductions = false;
    // bool implicit_resolution_reductions = false;

    /* print a fake prefix to the cnf--later rewrite when values are known
     * TODO: consider storing the CNF in memory as opposed to writing to
     * a file immediately--no need for this placeholder, and the CNF is usually
     * not that large anyway (maybe?) */
    cert.ofs << "p cnf ____________________ ____________________\n";
    //ClauseCNT num_cert_clauses = 0;

    /* read up to the preamble line, discard any comments */
    while (std::getline(qrp, line) && line[0] == 'c') {}

    // parse the preamble line, extract number of variables
    {
        std::istringstream iss(line);
        iss.ignore(6);
        iss >> max_var;
    }
    size_t qbf_num_vars = max_var;

    /* read the prefix and store quantifier types and depths of variables
     * into the *global* variable var_data */
    std::streampos matrix_begin = qrp.tellg();
    {
        char last_qtype = 'x';
        uint32_t last_qdepth = 0;
        
        while ((matrix_begin = qrp.tellg()) && std::getline(qrp, line)) {
            char qtype = line[0];
            if (qtype != 'a' && qtype != 'e')
                break;
            if (qtype != last_qtype) {
                last_qtype = qtype;
                last_qdepth++;
            }
            int32_t var;
            std::istringstream iss(line);
            iss.ignore(2);
            while (iss >> var) {
                if (var == 0)
                    break;
                var_data[var] = {last_qdepth, qtype == 'e'};
            }
        }
    }

    // BEGIN FIRST PASS ---------------------------------
    
    unordered_map<QRP_ClauseID, QRP_ClauseID> last_use_of;
    unordered_map<QRP_ClauseID, std::array<QRP_ClauseID, 2>> parents_of;

    QRP_ClauseID current_id;

    do {
        QRP_ClauseID p1 = 0, p2 = 0;
        char * tmp_line;
        current_id = strtoul(line.c_str(), &tmp_line, 10);
        tmp_line = strstr(tmp_line, " 0 ");
        if (tmp_line == NULL) {
            std::cerr << "Syntax error in step with the id " << current_id << std::endl;
            return -1;
        }
        tmp_line += 3;
        p1 = strtoul(tmp_line, &tmp_line, 10);
        if (p1 > 0) {
            p2 = strtoul(tmp_line, &tmp_line, 10);
            parents_of.insert({current_id, {{p1, p2}}});
        }
    } while (std::getline(qrp, line) && std::tolower(line[0]) != 'r');

    std::transform(line.begin(), line.end(), line.begin(), tolower);
    if (line == "r sat") {
        primary_type = 0;
    }

    // load the formula from the QDIMACS file, it's necessary in every case
    vector<vector<OldLit>> matrix = read_qdimacs();
    num_cnf_clauses = matrix.size();

    int8_t * initial_term_chi = NULL;
    if (primary_type == 0) {
        initial_term_chi = new int8_t[qbf_num_vars + 1];
        // recalculate num_cnf_clauses
        for (auto& c : matrix) {
            num_cnf_clauses += c.size();
        }
        // top level clause
        ++num_cnf_clauses;
    } else {
        // in the unsat case, we need to sort the clauses of the matrix for efficient comparisons 
        // however, careful, because in the sat case, they must not be sorted!
        for (auto& c : matrix) {
            sort(c.begin(), c.end(), compare_lits);
			c.resize(std::distance(c.begin(), std::unique(c.begin(), c.end())));
        }
    }

    stack<QRP_ClauseID, vector<QRP_ClauseID>> core_clauses;
    core_clauses.push(current_id);
    last_use_of[current_id] = 0;
    while (!core_clauses.empty()) {
        current_id = core_clauses.top();
        core_clauses.pop();
        unordered_map<QRP_ClauseID, std::array<QRP_ClauseID, 2>>::iterator pit = parents_of.find(current_id);
        if (pit != parents_of.end()) {
            for (auto parent: pit->second) {
                if (parent) {
                    unordered_map<QRP_ClauseID, QRP_ClauseID>::iterator it = last_use_of.find(parent);
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
    
    // END FIRST PASS   ---------------------------------
    qrp.clear();
    qrp.seekg(matrix_begin);

    /* read and translate the actual proof
     * begin with the line that was already read
     * hence the do {} while; instead of while */
    vector<OldLit> merged_lits;
    vector<OldLit> reduced_lits;
    vector<OldLit> reduced_simple;
    vector<OldVar> reduced_merged;
    vector<NewVar> shadcls;
    vector<NewVar> auxg; // holds intermediate g-variables for merged reduction steps
    
    /* this contains the ids of clauses that were replaced by 'g' variables,
     * and thus it makes no sense to print DRAT deletion information for them. */
    unordered_set<QRP_ClauseID> no_delete;

    // GRAT stuff
    //unordered_map<int32_t, vector<clause_id_grat>> propagate_false;
    //unordered_map<int32_t, vector<clause_id_grat>> propagate_true;
	
    /* instead of the RFAO arrays, we now only keep track of two clause ids, which
     * encode the current derived equivalence between a variable and its partial
     * circuit.
	 *
	 * prop holds these two clauses, and in fact whenever prop has an entry for var,
	 * then the two clauses whose ids it holds are
	 *
	 * (var, -countermodel_out_var[var]) and (-var, countermodel_out_var[var])
	 */
    unordered_map<OldVar, std::array<GRAT_ClauseID, 2>> prop;
    unordered_map<QRP_ClauseID, GRAT_ClauseID> get_grat_id;
    unordered_map<OldVar, NewVar> countermodel_out_var;
    vector<int32_t> grat_proof = {6, 0};
    GRAT_ClauseID conflict_clause = 0;

	// define an auxiliary variable that holds the value 1
	CONST_TRUE = get_fresh_variable();
	CONST_FALSE = -CONST_TRUE;
	cert.define_variable_term<NewLit>(CONST_TRUE, {});
	grat_proof.push_back(1);
	grat_proof.push_back(num_cnf_clauses + cert.num_clauses);
	grat_proof.push_back(0);

    uint64_t num_reductions = 0, num_merges = 0;
    size_t last_orig_clause_seen = 0;
    //size_t threshold = 1000;
    while (std::getline(qrp, line)) {
        if (line[0] == 'r')
            continue;

        QRP_ClauseID parent_left, parent_right;
        vector<OldLit>& clause = read_proof_line(line.c_str(), current_id, parent_left, parent_right);

        if (last_use_of.find(current_id) == last_use_of.end()) {
            clause_database.erase(current_id);
            continue;
        }

        if (primary_type == 0) {
            negate(clause);
        }

		// sort and remove duplicate literals
        // TODO: implement total sorted order, since negation can now take place before sorting
        sort(clause.begin(), clause.end(), compare_lits);
		clause.resize(std::distance(clause.begin(), std::unique(clause.begin(), clause.end())));

        if (parent_left != 0) {
            OldLit pivot = 0;
            vector<OldLit>& c1 = clause_database[parent_left];
            if (parent_right != 0) {
                // resolvent
                vector<OldLit>& c2 = clause_database[parent_right];
                pivot = check_resolution(c1, c2, clause, merged_lits, reduced_lits);
                if (pivot == 0) {
                    std::cerr << "Failed resolution step with id " << current_id << std::endl;
                    return -1;
                }
                // first update phases, then handle reductions
                for (size_t i = 0; i < merged_lits.size(); ++i) {
					OldLit lit = merged_lits[i];
                    OldVar var = abs(lit);
                    NewVar phase_left = get_phase(parent_left, lit);
                    NewVar phase_right = get_phase(parent_right, -lit);
                    PivotPhasesTuple cache_key = {pivot, phase_left, phase_right};
                    unordered_map<PivotPhasesTuple, NewVar>::iterator ppit = phase_cache.find(cache_key);
                    NewVar var_phase, var_eflit;
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
					phase.insert({{current_id, var}, var_phase});
                    if (verbose_output)
                        std::cerr << "Phase of " << var << " in " << current_id << " is " << var_phase << std::endl;

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
						//   pivot^0        +  phase_left^f              =>  var_phase^f  [ phase_def[var_phase]   ]
						//   eflit_left^1   +  phase_left^f              =>  var^f        [ eflit_def[eflit_left]  ] (only if phase_left is non-trivial)
						//   var_eflit^0    +  var_phase^f    + var^f    =>  0            [ eflit_def[var_eflit]   ]
						//
						//   pivot^1        +  phase_right^f             =>  var_phase^f  [ phase_def[var_phase]   ]
						//   eflit_right^1  +  phase_right^f             =>  var^f        [ eflit_def[eflit_right] ] (only if phase_right is non-trivial)
						//   var_eflit^0    +  var_phase^f    + var^f    =>  0            [ eflit_def[var_eflit]   ]
						// ##############################################################
						
						// TODO: rewrite sequences such as this one into vector.insert(end, initializer_list)
						
						// if phase_left (phase_right) is non-trivial, we need to make a RUP-style case distinction
						if (phase_left != CONST_TRUE) {
							rup.write_clause<NewLit>({var_eflit, pivot, -eflit_left, phase_left});
							grat_proof.push_back(3);
							grat_proof.push_back(-rup.num_clauses);
							//grat_proof.push_back(phase_def[var_phase] + neg_phase_offset);
							grat_proof.push_back(phase_def[{pivot, var_phase}] + 1);
							if (phase_left != CONST_FALSE) {
								grat_proof.push_back(eflit_def[eflit_left] + 0);
							}
							grat_proof.push_back(0);
							grat_proof.push_back(eflit_def[var_eflit] + 2);
						}

						if (phase_left != CONST_FALSE) {
							rup.write_clause<NewLit>({var_eflit, pivot, -eflit_left});
							grat_proof.push_back(3);
							grat_proof.push_back(-rup.num_clauses);
							if (phase_left != CONST_TRUE) {
								grat_proof.push_back(-(rup.num_clauses - 1));
							}
							grat_proof.push_back(phase_def[{pivot, var_phase}] + 0);
							if (phase_left != CONST_TRUE) {
								grat_proof.push_back(eflit_def[eflit_left] + 1);
							}
							grat_proof.push_back(0);
							grat_proof.push_back(eflit_def[var_eflit] + 3);
						}					

						eflit_shortcut[{pivot, var_eflit}] = rup.num_clauses;

						// shortcuts to falsify right parent
						if (phase_right != CONST_TRUE) {
							rup.write_clause<NewLit>({var_eflit, -pivot, -eflit_right, phase_right});
							grat_proof.push_back(3);
							grat_proof.push_back(-rup.num_clauses);
							grat_proof.push_back(phase_def[{-pivot, var_phase}] + 1);
							if (phase_right != CONST_FALSE) {
								grat_proof.push_back(eflit_def[eflit_right] + 0);
							}
							grat_proof.push_back(0);
							grat_proof.push_back(eflit_def[var_eflit] + 2);
						}

						if (phase_right != CONST_FALSE) {
							rup.write_clause<NewLit>({var_eflit, -pivot, -eflit_right});
							grat_proof.push_back(3);
							grat_proof.push_back(-rup.num_clauses);
							if (phase_right != CONST_TRUE) {
								grat_proof.push_back(-(rup.num_clauses - 1));
							}
							grat_proof.push_back(phase_def[{-pivot, var_phase}] + 0);
							if (phase_right != CONST_TRUE) {
								grat_proof.push_back(eflit_def[eflit_right] + 1);
							}
							grat_proof.push_back(0);
							grat_proof.push_back(eflit_def[var_eflit] + 3);
						}

						eflit_shortcut[{-pivot, var_eflit}] = rup.num_clauses;
                    }
                    if (verbose_output)
                        std::cerr << "Eflit of " << var << " in " << current_id << " is " << var_eflit << std::endl;
                }
                // carry over phases of already merged literals that are not being merged now
				copy_phases(parent_left, current_id);
				copy_phases(parent_right, current_id);
            } else {
                check_reduction(c1, clause, reduced_lits);
				copy_phases(parent_left, current_id);
            }

            split_reduction_step(current_id, reduced_lits, reduced_simple, reduced_merged);
            // TODO: avoid the computation of the shadow clause if not necessary
            shadcls = shadow(current_id);

			// compute the propagation sequence for newly merged literals
			// the "left" ("right") sequence is what propagates when the left (right) pivot and the new merged literals are falsified
			vector<GRAT_ClauseID> merge_propagation_sequence_left;
			vector<GRAT_ClauseID> merge_propagation_sequence_right;
			for (NewLit merged_lit : merged_lits) {
				NewVar merged_eflit = get_eflit(merged_lit, get_phase(current_id, merged_lit));
				merge_propagation_sequence_left.push_back(-eflit_shortcut[{pivot, merged_eflit}]);
				merge_propagation_sequence_right.push_back(-eflit_shortcut[{-pivot, merged_eflit}]);
			}

			if (!merged_lits.empty()) {
				++num_merges;
			}

            /* if there are any reduced literals, create the corresponding g_i variables
             * and update the countermodel circuits, else just print the shadow clause. */
            if (!reduced_lits.empty()) {

                // initialize all g-variables
                int64_t g = get_fresh_variable();
                cert.define_variable_clause(g, shadcls);

				// the current clause is at the end of the certificate at the moment
				GRAT_ClauseID current_grat_id = cert.num_clauses + num_cnf_clauses;
                get_grat_id[current_id] = current_grat_id;

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
					cert.define_variable_clause<NewLit>(auxg.back(), {last_aux, get_eflit(var, get_phase(current_id, var))});
					gvar_downwards_propagation_sequence.push_back(cert.num_clauses + num_cnf_clauses - 2);
					gvar_eflit_falsification_sequence.push_back(cert.num_clauses + num_cnf_clauses - 1);
					gvar_definition_conflict_clause.push_back(cert.num_clauses + num_cnf_clauses);
					if (gvar_downwards_propagation_sequence.size() > 1) {
						// the downwards shortcut clause from -g_k to -g, k > 1
						rup.write_clause<NewLit>({auxg.back(), -g});

						grat_proof.push_back(3);
						grat_proof.push_back(-rup.num_clauses);
						grat_proof.push_back(gvar_downwards_propagation_sequence.back());
						grat_proof.push_back(0);
						grat_proof.push_back(gvar_downwards_shortcut_sequence.back());
						
						gvar_downwards_shortcut_sequence.push_back(-rup.num_clauses);
					} else {
						gvar_downwards_shortcut_sequence.push_back(gvar_downwards_propagation_sequence.back());
					}
                }

				// TODO: collapse the gvar_downwards_propagation sequence, by iteratively shortening it by one

				// setting (-g) propagates the negation of the current clause via the 2-clauses
				vector<GRAT_ClauseID> g_def_propagation_sequence;

				for (GRAT_ClauseID g_binclause_id = current_grat_id - shadcls.size(); g_binclause_id < current_grat_id; ++g_binclause_id) {
					g_def_propagation_sequence.push_back(g_binclause_id);
				}

                // handle the simple part of the reduction step
				// compute the countermodel and the propagation sequence
				vector<GRAT_ClauseID> reduction_propagation_sequence;

                for (OldLit lit : reduced_simple) {

                    ++num_reductions;
                    OldVar var = abs(lit);

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
                    int64_t new_out = get_fresh_variable();

                    if (lit < 0) {
                        cert.define_variable_clause<NewLit>(out_var, {-g, new_out});
                        reduction_propagation_sequence.push_back(cert.num_clauses + num_cnf_clauses - 2);
                        auto prop_clause = prop.find(var);
                        if (prop_clause != prop.end()) {
                            reduction_propagation_sequence.push_back(prop_clause->second[0]);
                        }
                    } else {
                        cert.define_variable_term<NewLit>(out_var, {g, new_out});
                        reduction_propagation_sequence.push_back(cert.num_clauses + num_cnf_clauses - 2);
                        auto prop_clause = prop.find(var);
                        if (prop_clause != prop.end()) {
                            reduction_propagation_sequence.push_back(prop_clause->second[1]);
                        }
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

					// begin propagation sequence for a rup clause
					grat_proof.push_back(3);
					// the id of the newly added rup clause
					grat_proof.push_back(-rup.num_clauses);
					grat_proof.insert(grat_proof.end(), gvar_downwards_propagation_sequence.rbegin(), gvar_downwards_propagation_sequence.rend());
					grat_proof.insert(grat_proof.end(), gvar_eflit_falsification_sequence.rbegin(), gvar_eflit_falsification_sequence.rend());
					grat_proof.insert(grat_proof.end(), g_def_propagation_sequence.begin(), g_def_propagation_sequence.end());
					grat_proof.insert(grat_proof.end(), reduction_propagation_sequence.begin(), reduction_propagation_sequence.end());
					grat_proof.insert(grat_proof.end(), merge_propagation_sequence_left.begin(), merge_propagation_sequence_left.end());
					grat_proof.push_back(0);
					grat_proof.push_back(get_grat_id[parent_left]);

					rup.write_clause<NewLit>({gvar});

					// begin propagation sequence for a rup clause
					grat_proof.push_back(3);
					// the id of the newly added rup clause
					grat_proof.push_back(-rup.num_clauses);
					grat_proof.push_back(-(rup.num_clauses - 1));
					grat_proof.insert(grat_proof.end(), gvar_downwards_propagation_sequence.rbegin(), gvar_downwards_propagation_sequence.rend());
					grat_proof.insert(grat_proof.end(), gvar_eflit_falsification_sequence.rbegin(), gvar_eflit_falsification_sequence.rend());
					grat_proof.insert(grat_proof.end(), g_def_propagation_sequence.begin(), g_def_propagation_sequence.end());
					grat_proof.insert(grat_proof.end(), reduction_propagation_sequence.begin(), reduction_propagation_sequence.end());
					grat_proof.insert(grat_proof.end(), merge_propagation_sequence_right.begin(), merge_propagation_sequence_right.end());
					grat_proof.push_back(0);
					grat_proof.push_back(get_grat_id[parent_right]);

					// mark the newly added clause as unit
					grat_proof.push_back(1);
					grat_proof.push_back(-rup.num_clauses);
					grat_proof.push_back(0);

                } else {
					// no merges in this resolultion step
					rup.write_clause<NewLit>({gvar});

					grat_proof.push_back(3);
					grat_proof.push_back(-rup.num_clauses);
					grat_proof.insert(grat_proof.end(), gvar_downwards_propagation_sequence.rbegin(), gvar_downwards_propagation_sequence.rend());
					grat_proof.insert(grat_proof.end(), gvar_eflit_falsification_sequence.rbegin(), gvar_eflit_falsification_sequence.rend());
					grat_proof.insert(grat_proof.end(), g_def_propagation_sequence.begin(), g_def_propagation_sequence.end());
					grat_proof.insert(grat_proof.end(), reduction_propagation_sequence.begin(), reduction_propagation_sequence.end());

					// if this is a resolution step with reduction, additionally one of the parents propagates
					if (parent_right) {
						grat_proof.push_back(get_grat_id[parent_right]);
					}

					// end propagation sequence
					grat_proof.push_back(0);

					// finally, we get a conflict on the other parent
					grat_proof.push_back(get_grat_id[parent_left]);

					// mark the newly added clause as unit
					grat_proof.push_back(1);
					grat_proof.push_back(-rup.num_clauses);
					grat_proof.push_back(0);
				}

				gvar_downwards_propagation_sequence.clear();
				gvar_eflit_falsification_sequence.clear();

                // handle the part with reduced merged literals
                for (vector<OldVar>::reverse_iterator rit = reduced_merged.rbegin(); rit != reduced_merged.rend(); rit++) {
                    OldVar var = *rit;
                    NewVar var_phase = get_phase(current_id, var);
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
					cert.define_variable_clause<NewLit>(f1, {g, -var_phase});
					cert.define_variable_clause<NewLit>(f2, {g, var_phase});

					// new_out := f1 & ( -f2 | ... )
					NewVar new_out1 = get_fresh_variable();
					NewVar new_out2 = get_fresh_variable();
					cert.define_variable_term<NewLit>(out_var, {f1, new_out1});
					cert.define_variable_clause<NewLit>(new_out1, {-f2, new_out2});

					auto prop_clause = prop.find(var);

					rup.write_clause<NewLit>({gvar, -var_phase});

					grat_proof.push_back(3);
					grat_proof.push_back(-rup.num_clauses);
					//grat_proof.insert(grat_proof.end(), gvar_downwards_propagation_sequence.rbegin(), gvar_downwards_propagation_sequence.rend());
					if (!gvar_downwards_shortcut_sequence.empty()) {
						grat_proof.push_back(gvar_downwards_shortcut_sequence.back()); // g := false
					}
					grat_proof.push_back(cert.num_clauses + num_cnf_clauses - 9); // f1 := false
					grat_proof.push_back(cert.num_clauses + num_cnf_clauses - 5); // out_var := false
					if (prop_clause != prop.end()) {
						grat_proof.push_back(prop_clause->second[1]);
					}
					grat_proof.push_back(eflit_def[get_eflit(var, var_phase)] + 1);
					grat_proof.push_back(0);
					grat_proof.push_back(gvar_definition_conflict_clause.back());

					rup.write_clause<NewLit>({gvar});

					grat_proof.push_back(3);
					grat_proof.push_back(-rup.num_clauses);
					grat_proof.push_back(-(rup.num_clauses - 1));
					//grat_proof.insert(grat_proof.end(), gvar_downwards_propagation_sequence.rbegin(), gvar_downwards_propagation_sequence.rend());
					if (!gvar_downwards_shortcut_sequence.empty()) {
						grat_proof.push_back(gvar_downwards_shortcut_sequence.back()); // g := false
						gvar_downwards_shortcut_sequence.pop_back();
					}
					grat_proof.push_back(cert.num_clauses + num_cnf_clauses - 6);  // f2 := false
					grat_proof.push_back(cert.num_clauses + num_cnf_clauses - 2);  // new_out1 := true
					grat_proof.push_back(cert.num_clauses + num_cnf_clauses - 10); // f1 := true
					grat_proof.push_back(cert.num_clauses + num_cnf_clauses - 3);  // out_var := true
					if (prop_clause != prop.end()) {
						grat_proof.push_back(prop_clause->second[0]);
					}
					grat_proof.push_back(eflit_def[get_eflit(var, var_phase)] + 0);
					grat_proof.push_back(0);
					grat_proof.push_back(gvar_definition_conflict_clause.back());

					grat_proof.push_back(1);
					grat_proof.push_back(-rup.num_clauses);
					grat_proof.push_back(0);

					countermodel_out_var[var] = new_out2;
					
					gvar_definition_conflict_clause.pop_back();
                }
                
                /* add the clauses that short-circuit the RFAO array to the last partial circuit
				 *
				 * for a given var = abs(lit), we have that
				 *   ( "|" is logical or, "{}" designates a falsified literal )
				 *
				 * if lit > 0:
				 *   current_id     : -old_out | new_out
				 *   current_id + 1 : old_out | {-g} | -new_out
				 * if lit < 0:
				 *   current_id     : old_out | -new_out
				 *   current_id + 1 : -old_out | {-g} | new_out
				 *
				 * and regardless (prop_clause[x] propagates 1-x into var)
				 *
				 *           SHOULDN'T THIS BE CHANGED THOUGH?
				 * 
				 * prop_clause[0] = var | -old_out
				 * prop_clause[1] = -var | old_out
				 *
				 * the new prop_clause will be the resolvent of the old prop_clause and the
				 * appropriate definition. This is formalized below.
				 *
				 */
                GRAT_ClauseID running_grat_id = cert.num_clauses + num_cnf_clauses - 3*reduced_simple.size() - 12*reduced_merged.size() + 2;
                for (int32_t lit : reduced_simple) {
                    int32_t var = abs(lit);
                    GRAT_ClauseID delta = (lit > 0);

                    auto prop_clause = prop.find(var);
                    if (prop_clause != prop.end()) {

                        NewVar out_var = countermodel_out_var[var];

                        rup.write_clause<NewLit>({var, -out_var});
                        grat_proof.push_back(3);
                        grat_proof.push_back(-rup.num_clauses);
                        grat_proof.push_back(prop_clause->second[0]);
                        grat_proof.push_back(0);
                        grat_proof.push_back(running_grat_id + delta);
                        prop_clause->second[0] = -rup.num_clauses;

                        rup.write_clause<NewLit>({-var, out_var});
                        grat_proof.push_back(3);
                        grat_proof.push_back(-rup.num_clauses);
                        grat_proof.push_back(prop_clause->second[1]);
                        grat_proof.push_back(0);
                        grat_proof.push_back(running_grat_id + 1 - delta);
                        prop_clause->second[1] = -rup.num_clauses;

                    } else {
                        prop[var] = {{running_grat_id + delta, running_grat_id + 1 - delta}};
                    }
                    running_grat_id += 3;
                }

                running_grat_id = cert.num_clauses + num_cnf_clauses - 12*reduced_merged.size();

				// update prop clauses for reduced merged literals
                for (vector<OldVar>::reverse_iterator rit = reduced_merged.rbegin(); rit != reduced_merged.rend(); rit++) {
                    OldVar var = *rit;
                    auto prop_clause = prop.find(var);

					NewVar out_var = countermodel_out_var[var];

					grat_proof.push_back(1);
					grat_proof.push_back(running_grat_id + 1);
					grat_proof.push_back(running_grat_id + 4);
					grat_proof.push_back(0);

					rup.write_clause<NewLit>({var, -out_var});
					grat_proof.push_back(3);
					grat_proof.push_back(-rup.num_clauses);
					grat_proof.push_back(running_grat_id + 11);
                    if (prop_clause != prop.end()) {
                        grat_proof.push_back(prop_clause->second[0]);
						prop_clause->second[0] = -rup.num_clauses;
					}
					grat_proof.push_back(0);
					grat_proof.push_back(running_grat_id + 9);

					rup.write_clause<NewLit>({-var, out_var});
					grat_proof.push_back(3);
					grat_proof.push_back(-rup.num_clauses);
					grat_proof.push_back(running_grat_id + 12);
                    if (prop_clause != prop.end()) {
						grat_proof.push_back(prop_clause->second[1]);
						prop_clause->second[1] = -rup.num_clauses;
					}
					grat_proof.push_back(0);
					grat_proof.push_back(running_grat_id + 8);

                    running_grat_id += 12;

					if (prop_clause == prop.end()) {
						prop[var] = {{-(rup.num_clauses - 1), -rup.num_clauses}};
					}
                }

                reduced_lits.clear();
                reduced_simple.clear();
                reduced_merged.clear();
                /* if a clause has been replaced by a g variable, mark that it's deletion
                 * information should not be forwarded to the rup proof */
                if (delinfo)
                    no_delete.insert(current_id);
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
                        grat_proof.push_back(1);
                        grat_proof.push_back(get_grat_id[parent_left]);
                        grat_proof.push_back(0);
                        conflict_clause = get_grat_id[parent_right];
                    } else {
						// if there were merged literals, we need to distinguish cases
						// based on the pivot in order to propagate everything
						if (!merged_lits.empty()) {
							rup.ofs << pivot << " "; rup.write_clause(shadcls);

							grat_proof.push_back(3);
							grat_proof.push_back(-rup.num_clauses);
							grat_proof.insert(grat_proof.end(), merge_propagation_sequence_left.begin(), merge_propagation_sequence_left.end());
							grat_proof.push_back(0);
							grat_proof.push_back(get_grat_id[parent_left]);

							rup.write_clause(shadcls);

							grat_proof.push_back(3);
							grat_proof.push_back(-rup.num_clauses);
							grat_proof.push_back(-(rup.num_clauses - 1));
							grat_proof.insert(grat_proof.end(), merge_propagation_sequence_right.begin(), merge_propagation_sequence_right.end());
							grat_proof.push_back(0);
							grat_proof.push_back(get_grat_id[parent_right]);

						} else {
							rup.write_clause(shadcls);

							grat_proof.push_back(3);
							grat_proof.push_back(-rup.num_clauses);
							grat_proof.push_back(get_grat_id[parent_right]);
							grat_proof.push_back(0);
							grat_proof.push_back(get_grat_id[parent_left]);
						}
						get_grat_id[current_id] = -rup.num_clauses;
					}
                } else {
                    get_grat_id[current_id] = get_grat_id[parent_left];
                    if (shadcls.empty()) {
                        conflict_clause = get_grat_id[parent_left];
                    }
                }
                if (shadcls.size() <= delinfo) {
                    no_delete.insert(current_id);
                }
            }
            merged_lits.clear();
            shadcls.clear();
        } else {
            if (primary_type == 0) {
                // initial term, careful, it's already negated
                rup.write_clause(clause);
                get_grat_id[current_id] = -rup.num_clauses;

                grat_proof.push_back(3);
                grat_proof.push_back(-rup.num_clauses);
                memset(initial_term_chi, 0, qbf_num_vars+1);
                for (OldLit lit : clause) {
                    OldVar var = abs(lit);
                    if (lit < 0)
                        initial_term_chi[var] = 1;
                    else
                        initial_term_chi[var] = -1;
                }
                GRAT_ClauseID current_clause = 0;
                for (auto& c : matrix) {
                    size_t current_lit = 1;
                    for (auto lit : c) {
                        if (lit * initial_term_chi[abs(lit)] > 0) {
                            grat_proof.push_back(current_clause + current_lit);
                            break;
                        } else {
                            ++current_lit;
                        }
                    }
                    if (current_lit > c.size()) {
						// TODO: implement some incomplete heuristic in order to attempt to recover the satisfying assignment
                        std::cerr << "WARNING: Non-hitting initial term with the id " << current_id << std::endl; 
                        std::cerr << "FURTHER INFO: " << current_clause << " " << current_lit << std::endl;
                    }
                    current_clause += c.size() + 1;
                }
                grat_proof.push_back(0);
                grat_proof.push_back(num_cnf_clauses);
            } else {
				// input clause
				
				/* TODO: figure out how to test for input clause properly
				 * the problems are:
				 *
				 *   we assume the clauses come in the same order in the QRP as in the QDIMACS
				 */
				
				while (last_orig_clause_seen < matrix.size() && !setequal(clause, matrix[last_orig_clause_seen])) {
					++last_orig_clause_seen;
				}
				++last_orig_clause_seen;

				if (last_orig_clause_seen > matrix.size()) {
					// error, input clause is invalid
					std::cerr << "ERROR: Input clause with the id " << current_id << " does not occur in the matrix" << std::endl;
					return -1;
				}

                get_grat_id[current_id] = last_orig_clause_seen;
                if (clause.empty()) {
                    conflict_clause = last_orig_clause_seen;
                }
            }
            if (clause.size() <= delinfo) {
                no_delete.insert(current_id);
            }
        }

        // clear the phases of reduced literals
        for (OldLit lit : reduced_lits) {
            if (lit > 0) {
                phase.erase({current_id, lit});
            }
        }

        bool deletion_block_is_open = false;
        if (parent_left) {
            unordered_map<QRP_ClauseID, QRP_ClauseID>::iterator it = last_use_of.find(parent_left);
            if (it->second == current_id) {
                last_use_of.erase(it);
                if (delinfo) {
                    if (!no_delete.erase(parent_left)) {
                        //rup << "d "; print_clause(rup, shadow(parent_left));
                        // GRAT deletion instead
                        grat_proof.push_back(2);
                        grat_proof.push_back(get_grat_id[parent_left]);
                        deletion_block_is_open = true;
                    }
                }
                get_grat_id.erase(parent_left);
                clause_database.erase(parent_left);
            }
            if (parent_right) {
                it = last_use_of.find(parent_right);
                if (it->second == current_id) {
                    last_use_of.erase(it);
                    if (delinfo) {
                        if (!no_delete.erase(parent_right)) {
                            //rup << "d "; print_clause(rup, shadow(parent_right));
                            // GRAT deletion instead
                            if (!deletion_block_is_open) {
                                grat_proof.push_back(2);
                            }
                            grat_proof.push_back(get_grat_id[parent_right]);                            
                        }
                    }
                    get_grat_id.erase(parent_right);
                    clause_database.erase(parent_right);
                }
            }
            if (deletion_block_is_open) {
                grat_proof.push_back(0);
            }
        }
        /*if (grat_proof.size() > threshold) {
            std::cerr << "WARNING: GRAT proof now has " << grat_proof.size() << " entries." << std::endl;
            threshold += (threshold) / 3;
        }*/
    }

    delete[] initial_term_chi;
    grat_proof.push_back(5);
    grat_proof.push_back(conflict_clause);
    std::ofstream grat(gratfile, std::ios::binary);
    for (auto rit = grat_proof.rbegin(); rit != grat_proof.rend(); ++rit) {
        if (*rit < 0)
            *rit = num_cnf_clauses + cert.num_clauses - *rit;
        grat.write((char*)&(*rit), 4);
    }
    if (verbose_output) {
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
    grat.close();
    // now encode the countermodels into CNF
    // TODO: implement different types of encoding (quadratic one-sided, multi-gates)
    for (unordered_map<int32_t, vector<RFAO_node>>::iterator it = countermodel.begin(); it != countermodel.end(); it++) {
        int64_t var = it->first;
        vector<RFAO_node>& RFAO_array = it->second;
        //cnf << "RFAO array for " << var << " is: ";
        //print_clause(cnf, RFAO_array);
        // first propagate constants
        vector<RFAO_node>::reverse_iterator rit = RFAO_array.rbegin();
        bool type = rit->term;
        if (rit->var == 0) {
            //std::cerr << "Constant propagation for " << var << " with value " << type << ":";
            do {
                //std::cerr << " (" << rit->var << ", " << rit->term << ")";
                rit++;
            } while (rit != RFAO_array.rend() && type == rit->term); 
            //std::cerr << std::endl;
        }

        if (rit == RFAO_array.rend()) {
            //std::cerr << "Reached the end!" << std::endl;
            cert.write_clause<NewLit>({var * (2*type - 1)});
            continue;
        }

        vector<RFAO_node>::reverse_iterator begin = rit++;
        if (rit == RFAO_array.rend()) {
            cert.define_variable_clause<NewLit>(var, {begin->var});
            continue;
        }
        while (rit != RFAO_array.rend()) {
            type = rit->term;
            do {
                rit++;
            } while (rit != RFAO_array.rend() && rit->term == type);
            int64_t out_var = var;
            if (rit != RFAO_array.rend()) {
                out_var = get_fresh_variable();
            }
            if (type == 0) {
                cert.define_variable_term<RFAO_node>(out_var, begin, rit);
            } else {
                cert.define_variable_clause<RFAO_node>(out_var, begin, rit);
            }
            begin = rit - 1;
            *begin = out_var;
        }
    }
    countermodel.clear();

    // seek to the beginning of cnf and update the problem line
    cert.ofs.seekp(6);
    cert.ofs << std::setw(41) << std::left << std::to_string(max_var) + " " + std::to_string(cert.num_clauses) << "\n";
    //std::cerr << "Reductions: " << num_reductions << "\nMerges: " << num_merges << std::endl;
    cert.ofs.close();
    rup.ofs.close();
    combine(qdimacs, qrpfile + ".cert", qrpfile + ".cnf");
    std::cout << "OK" << std::endl;
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
int32_t ProofTranslator::check_resolution(vector<OldLit>& c1, vector<OldLit>& c2, vector<OldLit>& resolvent, vector<OldLit>& merged_lits, vector<OldLit>& reduced_lits) {
    int32_t pivot = 0;
    uint32_t max_primary_depth = 0;
    for (int32_t lit : resolvent) {
        int32_t var = abs(lit);
        if (var_data[var].type == primary_type && var_data[var].depth > max_primary_depth) {
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
        bool is_primary = (var_data[var].type == primary_type);
        if (oracle_c2.has(-lit)) {
            if (is_primary) {
                if (pivot != 0 && lit != pivot) {
                    std::cerr << lit << ": duplicate pivot\n";
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
                    if (verbose_output)
                        std::cout << lit << " is merged!\n";
                }
            }
        }
        if (!oracle_res.has(lit)) {
            if (is_primary) {
                if (lit != pivot) {
                    std::cerr << lit << ": primary reduction in c1\n";
                    return 0;
                }
            } else {
                if (var_data[var].depth <= max_primary_depth) {
                    std::cerr << lit << ": non-tailing reduction in c1\n";
                    return 0;
                }
                reduced_lits.push_back(lit);
            }
        }
    }

    if (pivot == 0) {
        std::cerr << "no pivot\n";
        return 0;
    }
    if (min_merged_depth < var_data[abs(pivot)].depth) {
        std::cerr << "illegal merge\n";
        return 0;
    }
	if (verbose_output && !merged_lits.empty())
		std::cerr << "pivot for these merges: " << pivot << std::endl;

    /* Since reduced_lits was populated in sorted order, we can use has_literal on it,
     * to determine if a given literal was already collected for reduction if it's
     * contained in both c1 and c2. */
    SortedQueryOracle oracle_reduced(reduced_lits, compare_lits_weak);
    oracle_res.rewind();
    //print_clause(std::cerr, reduced_lits);
    for (int32_t lit: c2) {
        if (!oracle_reduced.has(lit)) {
            //std::cerr << "reduced_lits does not have " << lit << std::endl;
            if (!oracle_res.has(lit)) {
                //std::cerr << "resolvent does not have " << lit << std::endl;
                int32_t var = abs(lit);
                if (var_data[var].type == primary_type) {
                    if (lit != -pivot) {
                        std::cerr << lit << ": primary reduction in c2\n";
                        return 0;
                    }
                } else {
                    if (var_data[var].depth < max_primary_depth) {
                        std::cerr << lit << ": non-tailing reduction in c2\n";
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
            std::cerr << "introduction of literals into resolvent\n";
            return 0;
        }
    }
    return pivot;
}

/* Check that the given reduction step is sound, returns 1 on success, otherwise
 * the following error codes:
 *   0: reduction on primary literal
 *  -1: reduction on non-tailing secondary literal
 *  -2: introduction of literal not from premise
 */
int32_t ProofTranslator::check_reduction(vector<OldLit>& premise, vector<OldLit>& conclusion, vector<OldLit>& reduced_lits) {
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
    if (verbose_output) {
        std::cout << "Shadow clause for step " << id << ":";
    }
    vector<int64_t> shadcls;
    for (int32_t lit : clause_database[id]) {
        int64_t ef_lit = get_eflit(lit, get_phase(id, lit));
        if (ef_lit == lit || lit > 0) {
            shadcls.push_back(ef_lit);
            if (verbose_output) {
				std::cout << " " << ef_lit << "(" << lit << ")";
            }
        }
    }
    if (verbose_output)
        std::cout << std::endl;
    return shadcls;
}






// #################################
// PHASE FUNCTIONS AND CO
// #################################

NewVar ProofTranslator::get_phase(QRP_ClauseID id, OldLit lit) {
    unordered_map<ClauseVarPair, int64_t>::iterator it = phase.find({id, abs(lit)});
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

/* NewVar ProofTranslator::update_phase_old(OldLit pivot, NewVar phase_left, NewVar phase_right) {
	// pivot is the literal as it appears in the left parent
    // always phase_left != phase_right
    int64_t phi = get_fresh_variable();
	phase_def[phi] = cert.num_clauses + 1;
    if (phase_left == 0) {
        if (phase_right == 1) {
            if (abs(pivot) == 1) {
                cert.define_variable_clause<OldLit>(phi, {pivot});
            } else {
                discard_last_variable();
				phase_def.erase(phi);
                phi = pivot;
            }
        } else {
            cert.define_variable_term<NewLit>(phi, {pivot, phase_right});
        }
    } else if (phase_left == 1) {
        if (phase_right == 0) {
            if (abs(pivot) == 1) {
                cert.define_variable_clause<OldLit>(phi, {-pivot});
            } else {
                discard_last_variable();
				phase_def.erase(phi);
                phi = -pivot;
            }
        } else {
            cert.define_variable_clause<NewLit>(phi, {-pivot, phase_right});
        }
    } else {
        if (phase_right == 0) {
            cert.define_variable_term<NewLit>(phi, {-pivot, phase_left});
        } else if (phase_right == 1) {
            cert.define_variable_clause<NewLit>(phi, {pivot, phase_left});
        } else {
			cert.write_clause<NewLit>({ pivot, -phase_left ,  phi});
			cert.write_clause<NewLit>({ pivot,  phase_left , -phi});
			cert.write_clause<NewLit>({-pivot, -phase_right,  phi});
			cert.write_clause<NewLit>({-pivot,  phase_right, -phi});
        }
    }
    phase_cache.insert({{pivot, phase_left, phase_right}, phi});
    return phi;
} */

NewVar ProofTranslator::update_phase(OldLit pivot, NewVar phase_left, NewVar phase_right) {
	// pivot is the literal as it appears in the left parent
    // always phase_left != phase_right
    int64_t phi = get_fresh_variable();
	phase_def[{pivot, phi}] = num_cnf_clauses + cert.num_clauses + 1;
	phase_def[{-pivot, phi}] = num_cnf_clauses + cert.num_clauses + 3;
	cert.write_clause<NewLit>({ pivot, -phase_left ,  phi});
	cert.write_clause<NewLit>({ pivot,  phase_left , -phi});
	cert.write_clause<NewLit>({-pivot, -phase_right,  phi});
	cert.write_clause<NewLit>({-pivot,  phase_right, -phi});
    phase_cache.insert({{pivot, phase_left, phase_right}, phi});
	/* if (phase_left == -phase_right) {
		phase_cache.insert({{-pivot, phase_left, phase_right}, -phi});
	} */
    return phi;
}

NewVar ProofTranslator::make_eflit(OldVar var, NewVar phase_var) {
    int64_t new_eflit = get_fresh_variable();
	eflit_def[new_eflit] = num_cnf_clauses + cert.num_clauses + 1;
	cert.write_clause<NewLit>({-new_eflit, -var,  phase_var});
	cert.write_clause<NewLit>({-new_eflit,  var, -phase_var});
	cert.write_clause<NewLit>({ new_eflit,  var,  phase_var});
	cert.write_clause<NewLit>({ new_eflit, -var, -phase_var});
    return new_eflit;
}

/* Each temporary countermodel circuit stores circuit nodes connected by the same connective
 * and the Tseitin variable to describe the temporary circuit. */

void ProofTranslator::push_to_array(OldVar var, NewVar entry, bool term) {
    unordered_map<int32_t, vector<RFAO_node>>::iterator it = countermodel.find(var);
    if (verbose_output)
        std::cerr << "Pushing (" << entry << "," << term << ") to the RFAO array of " << var << std::endl;
    if (it != countermodel.end()) {
        it->second.push_back({entry, term});
    } else {
        countermodel.insert({var, {{entry, term}}});
    }
}

void ProofTranslator::push_to_array(OldVar var, NewLit entry) {
    unordered_map<OldVar, vector<RFAO_node>>::iterator it = countermodel.find(var);
    if (verbose_output)
        std::cerr << "Pushing " << entry << " to the RFAO array of " << var << std::endl;
    if (it != countermodel.end()) {
        it->second.push_back(entry);
    } else {
        countermodel.insert({var, {entry}});
    }
}

/*
inline int signum(int64_t x) {return (0 < x) - (x < 0);}
uint64_t push_to_array(int32_t var, int64_t entry) {
    unordered_map<int32_t, Circuit>::iterator it = countermodel.find(var);
    if (it != countermodel.end()) {
        vector<int64_t>& RFAO_array = it->second.RFAO_array;
        int sgn = signum(RFAO_array[0]);
        if (sgn == signum(RFAO_array.back())) {
            RFAO_array.push_back(entry);
            return 0;
        } else {
            int64_t fresh_var = get_fresh_variable();
            uint64_t num_clauses;
            int64_t tmp = RFAO_array.back();
            if (sgn == 1) {
                RFAO_array.back() = -fresh_var;
                num_clauses = define_variable_term(cnf, it->second.out_var, RFAO_array);
                it->second.out_var = -fresh_var;
            } else {
                RFAO_array.back() = fresh_var;
                num_clauses = define_variable_clause(cnf, it->second.out_var, RFAO_array);
                it->second.out_var = fresh_var;
            }
            RFAO_array = {tmp, entry};
            return num_clauses;
        }
    } else {
        countermodel.insert({var, {var, {entry}}});
        return 0;
    }
}
*/

// #################
//        IO
// #################

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

vector<OldLit>& ProofTranslator::read_proof_line(const char * line, QRP_ClauseID& id, QRP_ClauseID& p1, QRP_ClauseID& p2) {
    char * tmp;
    id = strtoul(line, &tmp, 10);
    clause_database[id] = {};
    vector<int32_t>& clause = clause_database[id];
    int32_t lit;
    while ((lit = strtol(tmp, &tmp, 10)) != 0) {
        clause.push_back(lit);
    }
    p1 = strtoul(tmp, &tmp, 10);
    if (p1)
        p2 = strtoul(tmp, &tmp, 10);
    return clause;
}

void ProofTranslator::combine(string qdimacs, string certificate, string combined) {
    ifstream qbf(qdimacs);
    ifstream cert(certificate);
    ClauseWriter comb(combined);

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
                int32_t c = get_fresh_variable();
                comb.define_variable_clause(c, clause);
                top_level_clause.push_back(-c);
                clause.clear();
            } else {
                comb.ofs << line << "\n";
                num_clauses++;
            }
        }
    } while (std::getline(qbf, line));

    if (primary_type == 0) {
        comb.write_clause(top_level_clause);
    }

    while (std::getline(cert, line)) {
        comb.ofs << line << "\n";
    }

    comb.ofs.seekp(6);
    comb.ofs << std::setw(41) << std::left << std::to_string(max_var) + " " + std::to_string(num_clauses + comb.num_clauses) << "\n";

}

