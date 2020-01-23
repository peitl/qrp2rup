#ifndef _CLAUSE_WRITER_H_
#define _CLAUSE_WRITER_H_

#include <iostream>
#include <fstream>
#include <vector>
#include <string>

#include "types.hh"

using std::vector;
using std::ofstream;
using std::string;

class ClauseWriter {
	public:
	ofstream ofs; // clauses written to this file output stream
	ClauseCNT num_clauses; // total number of clauses written by this writer

	ClauseWriter(const string& filename) : ofs(ofstream(filename)), num_clauses(0) {}

	template <typename T> void write_clause(const vector<T>& clause);

	/* Several variants of the following functionality:
	 * Define a new variable as equivalent to a given clause or term by printing the required Tseitin clauses into the output stream.
	 * Records the number of clauses created. */
	template <typename T> void define_variable_clause(NewVar new_var, typename vector<T>::const_iterator begin, typename vector<T>::const_iterator end);
	template <typename T> void define_variable_term  (NewVar new_var, typename vector<T>::const_iterator begin, typename vector<T>::const_iterator end);
	template <typename T> void define_variable_clause(NewVar new_var, typename vector<T>::const_reverse_iterator begin, typename vector<T>::const_reverse_iterator end);
	template <typename T> void define_variable_term  (NewVar new_var, typename vector<T>::const_reverse_iterator begin, typename vector<T>::const_reverse_iterator end);
	template <typename T> void define_variable_clause(NewVar new_var, const std::vector<T>& clause);
	template <typename T> void define_variable_term  (NewVar new_var, const std::vector<T>& clause);
};

#endif
