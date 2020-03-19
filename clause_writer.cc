#include "clause_writer.hh"

template<typename T>
void ClauseWriter::write_clause(const std::vector<T>& clause) {
    for (T lit : clause) {
        ofs << lit << " ";
    }
    ofs << "0\n";
    ++num_clauses;
}

template void ClauseWriter::write_clause<OldLit>(const vector<OldLit>& clause);
// must be uncommented when NewLit becomes different from OldLit
//template void ClauseWriter::write_clause<NewLit>(const vector<NewLit>& clause);

/*
template <typename T>
void ClauseWriter::define_variable_clause(NewVar new_var, typename std::vector<T>::const_iterator begin, typename std::vector<T>::const_iterator end) {
    for (typename std::vector<T>::const_iterator it = begin; it != end; it++) {
        ofs << -*it << " " << new_var << " 0\n";
    }
    for (typename std::vector<T>::const_iterator it = begin; it != end; it++) {
        ofs << *it << " ";
    }
    ofs << -new_var << " 0\n";

    num_clauses += end - begin + 1;
}

template <typename T>
void ClauseWriter::define_variable_term(NewVar new_var, typename std::vector<T>::const_iterator begin, typename std::vector<T>::const_iterator end) {
    for (typename std::vector<T>::const_iterator it = begin; it != end; it++) {
        ofs << *it << " " << -new_var << " 0\n";
    }
    for (typename std::vector<T>::const_iterator it = begin; it != end; it++) {
        ofs << -*it << " ";
    }
    ofs << new_var << " 0\n";

    num_clauses += end - begin + 1;
}

template <typename T>
void ClauseWriter::define_variable_clause(NewVar new_var, typename std::vector<T>::const_reverse_iterator begin, typename std::vector<T>::const_reverse_iterator end) {
    for (typename std::vector<T>::const_reverse_iterator it = begin; it != end; it++) {
        ofs << -*it << " " << new_var << " 0\n";
    }
    for (typename std::vector<T>::const_reverse_iterator it = begin; it != end; it++) {
        ofs << *it << " ";
    }
    ofs << -new_var << " 0\n";

    num_clauses += end - begin + 1;
}

template <typename T>
void ClauseWriter::define_variable_term(NewVar new_var, typename std::vector<T>::const_reverse_iterator begin, typename std::vector<T>::const_reverse_iterator end) {
    for (typename std::vector<T>::const_reverse_iterator it = begin; it != end; it++) {
        ofs << *it << " " << -new_var << " 0\n";
    }
    for (typename std::vector<T>::const_reverse_iterator it = begin; it != end; it++) {
        ofs << -*it << " ";
    }
    ofs << new_var << " 0\n";

    num_clauses += end - begin + 1;
}

template <typename T>
void ClauseWriter::define_variable_clause(NewVar new_var, const std::vector<T>& clause) {
    define_variable_clause<T>(new_var, clause.cbegin(), clause.cend());
}

template <typename T>
void ClauseWriter::define_variable_term(NewVar new_var, const std::vector<T>& term) {
    define_variable_term<T>(new_var, term.cbegin(), term.cend());
}

// template functions need to be either defined in the header, or at least declared with concrete types


template void ClauseWriter::define_variable_clause<OldLit>(NewVar new_var, typename vector<OldLit>::const_iterator begin, typename vector<OldLit>::const_iterator end);
template void ClauseWriter::define_variable_term  <OldLit>(NewVar new_var, typename vector<OldLit>::const_iterator begin, typename vector<OldLit>::const_iterator end);
template void ClauseWriter::define_variable_clause<OldLit>(NewVar new_var, typename vector<OldLit>::const_reverse_iterator begin, typename vector<OldLit>::const_reverse_iterator end);
template void ClauseWriter::define_variable_term  <OldLit>(NewVar new_var, typename vector<OldLit>::const_reverse_iterator begin, typename vector<OldLit>::const_reverse_iterator end);
template void ClauseWriter::define_variable_clause<OldLit>(NewVar new_var, const std::vector<OldLit>& clause);
template void ClauseWriter::define_variable_term  <OldLit>(NewVar new_var, const std::vector<OldLit>& clause);

template void ClauseWriter::define_variable_clause<NewLit>(NewVar new_var, typename vector<NewLit>::const_iterator begin, typename vector<NewLit>::const_iterator end);
template void ClauseWriter::define_variable_term  <NewLit>(NewVar new_var, typename vector<NewLit>::const_iterator begin, typename vector<NewLit>::const_iterator end);
template void ClauseWriter::define_variable_clause<NewLit>(NewVar new_var, typename vector<NewLit>::const_reverse_iterator begin, typename vector<NewLit>::const_reverse_iterator end);
template void ClauseWriter::define_variable_term  <NewLit>(NewVar new_var, typename vector<NewLit>::const_reverse_iterator begin, typename vector<NewLit>::const_reverse_iterator end);
template void ClauseWriter::define_variable_clause<NewLit>(NewVar new_var, const std::vector<NewLit>& clause);
template void ClauseWriter::define_variable_term  <NewLit>(NewVar new_var, const std::vector<NewLit>& clause);
*/
