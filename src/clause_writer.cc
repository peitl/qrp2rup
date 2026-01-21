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
