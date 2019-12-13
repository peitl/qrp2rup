#ifndef _SORTED_QUERY_ORACLE_H_
#define _SORTED_QUERY_ORACLE_H_

#include "types.hh"

#include <vector>
#include <algorithm>

using std::vector;


/* This function defines a partial ordering on literals.
 * Other orderings can be used assuming that the property
 * that in any linear extension all literals on any given
 * variable form an interval holds. */
inline bool compare_lits_weak(OldLit x, OldLit y) {
    return abs(y) - abs(x) > 0;
}

inline bool compare_lits(OldLit x, OldLit y) {
    return abs(x) < abs(y) || (abs(x) == abs(y) && x < y) ;
}

// assumes both vectors are sorted
inline bool setequal(const vector<OldLit>& c1, const vector<OldLit>& c2) {
	if (c1.size() != c2.size())
		return false;
	for (size_t i = 0; i < c1.size(); ++i)
		if (c1[i] != c2[i])
			return false;
	return true;
}

// assumes clause is sorted by compare_lits
inline bool has_literal(vector<int32_t>& clause, int32_t literal) {
    std::vector<int32_t>::iterator it = std::lower_bound(clause.begin(), clause.end(), literal, compare_lits);
    while (it != clause.end() && !compare_lits(literal, *it)) {
        if (literal == *it)
            return true;
        it++;
    }
    return false;
}

// assumes clause is sorted by compare_lits
inline bool has_literal(std::vector<int32_t>::iterator begin, std::vector<int32_t>::iterator end, int32_t literal) {
    std::vector<int32_t>::iterator it = std::lower_bound(begin, end, literal, compare_lits);
    while (it != end && !compare_lits(literal, *it)) {
        if (literal == *it)
            return true;
        it++;
    }
    return false;
}

class SortedQueryOracle {
    // data has to be sorted by less, otherwise doesn't work
    // moreover, queries must come in sorted order
    std::vector<int32_t>& data;
    size_t next, end;
    bool (*less) (int32_t, int32_t);

    public:
    SortedQueryOracle (std::vector<int32_t>& data, bool (*less) (int32_t, int32_t)) : data(data), next(0), end(data.size()), less(less) {}

    inline bool done() {
        return next == end;
    }

    bool has(int32_t query) {
        while (!done() && less(data[next], query)) {
            next++;
        }
        size_t tmp = next;
        while (tmp != end && !less(query, data[tmp])) {
            if (data[tmp] == query)
                return true;
            tmp++;
        }
        /*if (tmp != end)
            std::cerr << "witness of not having " << query << " is " << data[tmp] << std::endl;
        else
            std::cerr << "witness of not having " << query << " is end\n";*/
        return false;
    }

    inline void rewind() {
        next = 0;
    }
};

#endif
