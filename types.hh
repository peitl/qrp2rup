#ifndef _TYPES_H_
#define _TYPES_H_

#include <cstdint>
#include <functional> // std::hash

/* there are only a few old variables, so it is OK to use a 32-bit integer for them,
 * but just to stay on the safe side, we have a separate type for newly created variables
 * and that is currently set to a 64-bit integer.
 *
 * Actually, no. */

typedef int32_t Var;
typedef int32_t Lit;
typedef Var OldVar;
typedef Lit OldLit;
typedef Var NewVar;
typedef Lit NewLit;

typedef uint32_t QRP_ClauseID;
typedef int32_t GRAT_ClauseID;

typedef int32_t ClauseCNT;

struct qdata {
    uint32_t depth:31; // the leftmost quantifier block has depth == 1
    uint8_t type:1; // type == 1 means the variable is existential (type == 0 is universal)
};

/* auxiliary tuple structures for tuples of objects which are used to retrieve
 * phase function variables, effective literals, and to cache phase function definitions */

// a pair of clause and variable serves as a key to retrieve the phase of the variable in the clause
struct ClauseVarPair {
    QRP_ClauseID id;
    OldVar var;
    bool operator== (const ClauseVarPair& other) const { return id == other.id && var == other.var; }
};

// a pair of variable and phase serves as a key to retrieve the effective literal of that variable under that phase
struct VarPhasePair {
    OldVar var;
    NewVar phase;
    bool operator== (const VarPhasePair& other) const { return var == other.var && phase == other.phase; }
};

// a triple of pivot and two phases serves as a key to retrieve the phase that results from the respective merge
struct PivotPhasesTuple {
    OldVar pivot;
    NewVar phase_left;
    NewVar phase_right;
    /* Equality is tricky here, because we want (p, phl, phr) == (-p, phr, phl),
     * because those are symmetric cases and the new phase variable is the same */
    bool operator== (const PivotPhasesTuple& other) const {
		return (pivot ==  other.pivot && phase_left == other.phase_left  && phase_right == other.phase_right)
			|| (pivot == -other.pivot && phase_left == other.phase_right && phase_right == other.phase_left);
	}
};

struct PivotPhasePair {
	OldLit pivot;
	NewVar phase;
    bool operator== (const PivotPhasePair& other) const { return pivot == other.pivot && phase == other.phase; }
};

struct PivotEflitPair {
	OldLit pivot;
	NewVar eflit;
    bool operator== (const PivotEflitPair& other) const { return pivot == other.pivot && eflit == other.eflit; }
};


namespace std {
    template<> struct hash<ClauseVarPair> {
        size_t operator() (const ClauseVarPair& X) const {
            return 77999 * hash<QRP_ClauseID>{}(X.id) + hash<OldVar>{}(X.var);
        }
    };
    template<> struct hash<VarPhasePair> {
        size_t operator() (const VarPhasePair& X) const {
            return 77999 * hash<OldVar>{}(X.var) + hash<NewVar>{}(X.phase);
        }
    };
    template<> struct hash<PivotPhasesTuple> {
        // the hash must be equal for (x,y,z) and (-x,z,y)
        size_t operator() (const PivotPhasesTuple& X) const {
            int64_t p = X.pivot, phl = X.phase_left, phr = X.phase_right;
            return hash<int64_t>{}(3*p*(phl - phr) + phl + phr);
        }
    };
    template<> struct hash<PivotEflitPair> {
        size_t operator() (const PivotEflitPair& X) const {
            return 77999 * hash<OldVar>{}(X.pivot) + hash<NewVar>{}(X.eflit);
        }
    };
    template<> struct hash<PivotPhasePair> {
        size_t operator() (const PivotPhasePair& X) const {
            return 77999 * hash<OldVar>{}(X.pivot) + hash<NewVar>{}(X.phase);
        }
    };
}

#endif
