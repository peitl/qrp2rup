#ifndef _RFAO_NODE_H_
#define _RFAO_NODE_H_

#include "types.hh"

struct RFAO_node {
    NewLit var:63;
    bool term:1;
    RFAO_node (int64_t var): var(var), term(var<0) {}
    RFAO_node (int64_t var, bool term): var(var), term(term) {}
    NewLit operator-() const {return -this->var;}
};

inline std::ostream& operator<< (std::ostream& out, const RFAO_node& node) {
    return out << node.var;
}

#endif
