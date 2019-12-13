#ifndef _MEMORY_UNSIGNED_INT_H_
#define _MEMORY_UNSIGNED_INT_H_

#include <cstdint>
#include <iostream>

struct MemoryUnsignedInt {
    uint64_t data;
    std::ostream& out;
    MemoryUnsignedInt(uint64_t data, std::ostream& out) : data(data), out(out) {}
    void operator+= (uint64_t other) {
        out << other << "\n";
        data += other;
    }
};

std::string to_string(MemoryUnsignedInt& mui) {
    return std::to_string(mui.data);
}

std::string to_string(uint64_t mui) {
    return std::to_string(mui);
}

#endif
