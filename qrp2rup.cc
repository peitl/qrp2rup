#include <iostream>
//#include <iomanip>
#include <cmath>
#include <algorithm>

#include <stdlib.h>
#include <string.h>

#include "proof_translator.hh"

#include <ctime>

using std::string;

bool has_unit_conclusion = false;
bool has_empty_conclusion = false;

int main(int argc, char** argv) {
    string qrpfile = "";// argv[1];
    string qdimacs = "";// argv[2];
    /* Print deletion information for clauses of size at least delinfo.
     * A value of 0 indicates to print no deletion information at all.
     * 
     * Actually, for gratchk, we always want deletion information! */
    //uint32_t delinfo = 0;
	bool verbose_output = false;

    for (int i = 1; i < argc; i++) {
        /*if (strcmp(argv[i], "-d") == 0) {
            ++i;
            if (i == argc) {
                std::cerr << "Expected a positive integer to follow '-d'" << std::endl;
                return -1;
            }
            delinfo = strtoul(argv[i], nullptr, 10);
        } else*/ if (strcmp(argv[i], "-v") == 0) {
            verbose_output = true;
        } else if (qrpfile.length() == 0) {
            qrpfile = argv[i];
        } else {
            qdimacs = argv[i];
        }
    }

    if (qrpfile.length() == 0 || qdimacs.length() == 0) {
        std::cout << "Please, specify a QRP and a QDIMACS file to work with." << std::endl;
        return 1;
    }

    //delinfo = 1;

	ProofTranslator pt(qrpfile, qdimacs, verbose_output);
	pt.translate();
}
