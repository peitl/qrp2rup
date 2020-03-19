#include <iostream>
#include <fstream>
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

int increase_verbosity_from_param(char * param) {
	size_t length = strlen(param);
	if (length < 2 || param[0] != '-') {
		return 0;
	}
	for (size_t i = 1; i < length; ++i) {
		if (param[i] != 'v') {
			return 0;
		}
	}
	return length - 1;
}

const string HELP_MESSAGE =
"USAGE: qrp2rup [-v[v[v]]] [-q] [--core] qdimacs [qrp]\n\
		\n\
		-v       increases verbosity\n\
		-q       turns off all output\n\
		--core   extracts the core proof into <qrp>.core\n\
		\n\
		if no qrp file is given, it is assumed that qrp=<qdimacs>.qrp\
"
;

int main(int argc, char** argv) {
    string qrpfile = "";// argv[1];
    string qdimacs = "";// argv[2];
    /* Print deletion information for clauses of size at least delinfo.
     * A value of 0 indicates to print no deletion information at all.
     * 
     * Actually, for gratchk, we always want deletion information! */
    //uint32_t delinfo = 0;
	int verbosity = 0;
	bool extract_core = false;

    for (int i = 1; i < argc; i++) {
        /*if (strcmp(argv[i], "-d") == 0) {
            ++i;
            if (i == argc) {
                std::cerr << "Expected a positive integer to follow '-d'" << std::endl;
                return -1;
            }
            delinfo = strtoul(argv[i], nullptr, 10);
        } else*/

		int verbosity_increase = increase_verbosity_from_param(argv[i]);
		if (verbosity_increase > 0) {
			verbosity += verbosity_increase;
		} else if (strcmp(argv[i], "-h") == 0) {
			std::cout << HELP_MESSAGE << std::endl;
			exit(0);
		} else if (strcmp(argv[i], "-q") == 0) {
            verbosity = -1;
		} else if (strcmp(argv[i], "--core") == 0) {
            extract_core = true;
		} else if (strlen(argv[i]) == 0) {
			std::cout << "qrp2rup WARNING: Skipping empty argument at possition " << i << std::endl;
			continue;
        } else if (argv[i][0] == '-') {
			std::cout << "qrp2rup ERROR: Unknown option " << string(argv[i]) << std::endl;
			std::cout << HELP_MESSAGE << std::endl;
			exit(1);
        } else if (qdimacs.length() == 0) {
            qdimacs = argv[i];
        } else {
            qrpfile = argv[i];
        }
    }

	if (qdimacs.length() == 0) {
        std::cout << "qrp2rup ERROR: Please, specify a QDIMACS and optionally a proof file to work with." << std::endl;
		exit(1);
	}

	if (!std::ifstream(qdimacs).good()) {
		std::cout << "qrp2rup ERROR: Unable to access file " << qdimacs << std::endl;
		std::cout << HELP_MESSAGE << std::endl;
		exit(1);
	}

	if (qrpfile.length() == 0) {
		qrpfile = qdimacs + ".qrp";
	}
	
	if (!std::ifstream(qrpfile).good()) {
		std::cout << "qrp2rup ERROR: Unable to access file " << qrpfile << std::endl;
		std::cout << HELP_MESSAGE << std::endl;
		exit(1);
	}


    //delinfo = 1;

	ProofTranslator pt(qrpfile, qdimacs, verbosity, extract_core);
	pt.translate();
}
