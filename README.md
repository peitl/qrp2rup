# qrp2rup

QRP2RUP is a proof checker and strategy extractor for long-distance Q-resolution proofs of both true and false quantified Boolean formulas.
It implements the algorithm described by Balabanov, Janota, Jiang, and Widl in their [AAAI'15 paper](https://ojs.aaai.org/index.php/AAAI/article/view/9750).
The program works with proofs in the [QRP](https://fmv.jku.at/qbfcert/qrp.format) format, as well as in a compact QRP-style format emitted by the QBF solver [Qute](https://github.com/fslivovsky/qute).

A distinctive feature of QRP2RUP is the ability to produce DRUP proofs certifying validity of the extracted strategies for the original formula, as described in [our SAT'18 paper](https://link.springer.com/chapter/10.1007/978-3-319-94144-8_16).

Compared to what is described in the SAT'18 paper, QRP2RUP can now also automatically produce a GRAT elaborated version of the DRUP proof of strategy soundness, checkable by the formally verified checker `gratchk` from the [GRAT package](https://www21.in.tum.de/~lammich/grat/).
In the course of the GRAT implementation, I discovered that the originally extracted DRUP proof was not optimal and improved the propagation properties (which are captured explicitly in the GRAT proof hint).
This development and the GRAT capability are not described in any published paper at the moment of writing (late 2025).

## Requirements

[CMake](https://cmake.org/) version >= 3.10 and a C++-14 compiler.

## Install

Run the usual CMake sequence. 

```bash
cmake -Bbuild
cmake --build build
```

## Usage

Check a proof with `./qrp2rup <qrpfile>`.
Optionally specify a QDIMACS file with `./qrp2rup <qrpfile> <qdimacs>`.
`qrp2rup` checks the correctness of the proof and automatically extracts a winning strategy in CNF format to `<qrpfile>.cert`, combines it with the original QDIMACS if given into `<qrpfile>.cnf`, writes a DRUP proof of unsatisfiability of the combined file (strategy plugged into the original QDIMACS formula) into `<qrpfile>.rup`, and writes GRAT annotations that allow checking with `gratchk` into `<qrpfile>.grat`.

## Limitations and Roadmap

At the moment `qrp2rup`

- cannot extract the strategy in a different format than CNF 
- always generates the DRUP+GRAT proof (neither can be skipped)
- has limited capabilities for core extraction
- has limited support for enumeration proofs (should be able to handle proofs emitted by `qute --enumerate`, but support is experimental)

## Troubleshooting

Reach out to me at `peitl@ac.tuwien.ac.at`.
