# qrp2rup

`qrp2rup is a proof checker and strategy extractor for long-distance Q-resolution.

## Install

Run

```
cmake -Bbuild
cmake --build build
```

## Usage

Check a QRP proof with `./qrp2rup <qrpfile>`.
Optionally specify a QDIMACS file with `./qrp2rup <qrpfile> <qdimacs>`.
`qrp2rup` checks the correctness of the proof and automatically extracts a winning strategy in CNF format to `<qrpfile>.cert`, combines it with the original QDIMACS if given into `<qrpfile>.cnf`, writes a DRUP proof of unsatisfiability of the combined file (strategy plugged into the original QDIMACS formula) into `<qrpfile>.rup`, and writes GRAT annotations that allow checking with `gratchk` into `<qrpfile>.grat`.

## Limitations and Roadmap

At the moment `qrp2rup`

- cannot extract the strategy in a different format than CNF 
- always generates the DRUP+GRAT proof (cannot be skipped)
- has limited capabilities for core extraction
- has limited support for enumeration proofs
- 
