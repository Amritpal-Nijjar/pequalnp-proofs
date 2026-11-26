# L-meta-18096 fourth verification round

Lean rules out every way to finish a ten-gate circuit with the internal NOT at gate 8 once the following three gates are fixed. The seven remaining gates, including their operand choices, are free. Gate positions here start at 1, while wires start at 0.

1. Wire 5 is the AND of inputs 1 and 2.
2. Wire 6 is the OR of inputs 1 and 2.
3. Wire 7 is the OR of inputs 0 and 4.

`FiveFixed3.exclusion` in `ThreeCoverage.lean` lifts the finite calculation to the physical circuit, with the target truth table `0xfee8eaa8`. The proof first assigns each of the 16 possible four-bit selector patterns and each of the two output operations to a checked case. The 16 selector patterns represent seven different outer wires because the projected model sends every out-of-range selector to its first internal wire. One particularly large case is further divided according to whether the gate on wire 11 is AND or OR. The resulting fifteen cases are exhaustive. Each can be replayed independently.

The fifteen subproofs use 13,166,758 bytes of text LRAT. The physical theorem depends on `propext`, `Classical.choice` and `Quot.sound`.

## Wider one-fixed-gate work

With only the first AND of inputs 1 and 2 fixed and the NOT still at gate 8, Lean checked 6 of 14 projected outer-wire and output-operation choices. The remaining projected pairs are wire 8 with AND, wire 8 with OR, wire 9 with AND, wire 9 with OR, wire 10 with AND, wire 10 with OR, wire 11 with AND, wire 11 with OR. Independent SAT searches returned UNSAT on all fourteen branches. Unreplayed branches are computational evidence.

The theorem `FiveOne.at_least_wire_eight` rules out all six cases using wires 5, 6 or 7 as the outer operand for either output operation. It combines the coordinator’s extremal-row constraint with independently checked prefixes.

For an outer operand on wire 8, `FiveOne.DirectCatalog.physical_wire_eight` restricts its 32-bit truth table to five possible values when the output is AND, and two when it is OR. The kernel checked a direct enumeration in 31 pieces. All later gate choices are covered.

| Final gate | Allowed truth tables on wire 8 |
| --- | --- |
| AND | `0xfefcfefc`, `0xffeaffaa`, `0xffecffec`, `0xfff8fff8`, `0xffffeaaa` |
| OR | `0xaaa8aaa8`, `0xc0c0c080` |

`FiveOne.DirectCatalog.wire_eight_witness` provides the actual output pin and proves the table restriction when that pin selects wire 8.

The assembled physical proof and a separate large branch were checked again from saved sources and certificate text with certificate generation disabled.

The source also includes a kernel replay that shares proved intermediate RUP clauses as ordinary Lean theorems. It was validated independently on the six-fixed-gate control.

These results concern a restricted gate position and first-gate family. The original desk statement still needs a complete proof or refutation.

## Reproduction

Extract the archive. From the PEqualNP Lean project with its dependencies installed, run `lake env python /absolute/path/to/replay.py`. The runner uses a temporary build directory and the included certificates. All numerical rows, proof sources, module order, SHA-256 hashes for the traces, and captured axiom declarations are included. Lean 4.36.0 was used for the verified run. The counting and lower-bound foundation is credited to pjscruggs and the project in its original sources. The Boolean reifier builds on Sarvesh Kapre’s kernel replay code.
