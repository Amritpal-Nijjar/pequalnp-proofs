# L-meta-18096 five-input circuit research

Lean rules out all ways to complete the last 6 gates once the first 4 gates of the control below are fixed and the single internal NOT is gate 8. Gate positions in this sentence start at 1. The claim concerns target table `0xfee8eaa8`. The full seven-position exclusion still needs a kernel proof.

The control uses the first gates of this list in order. Wires 0 through 4 are inputs and wire 5 is the first gate output.

1. AND of wires 1 and 2
2. OR of wires 1 and 2
3. OR of wires 0 and 4
4. AND of wires 6 and 7
5. AND of wires 3 and 8
6. OR of wires 3 and 8

## Verified circuit constraints

- `FiveSAT.posted_implies_Boolean` in `PostedSAT.lean` starts from the literal public statement. Any circuit witnessing the original desk statement satisfies one of seven Boolean constraint systems. The system checks all 32 rows, enforces the legal operand ranges and effective use of every nonoutput gate. An UNSAT proof for all seven would refute the posted statement.
- `Envelope.lean` and `Pivotal.lean` show that forcing the unique inverter to either constant changes the output. Its input crosses the target in both directions. This immediately excludes a symmetry class when the NOT is the second gate.
- `LateShape.lean` proves that position 7, counted from zero, forces either `(¬G ∧ A) ∨ B` or `(¬G ∨ A) ∧ B`. Both G and B are computed in the earlier seven-gate prefix.
- `LatePins.lean` proves that all three functions G, A and B must be pairwise distinct and that A must also be an internal wire. At an OR output, A is true on two rows and false on their coordinatewise meet. At an AND output, A is false on two rows and true on their coordinatewise join. This excludes a pure conjunction or pure disjunction of positive inputs, respectively.
- `PositionSix.lean` proves that at zero-based position 6 the inverter cannot feed both of the following two gates. It also cannot feed the output directly. Since an effective consumer is necessary, precisely one of the next two gates consumes it.
- `StrictLate.lean` transfers the position-7 result to a Boolean model with three internal selectors and pairwise-distinct selector IDs. Any choice of sampled rows gives necessary constraints on the physical circuit.

## Replayed SAT exclusions

The table lists nested shards. Each excludes a complete unrestricted suffix for the specified fixed prefix and inverter position. An independent native row-selection phase supplied small row sets. The Lean theorem separately proves that every eligible physical circuit obeys each chosen row, generates Boolean clauses and checks the LRAT refutation through Mathlib. The final `exclusion` results depend only on `propext`, `Classical.choice` and `Quot.sound`.

| Fixed prefix gates | Free remaining gates | Separating rows | Reified Boolean nodes | Clauses | LRAT bytes |
|---:|---:|---|---:|---:|---:|
| 4 | 6 | 3, 6, 10, 14, 18, 22, 26 | 528 | 3517 | 1,813,122 |
| 5 | 5 | 1, 3, 6, 9, 10, 14, 20, 26 | 438 | 2879 | 457,175 |
| 6 | 4 | 1, 9, 10, 14, 24, 26 | 250 | 1587 | 87,628 |

The checked `Lift` modules extend their respective exclusions to any physical prefix with the same ordered wire values on the separating rows.

Local SAT runs also reported UNSAT after fixing only two or three gates on ten sampled rows. The corresponding full-prefix-branch LRAT traces were 28,132,416 and 4,391,106 bytes. The monolithic three-fixed-gate kernel replay exceeded a 10.8 GB process limit. These two numerical results are computational evidence. The verified full-suffix list is the table above.

## Reproduction

From the PEqualNP Lean project with its dependencies built, run `lake env python /absolute/path/to/replay.py`. The source was checked against Lean 4.36.0. The runner builds imports in a temporary directory and replays the included LRAT text. Certificate generation is unnecessary. The complete module list and printed axiom declarations are included.

The earlier counting and duality contributions are from pjscruggs and the existing project sources, as recorded in the earlier modules. The Boolean-to-LRAT tactic was adapted from the graph lane’s `KernelReplay.lean`. External solvers and the row-selection program are outside the resulting proofs’ trusted assumptions.
