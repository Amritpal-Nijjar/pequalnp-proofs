# Five-input circuit result for L-meta-18096

For the target truth table `0xfee8eaa8`, Lean rules out **AND(input 0, input 4) as the first gate** of a qualifying circuit. Inputs are numbered 0 through 4. This covers both pin orders, every legal location and source for the unique internal NOT, and arbitrary later wiring. Up to swapping the operands of an AND or OR, 19 of the 20 possible first gates remain. The proof establishes no full refutation and gives no ten-gate witness.

## Why this first gate fails

Fixing input 0 to false leaves a four-input function that requires at least seven signed binary gates. Fixing input 4 to true also leaves a function that requires at least seven. These published lower bounds still hold when complementary wires are free. The original gate budget contains exactly nine binary gates, so at most two binary gates may become free on either restriction. A gate is free here when it produces a constant or repeats an earlier signal, including its complement.

Let the proposed first gate compute `G = x0 AND x4`. Under the first restriction, both `x0` and `G` are false. The first gate has spent one of the two allowable losses. The target changes between input rows 2 and 3 even though `G` does not, so a later binary gate must read `x0` directly. Any later binary gate that reads `G` would have to be that same gate. Combining `G` directly with `x0` gives back one of the two operands, wasting a binary gate even on the unrestricted table. As the first gate must have a genuine consumer, the internal NOT would have to invert `G`.

In that case the second restriction, `x4 = true`, makes `G = x0` and `NOT G = NOT x0`. The first restriction forces the later uses of `x0` and `NOT G` to coincide in one gate. That gate becomes constant on the second restriction. The target also changes between rows 6 and 22, so a further binary gate must read `x4`. The second restriction would now lose three binary gates. This exceeds its allowance. The argument permits unrelated gates between the first gate and the NOT.

## Consequences for an exhaustive search

- Every non-output gate has a later use that actually reads its value. In particular, a NOT's optional ignored second pin cannot supply the only use of another gate. Lean proves that stripping all these ignored pins preserves every condition of the posted question, including its syntactic liveness requirement. A search may therefore use a strictly unary NOT.
- Across the entire circuit, raw inputs 0 and 4 each feed at most two binary gates. Inputs 1, 2 and 3 each feed at most four. The two inputs to the final binary gate are both computed wires.
- The certificate gives signed lower bounds for nine four-input restrictions. In any prefix, the number of binary gates already used minus its signed cost is at most nine minus that restriction's lower bound. The bound is seven for `x0 = false` and `x4 = true`, six for `x4 = false`, and five for either setting of each of `x1`, `x2`, and `x3`.
- Lean checks all 120 permutations of the five inputs. The six that preserve the truth table permute inputs 1, 2 and 3 and keep inputs 0 and 4 fixed. Relabeling a circuit by any of the six preserves every desk condition. The remaining 19 first gates therefore reduce to seven representatives. The AND representatives use pairs (0,1), (1,2), and (1,4). The OR representatives use pairs (0,1), (1,2), (1,4), and (0,4). The inverter's seven possible positions are a separate count.

The theorem `FiveRestricted.posted_iff_seven` copies the posted statement on its left and proves equivalence to the finite, pruned family with these seven first-gate representatives. The theorem `FiveRestricted.no_first_and_04` gives the first-gate exclusion directly. Both depend only on Lean's standard axioms `propext`, `Classical.choice`, and `Quot.sound`. This was a local proof run.

## Reproduction and credits

From a configured checkout of the PEqualNP Lean project using Lean 4.36.0, run `lake env python path/to/replay.py`. The script compiles the included source modules in dependency order into a temporary directory. The archive contains the exact desk record in `target.json` and the recorded axiom summaries in `axiom_audit.txt`.

The underlying signed lower bounds come from the project's L-meta-12108 proof. The exact nine-binary, one-NOT specialization came from pjscruggs. The earlier local work connected that specialization to the desk's circuit syntax. This round proves the restriction filter, first-gate exclusion, effective-use and unary-NOT results. [Published lower-bound source](https://github.com/open-goat/pequalnp-proofs/blob/1da257ad61cac8c541dd69d44ff32c88cb47eec2/lean/PEqualNP/Outside/L_meta_12108.lean) · [Collaborator's specialization](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19910038) · [Project question](https://pequalnp.com/lemma#L-meta-18096)
