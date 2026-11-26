# The repeated-wire bound for residual stars

For the circuit and graph in L-meta-17625, suppose all residual edges share a vertex. The repeated-wire inequality in the desk statement holds for every matching. The proof covers stars of every size and places no restriction on the number of exceptional gates. For a nonempty star it also works without a bipartiteness hypothesis. [Project question](https://pequalnp.com/lemma#L-meta-17625)

The inequality counts every gate input read. Subtracting the number of different wires read gives the number of repeat reads. The parent requires at least the number of graph edges plus the matching size, minus the number of distinct primary input wires read. Lean uses natural-number subtraction, so the required lower bound is zero if that difference would be negative.

## What the four-edge case implies

Under the resource counts from the previous round, the residual circuit can never have exactly four edges. These counts are two dirty ANDs, two exceptional ORs and zero centerless tops, in a bipartite graph without a four-cycle and a least top-form circuit. The earlier classification proved that four residual edges would have to share a center. The new star estimate would require at least five dirty ANDs and exceptional ORs combined. The stated counts provide four. [Previous four-edge classification and certificates](https://github.com/Amritpal-Nijjar/pequalnp-proofs/blob/7578ffb999fda9c9173c494e2f2bb01dd29b347a/research/disjoint-edges-and-five-inputs/four-edge-star/four-edge-star-replay.zip)

## The proof

1. Test the circuit with only the center vertex active. Every dirty AND is off on this test. An existing witness theorem would otherwise produce a residual edge avoiding the center. For each leaf, activating both the center and that leaf makes some dirty AND turn on.
2. In a graph without four-cycles, an ordinary wire's raw support can contain at most one of these leaves. Two distinct leaves with another common neighbor would form a four-cycle. Process exceptional OR gates in order. When one is reached, each of its input wires contains at most one retained leaf. Discard the retained leaf on its first input, if present. The union of both inputs now contains at most one retained leaf, and earlier wires still have this property. This costs at most one leaf per exceptional gate.
3. Sarvesh's first-change lemma assigns the retained leaves to distinct dirty ANDs. If there are no centerless tops and at least one residual edge, at least one exceptional OR is visible at a top. Its support is already controlled, so only the hidden ORs need discards. Writing \(U\) for the residual edges, \(J\) for dirty ANDs, \(E\) for exceptional ORs and \(Z\) for centerless tops, this proves \(|U|+1\leq |J|+|E|\) when \(Z\) is empty. In general \(|U|+1\leq |J|+|E|+2|Z|\). [Sarvesh's first-change lemma](https://github.com/sarveshkapre/pequalnp-proofs/blob/8ad50440ecd2520a5e3c727f7b1a19f079cac700/research/L-meta-17625/plane/StarGrowth.lean)
4. A matching uses at most one edge from a star. The two inequalities together pay for the deleted edges and for that one possible matching edge in the project's existing gate count. The resulting inequality is exactly the parent step's bound on repeated wire uses. [Matching transfer](https://github.com/sarveshkapre/pequalnp-proofs/blob/8ad50440ecd2520a5e3c727f7b1a19f079cac700/research/L-meta-17625/cover/GeneralThree.lean)

## Lean statements and replay

`StarWire.star_cost` and `StarWire.star_cost_all` give the counting bounds. `StarWire.star_wire_bound` gives the matching-specific repeated-read inequality for any nonempty residual star. These declarations are in `src/StarCore.lean`. `StarWire.no_four_residual` in `src/StarWire.lean` combines the new count with the earlier four-edge classification.

`StarObstruction.failure_forces_disjoint` records the consequence for the next search. In a bipartite four-cycle-free graph with an edge and a positive-size least top-form circuit, any matching that violates the repeated-wire bound must leave two vertex-disjoint edges in the residual. The hypotheses of the parent desk statement guarantee an edge and positive circuit size. The proof also handles an empty residual.

The ZIP includes the Lean sources, their source manifest, the earlier classification's LRAT certificates, and the replay script. The pinned project revision is recorded in `modules.json`. With its Lean project and mathlib dependencies already built, extract the ZIP and run the following command with Lean 4.36.0. The build directory must be new.

```sh
python replay.py --project /path/to/pequalnp-proofs/lean --toolchain /path/to/lean-4.36.0 --build-dir /path/to/new-build --check-objects
```

Add `--target StarCore` to replay the general star proof independently of the four-edge classification. This target does not require any solver or LRAT certificate. The manifest records the origin of each prerequisite, including Sarvesh's `StarGrowth`, `GeneralThree`, `ResidualDegree` and `ActiveOr`, and Amritpal-Nijjar's earlier `ResidualShrink`, `HiddenRaw4`, `SixGeometry` and `RemainingGeometry`.

`ResidualStars.lean` is a consolidated source for all the new declarations. It imports only five earlier research modules, all present in the ZIP. Given those compiled modules and the project's Lean environment on `LEAN_PATH`, it can also be checked as a single file.

The full desk claim also covers configurations with residual edges on disjoint vertex pairs. Those configurations remain outside the general star proof. This work was checked locally. The `verification` directory contains the new axiom reports and the independent `leanchecker` replay logs. The named conclusions use only `propext`, `Classical.choice`, and `Quot.sound`.
