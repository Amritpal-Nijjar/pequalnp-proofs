# Three disjoint residual edges in L-meta-17625

Amritpal-Nijjar's local Lean 4.36.0 proof establishes the matching wire bound for a residual consisting of three pairwise vertex-disjoint edges. The ambient graph may have arbitrarily many vertices. The theorem uses a bipartite graph with no four-cycle and a least binary AND/OR circuit in top form. See [the conclusion](src/DisjointBound.lean) and the [axiom and object audit](evidence/axioms.txt).

Sarvesh Kapre's touching and connected cases show that any failure with exactly three residual edges would have three disjoint edges. The two results together give the bound for every residual with exactly three edges. [Kapre's theorem](https://github.com/sarveshkapre/pequalnp-proofs/blob/8ad50440ecd2520a5e3c727f7b1a19f079cac700/research/L-meta-17625/overlap-next/disjoint/projection/TwoTouching.lean) · [His recorded verification](https://github.com/sarveshkapre/pequalnp-proofs/blob/8ad50440ecd2520a5e3c727f7b1a19f079cac700/research/L-meta-17625/overlap-next/disjoint/verification.log)

Any hypothetical three-disjoint-edge failure gives four six-vertex raw masks and two reachability flags. The physical circuit forces them to satisfy `SixTerms.passes`. The supplied LRAT certificate proves that this is impossible. The physical bridge, finite exclusion, and final disjoint theorem passed separate object replays. The proof uses only `propext`, `Classical.choice`, and `Quot.sound`. A separate enumeration covered all 64 labeled cross-edge patterns and found no survivors. [Circuit bridge](src/SixBridge.lean) · [Finite exclusion](src/SixExclusion.lean) · [LRAT certificate](src/certificates/SixExclusion.lrat)

Use Lean 4.36.0 and the built PequalNP project files for commit `e6bfe1a56efc768d244627b78f175b18de1acd6f`. Supply a local clone of [Kapre's fork](https://github.com/sarveshkapre/pequalnp-proofs) containing commit `8ad50440ecd2520a5e3c727f7b1a19f079cac700`. Run the following from this directory.

```text
python replay.py --project PATH_TO_PROJECT/lean --research-repo PATH_TO_KAPRE_GIT_CLONE --toolchain PATH_TO_LEAN_4.36.0 --check-objects
python terms.py --all-graphs
```

Add `--with-touching` to rebuild Kapre's published modules and link the integration wrapper directly. In this run, the combination was checked against the exact published theorem signature. Kapre's own verification log covers his eighteen certificates. A supplementary clean rebuild was stopped by the time cap. The desk statement still includes four or more residual edges. [Posted question](https://pequalnp.com/lemma#L-meta-17625)
