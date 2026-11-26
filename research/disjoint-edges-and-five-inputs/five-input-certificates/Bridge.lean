import FinitePlan

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Five18096Finite

/-- The expression on the left is copied from the public L-meta-18096 desk record. -/
theorem posted_iff_pruned :
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 5 C ∧ C.size ≤ 10 ∧ (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = PEqualNP.MetaComplexity.tableFun 5 (([0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1] : List ℕ).map (fun b => b == 1)) x) ∧ (∀ j < C.size, C.output = 5 + j ∨ ∃ i < C.size, j < i ∧ 5 + j ∈ (C.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) ∧ (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → 5 ≤ g.inputs.headD 0 → (C.gates.getD (g.inputs.headD 0 - 5) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ 5 ≤ g.inputs.headD 0)) ↔ ∃ v : Plan, Qualifies (net v) ∧ Filters (net v) := by
  rw [←finite_model]
  constructor
  · rintro ⟨C, legal, back, cap, comp, used, nd, internal⟩
    exact ⟨C,legal,back,cap,comp,used,nd,internal⟩
  · rintro ⟨C,h⟩
    exact ⟨C,h.legal,h.back,h.cap,h.computes,h.used,h.noDouble,h.internal⟩

#print axioms posted_iff_pruned
