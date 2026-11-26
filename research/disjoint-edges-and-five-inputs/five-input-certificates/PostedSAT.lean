import SATExtract
namespace FiveSAT
open Five18096Finite
/-- The input is the literal desk statement. Thus UNSAT certificates for each of
the seven Boolean constraint families suffice to refute L-meta-18096. -/
theorem posted_implies_Boolean : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 5 C ∧ C.size ≤ 10 ∧ (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = PEqualNP.MetaComplexity.tableFun 5 (([0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1] : List ℕ).map (fun b => b == 1)) x) ∧ (∀ j < C.size, C.output = 5 + j ∨ ∃ i < C.size, j < i ∧ 5 + j ∈ (C.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) ∧ (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → 5 ≤ g.inputs.headD 0 → (C.gates.getD (g.inputs.headD 0 - 5) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ 5 ≤ g.inputs.headD 0)) →
    ∃ (k : Fin 10) (w : WireBits) (left right : Fin 10→Select) (op : Fin 10→Bool),
      1≤k.val ∧ k.val≤7 ∧ strictPass k w left right op=true := by
  intro h
  exact sat_necessary (finite_model.mpr (posted_iff_pruned.mp h))
#print axioms posted_implies_Boolean
end FiveSAT
