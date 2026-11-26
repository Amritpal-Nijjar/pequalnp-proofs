import HeadOptions
import OutputPins
namespace FiveRestricted
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Finite

structure RoundFilters (C : Circuit) : Prop where
  earlier : Filters C
  realNot : RealPins C
  firstChoice : firstAllowed C = true
  degrees : degree 0 C.gates ≤ 2 ∧ degree 4 C.gates ≤ 2 ∧ degree 1 C.gates ≤ 4 ∧
    degree 2 C.gates ≤ 4 ∧ degree 3 C.gates ≤ 4
  budgets : ∀ c ∈ cofs, ∀ p s, C.gates = p++s →
    p.countP (fun g => !isNot g) + c.L ≤ workCost p (restrictedW c) + 9
  finalPins : ∀ p f, C.gates=p++[f] → ∀ j∈f.inputs, 5 ≤ j

theorem pruned_model : (∃ C, Qualifies C) ↔ ∃ v : Plan, Qualifies (net v) ∧ RoundFilters (net v) := by
  constructor
  · intro h
    obtain ⟨C,hc,unary⟩ := unary_iff.mp h
    obtain ⟨v,eq⟩ := plan_covers hc
    refine ⟨v,eq ▸ hc,?_⟩
    rw [eq]
    exact ⟨filters hc,unary,first_among_nineteen hc,all_fanouts hc,
      fun c mem _ _ sp => prefix_budget hc mem sp,fun p f sp j hit => no_input_at_output hc p f sp j hit⟩
  · rintro ⟨v,h,_⟩; exact ⟨net v,h⟩

/-- The left side is copied verbatim from the public desk record. -/
theorem posted_iff_round_two :
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 5 C ∧ C.size ≤ 10 ∧ (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = PEqualNP.MetaComplexity.tableFun 5 (([0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1] : List ℕ).map (fun b => b == 1)) x) ∧ (∀ j < C.size, C.output = 5 + j ∨ ∃ i < C.size, j < i ∧ 5 + j ∈ (C.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) ∧ (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → 5 ≤ g.inputs.headD 0 → (C.gates.getD (g.inputs.headD 0 - 5) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ 5 ≤ g.inputs.headD 0)) ↔ ∃ v : Plan, Qualifies (net v) ∧ RoundFilters (net v) :=
  posted_iff_pruned.trans (finite_model.symm.trans pruned_model)

#print axioms posted_iff_round_two
end FiveRestricted
