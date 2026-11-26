import Forbidden

namespace Five18096Ends

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_12108 FiveInputLower Five18096Fresh

/-- Zero-based gate indices: the unique NOT must be one of 1,2,3,4,5,6,7. -/
theorem not_position (C : Circuit) (legal : FanInTwo C) (cap : C.size ≤ 10)
    (computes : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = tableFun 5 b x)
    (rb : NestedCover.ReadsBack 5 C) (used : UsedOrOutput C)
    (p s : List Gate) (g : Gate) (split : C.gates = p++g::s)
    (isn : g.op=.not) (outside : 5 ≤ g.inputs.headD 0) :
    1 ≤ p.length ∧ p.length ≤ 7 ∧ 2 ≤ s.length := by
  have back : Back 5 C.gates := back_of_index _ _ rb
  rw [split] at back
  have headmem : g.inputs.headD 0 ∈ g.inputs := by
    cases ins : g.inputs with
    | nil => simp [ins] at outside
    | cons a l => simp
  have early := (back_split p (g::s) 5 back).2.1 (g.inputs.headD 0) headmem
  have len : C.size = p.length + (s.length+1) := by simp [Circuit.size,split]
  have after : 2 ≤ s.length := by
    cases s with
    | nil => exact (not_cannot_be_output C legal cap computes rb used p g split isn outside).elim
    | cons f m =>
      cases m with
      | cons a m => simp
      | nil =>
        have sf : C.gates = (p++[g])++[f] := by simpa [List.append_assoc] using split
        have last := last_output C (p++[g]) f sf used
        simp only [List.length_append,List.length_singleton] at last
        have size : C.size=p.length+2 := by simp [Circuit.size,split]
        obtain eq | ⟨i,hi,gt,wire⟩ := used p.length (by omega)
        · omega
        · have idx : i=p.length+1 := by omega
          subst i
          have actual : C.gates.getD (p.length+1) ⟨.and,[]⟩ = f := by
            simp [split,List.getD_eq_getElem?_getD,List.getElem?_append_right]
          rw [actual] at wire
          exact (output_cannot_read_not C legal cap computes rb used p [] g f split isn outside wire).elim
  omega

#print axioms not_position
end Five18096Ends
