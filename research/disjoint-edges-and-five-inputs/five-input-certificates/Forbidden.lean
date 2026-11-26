import LastGate

namespace Five18096Ends

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_12108 FiveInputLower Five18096Fresh

lemma falling_pin (w : List Sig) (g : Gate) (i : ℕ) (hi : i ∈ g.inputs)
    (leg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (nn : isNot g=false) (fresh : ¬ Old w g)
    (falls : Falling (w.getD i zero)) : ¬Rising (gv w g) := by
  obtain ⟨a,b,ins,_⟩ := distinct_pins w g leg nn fresh
  have ab : i=a ∨ i=b := by simpa [ins] using hi
  obtain ⟨op,l⟩ := g
  change l=[a,b] at ins
  subst l
  have h := leg.1
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  intro r
  rcases h with rfl | rfl | rfl
  · rw [show gv w ⟨.and,[a,b]⟩ = _ from value_two w false a b] at r
    have v := r.2
    rcases ab with rfl | rfl <;>
      simp only [bit_prime,Bool.false_eq_true,↓reduceIte,falls.2] at v <;> simp at v
  · rw [show gv w ⟨.or,[a,b]⟩ = _ from value_two w true a b] at r
    have v := r.1
    rcases ab with rfl | rfl <;>
      simp only [bit_prime,↓reduceIte,falls.1] at v <;> simp at v
  · simp [isNot] at nn

theorem not_cannot_be_output (C : Circuit) (legal : FanInTwo C) (cap : C.size ≤ 10)
    (computes : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = tableFun 5 b x)
    (rb : NestedCover.ReadsBack 5 C) (used : UsedOrOutput C)
    (p : List Gate) (g : Gate) (split : C.gates=p++[g])
    (isn : g.op=.not) (outside : 5 ≤ g.inputs.headD 0) : False := by
  have h := internal_not_falls C legal cap computes rb p [] g split isn outside
  rw [value_last C legal computes used p g split] at h
  exact Bool.noConfusion (target_rises.1.symm.trans h.1)

theorem output_cannot_read_not (C : Circuit) (legal : FanInTwo C) (cap : C.size ≤ 10)
    (computes : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = tableFun 5 b x)
    (rb : NestedCover.ReadsBack 5 C) (used : UsedOrOutput C)
    (p m : List Gate) (g f : Gate) (split : C.gates=p++g::(m++[f]))
    (isn : g.op=.not) (outside : 5 ≤ g.inputs.headD 0) : 5+p.length ∉ f.inputs := by
  let front := (p ++ [g]) ++ m
  have sf : C.gates=front++[f] := by simpa [front,List.append_assoc] using split
  have int : ∃ a ∈ C.gates, a.op=.not ∧ 5≤a.inputs.headD 0 :=
    ⟨g, by simp [split], isn, outside⟩
  have count := (exactCounts C legal cap computes int).2.1
  have nn := (no_other_not C p (m++[f]) g split isn count).2 f (by simp)
  have leg := legal f (by simp [sf])
  have fr := fresh_exact C legal cap computes int
  rw [sf] at fr
  have ff := (run_split front [f] fiveInputs fr).2.1 nn
  have falls := internal_not_falls C legal cap computes rb p (m++[f]) g split isn outside
  have len : (execute p fiveInputs).length = 5+p.length := by rw [execute_len]; rfl
  have read : (execute front fiveInputs).getD (5+p.length) zero = gv (execute p fiveInputs) g := by
    rw [←len]
    simp only [front,execute_append]
    rw [show execute [g] (execute p fiveInputs) =
      execute p fiveInputs ++ [gv (execute p fiveInputs) g] from rfl]
    exact kept_wire m (execute p fiveInputs) (gv (execute p fiveInputs) g)
  intro pin
  have bad := falling_pin (execute front fiveInputs) f _ pin leg nn ff (read ▸ falls)
  rw [value_last C legal computes used front f sf] at bad
  exact bad target_rises

#print axioms output_cannot_read_not
end Five18096Ends
