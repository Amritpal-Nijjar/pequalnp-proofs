import Ends

namespace Five18096Ends

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_12108 FiveInputLower Five18096Fresh

lemma run_split (p s : List Gate) (w : List Sig) :
    FreshRun (p ++ s) w → FreshRun p w ∧ FreshRun s (execute p w) := by
  induction p generalizing w with
  | nil => exact fun h => ⟨trivial,h⟩
  | cons g p ih =>
    intro h
    obtain ⟨l,r⟩ := ih _ h.2
    exact ⟨⟨h.1,l⟩,r⟩

lemma back_split (p s : List Gate) (k : ℕ) :
    Back k (p ++ s) → Back k p ∧ Back (k+p.length) s := by
  induction p generalizing k with
  | nil => intro h; exact ⟨trivial,h⟩
  | cons g p ih =>
    intro h
    obtain ⟨l,r⟩ := ih _ h.2
    refine ⟨⟨h.1,l⟩,?_⟩
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1 _] using r

lemma execute_append (p s : List Gate) (w : List Sig) :
    execute (p ++ s) w = execute s (execute p w) := by simp [execute,List.foldl_append]

lemma execute_extends (gs : List Gate) (w : List Sig) : ∃ t, execute gs w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨t,h⟩ := ih (w ++ [gv w g])
    exact ⟨gv w g::t,by simpa [execute,List.append_assoc] using h⟩

lemma kept_wire (gs : List Gate) (w : List Sig) (v : Sig) :
    (execute gs (w ++ [v])).getD w.length zero = v := by
  obtain ⟨t,h⟩ := execute_extends gs (w ++ [v])
  rw [h,List.append_assoc]
  simp [List.getD_eq_getElem?_getD,List.getElem?_append_right]

lemma computed_sig (C : Circuit) (legal : FanInTwo C)
    (computes : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = tableFun 5 b x) :
    (execute C.gates fiveInputs).getD C.output zero = fiveGraph := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let r : Row := ⟨j,hj⟩
  exact (fiveEval C legal C.output r).trans ((computes (sample r)).trans (fiveTable r).symm)

def UsedOrOutput (C : Circuit) : Prop :=
  ∀ j < C.size, C.output = 5+j ∨ ∃ i < C.size, j < i ∧
    5+j ∈ (C.gates.getD i ⟨.and,[]⟩).inputs

lemma last_output (C : Circuit) (p : List Gate) (g : Gate)
    (split : C.gates = p ++ [g]) (used : UsedOrOutput C) :
    C.output = 5 + p.length := by
  have len : C.size = p.length + 1 := by simp [Circuit.size,split]
  obtain eq | ⟨i,hi,lo,_⟩ := used p.length (by omega)
  · exact eq
  · omega

lemma value_last (C : Circuit) (legal : FanInTwo C)
    (computes : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = tableFun 5 b x)
    (used : UsedOrOutput C) (p : List Gate) (g : Gate) (split : C.gates = p ++ [g]) :
    gv (execute p fiveInputs) g = fiveGraph := by
  have t := computed_sig C legal computes
  rw [last_output C p g split used,split,execute_append] at t
  have len : (execute p fiveInputs).length = 5+p.length := by rw [execute_len]; rfl
  rw [←len] at t
  simpa [execute,List.getD_eq_getElem?_getD,List.getElem?_append_right] using t

lemma no_other_not (C : Circuit) (p s : List Gate) (g : Gate) (split : C.gates=p++g::s)
    (isn : g.op = .not) (count : C.gates.countP isNot = 1) :
    (∀ q ∈ p, isNot q = false) ∧ ∀ q ∈ s, isNot q = false := by
  have a : isNot g = true := by simp [isNot,isn]
  rw [split,List.countP_append,List.countP_cons] at count
  simp only [a,↓reduceIte] at count
  have hp : p.countP isNot = 0 := by omega
  have hs : s.countP isNot = 0 := by omega
  constructor
  · intro q hq
    have z := List.countP_eq_zero.mp hp q hq
    cases n : isNot q <;> simp_all
  · intro q hq
    have z := List.countP_eq_zero.mp hs q hq
    cases n : isNot q <;> simp_all

theorem internal_not_falls (C : Circuit) (legal : FanInTwo C) (cap : C.size ≤ 10)
    (computes : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = tableFun 5 b x)
    (rb : NestedCover.ReadsBack 5 C)
    (p s : List Gate) (g : Gate) (split : C.gates=p++g::s)
    (isn : g.op=.not) (outside : 5 ≤ g.inputs.headD 0) :
    Falling (gv (execute p fiveInputs) g) := by
  have int : ∃ a ∈ C.gates, a.op=.not ∧ 5≤a.inputs.headD 0 :=
    ⟨g, by simp [split], isn, outside⟩
  have count := (exactCounts C legal cap computes int).2.1
  have nn := (no_other_not C p s g split isn count).1
  have whole := fresh_exact C legal cap computes int
  rw [split] at whole
  have pre := (run_split p (g::s) fiveInputs whole).1
  have back : Back 5 C.gates := back_of_index _ _ rb
  rw [split] at back
  have ba := back_split p (g::s) 5 back
  have rises := prefix_rises p fiveInputs roots_rise (fun a ha => legal a (by simp [split,ha])) nn ba.1 pre
  obtain ⟨op,l⟩ := g
  change op=.not at isn
  subst op
  cases l with
  | nil => simp at outside
  | cons a l =>
    have ha := ba.2.1 a (by simp)
    have len : (execute p fiveInputs).length = 5+p.length := by rw [execute_len]; rfl
    have ra := rises _ (read_mem _ a (len ▸ ha))
    change Falling (neg ((execute p fiveInputs).getD a zero))
    exact ⟨by rw [saved_bit_neg,ra.1]; rfl, by rw [saved_bit_neg,ra.2]; rfl⟩

#print axioms internal_not_falls
end Five18096Ends
