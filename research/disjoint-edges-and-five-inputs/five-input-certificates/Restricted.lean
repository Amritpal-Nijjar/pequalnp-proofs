import UniformPaths

/-! Physical-circuit lower bounds under four-input restrictions. Each AND/OR
is charged only when it contributes a new, nonconstant signed truth table.
The lower bounds for the four-input tables are the published L-meta-12108
results. This file supplies their connection to the exact physical witness. -/
namespace FiveRestricted
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_12108 FiveInputLower Five18096Fresh Five18096Ends Five18096Finite

def collapsed (w : List Sig) (g : Gate) : Bool :=
  let z := nrm true (gv w g)
  z == zero || z == one || (w.map (nrm true)).contains z

def workCost : List Gate → List Sig → ℕ
  | [], _ => 0
  | g::gs,w => (if isNot g || collapsed w g then 0 else 1) +
      workCost gs (w ++ [gv w g])

lemma collapsed_iff (w : List Sig) (g : Gate) : collapsed w g = true ↔ Old w g := by
  classical
  simp only [collapsed, Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,Old,
    PEqualNP.Outside.L_meta_12108.Repr,represented,proper,decide_eq_true_eq]
  tauto

lemma cost_eq (gs : List Gate) (w : List Sig) :
    workCost gs w = Five18096Fresh.cost gs w := by
  classical
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    by_cases old : Old w g
    · have hg := (collapsed_iff w g).2 old
      simp [workCost,Five18096Fresh.cost,fee,hg,old,ih]
    · have hg : collapsed w g=false := Bool.eq_false_iff.mpr (fun e => old ((collapsed_iff w g).1 e))
      simp [workCost,Five18096Fresh.cost,fee,hg,old,ih]

lemma cost_append (p s : List Gate) (w : List Sig) :
    workCost (p++s) w = workCost p w + workCost s (execute p w) := by
  induction p generalizing w with
  | nil => simp [workCost,execute]
  | cons g p ih =>
    change _ + workCost (p++s) (w++[gv w g]) = _ + workCost s (execute p (w++[gv w g]))
    rw [ih]; simp [workCost,Nat.add_assoc]

lemma cost_max (gs : List Gate) (w : List Sig) :
    workCost gs w ≤ gs.countP (fun g => !isNot g) := by
  rw [cost_eq]; exact cost_le _ _

lemma projected_output {C : Circuit} (h : Qualifies C) (w : List Sig) (f : Row → Row)
    (target : Sig) (inputs : ∀ r, w.map (bit r) = fiveInputs.map (bit (f r)))
    (spec : ∀ r, bit r target = bit (f r) fiveGraph) :
    (execute C.gates w).getD C.output zero = target := by
  apply bit_ext
  intro r
  rw [spec r, ←computed_sig C h.legal h.computes]
  rw [← Five18096Paths.bits_at, ← Five18096Paths.bits_at]
  rw [saved_execute_bits C.gates r w (fun a ha => (h.legal a ha).1),
      saved_execute_bits C.gates (f r) fiveInputs (fun a ha => (h.legal a ha).1), inputs r]

lemma signed_cost_lower (C : Circuit) (leg : FanInTwo C) (R : List Sig) (w : List Sig)
    (target : Sig) (L : ℕ) (prior : Lower true R target L)
    (hgood : proper target) (hzero : bit 0 target=false)
    (supplyRoots : ∀ a ∈ w.map (nrm true), a=zero ∨ a∈R)
    (out : (execute C.gates w).getD C.output zero = target) : L ≤ workCost C.gates w := by
  classical
  have repr := saved_get_rep (u:=true) (execute C.gates w) C.output
  rw [out] at repr
  unfold PEqualNP.Outside.L_meta_12108.Repr at repr
  rw [nrm_id hzero] at repr
  obtain ⟨k,S,hk,run,sub⟩ := extractCost C.gates w leg hgood (repr.resolve_right (fun h => h hgood))
  have steps := list_run run S.toList (Finset.nodup_toList _) (by simp)
  have supp : supply true (R.map observe) (S.toList.map observe) := by
    rintro a ha
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ha
    rcases supplyRoots z (sub z (Finset.mem_toList.mp hz)) with rfl | hr
    · exact Or.inr (Or.inl ⟨false,funext fun r => saved_bit_zero r⟩)
    · exact Or.inl (List.mem_map_of_mem hr)
  obtain ⟨q,bank,built,hit,limit⟩ := contraction (observe_proper hgood) steps (R.map observe) Reach.start supp
  have lower := prior q bank built hit
  rw [cost_eq]
  omega

end FiveRestricted
