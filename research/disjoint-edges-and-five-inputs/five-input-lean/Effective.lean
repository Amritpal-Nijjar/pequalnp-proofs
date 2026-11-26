import Touches
namespace FiveRestricted
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Ends Five18096Bypass Five18096Finite

def effective (g : Gate) : List ℕ := if isNot g then g.inputs.take 1 else g.inputs

lemma same_gate {j : ℕ} {a b : List Bool} (h : AgreeOff j a b) (g : Gate) (unread : j∉effective g) :
    g.op.eval (g.inputs.map fun i => a.getD i false)=g.op.eval (g.inputs.map fun i => b.getD i false) := by
  by_cases n : g.op=.not
  · obtain ⟨op, l⟩ := g
    change op=.not at n
    subst op
    cases l with
    | nil => rfl
    | cons i xs =>
      have ne : i≠j := by simpa [effective,isNot,eq_comm] using unread
      change (!(a.getD i false)) = (!(b.getD i false))
      rw [h.2 i ne]
  · have nn : isNot g=false := by obtain ⟨op,ins⟩:=g; cases op <;> simp_all [isNot]
    apply congrArg g.op.eval
    apply List.map_congr_left
    intro i hi
    exact h.2 i (fun eq => unread (by simpa [effective,nn,eq] using hi))

lemma effective_off (s : List Gate) (j : ℕ) (a b : List Bool) (head : AgreeOff j a b)
    (unread : ∀ g∈s,j∉effective g) : AgreeOff j (phys s a) (phys s b) := by
  induction s generalizing a b with
  | nil => exact head
  | cons g s ih =>
    have gate := same_gate head g (unread g (by simp))
    change AgreeOff j (phys s (a++[g.op.eval (g.inputs.map fun i => a.getD i false)]))
      (phys s (b++[g.op.eval (g.inputs.map fun i => b.getD i false)]))
    rw [gate]
    exact ih _ _ (snoc_off head _) (fun v hv => unread v (by simp [hv]))

lemma effective_required {C : Circuit} (h : Qualifies C) (p s : List Gate)
    (sp : C.gates=p++s) (i : ℕ) (r t : Row) (outputs : bit r fiveGraph ≠ bit t fiveGraph)
    (ow : C.output≠i) (wires : AgreeOff i ((execute p fiveInputs).map (bit r)) ((execute p fiveInputs).map (bit t))) :
    ∃ g∈s, i∈effective g := by
  by_contra! none
  have last := (effective_off s i _ _ wires none).2 C.output ow
  have physRow (q : Row) : phys s ((execute p fiveInputs).map (bit q)) =
      (execute C.gates fiveInputs).map (bit q) := by
    rw [sp,execute_append]
    exact (saved_execute_bits s q _ (fun a ha => (h.legal a (by simp [sp,ha])).1)).symm
  rw [physRow,physRow,Five18096Paths.bits_at,Five18096Paths.bits_at,
      computed_sig C h.legal h.computes] at last
  exact outputs last

lemma replace_last (w : List Bool) (x y : Bool) : AgreeOff w.length (w++[x]) (w++[y]) := by
  refine ⟨by simp,?_⟩
  intro i ne
  by_cases small : i<w.length
  · simp [List.getD_eq_getElem?_getD,List.getElem?_append_left small]
  · have e : (w++[x])[i]?=none := List.getElem?_eq_none (by simp; omega)
    have f : (w++[y])[i]?=none := List.getElem?_eq_none (by simp; omega)
    simp [List.getD_eq_getElem?_getD,e,f]

/-- Even if the desk's syntactic liveness is satisfied by an ignored NOT pin,
the first ordinary gate must be read on an *effective* pin. -/
theorem first_required {C : Circuit} (h : Qualifies C) (g : Gate) (s : List Gate)
    (sp : C.gates=g::s) (nn : isNot g=false) : ∃q∈s, 5∈effective q := by
  by_contra! none
  let dummy : Gate := ⟨.or,[]⟩
  let fake : Circuit := ⟨dummy::s,C.output⟩
  have mem (q) (hq : q∈s) := h.legal q (by simp [sp,hq])
  have legal : FanInTwo fake := by
    intro q hq
    change q∈dummy::s at hq
    rcases List.mem_cons.mp hq with rfl|hs
    · simp [dummy]
    · exact mem q hs
  have eq : (execute fake.gates fiveInputs).getD fake.output zero=fiveGraph := by
    rw [←computed_sig C h.legal h.computes]
    apply bit_ext
    intro r
    let w := fiveInputs.map (bit r)
    have sl : w.length=5 := by rw [show w=fiveInputs.map (bit r) from rfl,List.length_map]; rfl
    have base := replace_last w (bit r (gv fiveInputs dummy)) (bit r (gv fiveInputs g))
    rw [sl] at base
    have final := (effective_off s 5 _ _ base none).2 C.output (by rw [final_output h]; decide)
    rw [←Five18096Paths.bits_at,←Five18096Paths.bits_at,sp]
    change ((execute s (fiveInputs++[gv fiveInputs dummy])).map (bit r)).getD C.output false =
      ((execute s (fiveInputs++[gv fiveInputs g])).map (bit r)).getD C.output false
    rw [saved_execute_bits s r _ (fun a ha => (mem a ha).1),saved_execute_bits s r _ (fun a ha => (mem a ha).1)]
    simpa [phys,w] using final
  have base := baseOK_ok p13_B
  have low := signed_cost_lower fake legal fiveInputs fiveInputs fiveGraph 9 p13_L base.prop
    (by simpa [fiveGraph,plainWord] using base.plain)
    (by have pr : fiveInputs.all plainWord=true := base.plainR; rw [nrm_map pr]; intro a ha; exact Or.inr ha) eq
  have total := (exactCounts C h.legal h.cap h.computes h.internal).2.2
  simp [sp,List.countP_cons,nn] at total
  have zeroFee : (isNot dummy || collapsed fiveInputs dummy)=true := by decide +kernel
  change 9 ≤ (if isNot dummy || collapsed fiveInputs dummy then 0 else 1) + workCost s _ at low
  simp [zeroFee] at low
  have bound := cost_max s (fiveInputs++[gv fiveInputs dummy])
  omega

#print axioms first_required
end FiveRestricted
