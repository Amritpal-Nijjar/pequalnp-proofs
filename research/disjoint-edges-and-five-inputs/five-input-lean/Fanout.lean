import Cofactors

namespace FiveRestricted
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Ends Five18096Finite

def takes (j : ℕ) (g : Gate) := !isNot g && g.inputs.contains j
def degree (j : ℕ) (gs : List Gate) := gs.countP (takes j)

lemma units (a : Sig) : prime false zero a = zero ∧ prime false one a=a ∧
    prime false a zero=zero ∧ prime false a one=a ∧ prime true zero a=a ∧
    prime true one a=one ∧ prime true a zero=a ∧ prime true a one=one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro r <;>
    simp [bit_prime,saved_bit_zero,saved_bit_one]

lemma old_constant_pin (w : List Sig) (g : Gate) (j : ℕ)
    (legal : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp))
    (nn : isNot g=false) (binary : ∃ a b, g.inputs=[a,b] ∧ a≠b)
    (read : j ∈ g.inputs) (fixed : w.getD j zero = zero ∨ w.getD j zero=one) :
    collapsed w g=true := by
  apply (collapsed_iff w g).2
  obtain ⟨a,b,pins,_⟩ := binary
  obtain ⟨op,l⟩ := g
  change l=[a,b] at pins
  subst l
  have ab : j=a ∨ j=b := by simpa using read
  have op2 : op=.and ∨ op=.or := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at legal
    rcases legal with rfl|rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · simp [isNot] at nn
  have constant0 : PEqualNP.Outside.L_meta_12108.Repr true (w.map (nrm true)) zero :=
    repr_const (Or.inl rfl)
  have constant1 : PEqualNP.Outside.L_meta_12108.Repr true (w.map (nrm true)) one :=
    repr_const (Or.inr rfl)
  have ra := saved_get_rep (u:=true) w a
  have rb := saved_get_rep (u:=true) w b
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8⟩ := units (w.getD a zero)
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8⟩ := units (w.getD b zero)
  rcases op2 with rfl|rfl
  · change PEqualNP.Outside.L_meta_12108.Repr true _ (gv w ⟨.and,[a,b]⟩)
    rw [show gv w ⟨.and,[a,b]⟩ = _ from value_two w false a b]
    rcases ab with rfl|rfl <;> rcases fixed with hz|hz <;>
      rw [hz] <;> first | rwa [a1] | rwa [a2] | rwa [a3] | rwa [a4] |
                           rwa [b1] | rwa [b2] | rwa [b3] | rwa [b4]
  · change PEqualNP.Outside.L_meta_12108.Repr true _ (gv w ⟨.or,[a,b]⟩)
    rw [show gv w ⟨.or,[a,b]⟩ = _ from value_two w true a b]
    rcases ab with rfl|rfl <;> rcases fixed with hz|hz <;>
      rw [hz] <;> first | rwa [a5] | rwa [a6] | rwa [a7] | rwa [a8] |
                           rwa [b5] | rwa [b6] | rwa [b7] | rwa [b8]

lemma degree_cost (j : ℕ) (gs : List Gate) (w : List Sig)
    (leg : ∀ g∈gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp))
    (binary : EveryGateBinary gs)
    (index : j<w.length) (fixed : w.getD j zero = zero ∨ w.getD j zero=one) :
    workCost gs w + degree j gs ≤ gs.countP (fun g => !isNot g) := by
  induction gs generalizing w with
  | nil => simp [degree,workCost]
  | cons g gs ih =>
    have same : (w++[gv w g]).getD j zero=w.getD j zero := by
      simp [List.getD_eq_getElem?_getD,List.getElem?_append_left index]
    have tail := ih (w++[gv w g]) (fun a ha => leg a (by simp [ha]))
      (fun a ha hn => binary a (by simp [ha]) hn) (by simp; omega) (same ▸ fixed)
    cases nn : isNot g with
    | true => simpa [workCost,degree,takes,List.countP_cons,nn] using tail
    | false =>
      by_cases read : j∈g.inputs
      · have old := old_constant_pin w g j (leg g (by simp)) nn (binary g (by simp) nn) read fixed
        simp [workCost,degree,takes,List.countP_cons,nn,read,old] at *
        omega
      · cases c : collapsed w g <;> simp [workCost,degree,takes,List.countP_cons,nn,read,c] at * <;> omega

theorem fanout_bound {C : Circuit} (h : Qualifies C) {c : SCase} (hc : c∈cofs) :
    degree c.pin C.gates + c.L ≤ 9 := by
  have tab : cofs.all (fun d => decide (d.pin < (restrictedW d).length) &&
    (((restrictedW d).getD d.pin zero == zero) || ((restrictedW d).getD d.pin zero == one))) = true := by decide +kernel
  obtain ⟨small,fixed⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp tab c hc)
  have deg := degree_cost c.pin C.gates (restrictedW c) (fun g hg => (h.legal g hg).1)
    (filters h).binary (of_decide_eq_true small) (by simpa using fixed)
  have lower := cofactor_lower h hc
  have total := (exactCounts C h.legal h.cap h.computes h.internal).2.2
  omega

theorem all_fanouts {C : Circuit} (h : Qualifies C) :
    degree 0 C.gates ≤ 2 ∧ degree 4 C.gates ≤ 2 ∧ degree 1 C.gates ≤ 4 ∧
    degree 2 C.gates ≤ 4 ∧ degree 3 C.gates ≤ 4 := by
  have h0 := fanout_bound h (c:=⟨0,false,p5_T,7⟩) (by decide +kernel)
  have h4 := fanout_bound h (c:=⟨4,true,p7_T,7⟩) (by decide +kernel)
  have h1 := fanout_bound h (c:=⟨1,false,p8_T,5⟩) (by decide +kernel)
  have h2 := fanout_bound h (c:=⟨2,false,p8_T,5⟩) (by decide +kernel)
  have h3 := fanout_bound h (c:=⟨3,false,p8_T,5⟩) (by decide +kernel)
  dsimp only at h0 h4 h1 h2 h3
  omega

#print axioms all_fanouts
end FiveRestricted
