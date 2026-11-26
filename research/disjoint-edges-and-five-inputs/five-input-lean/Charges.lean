import Fanout
namespace FiveRestricted
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Ends Five18096Finite

def markA (g : Gate) := g.inputs.contains 0 || g.inputs.contains 6
def markB (g : Gate) := g.inputs.contains 4 || (g.inputs.contains 0 && g.inputs.contains 6)

def GValid (g : Gate) := g.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
  isNot g=false ∧ ∃ a b, g.inputs=[a,b] ∧ a≠b

lemma charges (anchor : List Sig) (score : Gate → Bool)
    (implies : ∀ w extra g, w=anchor++extra → GValid g → score g=true → collapsed w g=true)
    (s : List Gate) (valid : ∀ g∈s, GValid g) (extra : List Sig) :
    workCost s (anchor++extra) + s.countP score ≤ s.length := by
  induction s generalizing extra with
  | nil => simp [workCost]
  | cons g s ih =>
    let w := anchor++extra
    have tail := ih (fun a ha => valid a (by simp [ha])) (extra++[gv w g])
    have hn := (valid g (by simp)).2.1
    change _ + workCost s (w++[gv w g]) + _ ≤ _
    rw [show w++[gv w g] = anchor++(extra++[gv w g]) from List.append_assoc ..]
    cases sc : score g with
    | true =>
      have old := implies w extra g rfl (valid g (by simp)) sc
      simp [List.countP_cons,sc,old,hn,w] at *
      omega
    | false => cases old : collapsed w g <;> simp [List.countP_cons,sc,old,hn,w] at * <;> omega

lemma stable_read {anchor : List Sig} (extra : List Sig) {i : ℕ} (small : i<anchor.length) :
    (anchor++extra).getD i zero=anchor.getD i zero := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_append_left small]

lemma chargeA (anchor : List Sig) (len : 6<anchor.length)
    (z : anchor.getD 0 zero=zero) (u : anchor.getD 6 zero=one) (s : List Gate)
    (valid : ∀ g∈s, GValid g) : workCost s anchor + s.countP markA ≤ s.length := by
  have result := charges anchor markA (by
    rintro w extra g rfl hg yes
    have e := Bool.or_eq_true_iff.mp yes
    rcases e with a|a
    · apply old_constant_pin _ _ 0 hg.1 hg.2.1 hg.2.2 (by simpa using a)
      exact Or.inl ((stable_read extra (show 0<anchor.length by omega)).trans z)
    · apply old_constant_pin _ _ 6 hg.1 hg.2.1 hg.2.2 (by simpa using a)
      exact Or.inr ((stable_read extra len).trans u)) s valid []
  simpa using result

lemma complement_laws (d : Bool) (a : Sig) :
    prime d a (neg a)=(if d then one else zero) ∧ prime d (neg a) a=(if d then one else zero) := by
  constructor <;> apply bit_ext <;> intro r <;> cases d <;> simp [bit_prime,saved_bit_neg,saved_bit_one,saved_bit_zero]

lemma complement_collapse (w : List Sig) (g : Gate) (h : GValid g) (a b : ℕ)
    (ne : a≠b) (ha : a∈g.inputs) (hb : b∈g.inputs)
    (ab : w.getD b zero=neg (w.getD a zero)) : collapsed w g=true := by
  obtain ⟨v,u,pins,_⟩ := h.2.2
  have pair : (v=a ∧ u=b) ∨ (v=b ∧ u=a) := by
    simp only [pins,List.mem_cons,List.not_mem_nil,or_false] at ha hb
    grind
  have op := Five18096Bypass.legal_ao g h.1 h.2.1
  apply (collapsed_iff w g).2
  obtain ⟨o,ls⟩ := g
  change ls=[v,u] at pins
  subst ls
  rcases pair with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  all_goals
    rcases op with e|e <;> change o=_ at e <;> subst o
    · change PEqualNP.Outside.L_meta_12108.Repr true _ (gv w ⟨.and,[v,u]⟩)
      rw [show gv w ⟨.and,[v,u]⟩=_ from value_two w false v u,ab]
      first | rw [(complement_laws false _).1] | rw [(complement_laws false _).2]
      exact repr_const (Or.inl rfl)
    · change PEqualNP.Outside.L_meta_12108.Repr true _ (gv w ⟨.or,[v,u]⟩)
      rw [show gv w ⟨.or,[v,u]⟩=_ from value_two w true v u,ab]
      first | rw [(complement_laws true _).1] | rw [(complement_laws true _).2]
      exact repr_const (Or.inr rfl)

lemma chargeB (anchor : List Sig) (len : 6<anchor.length)
    (z : anchor.getD 4 zero=one) (cmp : anchor.getD 6 zero=neg (anchor.getD 0 zero)) (s : List Gate)
    (valid : ∀ g∈s, GValid g) : workCost s anchor + s.countP markB ≤ s.length := by
  have result := charges anchor markB (by
    rintro w extra g rfl hg yes
    rcases Bool.or_eq_true_iff.mp yes with a|a
    · apply old_constant_pin _ _ 4 hg.1 hg.2.1 hg.2.2 (by simpa using a)
      exact Or.inr ((stable_read extra (show 4<anchor.length by omega)).trans z)
    · obtain ⟨p,q⟩ := Bool.and_eq_true_iff.mp a
      apply complement_collapse _ _ hg 0 6 (by decide) (by simpa using p) (by simpa using q)
      rw [stable_read extra len,stable_read extra (show 0<anchor.length by omega),cmp]) s valid []
  simpa using result

#print axioms chargeA
#print axioms chargeB
end FiveRestricted
