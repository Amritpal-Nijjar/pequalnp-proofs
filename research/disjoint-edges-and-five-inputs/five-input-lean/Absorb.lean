import DelayedCharges
namespace FiveRestricted
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Ends Five18096Finite

def binaryRead (i j : ℕ) (g : Gate) := !isNot g && (g.inputs.contains i || g.inputs.contains j)

lemma marked_while (anchor : List Sig) (mark : Gate→Bool) (zeroNot : ∀g, isNot g=true → mark g=false)
    (old : ∀ w extra g, w=anchor++extra → GValid g → mark g=true → collapsed w g=true)
    (s : List Gate) (legal : ∀g∈s, isNot g=false → GValid g) (extra : List Sig) :
    workCost s (anchor++extra) + s.countP mark ≤ s.countP (fun g => !isNot g) := by
  induction s generalizing extra with
  | nil => simp [workCost]
  | cons g s ih =>
    let w := anchor++extra
    have tail := ih (fun a ha => legal a (by simp [ha])) (extra++[gv w g])
    change _ + workCost s (w++[gv w g]) + _ ≤ _
    rw [show w++[gv w g] = anchor++(extra++[gv w g]) from List.append_assoc ..]
    cases nn : isNot g with
    | true =>
      have z := zeroNot g nn
      simpa [w,nn,z,List.countP_cons] using tail
    | false =>
      cases sc : mark g with
      | true =>
        have v := old w extra g rfl (legal g (by simp) nn) sc
        simp [List.countP_cons,sc,v,nn,w] at *
        omega
      | false => cases c : collapsed w g <;> simp [List.countP_cons,sc,c,nn,w] at * <;> omega

theorem at_most_one_use {C : Circuit} (h : Qualifies C) (rev : Bool) (s : List Gate) (sp : C.gates=firstAnd rev::s) :
    s.countP (binaryRead 0 5) ≤ 1 := by
  let c : SCase := ⟨0,false,p5_T,7⟩
  let anchor := startW c rev
  have za : anchor.getD 0 zero=zero := by cases rev <;> decide +kernel
  have zb : anchor.getD 5 zero=zero := by cases rev <;> decide +kernel
  have len : anchor.length=6 := by cases rev <;> decide +kernel
  have charge := marked_while anchor (binaryRead 0 5) (by intro g n; simp [binaryRead,n]) (by
    rintro w extra g rfl hg yes
    obtain ⟨_,read⟩ := Bool.and_eq_true_iff.mp yes
    rcases Bool.or_eq_true_iff.mp read with a|b
    · apply old_constant_pin _ _ 0 hg.1 hg.2.1 hg.2.2 (by simpa using a)
      exact Or.inl ((stable_read extra (show 0<anchor.length by omega)).trans za)
    · apply old_constant_pin _ _ 5 hg.1 hg.2.1 hg.2.2 (by simpa using b)
      exact Or.inl ((stable_read extra (show 5<anchor.length by omega)).trans zb)) s (by
    intro g hg nn
    have mem : g∈C.gates := by simp [sp,hg]
    exact ⟨(h.legal g mem).1,nn,(filters h).binary g mem nn⟩) []
  have lower := cofactor_lower h (c:=c) (by decide +kernel)
  have pre : C.gates=[firstAnd rev]++s := sp
  have free : workCost [firstAnd rev] (restrictedW c)=0 := by cases rev <;> decide +kernel
  rw [pre,cost_append,free,Nat.zero_add] at lower
  change 7 ≤ workCost s anchor at lower
  rw [List.append_nil] at charge
  have total := (exactCounts C h.legal h.cap h.computes h.internal).2.2
  have nn : isNot (firstAnd rev)=false := rfl
  simp only [sp,List.countP_cons,nn,Bool.not_false, ↓reduceIte] at total
  omega

lemma absorption (d : Bool) (a c : Sig) :
    prime d a (prime false a c)=(if d then a else prime false a c) ∧
    prime d (prime false a c) a=(if d then a else prime false a c) := by
  constructor <;> apply bit_ext <;> intro r <;> cases d <;> simp only [bit_prime,Bool.false_eq_true, ↓reduceIte]
  all_goals cases bit r a <;> simp

lemma pair_old (w : List Sig) (g : Gate) (h : GValid g) (p0 : 0∈g.inputs) (p5 : 5∈g.inputs)
    (relation : w.getD 5 zero=prime false (w.getD 0 zero) (w.getD 4 zero)) : Old w g := by
  obtain ⟨a,b,pins,_⟩ := h.2.2
  have pair : (a=0 ∧ b=5) ∨ (a=5 ∧ b=0) := by
    simp only [pins,List.mem_cons,List.not_mem_nil,or_false] at p0 p5
    omega
  have op := Five18096Bypass.legal_ao g h.1 h.2.1
  have raw := saved_get_rep (u:=true) w 0
  have first := saved_get_rep (u:=true) w 5
  obtain ⟨o,ls⟩ := g
  change ls=[a,b] at pins
  subst ls
  rcases op with ho|ho <;> change o=_ at ho <;> subst o
  · change PEqualNP.Outside.L_meta_12108.Repr true _ (gv w ⟨.and,[a,b]⟩)
    rw [show gv w ⟨.and,[a,b]⟩=_ from value_two w false a b]
    rcases pair with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> rw [relation] <;>
      first | rw [(absorption false _ _).1,←relation]; exact first |
              rw [(absorption false _ _).2,←relation]; exact first
  · change PEqualNP.Outside.L_meta_12108.Repr true _ (gv w ⟨.or,[a,b]⟩)
    rw [show gv w ⟨.or,[a,b]⟩=_ from value_two w true a b]
    rcases pair with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> rw [relation] <;>
      first | rw [(absorption true _ _).1]; exact raw | rw [(absorption true _ _).2]; exact raw

lemma never_both {C : Circuit} (h : Qualifies C) (rev : Bool) (s : List Gate) (sp : C.gates=firstAnd rev::s) :
    ∀g∈s, isNot g=false → 0∈g.inputs → 5∉g.inputs := by
  intro g hg nn p0 p5
  obtain ⟨m,t,hs⟩ := List.append_of_mem hg
  let anchor := execute [firstAnd rev] fiveInputs
  let w := execute m anchor
  have full := (filters h).fresh
  have shape : C.gates=[firstAnd rev]++(m++g::t) := by simpa [hs] using sp
  rw [shape] at full
  have fr := (run_split m (g::t) anchor (run_split [firstAnd rev] _ fiveInputs full).2).2.1 nn
  have mem : g∈C.gates := by simp [sp,hg]
  apply fr
  apply pair_old w g ⟨(h.legal g mem).1,nn,(filters h).binary g mem nn⟩ p0 p5
  obtain ⟨extra,eq⟩ := execute_extends m anchor
  have len : anchor.length=6 := by cases rev <;> decide +kernel
  have rel : anchor.getD 5 zero=prime false (anchor.getD 0 zero) (anchor.getD 4 zero) := by cases rev <;> decide +kernel
  rw [show w=anchor++extra from eq,stable_read extra (show 5<anchor.length by omega),
    stable_read extra (show 0<anchor.length by omega),stable_read extra (show 4<anchor.length by omega),rel]

#print axioms at_most_one_use
#print axioms never_both
end FiveRestricted
