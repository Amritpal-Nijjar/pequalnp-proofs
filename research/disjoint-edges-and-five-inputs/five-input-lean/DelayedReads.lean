import DelayedCharges
import Touches
namespace FiveRestricted
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Ends Five18096Bypass Five18096Finite

def agreeCheck (w : List Sig) (j : ℕ) (r t : Row) :=
  (List.range w.length).all fun k => k==j || bit r (w.getD k zero)==bit t (w.getD k zero)
lemma agree_of_check (w : List Sig) (j : ℕ) (r t : Row) (ok : agreeCheck w j r t=true) :
    AgreeOff j (w.map (bit r)) (w.map (bit t)) := by
  refine ⟨by simp,?_⟩
  intro k ne
  rw [Five18096Paths.bits_at,Five18096Paths.bits_at]
  by_cases small : k<w.length
  · simpa [ne] using List.all_eq_true.mp ok k (List.mem_range.mpr small)
  · have none : w[k]?=none := List.getElem?_eq_none (by omega)
    simp [List.getD_eq_getElem?_getD,none,saved_bit_zero]

lemma delayed_required {C : Circuit} (h : Qualifies C) (rev : Bool) (noise : List ℕ) (m s : List Gate)
    (sp : C.gates=firstAnd rev::(m++invertFirst noise::s)) (j : ℕ) (r t : Row) (different : bit r fiveGraph≠bit t fiveGraph)
    (oj : C.output ≠ j) (skip : 5≠j)
    (ok : agreeCheck (execute [firstAnd rev] fiveInputs) j r t=true) : ∃g∈m++s, j∈g.inputs := by
  by_contra! none
  let w := execute [firstAnd rev] fiveInputs
  have base := agree_of_check w j r t ok
  let a := phys m (w.map (bit r))
  let b := phys m (w.map (bit t))
  have mid : AgreeOff j a b := unread_off m j _ _ base (fun g hg => none g (by simp [hg]))
  have at5 := mid.2 5 skip
  have gate (v : List Bool) : (invertFirst noise).op.eval ((invertFirst noise).inputs.map fun i => v.getD i false) =
      !(v.getD 5 false) := rfl
  have propagated := unread_off s j (a++[!(a.getD 5 false)]) (b++[!(b.getD 5 false)])
    (by rw [at5]; exact snoc_off mid _) (fun g hg => none g (by simp [hg]))
  have physical (q : Row) : phys s (phys m (w.map (bit q)) ++ [!((phys m (w.map (bit q))).getD 5 false)]) =
      (execute C.gates fiveInputs).map (bit q) := by
    have eq : C.gates=[firstAnd rev]++(m++invertFirst noise::s) := sp
    rw [eq,execute_append]
    rw [saved_execute_bits (m++invertFirst noise::s) q w (fun g hg => (h.legal g (by simp [eq,hg])).1)]
    change _ = phys (m++invertFirst noise::s) (w.map (bit q))
    simp only [phys,List.foldl_append,List.foldl_cons]
    rfl
  have diff := propagated.2 C.output oj
  change (phys s (phys m (w.map (bit r))++[_])).getD _ _ = (phys s (phys m (w.map (bit t))++[_])).getD _ _ at diff
  rw [physical r,physical t,Five18096Paths.bits_at,Five18096Paths.bits_at,
      computed_sig C h.legal h.computes] at diff
  exact different diff

theorem delayed_reads {C : Circuit} (h : Qualifies C) (rev : Bool) (noise : List ℕ) (m s : List Gate)
    (sp : C.gates=firstAnd rev::(m++invertFirst noise::s)) :
    (∃ g∈m++s, 0∈g.inputs) ∧ (∃ g∈m++s, 4∈g.inputs) ∧ (∃ g∈s, 6+m.length∈g.inputs) := by
  have out := final_output h
  refine ⟨delayed_required h rev noise m s sp 0 2 3 (by decide +kernel) (by omega) (by decide)
    (by cases rev <;> decide +kernel), delayed_required h rev noise m s sp 4 6 22
    (by decide +kernel) (by omega) (by decide) (by cases rev <;> decide +kernel),?_⟩
  let p := firstAnd rev::m
  have e : C.gates=p++invertFirst noise::s := sp
  have pos := not_position C h.legal h.cap h.computes h.back h.used p s (invertFirst noise) e rfl (by change 5≤5; decide)
  have length : p.length=m.length+1 := rfl
  have size : C.size=p.length+(s.length+1) := by simp [Circuit.size,e]
  obtain eq|⟨i,hi,gt,pin⟩ := h.used p.length (by omega)
  · omega
  · have small : i-(p++[invertFirst noise]).length<s.length := by simp; omega
    have shape : C.gates=(p++[invertFirst noise])++s := by simpa [List.append_assoc] using e
    have actual : C.gates.getD i ⟨.and,[]⟩=s[i-(p++[invertFirst noise]).length] := by
      rw [shape,List.getD_eq_getElem?_getD,List.getElem?_append_right (show (p++[invertFirst noise]).length ≤ i by simp; omega),
        List.getElem?_eq_getElem small]; rfl
    rw [actual,show 5+p.length=6+m.length by omega] at pin
    exact ⟨_,List.getElem_mem small,pin⟩

#print axioms delayed_reads
end FiveRestricted
