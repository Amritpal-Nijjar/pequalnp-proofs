import Canonical
namespace FiveRestricted
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Ends Five18096Finite

def oneHot (i : Fin 5) : Row := Fin.ofNat 128 (2^i.val)
def oneCold (i : Fin 5) : Row := Fin.ofNat 128 (31-2^i.val)
lemma extreme_tests : ∀ i : Fin 5,
    bit (oneHot i) fiveGraph = false ∧ bit (oneHot i) (fiveInputs.getD i.val zero) = true ∧
    bit (oneCold i) fiveGraph = true ∧ bit (oneCold i) (fiveInputs.getD i.val zero) = false := by decide +kernel

lemma final_ordinary {C : Circuit} (h : Qualifies C) (p : List Gate) (f : Gate) (sp : C.gates=p++[f]) :
    isNot f=false := by
  cases nn : isNot f with
  | false => rfl
  | true =>
    have op : f.op=.not := by obtain ⟨o,l⟩:=f; cases o <;> simp_all [isNot]
    have other := (no_other_not C p [] f sp op (exactCounts C h.legal h.cap h.computes h.internal).2.1).1
    obtain ⟨q,hq,n,hi⟩ := h.internal
    rw [sp] at hq
    rcases List.mem_append.mp hq with before|last
    · have e := other q before
      simp [isNot,n] at e
    · obtain rfl := List.mem_singleton.mp last
      exact (not_cannot_be_output C h.legal h.cap h.computes h.back h.used p q sp n hi).elim

/-- The last binary gate cannot have any of the five raw inputs on either pin.
The ten boundary row tests below are independent of the rest of the wiring. -/
theorem no_input_at_output {C : Circuit} (h : Qualifies C) (p : List Gate) (f : Gate) (sp : C.gates=p++[f])
    (j : ℕ) (pin : j∈f.inputs) : 5 ≤ j := by
  by_contra! small
  let i : Fin 5 := ⟨j,small⟩
  let w := execute p fiveInputs
  obtain ⟨t,et⟩ := execute_extends p fiveInputs
  have kept : w.getD j zero = fiveInputs.getD j zero := by
    change (execute p fiveInputs).getD j zero=_
    rw [et,stable_read t (show j<fiveInputs.length from small)]
  obtain ⟨e0,p1,e1,p0⟩ := extreme_tests i
  have nn := final_ordinary h p f sp
  have mem : f∈C.gates := by simp [sp]
  obtain ⟨a,b,pins,_⟩ := (filters h).binary f mem nn
  have op := Five18096Bypass.legal_ao f (h.legal f mem).1 nn
  have clause := value_last C h.legal h.computes h.used p f sp
  have ab : j=a ∨ j=b := by simpa [pins] using pin
  obtain ⟨o,ls⟩ := f
  change ls=[a,b] at pins
  subst ls
  rcases op with ho|ho <;> change o=_ at ho <;> subst o
  · change gv w ⟨.and,[a,b]⟩=fiveGraph at clause
    rw [show gv w ⟨.and,[a,b]⟩=_ from value_two w false a b] at clause
    have row := congrArg (bit (oneCold i)) clause
    have x : bit (oneCold i) (w.getD j zero)=false := kept ▸ p0
    rcases ab with rfl|rfl <;>
      simp only [bit_prime,Bool.false_eq_true,↓reduceIte,x,e1,Bool.false_and,Bool.and_false] at row
  · change gv w ⟨.or,[a,b]⟩=fiveGraph at clause
    rw [show gv w ⟨.or,[a,b]⟩=_ from value_two w true a b] at clause
    have row := congrArg (bit (oneHot i)) clause
    have x : bit (oneHot i) (w.getD j zero)=true := kept ▸ p1
    rcases ab with rfl|rfl <;>
      simp only [bit_prime,↓reduceIte,x,e0,Bool.true_or,Bool.or_true,Bool.true_eq_false] at row

#print axioms no_input_at_output
end FiveRestricted
