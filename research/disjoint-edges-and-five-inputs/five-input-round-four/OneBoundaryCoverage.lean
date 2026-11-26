import Atlas5And
import Atlas5Or
import Atlas6And
import Atlas6Or
import Atlas7And
import Atlas7Or
namespace FiveOne
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Finite FiveSAT FiveRoundThree FiveStrictLate
open FiveLateModel (Step)

theorem cannot_be_early (ss : List Step) (len : ss.length=6) (b : ℕ) (lo : 5≤b) (d : Bool)
    (bound : boundaryBits d (outerRow pre ss (enc b))=true) : 8≤b := by
  by_contra! low
  cases ss with
  | nil => simp at len
  | cons u1 s1 =>
    cases s1 with
    | nil => simp at len
    | cons u2 tail =>
      have h5 : outerRow pre (u1::u2::tail) (enc 5)=prefixBit [] 5 :=
        cut_suffix [] (u1::u2::tail) (by decide) (by decide) (by decide)
      have h6 : outerRow pre (u1::u2::tail) (enc 6)=prefixBit [u1] 6 :=
        cut_suffix [u1] (u2::tail) (by decide) (by simp) (by decide)
      have h7 : outerRow pre (u1::u2::tail) (enc 7)=prefixBit [u1,u2] 7 :=
        cut_suffix [u1,u2] tail (by decide) (by simp) (by decide)
      interval_cases b <;> cases d
      · rw [h5,Atlas5And.classified] at bound;contradiction
      · rw [h5,Atlas5Or.classified] at bound;contradiction
      · rw [h6,Atlas6And.classified] at bound;contradiction
      · rw [h6,Atlas6Or.classified] at bound;contradiction
      · rw [h7,Atlas7And.classified] at bound;contradiction
      · rw [h7,Atlas7Or.classified] at bound;contradiction

/-- For every qualified physical circuit with only its first gate fixed, the
outer operand in the alternating tail must be at least wire 8. -/
theorem at_least_wire_eight {C : Circuit} (h : Qualifies C) (mid : List Gate) (n q f : Gate)
    (shape : C.gates=pre++(mid++[n,q,f])) (op : n.op=.not) (hi : 5≤n.inputs.headD 0) :
    ∃ (ss : List Step) (g a b : ℕ), ss.length=6 ∧ 8≤b ∧ b<12 ∧
      (g=11 ∨ a=11 ∨ b=11) ∧
      boundaryBits (mode f) (outerRow pre ss (enc b))=true ∧
      ∀r : Row, rowPass pre ss (enc g) (enc a) (enc b) (mode f) r=true := by
  obtain ⟨ss,g,a,b,d,len,flag,_,_,_,_,lo,hiB,_,_,_,live,_,bound,rows⟩:=
    physical_filters h pre mid n q f shape op hi
  subst d
  have total:=size_exact h
  have pl : pre.length=1 := rfl
  rw [shape,List.length_append,List.length_append,pl] at total
  have six : ss.length=6 := by simp only [List.length_cons,List.length_nil] at total;omega
  exact ⟨ss,g,a,b,six,cannot_be_early ss six b lo _ bound,hiB,live,bound,rows⟩
#print axioms at_least_wire_eight
end FiveOne
