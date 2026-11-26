import DelayedExcluded
import Effective
import Absorb
namespace FiveRestricted
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Ends Five18096Finite

lemma inverted_pin (g : Gate) (n : g.op=.not) (k : ℕ) (e : k ∈ effective g) : g.inputs.headD 0 = k := by
  obtain ⟨o,l⟩ := g
  change o=.not at n
  subst o
  cases l with
  | nil => simp [effective,isNot] at e
  | cons a r => simpa [effective,isNot,eq_comm] using e

/-- A witness for the desk row cannot start by ANDing raw inputs 0 and 4.
The inverter and all other gates can be anywhere legal, on any wires. -/
theorem no_first_and_04 {C : Circuit} (h : Qualifies C) (rev : Bool) (tail : List Gate)
    (sp : C.gates=firstAnd rev::tail) : False := by
  have endWire := final_output h
  obtain ⟨n,hn,op,headBound⟩ := h.internal
  have nTail : n∈tail := by
    rw [sp,List.mem_cons] at hn
    rcases hn with rfl|other
    · cases op
    · exact other
  obtain ⟨m,s,tailSplit⟩ := List.append_of_mem nTail
  have form : C.gates=(firstAnd rev::m)++n::s := by simpa [tailSplit] using sp
  have count := (exactCounts C h.legal h.cap h.computes h.internal).2.1
  have other := no_other_not C (firstAnd rev::m) s n form op count
  have other_nn {g : Gate} (inTail : g∈tail) (different : g≠n) : isNot g=false := by
    rw [tailSplit] at inTail
    rcases List.mem_append.mp inTail with early|late
    · exact other.1 g (by simp [early])
    · rcases List.mem_cons.mp late with eq|hs
      · exact (different eq).elim
      · exact other.2 g hs
  obtain ⟨g,hg,p0⟩ := effective_required h [firstAnd rev] tail sp 0 2 3 (by decide +kernel) (by omega)
    (agree_of_check _ _ _ _ (by cases rev <;> decide +kernel))
  have gn : g≠n := by
    rintro rfl
    have eq := inverted_pin g op 0 p0
    omega
  have ng := other_nn hg gn
  have gp : 0∈g.inputs := by simpa [effective,ng] using p0
  obtain ⟨q,hq,p5⟩ := first_required h (firstAnd rev) tail sp rfl
  by_cases qn : q=n
  · subst q
    have k := inverted_pin n op 5 p5
    obtain ⟨o,l⟩ := n
    change o=.not at op
    subst o
    cases l with
    | nil => cases k
    | cons i noise =>
      change i=5 at k
      subst i
      exact no_delayed_not_of_first_and h rev noise m s form
  · have nn := other_nn hq qn
    have qp : 5∈q.inputs := by simpa [effective,nn] using p5
    have small := at_most_one_use h rev tail sp
    have eq := unique_mark tail (binaryRead 0 5) small hg hq
      (by simp [binaryRead,ng,gp]) (by simp [binaryRead,nn,qp])
    subst q
    exact never_both h rev tail sp g hg ng gp qp

#print axioms no_first_and_04
end FiveRestricted
