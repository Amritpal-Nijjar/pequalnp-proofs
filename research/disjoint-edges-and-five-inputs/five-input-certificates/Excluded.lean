import Touches
import Charges
namespace FiveRestricted
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Ends Five18096Finite

lemma unique_mark {α : Type} (s : List α) (m : α→Bool) (small : s.countP m≤1)
    {a b : α} (ha : a∈s) (hb : b∈s) (ma : m a=true) (mb : m b=true) : a=b := by
  have ea := List.mem_filter.mpr ⟨ha,ma⟩
  have eb := List.mem_filter.mpr ⟨hb,mb⟩
  rw [List.countP_eq_length_filter] at small
  cases q : s.filter m with
  | nil => simp [q] at ea
  | cons c xs =>
    cases xs with
    | nil => rw [q,List.mem_singleton] at ea eb; exact ea.trans eb.symm
    | cons v vs => simp [q] at small

lemma missing_mark (s : List Gate) (valid : ∀ g∈s,GValid g)
    (aa : s.countP markA≤1) (bb : s.countP markB≤1)
    (r0 : ∃ g∈s, 0∈g.inputs) (r4 : ∃ g∈s, 4∈g.inputs) (r6 : ∃ g∈s, 6∈g.inputs) : False := by
  obtain ⟨a,ha,i0⟩ := r0
  obtain ⟨b,hb,i4⟩ := r4
  obtain ⟨d,hd,i6⟩ := r6
  have ad : a=d := unique_mark s markA aa ha hd (by simp [markA,i0]) (by simp [markA,i6])
  subst d
  have ab : a=b := unique_mark s markB bb ha hb (by simp [markB,i0,i6]) (by simp [markB,i4])
  subst b
  obtain ⟨j,k,pins,_⟩ := (valid a ha).2.2
  simp only [pins,List.mem_cons,List.not_mem_nil,or_false] at i0 i4 i6
  omega

/-- This complete first-gate and inverter-position branch is impossible. No
assumptions are placed on the following eight gates. -/
theorem no_first_and_then_not {C : Circuit} (h : Qualifies C) (rev : Bool) (noise : List ℕ)
    (s : List Gate) (sp : C.gates=firstPair rev noise++s) : False := by
  let p := firstPair rev noise
  let cA : SCase := ⟨0,false,p5_T,7⟩
  let cB : SCase := ⟨4,true,p7_T,7⟩
  let wa := execute p (restrictedW cA)
  let wb := execute p (restrictedW cB)
  have length := size_exact h
  have n : s.length=8 := by simp only [sp,firstPair,List.length_append,List.length_cons,List.length_nil] at length; omega
  have ncount := (exactCounts C h.legal h.cap h.computes h.internal).2.1
  have zeroNot : s.countP isNot=0 := by
    rw [sp,List.countP_append] at ncount
    have count : (firstPair rev noise).countP isNot=1 := rfl
    omega
  have valid (g) (hg : g∈s) : GValid g := by
    have hm : g∈C.gates := by simp [sp,hg]
    have nn : isNot g=false := by simpa using List.countP_eq_zero.mp zeroNot g hg
    exact ⟨(h.legal g hm).1,nn,(filters h).binary g hm nn⟩
  have a := cofactor_lower h (c:=cA) (by decide +kernel)
  have b := cofactor_lower h (c:=cB) (by decide +kernel)
  rw [sp,cost_append] at a b
  have az : workCost (firstPair rev noise) (restrictedW cA)=0 := by
    change workCost (firstPair rev []) (restrictedW cA)=0
    cases rev <;> decide +kernel
  have bz : workCost (firstPair rev noise) (restrictedW cB)=0 := by
    change workCost (firstPair rev []) (restrictedW cB)=0
    cases rev <;> decide +kernel
  rw [az,Nat.zero_add] at a
  rw [bz,Nat.zero_add] at b
  change 7≤workCost s wa at a
  change 7≤workCost s wb at b
  have eA : wa = execute (firstPair rev []) (restrictedW cA) := rfl
  have eB : wb = execute (firstPair rev []) (restrictedW cB) := rfl
  have ca := chargeA wa (by rw [eA]; cases rev <;> decide +kernel)
    (by rw [eA]; cases rev <;> decide +kernel) (by rw [eA]; cases rev <;> decide +kernel) s valid
  have cb := chargeB wb (by rw [eB]; cases rev <;> decide +kernel)
    (by rw [eB]; cases rev <;> decide +kernel) (by rw [eB]; cases rev <;> decide +kernel) s valid
  obtain ⟨r0,r4,r6⟩ := three_reads h rev noise s sp
  apply missing_mark s valid (by omega) (by omega) r0 r4 r6

#print axioms no_first_and_then_not
end FiveRestricted
