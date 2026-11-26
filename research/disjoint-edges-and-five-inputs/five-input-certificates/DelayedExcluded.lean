import DelayedReads
import Excluded
namespace FiveRestricted
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Ends Five18096Finite

lemma later_read {j : ℕ} (m s : List Gate) (whole : ∃g∈m++s,j∈g.inputs)
    (none : m.countP (readJ j)=0) : ∃g∈s,j∈g.inputs := by
  obtain ⟨g,hg,hit⟩ := whole
  rcases List.mem_append.mp hg with early|late
  · have hm := List.countP_eq_zero.mp none g early
    simp [readJ,hit] at hm
  · exact ⟨g,late,hit⟩

lemma exclusive_reads (k : ℕ) (big : 4<k) (m s : List Gate) (valid : ∀ g∈s,GValid g)
    (aa : m.countP (readJ 0)+s.countP (scoreA k) ≤ 1)
    (bb : m.countP (readJ 4)+s.countP (scoreB k) ≤ 1)
    (r0 : ∃g∈m++s,0∈g.inputs) (r4 : ∃g∈m++s,4∈g.inputs) (rk : ∃g∈s,k∈g.inputs) : False := by
  obtain ⟨v,hv,pk⟩ := rk
  have yes : scoreA k v=true := by simp [scoreA,pk]
  have pos : 0<s.countP (scoreA k) := List.countP_pos_iff.mpr ⟨v,hv,yes⟩
  obtain ⟨a,ha,p0⟩ := later_read m s r0 (by omega)
  have av := unique_mark s (scoreA k) (by omega) ha hv (by simp [scoreA,p0]) yes
  subst v
  have yes' : scoreB k a=true := by simp [scoreB,p0,pk]
  have pos' : 0<s.countP (scoreB k) := List.countP_pos_iff.mpr ⟨a,ha,yes'⟩
  obtain ⟨b,hb,p4⟩ := later_read m s r4 (by omega)
  have ba := unique_mark s (scoreB k) (by omega) hb ha (by simp [scoreB,p4]) yes'
  subst b
  obtain ⟨i,j,pins,_⟩ := (valid a ha).2.2
  simp only [pins,List.mem_cons,List.not_mem_nil,or_false] at p0 p4 pk
  omega

theorem no_delayed_not_of_first_and {C : Circuit} (h : Qualifies C) (rev : Bool) (noise : List ℕ) (m s : List Gate)
    (sp : C.gates=firstAnd rev::(m++invertFirst noise::s)) : False := by
  let cA : SCase := ⟨0,false,p5_T,7⟩
  let cB : SCase := ⟨4,true,p7_T,7⟩
  have lA : (startW cA rev).length=6 := by cases rev <;> decide +kernel
  have lB : (startW cB rev).length=6 := by cases rev <;> decide +kernel
  have count := (exactCounts C h.legal h.cap h.computes h.internal).2.1
  have nn := no_other_not C (firstAnd rev::m) s (invertFirst noise) sp rfl count
  have valid (g) (hg : g∈m++s) : GValid g := by
    have non : isNot g=false := by
      rcases List.mem_append.mp hg with hm|hs
      · exact nn.1 g (by simp [hm])
      · exact nn.2 g hs
    have all : g∈C.gates := by
      rcases List.mem_append.mp hg with hm|hs
      · simp [sp,hm]
      · simp [sp,hs]
    exact ⟨(h.legal g all).1,non,(filters h).binary g all non⟩
  have vm g (hg : g∈m) := valid g (by simp [hg])
  have vs g (hg : g∈s) := valid g (by simp [hg])
  have ca := prepaid h m s rev noise sp (c:=cA) (by decide +kernel) (by cases rev <;> decide +kernel)
  have cb := prepaid h m s rev noise sp (c:=cB) (by decide +kernel) (by cases rev <;> decide +kernel)
  have a0 : (startW cA rev).getD 0 zero=zero := by cases rev <;> decide +kernel
  have a5 : (startW cA rev).getD 5 zero=zero := by cases rev <;> decide +kernel
  have b4 : (startW cB rev).getD 4 zero=one := by cases rev <;> decide +kernel
  have b5 : (startW cB rev).getD 5 zero=(startW cB rev).getD 0 zero := by cases rev <;> decide +kernel
  have pa := preCharge (startW cA rev) 0 (by omega) (Or.inl a0) m vm
  have pb := preCharge (startW cB rev) 4 (by omega) (Or.inr b4) m vm
  have sa := postA (6+m.length) (afterN cA rev m noise) (by omega) (after_len m noise lA)
    ((read_through m noise lA 0 (by decide)).trans a0) (by rw [read_new m noise lA,a5]; exact saved_neg_laws.1) s vs
  have sb := postB (6+m.length) (afterN cB rev m noise) (by omega) (after_len m noise lB)
    ((read_through m noise lB 4 (by decide)).trans b4) (by rw [read_new m noise lB,b5,read_through m noise lB 0 (by decide)]) s vs
  have sz := size_exact h
  simp only [sp,List.length_cons,List.length_append] at sz
  obtain ⟨r0,r4,rk⟩ := delayed_reads h rev noise m s sp
  change 7≤_ at ca cb
  exact exclusive_reads _ (by omega) m s vs (by omega) (by omega) r0 r4 rk

#print axioms no_delayed_not_of_first_and
end FiveRestricted
