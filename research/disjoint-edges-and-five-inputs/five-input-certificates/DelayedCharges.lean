import Charges
namespace FiveRestricted
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Ends Five18096Finite

def scoreA (k : ℕ) (g : Gate) := g.inputs.contains 0 || g.inputs.contains k
def scoreB (k : ℕ) (g : Gate) := g.inputs.contains 4 || (g.inputs.contains 0 && g.inputs.contains k)

lemma postA (k : ℕ) (anchor : List Sig) (lo : 4<k) (len : k<anchor.length)
    (z : anchor.getD 0 zero=zero) (u : anchor.getD k zero=one) (s : List Gate)
    (valid : ∀ g∈s, GValid g) : workCost s anchor + s.countP (scoreA k) ≤ s.length := by
  have result := charges anchor (scoreA k) (by
    rintro w extra g rfl hg yes
    rcases Bool.or_eq_true_iff.mp yes with a|a
    · apply old_constant_pin _ _ 0 hg.1 hg.2.1 hg.2.2 (by simpa using a)
      exact Or.inl ((stable_read extra (show 0<anchor.length by omega)).trans z)
    · apply old_constant_pin _ _ k hg.1 hg.2.1 hg.2.2 (by simpa using a)
      exact Or.inr ((stable_read extra len).trans u)) s valid []
  simpa using result

lemma postB (k : ℕ) (anchor : List Sig) (lo : 4<k) (len : k<anchor.length)
    (z : anchor.getD 4 zero=one) (cmp : anchor.getD k zero=neg (anchor.getD 0 zero)) (s : List Gate)
    (valid : ∀ g∈s, GValid g) : workCost s anchor + s.countP (scoreB k) ≤ s.length := by
  have result := charges anchor (scoreB k) (by
    rintro w extra g rfl hg yes
    rcases Bool.or_eq_true_iff.mp yes with a|a
    · apply old_constant_pin _ _ 4 hg.1 hg.2.1 hg.2.2 (by simpa using a)
      exact Or.inr ((stable_read extra (show 4<anchor.length by omega)).trans z)
    · obtain ⟨u,v⟩ := Bool.and_eq_true_iff.mp a
      apply complement_collapse _ _ hg 0 k (by omega) (by simpa using u) (by simpa using v)
      rw [stable_read extra len,stable_read extra (show 0<anchor.length by omega),cmp]) s valid []
  simpa using result

def readJ (j : ℕ) (g : Gate) := g.inputs.contains j
lemma preCharge (anchor : List Sig) (j : ℕ) (len : j<anchor.length)
    (fix : anchor.getD j zero=zero ∨ anchor.getD j zero=one) (m : List Gate)
    (valid : ∀ g∈m,GValid g) : workCost m anchor + m.countP (readJ j) ≤ m.length := by
  have result := charges anchor (readJ j) (by
    rintro w extra g rfl hg yes
    apply old_constant_pin _ _ j hg.1 hg.2.1 hg.2.2 (by simpa [readJ] using yes)
    rw [stable_read extra len]
    exact fix) m valid []
  simpa using result

def firstAnd (rev : Bool) : Gate := ⟨.and,if rev then [4,0] else [0,4]⟩
def invertFirst (noise : List ℕ) : Gate := ⟨.not, 5::noise⟩
def startW (c : SCase) (rev : Bool) := execute [firstAnd rev] (restrictedW c)
def beforeN (c : SCase) (rev : Bool) (m : List Gate) := execute m (startW c rev)
def afterN (c : SCase) (rev : Bool) (m : List Gate) (noise : List ℕ) :=
  let w := beforeN c rev m
  w++[gv w (invertFirst noise)]

lemma read_before {c : SCase} {rev : Bool} (m : List Gate) (i : ℕ)
    (sm : i<(startW c rev).length) : (beforeN c rev m).getD i zero=(startW c rev).getD i zero := by
  obtain ⟨t,eq⟩ := execute_extends m (startW c rev)
  exact (by rw [beforeN,eq,stable_read t sm])

lemma before_len {c : SCase} {rev : Bool} (m : List Gate) (l : (startW c rev).length=6) :
    (beforeN c rev m).length=6+m.length := by simp [beforeN,execute_len,l]

lemma read_new {c : SCase} {rev : Bool} (m : List Gate) (noise : List ℕ) (l : (startW c rev).length=6) :
    (afterN c rev m noise).getD (6+m.length) zero = neg ((startW c rev).getD 5 zero) := by
  rw [←before_len m l, afterN,List.getD_eq_getElem?_getD,List.getElem?_append_right (le_refl _)]
  simp only [Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
  change neg ((beforeN c rev m).getD 5 zero) = neg ((startW c rev).getD 5 zero)
  rw [read_before m 5 (by omega)]

lemma read_through {c : SCase} {rev : Bool} (m : List Gate) (noise : List ℕ) (l : (startW c rev).length=6)
    (j : ℕ) (sm : j<6) : (afterN c rev m noise).getD j zero = (startW c rev).getD j zero := by
  have length := before_len m l
  rw [afterN,stable_read _ (show j<(beforeN c rev m).length by omega),read_before m j (by omega)]

lemma after_len {c : SCase} {rev : Bool} (m : List Gate) (noise : List ℕ) (l : (startW c rev).length=6) :
    6+m.length < (afterN c rev m noise).length := by simp [afterN,before_len m l]

lemma prepaid {C : Circuit} (h : Qualifies C) (m s : List Gate) (rev : Bool) (noise : List ℕ)
    (sp : C.gates=firstAnd rev::(m++invertFirst noise::s)) {c : SCase} (hc : c∈cofs)
    (spent : workCost [firstAnd rev] (restrictedW c)=0) :
    c.L ≤ workCost m (startW c rev) + workCost s (afterN c rev m noise) := by
  have lo := cofactor_lower h hc
  have shape : C.gates=[firstAnd rev]++(m++invertFirst noise::s) := sp
  rw [shape,cost_append,spent,Nat.zero_add,cost_append] at lo
  simpa [startW,afterN,beforeN,workCost,invertFirst,isNot] using lo

#print axioms prepaid
end FiveRestricted
