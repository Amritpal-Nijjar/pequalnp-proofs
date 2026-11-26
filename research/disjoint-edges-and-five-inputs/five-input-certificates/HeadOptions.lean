import FirstGate
namespace FiveRestricted
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Ends Five18096Finite

abbrev FirstKey := Bool × ℕ × ℕ
def options : List FirstKey :=
  [false,true].flatMap fun d => (List.range 5).flatMap fun a => (List.range 5).filterMap fun b =>
    if a<b ∧ ¬(d=false ∧ a=0 ∧ b=4) then some (d,a,b) else none

theorem nineteen : options.length=19 ∧ options.Nodup := by decide +kernel

def optionKey (g : Gate) : Option FirstKey :=
  match g.op,g.inputs with
  | .and,[a,b] => some (false,min a b,max a b)
  | .or,[a,b] => some (true,min a b,max a b)
  | _,_ => none

def firstAllowed (C : Circuit) : Bool :=
  match C.gates.head?.bind optionKey with
  | some k => options.contains k
  | none => false

lemma in_options (d : Bool) (a b : ℕ) (ab : a<b) (b5 : b<5) (ok : ¬(d=false ∧ a=0 ∧ b=4)) :
    (d,a,b)∈options := by
  apply List.mem_flatMap.mpr
  refine ⟨d,by cases d <;> simp,List.mem_flatMap.mpr ⟨a,List.mem_range.mpr (by omega),?_⟩⟩
  exact List.mem_filterMap.mpr ⟨b,List.mem_range.mpr b5,by simp [ab,ok]⟩

lemma first_ordinary {C : Circuit} (h : Qualifies C) (g : Gate) (s : List Gate) (sp : C.gates=g::s) :
    isNot g=false := by
  cases ng : isNot g with
  | false => rfl
  | true =>
    have op : g.op=.not := by obtain ⟨o,l⟩:=g; cases o <;> simp_all [isNot]
    obtain ⟨n,hn,hnop,hi⟩ := h.internal
    have nt : isNot n=true := by simp [isNot,hnop]
    have other := (no_other_not C [] s g sp op (exactCounts C h.legal h.cap h.computes h.internal).2.1).2
    rw [sp,List.mem_cons] at hn
    rcases hn with rfl|hm
    · have mem : n.inputs.headD 0 ∈ n.inputs := by
        cases eq : n.inputs with
        | nil => simp [eq] at hi
        | cons a t => simp
      have back := h.back 0 (by simp [sp]) (n.inputs.headD 0) (by simpa [NestedCover.gateAt,sp] using mem)
      omega
    · rw [other n hm] at nt; cases nt

theorem first_among_nineteen {C : Circuit} (h : Qualifies C) : firstAllowed C=true := by
  cases sp : C.gates with
  | nil => have sz:=size_exact h; simp [sp] at sz
  | cons g s =>
    have ng := first_ordinary h g s sp
    have hm : g∈C.gates := by simp [sp]
    obtain ⟨a,b,pins,ne⟩ := (filters h).binary g hm ng
    have bounds (i) (q : i∈g.inputs) : i<5 := by
      have x := h.back 0 (by simp [sp]) i (by simpa [NestedCover.gateAt,sp] using q)
      simpa using x
    have a5 := bounds a (by simp [pins])
    have b5 := bounds b (by simp [pins])
    have op := Five18096Bypass.legal_ao g (h.legal g hm).1 ng
    obtain ⟨o,ls⟩ := g
    change ls=[a,b] at pins
    subst ls
    have bad (rev : Bool) (z : (⟨o,[a,b]⟩ : Gate)=firstAnd rev) : False :=
      no_first_and_04 h rev s (z ▸ sp)
    rcases op with ho|ho <;> change o=_ at ho <;> subst o
    · have off : ¬(min a b=0 ∧ max a b=4) := by
        intro z
        rcases Nat.lt_or_gt_of_ne ne with ab|ba
        · rw [Nat.min_eq_left (by omega),Nat.max_eq_right (by omega)] at z
          obtain ⟨rfl,rfl⟩ := z
          exact bad false rfl
        · rw [Nat.min_eq_right (by omega),Nat.max_eq_left (by omega)] at z
          obtain ⟨rfl,rfl⟩ := z
          exact bad true rfl
      have hmin : min a b < max a b := by omega
      have yes := in_options false _ _ hmin (by omega) (fun h => off h.2)
      simpa [firstAllowed,optionKey,sp] using yes
    · have hmin : min a b < max a b := by omega
      have yes := in_options true _ _ hmin (by omega) (by simp)
      simpa [firstAllowed,optionKey,sp] using yes

#print axioms first_among_nineteen
end FiveRestricted
