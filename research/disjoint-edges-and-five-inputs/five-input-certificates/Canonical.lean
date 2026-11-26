import RealUse
namespace FiveRestricted
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Ends Five18096Bypass Five18096Finite

def trimGate (g : Gate) : Gate := ⟨g.op,effective g⟩
def trimmed (C : Circuit) : Circuit := ⟨C.gates.map trimGate,C.output⟩

lemma trim_get (gs : List Gate) (i : ℕ) (d : Gate) :
    (gs.map trimGate).getD i (trimGate d) = trimGate (gs.getD i d) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases gs[i]? <;> rfl

lemma pins_subset (g : Gate) {i : ℕ} (h : i∈effective g) : i∈g.inputs := by
  cases e : isNot g with
  | false => simpa [effective,e] using h
  | true => exact List.mem_of_mem_take (by simpa [effective,e] using h)

lemma trim_head (g : Gate) : (effective g).headD 0=g.inputs.headD 0 := by
  cases n : isNot g with
  | false => simp [effective,n]
  | true => cases ins : g.inputs <;> simp [effective,n,ins]

lemma eval_trim (g : Gate) (w : List Bool) :
    (trimGate g).op.eval ((trimGate g).inputs.map fun i => w.getD i false)=
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨o,l⟩ := g
  cases o <;> cases l <;> rfl

lemma run_trim (gs : List Gate) (w : List Bool) : phys (gs.map trimGate) w = phys gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons,phys,List.foldl_cons]
    rw [eval_trim]
    exact ih _

lemma named_effective {C : Circuit} (h : Qualifies C) (j : ℕ) (hj : j<C.size) (ne : C.output≠5+j) :
    ∃ i < C.size, j < i ∧ 5+j∈effective (C.gates.getD i ⟨.and,[]⟩) := by
  let p := C.gates.take j
  let s := C.gates.drop (j+1)
  change j<C.gates.length at hj
  have pl : p.length=j := List.length_take_of_le (by omega)
  have shape : C.gates=p++C.gates[j]::s := by
    change C.gates = C.gates.take j ++ C.gates[j]::C.gates.drop (j+1)
    rw [←List.drop_eq_getElem_cons hj,List.take_append_drop]
  obtain ⟨g,hg,hit⟩ := effective_use h p s _ shape (by simpa [pl] using ne)
  obtain ⟨k,hk,atK⟩ := List.mem_iff_getElem.mp hg
  have sz : C.size=p.length+(s.length+1) := by
    change C.gates.length=_
    conv_lhs => rw [shape]
    rw [List.length_append,List.length_cons]
  refine ⟨p.length+1+k,by omega,by omega,?_⟩
  have split : C.gates=(p++[C.gates[j]])++s := by simpa [List.append_assoc] using shape
  have eq : C.gates.getD (p.length+1+k) ⟨.and,[]⟩ = g := by
    conv_lhs => rw [split]
    rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (show (p++[C.gates[j]]).length ≤ p.length+1+k by simp)]
    simp [List.getElem?_eq_getElem hk,atK]
  rw [eq,←pl]
  exact hit

theorem trimmed_qualifies {C : Circuit} (h : Qualifies C) : Qualifies (trimmed C) := by
  have len : (trimmed C).size=C.size := by simp [trimmed,Circuit.size]
  refine ⟨?_,?_,by simpa [len] using h.cap,?_,?_,?_,?_⟩
  · intro g hg
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
    obtain ⟨leg,sz⟩ := h.legal q hq
    refine ⟨leg,?_⟩
    cases n : isNot q <;> simp [trimGate,effective,n,sz]
  · intro j hj i pin
    change i∈((C.gates.map trimGate).getD j (trimGate ⟨.or,[]⟩)).inputs at pin
    rw [trim_get] at pin
    exact h.back j (by simpa [trimmed] using hj) i (pins_subset _ pin)
  · intro x
    change (phys (C.gates.map trimGate) (List.ofFn x)).getD C.output false=_
    rw [run_trim]; exact h.computes x
  · intro j hj
    rw [len] at hj
    by_cases e : C.output=5+j
    · exact Or.inl e
    · obtain ⟨i,hi,gt,hit⟩ := named_effective h j hj e
      refine Or.inr ⟨i,by simpa [len] using hi,gt,?_⟩
      change 5+j∈((C.gates.map trimGate).getD i (trimGate ⟨.and,[]⟩)).inputs
      rw [trim_get]; exact hit
  · intro g hg op high
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
    change 5≤(effective q).headD 0 at high
    rw [trim_head] at high
    have old := h.noDouble q hq op high
    change ((C.gates.map trimGate).getD ((effective q).headD 0 -5) (trimGate ⟨.and,[]⟩)).op≠.not
    rw [trim_head,trim_get]; exact old
  · obtain ⟨g,hg,n,hi⟩ := h.internal
    exact ⟨trimGate g,List.mem_map_of_mem hg,n,by change 5≤(effective g).headD 0; rwa [trim_head]⟩

def RealPins (C : Circuit) : Prop := ∀g∈C.gates, g.op=.not → g.inputs.length=1
theorem trimmed_is_unary {C : Circuit} (h : Qualifies C) : RealPins (trimmed C) := by
  intro g hg n
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
  change q.op=.not at n
  obtain ⟨v,hv,op,hi⟩ := h.internal
  obtain ⟨p,s,sp⟩ := List.append_of_mem hv
  have no := no_other_not C p s v sp op (exactCounts C h.legal h.cap h.computes h.internal).2.1
  have nq : isNot q=true := by simp [isNot,n]
  rw [sp] at hq
  rcases List.mem_append.mp hq with prev|after
  · have := no.1 q prev; simp_all
  · rcases List.mem_cons.mp after with rfl|later
    · change (effective q).length=1
      cases ins : q.inputs with
      | nil => simp [ins] at hi
      | cons a xs => simp [effective,nq,ins]
    · have := no.2 q later; simp_all

theorem unary_iff : (∃ C, Qualifies C) ↔ ∃ C, Qualifies C ∧ RealPins C := by
  constructor
  · rintro ⟨C,h⟩; exact ⟨trimmed C,trimmed_qualifies h,trimmed_is_unary h⟩
  · rintro ⟨C,h,_⟩; exact ⟨C,h⟩

#print axioms unary_iff
end FiveRestricted
