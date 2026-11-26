import Canonical
namespace FiveRestricted
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Ends Five18096Bypass Five18096Finite

def inputPerms : List (List (Fin 5)) :=
  [[0,1,2,3,4],[0,1,3,2,4],[0,2,1,3,4],[0,2,3,1,4],[0,3,1,2,4],[0,3,2,1,4]]
def permAt (p : List (Fin 5)) (i : Fin 5) := p.getD i.val i
def liftPin (p : List (Fin 5)) (i : Nat) := if small : i<5 then (permAt p ⟨i,small⟩).val else i
def permGate (p : List (Fin 5)) (g : Gate) : Gate := ⟨g.op,g.inputs.map (liftPin p)⟩
def permNet (p : List (Fin 5)) (C : Circuit) : Circuit := ⟨C.gates.map (permGate p),C.output⟩

theorem table_symmetry : ∀ p∈inputPerms, (∀x : Fin 5→Bool, tableFun 5 b (fun i => x (permAt p i))=tableFun 5 b x) ∧
    (∀i j : Fin 5, permAt p i = permAt p j → i=j) := by
  intro p hp
  simp only [inputPerms,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

def Match (p : List (Fin 5)) (a b : List Bool) : Prop :=
  a.length=b.length ∧ 5≤a.length ∧ ∀ j, a.getD (liftPin p j) false=b.getD j false

lemma match_snoc (p : List (Fin 5)) {a b : List Bool} (h : Match p a b) (v : Bool) :
    Match p (a++[v]) (b++[v]) := by
  refine ⟨by simp [h.1],by simp; have := h.2.1; omega,?_⟩
  intro j
  by_cases small : j<a.length
  · have bsmall : j<b.length := h.1 ▸ small
    have psmall : liftPin p j<a.length := by
      by_cases hp : j<5
      · simpa only [liftPin,dif_pos hp] using lt_of_lt_of_le (permAt p ⟨j,hp⟩).isLt h.2.1
      · simpa [liftPin,hp] using small
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left psmall,List.getElem?_append_left bsmall]
      using h.2.2 j
  · have ja : a.length ≤ j := by omega
    have jb : b.length ≤ j := h.1 ▸ ja
    have j5 : ¬j<5 := by have := h.2.1; omega
    simp [liftPin,j5,List.getD_eq_getElem?_getD,List.getElem?_append_right ja,List.getElem?_append_right jb,h.1]

lemma phys_perm (p : List (Fin 5)) (gs : List Gate) (a b : List Bool) (h : Match p a b) :
    Match p (phys (gs.map (permGate p)) a) (phys gs b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    have eq : (g.inputs.map (liftPin p)).map (fun i => a.getD i false)=g.inputs.map (fun i => b.getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i _; exact h.2.2 i
    change Match p (phys (gs.map (permGate p)) (a++[g.op.eval ((g.inputs.map (liftPin p)).map fun i => a.getD i false)]))
      (phys gs (b++[g.op.eval (g.inputs.map fun i => b.getD i false)]))
    rw [eq]
    exact ih _ _ (match_snoc p h _)

lemma match_roots (p : List (Fin 5)) (x : Fin 5→Bool) :
    Match p (List.ofFn x) (List.ofFn (fun i => x (permAt p i))) := by
  refine ⟨by simp,by simp,?_⟩
  intro j
  by_cases sm : j<5
  · have a : (liftPin p j)<5 := by simpa [liftPin,sm] using (permAt p ⟨j,sm⟩).isLt
    rw [List.getD_eq_getElem _ _ (by simpa using a),List.getD_eq_getElem _ _ (by simpa using sm)]
    simp only [List.getElem_ofFn]
    apply congrArg x
    apply Fin.ext
    simp [liftPin,sm]
  · have n1 : (List.ofFn x)[j]?=none := List.getElem?_eq_none (by simp; omega)
    have n2 : (List.ofFn (fun i => x (permAt p i)))[j]?=none := List.getElem?_eq_none (by simp; omega)
    simp [liftPin,sm,List.getD_eq_getElem?_getD,n1,n2]

lemma perm_get (p : List (Fin 5)) (gs : List Gate) (i : ℕ) (d : Gate) :
    (gs.map (permGate p)).getD i (permGate p d) = permGate p (gs.getD i d) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases gs[i]? <;> rfl

lemma internal_head (p : List (Fin 5)) (g : Gate) :
    5≤(permGate p g).inputs.headD 0 ↔ 5≤g.inputs.headD 0 := by
  obtain ⟨o,l⟩:=g
  cases l with
  | nil => simp [permGate]
  | cons j s =>
    by_cases sm : j<5
    · have a := (permAt p ⟨j,sm⟩).isLt
      simp [permGate,liftPin,sm]; omega
    · simp [permGate,liftPin,sm]

lemma perm_head_fixed (p : List (Fin 5)) (g : Gate) (h : 5≤g.inputs.headD 0) :
    (permGate p g).inputs.headD 0=g.inputs.headD 0 := by
  obtain ⟨o,l⟩:=g
  cases l with
  | nil => simp [permGate]
  | cons j s => have bound : ¬j<5 := by change 5≤j at h; omega
                simp [permGate,liftPin,bound]

theorem perm_qualifies {C : Circuit} (h : Qualifies C) {p : List (Fin 5)} (hp : p∈inputPerms) :
    Qualifies (permNet p C) := by
  have len : (permNet p C).size=C.size := by simp [permNet,Circuit.size]
  refine ⟨?_,?_,by simpa [len] using h.cap,?_,?_,?_,?_⟩
  · intro g hg
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
    simpa [permGate] using h.legal q hq
  · intro j hj i pin
    change i∈((C.gates.map (permGate p)).getD j (permGate p ⟨.or,[]⟩)).inputs at pin
    rw [perm_get] at pin
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp pin
    have bound := h.back j (by simpa [permNet] using hj) k hk
    by_cases sm : k<5
    · have := (permAt p ⟨k,sm⟩).isLt; simp [liftPin,sm]; omega
    · simpa [liftPin,sm] using bound
  · intro x
    have main := (phys_perm p C.gates _ _ (match_roots p x)).2.2 C.output
    have i := final_output h
    have same : liftPin p C.output=C.output := by rw [i]; rfl
    rw [same] at main
    exact main.trans ((h.computes _).trans ((table_symmetry p hp).1 x))
  · intro j hj
    rcases h.used j (by simpa [len] using hj) with out|⟨i,hi,gt,hit⟩
    · exact Or.inl out
    · refine Or.inr ⟨i,by simpa [len] using hi,gt,?_⟩
      change 5+j∈((C.gates.map (permGate p)).getD i (permGate p ⟨.and,[]⟩)).inputs
      rw [perm_get]
      apply List.mem_map.mpr
      exact ⟨5+j,hit,by simp [liftPin]⟩
  · intro g hg op high
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
    have bound := (internal_head p q).mp high
    have old := h.noDouble q hq op bound
    change ((C.gates.map (permGate p)).getD ((permGate p q).inputs.headD 0 -5) (permGate p ⟨.and,[]⟩)).op≠.not
    rw [perm_head_fixed p q bound,perm_get]; exact old
  · obtain ⟨g,hg,n,hi⟩ := h.internal
    exact ⟨permGate p g,List.mem_map_of_mem hg,n,(internal_head p g).mpr hi⟩

#print axioms perm_qualifies
end FiveRestricted
