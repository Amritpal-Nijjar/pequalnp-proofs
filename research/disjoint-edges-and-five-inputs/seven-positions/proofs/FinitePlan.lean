import Bypass

/-! A finite representation of every possible witness. The raw gate representation
retains a NOT's optional second pin because the official liveness test reads it
syntactically even though NOT ignores it in its evaluation. -/
namespace Five18096Finite
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_12108 FiveInputLower Five18096Fresh Five18096Ends Five18096Bypass

structure Qualifies (C : Circuit) : Prop where
  legal : FanInTwo C
  back : NestedCover.ReadsBack 5 C
  cap : C.size ≤ 10
  computes : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = tableFun 5 b x
  used : UsedOrOutput C
  noDouble : ∀ g ∈ C.gates, g.op = .not → 5 ≤ g.inputs.headD 0 →
    (C.gates.getD (g.inputs.headD 0 - 5) ⟨.and,[]⟩).op ≠ .not
  internal : ∃ g ∈ C.gates, g.op=.not ∧ 5 ≤ g.inputs.headD 0

inductive Kind where | and | or | not
deriving DecidableEq
instance : Fintype Kind := ⟨{.and,.or,.not},by intro k; cases k <;> simp⟩

structure Slot where
  kind : Kind
  count : Fin 3
  left : Fin 15
  right : Fin 15
deriving DecidableEq,Fintype

abbrev Plan := Fin 10 → Slot
def decode (s : Slot) : Gate :=
  ⟨match s.kind with | .and => .and | .or => .or | .not => .not,
   if s.count.val=0 then [] else if s.count.val=1 then [s.left.val] else [s.left.val,s.right.val]⟩
def net (v : Plan) : Circuit := ⟨List.ofFn (fun i => decode (v i)),14⟩
def pack (g : Gate) : Slot :=
  ⟨match g.op with | .and => .and | .not => .not | _ => .or,
   Fin.ofNat 3 g.inputs.length, Fin.ofNat 15 (g.inputs.getD 0 0), Fin.ofNat 15 (g.inputs.getD 1 0)⟩

lemma bounded_gate (g : Gate)
    (legal : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (bounds : ∀ i ∈ g.inputs, i<15) : decode (pack g) = g := by
  obtain ⟨op,l⟩ := g
  obtain ⟨h,sz⟩ := legal
  change l.length≤2 at sz
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  cases l with
  | nil => rcases h with rfl | rfl | rfl <;> rfl
  | cons a l =>
    have ha : a < 15 := bounds a (by simp)
    cases l with
    | nil =>
      rcases h with rfl | rfl | rfl <;> simp [decode,pack,Fin.ofNat,Nat.mod_eq_of_lt ha]
    | cons b l =>
      have hb : b < 15 := bounds b (by simp)
      cases l with
      | cons _ _ => simp at sz
      | nil =>
        rcases h with rfl | rfl | rfl <;> simp [decode,pack,Fin.ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb]

lemma size_exact {C : Circuit} (h : Qualifies C) : C.gates.length=10 :=
  (exactCounts C h.legal h.cap h.computes h.internal).1

lemma final_output {C : Circuit} (h : Qualifies C) : C.output=14 := by
  have n : C.size=10 := size_exact h
  obtain t | ⟨j,upper,high,_⟩ := h.used 9 (by omega)
  · exact t
  · omega

lemma plan_covers {C : Circuit} (h : Qualifies C) : ∃ v : Plan, net v = C := by
  have length:=size_exact h
  let v : Plan := fun i => pack (C.gates.getD i.val ⟨.or,[]⟩)
  refine ⟨v,?_⟩
  apply Circuit.mk.injEq _ _ _ _ |>.mpr
  constructor
  · apply List.ext_getElem
    · simpa [net] using length.symm
    · intro j hl hr
      rw [List.getElem_ofFn]
      simp only [v,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hr,Option.getD_some]
      apply bounded_gate
      · exact h.legal _ (List.getElem_mem hr)
      · intro a ha
        have mem : a ∈ (NestedCover.gateAt C j).inputs := by
          simpa [NestedCover.gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hr] using ha
        have bound := h.back j hr a mem
        omega
  · exact (final_output h).symm

def EveryGateBinary (gs : List Gate) : Prop :=
  ∀ g ∈ gs, isNot g=false → ∃ a b, g.inputs=[a,b] ∧ a≠b

lemma all_two (gs : List Gate) (w : List Sig) (fr : FreshRun gs w)
    (leg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    EveryGateBinary gs := by
  induction gs generalizing w with
  | nil => simp [EveryGateBinary]
  | cons g gs ih =>
    intro a ha n
    rcases List.mem_cons.mp ha with rfl | m
    · exact distinct_pins w a (leg a (by simp)) n (fr.1 n)
    · exact ih _ fr.2 (fun b hb => leg b (by simp [hb])) a m n

structure Filters (C : Circuit) : Prop where
  fresh : FreshRun C.gates fiveInputs
  binary : EveryGateBinary C.gates
  position : ∃ (p s : List Gate) (g : Gate), C.gates=p++g::s ∧
    g.op=.not ∧ 5≤g.inputs.headD 0 ∧ 1≤p.length ∧ p.length≤7 ∧ 2≤s.length
  bypass : ∀ i : Fin 5, (cleanPaths C.gates (List.ofFn (fun j : Fin 5 => decide (i=j)))).getD C.output false=true

theorem filters {C : Circuit} (h : Qualifies C) : Filters C := by
  have fr := fresh_exact C h.legal h.cap h.computes h.internal
  obtain ⟨g,hg,n,pin⟩ := h.internal
  obtain ⟨p,s,sp⟩ := List.append_of_mem hg
  refine ⟨fr,all_two _ _ fr h.legal,⟨p,s,g,sp,n,pin,?_⟩,?_⟩
  · exact not_position C h.legal h.cap h.computes h.back h.used p s g sp n pin
  · exact Five18096Bypass.bypass C h.legal h.cap h.computes h.internal

/-- Exact equivalence. To refute the posted statement it suffices to exclude this
finite gate family. The finite search itself remains a separate obligation. -/
theorem finite_model : (∃ C, Qualifies C) ↔ ∃ v : Plan, Qualifies (net v) ∧ Filters (net v) := by
  constructor
  · rintro ⟨C,h⟩
    obtain ⟨v,rfl⟩ := plan_covers h
    exact ⟨v,h,filters h⟩
  · rintro ⟨v,h,_⟩; exact ⟨net v,h⟩

#print axioms finite_model
end Five18096Finite
