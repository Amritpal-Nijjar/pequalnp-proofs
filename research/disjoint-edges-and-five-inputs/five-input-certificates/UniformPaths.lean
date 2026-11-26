import Bridge

namespace Five18096Paths
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_12108 FiveInputLower Five18096Fresh Five18096Ends Five18096Bypass Five18096Finite

def ofKind (d : Bool) : GateOp → Bool
  | .and => !d
  | .or => d
  | _ => false
lemma kind_of_match (d : Bool) (g : GateOp) (h : ofKind d g = true) :
    g=(if d then .or else .and) := by cases d <;> cases g <;> simp_all [ofKind]

/-- Propagate a mark through gates of just one operation. -/
def through (mode : Bool) (gs : List Gate) (w : List Bool) :=
  gs.foldl (fun ws g => ws ++ [ofKind mode g.op &&
    g.inputs.any (fun j => ws.getD j false)]) w

def Sound (c : Bool) (tags vals : List Bool) :=
  tags.length=vals.length ∧ ∀ j, tags.getD j false=true → vals.getD j false=c

lemma snoc_sound (c : Bool) {tags vals : List Bool} (h : Sound c tags vals) (t v : Bool)
    (hv : t=true → v=c) : Sound c (tags++[t]) (vals++[v]) := by
  constructor
  · simp [h.1]
  · intro j hj
    by_cases lt : j<tags.length
    · have lv : j<vals.length := h.1 ▸ lt
      simpa [List.getD_eq_getElem?_getD,List.getElem?_append_left lv] using h.2 j (by
        simpa [List.getD_eq_getElem?_getD,List.getElem?_append_left lt] using hj)
    · have ge : tags.length≤j := by omega
      have ge' : vals.length≤j := h.1 ▸ ge
      by_cases eq : j=tags.length
      · subst j
        have a : t=true := by simpa [List.getD_eq_getElem?_getD] using hj
        simpa [h.1,List.getD_eq_getElem?_getD] using hv a
      · have gap : tags.length+1≤j := by omega
        have z : (tags++[t])[j]? = none := List.getElem?_eq_none (by simpa using gap)
        simp [List.getD_eq_getElem?_getD,z] at hj

lemma propagate (mode : Bool) (gs : List Gate) (tags vals : List Bool) (h : Sound mode tags vals) :
    Sound mode (through mode gs tags) (phys gs vals) := by
  induction gs generalizing tags vals with
  | nil => simpa [through,phys] using h
  | cons g gs ih =>
    simp only [through,phys,List.foldl_cons]
    simp only [through,phys] at ih
    apply ih
    apply snoc_sound mode h
    intro fire
    obtain ⟨op,any⟩ := Bool.and_eq_true_iff.mp fire
    have kind := kind_of_match mode g.op op
    obtain ⟨i,mem,val⟩ := List.any_eq_true.mp any
    have atPin := h.2 i val
    cases mode with
    | false =>
      have opAnd : g.op=.and := kind
      rw [opAnd]
      change (g.inputs.map fun j => vals.getD j false).all id=false
      by_contra q
      have q' : (g.inputs.map fun j => vals.getD j false).all id=true := by
        cases z : (g.inputs.map fun j => vals.getD j false).all id <;> simp_all
      have yes := List.all_eq_true.mp q' _ (List.mem_map_of_mem mem)
      exact Bool.noConfusion (atPin.symm.trans yes)
    | true =>
      have opOr : g.op=.or := kind
      rw [opOr]
      exact List.any_eq_true.mpr ⟨vals.getD i false,List.mem_map_of_mem mem,atPin⟩

lemma all_clear (c : Bool) (vals : List Bool) : Sound c (List.replicate vals.length false) vals := by
  constructor
  · simp
  · intro j h
    have m : true ∈ List.replicate vals.length false := by
      rw [List.getD_eq_getElem?_getD] at h
      cases eq : (List.replicate vals.length false)[j]? with
      | none => simp [eq] at h
      | some a =>
        have ha := List.mem_of_getElem? eq
        have z : a=true := by simpa [eq] using h
        exact z ▸ ha
    simp at m

lemma bits_at (r : Row) (w : List Sig) (j : ℕ) :
    (w.map (bit r)).getD j false = bit r (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h : w[j]? with
  | none => exact (saved_bit_zero r).symm
  | some a => rfl

/-- Every path from the unique internal NOT to the output contains both an AND and
an OR. The reported reachability flag is false for each separate operation. -/
theorem no_uniform_path {C : Circuit} (h : Qualifies C) (p s : List Gate) (g : Gate)
    (split : C.gates=p++g::s) (n : g.op=.not) (pin : 5≤g.inputs.headD 0) (d : Bool) :
    (through d s (List.replicate (5+p.length) false ++ [true])).getD C.output false=false := by
  let r : Row := if d then 0 else 31
  let W := execute p fiveInputs
  let V := gv W g
  have len : W.length=5+p.length := by rw [show W=execute p fiveInputs from rfl,execute_len]; rfl
  have fall := internal_not_falls C h.legal h.cap h.computes h.back p s g split n pin
  have hit : bit r V = d := by
    cases d <;> first | exact fall.2 | exact fall.1
  have base := all_clear d (W.map (bit r))
  have start := snoc_sound d base true (bit r V) (fun _ => hit)
  have z := (propagate d s _ _ start).2 C.output
  simp only [List.length_map,len] at z
  have physical := saved_execute_bits s r (W++[V]) (fun a ha => (h.legal a (by simp [split,ha])).1)
  have project : phys s (W.map (bit r)++[bit r V]) = (execute s (W++[V])).map (bit r) := by
    simpa [phys] using physical.symm
  rw [project,bits_at] at z
  have allv : execute s (W++[V])=execute C.gates fiveInputs := by
    rw [split,execute_append]; rfl
  rw [allv,computed_sig C h.legal h.computes] at z
  have goal : bit r fiveGraph ≠ d := by
    cases d with
    | false => simpa [r,target_rises.2]
    | true => simpa [r,target_rises.1]
  cases mark : (through d s (List.replicate (5+p.length) false ++ [true])).getD C.output false
  · rfl
  · exact (goal (z mark)).elim

#print axioms no_uniform_path
end Five18096Paths
