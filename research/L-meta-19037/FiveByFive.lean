import PEqualNP.Defs

/-!
# The five-by-five case of L-meta-19037

For every Boolean table on five rows and five columns, an AND/OR circuit of size
at most s for its complement gives a circuit of size at most s + 10 for the table.
Both circuits are evaluated on one selected row and one selected column.
The main declaration is `FiveExact.exact` at the end of this file.

Proof by Amritpal-Nijjar's Codex agent. The wire-support definitions and bounds
below are adapted from `PEqualNP.MetaComplexity.Helpers.Shannon` and `.Support`.
The gate-fold monotonicity lemmas in `MinimumSupport` are adapted from `.LowMergeWires`.
These project helpers are distributed under Apache-2.0 in open-goat/pequalnp-proofs,
revision bd2267f1042fb33accd996111f966647eb6f4354. Selected declarations are included
locally so the only import is the project's public definitions.
-/

namespace FiveWireSupport
open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

/-- The support of a gate: the union of the supports of the wires it reads. -/
def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

/-- The supports of all wires, starting from the supports `L` of the wires present. -/
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

/-- The supports of the input wires: input `i` has support `{i}`. -/
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

/-- Wire lists `w`, `w'` (for the inputs `x`, `y`) agree on every wire whose support `x` and
`y` agree on. -/
def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

/-- Any set `W` of wires has a joint support of size at most `t + |W|`. -/
def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

end FiveWireSupport

namespace TwoPattern

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- A positive binary formula on the physical input wires. -/
inductive Tree (p : ℕ) where
  | var (i : Fin p)
  | node (isOr : Bool) (left right : Tree p)

namespace Tree

def value (x : Fin p → Bool) : Tree p → Bool
  | .var i => x i
  | .node op l r => if op then value x l || value x r else value x l && value x r

def size : Tree p → ℕ
  | .var _ => 0
  | .node _ l r => l.size + r.size + 1

def output (base : ℕ) : Tree p → ℕ
  | .var i => i.val
  | .node _ l r => base + l.size + r.size

def gates (base : ℕ) : Tree p → List Gate
  | .var _ => []
  | .node op l r => l.gates base ++ r.gates (base+l.size) ++
      [⟨if op then .or else .and, [l.output base, r.output (base+l.size)]⟩]

theorem length_gates (f : Tree p) (b : ℕ) : (f.gates b).length = f.size := by
  induction f generalizing b with
  | var => rfl
  | node _ _ _ ih jh => simp [gates, size, ih, jh, Nat.add_assoc]

theorem mono_gates (f : Tree p) (b : ℕ) : ∀ g ∈ f.gates b,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction f generalizing b with
  | var => simp [gates]
  | node op l r ih jh =>
    intro g h
    simp only [gates, List.mem_append, List.mem_singleton] at h
    rcases h with (h|h)|rfl
    · exact ih _ _ h
    · exact jh _ _ h
    · cases op <;> simp

def run (gs : List Gate) (w : List Bool) := (Circuit.mk gs 0).wires w

theorem run_app (gs hs : List Gate) (w : List Bool) : run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, Circuit.wires, List.foldl_append]

theorem run_ext (gs : List Gate) (w : List Bool) : ∃ t, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [run, Circuit.wires]⟩
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t,ht,hl⟩ := ih (w ++ [b])
    refine ⟨b :: t, ?_, by simp [hl]⟩
    change run gs (w ++ [b]) = _
    simpa using ht

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  obtain ⟨t,ht,hl⟩ := run_ext gs w
  simp [ht,hl]

theorem run_old (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t,ht,_⟩ := run_ext gs w
  simp [ht, List.getD_eq_getElem?_getD, List.getElem?_append, hi]

theorem output_lt (f : Tree p) (b : ℕ) (h : p ≤ b) : f.output b < b + f.size := by
  cases f with
  | var i => simpa [output,size] using lt_of_lt_of_le i.isLt h
  | node op l r => simp [output,size]; omega

theorem run_value (f : Tree p) (x : Fin p → Bool) (w : List Bool) (hp : p ≤ w.length)
    (hx : ∀ i : Fin p, w.getD i.val false = x i) :
    (run (f.gates w.length) w).getD (f.output w.length) false = f.value x := by
  induction f generalizing w with
  | var i => exact hx i
  | node op l r ih jh =>
    let a := run (l.gates w.length) w
    have ha : a.length = w.length + l.size := by simp [a,run_length,length_gates]
    let b := run (r.gates a.length) a
    have hb : b.length = w.length + l.size + r.size := by simp [b,run_length,length_gates,ha]
    have haX : ∀ i : Fin p, a.getD i.val false = x i := by
      intro i; exact (run_old _ _ _ (lt_of_lt_of_le i.isLt hp)).trans (hx i)
    have hr : b.getD (r.output a.length) false = r.value x := jh a (by omega) haX
    have hl : b.getD (l.output w.length) false = l.value x := by
      rw [show b = run (r.gates a.length) a from rfl, run_old]
      · exact ih w hp hx
      · rw [ha]; exact output_lt l _ hp
    simp only [gates, run_app, output, value]
    rw [← ha]
    change (b ++ [(if op then GateOp.or else GateOp.and).eval
      ([l.output w.length, r.output a.length].map fun i => b.getD i false)]).getD
      (a.length + r.size) false = _
    rw [← show b.length = a.length + r.size by simp [b,run_length,length_gates]]
    have snoc (z : Bool) : (b ++ [z]).getD b.length false = z := by
      simp [List.getD_eq_getElem?_getD]
    rw [snoc]
    simp only [List.map_cons, List.map_nil, hl, hr]
    cases op <;> simp [GateOp.eval]

end Tree

def either : Option (Tree p) → Option (Tree p) → Option (Tree p)
  | none, b => b
  | a, none => a
  | some a, some b => some (.node true a b)

def both : Option (Tree p) → Option (Tree p) → Option (Tree p)
  | some a, some b => some (.node false a b)
  | _, _ => none

def val (x : Fin p → Bool) : Option (Tree p) → Bool
  | none => false
  | some f => f.value x

def leaves : Option (Tree p) → ℕ
  | none => 0
  | some f => f.size + 1

@[simp] theorem val_either (x : Fin p → Bool) (a b : Option (Tree p)) :
    val x (either a b) = (val x a || val x b) := by
  cases a <;> cases b <;> simp [either,val,Tree.value]

@[simp] theorem val_both (x : Fin p → Bool) (a b : Option (Tree p)) :
    val x (both a b) = (val x a && val x b) := by
  cases a <;> cases b <;> simp [both,val,Tree.value]

theorem leaves_either (a b : Option (Tree p)) : leaves (either a b) = leaves a + leaves b := by
  cases a <;> cases b <;> simp [either,leaves,Tree.size] <;> omega

theorem leaves_both (a b : Option (Tree p)) : leaves (both a b) ≤ leaves a + leaves b := by
  cases a <;> cases b <;> simp [both,leaves,Tree.size] <;> omega

def group (l : List (Fin p)) : Option (Tree p) :=
  l.foldr (fun i t => either (some (.var i)) t) none

@[simp] theorem eval_group (x : Fin p → Bool) (l : List (Fin p)) : val x (group l) = l.any x := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change val x (either (some (.var i)) (group l)) = _
    rw [val_either,ih]; rfl

theorem leaves_group (l : List (Fin p)) : leaves (group l) = l.length := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change leaves (either (some (.var i)) (group l)) = _
    rw [leaves_either, ih]; simp [leaves,Tree.size, Nat.add_comm]

def readPair (u : Fin n) (v : Fin m) (i : Fin (n+m)) : Bool := (oneEach u v).getD i.val false

@[simp] theorem read_left (u i : Fin n) (v : Fin m) : readPair u v (Fin.castAdd m i) = decide (i = u) := by
  simp [readPair,oneEach,List.getD_eq_getElem?_getD,List.getElem?_append,i.isLt]

@[simp] theorem read_right (u : Fin n) (v j : Fin m) : readPair u v (Fin.natAdd n j) = decide (j = v) := by
  simp [readPair,oneEach,List.getD_eq_getElem?_getD,j.isLt]

end TwoPattern

namespace SignatureLower
open PEqualNP.Represents TwoPattern

theorem ofFn_read (i : Fin n) (j : Fin m) : List.ofFn (readPair i j) = oneEach i j := by
  apply List.ext_getElem
  · simp [oneEach]
  · intro k hk hl; simp [readPair,List.getD_eq_getElem?_getD,hl]

end SignatureLower

namespace MinimumSupport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity FiveWireSupport PEqualNP.Represents TwoPattern

/- The gate-fold monotonicity lemmas are from PEqualNP.MetaComplexity.Helpers.LowMergeWires. -/
/-- One gate step of the fold. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
/-- Pointwise order on Bool lists read through `getD`. -/
def LeL (a b : List Bool) : Prop := ∀ i, a.getD i false = true → b.getD i false = true

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

theorem fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length → LeL a b →
      LeL (gs.foldl step a) (gs.foldl step b) := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · intro i hi
      unfold step at hi ⊢
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [← hl]
        by_cases he : i - a.length = 0
        · rw [he] at hi ⊢
          simp only [List.getD_cons_zero] at hi ⊢
          exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi; simp at hi

def forcedRows (A : Fin n → Fin m → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ i' j, A i j = true ∧ A i' j = false

def forcedCols (A : Fin n → Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun j => ∃ j' i, A i j = true ∧ A i j' = false

theorem constrained_mono (C : Circuit) (hm : Monotone2 C) (x y : Fin k → Bool)
    (onSupport : ∀ i ∈ (suppsFrom C.gates (inputSupps k)).getD C.output ∅, x i = true → y i = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  classical
  let S := (suppsFrom C.gates (inputSupps k)).getD C.output ∅
  let z := fun i : Fin k => if i ∈ S then x i else false
  have agree := (agree_wiresFrom x z C.gates _ _ _ (agree_inputs x z)).2.2 C.output
    (fun i hi => by change i ∈ S at hi; simp only [z,if_pos hi])
  change C.eval (List.ofFn x) = C.eval (List.ofFn z) at agree
  rw [agree]
  have inputs : LeL (List.ofFn z) (List.ofFn y) := by
    intro i hi
    by_cases h : i < k
    · have hz : z ⟨i,h⟩ = true := by simpa [List.getD_eq_getElem?_getD,h] using hi
      have hzi : ⟨i,h⟩ ∈ S := by by_contra hn; simp [z,hn] at hz
      have hx : x ⟨i,h⟩ = true := by simpa [z,hzi] using hz
      have hy := onSupport ⟨i,h⟩ hzi hx
      simpa [List.getD_eq_getElem?_getD,h] using hy
    · simp [List.getD_eq_getElem?_getD,h] at hi
  have hops (g : Gate) (hg : g ∈ C.gates) : g.op = .and ∨ g.op = .or := by simpa using (hm g hg).1
  exact fold_mono C.gates hops (List.ofFn z) (List.ofFn y) (by simp) inputs C.output

theorem lower (A : Fin n → Fin m → Bool) {s : ℕ} (h : RepSizeAtMost A s) :
    (forcedRows A).card + (forcedCols A).card ≤ s + 1 := by
  classical
  obtain ⟨C,hm,hs,rep⟩ := h
  let S := (suppsFrom C.gates (inputSupps (n+m))).getD C.output ∅
  have hok (g : Gate) (hg : g ∈ C.gates) : Ok g := by
    obtain ⟨op,sz⟩ := hm g hg
    refine ⟨?_,sz⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
    exact op.imp_right Or.inl
  have hc := cnt_suppsFrom C.gates 0 (inputSupps (n+m)) hok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion,Finset.card_singleton,zero_add] at hc
  change S.card ≤ C.gates.length + 1 at hc
  have local_order (a b : Fin n) (i j : Fin m)
      (hp : ∀ w ∈ S, readPair a i w = true → readPair b j w = true) :
      A a i = true → A b j = true := by
    have h' := constrained_mono C hm (readPair a i) (readPair b j) hp
    rw [SignatureLower.ofFn_read,SignatureLower.ofFn_read,rep,rep] at h'
    exact h'
  let left := (forcedRows A).map (Fin.castAddEmb m)
  let right := (forcedCols A).map (Fin.natAddEmb n)
  have hl : left ⊆ S := by
    intro w hw
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨_,b,j,hpos,hneg⟩ := Finset.mem_filter.mp ha
    by_contra hn
    have hl' := local_order a b j j (by
      intro w hmem hi
      induction w using Fin.addCases with
      | left k =>
        have hka : k ≠ a := by intro eq; subst a; exact hn hmem
        simp [hka] at hi
      | right k => simpa using hi) hpos
    simp [hneg] at hl'
  have hr : right ⊆ S := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨_,k,i,hpos,hneg⟩ := Finset.mem_filter.mp hj
    by_contra hn
    have hr' := local_order i i j k (by
      intro w hmem hi
      induction w using Fin.addCases with
      | left a => simpa using hi
      | right a =>
        have haj : a ≠ j := by intro eq; subst j; exact hn hmem
        simp [haj] at hi) hpos
    simp [hneg] at hr'
  have hd : Disjoint left right := by
    rw [Finset.disjoint_left]; intro w hw hw'
    obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨b,_,eq⟩ := Finset.mem_map.mp hw'
    have hv := congrArg Fin.val eq
    change n+b.val = a.val at hv
    have := a.isLt
    omega
  have htotal := Finset.card_le_card (Finset.union_subset hl hr)
  rw [Finset.card_union_of_disjoint hd] at htotal
  simp only [left,right,Finset.card_map] at htotal
  change C.gates.length ≤ s at hs
  omega

end MinimumSupport

namespace FiveNormal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents TwoPattern

abbrev V := Fin 5
abbrev T := Option (Tree 15)

def row (transposed : Bool) (i : V) : Fin 15 := if transposed then ⟨5 + i.val, by omega⟩ else ⟨i.val, by omega⟩
def col (transposed : Bool) (i : V) : Fin 15 := row (!transposed) i

def pairGates (_hole : V) (t : Bool) : List Gate :=
  [⟨.or, [(col t 0).val,(col t 1).val]⟩, ⟨.or, [(col t 2).val,(col t 3).val]⟩,
   ⟨.or, [(col t 2).val,(col t 4).val]⟩, ⟨.or, [(col t 3).val,(col t 4).val]⟩, ⟨.or, [11,(col t 4).val]⟩]
def sample (t : Bool) (u v : V) := if t then oneEach v u else oneEach u v
def ext (hole : V) (t : Bool) (u v : V) (i : Fin 15) := (Tree.run (pairGates hole t) (sample t u v)).getD i.val false
def oriented (t : Bool) (A : V → V → Bool) (u v : V) := if t then A v u else A u v

def leaf (i : Fin 15) : T := some (.var i)

def bucket (both first second : Fin 15) (a b : Bool) : T :=
  if a then (if b then leaf both else leaf first) else (if b then leaf second else none)

def tail (t c d e : Bool) : T := if c then
  (if d then (if e then leaf 14 else leaf 11) else (if e then leaf 12 else leaf (col t 2)))
  else if d then (if e then leaf 13 else leaf (col t 3)) else if e then leaf (col t 4) else none
def cols (_h : V) (t a b c d e : Bool) : T := either (bucket 10 (col t 0) (col t 1) a b) (tail t c d e)
theorem cols_value : ∀ (h : V) (t a b c d e : Bool) (u v : V), val (ext h t u v) (cols h t a b c d e) = (![a,b,c,d,e] : V → Bool) v := by decide +kernel
theorem cols_leaves : ∀ (h : V) (t a b c d e : Bool), leaves (cols h t a b c d e) ≤ 2 := by decide +kernel
def mask (h : V) (t : Bool) (f : V → Bool) := cols h t (f 0) (f 1) (f 2) (f 3) (f 4)
theorem mask_value (h : V) (t : Bool) (f : V → Bool) (u v : V) : val (ext h t u v) (mask h t f) = f v := by
  rw [mask,cols_value]; fin_cases v <;> rfl
theorem mask_leaves (h : V) (t : Bool) (f : V → Bool) : leaves (mask h t f) ≤ 2 := cols_leaves ..
theorem row_value : ∀ (h : V) (t : Bool) (u v i : V), val (ext h t u v) (leaf (row t i)) = decide (u = i) := by decide +kernel
theorem realize (hole : V) (t : Bool) (f : T) (A : V → V → Bool)
    (h : ∀ u v, val (ext hole t u v) f = A u v) : RepSizeAtMost (oriented t A) (leaves f + 4) := by
  cases f with
  | none =>
    refine ⟨⟨[],10⟩, by simp [Monotone2], by simp [Circuit.size], ?_⟩
    intro u v
    have empty : ∀ u v : V, (Circuit.mk [] 10).eval (oneEach u v) = false := by decide +kernel
    rw [empty]
    cases t with
    | false => exact h u v
    | true => exact h v u
  | some tree =>
    let C : Circuit := ⟨pairGates hole t ++ tree.gates 15, tree.output 15⟩
    refine ⟨C, ?_, ?_, ?_⟩
    · intro g hg
      change g ∈ pairGates hole t ++ tree.gates 15 at hg
      rcases List.mem_append.mp hg with hp | hf
      · change g ∈ [_, _, _, _, _] at hp
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact ⟨Or.inr rfl, by simp⟩
      · exact tree.mono_gates 15 g hf
    · change (pairGates hole t ++ tree.gates 15).length ≤ tree.size + 1 + 4
      simp [pairGates,Tree.length_gates] <;> omega
    · have core (u v : V) : C.eval (sample t u v) = A u v := by
        let w := Tree.run (pairGates hole t) (sample t u v)
        have hw : w.length = 15 := by
          dsimp [w]
          rw [Tree.run_length]
          cases t <;> simp [sample,pairGates,oneEach]
        have ht := tree.run_value (ext hole t u v) w (by omega) (fun _ => rfl)
        rw [hw] at ht
        change (Tree.run (pairGates hole t ++ tree.gates 15) (sample t u v)).getD (tree.output 15) false = _
        rw [Tree.run_app]
        exact ht.trans (h u v)
      intro u v
      cases t with
      | false => exact core u v
      | true => exact core v u


def many (xs : List V) (g : V → T) : T := xs.foldr (fun i f => either (g i) f) none
theorem many_value (x : Fin 15 → Bool) (xs : List V) (g : V → T) :
    val x (many xs g) = xs.any (fun i => val x (g i)) := by
  induction xs with
  | nil => rfl
  | cons a l ih => change val x (either (g a) (many l g)) = _; rw [val_either,ih]; rfl
theorem many_leaves (xs : List V) (g : V → T) (bound : ∀ i, leaves (g i) ≤ 3) : leaves (many xs g) ≤ 3*xs.length := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons a l ih => change leaves (either (g a) (many l g)) ≤ _; rw [leaves_either,List.length_cons]; have := bound a; omega

def atom (h : V) (t : Bool) (A : V → V → Bool) (i : V) := both (leaf (row t i)) (mask h t (A i))
theorem atom_leaves (h : V) (t : Bool) (A : V → V → Bool) (i : V) : leaves (atom h t A i) ≤ 3 := by
  have h1 := leaves_both (leaf (row t i)) (mask h t (A i))
  change leaves (atom h t A i) ≤ 1+leaves (mask h t (A i)) at h1
  have h2 := mask_leaves h t (A i); omega
theorem atom_value (h : V) (t : Bool) (A : V → V → Bool)  (i u v : V) :
    val (ext h t u v) (atom h t A i) = (decide (u=i) && A i v) := by
  rw [atom,val_both,row_value,mask_value ]
noncomputable def grouped (t : Bool) (S : Finset V) : T := group (S.toList.map (row t))
theorem grouped_leaves (t : Bool) (S : Finset V) : leaves (grouped t S) = S.card := by simp [grouped,leaves_group]
theorem grouped_value (h : V) (t : Bool) (S : Finset V) (u v : V) :
    val (ext h t u v) (grouped t S) = decide (u∈S) := by
  have raw (i : V) : ext h t u v (row t i) = decide (u=i) := row_value ..
  apply Bool.eq_iff_iff.mpr
  simp [grouped,List.any_eq_true,raw]
theorem ordinary_value (h : V) (t : Bool) (A : V → V → Bool)  (R : Finset V) (u v : V) :
    val (ext h t u v) (many R.toList (atom h t A)) = (decide (u∈R) && A u v) := by
  apply Bool.eq_iff_iff.mpr
  simp [many_value,List.any_eq_true,atom_value ]

theorem upper (t : Bool) (A : V → V → Bool) (R : Finset V) (full : ∀ i ∉ R, ∀ j, A i j = true) :
    RepSizeAtMost (oriented t A) (2*R.card+9) := by
  let f := either (grouped t Rᶜ) (many R.toList (atom 0 t A))
  have hv (u v : V) : val (ext 0 t u v) f = A u v := by
    simp only [f,val_either,grouped_value,ordinary_value]
    by_cases hu : u∈R
    · simp [hu]
    · simp [hu,full u hu v]
  obtain ⟨C,hm,hs,rep⟩ := realize 0 t f A hv
  have hl := many_leaves R.toList (atom 0 t A) (atom_leaves 0 t A)
  simp only [f,leaves_either,grouped_leaves,Finset.card_compl] at hs
  simp only [Finset.length_toList] at hl
  have hr : R.card ≤ 5 := Finset.card_le_univ _
  change C.size ≤ 5-R.card+leaves (many R.toList (atom 0 t A))+4 at hs
  exact ⟨C,hm,by omega,rep⟩

end FiveNormal

namespace FiveSmall

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents TwoPattern

abbrev V := Fin 5
abbrev T := Option (Tree 12)

def row (transposed : Bool) (i : V) : Fin 12 := if transposed then ⟨5 + i.val, by omega⟩ else ⟨i.val, by omega⟩
def col (transposed : Bool) (i : V) : Fin 12 := row (!transposed) i

def perm (hole i : V) := Equiv.swap hole (4 : V) i
def pairGates (hole : V) (t : Bool) : List Gate :=
  [⟨.or, [(col t (perm hole 0)).val,(col t (perm hole 1)).val]⟩,
   ⟨.or, [(col t (perm hole 2)).val,(col t (perm hole 3)).val]⟩]
def sample (t : Bool) (u v : V) := if t then oneEach v u else oneEach u v
def ext (hole : V) (t : Bool) (u v : V) (i : Fin 12) := (Tree.run (pairGates hole t) (sample t u v)).getD i.val false
def oriented (t : Bool) (A : V → V → Bool) (u v : V) := if t then A v u else A u v

def leaf (i : Fin 12) : T := some (.var i)

def bucket (both first second : Fin 12) (a b : Bool) : T :=
  if a then (if b then leaf both else leaf first) else (if b then leaf second else none)

def cols (h : V) (t a b c d : Bool) : T := either (bucket 10 (col t (perm h 0)) (col t (perm h 1)) a b) (bucket 11 (col t (perm h 2)) (col t (perm h 3)) c d)
theorem cols_value : ∀ (h : V) (t a b c d : Bool) (u v : V), val (ext h t u v) (cols h t a b c d) = (![a,b,c,d,false] : V → Bool) (perm h v) := by decide +kernel
theorem cols_leaves : ∀ (h : V) (t a b c d : Bool), leaves (cols h t a b c d) ≤ 2 := by decide +kernel
def mask (h : V) (t : Bool) (f : V → Bool) := cols h t (f (perm h 0)) (f (perm h 1)) (f (perm h 2)) (f (perm h 3))
theorem mask_value (h : V) (t : Bool) (f : V → Bool) (hz : f h = false) (u v : V) : val (ext h t u v) (mask h t f) = f v := by
  rw [mask,cols_value]
  fin_cases h <;> fin_cases v <;> simp_all [perm,Equiv.swap_apply_def]
theorem mask_leaves (h : V) (t : Bool) (f : V → Bool) : leaves (mask h t f) ≤ 2 := cols_leaves ..
theorem row_value : ∀ (h : V) (t : Bool) (u v i : V), val (ext h t u v) (leaf (row t i)) = decide (u = i) := by decide +kernel
theorem realize (hole : V) (t : Bool) (f : T) (A : V → V → Bool)
    (h : ∀ u v, val (ext hole t u v) f = A u v) : RepSizeAtMost (oriented t A) (leaves f + 1) := by
  cases f with
  | none =>
    refine ⟨⟨[],10⟩, by simp [Monotone2], by simp [Circuit.size], ?_⟩
    intro u v
    have empty : ∀ u v : V, (Circuit.mk [] 10).eval (oneEach u v) = false := by decide +kernel
    rw [empty]
    cases t with
    | false => exact h u v
    | true => exact h v u
  | some tree =>
    let C : Circuit := ⟨pairGates hole t ++ tree.gates 12, tree.output 12⟩
    refine ⟨C, ?_, ?_, ?_⟩
    · intro g hg
      change g ∈ pairGates hole t ++ tree.gates 12 at hg
      rcases List.mem_append.mp hg with hp | hf
      · change g ∈ [_, _] at hp
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
        rcases hp with rfl | rfl <;> exact ⟨Or.inr rfl, by simp⟩
      · exact tree.mono_gates 12 g hf
    · change (pairGates hole t ++ tree.gates 12).length ≤ tree.size + 1 + 1
      simp [pairGates,Tree.length_gates] <;> omega
    · have core (u v : V) : C.eval (sample t u v) = A u v := by
        let w := Tree.run (pairGates hole t) (sample t u v)
        have hw : w.length = 12 := by
          dsimp [w]
          rw [Tree.run_length]
          cases t <;> simp [sample,pairGates,oneEach]
        have ht := tree.run_value (ext hole t u v) w (by omega) (fun _ => rfl)
        rw [hw] at ht
        change (Tree.run (pairGates hole t ++ tree.gates 12) (sample t u v)).getD (tree.output 12) false = _
        rw [Tree.run_app]
        exact ht.trans (h u v)
      intro u v
      cases t with
      | false => exact core u v
      | true => exact core v u


def many (xs : List V) (g : V → T) : T := xs.foldr (fun i f => either (g i) f) none
theorem many_value (x : Fin 12 → Bool) (xs : List V) (g : V → T) :
    val x (many xs g) = xs.any (fun i => val x (g i)) := by
  induction xs with
  | nil => rfl
  | cons a l ih => change val x (either (g a) (many l g)) = _; rw [val_either,ih]; rfl
theorem many_leaves (xs : List V) (g : V → T) (bound : ∀ i, leaves (g i) ≤ 3) : leaves (many xs g) ≤ 3*xs.length := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons a l ih => change leaves (either (g a) (many l g)) ≤ _; rw [leaves_either,List.length_cons]; have := bound a; omega

def atom (h : V) (t : Bool) (A : V → V → Bool) (i : V) := both (leaf (row t i)) (mask h t (A i))
theorem atom_leaves (h : V) (t : Bool) (A : V → V → Bool) (i : V) : leaves (atom h t A i) ≤ 3 := by
  have h1 := leaves_both (leaf (row t i)) (mask h t (A i))
  change leaves (atom h t A i) ≤ 1+leaves (mask h t (A i)) at h1
  have h2 := mask_leaves h t (A i); omega
theorem atom_value (h : V) (t : Bool) (A : V → V → Bool) (hz : ∀ i, A i h = false) (i u v : V) :
    val (ext h t u v) (atom h t A i) = (decide (u=i) && A i v) := by
  rw [atom,val_both,row_value,mask_value h t (A i) (hz i)]
noncomputable def grouped (t : Bool) (S : Finset V) : T := group (S.toList.map (row t))
theorem grouped_leaves (t : Bool) (S : Finset V) : leaves (grouped t S) = S.card := by simp [grouped,leaves_group]
theorem grouped_value (h : V) (t : Bool) (S : Finset V) (u v : V) :
    val (ext h t u v) (grouped t S) = decide (u∈S) := by
  have raw (i : V) : ext h t u v (row t i) = decide (u=i) := row_value ..
  apply Bool.eq_iff_iff.mpr
  simp [grouped,List.any_eq_true,raw]
theorem ordinary_value (h : V) (t : Bool) (A : V → V → Bool) (hz : ∀ i, A i h = false) (R : Finset V) (u v : V) :
    val (ext h t u v) (many R.toList (atom h t A)) = (decide (u∈R) && A u v) := by
  apply Bool.eq_iff_iff.mpr
  simp [many_value,List.any_eq_true,atom_value h t A hz]

theorem upper (hole : V) (t : Bool) (A : V → V → Bool) (R : Finset V) (g : V → Bool)
    (hz : ∀ i, A i hole = false) (hgz : g hole = false) (same : ∀ i ∉ R, A i = g) :
    RepSizeAtMost (oriented t A) (2*R.card+8) := by
  let common := both (grouped t Rᶜ) (mask hole t g)
  let f := either common (many R.toList (atom hole t A))
  have hv (u v : V) : val (ext hole t u v) f = A u v := by
    simp only [f,common,val_either,val_both,grouped_value,mask_value hole t g hgz,ordinary_value hole t A hz]
    by_cases hu : u∈R
    · simp [hu]
    · simp [hu,same u hu]
  obtain ⟨C,hm,hs,rep⟩ := realize hole t f A hv
  have hc := leaves_both (grouped t Rᶜ) (mask hole t g)
  change leaves common ≤ leaves (grouped t Rᶜ)+leaves (mask hole t g) at hc
  rw [grouped_leaves,Finset.card_compl] at hc
  have h2 := mask_leaves hole t g
  have hl := many_leaves R.toList (atom hole t A) (atom_leaves hole t A)
  simp only [f,leaves_either] at hs
  simp only [Finset.length_toList] at hl
  have hr : R.card ≤ 5 := Finset.card_le_univ _
  change leaves common ≤ 5-R.card+leaves (mask hole t g) at hc
  exact ⟨C,hm,by omega,rep⟩

end FiveSmall

namespace FiveExact

open PEqualNP.Represents MinimumSupport

abbrev V := Fin 5

theorem one_orientation (t : Bool) (A : V → V → Bool) :
    RepSizeAtMost (FiveNormal.oriented t A) (2*(forcedRows (fun i j => !A i j)).card+9) := by
  classical
  let R := forcedRows (fun i j => !A i j)
  have maximal (a : V) (ha : a ∉ R) (i j : V) (h : A i j = true) : A a j = true := by
    cases hav : A a j with
    | true => rfl
    | false =>
      exfalso; apply ha; apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,i,j,by simp [hav],by simp [h]⟩
  by_cases full : ∀ i ∉ R, ∀ j, A i j = true
  · exact FiveNormal.upper t A R full
  · push_neg at full
    obtain ⟨a,ha,j,hj⟩ := full
    have hzero : A a j = false := by cases h : A a j <;> simp_all
    have hole (i : V) : A i j = false := by
      cases hi : A i j with
      | false => rfl
      | true => have h := maximal a ha i j hi; simp [hzero] at h
    have same (i : V) (hi : i ∉ R) : A i = A a := by
      funext v
      apply Bool.eq_iff_iff.mpr
      exact ⟨maximal a ha i v,maximal i hi a v⟩
    obtain ⟨C,hm,cap,rep⟩ := FiveSmall.upper j t A R (A a) hole hzero same
    change RepSizeAtMost (FiveNormal.oriented t A) (2*R.card+9)
    exact ⟨C,hm,by omega,rep⟩

theorem exact (A : Fin 5 → Fin 5 → Bool) (s : ℕ) (h : RepSizeAtMost (fun i j => !A i j) s) :
    RepSizeAtMost A (s+10) := by
  let B := fun i j => !A i j
  have lower := MinimumSupport.lower B h
  by_cases hrc : (forcedRows B).card ≤ (forcedCols B).card
  · obtain ⟨C,hm,cap,rep⟩ := one_orientation false A
    change C.size ≤ 2*(forcedRows B).card+9 at cap
    exact ⟨C,hm,by omega,rep⟩
  · obtain ⟨C,hm,cap,rep⟩ := one_orientation true (fun i j => A j i)
    change C.size ≤ 2*(forcedCols B).card+9 at cap
    exact ⟨C,hm,by omega,rep⟩


end FiveExact
