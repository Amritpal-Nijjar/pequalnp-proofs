import Cofactors
namespace FiveRestricted
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Ends Five18096Bypass Five18096Finite

/-- The possible second pin on the NOT is ignored by evaluation but retained
in the syntax throughout. The binary pins have either order. -/
def firstPair (rev : Bool) (noise : List ℕ) : List Gate :=
  [⟨.and,if rev then [4,0] else [0,4]⟩,⟨.not,5::noise⟩]

def AgreeOff (j : ℕ) (a b : List Bool) : Prop :=
  a.length=b.length ∧ ∀ i, i≠j → a.getD i false=b.getD i false

lemma snoc_off {j : ℕ} {a b : List Bool} (h : AgreeOff j a b) (v : Bool) :
    AgreeOff j (a++[v]) (b++[v]) := by
  constructor
  · simp [h.1]
  · intro i ne
    by_cases e : i<a.length
    · have f : i<b.length := h.1 ▸ e
      simpa [List.getD_eq_getElem?_getD,List.getElem?_append_left e,List.getElem?_append_left f] using h.2 i ne
    · have f : a.length ≤ i := by omega
      have k : b.length ≤ i := h.1 ▸ f
      simp [List.getD_eq_getElem?_getD,List.getElem?_append_right f,List.getElem?_append_right k,h.1]

lemma unread_off (s : List Gate) (j : ℕ) (a b : List Bool) (h : AgreeOff j a b)
    (unread : ∀ g∈s, j∉g.inputs) : AgreeOff j (phys s a) (phys s b) := by
  induction s generalizing a b with
  | nil => exact h
  | cons g s ih =>
    have inp : g.inputs.map (fun i => a.getD i false) = g.inputs.map (fun i => b.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact h.2 i (fun e => unread g (by simp) (e ▸ hi))
    change AgreeOff j (phys s (a++[g.op.eval (g.inputs.map fun i => a.getD i false)]))
      (phys s (b++[g.op.eval (g.inputs.map fun i => b.getD i false)]))
    rw [inp]
    exact ih _ _ (snoc_off h _) (fun v hv => unread v (by simp [hv]))

lemma reading_required {C : Circuit} (h : Qualifies C) (p s : List Gate)
    (sp : C.gates=p++s) (i : ℕ) (r t : Row)
    (outputs : bit r fiveGraph ≠ bit t fiveGraph) (outwire : C.output≠i)
    (wires : AgreeOff i ((execute p fiveInputs).map (bit r)) ((execute p fiveInputs).map (bit t))) :
    ∃ g∈s, i∈g.inputs := by
  by_contra! none
  have last := (unread_off s i _ _ wires none).2 C.output outwire
  have physRow (q : Row) : phys s ((execute p fiveInputs).map (bit q)) =
      (execute C.gates fiveInputs).map (bit q) := by
    rw [sp,execute_append]
    exact (saved_execute_bits s q _ (fun a ha => (h.legal a (by simp [sp,ha])).1)).symm
  rw [physRow,physRow,Five18096Paths.bits_at,Five18096Paths.bits_at,
      computed_sig C h.legal h.computes] at last
  exact outputs last

def rowTags (i : ℕ) (r t : Row) : Bool :=
  let w := execute (firstPair false []) fiveInputs
  (List.range 7).all (fun j => j==i || bit r (w.getD j zero)==bit t (w.getD j zero))

lemma agree_first (rev : Bool) (noise : List ℕ) (j : ℕ) (r t : Row)
    (e : rowTags j r t=true) :
    AgreeOff j ((execute (firstPair rev noise) fiveInputs).map (bit r))
      ((execute (firstPair rev noise) fiveInputs).map (bit t)) := by
  have H : execute (firstPair rev noise) fiveInputs=execute (firstPair false []) fiveInputs := by
    cases rev <;> rfl
  rw [H]
  constructor
  · simp
  · intro i ne
    rw [Five18096Paths.bits_at,Five18096Paths.bits_at]
    by_cases small : i<7
    · have v := List.all_eq_true.mp e i (List.mem_range.mpr small)
      simpa [ne] using v
    · have len : (execute (firstPair false []) fiveInputs).length=7 := rfl
      have zn : (execute (firstPair false []) fiveInputs)[i]?=none := List.getElem?_eq_none (by omega)
      simp [List.getD_eq_getElem?_getD,zn,saved_bit_zero]

theorem three_reads {C : Circuit} (h : Qualifies C) (rev : Bool) (noise : List ℕ)
    (s : List Gate) (sp : C.gates=firstPair rev noise ++ s) :
    (∃ g∈s, 0∈g.inputs) ∧ (∃ g∈s, 4∈g.inputs) ∧ (∃ g∈s, 6∈g.inputs) := by
  have endWire := final_output h
  refine ⟨reading_required h _ s sp 0 2 3 (by decide +kernel) (by omega)
    (agree_first rev noise _ _ _ (by decide +kernel)),
    reading_required h _ s sp 4 6 22 (by decide +kernel) (by omega)
    (agree_first rev noise _ _ _ (by decide +kernel)),?_⟩
  obtain eq|⟨i,hi,lt,mem⟩ := h.used 1 (by have := size_exact h; change 1<C.gates.length; omega)
  · omega
  · have ix : 2 ≤ i := by omega
    have n : i-2 < s.length := by
      change i<C.gates.length at hi
      simp [sp,firstPair] at hi
      omega
    have adjust : C.gates.getD i ⟨.and,[]⟩ = s[i-2] := by
      rw [sp]
      rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (show (firstPair rev noise).length ≤ i from ix)]
      change s[i-2]?.getD ⟨.and,[]⟩=s[i-2]
      rw [List.getElem?_eq_getElem n]; rfl
    exact ⟨s[i-2],List.getElem_mem n,adjust ▸ mem⟩

#print axioms three_reads
end FiveRestricted
