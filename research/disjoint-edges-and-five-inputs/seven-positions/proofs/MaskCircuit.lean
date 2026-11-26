import MaskSlices
import UniformPaths

namespace FiveInputBoundary
open PEqualNP.CircuitLowerBounds Five18096Paths Five18096Bypass

def sourceBefore (p : List Gate) (g : Gate) (row : List Bool) : Bool :=
  (g.inputs.map fun i => (phys p row).getD i false).headD false

private theorem monotoneAO (s : List Gate) (a b : List Bool) (ab : Sound true a b)
    (ao : ∀ q ∈ s, q.op = .and ∨ q.op = .or) : Sound true (phys s a) (phys s b) := by
  induction s generalizing a b with
  | nil => exact ab
  | cons g s ih =>
    apply ih _ _ _ (fun q hq => ao q (by simp [hq]))
    exact snoc_sound true ab _ _ (preserve _ _ _ _ (ao g (by simp)) (fun i _ => ab.2 i))

private theorem evaluate_split (C : Circuit) (p s : List Gate) (g : Gate)
    (split : C.gates = p ++ g :: s) (inv : g.op = .not) (r : List Bool) :
    C.eval r = (phys s (phys p r ++ [!(sourceBefore p g r)])).getD C.output false := by
  simp [Circuit.eval, Circuit.wires, phys, sourceBefore, split, List.foldl_append, inv, GateOp.eval]

/-- The graph of a one-NOT circuit may be nonmonotone. Rows on which the source
    wire agrees still compare monotonically under the input order. -/
theorem one_not_within {α : Type*} [Preorder α] (bank : α → List Bool)
    (ordered : ∀ x y, x ≤ y → Sound true (bank x) (bank y))
    (C : Circuit) (p s : List Gate) (g : Gate) (split : C.gates = p ++ g :: s)
    (inv : g.op = .not) (before : ∀ q ∈ p, q.op = .and ∨ q.op = .or)
    (afterwards : ∀ q ∈ s, q.op = .and ∨ q.op = .or) (x y : α) (xy : x ≤ y)
    (same : sourceBefore p g (bank x) = sourceBefore p g (bank y)) :
    C.eval (bank x) = true → C.eval (bank y) = true := by
  rw [evaluate_split C p s g split inv, evaluate_split C p s g split inv]
  have base := monotoneAO p _ _ (ordered x y xy) before
  have joined := snoc_sound true base (!(sourceBefore p g (bank x))) (!(sourceBefore p g (bank y)))
    (by rw [same]; exact id)
  exact (monotoneAO s _ _ joined afterwards).2 C.output

/-- Exact finite extremal test directly for the project's Circuit.eval. -/
theorem one_not_exact_test {α : Type*} [PartialOrder α] [WellFoundedLT α] [WellFoundedGT α]
    (bank : α → List Bool) (ordered : ∀ x y, x ≤ y → Sound true (bank x) (bank y))
    (C : Circuit) (p s : List Gate) (g : Gate) (split : C.gates = p ++ g :: s)
    (inv : g.op = .not) (before : ∀ q ∈ p, q.op = .and ∨ q.op = .or)
    (afterwards : ∀ q ∈ s, q.op = .and ∨ q.op = .or) (target : α → Prop) :
    (∀ x, C.eval (bank x) = true ↔ target x) ↔
    (∀ x, MinPositive (fun y => sourceBefore p g (bank y)) target x → C.eval (bank x) = true) ∧
    (∀ x, MaxNegative (fun y => sourceBefore p g (bank y)) target x → ¬ C.eval (bank x) = true) :=
  extremal_rows _ _ _ (one_not_within bank ordered C p s g split inv before afterwards)

def activeInputs {n : Nat} (x : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i => decide (i ∈ x))

theorem orderedInputs {n : Nat} (x y : Finset (Fin n)) (sub : x ⊆ y) :
    Sound true (activeInputs x) (activeInputs y) := by
  constructor
  · simp [activeInputs]
  · intro i ht
    by_cases small : i < n
    · simpa [activeInputs,List.getD_eq_getElem?_getD,List.getElem?_ofFn,small] using
        sub (show (⟨i,small⟩ : Fin n) ∈ x from by
          simpa [activeInputs,List.getD_eq_getElem?_getD,List.getElem?_ofFn,small] using ht)
    · simp [activeInputs,List.getD_eq_getElem?_getD,List.getElem?_ofFn,small] at ht

/-- Specialization to the actual subset inputs of an n-input Boolean circuit. -/
theorem subset_input_test {n : Nat}
    (C : Circuit) (p s : List Gate) (g : Gate) (split : C.gates = p ++ g :: s)
    (inv : g.op = .not) (before : ∀ q ∈ p, q.op = .and ∨ q.op = .or)
    (afterwards : ∀ q ∈ s, q.op = .and ∨ q.op = .or) (target : Finset (Fin n) → Prop) :
    (∀ x, C.eval (activeInputs x) = true ↔ target x) ↔
    (∀ x, MinPositive (fun y => sourceBefore p g (activeInputs y)) target x → C.eval (activeInputs x) = true) ∧
    (∀ x, MaxNegative (fun y => sourceBefore p g (activeInputs y)) target x → ¬ C.eval (activeInputs x) = true) :=
  one_not_exact_test activeInputs orderedInputs C p s g split inv before afterwards target

#print axioms one_not_within
#print axioms one_not_exact_test
#print axioms subset_input_test
end FiveInputBoundary
