import Mathlib.Order.Minimal

namespace FiveInputBoundary

variable {α : Type*} [PartialOrder α] [WellFoundedLT α] [WellFoundedGT α]

/-- A positive row minimal within rows having the same source signal. -/
def MinPositive (source : α → Bool) (target : α → Prop) (x : α) : Prop :=
  Minimal (fun y => source y = source x ∧ target y) x

/-- A negative row maximal within rows having the same source signal. -/
def MaxNegative (source : α → Bool) (target : α → Prop) (x : α) : Prop :=
  Maximal (fun y => source y = source x ∧ ¬ target y) x

/-- Within one truth value of the inverter source, all remaining gates are monotone. -/
theorem extremal_rows (source : α → Bool) (computed target : α → Prop)
    (within : ∀ x y, x ≤ y → source x = source y → computed x → computed y) :
    (∀ x, computed x ↔ target x) ↔
      (∀ x, MinPositive source target x → computed x) ∧
      (∀ x, MaxNegative source target x → ¬ computed x) := by
  constructor
  · intro h
    exact ⟨fun x hx => (h x).2 hx.prop.2, fun x hx hc => hx.prop.2 ((h x).1 hc)⟩
  · rintro ⟨positive, negative⟩ x
    constructor
    · intro hc
      by_contra hnot
      obtain ⟨z, hxz, hz⟩ := exists_maximal_ge_of_wellFoundedGT
        (fun y => source y = source x ∧ ¬ target y) x ⟨rfl, hnot⟩
      have same : source z = source x := hz.prop.1
      have hz' : MaxNegative source target z := by
        unfold MaxNegative
        rwa [same]
      exact negative z hz' (within x z hxz same.symm hc)
    · intro ht
      obtain ⟨z, hzx, hz⟩ := exists_minimal_le_of_wellFoundedLT
        (fun y => source y = source x ∧ target y) x ⟨rfl, ht⟩
      have same : source z = source x := hz.prop.1
      have hz' : MinPositive source target z := by
        unfold MinPositive
        rwa [same]
      exact within z x hzx same (positive z hz')

/-- Forcing the unique NOT to each constant gives two monotone computations. -/
theorem forced_extrema (source : α → Bool) (low high target : α → Prop)
    (low_mono : ∀ ⦃x y⦄, x ≤ y → low x → low y)
    (high_mono : ∀ ⦃x y⦄, x ≤ y → high x → high y) :
    (∀ x, (if source x then low x else high x) ↔ target x) ↔
      (∀ x, MinPositive source target x → (if source x then low x else high x)) ∧
      (∀ x, MaxNegative source target x → ¬ (if source x then low x else high x)) := by
  apply extremal_rows
  intro x y hxy same
  rw [same]
  cases source y
  · simpa only [Bool.false_eq_true, ite_false] using (high_mono hxy : high x → high y)
  · simpa only [ite_true] using (low_mono hxy : low x → low y)

#print axioms extremal_rows
#print axioms forced_extrema
end FiveInputBoundary
