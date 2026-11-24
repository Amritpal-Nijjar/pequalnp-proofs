import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The 48 edge inputs and maximal independent inputs certify the main output.
-- Four singleton inputs and maximal independent inputs avoiding the pencil
-- certify the auxiliary wire wherever the main output is false.
theorem PEqualNP.Outside.R_meta_2215_1
    (hsearch : let E := fun (i j : Fin 25) => i.val < 12 ∧ 12 ≤ j.val ∧ (i.val + j.val + 2) % 13 ∈ ([0,1,3,9] : List ℕ); let Q := ({12,13,15,21} : Finset (Fin 25));
    let hit (s : Finset (Fin 25)) : Prop := ∃ i ∈ s, ∃ j ∈ s, E i j;
    ∃ (C : Circuit) (q : ℕ), Monotone2 C ∧ C.size ≤ 61 ∧ C.output < 25 + C.size ∧ q < 25 + C.size ∧
      (let on (s : Finset (Fin 25)) (w : ℕ) : Prop := (C.wires (List.ofFn (fun i => decide (i ∈ s)))).getD w false = true; (∀ i j, E i j → on {i,j} C.output) ∧
       (∀ s, Maximal (fun t => ¬ hit t) s → ¬ on s C.output) ∧
       (∀ i ∈ Q, on {i} q) ∧
       (∀ s, Maximal (fun t => ¬hit t ∧ Disjoint t Q) s → ¬ on s q)))
    (hsound : ∀ (n : ℕ) (E : Fin n → Fin n → Prop) (Q : Finset (Fin n)) (C : Circuit) (q : ℕ), Monotone2 C →
    let hit (s : Finset (Fin n)) : Prop := ∃ i ∈ s, ∃ j ∈ s, E i j; let on (s : Finset (Fin n)) (w : ℕ) : Prop := (C.wires (List.ofFn (fun i => decide (i ∈ s)))).getD w false = true;
    (∀ i j, E i j → on {i,j} C.output) →
    (∀ s, Maximal (fun t => ¬ hit t) s → ¬ on s C.output) →
    (∀ i ∈ Q, on {i} q) →
    (∀ s, Maximal (fun t => ¬hit t ∧ Disjoint t Q) s → ¬ on s q) →
    ∀ s, (on s C.output ↔ hit s) ∧ (¬hit s → (on s q ↔ ¬Disjoint s Q))) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (61 : ℕ) ∧       x1.output < (25 : ℕ) + x1.size ∧         x2 < (25 : ℕ) + x1.size ∧           ∀ (x3 : Fin (25 : ℕ) → Bool),             have x4 : Fin (25 : ℕ) → Fin (25 : ℕ) → Prop := fun (x4 x5 : Fin (25 : ℕ)) => ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];             have x5 : Bool := x1.eval (List.ofFn x3);             (x5 = Bool.true ↔ ∃ (x6 : Fin (25 : ℕ)) (x7 : Fin (25 : ℕ)), x4 x6 x7 ∧ x3 x6 = Bool.true ∧ x3 x7 = Bool.true) ∧ (x5 = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (12 : Fin (25 : ℕ)) || x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  classical
  let E := fun (i j : Fin 25) => i.val < 12 ∧ 12 ≤ j.val ∧ (i.val + j.val + 2) % 13 ∈ ([0,1,3,9] : List ℕ)
  let Q := ({12,13,15,21} : Finset (Fin 25))
  let hit (s : Finset (Fin 25)) := ∃ i ∈ s, ∃ j ∈ s, E i j
  obtain ⟨C,q,hm,hs,ho,hq,he,hn,hp,ha⟩ := hsearch
  have spec := hsound 25 E Q C q hm he hn hp ha
  refine ⟨C,q,hm,hs,ho,hq,?_⟩
  intro x
  let S : Finset (Fin 25) := Finset.univ.filter (fun i => x i = true)
  have mem (i : Fin 25) : i ∈ S ↔ x i = true := by simp [S]
  have encode : (fun i => decide (i ∈ S)) = x := by
    funext i
    cases h : x i <;> simp [S,h]
  have edge : hit S ↔ ∃ i j, E i j ∧ x i = true ∧ x j = true := by
    constructor
    · rintro ⟨i,hi,j,hj,e⟩
      exact ⟨i,j,e,(mem i).mp hi,(mem j).mp hj⟩
    · rintro ⟨i,j,e,hi,hj⟩
      exact ⟨i,(mem i).mpr hi,j,(mem j).mpr hj,e⟩
  have flag : (¬Disjoint S Q) ↔ (x 12 || x 13 || x 15 || x 21) = true := by
    simp only [Q,Finset.disjoint_insert_right,Finset.disjoint_singleton_right, mem, Bool.or_eq_true]
    tauto
  obtain ⟨main,aux⟩ := spec S
  dsimp only at main aux ⊢
  rw [encode] at main aux
  change (C.eval (List.ofFn x) = true ↔ hit S) at main
  change (¬hit S → ((C.wires (List.ofFn x)).getD q false = true ↔ ¬Disjoint S Q)) at aux
  refine ⟨main.trans edge,?_⟩
  intro rejected
  have hno : ¬hit S := fun h => Bool.false_ne_true (rejected.symm.trans (main.mpr h))
  exact Bool.eq_iff_iff.mpr ((aux hno).trans flag)
