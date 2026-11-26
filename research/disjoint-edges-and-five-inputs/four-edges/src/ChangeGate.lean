import SixBridge

namespace ResidualChange
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open PEqualNP.Outside.L_meta_1491
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

def copyWire (C : Circuit) (j i : ℕ) : Circuit := ⟨C.gates.set j ⟨.and,[i,i]⟩,C.output⟩
@[simp] theorem length_copy (C : Circuit) (j i : ℕ) : (copyWire C j i).gates.length=C.gates.length := by simp [copyWire]
theorem gate_same (C : Circuit) {j k : ℕ} (i : ℕ) (klen : k < C.gates.length) (ne : k ≠ j) :
    gateAt (copyWire C j i) k = gateAt C k := by
  rw [S98.gateAt_eq _ _ (by simpa),S98.gateAt_eq _ _ klen]
  simp [copyWire,Ne.symm ne]
theorem gate_copy (C : Circuit) {j : ℕ} (i : ℕ) (len : j < C.gates.length) :
    gateAt (copyWire C j i) j = ⟨.and,[i,i]⟩ := by
  rw [S98.gateAt_eq _ _ (by simpa)]; simp [copyWire,len]
theorem ao_copy (ao : IsAO2 n C) {j i : ℕ} (prev : i < n+j) : IsAO2 n (copyWire C j i) := by
  apply S98.IsAO2_of_AO
  intro k hk
  rw [length_copy] at hk
  by_cases eq : k=j
  · subst k; rw [gate_copy _ _ hk]; exact ⟨.inl rfl,i,i,rfl,prev,prev⟩
  · rw [gate_same C i hk eq]; exact S98.AO_of_IsAO2 _ _ ao k hk

abbrev value (C : Circuit) (x : Fin n → Bool) (w : ℕ) := S98.W n C x w
theorem copy_value {j i : ℕ} (len : j<C.gates.length) (prev : i<n+j) (x : Fin n → Bool) :
    value (copyWire C j i) x (n+j) = value (copyWire C j i) x i := by
  unfold value
  rw [S98.W_and n (copyWire C j i) x j (by simpa) (by rw [gate_copy _ _ len]) i i (by rw [gate_copy _ _ len]) prev prev]
  simp

/-- Compare two evaluations when all gates except one have identical wiring. -/
theorem compare {A B : Circuit} (ao : IsAO2 n A) (len : A.gates.length=B.gates.length) (j : ℕ)
    (same : ∀ k, k < A.gates.length → k ≠ j → gateAt A k = gateAt B k)
    (x : Fin n → Bool) (changed : value A x (n+j)=true → value B x (n+j)=true) :
    ∀ w, w < n+A.gates.length → value A x w=true → value B x w=true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro bd on
    unfold value at on ⊢
    by_cases inp : w<n
    · exact (S98.W_input n B x w inp).trans ((S98.W_input n A x w inp).symm.trans on)
    obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
    by_cases eq : k=j
    · subst k; exact changed on
    have ka : k<A.gates.length := by omega
    have kb : k<B.gates.length := by omega
    obtain ⟨op,a,b,h,ha,hb⟩ := S98.AO_of_IsAO2 _ _ ao k ka
    have eqGate := same k ka eq
    rcases op with andOp|orOp
    · rw [S98.W_and n A x k ka andOp _ _ h ha hb,Bool.and_eq_true] at on
      rw [S98.W_and n B x k kb (eqGate ▸ andOp) _ _ (eqGate ▸ h) ha hb,Bool.and_eq_true]
      exact ⟨ih a ha (by omega) on.1,ih b hb (by omega) on.2⟩
    · rw [S98.W_or n A x k ka orOp _ _ h ha hb,Bool.or_eq_true] at on
      rw [S98.W_or n B x k kb (eqGate ▸ orOp) _ _ (eqGate ▸ h) ha hb,Bool.or_eq_true]
      exact on.imp (ih a ha (by omega)) (ih b hb (by omega))

theorem copied_value {j : ℕ} (len : j<C.gates.length) (u : Fin n) (x : Fin n → Bool) :
    value (copyWire C j u.val) x (n+j)=x u := by
  exact (copy_value len (show u.val<n+j by have := u.isLt; omega) x).trans (S98.W_input n _ x u.val u.isLt)

end ResidualChange
