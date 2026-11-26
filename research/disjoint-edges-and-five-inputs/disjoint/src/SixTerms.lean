import Mathlib.Tactic
namespace SixTerms
abbrev I := Fin 3 × Bool
abbrev M := Fin 4 → I → Bool
def all3 (f : Fin 3 → Bool) := f 0 && f 1 && f 2
def all4 (f : Fin 4 → Bool) := f 0 && f 1 && f 2 && f 3
def some5 (f : Fin 5 → Bool) := f 0 || f 1 || f 2 || f 3 || f 4
def allI (f : I → Bool) := all3 fun i => f (i,false) && f (i,true)
def mono (m : I → Bool) := (all3 fun i => !m (i,false)) || (all3 fun i => !m (i,true))
def sep (m : M) (i j : Fin 3) :=
  all4 fun k => !(m k (i,false) && m k (j,false)) && !(m k (i,true) && m k (j,true))
def allowed (m : M) (p q : I) :=
  (p.2 != q.2) && ((p.1 == q.1) || sep m p.1 q.1)
def lit (f : I → Bool) (p q : I) := f p || f q
def d0 (m : M) (p q : I) := lit (m 0) p q && lit (m 1) p q
def d1 (m : M) (a b : Bool) (p q : I) :=
  (lit (m 2) p q || (a && d0 m p q)) && (lit (m 3) p q || (b && d0 m p q))
def vertex (u p q : I) := decide (u=p ∨ u=q)
def term (m : M) (a b : Bool) (i : Fin 3) (k : Fin 5) (p q : I) :=
  match k.val with
  | 0 => d0 m p q && vertex (i,false) p q
  | 1 => d0 m p q && vertex (i,true) p q
  | 2 => d1 m a b p q && vertex (i,false) p q
  | 3 => d1 m a b p q && vertex (i,true) p q
  | _ => d0 m p q && d1 m a b p q
def wins (m : M) (a b : Bool) (i : Fin 3) (k : Fin 5) :=
  term m a b i k (i,false) (i,true) &&
    allI fun p => allI fun q => !term m a b i k p q || allowed m p q
def passes (m : M) (a b : Bool) :=
  all4 (fun k => mono (m k)) && all3 (fun i => some5 (fun k => wins m a b i k))
theorem all3_iff (f : Fin 3 → Bool) : all3 f = true ↔ ∀ i, f i = true := by
  simp only [all3,Bool.and_eq_true]
  constructor
  · rintro ⟨⟨x,y⟩,z⟩ i; fin_cases i <;> assumption
  · intro h; exact ⟨⟨h 0,h 1⟩,h 2⟩
theorem all4_iff (f : Fin 4 → Bool) : all4 f = true ↔ ∀ i, f i = true := by
  simp only [all4,Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨a,b⟩,c⟩,d⟩ i; fin_cases i <;> assumption
  · intro h; exact ⟨⟨⟨h 0,h 1⟩,h 2⟩,h 3⟩
theorem allI_iff (f : I → Bool) : allI f = true ↔ ∀ p, f p = true := by
  simp only [allI,all3_iff,Bool.and_eq_true]
  constructor
  · intro h ⟨i,b⟩; cases b
    · exact (h i).1
    · exact (h i).2
  · intro h i; exact ⟨h _,h _⟩
theorem some5_of {f : Fin 5 → Bool} {k} (h : f k = true) : some5 f = true := by
  fin_cases k <;> simp_all [some5]
theorem passes_of (m : M) (a b : Bool) (r : ∀ k, mono (m k) = true)
    (sel : ∀ i, ∃ k, term m a b i k (i,false) (i,true) = true ∧
      ∀ p q, term m a b i k p q = true → allowed m p q = true) : passes m a b = true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨(all4_iff _).mpr r,(all3_iff _).mpr (fun i => ?_)⟩
  obtain ⟨k,pos,clean⟩ := sel i
  apply some5_of (k := k)
  refine Bool.and_eq_true_iff.mpr ⟨pos,(allI_iff _).mpr (fun p => (allI_iff _).mpr (fun q => ?_))⟩
  cases h : term m a b i k p q <;> simp [h,clean p q]
end SixTerms
