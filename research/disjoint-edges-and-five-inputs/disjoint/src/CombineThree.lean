import DisjointBound

namespace DisjointBound
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- The interface supplied by Kapre's published `failure_requires_three_disjoint`.
    This module can be verified without rebuilding his eighteen earlier certificates. -/
theorem three_from_touching (four : NoFourCycle G) (bip : G.IsBipartite)
    (least : IsLeastAO G C) (top : TopForm G C) (three : (Ustar G C).card = 3)
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ i, f i ∉ S ∧ G.Adj i.val (f i))
    (touching : ¬GeneralThree.wireBound G C S → ∀ {p q : Sym2 (Fin n)},
      p ∈ Ustar G C → q ∈ Ustar G C → p ≠ q → ∀ z : Fin n, z ∈ p → z ∉ q) :
    GeneralThree.wireBound G C S := by
  by_contra failure
  exact failure (three_disjoint four bip least top three
    (fun _ hp _ hq ne => touching failure hp hq ne) S f inj partners)

#print axioms three_from_touching
end DisjointBound
