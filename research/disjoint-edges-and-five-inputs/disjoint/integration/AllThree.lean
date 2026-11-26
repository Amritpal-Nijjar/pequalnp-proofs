import CombineThree
import TwoTouching

namespace DisjointBound
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem three_edges (four : NoFourCycle G) (bip : G.IsBipartite)
    (least : IsLeastAO G C) (top : TopForm G C) (three : (Ustar G C).card = 3)
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ i, f i ∉ S ∧ G.Adj i.val (f i)) : GeneralThree.wireBound G C S :=
  three_from_touching four bip least top three S f inj partners
    (fun failure => DisjointEdgeBound.failure_requires_three_disjoint four bip least top three S f inj partners failure)

#print axioms three_edges
end DisjointBound
