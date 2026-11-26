import CombineThree

namespace DisjointBound
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

abbrev PublishedFailureType (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Prop :=
  ∀ (four : NoFourCycle G) (bip : G.IsBipartite)
    (least : IsLeastAO G C) (top : TopForm G C) (three : (Ustar G C).card = 3)
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ i, f i ∉ S ∧ G.Adj i.val (f i)) (failure : ¬GeneralThree.wireBound G C S)
    {p q : Sym2 (Fin n)} (hp : p ∈ Ustar G C) (hq : q ∈ Ustar G C) (ne : p ≠ q),
    ∀ z : Fin n, z ∈ p → z ∉ q

theorem three_from_pinned_signature (published : PublishedFailureType G C) (four : NoFourCycle G) (bip : G.IsBipartite)
    (least : IsLeastAO G C) (top : TopForm G C) (three : (Ustar G C).card = 3)
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ i, f i ∉ S ∧ G.Adj i.val (f i)) : GeneralThree.wireBound G C S :=
  three_from_touching four bip least top three S f inj partners
    (fun failure => published four bip least top three S f inj partners failure)

#print axioms three_from_pinned_signature
end DisjointBound
