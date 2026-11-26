import FourMatching
namespace DeskMatching
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- In the official statement's matching representation, the previously open
    four-residual, two-matched, two-dirty, zero-centerless, two-OR counts
    are incompatible with a physical least top-form circuit. -/
theorem cap (four : NoFourCycle G) (bip : G.IsBipartite) (least : IsLeastAO G C) (top : TopForm G C)
    (empty : centreless G C=∅) (two : (junk G C).card=2) (twoOr : (orN G C \ lam G C).card=2)
    (card : (Ustar G C).card=4) (S : Finset (Fin n)) (f : S→Fin n) (inj : Function.Injective f)
    (partners : ∀ i, f i∉S ∧ G.Adj i.val (f i)) :
    (GeneralThree.matchingEdges S f ∩ Ustar G C).card≤1 := by
  classical
  apply FourMatching.matching_cap four bip least top empty two twoOr card _ Finset.inter_subset_right
  intro e he g hg ne v left right
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp he).1
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hg).1
  have ij : i≠j := fun eq => ne (eq ▸ rfl)
  rcases Sym2.mem_iff.mp left with rfl|rfl <;> rcases Sym2.mem_iff.mp right with eq|eq
  · exact ij (Subtype.ext eq)
  · exact (partners j).1 (eq ▸ i.2)
  · exact (partners i).1 (eq.symm ▸ j.2)
  · exact ij (inj eq)
#print axioms cap
end DeskMatching
