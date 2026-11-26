import SixBridge
import SixExclusion
namespace DisjointBound
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem three_disjoint (four : NoFourCycle G) (bip : G.IsBipartite) (least : IsLeastAO G C) (top : TopForm G C)
    (three : (Ustar G C).card=3) (disj : SixBridge.disjointPairs (Ustar G C))
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ i, f i ∉ S ∧ G.Adj i.val (f i)) : GeneralThree.wireBound G C S :=
  SixBridge.disjoint_bound_of_exclusion SixTerms.no_terms four bip least top three disj S f inj partners
#print axioms three_disjoint

/-- A matching of three residual edges forces an exceptional OR outside
    the first exceptional ORs visible at the top, at any residual size. -/
theorem matching_requires_hidden (four : NoFourCycle G) (bip : G.IsBipartite)
    (least : IsLeastAO G C) (top : TopForm G C) (empty : centreless G C = ∅)
    (two : (junk G C).card = 2) (U : Finset (Sym2 (Fin n))) (sub : U ⊆ Ustar G C)
    (three : 3 ≤ U.card) (disj : SixBridge.disjointPairs U) :
    ∃ g ∈ orN G C \ lam G C, g ∉ ActiveOr.atTops G C := by
  classical
  by_contra! all
  have visible : ActiveOr.atTops G C = orN G C \ lam G C :=
    Finset.Subset.antisymm (Finset.filter_subset _ _) (fun _ m => all _ m)
  obtain ⟨V,inside,card⟩ := Finset.exists_subset_card_eq three
  have sep : SixBridge.disjointPairs V := fun e he f hf => disj e (inside he) f (inside hf)
  obtain ⟨m,a,b,pass⟩ := SixBridge.actual_passes four bip least top empty two visible V (inside.trans sub) card sep
  exact Bool.false_ne_true ((SixTerms.no_terms m a b).symm.trans pass)
#print axioms matching_requires_hidden

/-- Three disjoint residual edges force a third exceptional OR even when
    the rest of the residual graph is arbitrarily large. -/
theorem matching_forces_three_or (four : NoFourCycle G) (bip : G.IsBipartite)
    (least : IsLeastAO G C) (top : TopForm G C) (empty : centreless G C = ∅)
    (two : (junk G C).card = 2) (U : Finset (Sym2 (Fin n))) (sub : U ⊆ Ustar G C)
    (three : 3 ≤ U.card) (disj : SixBridge.disjointPairs U) : 3 ≤ (orN G C \ lam G C).card := by
  classical
  by_contra! few
  have subVis : ActiveOr.atTops G C ⊆ orN G C \ lam G C := Finset.filter_subset _ _
  have hi := Finset.card_le_card subVis
  have nonempty := (Finset.card_pos.mp (show 0 < U.card by omega)).mono sub
  have pos := Finset.card_pos.mpr (ActiveOr.atTops_nonempty least empty nonempty)
  have twoOr : (orN G C \ lam G C).card = 2 := by
    by_contra h
    obtain ⟨g,one⟩ := Finset.card_eq_one.mp (show (ActiveOr.atTops G C).card = 1 by omega)
    have cap := ActiveOr.single_capacity bip four least top empty g one U sub disj
    rw [two] at cap
    have pow : 2^3 ≤ 2^U.card := Nat.pow_le_pow_right (by decide) three
    omega
  have visible := ActiveOr.three_need_both bip four least top empty two twoOr U sub three disj
  obtain ⟨g,member,hidden⟩ := matching_requires_hidden four bip least top empty two U sub three disj
  exact hidden (visible ▸ member)
#print axioms matching_forces_three_or
end DisjointBound
