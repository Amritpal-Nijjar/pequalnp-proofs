import BothBridge
import TwoStarCert
import ThreeStarCert
import TriSingle
namespace DisconnectedFour
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open Chart6 BothGeometry
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem visibility (least : IsLeastAO G C) (empty : centreless G C=∅) (twoOr : (orN G C \ lam G C).card=2)
    (edges : (Ustar G C).Nonempty) :
    (∃ h,ActiveOr.atTops G C={h}) ∨ ActiveOr.atTops G C=orN G C \ lam G C := by
  classical
  have sub : ActiveOr.atTops G C ⊆ orN G C \ lam G C := Finset.filter_subset _ _
  by_cases eq : ActiveOr.atTops G C=orN G C \ lam G C
  · exact Or.inr eq
  have lo := Finset.card_pos.mpr (ActiveOr.atTops_nonempty least empty edges)
  have hi := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub,eq⟩)
  exact Or.inl (Finset.card_eq_one.mp (by omega))

/-- The complete exclusion for the two disconnected four-edge residuals.
    false is AB, AC, DE, DF. true is AB, AC, AE, DF. -/
theorem impossible (four : NoFourCycle G) (bip : G.IsBipartite) (least : IsLeastAO G C)
    (top : TopForm G C) (empty : centreless G C=∅) (two : (junk G C).card=2)
    (twoOr : (orN G C \ lam G C).card=2) (tri : Bool) (v : V→Fin n)
    (inj : Function.Injective v) (shape : Ustar G C=edgeSet tri v) : False := by
  have res := each shape
  rcases visibility least empty twoOr ⟨_,res 0⟩ with ⟨h,one⟩|both
  · cases tri
    · exact OneSignal.no_two_stars_single four bip least top empty two twoOr one v inj (res 0) (res 1) (res 2) (res 3)
    · exact TriSingle.no_star3_edge_single four bip least top empty two twoOr one v inj (res 0) (res 1) (res 2) (res 3)
  · obtain ⟨m,a,b,flip,pass⟩ := BothBridge.realize four bip least top empty two twoOr both tri v inj shape
    cases tri
    · exact Bool.false_ne_true ((TwoStarCert.impossible m a b flip).symm.trans pass)
    · exact Bool.false_ne_true ((ThreeStarCert.impossible m a b flip).symm.trans pass)
#print axioms impossible
end DisconnectedFour
