import DeskMatching
namespace RemainingGeometry
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- The residual remaining under the four-edge circuit counts is a star, if
    this configuration occurs at all. No realizability assumption is needed. -/
theorem common_center (four : NoFourCycle G) (bip : G.IsBipartite) (least : IsLeastAO G C) (top : TopForm G C)
    (empty : centreless G C=∅) (two : (junk G C).card=2) (twoOr : (orN G C \ lam G C).card=2)
    (card : (Ustar G C).card=4) : ∃ z : Fin n, ∀ e∈Ustar G C, z∈e := by
  classical
  have F := FourMatching.forbidden four bip least top empty two twoOr card
  have edge {a b : Fin n} (ab : s(a,b)∈Ustar G C) : G.Adj a b := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp ab).1
  have meet (e f : Sym2 (Fin n)) (he : e∈Ustar G C) (hf : f∈Ustar G C) : ∃ x, x∈e ∧ x∈f := by
    induction e using Sym2.ind with
    | h a b =>
      induction f using Sym2.ind with
      | h c d =>
        by_contra! disj
        have an := disj a (Sym2.mem_mk_left _ _); have bn := disj b (Sym2.mem_mk_right _ _)
        simp only [Sym2.mem_iff,not_or] at an bn
        have nd : [a,b,c,d].Nodup := by simp [(edge he).ne,(edge hf).ne,an.1,an.2,bn.1,bn.2]
        exact EdgeCensus.exclude F card a b c d nd he hf
  obtain ⟨e,he,f,hf,ne⟩ := Finset.one_lt_card.mp (show 1 < (Ustar G C).card by omega)
  obtain ⟨z,ze,zf⟩ := meet e f he hf
  obtain ⟨p,rfl⟩ := Sym2.mem_iff_exists.mp ze
  obtain ⟨q,rfl⟩ := Sym2.mem_iff_exists.mp zf
  have pq : p≠q := fun eq => ne (eq ▸ rfl)
  refine ⟨z,fun g hg => ?_⟩
  by_contra missing
  obtain ⟨x,xg,xe⟩ := meet g _ hg he
  obtain ⟨y,yg,yf⟩ := meet g _ hg hf
  have xp : x=p := (Sym2.mem_iff.mp xe).resolve_left (fun eq => missing (eq ▸ xg))
  have yq : y=q := (Sym2.mem_iff.mp yf).resolve_left (fun eq => missing (eq ▸ yg))
  subst x; subst y
  have form := (Sym2.mem_and_mem_iff pq).mp ⟨xg,yg⟩
  subst g
  exact F.triangle z p q (by simp [(edge he).ne,(edge hf).ne,pq]) he hg (Sym2.eq_swap ▸ hf)
#print axioms common_center
end RemainingGeometry
