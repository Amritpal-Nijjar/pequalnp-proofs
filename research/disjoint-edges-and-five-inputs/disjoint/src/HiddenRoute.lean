import DisjointBound

namespace DisjointBound
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem ordinary_raw (ao : IsAO2 n C) {w v : ℕ} (start : (orIn n C w).Nonempty)
    (path : Relation.ReflTransGen (ActiveOr.ordinaryStep G C) w v) : (orIn n C v).Nonempty := by
  cases path with
  | refl => exact start
  | tail _ step =>
    obtain ⟨⟨g,len,eqG,_,member,_⟩,k,regular,eqK⟩ := step
    have same : k = g := by omega
    subst k
    obtain ⟨_,left,right,_⟩ := Finset.mem_filter.mp regular
    obtain ⟨i,eq⟩ := inputsAsOpnd ao len member
    rw [eq]
    fin_cases i
    · exact left
    · exact right

/-- At least one exception is actually unreachable via ordinary ORs from
    every top operand. Emptiness of its raw support cannot by itself explain
    the failure of the `atTops` membership test. -/
theorem matching_requires_unreachable (four : NoFourCycle G) (bip : G.IsBipartite)
    (least : IsLeastAO G C) (top : TopForm G C) (empty : centreless G C = ∅)
    (two : (junk G C).card = 2) (U : Finset (Sym2 (Fin n))) (sub : U ⊆ Ustar G C)
    (three : 3 ≤ U.card) (disj : SixBridge.disjointPairs U) :
    ∃ g ∈ orN G C \ lam G C, ∀ t ∈ tops G C, ∀ b : Fin 2,
      ¬Relation.ReflTransGen (ActiveOr.ordinaryStep G C) (opnd C t b) (n+g) := by
  classical
  obtain ⟨g,ex,hidden⟩ := matching_requires_hidden four bip least top empty two U sub three disj
  refine ⟨g,ex,?_⟩
  intro t ht b path
  exact hidden (Finset.mem_filter.mpr ⟨ex,ordinary_raw least.1 (topSides empty ht b) path,t,ht,b,path⟩)

#print axioms matching_requires_unreachable
end DisjointBound
