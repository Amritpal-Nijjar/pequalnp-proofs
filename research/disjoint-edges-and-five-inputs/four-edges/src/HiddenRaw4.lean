import SixGeometry
namespace HiddenRaw4
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open SixGeometry
attribute [local instance] gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- A wire whose raw support lacks a retained common neighbor must itself be a
    hidden exceptional OR. An indirect path through such an OR does not suffice. -/
theorem raw_except (ao : IsAO2 n C) (empty : centreless G C = ∅)
    (w : ℕ) (bound : w < n+C.gates.length)
    (outside : ∀ k∈(orN G C \ lam G C) \ ActiveOr.atTops G C, w≠n+k) : RawOK G C (orIn n C w) := by
  classical
  by_cases small : (orIn n C w).card ≤ 1
  · exact Or.inl small
  have nz : (orIn n C w).Nonempty := Finset.card_pos.mp (by omega)
  by_cases input : w<n
  · exfalso; apply small; apply Finset.card_le_one.mpr
    have eq (u : Fin n) (m : u ∈ orIn n C w) : u.val = w := by
      rcases Relation.ReflTransGen.cases_head (mem_orIn_reach u m) with h | ⟨_,step,_⟩
      · exact h.symm
      · obtain ⟨j,_,h,_,_,_⟩ := step; omega
    intro u hu v hv; exact Fin.ext ((eq u hu).trans (eq v hv).symm)
  obtain ⟨h,rfl⟩ : ∃ h, w = n+h := ⟨w-n,by omega⟩
  obtain ⟨u,mu⟩ := nz
  have len : h < C.gates.length := by omega
  have op : (gateAt C h).op = GateOp.or := by
    rcases ao.1 _ (gateAt_mem len) with ha|ho
    · rw [andRawEmpty ha] at mu; exact (Finset.notMem_empty _ mu).elim
    · exact ho
  have nonbelow : ¬BelowF G C h := by
    intro below
    have yes := reach_var_val (pairInput u u) _ u (mem_orIn_reach u mu) (pairInput_left u u)
    exact G.irrefl ((graphFun_pair G u u).mp (below _ yes))
  have inOr : h ∈ orN G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr len,op,nonbelow⟩
  have getTop : ∃ t : tops G C, ∃ j : Fin 2, OrReaches n C (opnd C t j) h := by
    by_cases regular : h ∈ lam G C
    · obtain ⟨_,_,_,a,ha,j,_,r⟩ := Finset.mem_filter.mp regular; exact ⟨⟨a,ha⟩,j,r⟩
    · have first : h∈ActiveOr.atTops G C := by
        by_contra hidden
        exact outside h (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨inOr,regular⟩,hidden⟩) rfl
      exact (DisjointCore.visible_earlier first).2.2
  obtain ⟨t,j,route⟩ := getTop
  obtain ⟨z,mz⟩ := topSides empty t.2 (1-j)
  right; refine ⟨z,fun x hx => ?_⟩
  have atPort := reach_mem_orIn x ((orReaches_reach h _ route).1.trans (mem_orIn_reach x hx))
  exact (cleanAdj ao t.2 j atPort mz).symm


/-- Two exceptions with a single first-visible exception leave at most one
    physical wire on which the raw-support condition can fail. -/
theorem only_hidden (ao : IsAO2 n C) (empty : centreless G C=∅)
    (two : (orN G C \ lam G C).card=2) {h : ℕ} (one : ActiveOr.atTops G C={h}) :
    ∃ k∈(orN G C \ lam G C) \ ActiveOr.atTops G C, ∀ w, w < n+C.gates.length →
      w ≠ n+k → RawOK G C (orIn n C w) := by
  classical
  have sub : ActiveOr.atTops G C ⊆ orN G C \ lam G C := Finset.filter_subset _ _
  have size := Finset.card_sdiff_of_subset sub
  rw [two,one] at size
  obtain ⟨k,e⟩ := Finset.card_eq_one.mp (show ((orN G C \ lam G C) \ ActiveOr.atTops G C).card=1 by
    simpa [one] using size)
  refine ⟨k,e ▸ Finset.mem_singleton_self _,fun w bound ne => raw_except ao empty w bound ?_⟩
  intro j hj
  have eq : j=k := Finset.mem_singleton.mp (e ▸ hj)
  simpa [eq] using ne
#print axioms only_hidden
end HiddenRaw4
