import LeafCount
import PathGeometry4
namespace StarCenters
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- For two distinct branching centers and one visible exception, neither center
    can be adjacent to a residual neighbor of the other. The only raw vertex at
    the visible exception lies outside both residual stars. -/
theorem no_cross (four : NoFourCycle G) (least : IsLeastAO G C) (empty : centreless G C=∅)
    {h : ℕ} (single : ActiveOr.atTops G C={h}) {a b p q r t : Fin n} (ab : a≠b)
    (pq : p≠q) (rt : r≠t) (ap : s(a,p)∈Ustar G C) (aq : s(a,q)∈Ustar G C)
    (br : s(b,r)∈Ustar G C) (bt : s(b,t)∈Ustar G C) :
    ∃ w, orIn n C (n+h)={w} ∧ w≠a ∧ w≠b ∧
      (∀ x, s(a,x)∈Ustar G C → x≠w ∧ ¬G.Adj b x) ∧
      (∀ y, s(b,y)∈Ustar G C → y≠w ∧ ¬G.Adj a y) := by
  obtain ⟨w,raw,wa,wb⟩ := BranchCharge.single_raw_center four least empty single ab pq rt ap aq br bt
  have left := SimpleGraph.deleteEdges_adj.mp wa.symm
  have right := SimpleGraph.deleteEdges_adj.mp wb.symm
  refine ⟨w,raw,wa.ne,wb.ne,?_,?_⟩
  · intro x edge
    have xw : x≠w := by rintro rfl; exact left.2 edge
    exact ⟨xw,FourPath.no_chord four ab.symm xw.symm right.1 left.1.symm
      (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp edge).1)⟩
  · intro x edge
    have xw : x≠w := by rintro rfl; exact right.2 edge
    exact ⟨xw,FourPath.no_chord four ab xw.symm left.1 right.1.symm
      (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp edge).1)⟩
#print axioms no_cross
end StarCenters
