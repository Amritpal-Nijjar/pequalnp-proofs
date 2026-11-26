import BranchCharge
import VisibleRaw

namespace BranchCharge
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- One distinct later exceptional OR per residual neighbor missed by the other
    dirty AND, for a dirty AND firing on the central singleton. -/
theorem count_later_ors (four : NoFourCycle G) (least : IsLeastAO G C) (top : TopForm G C)
    (empty : centreless G C=∅) {j h : ℕ} (pair : junk G C={j,h}) (u : Fin n)
    (hot : gateVal n C h (pairInput u u)=true) (leaves : Finset (Fin n))
    (res : ∀ v∈leaves, s(u,v)∈Ustar G C)
    (off : ∀ v∈leaves, gateVal n C j (pairInput u v)=false) :
    leaves.card ≤ ((orN G C \ lam G C).filter (fun m => h < m)).card := by
  classical
  have select (v : leaves) := leaf_anchor least top empty pair u v.val (res _ v.2) (off _ v.2) hot
  choose pick mem higher raw cover using select
  let f (v : leaves) : ((orN G C \ lam G C).filter (fun m => h < m)) :=
    ⟨pick v,Finset.mem_filter.mpr ⟨mem v,higher v⟩⟩
  have inj : Function.Injective f := by
    intro a b same
    have equal : pick a=pick b := congrArg Subtype.val same
    obtain ⟨z,hz⟩ := raw a
    have za := SimpleGraph.deleteEdges_adj.mp (cover a z hz)
    have zb := SimpleGraph.deleteEdges_adj.mp (cover b z (equal ▸ hz))
    have zu : z≠u := by rintro rfl; exact za.2 (res _ a.2)
    apply Subtype.ext
    exact Finset.card_le_one.mp (four z u zu) a (Finset.mem_filter.mpr ⟨Finset.mem_univ _,za.1,
      SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (res _ a.2)).1⟩) b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,zb.1,
      SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (res _ b.2)).1⟩)
  simpa using Fintype.card_le_of_injective f inj

/-- With only one first-visible exceptional OR and two distinct residual
    vertices of degree at least two, its raw support consists of one vertex
    joined to both centers by retained edges. -/
theorem single_raw_center (four : NoFourCycle G) (least : IsLeastAO G C) (empty : centreless G C=∅)
    {h : ℕ} (single : ActiveOr.atTops G C={h}) {a b p q r s : Fin n} (ab : a≠b)
    (pq : p≠q) (rs : r≠s) (ap : s(a,p)∈Ustar G C) (aq : s(a,q)∈Ustar G C)
    (br : s(b,r)∈Ustar G C) (bs : s(b,s)∈Ustar G C) :
    ∃ w, orIn n C (n+h)={w} ∧ (G.deleteEdges ↑(Ustar G C)).Adj w a ∧ (G.deleteEdges ↑(Ustar G C)).Adj w b := by
  classical
  have mh : h∈ActiveOr.atTops G C := single ▸ Finset.mem_singleton_self _
  obtain ⟨w,hw⟩ := (Finset.mem_filter.mp mh).2.1
  have anchor (z : Fin n) (hz : z∈orIn n C (n+h)) :
      (G.deleteEdges ↑(Ustar G C)).Adj z a ∧ (G.deleteEdges ↑(Ustar G C)).Adj z b := by
    have all (k : ℕ) (hk : k∈ActiveOr.atTops G C) : z∈orIn n C (n+k) := by
      have eq : k=h := Finset.mem_singleton.mp (single ▸ hk)
      simpa [eq] using hz
    exact ⟨VisibleRaw.branch_vertex four least empty z all pq ap aq,
      VisibleRaw.branch_vertex four least empty z all rs br bs⟩
  have cn (z : Fin n) (hz : z∈orIn n C (n+h)) :
      z∈(Finset.univ.filter fun t => G.Adj a t ∧ G.Adj b t) := by
    obtain ⟨x,y⟩ := anchor z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(SimpleGraph.deleteEdges_adj.mp x).1.symm,(SimpleGraph.deleteEdges_adj.mp y).1.symm⟩
  refine ⟨w,?_,anchor w hw⟩
  ext z; rw [Finset.mem_singleton]
  exact ⟨fun hz => Finset.card_le_one.mp (four a b ab) z (cn z hz) w (cn w hw),fun eq => eq ▸ hw⟩
#print axioms count_later_ors
#print axioms single_raw_center
end BranchCharge
