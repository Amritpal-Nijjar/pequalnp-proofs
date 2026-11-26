import HiddenRaw4
import HiddenStarCert
namespace StarRawGlue
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open HiddenStarCert
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- The shared retained neighbor fixes the two colors, and sibling leaves
    cannot share a good raw support in a four-cycle-free graph. -/
theorem good_on_stars (four : NoFourCycle G) (bip : G.IsBipartite) (v : V→Fin n)
    (inj : Function.Injective v) (w : Fin n) (wa : G.Adj w (v 0)) (wd : G.Adj w (v 3))
    (e1 : s(v 0,v 1)∈Ustar G C) (e2 : s(v 0,v 2)∈Ustar G C)
    (e4 : s(v 3,v 4)∈Ustar G C) (e5 : s(v 3,v 5)∈Ustar G C)
    (A : Finset (Fin n)) (ok : SixGeometry.RawOK G C A) : good (fun x => decide (v x∈A))=true := by
  obtain ⟨col⟩ := bip
  have adj {i j : V} (e : s(v i,v j)∈Ustar G C) : G.Adj (v i) (v j) :=
    SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp e).1
  have center : col (v 0)=col (v 3) := by
    have a := col.valid wa; have b := col.valid wd
    omega
  have mono {i j : V} (u : v i∈A) (z : v j∈A) : col (v i)=col (v j) := by
    rcases ok with small|⟨k,old⟩
    · exact congrArg col (Finset.card_le_one.mp small _ u _ z)
    · have x := col.valid (SimpleGraph.deleteEdges_adj.mp (old _ u)).1
      have y := col.valid (SimpleGraph.deleteEdges_adj.mp (old _ z)).1
      omega
  have split : ¬((v 0∈A ∨ v 3∈A) ∧ (((v 1∈A ∨ v 2∈A) ∨ v 4∈A) ∨ v 5∈A)) := by
    rintro ⟨u,z⟩
    have c1 := col.valid (adj e1); have c2 := col.valid (adj e2)
    have c4 := col.valid (adj e4); have c5 := col.valid (adj e5)
    rcases u with a|a <;> rcases z with ((b|b)|b)|b <;> have eq := mono a b <;> omega
  have sib {i j k : V} (ij : i≠j) (ki : s(v k,v i)∈Ustar G C) (kj : s(v k,v j)∈Ustar G C) :
      ¬(v i∈A ∧ v j∈A) := fun both => SixGeometry.forbid_cross four ok (inj.ne ij) both.1 both.2
        (Sym2.eq_swap ▸ ki) (adj kj)
  simp only [good,Bool.and_eq_true,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,Bool.or_eq_true,decide_eq_true_eq]
  exact ⟨⟨split,sib (by decide) e1 e2⟩,sib (by decide) e4 e5⟩

/-- Wire equality for the sole exceptional raw mask gives precisely the
    pairwise compatibility tested in the six-vertex certificate. -/
theorem physical_masks (ao : IsAO2 n C) (empty : centreless G C=∅)
    (two : (orN G C \ lam G C).card=2) {h : ℕ} (one : ActiveOr.atTops G C={h})
    (v : V→Fin n) (port : Fin 4→ℕ) (inside : ∀ i,port i < n+C.gates.length)
    (geom : ∀ A : Finset (Fin n), SixGeometry.RawOK G C A → good (fun x => decide (v x∈A))=true) :
    raw (fun i x => decide (v x∈orIn n C (port i)))=true := by
  classical
  obtain ⟨k,_,regular⟩ := HiddenRaw4.only_hidden ao empty two one
  let m : M := fun i x => decide (v x∈orIn n C (port i))
  have pair (i j : Fin 4) : compatible (m i) (m j)=true := by
    by_cases a : port i=n+k
    · by_cases b : port j=n+k
      · have same : m i=m j := by dsimp [m]; rw [a,b]
        simp [compatible,equal,same]
      · have ok : good (m j)=true := geom _ (regular _ (inside j) b)
        simp [compatible,ok]
    · have ok : good (m i)=true := geom _ (regular _ (inside i) a)
      simp [compatible,ok]
  change raw m=true
  simp [raw,pair]
#print axioms good_on_stars
#print axioms physical_masks
end StarRawGlue
