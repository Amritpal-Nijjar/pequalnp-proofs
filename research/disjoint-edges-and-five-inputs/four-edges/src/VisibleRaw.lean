import SixGeometry

namespace VisibleRaw
open ActiveOr
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}


attribute [local instance] gateOpDecEq
/- The first-source induction and the common-neighbor argument below adapt Sarvesh Kapre's
   ActiveOr.lean and CommonLiteral.lean at 8ad50440ecd2520a5e3c727f7b1a19f079cac700.
   The shared raw literal is required only on exceptional ORs reached first from a top. -/
private theorem firstSource (ao : IsAO2 n C) (x : Fin n → Bool) (w : ℕ)
    (bound : w < n+C.gates.length) (raw : (orIn n C w).Nonempty)
    (fires : val C (List.ofFn x) w = true) :
    (∃ t ∈ orIn n C w, x t = true) ∨
      ∃ h ∈ orN G C \ lam G C, (orIn n C (n+h)).Nonempty ∧
        Relation.ReflTransGen (ordinaryStep G C) w (n+h) ∧ gateVal n C h x = true := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases input : w < n
    · let t : Fin n := ⟨w,input⟩
      exact .inl ⟨t,reach_mem_orIn t .refl,(val_ofFn C x t).symm.trans fires⟩
    obtain ⟨h,rfl⟩ : ∃ h, w = n+h := ⟨w-n,by omega⟩
    have len : h < C.gates.length := by omega
    obtain ⟨t,mt⟩ := raw
    have op : (gateAt C h).op = GateOp.or := by
      rcases ao.1 _ (gateAt_mem len) with a|o
      · rw [andRawEmpty a] at mt; exact ((Finset.notMem_empty _) mt).elim
      · exact o
    by_cases ordinary : h ∈ lam G C
    · obtain ⟨_,r0,r1,_⟩ := Finset.mem_filter.mp ordinary
      obtain ⟨v,member,smaller,on⟩ := (val_or (n := n) (by simp) len op).mp fires
      obtain ⟨i,vi⟩ := inputsAsOpnd ao len member
      have rv : (orIn n C v).Nonempty := by
        rw [vi]
        fin_cases i
        · exact r0
        · exact r1
      have step : OrStep n C (n+h) v := ⟨h,len,rfl,op,member,smaller⟩
      rcases ih v smaller (by omega) rv on with ⟨u,hu,yes⟩|⟨j,hj,present,path,yes⟩
      · exact .inl ⟨u,reach_mem_orIn u (.head step (mem_orIn_reach u hu)),yes⟩
      · exact .inr ⟨j,hj,present,.head ⟨step,h,ordinary,rfl⟩ path,yes⟩
    · have offTarget : ¬ BelowF G C h := by
        intro below
        have on := reach_var_val (pairInput t t) _ t (mem_orIn_reach t mt) (pairInput_left t t)
        exact G.irrefl ((graphFun_pair G t t).mp (below _ on))
      have exception : h ∈ orN G C \ lam G C := Finset.mem_sdiff.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr len,op,offTarget⟩,ordinary⟩
      exact .inr ⟨h,exception,⟨t,mt⟩,.refl,fires⟩

set_option maxHeartbeats 1200000 in
/-- A common raw literal of all nonempty exceptional ORs forces every
residual edge to have an endpoint in its retained neighborhood. -/
theorem old_neighbor (least : IsLeastAO G C) (empty : centreless G C = ∅)
    (w : Fin n) (common : ∀ h ∈ atTops G C, w ∈ orIn n C (n+h))
    (u v : Fin n) (he : s(u,v) ∈ Ustar G C) :
    (G.deleteEdges ↑(Ustar G C)).Adj w u ∨ (G.deleteEdges ↑(Ustar G C)).Adj w v := by
  classical
  let old := G.deleteEdges ↑(Ustar G C)
  have adj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
  obtain ⟨a,ma,fires⟩ := acceptedTop least adj
  obtain ⟨len,hand,_⟩ := topData ma
  have ne (p : Fin 2) : (side (n := n) C a p).Nonempty := by
    by_contra failed
    have zero := Finset.not_nonempty_iff_eq_empty.mp failed
    have cen : a ∈ centreless G C := by
      apply Finset.mem_filter.mpr
      refine ⟨ma,?_⟩
      fin_cases p
      · exact Or.inl zero
      · exact Or.inr zero
    rw [empty] at cen; exact Finset.notMem_empty _ cen
  have witnesses (p : Fin 2) : w ∈ side (n := n) C a p ∨ u ∈ side (n := n) C a p ∨ v ∈ side (n := n) C a p := by
    have bd := opndBound least.1 len p
    have on := (andValOperands least.1 len hand _).mp fires p
    rcases firstSource (G := G) least.1 _ _ (by omega) (ne p) on with ⟨t,mt,bit⟩|⟨h,hm,raw,path,_⟩
    · rcases (pairInput_true _ _ _).mp bit with rfl|rfl
      · exact Or.inr (Or.inl mt)
      · exact Or.inr (Or.inr mt)
    · have member : h∈atTops G C := Finset.mem_filter.mpr ⟨hm,raw,a,ma,p,path⟩
      exact Or.inl (reach_mem_orIn w ((DisjointCore.ordinary_path path).trans (mem_orIn_reach w (common _ member))))
  have cross {x y : Fin n} (hx : x ∈ side (n := n) C a 0) (hy : y ∈ side (n := n) C a 1) : old.Adj x y :=
    cleanAdj least.1 ma 0 hx hy
  have removed : ¬old.Adj u v := fun d => (SimpleGraph.deleteEdges_adj.mp d).2 he
  rcases witnesses 0 with wx|ux|vx <;> rcases witnesses 1 with wy|uy|vy
  · exact (old.irrefl (cross wx wy)).elim
  · exact Or.inl (cross wx uy)
  · exact Or.inr (cross wx vy)
  · exact Or.inl (cross ux wy).symm
  · exact (old.irrefl (cross ux uy)).elim
  · exact (removed (cross ux vy)).elim
  · exact Or.inr (cross vx wy).symm
  · exact (removed (cross vx uy).symm).elim
  · exact (old.irrefl (cross vx vy)).elim

/-- Every repeated vertex of the residual graph belongs to the retained
neighborhood of the common literal. Otherwise the two other endpoints and w
form a forbidden four-cycle. -/
theorem branch_vertex (four : NoFourCycle G) (least : IsLeastAO G C) (empty : centreless G C = ∅)
    (w : Fin n) (common : ∀ h ∈ atTops G C, w ∈ orIn n C (n+h))
    {v p q : Fin n} (distinct : p ≠ q) (vp : s(v,p) ∈ Ustar G C) (vq : s(v,q) ∈ Ustar G C) :
    (G.deleteEdges ↑(Ustar G C)).Adj w v := by
  by_contra no
  have wp := (old_neighbor least empty w common _ _ vp).resolve_left no
  have wq := (old_neighbor least empty w common _ _ vq).resolve_left no
  have vw : v ≠ w := by
    rintro rfl
    exact (SimpleGraph.deleteEdges_adj.mp wp).2 vp
  have ap := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp vp).1
  have aq := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp vq).1
  exact distinct (Finset.card_le_one.mp (four v w vw) p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ap, (SimpleGraph.deleteEdges_adj.mp wp).1⟩) q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, aq, (SimpleGraph.deleteEdges_adj.mp wq).1⟩))

/-- A path of three residual edges cannot occur in the common-literal case
for a bipartite graph with no four-cycle. The circuit can share arbitrary wires. -/
theorem no_three_edge_path (four : NoFourCycle G) (bip : G.IsBipartite)
    (least : IsLeastAO G C) (empty : centreless G C = ∅)
    (w : Fin n) (common : ∀ h ∈ atTops G C, w ∈ orIn n C (n+h))
    {a b c d : Fin n} (ac : a ≠ c) (bd : b ≠ d) (ab : s(a,b) ∈ Ustar G C)
    (bc : s(b,c) ∈ Ustar G C) (cd : s(c,d) ∈ Ustar G C) : False := by
  have ba : s(b,a) ∈ Ustar G C := Sym2.eq_swap ▸ ab
  have cb : s(c,b) ∈ Ustar G C := Sym2.eq_swap ▸ bc
  have wb := (SimpleGraph.deleteEdges_adj.mp (branch_vertex four least empty w common ac ba bc)).1
  have wc := (SimpleGraph.deleteEdges_adj.mp (branch_vertex four least empty w common bd cb cd)).1
  have edge : G.Adj b c := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp bc).1
  obtain ⟨color⟩ := bip
  have left := color.valid wb
  have right := color.valid wc
  have diff := color.valid edge
  omega

/-- A three-edge path forces both exceptional ORs to be first-visible, at any residual size. -/
theorem path_visible (four : NoFourCycle G) (bip : G.IsBipartite) (least : IsLeastAO G C)
    (empty : centreless G C = ∅) (two : (orN G C \ lam G C).card = 2)
    {a b c d : Fin n} (ac : a ≠ c) (bd : b ≠ d) (ab : s(a,b) ∈ Ustar G C)
    (bc : s(b,c) ∈ Ustar G C) (cd : s(c,d) ∈ Ustar G C) : atTops G C = orN G C \ lam G C := by
  classical
  refine Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) ?_
  rw [two]
  by_contra! small
  have pos := Finset.card_pos.mpr (atTops_nonempty least empty ⟨_,ab⟩)
  obtain ⟨h,eq⟩ := Finset.card_eq_one.mp (show (atTops G C).card = 1 by omega)
  have mem : h ∈ atTops G C := eq ▸ Finset.mem_singleton_self _
  obtain ⟨w,raw⟩ := (Finset.mem_filter.mp mem).2.1
  exact no_three_edge_path four bip least empty w (fun k hk => by
    have same : k=h := Finset.mem_singleton.mp (eq ▸ hk); simpa [same] using raw) ac bd ab bc cd
#print axioms path_visible
end VisibleRaw
