import DisjointCore
import SixTerms
namespace SixGeometry
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open SixTerms
attribute [local instance] gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

abbrev old (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) := G.deleteEdges ↑(Ustar G C)
def RawOK (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (R : Finset (Fin n)) : Prop :=
  R.card ≤ 1 ∨ ∃ z, ∀ u ∈ R, (old G C).Adj z u
def bit (v : I → Fin n) (R : Finset (Fin n)) (i : I) := decide (v i ∈ R)

/-- Every globally raw-bearing internal wire belongs to an OR outside the
    graph function. Visibility of both exceptions therefore gives a retained
    common neighbor for any multi-vertex raw support. -/
theorem actual_raw (ao : IsAO2 n C) (empty : centreless G C = ∅)
    (visible : ActiveOr.atTops G C = orN G C \ lam G C)
    (w : ℕ) (bound : w < n+C.gates.length) : RawOK G C (orIn n C w) := by
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
    · exact (DisjointCore.visible_earlier (visible ▸ Finset.mem_sdiff.mpr ⟨inOr,regular⟩)).2.2
  obtain ⟨t,j,route⟩ := getTop
  obtain ⟨z,mz⟩ := topSides empty t.2 (1-j)
  right; refine ⟨z,fun x hx => ?_⟩
  have atPort := reach_mem_orIn x ((orReaches_reach h _ route).1.trans (mem_orIn_reach x hx))
  exact (cleanAdj ao t.2 j atPort mz).symm

theorem mono_of (v : I → Fin n) (inj : Function.Injective v) (col : G.Coloring (Fin 2))
    (align : ∀ p q : I, col (v p) = col (v q) ↔ p.2 = q.2)
    (R : Finset (Fin n)) (good : RawOK G C R) : mono (bit v R) = true := by
  classical
  have same (i j : I) (hi : v i ∈ R) (hj : v j ∈ R) : i.2=j.2 := by
    rcases good with s|⟨z,m⟩
    · exact congrArg Prod.snd (inj (Finset.card_le_one.mp s _ hi _ hj))
    · apply (align i j).mp
      have a := col.valid (SimpleGraph.deleteEdges_adj.mp (m _ hi)).1
      have b := col.valid (SimpleGraph.deleteEdges_adj.mp (m _ hj)).1
      omega
  by_cases hit : ∃ i : Fin 3, v (i,false) ∈ R
  · obtain ⟨i,hi⟩ := hit
    have off (j : Fin 3) : v (j,true) ∉ R := fun hj => Bool.false_ne_true (same (i,false) (j,true) hi hj)
    have t : all3 (fun j => !bit v R (j,true)) = true := (all3_iff _).mpr (fun j => by simp [bit,off j])
    simp [mono,t]
  · have off (j : Fin 3) : v (j,false) ∉ R := fun m => hit ⟨j,m⟩
    have t : all3 (fun j => !bit v R (j,false)) = true := (all3_iff _).mpr (fun j => by simp [bit,off j])
    simp [mono,t]

/-- If u,w share a raw port and u has residual partner d, then w cannot be
    adjacent to d. Otherwise the retained common neighbor and d make a C4. -/
theorem forbid_cross (four : NoFourCycle G) {R : Finset (Fin n)} (good : RawOK G C R)
    {u w d : Fin n} (different : u ≠ w) (ru : u ∈ R) (rw : w ∈ R)
    (res : s(u,d) ∈ Ustar G C) : ¬G.Adj d w := by
  intro edge
  rcases good with small|⟨z,conn⟩
  · exact different (Finset.card_le_one.mp small _ ru _ rw)
  have zu := SimpleGraph.deleteEdges_adj.mp (conn u ru)
  have zw := SimpleGraph.deleteEdges_adj.mp (conn w rw)
  have du := (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp res).1).symm
  have ne : z ≠ d := by rintro rfl; exact zu.2 (Sym2.eq_swap ▸ res)
  exact different (Finset.card_le_one.mp (four z d ne) u (Finset.mem_filter.mpr ⟨Finset.mem_univ _,zu.1,du⟩)
    w (Finset.mem_filter.mpr ⟨Finset.mem_univ _,zw.1,edge⟩))

theorem actual_allowed (v : I → Fin n) (inj : Function.Injective v) (four : NoFourCycle G)
    (col : G.Coloring (Fin 2)) (align : ∀ p q : I, col (v p) = col (v q) ↔ p.2 = q.2)
    (res : ∀ i : Fin 3, s(v (i,false),v (i,true)) ∈ Ustar G C)
    (R : Fin 4 → Finset (Fin n)) (good : ∀ k, RawOK G C (R k)) (p q : I)
    (edge : G.Adj (v p) (v q)) : allowed (fun k => bit v (R k)) p q = true := by
  classical
  have diff : p.2 ≠ q.2 := fun h => col.valid edge ((align p q).mpr h)
  unfold allowed
  apply Bool.and_eq_true_iff.mpr
  refine ⟨by simpa using diff,?_⟩
  by_cases same : p.1=q.1
  · simp [same]
  simp only [beq_eq_false_iff_ne.mpr same,Bool.false_or]
  apply (all4_iff _).mpr
  intro k
  have hz (b : Bool) : ¬(v (p.1,b) ∈ R k ∧ v (q.1,b) ∈ R k) := by
    rintro ⟨l,r⟩
    have ne : v (p.1,b) ≠ v (q.1,b) := by
      intro h
      have he := congrArg (fun r : I => r.1) (@inj (p.1,b) (q.1,b) h)
      exact same he
    obtain ⟨pi,pc⟩ := p; obtain ⟨qi,qc⟩ := q
    cases pc <;> cases qc <;> cases b <;> first
      | exact (diff rfl).elim
      | exact forbid_cross four (good k) ne l r (res pi) edge
      | exact forbid_cross four (good k) ne l r (Sym2.eq_swap ▸ res pi) edge
      | exact forbid_cross four (good k) ne.symm r l (res qi) edge.symm
      | exact forbid_cross four (good k) ne.symm r l (Sym2.eq_swap ▸ res qi) edge.symm
  simp only [bit,Bool.and_eq_true,Bool.not_eq_true',Bool.and_eq_false_iff,decide_eq_false_iff_not]
  exact ⟨not_and_or.mp (hz false),not_and_or.mp (hz true)⟩
end SixGeometry
