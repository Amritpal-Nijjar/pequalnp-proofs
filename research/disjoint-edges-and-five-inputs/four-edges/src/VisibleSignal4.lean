import LeafCount
namespace VisibleSignal4
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open ActiveOr
attribute [local instance] gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/- The three private lemmas below reproduce Sarvesh Kapre's ActiveOr source
   argument at 8ad50440ecd2520a5e3c727f7b1a19f079cac700; the ordinary-path
   conversion uses the equivalent reusable theorem in DisjointCore. -/
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

private theorem missing_operand (least : IsLeastAO G C) {u v : Fin n}
    (he : s(u,v) ∈ Ustar G C) {a : ℕ} (ha : a ∈ tops G C) :
    ∃ b : Fin 2, ¬ ∃ w ∈ side (n := n) C a b, w = u ∨ w = v := by
  classical
  let lit (b : Fin 2) := ∃ w ∈ side (n := n) C a b, w = u ∨ w = v
  have fresh : ∃ b, ¬ lit b := by
    by_contra! both
    obtain ⟨l,ml,hl⟩ := both 0
    obtain ⟨r,mr,hr⟩ := both 1
    have old := cleanAdj least.1 ha 0 ml mr
    obtain ⟨adj,kept⟩ := SimpleGraph.deleteEdges_adj.mp old
    rcases hl with rfl|rfl <;> rcases hr with rfl|rfl
    · exact adj.ne rfl
    · exact kept he
    · exact kept (Sym2.eq_swap .. ▸ he)
    · exact adj.ne rfl
  exact fresh

private theorem source (least : IsLeastAO G C) (empty : centreless G C = ∅)
    (h : ℕ) (unique : ∀ k ∈ atTops G C, k = h) (t : Fin n) (raw : t ∈ orIn n C (n+h))
    (u v : Fin n) (he : s(u,v) ∈ Ustar G C) :
    ∃ p d : Fin n, s(p,d) = s(u,v) ∧ (G.deleteEdges ↑(Ustar G C)).Adj t p ∧
      gateVal n C h (pairInput p d) = true ∧
      (∀ x : Fin n → Bool, x p = true → graphFun G ∅ x = false → gateVal n C h x = false) := by
  classical
  have real := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
  obtain ⟨a,ha,fire⟩ := acceptedTop least real
  have data := topData ha
  let lit (b : Fin 2) := ∃ w ∈ side (n := n) C a b, w = u ∨ w = v
  have fresh := missing_operand least he ha
  have route (b : Fin 2) (absent : ¬ lit b) :
      Relation.ReflTransGen (OrStep n C) (opnd C a b) (n+h) ∧
        gateVal n C h (pairInput u v) = true := by
    have on := (andValOperands least.1 data.1 data.2.1 _).mp fire b
    have bound := opndBound least.1 data.1 b
    have nonempty := topSides empty ha b
    rcases firstSource (G := G) least.1 _ _ (by omega) nonempty on with
        ⟨w,m,yes⟩ | ⟨k,elig,rawK,pathK,yes⟩
    · exact (absent ⟨w,m,(pairInput_true _ _ _).mp yes⟩).elim
    · have same := unique k (Finset.mem_filter.mpr ⟨elig,rawK,a,ha,b,pathK⟩)
      subst k
      exact ⟨DisjointCore.ordinary_path pathK,yes⟩
  obtain ⟨b,miss⟩ := fresh
  obtain ⟨path,on⟩ := route b miss
  have tl := reach_mem_orIn t (path.trans (mem_orIn_reach t raw))
  have oppositeHit : lit (1-b) := by
    by_contra no
    obtain ⟨path2,_⟩ := route (1-b) no
    have tr := reach_mem_orIn t (path2.trans (mem_orIn_reach t raw))
    exact (cleanAdj least.1 ha b tl tr).ne rfl
  obtain ⟨p,mp,sideEq⟩ := oppositeHit
  have old := cleanAdj least.1 ha b tl mp
  have safe (x : Fin n → Bool) (xp : x p = true) (off : graphFun G ∅ x = false) : gateVal n C h x = false := by
    apply Bool.eq_false_iff.mpr
    intro signal
    exact Bool.false_ne_true (off.symm.trans (firingTop least.1 ha path mp x signal xp))
  rcases sideEq with rfl|rfl
  · exact ⟨_,_,rfl,old,on,safe⟩
  · refine ⟨_,_,Sym2.eq_swap ..,old,?_,safe⟩
    have eq : pairInput p u = pairInput u p := by funext i; simp only [pairInput]; grind
    rwa [eq]

/-- An anchored endpoint is the guard on its residual edge in the one-visible
    configuration. This gives all residual positives and all guarded negatives. -/
theorem center_test (bip : G.IsBipartite) (least : IsLeastAO G C) (empty : centreless G C=∅)
    {h : ℕ} (one : atTops G C={h}) {w u v : Fin n} (raw : w∈orIn n C (n+h))
    (anchor : G.Adj w u) (res : s(u,v)∈Ustar G C) :
    gateVal n C h (pairInput u v)=true ∧
      (∀ x : Fin n → Bool, x u=true → graphFun G ∅ x=false → gateVal n C h x=false) := by
  have unique (k : ℕ) (hk : k∈atTops G C) : k=h := Finset.mem_singleton.mp (one ▸ hk)
  obtain ⟨p,d,edges,old,on,safe⟩ := source least empty h unique w raw u v res
  rcases Sym2.eq_iff.mp edges with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨on,safe⟩
  · obtain ⟨col⟩ := bip
    have a := col.valid anchor
    have b := col.valid (SimpleGraph.deleteEdges_adj.mp old).1
    have c := col.valid (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp res).1)
    change col d ≠ col p at c
    omega

/-- On each singleton/pair avoiding its single raw vertex, a visible OR is
    exactly the OR of the fixed subset of dirty ANDs in its OR-only cone. -/
theorem pair_signal (ao : IsAO2 n C) (top : TopForm G C) {h : ℕ} (visible : h∈atTops G C)
    {w : Fin n} (single : orIn n C (n+h)={w}) {u v : Fin n} (uw : u≠w) (vw : v≠w) :
    gateVal n C h (pairInput u v)=true ↔ ∃ k∈junk G C, OrReaches n C (n+h) k ∧ gateVal n C k (pairInput u v)=true := by
  obtain ⟨t,b,path⟩ := (DisjointCore.visible_earlier visible).2.2
  have tdata := topData t.2
  constructor
  · intro on
    have wire : val C (List.ofFn (pairInput u v)) (n+h)=true := (gateVal_eq_val n C h _ ▸ on)
    rcases operand_trace (C:=C) u v _ wire with ⟨z,eq,raw⟩|⟨k,inside,notOr,route,yes⟩
    · have zmem := reach_mem_orIn z raw
      rw [single,Finset.mem_singleton] at zmem
      rcases eq with rfl|rfl
      · exact (uw zmem).elim
      · exact (vw zmem).elim
    · have atTop := reach_orReaches ((orReaches_reach h _ path).1.trans route) k rfl inside
      have dirty := operandOrAndJunk ao top tdata.1 tdata.2.1 atTop ((ao.1 _ (gateAt_mem inside)).resolve_right notOr)
      exact ⟨k,dirty,reach_orReaches route k rfl inside,yes⟩
  · rintro ⟨k,_,route,yes⟩
    exact orStep_up (n:=n) (by simp : (List.ofFn (pairInput u v)).length=n) (orReaches_reach k _ route).1
      (gateVal_eq_val n C k _ ▸ yes)
#print axioms center_test
#print axioms pair_signal
end VisibleSignal4
