import ResidualShrink

namespace BranchCharge
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
attribute [local instance] gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- An OR-only path from a raw-bearing operand down to a raw-empty wire crosses
    a raw-bearing exceptional OR strictly above the empty wire. -/
theorem crossing (ao : IsAO2 n C) {w y : ℕ} (path : Relation.ReflTransGen (OrStep n C) w y)
    (zero : orIn n C y=∅) (raw : (orIn n C w).Nonempty) :
    ∃ m ∈ orN G C \ lam G C, y < n+m ∧ n+m ≤ w ∧ (orIn n C (n+m)).Nonempty ∧
      Relation.ReflTransGen (OrStep n C) w (n+m) := by
  classical
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact (Finset.not_nonempty_empty (zero ▸ raw)).elim
  | head step trail ih =>
    obtain ⟨k,kl,eq,op,mem,lt⟩ := step
    subst eq
    have ordinaryStep : OrStep n C (n+k) _ := ⟨k,kl,rfl,op,mem,lt⟩
    by_cases regular : k∈lam G C
    · obtain ⟨_,nz0,nz1,_⟩ := Finset.mem_filter.mp regular
      obtain ⟨b,bw⟩ := inputsAsOpnd ao kl mem
      obtain ⟨m,ex,lower,upper,nz,route⟩ := ih (by rw [bw]; fin_cases b <;> assumption)
      exact ⟨m,ex,lower,by omega,nz,.head ordinaryStep route⟩
    · obtain ⟨v,mv⟩ := raw
      have outside : ¬BelowF G C k := by
        intro clean
        have on := reach_var_val (pairInput v v) _ v (mem_orIn_reach v mv) (pairInput_left v v)
        exact G.irrefl ((graphFun_pair G v v).mp (clean _ on))
      have above := orStep_le trail
      exact ⟨k,Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr kl,op,outside⟩,regular⟩,
        by omega,le_rfl,⟨v,mv⟩,.refl⟩

/-- A raw-bearing operand of an AND that fires without either positive endpoint
    as a raw input requires an exceptional OR strictly before that AND. -/
theorem earlier (ao : IsAO2 n C) (top : TopForm G C) {h : ℕ} (hm : h∈junk G C)
    (b : Fin 2) (raw : (side (n:=n) C h b).Nonempty) (x y : Fin n)
    (absent : x∉side (n:=n) C h b ∧ y∉side C h b) (on : gateVal n C h (pairInput x y)=true) :
    ∃ m∈orN G C \ lam G C, m<h := by
  obtain ⟨hl,op,_⟩ := junkData hm
  have fired := (andValOperands ao hl op _).mp on b
  rcases operandSupport ao top hl op fired with ⟨p,mem,rfl|rfl⟩ | ⟨k,dirty,path,_⟩
  · exact (absent.1 mem).elim
  · exact (absent.2 mem).elim
  · have zero := andRawEmpty (n:=n) (junkData dirty).2.1
    obtain ⟨m,ex,_,le,_,_⟩ := crossing (G:=G) ao (orReaches_reach k _ path).1 zero raw
    have bd := opndBound ao hl b
    exact ⟨m,ex,by omega⟩

theorem leaf_anchor (least : IsLeastAO G C) (top : TopForm G C) (empty : centreless G C=∅)
    {j h : ℕ} (pair : junk G C={j,h}) (u v : Fin n) (res : s(u,v)∈Ustar G C)
    (off : gateVal n C j (pairInput u v)=false) (hot : gateVal n C h (pairInput u u)=true) :
    ∃ m∈orN G C \ lam G C, h < m ∧ (orIn n C (n+m)).Nonempty ∧
      ∀ z∈orIn n C (n+m), (G.deleteEdges ↑(Ustar G C)).Adj z v := by
  obtain ⟨t,tm,b,k,km,accept,path,kOn⟩ := residualTrace least top res
  have same {r : ℕ} (mem : r∈junk G C) (on : gateVal n C r (pairInput u v)=true) : r=h := by
    simp only [pair,Finset.mem_insert,Finset.mem_singleton] at mem
    exact mem.resolve_left (fun eq => Bool.false_ne_true (off.symm.trans (eq ▸ on)))
  have kh := same km kOn
  subst k
  obtain ⟨tl,op,clean⟩ := topData tm
  have route := (orReaches_reach h _ path).1
  have active : val C (List.ofFn (pairInput u u)) (opnd C t b)=true := orStep_up (by simp) route hot
  have quiet : val C (List.ofFn (pairInput u u)) (opnd C t (1-b))≠true := by
    intro wrong
    have topOn := (andValOperands least.1 tl op (pairInput u u)).2 (fun a => by
      rcases opposite b a with rfl|rfl <;> assumption)
    exact G.irrefl ((graphFun_pair G u u).mp (clean _ topOn))
  have other : v∈side (n:=n) C t (1-b) := by
    have on := (andValOperands least.1 tl op _).1 accept (1-b)
    rcases operandSupport least.1 top tl op on with ⟨z,mem,rfl|rfl⟩|⟨i,im,pth,yes⟩
    · exact (quiet (sideVal mem (pairInput_left _ _))).elim
    · exact mem
    · have eq := same im yes; subst i
      exact (quiet (orStep_up (by simp) (orReaches_reach h _ pth).1 hot)).elim
  obtain ⟨m,ex,lt,_,raw,toM⟩ := crossing (G:=G) least.1 route (andRawEmpty (junkData km).2.1) (topSides empty tm b)
  exact ⟨m,ex,by omega,raw,fun z mz => cleanAdj least.1 tm b
    (reach_mem_orIn z (toM.trans (mem_orIn_reach z mz))) other⟩

/-- The earlier exceptional OR and two different later anchor ORs are three
    distinct resources. This applies with any number of other residual edges. -/
theorem three_for_branch (four : NoFourCycle G) (least : IsLeastAO G C) (top : TopForm G C)
    (empty : centreless G C=∅) {j h : ℕ} (pair : junk G C={j,h})
    (prior : ∃ m∈orN G C \ lam G C, m<h) {u v w : Fin n} (vw : v≠w)
    (uv : s(u,v)∈Ustar G C) (uw : s(u,w)∈Ustar G C)
    (vOff : gateVal n C j (pairInput u v)=false) (wOff : gateVal n C j (pairInput u w)=false)
    (hot : gateVal n C h (pairInput u u)=true) : 3 ≤ (orN G C \ lam G C).card := by
  classical
  obtain ⟨b,bm,bh⟩ := prior
  obtain ⟨p,pm,hp,pnz,pc⟩ := leaf_anchor least top empty pair u v uv vOff hot
  obtain ⟨q,qm,hq,_,qc⟩ := leaf_anchor least top empty pair u w uw wOff hot
  have diff : p≠q := by
    rintro rfl
    obtain ⟨z,mem⟩ := pnz
    have zv := SimpleGraph.deleteEdges_adj.mp (pc z mem)
    have zw := SimpleGraph.deleteEdges_adj.mp (qc z mem)
    have zu : z≠u := by rintro rfl; exact zv.2 uv
    exact vw (Finset.card_le_one.mp (four z u zu) v (Finset.mem_filter.mpr ⟨Finset.mem_univ _,zv.1,
      SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp uv).1⟩) w (Finset.mem_filter.mpr ⟨Finset.mem_univ _,zw.1,
      SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp uw).1⟩))
  have inside : ({b,p,q} : Finset ℕ) ⊆ orN G C \ lam G C := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl <;> assumption
  have size := Finset.card_le_card inside
  simpa [show b≠p by omega,show b≠q by omega,diff] using size
#print axioms three_for_branch
end BranchCharge
