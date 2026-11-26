import HiddenRaw4
import ResidualShrink
import StarGrowth
import GeneralThree
import RemainingGeometry

namespace StarLeafBudget
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
attribute [local instance] gateOpDecEq

noncomputable abbrev hidden (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :=
  (orN G C \ lam G C) \ ActiveOr.atTops G C

/-- Two leaves of the same residual star cannot both lie in a raw support
that is small or has a common neighbour along retained edges. -/
theorem thin {v : Fin n} {L A : Finset (Fin n)} (four : NoFourCycle G)
    (res : ∀ l∈L, s(v,l)∈Ustar G C) (good : SixGeometry.RawOK G C A) :
    (A ∩ L).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro p hp q hq
  by_contra ne
  obtain ⟨cp, lp⟩ := Finset.mem_inter.mp hp
  obtain ⟨cq, lq⟩ := Finset.mem_inter.mp hq
  exact SixGeometry.forbid_cross four good ne cp cq (Sym2.eq_swap .. ▸ res p lp)
    (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (res q lq)).1)

private theorem trim_subset (four : NoFourCycle G) (ao : IsAO2 n C)
    (H : Finset ℕ) (exceptional : H ⊆ orN G C \ lam G C)
    (controlled : ∀ w < n+C.gates.length, (∀ j∈H, w ≠ n+j) → SixGeometry.RawOK G C (orIn n C w))
    (v : Fin n) (L : Finset (Fin n))
    (res : ∀ l∈L, s(v,l)∈Ustar G C) :
    ∀ t ≤ C.gates.length, ∃ K ⊆ L,
      L.card ≤ K.card + (H.filter (fun j => j<t)).card ∧
      ∀ w < n+t, ((orIn n C w) ∩ K).card ≤ 1 := by
  classical
  have regular (w : ℕ) (bw : w < n+C.gates.length)
      (clean : ∀ j∈H, w ≠ n+j) (K : Finset (Fin n)) (sub : K ⊆ L) :
      ((orIn n C w) ∩ K).card ≤ 1 :=
    thin four (fun x hx => res x (sub hx)) (controlled w bw clean)
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨L, Finset.Subset.rfl, by simp, ?_⟩
    intro w hw
    exact regular w (by omega) (fun j _ => by omega) L Finset.Subset.rfl
  | succ t ih =>
    intro size
    have lt : t < C.gates.length := by omega
    obtain ⟨K,sub,budget,old⟩ := ih (by omega)
    by_cases hid : t∈H
    · have inOr := (Finset.mem_sdiff.mp (exceptional hid)).1
      have op : (gateAt C t).op = GateOp.or := (Finset.mem_filter.mp inOr).2.1
      let cut := (side (n := n) C t 0) ∩ K
      let T := K \ cut
      have subT : T ⊆ K := Finset.sdiff_subset
      have cutSub : cut ⊆ K := Finset.inter_subset_right
      have cutSmall : cut.card ≤ 1 := old (opnd C t 0) (opndBound ao lt _)
      have split : T.card + cut.card = K.card := Finset.card_sdiff_add_card_eq_card cutSub
      have below : H.filter (fun j => j < t+1) = insert t (H.filter (fun j => j<t)) := by
        ext i
        simp only [Finset.mem_filter,Finset.mem_insert]
        constructor
        · rintro ⟨hi,bi⟩
          by_cases eq : i=t
          · exact Or.inl eq
          · exact Or.inr ⟨hi,by omega⟩
        · rintro (rfl|⟨hi,bi⟩)
          · exact ⟨hid,by omega⟩
          · exact ⟨hi,by omega⟩
      have add : (H.filter (fun j => j<t+1)).card = (H.filter (fun j => j<t)).card+1 := by
        rw [below,Finset.card_insert_of_notMem (by simp)]
      refine ⟨T,subT.trans sub, ?_, ?_⟩
      · change L.card ≤ T.card + (H.filter (fun j => j<t+1)).card
        change L.card ≤ K.card + (H.filter (fun j => j<t)).card at budget
        omega
      intro w hw
      by_cases earlier : w<n+t
      · exact (Finset.card_le_card (Finset.inter_subset_inter_left (s := orIn n C w) subT)).trans (old w earlier)
      have eq : w=n+t := by omega
      rw [eq,orRawUnion ao lt op]
      have transfer : ((side (n:=n) C t 0 ∪ side C t 1) ∩ T) ⊆ side C t 1 ∩ K := by
        intro u hu
        obtain ⟨mem,inT⟩ := Finset.mem_inter.mp hu
        have inK := subT inT
        refine Finset.mem_inter.mpr ⟨?_, inK⟩
        rcases Finset.mem_union.mp mem with h | h
        · exact ((Finset.mem_sdiff.mp inT).2 (Finset.mem_inter.mpr ⟨h,inK⟩)).elim
        · exact h
      exact (Finset.card_le_card transfer).trans (old (opnd C t 1) (opndBound ao lt _))
    · refine ⟨K,sub,?_,?_⟩
      · have inc : H.filter (fun j => j<t) ⊆ H.filter (fun j => j<t+1) := by
          intro j hj
          obtain ⟨inH, prior⟩ := Finset.mem_filter.mp hj
          exact Finset.mem_filter.mpr ⟨inH, Nat.lt_succ_of_lt prior⟩
        exact budget.trans (Nat.add_le_add_left (Finset.card_le_card inc) _)
      intro w hw
      by_cases earlier : w<n+t
      · exact old w earlier
      have eq : w = n+t := by omega
      apply regular w (by omega) _ K sub
      intro j hj same
      have je : j=t := by omega
      exact hid (je ▸ hj)

/-- Each hidden exceptional OR can increase the number of leaves to be
accounted for by at most one. Each remaining leaf needs a dirty AND. -/
theorem leaf_bound_of_control (four : NoFourCycle G) (least : IsLeastAO G C) (top : TopForm G C)
    (H : Finset ℕ) (exceptional : H ⊆ orN G C \ lam G C)
    (controlled : ∀ w < n+C.gates.length, (∀ j∈H, w ≠ n+j) → SixGeometry.RawOK G C (orIn n C w))
    (v : Fin n)
    (center : ∀ e∈Ustar G C, v∈e) (L : Finset (Fin n))
    (res : ∀ l∈L, s(v,l)∈Ustar G C) :
    L.card ≤ (junk G C).card + H.card := by
  classical
  obtain ⟨K,sub,budget,thinK⟩ := trim_subset four least.1 H exceptional controlled v L res C.gates.length (le_refl _)
  have sparse (j : ℕ) (hj : j∈junk G C) (b : Fin 2) :
      ((side (n:=n) C j b) ∩ K).card ≤ 1 := by
    obtain ⟨len,_,_⟩ := junkData hj
    have h := opndBound least.1 len b
    exact thinK _ (by omega)
  have changes (l : Fin n) (hl : l∈K) :
      ∃ j∈junk G C, gateVal n C j (pairInput v v)=false ∧ gateVal n C j (pairInput v l)=true := by
    have edge := res l (sub hl)
    obtain ⟨_,_,_,j,hj,_,on⟩ := PEqualNP.Outside.L_meta_8005.residualTrace least top edge
    refine ⟨j,hj, Bool.eq_false_iff.mpr ?_, on⟩
    intro hot
    have graphEdges : G.edgeFinset.Nonempty := ⟨_, (Finset.mem_sdiff.mp edge).1⟩
    obtain ⟨p,q,hpq,pv,qv,_⟩ := ResidualChange.residual_witness least top graphEdges hj v hot
    rcases Sym2.mem_iff.mp (center _ hpq) with e|e
    · exact pv e.symm
    · exact qv e.symm
  have residual := StarGrowth.first_changes least.1 top v K sparse changes
  have count := Finset.card_le_card (Finset.filter_subset (fun j => j < C.gates.length) H)
  omega

theorem leaf_bound (four : NoFourCycle G) (least : IsLeastAO G C) (top : TopForm G C)
    (empty : centreless G C = ∅) (v : Fin n)
    (center : ∀ e∈Ustar G C, v∈e) (L : Finset (Fin n))
    (res : ∀ l∈L, s(v,l)∈Ustar G C) :
    L.card ≤ (junk G C).card + (hidden G C).card :=
  leaf_bound_of_control four least top _ Finset.sdiff_subset
    (HiddenRaw4.raw_except least.1 empty) v center L res

#print axioms leaf_bound
end StarLeafBudget

namespace OrdinaryStar
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
attribute [local instance] gateOpDecEq

/-- An ordinary OR reaches a top whose opposite side contains one vertex.
Consequently the raw-support argument of HiddenRaw4 still applies to these
wires even when other tops have an empty side. -/
theorem raw_control (ao : IsAO2 n C) (w : ℕ) (bound : w < n+C.gates.length)
    (outside : ∀ k∈orN G C \ lam G C, w≠n+k) : SixGeometry.RawOK G C (orIn n C w) := by
  classical
  by_cases small : (orIn n C w).card ≤ 1
  · exact Or.inl small
  have nz : (orIn n C w).Nonempty := Finset.card_pos.mp (by omega)
  by_cases input : w<n
  · exfalso
    apply small
    apply Finset.card_le_one.mpr
    have eq (u : Fin n) (m : u∈orIn n C w) : u.val = w := by
      rcases Relation.ReflTransGen.cases_head (mem_orIn_reach u m) with h | ⟨_,step,_⟩
      · exact h.symm
      · obtain ⟨j,_,h,_,_,_⟩ := step
        omega
    intro u hu v hv
    exact Fin.ext ((eq u hu).trans (eq v hv).symm)
  obtain ⟨h,rfl⟩ : ∃ h, w = n+h := ⟨w-n,by omega⟩
  obtain ⟨u,mu⟩ := nz
  have len : h < C.gates.length := by omega
  have op : (gateAt C h).op = GateOp.or := by
    rcases ao.1 _ (gateAt_mem len) with ha|ho
    · rw [andRawEmpty ha] at mu
      exact (Finset.notMem_empty _ mu).elim
    · exact ho
  have nonbelow : ¬BelowF G C h := by
    intro below
    have yes := reach_var_val (pairInput u u) _ u (mem_orIn_reach u mu) (pairInput_left u u)
    exact G.irrefl ((graphFun_pair G u u).mp (below _ yes))
  have member : h∈orN G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr len,op,nonbelow⟩
  have regular : h∈lam G C := by
    by_contra missing
    exact outside h (Finset.mem_sdiff.mpr ⟨member,missing⟩) rfl
  obtain ⟨_,_,_,a,ha,b,one,route⟩ := Finset.mem_filter.mp regular
  obtain ⟨z,mz⟩ := Finset.card_pos.mp (show 0 < (side (n:=n) C a (1-b)).card by omega)
  right
  refine ⟨z,fun x hx => ?_⟩
  have atPort := reach_mem_orIn x ((orReaches_reach h _ route).1.trans (mem_orIn_reach x hx))
  exact (cleanAdj ao ha b atPort mz).symm

#print axioms raw_control
end OrdinaryStar

namespace StarWire
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- The nonempty residual star requires at least one more counted gate than
its number of edges. The visible exceptional OR and the hidden ones play
different roles in this estimate. -/
theorem star_cost (four : NoFourCycle G) (least : IsLeastAO G C) (top : TopForm G C)
    (empty : centreless G C = ∅) (nonempty : (Ustar G C).Nonempty)
    (v : Fin n) (center : ∀ e∈Ustar G C, v∈e) :
    (Ustar G C).card + 1 ≤ (junk G C).card + (orN G C \ lam G C).card := by
  classical
  let L : Finset (Fin n) := Finset.univ.filter (fun l => s(v,l) ∈ Ustar G C)
  have res (l : Fin n) (mem : l∈L) : s(v,l)∈Ustar G C := (Finset.mem_filter.mp mem).2
  have all : Ustar G C ⊆ L.image (fun l => s(v,l)) := by
    intro e mem
    obtain ⟨l,rfl⟩ := Sym2.mem_iff_exists.mp (center e mem)
    exact Finset.mem_image.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,mem⟩,rfl⟩
  have size := (Finset.card_le_card all).trans Finset.card_image_le
  have leaf := StarLeafBudget.leaf_bound four least top empty v center L res
  have visible := ActiveOr.atTops_nonempty least empty nonempty
  have sub : ActiveOr.atTops G C ⊆ orN G C \ lam G C := Finset.filter_subset _ _
  have split := Finset.card_sdiff_add_card_eq_card sub
  change (StarLeafBudget.hidden G C).card + (ActiveOr.atTops G C).card = (orN G C \ lam G C).card at split
  have pos := Finset.card_pos.mpr visible
  omega

/-- With a centerless top, all exceptional ORs can be charged. That top
already contributes two units to the project's gate accounting inequality. -/
theorem star_cost_all (four : NoFourCycle G) (least : IsLeastAO G C) (top : TopForm G C)
    (nonempty : (Ustar G C).Nonempty) (v : Fin n) (center : ∀ e∈Ustar G C, v∈e) :
    (Ustar G C).card + 1 ≤ 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card := by
  classical
  by_cases empty : centreless G C = ∅
  · simpa [empty] using star_cost four least top empty nonempty v center
  let L : Finset (Fin n) := Finset.univ.filter (fun l => s(v,l) ∈ Ustar G C)
  have res (l : Fin n) (mem : l∈L) : s(v,l)∈Ustar G C := (Finset.mem_filter.mp mem).2
  have all : Ustar G C ⊆ L.image (fun l => s(v,l)) := by
    intro e mem
    obtain ⟨l,rfl⟩ := Sym2.mem_iff_exists.mp (center e mem)
    exact Finset.mem_image.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,mem⟩,rfl⟩
  have size := (Finset.card_le_card all).trans Finset.card_image_le
  have leaf := StarLeafBudget.leaf_bound_of_control four least top _ Finset.Subset.rfl
    (OrdinaryStar.raw_control least.1) v center L res
  have positive := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
  omega

private theorem matching_one (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ i, f i ∉ S ∧ G.Adj i.val (f i)) (v : Fin n) (center : ∀ e∈Ustar G C, v∈e) :
    (GeneralThree.matchingEdges S f ∩ Ustar G C).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro e he g hg
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp he).1
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hg).1
  have a := Sym2.mem_iff.mp (center _ (Finset.mem_inter.mp he).2)
  have b := Sym2.mem_iff.mp (center _ (Finset.mem_inter.mp hg).2)
  have eq : i=j := by
    rcases a with a|a <;> rcases b with b|b
    · exact Subtype.ext (a.symm.trans b)
    · exact ((partners j).1 ((a.symm.trans b) ▸ i.2)).elim
    · exact ((partners i).1 ((b.symm.trans a) ▸ j.2)).elim
    · exact inj (a.symm.trans b)
  subst j
  rfl

/-- For an arbitrary matching the repeated-wire-read bound of L-meta-17625
holds for any nonempty residual star. Gate counts and star size are unrestricted. -/
theorem star_wire_bound (four : NoFourCycle G) (least : IsLeastAO G C) (top : TopForm G C)
    (nonempty : (Ustar G C).Nonempty)
    (v : Fin n) (center : ∀ e∈Ustar G C, v∈e)
    (S : Finset (Fin n)) (f : S→Fin n) (inj : Function.Injective f)
    (partners : ∀ i, f i∉S ∧ G.Adj i.val (f i)) :
    GeneralThree.wireBound G C S := by
  classical
  have edges : G.edgeFinset.Nonempty := by
    obtain ⟨e,mem⟩ := nonempty
    exact ⟨e,(Finset.mem_sdiff.mp mem).1⟩
  have positive : 0 < C.size := by
    obtain ⟨e,mem⟩ := nonempty
    induction e using Sym2.ind with
    | h a b =>
      obtain ⟨_,_,_,j,hj,_,_⟩ := PEqualNP.Outside.L_meta_8005.residualTrace least top mem
      have inside : j<C.size := (junkData hj).1
      omega
  apply ResidualDegree.repeat_of_size G C least.1 positive
  obtain ⟨count, old⟩ := PEqualNP.Outside.L_meta_1491 n G C four edges least top
  obtain ⟨K,hK⟩ := ResidualDegree.min_cover_exists (G.deleteEdges ↑(Ustar G C))
  have retained := old K hK
  have matching := GeneralThree.matching_after_deletion G (Ustar G C) S f inj partners K hK.1
  have cap := matching_one S f inj partners v center
  have cost := star_cost_all four least top nonempty v center
  omega

#print axioms star_cost
#print axioms star_cost_all
#print axioms star_wire_bound
end StarWire

namespace StarWire
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- The four-edge shape left by the preceding day's classification cannot
occur with exactly two dirty ANDs, two exceptional ORs and no centerless top. -/
theorem no_four_residual (four : NoFourCycle G) (bip : G.IsBipartite)
    (least : IsLeastAO G C) (top : TopForm G C) (empty : centreless G C=∅)
    (two : (junk G C).card=2) (twoOr : (orN G C \ lam G C).card=2) :
    (Ustar G C).card ≠ 4 := by
  intro card
  obtain ⟨v,center⟩ := RemainingGeometry.common_center four bip least top empty two twoOr card
  have nonempty := Finset.card_pos.mp (show 0 < (Ustar G C).card by omega)
  have cost := star_cost four least top empty nonempty v center
  omega

#print axioms no_four_residual
end StarWire

namespace StarObstruction
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- A nonempty pairwise-intersecting family of graph edges in a bipartite
graph has a common vertex. The only alternative in a simple graph is a triangle. -/
theorem common_of_intersection (bip : G.IsBipartite) (U : Finset (Sym2 (Fin n)))
    (edges : U⊆G.edgeFinset) (ne : U.Nonempty)
    (meet : ∀ e∈U, ∀ g∈U, ∃ z, z∈e ∧ z∈g) :
    ∃ v : Fin n, ∀ e∈U, v∈e := by
  classical
  by_cases two : 1 < U.card
  · obtain ⟨e,he,f,hf,ef⟩ := Finset.one_lt_card.mp two
    obtain ⟨z,ze,zf⟩ := meet e he f hf
    obtain ⟨p,rfl⟩ := Sym2.mem_iff_exists.mp ze
    obtain ⟨q,rfl⟩ := Sym2.mem_iff_exists.mp zf
    refine ⟨z,fun g hg => ?_⟩
    by_contra absent
    obtain ⟨x,xg,xe⟩ := meet g hg _ he
    obtain ⟨y,yg,yf⟩ := meet g hg _ hf
    have xp : x=p := (Sym2.mem_iff.mp xe).resolve_left (fun eq => absent (eq ▸ xg))
    have yq : y=q := (Sym2.mem_iff.mp yf).resolve_left (fun eq => absent (eq ▸ yg))
    subst x
    subst y
    have pq : p≠q := fun eq => ef (eq ▸ rfl)
    have sg := (Sym2.mem_and_mem_iff pq).mp ⟨xg,yg⟩
    subst g
    obtain ⟨col⟩ := bip
    have c₁ : col z ≠ col p := col.valid (SimpleGraph.mem_edgeFinset.mp (edges he))
    have c₂ : col z ≠ col q := col.valid (SimpleGraph.mem_edgeFinset.mp (edges hf))
    have c₃ : col p ≠ col q := col.valid (SimpleGraph.mem_edgeFinset.mp (edges hg))
    omega
  · obtain ⟨e,he⟩ := ne
    induction e using Sym2.ind with
    | h a b =>
      refine ⟨a, fun g hg => ?_⟩
      have eq := Finset.card_le_one.mp (Nat.le_of_not_gt two) g hg _ he
      exact eq ▸ Sym2.mem_mk_left a b

/-- Even the empty residual gives the wire bound when the graph and circuit
are nonempty, as they are under the parent step's hypotheses. -/
theorem empty_wire (four : NoFourCycle G) (least : IsLeastAO G C) (top : TopForm G C)
    (edges : G.edgeFinset.Nonempty) (pos : 0<C.size) (empty : Ustar G C = ∅)
    (S : Finset (Fin n)) (f : S→Fin n) (inj : Function.Injective f)
    (partners : ∀ i, f i∉S ∧ G.Adj i.val (f i)) : GeneralThree.wireBound G C S := by
  classical
  obtain ⟨count,old⟩ := PEqualNP.Outside.L_meta_1491 n G C four edges least top
  obtain ⟨K,hK⟩ := ResidualDegree.min_cover_exists (G.deleteEdges ↑(Ustar G C))
  have retained := old K hK
  have matching := GeneralThree.matching_after_deletion G (Ustar G C) S f inj partners K hK.1
  simp only [empty,Finset.inter_empty,Finset.card_empty,Nat.add_zero] at count matching
  apply ResidualDegree.repeat_of_size G C least.1 pos
  omega

/-- Any failure of the repeated-read bound must have two vertex-disjoint
residual edges, regardless of the number or arrangement of circuit gates. -/
theorem failure_forces_disjoint (four : NoFourCycle G) (bip : G.IsBipartite)
    (least : IsLeastAO G C) (top : TopForm G C) (edges : G.edgeFinset.Nonempty)
    (pos : 0<C.size) (S : Finset (Fin n)) (f : S→Fin n) (inj : Function.Injective f)
    (partners : ∀ i, f i∉S ∧ G.Adj i.val (f i)) (failure : ¬GeneralThree.wireBound G C S) :
    ∃ e∈Ustar G C, ∃ g∈Ustar G C, ∀ v∈e, v∉g := by
  classical
  by_contra impossible
  have nonempty : (Ustar G C).Nonempty := by
    by_contra none
    exact failure (empty_wire four least top edges pos (Finset.not_nonempty_iff_eq_empty.mp none)
      S f inj partners)
  have meet (e) (he : e∈Ustar G C) (g) (hg : g∈Ustar G C) : ∃ v, v∈e ∧ v∈g := by
    by_contra absent
    exact impossible ⟨e,he,g,hg,fun v ve vg => absent ⟨v,ve,vg⟩⟩
  obtain ⟨v,center⟩ := common_of_intersection bip (Ustar G C) Finset.sdiff_subset nonempty meet
  exact failure (StarWire.star_wire_bound four least top nonempty v center S f inj partners)

#print axioms failure_forces_disjoint
end StarObstruction
