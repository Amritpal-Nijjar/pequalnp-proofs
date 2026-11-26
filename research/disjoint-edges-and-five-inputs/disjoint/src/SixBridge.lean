import SixTops
import SixGeometry
namespace SixBridge
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open SixTerms SixPhysical SixGeometry
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
abbrev disjointPairs (U : Finset (Sym2 (Fin n))) := ∀ e ∈ U, ∀ f ∈ U, e ≠ f → ∀ x ∈ e, x ∉ f

theorem chart (col : G.Coloring (Fin 2)) (U : Finset (Sym2 (Fin n))) (sub : U ⊆ G.edgeFinset)
    (three : U.card=3) (sep : disjointPairs U) :
    ∃ v : I → Fin n, Function.Injective v ∧ (∀ i, s(v (i,false),v (i,true)) ∈ U) ∧
      ∀ p q : I, col (v p) = col (v q) ↔ p.2 = q.2 := by
  classical
  let key : Fin 3 ≃ U := Fintype.equivOfCardEq (by simp [three])
  have orient (e : Sym2 (Fin n)) (he : e∈U) :
      ∃ a b : Fin n, e=s(a,b) ∧ col a=0 ∧ col b=1 := by
    induction e using Sym2.ind with
    | h a b =>
      have adj := SimpleGraph.mem_edgeFinset.mp (sub he)
      have ne : col a ≠ col b := col.valid adj
      by_cases z : col a=0
      · exact ⟨a,b,rfl,z,by omega⟩
      · exact ⟨b,a,Sym2.eq_swap ..,by omega,by omega⟩
  choose l r rep left right using fun i : Fin 3 => orient (key i).val (key i).2
  let v (p : I) := if p.2 then r p.1 else l p.1
  have on (i : Fin 3) (b : Bool) : v (i,b) ∈ (key i).val := by
    rw [rep]; cases b
    · exact Sym2.mem_mk_left _ _
    · exact Sym2.mem_mk_right _ _
  have color (i : Fin 3) (b : Bool) : col (v (i,b)) = (if b then 1 else 0) := by
    cases b
    · exact left i
    · exact right i
  have align (p q : I) : col (v p) = col (v q) ↔ p.2 = q.2 := by
    obtain ⟨i,a⟩ := p; obtain ⟨j,b⟩ := q
    rw [color,color]; cases a <;> cases b <;> simp
  refine ⟨v,?_,fun i => ?_,align⟩
  · rintro ⟨i,a⟩ ⟨j,b⟩ eq
    have ab := (align (i,a) (j,b)).mp (congrArg col eq)
    have ij : i=j := by
      by_contra ne
      have diff : (key i).val ≠ (key j).val := fun e => ne (key.injective (Subtype.ext e))
      exact sep _ (key i).2 _ (key j).2 diff _ (on i a) (eq ▸ on j b)
    exact Prod.ext ij ab
  · change s(l i,r i) ∈ U
    rw [←rep]; exact (key i).2

/-- This is the physical bridge. No finite exclusion or certificate is used.
    The three matching edges may sit inside a larger residual. -/
theorem actual_passes (four : NoFourCycle G) (bip : G.IsBipartite)
    (least : IsLeastAO G C) (top : TopForm G C) (empty : centreless G C=∅)
    (two : (junk G C).card=2) (visible : ActiveOr.atTops G C = orN G C \ lam G C)
    (U : Finset (Sym2 (Fin n))) (sub : U ⊆ Ustar G C) (three : U.card=3) (disj : disjointPairs U) :
    ∃ (m : M) (a b : Bool), passes m a b = true := by
  classical
  obtain ⟨col⟩ := bip
  obtain ⟨v,inj,mem,align⟩ := chart col U (sub.trans Finset.sdiff_subset) three disj
  obtain ⟨j,h,lt,eqJ⟩ := sorted_pair two
  let R := supports n C j h
  let m := fun k => rb v (R k)
  have goodPort {g : ℕ} (gm : g ∈ junk G C) (i : Fin 2) : RawOK G C (side (n := n) C g i) := by
    have len := (junkData gm).1
    have bd := opndBound least.1 len i
    exact actual_raw least.1 empty visible _ (by omega)
  have jj : j ∈ junk G C := by simp [eqJ]
  have hh : h ∈ junk G C := by simp [eqJ]
  have good (k : Fin 4) : RawOK G C (R k) := by
    fin_cases k
    · exact goodPort jj 0
    · exact goodPort jj 1
    · exact goodPort hh 0
    · exact goodPort hh 1
  obtain ⟨a,b,e0,e1⟩ := gates v least.1 top lt eqJ
  refine ⟨m,a,b,passes_of m a b (fun k => mono_of v inj col align _ (good k)) ?_⟩
  intro i
  obtain ⟨k,yes,safe⟩ := SixTops.actual_win v least top eqJ m a b e0 e1 i (sub (mem i))
  exact ⟨k,yes,fun p q on => actual_allowed v inj four col align (fun j => sub (mem j)) R good p q (safe p q on)⟩

theorem disjoint_bound_of_exclusion (ex : ∀ (m : M) (a b : Bool), passes m a b=false)
    (four : NoFourCycle G) (bip : G.IsBipartite) (least : IsLeastAO G C) (top : TopForm G C)
    (three : (Ustar G C).card=3) (disj : disjointPairs (Ustar G C))
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ i, f i ∉ S ∧ G.Adj i.val (f i)) : GeneralThree.wireBound G C S := by
  classical
  by_contra fail
  have edges : G.edgeFinset.Nonempty := (Finset.card_pos.mp (by omega : 0 < (Ustar G C).card)).mono Finset.sdiff_subset
  obtain ⟨two,z,twoOr,_⟩ := GeneralThree.remaining G C four edges least top three S f inj partners fail
  have empty := Finset.card_eq_zero.mp z
  have visible := ActiveOr.three_need_both bip four least top empty two twoOr _ (Finset.Subset.refl _) (le_of_eq three.symm) disj
  obtain ⟨m,a,b,yes⟩ := actual_passes four bip least top empty two visible _ (Finset.Subset.refl _) three disj
  exact Bool.false_ne_true ((ex m a b).symm.trans yes)
#print axioms actual_passes
end SixBridge
