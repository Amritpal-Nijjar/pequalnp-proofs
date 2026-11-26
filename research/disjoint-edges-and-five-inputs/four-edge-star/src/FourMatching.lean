import EdgeCensus
import DisconnectedFour
import PathBound4
import ForkBound4
import DisjointBound
namespace FourMatching
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem lift_inj {m z : ℕ} (l r : Fin m→Fin z) (uniq : Function.Injective (fun i => s(l i,r i)))
    (v : Fin z→Fin n) (inj : Function.Injective v) : Function.Injective (fun i => s(v (l i),v (r i))) := by
  intro i j eq; apply uniq; apply Sym2.eq_iff.mpr
  rcases Sym2.eq_iff.mp eq with ⟨a,b⟩|⟨a,b⟩
  · exact Or.inl ⟨inj a,inj b⟩
  · exact Or.inr ⟨inj a,inj b⟩

theorem exhaust {z : ℕ} (l r : Fin 4→Fin z) (uniq : Function.Injective (fun i => s(l i,r i)))
    (v : Fin z→Fin n) (inj : Function.Injective v) {U : Finset (Sym2 (Fin n))} (card : U.card=4)
    (res : ∀ i,s(v (l i),v (r i))∈U) : U=Finset.univ.image (fun i => s(v (l i),v (r i))) := by
  symm; apply Finset.eq_of_subset_of_card_le
  · intro e me; obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp me; exact res i
  · rw [card,Finset.card_image_of_injective _ (lift_inj l r uniq v inj),Finset.card_univ]; decide

theorem no_three (four : NoFourCycle G) (bip : G.IsBipartite) (least : IsLeastAO G C) (top : TopForm G C)
    (empty : centreless G C=∅) (two : (junk G C).card=2) (twoOr : (orN G C \ lam G C).card=2)
    (v : Fin 6→Fin n) (inj : Function.Injective v)
    (ab : s(v 0,v 1)∈Ustar G C) (cd : s(v 2,v 3)∈Ustar G C) (ef : s(v 4,v 5)∈Ustar G C) : False := by
  classical
  let l : Fin 3→Fin 6 := ![0,2,4]; let r : Fin 3→Fin 6 := ![1,3,5]
  let key := fun i => s(v (l i),v (r i))
  let M := Finset.univ.image key
  have ki : Function.Injective key := lift_inj l r (by decide) v inj
  have size : M.card=3 := by rw [show M=Finset.univ.image key from rfl,Finset.card_image_of_injective _ ki]; decide
  have sub : M⊆Ustar G C := by
    intro e me; obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp me
    fin_cases i <;> first | exact ab | exact cd | exact ef
  have separate : ∀ i j : Fin 3,i≠j → l i≠l j ∧ l i≠r j ∧ r i≠l j ∧ r i≠r j := by decide
  have disj : SixBridge.disjointPairs M := by
    rintro e he f hf ne x mem belongs
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨a,b,c,d⟩ := separate i j (fun eq => ne (congrArg key eq))
    rcases Sym2.mem_iff.mp mem with m|m <;> rcases Sym2.mem_iff.mp belongs with k|k <;>
      first | exact a (inj (m.symm.trans k)) | exact b (inj (m.symm.trans k)) |
              exact c (inj (m.symm.trans k)) | exact d (inj (m.symm.trans k))
  have too := DisjointBound.matching_forces_three_or four bip least top empty two M sub (by omega) disj
  omega

theorem forbidden (four : NoFourCycle G) (bip : G.IsBipartite) (least : IsLeastAO G C) (top : TopForm G C)
    (empty : centreless G C=∅) (two : (junk G C).card=2) (twoOr : (orN G C \ lam G C).card=2)
    (card : (Ustar G C).card=4) : EdgeCensus.Forbidden (Ustar G C) := by
  have adj {a b : Fin n} (e : s(a,b)∈Ustar G C) : G.Adj a b := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp e).1
  constructor
  · intro x e; exact G.irrefl (adj e)
  · intro a b c _ ab bc ca; obtain ⟨col⟩ := bip
    have x := col.valid (adj ab); have y := col.valid (adj bc); have z := col.valid (adj ca); omega
  · intro a b c d nd ab bc cd da
    have ac : a≠c := by simp at nd; grind only
    have bd : b≠d := by simp at nd; grind only
    exact FourPath.no_chord four ac bd (adj ab) (adj bc) (adj cd) (adj da).symm
  · intro a b c d e f nd ab cd ef
    let v : Fin 6→Fin n := ![a,b,c,d,e,f]
    exact no_three four bip least top empty two twoOr v (List.nodup_ofFn.mp nd) ab cd ef
  · intro a b c d e nd ab bc cd de
    let v : Fin 5→Fin n := ![a,b,c,d,e]
    have inj : Function.Injective v := List.nodup_ofFn.mp nd
    apply FourPath.no_four_edge_path four bip least top empty two twoOr v inj
    exact exhaust FourPath.L FourPath.R (by decide) v inj card (fun i => by fin_cases i <;> first | exact ab | exact bc | exact cd | exact de)
  · intro a b c d e nd ab ac ad de
    let v : Fin 5→Fin n := ![a,b,c,d,e]
    have inj : Function.Injective v := List.nodup_ofFn.mp nd
    apply FourFork.no_four_edge_fork four bip least top empty two twoOr v inj
    exact exhaust FourFork.L FourFork.R (by decide) v inj card (fun i => by fin_cases i <;> first | exact ab | exact ac | exact ad | exact de)
  · intro a b c d e f nd ab ac de df
    let v : Fin 6→Fin n := ![a,b,c,d,e,f]
    have inj : Function.Injective v := List.nodup_ofFn.mp nd
    apply DisconnectedFour.impossible four bip least top empty two twoOr false v inj
    exact exhaust (fun e => Chart6.L (Chart6.edges false e)) (fun e => Chart6.R (Chart6.edges false e)) (by decide)
      v inj card (fun i => by fin_cases i <;> first | exact ab | exact ac | exact de | exact df)
  · intro a b c d e f nd ab ac ae df
    let v : Fin 6→Fin n := ![a,b,c,d,e,f]
    have inj : Function.Injective v := List.nodup_ofFn.mp nd
    apply DisconnectedFour.impossible four bip least top empty two twoOr true v inj
    exact exhaust (fun e => Chart6.L (Chart6.edges true e)) (fun e => Chart6.R (Chart6.edges true e)) (by decide)
      v inj card (fun i => by fin_cases i <;> first | exact ab | exact ac | exact ae | exact df)

/-- Every residual matching has at most one edge in this four-edge resource
    regime, independently of the number of other vertices and gates. -/
theorem matching_cap (four : NoFourCycle G) (bip : G.IsBipartite) (least : IsLeastAO G C) (top : TopForm G C)
    (empty : centreless G C=∅) (two : (junk G C).card=2) (twoOr : (orN G C \ lam G C).card=2)
    (card : (Ustar G C).card=4) (M : Finset (Sym2 (Fin n))) (sub : M⊆Ustar G C)
    (disj : SixBridge.disjointPairs M) : M.card≤1 := by
  classical
  by_contra! large
  obtain ⟨e,me,f,mf,ne⟩ := Finset.one_lt_card.mp large
  induction e using Sym2.ind with
  | h a b =>
    induction f using Sym2.ind with
    | h c d =>
      have e0 := sub me; have e1 := sub mf
      have h0 : G.Adj a b := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp e0).1
      have h1 : G.Adj c d := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp e1).1
      have apartA := disj _ me _ mf ne a (Sym2.mem_mk_left _ _)
      have apartB := disj _ me _ mf ne b (Sym2.mem_mk_right _ _)
      simp only [Sym2.mem_iff,not_or] at apartA apartB
      have nd : [a,b,c,d].Nodup := by simp [h0.ne,h1.ne,apartA.1,apartA.2,apartB.1,apartB.2]
      exact EdgeCensus.exclude (forbidden four bip least top empty two twoOr card) card a b c d nd e0 e1
#print axioms matching_cap
end FourMatching
