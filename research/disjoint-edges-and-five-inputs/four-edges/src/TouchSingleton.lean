import GeneralThree
import MatchingPorts
import StarGrowth
import DisconnectedGeometry
/-
Uses Sarvesh Kapre's top orientations, three-edge deficit, and tight matching bound
at research commit d762c6d9ad64050eda8a3f9f795abd950f278222.
-/
namespace TouchSingleton
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

private theorem rejectMixed {α β : Type*} {x : α} {y : β} (h : (Sum.inl x : α ⊕ β) = Sum.inr y) : False := by cases h

abbrev port (C : Circuit) (t : ℕ) (k : Fin 2) (x : Fin n → Bool) :=
  val C (List.ofFn x) (opnd C t k)
def shape {n : ℕ} (a b c d e : Fin n) : Finset (Sym2 (Fin n)) := {s(a,b),s(b,c),s(d,e)}

/-- Any orientation by singleton sides still covers the retained edges, including after a flip. -/
theorem orient_serves (p : tops G C → Fin 2) (z : tops G C → Fin n)
    (raw : ∀ t : tops G C, side (n := n) C t (p t) = {z t}) {u v : Fin n}
    (h : (G.deleteEdges ↑(Ustar G C)).Adj u v) :
    ∃ t, (u = z t ∧ v ∈ side (n := n) C t (1-p t)) ∨
         (v = z t ∧ u ∈ side (n := n) C t (1-p t)) := by
  classical
  obtain ⟨uv,ret⟩ := SimpleGraph.deleteEdges_adj.mp h
  have star : s(u,v) ∈ starEdges G C := by
    by_contra miss
    exact ret (Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr uv,miss⟩)
  obtain ⟨t,ht,hc⟩ := Finset.mem_biUnion.mp star
  obtain ⟨⟨l,r⟩,mem,eq⟩ := Finset.mem_image.mp hc
  let T : tops G C := ⟨t,ht⟩
  obtain ⟨hl,hr⟩ := Finset.mem_product.mp mem
  have ori : (l = z T ∧ r ∈ side (n := n) C t (1-p T)) ∨
             (r = z T ∧ l ∈ side (n := n) C t (1-p T)) := by
    have rr := raw T
    have casesP : p T = 0 ∨ p T = 1 := by omega
    rcases casesP with zz|oo
    · rw [zz] at rr
      exact Or.inl ⟨by simpa [T] using Finset.mem_singleton.mp (rr ▸ hl),by simpa [zz] using hr⟩
    · rw [oo] at rr
      exact Or.inr ⟨by simpa [T] using Finset.mem_singleton.mp (rr ▸ hr),by simpa [oo] using hl⟩
  change s(l,r) = s(u,v) at eq
  rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨T,ori⟩
  · exact ⟨T,ori.symm⟩

/-- Two extra cover slots are tight. Neither slot can duplicate any chosen center. -/
theorem tight_slots (p : tops G C → Fin 2) (z : tops G C → Fin n)
    (raw : ∀ t : tops G C, side (n := n) C t (p t) = {z t}) (extra : Fin 2 → Fin n)
    (hit : ∀ u v, s(u,v) ∈ Ustar G C → ∃ k, u = extra k ∨ v = extra k)
    (bound : ∀ K : Finset (Fin n), G.IsVertexCover (K : Set _) → (tops G C).card + 2 ≤ K.card) :
    Function.Injective (Sum.elim z extra) := by
  classical
  let slots : tops G C ⊕ Fin 2 → Fin n := Sum.elim z extra
  let K := Finset.univ.image slots
  have inside (i) : slots i ∈ K := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have cover : G.IsVertexCover (K : Set _) := by
    intro u v adj
    by_cases h : s(u,v) ∈ Ustar G C
    · obtain ⟨k,eq|eq⟩ := hit u v h
      · exact Or.inl (eq ▸ inside (.inr k))
      · exact Or.inr (eq ▸ inside (.inr k))
    · obtain ⟨t,⟨eq,_⟩|⟨eq,_⟩⟩ := orient_serves p z raw (SimpleGraph.deleteEdges_adj.mpr ⟨adj,h⟩)
      · exact Or.inl (eq ▸ inside (.inl t))
      · exact Or.inr (eq ▸ inside (.inl t))
  have card : (Finset.univ.image slots).card = (Finset.univ : Finset (tops G C ⊕ Fin 2)).card :=
    le_antisymm Finset.card_image_le (by simpa [K] using bound K cover)
  exact fun _ _ eq => Finset.injOn_of_card_image_eq card (Finset.mem_univ _) (Finset.mem_univ _) eq

/-- If a center port accepts singleton b, every raw leaf is a common neighbor of
    its center and b. A four-cycle-free graph leaves at most one such vertex. -/
theorem bad_center_leaves (four : NoFourCycle G) (ao : IsAO2 n C)
    (t : tops G C) (p : Fin 2) (z b : Fin n) (different : z ≠ b)
    (raw : side (n := n) C t p = {z}) (on : port C t p (pairInput b b) = true) :
    (side (n := n) C t (1-p)).card ≤ 1 := by
  obtain ⟨len,hand,below⟩ := topData t.2
  have common {w : Fin n} (hw : w ∈ side (n := n) C t (1-p)) : G.Adj z w ∧ G.Adj b w := by
    have hz : z ∈ side (n := n) C t p := by simp [raw]
    have left := (SimpleGraph.deleteEdges_adj.mp (cleanAdj ao t.2 p hz hw)).1
    have mono : ∀ v, pairInput b b v = true → pairInput b w v = true := by
      intro v hv
      rcases (pairInput_true _ _ _).mp hv with rfl|rfl <;> exact pairInput_left _ _
    have bd := opndBound ao len p
    have center := StarGrowth.wire_mono ao mono (by omega : opnd C t p < n+C.gates.length) on
    have leaf := sideVal hw (pairInput_right b w)
    have fires := (andValOperands ao len hand (pairInput b w)).mpr (fun j => by
      rcases opposite p j with rfl|rfl
      · exact center
      · exact leaf)
    exact ⟨left,(graphFun_pair G b w).mp (below _ fires)⟩
  exact (Finset.card_le_card (show side (n := n) C t (1-p) ⊆
    Finset.univ.filter (fun w => G.Adj z w ∧ G.Adj b w) from
    fun w hw => Finset.mem_filter.mpr ⟨Finset.mem_univ _,common hw⟩)).trans (four z b different)

/-- A top may be reoriented without changing the circuit. The chosen singleton
    port then rejects b in the actual circuit, even for a redundant near-cover center. -/
theorem quiet_choice (four : NoFourCycle G) (ao : IsAO2 n C) (empty : centreless G C = ∅)
    (t : tops G C) (p : Fin 2) (z b : Fin n) (different : z ≠ b)
    (raw : side (n := n) C t p = {z}) :
    ∃ k : Fin 2, ∃ y : Fin n, side (n := n) C t k = {y} ∧ port C t k (pairInput b b) = false := by
  cases h : port C t p (pairInput b b) with
  | false => exact ⟨p,z,raw,h⟩
  | true =>
    have small := bad_center_leaves four ao t p z b different raw h
    have pos := Finset.card_pos.mpr (topSides empty t.2 (1-p))
    obtain ⟨y,hy⟩ := Finset.card_eq_one.mp (by omega : (side (n := n) C t (1-p)).card = 1)
    refine ⟨1-p,y,hy,Bool.eq_false_iff.mpr ?_⟩
    intro both
    obtain ⟨len,hand,below⟩ := topData t.2
    have fires := (andValOperands ao len hand (pairInput b b)).mpr (fun j => by
      rcases opposite p j with rfl|rfl
      · exact h
      · exact both)
    exact G.irrefl ((graphFun_pair G b b).mp (below _ fires))

/-- Every gate in the OR closure of a chosen quiet port also rejects singleton b. -/
theorem routed_quiet {t h : ℕ} {p : Fin 2} {x : Fin n → Bool}
    (off : port C t p x = false)
    (path : OrReaches n C (opnd C t p) h) : gateVal n C h x = false := by
  apply Bool.eq_false_iff.mpr
  intro on
  have up := orStep_up (n := n) (by simp : (List.ofFn x).length = n)
    (orReaches_reach h _ path).1 (gateVal_eq_val n C h _ ▸ on)
  exact Bool.false_ne_true (off.symm.trans up)

private theorem hit_two {a b c d e : Fin n} (sh : Ustar G C = shape a b c d e)
    {v : Fin n} (which : v = d ∨ v = e) :
    ∀ x y, s(x,y) ∈ Ustar G C → ∃ k : Fin 2, x = (![b,v] : Fin 2 → Fin n) k ∨ y = (![b,v] : Fin 2 → Fin n) k := by
  intro x y h
  rw [sh] at h
  simp only [shape,Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with h|h|h
  · rcases Sym2.eq_iff.mp h with h|h
    · exact ⟨0,Or.inr h.2⟩
    · exact ⟨0,Or.inl h.1⟩
  · rcases Sym2.eq_iff.mp h with h|h
    · exact ⟨0,Or.inl h.1⟩
    · exact ⟨0,Or.inr h.2⟩
  · rcases which with rfl|rfl <;> rcases Sym2.eq_iff.mp h with h|h
    · exact ⟨1,Or.inl h.1⟩
    · exact ⟨1,Or.inr h.2⟩
    · exact ⟨1,Or.inr h.2⟩
    · exact ⟨1,Or.inl h.1⟩

theorem no_two_ends {a b c d e : Fin n} (sh : Ustar G C = shape a b c d e)
    (p : tops G C → Fin 2) (z : tops G C → Fin n) (raw : ∀ t : tops G C, side (n := n) C t (p t) = {z t})
    (bound : ∀ K : Finset (Fin n), G.IsVertexCover (K : Set _) → (tops G C).card + 2 ≤ K.card) :
    (∀ t, z t ≠ a) ∨ (∀ t, z t ≠ c) := by
  classical
  by_contra! fail
  obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := fail
  let Z := Finset.univ.image z
  let K := insert d Z
  have center (t) : z t ∈ K := Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩)
  have ma : a ∈ K := hi ▸ center i
  have mc : c ∈ K := hj ▸ center j
  have md : d ∈ K := Finset.mem_insert_self _ _
  have cover : G.IsVertexCover (K : Set _) := by
    intro x y adj
    by_cases m : s(x,y) ∈ Ustar G C
    · rw [sh] at m
      simp only [shape,Finset.mem_insert,Finset.mem_singleton] at m
      rcases m with h|h|h <;> rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      all_goals first | exact Or.inl ma | exact Or.inr ma | exact Or.inl mc | exact Or.inr mc | exact Or.inl md | exact Or.inr md
    · obtain ⟨t,⟨eq,_⟩|⟨eq,_⟩⟩ := orient_serves p z raw (SimpleGraph.deleteEdges_adj.mpr ⟨adj,m⟩)
      · exact Or.inl (eq ▸ center t)
      · exact Or.inr (eq ▸ center t)
  have bad := bound K cover
  have upper : K.card ≤ (tops G C).card + 1 :=
    (Finset.card_insert_le d Z).trans (Nat.add_le_add_right (Finset.card_image_le.trans_eq (by simp)) 1)
  omega

/-- The choice is simultaneous for all tops, uses the actual admissible matching,
    and has singleton-negative center signals. Two disjoint residual edges must
    avoid the centers; the other touching edge can contain a chosen center. -/
theorem oriented_of_failure {a b c d e : Fin n} (sh : Ustar G C = shape a b c d e)
    (four : NoFourCycle G) (edges : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (top : TopForm G C) (three : (Ustar G C).card = 3)
    (S : Finset (Fin n)) (f : S → Fin n) (inj : Function.Injective f)
    (partners : ∀ i, f i ∉ S ∧ G.Adj i.val (f i)) (fail : ¬GeneralThree.wireBound G C S) :
    ∃ (p : tops G C → Fin 2) (z : tops G C → Fin n),
      (∀ t : tops G C, side (n := n) C t (p t) = {z t}) ∧ Function.Injective z ∧
      (∀ t, z t ≠ b ∧ z t ≠ d ∧ z t ≠ e) ∧ ((∀ t, z t ≠ a) ∨ (∀ t, z t ≠ c)) ∧
      (∀ t : tops G C, port C t (p t) (pairInput b b) = false) ∧
      (∀ (t : tops G C) h, OrReaches n C (opnd C t (p t)) h → gateVal n C h (pairInput b b) = false) := by
  classical
  have empty := Finset.card_eq_zero.mp (GeneralThree.remaining G C four edges least top three S f inj partners fail).2.1
  have tight := (GeneralThree.tight_if_failed G C four edges least top three S f inj partners fail).1
  have bound (K : Finset (Fin n)) (cov : G.IsVertexCover (K : Set _)) : (tops G C).card + 2 ≤ K.card := by
    rw [←tight]; exact ResidualDegree.matched_le_cover G S f inj partners K cov
  obtain ⟨p₀,z₀,raw₀,_⟩ := topIndexedStars four least.1 empty
  have i₀ := tight_slots p₀ z₀ raw₀ (![b,d]) (hit_two sh (Or.inl rfl)) bound
  have ne₀ (t) : z₀ t ≠ b := fun eq => rejectMixed (@i₀ (.inl t) (.inr 0) eq)
  choose p z raw quiet using fun t => quiet_choice four least.1 empty t (p₀ t) (z₀ t) b (ne₀ t) (raw₀ t)
  have i₁ := tight_slots p z raw (![b,d]) (hit_two sh (Or.inl rfl)) bound
  have i₂ := tight_slots p z raw (![b,e]) (hit_two sh (Or.inr rfl)) bound
  refine ⟨p,z,raw,fun u v eq => Sum.inl.inj (@i₁ (.inl u) (.inl v) eq),?_,no_two_ends sh p z raw bound,quiet,?_⟩
  · exact fun t => ⟨fun eq => rejectMixed (@i₁ (.inl t) (.inr 0) eq),
      fun eq => rejectMixed (@i₁ (.inl t) (.inr 1) eq),
      fun eq => rejectMixed (@i₂ (.inl t) (.inr 1) eq)⟩
  · exact fun t _ path => routed_quiet (quiet t) path
end TouchSingleton
