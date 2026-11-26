import ActiveOr
import TouchSingleton
import P4Ports
namespace DisjointCore
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open TouchSingleton
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

abbrev Chart (n : ℕ) := Fin 3 → Bool → Fin n
def threeEdges (v : Chart n) := Finset.univ.image fun i => s(v i false,v i true)
def unhit (v : Chart n) (z : tops G C → Fin n) : Finset (Fin 3) :=
  Finset.univ.filter fun i => ∀ t b, z t ≠ v i b

/-- The center set plus one endpoint of every untouched edge is a cover.
    At most one residual pair contains centers. A hit pair forces injectivity
    of the physical top-to-center map. With three untouched pairs the map
    can have at most one collision in its cardinality. -/
theorem center_budget (v : Chart n) (sh : Ustar G C = threeEdges v)
    (p : tops G C → Fin 2) (z : tops G C → Fin n)
    (one : ∀ t : tops G C, side (n := n) C t (p t) = {z t})
    (bound : ∀ K : Finset (Fin n), G.IsVertexCover (K : Set _) → (tops G C).card+2 ≤ K.card) :
    2 ≤ (unhit v z).card ∧ (tops G C).card ≤ (Finset.univ.image z).card+1 ∧
    ((unhit v z).card < 3 → Function.Injective z) := by
  classical
  let Z := Finset.univ.image z
  let U := unhit v z
  let K := Z ∪ U.image (fun i => v i false)
  have owner (t) : z t ∈ K := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩)
  have cover : G.IsVertexCover (K : Set _) := by
    intro a b adj
    change a ∈ K ∨ b ∈ K
    by_cases res : s(a,b) ∈ Ustar G C
    · rw [sh] at res
      obtain ⟨i,_,eq⟩ := Finset.mem_image.mp res
      have hit : v i false ∈ K ∨ v i true ∈ K := by
        by_cases no : i ∈ U
        · exact .inl (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,no,rfl⟩))
        · have coll : ∃ t b, z t = v i b := by
            by_contra! none
            exact no (Finset.mem_filter.mpr ⟨Finset.mem_univ _,none⟩)
          obtain ⟨t,b,ht⟩ := coll
          cases b
          · exact .inl (ht ▸ owner t)
          · exact .inr (ht ▸ owner t)
      rcases Sym2.eq_iff.mp eq with ⟨eq₁,eq₂⟩|⟨eq₁,eq₂⟩
      · simpa only [eq₁,eq₂] using hit
      · simpa only [eq₁,eq₂] using hit.symm
    · obtain ⟨t,⟨eq,_⟩|⟨eq,_⟩⟩ := orient_serves p z one (SimpleGraph.deleteEdges_adj.mpr ⟨adj,res⟩)
      · exact .inl (eq ▸ owner t)
      · exact .inr (eq ▸ owner t)
  have bot := bound K cover
  have top := (Finset.card_union_le Z (U.image (fun i => v i false))).trans (Nat.add_le_add_left Finset.card_image_le _)
  have uz : U.card ≤ 3 := (Finset.card_le_univ U).trans_eq (by decide)
  have zt : Z.card ≤ (tops G C).card := Finset.card_image_le.trans_eq (by simp)
  change (tops G C).card+2 ≤ (Z ∪ U.image (fun i => v i false)).card at bot
  change 2 ≤ U.card ∧ (tops G C).card ≤ Z.card + 1 ∧ _
  refine ⟨by omega,by omega,?_⟩
  intro h
  change U.card < 3 at h
  have eq : Z.card = (Finset.univ : Finset (tops G C)).card := by simpa using (show Z.card = (tops G C).card by omega)
  exact fun _ _ a => Finset.injOn_of_card_image_eq eq (Finset.mem_univ _) (Finset.mem_univ _) a

theorem ordinary_path {x y : ℕ} (r : Relation.ReflTransGen (ActiveOr.ordinaryStep G C) x y) :
    Relation.ReflTransGen (OrStep n C) x y := by
  induction r with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail step.1

/-- Both charged ORs are globally raw-bearing. An empty operand below a
    charged gate therefore reads an earlier dirty AND directly. -/
theorem empty_direct (ao : IsAO2 n C) (top : TopForm G C)
    (visible : ActiveOr.atTops G C = orN G C \ lam G C)
    {g : ℕ} (active : g ∈ P4Ports.active G C) (i : Fin 2)
    (empty : side (n := n) C g i = ∅) :
    ∃ k ∈ junk G C, k < g ∧ opnd C g i = n+k := by
  classical
  obtain ⟨a,la,hand,b,context⟩ := P4Ports.under_port ao active i
  obtain ⟨k,eq,m | m⟩ := emptyPortSource ao top la hand context empty
  · have bd := opndBound ao (P4Ports.active_length active) i
    exact ⟨k,m,by omega,eq⟩
  · have ne := (Finset.mem_filter.mp (visible ▸ m : k ∈ ActiveOr.atTops G C)).2.1
    rw [show orIn n C (n+k) = ∅ from (eq ▸ empty : orIn n C (n+k) = ∅)] at ne
    exact (Finset.not_nonempty_empty ne).elim

theorem visible_earlier {g : ℕ} (m : g ∈ ActiveOr.atTops G C) :
    g ∈ P4Ports.active G C ∧ (orIn n C (n+g)).Nonempty ∧
    ∃ t : tops G C, ∃ b : Fin 2, OrReaches n C (opnd C t b) g := by
  classical
  obtain ⟨ex,nz,t,ht,b,trail⟩ := Finset.mem_filter.mp m
  have path := ordinary_path trail
  exact ⟨Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ex,t,(topData ht).1,(topData ht).2.1,b,path⟩),
    nz,⟨t,ht⟩,b,reach_orReaches path g rfl (orData ex).1⟩

/-- An exceptional OR that is not a direct dirty lift has globally singleton
    raw support. Both of its physical children have exactly that singleton.
    This follows from its actual top route and the definition of Lambda. -/
theorem or_alternatives (ao : IsAO2 n C) (top : TopForm G C)
    (visible : ActiveOr.atTops G C = orN G C \ lam G C)
    (p : tops G C → Fin 2) (z : tops G C → Fin n)
    (one : ∀ t : tops G C, side (n := n) C t (p t) = {z t})
    {h : ℕ} (ex : h ∈ orN G C \ lam G C) :
    (∃ i : Fin 2, ∃ k ∈ junk G C, k < h ∧ opnd C h i = n+k ∧
      side (n := n) C h (1-i) = orIn n C (n+h)) ∨
    ∃ t : tops G C, orIn n C (n+h) = {z t} ∧ ∀ i : Fin 2, side (n := n) C h i = {z t} := by
  classical
  obtain ⟨active,nz,t,j,route⟩ := visible_earlier (visible ▸ ex)
  have data := orData ex
  have rawUnion := orRawUnion ao data.1 data.2.1
  by_cases empty : ∃ i : Fin 2, side (n := n) C h i = ∅
  · obtain ⟨i,zero⟩ := empty
    obtain ⟨k,km,lt,eq⟩ := empty_direct ao top visible active i zero
    refine .inl ⟨i,k,km,lt,eq,?_⟩
    rw [rawUnion]
    fin_cases i <;> simp_all
  · have nonempty (i : Fin 2) : (side (n := n) C h i).Nonempty := Finset.nonempty_iff_ne_empty.mpr (fun eq => empty ⟨i,eq⟩)
    rcases opposite (p t) j with same|other
    · have sub : orIn n C (n+h) ⊆ {z t} := by
        rw [←one t,←same]
        exact fun u hu => reach_mem_orIn u ((orReaches_reach h _ route).1.trans (mem_orIn_reach u hu))
      have eq := Finset.eq_of_subset_of_card_le sub (by simpa using Finset.card_pos.mpr nz)
      refine .inr ⟨t,eq,fun i => ?_⟩
      have inside : side (n := n) C h i ⊆ orIn n C (n+h) := by
        rw [rawUnion]; fin_cases i <;> first | exact Finset.subset_union_left | exact Finset.subset_union_right
      exact Finset.eq_of_subset_of_card_le (eq ▸ inside) (by simpa using Finset.card_pos.mpr (nonempty i))
    · have pj : 1-j = p t := by rw [other]; omega
      have ordinary : h ∈ lam G C := Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp ex).1,nonempty 0,nonempty 1,
        t,t.2,j,by rw [pj,one]; simp,route⟩
      exact ((Finset.mem_sdiff.mp ex).2 ordinary).elim
end DisjointCore
