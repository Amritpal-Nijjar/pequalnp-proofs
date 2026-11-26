import ForkTable
import PathGeometry4

namespace FourFork
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

def pathEdges (v : V→Fin n) := Finset.univ.image fun i : Fin 4 => s(v (L i),v (R i))
theorem edge_mem (v : V→Fin n) (shape : Ustar G C=pathEdges v) (e : Fin 4) :
    s(v (L e),v (R e))∈Ustar G C := by
  rw [shape]; exact Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩

def color : V→Bool := ![false,true,true,true,false]

theorem color_chart (bip : G.IsBipartite) (v : V→Fin n) (path : ∀ i : Fin 4, G.Adj (v (L i)) (v (R i))) :
    ∃ col : G.Coloring (Fin 2), ∀ p q, col (v p)=col (v q) ↔ color p=color q := by
  obtain ⟨col⟩ := bip
  have e0 : G.Adj (v 0) (v 1) := path 0
  have e1 : G.Adj (v 0) (v 2) := path 1
  have e2 : G.Adj (v 0) (v 3) := path 2
  have e3 : G.Adj (v 3) (v 4) := path 3
  have t0 := col.valid e0; have t1 := col.valid e1; have t2 := col.valid e2; have t3 := col.valid e3
  have c21 : col (v 2)=col (v 1) := by omega
  have c31 : col (v 3)=col (v 1) := by omega
  have c40 : col (v 4)=col (v 0) := by omega
  have chart (p : V) : col (v p) = if color p then col (v 1) else col (v 0) := by
    fin_cases p <;> first | rfl | exact c21 | exact c31 | exact c40
  refine ⟨col,fun p q => ?_⟩
  rw [chart p,chart q]
  cases hp : color p <;> cases hq : color q <;> simp [t0,Ne.symm t0]

theorem induced_path (four : NoFourCycle G) (bip : G.IsBipartite) (v : V→Fin n) (inj : Function.Injective v)
    (path : ∀ i : Fin 4, G.Adj (v (L i)) (v (R i))) : ∀ p q, G.Adj (v p) (v q) → adj p q=true := by
  have e0 : G.Adj (v 0) (v 1) := path 0
  have e1 : G.Adj (v 0) (v 2) := path 1
  have e2 : G.Adj (v 0) (v 3) := path 2
  have e3 : G.Adj (v 3) (v 4) := path 3
  have c41 := FourPath.no_chord four (inj.ne (by decide)) (inj.ne (by decide)) e3.symm e2.symm e0
  have c42 := FourPath.no_chord four (inj.ne (by decide)) (inj.ne (by decide)) e3.symm e2.symm e1
  obtain ⟨col,align⟩ := color_chart bip v path
  have split : ∀ p q : V, color p ≠ color q → adj p q=true ∨
      (p=4 ∧ q=1) ∨ (p=1 ∧ q=4) ∨ (p=4 ∧ q=2) ∨ (p=2 ∧ q=4) := by decide
  intro p q edge
  have neq : color p ≠ color q := fun eq => col.valid edge ((align p q).2 eq)
  rcases split p q neq with done | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact done
  · exact (c41 edge).elim
  · exact (c41 edge.symm).elim
  · exact (c42 edge).elim
  · exact (c42 edge.symm).elim

theorem raw_thin (four : NoFourCycle G) (bip : G.IsBipartite) (v : V→Fin n) (inj : Function.Injective v)
    (res : ∀ i : Fin 4,s(v (L i),v (R i))∈Ustar G C) (A : Finset (Fin n)) (ok : SixGeometry.RawOK G C A) :
    thin (fun p => decide (v p∈A))=true := by
  have path (i : Fin 4) := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (res i)).1
  obtain ⟨col,align⟩ := color_chart bip v path
  have lookup : ∀ p q : V, adj p q=true → ∃ e : Fin 4, (L e=p ∧ R e=q) ∨ (L e=q ∧ R e=p) := by decide
  have edge {p q : V} (hit : adj p q=true) : s(v p,v q)∈Ustar G C := by
    obtain ⟨e,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ := lookup p q hit
    · exact res e
    · exact Sym2.eq_swap ▸ res e
  have shared : ∀ p q : V, p≠q → color p=color q → ∃ t : V, adj p t=true ∧ adj q t=true := by decide
  apply (all5_iff _).2; intro p; apply (all5_iff _).2; intro q
  by_cases eq : p=q
  · simp [eq]
  have avoid : ¬(v p∈A ∧ v q∈A) := by
    rintro ⟨one,two⟩
    have same : col (v p)=col (v q) := by
      rcases ok with small|⟨z,conn⟩
      · exact congrArg col (Finset.card_le_one.mp small _ one _ two)
      · have u := col.valid (SimpleGraph.deleteEdges_adj.mp (conn _ one)).1
        have w := col.valid (SimpleGraph.deleteEdges_adj.mp (conn _ two)).1
        omega
    obtain ⟨t,pt,qt⟩ := shared p q eq ((align p q).1 same)
    exact SixGeometry.forbid_cross four ok (inj.ne eq) one two (edge pt)
      (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (edge qt)).1).symm
  simp only [Bool.or_eq_true,Bool.not_eq_true',Bool.and_eq_false_iff,decide_eq_false_iff_not]
  exact Or.inl (not_and_or.mp avoid)
end FourFork
