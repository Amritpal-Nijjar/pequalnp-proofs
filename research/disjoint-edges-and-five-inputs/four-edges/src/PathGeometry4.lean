import PathTable
import SixGeometry

namespace FourPath
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

def pathEdges (v : V→Fin n) := Finset.univ.image fun i : Fin 4 => s(v (L i),v (R i))
theorem edge_mem (v : V→Fin n) (shape : Ustar G C=pathEdges v) (e : Fin 4) :
    s(v (L e),v (R e))∈Ustar G C := by
  rw [shape]; exact Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩

theorem no_chord (four : NoFourCycle G) {a b c d : Fin n} (ac : a≠c) (bd : b≠d)
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d) : ¬G.Adj a d := by
  intro chord
  exact bd (Finset.card_le_one.mp (four a c ac) b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ab,bc.symm⟩)
      d (Finset.mem_filter.mpr ⟨Finset.mem_univ _,chord,cd⟩))

theorem induced_path (four : NoFourCycle G) (bip : G.IsBipartite) (v : V→Fin n) (inj : Function.Injective v)
    (path : ∀ i : Fin 4, G.Adj (v (L i)) (v (R i))) : ∀ p q, G.Adj (v p) (v q) → adj p q=true := by
  have e0 : G.Adj (v 0) (v 1) := path 0
  have e1 : G.Adj (v 1) (v 2) := path 1
  have e2 : G.Adj (v 2) (v 3) := path 2
  have e3 : G.Adj (v 3) (v 4) := path 3
  have c03 := no_chord four (inj.ne (by decide)) (inj.ne (by decide)) e0 e1 e2
  have c14 := no_chord four (inj.ne (by decide)) (inj.ne (by decide)) e1 e2 e3
  obtain ⟨col⟩ := bip
  have t0 := col.valid e0; have t1 := col.valid e1; have t2 := col.valid e2; have t3 := col.valid e3
  have c20 : col (v 2)=col (v 0) := by omega
  have c31 : col (v 3)=col (v 1) := by omega
  have c40 : col (v 4)=col (v 0) := by omega
  let color : V→Bool := ![false,true,false,true,false]
  have chart (p : V) : col (v p) = if color p then col (v 1) else col (v 0) := by
    fin_cases p <;> first | rfl | exact c20 | exact c31 | exact c40
  have split : ∀ p q : V, color p ≠ color q → adj p q=true ∨
      (p=0 ∧ q=3) ∨ (p=3 ∧ q=0) ∨ (p=1 ∧ q=4) ∨ (p=4 ∧ q=1) := by decide
  intro p q edge
  have neq : color p ≠ color q := fun eq => col.valid edge (by rw [chart p,chart q,eq])
  rcases split p q neq with done | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact done
  · exact (c03 edge).elim
  · exact (c03 edge.symm).elim
  · exact (c14 edge).elim
  · exact (c14 edge.symm).elim

theorem raw_thin (four : NoFourCycle G) (v : V→Fin n) (inj : Function.Injective v)
    (res : ∀ i : Fin 4,s(v (L i),v (R i))∈Ustar G C) (A : Finset (Fin n)) (ok : SixGeometry.RawOK G C A) :
    thin (fun p => decide (v p∈A))=true := by
  have e (i : Fin 4) := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (res i)).1
  have ban {p q : V} {z : Fin n} (ne : p≠q) (r : s(v p,z)∈Ustar G C) (hit : G.Adj z (v q)) : ¬(v p∈A ∧ v q∈A) :=
    fun m => SixGeometry.forbid_cross four ok (inj.ne ne) m.1 m.2 r hit
  have a := ban (p:=0) (q:=2) (by decide) (res 0) (e 1)
  have b := ban (p:=1) (q:=3) (by decide) (res 1) (e 2)
  have c := ban (p:=2) (q:=4) (by decide) (res 2) (e 3)
  simp only [thin,Bool.and_eq_true,Bool.not_eq_true',Bool.and_eq_false_iff,decide_eq_false_iff_not]
  exact ⟨⟨not_and_or.mp a,not_and_or.mp b⟩,not_and_or.mp c⟩
end FourPath
