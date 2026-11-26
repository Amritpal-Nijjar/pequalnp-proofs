import FourTops
import PathGeometry4
import ResidualShrink
import VisibleRaw
import PathExclusion

namespace FourPath
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem necessary (least : IsLeastAO G C) (top : TopForm G C) {j : ℕ} (dirty : j∈junk G C)
    (v : V→Fin n) (shape : Ustar G C=pathEdges v) (d : V→V→Bool)
    (eq : ∀ p q, d p q=FourPhysical.Vg v C j p q) : needed d=true := by
  have pos : G.edgeFinset.Nonempty := ⟨_,(Finset.mem_sdiff.mp (edge_mem v shape 0)).1⟩
  apply needed_of
  intro u singleton
  obtain ⟨x,y,res,xu,yu,fires⟩ := ResidualChange.residual_witness least top pos dirty (v u) ((eq u u).symm.trans singleton)
  obtain ⟨e,_,reps⟩ := Finset.mem_image.mp (shape ▸ res : s(x,y) ∈ pathEdges v)
  refine ⟨e,?_⟩
  rcases Sym2.eq_iff.mp reps with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨⟨fun h => xu (congrArg v h.symm),fun h => yu (congrArg v h.symm)⟩,(eq _ _).trans fires⟩
  · have flip : pairInput (v (R e)) (v (L e)) = pairInput (v (L e)) (v (R e)) := by
      funext k; simp only [pairInput]; grind
    rw [flip] at fires
    exact ⟨⟨fun h => yu (congrArg v h.symm),fun h => xu (congrArg v h.symm)⟩,(eq _ _).trans fires⟩

/-- No least top-form circuit with this resource pattern has a four-edge residual path. -/
theorem no_four_edge_path (four : NoFourCycle G) (bip : G.IsBipartite) (least : IsLeastAO G C)
    (top : TopForm G C) (empty : centreless G C=∅) (two : (junk G C).card=2)
    (twoOr : (orN G C \ lam G C).card=2) (v : V→Fin n) (inj : Function.Injective v)
    (shape : Ustar G C=pathEdges v) : False := by
  classical
  have res := edge_mem v shape
  have path (e : Fin 4) := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (res e)).1
  have visible := VisibleRaw.path_visible four bip least empty twoOr
    (a:=v 0) (b:=v 1) (c:=v 2) (d:=v 3) (inj.ne (by decide)) (inj.ne (by decide)) (res 0) (res 1) (res 2)
  obtain ⟨j,h,lt,eqJ⟩ := FourPhysical.sorted_pair two
  let raw := FourPhysical.supports n C j h
  let m := fun k => FourPhysical.rb v (raw k)
  have atPort {g : ℕ} (gm : g∈junk G C) (i : Fin 2) : SixGeometry.RawOK G C (side (n:=n) C g i) := by
    have inside := (junkData gm).1
    have bd := opndBound least.1 inside i
    exact SixGeometry.actual_raw least.1 empty visible _ (by omega)
  have jj : j ∈ junk G C := by simp [eqJ]
  have hh : h ∈ junk G C := by simp [eqJ]
  have ok (k : Fin 4) : SixGeometry.RawOK G C (raw k) := by
    fin_cases k
    · exact atPort jj 0
    · exact atPort jj 1
    · exact atPort hh 0
    · exact atPort hh 1
  obtain ⟨a,b,eq0,eq1⟩ := FourPhysical.gates v least.1 top lt eqJ
  have passes := accept_of m a b (fun k => raw_thin four v inj res _ (ok k))
    (necessary least top jj v shape _ eq0) (necessary least top hh v shape _ eq1) (fun e => by
      obtain ⟨k,yes,safe⟩ := FourTops.actual_win v least top eqJ m a b eq0 eq1 e (res e)
      exact ⟨k,yes,fun p q on => induced_path four bip v inj path p q (safe p q on)⟩)
  exact Bool.false_ne_true ((impossible m a b).symm.trans passes)

#print axioms no_four_edge_path
end FourPath
