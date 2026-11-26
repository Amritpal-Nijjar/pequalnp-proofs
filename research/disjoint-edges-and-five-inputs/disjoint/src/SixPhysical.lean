import DisjointCore
import SixTerms
namespace SixPhysical
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open SixTerms
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
def row (v : I → Fin n) (p q : I) := pairInput (v p) (v q)
def Vg (v : I → Fin n) (C : Circuit) (g : ℕ) (p q : I) := gateVal n C g (row v p q)
def Vp (v : I → Fin n) (C : Circuit) (g : ℕ) (b : Fin 2) (p q : I) :=
  val C (List.ofFn (row v p q)) (opnd C g b)
def rb (v : I → Fin n) (R : Finset (Fin n)) (p : I) := decide (v p ∈ R)
def supports (n : ℕ) (C : Circuit) (j h : ℕ) : Fin 4 → Finset (Fin n) :=
  ![side (n := n) C j 0,side C j 1,side C h 0,side C h 1]

theorem direct_lit (v : I → Fin n) (g : ℕ) (b : Fin 2) (p q : I)
    (yes : lit (rb v (side (n := n) C g b)) p q = true) : Vp v C g b p q = true := by
  rcases Bool.or_eq_true_iff.mp yes with l|r
  · exact sideVal (of_decide_eq_true l) (pairInput_left _ _)
  · exact sideVal (of_decide_eq_true r) (pairInput_right _ _)

theorem path_on (v : I → Fin n) {g h : ℕ} {b : Fin 2} (path : OrReaches n C (opnd C g b) h)
    (p q : I) (on : Vg v C h p q = true) : Vp v C g b p q = true :=
  orStep_up (n := n) (by simp : (List.ofFn (row v p q)).length = n)
    (orReaches_reach h _ path).1 (gateVal_eq_val n C h _ ▸ on)

theorem port_decomp (v : I → Fin n) (ao : IsAO2 n C) (top : TopForm G C)
    {g : ℕ} (len : g < C.gates.length) (andOp : (gateAt C g).op = GateOp.and)
    (b : Fin 2) (p q : I) (yes : Vp v C g b p q = true) :
    lit (rb v (side (n := n) C g b)) p q = true ∨
      ∃ h ∈ junk G C, h < g ∧ OrReaches n C (opnd C g b) h ∧ Vg v C h p q = true := by
  rcases operandSupport ao top len andOp yes with ⟨w,mem,eq|eq⟩|⟨h,mem,path,on⟩
  · exact .inl (Bool.or_eq_true_iff.mpr (.inl (decide_eq_true (eq ▸ mem))))
  · exact .inl (Bool.or_eq_true_iff.mpr (.inr (decide_eq_true (eq ▸ mem))))
  · have lt := opndBound ao len b
    have le := orStep_le (orReaches_reach h _ path).1
    exact .inr ⟨h,mem,by omega,path,on⟩

theorem sorted_pair {D : Finset ℕ} (two : D.card = 2) : ∃ j h, j<h ∧ D={j,h} := by
  obtain ⟨j,h,ne,eq⟩ := Finset.card_eq_two.mp two
  by_cases lt : j<h
  · exact ⟨j,h,lt,eq⟩
  · exact ⟨h,j,by omega,by rw [eq,Finset.pair_comm]⟩

/-- The two physical dirty ANDs restricted to singleton and pair inputs.
    Each second-stage operand adds only a fixed optional first-stage signal. -/
theorem gates (v : I → Fin n) (ao : IsAO2 n C) (top : TopForm G C)
    {j h : ℕ} (lt : j<h) (eqJ : junk G C={j,h}) :
    let m := fun k => rb v (supports n C j h k)
    ∃ a b : Bool, (∀ p q, d0 m p q = Vg v C j p q) ∧
      (∀ p q, d1 m a b p q = Vg v C h p q) := by
  classical
  let R := supports n C j h
  let m := fun k => rb v (R k)
  let take (i : Fin 2) := decide (OrReaches n C (opnd C h i) j)
  have jj : j ∈ junk G C := by simp [eqJ]
  have hh : h ∈ junk G C := by simp [eqJ]
  have jdata := junkData jj
  have hdata := junkData hh
  have first (i : Fin 2) (p q : I) :
      Vp v C j i p q = lit (rb v (side (n := n) C j i)) p q := by
    apply Bool.eq_iff_iff.mpr
    refine ⟨fun on => ?_,direct_lit v j i p q⟩
    rcases port_decomp v ao top jdata.1 jdata.2.1 i p q on with l|⟨k,km,kl,_⟩
    · exact l
    · simp only [eqJ,Finset.mem_insert,Finset.mem_singleton] at km; omega
  have e0 (p q : I) : d0 m p q = Vg v C j p q := by
    apply Bool.eq_iff_iff.mpr
    change (_ && _) = true ↔ gateVal n C j (row v p q) = true
    rw [andValBoth ao jdata.1 jdata.2.1]
    change (lit (rb v (side C j 0)) p q && lit (rb v (side C j 1)) p q) = true ↔
      Vp v C j 0 p q = true ∧ Vp v C j 1 p q = true
    rw [first,first,Bool.and_eq_true]
  have second (i : Fin 2) (p q : I) :
      Vp v C h i p q = (lit (rb v (side (n := n) C h i)) p q || (take i && d0 m p q)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true,Bool.and_eq_true,take,decide_eq_true_eq,e0]
    constructor
    · intro on
      rcases port_decomp v ao top hdata.1 hdata.2.1 i p q on with l|⟨k,km,kl,path,yes⟩
      · exact .inl l
      · have eq : k=j := by simp only [eqJ,Finset.mem_insert,Finset.mem_singleton] at km; omega
        subst k; exact .inr ⟨path,yes⟩
    · rintro (l|⟨r,on⟩)
      · exact direct_lit v h i p q l
      · exact path_on v r p q on
  refine ⟨take 0,take 1,e0,fun p q => ?_⟩
  apply Bool.eq_iff_iff.mpr
  change (_ && _) = true ↔ gateVal n C h (row v p q) = true
  rw [andValBoth ao hdata.1 hdata.2.1]
  change ((lit (rb v (side C h 0)) p q || (take 0 && d0 m p q)) &&
    (lit (rb v (side C h 1)) p q || (take 1 && d0 m p q))) = true ↔
    Vp v C h 0 p q = true ∧ Vp v C h 1 p q = true
  rw [second,second,Bool.and_eq_true]
end SixPhysical
