import SixPhysical
namespace SixTops
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open SixTerms SixPhysical
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

def sig (m : M) (a b k : Bool) (p q : I) := if k then d1 m a b p q else d0 m p q
def mix (d s : Bool) : Fin 5 := if d then (if s then 3 else 2) else (if s then 1 else 0)
theorem mix_eq (m : M) (a b d s : Bool) (i : Fin 3) (p q : I) :
    term m a b i (mix d s) p q = (sig m a b d p q && vertex (i,s) p q) := by
  cases d <;> cases s <;> rfl
def Winner (m : M) (a b : Bool) (i : Fin 3) (edge : I → I → Prop) :=
  ∃ k, term m a b i k (i,false) (i,true) = true ∧ ∀ p q, term m a b i k p q = true → edge p q
theorem positive_vertex (i : Fin 3) (s : Bool) : vertex (i,s) (i,false) (i,true) = true := by
  cases s <;> simp [vertex]
theorem mixed (m : M) (a b : Bool) (i : Fin 3) (edge : I → I → Prop) (d s : Bool)
    (on : sig m a b d (i,false) (i,true) = true)
    (safe : ∀ p q, sig m a b d p q = true → vertex (i,s) p q = true → edge p q) : Winner m a b i edge := by
  refine ⟨mix d s,by rw [mix_eq,on,positive_vertex]; rfl,?_⟩
  intro p q h
  rw [mix_eq,Bool.and_eq_true] at h
  exact safe p q h.1 h.2

theorem double (m : M) (a b : Bool) (i : Fin 3) (edge : I → I → Prop) (d e : Bool)
    (left : sig m a b d (i,false) (i,true) = true) (right : sig m a b e (i,false) (i,true) = true)
    (safe : ∀ p q, sig m a b d p q = true → sig m a b e p q = true → edge p q) : Winner m a b i edge := by
  by_cases eq : d=e
  · subst e; exact mixed m a b i edge d false left (fun p q h _ => safe p q h h)
  refine ⟨4,?_,?_⟩
  · cases d <;> cases e <;> simp_all [sig,term]
  · intro p q h
    change (d0 m p q && d1 m a b p q)=true at h
    obtain ⟨l,r⟩ := Bool.and_eq_true_iff.mp h
    cases d <;> cases e <;> first | exact (eq rfl).elim | exact safe p q l r | exact safe p q r l

theorem choose_port (v : I → Fin n) (ao : IsAO2 n C) (top : TopForm G C)
    {j h : ℕ} (eqJ : junk G C={j,h}) (m : M) (a b : Bool)
    (e0 : ∀ p q, d0 m p q = Vg v C j p q) (e1 : ∀ p q, d1 m a b p q = Vg v C h p q)
    (i : Fin 3) (t : tops G C) (s : Fin 2) (pos : Vp v C t s (i,false) (i,true) = true) :
    (∃ k : Bool, v (i,k) ∈ side (n := n) C t s) ∨
    ∃ d : Bool, sig m a b d (i,false) (i,true) = true ∧
      ∀ p q, sig m a b d p q = true → Vp v C t s p q = true := by
  obtain ⟨len,op,_⟩ := topData t.2
  rcases port_decomp v ao top len op s (i,false) (i,true) pos with litOn|⟨k,km,_,path,on⟩
  · rcases Bool.or_eq_true_iff.mp litOn with l|r
    · exact .inl ⟨false,of_decide_eq_true l⟩
    · exact .inl ⟨true,of_decide_eq_true r⟩
  · simp only [eqJ,Finset.mem_insert,Finset.mem_singleton] at km
    rcases km with rfl|rfl
    · exact .inr ⟨false,(e0 _ _).trans on,fun p q yes => path_on v path p q ((e0 p q) ▸ yes)⟩
    · exact .inr ⟨true,(e1 _ _).trans on,fun p q yes => path_on v path p q ((e1 p q) ▸ yes)⟩

theorem raw_on (v : I → Fin n) {t : ℕ} {s : Fin 2} {u : I}
    (mem : v u ∈ side (n := n) C t s) (p q : I) (on : vertex u p q=true) : Vp v C t s p q=true := by
  rcases (of_decide_eq_true on : u=p ∨ u=q) with rfl|rfl
  · exact sideVal mem (pairInput_left _ _)
  · exact sideVal mem (pairInput_right _ _)

/-- A clean accepting top supplies one of five clean terms on every projected
    singleton or pair. The all-raw choice would make the residual edge retained. -/
theorem actual_win (v : I → Fin n) (least : IsLeastAO G C) (top : TopForm G C)
    {j h : ℕ} (eqJ : junk G C={j,h}) (m : M) (a b : Bool)
    (e0 : ∀ p q, d0 m p q = Vg v C j p q) (e1 : ∀ p q, d1 m a b p q = Vg v C h p q)
    (i : Fin 3) (res : s(v (i,false),v (i,true)) ∈ Ustar G C) :
    Winner m a b i (fun p q => G.Adj (v p) (v q)) := by
  obtain ⟨g,hg,yes⟩ := acceptedTop least (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp res).1)
  let t : tops G C := ⟨g,hg⟩
  obtain ⟨len,op,below⟩ := topData hg
  obtain ⟨l,r⟩ := (andValBoth least.1 len op _).mp yes
  have safe (p q : I) (l : Vp v C t 0 p q=true) (r : Vp v C t 1 p q=true) : G.Adj (v p) (v q) :=
    (graphFun_pair G (v p) (v q)).mp (below _ ((andValBoth least.1 len op _).mpr ⟨l,r⟩))
  rcases choose_port v least.1 top eqJ m a b e0 e1 i t 0 l with ⟨s,sm⟩|⟨d,dp,du⟩ <;>
    rcases choose_port v least.1 top eqJ m a b e0 e1 i t 1 r with ⟨u,um⟩|⟨e,ep,eu⟩
  · have old := SimpleGraph.deleteEdges_adj.mp (cleanAdj least.1 hg 0 sm um)
    cases s <;> cases u
    · exact (old.1.ne rfl).elim
    · exact (old.2 res).elim
    · exact (old.2 (Sym2.eq_swap ▸ res)).elim
    · exact (old.1.ne rfl).elim
  · exact mixed m a b i _ e s ep (fun p q hE hl => safe p q (raw_on v sm p q hl) (eu p q hE))
  · exact mixed m a b i _ d u dp (fun p q hD hr => safe p q (du p q hD) (raw_on v um p q hr))
  · exact double m a b i _ d e dp ep (fun p q l' r' => safe p q (du p q l') (eu p q r'))
end SixTops
