import ChangeGate

namespace ResidualChange
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_7465_aux PEqualNP.Outside.L_meta_7465_aux.Routing
open PEqualNP.Outside.L_meta_1491
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem abstract_least (least : IsLeastAO G C) : S98.Least n C :=
  ⟨S98.AO_of_IsAO2 _ _ least.1,fun D ao eq => least.2.2 D (S98.IsAO2_of_AO _ _ ao)
    (funext fun x => (eq x).trans (congrFun least.2.1 x))⟩

theorem output_bound (least : IsLeastAO G C) (edges : G.edgeFinset.Nonempty) : C.output<n+C.gates.length := by
  obtain ⟨x,on⟩ := S98.gf_true n G edges
  have yes : value C x C.output = true := (congrFun least.2.1 x).trans on
  by_contra! hi
  exact Bool.false_ne_true ((val_ge (n := n) (C := C) (x := List.ofFn x) (by simp) hi).symm.trans yes)

/-- Every clean gate has an OR-only route to the output of the least top-form circuit. -/
theorem route_to_output (least : IsLeastAO G C) (form : TopForm G C) (edges : G.edgeFinset.Nonempty)
    (k : ℕ) (len : k<C.gates.length) (below : BelowF G C k) :
    Relation.ReflTransGen (OrStep n C) C.output (n+k) := by
  by_cases out : n+k=C.output
  · rw [out]
  obtain ⟨r,read,op,clean⟩ := (S98.main_real n G C edges least form).1 k len below out
  have rm : r∈readers n C k := read ▸ Finset.mem_singleton_self _
  obtain ⟨lr,mem⟩ := Finset.mem_filter.mp rm
  have bound := Finset.mem_range.mp lr
  have earlier := least.1.2.1 r bound _ mem
  exact (route_to_output least form edges r bound clean).tail ⟨r,bound,rfl,op,mem,earlier⟩
termination_by C.gates.length-k
decreasing_by omega

theorem copy_or_path {j : ℕ} (andOp : (gateAt C j).op = GateOp.and) (i : ℕ) {p q : ℕ}
    (path : Relation.ReflTransGen (OrStep n C) p q) :
    Relation.ReflTransGen (OrStep n (copyWire C j i)) p q := by
  induction path with
  | refl => exact .refl
  | tail _ step ih =>
    obtain ⟨k,kl,eq,op,mem,lt⟩ := step
    have ne : k ≠ j := by rintro rfl; rw [andOp] at op; cases op
    have gate := gate_same C i kl ne
    exact ih.tail ⟨k,by simpa,eq,gate ▸ op,gate ▸ mem,lt⟩

/-- Every raw star edge keeps a complete positive path after any one dirty AND is narrowed. -/
theorem star_survives (least : IsLeastAO G C) (form : TopForm G C) (edges : G.edgeFinset.Nonempty)
    {j : ℕ} (dirty : j∈junk G C) (u : Fin n) (x : Fin n → Bool) (p q : Fin n)
    (star : s(p,q)∈starEdges G C) (onP : x p=true) (onQ : x q=true) :
    value (copyWire C j u.val) x C.output = true := by
  obtain ⟨jl,jo,xx,bad,off⟩ := junkData dirty
  obtain ⟨t,ht,mem⟩ := Finset.mem_biUnion.mp star
  obtain ⟨⟨v,w⟩,both,eq⟩ := Finset.mem_image.mp mem
  obtain ⟨lv,rw'⟩ := Finset.mem_product.mp both
  have bits : x v=true ∧ x w=true := by
    rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> exact ⟨by assumption,by assumption⟩
  obtain ⟨tl,to',tb⟩ := topData ht
  have ne : t ≠ j := by rintro rfl; exact Bool.false_ne_true (off.symm.trans (tb _ bad))
  have gate := gate_same C u.val tl ne
  have inputs (b : Fin 2) : opnd (copyWire C j u.val) t b = opnd C t b := by simp [opnd,gate]
  have lo := copy_or_path jo u.val (mem_orIn_reach v lv)
  have ro := copy_or_path jo u.val (mem_orIn_reach w rw')
  have fired := (andValBoth (ao_copy least.1 (show u.val<n+j by have := u.isLt; omega))
    (show t<(copyWire C j u.val).gates.length by simpa) (gate ▸ to') x).2
    ⟨(inputs 0) ▸ reach_var_val x _ v lo bits.1,(inputs 1) ▸ reach_var_val x _ w ro bits.2⟩
  exact orStep_up (by simp) (copy_or_path jo u.val (route_to_output least form edges t tl tb)) fired

/-- A dirty gate that fires on a singleton must fire on a residual edge away
    from that vertex. Otherwise copying the input there preserves the entire
    graph function and leaves a duplicate gate in a least circuit. -/
theorem residual_witness (least : IsLeastAO G C) (form : TopForm G C) (edges : G.edgeFinset.Nonempty)
    {j : ℕ} (dirty : j ∈ junk G C) (u : Fin n) (singleton : gateVal n C j (pairInput u u)=true) :
    ∃ p q : Fin n, s(p,q) ∈ Ustar G C ∧ p≠u ∧ q≠u ∧ gateVal n C j (pairInput p q)=true := by
  classical
  by_contra! none
  let D := copyWire C j u.val
  have inside := (junkData dirty).1
  have prior : u.val<n+j := by have := u.isLt; omega
  have ao : IsAO2 n D := ao_copy least.1 prior
  have sz : D.gates.length=C.gates.length := length_copy _ _ _
  have out := output_bound least edges
  have gate (k) (hk : k<C.gates.length) (ne : k≠j) : gateAt D k=gateAt C k := gate_same C _ hk ne
  have comp (x : Fin n → Bool) : D.eval (List.ofFn x) = graphFun G ∅ x := by
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro on
      have lower : value D x (n+j)=true → value C x (n+j)=true := by
        rw [copied_value inside]
        intro xu
        exact StarGrowth.wire_mono least.1 (fun w yes => by
          rcases (pairInput_true _ _ _).mp yes with rfl|rfl <;> exact xu) (by omega) singleton
      have old := compare ao sz j (fun k hk => gate k (by omega)) x lower C.output (by omega) on
      exact (congrFun least.2.1 x) ▸ old
    · intro on
      have pair : ∃ p q : Fin n, G.Adj p q ∧ x p=true ∧ x q=true := by simpa [graphFun] using on
      obtain ⟨p,q,adj,px,qx⟩ := pair
      by_cases star : s(p,q) ∈ starEdges G C
      · exact star_survives least form edges dirty u x p q star px qx
      have res : s(p,q) ∈ Ustar G C := Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr adj,star⟩
      have lower : value C (pairInput p q) (n+j)=true → value D (pairInput p q) (n+j)=true := by
        rw [copied_value inside]
        intro yes
        apply (pairInput_true _ _ _).mpr
        by_contra! nope
        exact (none p q res (Ne.symm nope.1) (Ne.symm nope.2)) yes
      have old : value C (pairInput p q) C.output=true := (congrFun least.2.1 _).trans ((graphFun_pair G p q).2 adj)
      have new := compare least.1 sz.symm j (fun k hk ne => (gate k hk ne).symm) _ lower C.output out old
      exact StarGrowth.wire_mono ao (fun w yes => by rcases (pairInput_true _ _ _).mp yes with rfl|rfl <;> assumption)
        (by omega : C.output<n+D.gates.length) new
  have dl : IsLeastAO G D := ⟨ao,funext comp,fun E eao eq => by
    change D.gates.length ≤ E.gates.length
    rw [sz]; exact least.2.2 E eao eq⟩
  obtain ⟨x,ne⟩ := S98.least_nodup n D (abstract_least dl) u.val j prior (by omega)
  exact ne ((S98.W_input n D x u.val u.isLt).trans (copied_value inside u x).symm)

#print axioms residual_witness
end ResidualChange
