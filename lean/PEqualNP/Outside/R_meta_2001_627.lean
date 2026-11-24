import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Maximal cross-independent pairs are described by one closed vertex set.
-- All bounded-chromatic families are solved by explicit color-class projections.
-- Equal sides are handled by the original graph circuit on the union.
-- Each remaining class needs only one orientation and singleton edge tests.
set_option maxHeartbeats 3200000 in
theorem PEqualNP.Outside.R_meta_2001_627
    (nested : ∃ a k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ¬ G.Colorable k → (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ C : Circuit, Monotone2 C →
      (∀ z : Fin n → Bool, C.eval (List.ofFn z) =
        decide (∃ u v, G.Adj u v ∧ z u = true ∧ z v = true)) →
      let mark := fun (S : Finset (Fin n)) => List.ofFn (fun i : Fin n => decide (i ∈ S))
      let polar := fun (S : Finset (Fin n)) =>
        Finset.univ.filter (fun v => ∀ u ∈ S, ¬ G.Adj u v)
      ∃ H : Circuit, Monotone2 H ∧ H.size + 1 ≤ a * (C.size + 1) ∧
        (∀ u v, G.Adj u v → H.eval (mark {u} ++ mark {v}) = true) ∧
        ∀ S, polar (polar S) = S → S ⊂ polar S →
          H.eval (mark S ++ mark (polar S)) = false)
    (incomparable : ∃ a k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ¬ G.Colorable k → (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ C : Circuit, Monotone2 C →
      (∀ z : Fin n → Bool, C.eval (List.ofFn z) =
        decide (∃ u v, G.Adj u v ∧ z u = true ∧ z v = true)) →
      let mark := fun (S : Finset (Fin n)) => List.ofFn (fun i : Fin n => decide (i ∈ S))
      let polar := fun (S : Finset (Fin n)) =>
        Finset.univ.filter (fun v => ∀ u ∈ S, ¬ G.Adj u v)
      ∃ H : Circuit, Monotone2 H ∧ H.size + 1 ≤ a * (C.size + 1) ∧
        (∀ u v, G.Adj u v → H.eval (mark {u} ++ mark {v}) = true) ∧
        ∀ S, polar (polar S) = S → ¬ S ⊆ polar S → ¬ polar S ⊆ S → S.sort < (polar S).sort →
          H.eval (mark S ++ mark (polar S)) = false) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [_x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : Fin x2 → Bool), x7.eval (List.ofFn x9) = Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size + (1 : ℕ) ≤ x1 * (x7.size + (1 : ℕ)) ∧ ∀ (x11 x12 : Fin x2 → Bool), x10.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x2), x3.Adj x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true) := by
  classical
  obtain ⟨a, ka, ha⟩ := nested
  obtain ⟨b, kb, hb⟩ := incomparable
  let q := max ka kb
  refine ⟨max (10 * (1+a+b)) (3*q*q+2), ?_⟩
  intro n G inst hdeg hgirth C hC hg
  let good (g : Gate) := g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
  let run (gs : List Gate) (w : List Bool) := gs.foldl step w
  let read (w : List Bool) (ks : List ℕ) := GateOp.or.eval (ks.map (fun i => w.getD i false))
  let og (ks : List ℕ) : Gate := ⟨.or, ks⟩
  have readOne (w : List Bool) (i : ℕ) : read w [i] = w.getD i false := by
    change (w.getD i false || false) = _
    exact Bool.or_false _
  have readTwo (w : List Bool) (i j : ℕ) : read w [i,j] = (w.getD i false || w.getD j false) := by
    change (w.getD i false || (w.getD j false || false)) = _
    rw [Bool.or_false]
  have readNil (w : List Bool) : read w [] = false := rfl
  have readPrefix (w t : List Bool) (ks : List ℕ) (hk : ∀ i ∈ ks, i < w.length) :
      read (w ++ t) ks = read w ks := by
    unfold read
    congr 1
    exact List.map_congr_left (fun i hi => List.getD_append _ _ _ _ (hk i hi))
  have prepared (w : List Bool) (ss : List (List ℕ)) (hb : ∀ ks ∈ ss, ∀ i ∈ ks, i < w.length) :
      ∀ t, run (ss.map og) (w ++ t) = (w ++ t) ++ ss.map (read w) := by
    induction ss with
    | nil => intro t; simp [run]
    | cons ks ss ih =>
      intro t
      change run (ss.map og) ((w ++ t) ++ [read (w ++ t) ks]) = _
      rw [readPrefix w t ks (hb ks List.mem_cons_self), List.append_assoc,
        ih (fun l hl => hb l (List.mem_cons_of_mem _ hl))]
      simp [List.append_assoc]
  have untouched (w : List Bool) (v : Bool) (i : ℕ) (h : i ≠ w.length) :
      (w ++ [v]).getD i false = w.getD i false := by
    by_cases hi : i < w.length
    · exact List.getD_append _ _ _ _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  -- At each gate use one OR for each of its at most two operands.
  -- Missing and forward reads remain empty disjunctions until their wires exist.
  have compile (gs : List Gate) (hgs : ∀ g ∈ gs, good g) (o : ℕ) :
      ∀ (r m : ℕ) (ref : ℕ → List ℕ), (∀ i, (ref i).length ≤ 2) →
      (∀ i j, j ∈ ref i → j < m) →
      ∃ (ts : List Gate) (out : ℕ), (∀ g ∈ ts, good g) ∧ ts.length ≤ 3 * gs.length + 1 ∧
        out < m + ts.length ∧ ∀ (w old : List Bool), w.length = m → old.length = r →
        (∀ i, read w (ref i) = old.getD i false) →
        (run ts w).getD out false = (run gs old).getD o false := by
    induction gs with
    | nil =>
      intro r m ref hl hb
      refine ⟨[og (ref o)], m, ?_, by simp, by simp, ?_⟩
      · intro g hg
        obtain rfl : g = og (ref o) := by simpa using hg
        exact ⟨Or.inr rfl, hl o⟩
      · intro w old hw _ hv
        change (w ++ [read w (ref o)]).getD m false = old.getD o false
        rw [← hw]
        simpa using hv o
    | cons g gs ih =>
      intro r m ref hl hb
      let ls := g.inputs.map ref
      let finalG : Gate := ⟨g.op, (List.range g.inputs.length).map (fun j => m + j)⟩
      let block := ls.map og ++ [finalG]
      let next := fun i => if i = r then [m + g.inputs.length] else ref i
      have gl := (hgs g List.mem_cons_self).2
      have nlen (i : ℕ) : (next i).length ≤ 2 := by
        by_cases hi : i = r <;> simp [next, hi, hl]
      have nbound (i j : ℕ) (hj : j ∈ next i) : j < m + g.inputs.length + 1 := by
        by_cases hi : i = r
        · simp [next, hi] at hj
          omega
        · simp [next, hi] at hj
          have := hb i j hj
          omega
      obtain ⟨ts, out, ht, hs, ho, he⟩ := ih (fun k hk => hgs k (List.mem_cons_of_mem _ hk))
        (r+1) (m + g.inputs.length + 1) next nlen nbound
      have lb : block.length = g.inputs.length + 1 := by simp [block, ls]
      refine ⟨block ++ ts, out, ?_, ?_, ?_, ?_⟩
      · intro k hk
        obtain hk | hk := List.mem_append.mp hk
        · obtain hk | hk := List.mem_append.mp hk
          · obtain ⟨refs, hrefs, rfl⟩ := List.mem_map.mp hk
            obtain ⟨i, _, rfl⟩ := List.mem_map.mp hrefs
            exact ⟨Or.inr rfl, hl i⟩
          · obtain rfl : k = finalG := by simpa using hk
            exact ⟨(hgs g List.mem_cons_self).1, by simpa [finalG] using gl⟩
        · exact ht k hk
      · simp only [List.length_append, List.length_cons, lb]
        omega
      · simp only [List.length_append, lb]
        omega
      · intro w old hw hr hv
        let vals := ls.map (read w)
        let val := g.op.eval (g.inputs.map (fun i => old.getD i false))
        have lv : vals.length = g.inputs.length := by simp [vals, ls]
        have initial : run (ls.map og) w = w ++ vals := by
          have hh (ks : List ℕ) (hk : ks ∈ ls) (j : ℕ) (hj : j ∈ ks) : j < w.length := by
            obtain ⟨i, _, rfl⟩ := List.mem_map.mp hk
            rw [hw]
            exact hb i j hj
          simpa [vals] using prepared w ls hh []
        have eyes : (List.range g.inputs.length).map
            (fun j => (w ++ vals).getD (m + j) false) = g.inputs.map (fun i => old.getD i false) := by
          apply List.ext_getElem
          · simp
          · intro i hi hj
            have ix : i < g.inputs.length := by simpa using hj
            simp only [List.getElem_map, List.getElem_range]
            rw [List.getD_append_right _ _ _ _ (by omega), show m + i - w.length = i by omega,
              List.getD_eq_getElem _ _ (by omega)]
            simpa [vals, ls] using hv g.inputs[i]
        have blockval : run block w = (w ++ vals) ++ [val] := by
          change (ls.map og ++ [finalG]).foldl step w = _
          rw [List.foldl_append]
          change step (run (ls.map og) w) finalG = _
          rw [initial]
          simp only [step, finalG, List.map_map, Function.comp_def, eyes, val]
        have rep (i : ℕ) : read (run block w) (next i) = (step old g).getD i false := by
          rw [blockval]
          by_cases eq : i = r
          · subst i
            have eqw : (w ++ vals).length = m + g.inputs.length := by simp [hw, lv]
            rw [show next r = [m + g.inputs.length] by simp [next], ← eqw, ← hr]
            rw [readOne]
            simp [step, val]
          · rw [show next i = ref i by simp [next, eq], List.append_assoc,
              readPrefix w _ _ (fun j hj => hw ▸ hb i j hj), hv]
            exact (untouched old _ i (by omega)).symm
        change ((block ++ ts).foldl step w).getD out false = (run gs (step old g)).getD o false
        rw [List.foldl_append]
        apply he (run block w) (step old g) _ _ rep
        · rw [blockval]
          simp [hw, lv, Nat.add_assoc]
        · simp [step, hr]
  let base (x y : Fin n → Bool) := List.ofFn x ++ List.ofFn y
  let Bld (F : (Fin n → Bool) → (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
    ∀ m, 2*n ≤ m → ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, good g) ∧
      gs.length ≤ s ∧ o < m + gs.length ∧ ∀ (w : List Bool), w.length = m →
      ∀ x y, base x y <+: w → (run gs w).getD o false = F x y
  have fromCircuit (Q : Circuit) (hq : Monotone2 Q) (r : ℕ)
      (src : (Fin n → Bool) → (Fin n → Bool) → List Bool) (ref : ℕ → List ℕ)
      (len : ∀ x y, (src x y).length = r) (hl : ∀ i, (ref i).length ≤ 2)
      (hb : ∀ i j, j ∈ ref i → j < 2*n)
      (hv : ∀ x y i, read (base x y) (ref i) = (src x y).getD i false) :
      Bld (fun x y => Q.eval (src x y)) (3 * Q.size + 1) := by
    intro m hm
    obtain ⟨gs, out, ok, sl, ol, e⟩ := compile Q.gates hq Q.output r m ref hl
      (fun i j h => (hb i j h).trans_le hm)
    refine ⟨gs, out, ok, sl, ol, ?_⟩
    intro w hw x y hp
    apply e w (src x y) hw (len x y)
    obtain ⟨t, rfl⟩ := hp
    intro i
    rw [readPrefix (base x y) t (ref i) (fun j h => by simpa [base, two_mul] using hb i j h)]
    exact hv x y i
  have atInput (x : Fin n → Bool) (j : ℕ) (hj : j < n) :
      (List.ofFn x).getD j false = x ⟨j, hj⟩ := by
    rw [List.getD_eq_getElem _ _ (by simpa using hj)]
    simp
  have left (x y : Fin n → Bool) (j : ℕ) (hj : j < n) :
      (base x y).getD j false = x ⟨j,hj⟩ := by
    unfold base
    rw [List.getD_append _ _ _ _ (by simpa using hj), atInput x j hj]
  have right (x y : Fin n → Bool) (j : ℕ) (hj : j < n) :
      (base x y).getD (n+j) false = y ⟨j,hj⟩ := by
    unfold base
    rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.add_sub_cancel_left,
      atInput y j hj]
  have unionBox : Bld (fun x y => C.eval (List.ofFn (fun i => x i || y i))) (3*C.size+1) := by
    let f (i : ℕ) := if i < n then [i,n+i] else []
    apply fromCircuit C hC n _ f (by simp) _ _ _
    · intro i; by_cases h : i<n <;> simp [f,h]
    · intro i j hj
      by_cases h : i<n
      · simp [f,h] at hj; rcases hj with rfl | rfl <;> omega
      · simp [f,h] at hj
    · intro x y i
      by_cases h : i<n
      · rw [show f i = [i,n+i] by simp [f,h], readTwo, left x y i h, right x y i h, atInput _ i h]
      · rw [List.getD_eq_default _ _ (by simp; omega)]
        rw [show f i = [] by simp [f,h], readNil]
  have plainBox (Q : Circuit) (hq : Monotone2 Q) :
      Bld (fun x y => Q.eval (base x y)) (3*Q.size+1) := by
    let f (i : ℕ) := if i < 2*n then [i] else []
    apply fromCircuit Q hq (2*n) base f (by simp [base,two_mul]) _ _ _
    · intro i; by_cases h : i<2*n <;> simp [f,h]
    · intro i j hj
      by_cases h : i<2*n
      · simp [f,h] at hj; omega
      · simp [f,h] at hj
    · intro x y i
      by_cases h : i<2*n
      · rw [show f i = [i] by simp [f,h], readOne]
      · rw [List.getD_eq_default _ _ (by simp [base]; omega)]
        rw [show f i = [] by simp [f,h], readNil]
  have flipBox (Q : Circuit) (hq : Monotone2 Q) :
      Bld (fun x y => Q.eval (base y x)) (3*Q.size+1) := by
    let f (i : ℕ) := if i < n then [n+i] else if i < 2*n then [i-n] else []
    apply fromCircuit Q hq (2*n) (fun x y => base y x) f (by simp [base,two_mul]) _ _ _
    · intro i; by_cases h : i<n <;> by_cases h' : i<2*n <;> simp [f,h,h']
    · intro i j hj
      by_cases h : i<n
      · simp [f,h] at hj; omega
      · by_cases h' : i<2*n
        · simp [f,h,h'] at hj; omega
        · simp [f,h,h'] at hj
    · intro x y i
      by_cases h : i<n
      · rw [show f i = [n+i] by simp [f,h], readOne, right x y i h, left y x i h]
      · by_cases h' : i < 2*n
        · have d : i-n<n := by omega
          have rev := right y x (i-n) d
          rw [show n+(i-n)=i by omega] at rev
          rw [show f i = [i-n] by simp [f,h,h'], readOne, rev, left x y (i-n) d]
        · rw [List.getD_eq_default _ _ (by simp [base]; omega)]
          rw [show f i = [] by simp [f,h,h'], readNil]
  have suffix (gs : List Gate) : ∀ w, ∃ t : List Bool, run gs w = w ++ t ∧ t.length = gs.length := by
    induction gs with
    | nil => intro w; exact ⟨[], by simp [run], rfl⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t,h,ht⟩ := ih (step w g)
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [ht]⟩
      change run gs (step w g) = _
      rw [h]
      simp [step]
  -- Append the second block after the first, then read both saved outputs.
  have binary (op : GateOp) (f : Bool → Bool → Bool)
      (goodOp : op = GateOp.and ∨ op = GateOp.or) (calcOp : ∀ a b, op.eval [a,b] = f a b)
      {F J : (Fin n → Bool) → (Fin n → Bool) → Bool} {s k : ℕ}
      (hF : Bld F s) (hJ : Bld J k) : Bld (fun x y => f (F x y) (J x y)) (s+k+1) := by
    intro m hm
    obtain ⟨g1, o1, ok1, l1, b1, e1⟩ := hF m hm
    obtain ⟨g2, o2, ok2, l2, _, e2⟩ := hJ (m+g1.length) (by omega)
    let lastG : Gate := ⟨op,[o1,o2]⟩
    refine ⟨g1++g2++[lastG], m+g1.length+g2.length, ?_, by simp; omega, by simp; omega, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with (hg|hg)|rfl
      · exact ok1 g hg
      · exact ok2 g hg
      · exact ⟨goodOp, le_rfl⟩
    · intro w hw x y hp
      obtain ⟨t, h1, ht⟩ := suffix g1 w
      obtain ⟨u, h2, hu⟩ := suffix g2 (run g1 w)
      have w1 : (run g1 w).length = m+g1.length := by simp [h1,hw,ht]
      have w2 : (run g2 (run g1 w)).length = m+g1.length+g2.length := by simp [h2,w1,hu]
      have val1 : (run g2 (run g1 w)).getD o1 false = F x y := by
        rw [h2,List.getD_append _ _ _ _ (by omega),e1 w hw x y hp]
      have val2 := e2 (run g1 w) w1 x y (hp.trans (show w <+: run g1 w from ⟨t,h1.symm⟩))
      change ((g1++g2++[lastG]).foldl step w).getD _ false = _
      rw [List.foldl_append,List.foldl_append]
      change ((run g2 (run g1 w)) ++ [op.eval
        ([o1,o2].map (fun i => (run g2 (run g1 w)).getD i false))]).getD _ false = _
      rw [← w2]
      rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
      change op.eval [(run g2 (run g1 w)).getD o1 false,(run g2 (run g1 w)).getD o2 false] = _
      rw [calcOp,val1,val2]
  have conjoin {F J : (Fin n → Bool) → (Fin n → Bool) → Bool} {s k : ℕ}
      (hF : Bld F s) (hJ : Bld J k) : Bld (fun x y => F x y && J x y) (s+k+1) :=
    binary GateOp.and (· && ·) (Or.inl rfl) (by
      intro v w; change (v && (w && true)) = _; rw [Bool.and_true]) hF hJ
  have disjoin {F J : (Fin n → Bool) → (Fin n → Bool) → Bool} {s k : ℕ}
      (hF : Bld F s) (hJ : Bld J k) : Bld (fun x y => F x y || J x y) (s+k+1) :=
    binary GateOp.or (· || ·) (Or.inr rfl) (by
      intro v w; change (v || (w || false)) = _; rw [Bool.or_false]) hF hJ
  -- For a proper q-coloring, each ordered pair of color classes gives one projection
  -- of the original circuit. The disjunction has at most a quadratic factor in q.
  by_cases low : G.Colorable q
  · obtain ⟨color⟩ := low
    let mix (e : Fin q × Fin q) (x y : Fin n → Bool) (i : Fin n) :=
      if color i = e.1 then x i else if color i = e.2 then y i else false
    have colorBox (e : Fin q × Fin q) :
        Bld (fun x y => C.eval (List.ofFn (mix e x y))) (3 * C.size + 1) := by
      let f (i : ℕ) := if h : i < n then
        if color ⟨i,h⟩ = e.1 then [i] else if color ⟨i,h⟩ = e.2 then [n+i] else [] else []
      apply fromCircuit C hC n _ f (by simp) _ _ _
      · intro i
        unfold f
        split_ifs <;> simp
      · intro i j hj
        unfold f at hj
        split_ifs at hj <;> simp at hj <;> omega
      · intro x y i
        by_cases h : i < n
        · rw [atInput _ i h]
          by_cases ha : color ⟨i,h⟩ = e.1
          · rw [show f i = [i] by simp [f,h,ha], readOne, left x y i h]
            simp [mix,ha]
          · by_cases hb : color ⟨i,h⟩ = e.2
            · rw [show f i = [n+i] by simp only [f,dite_eq_left h, ite_eq_right ha, ite_eq_left hb],
                readOne, right x y i h]
              simp only [mix,ite_eq_right ha,ite_eq_left hb]
            · rw [show f i = [] by simp [f,h,ha,hb], readNil]
              simp [mix,ha,hb]
        · rw [List.getD_eq_default _ _ (by simp; omega), show f i = [] by simp [f,h], readNil]
    have many (es : List (Fin q × Fin q)) :
        Bld (fun x y => es.any (fun e => C.eval (List.ofFn (mix e x y))))
          ((3 * C.size + 2) * es.length + 1) := by
      induction es with
      | nil =>
        intro m hm
        refine ⟨[og []],m, ?_, by simp, by simp, ?_⟩
        · intro g hg
          obtain rfl : g = og [] := by simpa using hg
          exact ⟨Or.inr rfl, Nat.zero_le _⟩
        · intro w hw x y hp
          change (w ++ [false]).getD m false = false
          rw [← hw]
          simp
      | cons e es ih =>
        have add := disjoin (colorBox e) ih
        have cost : (3 * C.size + 1) + ((3 * C.size + 2) * es.length + 1) + 1 =
            (3 * C.size + 2) * (e :: es).length + 1 := by simp; ring
        rw [← cost]
        exact add
    let allPairs := (Finset.univ : Finset (Fin q × Fin q)).toList
    obtain ⟨gs,o,ok,sl,_,ev⟩ := many allPairs (2*n) le_rfl
    have len : allPairs.length = q*q := by simp [allPairs]
    rw [len] at sl
    refine ⟨⟨gs,o⟩, ok, ?_, ?_⟩
    · change gs.length + 1 ≤ _
      calc
        gs.length + 1 ≤ (3*C.size+2)*(q*q)+2 := by omega
        _ ≤ (3*q*q+2)*(C.size+1) := by nlinarith [Nat.zero_le (q*q)]
        _ ≤ _ := Nat.mul_le_mul_right _ (le_max_right _ _)
    · intro x y
      rw [show (⟨gs,o⟩ : Circuit).eval (List.ofFn x ++ List.ofFn y) = _ from
        ev (base x y) (by simp [base,two_mul]) x y (List.prefix_refl _), Bool.eq_iff_iff]
      simp only [List.any_eq_true, allPairs, Finset.mem_toList, Finset.mem_univ, true_and,
        decide_eq_true_eq]
      constructor
      · rintro ⟨e, he⟩
        rw [hg, decide_eq_true_eq] at he
        obtain ⟨u,v,edge,hu,hv⟩ := he
        have side (i : Fin n) (hi : mix e x y i = true) :
            (color i = e.1 ∧ x i = true) ∨ (color i = e.2 ∧ y i = true) := by
          by_cases ha : color i = e.1
          · exact Or.inl ⟨ha, by simpa [mix,ha] using hi⟩
          · by_cases hb : color i = e.2
            · exact Or.inr ⟨hb, by simpa only [mix,ite_eq_right ha,ite_eq_left hb] using hi⟩
            · simp [mix,ha,hb] at hi
        rcases side u hu with ⟨cu,xu⟩ | ⟨cu,yu⟩ <;> rcases side v hv with ⟨cv,xv⟩ | ⟨cv,yv⟩
        · exact (color.valid edge (cu.trans cv.symm)).elim
        · exact ⟨u,v,edge,xu,yv⟩
        · exact ⟨v,u,G.adj_symm edge,xv,yu⟩
        · exact (color.valid edge (cu.trans cv.symm)).elim
      · rintro ⟨u,v,edge,xu,yv⟩
        refine ⟨(color u,color v), ?_⟩
        rw [hg, decide_eq_true_eq]
        exact ⟨u,v,edge,by simp [mix,xu],by simp [mix,(color.valid edge).symm,yv]⟩
  have highA : ¬ G.Colorable ka := fun hc => low (SimpleGraph.Colorable.mono (le_max_left _ _) hc)
  have highB : ¬ G.Colorable kb := fun hc => low (SimpleGraph.Colorable.mono (le_max_right _ _) hc)
  let char (S : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ S)
  let mark (S : Finset (Fin n)) := List.ofFn (char S)
  let polar (S : Finset (Fin n)) : Finset (Fin n) :=
    Finset.univ.filter (fun v => ∀ u ∈ S, ¬ G.Adj u v)
  have polmem {S : Finset (Fin n)} {v : Fin n} : v ∈ polar S ↔ ∀ u ∈ S, ¬ G.Adj u v := by
    simp [polar]
  have anti {S T : Finset (Fin n)} (h : S ⊆ T) : polar T ⊆ polar S :=
    fun _ hv => polmem.mpr (fun u hu => polmem.mp hv u (h hu))
  have extensive (S : Finset (Fin n)) : S ⊆ polar (polar S) := by
    intro u hu
    exact polmem.mpr (fun v hv hvu => polmem.mp hv u hu (G.adj_symm hvu))
  have triple (S : Finset (Fin n)) : polar (polar (polar S)) = polar S :=
    Finset.Subset.antisymm (anti (extensive S)) (extensive (polar S))
  obtain ⟨H, hH, sH, eH, zH⟩ := ha n G highA hdeg hgirth C hC hg
  obtain ⟨K, hK, sK, eK, zK⟩ := hb n G highB hdeg hgirth C hC hg
  change ∀ u v, G.Adj u v → H.eval (mark {u} ++ mark {v}) = true at eH
  change ∀ u v, G.Adj u v → K.eval (mark {u} ++ mark {v}) = true at eK
  change ∀ S, polar (polar S) = S → S ⊂ polar S → H.eval (mark S ++ mark (polar S)) = false at zH
  change ∀ S, polar (polar S) = S → ¬ S ⊆ polar S → ¬ polar S ⊆ S →
    S.sort < (polar S).sort → K.eval (mark S ++ mark (polar S)) = false at zK
  have assembled :
      ∃ D : Circuit, Monotone2 D ∧ D.size + 1 ≤ 10 * (C.size + H.size + K.size + 1) ∧
        ∀ x y : Fin n → Bool, let X := List.ofFn x; let Y := List.ofFn y
          D.eval (X ++ Y) = (C.eval (List.ofFn (fun i => x i || y i)) &&
            H.eval (X ++ Y) && H.eval (Y ++ X) && K.eval (X ++ Y) && K.eval (Y ++ X)) := by
    have total := conjoin (conjoin (conjoin (conjoin unionBox (plainBox H hH)) (flipBox H hH))
      (plainBox K hK)) (flipBox K hK)
    obtain ⟨gs,o,ok,sl,_,ev⟩ := total (2*n) le_rfl
    refine ⟨⟨gs,o⟩, ok, ?_, ?_⟩
    · change gs.length + 1 ≤ _
      omega
    · intro x y
      exact ev (base x y) (by simp [base,two_mul]) x y (List.prefix_refl _)
  obtain ⟨D, hD, sD, valD⟩ := assembled
  refine ⟨D, hD, ?_, ?_⟩
  · calc
      D.size + 1 ≤ 10 * (C.size + H.size + K.size + 1) := sD
      _ ≤ 10 * ((C.size + 1) + a * (C.size + 1) + b * (C.size + 1)) :=
        Nat.mul_le_mul_left 10 (by omega)
      _ = 10 * (1 + a + b) * (C.size + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (le_max_left _ _)
  -- The gate and fold argument follows the library's LowMergeWires proof.
  · let LeL (a b : List Bool) : Prop := ∀ i, a.getD i false = true → b.getD i false = true
    have eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
        (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
        op.eval (l.map f) = true → op.eval (l.map f') = true := by
      rcases hop with rfl | rfl
      · change (l.map f).all id = true → (l.map f').all id = true
        simp only [List.all_eq_true, List.mem_map, id]
        intro H x hx
        obtain ⟨i, hi, rfl⟩ := hx
        exact h i (H (f i) ⟨i, hi, rfl⟩)
      · change (l.map f).any id = true → (l.map f').any id = true
        simp only [List.any_eq_true, List.mem_map, id]
        rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
        exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

    have fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
        ∀ a b : List Bool, a.length = b.length → LeL a b →
          LeL (gs.foldl step a) (gs.foldl step b) := by
      induction gs with
      | nil => intro a b _ h; exact h
      | cons g gs ih =>
        intro a b hl h
        rw [List.foldl_cons, List.foldl_cons]
        apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
        · simp [step, hl]
        · intro i hi
          unfold step at hi ⊢
          by_cases hia : i < a.length
          · rw [List.getD_append _ _ _ _ hia] at hi
            rw [List.getD_append _ _ _ _ (by omega)]
            exact h i hi
          · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
            rw [List.getD_append_right _ _ _ _ (by omega)]
            rw [← hl]
            by_cases he : i - a.length = 0
            · rw [he] at hi ⊢
              simp only [List.getD_cons_zero] at hi ⊢
              exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
            · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
              rw [hm] at hi; simp at hi
    have rise {x y x' y' : Fin n → Bool}
        (hx : ∀ i, x i = true → x' i = true) (hy : ∀ i, y i = true → y' i = true) :
        D.eval (List.ofFn x ++ List.ofFn y) = true →
          D.eval (List.ofFn x' ++ List.ofFn y') = true := by
      have one {p q : Fin n → Bool} (h : ∀ i, p i = true → q i = true) :
          LeL (List.ofFn p) (List.ofFn q) := by
        intro i hi
        by_cases ilt : i < n
        · rw [List.getD_eq_getElem _ _ (by simpa using ilt)] at hi ⊢
          simpa using h ⟨i, ilt⟩ (by simpa using hi)
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
          contradiction
      apply fold_mono D.gates (fun g hg' => (hD g hg').1) _ _ (by simp) _ D.output
      intro i hi
      by_cases ilt : i < n
      · rw [List.getD_append _ _ _ _ (by simpa using ilt)] at hi ⊢
        exact one hx i hi
      · rw [List.getD_append_right _ _ _ _ (by simp; omega)] at hi ⊢
        simpa only [List.length_ofFn] using one hy (i - n) (by simpa only [List.length_ofFn] using hi)
    have vsets (S T : Finset (Fin n)) :
        D.eval (mark S ++ mark T) =
        (C.eval (List.ofFn (fun i => char S i || char T i)) &&
          H.eval (mark S ++ mark T) && H.eval (mark T ++ mark S) &&
          K.eval (mark S ++ mark T) && K.eval (mark T ++ mark S)) := valD (char S) (char T)
    have hit (u v : Fin n) (hedge : G.Adj u v) : D.eval (mark {u} ++ mark {v}) = true := by
      rw [vsets, hg]
      have h : ∃ s t, G.Adj s t ∧ (char {u} s || char {v} s) = true ∧
          (char {u} t || char {v} t) = true := ⟨u, v, hedge, by simp [char], by simp [char]⟩
      rw [decide_eq_true h, eH u v hedge, eH v u (G.adj_symm hedge), eK u v hedge, eK v u (G.adj_symm hedge)]
      rfl
    have miss (A B : Finset (Fin n)) (pA : polar A = B) (pB : polar B = A) :
        D.eval (mark A ++ mark B) = false := by
      have cA : polar (polar A) = A := pA ▸ pB
      have cB : polar (polar B) = B := pB ▸ pA
      rw [vsets]
      by_cases eqAB : A = B
      · rw [← eqAB]
        have stable : polar A = A := pA.trans eqAB.symm
        have clean : ¬ ∃ u v, G.Adj u v ∧ (char A u || char A u) = true ∧
            (char A v || char A v) = true := by
          simp only [Bool.or_self, char, decide_eq_true_eq]
          rintro ⟨u, v, huv, hu, hv⟩
          exact polmem.mp (stable.symm ▸ hv) u hu huv
        rw [hg, decide_eq_false clean]
        rfl
      · by_cases ab : A ⊆ B
        · have nz := zH A cA (by rw [pA]; exact Finset.ssubset_iff_subset_ne.mpr ⟨ab, eqAB⟩)
          rw [pA] at nz
          simp [nz]
        · by_cases ba : B ⊆ A
          · have nz := zH B cB (by rw [pB]; exact Finset.ssubset_iff_subset_ne.mpr ⟨ba, Ne.symm eqAB⟩)
            rw [pB] at nz
            simp [nz]
          · have different : A.sort ≠ B.sort := by
              intro heq
              apply eqAB
              simpa only [Finset.sort_toFinset] using congrArg List.toFinset heq
            rcases lt_or_gt_of_ne different with small | small
            · have nz := zK A cA (pA ▸ ab) (pA ▸ ba) (pA ▸ small)
              rw [pA] at nz
              simp [nz]
            · have nz := zK B cB (pB ▸ ba) (pB ▸ ab) (pB ▸ small)
              rw [pB] at nz
              simp [nz]
    intro x y
    by_cases cross : ∃ u v, G.Adj u v ∧ x u = true ∧ y v = true
    · rw [decide_eq_true cross]
      obtain ⟨u, v, huv, hx, hy⟩ := cross
      apply rise (x := char {u}) (y := char {v}) _ _ (hit u v huv)
      · intro i hi
        have hiu : i = u := by simpa [char] using hi
        exact hiu ▸ hx
      · intro i hi
        have hiv : i = v := by simpa [char] using hi
        exact hiv ▸ hy
    · rw [decide_eq_false cross]
      let S := Finset.univ.filter (fun i => x i = true)
      let B := polar S
      let A := polar B
      have xA (i : Fin n) (hi : x i = true) : char A i = true := by
        exact decide_eq_true (extensive S (by simp [S, hi]))
      have yB (i : Fin n) (hi : y i = true) : char B i = true := by
        apply decide_eq_true
        apply polmem.mpr
        intro u hu huv
        exact cross ⟨u, i, huv, (Finset.mem_filter.mp hu).2, hi⟩
      have hfalse := miss A B (triple S) rfl
      cases hv : D.eval (List.ofFn x ++ List.ofFn y) with
      | false => rfl
      | true =>
        have htrue := rise xA yB hv
        change D.eval (mark A ++ mark B) = true at htrue
        rw [hfalse] at htrue
        contradiction
