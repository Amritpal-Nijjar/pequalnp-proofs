import Positions

namespace Five18096Bypass

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_12108 FiveInputLower Five18096Fresh Five18096Ends

structure Mark where
  low : Bool
  high : Bool
  path : Bool

def empty : Mark := ⟨false,false,false⟩
def read (w : List Mark) (i : ℕ) := w.getD i empty
def step (w : List Mark) (g : Gate) : Mark :=
  ⟨g.op.eval (g.inputs.map fun j => (read w j).low),
   g.op.eval (g.inputs.map fun j => (read w j).high),
   !isNot g && g.inputs.any (fun j => (read w j).path)⟩
def run (gs : List Gate) (w : List Mark) :=
  gs.foldl (fun ws g => ws ++ [step ws g]) w

def Asc (v : Mark) := v.low=true → v.high=true
def Covered (v : Mark) := v.path=false → v.high=true → v.low=true
def Legal (g : Gate) := g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)

lemma read_inv (w : List Mark) (P : Mark → Prop) (h : ∀ v ∈ w, P v) (he : P empty)
    (j : ℕ) : P (read w j) := by
  unfold read
  rw [List.getD_eq_getElem?_getD]
  cases e : w[j]? with
  | none => exact he
  | some v => exact h v (List.mem_of_getElem? e)

lemma legal_ao (g : Gate) (leg : Legal g) (nn : isNot g=false) :
    g.op = .and ∨ g.op = .or := by
  unfold Legal at leg
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at leg
  rcases leg with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · simp [isNot,h] at nn

lemma preserve (l : List ℕ) (u v : ℕ → Bool) (op : GateOp) (ao : op=.and ∨ op=.or)
    (h : ∀ j ∈ l, u j=true → v j=true) :
    op.eval (l.map u)=true → op.eval (l.map v)=true := by
  rcases ao with rfl | rfl
  · intro e
    apply List.all_eq_true.mpr
    intro b hb
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hb
    exact h j hj (List.all_eq_true.mp e _ (List.mem_map_of_mem hj))
  · intro e
    obtain ⟨b,hb,t⟩ := List.any_eq_true.mp e
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hb
    exact List.any_eq_true.mpr ⟨v j,List.mem_map_of_mem hj,h j hj t⟩

lemma append_inv (P : Mark → Prop) {w : List Mark} {z : Mark}
    (h : ∀ v ∈ w, P v) (hz : P z) : ∀ v ∈ w++[z], P v := by
  intro v hv
  rcases List.mem_append.mp hv with hp | hp
  · exact h v hp
  · exact List.mem_singleton.mp hp ▸ hz

lemma asc_ao (w : List Mark) (g : Gate) (ao : g.op=.and ∨ g.op=.or) (h : ∀ v ∈ w, Asc v) :
    Asc (step w g) := by
  apply preserve _ _ _ _ ao
  intro j _
  exact read_inv w Asc h (fun h => h) j

lemma cover_ao (w : List Mark) (g : Gate) (leg : Legal g) (nn : isNot g=false)
    (h : ∀ v ∈ w, Covered v) : Covered (step w g) := by
  intro off
  apply preserve _ _ _ _ (legal_ao g leg nn)
  intro j hj
  have no : ∀ k ∈ g.inputs, (read w k).path=false := by
    simpa [step,nn,List.any_eq_false] using off
  exact read_inv w Covered h (fun _ h => h) j (no j hj)

lemma cover_not (w : List Mark) (g : Gate) (n : g.op=.not) (h : ∀ v ∈ w, Asc v) :
    Covered (step w g) := by
  intro _ yes
  obtain ⟨op,l⟩ := g
  change op=.not at n
  subst op
  cases l with
  | nil => rfl
  | cons j l =>
    have hj := read_inv w Asc h (fun h => h) j
    change !(read w j).high = true at yes
    change !(read w j).low = true
    unfold Asc at hj
    cases e : (read w j).low <;> simp_all

lemma ao_both (p : List Gate) (w : List Mark) (leg : ∀ g ∈ p, Legal g)
    (nn : ∀ g ∈ p, isNot g=false) (asc : ∀ v ∈ w, Asc v) (cov : ∀ v ∈ w, Covered v) :
    (∀ v ∈ run p w, Asc v) ∧ ∀ v ∈ run p w, Covered v := by
  induction p generalizing w with
  | nil => exact ⟨asc,cov⟩
  | cons g p ih =>
    have l := leg g (by simp)
    have n := nn g (by simp)
    exact ih _ (fun a ha => leg a (by simp [ha])) (fun a ha => nn a (by simp [ha]))
      (append_inv Asc asc (asc_ao w g (legal_ao g l n) asc))
      (append_inv Covered cov (cover_ao w g l n cov))

lemma ao_cover (s : List Gate) (w : List Mark) (leg : ∀ g ∈ s, Legal g)
    (nn : ∀ g ∈ s, isNot g=false) (cov : ∀ v ∈ w, Covered v) :
    ∀ v ∈ run s w, Covered v := by
  induction s generalizing w with
  | nil => exact cov
  | cons g s ih =>
    have l := leg g (by simp)
    have n := nn g (by simp)
    exact ih _ (fun a ha => leg a (by simp [ha])) (fun a ha => nn a (by simp [ha]))
      (append_inv Covered cov (cover_ao w g l n cov))

def phys (gs : List Gate) (w : List Bool) :=
  gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun j => ws.getD j false)]) w

lemma project_read (f : Mark → Bool) (e : f empty=false) (w : List Mark) (j : ℕ) :
    f (read w j)=(w.map f).getD j false := by
  simp only [read,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h : w[j]? <;> simp [e]

lemma project_run (f : Mark → Bool) (e : f empty=false)
    (single : ∀ w g, f (step w g) = g.op.eval (g.inputs.map fun j => f (read w j)))
    (gs : List Gate) (w : List Mark) : (run gs w).map f = phys gs (w.map f) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w++[step w g])).map f = _
    rw [ih]
    simp [phys,List.foldl_cons,single,project_read f e]

def pairs (i : Fin 5) : ℕ := [2,1,1,1,6].getD i.val 0
def pre (i j : Fin 5) : Bool := (pairs i).testBit j
def post (i j : Fin 5) : Bool := (pairs i).testBit j || decide (i=j)
def roots (i : Fin 5) : List Mark := List.ofFn fun j : Fin 5 => ⟨pre i j,post i j,decide (i=j)⟩

lemma sensitive : ∀ i : Fin 5, tableFun 5 b (pre i)=false ∧ tableFun 5 b (post i)=true :=
  by decide +kernel

def cleanPaths (gs : List Gate) (w : List Bool) :=
  gs.foldl (fun ws g => ws ++ [!isNot g && g.inputs.any (fun j => ws.getD j false)]) w

lemma path_run (gs : List Gate) (w : List Mark) :
    (run gs w).map Mark.path = cleanPaths gs (w.map Mark.path) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w++[step w g])).map Mark.path = _
    rw [ih]
    simp [cleanPaths,List.foldl_cons,step,project_read Mark.path rfl]

theorem bypass (C : Circuit) (legal : FanInTwo C) (cap : C.size ≤ 10)
    (computes : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = tableFun 5 b x)
    (internal : ∃ g ∈ C.gates, g.op=.not ∧ 5 ≤ g.inputs.headD 0) (i : Fin 5) :
    (cleanPaths C.gates (List.ofFn (fun j : Fin 5 => decide (i=j)))).getD C.output false=true := by
  obtain ⟨g,mem,n,internalPin⟩ := internal
  obtain ⟨p,s,split⟩ := List.append_of_mem mem
  have count := (exactCounts C legal cap computes ⟨g,mem,n,internalPin⟩).2.1
  obtain ⟨np,ns⟩ := no_other_not C p s g split n count
  have hroots : (∀ v ∈ roots i, Asc v) ∧ ∀ v ∈ roots i, Covered v := by
    constructor <;> intro v hv <;> obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hv <;>
      simp [Asc,Covered,pre,post] <;> aesop
  have before := ao_both p (roots i) (fun a ha => (legal a (by simp [split,ha])).1) np hroots.1 hroots.2
  have atNot := cover_not (run p (roots i)) g n before.1
  have after := ao_cover s _ (fun a ha => (legal a (by simp [split,ha])).1) ns
    (append_inv Covered before.2 atNot)
  have full : ∀ v ∈ run C.gates (roots i), Covered v := by
    simpa only [split,run,List.foldl_append,List.foldl_cons] using after
  have covered := read_inv _ Covered full (fun _ h => h) C.output
  have lo := project_read Mark.low rfl (run C.gates (roots i)) C.output
  have hi := project_read Mark.high rfl (run C.gates (roots i)) C.output
  rw [project_run Mark.low rfl (fun _ _ => rfl)] at lo
  rw [project_run Mark.high rfl (fun _ _ => rfl)] at hi
  have loRoots : (roots i).map Mark.low = List.ofFn (pre i) := by simp [roots,List.map_ofFn]
  have hiRoots : (roots i).map Mark.high = List.ofFn (post i) := by simp [roots,List.map_ofFn]
  rw [loRoots] at lo
  rw [hiRoots] at hi
  change _ = C.eval (List.ofFn (pre i)) at lo
  change _ = C.eval (List.ofFn (post i)) at hi
  rw [computes,(sensitive i).1] at lo
  rw [computes,(sensitive i).2] at hi
  have hp : (read (run C.gates (roots i)) C.output).path=true := by
    cases e : (read (run C.gates (roots i)) C.output).path
    · exact Bool.noConfusion (lo.symm.trans (covered e hi))
    · rfl
  rw [project_read Mark.path rfl,path_run] at hp
  simpa [roots,List.map_ofFn] using hp

#print axioms bypass
end Five18096Bypass
