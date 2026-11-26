import Counts

/-!
This proof refines the signed lower bound reused by pjscruggs. The original
signed-program extraction is from PEqualNP.Outside.L_meta_12108 (credited
in Counts.lean). Here a physical AND/OR is charged only when its signed
truth table is a new, nonconstant wire.
-/
namespace Five18096Fresh

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_12108 FiveInputLower

def Old (w : List Sig) (g : Gate) : Prop := Repr true (w.map (nrm true)) (gv w g)

noncomputable def fee (w : List Sig) (g : Gate) : ℕ := by
  classical
  exact if isNot g || decide (Old w g) then 0 else 1

noncomputable def cost : List Gate → List Sig → ℕ
  | [], _ => 0
  | g::gs, w => fee w g + cost gs (w ++ [gv w g])

def FreshRun : List Gate → List Sig → Prop
  | [], _ => True
  | g::gs, w => (isNot g = false → ¬Old w g) ∧ FreshRun gs (w ++ [gv w g])

lemma fee_le (w : List Sig) (g : Gate) :
    fee w g ≤ (if isNot g then 0 else 1) := by
  classical
  cases n : isNot g <;> by_cases h : Old w g <;> simp [fee,n,h]

lemma cost_le (gs : List Gate) (w : List Sig) :
    cost gs w ≤ gs.countP (fun g => !isNot g) := by
  induction gs generalizing w with
  | nil => exact Nat.le_refl 0
  | cons g gs ih =>
    have h := fee_le w g
    have t := ih (w ++ [gv w g])
    cases n : isNot g <;> simp [cost,List.countP_cons,n] at * <;> omega

lemma fresh_full (gs : List Gate) (w : List Sig)
    (h : gs.countP (fun g => !isNot g) ≤ cost gs w) : FreshRun gs w := by
  classical
  induction gs generalizing w with
  | nil => trivial
  | cons g gs ih =>
    have q := fee_le w g
    have t := cost_le gs (w ++ [gv w g])
    constructor
    · intro n old
      simp [List.countP_cons,cost,fee,n,old] at h
      omega
    · apply ih
      cases n : isNot g <;> simp [List.countP_cons,cost,n] at * <;> omega

lemma extractCost {target : Sig} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm true)) :
    ∃ k S, k ≤ cost gs w ∧ Live true target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm true) := by
  classical
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp [cost], Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,run,sub⟩ := ih (w ++ [gv w g]) (fun a ha => legal a (by simp [ha])) hout
    rw [List.map_append] at sub
    have rep := saved_gate_rep true w g (legal g (by simp)) (fun h => by cases h)
    have step : represented (w.map (nrm true)) (nrm true (gv w g)) ∨
        (fee w g = 1 ∧ witness true (w.map (nrm true)) (nrm true (gv w g))) := by
      by_cases h : Old w g
      · exact Or.inl h
      · obtain ⟨n,hg⟩ := rep.resolve_left h
        exact Or.inr ⟨by simp [fee,n,h],hg⟩
    obtain ⟨m,T,hm,rt,st⟩ := saved_pull_gate (u:=true) (target:=target) (w:=w.map (nrm true))
      (z:=nrm true (gv w g)) (k:=k) (S:=S) (c:=fee w g) run step sub
    exact ⟨m,T,by simp only [cost]; omega,rt,st⟩

theorem nine_productive (C : Circuit) (legal : FanInTwo C)
    (computes : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = tableFun 5 b x) :
    9 ≤ cost C.gates fiveInputs := by
  have base := baseOK_ok p13_B
  have good : proper fiveGraph := base.prop
  have eq : (execute C.gates fiveInputs).getD C.output zero = fiveGraph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (fiveEval C legal C.output r).trans ((computes (sample r)).trans (fiveTable r).symm)
  have out := saved_get_rep (u:=true) (execute C.gates fiveInputs) C.output
  rw [eq] at out
  unfold PEqualNP.Outside.L_meta_12108.Repr at out
  have pg : bit 0 fiveGraph = false := by
    change bit 0 (W p13_T) = false
    have h := base.plain
    unfold plainWord at h
    simpa using h
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extractCost C.gates fiveInputs legal good
    (out.resolve_right (fun h => h good))
  have ns : fiveInputs.all plainWord = true := base.plainR
  rw [nrm_map ns] at sub
  have full : S = fiveInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨r,s,hd,iso⟩ := base.ess a (List.mem_toFinset.mp ha)
      exact raw_required run fiveInputs a sub r s hd iso
  have steps := list_run (full ▸ run) fiveInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper good)
    steps (fiveInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := p13_L q bank built hit
  omega

theorem fresh_exact (C : Circuit) (legal : FanInTwo C) (cap : C.size ≤ 10)
    (computes : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = tableFun 5 b x)
    (internal : ∃ g ∈ C.gates, g.op = GateOp.not ∧ 5 ≤ g.inputs.headD 0) :
    FreshRun C.gates fiveInputs := by
  have counts := exactCounts C legal cap computes internal
  apply fresh_full
  rw [counts.2.2]
  exact nine_productive C legal computes

#print axioms fresh_exact
end Five18096Fresh
