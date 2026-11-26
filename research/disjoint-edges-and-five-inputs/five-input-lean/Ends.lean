import Structural

namespace Five18096Ends

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_12108 FiveInputLower Five18096Fresh

lemma and_unit (a : Sig) : prime false a one = a := by
  apply bit_ext; intro i; simp [bit_prime, saved_bit_one]
lemma or_unit (a : Sig) : prime true a zero = a := by
  apply bit_ext; intro i; simp [bit_prime, saved_bit_zero]
lemma self_prime (d : Bool) (a : Sig) : prime d a a = a := by
  cases d <;> simp [prime]

lemma distinct_pins (w : List Sig) (g : Gate)
    (hleg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (nn : isNot g = false) (fresh : ¬ Old w g) :
    ∃ a b, g.inputs = [a,b] ∧ a ≠ b := by
  obtain ⟨op,l⟩ := g
  obtain ⟨ops,sz⟩ := hleg
  change l.length ≤ 2 at sz
  have op2 : op = .and ∨ op = .or := by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
    rcases ops with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · simp [isNot] at nn
  cases l with
  | nil =>
    exfalso; apply fresh
    rcases op2 with rfl | rfl
    · exact repr_const (Or.inr rfl)
    · exact repr_const (Or.inl rfl)
  | cons a l =>
    cases l with
    | nil =>
      exfalso; apply fresh
      have h := saved_get_rep (u:=true) w a
      rcases op2 with rfl | rfl <;> simpa only [Old,gv,List.map_cons,List.map_nil,
        List.foldr_cons,List.foldr_nil,and_unit,or_unit] using h
    | cons b l =>
      cases l with
      | cons _ _ => simp at sz
      | nil =>
        refine ⟨a,b,rfl,?_⟩
        intro eq; subst b; apply fresh
        have h := saved_get_rep (u:=true) w a
        rcases op2 with rfl | rfl <;> simpa only [Old,gv,List.map_cons,List.map_nil,
          List.foldr_cons,List.foldr_nil,and_unit,or_unit,self_prime] using h

def Back : ℕ → List Gate → Prop
  | _, [] => True
  | k, g::gs => (∀ i ∈ g.inputs, i < k) ∧ Back (k+1) gs

lemma back_of_index (k : ℕ) (gs : List Gate)
    (h : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨.or,[]⟩).inputs, i < k+j) :
    Back k gs := by
  induction gs generalizing k with
  | nil => trivial
  | cons g gs ih =>
    constructor
    · intro i hi; simpa using h 0 (by simp) i (by simpa using hi)
    · apply ih
      intro j hj i hi
      have z := h (j+1) (by simpa using hj) i (by simpa using hi)
      omega

def Rising (v : Sig) : Prop := bit 0 v = false ∧ bit 31 v = true
def Falling (v : Sig) : Prop := bit 0 v = true ∧ bit 31 v = false

lemma roots_rise : ∀ v ∈ fiveInputs, Rising v := by
  have rows : fiveInputs.all (fun v => !(bit 0 v) && bit 31 v) = true := by decide +kernel
  intro v hv
  simpa [Rising] using List.all_eq_true.mp rows v hv
lemma target_rises : Rising fiveGraph := by unfold Rising; decide +kernel

lemma read_mem (w : List Sig) (i : ℕ) (hi : i < w.length) : w.getD i zero ∈ w := by
  simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi] using List.getElem_mem hi

lemma value_two (w : List Sig) (d : Bool) (a b : ℕ) :
    gv w ⟨if d then .or else .and,[a,b]⟩ = prime d (w.getD a zero) (w.getD b zero) := by
  cases d <;> simp only [Bool.false_eq_true, ↓reduceIte,gv,List.map_cons,List.map_nil,
    List.foldr_cons,List.foldr_nil,and_unit,or_unit]

lemma execute_len (gs : List Gate) (w : List Sig) : (execute gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [execute]
  | cons g gs ih =>
    change (execute gs (w ++ [gv w g])).length = _
    simp [ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

lemma prefix_rises (pre : List Gate) (w : List Sig) (hw : ∀ v ∈ w, Rising v)
    (leg : ∀ g ∈ pre, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (nn : ∀ g ∈ pre, isNot g = false) (back : Back w.length pre) (fresh : FreshRun pre w) :
    ∀ v ∈ execute pre w, Rising v := by
  induction pre generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    have hg := leg g (by simp)
    have hn := nn g (by simp)
    obtain ⟨a,b,inputs,_⟩ := distinct_pins w g hg hn (fresh.1 hn)
    have ha := hw _ (read_mem w a (back.1 a (by simp [inputs])))
    have hb := hw _ (read_mem w b (back.1 b (by simp [inputs])))
    have z : Rising (gv w g) := by
      obtain ⟨op,l⟩ := g
      change l = [a,b] at inputs
      subst l
      have h := hg.1
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
      rcases h with rfl | rfl | rfl
      · rw [show gv w ⟨.and,[a,b]⟩ = _ from value_two w false a b]
        simp only [Rising,bit_prime,ha.1,ha.2,hb.1,hb.2]; decide
      · rw [show gv w ⟨.or,[a,b]⟩ = _ from value_two w true a b]
        simp only [Rising,bit_prime,ha.1,ha.2,hb.1,hb.2]; decide
      · simp [isNot] at hn
    apply ih (w ++ [gv w g])
    · intro v hv
      rcases List.mem_append.mp hv with h | h
      · exact hw v h
      · simpa [List.mem_singleton.mp h] using z
    · exact fun q hq => leg q (by simp [hq])
    · exact fun q hq => nn q (by simp [hq])
    · simpa using back.2
    · exact fresh.2

end Five18096Ends
