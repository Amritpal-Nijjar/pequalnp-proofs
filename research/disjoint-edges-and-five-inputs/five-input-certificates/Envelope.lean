import PostedSeven
namespace FiveRoundThree
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Ends Five18096Finite Five18096Bypass Five18096Paths FiveRestricted

def fixed (c : Bool) : Sig := if c then one else zero
def constantGate (c : Bool) : Gate := ⟨if c then .and else .or,[]⟩
def forced (C : Circuit) (p s : List Gate) (c : Bool) : Sig :=
  (execute s (execute p fiveInputs++[fixed c])).getD C.output zero
def src (p : List Gate) (g : Gate) := (execute p fiveInputs).getD (g.inputs.headD 0) zero
def below (a b : Sig) : Prop := ∀ r : Row, bit r a=true → bit r b=true

lemma fixed_value (c : Bool) (w : List Sig) : gv w (constantGate c)=fixed c := by cases c <;> rfl
lemma fixed_bit (c : Bool) (r : Row) : bit r (fixed c)=c := by
  cases c <;> first | exact saved_bit_zero r | exact saved_bit_one r
lemma fixed_free (c : Bool) (w : List Sig) : collapsed w (constantGate c)=true := by
  apply (collapsed_iff _ _).2
  unfold Old
  rw [fixed_value]
  cases c <;> first | exact repr_const (Or.inl rfl) | exact repr_const (Or.inr rfl)
lemma inverter_value (p : List Gate) (g : Gate) (n : g.op=.not) (hi : 5≤g.inputs.headD 0) :
    gv (execute p fiveInputs) g = neg (src p g) := by
  obtain ⟨o,l⟩:=g
  change o=.not at n
  subst o
  cases l with
  | nil => simp at hi
  | cons a t => rfl

lemma suffix_ao {C : Circuit} (h : Qualifies C) (p s : List Gate) (g : Gate)
    (sp : C.gates=p++g::s) (n : g.op=.not) : ∀q∈s, q.op=.and ∨ q.op=.or := by
  have all := (no_other_not C p s g sp n (exactCounts C h.legal h.cap h.computes h.internal).2.1).2
  exact fun q hq => legal_ao q (h.legal q (by simp [sp,hq])).1 (all q hq)

lemma mono_run (s : List Gate) (a b : List Bool) (le : Sound true a b)
    (ao : ∀g∈s, g.op=.and ∨ g.op=.or) : Sound true (phys s a) (phys s b) := by
  induction s generalizing a b with
  | nil => exact le
  | cons g s ih =>
    apply ih _ _ _ (fun q hq=>ao q (by simp [hq]))
    exact snoc_sound true le _ _ (preserve _ _ _ _ (ao g (by simp)) (fun i _ => le.2 i))

lemma physical_bit {C : Circuit} (h : Qualifies C) (p s : List Gate) (g : Gate)
    (sp : C.gates=p++g::s) (r : Row) (v : Sig) :
    bit r ((execute s (execute p fiveInputs++[v])).getD C.output zero) =
      (phys s ((execute p fiveInputs).map (bit r)++[bit r v])).getD C.output false := by
  rw [← bits_at,saved_execute_bits s r _ (fun q hq => (h.legal q (by simp [sp,hq])).1)]
  simp [phys]

lemma original_bit {C : Circuit} (h : Qualifies C) (p s : List Gate) (g : Gate)
    (sp : C.gates=p++g::s) (n : g.op=.not) (hi : 5≤g.inputs.headD 0) (r : Row) :
    bit r fiveGraph = (phys s ((execute p fiveInputs).map (bit r)++[!(bit r (src p g))])).getD C.output false := by
  have eq := computed_sig C h.legal h.computes
  rw [sp,execute_append] at eq
  change (execute s (execute p fiveInputs++[gv (execute p fiveInputs) g])).getD C.output zero=_ at eq
  rw [←eq, physical_bit h p s g sp r _,inverter_value p g n hi,saved_bit_neg]

lemma forced_bit {C : Circuit} (h : Qualifies C) (p s : List Gate) (g : Gate)
    (sp : C.gates=p++g::s) (r : Row) (c : Bool) :
    bit r (forced C p s c) = (phys s ((execute p fiveInputs).map (bit r)++[c])).getD C.output false := by
  rw [forced,physical_bit h p s g sp r _,fixed_bit]

lemma sandwich {C : Circuit} (h : Qualifies C) (p s : List Gate) (g : Gate)
    (sp : C.gates=p++g::s) (n : g.op=.not) (hi : 5≤g.inputs.headD 0) :
    below (forced C p s false) fiveGraph ∧ below fiveGraph (forced C p s true) := by
  have ao := suffix_ao h p s g sp n
  have reflex (w : List Bool) : Sound true w w := ⟨rfl,fun _ h=>h⟩
  constructor
  · intro r
    rw [forced_bit h p s g sp,original_bit h p s g sp n hi]
    apply (mono_run s _ _ _ ao).2 C.output
    exact snoc_sound true (reflex _) false _ (by simp)
  · intro r
    rw [forced_bit h p s g sp,original_bit h p s g sp n hi]
    apply (mono_run s _ _ _ ao).2 C.output
    exact snoc_sound true (reflex _) _ true (by simp)

theorem forced_ne {C : Circuit} (h : Qualifies C) (p s : List Gate) (g : Gate)
    (sp : C.gates=p++g::s) (n : g.op=.not) (hi : 5≤g.inputs.headD 0) (c : Bool) : forced C p s c ≠ fiveGraph := by
  intro eq
  let fake : Circuit := ⟨p++constantGate c::s,C.output⟩
  let w := execute p fiveInputs
  let z := 5+p.length
  have sz := size_exact h
  have sizes : p.length+s.length=9 := by simp [sp] at sz; omega
  have pos := not_position C h.legal h.cap h.computes h.back h.used p s g sp n hi
  obtain ⟨use,useMem,pin⟩ := effective_use h p s g sp (by rw [final_output h]; omega)
  have nn := (no_other_not C p s g sp n (exactCounts C h.legal h.cap h.computes h.internal).2.1).2
  have usual : z∈use.inputs := pins_subset use pin
  have used : 0<degree z s := List.countP_pos_iff.mpr ⟨use,useMem,by simp [takes,nn use useMem,usual]⟩
  have leg : FanInTwo fake := by
    intro a ha
    change a∈p++constantGate c::s at ha
    rcases List.mem_append.mp ha with hp|hs
    · exact h.legal a (by simp [sp,hp])
    · rcases List.mem_cons.mp hs with rfl|hs
      · cases c <;> simp [constantGate]
      · exact h.legal a (by simp [sp,hs])
  have reaches : (execute fake.gates fiveInputs).getD fake.output zero=fiveGraph := by
    change (execute (p++constantGate c::s) fiveInputs).getD C.output zero=_
    rw [execute_append]
    change (execute s (w++[gv w (constantGate c)])).getD C.output zero=_
    rw [fixed_value]; exact eq
  have base := baseOK_ok p13_B
  have low := signed_cost_lower fake leg fiveInputs fiveInputs fiveGraph 9 p13_L base.prop
    (by simpa [fiveGraph,plainWord] using base.plain) (by
      have pr : fiveInputs.all plainWord=true := base.plainR
      rw [nrm_map pr]; intro x hx; exact Or.inr hx) reaches
  change 9≤workCost (p++constantGate c::s) fiveInputs at low
  rw [cost_append] at low
  change 9≤workCost p fiveInputs + ((if isNot (constantGate c) || collapsed w (constantGate c) then 0 else 1)+workCost s (w++[gv w (constantGate c)])) at low
  rw [fixed_free,fixed_value] at low
  simp only [Bool.or_true,↓reduceIte,Nat.zero_add] at low
  have len : w.length=z := by unfold w z; rw [execute_len]; rfl
  have atZ : (w++[fixed c]).getD z zero=fixed c := by
    rw [←len]; simp [List.getD_eq_getElem?_getD,List.getElem?_append_right]
  have de := degree_cost z s (w++[fixed c]) (fun a ha=>(h.legal a (by simp [sp,ha])).1)
    (fun a ha=> (filters h).binary a (by simp [sp,ha])) (by simp [len]) (by rw [atZ]; cases c <;> simp [fixed])
  have cp := cost_max p fiveInputs
  have capP := List.countP_le_length (p:=fun a=> !isNot a) (l:=p)
  have capS := List.countP_le_length (p:=fun a=> !isNot a) (l:=s)
  omega

#print axioms forced_ne
end FiveRoundThree
