import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

-- One hypothesis classifies the maximal negative inputs. The other is a
-- 26-instruction, two-register finite synthesis problem. Bits 0 through 20
-- are incidences, 21 through 57 are maximal negatives, and 58 and 59 are
-- the two marked singleton inputs.
set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8000 in
theorem PEqualNP.Outside.R_meta_4873_628
    (catalogue : let cols : List Nat := [288247147371954183,15270196031782968,58150373818816,94946423956573696,54820275478360064,3870282840506368,133412159488,759033086762549769,218716039641305168,189725234880873600,156548607028504576,229736628137050114,270286071509155872,288160007408582916]
let f := fun z : Fin 14 → Bool => ∃ p l : Fin 7, (p=l ∨ p=l+1 ∨ p=l+3) ∧
  z (Fin.castAdd 7 p)=true ∧ z (Fin.natAdd 7 l)=true
∀ z : Fin 14 → Bool, Maximal (fun y => ¬f y) z ↔
  ∃ i : Fin 37, z=fun v => (cols.getD v.val 0).testBit (21+i.val))
    (program : let initial : List Nat := [288247147371954183,15270196031782968,58150373818816,94946423956573696,54820275478360064,3870282840506368,133412159488,759033086762549769,218716039641305168,189725234880873600,156548607028504576,229736628137050114,270286071509155872,288160007408582916]
let step := fun (w : List Nat) (c : Fin 8192) =>
  let a := w.getD (c.val%64) 0
  let b := w.getD (c.val/64%64) 0
  w++[if c.val<4096 then a &&& b else a ||| b]
∃ s : List (Fin 8192), s.length≤26 ∧
  (∀ i : Fin s.length, let t := (s.get i).val; t%64<t/64%64 ∧ t/64%64<14+i.val) ∧
  ∃ u v : Fin (14+s.length), u≠v ∧
    let w := s.foldl step initial
    let a := w.getD u.val 0
    let b := w.getD v.val 0
    a &&& b = 2097151 ∧ a<288230376151711744 ∧ b<288230376151711744) : have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),   x3.size ≤ (27 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (14 : ℕ) x3 ∧       (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧         x3.output = (14 : ℕ) + x4 ∧           x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧             (∀ (x7 x8 : Fin (7 : ℕ)), x1 x7 x8 → x3.eval (List.ofFn fun (x10 : Fin (14 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (7 : ℕ) x7 ∨ x10 = Fin.natAdd (7 : ℕ) x8)) = Bool.true) ∧               (∀ (x7 : Fin (14 : ℕ) → Bool), Maximal (fun (x8 : Fin (14 : ℕ) → Bool) => ¬x2 x8) x7 → x3.eval (List.ofFn x7) = Bool.false) ∧                 ∀ x7 ∈ [(0 : Fin (14 : ℕ)), (7 : Fin (14 : ℕ))],                   have x9 : Fin (14 : ℕ) → Bool := fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = x7);                   PEqualNP.BlindGate.wireValue x3 (14 : ℕ) x9 x5 = Bool.false ∧ PEqualNP.BlindGate.wireValue x3 (14 : ℕ) x9 x6 = Bool.false := by
  let cols : List Nat := [288247147371954183,15270196031782968,58150373818816,94946423956573696,54820275478360064,3870282840506368,133412159488,759033086762549769,218716039641305168,189725234880873600,156548607028504576,229736628137050114,270286071509155872,288160007408582916]
  let input (r : Nat) (v : Fin 14) := (cols.getD v.val 0).testBit r
  let inc (p l : Fin 7) := p=l ∨ p=l+1 ∨ p=l+3
  let f := fun z : Fin 14 → Bool => ∃ p l : Fin 7, inc p l ∧
    z (Fin.castAdd 7 p)=true ∧ z (Fin.natAdd 7 l)=true
  let step := fun (w : List Nat) (c : Fin 8192) =>
    let a := w.getD (c.val%64) 0
    let b := w.getD (c.val/64%64) 0
    w++[if c.val<4096 then a &&& b else a ||| b]
  let decode := fun (c : Fin 8192) =>
    (⟨if c.val<4096 then .and else .or,[c.val%64,c.val/64%64]⟩ : Gate)
  let bit := fun (w : List Bool) (g : Gate) =>
    w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
  have evAnd : ∀ a b : Bool, GateOp.and.eval [a,b]=(a && b) := by decide
  have evOr : ∀ a b : Bool, GateOp.or.eval [a,b]=(a || b) := by decide
  have get (w : List Nat) (r i : Nat) :
      (w.map (fun v => v.testBit r)).getD i false=(w.getD i 0).testBit r := by
    by_cases hi : i<w.length
    · simp [List.getD_eq_getElem?_getD,hi]
    · simp [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_none (Nat.le_of_not_gt hi)]
  have run (s : List (Fin 8192)) (w : List Nat) (r : Nat) :
      (s.map decode).foldl bit (w.map fun v => v.testBit r) =
        (s.foldl step w).map (fun v => v.testBit r) := by
    induction s generalizing w with
    | nil => rfl
    | cons c s ih =>
      have h : bit (w.map fun v => v.testBit r) (decode c) =
          (step w c).map (fun v => v.testBit r) := by
        by_cases gate : c.val<4096 <;>
          simp only [bit,decode,step,gate,ite_true,ite_false,List.map_cons,List.map_nil,
            evAnd,evOr,List.map_append,Nat.testBit_and,Nat.testBit_or,get]
      simp only [List.map_cons,List.foldl_cons,h,ih]
  have length (s : List (Fin 8192)) (w : List Nat) :
      (s.foldl step w).length=w.length+s.length := by
    induction s generalizing w with
    | nil => simp
    | cons c s ih =>
      simp only [List.foldl_cons,List.length_cons]
      rw [ih]
      simp [step];omega
  obtain ⟨s,cap,pins,u,v,uv,regs⟩ := program
  let w := s.foldl step cols
  let x := w.getD u.val 0
  let y := w.getD v.val 0
  change x &&& y=2097151 ∧ x<288230376151711744 ∧ y<288230376151711744 at regs
  have clen : cols.length=14 := rfl
  have wlen : w.length=14+s.length := by rw [show w=s.foldl step cols from rfl,length,clen]
  let gs := s.map decode
  let last : Gate := ⟨.and,[u.val,v.val]⟩
  let C : Circuit := ⟨gs++[last],14+s.length⟩
  have glen : gs.length=s.length := by simp [gs]
  have diff : u.val≠v.val := fun h => uv (Fin.ext h)
  have finalGate : C.gates[s.length]?=some last := by simp [C,gs]
  have shape (k : Nat) (g : Gate) (atg : C.gates[k]?=some g) :
      (g.op=.and ∨ g.op=.or) ∧ ∃ a b, g.inputs=[a,b] ∧ a≠b ∧ a<14+k ∧ b<14+k := by
    by_cases hk : k<s.length
    · have e : C.gates[k]?=some (decode s[k]) := by
        change (gs++[last])[k]?=_
        rw [List.getElem?_append_left (glen ▸ hk)]
        simp [gs,hk]
      have eqg := Option.some.inj (atg.symm.trans e)
      subst g
      obtain ⟨ab,hi⟩ := pins ⟨k,hk⟩
      refine ⟨?_,s[k].val%64,s[k].val/64%64,rfl,ab.ne,ab.trans hi,hi⟩
      by_cases h : s[k].val<4096 <;> simp [decode,h]
    · have lk := (List.getElem?_eq_some_iff.1 atg).1
      have full : C.gates.length=s.length+1 := by simp [C,gs]
      have e : k=s.length := by omega
      subst k
      obtain rfl := Option.some.inj (atg.symm.trans finalGate)
      exact ⟨Or.inl rfl,u.val,v.val,rfl,diff,u.isLt,v.isLt⟩
  have ao : PEqualNP.TopForm.IsAO2 14 C := by
    refine ⟨?_,?_,?_⟩
    · intro g hg
      obtain ⟨k,hk⟩ := List.mem_iff_getElem?.1 hg
      exact (shape k g hk).1
    · intro k hk t ht
      obtain ⟨a,b,ins,_,ha,hb⟩ := (shape k C.gates[k] (List.getElem?_eq_getElem hk)).2
      change t∈(C.gates.getD k ⟨.or,[]⟩).inputs at ht
      have h : t∈C.gates[k].inputs := by rwa [List.getD_eq_getElem _ _ hk] at ht
      rw [ins] at h
      rcases List.mem_cons.1 h with rfl|h
      · exact ha
      · exact List.mem_singleton.1 h ▸ hb
    · intro g hg
      obtain ⟨k,hk⟩ := List.mem_iff_getElem?.1 hg
      obtain ⟨a,b,ins,_⟩ := (shape k g hk).2
      rw [ins];rfl
  have dis : ∀ g∈C.gates, g.inputs.Nodup := by
    intro g hg
    obtain ⟨k,hk⟩ := List.mem_iff_getElem?.1 hg
    obtain ⟨a,b,ins,ab,_⟩ := (shape k g hk).2
    simp [ins,ab]
  have ci : cols=List.ofFn (fun i : Fin 14 => cols.getD i.val 0) := by decide +kernel
  have initial (r : Nat) : cols.map (fun n => n.testBit r)=List.ofFn (input r) := by
    calc
      _ = (List.ofFn (fun i : Fin 14 => cols.getD i.val 0)).map (fun n => n.testBit r) :=
        congrArg (List.map (fun n : Nat => n.testBit r)) ci
      _ = _ := by simp [input]
  have allWires (r : Nat) : C.wires (List.ofFn (input r))=
      w.map (fun n => n.testBit r)++[x.testBit r && y.testBit r] := by
    have h := run s cols r
    rw [initial] at h
    change (gs++[last]).foldl bit (List.ofFn (input r))=_
    rw [List.foldl_append]
    change bit (gs.foldl bit (List.ofFn (input r))) last=_
    change gs.foldl bit (List.ofFn (input r))=w.map (fun n => n.testBit r) at h
    rw [h]
    simp only [bit,last,List.map_cons,List.map_nil,evAnd,get,x,y]
  have result (r : Nat) : C.eval (List.ofFn (input r))=(2097151 : Nat).testBit r := by
    unfold Circuit.eval
    rw [allWires,←regs.1,Nat.testBit_and]
    change ((w.map _++[_]).getD (14+s.length) false)=_
    have len : (w.map (fun n => n.testBit r)).length=14+s.length := by simpa using wlen
    rw [←len];simp [List.getD_eq_getElem?_getD]
  have pin (r i : Nat) (hi : i<14+s.length) :
      PEqualNP.BlindGate.wireValue C 14 (input r) i=(w.getD i 0).testBit r := by
    unfold PEqualNP.BlindGate.wireValue
    rw [allWires]
    have small : i<(w.map (fun n => n.testBit r)).length := by simpa [wlen] using hi
    change ((w.map _++[_]).getD i false)=_
    rw [List.getD_eq_getElem?_getD,List.getElem?_append_left small]
    exact get w r i
  have pos : ∀ p l : Fin 7, inc p l → ∃ r : Fin 21, ∀ z : Fin 14,
      input r.val z=decide (z=Fin.castAdd 7 p ∨ z=Fin.natAdd 7 l) := by decide +kernel
  have singleton : ∀ (k : Fin 2) (i : Fin 14), input (58+k.val) i=decide (i=if k=0 then 0 else 7) := by
    decide +kernel
  have ones : ∀ i : Fin 21, (2097151 : Nat).testBit i.val=true := by decide +kernel
  have zeros : ∀ i : Fin 37, (2097151 : Nat).testBit (21+i.val)=false := by decide +kernel
  refine ⟨C,s.length,u.val,v.val,?_,ao,dis,rfl,finalGate,?_,?_,?_⟩
  · change (gs++[last]).length≤27
    simp [glen];omega
  · intro p l pl
    obtain ⟨r,h⟩ := pos p l pl
    rw [←funext h,result];exact ones r
  · intro z neg
    obtain ⟨r,hr⟩ := (catalogue z).1 neg
    change z=input (21+r.val) at hr
    rw [hr,result];exact zeros r
  · intro z member
    obtain ⟨k,eq⟩ : ∃ k : Fin 2, z=(if k=0 then 0 else 7) := by
      rcases List.mem_cons.1 member with h|h
      · exact ⟨0,by simpa using h⟩
      · exact ⟨1,by simpa using List.mem_singleton.1 h⟩
    have row : input (58+k.val)=fun i : Fin 14 => decide (i=z) := by
      rw [eq];exact funext (singleton k)
    have bound : 288230376151711744≤2^(58+k.val) := by fin_cases k <;> decide +kernel
    change PEqualNP.BlindGate.wireValue C 14 _ u.val=false ∧ PEqualNP.BlindGate.wireValue C 14 _ v.val=false
    rw [←row,pin _ _ u.isLt,pin _ _ v.isLt]
    exact ⟨Nat.testBit_lt_two_pow (regs.2.1.trans_le bound),Nat.testBit_lt_two_pow (regs.2.2.trans_le bound)⟩
