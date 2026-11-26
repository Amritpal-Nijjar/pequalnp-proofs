import SATModel
namespace FiveSAT
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Ends Five18096Finite FiveRestricted

def gatesAt (C : Circuit) (j : Fin 10) := C.gates.getD j.val ⟨.or,[]⟩
def values (C : Circuit) : WireBits := fun j r => bit (row r) ((execute C.gates fiveInputs).getD (5+j.val) zero)
def lhs (C : Circuit) (j : Fin 10) := enc ((gatesAt C j).inputs.getD 0 0)
def rhs (C : Circuit) (j : Fin 10) := enc ((gatesAt C j).inputs.getD 1 0)
def isOr (g : Gate) := match g.op with | .or => true | _ => false

lemma input_bit {C : Circuit} (i : Fin 16) (sm : i.val<15) (r : Rows) :
    wire (values C) r i=bit (row r) ((execute C.gates fiveInputs).getD i.val zero) := by
  by_cases raw : i.val<5
  · obtain ⟨extra,e⟩ := execute_extends C.gates fiveInputs
    rw [wire,if_pos raw,e,stable_read extra (show i.val<fiveInputs.length from raw)]
  · have k : i.val-5<10 := by omega
    simp only [wire,if_neg raw,dif_pos k,values]
    rw [show 5+(i.val-5)=i.val by omega]

lemma split_gate {C : Circuit} (h : Qualifies C) (j : Fin 10) :
    ∃ p s : List Gate, C.gates=p++gatesAt C j::s ∧ p.length=j.val := by
  have size := size_exact h
  have bound : j.val<C.gates.length := by have := j.isLt;omega
  let p := C.gates.take j.val
  let s := C.gates.drop (j.val+1)
  refine ⟨p,s,?_,List.length_take_of_le (by omega)⟩
  have take : gatesAt C j=C.gates[j.val] :=by simp [gatesAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem bound]
  rw [take]
  change _=C.gates.take j.val++C.gates[j.val]::C.gates.drop (j.val+1)
  rw [←List.drop_eq_getElem_cons bound,List.take_append_drop]

lemma computed (C : Circuit) (j : Fin 10) (p s : List Gate)
    (sp : C.gates=p++gatesAt C j::s) (len : p.length=j.val) (r : Rows) :
    values C j r=bit (row r) (gv (execute p fiveInputs) (gatesAt C j)) := by
  let w := execute p fiveInputs
  have len' : w.length=5+j.val := by unfold w;rw [execute_len,len];rfl
  unfold values
  conv_lhs => arg 2; arg 1; rw [sp,execute_append]
  change bit _ ((execute s (w++[gv w (gatesAt C j)])).getD (5+j.val) zero)=_
  rw [←len',kept_wire]

lemma selected (C : Circuit) (j : Fin 10) (p s : List Gate)
    (sp : C.gates=p++gatesAt C j::s) (len : p.length=j.val) (r : Rows) (pin : ℕ) (hp : pin<5+j.val) :
    mux (enc pin) (wire (values C) r)=bit (row r) ((execute p fiveInputs).getD pin zero) := by
  have b16 : pin<16 := by have := j.isLt;omega
  have b15 : pin<15 := by have := j.isLt;omega
  rw [mux_enc ⟨pin,b16⟩,input_bit _ b15]
  obtain ⟨t,extendsEq⟩ := execute_extends (gatesAt C j::s) (execute p fiveInputs)
  have small : pin<(execute p fiveInputs).length := by rw [execute_len,len];exact hp
  conv_lhs => arg 2; arg 1; rw [sp,execute_append,extendsEq]
  rw [stable_read t small]

lemma bound_enc (i limit : ℕ) (hi : i<16) : lowerOK (enc i) limit=decide (i<limit) := mux_enc ⟨i,hi⟩ _

lemma pair_value (w : List Sig) (g : Gate) (a b : ℕ) (pins : g.inputs=[a,b])
    (ao : g.op=.and ∨ g.op=.or) :
    gv w g=prime (isOr g) (w.getD a zero) (w.getD b zero) := by
  obtain ⟨o,l⟩:=g
  change l=[a,b] at pins
  subst l
  rcases ao with e|e <;> change o=_ at e <;> subst o
  · exact value_two w false a b
  · exact value_two w true a b

lemma gate_clause {C : Circuit} (h : Qualifies C) (k j : Fin 10)
    (which : isNot (gatesAt C j)=decide (j=k))
    (int : j=k → 5≤(gatesAt C j).inputs.headD 0) :
    okayPin k j (lhs C) (rhs C)=true ∧ ∀r,checkRow (values C) (lhs C) (rhs C) (fun n=>isOr (gatesAt C n)) k j r=true := by
  obtain ⟨p,s,sp,len⟩ := split_gate h j
  let g := gatesAt C j
  have sz := size_exact h
  have mem : g∈C.gates := by rw [sp];simp [g]
  have early (a : ℕ) (ha : a∈g.inputs) : a<5+j.val := h.back j.val (by have := j.isLt;omega) a ha
  have idx (a : ℕ) (ha : a∈g.inputs) : a<16 := by have := early a ha; have := j.isLt;omega
  have val (r : Rows) := computed C j p s sp len r
  have picked (r : Rows) (a : ℕ) (ha : a∈g.inputs) := selected C j p s sp len r a (early a ha)
  by_cases jk : j=k
  · have n : isNot g=true := by simpa [jk,g] using which
    have op : g.op=.not := by cases e:g.op <;> simp_all [isNot]
    have high := int jk
    change 5≤g.inputs.headD 0 at high
    cases ins : g.inputs with
    | nil => simp [ins] at high
    | cons a xs =>
      have m : a∈g.inputs := by simp [ins]
      have high' : 5≤a := by simpa [ins] using high
      have le : lhs C j=enc a := by change enc (g.inputs.getD 0 0)=_;rw [ins];rfl
      constructor
      · simp only [okayPin,if_pos jk,le,bound_enc _ _ (idx a m),decide_eq_true (early a m),decide_eq_false (show ¬a<5 by omega)]
        rfl
      · intro r
        have gvEq : gv (execute p fiveInputs) g=neg ((execute p fiveInputs).getD a zero) := by simp [gv,op,ins]
        have v := val r
        change values C j r=bit (row r) (gv (execute p fiveInputs) g) at v
        simp only [checkRow,if_pos jk,le,picked r a m,beq_iff_eq]
        exact v.trans (by rw [gvEq,saved_bit_neg])
  · have n : isNot g=false := by simpa [g,jk] using which
    obtain ⟨a,b,pins,ne⟩ := (filters h).binary g mem n
    have ma : a∈g.inputs := by simp [pins]
    have mb : b∈g.inputs := by simp [pins]
    have le : lhs C j=enc a := by change enc (g.inputs.getD 0 0)=_;rw [pins];rfl
    have ri : rhs C j=enc b := by change enc (g.inputs.getD 1 0)=_;rw [pins];rfl
    constructor
    · have different : (⟨a,idx a ma⟩ : Fin 16) ≠ ⟨b,idx b mb⟩ := by intro hi;exact ne (congrArg Fin.val hi)
      simp only [okayPin,if_neg jk,le,ri,bound_enc _ _ (idx a ma),bound_enc _ _ (idx b mb),
        same_enc ⟨a,idx a ma⟩ ⟨b,idx b mb⟩,decide_eq_true (early a ma),decide_eq_true (early b mb),decide_eq_false different]
      rfl
    · intro r
      have v := val r
      change values C j r=bit (row r) (gv (execute p fiveInputs) g) at v
      simp only [checkRow,if_neg jk,le,ri,picked r a ma,picked r b mb,beq_iff_eq]
      have ao := Five18096Bypass.legal_ao g (h.legal g mem).1 n
      rwa [pair_value _ g a b pins ao,bit_prime] at v

end FiveSAT
