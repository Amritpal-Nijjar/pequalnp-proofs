import SATBridge
namespace FiveSAT
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Ends Five18096Finite FiveRestricted

def any10 (p : Fin 10→Bool) := (List.finRange 10).any p
def effectiveUse (k i j : Fin 10) (left right : Fin 10→Select) :=
  decide (i.val<j.val) && (sameSel (left j) (enc (5+i.val)) || (decide (j≠k) && sameSel (right j) (enc (5+i.val))))
def live (k : Fin 10) (left right : Fin 10→Select) : Bool :=
  all10 fun i => i==9 || any10 (fun j=>effectiveUse k i j left right)
def strictPass (k : Fin 10) (w : WireBits) (left right : Fin 10→Select) (op : Fin 10→Bool) :=
  passes k w left right op && live k left right

lemma unique_pos {C : Circuit} (h : Qualifies C) (p s : List Gate) (g : Gate)
    (sp : C.gates=p++g::s) (op : g.op=.not) (high : 5≤g.inputs.headD 0) :
    ∃ k : Fin 10, k.val=p.length ∧ 1≤k.val ∧ k.val≤7 ∧
    (∀j, isNot (gatesAt C j)=decide (j=k)) ∧ (5≤(gatesAt C k).inputs.headD 0) := by
  have pos := not_position C h.legal h.cap h.computes h.back h.used p s g sp op high
  let k : Fin 10 := ⟨p.length,by omega⟩
  have atK : gatesAt C k=g := by
    unfold gatesAt
    change C.gates.getD p.length ⟨.or,[]⟩=g
    rw [sp,List.getD_eq_getElem?_getD,List.getElem?_append_right (le_refl _)]
    simp
  refine ⟨k,rfl,pos.1,pos.2.1,?_,atK ▸ high⟩
  have others := no_other_not C p s g sp op (exactCounts C h.legal h.cap h.computes h.internal).2.1
  intro j
  by_cases equal : j=k
  · subst j; simp [atK,isNot,op]
  · simp only [decide_eq_false equal]
    have neq : j.val≠p.length := fun e=>equal (Fin.ext e)
    by_cases early : j.val<p.length
    · have eq : gatesAt C j=p[j.val] := by
        unfold gatesAt
        rw [sp,List.getD_eq_getElem?_getD,List.getElem?_append_left early,List.getElem?_eq_getElem early];rfl
      exact eq ▸ others.1 _ (List.getElem_mem early)
    · have len := size_exact h
      simp [sp] at len
      have sm : j.val-(p++[g]).length<s.length := by have := j.isLt; simp;omega
      have form : C.gates=(p++[g])++s := by simpa [List.append_assoc] using sp
      have eq : gatesAt C j=s[j.val-(p++[g]).length] := by
        unfold gatesAt
        rw [form,List.getD_eq_getElem?_getD,List.getElem?_append_right (show (p++[g]).length ≤ j.val by simp;omega),
          List.getElem?_eq_getElem sm];rfl
      exact eq ▸ others.2 _ (List.getElem_mem sm)

lemma live_of {C : Circuit} (h : Qualifies C) (k : Fin 10) (whereNot : ∀j, isNot (gatesAt C j)=decide (j=k)) :
    live k (lhs C) (rhs C)=true := by
  apply all10_of
  intro i
  by_cases last : i=9
  · simp [last]
  · have notOut : C.output≠5+i.val := by
      rw [final_output h]
      intro eq
      apply last
      apply Fin.ext
      change i.val=9
      omega
    have sz := size_exact h
    obtain ⟨j,hj,gt,hit⟩ := named_effective h i.val (by change i.val<C.gates.length;rw [sz];exact i.isLt) notOut
    let J : Fin 10 := ⟨j,by change j<C.gates.length at hj;omega⟩
    let G := gatesAt C J
    have same : C.gates.getD j ⟨.and,[]⟩=G := by
      change _=C.gates.getD j ⟨.or,[]⟩
      simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (show j<C.gates.length from hj)]
    rw [same] at hit
    have mem : G∈C.gates := by
      rw [←same,List.getD_eq_getElem _ _ (show j<C.gates.length from hj)]
      exact List.getElem_mem _
    apply Bool.or_eq_true_iff.mpr
    right
    apply List.any_eq_true.mpr
    refine ⟨J,List.mem_finRange J,Bool.and_eq_true_iff.mpr ⟨decide_eq_true gt,?_⟩⟩
    have sameSelf : sameSel (enc (5+i.val)) (enc (5+i.val))=true := by
      have small : 5+i.val<16 := by have := i.isLt;omega
      have e := same_enc (⟨5+i.val,small⟩ : Fin 16) ⟨5+i.val,small⟩
      simpa using e
    by_cases jk : J=k
    · have nn : isNot G=true := by simpa [G,jk] using whereNot J
      change 5+i.val∈(if isNot G then G.inputs.take 1 else G.inputs) at hit
      cases pins : G.inputs with
      | nil => simp [nn,pins] at hit
      | cons a tail =>
        have eq : 5+i.val=a := by simpa [nn,pins] using hit
        apply Bool.or_eq_true_iff.mpr; left
        change sameSel (enc (G.inputs.getD 0 0)) _=true
        simpa [pins,←eq] using sameSelf
    · have nn : isNot G=false := by simpa [G,jk] using whereNot J
      obtain ⟨a,b,pins,_⟩ := (filters h).binary G mem nn
      have ab : 5+i.val=a ∨ 5+i.val=b := by simpa [effective,nn,pins] using hit
      rcases ab with rfl|rfl
      · apply Bool.or_eq_true_iff.mpr;left
        change sameSel (enc (G.inputs.getD 0 0)) _=true
        simpa [pins] using sameSelf
      · apply Bool.or_eq_true_iff.mpr;right
        refine Bool.and_eq_true_iff.mpr ⟨decide_eq_true jk,?_⟩
        change sameSel (enc (G.inputs.getD 1 0)) _=true
        simpa [pins] using sameSelf

theorem extraction {C : Circuit} (h : Qualifies C) (p s : List Gate) (g : Gate)
    (sp : C.gates=p++g::s) (op : g.op=.not) (high : 5≤g.inputs.headD 0) :
    ∃ k : Fin 10, k.val=p.length ∧ 1≤k.val ∧ k.val≤7 ∧
      strictPass k (values C) (lhs C) (rhs C) (fun j => isOr (gatesAt C j))=true := by
  obtain ⟨k,atK,lo,hi,whereNot,khi⟩ := unique_pos h p s g sp op high
  refine ⟨k,atK,lo,hi,Bool.and_eq_true_iff.mpr ⟨?_,live_of h k whereNot⟩⟩
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply all10_of
    intro j
    obtain ⟨pins,rows⟩ := gate_clause h k j (whereNot j) (fun eq=>eq ▸ khi)
    exact Bool.and_eq_true_iff.mpr ⟨pins,all32_of _ rows⟩
  · apply all32_of
    intro r
    have value := computed_sig C h.legal h.computes
    rw [final_output h] at value
    change (bit (row r) ((execute C.gates fiveInputs).getD 14 zero)==bit (row r) fiveGraph)=true
    rw [value];simp

theorem sat_necessary (h : ∃ C, Qualifies C) :
    ∃ (k : Fin 10) (w : WireBits) (a b : Fin 10→Select) (op : Fin 10→Bool),
      1≤k.val ∧ k.val≤7 ∧ strictPass k w a b op=true := by
  obtain ⟨C,h⟩ := h
  obtain ⟨n,hn,nop,high⟩:=h.internal
  obtain ⟨p,s,sp⟩:=List.append_of_mem hn
  obtain ⟨k,_,lo,hi,pf⟩:=extraction h p s n sp nop high
  exact ⟨k,_,_,_,_,lo,hi,pf⟩

#print axioms sat_necessary
end FiveSAT
