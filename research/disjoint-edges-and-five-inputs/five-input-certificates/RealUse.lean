import FirstGate
namespace FiveRestricted
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Ends Five18096Bypass Five18096Finite

/-- Full effective liveness of an arbitrary ordinary gate. Deleting a gate
whose only apparent consumer uses it as a NOT's ignored second pin would
give a signed realization of cost at most eight. -/
theorem ordinary_use {C : Circuit} (h : Qualifies C) (p s : List Gate) (g : Gate)
    (sp : C.gates=p++g::s) (nn : isNot g=false) (notOut : C.output≠5+p.length) :
    ∃ q∈s, 5+p.length∈effective q := by
  by_contra! none
  let pos := 5+p.length
  let anchor := execute p fiveInputs
  let dummy : Gate := ⟨.or,[]⟩
  let fake : Circuit := ⟨p++dummy::s,C.output⟩
  have length : anchor.length=pos := by unfold anchor pos; rw [execute_len]; rfl
  have tailLegal (q) (hq : q∈s) := h.legal q (by simp [sp,hq])
  have legal : FanInTwo fake := by
    intro q hq
    change q∈p++dummy::s at hq
    rcases List.mem_append.mp hq with before|after
    · exact h.legal q (by simp [sp,before])
    · rcases List.mem_cons.mp after with rfl|hs
      · simp [dummy]
      · exact tailLegal q hs
  have eq : (execute fake.gates fiveInputs).getD fake.output zero=fiveGraph := by
    rw [←computed_sig C h.legal h.computes]
    apply bit_ext
    intro r
    let w := anchor.map (bit r)
    have sl : w.length=pos := by rw [show w=anchor.map (bit r) from rfl,List.length_map,length]
    have base := replace_last w (bit r (gv anchor dummy)) (bit r (gv anchor g))
    rw [sl] at base
    have final := (effective_off s pos _ _ base none).2 C.output notOut
    rw [←Five18096Paths.bits_at,←Five18096Paths.bits_at,sp]
    change ((execute (p++dummy::s) fiveInputs).map (bit r)).getD C.output false =
      ((execute (p++g::s) fiveInputs).map (bit r)).getD C.output false
    rw [execute_append,execute_append]
    change ((execute s (anchor++[gv anchor dummy])).map (bit r)).getD C.output false =
      ((execute s (anchor++[gv anchor g])).map (bit r)).getD C.output false
    rw [saved_execute_bits s r _ (fun a ha => (tailLegal a ha).1),saved_execute_bits s r _ (fun a ha => (tailLegal a ha).1)]
    simpa [phys,w] using final
  have base := baseOK_ok p13_B
  have lower := signed_cost_lower fake legal fiveInputs fiveInputs fiveGraph 9 p13_L base.prop
    (by simpa [fiveGraph,plainWord] using base.plain)
    (by have pr : fiveInputs.all plainWord=true := base.plainR; rw [nrm_map pr]; intro a ha; exact Or.inr ha) eq
  have total := (exactCounts C h.legal h.cap h.computes h.internal).2.2
  rw [sp,List.countP_append,List.countP_cons] at total
  simp only [nn,Bool.not_false,↓reduceIte] at total
  have zeroFee : collapsed anchor dummy=true := by
    apply (collapsed_iff _ _).2
    exact repr_const (Or.inl rfl)
  change 9 ≤ workCost (p++dummy::s) fiveInputs at lower
  rw [cost_append] at lower
  change 9 ≤ workCost p fiveInputs +
    ((if isNot dummy || collapsed anchor dummy then 0 else 1)+workCost s (anchor++[gv anchor dummy])) at lower
  rw [zeroFee] at lower
  simp only [Bool.or_true,↓reduceIte,Nat.zero_add] at lower
  have before := cost_max p fiveInputs
  have after := cost_max s (anchor++[gv anchor dummy])
  omega

theorem effective_use {C : Circuit} (h : Qualifies C) (p s : List Gate) (g : Gate)
    (sp : C.gates=p++g::s) (notOut : C.output≠5+p.length) :
    ∃ q∈s, 5+p.length∈effective q := by
  cases nn : isNot g with
  | false => exact ordinary_use h p s g sp nn notOut
  | true =>
    have op : g.op=.not := by obtain ⟨o,l⟩:=g; cases o <;> simp_all [isNot]
    have nots := (exactCounts C h.legal h.cap h.computes h.internal).2.1
    have rest := (no_other_not C p s g sp op nots).2
    have size : C.size=p.length+(s.length+1) := by simp [Circuit.size,sp]
    obtain endWire | ⟨i,hi,gt,pin⟩ := h.used p.length (by omega)
    · exact (notOut endWire).elim
    · have shape : C.gates=(p++[g])++s := by simpa [List.append_assoc] using sp
      have n : i-(p++[g]).length<s.length := by simp; omega
      have actual : C.gates.getD i ⟨.and,[]⟩ = s[i-(p++[g]).length] := by
        rw [shape,List.getD_eq_getElem?_getD,List.getElem?_append_right (show (p++[g]).length ≤ i by simp; omega),
          List.getElem?_eq_getElem n]; rfl
      rw [actual] at pin
      refine ⟨_,List.getElem_mem n,?_⟩
      rw [effective,rest _ (List.getElem_mem n)]
      exact pin

#print axioms ordinary_use
#print axioms effective_use
end FiveRestricted
