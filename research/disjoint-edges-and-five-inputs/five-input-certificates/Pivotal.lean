import Envelope
namespace FiveRoundThree
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Ends Five18096Finite Five18096Bypass Five18096Paths FiveRestricted

/-- On two opposite-label rows the inverter must switch the final output in
both directions when overridden. This filters the exact wire the NOT reads. -/
theorem pivotal_rows {C : Circuit} (h : Qualifies C) (p s : List Gate) (g : Gate)
    (sp : C.gates=p++g::s) (op : g.op=.not) (hi : 5≤g.inputs.headD 0) :
    (∃ r : Row, bit r fiveGraph=true ∧ bit r (src p g)=false ∧ bit r (forced C p s false)=false) ∧
    (∃ r : Row, bit r fiveGraph=false ∧ bit r (src p g)=true ∧ bit r (forced C p s true)=true) := by
  have ⟨lower,upper⟩ := sandwich h p s g sp op hi
  have sep (c : Bool) : ∃ r : Row, bit r (forced C p s c) ≠ bit r fiveGraph := by
    by_contra! same
    exact forced_ne h p s g sp op hi c (bit_ext same)
  constructor
  · obtain ⟨r,diff⟩ := sep false
    have le := lower r
    have f : bit r fiveGraph=true ∧ bit r (forced C p s false)=false := by
      cases er : bit r fiveGraph <;> cases low : bit r (forced C p s false) <;> simp_all
    refine ⟨r,f.1,?_,f.2⟩
    cases source : bit r (src p g) with
    | false => rfl
    | true =>
      rw [original_bit h p s g sp op hi r,forced_bit h p s g sp r false,source] at diff
      exact (diff rfl).elim
  · obtain ⟨r,diff⟩ := sep true
    have le := upper r
    have f : bit r fiveGraph=false ∧ bit r (forced C p s true)=true := by
      cases er : bit r fiveGraph <;> cases high : bit r (forced C p s true) <;> simp_all
    refine ⟨r,f.1,?_,f.2⟩
    cases source : bit r (src p g) with
    | true => rfl
    | false =>
      rw [original_bit h p s g sp op hi r,forced_bit h p s g sp r true,source] at diff
      exact (diff rfl).elim

theorem incomparable {C : Circuit} (h : Qualifies C) (p s : List Gate) (g : Gate)
    (sp : C.gates=p++g::s) (op : g.op=.not) (hi : 5≤g.inputs.headD 0) :
    ¬below (src p g) fiveGraph ∧ ¬below fiveGraph (src p g) := by
  obtain ⟨⟨p',pg,pi,_⟩,⟨n,ng,ni,_⟩⟩ := pivotal_rows h p s g sp op hi
  exact ⟨fun low=>Bool.noConfusion (ng.symm.trans (low n ni)),fun up=>Bool.noConfusion (pi.symm.trans (up p' pg))⟩

def crosses (v : Sig) : Bool :=
  (List.finRange 128).any (fun r => bit r fiveGraph && !(bit r v)) &&
  (List.finRange 128).any (fun r => !(bit r fiveGraph) && bit r v)
theorem crosses_source {C : Circuit} (h : Qualifies C) (p s : List Gate) (g : Gate)
    (sp : C.gates=p++g::s) (op : g.op=.not) (hi : 5≤g.inputs.headD 0) : crosses (src p g)=true := by
  obtain ⟨⟨r,fg,ss,_⟩,⟨t,hg,st,_⟩⟩ := pivotal_rows h p s g sp op hi
  exact Bool.and_eq_true_iff.mpr ⟨List.any_eq_true.mpr ⟨r,List.mem_finRange r,by simp [fg,ss]⟩,
    List.any_eq_true.mpr ⟨t,List.mem_finRange t,by simp [hg,st]⟩⟩

def firstWord (k : FirstKey) : Sig :=
  prime k.1 (fiveInputs.getD k.2.1 zero) (fiveInputs.getD k.2.2 zero)
theorem immediate_options : representatives.filter (fun k => crosses (firstWord k)) =
    [(false,1,2),(false,1,4),(true,0,1),(true,1,2),(true,1,4),(true,0,4)] := by decide +kernel

#print axioms pivotal_rows
#print axioms immediate_options
end FiveRoundThree
