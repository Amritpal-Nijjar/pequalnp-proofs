import PhysicalCatalog
namespace FiveOne.DirectCatalog
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Finite Five18096Ends FiveSAT FiveRoundThree

/-- The selected physical output operand automatically carries its enumerated table restriction. -/
theorem wire_eight_witness {C : Circuit} (h : Qualifies C) (x y z : Gate) (t : List Gate)
    (n q f : Gate) (p : List Gate) (earlier : p=pre++(x::y::z::t))
    (shape : C.gates=p++[n,q,f]) (op : n.op=.not) (inner : 5≤n.inputs.headD 0) :
    ∃ a b : ℕ, a∈q.inputs ∧ b∈f.inputs ∧ (n.inputs.headD 0=11 ∨ a=11 ∨ b=11) ∧
      fiveGraph=combine3 (mode f) (src p n) ((execute p fiveInputs).getD a zero) ((execute p fiveInputs).getD b zero) ∧
      (b=8 → (if mode f then goodOr else goodAnd).contains (low32 ((execute p fiveInputs).getD b zero))=true) := by
  obtain ⟨a,b,live,pa,pb,_,_,_,_,_,_,_,output,_⟩ := live_internal_shape h p n q f shape op inner
  refine ⟨a,b,pa,pb,live,output,?_⟩
  intro selected
  subst b
  exact physical_wire_eight h x y z t n q f p earlier shape op inner _ output

#print axioms wire_eight_witness
end FiveOne.DirectCatalog
