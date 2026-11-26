import DirectCatalog
namespace FiveOne.DirectCatalog
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Finite Five18096Ends FiveSAT FiveRoundThree FiveRestricted

/-- The complete 32-row table of physical wire 8, whenever it supplies the outer operand. -/
theorem physical_wire_eight {C : Circuit} (h : Qualifies C) (x y z : Gate) (t : List Gate)
    (n q f : Gate) (p : List Gate) (earlier : p=pre++(x::y::z::t))
    (shape : C.gates=p++[n,q,f]) (op : n.op=.not) (inner : 5≤n.inputs.headD 0)
    (A : Sig) (output : fiveGraph=combine3 (mode f) (src p n) A ((execute p fiveInputs).getD 8 zero)) :
    (if mode f then goodOr else goodAnd).contains (low32 ((execute p fiveInputs).getD 8 zero))=true := by
  have bounds := back_of_index 5 C.gates h.back
  rw [shape,earlier] at bounds
  have back : Back 6 (x::y::z::t) := (back_split pre (x::y::z::t) 5
    (back_split (pre++(x::y::z::t)) [n,q,f] 5 bounds).1).2
  have all := (no_other_not C p [q,f] n shape op (exactCounts C h.legal h.cap h.computes h.internal).2.1).1
  have valid (w : Gate) (hw : w∈p) : GValid w := by
    have hm : w∈C.gates := by simp [shape,hw]
    have no:=all w hw
    exact ⟨(h.legal w hm).1,no,(filters h).binary w hm no⟩
  let u:=gv raw x
  let v:=gv (raw++[u]) y
  let last:=gv ((raw++[u])++[v]) z
  have hu : u∈words raw := candidate raw x (valid x (by simp [earlier])) back.1
  have hv : v∈words (raw++[u]) := candidate _ y (valid y (by simp [earlier])) (by simpa [raw] using back.2.1)
  have hz : last∈words ((raw++[u])++[v]) := candidate _ z (valid z (by simp [earlier])) (by simpa [raw] using back.2.2.1)
  have value : (execute p fiveInputs).getD 8 zero=last := by
    rw [earlier,execute_append,raw_exact]
    change (execute t (((raw++[u])++[v])++[last])).getD 8 zero=last
    have count : ((raw++[u])++[v]).length=8 := by simp [raw]
    rw [←count]; exact kept_wire t _ last
  have pass:=outer_boundary h p n q f shape op inner A _ output
  rw [value] at pass ⊢
  exact accepted u v last hu hv hz (mode f) pass

#print axioms physical_wire_eight
end FiveOne.DirectCatalog
