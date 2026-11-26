import LateModel
namespace FiveLateModel
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Ends Five18096Finite FiveRestricted FiveRoundThree FiveSAT

theorem late_rows_mode {C : Circuit} (h : Qualifies C) (pre mid : List Gate) (n q f : Gate)
    (sp : C.gates=pre++(mid++[n,q,f])) (op : n.op=.not) (inner : 5≤n.inputs.headD 0) :
    ∃(ss : List Step) (g a b : Select) (d : Bool), ss.length=mid.length ∧ d=mode f ∧
      ∀r : Row,rowPass pre ss g a b d r=true := by
  let p := pre++mid
  let w := execute pre fiveInputs
  have e : C.gates=p++[n,q,f] := by simpa [p,List.append_assoc] using sp
  obtain ⟨a,b,as,bs,bl,gs,_,output,_⟩:=late_shape h p n q f e op inner
  have sz:=size_exact h
  have plen : p.length=7 := by simp [e] at sz;omega
  have bounds := back_of_index 5 C.gates h.back
  rw [sp] at bounds
  have preBack := (back_split pre (mid++[n,q,f]) 5 bounds).2
  have mb := (back_split mid [n,q,f] _ preBack).1
  have lw : w.length=5+pre.length := by unfold w;rw [execute_len];rfl
  have all := (no_other_not C p [q,f] n e op (exactCounts C h.legal h.cap h.computes h.internal).2.1).1
  have valid (g) (hg : g∈mid) : GValid g := by
    have hm : g∈C.gates := by simp [sp,hg]
    have no := all g (by simp [p,hg])
    exact ⟨(h.legal g hm).1,no,(filters h).binary g hm no⟩
  have pl : p.length=pre.length+mid.length := List.length_append
  obtain ⟨ss,l,val⟩:=grow mid w valid (lw ▸ mb) (by omega)
  refine ⟨ss,enc (n.inputs.headD 0),enc a,enc b,mode f,l,rfl,?_⟩
  intro r
  have W : execute mid w=execute p fiveInputs := (execute_append pre mid fiveInputs).symm
  have length : (execute p fiveInputs).length=5+p.length := by rw [execute_len];rfl
  unfold rowPass
  change (finish (ss.foldl applyStep (w.map (bit r))) _ _ _ _ == _) = true
  rw [val r,W,finish,read_internal _ r inner (by omega) (by omega),
    read_own _ r (i:=a) (by omega) (by omega),read_internal _ r bl (by omega) (by omega),beq_iff_eq]
  conv_rhs => rw [output]
  unfold combine3 src
  rw [bit_prime,bit_prime,saved_bit_neg]
  cases mode f <;> rfl

#print axioms late_rows_mode
end FiveLateModel
