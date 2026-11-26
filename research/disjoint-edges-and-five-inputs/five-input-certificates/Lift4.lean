import Cert4
namespace FiveFixed4
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108 FiveInputLower Five18096Finite FiveSAT FiveLateModel
def rows : List PEqualNP.Outside.L_meta_12108.Row := [3,6,10,14,18,22,26]
/-- Only the committed wire values on the listed input rows matter. The
physical prefix may have different gate syntax or different values on other rows. -/
theorem exclusion_signature {C : Circuit} (h : Qualifies C) (initial mid : List Gate) (n q f : Gate)
    (pl : initial.length=4) (shape : C.gates=initial++(mid++[n,q,f]))
    (op : n.op=.not) (hi : 5≤n.inputs.headD 0)
    (same : ∀r∈rows, (execute initial fiveInputs).map (bit r)=(execute pre fiveInputs).map (bit r)) : False := by
  obtain ⟨ss,g,a,b,d,len,hit⟩ := late_rows h initial mid n q f shape op hi
  have total:=size_exact h
  rw [shape,List.length_append,List.length_append,pl] at total
  have how : ss.length=3 := by simp only [List.length_cons,List.length_nil] at total;omega
  cases h4 : ss with
  | nil => simp [h4] at how
  | cons u4 rest4 =>
    cases h5 : rest4 with
    | nil => simp [h4,h5] at how
    | cons u5 rest5 =>
      cases h6 : rest5 with
      | nil => simp [h4,h5,h6] at how
      | cons u6 rest6 =>
        have empty : rest6=[] := List.length_eq_zero_iff.mp (by simpa [h4,h5,h6] using how)
        have vals (r : Row) (hr : r∈rows) : rowPass pre [u4,u5,u6] g a b d r=true := by
          have base := hit r
          unfold rowPass at base ⊢
          rw [same r hr] at base
          simpa only [h4,h5,h6,empty] using base
        have ok3 : expr3 u4 u5 u6 g a b d=true := by rw [←row3];exact vals 3 (by decide)
        have ok6 : expr6 u4 u5 u6 g a b d=true := by rw [←row6];exact vals 6 (by decide)
        have ok10 : expr10 u4 u5 u6 g a b d=true := by rw [←row10];exact vals 10 (by decide)
        have ok14 : expr14 u4 u5 u6 g a b d=true := by rw [←row14];exact vals 14 (by decide)
        have ok18 : expr18 u4 u5 u6 g a b d=true := by rw [←row18];exact vals 18 (by decide)
        have ok22 : expr22 u4 u5 u6 g a b d=true := by rw [←row22];exact vals 22 (by decide)
        have ok26 : expr26 u4 u5 u6 g a b d=true := by rw [←row26];exact vals 26 (by decide)
        have yes : check u4 u5 u6 g a b d=true := by simp [check,ok3,ok6,ok10,ok14,ok18,ok22,ok26]
        exact Bool.noConfusion (yes.symm.trans (no_rows u4 u5 u6 g a b d))
#print axioms exclusion_signature
end FiveFixed4
