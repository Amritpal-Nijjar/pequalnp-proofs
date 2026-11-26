import Pin5And
import Pin5Or
import Pin6And
import Pin6Or
import Pin7And
import Pin7Or
import Pin8And
import Pin8Or
import Pin9And
import Pin9Or
import Pin10And
import Pin10Or
import Pin11Split
import Pin11Or
import Base3
namespace FiveFixed3
open FiveSAT FiveLateModel
set_option maxRecDepth 150000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
theorem no_rows (u3 u4 u5 u6 : Step) (g a b : Select) (d : Bool) :
    check u3 u4 u5 u6 g a b d=false := by
  obtain ⟨b0,b1,b2,b3⟩:=b
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases d
  · exact noPin5And u3 u4 u5 u6 g a
  · exact noPin5Or u3 u4 u5 u6 g a
  · exact noPin8And u3 u4 u5 u6 g a
  · exact noPin8Or u3 u4 u5 u6 g a
  · exact noPin5And u3 u4 u5 u6 g a
  · exact noPin5Or u3 u4 u5 u6 g a
  · exact noPin5And u3 u4 u5 u6 g a
  · exact noPin5Or u3 u4 u5 u6 g a
  · exact noPin5And u3 u4 u5 u6 g a
  · exact noPin5Or u3 u4 u5 u6 g a
  · exact noPin10And u3 u4 u5 u6 g a
  · exact noPin10Or u3 u4 u5 u6 g a
  · exact noPin6And u3 u4 u5 u6 g a
  · exact noPin6Or u3 u4 u5 u6 g a
  · exact noPin5And u3 u4 u5 u6 g a
  · exact noPin5Or u3 u4 u5 u6 g a
  · exact noPin5And u3 u4 u5 u6 g a
  · exact noPin5Or u3 u4 u5 u6 g a
  · exact noPin9And u3 u4 u5 u6 g a
  · exact noPin9Or u3 u4 u5 u6 g a
  · exact noPin5And u3 u4 u5 u6 g a
  · exact noPin5Or u3 u4 u5 u6 g a
  · exact noPin5And u3 u4 u5 u6 g a
  · exact noPin5Or u3 u4 u5 u6 g a
  · exact noPin5And u3 u4 u5 u6 g a
  · exact noPin5Or u3 u4 u5 u6 g a
  · exact noPin11And u3 u4 u5 u6 g a
  · exact noPin11Or u3 u4 u5 u6 g a
  · exact noPin7And u3 u4 u5 u6 g a
  · exact noPin7Or u3 u4 u5 u6 g a
  · exact noPin5And u3 u4 u5 u6 g a
  · exact noPin5Or u3 u4 u5 u6 g a
#print axioms no_rows
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity FiveInputLower Five18096Finite
theorem exclusion {C : Circuit} (h : Qualifies C) (mid : List Gate) (n q f : Gate)
    (shape : C.gates=pre++(mid++[n,q,f])) (op : n.op=.not) (hi : 5≤n.inputs.headD 0) : False := by
  obtain ⟨ss,g,a,b,d,len,hit⟩ := late_rows h pre mid n q f shape op hi
  have total := size_exact h
  have pl : pre.length=3 := rfl
  rw [shape,List.length_append,List.length_append,pl] at total
  have how : ss.length=4 := by simp only [List.length_cons,List.length_nil] at total;omega
  cases h3 : ss with
  | nil => simp [h3] at how
  | cons u3 rest3 =>
    cases h4 : rest3 with
    | nil => simp [h3,h4] at how
    | cons u4 rest4 =>
      cases h5 : rest4 with
      | nil => simp [h3,h4,h5] at how
      | cons u5 rest5 =>
        cases h6 : rest5 with
        | nil => simp [h3,h4,h5,h6] at how
        | cons u6 rest6 =>
          have empty : rest6=[] := List.length_eq_zero_iff.mp (by simpa [h3,h4,h5,h6] using how)
          have vals (r) : rowPass pre [u3,u4,u5,u6] g a b d r=true := by simpa only [h3,h4,h5,h6,empty] using hit r
          have ok1 : expr1 u3 u4 u5 u6 g a b d=true := by rw [←row1];exact vals 1
          have ok3 : expr3 u3 u4 u5 u6 g a b d=true := by rw [←row3];exact vals 3
          have ok6 : expr6 u3 u4 u5 u6 g a b d=true := by rw [←row6];exact vals 6
          have ok9 : expr9 u3 u4 u5 u6 g a b d=true := by rw [←row9];exact vals 9
          have ok10 : expr10 u3 u4 u5 u6 g a b d=true := by rw [←row10];exact vals 10
          have ok14 : expr14 u3 u4 u5 u6 g a b d=true := by rw [←row14];exact vals 14
          have ok18 : expr18 u3 u4 u5 u6 g a b d=true := by rw [←row18];exact vals 18
          have ok20 : expr20 u3 u4 u5 u6 g a b d=true := by rw [←row20];exact vals 20
          have ok22 : expr22 u3 u4 u5 u6 g a b d=true := by rw [←row22];exact vals 22
          have ok26 : expr26 u3 u4 u5 u6 g a b d=true := by rw [←row26];exact vals 26
          have yes : check u3 u4 u5 u6 g a b d=true := by simp [check,ok1,ok3,ok6,ok9,ok10,ok14,ok18,ok20,ok22,ok26]
          exact Bool.noConfusion (yes.symm.trans (no_rows u3 u4 u5 u6 g a b d))
#print axioms exclusion
end FiveFixed3
