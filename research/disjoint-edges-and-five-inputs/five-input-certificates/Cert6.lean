import LateModel
import KernelReplay
namespace FiveFixed6
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity FiveInputLower Five18096Finite FiveSAT FiveLateModel
set_option maxRecDepth 150000
set_option maxHeartbeats 12000000
def pre : List Gate := [⟨.and,[1,2]⟩,⟨.or,[1,2]⟩,⟨.or,[0,4]⟩,⟨.and,[6,7]⟩,⟨.and,[3,8]⟩,⟨.or,[3,8]⟩]
def expr1 (u6 : Step) (g a b : Select) (d : Bool) : Bool :=
  let l6 := (if u6.left.b3 then (if u6.left.b2 then (if u6.left.b1 then (if u6.left.b0 then true else true) else (if u6.left.b0 then true else true)) else (if u6.left.b1 then (if u6.left.b0 then true else false) else (if u6.left.b0 then false else false))) else (if u6.left.b2 then (if u6.left.b1 then (if u6.left.b0 then true else false) else (if u6.left.b0 then false else false)) else (if u6.left.b1 then (if u6.left.b0 then false else false) else (if u6.left.b0 then false else true))))
  let r6 := (if u6.right.b3 then (if u6.right.b2 then (if u6.right.b1 then (if u6.right.b0 then true else true) else (if u6.right.b0 then true else true)) else (if u6.right.b1 then (if u6.right.b0 then true else false) else (if u6.right.b0 then false else false))) else (if u6.right.b2 then (if u6.right.b1 then (if u6.right.b0 then true else false) else (if u6.right.b0 then false else false)) else (if u6.right.b1 then (if u6.right.b0 then false else false) else (if u6.right.b0 then false else true))))
  let v6 := if u6.op then l6||r6 else l6&&r6
  let inv := !(if g.b3 then (if g.b2 then (if g.b1 then (if g.b0 then false else false) else (if g.b0 then false else false)) else (if g.b1 then (if g.b0 then v6 else false) else (if g.b0 then false else false))) else (if g.b2 then (if g.b1 then (if g.b0 then true else false) else (if g.b0 then false else false)) else (if g.b1 then (if g.b0 then false else false) else (if g.b0 then false else false))))
  let aa := (if a.b3 then (if a.b2 then (if a.b1 then (if a.b0 then true else true) else (if a.b0 then true else true)) else (if a.b1 then (if a.b0 then v6 else false) else (if a.b0 then false else false))) else (if a.b2 then (if a.b1 then (if a.b0 then true else false) else (if a.b0 then false else false)) else (if a.b1 then (if a.b0 then false else false) else (if a.b0 then false else true))))
  let bb := (if b.b3 then (if b.b2 then (if b.b1 then (if b.b0 then false else false) else (if b.b0 then false else false)) else (if b.b1 then (if b.b0 then v6 else false) else (if b.b0 then false else false))) else (if b.b2 then (if b.b1 then (if b.b0 then true else false) else (if b.b0 then false else false)) else (if b.b1 then (if b.b0 then false else false) else (if b.b0 then false else false))))
  (if d then (inv&&aa)||bb else (inv||aa)&&bb)==false
lemma row1 (u6 : Step) (g a b : Select) (d : Bool) : rowPass pre [u6] g a b d 1 = expr1 u6 g a b d := rfl
def expr9 (u6 : Step) (g a b : Select) (d : Bool) : Bool :=
  let l6 := (if u6.left.b3 then (if u6.left.b2 then (if u6.left.b1 then (if u6.left.b0 then true else true) else (if u6.left.b0 then true else true)) else (if u6.left.b1 then (if u6.left.b0 then true else true) else (if u6.left.b0 then false else false))) else (if u6.left.b2 then (if u6.left.b1 then (if u6.left.b0 then true else false) else (if u6.left.b0 then false else false)) else (if u6.left.b1 then (if u6.left.b0 then true else false) else (if u6.left.b0 then false else true))))
  let r6 := (if u6.right.b3 then (if u6.right.b2 then (if u6.right.b1 then (if u6.right.b0 then true else true) else (if u6.right.b0 then true else true)) else (if u6.right.b1 then (if u6.right.b0 then true else true) else (if u6.right.b0 then false else false))) else (if u6.right.b2 then (if u6.right.b1 then (if u6.right.b0 then true else false) else (if u6.right.b0 then false else false)) else (if u6.right.b1 then (if u6.right.b0 then true else false) else (if u6.right.b0 then false else true))))
  let v6 := if u6.op then l6||r6 else l6&&r6
  let inv := !(if g.b3 then (if g.b2 then (if g.b1 then (if g.b0 then false else false) else (if g.b0 then false else false)) else (if g.b1 then (if g.b0 then v6 else true) else (if g.b0 then false else false))) else (if g.b2 then (if g.b1 then (if g.b0 then true else false) else (if g.b0 then false else false)) else (if g.b1 then (if g.b0 then false else false) else (if g.b0 then false else false))))
  let aa := (if a.b3 then (if a.b2 then (if a.b1 then (if a.b0 then true else true) else (if a.b0 then true else true)) else (if a.b1 then (if a.b0 then v6 else true) else (if a.b0 then false else false))) else (if a.b2 then (if a.b1 then (if a.b0 then true else false) else (if a.b0 then false else false)) else (if a.b1 then (if a.b0 then true else false) else (if a.b0 then false else true))))
  let bb := (if b.b3 then (if b.b2 then (if b.b1 then (if b.b0 then false else false) else (if b.b0 then false else false)) else (if b.b1 then (if b.b0 then v6 else true) else (if b.b0 then false else false))) else (if b.b2 then (if b.b1 then (if b.b0 then true else false) else (if b.b0 then false else false)) else (if b.b1 then (if b.b0 then false else false) else (if b.b0 then false else false))))
  (if d then (inv&&aa)||bb else (inv||aa)&&bb)==true
lemma row9 (u6 : Step) (g a b : Select) (d : Bool) : rowPass pre [u6] g a b d 9 = expr9 u6 g a b d := rfl
def expr10 (u6 : Step) (g a b : Select) (d : Bool) : Bool :=
  let l6 := (if u6.left.b3 then (if u6.left.b2 then (if u6.left.b1 then (if u6.left.b0 then false else false) else (if u6.left.b0 then false else false)) else (if u6.left.b1 then (if u6.left.b0 then false else true) else (if u6.left.b0 then false else false))) else (if u6.left.b2 then (if u6.left.b1 then (if u6.left.b0 then false else true) else (if u6.left.b0 then false else false)) else (if u6.left.b1 then (if u6.left.b0 then true else false) else (if u6.left.b0 then true else false))))
  let r6 := (if u6.right.b3 then (if u6.right.b2 then (if u6.right.b1 then (if u6.right.b0 then false else false) else (if u6.right.b0 then false else false)) else (if u6.right.b1 then (if u6.right.b0 then false else true) else (if u6.right.b0 then false else false))) else (if u6.right.b2 then (if u6.right.b1 then (if u6.right.b0 then false else true) else (if u6.right.b0 then false else false)) else (if u6.right.b1 then (if u6.right.b0 then true else false) else (if u6.right.b0 then true else false))))
  let v6 := if u6.op then l6||r6 else l6&&r6
  let inv := !(if g.b3 then (if g.b2 then (if g.b1 then (if g.b0 then false else false) else (if g.b0 then false else false)) else (if g.b1 then (if g.b0 then v6 else true) else (if g.b0 then false else false))) else (if g.b2 then (if g.b1 then (if g.b0 then false else true) else (if g.b0 then false else false)) else (if g.b1 then (if g.b0 then false else false) else (if g.b0 then false else false))))
  let aa := (if a.b3 then (if a.b2 then (if a.b1 then (if a.b0 then false else false) else (if a.b0 then false else false)) else (if a.b1 then (if a.b0 then v6 else true) else (if a.b0 then false else false))) else (if a.b2 then (if a.b1 then (if a.b0 then false else true) else (if a.b0 then false else false)) else (if a.b1 then (if a.b0 then true else false) else (if a.b0 then true else false))))
  let bb := (if b.b3 then (if b.b2 then (if b.b1 then (if b.b0 then false else false) else (if b.b0 then false else false)) else (if b.b1 then (if b.b0 then v6 else true) else (if b.b0 then false else false))) else (if b.b2 then (if b.b1 then (if b.b0 then false else true) else (if b.b0 then false else false)) else (if b.b1 then (if b.b0 then false else false) else (if b.b0 then false else false))))
  (if d then (inv&&aa)||bb else (inv||aa)&&bb)==false
lemma row10 (u6 : Step) (g a b : Select) (d : Bool) : rowPass pre [u6] g a b d 10 = expr10 u6 g a b d := rfl
def expr14 (u6 : Step) (g a b : Select) (d : Bool) : Bool :=
  let l6 := (if u6.left.b3 then (if u6.left.b2 then (if u6.left.b1 then (if u6.left.b0 then false else false) else (if u6.left.b0 then false else false)) else (if u6.left.b1 then (if u6.left.b0 then false else true) else (if u6.left.b0 then false else false))) else (if u6.left.b2 then (if u6.left.b1 then (if u6.left.b0 then false else true) else (if u6.left.b0 then true else false)) else (if u6.left.b1 then (if u6.left.b0 then true else true) else (if u6.left.b0 then true else false))))
  let r6 := (if u6.right.b3 then (if u6.right.b2 then (if u6.right.b1 then (if u6.right.b0 then false else false) else (if u6.right.b0 then false else false)) else (if u6.right.b1 then (if u6.right.b0 then false else true) else (if u6.right.b0 then false else false))) else (if u6.right.b2 then (if u6.right.b1 then (if u6.right.b0 then false else true) else (if u6.right.b0 then true else false)) else (if u6.right.b1 then (if u6.right.b0 then true else true) else (if u6.right.b0 then true else false))))
  let v6 := if u6.op then l6||r6 else l6&&r6
  let inv := !(if g.b3 then (if g.b2 then (if g.b1 then (if g.b0 then true else true) else (if g.b0 then true else true)) else (if g.b1 then (if g.b0 then v6 else true) else (if g.b0 then false else false))) else (if g.b2 then (if g.b1 then (if g.b0 then false else true) else (if g.b0 then true else true)) else (if g.b1 then (if g.b0 then true else true) else (if g.b0 then true else true))))
  let aa := (if a.b3 then (if a.b2 then (if a.b1 then (if a.b0 then false else false) else (if a.b0 then false else false)) else (if a.b1 then (if a.b0 then v6 else true) else (if a.b0 then false else false))) else (if a.b2 then (if a.b1 then (if a.b0 then false else true) else (if a.b0 then true else false)) else (if a.b1 then (if a.b0 then true else true) else (if a.b0 then true else false))))
  let bb := (if b.b3 then (if b.b2 then (if b.b1 then (if b.b0 then true else true) else (if b.b0 then true else true)) else (if b.b1 then (if b.b0 then v6 else true) else (if b.b0 then false else false))) else (if b.b2 then (if b.b1 then (if b.b0 then false else true) else (if b.b0 then true else true)) else (if b.b1 then (if b.b0 then true else true) else (if b.b0 then true else true))))
  (if d then (inv&&aa)||bb else (inv||aa)&&bb)==true
lemma row14 (u6 : Step) (g a b : Select) (d : Bool) : rowPass pre [u6] g a b d 14 = expr14 u6 g a b d := rfl
def expr24 (u6 : Step) (g a b : Select) (d : Bool) : Bool :=
  let l6 := (if u6.left.b3 then (if u6.left.b2 then (if u6.left.b1 then (if u6.left.b0 then false else false) else (if u6.left.b0 then false else false)) else (if u6.left.b1 then (if u6.left.b0 then false else true) else (if u6.left.b0 then false else false))) else (if u6.left.b2 then (if u6.left.b1 then (if u6.left.b0 then true else false) else (if u6.left.b0 then false else true)) else (if u6.left.b1 then (if u6.left.b0 then true else false) else (if u6.left.b0 then false else false))))
  let r6 := (if u6.right.b3 then (if u6.right.b2 then (if u6.right.b1 then (if u6.right.b0 then false else false) else (if u6.right.b0 then false else false)) else (if u6.right.b1 then (if u6.right.b0 then false else true) else (if u6.right.b0 then false else false))) else (if u6.right.b2 then (if u6.right.b1 then (if u6.right.b0 then true else false) else (if u6.right.b0 then false else true)) else (if u6.right.b1 then (if u6.right.b0 then true else false) else (if u6.right.b0 then false else false))))
  let v6 := if u6.op then l6||r6 else l6&&r6
  let inv := !(if g.b3 then (if g.b2 then (if g.b1 then (if g.b0 then false else false) else (if g.b0 then false else false)) else (if g.b1 then (if g.b0 then v6 else true) else (if g.b0 then false else false))) else (if g.b2 then (if g.b1 then (if g.b0 then true else false) else (if g.b0 then false else false)) else (if g.b1 then (if g.b0 then false else false) else (if g.b0 then false else false))))
  let aa := (if a.b3 then (if a.b2 then (if a.b1 then (if a.b0 then false else false) else (if a.b0 then false else false)) else (if a.b1 then (if a.b0 then v6 else true) else (if a.b0 then false else false))) else (if a.b2 then (if a.b1 then (if a.b0 then true else false) else (if a.b0 then false else true)) else (if a.b1 then (if a.b0 then true else false) else (if a.b0 then false else false))))
  let bb := (if b.b3 then (if b.b2 then (if b.b1 then (if b.b0 then false else false) else (if b.b0 then false else false)) else (if b.b1 then (if b.b0 then v6 else true) else (if b.b0 then false else false))) else (if b.b2 then (if b.b1 then (if b.b0 then true else false) else (if b.b0 then false else false)) else (if b.b1 then (if b.b0 then false else false) else (if b.b0 then false else false))))
  (if d then (inv&&aa)||bb else (inv||aa)&&bb)==false
lemma row24 (u6 : Step) (g a b : Select) (d : Bool) : rowPass pre [u6] g a b d 24 = expr24 u6 g a b d := rfl
def expr26 (u6 : Step) (g a b : Select) (d : Bool) : Bool :=
  let l6 := (if u6.left.b3 then (if u6.left.b2 then (if u6.left.b1 then (if u6.left.b0 then false else false) else (if u6.left.b0 then false else false)) else (if u6.left.b1 then (if u6.left.b0 then false else true) else (if u6.left.b0 then true else true))) else (if u6.left.b2 then (if u6.left.b1 then (if u6.left.b0 then true else true) else (if u6.left.b0 then false else true)) else (if u6.left.b1 then (if u6.left.b0 then true else false) else (if u6.left.b0 then true else false))))
  let r6 := (if u6.right.b3 then (if u6.right.b2 then (if u6.right.b1 then (if u6.right.b0 then false else false) else (if u6.right.b0 then false else false)) else (if u6.right.b1 then (if u6.right.b0 then false else true) else (if u6.right.b0 then true else true))) else (if u6.right.b2 then (if u6.right.b1 then (if u6.right.b0 then true else true) else (if u6.right.b0 then false else true)) else (if u6.right.b1 then (if u6.right.b0 then true else false) else (if u6.right.b0 then true else false))))
  let v6 := if u6.op then l6||r6 else l6&&r6
  let inv := !(if g.b3 then (if g.b2 then (if g.b1 then (if g.b0 then false else false) else (if g.b0 then false else false)) else (if g.b1 then (if g.b0 then v6 else true) else (if g.b0 then true else true))) else (if g.b2 then (if g.b1 then (if g.b0 then true else true) else (if g.b0 then false else false)) else (if g.b1 then (if g.b0 then false else false) else (if g.b0 then false else false))))
  let aa := (if a.b3 then (if a.b2 then (if a.b1 then (if a.b0 then false else false) else (if a.b0 then false else false)) else (if a.b1 then (if a.b0 then v6 else true) else (if a.b0 then true else true))) else (if a.b2 then (if a.b1 then (if a.b0 then true else true) else (if a.b0 then false else true)) else (if a.b1 then (if a.b0 then true else false) else (if a.b0 then true else false))))
  let bb := (if b.b3 then (if b.b2 then (if b.b1 then (if b.b0 then false else false) else (if b.b0 then false else false)) else (if b.b1 then (if b.b0 then v6 else true) else (if b.b0 then true else true))) else (if b.b2 then (if b.b1 then (if b.b0 then true else true) else (if b.b0 then false else false)) else (if b.b1 then (if b.b0 then false else false) else (if b.b0 then false else false))))
  (if d then (inv&&aa)||bb else (inv||aa)&&bb)==true
lemma row26 (u6 : Step) (g a b : Select) (d : Bool) : rowPass pre [u6] g a b d 26 = expr26 u6 g a b d := rfl
def check (u6 : Step) (g a b : Select) (d : Bool) : Bool := (((expr1 u6 g a b d) && ((expr9 u6 g a b d) && (expr10 u6 g a b d))) && ((expr14 u6 g a b d) && ((expr24 u6 g a b d) && (expr26 u6 g a b d))))
theorem no_rows (u6 : Step) (g a b : Select) (d : Bool) : check u6 g a b d=false := by
  simp only [check,expr1,expr9,expr10,expr14,expr24,expr26,ite_self,Bool.not_true,Bool.not_false,Bool.and_false,Bool.false_and,Bool.or_false,Bool.false_or,Bool.and_true,Bool.true_and,Bool.or_true,Bool.true_or]
  kernel_bool_sat
theorem exclusion {C : Circuit} (h : Qualifies C) (mid : List Gate) (n q f : Gate)
    (shape : C.gates=pre++(mid++[n,q,f])) (op : n.op=.not) (hi : 5≤n.inputs.headD 0) : False := by
  obtain ⟨ss,g,a,b,d,len,hit⟩ := late_rows h pre mid n q f shape op hi
  have total := size_exact h
  have pl : pre.length=6 := rfl
  rw [shape,List.length_append,List.length_append,pl] at total
  have how : ss.length=1 := by simp only [List.length_cons,List.length_nil] at total;omega
  cases h6 : ss with
  | nil => simp [h6] at how
  | cons u6 rest6 =>
    have empty : rest6=[] := List.length_eq_zero_iff.mp (by simpa [h6] using how)
    have vals (r) : rowPass pre [u6] g a b d r=true := by simpa only [h6,empty] using hit r
    have ok1 : expr1 u6 g a b d=true := by rw [←row1];exact vals 1
    have ok9 : expr9 u6 g a b d=true := by rw [←row9];exact vals 9
    have ok10 : expr10 u6 g a b d=true := by rw [←row10];exact vals 10
    have ok14 : expr14 u6 g a b d=true := by rw [←row14];exact vals 14
    have ok24 : expr24 u6 g a b d=true := by rw [←row24];exact vals 24
    have ok26 : expr26 u6 g a b d=true := by rw [←row26];exact vals 26
    have yes : check u6 g a b d=true := by simp [check,ok1,ok9,ok10,ok14,ok24,ok26]
    exact Bool.noConfusion (yes.symm.trans (no_rows u6 g a b d))
#print axioms exclusion
end FiveFixed6
