import LateShape
import SATExtract
namespace FiveLateModel
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Ends Five18096Finite FiveRestricted FiveRoundThree FiveSAT

structure Step where
  left : Select
  right : Select
  op : Bool

def get (bits : List Bool) (s : Select) := mux s (fun i => bits.getD i.val (bits.getD 0 false))
def internalGet (bits : List Bool) (s : Select) := mux s (fun i =>
  if i.val<5 then bits.getD 5 false else bits.getD i.val (bits.getD 5 false))
def applyStep (bits : List Bool) (g : Step) :=
  let a:=get bits g.left
  let b:=get bits g.right
  bits++[if g.op then a||b else a&&b]
def finish (bits : List Bool) (g a b : Select) (d : Bool) :=
  let n:= !(internalGet bits g)
  let v:=get bits a
  let t:=internalGet bits b
  if d then (n&&v)||t else (n||v)&&t

lemma read_own (w : List Sig) (r : Row) {i : ℕ} (small : i<w.length) (cap : i<16) :
    get (w.map (bit r)) (enc i) = bit r (w.getD i zero) := by
  rw [get,mux_enc ⟨i,cap⟩]
  simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem small]
lemma read_internal (w : List Sig) (r : Row) {i : ℕ} (low : 5 ≤ i) (small : i<w.length) (cap : i<16) :
    internalGet (w.map (bit r)) (enc i)=bit r (w.getD i zero) := by
  rw [internalGet,mux_enc ⟨i,cap⟩]
  simp [show ¬i<5 by omega,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem small]

def rowPass (pre : List Gate) (steps : List Step) (g a b : Select) (d : Bool) (r : Row) :=
  finish (steps.foldl applyStep ((execute pre fiveInputs).map (bit r))) g a b d == bit r fiveGraph

lemma step_exists (w : List Sig) (g : Gate) (valid : GValid g)
    (back : ∀i∈g.inputs,i<w.length) (cap : w.length≤15) :
    ∃ t : Step, ∀r : Row, applyStep (w.map (bit r)) t=(w++[gv w g]).map (bit r) := by
  obtain ⟨a,b,pins,_⟩:=valid.2.2
  have ma := back a (by simp [pins])
  have mb := back b (by simp [pins])
  have ao := Five18096Bypass.legal_ao g valid.1 valid.2.1
  have val:=FiveSAT.pair_value w g a b pins ao
  refine ⟨⟨enc a,enc b,FiveSAT.isOr g⟩,?_⟩
  intro r
  simp [applyStep,read_own w r ma (by omega),read_own w r mb (by omega),val,bit_prime]

lemma grow (gs : List Gate) (w : List Sig) (valid : ∀g∈gs,GValid g) (back : Back w.length gs)
    (cap : w.length+gs.length≤15) :
    ∃ steps : List Step, steps.length=gs.length ∧ ∀r : Row,
      steps.foldl applyStep (w.map (bit r))=(execute gs w).map (bit r) := by
  induction gs generalizing w with
  | nil => exact ⟨[],rfl,fun _=>rfl⟩
  | cons g gs ih =>
    obtain ⟨t,teq⟩:=step_exists w g (valid g (by simp)) back.1 (by omega)
    obtain ⟨ts,l,e⟩:=ih (w++[gv w g]) (fun q hq=>valid q (by simp [hq])) (by simpa using back.2)
      (by simp at cap ⊢;omega)
    refine ⟨t::ts,by simp [l],?_⟩
    intro r
    rw [List.foldl_cons,teq r,e];rfl

theorem late_rows {C : Circuit} (h : Qualifies C) (pre mid : List Gate) (n q f : Gate)
    (sp : C.gates=pre++(mid++[n,q,f])) (op : n.op=.not) (inner : 5≤n.inputs.headD 0) :
    ∃(ss : List Step) (g a b : Select) (d : Bool), ss.length=mid.length ∧
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
  refine ⟨ss,enc (n.inputs.headD 0),enc a,enc b,mode f,l,?_⟩
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

#print axioms late_rows
end FiveLateModel
