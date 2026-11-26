import LateShape
namespace FiveRoundThree
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Ends Five18096Finite Five18096Bypass Five18096Paths FiveRestricted

private lemma from_pair (g : Gate) (v : GValid g) (i j : ℕ) (ne : i≠j)
    (mi : i∈g.inputs) (mj : j∈g.inputs) (w : List Sig) :
    gv w g=prime (mode g) (w.getD i zero) (w.getD j zero) := by
  obtain ⟨b,mb,bi,read⟩:=split_operand g i mi v
  obtain ⟨s,t,pins,_⟩:=v.2.2
  simp only [pins,List.mem_cons,List.not_mem_nil,or_false] at mi mj mb
  have same : b=j := by omega
  exact same ▸ read w

private lemma reduced (d e : Bool) (n a : Sig) :
    prime d n (prime e n a) = if d=e then prime e n a else n := by
  apply bit_ext
  intro k
  cases d <;> cases e <;> simp only [bit_prime,↓reduceIte,Bool.false_eq_true,Bool.true_eq_false]
  all_goals cases bit k n <;> cases bit k a <;> rfl

private lemma stable_pin (d : Bool) {v a : Sig} (fall : Falling v) (rise : Rising a) :
    bit 0 (prime d v a)=bit 31 (prime d v a) := by
  rw [bit_prime,bit_prime,fall.1,fall.2,rise.1,rise.2]
  cases d <;> rfl

/-- If the NOT is followed by three gates it cannot fan out to both of the
first two. Direct input to the final gate is already impossible. -/
theorem position_six_single {C : Circuit} (h : Qualifies C) (p : List Gate) (n x y f : Gate)
    (sp : C.gates=p++[n,x,y,f]) (nop : n.op=.not) (hi : 5≤n.inputs.headD 0) :
    ¬(5+p.length∈x.inputs ∧ 5+p.length∈y.inputs) := by
  rintro ⟨px,py⟩
  let w:=execute p fiveInputs
  let k:=5+p.length
  let N:=gv w n
  let wn:=w++[N]
  let X:=gv wn x
  let wx:=wn++[X]
  let Y:=gv wx y
  let wy:=wx++[Y]
  change k∈x.inputs at px
  change k∈y.inputs at py
  have len : w.length=k := by unfold w k;rw [execute_len];rfl
  have l1 : wn.length=k+1 := by simp [wn,len]
  have l2 : wx.length=k+1+1 := by simp [wx,l1]
  have endWire (a : List Sig) (z : Sig) : (a++[z]).getD a.length zero=z := by simp [List.getD_eq_getElem?_getD]
  have nk : wn.getD k zero=N := by rw [←len];exact endWire w N
  have xk : wx.getD (k+1) zero=X := by rw [←l1];exact endWire wn X
  have nk2 : wx.getD k zero=N := (stable_read _ (show k<wn.length by omega)).trans nk
  have yk : wy.getD (k+1+1) zero=Y := by rw [←l2];exact endWire wx Y
  have xk2 : wy.getD (k+1) zero=X := (stable_read _ (show k+1<wx.length by omega)).trans xk
  have sz:=size_exact h
  have pl : p.length=6 := by simp [sp] at sz;omega
  have no := no_other_not C p [x,y,f] n sp nop (exactCounts C h.legal h.cap h.computes h.internal).2.1
  have valid (g) (hg:g∈[x,y,f]) : GValid g :=
    ⟨(h.legal g (by simp [sp,hg])).1,no.2 g hg,(filters h).binary g (by simp [sp,hg]) (no.2 g hg)⟩
  have vx:=valid x (by simp)
  have vy:=valid y (by simp)
  have vf:=valid f (by simp)
  have back:=back_of_index 5 C.gates h.back
  have fr:=(filters h).fresh
  rw [sp] at back fr
  have ends := back_split p [n,x,y,f] 5 back
  have fres := run_split p [n,x,y,f] fiveInputs fr
  have rise (i) (small:i<k) : Rising (w.getD i zero) :=
    prefix_rises p fiveInputs roots_rise (fun g hg=>h.legal g (by simp [sp,hg])) no.1 ends.1 fres.1 _
      (read_mem w i (len.symm ▸ small))
  have fall : Falling N := internal_not_falls C h.legal h.cap h.computes h.back p [x,y,f] n sp nop hi
  obtain ⟨a,ma,na,xa⟩:=split_operand x k px vx
  have as : a<k := by have z:=ends.2.2.1 a ma;change a<k+1 at z;omega
  have xv : X=prime (mode x) N (w.getD a zero) := by
    change gv wn x=_
    rw [xa,nk,stable_read _ (show a<w.length by omega)]
  by_cases inY : k+1∈y.inputs
  · have old : ¬Old wx y := fres.2.2.2.1 vy.2.1
    apply old
    unfold Old
    rw [from_pair y vy k (k+1) (by omega) py inY wx,nk2,xk,xv,reduced]
    by_cases eq : mode y=mode x
    · rw [if_pos eq,←xv,←xk];exact saved_get_rep wx (k+1)
    · rw [if_neg eq,←nk2];exact saved_get_rep wx k
  · obtain ⟨b,mb,nb,yb⟩:=split_operand y k py vy
    have bs : b<k := by
      have z:=ends.2.2.2.1 b mb
      change b<k+1+1 at z
      have different : b≠k+1 := by intro e;exact inY (e ▸ mb)
      omega
    have yv : Y=prime (mode y) N (w.getD b zero) := by
      change gv wx y=_
      rw [yb,nk2,stable_read _ (show b<wn.length by omega),stable_read _ (show b<w.length by omega)]
    have stableX : bit 0 X=bit 31 X := xv ▸ stable_pin (mode x) fall (rise a as)
    have stableY : bit 0 Y=bit 31 Y := yv ▸ stable_pin (mode y) fall (rise b bs)
    have splitX : C.gates=(p++[n])++x::[y,f] := by simpa [List.append_assoc] using sp
    obtain ⟨q,qm,qp⟩:=effective_use h (p++[n]) [y,f] x splitX (by simp [pl,final_output h])
    have qpin : k+1∈q.inputs := by simpa [k,Nat.add_assoc] using pins_subset q qp
    have fx : k+1∈f.inputs := by
      rcases List.mem_cons.mp qm with rfl|qm
      · exact (inY qpin).elim
      · simpa [List.mem_singleton.mp qm] using qpin
    have splitY : C.gates=(p++[n,x])++y::[f] := by simpa [List.append_assoc] using sp
    obtain ⟨r,rm,rp⟩:=effective_use h (p++[n,x]) [f] y splitY (by simp [pl,final_output h])
    have rf : r=f := List.mem_singleton.mp rm
    subst r
    have fy : k+1+1∈f.inputs := by simpa [k,Nat.add_assoc] using pins_subset f rp
    have last : C.gates=(p++[n,x,y])++[f] := by simpa [List.append_assoc] using sp
    have out:=value_last C h.legal h.computes h.used _ f last
    rw [execute_append] at out
    change gv wy f=fiveGraph at out
    rw [from_pair f vf (k+1) (k+1+1) (by omega) fx fy wy,xk2,yk] at out
    have equal : bit 0 fiveGraph=bit 31 fiveGraph := by
      rw [←out,bit_prime,bit_prime,stableX,stableY]
    rw [target_rises.1,target_rises.2] at equal
    contradiction
#print axioms position_six_single
end FiveRoundThree
