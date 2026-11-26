import Pivotal
namespace FiveRoundThree
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Ends Five18096Finite Five18096Bypass Five18096Paths FiveRestricted

def combine3 (d : Bool) (g a b : Sig) := prime d (prime (!d) (neg g) a) b
def mode (g : Gate) := match g.op with | .or => true | _ => false
lemma comm (d : Bool) (a b : Sig) : prime d a b=prime d b a := by cases d <;> simp [prime,BitVec.and_comm,BitVec.or_comm]

lemma split_operand (g : Gate) (i : ℕ) (mem : i∈g.inputs) (valid : GValid g) :
    ∃ a, a∈g.inputs ∧ a≠i ∧ ∀w, gv w g=prime (mode g) (w.getD i zero) (w.getD a zero) := by
  obtain ⟨x,y,pins,ne⟩ := valid.2.2
  have two : i=x ∨ i=y := by simpa [pins] using mem
  have eq (w : List Sig) : gv w g=prime (mode g) (w.getD x zero) (w.getD y zero) := by
    have ao := legal_ao g valid.1 valid.2.1
    obtain ⟨o,l⟩:=g
    change l=[x,y] at pins
    subst l
    rcases ao with e|e <;> change o=_ at e <;> subst o
    · exact value_two w false x y
    · exact value_two w true x y
  rcases two with rfl|rfl
  · exact ⟨y,by simp [pins],Ne.symm ne,eq⟩
  · exact ⟨x,by simp [pins],ne,fun w=>(eq w).trans (comm ..)⟩

/-- When only two gates follow the NOT, its signal must pass through both,
with opposite operations; each of their other operands is in the prefix bank. -/
theorem late_shape {C : Circuit} (h : Qualifies C) (p : List Gate) (n q f : Gate)
    (sp : C.gates=p++[n,q,f]) (op : n.op=.not) (inner : 5≤n.inputs.headD 0) :
    ∃ a b : ℕ, a<5+p.length ∧ b<5+p.length ∧ 5≤b ∧ n.inputs.headD 0<5+p.length ∧
      mode q = !mode f ∧
      fiveGraph=combine3 (mode f) (src p n) ((execute p fiveInputs).getD a zero) ((execute p fiveInputs).getD b zero) ∧
      ∀c, forced C p [q,f] c=prime (mode f) (prime (!mode f) (fixed c) ((execute p fiveInputs).getD a zero))
        ((execute p fiveInputs).getD b zero) := by
  let w := execute p fiveInputs
  let k := 5+p.length
  have length : w.length=k := by unfold w k;rw [execute_len];rfl
  have sz:=size_exact h
  have p7 : p.length=7 := by simp [sp] at sz;omega
  have final := final_output h
  have num := (exactCounts C h.legal h.cap h.computes h.internal).2.1
  have ns := (no_other_not C p [q,f] n sp op num).2
  have gvQ : GValid q := ⟨(h.legal q (by simp [sp])).1,ns q (by simp),(filters h).binary q (by simp [sp]) (ns q (by simp))⟩
  have gvF : GValid f := ⟨(h.legal f (by simp [sp])).1,ns f (by simp),(filters h).binary f (by simp [sp]) (ns f (by simp))⟩
  have notFinal := output_cannot_read_not C h.legal h.cap h.computes h.back h.used p [q] n f sp op inner
  have rq : k∈q.inputs := by
    obtain ⟨r,rm,rp⟩ := effective_use h p [q,f] n sp (by rw [final,p7];decide)
    have necessary := pins_subset r rp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at rm
    rcases rm with rfl|rfl
    · exact necessary
    · exact (notFinal necessary).elim
  have sf : C.gates=(p++[n])++q::[f] := by simpa [List.append_assoc] using sp
  have rf : k+1∈f.inputs := by
    obtain ⟨r,rm,rp⟩ := effective_use h (p++[n]) [f] q sf (by simp [final,List.length_append,p7])
    obtain rfl := List.mem_singleton.mp rm
    simpa [k,Nat.add_assoc] using pins_subset r rp
  obtain ⟨a,ma,na,qa⟩:=split_operand q k rq gvQ
  obtain ⟨b,mb,nb,fb⟩:=split_operand f (k+1) rf gvF
  have back : Back 5 C.gates := back_of_index 5 _ h.back
  rw [sp] at back
  have be := (back_split p [n,q,f] 5 back).2
  have rawN : n.inputs.headD 0∈n.inputs := by cases e:n.inputs with
                                           | nil => simp [e] at inner
                                           | cons a t => simp
  have validN := be.1 _ rawN
  have smallA : a<k := by have z:=be.2.1 a ma;change a<k+1 at z;omega
  have smallB : b<k := by
    have z :=be.2.2.1 b mb
    change b<k+1+1 at z
    have ne : b≠k := by intro e;apply notFinal;simpa only [←show k=5+p.length from rfl,←e] using mb
    omega
  have tailValue (v : Sig) :
      (execute [q,f] (w++[v])).getD C.output zero=
      prime (mode f) (prime (mode q) v (w.getD a zero)) (w.getD b zero) := by
    change (((w++[v])++[gv (w++[v]) q])++[gv ((w++[v])++[gv (w++[v]) q]) f]).getD C.output zero=_
    have index : C.output=(((w++[v])++[gv (w++[v]) q])).length := by simp [length,k,p7,final]
    have atEnd (xs : List Sig) (u : Sig) : (xs++[u]).getD xs.length zero=u := by simp [List.getD_eq_getElem?_getD]
    rw [index,atEnd,fb]
    have l1 : k+1=(w++[v]).length := by simp [length]
    rw [l1,atEnd,qa,←length,atEnd]
    rw [stable_read _ (show b<(w++[v]).length by simp [length];omega),
      stable_read _ (show b<w.length by omega),stable_read _ (show a<w.length by omega)]
  have normal := computed_sig C h.legal h.computes
  rw [sp,execute_append] at normal
  change (execute [q,f] (w++[gv w n])).getD C.output zero=fiveGraph at normal
  rw [tailValue,inverter_value p n op inner] at normal
  have opposite : mode q = !mode f := by
    have falls := internal_not_falls C h.legal h.cap h.computes h.back p [q,f] n sp op inner
    rw [inverter_value p n op inner] at falls
    cases u : mode q <;> cases v : mode f
    · have row := congrArg (bit 31) normal
      simp only [u,v,bit_prime,Bool.false_eq_true,↓reduceIte,falls.2,Bool.false_and,target_rises.2] at row
    · rfl
    · rfl
    · have row := congrArg (bit 0) normal
      simp only [u,v,bit_prime,↓reduceIte,falls.1,Bool.true_or,target_rises.1,Bool.true_eq_false] at row
  have last : C.gates=(p++[n,q])++[f] := by simpa [List.append_assoc] using sp
  refine ⟨a,b,smallA,smallB,no_input_at_output h _ _ last b mb,validN,opposite,?_,?_⟩
  · simpa [combine3,←opposite,w] using normal.symm
  · intro c; simpa [forced,w,←opposite] using tailValue (fixed c)

#print axioms late_shape
end FiveRoundThree
