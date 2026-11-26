import LateShape
namespace FiveRoundThree
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Ends Five18096Finite Five18096Bypass Five18096Paths FiveRestricted

def atom (i : Fin 5) := fiveInputs.getD i.val zero
def singleton (i : Fin 5) : Row := Fin.ofNat _ (2^i.val)
def cosingleton (i : Fin 5) : Row := Fin.ofNat _ (31-2^i.val)
def rowLE (r t : Row) : Prop := ∀ i : Fin 5, bit r (atom i)=true → bit t (atom i)=true
instance (r t : Row) : Decidable (rowLE r t) := inferInstanceAs (Decidable (∀ i : Fin 5, _))
theorem target_extrema : ∀ i : Fin 5, bit (singleton i) (atom i)=true ∧ bit (cosingleton i) (atom i)=false ∧
    bit (singleton i) fiveGraph=false ∧ bit (cosingleton i) fiveGraph=true := by decide +kernel
theorem cube_extrema : ∀ (i : Fin 5) (r : Row),
    (bit r (atom i)=true → rowLE (singleton i) r) ∧
    (bit r (atom i)=false → rowLE r (cosingleton i)) := by decide +kernel

def meetRow (r t : Row) : Row := Fin.ofNat _ ((r.val &&& t.val)%32)
def joinRow (r t : Row) : Row := Fin.ofNat _ ((r.val ||| t.val)%32)
def cutRow (d : Bool) (r t : Row) := if d then meetRow r t else joinRow r t
theorem cube_cuts : ∀ (r t : Row),
    rowLE (meetRow r t) r ∧ rowLE t (joinRow r t) ∧
    (bit t fiveGraph=false → bit (meetRow r t) fiveGraph=false) ∧
    (bit r fiveGraph=true → bit (joinRow r t) fiveGraph=true) := by decide +kernel

theorem monotone_source {C : Circuit} (h : Qualifies C) (p s : List Gate) (n : Gate)
    (sp : C.gates=p++n::s) (op : n.op=.not) {r t : Row} (le : rowLE r t) :
    bit r (src p n)=true → bit t (src p n)=true := by
  have cm := (no_other_not C p s n sp op (exactCounts C h.legal h.cap h.computes h.internal).2.1).1
  have legal (g) (hg:g∈p) := (h.legal g (by simp [sp,hg])).1
  have ao g (hg:g∈p) := legal_ao g (legal g hg) (cm g hg)
  have roots : Sound true (fiveInputs.map (bit r)) (fiveInputs.map (bit t)) := by
    constructor
    · simp
    · intro j hj
      rw [bits_at] at hj ⊢
      by_cases k : j<5
      · exact le ⟨j,k⟩ hj
      · have none : fiveInputs[j]? = none := List.getElem?_eq_none (by change 5≤j;omega)
        simp [List.getD_eq_getElem?_getD,none,saved_bit_zero] at hj
  have both := (mono_run p _ _ roots ao).2 (n.inputs.headD 0)
  have project (x : Row) : phys p (fiveInputs.map (bit x))=(execute p fiveInputs).map (bit x) :=
    (saved_execute_bits p x fiveInputs legal).symm
  simpa only [project,bits_at,src] using both

def tailBits (d c a b : Bool) := if d then (c && a) || b else (c || a) && b
private theorem flips (d a b : Bool) (hf : tailBits d false a b=false) (ht : tailBits d true a b=true) :
    a=d ∧ b=(!d) := by cases d <;> cases a <;> cases b <;> simp_all [tailBits]

/-- All three arguments in the alternating final expression are distinct
computed prefix functions. No raw input can serve as the middle argument. -/
theorem late_internal_shape {C : Circuit} (h : Qualifies C) (p : List Gate) (n q f : Gate)
    (sp : C.gates=p++[n,q,f]) (op : n.op=.not) (inner : 5≤n.inputs.headD 0) :
    ∃ a b : ℕ, 5≤a ∧ a<5+p.length ∧ 5≤b ∧ b<5+p.length ∧
      let W := execute p fiveInputs
      let G := src p n
      let A := W.getD a zero
      let B := W.getD b zero
      G≠A ∧ G≠B ∧ A≠B ∧ fiveGraph=combine3 (mode f) G A B ∧
      ∃ r t : Row, bit r A=mode f ∧ bit t A=mode f ∧ bit (cutRow (mode f) r t) A=(!mode f) := by
  obtain ⟨a,b,as,bs,bl,_,_,value,forcedValue⟩:=late_shape h p n q f sp op inner
  let W := execute p fiveInputs
  let G := src p n
  let A := W.getD a zero
  let B := W.getD b zero
  let d := mode f
  have on (r : Row) : bit r fiveGraph=tailBits d (!(bit r G)) (bit r A) (bit r B) := by
    conv_lhs => rw [value]
    unfold combine3
    rw [bit_prime,bit_prime,saved_bit_neg]
    cases eq:mode f <;> simp [tailBits,d,eq,G,A,B,W]
  have off (r : Row) (c : Bool) : bit r (forced C p [q,f] c)=tailBits d c (bit r A) (bit r B) := by
    rw [forcedValue,bit_prime,bit_prime,fixed_bit]
    cases eq:mode f <;> simp [tailBits,d,eq,A,B,W]
  obtain ⟨⟨r,fr,gr,lr⟩,⟨t,ft,gt,ht⟩⟩:= pivotal_rows h p [q,f] n sp op inner
  change bit r G=false at gr
  change bit t G=true at gt
  have rh:= (on r).symm.trans fr
  have tl:= (on t).symm.trans ft
  rw [gr,Bool.not_false] at rh
  rw [gt,Bool.not_true] at tl
  have ⟨ar,br⟩:=flips d _ _ ((off r false).symm.trans lr) rh
  have ⟨at',bt⟩:=flips d _ _ tl ((off t true).symm.trans ht)
  have high : 5≤a := by
    by_contra! raw
    let i : Fin 5 := ⟨a,raw⟩
    have eqA : A=atom i := by
      obtain ⟨v,e⟩ := execute_extends p fiveInputs
      change (execute p fiveInputs).getD a zero=fiveInputs.getD a zero
      rw [e,stable_read _ (show a<fiveInputs.length from raw)]
    obtain ⟨y,nv,fs,fc⟩:=target_extrema i
    cases flag:d with
    | true =>
      have ar' : bit r (atom i)=true := eqA ▸ (ar.trans flag)
      have mon:=monotone_source h p [q,f] n sp op ((cube_extrema i r).1 ar')
      have ng : bit (singleton i) G=false := by
        cases z:bit (singleton i) G with
        | false => rfl
        | true => exact Bool.noConfusion (gr.symm.trans (mon z))
      have eq := on (singleton i)
      simp [tailBits,flag,ng,eqA,y,fs] at eq
    | false =>
      have at'' : bit t (atom i)=false := eqA ▸ (at'.trans flag)
      have yes:=monotone_source h p [q,f] n sp op ((cube_extrema i t).2 at'') gt
      change bit (cosingleton i) G=true at yes
      have eq:=on (cosingleton i)
      simp [tailBits,flag,yes,eqA,nv,fc] at eq
  have neA : G≠A := by
    intro e
    rw [←e,gr] at ar
    rw [←e,gt] at at'
    exact Bool.noConfusion (at'.trans ar.symm)
  have neB : G≠B := by
    intro e
    rw [←e,gr] at br
    rw [←e,gt] at bt
    exact Bool.noConfusion (bt.trans br.symm)
  have diff : A≠B := by
    intro e
    have bad := ar.symm.trans ((congrArg (bit r) e).trans br)
    have impossible (v : Bool) : v≠(!v) := by cases v <;> decide
    exact impossible d bad
  refine ⟨a,b,high,as,bl,bs,neA,neB,diff,value,r,t,ar,at',?_⟩
  change bit (cutRow d r t) A = !d
  obtain ⟨ml,jr,mlf,jrf⟩:=cube_cuts r t
  cases flag:d with
  | true =>
    have gx : bit (meetRow r t) G=false := by
      cases u:bit (meetRow r t) G with
      | false => rfl
      | true => exact Bool.noConfusion (gr.symm.trans (monotone_source h p [q,f] n sp op ml u))
    have eq:=on (meetRow r t)
    have fx:=mlf ft
    change bit (meetRow r t) A=false
    cases ax:bit (meetRow r t) A with
    | false => rfl
    | true => simp [tailBits,flag,gx,ax,fx] at eq
  | false =>
    have gx:=monotone_source h p [q,f] n sp op jr gt
    change bit (joinRow r t) G=true at gx
    have eq:=on (joinRow r t)
    have fx:=jrf fr
    change bit (joinRow r t) A=true
    cases ax:bit (joinRow r t) A with
    | true => rfl
    | false => simp [tailBits,flag,gx,ax,fx] at eq
#print axioms late_internal_shape
end FiveRoundThree
