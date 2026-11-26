import SixTerms
namespace FourFork
abbrev V := Fin 5
abbrev M := Fin 4 → V → Bool
def L (e : Fin 4) : V := (![0,0,0,3] : Fin 4 → V) e
def R (e : Fin 4) : V := (![1,2,3,4] : Fin 4 → V) e
def all5 (f : V → Bool) := f 0 && f 1 && f 2 && f 3 && f 4
def any4 (f : Fin 4 → Bool) := f 0 || f 1 || f 2 || f 3
def adj (p q : V) := decide ((p=0 ∧ (q=1 ∨ q=2 ∨ q=3)) ∨ (q=0 ∧ (p=1 ∨ p=2 ∨ p=3)) ∨ (p=3 ∧ q=4) ∨ (q=3 ∧ p=4))
def lit (s : V → Bool) (p q : V) := s p || s q
def d0 (m : M) (p q : V) := lit (m 0) p q && lit (m 1) p q
def d1 (m : M) (a b : Bool) (p q : V) :=
  (lit (m 2) p q || (a && d0 m p q)) && (lit (m 3) p q || (b && d0 m p q))
def vert (u p q : V) := decide (u=p ∨ u=q)
def sig (m : M) (a b d : Bool) := if d then d1 m a b else d0 m
def term (m : M) (a b : Bool) (e : Fin 4) (k : Fin 5) (p q : V) :=
  match k.val with
  | 0 => d0 m p q && vert (L e) p q
  | 1 => d0 m p q && vert (R e) p q
  | 2 => d1 m a b p q && vert (L e) p q
  | 3 => d1 m a b p q && vert (R e) p q
  | _ => d0 m p q && d1 m a b p q
def wins (m : M) (a b : Bool) (e : Fin 4) (k : Fin 5) :=
  term m a b e k (L e) (R e) && all5 fun p => all5 fun q => !term m a b e k p q || adj p q
def thin (s : V→Bool) := all5 fun x => all5 fun y => !(s x && s y) || (x == y)
def needed (d : V→V→Bool) := all5 fun u => !d u u || any4 fun e =>
  !vert u (L e) (R e) && d (L e) (R e)
def branchBad (m : M) (a b : Bool) := d1 m a b 0 0 && !d0 m 0 1 && !d0 m 0 2 &&
  d1 m a b 3 4 && m 2 0 && !lit (m 2) 3 4
def admissible (m : M) (a b : Bool) :=
  SixTerms.all4 (fun k => thin (m k)) && needed (d0 m) && needed (d1 m a b) &&
  SixTerms.all4 (fun e => SixTerms.some5 (fun k => wins m a b e k)) && !branchBad m a b
theorem all5_iff (f : V→Bool) : all5 f=true ↔ ∀ p, f p=true := by
  simp only [all5,Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨u,v⟩,w⟩,x⟩,y⟩ p; fin_cases p <;> assumption
  · intro h; exact ⟨⟨⟨⟨h 0,h 1⟩,h 2⟩,h 3⟩,h 4⟩
theorem any4_of (f : Fin 4→Bool) (e : Fin 4) (on : f e=true) : any4 f=true := by
  fin_cases e <;> simp_all [any4]
theorem needed_of (d : V→V→Bool)
    (w : ∀ u, d u u=true → ∃ e, (u≠L e ∧ u≠R e) ∧ d (L e) (R e)=true) : needed d=true := by
  apply (all5_iff _).2; intro u
  cases h : d u u
  · simp
  · obtain ⟨e,⟨a,b⟩,yes⟩ := w u h
    simp only [Bool.not_true,Bool.false_or]
    exact any4_of _ e (by simp [vert,a,b,yes])
theorem accept_of (m : M) (a b : Bool) (r : ∀ k,thin (m k)=true)
    (n0 : needed (d0 m)=true) (n1 : needed (d1 m a b)=true) (guard : branchBad m a b=false)
    (w : ∀ e, ∃ k, term m a b e k (L e) (R e)=true ∧ ∀ p q, term m a b e k p q=true → adj p q=true) :
    admissible m a b=true := by
  apply Bool.and_eq_true_iff.mpr; refine ⟨?_,by simp [guard]⟩
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨(SixTerms.all4_iff _).2 r,n0⟩,n1⟩,
    (SixTerms.all4_iff _).2 (fun e => ?_)⟩
  obtain ⟨k,on,ok⟩ := w e
  apply SixTerms.some5_of (k := k)
  refine Bool.and_eq_true_iff.mpr ⟨on,(all5_iff _).2 (fun p => (all5_iff _).2 (fun q => ?_))⟩
  cases h : term m a b e k p q <;> simp [h,ok p q]
end FourFork
