import Symmetry
import RoundTwo
namespace FiveRestricted
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Finite

def rawFive : List (Fin 5) := [0,1,2,3,4]
def tableOK (p : List (Fin 5)) : Bool :=
  decide (∀x : Fin 5→Bool, tableFun 5 b (fun i => x (permAt p i))=tableFun 5 b x)

set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem all_automorphisms : rawFive.permutations'.all (fun p => tableOK p == inputPerms.contains p)=true := by decide +kernel
theorem exact_group (p : List (Fin 5)) (perm : p.Perm rawFive) :
    (∀x : Fin 5→Bool, tableFun 5 b (fun i => x (permAt p i))=tableFun 5 b x) ↔ p∈inputPerms := by
  have check := beq_iff_eq.mp (List.all_eq_true.mp all_automorphisms p (List.mem_permutations'.mpr perm))
  have eq : (tableOK p=true) ↔ (inputPerms.contains p=true) := by rw [check]
  simpa only [tableOK,List.contains_eq_mem,decide_eq_true_eq] using eq

def representatives : List FirstKey :=
  [(false,0,1),(false,1,2),(false,1,4),
   (true,0,1),(true,1,2),(true,1,4),(true,0,4)]
def moveKey (p : List (Fin 5)) (k : FirstKey) : FirstKey :=
  (k.1,min (liftPin p k.2.1) (liftPin p k.2.2),max (liftPin p k.2.1) (liftPin p k.2.2))
theorem seven_count : representatives.length=7 ∧ representatives.Nodup := by decide +kernel
theorem representatives_cover : options.all (fun k => inputPerms.any (fun p => representatives.contains (moveKey p k))) = true := by decide +kernel

lemma move_key (p : List (Fin 5)) (g : Gate) :
    optionKey (permGate p g)=(optionKey g).map (moveKey p) := by
  obtain ⟨op,l⟩ := g
  cases l with
  | nil => cases op <;> rfl
  | cons a r =>
    cases r with
    | nil => cases op <;> rfl
    | cons b r =>
      cases r with
      | cons c t => cases op <;> rfl
      | nil =>
        by_cases h : a≤b
        · cases op <;> simp [optionKey,permGate,moveKey,Nat.min_eq_left h,Nat.max_eq_right h]
        · have ba : b≤a := by omega
          cases op <;> simp [optionKey,permGate,moveKey,Nat.min_eq_right ba,Nat.max_eq_left ba,Nat.min_comm,Nat.max_comm]

def chooseSeven (C : Circuit) : Bool :=
  match C.gates.head?.bind optionKey with
  | some k => representatives.contains k
  | none => false

lemma move_head (p : List (Fin 5)) (C : Circuit) :
    (permNet p C).gates.head?.bind optionKey=(C.gates.head?.bind optionKey).map (moveKey p) := by
  cases c : C.gates with
  | nil => simp [permNet,c]
  | cons g s => simpa [permNet,c] using move_key p g

theorem seven_model : (∃ C, Qualifies C) ↔ ∃ v : Plan, Qualifies (net v) ∧ RoundFilters (net v) ∧ chooseSeven (net v)=true := by
  constructor
  · intro start
    obtain ⟨C,h,unary⟩ := unary_iff.mp start
    have first := first_among_nineteen h
    cases k : C.gates.head?.bind optionKey with
    | none => simp [firstAllowed,k] at first
    | some key =>
      have member : key∈options := by simpa [firstAllowed,k] using first
      obtain ⟨p,hp,rep⟩ := List.any_eq_true.mp (List.all_eq_true.mp representatives_cover key member)
      have hc := perm_qualifies h hp
      have un : RealPins (permNet p C) := by
        intro g hg op
        obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
        simpa [permGate] using unary q hq op
      obtain ⟨v,hv⟩ := plan_covers hc
      refine ⟨v,hv ▸ hc,?_,?_⟩
      · rw [hv]
        exact ⟨filters hc,un,first_among_nineteen hc,all_fanouts hc,
          fun _ m _ _ sp => prefix_budget hc m sp,fun p f sp j hit => no_input_at_output hc p f sp j hit⟩
      · rw [hv,chooseSeven,move_head,k]
        exact rep
  · rintro ⟨v,h,_⟩
    exact ⟨net v,h⟩

#print axioms all_automorphisms
#print axioms seven_model
end FiveRestricted
