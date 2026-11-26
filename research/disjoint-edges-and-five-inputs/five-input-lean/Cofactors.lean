import Restricted

namespace FiveRestricted
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Ends Five18096Finite

structure SCase where
  pin : ℕ
  high : Bool
  T : ℕ
  L : ℕ
deriving DecidableEq

def cofs : List SCase :=
  [⟨0,false,p5_T,7⟩, ⟨4,true,p7_T,7⟩, ⟨4,false,p12_T,6⟩,
   ⟨1,false,p8_T,5⟩, ⟨1,true,p9_T,5⟩, ⟨2,false,p8_T,5⟩, ⟨2,true,p9_T,5⟩,
   ⟨3,false,p8_T,5⟩, ⟨3,true,p9_T,5⟩]

def fourR := rootsW [0,1,2,3]
def restrictedW (c : SCase) :=
  fourR.take c.pin ++ [if c.high then one else zero] ++ fourR.drop c.pin
def embedding (c : SCase) (r : Row) : Row :=
  Fin.ofNat 128 (rowOf ((List.range 5).erase c.pin) (if c.high then 2^c.pin else 0) r.val)

def checkRows (c : SCase) : Bool :=
  (List.finRange 128).all fun r =>
    ((restrictedW c).map (bit r) == fiveInputs.map (bit (embedding c r))) &&
    (bit r (W c.T) == bit (embedding c r) fiveGraph)

def checkRoots (c : SCase) : Bool :=
  ((restrictedW c).map (nrm true)).all (fun u => u == zero || fourR.contains u)

set_option maxRecDepth 15000
set_option maxHeartbeats 0
theorem valid_cofs : cofs.all (fun c => checkRows c && checkRoots c)=true := by decide +kernel

lemma prior {c : SCase} (hc : c∈cofs) :
    Lower true fourR (W c.T) c.L ∧ proper (W c.T) ∧ bit 0 (W c.T)=false := by
  have general {R E T : _} {L : Nat} (b : baseOK T R E=true) (hl : LowN true R T L) :
      Lower true (rootsW R) (W T) L ∧ proper (W T) ∧ bit 0 (W T)=false := by
    have pb := baseOK_ok b
    exact ⟨hl,pb.prop,by simpa [plainWord] using pb.plain⟩
  simp only [cofs,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact general p5_B p5_L
  · exact general p7_B p7_L
  · exact general p12_B p12_L
  · exact general p8_B p8_L
  · exact general p9_B p9_L
  · exact general p8_B p8_L
  · exact general p9_B p9_L
  · exact general p8_B p8_L
  · exact general p9_B p9_L

theorem cofactor_lower {C : Circuit} (h : Qualifies C) {c : SCase} (hc : c∈cofs) :
    c.L ≤ workCost C.gates (restrictedW c) := by
  obtain ⟨tab,roots⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp valid_cofs c hc)
  have rows (r : Row) := Bool.and_eq_true_iff.mp (List.all_eq_true.mp tab r (List.mem_finRange r))
  obtain ⟨bound,hp,hz⟩ := prior hc
  apply signed_cost_lower C h.legal fourR _ _ _ bound hp hz
  · intro v hv
    simpa using List.all_eq_true.mp roots v hv
  · apply projected_output h _ (embedding c)
    · intro r; exact beq_iff_eq.mp (rows r).1
    · intro r; exact beq_iff_eq.mp (rows r).2

/-- A prefix may be pruned with the signed cost already spent, counting every
remaining ordinary gate generously as one. This works with arbitrary suffixes. -/
theorem prefix_budget {C : Circuit} (h : Qualifies C) {c : SCase} (hc : c∈cofs)
    {p s : List Gate} (split : C.gates=p++s) :
    p.countP (fun g => !isNot g) + c.L ≤ workCost p (restrictedW c) + 9 := by
  have lower := cofactor_lower h hc
  have total := (exactCounts C h.legal h.cap h.computes h.internal).2.2
  rw [split,cost_append] at lower
  rw [split,List.countP_append] at total
  have upper := cost_max s (execute p (restrictedW c))
  omega

#print axioms cofactor_lower
#print axioms prefix_budget
end FiveRestricted
