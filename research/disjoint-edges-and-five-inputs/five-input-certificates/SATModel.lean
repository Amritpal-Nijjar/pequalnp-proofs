import PostedSeven
namespace FiveSAT
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12108
open FiveInputLower Five18096Fresh Five18096Ends Five18096Finite FiveRestricted

structure Select where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool
deriving DecidableEq
def enc (j : Nat) : Select := ⟨j.testBit 0,j.testBit 1,j.testBit 2,j.testBit 3⟩
def mux (s : Select) (v : Fin 16 → Bool) : Bool := (if s.b3 then (if s.b2 then (if s.b1 then (if s.b0 then v 15 else v 14) else (if s.b0 then v 13 else v 12)) else (if s.b1 then (if s.b0 then v 11 else v 10) else (if s.b0 then v 9 else v 8))) else (if s.b2 then (if s.b1 then (if s.b0 then v 7 else v 6) else (if s.b0 then v 5 else v 4)) else (if s.b1 then (if s.b0 then v 3 else v 2) else (if s.b0 then v 1 else v 0))))
theorem mux_enc (j : Fin 16) (vals : Fin 16→Bool) : mux (enc j.val) vals=vals j := by fin_cases j <;> rfl
def lowerOK (s : Select) (limit : ℕ) : Bool := mux s (fun j => decide (j.val<limit))
def sameSel (a b : Select) := (a.b0==b.b0) && (a.b1==b.b1) && (a.b2==b.b2) && (a.b3==b.b3)
lemma same_enc (a b : Fin 16) : sameSel (enc a.val) (enc b.val) = decide (a=b) := by revert a b; decide +kernel

abbrev Rows := Fin 32
abbrev WireBits := Fin 10 → Rows → Bool
def row (r : Rows) : Row := ⟨r.val,by have := r.isLt; omega⟩
def wire (w : WireBits) (r : Rows) (i : Fin 16) : Bool :=
  if i.val<5 then bit (row r) (fiveInputs.getD i.val zero)
  else if h : i.val-5<10 then w ⟨i.val-5,h⟩ r else false
def expected (r : Rows) := bit (row r) fiveGraph
def all32 (p : Rows→Bool) : Bool := (((((p 0 && p 1) && (p 2 && p 3)) && ((p 4 && p 5) && (p 6 && p 7))) && (((p 8 && p 9) && (p 10 && p 11)) && ((p 12 && p 13) && (p 14 && p 15)))) && ((((p 16 && p 17) && (p 18 && p 19)) && ((p 20 && p 21) && (p 22 && p 23))) && (((p 24 && p 25) && (p 26 && p 27)) && ((p 28 && p 29) && (p 30 && p 31)))))
def all10 (p : Fin 10→Bool) : Bool := (((p 0 && p 1) && (p 2 && (p 3 && p 4))) && ((p 5 && p 6) && (p 7 && (p 8 && p 9))))
lemma all32_of (p : Rows→Bool) (h : ∀r,p r=true) : all32 p=true := by simp only [all32,h,Bool.and_true]
lemma all10_of (p : Fin 10→Bool) (h : ∀r,p r=true) : all10 p=true := by simp only [all10,h,Bool.and_true]

def checkRow (w : WireBits) (left right : Fin 10→Select) (op : Fin 10→Bool)
    (k j : Fin 10) (r : Rows) : Bool :=
  let a := mux (left j) (wire w r)
  let b := mux (right j) (wire w r)
  let output := if j=k then !a else if op j then a || b else a && b
  w j r == output

def okayPin (k j : Fin 10) (left right : Fin 10→Select) : Bool :=
  lowerOK (left j) (5+j.val) &&
    (if j=k then !(lowerOK (left j) 5) else lowerOK (right j) (5+j.val) && !(sameSel (left j) (right j)))

def passes (k : Fin 10) (w : WireBits) (left right : Fin 10→Select) (op : Fin 10→Bool) : Bool :=
  all10 (fun j => okayPin k j left right && all32 (checkRow w left right op k j)) &&
  all32 (fun r => w 9 r == expected r)
end FiveSAT
