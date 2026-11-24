import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_5168_aux

private def reflection (i : Fin 9) : Fin 9 :=
  (![0,5,8,3,4,1,7,6,2] : Fin 9 → Fin 9) i

private def wireIndex (i : ℕ) : ℕ :=
  if h : i < 9 then (reflection ⟨i,h⟩).val else i

private def reflectedGate (g : Gate) : Gate := ⟨g.op, g.inputs.map wireIndex⟩

private def reflectedCircuit (C : Circuit) : Circuit :=
  ⟨C.gates.map reflectedGate, wireIndex C.output⟩

private def advanceWire (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))]

private theorem read_reflected (x : Fin 9 → Bool) (tail : List Bool) (i : ℕ) :
    (List.ofFn x ++ tail).getD (wireIndex i) false =
    (List.ofFn (fun k => x (reflection k)) ++ tail).getD i false := by
  by_cases hi : i < 9
  · interval_cases i <;> rfl
  · have hn : 9 ≤ i := by omega
    have h₁ : (List.ofFn x).length ≤ i := by simpa using hn
    have h₂ : (List.ofFn (fun k => x (reflection k))).length ≤ i := by simpa using hn
    simp only [wireIndex, dif_neg hi, List.getD_eq_getElem?_getD,
      List.getElem?_append_right h₁, List.getElem?_append_right h₂, List.length_ofFn]

private theorem shared_tail (gs : List Gate) (x : Fin 9 → Bool) (tail : List Bool) :
    ∃ out : List Bool,
      (gs.map reflectedGate).foldl advanceWire (List.ofFn x ++ tail) = List.ofFn x ++ out ∧
      gs.foldl advanceWire (List.ofFn (fun k => x (reflection k)) ++ tail) =
        List.ofFn (fun k => x (reflection k)) ++ out := by
  induction gs generalizing tail with
  | nil => exact ⟨tail,rfl,rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map (fun i =>
      (List.ofFn (fun k => x (reflection k)) ++ tail).getD i false))
    have h₁ : advanceWire (List.ofFn x ++ tail) (reflectedGate g) =
        List.ofFn x ++ (tail ++ [v]) := by
      simp only [advanceWire, reflectedGate, List.map_map, Function.comp_def,
        read_reflected, List.append_assoc, v]
    have h₂ : advanceWire (List.ofFn (fun k => x (reflection k)) ++ tail) g =
        List.ofFn (fun k => x (reflection k)) ++ (tail ++ [v]) := by
      simp only [advanceWire, List.append_assoc, v]
    simpa only [List.map_cons, List.foldl_cons, h₁, h₂] using ih (tail ++ [v])

private theorem evaluate_reflection (C : Circuit) (x : Fin 9 → Bool) (tail : List Bool) :
    (reflectedCircuit C).eval (List.ofFn x ++ tail) =
    C.eval (List.ofFn (fun k => x (reflection k)) ++ tail) := by
  obtain ⟨out,h₁,h₂⟩ := shared_tail C.gates x tail
  change ((C.gates.map reflectedGate).foldl advanceWire (List.ofFn x ++ tail)).getD
    (wireIndex C.output) false = (C.gates.foldl advanceWire
    (List.ofFn (fun k => x (reflection k)) ++ tail)).getD C.output false
  rw [h₁, h₂, read_reflected]

private theorem reflected_fanin (C : Circuit) (h : FanInTwo C) : FanInTwo (reflectedCircuit C) := by
  intro g hg
  obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hg
  obtain ⟨hop,hn⟩ := h old ho
  exact ⟨hop,by simpa [reflectedGate] using hn⟩

private def edgeValue (x : Fin 9 → Bool) : Bool :=
  ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
    List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)

private theorem reflected_edges (x : Fin 9 → Bool) :
    edgeValue (fun k => x (reflection k)) = edgeValue x := by
  simp only [edgeValue, List.any_cons, List.any_nil, Bool.or_false,
    show reflection 0 = 0 from rfl, show reflection 1 = 5 from rfl,
    show reflection 2 = 8 from rfl, show reflection 3 = 3 from rfl,
    show reflection 4 = 4 from rfl, show reflection 5 = 1 from rfl,
    show reflection 6 = 7 from rfl, show reflection 7 = 6 from rfl,
    show reflection 8 = 2 from rfl]
  ac_rfl

private def acceptedCodes : List ℕ := [1,2,3,4,6,11,12,13,14,15,16,17,21,22,24,25,26,31,33,42,61]

private theorem covers_pairs : ∀ a b : Fin 9, a < b →
    9*a.val+b.val ∈ acceptedCodes ∨
      9*(reflection a).val+(reflection b).val ∈ acceptedCodes ∨
      9*(reflection b).val+(reflection a).val ∈ acceptedCodes := by decide +kernel

private def solvesPair (a b : Fin 9) (C : Circuit) := ∀ x : Fin 9 → Bool,
  C.eval (List.ofFn x ++ [!x 0,x a || x b]) = edgeValue x

private theorem reflects_pair {a b : Fin 9} {C : Circuit} (h : solvesPair a b C) :
    solvesPair (reflection a) (reflection b) (reflectedCircuit C) := by
  intro x
  rw [evaluate_reflection]
  have hx := h (fun k => x (reflection k))
  change C.eval (List.ofFn (fun k => x (reflection k)) ++
    [!x 0,x (reflection a) || x (reflection b)]) = _ at hx
  exact hx.trans (reflected_edges x)

end PEqualNP.Outside.L_meta_5168_aux

open PEqualNP.Outside.L_meta_5168_aux

theorem PEqualNP.Outside.L_meta_5168 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; have x2 : Fin (9 : ℕ) → Fin (9 : ℕ) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 x3 : Fin (9 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x5 ++ [!x5 (0 : Fin (9 : ℕ)), x5 x2 || x5 x3]) = x1 x5; ∀ (x3 x4 : Fin (9 : ℕ)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), x3 < x4 → PEqualNP.MetaComplexity.FanInTwo x5 → x5.size ≤ (13 : ℕ) → x2 x3 x4 x5 → ∃ (x10 : Fin (9 : ℕ)) (x11 : Fin (9 : ℕ)) (x12 : PEqualNP.CircuitLowerBounds.Circuit), (9 : ℕ) * ↑x10 + ↑x11 ∈ [(1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (6 : ℕ), (11 : ℕ), (12 : ℕ), (13 : ℕ), (14 : ℕ), (15 : ℕ), (16 : ℕ), (17 : ℕ), (21 : ℕ), (22 : ℕ), (24 : ℕ), (25 : ℕ), (26 : ℕ), (31 : ℕ), (33 : ℕ), (42 : ℕ), (61 : ℕ)] ∧ PEqualNP.MetaComplexity.FanInTwo x12 ∧ x12.size ≤ (13 : ℕ) ∧ x2 x10 x11 x12 := by
  change ∀ (a b : Fin 9) (C : Circuit), a < b → FanInTwo C → C.size ≤ 13 → solvesPair a b C →
    ∃ (p q : Fin 9) (D : Circuit), 9*p.val+q.val ∈ acceptedCodes ∧ FanInTwo D ∧ D.size ≤ 13 ∧ solvesPair p q D
  intro a b C hab hfan hsize hsolve
  rcases covers_pairs a b hab with h | h | h
  · exact ⟨a,b,C,h,hfan,hsize,hsolve⟩
  · exact ⟨reflection a,reflection b,reflectedCircuit C,h,reflected_fanin C hfan,
      by simpa [reflectedCircuit,Circuit.size] using hsize, reflects_pair hsolve⟩
  · refine ⟨reflection b,reflection a,reflectedCircuit C,h,reflected_fanin C hfan,
      by simpa [reflectedCircuit,Circuit.size] using hsize, ?_⟩
    intro x
    simpa only [Bool.or_comm (x (reflection a)) (x (reflection b))] using (reflects_pair hsolve x)
