import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.ReadK PEqualNP.GenericRejection PEqualNP.LowMerge
open PEqualNP.MetaComplexity.NestedCover
open scoped BigOperators

-- A small circuit must merge two surviving points at one gate on over one hundred lines.
-- A maximal collection of disjoint pairs either has eight members or gives
-- a point cover of size at most fourteen. Seven lines per point cover at most ninety-eight.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 2800000 in
theorem PEqualNP.Outside.R_meta_4704_629
  (single : ∀ (n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit) (l : Fin n),
      IsAO2 (n+n) C →
      (∀ p ∈ S l, C.eval (incidenceInput {p} {l}) = true) →
      (∀ X : Finset (Fin n), IsFalseInput S X {l} → C.eval (incidenceInput X {l}) = false) →
      let side := fun (j : Fin C.size) (k : ℕ) => aliveSet n n C ((gateAt C j.val).inputs.getD k 0) l
      let G : Finset (Fin C.size) := Finset.univ.filter (fun j : Fin C.size =>
        IsLowMerge n n (fun p t => decide (p ∈ S t)) C (n+n+j.val) l ∧
        (S l ∩ (side j 0 \ side j 1)).Nonempty ∧ (S l ∩ (side j 1 \ side j 0)).Nonempty)
      (S l).card ≤ G.card + 1)
  (position : ∀ (n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit) (j : Fin C.size)
      (T : Finset (Fin n)) (r : Fin n → Fin n), IsAO2 (n+n) C → 1 < T.card →
      let side := fun (l : Fin n) (k : ℕ) => aliveSet n n C ((gateAt C j.val).inputs.getD k 0) l
      (∀ l ∈ T, IsLowMerge n n (fun p t => decide (p ∈ S t)) C (n+n+j.val) l ∧
        r l ∈ S l ∧ (r l ∈ side l 0 ∨ r l ∈ side l 1)) →
      (∀ l ∈ T, ∀ k ∈ T, r l ∈ S k → l = k) → 2*T.card ≤ j.val+2)
  (pencil : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      200 ≤ q → n = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ a b : Fin n, a ≠ b → ∃! l, a ∈ S l ∧ b ∈ S l) →
      IsAO2 (n+n) C → ¬ IsReadK (n+n) C 2 →
      RightOnIncidentPairs S C →
      (∀ X Y : Finset (Fin n), Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      (∀ B : Circuit, IsAO2 (n+n) B → B.output < n+n+B.size →
        (∀ X Y : Finset (Fin n), B.eval (incidenceInput X Y) = C.eval (incidenceInput X Y)) → C.size ≤ B.size) →
      100*C.size < n*q → ∀ (j : Fin C.size) (p : Fin n) (T : Finset (Fin n)) (r : Fin n → Fin n),
      let side := fun (l : Fin n) (k : ℕ) => aliveSet n n C ((gateAt C j.val).inputs.getD k 0) l
      let A := fun l => S l ∩ (side l 0 \ side l 1)
      let B := fun l => S l ∩ (side l 1 \ side l 0)
      (∀ l ∈ T, IsLowMerge n n (fun x t => decide (x ∈ S t)) C (n+n+j.val) l ∧
        ((p ∈ A l ∧ r l ∈ B l) ∨ (r l ∈ A l ∧ p ∈ B l))) →
      (∀ l ∈ T, ∀ k ∈ T, r l ∈ S k → l = k) → 2*T.card ≤ j.val+2 → T.card ≤ 7)
  (matching : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      200 ≤ q → n = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ a b : Fin n, a ≠ b → ∃! l, a ∈ S l ∧ b ∈ S l) →
      IsAO2 (n+n) C → ¬ IsReadK (n+n) C 2 →
      RightOnIncidentPairs S C →
      (∀ X Y : Finset (Fin n), Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      (∀ B : Circuit, IsAO2 (n+n) B → B.output < n+n+B.size →
        (∀ X Y : Finset (Fin n), B.eval (incidenceInput X Y) = C.eval (incidenceInput X Y)) → C.size ≤ B.size) →
      100*C.size < n*q → ∀ (j : Fin C.size) (T : Finset (Fin n)) (u v : Fin n → Fin n),
      let side := fun (l : Fin n) (k : ℕ) => aliveSet n n C ((gateAt C j.val).inputs.getD k 0) l
      let pair : Fin n → Finset (Fin n) := fun l => {u l,v l}
      (∀ l ∈ T, IsLowMerge n n (fun p t => decide (p ∈ S t)) C (n+n+j.val) l ∧
        u l ∈ S l ∩ (side l 0 \ side l 1) ∧ v l ∈ S l ∩ (side l 1 \ side l 0)) →
      (∀ l ∈ T, ∀ k ∈ T, l ≠ k → Disjoint (pair l) (S k) ∨ Disjoint (pair k) (S l)) → T.card ≤ 7) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → x4.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = Bool.false) → (∀ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x14 → x14.output < x2 + x2 + x14.size → (∀ (x17 x18 : Finset (Fin x2)), x14.eval (PEqualNP.GenericRejection.incidenceInput x17 x18) = x4.eval (PEqualNP.GenericRejection.incidenceInput x17 x18)) → x4.size ≤ x14.size) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  classical
  intro q n S C big order lineCard incidence shape reread out positive negative minimal
  by_contra! tiny
  let merge (j : Fin C.size) (l : Fin n) :=
    IsLowMerge n n (fun p t => decide (p ∈ S t)) C (n+n+j.val) l
  let side (j : Fin C.size) (l : Fin n) (k : ℕ) := aliveSet n n C ((gateAt C j.val).inputs.getD k 0) l
  let left (j : Fin C.size) (l : Fin n) := S l ∩ (side j l 0 \ side j l 1)
  let right (j : Fin C.size) (l : Fin n) := S l ∩ (side j l 1 \ side j l 0)
  let mark (j : Fin C.size) (l : Fin n) := merge j l ∧ (left j l).Nonempty ∧ (right j l).Nonempty
  have per (l : Fin n) : q ≤ (Finset.univ.filter (fun j => mark j l)).card := by
    have h := single n S C l shape (positive l) (fun X hx =>
      negative X {l} (by simp; omega) hx)
    change (S l).card ≤ (Finset.univ.filter (fun j => mark j l)).card+1 at h
    rw [lineCard] at h
    omega
  have many : ∃ j : Fin C.size, 100 < (Finset.univ.filter (mark j)).card := by
    by_contra! h
    have lo : n*q ≤ ∑ l : Fin n, (Finset.univ.filter (fun j => mark j l)).card := by
      simpa using
        Finset.sum_le_sum (s := Finset.univ) (fun l _ => per l)
    have hi : (∑ j : Fin C.size, (Finset.univ.filter (mark j)).card) ≤ C.size*100 := by
      simpa using
        Finset.sum_le_sum (s := Finset.univ) (fun j _ => h j)
    have flip : (∑ l : Fin n, (Finset.univ.filter (fun j => mark j l)).card) =
        ∑ j : Fin C.size, (Finset.univ.filter (mark j)).card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
    rw [flip] at lo
    have bad := lo.trans hi
    rw [Nat.mul_comm C.size 100] at bad
    omega
  obtain ⟨j, hj⟩ := many
  let K := Finset.univ.filter (mark j)
  change 100 < K.card at hj
  have info (l : Fin n) (hl : l ∈ K) : mark j l :=
    (Finset.mem_filter.mp hl).2
  have choices (l : Fin n) : ∃ p r : Fin n, l ∈ K → p ∈ left j l ∧ r ∈ right j l := by
    by_cases hl : l ∈ K
    · obtain ⟨p,hp⟩ := (info l hl).2.1
      obtain ⟨r,hr⟩ := (info l hl).2.2
      exact ⟨p,r,fun _ => ⟨hp,hr⟩⟩
    · exact ⟨l,l,fun h => (hl h).elim⟩
  choose u v labels using choices
  let F (l : Fin n) : Finset (Fin n) := {u l,v l}
  have Fcard (l : Fin n) (hl : l ∈ K) : (F l).card = 2 := by
    have hu := (Finset.mem_sdiff.mp (Finset.mem_inter.mp (labels l hl).1).2).1
    have hv := (Finset.mem_sdiff.mp (Finset.mem_inter.mp (labels l hl).2).2).2
    have ne : u l ≠ v l := fun eq => hv (eq ▸ hu)
    simp [F,ne]
  have degree (p : Fin n) : (K.filter (fun l => p ∈ F l)).card ≤ 7 := by
    let T := K.filter (fun l => p ∈ F l)
    let r (l : Fin n) := if p = u l then v l else u l
    have petals (l : Fin n) (hl : l ∈ T) : merge j l ∧
        ((p ∈ left j l ∧ r l ∈ right j l) ∨ (r l ∈ left j l ∧ p ∈ right j l)) := by
      obtain ⟨hK,hp⟩ := Finset.mem_filter.mp hl
      refine ⟨(info l hK).1,?_⟩
      by_cases e : p = u l
      · exact Or.inl ⟨e.symm ▸ (labels l hK).1,by simpa [r,e] using (labels l hK).2⟩
      · have eq : p = v l := Finset.mem_singleton.mp ((Finset.mem_insert.mp hp).resolve_left e)
        exact Or.inr ⟨by simpa [r,e] using (labels l hK).1, eq.symm ▸ (labels l hK).2⟩
    have geom (l : Fin n) (hl : l ∈ T) : p ∈ S l ∧ r l ∈ S l ∧ p ≠ r l := by
      rcases (petals l hl).2 with ⟨a,b⟩ | ⟨b,a⟩
      · refine ⟨(Finset.mem_inter.mp a).1,(Finset.mem_inter.mp b).1,?_⟩
        have h := (Finset.mem_sdiff.mp (Finset.mem_inter.mp a).2).1
        have k := (Finset.mem_sdiff.mp (Finset.mem_inter.mp b).2).2
        exact fun eq => k (eq ▸ h)
      · refine ⟨(Finset.mem_inter.mp a).1,(Finset.mem_inter.mp b).1,?_⟩
        have h := (Finset.mem_sdiff.mp (Finset.mem_inter.mp a).2).1
        have k := (Finset.mem_sdiff.mp (Finset.mem_inter.mp b).2).2
        exact fun eq => k (eq ▸ h)
    have privateLine (l : Fin n) (hl : l ∈ T) (k : Fin n) (hk : k ∈ T) (tip : r l ∈ S k) : l = k := by
      obtain ⟨t,_,unique⟩ := incidence p (r l) (geom l hl).2.2
      have a := unique l ⟨(geom l hl).1,(geom l hl).2.1⟩
      have b := unique k ⟨(geom k hk).1,tip⟩
      exact a.trans b.symm
    by_cases two : 1 < T.card
    · have past : 2*T.card ≤ j.val+2 := by
        apply position n S C j T r shape two _ privateLine
        intro l hl
        refine ⟨(petals l hl).1,(geom l hl).2.1,?_⟩
        rcases (petals l hl).2 with ⟨_,b⟩ | ⟨a,_⟩
        · exact Or.inr (Finset.mem_sdiff.mp (Finset.mem_inter.mp b).2).1
        · exact Or.inl (Finset.mem_sdiff.mp (Finset.mem_inter.mp a).2).1
      exact pencil q n S C big order lineCard incidence shape reread positive negative minimal tiny j p T r petals privateLine past
    · change T.card ≤ 7
      omega
  let separated (T : Finset (Fin n)) := ∀ l ∈ T, ∀ k ∈ T, l ≠ k → Disjoint (F l) (F k)
  let pack := K.powerset.filter separated
  have empty : ∅ ∈ pack := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by
    intro l hl; exact (Finset.notMem_empty l hl).elim⟩
  obtain ⟨T, hT, largest⟩ := pack.exists_max_image Finset.card ⟨∅,empty⟩
  obtain ⟨hpow, dis⟩ := Finset.mem_filter.mp hT
  have Tsub : T ⊆ K := Finset.mem_powerset.mp hpow
  have Tsize : T.card ≤ 7 := by
    apply matching q n S C big order lineCard incidence shape reread positive negative minimal tiny j T u v
    · intro l hl
      exact ⟨(info l (Tsub hl)).1, labels l (Tsub hl)⟩
    · have onLine (l : Fin n) (hl : l ∈ T) : F l ⊆ S l := by
        intro r hr
        rcases Finset.mem_insert.mp hr with eq | eq
        · rw [eq]; exact (Finset.mem_inter.mp (labels l (Tsub hl)).1).1
        · rw [Finset.mem_singleton.mp eq]; exact (Finset.mem_inter.mp (labels l (Tsub hl)).2).1
      intro l hl k hk ne
      by_cases no : Disjoint (F l) (S k)
      · exact Or.inl no
      · right
        obtain ⟨x,hx,hxk⟩ := Finset.not_disjoint_iff.mp no
        apply Finset.disjoint_left.mpr
        intro y hy hyl
        have diff : x ≠ y := by
          intro eq
          exact Finset.disjoint_left.mp (dis l hl k hk ne) hx (eq.symm ▸ hy)
        obtain ⟨_,_,unique⟩ := incidence x y diff
        exact ne ((unique l ⟨onLine l hl hx,hyl⟩).trans (unique k ⟨hxk,onLine k hk hy⟩).symm)
  let D := T.biUnion F
  have Dsize : D.card ≤ 14 := by
    have same : (∑ l ∈ T, (F l).card) = T.card*2 := by
      calc
        _ = ∑ _l ∈ T, 2 := Finset.sum_congr rfl (fun l hl => Fcard l (Tsub hl))
        _ = _ := by simp
    have h : D.card ≤ ∑ l ∈ T, (F l).card := Finset.card_biUnion_le
    omega
  have cover (k : Fin n) (hk : k ∈ K) : ∃ p ∈ D, p ∈ F k := by
    by_cases mem : k ∈ T
    · obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (F k).card by rw [Fcard k hk]; decide)
      exact ⟨p, Finset.mem_biUnion.mpr ⟨k,mem,hp⟩, hp⟩
    · by_contra miss
      have apart (l : Fin n) (hl : l ∈ T) : Disjoint (F k) (F l) := by
        apply Finset.disjoint_left.mpr
        intro p hp hlp
        exact miss ⟨p, Finset.mem_biUnion.mpr ⟨l,hl,hlp⟩, hp⟩
      have ins : insert k T ∈ pack := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset hk Tsub),?_⟩
        intro l hl v hv ne
        rcases Finset.mem_insert.mp hl with eqL | inL
        · subst l
          rcases Finset.mem_insert.mp hv with eqV | inV
          · exact (ne eqV.symm).elim
          · exact apart v inV
        · rcases Finset.mem_insert.mp hv with eqV | inV
          · subst v
            exact (apart l inL).symm
          · exact dis l inL v inV ne
      have too := largest _ ins
      rw [Finset.card_insert_of_notMem mem] at too
      omega
  have Ksub : K ⊆ D.biUnion (fun p => K.filter (fun l => p ∈ F l)) := by
    intro l hl
    obtain ⟨p,hD,hp⟩ := cover l hl
    exact Finset.mem_biUnion.mpr ⟨p,hD,Finset.mem_filter.mpr ⟨hl,hp⟩⟩
  have small : K.card ≤ D.card*7 := calc
    _ ≤ _ := Finset.card_le_card Ksub
    _ ≤ ∑ p ∈ D, (K.filter (fun l => p ∈ F l)).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ D, 7 := Finset.sum_le_sum (fun p _ => degree p)
    _ = _ := by simp
  omega
