import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.BasicProperties
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

/-!
# Lemma 3: Double counting intersection sizes

This module proves the double-counting bounds for intersection sizes used
in the Marcus-Tardos equal-length sequence theorem.

## Whiteprint node
- `IntersectionCounting`
-/

namespace MarcusTardos

variable {α : Type*} [DecidableEq α] {m : ℕ}

/-- Number of sequences containing symbol `a`. -/
def freq (A : Fin m → List α) (a : α) : ℕ :=
  (Finset.filter (fun i : Fin m => a ∈ A i) Finset.univ).card

/-- Cardinality of intersection of two sequences. -/
def pairIntersection (A : Fin m → List α) (i j : Fin m) : ℕ :=
  ((A i).toFinset ∩ (A j).toFinset).card

/-- Total ordered intersection over all i ≠ j. -/
def totalIntersection (A : Fin m → List α) : ℕ :=
  ∑ ij ∈ Finset.offDiag (Finset.univ : Finset (Fin m)),
    pairIntersection A ij.1 ij.2

/-! ### Double counting identities -/

/-- The sum of symbol frequencies equals the total number of symbol occurrences. -/
lemma freq_sum {d n : ℕ} {alphabet : Finset α} (_hcard : alphabet.card = n)
    {A : Fin m → List α} (hnodup : ∀ i, (A i).Nodup)
    (hlen : ∀ i, (A i).length = d) (halph : ∀ i, ∀ x ∈ A i, x ∈ alphabet) :
    ∑ a ∈ alphabet, freq A a = d * m := by
  have h1 : ∑ a ∈ alphabet, freq A a =
      ∑ i : Fin m, ∑ a ∈ alphabet, (if a ∈ A i then 1 else 0) := by
    calc
      ∑ a ∈ alphabet, freq A a
        = ∑ a ∈ alphabet, ∑ i : Fin m, (if a ∈ A i then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          simp [freq]
      _ = ∑ i : Fin m, ∑ a ∈ alphabet, (if a ∈ A i then 1 else 0) := by
          rw [Finset.sum_comm]
  rw [h1]
  have h2 : ∀ (i : Fin m), ∑ a ∈ alphabet, (if a ∈ A i then 1 else 0) = (A i).length := by
    intro i
    have h3 : ∑ a ∈ alphabet, (if a ∈ A i then 1 else 0) =
        (alphabet.filter (fun a => a ∈ A i)).card := by
      rw [Finset.sum_ite]
      ; simp
    rw [h3]
    have h4 : alphabet.filter (fun a => a ∈ A i) = (A i).toFinset := by
      apply Finset.ext
      intro x
      simp only [Finset.mem_filter, List.mem_toFinset]
      constructor
      · intro h; exact h.2
      · intro hx; exact ⟨halph i x hx, hx⟩
    rw [h4, List.toFinset_card_of_nodup (hnodup i), hlen i]
  have h3 : ∑ i : Fin m, ∑ a ∈ alphabet, (if a ∈ A i then 1 else 0) =
      ∑ i : Fin m, (A i).length := by
    apply Finset.sum_congr rfl
    intro i _
    exact h2 i
  rw [h3]
  have h4 : ∑ i : Fin m, (A i).length = d * m := by
    rw [Finset.sum_congr rfl (fun i _ => hlen i)]
    simp [Finset.sum_const]
    ; ring
  exact h4

/-- For a fixed symbol, count ordered pairs (i,j), i≠j, both containing it. -/
private lemma count_pairs_for_symbol {a : α} {A : Fin m → List α} :
    ∑ ij ∈ Finset.offDiag (Finset.univ : Finset (Fin m)),
      (if a ∈ A ij.1 ∧ a ∈ A ij.2 then 1 else 0) =
    freq A a * (freq A a - 1) := by
  let S := Finset.filter (fun i : Fin m => a ∈ A i) Finset.univ
  have hS : S.card = freq A a := by rfl
  have h_set : Finset.filter (fun ij : Fin m × Fin m => a ∈ A ij.1 ∧ a ∈ A ij.2)
        (Finset.offDiag (Finset.univ : Finset (Fin m))) =
      Finset.offDiag S := by
    ext ⟨i, j⟩
    simp [S, Finset.mem_offDiag, Finset.mem_filter]
    <;> tauto
  have h_sum : ∑ ij ∈ Finset.offDiag (Finset.univ : Finset (Fin m)),
        (if a ∈ A ij.1 ∧ a ∈ A ij.2 then 1 else 0) =
      (Finset.offDiag S).card := by
    rw [Finset.sum_ite]
    ; simp [h_set]
  rw [h_sum]
  have h_eq : (Finset.offDiag S) = (S ×ˢ S) \ Finset.diag S := by
    ext ⟨x, y⟩
    simp [Finset.mem_offDiag, Finset.mem_diag]
    <;> tauto
  rw [h_eq]
  have h5 : Finset.diag S ⊆ S ×ˢ S := by
    intro z hz
    have hz' : z.1 ∈ S ∧ z.1 = z.2 := by
      simpa [Finset.mem_diag] using hz
    have h1 : z.1 ∈ S := hz'.1
    have h2 : z.2 ∈ S := by rw [←hz'.2]; exact h1
    exact Finset.mem_product.mpr ⟨h1, h2⟩
  have h6 : (Finset.diag S).card = S.card := by
    have h7 : Finset.diag S = Finset.image (fun x : Fin m => (x, x)) S := by
      ext p
      simp only [Finset.mem_diag, Finset.mem_image]
      constructor
      · rintro ⟨h1, h2⟩
        refine' ⟨p.1, h1, _⟩
        have h3 : (p.1, p.1) = p := by
          ext <;> simp [h2]
        exact h3
      · rintro ⟨x, hx, hxy⟩
        have h1 : p.1 = x := by
          simp [Prod.ext_iff] at hxy ⊢ <;> tauto
        have h2 : p.2 = x := by
          simp [Prod.ext_iff] at hxy ⊢ <;> tauto
        exact ⟨by rw [h1]; exact hx, by rw [h1, h2]⟩
    rw [h7, Finset.card_image_of_injective _ (fun a b h => by simp_all)]
  have h_card : ((S ×ˢ S) \ Finset.diag S).card = (S ×ˢ S).card - (Finset.diag S).card :=
    Finset.card_sdiff_of_subset h5
  have h_arith : ∀ (x : ℕ), x * x - x = x * (x - 1) := by
    intro x
    by_cases h : x = 0
    · simp [h]
    · have hpos : 0 < x := by omega
      have h7 : x * (x - 1) = x * x - x := by
        rw [Nat.mul_sub_left_distrib] <;> omega
      exact h7.symm
  rw [h_card, Finset.card_product, h6, hS]
  exact h_arith (freq A a)

/-- Total intersection equals sum over symbols of freq*(freq-1). -/
lemma totalIntersection_eq {d n : ℕ} {alphabet : Finset α} (_hcard : alphabet.card = n)
    {A : Fin m → List α} (hnodup : ∀ i, (A i).Nodup)
    (hlen : ∀ i, (A i).length = d) (halph : ∀ i, ∀ x ∈ A i, x ∈ alphabet) :
    totalIntersection A = ∑ a ∈ alphabet, freq A a * (freq A a - 1) := by
  have h1 : ∀ (i j : Fin m), ((A i).toFinset ∩ (A j).toFinset).card =
      ∑ a ∈ alphabet, (if a ∈ A i ∧ a ∈ A j then 1 else 0) := by
    intro i j
    let I := (A i).toFinset ∩ (A j).toFinset
    have h2 : I ⊆ alphabet := by
      intro x hx
      have h4 : x ∈ (A i).toFinset := (Finset.mem_inter.mp hx).1
      exact halph i x (List.mem_toFinset.mp h4)
    have h3 : I.card = ∑ a ∈ alphabet, (if a ∈ I then 1 else 0) := by
      have h4 : ∑ a ∈ alphabet, (if a ∈ I then 1 else 0) =
          (alphabet.filter (fun a => a ∈ I)).card := by
        rw [Finset.sum_ite] <;> simp
      rw [h4]
      have h5 : alphabet.filter (fun a => a ∈ I) = I := by
        apply Finset.ext
        intro x
        simp only [Finset.mem_filter]
        constructor
        · intro h; exact h.2
        · intro hx; exact ⟨h2 hx, hx⟩
      rw [h5]
    simpa [I, Finset.mem_inter] using h3
  calc
    totalIntersection A
      = ∑ ij ∈ Finset.offDiag (Finset.univ : Finset (Fin m)),
          ((A ij.1).toFinset ∩ (A ij.2).toFinset).card := by rfl
    _ = ∑ ij ∈ Finset.offDiag (Finset.univ : Finset (Fin m)),
          ∑ a ∈ alphabet, (if a ∈ A ij.1 ∧ a ∈ A ij.2 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro ij _
        exact h1 ij.1 ij.2
    _ = ∑ a ∈ alphabet, ∑ ij ∈ Finset.offDiag (Finset.univ : Finset (Fin m)),
          (if a ∈ A ij.1 ∧ a ∈ A ij.2 then 1 else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ a ∈ alphabet, freq A a * (freq A a - 1) := by
        apply Finset.sum_congr rfl
        intro a _
        exact count_pairs_for_symbol

/-! ### Lemma 3a: Lower bound on total intersection -/

/-- Cast identity: `↑(x * (x - 1)) = (x : Real)^2 - (x : Real)`. -/
private lemma cast_mul_sub_one (x : ℕ) :
    (↑(x * (x - 1)) : Real) = (x : Real)^2 - (x : Real) := by
  by_cases h : x = 0
  · simp [h]
  · have hpos : 0 < x := by omega
    have h1 : (↑(x - 1) : Real) = (x : Real) - 1 := by
      rw [Nat.cast_sub hpos] <;> norm_num
    rw [Nat.cast_mul, h1]
    <;> ring

/-- Cancel common nonzero factor in division: `a * b / a = b`. -/
private lemma cancel_mul_div (a b : Real) (ha : a ≠ 0) : a * b / a = b := by
  have h1 : (a * b / a) * a = a * b := by
    rw [div_mul_cancel₀ _ ha]
  have h2 : a * (a * b / a) = a * b := by
    have h3 : a * (a * b / a) = (a * b / a) * a := by ring
    rw [h3, h1]
  exact (mul_right_inj' ha).mp h2

/-- Cancel common nonzero factor: `a * (b / a) = b`. -/
private lemma mul_div_cancel (a b : Real) (ha : a ≠ 0) : a * (b / a) = b := by
  have h1 : (b / a) * a = b := div_mul_cancel₀ b ha
  have h2 : a * (b / a) = (b / a) * a := by ring
  rw [h2, h1]

/-- Lemma 3a: If `d * m > 2 * n`, then total intersection is at least `d² * m² / (2n)`. -/
lemma totalIntersection_lower_bound {d n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {alphabet : Finset α} (hcard : alphabet.card = n)
    {A : Fin m → List α} (hnodup : ∀ i, (A i).Nodup)
    (hlen : ∀ i, (A i).length = d) (halph : ∀ i, ∀ x ∈ A i, x ∈ alphabet)
    (h : d * m > 2 * n) :
    (totalIntersection A : Real) ≥ (d : Real)^2 * (m : Real)^2 / (2 * (n : Real)) := by
  set p : ℕ := totalIntersection A with hp
  have h_freq_sum : ∑ a ∈ alphabet, freq A a = d * m :=
    freq_sum hcard hnodup hlen halph
  have h_eq_nat : p = ∑ a ∈ alphabet, freq A a * (freq A a - 1) :=
    totalIntersection_eq hcard hnodup hlen halph
  have h_p_eq : (p : Real) = ∑ a ∈ alphabet, ((freq A a : Real)^2 - (freq A a : Real)) := by
    rw [h_eq_nat]
    have h : (↑(∑ a ∈ alphabet, freq A a * (freq A a - 1)) : Real) =
        ∑ a ∈ alphabet, (↑(freq A a * (freq A a - 1)) : Real) := by
      rw [Nat.cast_sum]
    rw [h]
    apply Finset.sum_congr rfl
    intro a _
    exact cast_mul_sub_one (freq A a)
  rw [h_p_eq]
  have h_cs : (∑ a ∈ alphabet, (freq A a : Real))^2 ≤
      (alphabet.card : Real) * ∑ a ∈ alphabet, (freq A a : Real)^2 :=
    sq_sum_le_card_mul_sum_sq (s := alphabet) (f := fun a => (freq A a : Real))
  have h_sum : (∑ a ∈ alphabet, (freq A a : Real)) = ((d : Real) * (m : Real)) := by
    exact_mod_cast h_freq_sum
  have hn' : (n : Real) > 0 := by exact_mod_cast hn
  rw [h_sum] at h_cs
  rw [hcard] at h_cs
  have h5 : ((d : Real) * (m : Real))^2 ≤ (n : Real) * ∑ a ∈ alphabet, (freq A a : Real)^2 := h_cs
  have h_dm : (d : Real) * (m : Real) > 2 * (n : Real) := by exact_mod_cast h
  have hn_pos : (n : Real) > 0 := by exact_mod_cast hn
  have h_dm_pos : 0 < (d : Real) * (m : Real) := by linarith
  have h4 : ∑ a ∈ alphabet, (freq A a : Real)^2 ≥
      ((d : Real) * (m : Real))^2 / (n : Real) := by
    have h6 : (((d : Real) * (m : Real))^2) / (n : Real) ≤
        ((n : Real) * ∑ a ∈ alphabet, (freq A a : Real)^2) / (n : Real) := by gcongr
    have h7 : ((n : Real) * ∑ a ∈ alphabet, (freq A a : Real)^2) / (n : Real) =
        ∑ a ∈ alphabet, (freq A a : Real)^2 :=
      cancel_mul_div (n : Real) (∑ a ∈ alphabet, (freq A a : Real)^2) (ne_of_gt hn_pos)
    rw [h7] at h6
    exact h6
  have h_step3 : ((d : Real) * (m : Real))^2 / (n : Real) - ((d : Real) * (m : Real)) ≥
      ((d : Real) * (m : Real))^2 / (2 * (n : Real)) := by
    set Y : Real := (d : Real) * (m : Real) with hY
    set X : Real := Y^2 with hX_def
    have h_ineq : X ≥ 2 * (n : Real) * Y := by
      rw [hX_def]
      nlinarith
    have h_pos2 : 0 < 2 * (n : Real) := by positivity
    have h5 : 2 * (n : Real) * (X / (n : Real)) = 2 * X := by
      have h51 : (n : Real) * (X / (n : Real)) = X :=
        mul_div_cancel (n : Real) X (ne_of_gt hn_pos)
      calc
        2 * (n : Real) * (X / (n : Real))
          = 2 * ((n : Real) * (X / (n : Real))) := by ring
        _ = 2 * X := by rw [h51]
    have h6 : 2 * (n : Real) * (X / (2 * (n : Real))) = X :=
      mul_div_cancel (2 * (n : Real)) X (ne_of_gt h_pos2)
    have h7 : 2 * (n : Real) * (X / (n : Real) - Y) ≥ 2 * (n : Real) * (X / (2 * (n : Real))) := by
      rw [mul_sub, h5, h6]
      linarith [h_ineq]
    by_contra h9
    have h10 : X / (n : Real) - Y < X / (2 * (n : Real)) := by linarith
    have h11 : 2 * (n : Real) * (X / (n : Real) - Y) < 2 * (n : Real) * (X / (2 * (n : Real))) :=
      mul_lt_mul_of_pos_left h10 h_pos2
    linarith
  calc
    ∑ a ∈ alphabet, ((freq A a : Real)^2 - (freq A a : Real))
      = (∑ a ∈ alphabet, (freq A a : Real)^2) - ∑ a ∈ alphabet, (freq A a : Real) := by
        rw [Finset.sum_sub_distrib]
    _ ≥ ((d : Real) * (m : Real))^2 / (n : Real) - ((d : Real) * (m : Real)) := by
        rw [h_sum]
        <;> linarith [h4]
    _ ≥ ((d : Real) * (m : Real))^2 / (2 * (n : Real)) := h_step3
    _ = (d : Real)^2 * (m : Real)^2 / (2 * (n : Real)) := by ring

/-! ### Lemma 3b: Cauchy-Schwarz lower bound on sum of squares -/

/-- Lemma 3b: Sum of squared pairwise intersections is at least `p² / m²`. -/
lemma sum_sq_pairIntersection_lower_bound (hm : 0 < m)
    {A : Fin m → List α} :
    ∑ ij ∈ Finset.offDiag (Finset.univ : Finset (Fin m)),
      (pairIntersection A ij.1 ij.2 : Real)^2 ≥
    (∑ ij ∈ Finset.offDiag (Finset.univ : Finset (Fin m)),
      (pairIntersection A ij.1 ij.2 : Real))^2 / (m : Real)^2 := by
  let s := Finset.offDiag (Finset.univ : Finset (Fin m))
  let f : (Fin m × Fin m) → Real := fun ij => (pairIntersection A ij.1 ij.2 : Real)
  by_cases h_m1 : m ≤ 1
  · -- m = 1 (since hm : 0 < m)
    have h_m_eq_1 : m = 1 := by omega
    subst h_m_eq_1
    have h_s_empty : s = ∅ := by
      ext ⟨i, j⟩
      simp [s, Finset.mem_offDiag, Fin.ext_iff]
      <;> decide
    have h_goal : ∑ ij ∈ s, (f ij)^2 ≥ (∑ ij ∈ s, f ij)^2 / (1 : Real)^2 := by
      rw [h_s_empty]
      <;> simp
    simpa [s, f] using h_goal
  · -- m ≥ 2
    have h_m2 : m ≥ 2 := by omega
    let i : Fin m := ⟨0, by omega⟩
    let j : Fin m := ⟨1, by omega⟩
    have hne : i ≠ j := by
      intro h
      have h' : i.val = j.val := by rw [h]
      simp [i, j] at h' <;> omega
    have h_in : (i, j) ∈ s := by
      simp [s, Finset.mem_offDiag, hne]
    have h_card_pos : 0 < s.card := Finset.card_pos.mpr ⟨(i, j), h_in⟩
    have h_cs : (∑ ij ∈ s, f ij)^2 ≤ (s.card : Real) * ∑ ij ∈ s, (f ij)^2 :=
      sq_sum_le_card_mul_sum_sq (s := s) (f := f)
    have h_card_le : s.card ≤ m * m := by
      have h : s ⊆ (Finset.univ : Finset (Fin m)) ×ˢ (Finset.univ : Finset (Fin m)) := by
        intro p hp
        simp only [Finset.mem_product, Finset.mem_univ]
        <;> exact ⟨trivial, trivial⟩
      have h' : s.card ≤ ((Finset.univ : Finset (Fin m)) ×ˢ (Finset.univ : Finset (Fin m))).card :=
        Finset.card_le_card h
      simpa [Finset.card_product] using h'
    have h_card_le' : (s.card : Real) ≤ (m : Real)^2 := by
      have h : (s.card : Real) ≤ ↑(m * m) := by exact_mod_cast h_card_le
      have h2 : (↑(m * m) : Real) = (m : Real)^2 := by
        simp <;> ring
      rw [h2] at h
      exact h
    have hpos : (s.card : Real) > 0 := by exact_mod_cast h_card_pos
    have h1 : (∑ ij ∈ s, (f ij)^2) ≥ (∑ ij ∈ s, f ij)^2 / (s.card : Real) := by
      have h_pos : 0 < (s.card : Real) := by exact_mod_cast h_card_pos
      have h : (∑ ij ∈ s, f ij)^2 ≤ (s.card : Real) * ∑ ij ∈ s, (f ij)^2 := h_cs
      have h_div : (∑ ij ∈ s, f ij)^2 / (s.card : Real) ≤
          ((s.card : Real) * ∑ ij ∈ s, (f ij)^2) / (s.card : Real) := by gcongr
      have h_cancel : ((s.card : Real) * ∑ ij ∈ s, (f ij)^2) / (s.card : Real) =
          ∑ ij ∈ s, (f ij)^2 :=
        cancel_mul_div (s.card : Real) (∑ ij ∈ s, (f ij)^2) (ne_of_gt h_pos)
      rw [h_cancel] at h_div
      exact h_div
    have h_main : ∑ ij ∈ s, (f ij)^2 ≥ (∑ ij ∈ s, f ij)^2 / (m : Real)^2 := by
      calc
        ∑ ij ∈ s, (f ij)^2
          ≥ (∑ ij ∈ s, f ij)^2 / (s.card : Real) := h1
        _ ≥ (∑ ij ∈ s, f ij)^2 / (m : Real)^2 := by
            gcongr <;> linarith
    exact h_main

end MarcusTardos
