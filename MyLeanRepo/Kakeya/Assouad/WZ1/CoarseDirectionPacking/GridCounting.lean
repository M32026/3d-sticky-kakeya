import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Grid cell counting infrastructure for WZ1 coarse direction packing
-/

noncomputable section

open Real

namespace Kakeya.Assouad

/-- 1D grid bound. -/
lemma grid1d_bounded {R h : ℝ} (hR : 0 ≤ R) (hh : 0 < h)
    {x : ℝ} (hx : |x| ≤ R) (n : ℕ) (hn : Nat.ceil (R / h) = n) :
    Int.floor (x / h) ∈ Set.Icc (-(n : ℤ)) (n : ℤ) := by
  have hn' : (R / h : ℝ) ≤ (n : ℝ) := by
    rw [←hn]
    exact Nat.le_ceil (R / h)
  have h1 : x ≤ R := (abs_le.mp hx).2
  have h2 : -R ≤ x := (abs_le.mp hx).1
  have hpos : x / h ≤ (n : ℝ) := by
    have h3 : x / h ≤ R / h := div_le_div_of_nonneg_right h1 hh.le
    linarith
  have hneg : (-(n : ℝ)) ≤ x / h := by
    have h3 : -R / h ≤ x / h := div_le_div_of_nonneg_right h2 hh.le
    have h4 : -(n : ℝ) ≤ -R / h := by
      have h5 : -(n : ℝ) ≤ -(R / h) := by gcongr
      have h6 : -(R / h) = -R / h := by ring
      rw [h6] at h5
      exact h5
    linarith
  have hpos' : x / h < (n : ℝ) + 1 := by linarith
  have hupper : Int.floor (x / h) ≤ (n : ℤ) := by
    have h_iff : Int.floor (x / h) ≤ (n : ℤ) ↔ x / h < ((n : ℤ) : ℝ) + 1 :=
      Int.floor_le_iff (a := x / h) (z := (n : ℤ))
    exact h_iff.mpr hpos'
  have hlower : (-(n : ℤ)) ≤ Int.floor (x / h) := by
    apply Int.le_floor.mpr
    have h10 : (↑(-(n : ℤ)) : ℝ) = -(n : ℝ) := by simp
    rw [h10]
    exact hneg
  exact ⟨hlower, hupper⟩

/-- Same-cell closeness in 1D. -/
lemma grid1d_close {h : ℝ} (hh : 0 < h) {x y : ℝ}
    (hcell : Int.floor (x / h) = Int.floor (y / h)) :
    |x - y| < h := by
  set k : ℤ := Int.floor (x / h) with hk_def
  have hxk : (k : ℝ) ≤ x / h := Int.floor_le (x / h)
  have hyk : (k : ℝ) ≤ y / h := by
    have h_eq : k = Int.floor (y / h) := hcell
    rw [h_eq]
    exact Int.floor_le (y / h)
  have hxk' : x / h < (k : ℝ) + 1 := by
    have h_iff : Int.floor (x / h) ≤ k ↔ x / h < (k : ℝ) + 1 :=
      Int.floor_le_iff (a := x / h) (z := k)
    exact h_iff.mp (by simp [hk_def])
  have hyk' : y / h < (k : ℝ) + 1 := by
    have h_eq : k = Int.floor (y / h) := hcell
    have h_iff : Int.floor (y / h) ≤ k ↔ y / h < (k : ℝ) + 1 :=
      Int.floor_le_iff (a := y / h) (z := k)
    have h_le : Int.floor (y / h) ≤ k := by
      exact h_eq ▸ le_refl k
    exact h_iff.mp h_le
  have hdiff : |x / h - y / h| < 1 := by
    rw [abs_lt] <;> constructor <;> linarith
  have h_eq2 : x - y = (x / h - y / h) * h := by
    field_simp [hh.ne'] <;> ring
  have h_abs : |x - y| = |x / h - y / h| * h := by
    rw [h_eq2, abs_mul, abs_of_pos hh] <;> ring
  rw [h_abs]
  have h_final : |x / h - y / h| * h < h := by
    have h' : |x / h - y / h| * h < 1 * h := mul_lt_mul_of_pos_right hdiff hh
    rw [one_mul] at h'
    exact h'
  exact h_final

/-- Axial cell: partition `[0,1]` into 4 quarters. -/
def axialCell (t : ℝ) : ℕ :=
  if t < 1 / 4 then 0
  else if t < 1 / 2 then 1
  else if t < 3 / 4 then 2
  else 3

/-- Characterize `axialCell t = 0`. -/
lemma axialCell_eq_zero {t : ℝ} : axialCell t = 0 ↔ t < 1 / 4 := by
  constructor
  · intro h
    by_cases h1 : t < 1 / 4
    · exact h1
    · have h2 : axialCell t ≠ 0 := by
        unfold axialCell
        rw [if_neg h1]
        split_ifs <;> norm_num
      contradiction
  · intro h
    unfold axialCell
    rw [if_pos h]

/-- Characterize `axialCell t = 1`. -/
lemma axialCell_eq_one {t : ℝ} : axialCell t = 1 ↔ 1 / 4 ≤ t ∧ t < 1 / 2 := by
  constructor
  · intro h
    have h1 : ¬(t < 1 / 4) := by
      by_contra h2
      unfold axialCell at h
      rw [if_pos h2] at h <;> norm_num at h
    have h2 : t < 1 / 2 := by
      by_contra h3
      have h4 : ¬(t < 1 / 2) := by linarith
      unfold axialCell at h
      rw [if_neg h1, if_neg h4] at h
      split_ifs at h <;> norm_num at h
    exact ⟨by linarith, h2⟩
  · rintro ⟨h1, h2⟩
    have h3 : ¬(t < 1 / 4) := by linarith
    unfold axialCell
    rw [if_neg h3, if_pos h2]

/-- Characterize `axialCell t = 2`. -/
lemma axialCell_eq_two {t : ℝ} : axialCell t = 2 ↔ 1 / 2 ≤ t ∧ t < 3 / 4 := by
  constructor
  · intro h
    have h1 : ¬(t < 1 / 4) := by
      by_contra h2
      unfold axialCell at h
      rw [if_pos h2] at h <;> norm_num at h
    have h2 : ¬(t < 1 / 2) := by
      by_contra h3
      unfold axialCell at h
      rw [if_neg h1, if_pos h3] at h <;> norm_num at h
    have h3 : t < 3 / 4 := by
      by_contra h4
      have h5 : ¬(t < 3 / 4) := by linarith
      unfold axialCell at h
      rw [if_neg h1, if_neg h2, if_neg h5] at h
      norm_num at h
    exact ⟨by linarith, h3⟩
  · rintro ⟨h1, h2⟩
    have h3 : ¬(t < 1 / 4) := by linarith
    have h4 : ¬(t < 1 / 2) := by linarith
    unfold axialCell
    rw [if_neg h3, if_neg h4, if_pos h2]

/-- Characterize `axialCell t = 3`. -/
lemma axialCell_eq_three {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    axialCell t = 3 ↔ 3 / 4 ≤ t := by
  constructor
  · intro h
    have h1 : ¬(t < 1 / 4) := by
      by_contra h2
      unfold axialCell at h
      rw [if_pos h2] at h <;> norm_num at h
    have h2 : ¬(t < 1 / 2) := by
      by_contra h3
      unfold axialCell at h
      rw [if_neg h1, if_pos h3] at h <;> norm_num at h
    have h3 : ¬(t < 3 / 4) := by
      by_contra h4
      unfold axialCell at h
      rw [if_neg h1, if_neg h2, if_pos h4] at h <;> norm_num at h
    linarith
  · intro h1
    have h2 : ¬(t < 1 / 4) := by linarith
    have h3 : ¬(t < 1 / 2) := by linarith
    have h4 : ¬(t < 3 / 4) := by linarith
    unfold axialCell
    rw [if_neg h2, if_neg h3, if_neg h4]

/-- If `t₁, t₂ ∈ [0,1]` have the same `axialCell`, then `|t₁ - t₂| ≤ 1/4`. -/
lemma axialCell_close {t1 t2 : ℝ} (ht1 : t1 ∈ Set.Icc (0 : ℝ) 1)
    (ht2 : t2 ∈ Set.Icc (0 : ℝ) 1)
    (hcell : axialCell t1 = axialCell t2) :
    |t1 - t2| ≤ 1 / 4 := by
  have h11 : 0 ≤ t1 := ht1.1
  have h12 : t1 ≤ 1 := ht1.2
  have h21 : 0 ≤ t2 := ht2.1
  have h22 : t2 ≤ 1 := ht2.2
  have h_main : axialCell t1 = 0 ∨ axialCell t1 = 1 ∨ axialCell t1 = 2 ∨ axialCell t1 = 3 := by
    have h : axialCell t1 < 4 := by
      simp [axialCell] <;> split_ifs <;> norm_num
    omega
  rcases h_main with (h | h | h | h)
  · -- cell 0
    have ht1' : t1 < 1 / 4 := axialCell_eq_zero.mp h
    have h2 : axialCell t2 = 0 := by rw [←hcell, h]
    have ht2' : t2 < 1 / 4 := axialCell_eq_zero.mp h2
    rw [abs_le] <;> constructor <;> linarith
  · -- cell 1
    have ht1' : 1 / 4 ≤ t1 ∧ t1 < 1 / 2 := axialCell_eq_one.mp h
    have h2 : axialCell t2 = 1 := by rw [←hcell, h]
    have ht2' : 1 / 4 ≤ t2 ∧ t2 < 1 / 2 := axialCell_eq_one.mp h2
    rw [abs_le] <;> constructor <;> linarith
  · -- cell 2
    have ht1' : 1 / 2 ≤ t1 ∧ t1 < 3 / 4 := axialCell_eq_two.mp h
    have h2 : axialCell t2 = 2 := by rw [←hcell, h]
    have ht2' : 1 / 2 ≤ t2 ∧ t2 < 3 / 4 := axialCell_eq_two.mp h2
    rw [abs_le] <;> constructor <;> linarith
  · -- cell 3
    have ht1' : 3 / 4 ≤ t1 := (axialCell_eq_three ht1).mp h
    have h2 : axialCell t2 = 3 := by rw [←hcell, h]
    have ht2' : 3 / 4 ≤ t2 := (axialCell_eq_three ht2).mp h2
    rw [abs_le] <;> constructor <;> linarith [ht1.2, ht2.2]

/-- Number of integer values in `Finset.Icc (-(n : ℤ)) (n : ℤ)`. -/
lemma int_interval_card (n : ℕ) :
    (Finset.Icc (-(n : ℤ)) (n : ℤ)).card = 2 * n + 1 := by
  rw [Int.card_Icc]
  have h : ((n : ℤ) + 1 - (-(n : ℤ))) = 2 * (n : ℤ) + 1 := by ring
  rw [h]
  have hnonneg : 0 ≤ 2 * (n : ℤ) + 1 := by positivity
  have h3 : ((2 * (n : ℤ) + 1).toNat : ℤ) = 2 * (n : ℤ) + 1 := Int.toNat_of_nonneg hnonneg
  exact_mod_cast h3

end Kakeya.Assouad
