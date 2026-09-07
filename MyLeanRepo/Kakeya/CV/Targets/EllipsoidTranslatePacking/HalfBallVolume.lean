import MyLeanRepo.Kakeya.CV.Targets.EllipsoidTranslatePacking.VolumeScaling
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Half-ball volume and ENNReal packing arithmetic

Auxiliary volume and arithmetic lemmas for the finite translate packing
argument.

## Main results

- `volume_closedBall_scaling`: volume of a radius-`r` ball scales as `r^3`.
- `volume_halfBall`: the half-radius ball has `1/8` of the unit ball volume.
- `packing_upper_bound_div`, `packing_lower_bound_div`: ENNReal arithmetic
  helpers converting packing density inequalities into bounds on `n`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace Kakeya.CV

/-- Volume of a closed ball of radius `r` scales as `r^3` relative to the unit ball. -/
lemma volume_closedBall_scaling (r : ℝ) (hr : 0 ≤ r) :
    volume (Metric.closedBall (0 : Point 3) r) =
      ENNReal.ofReal (r ^ 3) * volume (unitBall 3) := by
  have h_main : volume (Metric.closedBall (0 : Point 3) r) =
      ENNReal.ofReal (r ^ Module.finrank ℝ (Point 3)) * volume (Metric.closedBall (0 : Point 3) 1) :=
    MeasureTheory.Measure.addHaar_closedBall' volume (0 : Point 3) hr
  have h_finrank : Module.finrank ℝ (Point 3) = 3 := by simp
  rw [h_main, h_finrank]
  <;> rfl

/-- The half-radius closed ball has one eighth the volume of the unit ball. -/
lemma volume_halfBall :
    volume (Metric.closedBall (0 : Point 3) (1 / 2 : ℝ)) =
      (1 / 8 : ℝ≥0∞) * volume (unitBall 3) := by
  rw [volume_closedBall_scaling (1 / 2 : ℝ) (by norm_num)]
  have h1 : (1 / 2 : ℝ) ^ 3 = (1 / 8 : ℝ) := by norm_num
  rw [h1]
  have h2 : ENNReal.ofReal (1 / 8 : ℝ) = (1 / 8 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 8)]
    <;> simp
  rw [h2]

/-- Given `n * V ≤ B`, derive `n ≤ B / V` in `ℝ≥0∞`. -/
lemma packing_upper_bound_div {n : ℕ} {V B : ℝ≥0∞}
    (hV_pos : V ≠ 0) (hV_lt_top : V ≠ ⊤)
    (h : (n : ℝ≥0∞) * V ≤ B) :
    (n : ℝ≥0∞) ≤ B / V := by
  have h_iff : (n : ℝ≥0∞) ≤ B / V ↔ (n : ℝ≥0∞) * V ≤ B :=
    ENNReal.le_div_iff_mul_le (Or.inl hV_pos) (Or.inl hV_lt_top)
  exact h_iff.mpr h

/-- Given `(1/8) * B ≤ n * (8 * V)`, derive `B / V ≤ 64 * n` in `ℝ≥0∞`. -/
lemma packing_lower_bound_div {n : ℕ} {V B : ℝ≥0∞}
    (hV_pos : V ≠ 0) (hV_lt_top : V ≠ ⊤)
    (_hB_lt_top : B ≠ ⊤)
    (h : (1 / 8 : ℝ≥0∞) * B ≤ (n : ℝ≥0∞) * (8 * V)) :
    B / V ≤ (64 : ℝ≥0∞) * (n : ℝ≥0∞) := by
  have h1 : (1 / 8 : ℝ≥0∞) * B ≤ (8 : ℝ≥0∞) * ((n : ℝ≥0∞) * V) := by
    have h2 : (n : ℝ≥0∞) * (8 * V) = (8 : ℝ≥0∞) * ((n : ℝ≥0∞) * V) := by
      ring
    rw [h2] at h
    exact h
  have h8_pos : (8 : ℝ≥0∞) ≠ 0 := by norm_num
  have h8_top : (8 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h_inv : (1 / 8 : ℝ≥0∞) = (8 : ℝ≥0∞)⁻¹ := by
    have h_div : (1 / 8 : ℝ≥0∞) = (1 : ℝ≥0∞) * (8 : ℝ≥0∞)⁻¹ := by
      rw [div_eq_mul_inv]
    rw [h_div, one_mul]
  have h4 : (8 : ℝ≥0∞) * ((1 / 8 : ℝ≥0∞) * B) = B := by
    rw [h_inv]
    exact ENNReal.mul_inv_cancel_left h8_pos h8_top
  have h5 : (8 : ℝ≥0∞) * ((1 / 8 : ℝ≥0∞) * B) ≤
      (8 : ℝ≥0∞) * ((8 : ℝ≥0∞) * ((n : ℝ≥0∞) * V)) := by
    gcongr
  have h3 : B ≤ (8 : ℝ≥0∞) * ((8 : ℝ≥0∞) * ((n : ℝ≥0∞) * V)) := by
    rw [h4] at h5
    exact h5
  have h6 : (8 : ℝ≥0∞) * ((8 : ℝ≥0∞) * ((n : ℝ≥0∞) * V)) =
      ((64 : ℝ≥0∞) * (n : ℝ≥0∞)) * V := by
    ring
  rw [h6] at h3
  have h_iff : B / V ≤ (64 : ℝ≥0∞) * (n : ℝ≥0∞) ↔
      B ≤ ((64 : ℝ≥0∞) * (n : ℝ≥0∞)) * V :=
    ENNReal.div_le_iff hV_pos hV_lt_top
  exact h_iff.mpr h3

end Kakeya.CV
