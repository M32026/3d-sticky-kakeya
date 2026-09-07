import MyLeanRepo.Kakeya.CV.Targets.ManyBisections.AffineTools
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Volume scaling lemmas for ellipsoid translate packing

Provides the volume scaling factor for doubled ellipsoids and positivity /
finiteness of the unit ball volume, which are needed for the finite translate
packing argument.

## Main results

- `volume_scaledEllipsoid_double`: volume scales by `8` when `η` is doubled.
- `volume_scaledEllipsoid_pos`: a non-degenerate scaled ellipsoid has positive volume.
- `volume_unitBall_pos` / `volume_unitBall_lt_top`: the unit ball has positive,
  finite volume.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace Kakeya.CV

/-- The volume of the unit ball in `Point 3` is positive. -/
lemma volume_unitBall_pos : 0 < volume (unitBall 3) := by
  have h_int : (interior (unitBall 3)).Nonempty := by
    refine' ⟨(0 : Point 3), _⟩
    have h : Metric.ball (0 : Point 3) 1 ⊆ interior (unitBall 3) :=
      Metric.ball_subset_interior_closedBall
    exact h (Metric.mem_ball_self (by norm_num))
  exact Measure.measure_pos_of_nonempty_interior volume h_int

/-- The volume of the unit ball in `Point 3` is finite. -/
lemma volume_unitBall_lt_top : volume (unitBall 3) < ⊤ :=
  Metric.isBounded_closedBall.measure_lt_top

/-- Volume of a scaled ellipsoid doubles in each dimension, so scaling `η` by `2`
multiplies the volume by `8`. -/
lemma volume_scaledEllipsoid_double (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ)
    (hη : 0 < η) (z : Point 3) :
    volume (scaledEllipsoid A (2 * η) z) = 8 * volume (scaledEllipsoid A η z) := by
  have h_pos2 : 0 < 2 * η := by positivity
  set detA := |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)| with hdetA
  have hdetA_nonneg : 0 ≤ detA := abs_nonneg _
  rw [volume_affine_ball A (2 * η) h_pos2 z, volume_affine_ball A η hη z]
  have h1 : (2 * η) ^ 3 * detA = 8 * (η ^ 3 * detA) := by ring
  rw [h1]
  have h_nonneg1 : 0 ≤ (8 : ℝ) := by norm_num
  have h_nonneg2 : 0 ≤ η ^ 3 * detA := by positivity
  have h2 : ENNReal.ofReal (8 * (η ^ 3 * detA)) =
      (8 : ENNReal) * ENNReal.ofReal (η ^ 3 * detA) := by
    have h3 : ENNReal.ofReal (8 * (η ^ 3 * detA)) =
        ENNReal.ofReal (8 : ℝ) * ENNReal.ofReal (η ^ 3 * detA) :=
      ENNReal.ofReal_mul h_nonneg1
    rw [h3]
    have h4 : ENNReal.ofReal (8 : ℝ) = (8 : ENNReal) := by norm_cast
    rw [h4]
  rw [h2, mul_assoc]

/-- A non-degenerate scaled ellipsoid has positive volume. -/
lemma volume_scaledEllipsoid_pos (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ)
    (hη : 0 < η) (z : Point 3) :
    0 < volume (scaledEllipsoid A η z) := by
  rw [volume_affine_ball A η hη z]
  have hdet_ne_zero : LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3) ≠ 0 :=
    (LinearEquiv.isUnit_det' A).ne_zero
  have hdet_abs_pos : 0 < |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)| :=
    abs_pos.mpr hdet_ne_zero
  have h_factor_pos : 0 < η ^ 3 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)| :=
    mul_pos (pow_pos hη 3) hdet_abs_pos
  have h1 : 0 < ENNReal.ofReal (η ^ 3 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) :=
    ENNReal.ofReal_pos.mpr h_factor_pos
  have h2 : 0 < volume (unitBall 3) := volume_unitBall_pos
  exact ENNReal.mul_pos h1.ne' h2.ne'

end Kakeya.CV
