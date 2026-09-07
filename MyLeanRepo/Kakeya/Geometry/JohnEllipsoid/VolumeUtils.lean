import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Basic
import Mathlib.Tactic

/-! # Volume and measure utilities for ellipsoids

This module provides lemmas about the volume of ellipsoids and related sets
in finite-dimensional Euclidean space.

## Main results

- `volume_ellipsoid_eq`: volume of an ellipsoid equals `|det A|` times the volume of the unit ball
- `volume_ellipsoid_pos`: ellipsoid volume is positive (for invertible `A`)
- `volume_ellipsoid_le_iff`: comparison of ellipsoid volumes reduces to determinant comparison
- `volume_ball_pos`: volume of the unit closed ball is positive (for `n > 0`)
- `volume_homothety`: volume scaling under homothety by `r` is `|r|^n`

## Key Mathlib facts

- `Measure.addHaar_image_continuousLinearMap`: linear map image scales measure by `|det|`
- `measure_preimage_add`: translation invariance of Haar measure
- `Metric.measure_closedBall_pos`: positive measure of closed balls
-/

open MeasureTheory
open scoped Pointwise Real

namespace JohnEllipsoid

section VolumeUtils

variable {n : ℕ}

/-- Translation invariance of volume on Euclidean space. -/
private theorem volume_vadd (c : E n) (s : Set (E n)) :
    volume (c +ᵥ s) = volume s := by
  have h_eq : c +ᵥ s = (fun x : E n => -c + x) ⁻¹' s := by
    ext y
    simp only [Set.mem_preimage, Set.mem_vadd]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h' : -c + (c +ᵥ x) = x := by
        simp [vadd_eq_add] <;> abel
      rw [h']
      exact hx
    · intro hy
      refine ⟨-c + y, hy, ?_⟩
      have h' : c +ᵥ (-c + y) = y := by
        simp [vadd_eq_add] <;> abel
      exact h'
  rw [h_eq]
  exact measure_preimage_add volume (-c) s

/-- Volume of an ellipsoid: determinant factor times volume of unit ball. -/
theorem volume_ellipsoid_eq (c : E n) (A : E n ≃ₗ[ℝ] E n) :
    volume (ellipsoid c A) =
      ENNReal.ofReal |LinearMap.det (A : E n →ₗ[ℝ] E n)| *
        volume (Metric.closedBall (0 : E n) 1) := by
  have h1 : volume (ellipsoid c A) = volume (A '' Metric.closedBall (0 : E n) 1) := by
    simpa [ellipsoid] using volume_vadd c (A '' Metric.closedBall (0 : E n) 1)
  rw [h1]
  let Acl : E n →L[ℝ] E n := (A : E n →ₗ[ℝ] E n).toContinuousLinearMap
  exact Measure.addHaar_image_continuousLinearMap volume Acl (Metric.closedBall (0 : E n) 1)

/-- Volume of any ellipsoid is positive. -/
theorem volume_ellipsoid_pos (c : E n) (A : E n ≃ₗ[ℝ] E n) :
    0 < volume (ellipsoid c A) := by
  rw [volume_ellipsoid_eq]
  have hdet : LinearMap.det (A : E n →ₗ[ℝ] E n) ≠ 0 := by
    have h : IsUnit (LinearMap.det (A : E n →ₗ[ℝ] E n)) := by
      exact LinearEquiv.isUnit_det' A
    exact h.ne_zero
  have habs : 0 < |LinearMap.det (A : E n →ₗ[ℝ] E n)| := abs_pos.mpr hdet
  have hball : 0 < volume (Metric.closedBall (0 : E n) 1) := by
    exact Metric.measure_closedBall_pos volume (0 : E n) (by norm_num)
  have h : ENNReal.ofReal |LinearMap.det (A : E n →ₗ[ℝ] E n)| ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr habs).ne'
  exact ENNReal.mul_pos h hball.ne'

/-- Volume of the unit closed ball in Euclidean space is positive. -/
theorem volume_ball_pos (hn : 0 < n) :
    0 < volume (Metric.closedBall (0 : E n) 1) :=
  Metric.measure_closedBall_pos volume (0 : E n) (by norm_num)

/-- Comparison of ellipsoid volumes reduces to determinant comparison. -/
theorem volume_ellipsoid_le_iff (c1 : E n) (A1 : E n ≃ₗ[ℝ] E n)
    (c2 : E n) (A2 : E n ≃ₗ[ℝ] E n) :
    volume (ellipsoid c1 A1) ≤ volume (ellipsoid c2 A2) ↔
      |LinearMap.det (A1 : E n →ₗ[ℝ] E n)| ≤ |LinearMap.det (A2 : E n →ₗ[ℝ] E n)| := by
  rw [volume_ellipsoid_eq, volume_ellipsoid_eq]
  set V := volume (Metric.closedBall (0 : E n) 1) with hV
  have hV_pos : 0 < V := Metric.measure_closedBall_pos volume (0 : E n) (by norm_num)
  have hV_ne_top : V ≠ ⊤ := by
    have h_compact : IsCompact (Metric.closedBall (0 : E n) 1) := by
      exact ProperSpace.isCompact_closedBall (0 : E n) 1
    exact h_compact.measure_ne_top
  set d1 := ENNReal.ofReal |LinearMap.det (A1 : E n →ₗ[ℝ] E n)| with hd1
  set d2 := ENNReal.ofReal |LinearMap.det (A2 : E n →ₗ[ℝ] E n)| with hd2
  have h : d1 * V ≤ d2 * V ↔ d1 ≤ d2 := ENNReal.mul_le_mul_iff_left hV_pos.ne' hV_ne_top
  rw [h]
  have hpos2 : 0 ≤ |LinearMap.det (A2 : E n →ₗ[ℝ] E n)| := by positivity
  exact ENNReal.ofReal_le_ofReal_iff hpos2

/-- Volume scaling under homothety: `volume (homothety z r '' s) = |r|^n * volume s`. -/
theorem volume_homothety (z : E n) (r : ℝ) (s : Set (E n)) :
    volume (AffineMap.homothety z r '' s) = ENNReal.ofReal (|r| ^ n) * volume s := by
  let one_clm : E n →L[ℝ] E n := 1
  let scale : E n →L[ℝ] E n := r • one_clm
  have hdet : LinearMap.det (scale : E n →ₗ[ℝ] E n) = r ^ n := by
    simp [scale, one_clm, LinearMap.det_smul] <;> rfl
  have h_decomp : (AffineMap.homothety z r : E n → E n) =
      (fun y : E n => z + y) ∘ scale ∘ (fun x : E n => x - z) := by
    funext x
    simp [AffineMap.homothety_apply, scale, one_clm, smul_sub] <;> abel
  rw [h_decomp]
  rw [Set.image_comp, Set.image_comp]
  have h1 : volume ((fun y : E n => z + y) '' (scale '' ((fun x : E n => x - z) '' s))) =
      volume (scale '' ((fun x : E n => x - z) '' s)) := by
    have h_set : (fun y : E n => z + y) '' (scale '' ((fun x : E n => x - z) '' s)) =
        z +ᵥ (scale '' ((fun x : E n => x - z) '' s)) := by rfl
    rw [h_set]
    exact volume_vadd z _
  rw [h1]
  rw [Measure.addHaar_image_continuousLinearMap volume scale ((fun x : E n => x - z) '' s)]
  rw [hdet]
  have h_abs : |r ^ n| = |r| ^ n := by rw [abs_pow]
  rw [h_abs]
  have h2 : (fun x : E n => x - z) '' s = (-z) +ᵥ s := by
    ext y
    simp only [Set.mem_image, Set.mem_vadd]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx, ?_⟩
      have h' : (-z : E n) +ᵥ x = x - z := by
        simp [vadd_eq_add] <;> abel
      exact h'
    · rintro ⟨x, hx, h_eq⟩
      refine ⟨x, hx, ?_⟩
      have h' : x - z = (-z : E n) +ᵥ x := by
        simp [vadd_eq_add] <;> abel
      rw [h']
      exact h_eq
  rw [h2]
  rw [volume_vadd (-z) s]

end VolumeUtils

end JohnEllipsoid
