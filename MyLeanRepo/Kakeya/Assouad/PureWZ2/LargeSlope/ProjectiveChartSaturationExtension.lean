import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.SaturationPlaneMapCore
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Chart-preserving saturation extension

The generic finite-dimensional extension loses an opaque constant and then
pays again for normalization.  For a projective chart whose middle coordinate
is identically one, extend only the two varying real coordinates.  Their
McShane extensions preserve the scalar Lipschitz constants, the middle
coordinate stays one, and normalization is nonexpansive because every
extended chart vector has norm at least one.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

attribute [local instance] Classical.propDecidable

/-- Extend a half-Lipschitz projective chart to a nearby target while
preserving a unit-Lipschitz normalized plane map. -/
theorem pureWZ2_extend_halfLipschitz_projective_chart_to_saturation_core
    {exactImage target : Set Point3}
    {rawChart : {point : Point3 // point ∈ exactImage} → Point3}
    {witnessRadius : ℝ}
    (hrawLipschitz : LipschitzWith (1 / 2 : NNReal) rawChart)
    (hrawCoordTwo : LipschitzWith (1 / 100 : NNReal)
      (fun point => rawChart point 2))
    (hcoord : ∀ point, rawChart point 1 = 1)
    (hwitnessRadius : 0 ≤ witnessRadius)
    (targetWitness : ∀ point : {point : Point3 // point ∈ target},
      ∃ source : {point : Point3 // point ∈ exactImage},
        dist (point : Point3) (source : Point3) ≤ witnessRadius) :
    Nonempty
      (PureWZ2SaturationPlaneMapCoreData exactImage target
        (fun point => NormedSpace.normalize (rawChart point))
        witnessRadius ((51 / 100 : ℝ) * witnessRadius)) := by
  let partial0 : Point3 → ℝ := fun point =>
    if hpoint : point ∈ exactImage then rawChart ⟨point, hpoint⟩ 0 else 0
  let partial2 : Point3 → ℝ := fun point =>
    if hpoint : point ∈ exactImage then rawChart ⟨point, hpoint⟩ 2 else 0
  have hpartial0 : LipschitzOnWith (1 / 2 : NNReal) partial0 exactImage := by
    apply LipschitzOnWith.of_dist_le_mul
    intro first hfirst second hsecond
    have hraw := hrawLipschitz.dist_le_mul
      (⟨first, hfirst⟩ : {point : Point3 // point ∈ exactImage})
      (⟨second, hsecond⟩ : {point : Point3 // point ∈ exactImage})
    have hcoordBound := PiLp.norm_apply_le
      (rawChart ⟨first, hfirst⟩ - rawChart ⟨second, hsecond⟩) (0 : Fin 3)
    rw [Real.norm_eq_abs] at hcoordBound
    rw [show partial0 first = rawChart ⟨first, hfirst⟩ 0 by
      simp [partial0, hfirst],
      show partial0 second = rawChart ⟨second, hsecond⟩ 0 by
        simp [partial0, hsecond]]
    rw [Real.dist_eq]
    exact hcoordBound.trans (by simpa [dist_eq_norm, Subtype.dist_eq,
      PiLp.sub_apply] using hraw)
  have hpartial2 : LipschitzOnWith (1 / 100 : NNReal) partial2 exactImage := by
    apply LipschitzOnWith.of_dist_le_mul
    intro first hfirst second hsecond
    have hraw := hrawCoordTwo.dist_le_mul
      (⟨first, hfirst⟩ : {point : Point3 // point ∈ exactImage})
      (⟨second, hsecond⟩ : {point : Point3 // point ∈ exactImage})
    rw [show partial2 first = rawChart ⟨first, hfirst⟩ 2 by
      simp [partial2, hfirst],
      show partial2 second = rawChart ⟨second, hsecond⟩ 2 by
        simp [partial2, hsecond]]
    rw [Real.dist_eq]
    rw [Real.dist_eq] at hraw
    simpa [Subtype.dist_eq] using hraw
  rcases hpartial0.extend_real with ⟨extended0, hextended0, heq0⟩
  rcases hpartial2.extend_real with ⟨extended2, hextended2, heq2⟩
  let extendedChart : Point3 → Point3 := fun point =>
    point3 (extended0 point) 1 (extended2 point)
  have hextendedEq : ∀ point : {point : Point3 // point ∈ exactImage},
      extendedChart point = rawChart point := by
    intro point
    ext coordinate
    fin_cases coordinate
    · simpa [extendedChart, point3, partial0, point.property] using
        (heq0 point.property).symm
    · simp [extendedChart, point3, hcoord point]
    · simpa [extendedChart, point3, partial2, point.property] using
        (heq2 point.property).symm
  have hextendedLipschitz : LipschitzWith (51 / 100 : NNReal) extendedChart := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    have h0 := hextended0.dist_le_mul first second
    have h2 := hextended2.dist_le_mul first second
    rw [Real.dist_eq] at h0 h2
    rw [dist_eq_norm]
    have hformula : extendedChart first - extendedChart second =
        point3 (extended0 first - extended0 second) 0
          (extended2 first - extended2 second) := by
      ext coordinate
      fin_cases coordinate <;> simp [extendedChart, point3]
    rw [hformula]
    have hnormSq := point3_coord_norm_sq
      (point3 (extended0 first - extended0 second) 0
        (extended2 first - extended2 second))
    have h0Abs : |extended0 first - extended0 second| ≤
        (1 / 2 : ℝ) * dist first second := by simpa using h0
    have h2Abs : |extended2 first - extended2 second| ≤
        (1 / 100 : ℝ) * dist first second := by simpa using h2
    have h0Sq : (extended0 first - extended0 second) ^ 2 ≤
        ((1 / 2 : ℝ) * dist first second) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _)
          (mul_nonneg (by norm_num) dist_nonneg)).2 h0Abs
    have h2Sq : (extended2 first - extended2 second) ^ 2 ≤
        ((1 / 100 : ℝ) * dist first second) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _)
          (mul_nonneg (by norm_num) dist_nonneg)).2 h2Abs
    have hsquare :
        ‖point3 (extended0 first - extended0 second) 0
          (extended2 first - extended2 second)‖ ^ 2 ≤
            ((51 / 100 : ℝ) * dist first second) ^ 2 := by
      rw [hnormSq]
      simp only [point3_coord0, point3_coord1, point3_coord2, zero_pow]
      nlinarith [sq_nonneg (dist first second)]
    have hright : 0 ≤ (51 / 100 : ℝ) * dist first second := by positivity
    have hle := (sq_le_sq₀ (norm_nonneg _) hright).mp hsquare
    simpa using hle
  have hextendedNorm : ∀ point, 1 ≤ ‖extendedChart point‖ := by
    intro point
    have hcoordinate := PiLp.norm_apply_le (extendedChart point) (1 : Fin 3)
    simpa [extendedChart, point3, Real.norm_eq_abs] using hcoordinate
  let sourcePoint : {point : Point3 // point ∈ target} →
      {point : Point3 // point ∈ exactImage} :=
    fun point => Classical.choose (targetWitness point)
  have hsourcePoint : ∀ point : {point : Point3 // point ∈ target},
      dist (point : Point3) (sourcePoint point : Point3) ≤ witnessRadius := by
    intro point
    exact Classical.choose_spec (targetWitness point)
  let planeMap : {point : Point3 // point ∈ target} → Point3 :=
    fun point => NormedSpace.normalize (extendedChart point)
  have hplaneLipschitz : LipschitzWith 1 planeMap := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    rw [dist_eq_norm]
    exact (norm_normalize_sub_normalize_le_norm_sub
      (hextendedNorm first) (hextendedNorm second)).trans (by
        have hlip := hextendedLipschitz.dist_le_mul
          (first : Point3) (second : Point3)
        rw [dist_eq_norm] at hlip
        calc
          ‖extendedChart ↑first - extendedChart ↑second‖ ≤
              (51 / 100 : ℝ) *
                dist (first : Point3) (second : Point3) := by simpa using hlip
          _ ≤ 1 * dist (first : Point3) (second : Point3) := by
            gcongr <;> norm_num
          _ = ((1 : NNReal) : ℝ) * dist first second := by
            rw [Subtype.dist_eq]
            norm_num)
  have hplaneUnit : ∀ point, ‖planeMap point‖ = 1 := by
    intro point
    apply NormedSpace.norm_normalize
    intro hzero
    have hnorm := hextendedNorm point
    have hzeroNorm : ‖extendedChart point‖ = 0 := norm_eq_zero.mpr hzero
    linarith
  have hcloseOfDist : ∀ (point : {point : Point3 // point ∈ target})
      (source : {point : Point3 // point ∈ exactImage}),
      dist (point : Point3) (source : Point3) ≤ witnessRadius →
        ‖planeMap point - NormedSpace.normalize (rawChart source)‖ ≤
          (51 / 100 : ℝ) * witnessRadius := by
    intro point source hdist
    have hsourceNorm : 1 ≤ ‖rawChart source‖ := by
      rw [← hextendedEq source]
      exact hextendedNorm source
    have hnormal :
        ‖planeMap point - NormedSpace.normalize (rawChart source)‖ ≤
          ‖extendedChart point - rawChart source‖ := by
      simpa [planeMap] using norm_normalize_sub_normalize_le_norm_sub
        (hextendedNorm point) hsourceNorm
    have hlip := hextendedLipschitz.dist_le_mul
      (point : Point3) (source : Point3)
    rw [dist_eq_norm] at hlip
    have hnormal' :
        ‖planeMap point - NormedSpace.normalize (rawChart source)‖ ≤
          ‖extendedChart point - extendedChart source‖ := by
      simpa only [hextendedEq source] using hnormal
    exact hnormal'.trans (hlip.trans (by
      exact mul_le_mul_of_nonneg_left hdist (by norm_num)))
  have hclose : ∀ point,
      ‖planeMap point -
        NormedSpace.normalize (rawChart (sourcePoint point))‖ ≤
          (51 / 100 : ℝ) * witnessRadius := by
    intro point
    exact hcloseOfDist point (sourcePoint point) (hsourcePoint point)
  exact ⟨{
    sourcePoint := sourcePoint
    sourcePoint_dist := hsourcePoint
    planeMap := planeMap
    planeMap_lipschitz := hplaneLipschitz
    planeMap_unit := hplaneUnit
    planeMap_close_of_dist := hcloseOfDist
    planeMap_close := hclose
  }⟩

end Kakeya.Assouad

end
