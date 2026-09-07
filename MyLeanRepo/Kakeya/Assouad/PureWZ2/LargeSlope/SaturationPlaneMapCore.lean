import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LocalGrainTransfer
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Analytic core for extending a plane map to a nearby set

This module has no Section-6 assembly dependency.  It extends a Lipschitz unit
normal from an exact set to ambient space, restricts it to a target set, and
renormalizes it while retaining an explicit nearby-source certificate.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

attribute [local instance] Classical.propDecidable

/-- A unit plane map on a target saturation, with actual exact-image
provenance at every target point. -/
structure PureWZ2SaturationPlaneMapCoreData
    (exactImage target : Set Point3)
    (rawNormal : {point : Point3 // point ∈ exactImage} → Point3)
    (witnessRadius error : ℝ) where
  sourcePoint :
    {point : Point3 // point ∈ target} →
      {point : Point3 // point ∈ exactImage}
  sourcePoint_dist : ∀ point : {point : Point3 // point ∈ target},
    dist (point : Point3) (sourcePoint point : Point3) ≤ witnessRadius
  planeMap : {point : Point3 // point ∈ target} → Point3
  planeMap_lipschitz : LipschitzWith 1 planeMap
  planeMap_unit : ∀ point : {point : Point3 // point ∈ target},
    ‖planeMap point‖ = 1
  planeMap_close_of_dist :
    ∀ (point : {point : Point3 // point ∈ target})
      (source : {point : Point3 // point ∈ exactImage}),
        dist (point : Point3) (source : Point3) ≤ witnessRadius →
          ‖planeMap point - rawNormal source‖ ≤ error
  planeMap_close : ∀ point : {point : Point3 // point ∈ target},
    ‖planeMap point - rawNormal (sourcePoint point)‖ ≤ error

/-- Extend a Lipschitz unit normal to a nearby target set and normalize it. -/
theorem pureWZ2_extend_plane_map_to_saturation_core
    {exactImage target : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactImage} → Point3}
    {K : NNReal} {witnessRadius : ℝ}
    (hrawLipschitz : LipschitzWith K rawNormal)
    (hrawUnit : ∀ point, ‖rawNormal point‖ = 1)
    (hwitnessRadius : 0 ≤ witnessRadius)
    (targetWitness : ∀ point : {point : Point3 // point ∈ target},
      ∃ source : {point : Point3 // point ∈ exactImage},
        dist (point : Point3) (source : Point3) ≤ witnessRadius)
    (hsmall :
      ((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ) *
          witnessRadius ≤ 1 / 2)
    (hone :
      4 * ((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ) ≤ 1) :
    Nonempty
      (PureWZ2SaturationPlaneMapCoreData exactImage target rawNormal
        witnessRadius
        (4 * ((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ) *
          witnessRadius)) := by
  let partialMap : Point3 → Point3 := fun point =>
    if hpoint : point ∈ exactImage then rawNormal ⟨point, hpoint⟩ else 0
  have hpartial : LipschitzOnWith K partialMap exactImage := by
    apply LipschitzOnWith.of_dist_le_mul
    intro first hfirst second hsecond
    have hfirstEq : partialMap first = rawNormal ⟨first, hfirst⟩ := by
      simp [partialMap, hfirst]
    have hsecondEq : partialMap second = rawNormal ⟨second, hsecond⟩ := by
      simp [partialMap, hsecond]
    rw [hfirstEq, hsecondEq]
    simpa [Subtype.dist_eq] using
      hrawLipschitz.dist_le_mul ⟨first, hfirst⟩ ⟨second, hsecond⟩
  rcases hpartial.extend_finite_dimension with
    ⟨extended, hextendedLipschitz, hextendedEq⟩
  let sourcePoint :
      {point : Point3 // point ∈ target} →
        {point : Point3 // point ∈ exactImage} :=
    fun point => Classical.choose (targetWitness point)
  have hsourcePoint : ∀ point : {point : Point3 // point ∈ target},
      dist (point : Point3) (sourcePoint point : Point3) ≤
        witnessRadius := by
    intro point
    exact Classical.choose_spec (targetWitness point)
  let rawExtended : {point : Point3 // point ∈ target} → Point3 :=
    fun point => extended point
  have hrawExtendedLipschitz :
      LipschitzWith (lipschitzExtensionConstant Point3 * K) rawExtended := by
    intro first second
    simpa [rawExtended, Subtype.edist_eq] using
      hextendedLipschitz first.1 second.1
  have hextendedSource : ∀ point,
      extended (sourcePoint point : Point3) = rawNormal (sourcePoint point) := by
    intro point
    have heq := hextendedEq (sourcePoint point).property
    simpa [partialMap, (sourcePoint point).property] using heq.symm
  have hrawClose : ∀ point,
      ‖rawExtended point - rawNormal (sourcePoint point)‖ ≤
        ((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ) *
          witnessRadius := by
    intro point
    have hdist := hextendedLipschitz.dist_le_mul
      (point : Point3) (sourcePoint point : Point3)
    rw [hextendedSource point] at hdist
    have hreal : dist (rawExtended point) (rawNormal (sourcePoint point)) ≤
        ((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ) *
          dist (point : Point3) (sourcePoint point : Point3) := by
      simpa [rawExtended] using hdist
    rw [dist_eq_norm] at hreal
    exact hreal.trans (by
      gcongr
      exact hsourcePoint point)
  have hrawNormLower : ∀ point, 1 / 2 ≤ ‖rawExtended point‖ := by
    intro point
    have hnormDiff :
        |‖rawExtended point‖ - ‖rawNormal (sourcePoint point)‖| ≤
          ‖rawExtended point - rawNormal (sourcePoint point)‖ :=
      abs_norm_sub_norm_le _ _
    rw [hrawUnit (sourcePoint point)] at hnormDiff
    have hclose := hrawClose point
    have habsLower : 1 - ‖rawExtended point‖ ≤
        |‖rawExtended point‖ - 1| := by
      have heq : 1 - ‖rawExtended point‖ =
          -(‖rawExtended point‖ - 1) := by ring
      rw [heq]
      exact neg_le_abs _
    linarith
  let planeMap : {point : Point3 // point ∈ target} → Point3 :=
    fun point => (‖rawExtended point‖⁻¹ : ℝ) • rawExtended point
  have hplaneUnit : ∀ point, ‖planeMap point‖ = 1 := by
    intro point
    have hnormPos : 0 < ‖rawExtended point‖ := by
      linarith [hrawNormLower point]
    simp [planeMap, norm_smul, abs_of_nonneg, hnormPos.ne']
  have hplaneLipschitzFour :
      LipschitzWith
        ⟨4 * ((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ), by
          positivity⟩ planeMap := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    rw [dist_eq_norm]
    have hnormal := normalization_lipschitz
      (x := rawExtended first) (y := rawExtended second)
      (m := (1 / 2 : ℝ)) (by norm_num)
      (hrawNormLower first) (hrawNormLower second)
    have hfour : (2 / (1 / 2 : ℝ)) = 4 := by norm_num
    rw [hfour] at hnormal
    have hrawDist := hrawExtendedLipschitz.dist_le_mul first second
    rw [dist_eq_norm] at hrawDist
    calc
      ‖planeMap first - planeMap second‖
          ≤ 4 * ‖rawExtended first - rawExtended second‖ := by
            simpa [planeMap] using hnormal
      _ ≤ 4 *
          (((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ) *
            dist first second) := by gcongr
      _ = (4 *
          ((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ)) *
            dist first second := by ring
  have hplaneLipschitz : LipschitzWith 1 planeMap :=
    hplaneLipschitzFour.weaken (by
      exact_mod_cast hone)
  have hplaneCloseOfDist :
      ∀ (point : {point : Point3 // point ∈ target})
        (source : {point : Point3 // point ∈ exactImage}),
      dist (point : Point3) (source : Point3) ≤ witnessRadius →
      ‖planeMap point - rawNormal source‖ ≤
        4 * ((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ) *
          witnessRadius := by
    intro point source hdist
    have hextendedSource' : extended (source : Point3) = rawNormal source := by
      have heq := hextendedEq source.property
      simpa [partialMap, source.property] using heq.symm
    have hrawClose' :
        ‖rawExtended point - rawNormal source‖ ≤
          ((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ) *
            witnessRadius := by
      have hdistExtended := hextendedLipschitz.dist_le_mul
        (point : Point3) (source : Point3)
      rw [hextendedSource'] at hdistExtended
      rw [dist_eq_norm] at hdistExtended
      exact hdistExtended.trans (by gcongr)
    have hnormal := normalization_lipschitz
      (x := rawExtended point)
      (y := rawNormal source)
      (m := (1 / 2 : ℝ)) (by norm_num)
      (hrawNormLower point) (by
        rw [hrawUnit source]
        norm_num)
    have hfour : (2 / (1 / 2 : ℝ)) = 4 := by norm_num
    rw [hfour] at hnormal
    have hrawNormalized :
        (‖rawNormal source‖⁻¹ : ℝ) • rawNormal source =
            rawNormal source := by
      rw [hrawUnit source]
      simp
    rw [hrawNormalized] at hnormal
    calc
      ‖planeMap point - rawNormal source‖
          ≤ 4 * ‖rawExtended point - rawNormal source‖ := by
            simpa [planeMap] using hnormal
      _ ≤ 4 *
          (((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ) *
            witnessRadius) := by gcongr
      _ = 4 *
          ((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ) *
            witnessRadius := by ring
  have hplaneClose : ∀ point,
      ‖planeMap point - rawNormal (sourcePoint point)‖ ≤
        4 * ((lipschitzExtensionConstant Point3 * K : NNReal) : ℝ) *
          witnessRadius := by
    intro point
    exact hplaneCloseOfDist point (sourcePoint point) (hsourcePoint point)
  exact ⟨{
    sourcePoint := sourcePoint
    sourcePoint_dist := hsourcePoint
    planeMap := planeMap
    planeMap_lipschitz := hplaneLipschitz
    planeMap_unit := hplaneUnit
    planeMap_close_of_dist := hplaneCloseOfDist
    planeMap_close := hplaneClose
  }⟩

/-- Incidence is stable when the extended unit field is compared with any
nearby exact-image witness. -/
theorem PureWZ2SaturationPlaneMapCoreData.incidence_of_nearby_exact
    {exactImage target : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactImage} → Point3}
    {witnessRadius error sourceDelta targetDelta : ℝ}
    (data : PureWZ2SaturationPlaneMapCoreData exactImage target rawNormal
      witnessRadius error)
    {direction : Point3} (hdirection : ‖direction‖ = 1)
    (point : {point : Point3 // point ∈ target})
    (source : {point : Point3 // point ∈ exactImage})
    (hdist : dist (point : Point3) (source : Point3) ≤ witnessRadius)
    (hexact : |inner ℝ direction (rawNormal source)| ≤ sourceDelta)
    (hbudget : sourceDelta + error ≤ targetDelta) :
    |inner ℝ direction (data.planeMap point)| ≤ targetDelta := by
  have hperturb :
      |inner ℝ direction (data.planeMap point - rawNormal source)| ≤
        error := by
    calc
      |inner ℝ direction (data.planeMap point - rawNormal source)|
          ≤ ‖direction‖ * ‖data.planeMap point - rawNormal source‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ 1 * error := by
        simpa only [hdirection, one_mul] using
          data.planeMap_close_of_dist point source hdist
      _ = error := one_mul error
  have hsplit :
      inner ℝ direction (data.planeMap point) =
        inner ℝ direction (data.planeMap point - rawNormal source) +
          inner ℝ direction (rawNormal source) := by
    rw [inner_sub_right]
    ring
  rw [hsplit]
  calc
    |inner ℝ direction (data.planeMap point - rawNormal source) +
        inner ℝ direction (rawNormal source)| ≤
      |inner ℝ direction (data.planeMap point - rawNormal source)| +
        |inner ℝ direction (rawNormal source)| := abs_add_le _ _
    _ ≤ error + sourceDelta := add_le_add hperturb hexact
    _ = sourceDelta + error := add_comm _ _
    _ ≤ targetDelta := hbudget

end Kakeya.Assouad

end
