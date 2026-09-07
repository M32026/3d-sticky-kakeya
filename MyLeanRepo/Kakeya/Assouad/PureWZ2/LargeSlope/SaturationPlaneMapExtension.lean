import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LocalGrainTransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.GridCubeCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicExactPlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.NearbyProjectionADTransfer
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Extend genuine affine-image normals to a cubical saturation

An affine image of a cubical source shading is not cubical in the fixed target
grid.  The paper therefore replaces it by the union of target cubes meeting
the image.  The new points do not have literal affine preimages.

This module performs the required non-circular step.  A unit normal field on
the exact image is extended to ambient space by the finite-dimensional
Lipschitz extension theorem.  At every saturation point we retain an actual
same-cell exact-image witness.  If one target cube is small compared with the
extension constant, the extended vector stays away from zero and can be
normalized.  The result is a genuine one-Lipschitz unit plane map together
with an explicit perturbation bound from the transported source normal.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

attribute [local instance] Classical.propDecidable

/-- Every point added by literal paper cubical saturation has a genuine
source point in the same grid cell, hence lies within one cube diagonal. -/
theorem wz1PaperCubicalSaturation_exists_source_dist_le
    {scale : ℝ} (hscale : 0 < scale) (source : Set Point3)
    {point : Point3}
    (hpoint : point ∈ wz1PaperCubicalSaturation scale source) :
    ∃ sourcePoint ∈ source,
      dist point sourcePoint ≤ scale * Real.sqrt 3 := by
  rcases hpoint with ⟨sourcePoint, hsourcePoint, hcell⟩
  refine ⟨sourcePoint, hsourcePoint, ?_⟩
  apply dist_le_sqrt3_of_mem_wz1PaperGridCube hscale
    (cell := wz1PaperGridIndex scale point)
  · exact (mem_wz1PaperGridCube _ _ _).mpr rfl
  · exact (mem_wz1PaperGridCube _ _ _).mpr hcell.symm

/-- A unit plane map on a target saturation, with actual exact-image
provenance at every target point. -/
structure PureWZ2SaturationPlaneMapData
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

/-- Extend a Lipschitz unit normal from the exact affine image to a target
saturation and normalize it.

`targetWitness` is the literal cubical-saturation provenance: every target
point has an actual exact-image point in the same target cell.  The theorem is
stated with a metric radius so callers can use the standard `sqrt 3 * rho`
cell-diameter estimate. -/
theorem pureWZ2_extend_plane_map_to_saturation
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
      (PureWZ2SaturationPlaneMapData exactImage target rawNormal
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
      exact hdistExtended.trans (by
        gcongr)
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

/-- Incidence is stable under replacing an exact-image unit normal by the
extended saturation normal.  This is stated for an arbitrary nearby exact
witness, so a point lying in several saturated tube shadings may use the
witness belonging to the tube whose incidence is being checked. -/
theorem PureWZ2SaturationPlaneMapData.incidence_of_nearby_exact
    {exactImage target : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactImage} → Point3}
    {witnessRadius error sourceDelta targetDelta : ℝ}
    (data : PureWZ2SaturationPlaneMapData exactImage target rawNormal
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
      _ = ‖data.planeMap point - rawNormal source‖ := by
            rw [hdirection, one_mul]
      _ ≤ error := data.planeMap_close_of_dist point source hdist
  have hsplit : inner ℝ direction (data.planeMap point) =
      inner ℝ direction (rawNormal source) +
        inner ℝ direction (data.planeMap point - rawNormal source) := by
    rw [inner_sub_right]
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans <|
    (add_le_add hexact hperturb).trans hbudget

/-- Local paper AD survives cubical saturation.  The exact-image hypothesis
is deliberately centered at the exact witness of the distinguished target
point and uses the enlarged radius `sqrt rho + 2 * witnessRadius`: one cell
radius is spent at each endpoint.  Projection thickening costs the explicit
amount `witnessRadius + pointBound * error` and a factor `6` in the AD
constant. -/
theorem PureWZ2SaturationPlaneMapData.local_ad_of_exact
    {exactImage target : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactImage} → Point3}
    {witnessRadius error rho alpha pointBound : ℝ} {C : ENNReal}
    (data : PureWZ2SaturationPlaneMapData exactImage target rawNormal
      witnessRadius error)
    (hwitnessRadius : 0 ≤ witnessRadius) (herror : 0 ≤ error)
    (hpointBound : 0 ≤ pointBound)
    (hexactBound : ∀ source : {point : Point3 // point ∈ exactImage},
      ‖(source : Point3)‖ ≤ pointBound)
    (point : {point : Point3 // point ∈ target})
    (hexactAD : PureWZ2PaperADSet1
      (scalarProjection (rawNormal (data.sourcePoint point))
        (exactImage ∩
          Metric.closedBall (data.sourcePoint point : Point3)
            (Real.sqrt rho + 2 * witnessRadius)))
      rho alpha C)
    (hprojectionBudget : witnessRadius + pointBound * error ≤ rho) :
    PureWZ2PaperADSet1
      (scalarProjection (data.planeMap point)
        (target ∩ Metric.closedBall (point : Point3) (Real.sqrt rho)))
      rho alpha (6 * C) := by
  apply hexactAD.of_subset_cthickening
      (D := witnessRadius + pointBound * error)
  · rintro value ⟨targetPoint, htargetPoint, rfl⟩
    let targetSubtype : {point : Point3 // point ∈ target} :=
      ⟨targetPoint, htargetPoint.1⟩
    let sourceSubtype : {point : Point3 // point ∈ exactImage} :=
      data.sourcePoint targetSubtype
    have hsourceDistance :
        dist targetPoint (sourceSubtype : Point3) ≤ witnessRadius :=
      data.sourcePoint_dist targetSubtype
    have hsourceBall : (sourceSubtype : Point3) ∈
        Metric.closedBall (data.sourcePoint point : Point3)
          (Real.sqrt rho + 2 * witnessRadius) := by
      rw [Metric.mem_closedBall]
      calc
        dist (sourceSubtype : Point3) (data.sourcePoint point : Point3)
            ≤ dist (sourceSubtype : Point3) targetPoint +
                dist targetPoint (point : Point3) +
                  dist (point : Point3) (data.sourcePoint point : Point3) := by
              exact dist_triangle4 (sourceSubtype : Point3) targetPoint
                (point : Point3) (data.sourcePoint point : Point3)
        _ ≤ witnessRadius + Real.sqrt rho + witnessRadius := by
              gcongr
              · simpa [dist_comm] using hsourceDistance
              · exact htargetPoint.2
              · exact data.sourcePoint_dist point
        _ = Real.sqrt rho + 2 * witnessRadius := by ring
    let sourceValue := inner ℝ (sourceSubtype : Point3)
      (rawNormal (data.sourcePoint point))
    refine ⟨sourceValue, ?_, ?_⟩
    · exact ⟨sourceSubtype, ⟨sourceSubtype.property, hsourceBall⟩, rfl⟩
    rw [Real.dist_eq]
    have hsplit :
        inner ℝ targetPoint (data.planeMap point) - sourceValue =
          inner ℝ (targetPoint - (sourceSubtype : Point3))
              (data.planeMap point) +
            inner ℝ (sourceSubtype : Point3)
              (data.planeMap point - rawNormal (data.sourcePoint point)) := by
      dsimp only [sourceValue]
      rw [inner_sub_left, inner_sub_right]
      ring
    rw [hsplit]
    calc
      |inner ℝ (targetPoint - (sourceSubtype : Point3))
          (data.planeMap point) +
        inner ℝ (sourceSubtype : Point3)
          (data.planeMap point - rawNormal (data.sourcePoint point))|
          ≤ |inner ℝ (targetPoint - (sourceSubtype : Point3))
                (data.planeMap point)| +
              |inner ℝ (sourceSubtype : Point3)
                (data.planeMap point - rawNormal (data.sourcePoint point))| :=
            abs_add_le _ _
      _ ≤ ‖targetPoint - (sourceSubtype : Point3)‖ *
              ‖data.planeMap point‖ +
            ‖(sourceSubtype : Point3)‖ *
              ‖data.planeMap point - rawNormal (data.sourcePoint point)‖ := by
            gcongr <;> apply abs_real_inner_le_norm
      _ ≤ witnessRadius * 1 + pointBound * error := by
            gcongr
            · simpa [dist_eq_norm] using hsourceDistance
            · exact data.planeMap_unit point |>.le
            · exact hexactBound sourceSubtype
            · exact data.planeMap_close point
      _ = witnessRadius + pointBound * error := by ring
  · positivity
  · exact hprojectionBudget

/-- The fixed-constant saturation AD transfer when the projection error is at
most twice the base scale.  Honest target-grid saturation naturally has this
budget because one cell diagonal is already larger than the cell width. -/
theorem PureWZ2SaturationPlaneMapData.local_ad_of_exact_two
    {exactImage target : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactImage} → Point3}
    {witnessRadius error rho alpha pointBound : ℝ} {C : ENNReal}
    (data : PureWZ2SaturationPlaneMapData exactImage target rawNormal
      witnessRadius error)
    (hwitnessRadius : 0 ≤ witnessRadius) (herror : 0 ≤ error)
    (hpointBound : 0 ≤ pointBound)
    (hexactBound : ∀ source : {point : Point3 // point ∈ exactImage},
      ‖(source : Point3)‖ ≤ pointBound)
    (point : {point : Point3 // point ∈ target})
    (hexactAD : PureWZ2PaperADSet1
      (scalarProjection (rawNormal (data.sourcePoint point))
        (exactImage ∩
          Metric.closedBall (data.sourcePoint point : Point3)
            (Real.sqrt rho + 2 * witnessRadius)))
      rho alpha C)
    (hprojectionBudget : witnessRadius + pointBound * error ≤ 2 * rho) :
    PureWZ2PaperADSet1
      (scalarProjection (data.planeMap point)
        (target ∩ Metric.closedBall (point : Point3) (Real.sqrt rho)))
      rho alpha (15 * C) := by
  apply hexactAD.of_subset_cthickening_two
      (D := witnessRadius + pointBound * error)
  · rintro value ⟨targetPoint, htargetPoint, rfl⟩
    let targetSubtype : {point : Point3 // point ∈ target} :=
      ⟨targetPoint, htargetPoint.1⟩
    let sourceSubtype : {point : Point3 // point ∈ exactImage} :=
      data.sourcePoint targetSubtype
    have hsourceDistance :
        dist targetPoint (sourceSubtype : Point3) ≤ witnessRadius :=
      data.sourcePoint_dist targetSubtype
    have hsourceBall : (sourceSubtype : Point3) ∈
        Metric.closedBall (data.sourcePoint point : Point3)
          (Real.sqrt rho + 2 * witnessRadius) := by
      rw [Metric.mem_closedBall]
      calc
        dist (sourceSubtype : Point3) (data.sourcePoint point : Point3)
            ≤ dist (sourceSubtype : Point3) targetPoint +
                dist targetPoint (point : Point3) +
                  dist (point : Point3) (data.sourcePoint point : Point3) := by
              exact dist_triangle4 (sourceSubtype : Point3) targetPoint
                (point : Point3) (data.sourcePoint point : Point3)
        _ ≤ witnessRadius + Real.sqrt rho + witnessRadius := by
              gcongr
              · simpa [dist_comm] using hsourceDistance
              · exact htargetPoint.2
              · exact data.sourcePoint_dist point
        _ = Real.sqrt rho + 2 * witnessRadius := by ring
    let sourceValue := inner ℝ (sourceSubtype : Point3)
      (rawNormal (data.sourcePoint point))
    refine ⟨sourceValue, ?_, ?_⟩
    · exact ⟨sourceSubtype, ⟨sourceSubtype.property, hsourceBall⟩, rfl⟩
    rw [Real.dist_eq]
    have hsplit :
        inner ℝ targetPoint (data.planeMap point) - sourceValue =
          inner ℝ (targetPoint - (sourceSubtype : Point3))
              (data.planeMap point) +
            inner ℝ (sourceSubtype : Point3)
              (data.planeMap point - rawNormal (data.sourcePoint point)) := by
      dsimp only [sourceValue]
      rw [inner_sub_left, inner_sub_right]
      ring
    rw [hsplit]
    calc
      |inner ℝ (targetPoint - (sourceSubtype : Point3))
          (data.planeMap point) +
        inner ℝ (sourceSubtype : Point3)
          (data.planeMap point - rawNormal (data.sourcePoint point))|
          ≤ |inner ℝ (targetPoint - (sourceSubtype : Point3))
                (data.planeMap point)| +
              |inner ℝ (sourceSubtype : Point3)
                (data.planeMap point - rawNormal (data.sourcePoint point))| :=
            abs_add_le _ _
      _ ≤ ‖targetPoint - (sourceSubtype : Point3)‖ *
              ‖data.planeMap point‖ +
            ‖(sourceSubtype : Point3)‖ *
              ‖data.planeMap point - rawNormal (data.sourcePoint point)‖ := by
            gcongr <;> apply abs_real_inner_le_norm
      _ ≤ witnessRadius * 1 + pointBound * error := by
            gcongr
            · simpa [dist_eq_norm] using hsourceDistance
            · exact data.planeMap_unit point |>.le
            · exact hexactBound sourceSubtype
            · exact data.planeMap_close point
      _ = witnessRadius + pointBound * error := by ring
  · positivity
  · exact hprojectionBudget

/-- Package the two stability statements into the public local-grain API.
The caller supplies the exact-image AD estimate with the enlarged local ball;
this is where the preceding combined affine/isotropic transport is connected. -/
def PureWZ2SaturationPlaneMapData.toLocalGrainData
    {delta sourceDelta sigma witnessRadius error pointBound : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {exactImage : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactImage} → Point3}
    {C : ENNReal}
    (data : PureWZ2SaturationPlaneMapData exactImage shading.union rawNormal
      witnessRadius error)
    (hwitnessRadius : 0 ≤ witnessRadius) (herror : 0 ≤ error)
    (hpointBound : 0 ≤ pointBound)
    (hexactBound : ∀ source : {point : Point3 // point ∈ exactImage},
      ‖(source : Point3)‖ ≤ pointBound)
    (hincidence : ∀ index point,
      ∀ hpoint : point ∈ shading.carrier index,
        ∃ source : {point : Point3 // point ∈ exactImage},
          dist point (source : Point3) ≤ witnessRadius ∧
          |inner ℝ (family.tube index).direction (rawNormal source)| ≤
            sourceDelta)
    (hincidenceBudget : sourceDelta + error ≤ delta)
    (hprojectionBudget : witnessRadius + pointBound * error ≤ delta)
    (hexactAD : ∀ rho : ℝ, delta ≤ rho → rho ≤ 1 →
      ∀ point : {point : Point3 // point ∈ shading.union},
        PureWZ2PaperADSet1
          (scalarProjection (rawNormal (data.sourcePoint point))
            (exactImage ∩
              Metric.closedBall (data.sourcePoint point : Point3)
                (Real.sqrt rho + 2 * witnessRadius)))
          rho (1 - sigma) C) :
    PureWZ2LocalGrainData shading sigma (6 * C) := by
  refine {
    planeMap := data.planeMap
    planeMap_lipschitz := data.planeMap_lipschitz
    planeMap_unit := data.planeMap_unit
    planeMap_incidence := ?_
    local_ad := ?_
  }
  · intro index point hpoint
    rcases hincidence index point hpoint with
      ⟨source, hdist, hexact⟩
    exact data.incidence_of_nearby_exact
      (family.tube index).direction_unit
      ⟨point, ⟨index, hpoint⟩⟩ source hdist hexact hincidenceBudget
  · intro rho hrhoLower hrhoOne point
    apply data.local_ad_of_exact hwitnessRadius herror hpointBound
      hexactBound point (hexactAD rho hrhoLower hrhoOne point)
    exact hprojectionBudget.trans hrhoLower

/-- Package saturation incidence and the twice-scale AD transfer into the
public local-grain interface, with the fixed output constant `15 * C`. -/
def PureWZ2SaturationPlaneMapData.toLocalGrainDataTwo
    {delta sourceDelta sigma witnessRadius error pointBound : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {exactImage : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactImage} → Point3}
    {C : ENNReal}
    (data : PureWZ2SaturationPlaneMapData exactImage shading.union rawNormal
      witnessRadius error)
    (hwitnessRadius : 0 ≤ witnessRadius) (herror : 0 ≤ error)
    (hpointBound : 0 ≤ pointBound)
    (hexactBound : ∀ source : {point : Point3 // point ∈ exactImage},
      ‖(source : Point3)‖ ≤ pointBound)
    (hincidence : ∀ index point,
      ∀ hpoint : point ∈ shading.carrier index,
        ∃ source : {point : Point3 // point ∈ exactImage},
          dist point (source : Point3) ≤ witnessRadius ∧
          |inner ℝ (family.tube index).direction (rawNormal source)| ≤
            sourceDelta)
    (hincidenceBudget : sourceDelta + error ≤ delta)
    (hprojectionBudget : witnessRadius + pointBound * error ≤ 2 * delta)
    (hexactAD : ∀ rho : ℝ, delta ≤ rho → rho ≤ 1 →
      ∀ point : {point : Point3 // point ∈ shading.union},
        PureWZ2PaperADSet1
          (scalarProjection (rawNormal (data.sourcePoint point))
            (exactImage ∩
              Metric.closedBall (data.sourcePoint point : Point3)
                (Real.sqrt rho + 2 * witnessRadius)))
          rho (1 - sigma) C) :
    PureWZ2LocalGrainData shading sigma (15 * C) := by
  refine {
    planeMap := data.planeMap
    planeMap_lipschitz := data.planeMap_lipschitz
    planeMap_unit := data.planeMap_unit
    planeMap_incidence := ?_
    local_ad := ?_
  }
  · intro index point hpoint
    rcases hincidence index point hpoint with
      ⟨source, hdist, hexact⟩
    exact data.incidence_of_nearby_exact
      (family.tube index).direction_unit
      ⟨point, ⟨index, hpoint⟩⟩ source hdist hexact hincidenceBudget
  · intro rho hrhoLower hrhoOne point
    apply data.local_ad_of_exact_two hwitnessRadius herror hpointBound
      hexactBound point (hexactAD rho hrhoLower hrhoOne point)
    exact hprojectionBudget.trans <|
      mul_le_mul_of_nonneg_left hrhoLower (by norm_num)

/-- Specialize the ambient extension theorem to the literal cubical
saturation in an exact triangular retubing.  The chosen source point lies in
the exact affine-image union and in the same target grid cube. -/
theorem PureWZ2AnisotropicExactPlaneMapData.extendToRetubingShading
    {sourceDelta targetDelta c d m sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceLocal : PureWZ2LocalGrainData sourceShading sigma C}
    (exact : PureWZ2AnisotropicExactPlaneMapData raw sourceLocal)
    (htargetDelta : 0 < targetDelta)
    (hsmall :
      ((lipschitzExtensionConstant Point3 * exact.K : NNReal) : ℝ) *
          (targetDelta * Real.sqrt 3) ≤ 1 / 2)
    (hone :
      4 * ((lipschitzExtensionConstant Point3 * exact.K : NNReal) : ℝ) ≤ 1) :
    Nonempty
      (PureWZ2SaturationPlaneMapData raw.exactShading.union raw.shading.union
        exact.planeMap (targetDelta * Real.sqrt 3)
        (4 * ((lipschitzExtensionConstant Point3 * exact.K : NNReal) : ℝ) *
          (targetDelta * Real.sqrt 3))) := by
  apply pureWZ2_extend_plane_map_to_saturation
    exact.planeMap_lipschitz exact.planeMap_unit (by positivity)
  · intro point
    rcases point.property with ⟨index, hpoint⟩
    rw [raw.shading_carrier index] at hpoint
    rcases wz1PaperCubicalSaturation_exists_source_dist_le
        htargetDelta _ hpoint with
      ⟨sourcePoint, hsourcePoint, hdist⟩
    exact ⟨⟨sourcePoint, ⟨index, hsourcePoint⟩⟩, hdist⟩
  · exact hsmall
  · exact hone

/-- Finish the cubical-saturation part of local-grain transport for one exact
triangular retubing.  Incidence uses the exact witness in the same tube cell,
while local AD uses the distinguished union witness and the enlarged exact
ball supplied by the preceding combined affine/isotropic transport. -/
def PureWZ2AnisotropicExactPlaneMapData.toRetubingLocalGrains
    {sourceDelta targetDelta c d m sigma witnessRadius error pointBound : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceLocal : PureWZ2LocalGrainData sourceShading sigma C}
    (exact : PureWZ2AnisotropicExactPlaneMapData raw sourceLocal)
    (saturation : PureWZ2SaturationPlaneMapData
      raw.exactShading.union raw.shading.union exact.planeMap
        witnessRadius error)
    (htargetDelta : 0 < targetDelta)
    (hwitnessRadius : 0 ≤ witnessRadius) (herror : 0 ≤ error)
    (hcellRadius : targetDelta * Real.sqrt 3 ≤ witnessRadius)
    (hpointBound : 0 ≤ pointBound)
    (hexactBound : ∀ source :
      {point : Point3 // point ∈ raw.exactShading.union},
        ‖(source : Point3)‖ ≤ pointBound)
    (hincidenceBudget : 3 * sourceDelta + error ≤ targetDelta)
    (hprojectionBudget : witnessRadius + pointBound * error ≤ targetDelta)
    (hexactAD : ∀ rho : ℝ, targetDelta ≤ rho → rho ≤ 1 →
      ∀ point : {point : Point3 // point ∈ raw.shading.union},
        PureWZ2PaperADSet1
          (scalarProjection (exact.planeMap (saturation.sourcePoint point))
            (raw.exactShading.union ∩
              Metric.closedBall (saturation.sourcePoint point : Point3)
                (Real.sqrt rho + 2 * witnessRadius)))
          rho (1 - sigma) C) :
    PureWZ2LocalGrainData raw.shading sigma (6 * C) := by
  apply saturation.toLocalGrainData hwitnessRadius herror hpointBound
    hexactBound
  · intro index point hpoint
    rw [raw.shading_carrier index] at hpoint
    rcases wz1PaperCubicalSaturation_exists_source_dist_le
        htargetDelta
        _ hpoint with ⟨sourcePoint, hsourcePoint, hdist⟩
    let source : {point : Point3 // point ∈ raw.exactShading.union} :=
      ⟨sourcePoint, ⟨index, hsourcePoint⟩⟩
    refine ⟨source, ?_, ?_⟩
    · exact hdist.trans hcellRadius
    · exact exact.planeMap_incidence_source index sourcePoint hsourcePoint
  · exact hincidenceBudget
  · exact hprojectionBudget
  · exact hexactAD

end Kakeya.Assouad

end
