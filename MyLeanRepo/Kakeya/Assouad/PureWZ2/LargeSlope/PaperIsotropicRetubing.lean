import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperIsotropicLocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.GridCubeCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LocalizedOrdinaryDistinctnessToLineDistance
import MyLeanRepo.Kakeya.Assouad.PropStickyOrdinaryToCroppedShading
import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingIsotropicVolume

/-!
# One-to-one isotropic retubing in the cropped full-line model

Unlike ordinary unit-segment tubes, cropped paper tubes use complete coaxial
lines.  A positive similarity therefore preserves one source index per target
index; no axial multi-child rediscretization is needed.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

/-- A canonical target tube on the isotropic image axis. -/
def pureWZ2IsotropicPaperTube
    {sourceDelta targetDelta : ℝ}
    (center : Point3) (scale : ℝ)
    (source : Kakeya.DeltaTube sourceDelta) :
    Kakeya.DeltaTube targetDelta where
  base := pureWZ2IsotropicMap center scale source.base
  direction := source.direction
  direction_unit := source.direction_unit

theorem pureWZ2IsotropicPaperTube_axis
    {sourceDelta targetDelta : ℝ}
    (center : Point3) {scale : ℝ} (hscale : 0 < scale)
    (source : Kakeya.DeltaTube sourceDelta) :
    tubeAxisLine
        (pureWZ2IsotropicPaperTube (targetDelta := targetDelta)
          center scale source) =
      pureWZ2IsotropicMap center scale '' tubeAxisLine source := by
  ext point
  constructor
  · rintro ⟨parameter, rfl⟩
    refine ⟨source.base + (parameter / scale : ℝ) • source.direction,
      ⟨parameter / scale, rfl⟩, ?_⟩
    simp only [pureWZ2IsotropicMap, pureWZ2IsotropicPaperTube]
    rw [show source.base + (parameter / scale : ℝ) • source.direction - center =
      (source.base - center) + (parameter / scale) • source.direction by abel,
      smul_add, smul_smul]
    field_simp [hscale.ne']
  · rintro ⟨sourcePoint, ⟨parameter, rfl⟩, rfl⟩
    refine ⟨scale * parameter, ?_⟩
    simp only [pureWZ2IsotropicMap, pureWZ2IsotropicPaperTube]
    rw [show source.base + parameter • source.direction - center =
      (source.base - center) + parameter • source.direction by abel,
      smul_add, smul_smul]

def pureWZ2IsotropicPaperFamily
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (center : Point3) (scale : ℝ) :
    Kakeya.Streamlined.TubeFamily targetDelta where
  card := sourceFamily.card
  tube index := pureWZ2IsotropicPaperTube center scale
    (sourceFamily.tube index)

/-- Use the midpoint-centered ordinary representative of every isotropic
image line.  Its cropped paper carrier is unchanged. -/
def pureWZ2IsotropicCenteredPaperFamily
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (center : Point3) (scale : ℝ) :
    Kakeya.Streamlined.TubeFamily targetDelta where
  card := sourceFamily.card
  tube index := pureWZ2PaperCenteredTube
    (pureWZ2IsotropicPaperTube center scale (sourceFamily.tube index))

/-- The same isotropic supporting lines, represented by their canonical
height-zero paper tubes. -/
def pureWZ2IsotropicZeroBasedPaperFamily
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (center : Point3) (scale : ℝ) :
    Kakeya.Streamlined.TubeFamily targetDelta :=
  pureWZ2PaperZeroBasedFamily
    (pureWZ2IsotropicPaperFamily sourceFamily center scale)

/-- The literal target-grid saturation of an isotropically transformed
cropped shading. -/
def pureWZ2IsotropicPaperShading
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        targetDelta * Real.sqrt 3 ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale))) :
    WZ1PaperTubeShading
      (pureWZ2IsotropicPaperFamily (targetDelta := targetDelta)
        sourceFamily center scale) where
  carrier index := wz1PaperCubicalSaturation targetDelta
    (pureWZ2IsotropicMap center scale '' sourceShading.carrier index)
  measurable_carrier index :=
    wz1PaperCubicalSaturation_measurable targetDelta _
  subset_body index := by
    change Fin sourceFamily.card at index
    intro point hpoint
    rcases hpoint with ⟨imagePoint, ⟨sourcePoint, hsourcePoint, rfl⟩, hcell⟩
    have hsameCell : dist point
        (pureWZ2IsotropicMap center scale sourcePoint) ≤
          targetDelta * Real.sqrt 3 := by
      apply dist_le_sqrt3_of_mem_wz1PaperGridCube htargetDelta
        (cell := wz1PaperGridIndex targetDelta point)
      · exact (mem_wz1PaperGridCube _ _ _).mpr rfl
      · exact (mem_wz1PaperGridCube _ _ _).mpr hcell.symm
    have hsourceAxis := (sourceShading.subset_body index hsourcePoint).1
    rcases exists_dist_le_of_mem_cthickening_closed
        (isClosed_tubeAxisLine (sourceFamily.tube index))
        (mul_nonneg (by norm_num) hsourceDelta.le) hsourceAxis with
      ⟨axisPoint, haxisPoint, hsourceDist⟩
    let targetAxisPoint := pureWZ2IsotropicMap center scale axisPoint
    have htargetAxis : targetAxisPoint ∈ tubeAxisLine
        ((pureWZ2IsotropicPaperFamily (targetDelta := targetDelta)
          sourceFamily center scale).tube index) := by
      change targetAxisPoint ∈ tubeAxisLine
        (pureWZ2IsotropicPaperTube (targetDelta := targetDelta)
          center scale (sourceFamily.tube index))
      rw [pureWZ2IsotropicPaperTube_axis center
        (lt_of_lt_of_le (by norm_num) hscale)]
      exact ⟨axisPoint, haxisPoint, rfl⟩
    have himageDist : dist
        (pureWZ2IsotropicMap center scale sourcePoint) targetAxisPoint ≤
          scale * (6 * sourceDelta) := by
      simp only [pureWZ2IsotropicMap, dist_eq_norm]
      change ‖scale • (sourcePoint - center) -
        scale • (axisPoint - center)‖ ≤ _
      rw [← smul_sub]
      have hsub : (sourcePoint - center) - (axisPoint - center) =
          sourcePoint - axisPoint := by module
      rw [hsub, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : 0 ≤ scale)]
      gcongr
      simpa [dist_eq_norm] using hsourceDist
    constructor
    · exact Metric.mem_cthickening_of_dist_le point targetAxisPoint
        (6 * targetDelta) _ htargetAxis <|
          (dist_triangle point
            (pureWZ2IsotropicMap center scale sourcePoint) targetAxisPoint)
            |>.trans (by linarith)
    · have hsourceCenter := hsourceWindow ⟨index, hsourcePoint⟩
      rw [Metric.mem_closedBall, dist_eq_norm] at hsourceCenter
      have himageNorm : ‖pureWZ2IsotropicMap center scale sourcePoint‖ ≤ 1 / 2 := by
        simp only [pureWZ2IsotropicMap, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (by linarith : 0 ≤ scale), dist_eq_norm] at hsourceCenter ⊢
        have hscalePos : 0 < scale := lt_of_lt_of_le (by norm_num) hscale
        calc
          scale * ‖sourcePoint - center‖ ≤ scale * (1 / (2 * scale)) := by gcongr
          _ = 1 / 2 := by field_simp [hscalePos.ne']
      have hpointNorm : ‖point‖ ≤ 1 := by
        calc
          ‖point‖ ≤ ‖pureWZ2IsotropicMap center scale sourcePoint‖ +
              ‖point - pureWZ2IsotropicMap center scale sourcePoint‖ := by
            exact norm_le_norm_add_norm_sub' _ _
          _ ≤ 1 / 2 + targetDelta * Real.sqrt 3 := by
            gcongr
            simpa [dist_eq_norm] using hsameCell
          _ ≤ 1 := by
            have hsqrt : Real.sqrt 3 ≤ 2 := by
              nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
                Real.sqrt_nonneg 3]
            have hnonneg : 0 ≤ scale * (6 * sourceDelta) := by positivity
            nlinarith [htargetDeltaSmall]
      exact wz2_paper_unitBall_subset_axisBox <| by
        simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall,
          dist_zero_right] using hpointNorm

theorem pureWZ2IsotropicPaperShading_carrier
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        targetDelta * Real.sqrt 3 ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale)))
    (index : Fin sourceFamily.card) :
    (pureWZ2IsotropicPaperShading sourceShading center scale
      hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
        hsourceWindow).carrier index =
      wz1PaperCubicalSaturation targetDelta
        (pureWZ2IsotropicMap center scale '' sourceShading.carrier index) := rfl

theorem pureWZ2IsotropicPaperShading_cubical
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        targetDelta * Real.sqrt 3 ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale))) :
    WZ1PaperIsCubicalShading
      (pureWZ2IsotropicPaperShading sourceShading center scale
        hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
          hsourceWindow) := by
  intro index point hpoint
  change Fin sourceFamily.card at index
  rw [pureWZ2IsotropicPaperShading_carrier] at hpoint ⊢
  exact wz1PaperCubicalSaturation_isCubical targetDelta _ point hpoint

theorem pureWZ2IsotropicPaperShading_targetWitness
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        targetDelta * Real.sqrt 3 ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale))) :
    ∀ point : {point : Point3 // point ∈
      (pureWZ2IsotropicPaperShading sourceShading center scale
        hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
          hsourceWindow).union},
      ∃ source : {point : Point3 // point ∈
        pureWZ2IsotropicMap center scale '' sourceShading.union},
        dist (point : Point3) (source : Point3) ≤
          targetDelta * Real.sqrt 3 := by
  intro point
  rcases point.property with ⟨index, hpoint⟩
  change Fin sourceFamily.card at index
  rw [pureWZ2IsotropicPaperShading_carrier] at hpoint
  rcases hpoint with ⟨sourcePoint, ⟨original, horiginal, rfl⟩, hcell⟩
  refine ⟨⟨pureWZ2IsotropicMap center scale original,
    ⟨original, ⟨index, horiginal⟩, rfl⟩⟩, ?_⟩
  apply dist_le_sqrt3_of_mem_wz1PaperGridCube htargetDelta
    (cell := wz1PaperGridIndex targetDelta point)
  · exact (mem_wz1PaperGridCube _ _ _).mpr rfl
  · exact (mem_wz1PaperGridCube _ _ _).mpr hcell.symm

/-- Reindex the isotropic paper shading along the canonical midpoint-centered
representatives used by the quotient-parent construction.  Cropped full-line
carriers are unchanged. -/
def pureWZ2IsotropicCenteredPaperShading
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        targetDelta * Real.sqrt 3 ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale))) :
    WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale) := by
  let isotropic := pureWZ2IsotropicPaperShading sourceShading center scale
    hsourceDelta htargetDelta htargetDeltaSmall hscale hradius hsourceWindow
  exact
    { carrier := fun index => isotropic.carrier ⟨index, index.isLt⟩
      measurable_carrier := fun index =>
        isotropic.measurable_carrier ⟨index, index.isLt⟩
      subset_body := fun index point hpoint => by
        let sourceIndex : Fin sourceFamily.card := ⟨index, index.isLt⟩
        have hcarrier := isotropic.subset_body sourceIndex hpoint
        change point ∈ wz1PaperTubeCarrier (pureWZ2PaperCenteredTube _)
        rw [pureWZ2PaperCenteredTube_paperCarrier]
        exact hcarrier }

@[simp] theorem pureWZ2IsotropicCenteredPaperShading_carrier
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        targetDelta * Real.sqrt 3 ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale)))
    (index : Fin sourceFamily.card) :
    (pureWZ2IsotropicCenteredPaperShading sourceShading center scale
      hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
        hsourceWindow).carrier index =
      (pureWZ2IsotropicPaperShading sourceShading center scale
        hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
          hsourceWindow).carrier index := rfl

theorem pureWZ2IsotropicCenteredPaperShading_cubical
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        targetDelta * Real.sqrt 3 ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale))) :
    WZ1PaperIsCubicalShading
      (pureWZ2IsotropicCenteredPaperShading sourceShading center scale
        hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
          hsourceWindow) := by
  intro index point hpoint
  rw [pureWZ2IsotropicCenteredPaperShading_carrier] at hpoint ⊢
  exact pureWZ2IsotropicPaperShading_cubical sourceShading center scale
    hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
      hsourceWindow index point hpoint

theorem pureWZ2IsotropicCenteredPaperShading_targetWitness
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        targetDelta * Real.sqrt 3 ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale))) :
    ∀ point : {point : Point3 // point ∈
      (pureWZ2IsotropicCenteredPaperShading sourceShading center scale
        hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
          hsourceWindow).union},
      ∃ source : {point : Point3 // point ∈
        pureWZ2IsotropicMap center scale '' sourceShading.union},
        dist (point : Point3) (source : Point3) ≤
          targetDelta * Real.sqrt 3 := by
  intro point
  let isotropic := pureWZ2IsotropicPaperShading sourceShading center scale
    hsourceDelta htargetDelta htargetDeltaSmall hscale hradius hsourceWindow
  have hpoint : (point : Point3) ∈ isotropic.union := by
    rcases point.property with ⟨index, hindex⟩
    exact ⟨⟨index, index.isLt⟩, hindex⟩
  exact pureWZ2IsotropicPaperShading_targetWitness sourceShading center scale
    hsourceDelta htargetDelta htargetDeltaSmall hscale hradius hsourceWindow
    ⟨point, hpoint⟩

/-- The union-level witness above can be chosen in the same tube carrier as
the target point. -/
theorem pureWZ2IsotropicCenteredPaperShading_tubeWitness
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        targetDelta * Real.sqrt 3 ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale)))
    (index : Fin sourceFamily.card) (point : Point3)
    (hpoint : point ∈
      (pureWZ2IsotropicCenteredPaperShading sourceShading center scale
        hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
          hsourceWindow).carrier index) :
    ∃ source : {point : Point3 // point ∈
        pureWZ2IsotropicMap center scale '' sourceShading.union},
      dist point (source : Point3) ≤ targetDelta * Real.sqrt 3 ∧
      (pureWZ2IsotropicInverse center scale source : Point3) ∈
        sourceShading.carrier index := by
  rw [pureWZ2IsotropicCenteredPaperShading_carrier,
    pureWZ2IsotropicPaperShading_carrier] at hpoint
  rcases hpoint with ⟨imagePoint, ⟨original, horiginal, himage⟩, hcell⟩
  subst imagePoint
  have hscalePos : 0 < scale := lt_of_lt_of_le (by norm_num) hscale
  let source : {point : Point3 // point ∈
      pureWZ2IsotropicMap center scale '' sourceShading.union} :=
    ⟨pureWZ2IsotropicMap center scale original,
      ⟨original, ⟨index, horiginal⟩, rfl⟩⟩
  refine ⟨source, ?_, ?_⟩
  · apply dist_le_sqrt3_of_mem_wz1PaperGridCube htargetDelta
      (cell := wz1PaperGridIndex targetDelta point)
    · exact (mem_wz1PaperGridCube _ _ _).mpr rfl
    · exact (mem_wz1PaperGridCube _ _ _).mpr hcell.symm
  · simpa [source, pureWZ2IsotropicInverse_map center hscalePos] using horiginal

/-- The centered isotropic saturation contains the exact similarity image, so
its indexed mass retains the full positive isotropic Jacobian. -/
theorem pureWZ2IsotropicCenteredPaperShading_mass_lower
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        targetDelta * Real.sqrt 3 ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale))) :
    ENNReal.ofReal (scale ^ 3) * sourceShading.mass ≤
      (pureWZ2IsotropicCenteredPaperShading sourceShading center scale
        hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
          hsourceWindow).mass := by
  have hscalePos : 0 < scale := lt_of_lt_of_le (by norm_num) hscale
  change ENNReal.ofReal (scale ^ 3) *
      (∑ index : Fin sourceFamily.card, volume (sourceShading.carrier index)) ≤
    ∑ index : Fin sourceFamily.card,
      volume ((pureWZ2IsotropicCenteredPaperShading sourceShading center scale
        hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
          hsourceWindow).carrier index)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro index _
  rw [← volume_image_wz1IsotropicRescalingMap hscalePos center
    (sourceShading.measurable_carrier index)]
  apply measure_mono
  intro point hpoint
  rw [pureWZ2IsotropicCenteredPaperShading_carrier]
  exact ⟨point, hpoint, (mem_wz1PaperGridCube _ _ _).mpr rfl⟩

/-- Reindex an isotropic paper shading along the canonical zero-based
representatives.  Cropped full-line carriers are unchanged. -/
def pureWZ2IsotropicZeroBasedPaperShading
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        targetDelta * Real.sqrt 3 ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale))) :
    WZ1PaperTubeShading
      (pureWZ2IsotropicZeroBasedPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale) := by
  let isotropic := pureWZ2IsotropicPaperShading sourceShading center scale
    hsourceDelta htargetDelta htargetDeltaSmall hscale hradius hsourceWindow
  exact
    { carrier := fun index => isotropic.carrier ⟨index, index.isLt⟩
      measurable_carrier := fun index =>
        isotropic.measurable_carrier ⟨index, index.isLt⟩
      subset_body := fun index point hpoint => by
        let sourceIndex : Fin sourceFamily.card := ⟨index, index.isLt⟩
        have hcarrier := isotropic.subset_body sourceIndex hpoint
        change point ∈ wz1PaperTubeCarrier (pureWZ2PaperZeroBasedTube _)
        rw [pureWZ2PaperZeroBasedTube_paperCarrier]
        exact hcarrier }

@[simp] theorem pureWZ2IsotropicZeroBasedPaperShading_carrier
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        targetDelta * Real.sqrt 3 ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale)))
    (index : Fin sourceFamily.card) :
    (pureWZ2IsotropicZeroBasedPaperShading sourceShading center scale
      hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
        hsourceWindow).carrier index =
      (pureWZ2IsotropicPaperShading sourceShading center scale
        hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
          hsourceWindow).carrier index := rfl

theorem pureWZ2IsotropicZeroBasedPaperShading_cubical
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        targetDelta * Real.sqrt 3 ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale))) :
    WZ1PaperIsCubicalShading
      (pureWZ2IsotropicZeroBasedPaperShading sourceShading center scale
        hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
          hsourceWindow) := by
  intro index point hpoint
  rw [pureWZ2IsotropicZeroBasedPaperShading_carrier] at hpoint ⊢
  exact pureWZ2IsotropicPaperShading_cubical sourceShading center scale
    hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
      hsourceWindow index point hpoint

theorem pureWZ2IsotropicZeroBasedPaperShading_targetWitness
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (scale : ℝ)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 4)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
        targetDelta * Real.sqrt 3 ≤ 6 * targetDelta)
    (hsourceWindow : sourceShading.union ⊆
      Metric.closedBall center (1 / (2 * scale))) :
    ∀ point : {point : Point3 // point ∈
      (pureWZ2IsotropicZeroBasedPaperShading sourceShading center scale
        hsourceDelta htargetDelta htargetDeltaSmall hscale hradius
          hsourceWindow).union},
      ∃ source : {point : Point3 // point ∈
        pureWZ2IsotropicMap center scale '' sourceShading.union},
        dist (point : Point3) (source : Point3) ≤
          targetDelta * Real.sqrt 3 := by
  intro point
  let isotropic := pureWZ2IsotropicPaperShading sourceShading center scale
    hsourceDelta htargetDelta htargetDeltaSmall hscale hradius hsourceWindow
  have hpoint : (point : Point3) ∈ isotropic.union := by
    rcases point.property with ⟨index, hindex⟩
    refine ⟨⟨index, index.isLt⟩, ?_⟩
    exact hindex
  rcases pureWZ2IsotropicPaperShading_targetWitness sourceShading center scale
      hsourceDelta htargetDelta htargetDeltaSmall hscale hradius hsourceWindow
      ⟨point, hpoint⟩ with ⟨source, hdist⟩
  exact ⟨source, hdist⟩

end Kakeya.Assouad

end
