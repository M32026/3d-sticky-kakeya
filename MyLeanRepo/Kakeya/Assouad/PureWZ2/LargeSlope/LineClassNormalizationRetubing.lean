import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LineClassNormalizationNormal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.GridCubeCover
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment

/-!
# Cubical retubing for the line-class-compatible normalization

The target shading is the literal target-grid saturation of the exact image
under `diag(lambda,1,lambda)`.  Its source-to-target Jacobian is `lambda^2`;
the target tube radius and the final paper crop remain explicit hypotheses.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

attribute [local instance] Classical.propDecidable

/-- Control the source axis point at the chosen terminal height using one
occupied carrier point.  The point-coordinate bound may depend on the
coordinate, which is what permits a two-coordinate terminal localization
when the preceding affine map already controls the remaining coordinate. -/
theorem pureWZ2_paperAxis_center_coordinate_bound_of_point
    {sourceDelta : ℝ}
    {tube : Kakeya.DeltaTube sourceDelta}
    (hsourceDelta : 0 < sourceDelta)
    (hline : WZ1PaperTubeInLineClass tube)
    (center point : Point3) (heightWidth pointBound : ℝ)
    (hpointCarrier : point ∈ wz1PaperTubeCarrier tube)
    (hheight : |center 2 - point 2| ≤ heightWidth)
    (coordinate : Fin 3)
    (hpointCoordinate : |point coordinate - center coordinate| ≤ pointBound) :
    |(tubeAxisPointAtHeight tube (center 2) - center) coordinate| ≤
      2 * heightWidth + 18 * sourceDelta + pointBound := by
  let sameHeight := wz1PaperAxisPointAtHeight tube (point 2)
  have hsameDist : dist point sameHeight ≤ 18 * sourceDelta :=
    wz2_paper_carrier_same_height_dist_18delta
      hsourceDelta tube hline hpointCarrier
  have hcenterAxis : dist
      (wz1PaperAxisPointAtHeight tube (center 2)) sameHeight ≤
        2 * heightWidth :=
    wz1Paper_axisPointAtHeight_dist_le_of_axis_point hline
      (center 2) heightWidth
      (wz1PaperAxisPointAtHeight_mem_axis tube (point 2)) <| by
        rw [wz1PaperAxisPointAtHeight_coord_two hline]
        exact hheight
  have haxisEq : wz1PaperAxisPointAtHeight tube (center 2) =
      tubeAxisPointAtHeight tube (center 2) := by
    apply PiLp.ext
    intro index
    have hvertical : tube.direction 2 ≠ 0 := by
      intro hzero
      have hbound := hline.vertical
      rw [hzero, abs_zero] at hbound
      norm_num at hbound
    unfold wz1PaperAxisPointAtHeight wz1PaperDirection
    split_ifs <;>
      simp [wz1TubeAxisZeroPoint, tubeAxisPointAtHeight, hvertical,
        smul_eq_mul] <;> field_simp [hvertical] <;> ring
  rw [← haxisEq]
  calc
    |(wz1PaperAxisPointAtHeight tube (center 2) - center) coordinate| ≤
        |(wz1PaperAxisPointAtHeight tube (center 2) - sameHeight) coordinate| +
          |(sameHeight - point) coordinate| +
            |(point - center) coordinate| := by
      rw [show wz1PaperAxisPointAtHeight tube (center 2) - center =
          (wz1PaperAxisPointAtHeight tube (center 2) - sameHeight) +
            (sameHeight - point) + (point - center) by abel]
      simp only [PiLp.add_apply]
      calc
        |((wz1PaperAxisPointAtHeight tube (center 2) - sameHeight) coordinate +
              (sameHeight - point) coordinate) +
            (point - center) coordinate| ≤
            |(wz1PaperAxisPointAtHeight tube (center 2) - sameHeight) coordinate +
              (sameHeight - point) coordinate| +
              |(point - center) coordinate| := abs_add_le _ _
        _ ≤ (|(wz1PaperAxisPointAtHeight tube (center 2) - sameHeight)
                coordinate| + |(sameHeight - point) coordinate|) +
              |(point - center) coordinate| := by
            gcongr
            exact abs_add_le _ _
    _ ≤ 2 * heightWidth + 18 * sourceDelta + pointBound := by
      gcongr
      · simpa [dist_eq_norm] using
          (PiLp.norm_apply_le
            (wz1PaperAxisPointAtHeight tube (center 2) - sameHeight)
              coordinate |>.trans <| by simpa [dist_eq_norm] using hcenterAxis)
      · calc
          |(sameHeight - point) coordinate| ≤ ‖sameHeight - point‖ := by
            simpa [Real.norm_eq_abs] using
              PiLp.norm_apply_le (sameHeight - point) coordinate
          _ = dist sameHeight point := by rw [dist_eq_norm]
          _ = dist point sameHeight := dist_comm _ _
          _ ≤ 18 * sourceDelta := hsameDist
      · simpa [PiLp.sub_apply] using hpointCoordinate

/-- For `lambda >= 1`, the line-class map is `lambda`-Lipschitz. -/
theorem pureWZ2LineClassNormalizationMap_dist_le
    (center : Point3) {lambda : ℝ} (hlambda : 1 ≤ lambda)
    (first second : Point3) :
    dist (pureWZ2LineClassNormalizationMap center lambda first)
        (pureWZ2LineClassNormalizationMap center lambda second) ≤
      lambda * dist first second := by
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  rw [dist_eq_norm, dist_eq_norm]
  have hdifference :
      pureWZ2LineClassNormalizationMap center lambda first -
          pureWZ2LineClassNormalizationMap center lambda second =
        pureWZ2LineClassNormalizationLinear lambda (first - second) := by
    ext coordinate
    fin_cases coordinate <;>
      simp [pureWZ2LineClassNormalizationMap,
        pureWZ2LineClassNormalizationLinear, point3, PiLp.sub_apply] <;> ring
  rw [hdifference]
  have hsource := point3_coord_norm_sq (first - second)
  have htarget := point3_coord_norm_sq
    (pureWZ2LineClassNormalizationLinear lambda (first - second))
  have hsquare :
      ‖pureWZ2LineClassNormalizationLinear lambda (first - second)‖ ^ 2 ≤
        (lambda * ‖first - second‖) ^ 2 := by
    rw [htarget, mul_pow, hsource]
    simp only [pureWZ2LineClassNormalizationLinear, point3_coord0,
      point3_coord1, point3_coord2]
    have hscale : 1 ≤ lambda ^ 2 := by nlinarith [sq_nonneg lambda]
    have hy : (first 1 - second 1) ^ 2 ≤
        lambda ^ 2 * (first 1 - second 1) ^ 2 := by
      nlinarith [sq_nonneg (first 1 - second 1)]
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hlambdaPos.le (norm_nonneg _))).mp hsquare

/-- Exact carrier images lie in the target line neighborhood once the target
radius pays the `lambda` metric loss. -/
theorem pureWZ2LineClassNormalizationExactCarrier_subset_cthickening
    (center : Point3) {lambda : ℝ} (hlambda : 1 ≤ lambda)
    {sourceDelta targetDelta : ℝ} (hsourceDelta : 0 < sourceDelta)
    (source : Kakeya.DeltaTube sourceDelta)
    (hradius : lambda * (6 * sourceDelta) ≤ 6 * targetDelta) :
    pureWZ2LineClassNormalizationMap center lambda ''
        wz1PaperTubeCarrier source ⊆
      Metric.cthickening (6 * targetDelta)
        (tubeAxisLine
          (pureWZ2LineClassNormalizationTube center lambda
            (lt_of_lt_of_le (by norm_num) hlambda) source :
              Kakeya.DeltaTube targetDelta)) := by
  intro targetPoint htargetPoint
  rcases htargetPoint with ⟨sourcePoint, hsourcePoint, rfl⟩
  rcases exists_dist_le_of_mem_cthickening_closed
      (isClosed_tubeAxisLine source) (mul_nonneg (by norm_num) hsourceDelta.le)
      hsourcePoint.1 with ⟨sourceAxisPoint, hsourceAxisPoint, hsourceDistance⟩
  let targetAxisPoint :=
    pureWZ2LineClassNormalizationMap center lambda sourceAxisPoint
  have htargetAxisPoint : targetAxisPoint ∈ tubeAxisLine
      (pureWZ2LineClassNormalizationTube center lambda
        (lt_of_lt_of_le (by norm_num) hlambda) source :
          Kakeya.DeltaTube targetDelta) := by
    rw [pureWZ2LineClassNormalizationTube_axis]
    exact ⟨sourceAxisPoint, hsourceAxisPoint, rfl⟩
  have himageDistance : dist
      (pureWZ2LineClassNormalizationMap center lambda sourcePoint)
      targetAxisPoint ≤ lambda * (6 * sourceDelta) := by
    exact (pureWZ2LineClassNormalizationMap_dist_le center hlambda
      sourcePoint sourceAxisPoint).trans <| by gcongr
  exact Metric.mem_cthickening_of_dist_le _ targetAxisPoint
    (6 * targetDelta) _ htargetAxisPoint (himageDistance.trans hradius)

/-- Target-grid saturation stays in the target line neighborhood after one
cell-diameter allowance. -/
theorem pureWZ2LineClassNormalizationCubicalSaturation_subset_cthickening
    (center : Point3) {lambda : ℝ} (hlambda : 1 ≤ lambda)
    {sourceDelta targetDelta : ℝ}
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (source : Kakeya.DeltaTube sourceDelta) (sourceSet : Set Point3)
    (hsourceSet : sourceSet ⊆ wz1PaperTubeCarrier source)
    (hradius : lambda * (6 * sourceDelta) + 2 * targetDelta ≤
      6 * targetDelta) :
    wz1PaperCubicalSaturation targetDelta
        (pureWZ2LineClassNormalizationMap center lambda '' sourceSet) ⊆
      Metric.cthickening (6 * targetDelta)
        (tubeAxisLine
          (pureWZ2LineClassNormalizationTube center lambda
            (lt_of_lt_of_le (by norm_num) hlambda) source :
              Kakeya.DeltaTube targetDelta)) := by
  intro targetPoint htargetPoint
  rcases htargetPoint with
    ⟨imagePoint, ⟨sourcePoint, hsourcePoint, rfl⟩, hgrid⟩
  have hsameCell : dist targetPoint
      (pureWZ2LineClassNormalizationMap center lambda sourcePoint) <
        2 * targetDelta := by
    apply wz1_paper_grid_cube_diameter_lt_two_rho htargetDelta
      (cell := wz1PaperGridIndex targetDelta targetPoint)
    · exact (mem_wz1PaperGridCube _ _ _).mpr rfl
    · exact (mem_wz1PaperGridCube _ _ _).mpr hgrid.symm
  rcases exists_dist_le_of_mem_cthickening_closed
      (isClosed_tubeAxisLine source) (mul_nonneg (by norm_num) hsourceDelta.le)
      (hsourceSet hsourcePoint).1 with
    ⟨sourceAxisPoint, hsourceAxisPoint, hsourceDistance⟩
  let targetAxisPoint :=
    pureWZ2LineClassNormalizationMap center lambda sourceAxisPoint
  have htargetAxisPoint : targetAxisPoint ∈ tubeAxisLine
      (pureWZ2LineClassNormalizationTube center lambda
        (lt_of_lt_of_le (by norm_num) hlambda) source :
          Kakeya.DeltaTube targetDelta) := by
    rw [pureWZ2LineClassNormalizationTube_axis]
    exact ⟨sourceAxisPoint, hsourceAxisPoint, rfl⟩
  have himageDistance : dist
      (pureWZ2LineClassNormalizationMap center lambda sourcePoint)
      targetAxisPoint ≤ lambda * (6 * sourceDelta) := by
    exact (pureWZ2LineClassNormalizationMap_dist_le center hlambda
      sourcePoint sourceAxisPoint).trans <| by gcongr
  have htargetDistance : dist targetPoint targetAxisPoint ≤
      6 * targetDelta := by
    calc
      dist targetPoint targetAxisPoint ≤
          dist targetPoint
              (pureWZ2LineClassNormalizationMap center lambda sourcePoint) +
            dist (pureWZ2LineClassNormalizationMap center lambda sourcePoint)
              targetAxisPoint := dist_triangle _ _ _
      _ ≤ 2 * targetDelta + lambda * (6 * sourceDelta) :=
        add_le_add hsameCell.le himageDistance
      _ ≤ 6 * targetDelta := by linarith
  exact Metric.mem_cthickening_of_dist_le _ targetAxisPoint
    (6 * targetDelta) _ htargetAxisPoint htargetDistance

/-- Literal cubical shading on the exact normalized family. -/
def pureWZ2LineClassNormalizationCubicalShading
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) {lambda : ℝ} (hlambda : 1 ≤ lambda)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (hradius : lambda * (6 * sourceDelta) + 2 * targetDelta ≤
      6 * targetDelta)
    (hcrop : ∀ index,
      wz1PaperCubicalSaturation targetDelta
        (pureWZ2LineClassNormalizationMap center lambda ''
          sourceShading.carrier index) ⊆
        Kakeya.Streamlined.axisBox 2 2 2) :
    WZ1PaperTubeShading
      (pureWZ2LineClassNormalizationFamily (targetDelta := targetDelta)
        sourceFamily center lambda
          (lt_of_lt_of_le (by norm_num) hlambda)) where
  carrier index := wz1PaperCubicalSaturation targetDelta
    (pureWZ2LineClassNormalizationMap center lambda ''
      sourceShading.carrier index)
  measurable_carrier index := wz1PaperCubicalSaturation_measurable _ _
  subset_body index := by
    intro point hpoint
    exact ⟨pureWZ2LineClassNormalizationCubicalSaturation_subset_cthickening
      center hlambda hsourceDelta htargetDelta (sourceFamily.tube index)
      (sourceShading.carrier index) (sourceShading.subset_body index)
      hradius hpoint, hcrop index hpoint⟩

theorem pureWZ2LineClassNormalizationCubicalShading_cubical
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) {lambda : ℝ} (hlambda : 1 ≤ lambda)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (hradius : lambda * (6 * sourceDelta) + 2 * targetDelta ≤
      6 * targetDelta)
    (hcrop : ∀ index,
      wz1PaperCubicalSaturation targetDelta
        (pureWZ2LineClassNormalizationMap center lambda ''
          sourceShading.carrier index) ⊆
        Kakeya.Streamlined.axisBox 2 2 2) :
    WZ1PaperIsCubicalShading
      (pureWZ2LineClassNormalizationCubicalShading sourceShading center
        hlambda hsourceDelta htargetDelta hradius hcrop) := by
  intro index point hpoint
  exact wz1PaperCubicalSaturation_isCubical targetDelta _ point hpoint

/-- Every cubical target point has an exact same-cell witness. -/
theorem pureWZ2LineClassNormalizationCubicalShading_targetWitness
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) {lambda : ℝ} (hlambda : 1 ≤ lambda)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (hradius : lambda * (6 * sourceDelta) + 2 * targetDelta ≤
      6 * targetDelta)
    (hcrop : ∀ index,
      wz1PaperCubicalSaturation targetDelta
        (pureWZ2LineClassNormalizationMap center lambda ''
          sourceShading.carrier index) ⊆
        Kakeya.Streamlined.axisBox 2 2 2) :
    ∀ point : {point : Point3 // point ∈
      (pureWZ2LineClassNormalizationCubicalShading sourceShading center
        hlambda hsourceDelta htargetDelta hradius hcrop).union},
      ∃ source : {point : Point3 // point ∈
        pureWZ2LineClassNormalizationMap center lambda ''
          sourceShading.union},
        dist (point : Point3) (source : Point3) ≤
          targetDelta * Real.sqrt 3 := by
  intro point
  rcases point.property with ⟨index, imagePoint, himagePoint, hcell⟩
  refine ⟨⟨imagePoint, ?_⟩, ?_⟩
  · rcases himagePoint with ⟨sourcePoint, hsourcePoint, heq⟩
    exact ⟨sourcePoint, ⟨index, hsourcePoint⟩, heq⟩
  · apply dist_le_sqrt3_of_mem_wz1PaperGridCube htargetDelta
      (cell := wz1PaperGridIndex targetDelta point)
    · exact (mem_wz1PaperGridCube _ _ _).mpr rfl
    · exact (mem_wz1PaperGridCube _ _ _).mpr hcell.symm

/-- Cubical saturation retains the exact `lambda^2` image mass. -/
theorem pureWZ2LineClassNormalizationCubicalShading_mass_lower
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) {lambda : ℝ} (hlambda : 1 ≤ lambda)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (hradius : lambda * (6 * sourceDelta) + 2 * targetDelta ≤
      6 * targetDelta)
    (hcrop : ∀ index,
      wz1PaperCubicalSaturation targetDelta
        (pureWZ2LineClassNormalizationMap center lambda ''
          sourceShading.carrier index) ⊆
        Kakeya.Streamlined.axisBox 2 2 2) :
    ENNReal.ofReal (lambda ^ 2) * sourceShading.mass ≤
      (pureWZ2LineClassNormalizationCubicalShading sourceShading center
        hlambda hsourceDelta htargetDelta hradius hcrop).mass := by
  change ENNReal.ofReal (lambda ^ 2) *
      (∑ index, volume (sourceShading.carrier index)) ≤
    ∑ index, volume
      (wz1PaperCubicalSaturation targetDelta
        (pureWZ2LineClassNormalizationMap center lambda ''
          sourceShading.carrier index))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro index _
  have himageMeasure : volume
      (pureWZ2LineClassNormalizationMap center lambda ''
        sourceShading.carrier index) ≤
    volume (wz1PaperCubicalSaturation targetDelta
      (pureWZ2LineClassNormalizationMap center lambda ''
        sourceShading.carrier index)) :=
    measure_mono fun point hpoint => ⟨point, hpoint, rfl⟩
  rw [pureWZ2LineClassNormalizationMap_volume_image center lambda
    (lt_of_lt_of_le (by norm_num) hlambda)] at himageMeasure
  exact himageMeasure

end Kakeya.Assouad

end
