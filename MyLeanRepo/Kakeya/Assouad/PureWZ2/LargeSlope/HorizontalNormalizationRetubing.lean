import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HorizontalNormalizationExactFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.GridCubeCover
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometryHelpers

/-!
# Cubical retubing after horizontal normalization

This layer separates the two geometric budgets needed after the exact
combined affine map: an operator-norm bound pays for the transformed source
tube radius, and one target grid-cell diameter pays for cubical saturation.
The crop inside the fixed paper box is kept as an explicit hypothesis.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

attribute [local instance] Classical.propDecidable

/-- The combined affine map transports distance by at most the operator norm
of its linear part. -/
theorem pureWZ2HorizontalNormalizedMap_dist_le
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (first second : Point3) :
    dist
        (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda first)
        (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda second) ≤
      ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda).linear
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
        dist first second := by
  let equivalence := pureWZ2HorizontalNormalizedAffineEquiv
    g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
  let linear := equivalence.linear.toContinuousLinearEquiv.toContinuousLinearMap
  have hsub : equivalence first - equivalence second =
      linear (first - second) := by
    have h := AffineMap.linearMap_vsub equivalence.toAffineMap first second
    exact h.symm
  rw [← pureWZ2HorizontalNormalizedAffineEquiv_apply g c d m
      anisotropicCenter horizontalCenter lambda hcd hm hlambda first,
    ← pureWZ2HorizontalNormalizedAffineEquiv_apply g c d m
      anisotropicCenter horizontalCenter lambda hcd hm hlambda second,
    dist_eq_norm, dist_eq_norm, hsub]
  exact linear.le_opNorm (first - second)

/-- The exact image of a source paper carrier lies in the target supporting
line neighborhood when the target radius pays for the operator-norm loss. -/
theorem pureWZ2HorizontalNormalizedExactCarrier_subset_cthickening
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    {sourceDelta targetDelta : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (source : Kakeya.DeltaTube sourceDelta)
    (hradius :
      ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda).linear
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
          (6 * sourceDelta) ≤ 6 * targetDelta) :
    pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
        horizontalCenter lambda '' wz1PaperTubeCarrier source ⊆
      Metric.cthickening (6 * targetDelta)
        (tubeAxisLine
          (pureWZ2HorizontalNormalizedExactTube g c d m anisotropicCenter
            horizontalCenter lambda hcd hm hlambda source :
              Kakeya.DeltaTube targetDelta)) := by
  intro targetPoint htargetPoint
  rcases htargetPoint with ⟨sourcePoint, hsourcePoint, rfl⟩
  rcases exists_dist_le_of_mem_cthickening_closed
      (isClosed_tubeAxisLine source) (mul_nonneg (by norm_num) hsourceDelta.le)
      hsourcePoint.1 with ⟨sourceAxisPoint, hsourceAxisPoint, hsourceDistance⟩
  let targetAxisPoint := pureWZ2HorizontalNormalizedMap g c d m
    anisotropicCenter horizontalCenter lambda sourceAxisPoint
  have htargetAxisPoint : targetAxisPoint ∈ tubeAxisLine
      (pureWZ2HorizontalNormalizedExactTube g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda source :
          Kakeya.DeltaTube targetDelta) := by
    rw [pureWZ2HorizontalNormalizedExactTube_axis g c d m
      anisotropicCenter horizontalCenter lambda hcd hm hlambda source]
    exact ⟨sourceAxisPoint, hsourceAxisPoint, rfl⟩
  have himageDistance : dist
      (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
        horizontalCenter lambda sourcePoint) targetAxisPoint ≤
      ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda).linear
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
        (6 * sourceDelta) := by
    exact (pureWZ2HorizontalNormalizedMap_dist_le g c d m
      anisotropicCenter horizontalCenter lambda hcd hm hlambda
        sourcePoint sourceAxisPoint).trans <| by
          gcongr
  exact Metric.mem_cthickening_of_dist_le _ targetAxisPoint
    (6 * targetDelta) _ htargetAxisPoint (himageDistance.trans hradius)

/-- Cubical saturation stays in the target line neighborhood after adding
one target-cell diameter to the transported source radius. -/
theorem pureWZ2HorizontalNormalizedCubicalSaturation_subset_cthickening
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    {sourceDelta targetDelta : ℝ}
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (source : Kakeya.DeltaTube sourceDelta)
    (sourceSet : Set Point3)
    (hsourceSet : sourceSet ⊆ wz1PaperTubeCarrier source)
    (hradius :
      ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda).linear
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
          (6 * sourceDelta) + 2 * targetDelta ≤ 6 * targetDelta) :
    wz1PaperCubicalSaturation targetDelta
        (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceSet) ⊆
      Metric.cthickening (6 * targetDelta)
        (tubeAxisLine
          (pureWZ2HorizontalNormalizedExactTube g c d m anisotropicCenter
            horizontalCenter lambda hcd hm hlambda source :
              Kakeya.DeltaTube targetDelta)) := by
  intro targetPoint htargetPoint
  rcases htargetPoint with
    ⟨imagePoint, ⟨sourcePoint, hsourcePoint, rfl⟩, hgrid⟩
  have hsameCell : dist targetPoint
      (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
        horizontalCenter lambda sourcePoint) < 2 * targetDelta := by
    apply wz1_paper_grid_cube_diameter_lt_two_rho htargetDelta
      (cell := wz1PaperGridIndex targetDelta targetPoint)
    · exact (mem_wz1PaperGridCube _ _ _).mpr rfl
    · exact (mem_wz1PaperGridCube _ _ _).mpr hgrid.symm
  rcases exists_dist_le_of_mem_cthickening_closed
      (isClosed_tubeAxisLine source) (mul_nonneg (by norm_num) hsourceDelta.le)
      (hsourceSet hsourcePoint).1 with
    ⟨sourceAxisPoint, hsourceAxisPoint, hsourceDistance⟩
  let targetAxisPoint := pureWZ2HorizontalNormalizedMap g c d m
    anisotropicCenter horizontalCenter lambda sourceAxisPoint
  have htargetAxisPoint : targetAxisPoint ∈ tubeAxisLine
      (pureWZ2HorizontalNormalizedExactTube g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda source :
          Kakeya.DeltaTube targetDelta) := by
    rw [pureWZ2HorizontalNormalizedExactTube_axis g c d m
      anisotropicCenter horizontalCenter lambda hcd hm hlambda source]
    exact ⟨sourceAxisPoint, hsourceAxisPoint, rfl⟩
  have himageDistance : dist
      (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
        horizontalCenter lambda sourcePoint) targetAxisPoint ≤
      ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda).linear
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
        (6 * sourceDelta) := by
    exact (pureWZ2HorizontalNormalizedMap_dist_le g c d m
      anisotropicCenter horizontalCenter lambda hcd hm hlambda
        sourcePoint sourceAxisPoint).trans <| by
          gcongr
  have htargetDistance : dist targetPoint targetAxisPoint ≤
      6 * targetDelta := by
    calc
      dist targetPoint targetAxisPoint ≤
          dist targetPoint
              (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
                horizontalCenter lambda sourcePoint) +
            dist
              (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
                horizontalCenter lambda sourcePoint) targetAxisPoint :=
        dist_triangle _ _ _
      _ ≤ 2 * targetDelta +
          ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m
            anisotropicCenter horizontalCenter lambda hcd hm hlambda).linear
              |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
            (6 * sourceDelta) := add_le_add hsameCell.le himageDistance
      _ ≤ 6 * targetDelta := by linarith
  exact Metric.mem_cthickening_of_dist_le _ targetAxisPoint
    (6 * targetDelta) _ htargetAxisPoint htargetDistance

/-- Construct the literal cubical shading once the radius and crop budgets
have been discharged. -/
def pureWZ2HorizontalNormalizedCubicalShading
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (hradius :
      ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda).linear
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
          (6 * sourceDelta) + 2 * targetDelta ≤ 6 * targetDelta)
    (hcrop : ∀ index,
      wz1PaperCubicalSaturation targetDelta
        (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index) ⊆
        Kakeya.Streamlined.axisBox 2 2 2) :
    WZ1PaperTubeShading
      (pureWZ2HorizontalNormalizedExactFamily (targetDelta := targetDelta)
        sourceFamily g c d m anisotropicCenter horizontalCenter lambda
          hcd hm hlambda) where
  carrier index := wz1PaperCubicalSaturation targetDelta
    (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
      horizontalCenter lambda '' sourceShading.carrier index)
  measurable_carrier index := wz1PaperCubicalSaturation_measurable _ _
  subset_body index := by
    change wz1PaperCubicalSaturation targetDelta
        (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index) ⊆
      wz1PaperTubeCarrier
        ((pureWZ2HorizontalNormalizedExactFamily
          (targetDelta := targetDelta) sourceFamily g c d m
            anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
          index)
    unfold wz1PaperTubeCarrier
    intro point hpoint
    constructor
    · exact pureWZ2HorizontalNormalizedCubicalSaturation_subset_cthickening
        g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
          hsourceDelta htargetDelta (sourceFamily.tube index)
            (sourceShading.carrier index) (sourceShading.subset_body index)
              hradius hpoint
    · exact hcrop index hpoint

@[simp] theorem pureWZ2HorizontalNormalizedCubicalShading_carrier
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (hradius :
      ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda).linear
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
          (6 * sourceDelta) + 2 * targetDelta ≤ 6 * targetDelta)
    (hcrop : ∀ index,
      wz1PaperCubicalSaturation targetDelta
        (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index) ⊆
        Kakeya.Streamlined.axisBox 2 2 2)
    (index : Fin sourceFamily.card) :
    (pureWZ2HorizontalNormalizedCubicalShading sourceShading g c d m
      anisotropicCenter horizontalCenter lambda hcd hm hlambda
        hsourceDelta htargetDelta hradius hcrop).carrier index =
      wz1PaperCubicalSaturation targetDelta
        (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index) :=
  rfl

/-- The constructed target shading is cubical by construction. -/
theorem pureWZ2HorizontalNormalizedCubicalShading_cubical
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (hradius :
      ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda).linear
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
          (6 * sourceDelta) + 2 * targetDelta ≤ 6 * targetDelta)
    (hcrop : ∀ index,
      wz1PaperCubicalSaturation targetDelta
        (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index) ⊆
        Kakeya.Streamlined.axisBox 2 2 2) :
    WZ1PaperIsCubicalShading
      (pureWZ2HorizontalNormalizedCubicalShading sourceShading g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda
          hsourceDelta htargetDelta hradius hcrop) := by
  intro index point hpoint
  exact wz1PaperCubicalSaturation_isCubical targetDelta _ point hpoint

/-- The exact affine image is a subshading of its cubical saturation. -/
theorem pureWZ2HorizontalNormalizedExact_subset_cubical
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (hradius :
      ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda).linear
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
          (6 * sourceDelta) + 2 * targetDelta ≤ 6 * targetDelta)
    (hcrop : ∀ index,
      wz1PaperCubicalSaturation targetDelta
        (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index) ⊆
        Kakeya.Streamlined.axisBox 2 2 2) :
    ∀ index,
      pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index ⊆
        (pureWZ2HorizontalNormalizedCubicalShading sourceShading g c d m
          anisotropicCenter horizontalCenter lambda hcd hm hlambda
            hsourceDelta htargetDelta hradius hcrop).carrier index := by
  intro index point hpoint
  exact ⟨point, hpoint, rfl⟩

/-- Every point added by a target-grid cubical saturation has an exact-image
witness in the same target cell. -/
theorem pureWZ2HorizontalNormalizedCubicalSaturation_exists_source_dist_le
    {targetDelta : ℝ} (htargetDelta : 0 < targetDelta)
    (source : Set Point3) {point : Point3}
    (hpoint : point ∈ wz1PaperCubicalSaturation targetDelta source) :
    ∃ sourcePoint ∈ source,
      dist point sourcePoint ≤ targetDelta * Real.sqrt 3 := by
  rcases hpoint with ⟨sourcePoint, hsourcePoint, hcell⟩
  refine ⟨sourcePoint, hsourcePoint, ?_⟩
  apply dist_le_sqrt3_of_mem_wz1PaperGridCube htargetDelta
    (cell := wz1PaperGridIndex targetDelta point)
  · exact (mem_wz1PaperGridCube _ _ _).mpr rfl
  · exact (mem_wz1PaperGridCube _ _ _).mpr hcell.symm

/-- Every point of the cubical target shading has an exact-image witness in
the same target cell. -/
theorem pureWZ2HorizontalNormalizedCubicalShading_targetWitness
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (hradius :
      ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda).linear
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
          (6 * sourceDelta) + 2 * targetDelta ≤ 6 * targetDelta)
    (hcrop : ∀ index,
      wz1PaperCubicalSaturation targetDelta
        (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index) ⊆
        Kakeya.Streamlined.axisBox 2 2 2) :
    ∀ point : {point : Point3 // point ∈
      (pureWZ2HorizontalNormalizedCubicalShading sourceShading g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda
          hsourceDelta htargetDelta hradius hcrop).union},
      ∃ source : {point : Point3 // point ∈
        pureWZ2HorizontalNormalizedExactImage g c d m anisotropicCenter
          horizontalCenter lambda sourceShading.union},
        dist (point : Point3) (source : Point3) ≤
          targetDelta * Real.sqrt 3 := by
  intro point
  rcases point.property with ⟨index, hpoint⟩
  change point.1 ∈ wz1PaperCubicalSaturation targetDelta
    (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
      horizontalCenter lambda '' sourceShading.carrier index) at hpoint
  rcases pureWZ2HorizontalNormalizedCubicalSaturation_exists_source_dist_le
      htargetDelta _ hpoint with ⟨imagePoint, himagePoint, hdist⟩
  rcases himagePoint with ⟨sourcePoint, hsourcePoint, heq⟩
  refine ⟨⟨imagePoint, ?_⟩, hdist⟩
  exact ⟨sourcePoint, ⟨index, hsourcePoint⟩, heq⟩

/-- Cubical saturation retains at least the exact combined-image mass. -/
theorem pureWZ2HorizontalNormalizedCubicalShading_mass_lower
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (hradius :
      ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda).linear
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
          (6 * sourceDelta) + 2 * targetDelta ≤ 6 * targetDelta)
    (hcrop : ∀ index,
      wz1PaperCubicalSaturation targetDelta
        (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index) ⊆
        Kakeya.Streamlined.axisBox 2 2 2) :
    ENNReal.ofReal (m * lambda ^ 2) * sourceShading.mass ≤
      (pureWZ2HorizontalNormalizedCubicalShading sourceShading g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda
          hsourceDelta htargetDelta hradius hcrop).mass := by
  change ENNReal.ofReal (m * lambda ^ 2) *
      (∑ index, volume (sourceShading.carrier index)) ≤
    ∑ index, volume
      (wz1PaperCubicalSaturation targetDelta
        (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro index _
  have himageMeasure : volume
      (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
        horizontalCenter lambda '' sourceShading.carrier index) ≤
    volume
      (wz1PaperCubicalSaturation targetDelta
        (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index)) :=
    measure_mono fun point hpoint => ⟨point, hpoint, rfl⟩
  rw [volume_image_pureWZ2HorizontalNormalizedMap g c d m
    anisotropicCenter horizontalCenter lambda hcd hm hlambda] at himageMeasure
  exact himageMeasure

end Kakeya.Assouad

end
