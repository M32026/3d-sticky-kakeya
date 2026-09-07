import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7OrdinaryRetubing
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalTopLevelCWA

/-!
# Convex--Wolff bounds for the Node 7 ordinary retubing

The selected source CWA is transported through the direct affine map to the
localized family, then preserved under the same-axis radius enlargement.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

attribute [local instance] Classical.propDecidable

namespace PureWZ2Node7AffineDiagonalPreparationData

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}

/-- The CWA constant of the directly selected source family. -/
def selectedSourceTopLevelConstant
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) : ENNReal :=
  ((pureWZ2PopularSourceNormalization
      (band := commonSource.commonBand.band))⁻¹ *
      data.sourceRegularization.regularized.retentionConstant) *
    commonSource.commonBand.band.sourceConstant

/-- The single affine-envelope loss used before ordinary retubing. -/
def selectedAffineTopLevelLoss
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) : ENNReal :=
  let scale := data.node7Scale.affineScale
  let equivalence := pureWZ2AffineDiagonalAffineEquivCentered
    scale.slopeData.frameSlope data.selected.center
    scale.slopeData.heightScale scale.slopeData.transverseScale 1
    (by linarith [scale.height_lower]) scale.transverse_pos.ne' one_ne_zero
  ENNReal.ofReal
      (27 * (2 * (8 * scale.slopeData.heightScale) - 1) ^ 3) *
    ENNReal.ofReal
      |LinearMap.det (equivalence.symm.linear : Point3 →ₗ[ℝ] Point3)|

private theorem selected_center_norm_le_two
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    ‖data.selected.center‖ ≤ 2 := by
  let band := commonSource.commonBand.band
  let subband := commonSource.subband
  let scale := data.node7Scale.affineScale
  have hcenter0 : |data.selected.center 0| ≤ 1 := by
    rw [data.selected.center_eq]
    simpa [pureWZ2AffineDiagonalCommonCenter, point3] using
      data.popular.popular.center_mem (0 : Fin 3)
  have hcenter1 : |data.selected.center 1| ≤ 1 := by
    rw [data.selected.center_eq]
    simpa [pureWZ2AffineDiagonalCommonCenter, point3] using
      data.popular.popular.center_mem (1 : Fin 3)
  have hcenter2 : |data.selected.center 2| ≤ 1 := by
    have hcenterHeight : data.selected.center 2 =
        scale.slopeData.anchor := by
      rw [data.selected.center_eq]
      simp [scale, pureWZ2AffineDiagonalCommonCenter, point3]
    rw [hcenterHeight, abs_le]
    exact ⟨band.lemma31.data.scaleData.slabLeft_mem.trans
        (band.left_mem.trans <| subband.left_mem.trans
          scale.slope_anchor_mem.1),
      scale.slope_anchor_mem.2.trans <| subband.right_mem.trans <|
        band.right_mem.trans
        band.lemma31.data.scaleData.slabRight_mem⟩
  have h0sq : data.selected.center 0 ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (data.selected.center 0)]
  have h1sq : data.selected.center 1 ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (data.selected.center 1)]
  have h2sq : data.selected.center 2 ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (data.selected.center 2)]
  have hnorm := point3_coord_norm_sq data.selected.center
  nlinarith [norm_nonneg data.selected.center]

/-- Direct selected-family CWA, with no cleanup or cardinality loss. -/
theorem selected_localized_top_level_cwa
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    WZ2PaperConvexWolffBound data.selected.localizedFamily
      (data.selectedAffineTopLevelLoss *
        data.selectedSourceTopLevelConstant) := by
  let band := commonSource.commonBand.band
  let scale := data.node7Scale.affineScale
  let sourceFamily := data.sourceRegularization.regularized.selected.family
  have hsourceCWA : WZ2PaperConvexWolffBound sourceFamily
      data.selectedSourceTopLevelConstant := by
    exact data.sourceRegularization.regularized.top_level_cwa
      band.lemma31.data.cfg.top_level_cwa
      (pureWZ2_popularSourceNormalization_pos (band := band)).ne'
      pureWZ2_popularSourceNormalization_ne_top
  let hheight : scale.slopeData.heightScale ≠ 0 :=
    (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
  let htransverse : scale.slopeData.transverseScale ≠ 0 :=
    scale.transverse_pos.ne'
  let equivalence := pureWZ2AffineDiagonalAffineEquivCentered
    scale.slopeData.frameSlope data.selected.center
    scale.slopeData.heightScale scale.slopeData.transverseScale 1
    hheight htransverse one_ne_zero
  let indexEquiv : Fin data.selected.localizedFamily.card ≃
      Fin sourceFamily.card := Equiv.refl _
  have hraw : WZ2PaperConvexWolffBound data.selected.localizedFamily
      (ENNReal.ofReal
          (27 * (2 * (8 * scale.slopeData.heightScale) - 1) ^ 3) *
        ENNReal.ofReal
          |LinearMap.det
            (equivalence.symm.linear : Point3 →ₗ[ℝ] Point3)| *
        data.selectedSourceTopLevelConstant) := by
    apply pureWZ2_croppedCWA_of_affine_homothetic_envelope
      (sourceFamily := sourceFamily)
      (targetFamily := data.selected.localizedFamily)
      equivalence indexEquiv (8 * scale.slopeData.heightScale)
    · linarith [scale.height_lower]
    · exact scale.targetDelta_pos
    · exact scale.targetDelta_le_tenth
    · exact data.selected.localized_line_class
    · intro index
      have hindex : indexEquiv index = index := rfl
      have haxis : tubeAxisLine
            (data.selected.localizedFamily.tube index) =
          pureWZ2AffineDiagonalMapCentered
              scale.slopeData.frameSlope data.selected.center
              scale.slopeData.heightScale scale.slopeData.transverseScale 1 ''
            tubeAxisLine (sourceFamily.tube index) :=
        data.selected.localized_axis index
      have hcarrier :=
        pureWZ2_affineDiagonal_paperCarrier_image_subset_homothety
          scale.slopeData.frameSlope data.selected.center
          scale.slopeData.heightScale scale.slopeData.transverseScale
          scale.height_lower scale.transverse_pos
          (scale.transverse_le.trans (by norm_num))
          data.selected_center_norm_le_two
          band.lemma31.data.cfg.extremal.delta_pos
          scale.targetDelta_eq
          (sourceFamily.tube index)
          (data.selected.localizedFamily.tube index)
          (data.selected.localized_line_class index) haxis
      rw [hindex]
      simpa only [equivalence,
        pureWZ2AffineDiagonalAffineEquivCentered_apply] using hcarrier
    · exact hsourceCWA
  simpa [selectedAffineTopLevelLoss, equivalence, hheight, htransverse,
    mul_assoc] using hraw

/-- The same-axis ordinary family remains in the paper line class. -/
theorem ordinaryFamily_line_class
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    WZ1PaperIsLineClass data.ordinaryFamily := by
  intro index
  exact data.selected.localized_line_class index

/-- Enlarging every paper carrier along the same axis preserves the CWA with
exactly the same constant. -/
theorem ordinaryFamily_top_level_cwa
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    WZ2PaperConvexWolffBound data.ordinaryFamily
      (data.selectedAffineTopLevelLoss *
        data.selectedSourceTopLevelConstant) := by
  apply WZ2PaperBodyConvexWolffBound.of_pointwise_subset
    (source := wz1PaperBodyFamily data.selected.localizedFamily)
    (target := wz1PaperBodyFamily data.ordinaryFamily) rfl
  · intro index
    change wz1PaperTubeCarrier
        (data.selected.localizedFamily.tube index) ⊆
      wz1PaperTubeCarrier (data.ordinaryFamily.tube index)
    intro point hpoint
    refine ⟨?_, hpoint.2⟩
    have hthick : point ∈ Metric.cthickening
        (6 * data.node7Scale.affineScale.targetDelta)
        (tubeAxisLine (data.selected.localizedFamily.tube index)) :=
      hpoint.1
    change point ∈ Metric.cthickening
      (6 * data.finalRadius)
      (tubeAxisLine
        (sameAxisTube
          (rho := data.finalRadius)
          (data.selected.localizedFamily.tube index)))
    exact Metric.cthickening_mono
      (by
        unfold PureWZ2Node7AffineDiagonalPreparationData.finalRadius
        nlinarith [data.node7Scale.affineScale.targetDelta_pos])
      (tubeAxisLine (data.selected.localizedFamily.tube index)) hthick
  · exact data.selected_localized_top_level_cwa

end PureWZ2Node7AffineDiagonalPreparationData

end Kakeya.Assouad

end
