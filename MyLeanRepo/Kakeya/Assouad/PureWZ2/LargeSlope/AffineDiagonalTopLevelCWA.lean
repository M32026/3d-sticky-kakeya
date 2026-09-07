import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalSelectedLocalizedCleanup
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalPaperCarrierEnvelope
import MyLeanRepo.Kakeya.Assouad.PropStickyConvexWolffSubfamilyTransfer
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingBridge

/-!
# Top-level cropped CWA for the localized fixed-diagonal cleanup
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

attribute [local instance] Classical.propDecidable

/-- Transfer normalized cropped CWA through one affine map when every source
carrier image lies in a controlled homothety of the corresponding target
carrier. -/
theorem pureWZ2_croppedCWA_of_affine_homothetic_envelope
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFamily : Kakeya.Streamlined.TubeFamily targetDelta}
    (equivalence : Point3 ≃ᵃ[ℝ] Point3)
    (indexEquiv : Fin targetFamily.card ≃ Fin sourceFamily.card)
    (factor : ℝ) (hfactor : 1 ≤ factor)
    (htargetDeltaPos : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 10)
    (htargetLine : WZ1PaperIsLineClass targetFamily)
    (hcarrier : ∀ index,
      equivalence '' wz1PaperTubeCarrier
          (sourceFamily.tube (indexEquiv index)) ⊆
        AffineMap.homothety
          (wz1TubeAxisZeroPoint (targetFamily.tube index)) factor ''
            wz1PaperTubeCarrier (targetFamily.tube index))
    {sourceConstant : ENNReal}
    (hsource : WZ2PaperConvexWolffBound sourceFamily sourceConstant) :
    WZ2PaperConvexWolffBound targetFamily
      (ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
        ENNReal.ofReal
          |LinearMap.det
            (equivalence.symm.linear : Point3 →ₗ[ℝ] Point3)| *
        sourceConstant) := by
  apply wz2PaperBodyConvexWolffBound_of_indexed_envelope
      (source := wz1PaperBodyFamily sourceFamily)
      (target := wz1PaperBodyFamily targetFamily)
      indexEquiv
  · intro targetSet htargetConvex
    by_cases heligible : ∃ index : Fin targetFamily.card,
        wz1PaperTubeCarrier (targetFamily.tube index) ⊆ targetSet
    · rcases heligible with ⟨eligible, heligible⟩
      let boundedTarget := targetSet ∩ Metric.closedBall (0 : Point3) 5
      let body := closure boundedTarget
      have hballConvex : Convex ℝ (Metric.closedBall (0 : Point3) 5) :=
        convex_closedBall (0 : Point3) 5
      have hboundedConvex : Convex ℝ boundedTarget :=
        htargetConvex.inter hballConvex
      have hbodyConvex : Convex ℝ body := hboundedConvex.closure
      have hbodyCompact : IsCompact body := by
        apply Metric.isCompact_of_isClosed_isBounded isClosed_closure
        exact (Metric.isBounded_closedBall.subset fun point hpoint =>
          closure_minimal (fun _ h => h.2) Metric.isClosed_closedBall hpoint)
      let eligibleZero :=
        wz1TubeAxisZeroPoint (targetFamily.tube eligible)
      have heligibleZeroNorm : ‖eligibleZero‖ ≤ 1 :=
        pureWZ2_zeroPoint_norm_le_one (htargetLine eligible)
      have hballBody : Metric.ball eligibleZero targetDelta ⊆ body := by
        intro point hpoint
        have hdist : dist point eligibleZero < targetDelta := by
          simpa [Metric.mem_ball] using hpoint
        have hcoord : ∀ coordinate : Fin 3,
            |point coordinate - eligibleZero coordinate| ≤ targetDelta := by
          intro coordinate
          exact (PiLp.dist_apply_le point eligibleZero coordinate).trans
            hdist.le
        have hzeroTwo : eligibleZero 2 = 0 :=
          wz1TubeAxisZeroPoint_coord_two _ (htargetLine eligible).vertical
        have hpointBox : point ∈ Kakeya.Streamlined.axisBox 2 2 2 := by
          simp only [Kakeya.Streamlined.axisBox]
          norm_num
          constructor
          · calc
              |point 0| = |(point 0 - eligibleZero 0) + eligibleZero 0| := by
                ring_nf
              _ ≤ |point 0 - eligibleZero 0| + |eligibleZero 0| :=
                abs_add_le _ _
              _ ≤ targetDelta + 1 / 3 :=
                add_le_add (hcoord 0) (htargetLine eligible).2.1
              _ ≤ 1 := by linarith
          constructor
          · calc
              |point 1| = |(point 1 - eligibleZero 1) + eligibleZero 1| := by
                ring_nf
              _ ≤ |point 1 - eligibleZero 1| + |eligibleZero 1| :=
                abs_add_le _ _
              _ ≤ targetDelta + 1 / 3 :=
                add_le_add (hcoord 1) (htargetLine eligible).2.2
              _ ≤ 1 := by linarith
          · rw [show point 2 = point 2 - eligibleZero 2 by
                rw [hzeroTwo, sub_zero]]
            exact (hcoord 2).trans (by linarith)
        have hpointCarrier : point ∈
            wz1PaperTubeCarrier (targetFamily.tube eligible) := by
          constructor
          · exact Metric.mem_cthickening_of_dist_le point eligibleZero
              (6 * targetDelta) _ (wz1TubeAxisZeroPoint_mem_axis _)
              (by linarith)
          · exact hpointBox
        have hpointNorm : ‖point‖ ≤ 2 :=
          pureWZ2_point_norm_le_two_of_mem_axisBox hpointBox
        exact subset_closure
          ⟨heligible hpointCarrier, by
            simpa [Metric.mem_closedBall, dist_zero_right] using
              hpointNorm.trans (by norm_num : (2 : ℝ) ≤ 5)⟩
      have hbodyInterior : (interior body).Nonempty := by
        refine ⟨eligibleZero, mem_interior.2
          ⟨Metric.ball eligibleZero targetDelta, hballBody, isOpen_ball, ?_⟩⟩
        exact mem_ball_self htargetDeltaPos
      have hbody : JohnEllipsoid.IsConvexBody body :=
        ⟨hbodyConvex, hbodyCompact, hbodyInterior⟩
      rcases pureWZ2_variable_john_homothetic_envelope
          factor hfactor body hbody with
        ⟨targetEnvelope, htargetEnvelopeConvex, htargetEnvelopeVolume,
          htargetEnvelope⟩
      let sourceEnvelope := equivalence.symm '' targetEnvelope
      have hsourceEnvelopeConvex : Convex ℝ sourceEnvelope :=
        Convex.affine_image equivalence.symm.toAffineMap htargetEnvelopeConvex
      have hsourceEnvelopeVolume : volume sourceEnvelope ≤
          (ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
            ENNReal.ofReal
              |LinearMap.det
                (equivalence.symm.linear : Point3 →ₗ[ℝ] Point3)|) *
            volume targetSet := by
        rw [wz2PaperAffineEquiv_volume_image_eq]
        have hbodyVolume : volume body ≤ volume targetSet := by
          have hbodySubset : body ⊆ closure targetSet :=
            closure_mono fun _ hpoint => hpoint.1
          have hfrontier : volume (frontier targetSet) = 0 :=
            Convex.addHaar_frontier volume htargetConvex
          calc
            volume body ≤ volume (closure targetSet) := measure_mono hbodySubset
            _ = volume targetSet := measure_closure_of_null_frontier hfrontier
        calc
          ENNReal.ofReal
                |LinearMap.det
                  (equivalence.symm.linear : Point3 →ₗ[ℝ] Point3)| *
              volume targetEnvelope ≤
            ENNReal.ofReal
                |LinearMap.det
                  (equivalence.symm.linear : Point3 →ₗ[ℝ] Point3)| *
              (ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
                volume body) := by gcongr
          _ ≤ ENNReal.ofReal
                |LinearMap.det
                  (equivalence.symm.linear : Point3 →ₗ[ℝ] Point3)| *
              (ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
                volume targetSet) := by gcongr
          _ = (ENNReal.ofReal (27 * (2 * factor - 1) ^ 3) *
                ENNReal.ofReal
                  |LinearMap.det
                    (equivalence.symm.linear : Point3 →ₗ[ℝ] Point3)|) *
              volume targetSet := by ring
      refine ⟨sourceEnvelope, hsourceEnvelopeConvex,
        hsourceEnvelopeVolume, ?_⟩
      intro targetIndex htargetCarrier sourcePoint hsourcePoint
      let targetZero := wz1TubeAxisZeroPoint (targetFamily.tube targetIndex)
      have htargetCarrierBody :
          wz1PaperTubeCarrier (targetFamily.tube targetIndex) ⊆ body := by
        intro point hpoint
        have hnorm : ‖point‖ ≤ 2 :=
          pureWZ2_point_norm_le_two_of_mem_axisBox hpoint.2
        exact subset_closure
          ⟨htargetCarrier hpoint, by
            simpa [Metric.mem_closedBall, dist_zero_right] using
              hnorm.trans (by norm_num : (2 : ℝ) ≤ 5)⟩
      have hzeroTarget : targetZero ∈ body := by
        apply htargetCarrierBody
        constructor
        · exact Metric.mem_cthickening_of_dist_le targetZero targetZero
            (6 * targetDelta) _ (wz1TubeAxisZeroPoint_mem_axis _)
            (by simp [htargetDeltaPos.le])
        · have hzeroNorm := pureWZ2_zeroPoint_norm_le_one
            (htargetLine targetIndex)
          simp only [Kakeya.Streamlined.axisBox]
          norm_num
          exact ⟨(PiLp.norm_apply_le targetZero 0).trans hzeroNorm,
            (PiLp.norm_apply_le targetZero 1).trans hzeroNorm,
            (PiLp.norm_apply_le targetZero 2).trans hzeroNorm⟩
      have himageHomothetic : equivalence sourcePoint ∈
          AffineMap.homothety targetZero factor '' body :=
        Set.image_mono htargetCarrierBody
          (hcarrier targetIndex ⟨sourcePoint, hsourcePoint, rfl⟩)
      have himage : equivalence sourcePoint ∈ targetEnvelope :=
        htargetEnvelope targetZero hzeroTarget himageHomothetic
      exact ⟨equivalence sourcePoint, himage, equivalence.symm_apply_apply sourcePoint⟩
    · refine ⟨(∅ : Set Point3), convex_empty, by simp, ?_⟩
      intro targetIndex htarget
      exact (heligible ⟨targetIndex, htarget⟩).elim
  · exact hsource

namespace PureWZ2AffineDiagonalSelectedLocalizedCleanupData

def finalTopLevelSourceWeight
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (_data : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized) : ENNReal :=
  ENNReal.ofReal scale.slopeData.rotatedSlopeScale *
    regularized.selectedWeightLevel *
      pureWZ2PopularSourceNormalization (band := band)

def finalTopLevelCardinalityLoss
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (_data : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized) : ENNReal :=
  regularized.retentionConstant *
    (pureWZ2AffineDiagonalConflictDegreeBound scale + 1) * 8

def finalTopLevelAffineLoss
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized) : ENNReal :=
  let equivalence := pureWZ2AffineDiagonalAffineEquivCentered
    scale.slopeData.frameSlope data.raw.center
    scale.slopeData.heightScale scale.slopeData.transverseScale 1
    (by linarith [scale.height_lower]) scale.transverse_pos.ne' one_ne_zero
  ENNReal.ofReal (27 * (2 * (8 * scale.slopeData.heightScale) - 1) ^ 3) *
    ENNReal.ofReal
      |LinearMap.det (equivalence.symm.linear : Point3 →ₗ[ℝ] Point3)|

private theorem final_center_norm_le_two
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized) :
    ‖data.raw.center‖ ≤ 2 := by
  have hcenter0 : |data.raw.center 0| ≤ 1 := by
    rw [data.raw.center_eq]
    simpa [pureWZ2AffineDiagonalCommonCenter, point3] using
      popular.popular.center_mem (0 : Fin 3)
  have hcenter1 : |data.raw.center 1| ≤ 1 := by
    rw [data.raw.center_eq]
    simpa [pureWZ2AffineDiagonalCommonCenter, point3] using
      popular.popular.center_mem (1 : Fin 3)
  have hcenter2 : |data.raw.center 2| ≤ 1 := by
    have hcenterHeight : data.raw.center 2 = scale.slopeData.anchor := by
      rw [data.raw.center_eq]
      simp [pureWZ2AffineDiagonalCommonCenter, point3]
    rw [hcenterHeight]
    rw [abs_le]
    exact ⟨band.lemma31.data.scaleData.slabLeft_mem.trans
        (band.left_mem.trans <| subband.left_mem.trans
          scale.slope_anchor_mem.1),
      scale.slope_anchor_mem.2.trans <| subband.right_mem.trans <|
        band.right_mem.trans
        band.lemma31.data.scaleData.slabRight_mem⟩
  have h0sq : data.raw.center 0 ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (data.raw.center 0)]
  have h1sq : data.raw.center 1 ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (data.raw.center 1)]
  have h2sq : data.raw.center 2 ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (data.raw.center 2)]
  have hnorm := point3_coord_norm_sq data.raw.center
  nlinarith [norm_nonneg data.raw.center]

/-- Closed normalized top-level CWA for the unique localized final family. -/
theorem final_top_level_cwa
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    (data : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular scale regularized) :
    WZ2PaperConvexWolffBound data.finalFamily
      (data.finalTopLevelAffineLoss *
        ((data.finalTopLevelSourceWeight⁻¹ *
          data.finalTopLevelCardinalityLoss) * band.sourceConstant)) := by
  let ambient := band.lemma31.data.cfg.family
  let selectedSource := regularized.selected.comp data.finalSourceSubfamily
  have hweightZero : data.finalTopLevelSourceWeight ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact ENNReal.ofReal_ne_zero_iff.mpr
          scale.slopeData.rotatedSlopeScale_pos
      · exact regularized.selectedWeightLevel_pos.ne'
    · exact (pureWZ2_popularSourceNormalization_pos (band := band)).ne'
  have hweightTop : data.finalTopLevelSourceWeight ≠ ⊤ := by
    unfold finalTopLevelSourceWeight
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        regularized.selectedWeightLevel_ne_top)
      pureWZ2_popularSourceNormalization_ne_top
  have hselectedCard :
      data.finalTopLevelSourceWeight * ambient.enncard ≤
        data.finalTopLevelCardinalityLoss *
          selectedSource.family.enncard := by
    change data.finalTopLevelSourceWeight *
        band.lemma31.data.cfg.family.enncard ≤
      data.finalTopLevelCardinalityLoss * data.finalFamily.enncard
    exact data.ambient_weighted_cardinality_retention
  have hsourceCWA : WZ2PaperConvexWolffBound
      data.finalSourceSubfamily.family
      ((data.finalTopLevelSourceWeight⁻¹ *
        data.finalTopLevelCardinalityLoss) * band.sourceConstant) := by
    change WZ2PaperConvexWolffBound selectedSource.family _
    exact band.lemma31.data.cfg.top_level_cwa.subfamily_of_weighted_cardinality
      selectedSource hweightZero hweightTop hselectedCard
  let hheight : scale.slopeData.heightScale ≠ 0 :=
    (lt_of_lt_of_le (by norm_num) scale.height_lower).ne'
  let htransverse : scale.slopeData.transverseScale ≠ 0 :=
    scale.transverse_pos.ne'
  let equivalence := pureWZ2AffineDiagonalAffineEquivCentered
    scale.slopeData.frameSlope data.raw.center
      scale.slopeData.heightScale scale.slopeData.transverseScale 1
      hheight htransverse one_ne_zero
  let indexEquiv : Fin data.finalFamily.card ≃
      Fin data.finalSourceSubfamily.family.card :=
    Equiv.refl _
  have hraw : WZ2PaperConvexWolffBound data.finalFamily
      (ENNReal.ofReal
          (27 * (2 * (8 * scale.slopeData.heightScale) - 1) ^ 3) *
        ENNReal.ofReal
          |LinearMap.det
            (equivalence.symm.linear : Point3 →ₗ[ℝ] Point3)| *
        ((data.finalTopLevelSourceWeight⁻¹ *
          data.finalTopLevelCardinalityLoss) * band.sourceConstant)) := by
    apply pureWZ2_croppedCWA_of_affine_homothetic_envelope
      (sourceFamily := data.finalSourceSubfamily.family)
      (targetFamily := data.finalFamily)
      equivalence indexEquiv (8 * scale.slopeData.heightScale)
    · linarith [scale.height_lower]
    · exact scale.targetDelta_pos
    · exact scale.targetDelta_le_tenth
    · exact data.final_line_class
    · intro index
      have hindex : indexEquiv index = index := rfl
      have hembedding : data.finalSourceSubfamily.embedding index =
          data.selected.orderEmbOfFin rfl index := rfl
      have hsourceTube : data.finalSourceSubfamily.family.tube index =
          band.lemma31.data.cfg.family.tube
            (regularized.selected.embedding
              (data.selected.orderEmbOfFin rfl index)) := by
        rw [data.finalSourceSubfamily.tube_eq index,
          regularized.selected.tube_eq, hembedding]
      have haxis : tubeAxisLine (data.finalFamily.tube index) =
          pureWZ2AffineDiagonalMapCentered scale.slopeData.frameSlope
            data.raw.center scale.slopeData.heightScale
              scale.slopeData.transverseScale 1 ''
            tubeAxisLine (data.finalSourceSubfamily.family.tube index) := by
        calc
          tubeAxisLine (data.finalFamily.tube index) =
              pureWZ2AffineDiagonalMapCentered
                scale.slopeData.frameSlope data.raw.center
                  scale.slopeData.heightScale
                    scale.slopeData.transverseScale 1 ''
                tubeAxisLine
                  (band.lemma31.data.cfg.family.tube
                    (regularized.selected.embedding
                      (data.selected.orderEmbOfFin rfl index))) :=
            data.final_axis_ambient index
          _ = pureWZ2AffineDiagonalMapCentered
                scale.slopeData.frameSlope data.raw.center
                  scale.slopeData.heightScale
                    scale.slopeData.transverseScale 1 ''
                tubeAxisLine (data.finalSourceSubfamily.family.tube index) := by
            rw [hsourceTube]
      have hcarrier :=
        pureWZ2_affineDiagonal_paperCarrier_image_subset_homothety
          scale.slopeData.frameSlope data.raw.center
          scale.slopeData.heightScale scale.slopeData.transverseScale
          scale.height_lower scale.transverse_pos
          (scale.transverse_le.trans (by norm_num))
          data.final_center_norm_le_two
          band.lemma31.data.cfg.extremal.delta_pos
          scale.targetDelta_eq
          (data.finalSourceSubfamily.family.tube index)
          (data.finalFamily.tube index) (data.final_line_class index) haxis
      rw [hindex]
      simpa only [equivalence,
        pureWZ2AffineDiagonalAffineEquivCentered_apply] using hcarrier
    · exact hsourceCWA
  simpa [finalTopLevelAffineLoss, equivalence, hheight, htransverse,
    mul_assoc] using hraw

end PureWZ2AffineDiagonalSelectedLocalizedCleanupData

end Kakeya.Assouad

end
