import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition63M9ReentrantTail

/-!
# Final re-entry normalization for the Proposition 6.3 M9 tail

The production M9 target already carries the exact ordinary trace, its dense
cubicalization, a uniform per-tube floor, and the dense-trace retention
estimate.  This module records only the scalar losses needed to turn those
objects into the next exact re-entry normalization.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory

/-- Purely scalar certificate for the final M9 re-entry normalization.

The production grain, target, and exact trace are indices of the certificate,
not fields that can be replaced independently. -/
structure Proposition63M9FinalReentryNormalizationCertificate
    {sigma sourceLoss sourceDeltaCutoff scale grainLoss ordinaryLoss
      outputLoss : ℝ}
    (source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff)
    (hsourceLoss : 0 < sourceLoss)
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    (sourceData : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant)
    (sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount)
    (targetData : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule)
    (finalGrain :
      Proposition63MildRescalingFiniteParentScheduleData.Proposition63MildRescalingFinalGrainData
        (outputLoss := grainLoss) sourceData.refined
        sourceData.preGrainSelected
        (targetData.quotientSchedule.jointRegularizedTarget
          targetData.jointRegularized).family targetData.finalShading)
    (normalizationExponent : ℕ) : Prop where
  grainLoss_pos : 0 < grainLoss
  ordinaryLoss_pos : 0 < ordinaryLoss
  outputLoss_pos : 0 < outputLoss
  grainLoss_le_ordinaryLoss : grainLoss ≤ ordinaryLoss
  ordinaryLoss_le_half : ordinaryLoss ≤ outputLoss / 2
  ordinary_density_absorption :
    Kakeya.realRpowENN (scale * source.delta) ordinaryLoss *
          ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN (scale * source.delta) 2) ≤
      Proposition63M9MildRescalingQuotientTargetData.finalOrdinaryDensityFloor
        (scale := scale) (sourceData := sourceData) source hsourceLoss
  dense_crop_absorption :
    Kakeya.realRpowENN (scale * source.delta) outputLoss ≤
      (73 / 100 : ENNReal) *
        Kakeya.realRpowENN (scale * source.delta) ordinaryLoss
  refinement_fraction_le_one :
    wz2PaperPureRefinementFraction
      (scale * source.delta) normalizationExponent ≤ 1

namespace Proposition63M9FinalReentryNormalizationCertificate

variable
    {sigma sourceLoss sourceDeltaCutoff scale grainLoss ordinaryLoss
      outputLoss : ℝ}
    {source : Proposition63M9NestedPreGrainSourceData
      sigma sourceLoss sourceDeltaCutoff}
    {hsourceLoss : 0 < sourceLoss}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * source.delta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData source.shading
      (source.tailExtremal hsourceLoss) source.lineClass
      source.essentiallyDistinct source.midpoint_le_three
      (source.tailPreGrain hsourceLoss) hscale hscaleDeltaSmall
      levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    {targetData : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule}
    {finalGrain :
      Proposition63MildRescalingFiniteParentScheduleData.Proposition63MildRescalingFinalGrainData
        (outputLoss := grainLoss) sourceData.refined
        sourceData.preGrainSelected
        (targetData.quotientSchedule.jointRegularizedTarget
          targetData.jointRegularized).family targetData.finalShading}
    {normalizationExponent : ℕ}

include hscale in
private theorem targetDelta_pos :
    0 < scale * source.delta :=
  mul_pos (lt_of_lt_of_le zero_lt_one hscale) source.delta_pos

include hscaleDeltaSmall in
private theorem targetDelta_small :
    scale * source.delta ≤ 1 / 24 :=
  hscaleDeltaSmall.trans (by norm_num)

include hscale hscaleDeltaSmall finalGrain in
private theorem paperBody_mass_upper :
    (wz1PaperBodyFamily
      (targetData.quotientSchedule.jointRegularizedTarget
        targetData.jointRegularized).family).mass ≤
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN (scale * source.delta) 2 *
          (targetData.quotientSchedule.jointRegularizedTarget
            targetData.jointRegularized).family.enncard := by
  let fullShading : WZ1PaperTubeShading
      (targetData.quotientSchedule.jointRegularizedTarget
        targetData.jointRegularized).family :=
    { carrier := fun index =>
        wz1PaperTubeCarrier
          ((targetData.quotientSchedule.jointRegularizedTarget
            targetData.jointRegularized).family.tube index)
      measurable_carrier := fun index =>
        wz1PaperTubeCarrier_measurable
          ((targetData.quotientSchedule.jointRegularizedTarget
            targetData.jointRegularized).family.tube index)
      subset_body := fun _ => Set.Subset.rfl }
  have upper := wz2_paper_shading_mass_upper
    (targetDelta_pos (source := source) (hscale := hscale))
    (targetDelta_small
      (source := source) (hscaleDeltaSmall := hscaleDeltaSmall))
    finalGrain.line_class fullShading
  change (wz1PaperBodyFamily
      (targetData.quotientSchedule.jointRegularizedTarget
        targetData.jointRegularized).family).mass ≤
    ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
      Kakeya.realRpowENN (scale * source.delta) 2 *
        (targetData.quotientSchedule.jointRegularizedTarget
          targetData.jointRegularized).family.enncard at upper
  exact upper

/-- The scalar floor absorption upgrades the uniform ordinary floor to the
paper-body density inequality on the exact final ordinary shading. -/
theorem finalOrdinaryShading_paper_dense
    (certificate : Proposition63M9FinalReentryNormalizationCertificate
      (ordinaryLoss := ordinaryLoss) (outputLoss := outputLoss)
      source hsourceLoss sourceData sourceSchedule targetData finalGrain
        normalizationExponent) :
    Kakeya.realRpowENN (scale * source.delta) ordinaryLoss *
          (wz1PaperBodyFamily
            (targetData.quotientSchedule.jointRegularizedTarget
              targetData.jointRegularized).family).mass ≤
      (targetData.finalOrdinaryShading source hsourceLoss).mass := by
  calc
    Kakeya.realRpowENN (scale * source.delta) ordinaryLoss *
          (wz1PaperBodyFamily
            (targetData.quotientSchedule.jointRegularizedTarget
              targetData.jointRegularized).family).mass ≤
        Kakeya.realRpowENN (scale * source.delta) ordinaryLoss *
          (((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN (scale * source.delta) 2 *
              (targetData.quotientSchedule.jointRegularizedTarget
                targetData.jointRegularized).family.enncard) := by
      gcongr
      exact paperBody_mass_upper
        (source := source) (targetData := targetData)
        (finalGrain := finalGrain)
    _ =
        (Kakeya.realRpowENN (scale * source.delta) ordinaryLoss *
          ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN (scale * source.delta) 2)) *
              (targetData.quotientSchedule.jointRegularizedTarget
                targetData.jointRegularized).family.enncard := by ring
    _ ≤
        Proposition63M9MildRescalingQuotientTargetData.finalOrdinaryDensityFloor
            (scale := scale) (sourceData := sourceData) source hsourceLoss *
          (targetData.quotientSchedule.jointRegularizedTarget
            targetData.jointRegularized).family.enncard := by
      gcongr
      exact certificate.ordinary_density_absorption
    _ ≤ (targetData.finalOrdinaryShading source hsourceLoss).mass :=
      targetData.finalOrdinaryShading_mass_lower source hsourceLoss

/-- The exact final ordinary shading is a pure extremal configuration at
`ordinaryLoss`. -/
noncomputable def ordinarySource
    (certificate : Proposition63M9FinalReentryNormalizationCertificate
      (ordinaryLoss := ordinaryLoss) (outputLoss := outputLoss)
      source hsourceLoss sourceData sourceSchedule targetData finalGrain
        normalizationExponent) :
    PureWZ2ExtremalConfiguration
      sigma ordinaryLoss (scale * source.delta) where
  family :=
    (targetData.quotientSchedule.jointRegularizedTarget
      targetData.jointRegularized).family
  shading := targetData.finalOrdinaryShading source hsourceLoss
  extremal := by
    let ambientAtOrdinary :=
      finalGrain.extremal.mono_loss certificate.grainLoss_le_ordinaryLoss
    exact
      { delta_pos := ambientAtOrdinary.delta_pos
        delta_le_one := ambientAtOrdinary.delta_le_one
        nonempty := ambientAtOrdinary.nonempty
        cwa_nearby_scales := ambientAtOrdinary.cwa_nearby_scales
        dense := by
          rw [Kakeya.Streamlined.Shading.IsLambdaDense]
          have ordinaryBody :
              (targetData.quotientSchedule.jointRegularizedTarget
                  targetData.jointRegularized).family.toBodyFamily.mass ≤
                (wz1PaperBodyFamily
                  (targetData.quotientSchedule.jointRegularizedTarget
                    targetData.jointRegularized).family).mass :=
            pureWZ2_ordinary_body_mass_le_cropped_body_mass
              ambientAtOrdinary.delta_pos
              ((targetDelta_small
                (source := source)
                (hscaleDeltaSmall := hscaleDeltaSmall)).trans (by norm_num))
              (targetData.quotientSchedule.jointRegularizedTarget
                targetData.jointRegularized).family finalGrain.line_class
          exact
            (mul_le_mul_right
              ordinaryBody
              (Kakeya.realRpowENN
                (scale * source.delta) ordinaryLoss)).trans
              certificate.finalOrdinaryShading_paper_dense
        volume_upper := by
          apply (measure_mono ?_).trans ambientAtOrdinary.volume_upper
          rintro point ⟨index, pointMem⟩
          exact ⟨index,
            targetData.finalOrdinaryShading_sub_finalShading
              source hsourceLoss index pointMem⟩ }

/-- The retained `73/100` ordinary trace and the dense-crop scalar absorption
make the literal dense cubicalization extremal at `outputLoss`. -/
theorem finalDenseExtremal
    (certificate : Proposition63M9FinalReentryNormalizationCertificate
      (ordinaryLoss := ordinaryLoss) (outputLoss := outputLoss)
      source hsourceLoss sourceData sourceSchedule targetData finalGrain
        normalizationExponent) :
    WZ2PaperCroppedIsExtremal sigma outputLoss
      (targetData.quotientSchedule.jointRegularizedTarget
        targetData.jointRegularized).family
      (targetData.finalDenseShading source hsourceLoss) := by
  have ordinaryLoss_le_output : ordinaryLoss ≤ outputLoss := by
    linarith [certificate.ordinaryLoss_le_half, certificate.outputLoss_pos]
  let ambientAtOutput :=
    finalGrain.extremal.mono_loss
      (certificate.grainLoss_le_ordinaryLoss.trans ordinaryLoss_le_output)
  exact
    { delta_pos := ambientAtOutput.delta_pos
      delta_le_one := ambientAtOutput.delta_le_one
      nonempty := ambientAtOutput.nonempty
      cwa_nearby_scales := ambientAtOutput.cwa_nearby_scales
      cubical := targetData.finalDenseShading_cubical source hsourceLoss
      dense := by
        rw [Kakeya.Streamlined.Shading.IsLambdaDense]
        have traceLeDense :
            (proposition63OrdinaryTrace
              (targetData.finalOrdinaryShading source hsourceLoss)
              (targetData.finalDenseShading source hsourceLoss)).mass ≤
            (targetData.finalDenseShading source hsourceLoss).mass := by
          apply Finset.sum_le_sum
          intro index _
          exact measure_mono Set.inter_subset_right
        calc
          Kakeya.realRpowENN (scale * source.delta) outputLoss *
                (wz1PaperBodyFamily
                  (targetData.quotientSchedule.jointRegularizedTarget
                    targetData.jointRegularized).family).mass ≤
              ((73 / 100 : ENNReal) *
                Kakeya.realRpowENN (scale * source.delta) ordinaryLoss) *
                  (wz1PaperBodyFamily
                    (targetData.quotientSchedule.jointRegularizedTarget
                      targetData.jointRegularized).family).mass := by
            gcongr
            exact certificate.dense_crop_absorption
          _ = (73 / 100 : ENNReal) *
              (Kakeya.realRpowENN (scale * source.delta) ordinaryLoss *
                (wz1PaperBodyFamily
                  (targetData.quotientSchedule.jointRegularizedTarget
                    targetData.jointRegularized).family).mass) := by ring
          _ ≤ (73 / 100 : ENNReal) *
              (targetData.finalOrdinaryShading source hsourceLoss).mass := by
            gcongr
            exact certificate.finalOrdinaryShading_paper_dense
          _ ≤
              (proposition63OrdinaryTrace
                (targetData.finalOrdinaryShading source hsourceLoss)
                (targetData.finalDenseShading source hsourceLoss)).mass :=
            targetData.finalDenseShading_trace_mass_retention
              source hsourceLoss
          _ ≤ (targetData.finalDenseShading source hsourceLoss).mass :=
            traceLeDense
      volume_upper := by
        apply (measure_mono ?_).trans ambientAtOutput.volume_upper
        rintro point ⟨index, pointMem⟩
        exact ⟨index,
          targetData.finalDenseShading_sub_finalShading
            source hsourceLoss index pointMem⟩ }

private theorem ordinary_per_tube
    (certificate : Proposition63M9FinalReentryNormalizationCertificate
      (ordinaryLoss := ordinaryLoss) (outputLoss := outputLoss)
      source hsourceLoss sourceData sourceSchedule targetData finalGrain
        normalizationExponent) :
    ∀ index,
      (Kakeya.realRpowENN (scale * source.delta) ordinaryLoss / 2) *
            volume
              ((targetData.quotientSchedule.jointRegularizedTarget
                targetData.jointRegularized).family.tube index).carrier ≤
        volume
          ((targetData.finalOrdinaryShading source hsourceLoss).carrier
            index) := by
  intro index
  have tubeUpper :
      volume
          ((targetData.quotientSchedule.jointRegularizedTarget
            targetData.jointRegularized).family.tube index).carrier ≤
        ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN (scale * source.delta) 2 := by
    calc
      volume
          ((targetData.quotientSchedule.jointRegularizedTarget
            targetData.jointRegularized).family.tube index).carrier =
          volume
            (wz2PaperInnerTube
              ((targetData.quotientSchedule.jointRegularizedTarget
                targetData.jointRegularized).family.tube index)).carrier := by
        exact Kakeya.Streamlined.tube_volume_eq _ _
      _ ≤
          volume
            (wz1PaperTubeCarrier
              ((targetData.quotientSchedule.jointRegularizedTarget
                targetData.jointRegularized).family.tube index)) :=
        measure_mono
          (wz2PaperInnerTube_carrier_subset
            (targetDelta_pos (source := source) (hscale := hscale))
            ((targetDelta_small
              (source := source)
              (hscaleDeltaSmall := hscaleDeltaSmall)).trans (by norm_num))
            ((targetData.quotientSchedule.jointRegularizedTarget
              targetData.jointRegularized).family.tube index)
            (finalGrain.line_class index))
      _ ≤ ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN (scale * source.delta) 2 :=
        (wz2PaperTubeCarrier_convex_and_volume_quadratic
          wz2_paper_tube_carrier_geometry
          (targetDelta_pos (source := source) (hscale := hscale))
          (targetDelta_small
            (source := source) (hscaleDeltaSmall := hscaleDeltaSmall))
          ((targetData.quotientSchedule.jointRegularizedTarget
            targetData.jointRegularized).family.tube index)
          (finalGrain.line_class index)).2
  calc
    (Kakeya.realRpowENN (scale * source.delta) ordinaryLoss / 2) *
          volume
            ((targetData.quotientSchedule.jointRegularizedTarget
              targetData.jointRegularized).family.tube index).carrier ≤
        Kakeya.realRpowENN (scale * source.delta) ordinaryLoss *
          volume
            ((targetData.quotientSchedule.jointRegularizedTarget
              targetData.jointRegularized).family.tube index).carrier := by
      gcongr
      rw [ENNReal.div_eq_inv_mul]
      exact mul_le_of_le_one_left (by positivity) (by norm_num)
    _ ≤ Kakeya.realRpowENN (scale * source.delta) ordinaryLoss *
          (((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN (scale * source.delta) 2) := by
      gcongr
    _ ≤
        Proposition63M9MildRescalingQuotientTargetData.finalOrdinaryDensityFloor
          (scale := scale) (sourceData := sourceData) source hsourceLoss :=
      certificate.ordinary_density_absorption
    _ ≤ volume
          ((targetData.finalOrdinaryShading source hsourceLoss).carrier
            index) :=
      targetData.finalOrdinaryShading_per_tube_lower
        source hsourceLoss index

/-- Exact identity-frame normalization of the final ordinary shading and its
literal dense cubicalization. -/
noncomputable def normalization
    (certificate : Proposition63M9FinalReentryNormalizationCertificate
      (ordinaryLoss := ordinaryLoss) (outputLoss := outputLoss)
      source hsourceLoss sourceData sourceSchedule targetData finalGrain
        normalizationExponent) :
    PureWZ2CroppedCriticalNormalizationData
      (outputLoss := outputLoss) certificate.ordinarySource
        normalizationExponent := by
  apply proposition63IdentityFullOrdinaryNormalization
    certificate.ordinaryLoss_le_half normalizationExponent
    (targetData.finalDenseShading source hsourceLoss)
    (targetData.finalDenseShading_cubical source hsourceLoss)
  · intro index
    rfl
  · calc
      wz2PaperPureRefinementFraction
            (scale * source.delta) normalizationExponent *
          (targetData.finalOrdinaryShading source hsourceLoss).mass ≤
        1 * (targetData.finalOrdinaryShading source hsourceLoss).mass := by
          gcongr
          exact certificate.refinement_fraction_le_one
      _ = (targetData.finalOrdinaryShading source hsourceLoss).mass := by simp
  · exact ordinary_per_tube certificate
  · exact targetData.finalOrdinaryShading_axial_window source hsourceLoss
  · exact finalGrain.line_class
  · apply weaken_convex_wolff_bound finalGrain.top_level_cwa
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge
      (targetDelta_pos (source := source) (hscale := hscale))
      (hscaleDeltaSmall.trans (by norm_num))
      (by
        have ordinaryLoss_le_output : ordinaryLoss ≤ outputLoss := by
          linarith [certificate.ordinaryLoss_le_half,
            certificate.outputLoss_pos]
        linarith [certificate.grainLoss_le_ordinaryLoss])
  · exact certificate.finalDenseExtremal
  · exact
      targetData.finalOrdinaryShading_ordinary_cell_containment
        source hsourceLoss
  · exact targetData.finalFamily_hasBoundedBase_four

/-- Project the exact identity normalization to the public sticky re-entry
receipt on the literal final dense shading. -/
noncomputable def reentry
    (certificate : Proposition63M9FinalReentryNormalizationCertificate
      (ordinaryLoss := ordinaryLoss) (outputLoss := outputLoss)
      source hsourceLoss sourceData sourceSchedule targetData finalGrain
        normalizationExponent) :
    PureWZ2PropStickyReentryData
      (sigma := sigma)
      (targetData.finalDenseShading source hsourceLoss)
      normalizationExponent ordinaryLoss outputLoss :=
  certificate.normalization.toPropStickyReentryData
    certificate.ordinaryLoss_pos certificate.outputLoss_pos

end Proposition63M9FinalReentryNormalizationCertificate

end Kakeya.Assouad.PureWZ2

end
