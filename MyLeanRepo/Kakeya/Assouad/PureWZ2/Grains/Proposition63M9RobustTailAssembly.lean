import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9MildRescalingQuotientAssembly

/-!
# Proposition 6.3 M9: robust pre-grain to quotient tail

This module records the exact remaining boundary after the robust middle has
produced a general pre-grain.  Source-side regularization is delegated to the
existing mild-rescaling producer.  Target-side scalar certificates are
quantified over its actual quotient target, so no independently selected
target witness is identified with the produced one.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- The source-side scalar receipts still required after a robust pre-grain
has been constructed.  Geometric line, distinctness, and midpoint provenance
remain separate arguments of the producer below. -/
structure Proposition63M9RobustTailSourceCertificates
    {sourceDelta sourceLoss scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (hscale : 1 ≤ scale) (levelCount : ℕ)
    (sourceOutputConstant : ENNReal) where
  scale_delta_small : scale * sourceDelta ≤ 1 / 1000
  ambient_two : (2 : ENNReal) <
    Kakeya.realRpowENN sourceDelta (-sourceLoss)
  levels : ENNReal.ofReal (1 / sourceDelta) ≤
    Kakeya.realRpowENN sourceDelta (-sourceLoss) ^ levelCount
  output_ne_top : sourceOutputConstant ≠ ⊤
  output_window :
    Kakeya.realRpowENN sourceDelta (-sourceLoss) *
        Kakeya.realRpowENN sourceDelta (-sourceLoss) ≤
      sourceOutputConstant
  regularization_absorb :
    let density :=
      ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3) *
        Kakeya.realRpowENN sourceDelta sourceLoss
    let degreeConstant :=
      16 * ((levelCount + 1 : ℕ) : ENNReal) *
        (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
          (levelCount + 1)
    let regularizationLoss :=
      (8 : ENNReal) *
        (Nat.log 2 (2 * sourceFamily.card) + 1 : ENNReal) ^
          (levelCount + 2)
    let weight := (1 / 2 : ENNReal) * density
    let cardinalityLoss :=
      (2 * regularizationLoss) *
        (55296 * Kakeya.deltaTubeVolume 1)
    max degreeConstant
        ((weight⁻¹ *
            (Kakeya.realRpowENN sourceDelta (-sourceLoss) *
              cardinalityLoss * degreeConstant)) *
          Kakeya.realRpowENN sourceDelta (-sourceLoss)) ≤
      sourceOutputConstant

/-- Apply the existing source-side mild-rescaling producer to a current
pre-grain.  No family, shading, or pre-grain map is replaced. -/
theorem proposition63_m9_robust_tail_source
    {sourceDelta sigma sourceLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading)
    (sourceLine : WZ1PaperIsLineClass sourceFamily)
    (sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily)
    (sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3)
    (preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1)
    (hscale : 1 ≤ scale) (levelCount : ℕ)
    (sourceOutputConstant : ENNReal)
    (certificates : Proposition63M9RobustTailSourceCertificates
      (sourceLoss := sourceLoss) (sourceFamily := sourceFamily) hscale
      levelCount sourceOutputConstant) :
    Nonempty (Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      certificates.scale_delta_small levelCount sourceOutputConstant) := by
  exact proposition63_m9_mild_rescaling_source sourceShading sourceExtremal
    sourceLine sourceDistinct sourceMidpoint preGrain hscale
    certificates.scale_delta_small levelCount certificates.ambient_two
    certificates.levels sourceOutputConstant certificates.output_ne_top
    certificates.output_window certificates.regularization_absorb

/-- Scalar obligations for the actual quotient target selected by the
existing target producer.  Keeping this package dependent on `targetData`
prevents certificates for an independently selected quotient witness from
being substituted. -/
structure Proposition63M9RobustQuotientTailCertificates
    {sourceDelta sigma sourceLoss outputLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    {sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount}
    (targetData : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) where
  targetConstant : ENNReal
  target_finite : WZ2PaperFiniteErrorConstant targetConstant
  scale_budget :
    Proposition63MildRescalingQuotientScheduleData.quotientScaleWindowConstant
      scheduleWindowConstant ≤ targetConstant
  constant_budget : ∀ _coordinate : Fin sourceSchedule.scaleCount,
    max (targetData.quotientSchedule.quotientFiberRegularizationConstant
        targetData.selection)
      (targetData.quotientSchedule.quotientScheduleBodyConstant
        targetData.jointRegularized
        (((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
          ENNReal.ofReal scale) *
          ((1 / 2 : ENNReal) * sourceData.sourceDensity))
        (targetData.selectionLoss *
          (55296 * Kakeya.deltaTubeVolume 1))) ≤ targetConstant
  final_cwa_absorb : (4 : ENNReal) * targetConstant ≤
    Kakeya.realRpowENN (scale * sourceDelta) (-outputLoss)
  density_absorb : targetData.selectionLoss *
      Kakeya.realRpowENN (scale * sourceDelta) outputLoss ≤
    ((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
      ENNReal.ofReal scale) *
      ((1 / 2 : ENNReal) * sourceData.sourceDensity)
  volume_absorb : ENNReal.ofReal (scale ^ 3) *
      Kakeya.realRpowENN sourceDelta (sigma - sourceLoss) ≤
    Kakeya.realRpowENN (scale * sourceDelta) (sigma - outputLoss)
  source_loss_pos : 0 < sourceLoss
  source_loss_lt : sourceLoss < outputLoss
  ad_absorb : Real.rpow sourceDelta (outputLoss - sourceLoss) ≤
    Real.rpow scale (-outputLoss)
  plane_scale : (Lplane : ℝ) ≤ scale
  slope_scale : (Lslope : ℝ) ≤ scale
  sigma_pos : 0 < sigma
  sigma_lt_one : sigma < 1

/-- Run the quotient target producer while retaining the exact transported
slope and plane-map provenance for the Node-5-private quantitative output. -/
theorem proposition63_m9_robust_quotient_tail_with_bounds
    {sourceDelta sigma sourceLoss outputLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    (sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant)
    (sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount)
    (certificates : ∀ targetData :
      Proposition63M9MildRescalingQuotientTargetData sourceData sourceSchedule,
      Proposition63M9RobustQuotientTailCertificates
        (outputLoss := outputLoss) targetData) :
    Nonempty (Sigma fun targetData :
      Proposition63M9MildRescalingQuotientTargetData sourceData sourceSchedule =>
      Proposition63MildRescalingFiniteParentScheduleData.Proposition63MildRescalingFinalGrainData
          (outputLoss := outputLoss) sourceData.refined
          sourceData.preGrainSelected
          (targetData.quotientSchedule.jointRegularizedTarget
            targetData.jointRegularized).family targetData.finalShading) := by
  rcases sourceData.buildQuotientTarget sourceSchedule with ⟨targetData⟩
  let cert := certificates targetData
  rcases targetData.finalGrainConfigurationWithBounds cert.targetConstant
      cert.target_finite cert.scale_budget cert.constant_budget
      cert.final_cwa_absorb cert.density_absorb cert.volume_absorb
      cert.source_loss_pos cert.source_loss_lt cert.ad_absorb cert.plane_scale
      cert.slope_scale cert.sigma_pos cert.sigma_lt_one with ⟨grain⟩
  exact ⟨targetData, grain⟩

/-- Paper-facing compatibility projection of the construction-aware tail. -/
theorem proposition63_m9_robust_quotient_tail
    {sourceDelta sigma sourceLoss outputLoss scale : ℝ}
    {Lplane Lslope : NNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss sourceFamily sourceShading}
    {sourceLine : WZ1PaperIsLineClass sourceFamily}
    {sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily}
    {sourceMidpoint : ∀ index,
      ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3}
    {preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {hscale : 1 ≤ scale}
    {hscaleDeltaSmall : scale * sourceDelta ≤ 1 / 1000}
    {levelCount : ℕ}
    {sourceOutputConstant scheduleConstant scheduleWindowConstant : ENNReal}
    {scheduleLevelCount : ℕ}
    (sourceData : Proposition63M9MildRescalingSourceData sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain hscale
      hscaleDeltaSmall levelCount sourceOutputConstant)
    (sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceData.selected.family) scheduleConstant
      scheduleWindowConstant scheduleLevelCount)
    (certificates : ∀ targetData :
      Proposition63M9MildRescalingQuotientTargetData sourceData sourceSchedule,
      Proposition63M9RobustQuotientTailCertificates
        (outputLoss := outputLoss) targetData) :
    Nonempty (PureWZ2GrainConfiguration sigma outputLoss
      (scale * sourceDelta)) := by
  rcases proposition63_m9_robust_quotient_tail_with_bounds sourceData
      sourceSchedule certificates with ⟨targetData, result⟩
  exact ⟨result.toGrainConfiguration⟩

end Kakeya.Assouad.PureWZ2

end
