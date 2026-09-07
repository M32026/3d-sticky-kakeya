import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition63M9FinalReentryNormalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition63M9FinalReentrySchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyInitialReentrantSource
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ConfigurationWeakening

/-!
# Production initial re-entry source for the Pure WZ2 hierarchy

This module runs the genuine Proposition 6.3/M9 producer once and retains its
dependent final grain, exact ordinary trace, dense cubicalization, and sticky
re-entry certificate.  Every loss and scale cutoff is selected before the
runtime source family.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory
open PureWZ2

private theorem proposition63M9Final_selectionLoss_one
    {sourceDelta sigma sourceLoss scale : ℝ}
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
    (data : Proposition63M9MildRescalingQuotientTargetData
      sourceData sourceSchedule) :
    1 ≤ data.selectionLoss := by
  have firstNat :
      1 ≤ proposition63MildRescalingConflictDegree sourceDelta scale + 1 := by
    omega
  have first :
      (1 : ENNReal) ≤
        (proposition63MildRescalingConflictDegree sourceDelta scale + 1 :
          ℕ) := by
    exact_mod_cast firstNat
  have degreeBase :
      (1 : ENNReal) ≤
        proposition63MildRescalingQuotientConflictDegree := by
    unfold proposition63MildRescalingQuotientConflictDegree
    norm_num
  have degreePower :
      (1 : ENNReal) ≤
        (proposition63MildRescalingQuotientConflictDegree : ENNReal) ^
          sourceSchedule.scaleCount := by
    simpa using pow_le_pow_left' degreeBase sourceSchedule.scaleCount
  have logNat :
      1 ≤ Nat.log 2
          (2 * (data.quotientSchedule.selectedTarget
            data.selection).family.card) + 1 := by
    omega
  have logTerm :
      (1 : ENNReal) ≤
        (Nat.log 2
          (2 * (data.quotientSchedule.selectedTarget
            data.selection).family.card) + 1 : ℕ) := by
    exact_mod_cast logNat
  have logPower :
      (1 : ENNReal) ≤
        (Nat.log 2
          (2 * (data.quotientSchedule.selectedTarget
            data.selection).family.card) + 1 : ENNReal) ^
          (sourceSchedule.scaleCount + sourceSchedule.scaleCount + 1) := by
    simpa using pow_le_pow_left' logTerm
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount + 1)
  have finalFactor :
      (1 : ENNReal) ≤
        8 *
          (Nat.log 2
            (2 * (data.quotientSchedule.selectedTarget
              data.selection).family.card) + 1 : ENNReal) ^
            (sourceSchedule.scaleCount + sourceSchedule.scaleCount + 1) := by
    calc
      (1 : ENNReal) ≤ 8 * 1 := by norm_num
      _ ≤
          8 *
            (Nat.log 2
              (2 * (data.quotientSchedule.selectedTarget
                data.selection).family.card) + 1 : ENNReal) ^
              (sourceSchedule.scaleCount + sourceSchedule.scaleCount + 1) := by
        gcongr
  rw [Proposition63M9MildRescalingQuotientTargetData.selectionLoss]
  calc
    (1 : ENNReal) = 1 * 1 * 1 := by norm_num
    _ ≤
        ((proposition63MildRescalingConflictDegree sourceDelta scale + 1 :
            ℕ) : ENNReal) *
          (proposition63MildRescalingQuotientConflictDegree : ENNReal) ^
            sourceSchedule.scaleCount *
          (8 *
            (Nat.log 2
              (2 * (data.quotientSchedule.selectedTarget
                data.selection).family.card) + 1 : ENNReal) ^
              (sourceSchedule.scaleCount + sourceSchedule.scaleCount + 1)) := by
      gcongr

private theorem wz2PaperPureRefinementFraction_le_one_of_final_schedule
    {delta : ℝ} (deltaPos : 0 < delta) (deltaSmall : delta ≤ 1 / 12)
    (exponent : ℕ) :
    wz2PaperPureRefinementFraction delta exponent ≤ 1 := by
  have threeLeInv : (3 : ℝ) ≤ 1 / delta := by
    rw [le_div_iff₀ deltaPos]
    nlinarith
  have logOne : 1 ≤ Real.log (1 / delta) := by
    apply (Real.le_log_iff_exp_le (by positivity)).2
    exact Real.exp_one_lt_three.le.trans threeLeInv
  unfold wz2PaperPureRefinementFraction
  apply pow_le_one₀
  · positivity
  · exact ENNReal.inv_le_one.mpr (ENNReal.one_le_ofReal.mpr logOne)

/-- The production M9 path supplies the exact dependent initial state needed
by the re-entrant hierarchy.  No root restoration or independently selected
grain witness occurs in the construction. -/
theorem pureWZ2_hierarchy_initial_reentrant_source_production
    (capability : PureWZ2PropStickyCapability)
    {sigma : ℝ}
    (critical : PureWZ2CriticalPackage sigma) :
    PureWZ2HierarchyInitialReentrantSourceAt capability sigma := by
  intro callerLoss callerDelta₀ callerLossPos callerDelta₀Pos
  let outputLoss : ℝ := min (callerLoss / 2) (1 / 2)
  have outputLossPos : 0 < outputLoss := by
    dsimp only [outputLoss]
    exact lt_min (by positivity) (by norm_num)
  have outputLossLeOne : outputLoss ≤ 1 := by
    dsimp only [outputLoss]
    exact (min_le_right _ _).trans (by norm_num)
  have outputLossLtCaller : outputLoss < callerLoss := by
    have hle : outputLoss ≤ callerLoss / 2 := by
      dsimp only [outputLoss]
      exact min_le_left _ _
    linarith
  rcases exists_proposition63_m9_final_reentry_loss_schedule
      critical outputLossPos outputLossLeOne with ⟨schedule⟩
  let p : ℝ := schedule.nested.outer.preGrainLoss
  have pPos : 0 < p := schedule.nested.outer.preGrain_pos
  have pLtOne : p < 1 := by
    simpa only [p, schedule.p_eq] using schedule.p_lt_one
  have runTail : Proposition63M9FinalReentryPowerTailRunner
      (4 * p) p schedule.grainLoss (16 * p)
      schedule.robustSchedule.levelCount schedule.powerTailCutoff := by
    unfold Proposition63M9FinalReentryPowerTailRunner
    intro sourceDelta sigma sourceDeltaPos sourceDeltaLe Lplane Lslope
      sourceFamily sourceShading sourceExtremal sourceLine sourceDistinct
      sourceMidpoint preGrain planeScale slopeScale sigmaPos sigmaOne
    exact schedule.powerTail_run sourceDeltaPos sourceDeltaLe sourceShading
      sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain
      planeScale slopeScale sigmaPos sigmaOne
  rcases exists_proposition63_m9_final_scale_cutoff pLtOne callerDelta₀Pos with
    ⟨callerCutoff, callerCutoffPos, _callerCutoffOne, callerScaleLe⟩
  let sourceCutoff := min schedule.delta₀ callerCutoff
  have sourceCutoffPos : 0 < sourceCutoff :=
    lt_min schedule.delta₀_pos callerCutoffPos
  rcases proposition63_m9_nested_preGrain_source critical schedule.nested
      sourceCutoffPos with ⟨source⟩
  have sourceLeSchedule : source.delta ≤ schedule.delta₀ :=
    source.delta_le_cutoff.trans (min_le_left _ _)
  have sourceLeCaller : source.delta ≤ callerCutoff :=
    source.delta_le_cutoff.trans (min_le_right _ _)
  have sourceLePower : source.delta ≤ schedule.powerTailCutoff :=
    sourceLeSchedule.trans schedule.delta₀_le_powerTail
  have sourceDeltaOne : source.delta ≤ 1 :=
    sourceLeSchedule.trans schedule.delta₀_le_one
  let tailExtremal := source.tailExtremal pPos
  let tailPreGrain := source.tailPreGrain pPos
  have commonScale :
      (source.tailLipschitz : ℝ) =
        proposition63M9PowerScale source.delta p := by
    unfold Proposition63M9NestedPreGrainSourceData.tailLipschitz
      proposition63M9PowerScale
    exact Real.coe_toNNReal _
      (Real.rpow_nonneg source.delta_pos.le _)
  rcases runTail source.delta_pos sourceLePower source.shading tailExtremal
      source.lineClass source.essentiallyDistinct source.midpoint_le_three
      tailPreGrain (by rw [commonScale]) (by rw [commonScale])
      critical.sigma_pos critical.sigma_lt_one with
    ⟨hscale, hscaleDeltaSmall, sourceData, sourceSchedule, certificates⟩
  let scale := proposition63M9PowerScale source.delta p
  have scalePos : 0 < scale :=
    proposition63M9PowerScale_pos source.delta_pos
  have targetDeltaPos : 0 < scale * source.delta :=
    mul_pos scalePos source.delta_pos
  have targetDeltaLeTrace :
      scale * source.delta ≤ schedule.traceSchedule.delta₀ := by
    simpa only [scale, schedule.p_eq, p] using
      schedule.targetDelta_le_traceCutoff source.delta_pos sourceLeSchedule
  have targetDeltaOne : scale * source.delta ≤ 1 :=
    targetDeltaLeTrace.trans schedule.traceSchedule.delta₀_le_one
  have targetDeltaTwelve : scale * source.delta ≤ 1 / 12 :=
    targetDeltaLeTrace.trans schedule.traceSchedule.delta₀_le_twelve
  have targetDeltaLeDenseCrop :
      scale * source.delta ≤ schedule.denseCropCutoff := by
    simpa only [scale, schedule.p_eq, p] using
      schedule.finalScale_le_denseCropCutoff source.delta_pos
        (sourceLeSchedule.trans schedule.delta₀_le_finalScale)
  let certificateFor := fun targetData =>
    Classical.choice (certificates targetData)
  rcases proposition63_m9_robust_quotient_tail_with_bounds sourceData
      sourceSchedule certificateFor with ⟨targetData, finalGrain⟩
  let tailCertificate := certificateFor targetData
  let geometryConstant : ENNReal :=
    55296 * Kakeya.deltaTubeVolume 1
  have geometryConstantOne : 1 ≤ geometryConstant := by
    dsimp only [geometryConstant]
    calc
      (1 : ENNReal) = 1 * 1 := by norm_num
      _ ≤ 55296 * Kakeya.deltaTubeVolume 1 := by
        gcongr
        · norm_num
        · exact one_le_deltaTubeVolume_one
  have geometryConstantZero : geometryConstant ≠ 0 :=
    (zero_lt_one.trans_le geometryConstantOne).ne'
  have geometryConstantTop : geometryConstant ≠ ⊤ := by
    dsimp only [geometryConstant]
    exact ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top
  have selectionLossOne : 1 ≤ targetData.selectionLoss :=
    proposition63M9Final_selectionLoss_one targetData
  have grainPowerToSource :
      Kakeya.realRpowENN (scale * source.delta) schedule.grainLoss ≤
        (geometryConstant⁻¹ * ENNReal.ofReal scale) *
          ((1 / 2 : ENNReal) * sourceData.sourceDensity) := by
    calc
      Kakeya.realRpowENN (scale * source.delta) schedule.grainLoss =
          1 * Kakeya.realRpowENN
            (scale * source.delta) schedule.grainLoss := by simp
      _ ≤ targetData.selectionLoss *
          Kakeya.realRpowENN
            (scale * source.delta) schedule.grainLoss := by gcongr
      _ ≤
          ((55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
              ENNReal.ofReal scale) *
            ((1 / 2 : ENNReal) * sourceData.sourceDensity) :=
        tailCertificate.density_absorb
      _ =
          (geometryConstant⁻¹ * ENNReal.ofReal scale) *
            ((1 / 2 : ENNReal) * sourceData.sourceDensity) := by
        rfl
  let fixedDensity : ENNReal :=
    geometryConstant⁻¹ *
      ((1 / 2 : ENNReal) * ENNReal.ofReal (1 / 2000000 : ℝ))
  have fixedDensityLe : fixedDensity ≤ (1 / 200 : ENNReal) := by
    have geometryInvOne : geometryConstant⁻¹ ≤ 1 :=
      ENNReal.inv_le_one.mpr geometryConstantOne
    dsimp only [fixedDensity]
    have halfOne : (1 / 2 : ENNReal) ≤ 1 := by
      rw [ENNReal.div_eq_inv_mul]
      simpa only [mul_one] using
        (ENNReal.inv_le_one.mpr (show (1 : ENNReal) ≤ 2 by norm_num))
    calc
      geometryConstant⁻¹ *
            ((1 / 2 : ENNReal) * ENNReal.ofReal (1 / 2000000 : ℝ)) ≤
          1 * (1 * ENNReal.ofReal (1 / 2000000 : ℝ)) := by gcongr
      _ = ENNReal.ofReal (1 / 2000000 : ℝ) := by simp
      _ ≤ ENNReal.ofReal (1 / 200 : ℝ) := by
        exact ENNReal.ofReal_mono (by norm_num)
      _ = 1 / 200 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 200)]
        norm_num
  have densityCoefficientEq :
      (geometryConstant⁻¹ * ENNReal.ofReal scale) *
          ((1 / 2 : ENNReal) *
            ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3)) =
        fixedDensity * Kakeya.realRpowENN source.delta (2 * p) := by
    have scaleENNZero : ENNReal.ofReal scale ≠ 0 :=
      (ENNReal.ofReal_pos.mpr scalePos).ne'
    have scaleENNTop : ENNReal.ofReal scale ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    let s : ENNReal := ENNReal.ofReal scale
    have reduceScale : s * (s ^ 3)⁻¹ = (s ^ 2)⁻¹ := by
      rw [show s ^ 3 = s * s ^ 2 by ring]
      rw [ENNReal.mul_inv (Or.inl scaleENNZero) (Or.inl scaleENNTop)]
      rw [← mul_assoc,
        ENNReal.mul_inv_cancel scaleENNZero scaleENNTop]
      simp
    have scaleSquare :
        s ^ 2 = Kakeya.realRpowENN source.delta (-2 * p) := by
      change (ENNReal.ofReal scale) ^ 2 =
        Kakeya.realRpowENN source.delta (-2 * p)
      rw [← ENNReal.ofReal_pow scalePos.le]
      convert proposition63M9PowerScale_ennreal_pow
        (scaleLoss := p) source.delta_pos 2 using 1
      norm_num
    have scaleSquareInv :
        (s ^ 2)⁻¹ = Kakeya.realRpowENN source.delta (2 * p) := by
      rw [scaleSquare, pure_wz2_realRpowENN_inv source.delta_pos]
      congr 2
      ring
    rw [ENNReal.ofReal_div_of_pos (pow_pos scalePos 3)]
    rw [ENNReal.ofReal_pow scalePos.le]
    change
      (geometryConstant⁻¹ * s) *
          ((1 / 2 : ENNReal) *
            (ENNReal.ofReal (1 / 2000000 : ℝ) * (s ^ 3)⁻¹)) =
        fixedDensity * Kakeya.realRpowENN source.delta (2 * p)
    calc
      (geometryConstant⁻¹ * s) *
            ((1 / 2 : ENNReal) *
              (ENNReal.ofReal (1 / 2000000 : ℝ) * (s ^ 3)⁻¹)) =
          fixedDensity * (s * (s ^ 3)⁻¹) := by
        dsimp only [fixedDensity]
        ring
      _ = fixedDensity * (s ^ 2)⁻¹ := by rw [reduceScale]
      _ = fixedDensity *
          Kakeya.realRpowENN source.delta (2 * p) := by
        rw [scaleSquareInv]
  have sourceDensityExpression :
      (geometryConstant⁻¹ * ENNReal.ofReal scale) *
          ((1 / 2 : ENNReal) * sourceData.sourceDensity) =
        fixedDensity * Kakeya.realRpowENN source.delta (6 * p) := by
    rw [sourceData.sourceDensity_eq]
    change
      (geometryConstant⁻¹ * ENNReal.ofReal scale) *
            ((1 / 2 : ENNReal) *
              (ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3) *
                Kakeya.realRpowENN source.delta (4 * p))) =
        fixedDensity * Kakeya.realRpowENN source.delta (6 * p)
    rw [show
        (geometryConstant⁻¹ * ENNReal.ofReal scale) *
              ((1 / 2 : ENNReal) *
                (ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3) *
                  Kakeya.realRpowENN source.delta (4 * p))) =
            ((geometryConstant⁻¹ * ENNReal.ofReal scale) *
              ((1 / 2 : ENNReal) *
                ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3))) *
              Kakeya.realRpowENN source.delta (4 * p) by ring]
    calc
      ((geometryConstant⁻¹ * ENNReal.ofReal scale) *
            ((1 / 2 : ENNReal) *
              ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3))) *
          Kakeya.realRpowENN source.delta (4 * p) =
        (fixedDensity * Kakeya.realRpowENN source.delta (2 * p)) *
          Kakeya.realRpowENN source.delta (4 * p) := by
            rw [densityCoefficientEq]
      _ = fixedDensity *
          (Kakeya.realRpowENN source.delta (2 * p) *
            Kakeya.realRpowENN source.delta (4 * p)) := by ring
      _ = fixedDensity *
          Kakeya.realRpowENN source.delta (6 * p) := by
        rw [← realRpowENN_add source.delta_pos]
        congr 2
        ring
  have sourcePowerLeAncestor :
      Kakeya.realRpowENN source.delta (6 * p) ≤
        Kakeya.realRpowENN source.delta source.ancestorSourceLoss := by
    apply pure_wz2_rpowENN_antitone source.delta_pos sourceDeltaOne
    exact source.ancestorSourceLoss_le_sourceLoss.trans (by
      dsimp only [p]
      linarith [pPos])
  have grainPowerToAncestor :
      Kakeya.realRpowENN (scale * source.delta) schedule.grainLoss ≤
        (1 / 100 : ENNReal) *
          source.ancestorReentry.geometry.ordinaryDensity := by
    calc
      Kakeya.realRpowENN (scale * source.delta) schedule.grainLoss ≤
          (geometryConstant⁻¹ * ENNReal.ofReal scale) *
            ((1 / 2 : ENNReal) * sourceData.sourceDensity) :=
        grainPowerToSource
      _ = fixedDensity *
          Kakeya.realRpowENN source.delta (6 * p) :=
        sourceDensityExpression
      _ ≤ (1 / 200 : ENNReal) *
          Kakeya.realRpowENN source.delta source.ancestorSourceLoss := by
        gcongr
      _ = (1 / 100 : ENNReal) *
          (Kakeya.realRpowENN source.delta source.ancestorSourceLoss / 2) := by
        have oneTwoHundred : (1 / 200 : ENNReal) =
            (1 / 100 : ENNReal) * (1 / 2 : ENNReal) := by
            rw [show (200 : ENNReal) = 100 * 2 by norm_num]
            simp only [div_eq_mul_inv, one_mul]
            rw [ENNReal.mul_inv (Or.inl (by norm_num))
              (Or.inl (by norm_num))]
        calc
          (1 / 200 : ENNReal) *
                Kakeya.realRpowENN source.delta source.ancestorSourceLoss =
              ((1 / 100 : ENNReal) * (1 / 2 : ENNReal)) *
                Kakeya.realRpowENN source.delta
                  source.ancestorSourceLoss := by rw [oneTwoHundred]
          _ = (1 / 100 : ENNReal) *
              (Kakeya.realRpowENN source.delta
                source.ancestorSourceLoss / 2) := by
            simp only [div_eq_mul_inv]
            ring
      _ ≤ (1 / 100 : ENNReal) *
          source.ancestorReentry.geometry.ordinaryDensity := by
        gcongr
        exact source.ancestorReentry.ordinary_density_budget
  have grainPowerWithGeometry :
      Kakeya.realRpowENN (scale * source.delta) schedule.grainLoss *
          geometryConstant ≤
        ENNReal.ofReal scale *
          ((1 / 2 : ENNReal) * sourceData.sourceDensity) := by
    calc
      Kakeya.realRpowENN (scale * source.delta) schedule.grainLoss *
            geometryConstant ≤
          ((geometryConstant⁻¹ * ENNReal.ofReal scale) *
              ((1 / 2 : ENNReal) * sourceData.sourceDensity)) *
            geometryConstant := by gcongr
      _ = ENNReal.ofReal scale *
          ((1 / 2 : ENNReal) * sourceData.sourceDensity) := by
        rw [show
          (geometryConstant⁻¹ * ENNReal.ofReal scale) *
                ((1 / 2 : ENNReal) * sourceData.sourceDensity) *
              geometryConstant =
            (geometryConstant * geometryConstant⁻¹) *
              (ENNReal.ofReal scale *
                ((1 / 2 : ENNReal) * sourceData.sourceDensity)) by ring]
        rw [ENNReal.mul_inv_cancel geometryConstantZero geometryConstantTop,
          one_mul]
  have scaleTargetSquare :
      ENNReal.ofReal scale *
          Kakeya.realRpowENN (scale * source.delta) 2 =
        ENNReal.ofReal (scale ^ 3) *
          Kakeya.realRpowENN source.delta 2 := by
    rw [realRpowENN_mul scalePos source.delta_pos]
    have scaleTwo :
        Kakeya.realRpowENN scale 2 = ENNReal.ofReal (scale ^ 2) := by
      unfold Kakeya.realRpowENN
      congr 1
      exact Real.rpow_two scale
    rw [scaleTwo, ← mul_assoc, ← ENNReal.ofReal_mul scalePos.le]
    congr 1
    ring
  have ordinaryPower :
      Kakeya.realRpowENN (scale * source.delta) schedule.ordinaryLoss =
        Kakeya.realRpowENN (scale * source.delta) schedule.grainLoss *
          Kakeya.realRpowENN (scale * source.delta) schedule.grainLoss := by
    rw [← realRpowENN_add targetDeltaPos]
    congr 2
    rw [schedule.ordinaryLoss_eq]
    ring
  have ordinaryDensityAbsorption :
      Kakeya.realRpowENN (scale * source.delta) schedule.ordinaryLoss *
            ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN (scale * source.delta) 2) ≤
        Proposition63M9MildRescalingQuotientTargetData.finalOrdinaryDensityFloor
          (scale := scale) (sourceData := sourceData) source pPos := by
    rw [Proposition63M9MildRescalingQuotientTargetData.finalOrdinaryDensityFloor_eq]
    change
      Kakeya.realRpowENN (scale * source.delta) schedule.ordinaryLoss *
            (geometryConstant *
              Kakeya.realRpowENN (scale * source.delta) 2) ≤
        ENNReal.ofReal (scale ^ 3) *
          ((100 : ENNReal)⁻¹ *
            source.ancestorReentry.geometry.ordinaryDensity *
              ((1 / 2 : ENNReal) * sourceData.sourceDensity *
                Kakeya.realRpowENN source.delta 2))
    rw [ordinaryPower]
    calc
      (Kakeya.realRpowENN (scale * source.delta) schedule.grainLoss *
            Kakeya.realRpowENN (scale * source.delta) schedule.grainLoss) *
          (geometryConstant *
            Kakeya.realRpowENN (scale * source.delta) 2) =
        (Kakeya.realRpowENN (scale * source.delta) schedule.grainLoss *
            geometryConstant) *
          (Kakeya.realRpowENN (scale * source.delta) schedule.grainLoss *
            Kakeya.realRpowENN (scale * source.delta) 2) := by ring
      _ ≤
          (ENNReal.ofReal scale *
              ((1 / 2 : ENNReal) * sourceData.sourceDensity)) *
            (((1 / 100 : ENNReal) *
                source.ancestorReentry.geometry.ordinaryDensity) *
              Kakeya.realRpowENN (scale * source.delta) 2) := by
        gcongr
      _ =
          ENNReal.ofReal (scale ^ 3) *
            ((100 : ENNReal)⁻¹ *
              source.ancestorReentry.geometry.ordinaryDensity *
                ((1 / 2 : ENNReal) * sourceData.sourceDensity *
                  Kakeya.realRpowENN source.delta 2)) := by
        rw [show
          (ENNReal.ofReal scale *
                ((1 / 2 : ENNReal) * sourceData.sourceDensity)) *
              (((1 / 100 : ENNReal) *
                  source.ancestorReentry.geometry.ordinaryDensity) *
                Kakeya.realRpowENN (scale * source.delta) 2) =
            (ENNReal.ofReal scale *
                Kakeya.realRpowENN (scale * source.delta) 2) *
              ((100 : ENNReal)⁻¹ *
                source.ancestorReentry.geometry.ordinaryDensity *
                  ((1 / 2 : ENNReal) * sourceData.sourceDensity)) by
            norm_num
            ring]
        rw [scaleTargetSquare]
        ring
  have ordinaryLossLeHalfDensity :
      schedule.ordinaryLoss ≤ schedule.traceSchedule.densityLoss / 2 := by
    have grainLe :
        schedule.grainLoss ≤
          schedule.traceSchedule.traceSourceCeiling / 4 := by
      rw [schedule.grainLoss_eq]
      exact min_le_right _ _
    rw [schedule.ordinaryLoss_eq,
      schedule.traceSchedule.traceSourceCeiling_eq,
      schedule.traceSchedule.densityLoss_eq] at *
    linarith [schedule.traceSchedule.criticalFloor.structuralLoss_pos]
  have densityCropAbsorption :
      Kakeya.realRpowENN (scale * source.delta)
            schedule.traceSchedule.densityLoss ≤
        (73 / 100 : ENNReal) *
          Kakeya.realRpowENN
            (scale * source.delta) schedule.ordinaryLoss :=
    schedule.dense_crop_absorption targetDeltaPos targetDeltaLeDenseCrop
  have densityLossLeOutput :
      schedule.traceSchedule.densityLoss ≤ outputLoss := by
    rw [schedule.traceSchedule.densityLoss_eq]
    calc
      schedule.traceSchedule.criticalFloor.structuralLoss / 4 ≤
          schedule.traceFloorLoss / 4 := by
        gcongr
        exact schedule.traceSchedule.criticalFloor.structuralLoss_le
      _ = outputLoss / 32 := by rw [schedule.traceFloorLoss_eq]; ring
      _ ≤ outputLoss := by linarith
  have outputGapAbsorption :
      Kakeya.realRpowENN (scale * source.delta) outputLoss ≤
        (73 / 100 : ENNReal) *
          Kakeya.realRpowENN
            (scale * source.delta) schedule.ordinaryLoss :=
    (pure_wz2_rpowENN_antitone targetDeltaPos targetDeltaOne
      densityLossLeOutput).trans densityCropAbsorption
  let densityCertificate :
      Proposition63M9FinalReentryNormalizationCertificate
        (grainLoss := schedule.grainLoss)
        (ordinaryLoss := schedule.ordinaryLoss)
        (outputLoss := schedule.traceSchedule.densityLoss)
        source pPos sourceData sourceSchedule targetData finalGrain
          capability.normalizationExponent :=
    { grainLoss_pos := schedule.grainLoss_pos
      ordinaryLoss_pos := schedule.ordinaryLoss_pos
      outputLoss_pos := schedule.traceSchedule.densityLoss_pos
      grainLoss_le_ordinaryLoss := schedule.grainLoss_lt_ordinaryLoss.le
      ordinaryLoss_le_half := ordinaryLossLeHalfDensity
      ordinary_density_absorption := ordinaryDensityAbsorption
      dense_crop_absorption := densityCropAbsorption
      refinement_fraction_le_one :=
        wz2PaperPureRefinementFraction_le_one_of_final_schedule
          targetDeltaPos targetDeltaTwelve capability.normalizationExponent }
  let normalizationCertificate :
      Proposition63M9FinalReentryNormalizationCertificate
        (grainLoss := schedule.grainLoss)
        (ordinaryLoss := schedule.ordinaryLoss)
        (outputLoss := outputLoss)
        source pPos sourceData sourceSchedule targetData finalGrain
          capability.normalizationExponent :=
    { grainLoss_pos := schedule.grainLoss_pos
      ordinaryLoss_pos := schedule.ordinaryLoss_pos
      outputLoss_pos := outputLossPos
      grainLoss_le_ordinaryLoss := schedule.grainLoss_lt_ordinaryLoss.le
      ordinaryLoss_le_half := schedule.ordinaryLoss_lt_half_output.le
      ordinary_density_absorption := ordinaryDensityAbsorption
      dense_crop_absorption := outputGapAbsorption
      refinement_fraction_le_one :=
        wz2PaperPureRefinementFraction_le_one_of_final_schedule
          targetDeltaPos targetDeltaTwelve capability.normalizationExponent }
  have grainLossLeOutput : schedule.grainLoss ≤ outputLoss := by
    linarith [schedule.grainLoss_lt_ordinaryLoss,
      schedule.ordinaryLoss_lt_half_output, outputLossPos]
  have grainConstantLe :
      Kakeya.realRpowENN (scale * source.delta) (-schedule.grainLoss) ≤
        Kakeya.realRpowENN (scale * source.delta) (-outputLoss) :=
    pure_wz2_rpowENN_antitone targetDeltaPos targetDeltaOne (by
      linarith [grainLossLeOutput])
  have outputConstantTop :
      Kakeya.realRpowENN (scale * source.delta) (-outputLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let denseSubshading :=
    targetData.finalDenseShading_sub_finalShading source pPos
  let finalDenseGrain :
      Proposition63MildRescalingFiniteParentScheduleData.Proposition63MildRescalingFinalGrainData
        (outputLoss := outputLoss) sourceData.refined
        sourceData.preGrainSelected
        (targetData.quotientSchedule.jointRegularizedTarget
          targetData.jointRegularized).family
        (targetData.finalDenseShading source pPos) :=
    { line_class := finalGrain.line_class
      cubical := targetData.finalDenseShading_cubical source pPos
      extremal := normalizationCertificate.finalDenseExtremal
      top_level_cwa :=
        weaken_convex_wolff_bound finalGrain.top_level_cwa grainConstantLe
      globalGrains :=
        { f := finalGrain.globalGrains.f
          lipschitz := finalGrain.globalGrains.lipschitz
          paper_ad := by
            intro height
            apply
              ((finalGrain.globalGrains.paper_ad height).mono_set ?_).mono_const
                grainConstantLe outputConstantTop
            rintro value ⟨point, pointMem, rfl⟩
            exact
              ⟨point,
                ⟨paper_subshading_union_subset denseSubshading pointMem.1,
                  pointMem.2⟩, rfl⟩ }
      localGrains :=
        (finalGrain.localGrains.weaken_constant
          grainConstantLe outputConstantTop).restrict denseSubshading
      planeMap_vertical_bound := by
        intro sourceVertical point
        exact finalGrain.planeMap_vertical_bound sourceVertical
          ⟨point,
            paper_subshading_union_subset denseSubshading point.property⟩
      slope_bound := by
        intro sourceSlope height heightMem
        exact finalGrain.slope_bound sourceSlope height heightMem }
  let floorNormalized := densityCertificate.normalization
  let selected :=
    proposition63IdentitySubfamily floorNormalized.croppedFamily
  have floorNormalized_cropped :
      floorNormalized.croppedRefined =
        targetData.finalDenseShading source pPos :=
    rfl
  have criticalVolumeFloorOnNormalization :
      Kakeya.realRpowENN (scale * source.delta)
          (sigma + schedule.traceFloorLoss) ≤
        volume floorNormalized.croppedRefined.union :=
    floorNormalized.volume_lower_of_trace_and_pure_floor selected
      floorNormalized.croppedRefined floorNormalized.final_extremal.nonempty
      floorNormalized.cropped_cubical
      (by
        intro index point pointMem
        simpa only [selected, proposition63IdentitySubfamily_embedding] using
          pointMem)
      (Kakeya.realRpowENN
        (scale * source.delta) schedule.ordinaryLoss / 2)
      (schedule.traceSchedule.lossConstant (scale * source.delta))
      (fun index =>
        floorNormalized.framed_ordinary_per_tube selected index)
      schedule.traceSchedule.criticalFloor
      (schedule.traceSchedule.lossConstant_one
        targetDeltaPos targetDeltaLeTrace)
      (schedule.traceSchedule.lossConstant_ne_top _)
      (schedule.trace_absorption_for_ordinaryLoss
        targetDeltaPos targetDeltaLeTrace)
      floorNormalized.final_extremal.cwa_nearby_scales
      floorNormalized.final_extremal.dense
      (schedule.traceSchedule.cwa_absorption targetDeltaPos).le
      (schedule.traceSchedule.density_absorption targetDeltaPos).le
      targetDeltaTwelve
      (targetDeltaLeTrace.trans schedule.traceSchedule.delta₀_le_floor)
  have criticalVolumeFloor :
      Kakeya.realRpowENN (scale * source.delta)
          (sigma + schedule.traceFloorLoss) ≤
        volume (targetData.finalDenseShading source pPos).union :=
    by
      rw [floorNormalized_cropped] at criticalVolumeFloorOnNormalization
      exact criticalVolumeFloorOnNormalization
  have traceFloorLeOutput : schedule.traceFloorLoss ≤ outputLoss := by
    rw [schedule.traceFloorLoss_eq]
    linarith
  have finalVolumeLower :
      Kakeya.realRpowENN (scale * source.delta) (sigma + outputLoss) ≤
        volume (targetData.finalDenseShading source pPos).union :=
    (pure_wz2_rpowENN_antitone targetDeltaPos targetDeltaOne (by
      linarith [traceFloorLeOutput])).trans criticalVolumeFloor
  let reentrantTail :
      Proposition63M9ReentrantTailData sourceData.refined
        sourceData.preGrainSelected
        (targetData.quotientSchedule.jointRegularizedTarget
          targetData.jointRegularized).family
        (targetData.finalDenseShading source pPos) finalDenseGrain
          capability.normalizationExponent :=
    { volume_lower := finalVolumeLower
      source_vertical := by
        intro point
        rcases sourceData.preGrainSelected_planeMap_source point with
          ⟨sourcePoint, planeMapEq⟩
        rw [planeMapEq]
        exact source.tailPreGrain_planeMap_vertical_bound pPos sourcePoint
      source_slope := by
        intro height _heightMem
        rw [sourceData.preGrainSelected_slope_eq]
        exact source.tailPreGrain_slope_bound pPos height
      ordinaryLoss := schedule.ordinaryLoss
      reentry := normalizationCertificate.reentry
      ordinary_axial_window_eighth := by
        intro index point pointMem
        dsimp [Proposition63M9FinalReentryNormalizationCertificate.reentry,
          Proposition63M9FinalReentryNormalizationCertificate.normalization,
          PureWZ2CroppedCriticalNormalizationData.toPropStickyReentryData,
          proposition63IdentityFullOrdinaryNormalization] at pointMem
        rcases pointMem with ⟨sourcePoint, sourcePointMem, rfl⟩
        exact targetData.finalOrdinaryShading_axial_window_eighth
          source pPos index sourcePoint sourcePointMem }
  have finalDeltaLeCaller :
      scale * source.delta ≤ callerDelta₀ :=
    callerScaleLe source.delta_pos sourceLeCaller
  exact
    ⟨outputLoss, scale * source.delta, outputLossPos, outputLossLtCaller,
      targetDeltaPos, finalDeltaLeCaller,
      ⟨reentrantTail.toReentrantGrainSource⟩⟩

end Kakeya.Assouad

end
