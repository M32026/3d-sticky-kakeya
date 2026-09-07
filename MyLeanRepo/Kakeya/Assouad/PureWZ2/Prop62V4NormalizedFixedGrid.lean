import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PaperFinalV4FixedGridPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers

/-!
# Fixed-grid preparation from a normalized pure source

This module applies the frozen fixed-grid boundary-removal theorem directly
to `PureWZ2CroppedCriticalNormalizationData`.

The boundary estimate uses the historical top-level CWA already stored in
`normalized.cropped_top_level_cwa`.  The cleaned extremal structure keeps the
pure nearby-scale CWA from `normalized.final_extremal`; no historical nearby
CWA is assumed or constructed.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open MeasureTheory
open Kakeya.Assouad

private theorem normalizedFixedGrid_directionLevelCount_le_logEnvelope
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1) :
    logarithmicLoss delta ≤
      2 * ENNReal.ofReal (1 + Real.log delta⁻¹) := by
  have logNonneg : 0 ≤ Real.log delta⁻¹ := by
    exact Real.log_nonneg ((one_le_inv₀ deltaPos).mpr deltaLeOne)
  have quotientNonneg :
      0 ≤ Real.log delta⁻¹ / Real.log 2 := by
    positivity
  have floorLe :
      (Nat.floor (Real.log delta⁻¹ / Real.log 2) : ℝ) ≤
        Real.log delta⁻¹ / Real.log 2 :=
    Nat.floor_le quotientNonneg
  have logTwoHalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have bound :
        Real.log (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    have rewrite :
        Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num)]
      simp
    rw [rewrite] at bound
    linarith
  have quotientLe :
      Real.log delta⁻¹ / Real.log 2 ≤
        2 * Real.log delta⁻¹ := by
    rw [div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    nlinarith
  have realBound :
      (pureWZ2Prop62DirectionLevelCount delta : ℝ) ≤
        2 * (1 + Real.log delta⁻¹) := by
    change
      ((Nat.floor (Real.log (1 / delta) / Real.log 2) + 1 : ℕ) : ℝ) ≤
        2 * (1 + Real.log delta⁻¹)
    rw [show 1 / delta = delta⁻¹ by simp]
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have converted := ENNReal.ofReal_mono realBound
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at converted
  norm_num at converted ⊢
  simpa [logarithmicLoss] using converted

private theorem normalizedFixedGrid_refinementFraction_one_le_half
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (deltaSmall : delta ≤ Real.exp (-2)) :
    wz1PaperRefinementFraction delta 1 ≤ (1 / 2 : ENNReal) := by
  have expNegPos : 0 < Real.exp (-2) := Real.exp_pos _
  have inverse : Real.exp 2 ≤ delta⁻¹ := by
    have bound := (inv_le_inv₀ expNegPos deltaPos).mpr deltaSmall
    simpa [Real.exp_neg] using bound
  have logBound : 2 ≤ Real.log delta⁻¹ := by
    rw [← Real.log_exp 2]
    exact Real.log_le_log (Real.exp_pos 2) inverse
  unfold wz1PaperRefinementFraction
  simp only [pow_one, one_div]
  rw [ENNReal.inv_le_inv]
  have two : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by
    norm_num
  rw [two]
  simpa [one_div] using ENNReal.ofReal_mono logBound

/--
The normalized fixed-grid output.  Its one-log refinement and cleaned
extremal use the original normalized indexed family.
-/
structure Prop62V4NormalizedFixedGridData
    {sigma inputLoss normalizationLoss workingEta delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss)
        source normalizationExponent)
    (rho : WZ2PaperRequestedScale delta) where
  preparation :
    FixedGridPreparationData
      (rho := rho.1)
      normalized.croppedRefined
      normalized.final_extremal.delta_pos
  cleaned_extremal :
    WZ2PaperCroppedIsExtremal
      sigma workingEta
      normalized.croppedFamily preparation.cleanup.refined
  line_class :
    WZ1PaperIsLineClass normalized.croppedFamily
  cleaned_cubical :
    WZ1PaperIsCubicalShading preparation.cleanup.refined
  ordinary_bounded_base :
    HasBoundedBase normalized.croppedFamily 4

namespace Prop62V4NormalizedFixedGridData

variable
    {sigma inputLoss normalizationLoss workingEta delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss)
        source normalizationExponent}
    {rho : WZ2PaperRequestedScale delta}
    (data : Prop62V4NormalizedFixedGridData normalized rho)

/-- The fixed-grid cleanup as an actual one-log paper refinement. -/
noncomputable def oneLogRefinement :
    WZ1PaperRefinement normalized.croppedRefined 1 :=
  (Prop62V4NormalizedFixedGridData.preparation
    (workingEta := workingEta) data).fixedGridRefinement

@[simp] theorem oneLogRefinement_selected_family :
    (oneLogRefinement (workingEta := workingEta) data).selected.family =
      normalized.croppedFamily :=
  rfl

@[simp] theorem oneLogRefinement_refined :
    (oneLogRefinement (workingEta := workingEta) data).refined =
      (Prop62V4NormalizedFixedGridData.preparation
        (workingEta := workingEta) data).cleanup.refined :=
  rfl

end Prop62V4NormalizedFixedGridData

/--
A threshold fixed before the normalized source.  The first loss gap pays the
half-mass deletion in the cleaned density, while the second pays the two
boundary scale factors against the normalized top-level CWA.
-/
structure Prop62V4NormalizedFixedGridThresholdReceipt
    (normalizationLoss workingEta callerLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one_hundred : delta₀ ≤ 1 / 100
  prepare :
    ∀ {delta sigma inputLoss : ℝ},
      0 < delta →
      delta ≤ delta₀ →
      ∀ {source :
          PureWZ2ExtremalConfiguration sigma inputLoss delta},
        ∀ {normalizationExponent : ℕ},
          ∀ (normalized :
              PureWZ2CroppedCriticalNormalizationData
                (outputLoss := normalizationLoss)
                source normalizationExponent),
            ∀ rho : WZ2PaperRequestedScale delta,
              Real.rpow delta (1 - callerLoss) ≤ rho.1 →
              rho.1 ≤ Real.rpow delta callerLoss →
                Nonempty
                  (Prop62V4NormalizedFixedGridData
                    (workingEta := workingEta) normalized rho)

/--
Construct fixed-grid cleanup and cleaned pure extremality directly from an
arbitrary completed normalization.
-/
theorem prop62V4NormalizedFixedGridThreshold
    {normalizationLoss workingEta callerLoss : ℝ}
    (normalizationToWorking : normalizationLoss < workingEta)
    (boundaryGap : 2 * normalizationLoss < callerLoss)
    (hFixedGrid : FixedGridBoundaryRemovalStatement) :
    Nonempty
      (Prop62V4NormalizedFixedGridThresholdReceipt
        normalizationLoss workingEta callerLoss) := by
  rcases hFixedGrid with
    ⟨gridConstant, outerConstant, gridConstantPos,
      gridConstantTop, outerConstantPos, outerConstantTop,
      fixedGrid⟩
  let absorptionConstant : ENNReal :=
    4 * (gridConstant + outerConstant)
  have absorptionConstantTop : absorptionConstant ≠ ⊤ := by
    dsimp only [absorptionConstant]
    exact ENNReal.mul_ne_top (by norm_num) <|
      ENNReal.add_ne_top.mpr ⟨gridConstantTop, outerConstantTop⟩
  have boundaryGapPos :
      0 < callerLoss - 2 * normalizationLoss := by
    linarith
  rcases exists_delta_log_absorbed_ennreal
      absorptionConstant absorptionConstantTop boundaryGapPos
      (show 0 < (1 : ℕ) by norm_num) with
    ⟨boundaryDelta, boundaryDeltaPos, boundaryDeltaOne,
      absorbBoundary⟩
  rcases Subunit.exists_delta₀_mul_pow_le_one
      2 (by norm_num)
      (workingEta - normalizationLoss)
      (by linarith) with
    ⟨densityDelta, densityDeltaPos, densityDeltaOne,
      absorbDensity⟩
  let delta₀ : ℝ :=
    min (1 / 100 : ℝ)
      (min (Real.exp (-2))
        (min boundaryDelta densityDelta))
  have delta₀Pos : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  refine
    ⟨{
      delta₀ := delta₀
      delta₀_pos := delta₀Pos
      delta₀_le_one_hundred := min_le_left _ _
      prepare := ?_
    }⟩
  intro delta sigma inputLoss deltaPos deltaLe source
    normalizationExponent normalized rho rhoLower rhoUpper
  have deltaLeHundred : delta ≤ 1 / 100 :=
    deltaLe.trans (min_le_left _ _)
  have deltaLeOne : delta ≤ 1 :=
    deltaLeHundred.trans (by norm_num)
  have deltaLeExp : delta ≤ Real.exp (-2) :=
    deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
  have deltaLeBoundary : delta ≤ boundaryDelta :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have deltaLeDensity : delta ≤ densityDelta :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_right _ _)
  have rhoPos : 0 < rho.1 :=
    deltaPos.trans_le rho.2.1
  have ratioUpper :
      delta / rho.1 ≤ Real.rpow delta callerLoss := by
    rw [div_le_iff₀ rhoPos]
    calc
      delta = Real.rpow delta 1 := by simp
      _ =
          Real.rpow delta (1 - callerLoss) *
            Real.rpow delta callerLoss := by
        calc
          Real.rpow delta 1 =
              Real.rpow delta ((1 - callerLoss) + callerLoss) := by
            congr 1
            ring
          _ =
              Real.rpow delta (1 - callerLoss) *
                Real.rpow delta callerLoss :=
            Real.rpow_add deltaPos (1 - callerLoss) callerLoss
      _ ≤ rho.1 * Real.rpow delta callerLoss := by
        gcongr
        exact Real.rpow_nonneg deltaPos.le callerLoss
      _ = Real.rpow delta callerLoss * rho.1 := mul_comm _ _
  let sourceConstant : ENNReal :=
    Kakeya.realRpowENN delta (-normalizationLoss)
  have sourceConstantFinite :
      finiteErrorConstant sourceConstant := by
    exact
      ⟨normalized.final_extremal.cwa_nearby_scales.2.1.1,
        normalized.final_extremal.cwa_nearby_scales.2.1.2⟩
  have levelBound :
      logarithmicLoss delta ≤
        2 * ENNReal.ofReal (1 + Real.log delta⁻¹) :=
    normalizedFixedGrid_directionLevelCount_le_logEnvelope
      deltaPos deltaLeOne
  have gridScale :
      ENNReal.ofReal (delta / rho.1) ≤
        Kakeya.realRpowENN delta callerLoss :=
    ENNReal.ofReal_mono ratioUpper
  have outerScale :
      ENNReal.ofReal rho.1 ≤
        Kakeya.realRpowENN delta callerLoss :=
    ENNReal.ofReal_mono rhoUpper
  have absorbedBoundary :
      absorptionConstant *
          ENNReal.ofReal (1 + Real.log delta⁻¹) ≤
        Kakeya.realRpowENN delta
          (-(callerLoss - 2 * normalizationLoss)) := by
    simpa only [pow_one] using
      absorbBoundary delta deltaPos deltaLeBoundary
  have coefficientBound :
      gridConstant * sourceConstant *
            ENNReal.ofReal (delta / rho.1) *
            logarithmicLoss delta +
          outerConstant * sourceConstant *
            ENNReal.ofReal rho.1 *
            logarithmicLoss delta ≤
        (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta normalizationLoss := by
    let envelope : ENNReal :=
      ENNReal.ofReal (1 + Real.log delta⁻¹)
    let callerPower : ENNReal :=
      Kakeya.realRpowENN delta callerLoss
    let sourceInverse : ENNReal :=
      Kakeya.realRpowENN delta (-normalizationLoss)
    let gapInverse : ENNReal :=
      Kakeya.realRpowENN delta
        (-(callerLoss - 2 * normalizationLoss))
    have sourceCallerIdentity :
        sourceInverse * callerPower =
          Kakeya.realRpowENN delta
            (callerLoss - normalizationLoss) := by
      dsimp only [sourceInverse, callerPower]
      rw [← realRpowENN_add deltaPos]
      congr 1
      ring
    have gapIdentity :
        gapInverse *
            Kakeya.realRpowENN delta
              (callerLoss - normalizationLoss) =
          Kakeya.realRpowENN delta normalizationLoss := by
      dsimp only [gapInverse]
      rw [← realRpowENN_add deltaPos]
      congr 1
      ring
    calc
      gridConstant * sourceConstant *
              ENNReal.ofReal (delta / rho.1) *
              logarithmicLoss delta +
            outerConstant * sourceConstant *
              ENNReal.ofReal rho.1 *
              logarithmicLoss delta ≤
          gridConstant * sourceConstant * callerPower *
              logarithmicLoss delta +
            outerConstant * sourceConstant * callerPower *
              logarithmicLoss delta := by
        gcongr
      _ =
          ((gridConstant + outerConstant) *
              logarithmicLoss delta) *
            (sourceInverse * callerPower) := by
        dsimp only [sourceConstant]
        ring
      _ ≤
          ((gridConstant + outerConstant) *
              (2 * envelope)) *
            (sourceInverse * callerPower) := by
        gcongr
      _ =
          ((1 / 2 : ENNReal) *
              (absorptionConstant * envelope)) *
            (sourceInverse * callerPower) := by
        have halfFour : (1 / 2 : ENNReal) * 4 = 2 := by
          rw [show (4 : ENNReal) = 2 * 2 by norm_num, one_div,
            ← mul_assoc,
            ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
            one_mul]
        dsimp only [absorptionConstant]
        calc
          ((gridConstant + outerConstant) * (2 * envelope)) *
                (sourceInverse * callerPower) =
              (2 * ((gridConstant + outerConstant) * envelope)) *
                (sourceInverse * callerPower) := by ring
          _ =
              (((1 / 2 : ENNReal) * 4) *
                  ((gridConstant + outerConstant) * envelope)) *
                (sourceInverse * callerPower) := by rw [halfFour]
          _ =
              ((1 / 2 : ENNReal) *
                  (4 * (gridConstant + outerConstant) * envelope)) *
                (sourceInverse * callerPower) := by ring
      _ ≤
          ((1 / 2 : ENNReal) * gapInverse) *
            (sourceInverse * callerPower) := by
        gcongr
      _ =
          (1 / 2 : ENNReal) *
            Kakeya.realRpowENN delta normalizationLoss := by
        rw [sourceCallerIdentity]
        calc
          ((1 / 2 : ENNReal) * gapInverse) *
                Kakeya.realRpowENN delta
                  (callerLoss - normalizationLoss) =
              (1 / 2 : ENNReal) *
                (gapInverse *
                  Kakeya.realRpowENN delta
                    (callerLoss - normalizationLoss)) := by ring
          _ =
              (1 / 2 : ENNReal) *
                Kakeya.realRpowENN delta normalizationLoss := by
            rw [gapIdentity]
  have boundarySmall :
      gridConstant * sourceConstant *
              ENNReal.ofReal (delta / rho.1) *
              logarithmicLoss delta *
                (wz1PaperBodyFamily normalized.croppedFamily).mass +
            outerConstant * sourceConstant *
              ENNReal.ofReal rho.1 *
              logarithmicLoss delta *
                (wz1PaperBodyFamily normalized.croppedFamily).mass ≤
        normalized.croppedRefined.mass / 2 := by
    calc
      gridConstant * sourceConstant *
              ENNReal.ofReal (delta / rho.1) *
              logarithmicLoss delta *
                (wz1PaperBodyFamily normalized.croppedFamily).mass +
            outerConstant * sourceConstant *
              ENNReal.ofReal rho.1 *
              logarithmicLoss delta *
                (wz1PaperBodyFamily normalized.croppedFamily).mass =
          (gridConstant * sourceConstant *
                ENNReal.ofReal (delta / rho.1) *
                logarithmicLoss delta +
              outerConstant * sourceConstant *
                ENNReal.ofReal rho.1 *
                logarithmicLoss delta) *
            (wz1PaperBodyFamily normalized.croppedFamily).mass := by
        ring
      _ ≤
          ((1 / 2 : ENNReal) *
              Kakeya.realRpowENN delta normalizationLoss) *
            (wz1PaperBodyFamily normalized.croppedFamily).mass := by
        gcongr
      _ =
          (1 / 2 : ENNReal) *
            (Kakeya.realRpowENN delta normalizationLoss *
              (wz1PaperBodyFamily normalized.croppedFamily).mass) := by
        ring
      _ ≤ (1 / 2 : ENNReal) * normalized.croppedRefined.mass := by
        gcongr
        exact normalized.final_extremal.dense
      _ = normalized.croppedRefined.mass / 2 := by
        simp only [ENNReal.div_eq_inv_mul, mul_one]
  have boundary :=
    fixedGrid delta rho.1 deltaPos deltaLeHundred rhoPos rho.2.2
      rho.2.1 normalized.croppedFamily normalized.line_class
      normalized.croppedRefined normalized.cropped_cubical
      sourceConstant sourceConstantFinite
      normalized.cropped_top_level_cwa
  dsimp only at boundary
  rcases boundary.2.2 boundarySmall with ⟨cleanup⟩
  have refinementRetained :
      wz1PaperRefinementFraction delta 1 *
          normalized.croppedRefined.mass ≤
        cleanup.refined.mass := by
    calc
      wz1PaperRefinementFraction delta 1 *
            normalized.croppedRefined.mass ≤
          (1 / 2 : ENNReal) *
            normalized.croppedRefined.mass := by
        gcongr
        exact
          normalizedFixedGrid_refinementFraction_one_le_half
            deltaPos deltaLeExp
      _ = normalized.croppedRefined.mass / 2 := by
        simp only [ENNReal.div_eq_inv_mul, mul_one]
      _ ≤ cleanup.refined.mass :=
        cleanup.mass_retention
  let preparation :
      FixedGridPreparationData
        (rho := rho.1)
        normalized.croppedRefined
        normalized.final_extremal.delta_pos :=
    {
      cleanup := cleanup
      refinement_retained := refinementRetained
    }
  have densityPower :
      Kakeya.realRpowENN delta workingEta ≤
        (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta normalizationLoss := by
    apply pure_wz2_pruning_power_bound deltaPos
    exact
      absorbDensity delta deltaPos deltaLeDensity
  have cleanedDense :
      cleanup.refined.IsLambdaDense
        (Kakeya.realRpowENN delta workingEta) := by
    calc
      Kakeya.realRpowENN delta workingEta *
            (wz1PaperBodyFamily normalized.croppedFamily).mass ≤
          ((1 / 2 : ENNReal) *
              Kakeya.realRpowENN delta normalizationLoss) *
            (wz1PaperBodyFamily normalized.croppedFamily).mass := by
        gcongr
      _ =
          (1 / 2 : ENNReal) *
            (Kakeya.realRpowENN delta normalizationLoss *
              (wz1PaperBodyFamily normalized.croppedFamily).mass) := by
        ring
      _ ≤ (1 / 2 : ENNReal) * normalized.croppedRefined.mass := by
        gcongr
        exact normalized.final_extremal.dense
      _ = normalized.croppedRefined.mass / 2 := by
        simp only [ENNReal.div_eq_inv_mul, mul_one]
      _ ≤ cleanup.refined.mass :=
        cleanup.mass_retention
  have cleanedUnionSubset :
      cleanup.refined.union ⊆
        normalized.croppedRefined.union := by
    rintro point ⟨index, pointMem⟩
    exact ⟨index, cleanup.subshading index pointMem⟩
  let weakened :=
    normalized.final_extremal.mono_loss normalizationToWorking.le
  let cleanedExtremal :
      WZ2PaperCroppedIsExtremal
        sigma workingEta
        normalized.croppedFamily cleanup.refined :=
    {
      delta_pos := normalized.final_extremal.delta_pos
      delta_le_one := normalized.final_extremal.delta_le_one
      nonempty := normalized.final_extremal.nonempty
      cwa_nearby_scales := weakened.cwa_nearby_scales
      cubical := cleanup.cubical
      dense := cleanedDense
      volume_upper :=
        (measure_mono cleanedUnionSubset).trans weakened.volume_upper
    }
  exact
    ⟨{
      preparation := preparation
      cleaned_extremal := cleanedExtremal
      line_class := normalized.line_class
      cleaned_cubical := cleanup.cubical
      ordinary_bounded_base := normalized.ordinary_bounded_base
    }⟩

end Kakeya.Assouad.Prop62PaperAudit.V4

end
