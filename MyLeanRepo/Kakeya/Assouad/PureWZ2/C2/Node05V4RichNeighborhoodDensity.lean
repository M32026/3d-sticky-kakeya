import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64PreCommonBinProduction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalAnalyticSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RobustTransversality

/-!
# Exact first-call density for the Node-5 pre-common-bin neighborhood

The paper's line-neighborhood argument needs the actual point multiplicity
inside the first rich output, not merely positivity of the terminal dyadic
levels.  The first rich V4 witness already contains the required information:
its exact terminal multiplicity theorem controls
`fineDegreeFloor * muFine`, while the current source's Convex--Wolff bound
supplies the absolute source-cardinality floor.  This file combines those two
same-witness facts without selecting a new family, cell, or envelope.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2Node05V4RichSecondCallData

private theorem neighborhood_realRpowENN_div_mul
    {delta rho exponent : ℝ} (hdelta : 0 < delta) (hrho : 0 < rho) :
    Kakeya.realRpowENN (delta / rho) exponent *
        Kakeya.realRpowENN rho exponent =
      Kakeya.realRpowENN delta exponent := by
  have hmul := realRpowENN_mul (div_pos hdelta hrho) hrho exponent
  rw [show delta / rho * rho = delta by field_simp [hrho.ne']] at hmul
  exact hmul.symm

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss inputLoss delta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    (twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested)

/-- Recover an absolute lower bound for the exact terminal point degree from
two family-independent scalar inequalities.  The first scalar is precisely
the one consumed by `fineMultiplicity_density_of_scalar`; the second pays the
single source-cardinality constant.  All geometric objects on the right come
from the same first rich call. -/
theorem first_terminal_pointDensity_lower_of_scalars
    (densityPower target : ENNReal)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hdensityScalar :
      densityPower *
          ((twoScale.first.fourDegreeReceipts.regularity : ENNReal) *
            Kakeya.realRpowENN delta
              (sigma -
                (schedule.firstCallSchedule capability).kernel.normalizationLoss)) ≤
        wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta
            ((schedule.firstCallSchedule capability).kernel.normalizationLoss + 2))
    (hcardinalityScalar :
      target * ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
          Kakeya.realRpowENN delta (2 - inputLoss) ≤ densityPower) :
    target ≤
      ((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
          twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) := by
  have hcardinality :=
    PureWZ2.cwa_cardinality_weight_floor current.grain.extremal hdeltaSmall
  have hdensity :=
    twoScale.first.rich.fineMultiplicity_density_of_source_cardinality
      densityPower (hdeltaSmall.trans (by norm_num)) hdensityScalar
  calc
    target = target * 1 := by simp
    _ ≤ target *
        (((12 : ENNReal) * ENNReal.ofReal Real.pi) *
          (Kakeya.realRpowENN delta (2 - inputLoss) *
            current.grain.family.enncard)) := by gcongr
    _ = (target * ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
          Kakeya.realRpowENN delta (2 - inputLoss)) *
            current.grain.family.enncard := by ring
    _ ≤ densityPower * current.grain.family.enncard := by gcongr
    _ ≤ _ := hdensity

/-- The fixed loss assigned to the absolute point-density lower bound in the
first rich output. -/
def pureWZ2Node05V4RichNeighborhoodPointDensityLoss
    (sourceLossCeiling firstOutputLoss : ℝ) : ℝ :=
  sourceLossCeiling + 4 * firstOutputLoss

/-- A family-independent cutoff which recovers the actual point density of
the first rich terminal witness.  One quarter of `firstOutputLoss` absorbs
the terminal regularity, and another quarter pays the 61-log refinement. -/
structure PureWZ2Node05V4RichNeighborhoodDensityThreshold
    (sigma sourceLossCeiling firstOutputLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one_twenty_four : delta₀ ≤ 1 / 24
  density_scalar :
    ∀ {normalizationLoss delta : ℝ} {regularity : ℕ},
      normalizationLoss < firstOutputLoss →
      0 < delta → delta ≤ delta₀ →
      (regularity : ENNReal) ≤
        Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 →
      Kakeya.realRpowENN delta
            (2 - sigma + 3 * firstOutputLoss) *
          ((regularity : ENNReal) *
            Kakeya.realRpowENN delta (sigma - normalizationLoss)) ≤
        wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta (normalizationLoss + 2)
  cardinality_scalar :
    ∀ {inputLoss delta : ℝ},
      inputLoss ≤ sourceLossCeiling →
      0 < delta → delta ≤ delta₀ →
      Kakeya.realRpowENN delta
            (-sigma +
              pureWZ2Node05V4RichNeighborhoodPointDensityLoss
                sourceLossCeiling firstOutputLoss) *
          ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
          Kakeya.realRpowENN delta (2 - inputLoss) ≤
        Kakeya.realRpowENN delta
          (2 - sigma + 3 * firstOutputLoss)

/-- Select the point-density cutoff before the runtime source and scales. -/
theorem pureWZ2Node05V4Rich_neighborhoodDensity_threshold
    {sigma sourceLossCeiling firstOutputLoss : ℝ}
    (hfirstOutput : 0 < firstOutputLoss) :
    Nonempty (PureWZ2Node05V4RichNeighborhoodDensityThreshold
      sigma sourceLossCeiling firstOutputLoss) := by
  let quarterLoss := firstOutputLoss / 4
  have hquarter : 0 < quarterLoss := by
    dsimp only [quarterLoss]
    positivity
  rcases pureWZ2_refinementFraction_power_schedule 61 hquarter with
    ⟨refinementDelta₀, hrefinementDelta₀, hrefinementDelta₀One,
      hrefinement⟩
  let logCoefficient : ENNReal := 2 ^ (10 : ℕ)
  have hlogCoefficientTop : logCoefficient ≠ ⊤ := by
    dsimp only [logCoefficient]
    exact ENNReal.pow_ne_top (by norm_num)
  rcases exists_delta_log_absorbed_ennreal
      logCoefficient hlogCoefficientTop hquarter
      (show 0 < (10 : ℕ) by norm_num) with
    ⟨regularityDelta₀, hregularityDelta₀, hregularityDelta₀One,
      hregularityAbsorb⟩
  let cardinalityCoefficient : ENNReal :=
    (12 : ENNReal) * ENNReal.ofReal Real.pi
  have hcardinalityCoefficientTop : cardinalityCoefficient ≠ ⊤ := by
    dsimp only [cardinalityCoefficient]
    exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  rcases exists_scale_absorb_constant cardinalityCoefficient
      hcardinalityCoefficientTop (c := 0) (c' := firstOutputLoss)
      (by norm_num) hfirstOutput with
    ⟨cardinalityDelta₀, hcardinalityDelta₀, hcardinalityDelta₀One,
      hcardinalityAbsorb⟩
  let delta₀ := min (1 / 24 : ℝ)
    (min refinementDelta₀ (min regularityDelta₀ cardinalityDelta₀))
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min (by norm_num) <|
      lt_min hrefinementDelta₀ <|
        lt_min hregularityDelta₀ hcardinalityDelta₀
    delta₀_le_one_twenty_four := min_le_left _ _
    density_scalar := ?_
    cardinality_scalar := ?_
  }⟩
  · intro normalizationLoss delta regularity hnormalization hdelta hdeltaSmall
      hregularity
    have hdeltaOne : delta ≤ 1 :=
      hdeltaSmall.trans <| (min_le_left _ _).trans (by norm_num)
    have hdeltaRefinement : delta ≤ refinementDelta₀ :=
      hdeltaSmall.trans <| (min_le_right _ _).trans (min_le_left _ _)
    have hdeltaRegularity : delta ≤ regularityDelta₀ :=
      hdeltaSmall.trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
    have hlogarithmic :
        Prop62PaperAudit.V4.logarithmicLoss delta ≤
          2 * ENNReal.ofReal (1 + Real.log delta⁻¹) := by
      simpa only [Prop62PaperAudit.V4.logarithmicLoss,
        show ENNReal.ofReal (2 * (1 + Real.log delta⁻¹)) =
          2 * ENNReal.ofReal (1 + Real.log delta⁻¹) by
            rw [ENNReal.ofReal_mul (by norm_num)]
            norm_num] using
        PureWZ2.proposition63_logarithmicLoss_le_two_logEnvelope
          hdelta hdeltaOne
    have hregularityPower :
        (regularity : ENNReal) ≤
          Kakeya.realRpowENN delta (-quarterLoss) := by
      calc
        (regularity : ENNReal) ≤
            Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 := hregularity
        _ ≤ (2 * ENNReal.ofReal (1 + Real.log delta⁻¹)) ^ 10 := by
          gcongr
        _ = logCoefficient *
            ENNReal.ofReal (1 + Real.log delta⁻¹) ^ 10 := by
          dsimp only [logCoefficient]
          rw [mul_pow]
        _ ≤ Kakeya.realRpowENN delta (-quarterLoss) :=
          hregularityAbsorb delta hdelta hdeltaRegularity
    have hrefinementPower :
        Kakeya.realRpowENN delta quarterLoss ≤
          wz2PaperPureRefinementFraction delta 61 :=
      hrefinement delta hdelta hdeltaRefinement
    have hexponent :
        quarterLoss + (normalizationLoss + 2) ≤
          (2 - sigma + 3 * firstOutputLoss) +
            (-quarterLoss) + (sigma - normalizationLoss) := by
      dsimp only [quarterLoss]
      linarith
    have hleftPower :
        Kakeya.realRpowENN delta
              (2 - sigma + 3 * firstOutputLoss) *
            (Kakeya.realRpowENN delta (-quarterLoss) *
              Kakeya.realRpowENN delta (sigma - normalizationLoss)) =
          Kakeya.realRpowENN delta
            ((2 - sigma + 3 * firstOutputLoss) +
              (-quarterLoss) + (sigma - normalizationLoss)) := by
      rw [← realRpowENN_add hdelta, ← realRpowENN_add hdelta]
      congr 1 <;> ring
    calc
      Kakeya.realRpowENN delta
              (2 - sigma + 3 * firstOutputLoss) *
            ((regularity : ENNReal) *
              Kakeya.realRpowENN delta (sigma - normalizationLoss)) ≤
          Kakeya.realRpowENN delta
              (2 - sigma + 3 * firstOutputLoss) *
            (Kakeya.realRpowENN delta (-quarterLoss) *
              Kakeya.realRpowENN delta (sigma - normalizationLoss)) := by
        gcongr
      _ = Kakeya.realRpowENN delta
          ((2 - sigma + 3 * firstOutputLoss) +
            (-quarterLoss) + (sigma - normalizationLoss)) := hleftPower
      _ ≤ Kakeya.realRpowENN delta
          (quarterLoss + (normalizationLoss + 2)) :=
        realRpowENN_antitone hdelta hdeltaOne hexponent
      _ = Kakeya.realRpowENN delta quarterLoss *
          Kakeya.realRpowENN delta (normalizationLoss + 2) := by
        rw [realRpowENN_add hdelta]
      _ ≤ wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta (normalizationLoss + 2) := by
        gcongr
  · intro inputLoss delta hinput hdelta hdeltaSmall
    have hdeltaOne : delta ≤ 1 :=
      hdeltaSmall.trans <| (min_le_left _ _).trans (by norm_num)
    have hdeltaCardinality : delta ≤ cardinalityDelta₀ :=
      hdeltaSmall.trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _)
    have hcoefficient :
        cardinalityCoefficient ≤
          Kakeya.realRpowENN delta (-firstOutputLoss) := by
      have hraw := hcardinalityAbsorb delta hdelta hdeltaCardinality
      simpa [Kakeya.realRpowENN] using hraw
    have hnonnegative : 0 ≤ sourceLossCeiling - inputLoss := by linarith
    have hsourcePower :
        Kakeya.realRpowENN delta (sourceLossCeiling - inputLoss) ≤ 1 :=
      realRpowENN_le_one hdelta hdeltaOne hnonnegative
    have hcombinedPower :
        Kakeya.realRpowENN delta
              (-sigma + (sourceLossCeiling + 4 * firstOutputLoss)) *
            Kakeya.realRpowENN delta (2 - inputLoss) =
          Kakeya.realRpowENN delta
            (2 - sigma + sourceLossCeiling +
              4 * firstOutputLoss - inputLoss) := by
      rw [← realRpowENN_add hdelta]
      congr 1 <;> ring
    calc
      Kakeya.realRpowENN delta
              (-sigma +
                pureWZ2Node05V4RichNeighborhoodPointDensityLoss
                  sourceLossCeiling firstOutputLoss) *
            ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
            Kakeya.realRpowENN delta (2 - inputLoss) =
          cardinalityCoefficient *
            Kakeya.realRpowENN delta
              (2 - sigma + sourceLossCeiling +
                4 * firstOutputLoss - inputLoss) := by
        dsimp only [cardinalityCoefficient,
          pureWZ2Node05V4RichNeighborhoodPointDensityLoss]
        rw [show Kakeya.realRpowENN delta
                (-sigma + (sourceLossCeiling + 4 * firstOutputLoss)) *
              (12 * ENNReal.ofReal Real.pi) *
              Kakeya.realRpowENN delta (2 - inputLoss) =
            (12 * ENNReal.ofReal Real.pi) *
              (Kakeya.realRpowENN delta
                  (-sigma + (sourceLossCeiling + 4 * firstOutputLoss)) *
                Kakeya.realRpowENN delta (2 - inputLoss)) by ring,
          hcombinedPower]
      _ ≤ Kakeya.realRpowENN delta (-firstOutputLoss) *
          Kakeya.realRpowENN delta
            (2 - sigma + sourceLossCeiling +
              4 * firstOutputLoss - inputLoss) := by gcongr
      _ = Kakeya.realRpowENN delta (2 - sigma + 3 * firstOutputLoss) *
          Kakeya.realRpowENN delta (sourceLossCeiling - inputLoss) := by
        rw [← realRpowENN_add hdelta, ← realRpowENN_add hdelta]
        congr 1 <;> ring
      _ ≤ Kakeya.realRpowENN delta (2 - sigma + 3 * firstOutputLoss) := by
        simpa using mul_le_of_le_one_right (by positivity) hsourcePower

/-- The P0 cutoff instantiated on the actual first rich witness. -/
theorem first_terminal_pointDensity_lower
    {sourceLossCeiling : ℝ}
    (threshold : PureWZ2Node05V4RichNeighborhoodDensityThreshold
      sigma sourceLossCeiling schedule.firstOutputLoss)
    (hinput : inputLoss ≤ sourceLossCeiling)
    (hdeltaSmall : delta ≤ threshold.delta₀) :
    Kakeya.realRpowENN delta
        (-sigma + pureWZ2Node05V4RichNeighborhoodPointDensityLoss
          sourceLossCeiling schedule.firstOutputLoss) ≤
      ((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
          twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) := by
  apply twoScale.first_terminal_pointDensity_lower_of_scalars
    (Kakeya.realRpowENN delta
      (2 - sigma + 3 * schedule.firstOutputLoss))
    (Kakeya.realRpowENN delta
      (-sigma + pureWZ2Node05V4RichNeighborhoodPointDensityLoss
        sourceLossCeiling schedule.firstOutputLoss))
    (hdeltaSmall.trans threshold.delta₀_le_one_twenty_four)
  · exact threshold.density_scalar
      (schedule.firstCallSchedule capability).kernel.normalizationLoss_lt_output
      current.grain.extremal.delta_pos hdeltaSmall
      twoScale.first.rich.terminal_regularity_bound
  · exact threshold.cardinality_scalar hinput
      current.grain.extremal.delta_pos hdeltaSmall

/-- The exact first-terminal point density and the two balanced-cell floors
give the physical mass available to each selected side-`sqrt rho` parent.
The sole remaining scalar premise is the conversion from the fine scale to
the internal ordinary scale. -/
theorem preCommonBin_balanceMass_lower_of_pointDensity
    {pointDensityLoss : ℝ}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rhoRequested.1) twoScale)
    (hpointDensity :
      Kakeya.realRpowENN delta (-sigma + pointDensityLoss) ≤
        ((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
          twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal))
    (hscaleConversion :
      Kakeya.realRpowENN rhoRequested.1
          (sigma + 2 * twoScale.first.rich.terminalLoss -
            twoScale.second.terminalLoss) ≤
        Kakeya.realRpowENN delta
          (pointDensityLoss + 2 * twoScale.first.rich.terminalLoss)) :
    Kakeya.realRpowENN rhoRequested.1 (9 / 2 + sigma / 2) ≤
      (((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
          twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) *
        twoScale.second.terminal.balanced.cellMass) *
          pullback.firstPostBalanced.cellMass := by
  let firstLoss := twoScale.first.rich.terminalLoss
  let secondLoss := twoScale.second.terminalLoss
  let remainder := 9 / 2 - sigma / 2 - 2 * firstLoss + secondLoss
  have hdelta : 0 < delta := current.grain.extremal.delta_pos
  have hrho : 0 < rhoRequested.1 :=
    twoScale.first.publicSticky.coarse_extremal.delta_pos
  have htargetSplit :
      Kakeya.realRpowENN rhoRequested.1 (9 / 2 + sigma / 2) =
        Kakeya.realRpowENN rhoRequested.1
            (sigma + 2 * firstLoss - secondLoss) *
          Kakeya.realRpowENN rhoRequested.1 remainder := by
    rw [← realRpowENN_add hrho]
    dsimp only [remainder, firstLoss, secondLoss]
    congr 1 <;> ring
  have hcellFloorProduct :
      (Kakeya.realRpowENN rhoRequested.1 3 *
          Kakeya.realRpowENN (delta / rhoRequested.1)
            (sigma + 2 * firstLoss)) *
        Kakeya.realRpowENN rhoRequested.1
          (3 / 2 + sigma / 2 + secondLoss) ≤
      pullback.firstPostBalanced.cellMass *
        twoScale.second.terminal.balanced.cellMass := by
    gcongr
    · rw [pullback.firstPost_cellMass_eq]
      exact twoScale.first_cellMass_power_lower
    · exact twoScale.second_cellMass_rho_power_lower
  have hfloorIdentity :
      Kakeya.realRpowENN delta
            (pointDensityLoss + 2 * firstLoss) *
          Kakeya.realRpowENN rhoRequested.1 remainder =
        Kakeya.realRpowENN delta (-sigma + pointDensityLoss) *
          ((Kakeya.realRpowENN rhoRequested.1 3 *
              Kakeya.realRpowENN (delta / rhoRequested.1)
                (sigma + 2 * firstLoss)) *
            Kakeya.realRpowENN rhoRequested.1
              (3 / 2 + sigma / 2 + secondLoss)) := by
    let exponent := sigma + 2 * firstLoss
    have hquotient := neighborhood_realRpowENN_div_mul
      (delta := delta) (rho := rhoRequested.1) (exponent := exponent)
      hdelta hrho
    have hdeltaSplit :
        Kakeya.realRpowENN delta (-sigma + pointDensityLoss) *
            Kakeya.realRpowENN delta exponent =
          Kakeya.realRpowENN delta
            (pointDensityLoss + 2 * firstLoss) := by
      rw [← realRpowENN_add hdelta]
      dsimp only [exponent]
      congr 1 <;> ring
    have hrhoSplit :
        Kakeya.realRpowENN rhoRequested.1 exponent *
            Kakeya.realRpowENN rhoRequested.1 remainder =
          Kakeya.realRpowENN rhoRequested.1
            (9 / 2 + sigma / 2 + secondLoss) := by
      rw [← realRpowENN_add hrho]
      dsimp only [exponent, remainder, firstLoss, secondLoss]
      congr 1 <;> ring
    have hcellPower :
        (Kakeya.realRpowENN rhoRequested.1 3 *
            Kakeya.realRpowENN (delta / rhoRequested.1) exponent) *
          Kakeya.realRpowENN rhoRequested.1
            (3 / 2 + sigma / 2 + secondLoss) =
        (Kakeya.realRpowENN (delta / rhoRequested.1) exponent *
            Kakeya.realRpowENN rhoRequested.1 exponent) *
          Kakeya.realRpowENN rhoRequested.1 remainder := by
      calc
        (Kakeya.realRpowENN rhoRequested.1 3 *
              Kakeya.realRpowENN (delta / rhoRequested.1) exponent) *
            Kakeya.realRpowENN rhoRequested.1
              (3 / 2 + sigma / 2 + secondLoss) =
          Kakeya.realRpowENN (delta / rhoRequested.1) exponent *
            (Kakeya.realRpowENN rhoRequested.1 3 *
              Kakeya.realRpowENN rhoRequested.1
                (3 / 2 + sigma / 2 + secondLoss)) := by ring
        _ = Kakeya.realRpowENN (delta / rhoRequested.1) exponent *
            Kakeya.realRpowENN rhoRequested.1
              (9 / 2 + sigma / 2 + secondLoss) := by
          rw [← realRpowENN_add hrho]
          congr 1 <;> ring
        _ = Kakeya.realRpowENN (delta / rhoRequested.1) exponent *
            (Kakeya.realRpowENN rhoRequested.1 exponent *
              Kakeya.realRpowENN rhoRequested.1 remainder) := by
          rw [hrhoSplit]
        _ = _ := by ring
    calc
      Kakeya.realRpowENN delta
            (pointDensityLoss + 2 * firstLoss) *
          Kakeya.realRpowENN rhoRequested.1 remainder =
        (Kakeya.realRpowENN delta (-sigma + pointDensityLoss) *
            Kakeya.realRpowENN delta exponent) *
          Kakeya.realRpowENN rhoRequested.1 remainder := by rw [hdeltaSplit]
      _ = Kakeya.realRpowENN delta (-sigma + pointDensityLoss) *
          ((Kakeya.realRpowENN (delta / rhoRequested.1) exponent *
              Kakeya.realRpowENN rhoRequested.1 exponent) *
            Kakeya.realRpowENN rhoRequested.1 remainder) := by
        rw [hquotient, mul_assoc]
      _ = _ := by
        dsimp only [exponent]
        rw [hcellPower]
  rw [htargetSplit]
  calc
    Kakeya.realRpowENN rhoRequested.1
          (sigma + 2 * firstLoss - secondLoss) *
        Kakeya.realRpowENN rhoRequested.1 remainder ≤
      Kakeya.realRpowENN delta (pointDensityLoss + 2 * firstLoss) *
        Kakeya.realRpowENN rhoRequested.1 remainder := by gcongr
    _ = Kakeya.realRpowENN delta (-sigma + pointDensityLoss) *
        ((Kakeya.realRpowENN rhoRequested.1 3 *
            Kakeya.realRpowENN (delta / rhoRequested.1)
              (sigma + 2 * firstLoss)) *
          Kakeya.realRpowENN rhoRequested.1
            (3 / 2 + sigma / 2 + secondLoss)) := hfloorIdentity
    _ ≤ ((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
            twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) *
          (pullback.firstPostBalanced.cellMass *
            twoScale.second.terminal.balanced.cellMass) := by
      gcongr
    _ = _ := by ring

/-- Once the exact multiplicity--cell-mass product reaches the paper power,
the mass branch in `RequiredCubeCount` is dominated by its cardinality
branch.  This is the explicit cell-density statement hidden in the informal
line-neighborhood pigeonhole. -/
theorem preCommonBin_requiredCubeCount_le_of_balanceMass
    {neighborhoodLoss : ℝ}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rhoRequested.1) twoScale)
    (hbalance :
      Kakeya.realRpowENN rhoRequested.1 (9 / 2 + sigma / 2) ≤
        (((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
            twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) *
          twoScale.second.terminal.balanced.cellMass) *
            pullback.firstPostBalanced.cellMass) :
    pureWZ2PreCommonBinRequiredCubeCount pullback neighborhoodLoss ≤
      Kakeya.realRpowENN rhoRequested.1 (-1 / 2 + neighborhoodLoss) := by
  let balanceMass : ENNReal :=
    (((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
          twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) *
      twoScale.second.terminal.balanced.cellMass) *
        pullback.firstPostBalanced.cellMass
  have hrho : 0 < rhoRequested.1 :=
    twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hbalancePos : 0 < balanceMass := by
    dsimp only [balanceMass]
    have hdegreeNat : 0 <
        twoScale.first.fourDegreeReceipts.fineDegreeFloor *
          twoScale.first.fourDegreeReceipts.muFine :=
      Nat.mul_pos twoScale.first.fourDegreeReceipts.fineDegreeFloor_pos
        twoScale.first.fourDegreeReceipts.muFine_pos
    have hdegree :
        (0 : ENNReal) <
          ((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
            twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) := by
      exact_mod_cast hdegreeNat
    exact ENNReal.mul_pos
      (ENNReal.mul_pos hdegree.ne'
        twoScale.second.terminal.balanced.cellMass_pos.ne').ne'
      pullback.firstPostBalanced.cellMass_pos.ne'
  have hbalanceTop : balanceMass ≠ ⊤ := by
    dsimp only [balanceMass]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        twoScale.second.terminal.balanced.cellMass_ne_top)
      pullback.firstPostBalanced.cellMass_ne_top
  have hcube :
      volume (wz1PaperGridCube rhoRequested.1 (0, 0, 0)) =
        Kakeya.realRpowENN rhoRequested.1 3 := by
    rw [wz1PaperGridCube_volume_exact hrho]
    simp [Kakeya.realRpowENN, Real.rpow_natCast]
  have hpowerIdentity :
      Kakeya.realRpowENN rhoRequested.1
            (1 + sigma / 2 + neighborhoodLoss) *
          Kakeya.realRpowENN rhoRequested.1 3 =
        Kakeya.realRpowENN rhoRequested.1
            (-1 / 2 + neighborhoodLoss) *
          Kakeya.realRpowENN rhoRequested.1 (9 / 2 + sigma / 2) := by
    rw [← realRpowENN_add hrho, ← realRpowENN_add hrho]
    congr 1 <;> ring
  have hratio :
      (Kakeya.realRpowENN rhoRequested.1
            (1 + sigma / 2 + neighborhoodLoss) *
          volume (wz1PaperGridCube rhoRequested.1 (0, 0, 0))) /
        balanceMass ≤
      Kakeya.realRpowENN rhoRequested.1 (-1 / 2 + neighborhoodLoss) := by
    apply (ENNReal.div_le_iff_le_mul
      (Or.inl hbalancePos.ne') (Or.inl hbalanceTop)).2
    rw [hcube]
    calc
      Kakeya.realRpowENN rhoRequested.1
            (1 + sigma / 2 + neighborhoodLoss) *
          Kakeya.realRpowENN rhoRequested.1 3 =
        Kakeya.realRpowENN rhoRequested.1
            (-1 / 2 + neighborhoodLoss) *
          Kakeya.realRpowENN rhoRequested.1 (9 / 2 + sigma / 2) :=
        hpowerIdentity
      _ ≤ Kakeya.realRpowENN rhoRequested.1
          (-1 / 2 + neighborhoodLoss) * balanceMass := by gcongr
  unfold pureWZ2PreCommonBinRequiredCubeCount
  exact max_le le_rfl (by simpa only [balanceMass] using hratio)

/-- The complete finite constant in the heavy-slab neighborhood budget. -/
def pureWZ2Node05V4RichHeavyNeighborhoodConstant : ENNReal :=
  2 * 10 * 132 * 10 * 4 * 13 * 512

private theorem neighborhood_one_div_power
    {delta sigma : ℝ} (hdelta : 0 < delta) :
    Kakeya.realRpowENN (1 / delta) (1 - sigma) =
      Kakeya.realRpowENN delta (sigma - 1) := by
  simp only [Kakeya.realRpowENN]
  apply congrArg ENNReal.ofReal
  rw [one_div]
  calc
    Real.rpow delta⁻¹ (1 - sigma) =
        (Real.rpow delta (1 - sigma))⁻¹ := Real.inv_rpow hdelta.le _
    _ = Real.rpow delta (-(1 - sigma)) :=
      (Real.rpow_neg hdelta.le _).symm
    _ = Real.rpow delta (sigma - 1) := by congr 1; ring

private theorem neighborhood_slab_width_power
    {delta rho : ℝ} (hdelta : 0 < delta) (hrho : 0 < rho) :
    ENNReal.ofReal (4 * Real.sqrt rho * delta) =
      (4 : ENNReal) * Kakeya.realRpowENN rho (1 / 2) *
        Kakeya.realRpowENN delta 1 := by
  calc
    ENNReal.ofReal (4 * Real.sqrt rho * delta) =
        ENNReal.ofReal (4 * Real.sqrt rho) * ENNReal.ofReal delta :=
      ENNReal.ofReal_mul (by positivity)
    _ = (ENNReal.ofReal 4 * ENNReal.ofReal (Real.sqrt rho)) *
        ENNReal.ofReal delta := by rw [ENNReal.ofReal_mul (by norm_num)]
    _ = _ := by simp [Kakeya.realRpowENN, Real.sqrt_eq_rpow]

/-- Exact scalar normal form of the first `RequiredCubeCount` branch.  In
particular, the horizontal `sqrt rho` thickness cancels the `rho⁻¹/²` count,
leaving the positive `rho^neighborhoodLoss` gain visible. -/
theorem heavyNeighborhoodCost_firstBranch_power_identity
    {sigma inputLoss delta rho neighborhoodLoss : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    (pureWZ2PreCommonBinHeavySlabNeighborhoodCost
          sigma inputLoss delta rho *
        Kakeya.realRpowENN rho (-1 / 2 + neighborhoodLoss)) *
        volume (wz1PaperGridCube rho (0, 0, 0)) =
      pureWZ2Node05V4RichHeavyNeighborhoodConstant *
        Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 *
        Kakeya.realRpowENN delta (sigma - inputLoss) *
        Kakeya.realRpowENN rho (3 + neighborhoodLoss) := by
  have hinverse := neighborhood_one_div_power
    (delta := delta) (sigma := sigma) hdelta
  have hwidth := neighborhood_slab_width_power hdelta hrho
  have hcube :
      volume (wz1PaperGridCube rho (0, 0, 0)) =
        Kakeya.realRpowENN rho 3 := by
    rw [wz1PaperGridCube_volume_exact hrho]
    simp [Kakeya.realRpowENN]
  have hdeltaPower :
      Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN delta (sigma - 1) *
          Kakeya.realRpowENN delta 1 =
        Kakeya.realRpowENN delta (sigma - inputLoss) := by
    rw [← realRpowENN_add hdelta, ← realRpowENN_add hdelta]
    congr 1 <;> ring
  have hrhoPower :
      Kakeya.realRpowENN rho (1 / 2) *
          Kakeya.realRpowENN rho (-1 / 2 + neighborhoodLoss) *
          Kakeya.realRpowENN rho 3 =
        Kakeya.realRpowENN rho (3 + neighborhoodLoss) := by
    rw [← realRpowENN_add hrho, ← realRpowENN_add hrho]
    congr 1 <;> ring
  unfold pureWZ2PreCommonBinHeavySlabNeighborhoodCost
    pureWZ2PreCommonBinGlobalNeighborhoodCostWithSlabFactor
    pureWZ2Node05V4RichHeavyNeighborhoodConstant
  rw [hinverse, hwidth, hcube]
  calc
    2 * 10 *
          (132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
            Kakeya.realRpowENN delta (sigma - 1)) *
          (4 * Kakeya.realRpowENN rho (1 / 2) *
            Kakeya.realRpowENN delta 1) *
          13 * 512 * Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 *
          Kakeya.realRpowENN rho (-1 / 2 + neighborhoodLoss) *
          Kakeya.realRpowENN rho 3 =
        (2 * 10 * 132 * 10 * 4 * 13 * 512) *
          Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 *
          (Kakeya.realRpowENN delta (-inputLoss) *
            Kakeya.realRpowENN delta (sigma - 1) *
            Kakeya.realRpowENN delta 1) *
          (Kakeya.realRpowENN rho (1 / 2) *
            Kakeya.realRpowENN rho (-1 / 2 + neighborhoodLoss) *
            Kakeya.realRpowENN rho 3) := by ring
    _ = (2 * 10 * 132 * 10 * 4 * 13 * 512) *
          Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 *
          Kakeya.realRpowENN delta (sigma - inputLoss) *
          Kakeya.realRpowENN rho (3 + neighborhoodLoss) := by
      rw [hdeltaPower, hrhoPower]

/-- Family-independent P0 data for the complete heavy-slab neighborhood
budget.  The point-density cutoff is stored together with the one normalized
cost inequality needed after `RequiredCubeCount` has been reduced to its
paper `rho⁻¹/²` branch. -/
structure PureWZ2Node05V4RichNeighborhoodBudgetThreshold
    (sigma sourceLossCeiling firstOutputLoss secondLossCeiling neighborhoodLoss
      scaleLoss : ℝ) where
  pointDensity : PureWZ2Node05V4RichNeighborhoodDensityThreshold
    sigma sourceLossCeiling firstOutputLoss
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_pointDensity : delta₀ ≤ pointDensity.delta₀
  rho₀ : ℝ
  rho₀_pos : 0 < rho₀
  rho₀_le_one : rho₀ ≤ 1
  scale_conversion :
    ∀ {firstTerminalLoss secondTerminalLoss delta rho : ℝ},
      0 ≤ firstTerminalLoss → firstTerminalLoss ≤ firstOutputLoss →
      0 ≤ secondTerminalLoss → secondTerminalLoss ≤ secondLossCeiling →
      0 < delta → delta ≤ 1 → 0 < rho → rho ≤ 1 →
      rho ≤ Real.rpow delta scaleLoss →
      Kakeya.realRpowENN rho
          (sigma + 2 * firstTerminalLoss - secondTerminalLoss) ≤
        Kakeya.realRpowENN delta
          (pureWZ2Node05V4RichNeighborhoodPointDensityLoss
            sourceLossCeiling firstOutputLoss + 2 * firstTerminalLoss)
  normalized_budget :
    ∀ {inputLoss firstTerminalLoss delta rho : ℝ},
      0 ≤ inputLoss → inputLoss ≤ sourceLossCeiling →
      0 ≤ firstTerminalLoss → firstTerminalLoss ≤ firstOutputLoss →
      0 < delta → delta ≤ delta₀ → 0 < rho → rho ≤ rho₀ →
      rho ≤ Real.rpow delta scaleLoss →
      pureWZ2Node05V4RichHeavyNeighborhoodConstant *
          Prop62PaperAudit.V4.logarithmicLoss delta ^ 20 *
          Kakeya.realRpowENN delta
            (-(inputLoss + 2 * firstTerminalLoss)) ≤
        wz2PaperPureRefinementFraction rho 61 *
          Kakeya.realRpowENN rho
            (2 * firstOutputLoss - 2 * firstTerminalLoss - neighborhoodLoss)

/-- Select the complete heavy-neighborhood cutoff before any runtime family,
scale, cell, or slab is known. -/
theorem pureWZ2Node05V4Rich_neighborhoodBudget_threshold
    {sigma sourceLossCeiling firstOutputLoss secondLossCeiling neighborhoodLoss
      scaleLoss : ℝ}
    (hsource : 0 ≤ sourceLossCeiling)
    (hfirst : 0 < firstOutputLoss)
    (hsecond : 0 ≤ secondLossCeiling)
    (hscale : 0 < scaleLoss)
    (hscaleConversionGap :
      pureWZ2Node05V4RichNeighborhoodPointDensityLoss
            sourceLossCeiling firstOutputLoss + 2 * firstOutputLoss ≤
        scaleLoss * (sigma - secondLossCeiling))
    (hgap :
      sourceLossCeiling + 2 * firstOutputLoss <
        scaleLoss * (neighborhoodLoss - 3 * firstOutputLoss)) :
    Nonempty (PureWZ2Node05V4RichNeighborhoodBudgetThreshold
      sigma sourceLossCeiling firstOutputLoss secondLossCeiling
        neighborhoodLoss scaleLoss) := by
  rcases pureWZ2Node05V4Rich_neighborhoodDensity_threshold
      (sigma := sigma) (sourceLossCeiling := sourceLossCeiling) hfirst with
    ⟨pointDensity⟩
  let sourceCost := sourceLossCeiling + 2 * firstOutputLoss
  let gain := neighborhoodLoss - 3 * firstOutputLoss
  have hsourceCost : 0 ≤ sourceCost := by
    dsimp only [sourceCost]
    positivity
  have hgain : 0 < gain := by
    dsimp only [gain]
    have hpositive : 0 < scaleLoss * gain := by
      dsimp only [gain] at hgap ⊢
      exact hsourceCost.trans_lt hgap
    exact pos_of_mul_pos_right hpositive hscale.le
  let logLoss := (scaleLoss * gain - sourceCost) / 2
  let intermediate := sourceCost + logLoss
  have hlogLoss : 0 < logLoss := by
    dsimp only [logLoss]
    linarith
  have hintermediate : 0 ≤ intermediate := by
    dsimp only [intermediate]
    positivity
  have hintermediateGap : intermediate < scaleLoss * gain := by
    dsimp only [intermediate, logLoss]
    linarith
  let logCoefficient :=
    pureWZ2Node05V4RichHeavyNeighborhoodConstant * 2 ^ (20 : ℕ)
  have hlogCoefficientTop : logCoefficient ≠ ⊤ := by
    dsimp only [logCoefficient,
      pureWZ2Node05V4RichHeavyNeighborhoodConstant]
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (by norm_num))
  rcases exists_delta_log_absorbed_ennreal logCoefficient hlogCoefficientTop
      hlogLoss (show 0 < (20 : ℕ) by norm_num) with
    ⟨logDelta₀, hlogDelta₀, hlogDelta₀One, hlogAbsorb⟩
  rcases exists_scale_power_conversion
      (C := 1) (p := scaleLoss) (a := intermediate) (b := gain)
      (by norm_num) hscale hintermediate hintermediateGap with
    ⟨transportDelta₀, htransportDelta₀, htransportDelta₀One, htransport⟩
  rcases pureWZ2_refinementFraction_power_schedule 61 hfirst with
    ⟨refinementRho₀, hrefinementRho₀, hrefinementRho₀One, hrefinement⟩
  let delta₀ := min pointDensity.delta₀ (min logDelta₀ transportDelta₀)
  let rho₀ := refinementRho₀
  refine ⟨{
    pointDensity := pointDensity
    delta₀ := delta₀
    delta₀_pos := lt_min pointDensity.delta₀_pos <|
      lt_min hlogDelta₀ htransportDelta₀
    delta₀_le_pointDensity := min_le_left _ _
    rho₀ := rho₀
    rho₀_pos := hrefinementRho₀
    rho₀_le_one := hrefinementRho₀One
    scale_conversion := ?_
    normalized_budget := ?_
  }⟩
  · intro firstTerminalLoss secondTerminalLoss delta rho hfirstNonneg
      hfirstCeiling hsecondNonneg hsecondCeiling hdelta hdeltaOne hrho hrhoOne
      hrhoPower
    have hbaseExponent : 0 < sigma - secondLossCeiling := by
      have hleftPos : 0 <
          pureWZ2Node05V4RichNeighborhoodPointDensityLoss
              sourceLossCeiling firstOutputLoss + 2 * firstOutputLoss := by
        unfold pureWZ2Node05V4RichNeighborhoodPointDensityLoss
        nlinarith
      have hproduct : 0 < scaleLoss * (sigma - secondLossCeiling) :=
        hleftPos.trans_le hscaleConversionGap
      exact pos_of_mul_pos_right hproduct hscale.le
    have hactualExponent : 0 ≤
        sigma + 2 * firstTerminalLoss - secondTerminalLoss := by
      linarith
    have hbasePower :
        Real.rpow rho
            (sigma + 2 * firstTerminalLoss - secondTerminalLoss) ≤
          Real.rpow (Real.rpow delta scaleLoss)
            (sigma + 2 * firstTerminalLoss - secondTerminalLoss) :=
      Real.rpow_le_rpow hrho.le hrhoPower hactualExponent
    have hcompose :
        Real.rpow (Real.rpow delta scaleLoss)
            (sigma + 2 * firstTerminalLoss - secondTerminalLoss) =
          Real.rpow delta
            (scaleLoss *
              (sigma + 2 * firstTerminalLoss - secondTerminalLoss)) :=
      (Real.rpow_mul hdelta.le _ _).symm
    have hexponent :
        pureWZ2Node05V4RichNeighborhoodPointDensityLoss
              sourceLossCeiling firstOutputLoss + 2 * firstTerminalLoss ≤
          scaleLoss *
            (sigma + 2 * firstTerminalLoss - secondTerminalLoss) := by
      calc
        _ ≤ pureWZ2Node05V4RichNeighborhoodPointDensityLoss
              sourceLossCeiling firstOutputLoss + 2 * firstOutputLoss := by
          gcongr
        _ ≤ scaleLoss * (sigma - secondLossCeiling) := hscaleConversionGap
        _ ≤ scaleLoss *
            (sigma + 2 * firstTerminalLoss - secondTerminalLoss) := by
          gcongr
          linarith
    apply ENNReal.ofReal_mono
    calc
      Real.rpow rho
          (sigma + 2 * firstTerminalLoss - secondTerminalLoss) ≤
        Real.rpow (Real.rpow delta scaleLoss)
          (sigma + 2 * firstTerminalLoss - secondTerminalLoss) := hbasePower
      _ = Real.rpow delta
          (scaleLoss *
            (sigma + 2 * firstTerminalLoss - secondTerminalLoss)) := hcompose
      _ ≤ Real.rpow delta
          (pureWZ2Node05V4RichNeighborhoodPointDensityLoss
            sourceLossCeiling firstOutputLoss + 2 * firstTerminalLoss) :=
        Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne hexponent
  intro inputLoss firstTerminalLoss delta rho hinputNonneg hinputCeiling
    hterminalNonneg hterminalCeiling hdelta hdeltaSmall hrho hrhoSmall
    hrhoPower
  have hdeltaOne : delta ≤ 1 :=
    hdeltaSmall.trans <| (min_le_right _ _).trans <|
      (min_le_left _ _).trans hlogDelta₀One
  have hrhoOne : rho ≤ 1 := hrhoSmall.trans hrefinementRho₀One
  have hdeltaLog : delta ≤ logDelta₀ :=
    hdeltaSmall.trans <| (min_le_right _ _).trans (min_le_left _ _)
  have hdeltaTransport : delta ≤ transportDelta₀ :=
    hdeltaSmall.trans <| (min_le_right _ _).trans (min_le_right _ _)
  have hactualCost : inputLoss + 2 * firstTerminalLoss ≤ sourceCost := by
    dsimp only [sourceCost]
    linarith
  have hlogarithmic :
      Prop62PaperAudit.V4.logarithmicLoss delta ≤
        2 * ENNReal.ofReal (1 + Real.log delta⁻¹) := by
    simpa only [Prop62PaperAudit.V4.logarithmicLoss,
      show ENNReal.ofReal (2 * (1 + Real.log delta⁻¹)) =
        2 * ENNReal.ofReal (1 + Real.log delta⁻¹) by
          rw [ENNReal.ofReal_mul (by norm_num)]
          norm_num] using
      PureWZ2.proposition63_logarithmicLoss_le_two_logEnvelope hdelta hdeltaOne
  have hlogPower :
      pureWZ2Node05V4RichHeavyNeighborhoodConstant *
          Prop62PaperAudit.V4.logarithmicLoss delta ^ 20 ≤
        Kakeya.realRpowENN delta (-logLoss) := by
    calc
      pureWZ2Node05V4RichHeavyNeighborhoodConstant *
          Prop62PaperAudit.V4.logarithmicLoss delta ^ 20 ≤
        pureWZ2Node05V4RichHeavyNeighborhoodConstant *
          (2 * ENNReal.ofReal (1 + Real.log delta⁻¹)) ^ 20 := by gcongr
      _ = logCoefficient *
          ENNReal.ofReal (1 + Real.log delta⁻¹) ^ 20 := by
        dsimp only [logCoefficient]
        rw [mul_pow]
        ring
      _ ≤ Kakeya.realRpowENN delta (-logLoss) :=
        hlogAbsorb delta hdelta hdeltaLog
  have hactualPower :
      Kakeya.realRpowENN delta (-(inputLoss + 2 * firstTerminalLoss)) ≤
        Kakeya.realRpowENN delta (-sourceCost) :=
    realRpowENN_antitone hdelta hdeltaOne (by linarith)
  have htransported :
      Kakeya.realRpowENN delta (-intermediate) ≤
        Kakeya.realRpowENN rho (-gain) :=
    htransport delta rho hdelta hdeltaTransport hrho hrhoOne (by
      simpa using hrhoPower)
  have hbase :
      pureWZ2Node05V4RichHeavyNeighborhoodConstant *
          Prop62PaperAudit.V4.logarithmicLoss delta ^ 20 *
          Kakeya.realRpowENN delta
            (-(inputLoss + 2 * firstTerminalLoss)) ≤
        Kakeya.realRpowENN rho (-gain) := by
    calc
      _ ≤ Kakeya.realRpowENN delta (-logLoss) *
          Kakeya.realRpowENN delta (-sourceCost) := by gcongr
      _ = Kakeya.realRpowENN delta (-intermediate) := by
        rw [← realRpowENN_add hdelta]
        dsimp only [intermediate]
        congr 1 <;> ring
      _ ≤ _ := htransported
  have hactualGain :
      gain ≤ neighborhoodLoss - 3 * firstOutputLoss +
        2 * firstTerminalLoss := by
    dsimp only [gain]
    linarith
  have hgainPower :
      Kakeya.realRpowENN rho (-gain) ≤
        Kakeya.realRpowENN rho
          (-(neighborhoodLoss - 3 * firstOutputLoss +
            2 * firstTerminalLoss)) :=
    realRpowENN_antitone hrho hrhoOne (by linarith)
  have hrefinementPower :
      Kakeya.realRpowENN rho firstOutputLoss ≤
        wz2PaperPureRefinementFraction rho 61 :=
    hrefinement rho hrho hrhoSmall
  calc
    pureWZ2Node05V4RichHeavyNeighborhoodConstant *
          Prop62PaperAudit.V4.logarithmicLoss delta ^ 20 *
          Kakeya.realRpowENN delta
            (-(inputLoss + 2 * firstTerminalLoss)) ≤
        Kakeya.realRpowENN rho
          (-(neighborhoodLoss - 3 * firstOutputLoss +
            2 * firstTerminalLoss)) := hbase.trans hgainPower
    _ = Kakeya.realRpowENN rho firstOutputLoss *
        Kakeya.realRpowENN rho
          (2 * firstOutputLoss - 2 * firstTerminalLoss - neighborhoodLoss) := by
      rw [← realRpowENN_add hrho]
      congr 1 <;> ring
    _ ≤ wz2PaperPureRefinementFraction rho 61 *
        Kakeya.realRpowENN rho
          (2 * firstOutputLoss - 2 * firstTerminalLoss - neighborhoodLoss) := by
      gcongr

/-- The complete P0 budget instantiated on one actual dependent two-call
witness.  Both branches of `RequiredCubeCount` are discharged internally;
the caller supplies no envelope-density or parent-count hypothesis. -/
theorem heavySlabNeighborhood_budget
    {sourceLossCeiling secondLossCeiling neighborhoodLoss scaleLoss : ℝ}
    (threshold : PureWZ2Node05V4RichNeighborhoodBudgetThreshold
      sigma sourceLossCeiling schedule.firstOutputLoss secondLossCeiling
        neighborhoodLoss scaleLoss)
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rhoRequested.1) twoScale)
    (hinputNonneg : 0 ≤ inputLoss)
    (hinputCeiling : inputLoss ≤ sourceLossCeiling)
    (hsecondCeiling : outputLoss ≤ secondLossCeiling)
    (hdeltaSmall : delta ≤ threshold.delta₀)
    (hrhoSmall : rhoRequested.1 ≤ 1 / 12)
    (hrhoThreshold : rhoRequested.1 ≤ threshold.rho₀)
    (hrhoPower : rhoRequested.1 ≤ Real.rpow delta scaleLoss) :
    pureWZ2PreCommonBinHeavySlabNeighborhoodCost
          sigma inputLoss delta rhoRequested.1 *
        pureWZ2PreCommonBinRequiredCubeCount pullback neighborhoodLoss ≤
      volume pullback.shading.union := by
  let firstTerminalLoss := twoScale.first.rich.terminalLoss
  let secondTerminalLoss := twoScale.second.terminalLoss
  have hdelta : 0 < delta := current.grain.extremal.delta_pos
  have hdeltaOne : delta ≤ 1 := current.grain.extremal.delta_le_one
  have hrho : 0 < rhoRequested.1 :=
    twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hrhoOne : rhoRequested.1 ≤ 1 := rhoRequested.property.2
  have hfirstTerminalNonneg : 0 ≤ firstTerminalLoss :=
    twoScale.first.rich.terminalLoss_pos.le
  have hfirstTerminalCeiling : firstTerminalLoss ≤ schedule.firstOutputLoss :=
    twoScale.first.rich.terminalLoss_le_output
  have hsecondTerminalNonneg : 0 ≤ secondTerminalLoss :=
    twoScale.second.terminalLoss_pos.le
  have hsecondTerminalCeiling : secondTerminalLoss ≤ secondLossCeiling :=
    twoScale.second.terminalLoss_le_output.trans hsecondCeiling
  have hpointDensity := twoScale.first_terminal_pointDensity_lower
    threshold.pointDensity hinputCeiling
      (hdeltaSmall.trans threshold.delta₀_le_pointDensity)
  have hscaleConversion := threshold.scale_conversion
    hfirstTerminalNonneg hfirstTerminalCeiling hsecondTerminalNonneg
    hsecondTerminalCeiling hdelta hdeltaOne hrho hrhoOne hrhoPower
  have hbalance := twoScale.preCommonBin_balanceMass_lower_of_pointDensity
    pullback hpointDensity hscaleConversion
  have hrequired := twoScale.preCommonBin_requiredCubeCount_le_of_balanceMass
    (neighborhoodLoss := neighborhoodLoss) pullback hbalance
  have hregularity :
      (twoScale.first.fourDegreeReceipts.regularity : ENNReal) ≤
        Prop62PaperAudit.V4.logarithmicLoss delta ^ 10 :=
    twoScale.first.rich.terminal_regularity_bound
  have hnormalized := threshold.normalized_budget
    hinputNonneg hinputCeiling hfirstTerminalNonneg hfirstTerminalCeiling
    hdelta hdeltaSmall hrho hrhoThreshold hrhoPower
  apply pullback.heavySlabNeighborhood_budget_of_secondRefinedVolume hrhoSmall
  let logarithmic := Prop62PaperAudit.V4.logarithmicLoss delta
  let constant := pureWZ2Node05V4RichHeavyNeighborhoodConstant
  let common := Kakeya.realRpowENN delta
      (sigma + 2 * firstTerminalLoss) *
    Kakeya.realRpowENN rhoRequested.1 (3 + neighborhoodLoss)
  have hcost := heavyNeighborhoodCost_firstBranch_power_identity
    (sigma := sigma) (inputLoss := inputLoss) (delta := delta)
    (rho := rhoRequested.1) (neighborhoodLoss := neighborhoodLoss) hdelta hrho
  have hleftIdentity :
      logarithmic ^ 10 *
          ((pureWZ2PreCommonBinHeavySlabNeighborhoodCost
                sigma inputLoss delta rhoRequested.1 *
              Kakeya.realRpowENN rhoRequested.1
                (-1 / 2 + neighborhoodLoss)) *
            volume (wz1PaperGridCube rhoRequested.1 (0, 0, 0))) =
        (constant * logarithmic ^ 20 *
            Kakeya.realRpowENN delta
              (-(inputLoss + 2 * firstTerminalLoss))) * common := by
    rw [hcost]
    dsimp only [logarithmic, constant, common]
    have hdeltaPower :
        Kakeya.realRpowENN delta (sigma - inputLoss) =
          Kakeya.realRpowENN delta
              (-(inputLoss + 2 * firstTerminalLoss)) *
            Kakeya.realRpowENN delta
              (sigma + 2 * firstTerminalLoss) := by
      rw [← realRpowENN_add hdelta]
      congr 1 <;> ring
    rw [hdeltaPower, show logarithmic ^ 20 =
        logarithmic ^ 10 * logarithmic ^ 10 by rw [← pow_add]]
    ring
  have hrightIdentity :
      (wz2PaperPureRefinementFraction rhoRequested.1 61 *
          Kakeya.realRpowENN rhoRequested.1
            (2 * schedule.firstOutputLoss - 2 * firstTerminalLoss -
              neighborhoodLoss)) * common =
        (wz2PaperPureRefinementFraction rhoRequested.1 61 *
            Kakeya.realRpowENN rhoRequested.1
              (sigma + 2 * schedule.firstOutputLoss)) *
          (Kakeya.realRpowENN rhoRequested.1 3 *
            Kakeya.realRpowENN (delta / rhoRequested.1)
              (sigma + 2 * firstTerminalLoss)) := by
    let exponent := sigma + 2 * firstTerminalLoss
    have hquotient := neighborhood_realRpowENN_div_mul
      (delta := delta) (rho := rhoRequested.1) (exponent := exponent)
      hdelta hrho
    have hrhoPowerIdentity :
        Kakeya.realRpowENN rhoRequested.1
              (2 * schedule.firstOutputLoss - 2 * firstTerminalLoss -
                neighborhoodLoss) *
            Kakeya.realRpowENN rhoRequested.1 (3 + neighborhoodLoss) =
          Kakeya.realRpowENN rhoRequested.1
            (3 + 2 * schedule.firstOutputLoss - 2 * firstTerminalLoss) := by
      rw [← realRpowENN_add hrho]
      congr 1 <;> ring
    have htargetRho :
        Kakeya.realRpowENN rhoRequested.1
              (sigma + 2 * schedule.firstOutputLoss) *
            Kakeya.realRpowENN rhoRequested.1 3 =
          Kakeya.realRpowENN rhoRequested.1 exponent *
            Kakeya.realRpowENN rhoRequested.1
              (3 + 2 * schedule.firstOutputLoss - 2 * firstTerminalLoss) := by
      rw [← realRpowENN_add hrho, ← realRpowENN_add hrho]
      dsimp only [exponent]
      congr 1 <;> ring
    dsimp only [common]
    calc
      wz2PaperPureRefinementFraction rhoRequested.1 61 *
            Kakeya.realRpowENN rhoRequested.1
              (2 * schedule.firstOutputLoss - 2 * firstTerminalLoss -
                neighborhoodLoss) *
            (Kakeya.realRpowENN delta exponent *
              Kakeya.realRpowENN rhoRequested.1 (3 + neighborhoodLoss)) =
        wz2PaperPureRefinementFraction rhoRequested.1 61 *
          Kakeya.realRpowENN delta exponent *
          (Kakeya.realRpowENN rhoRequested.1
              (2 * schedule.firstOutputLoss - 2 * firstTerminalLoss -
                neighborhoodLoss) *
            Kakeya.realRpowENN rhoRequested.1 (3 + neighborhoodLoss)) := by ring
      _ = wz2PaperPureRefinementFraction rhoRequested.1 61 *
          Kakeya.realRpowENN delta exponent *
            Kakeya.realRpowENN rhoRequested.1
              (3 + 2 * schedule.firstOutputLoss - 2 * firstTerminalLoss) := by
        rw [hrhoPowerIdentity]
      _ = wz2PaperPureRefinementFraction rhoRequested.1 61 *
          ((Kakeya.realRpowENN (delta / rhoRequested.1) exponent *
              Kakeya.realRpowENN rhoRequested.1 exponent) *
            Kakeya.realRpowENN rhoRequested.1
              (3 + 2 * schedule.firstOutputLoss - 2 * firstTerminalLoss)) := by
        rw [hquotient, mul_assoc]
      _ = wz2PaperPureRefinementFraction rhoRequested.1 61 *
          (Kakeya.realRpowENN rhoRequested.1 exponent *
            Kakeya.realRpowENN rhoRequested.1
              (3 + 2 * schedule.firstOutputLoss - 2 * firstTerminalLoss)) *
          Kakeya.realRpowENN (delta / rhoRequested.1) exponent := by ring
      _ = wz2PaperPureRefinementFraction rhoRequested.1 61 *
          (Kakeya.realRpowENN rhoRequested.1
              (sigma + 2 * schedule.firstOutputLoss) *
            Kakeya.realRpowENN rhoRequested.1 3) *
          Kakeya.realRpowENN (delta / rhoRequested.1) exponent := by
        rw [htargetRho]
      _ = (wz2PaperPureRefinementFraction rhoRequested.1 61 *
            Kakeya.realRpowENN rhoRequested.1
              (sigma + 2 * schedule.firstOutputLoss)) *
          (Kakeya.realRpowENN rhoRequested.1 3 *
            Kakeya.realRpowENN (delta / rhoRequested.1)
              (sigma + 2 * firstTerminalLoss)) := by
        dsimp only [exponent]
        ring
  calc
    (twoScale.first.fourDegreeReceipts.regularity : ENNReal) *
          ((pureWZ2PreCommonBinHeavySlabNeighborhoodCost
                sigma inputLoss delta rhoRequested.1 *
              pureWZ2PreCommonBinRequiredCubeCount
                pullback neighborhoodLoss) *
            volume (wz1PaperGridCube rhoRequested.1 (0, 0, 0))) ≤
        logarithmic ^ 10 *
          ((pureWZ2PreCommonBinHeavySlabNeighborhoodCost
                sigma inputLoss delta rhoRequested.1 *
              Kakeya.realRpowENN rhoRequested.1
                (-1 / 2 + neighborhoodLoss)) *
            volume (wz1PaperGridCube rhoRequested.1 (0, 0, 0))) := by
      gcongr
    _ = (constant * logarithmic ^ 20 *
          Kakeya.realRpowENN delta
            (-(inputLoss + 2 * firstTerminalLoss))) * common := hleftIdentity
    _ ≤ (wz2PaperPureRefinementFraction rhoRequested.1 61 *
          Kakeya.realRpowENN rhoRequested.1
            (2 * schedule.firstOutputLoss - 2 * firstTerminalLoss -
              neighborhoodLoss)) * common := by gcongr
    _ = _ := hrightIdentity

end PureWZ2Node05V4RichSecondCallData

end Kakeya.Assouad

end
