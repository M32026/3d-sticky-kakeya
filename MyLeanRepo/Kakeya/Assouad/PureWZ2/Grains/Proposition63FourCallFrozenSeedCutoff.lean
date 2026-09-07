import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallInnerLossSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CordobaLogAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers

/-!
# Family-free cutoffs for a frozen Proposition 6.3 four-call seed

The `rho` cutoff collects exactly the thresholds used at the coarse and
ordered-pair scales.  The aligned-interval threshold belongs to the fine
input scale and is deliberately kept in the separate `fineCutoff` field.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- All scale choices which can be frozen immediately after choosing the
three-budget four-call loss seed, before a family or shading is exposed. -/
structure Proposition63FourCallFrozenSeedCutoffData
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss) where
  rhoCutoff : ℝ
  rhoCutoff_pos : 0 < rhoCutoff
  rhoCutoff_le_one : rhoCutoff ≤ 1
  rhoCutoff_le_first : rhoCutoff ≤ seed.schedule.first.delta₀
  rhoCutoff_le_second : rhoCutoff ≤ seed.schedule.second.delta₀
  rhoCutoff_le_third : rhoCutoff ≤ seed.schedule.third.delta₀
  rhoCutoff_le_fourth : rhoCutoff ≤ seed.schedule.fourth.delta₀
  rhoCutoff_le_rhoAbsorption : rhoCutoff ≤ seed.rhoAbsorption.delta₀
  rhoCutoff_le_firstStageAbsorption :
    rhoCutoff ≤ seed.firstStageAbsorption.delta₀
  rhoCutoff_le_secondReentryAbsorption :
    rhoCutoff ≤ seed.secondReentryAbsorption.delta₀
  rhoCutoff_le_firstGridAbsorption :
    rhoCutoff ≤ seed.firstGridAbsorption.delta₀
  rhoCutoff_le_secondGridAbsorption :
    rhoCutoff ≤ seed.secondGridAbsorption.delta₀
  rhoCutoff_le_firstCrossAbsorption :
    rhoCutoff ≤ seed.firstCrossAbsorption.delta₀
  rhoCutoff_le_secondCrossAbsorption :
    rhoCutoff ≤ seed.secondCrossAbsorption.delta₀
  rhoCutoff_le_firstBoundaryAbsorption :
    rhoCutoff ≤ seed.firstBoundaryAbsorption.delta₀
  rhoCutoff_le_secondBoundaryAbsorption :
    rhoCutoff ≤ seed.secondBoundaryAbsorption.delta₀
  rhoCutoff_le_outerRetentionAbsorption :
    rhoCutoff ≤ seed.outerRetentionAbsorption.delta₀
  rhoCutoff_le_parentRetentionAbsorption :
    rhoCutoff ≤ seed.parentRetentionAbsorption.delta₀
  rhoCutoff_le_firstRestoreAbsorption :
    rhoCutoff ≤ seed.firstRestoreAbsorption.delta₀
  rhoCutoff_le_secondRestoreAbsorption :
    rhoCutoff ≤ seed.secondRestoreAbsorption.delta₀
  rhoCutoff_le_multiplicityAbsorption :
    rhoCutoff ≤ seed.multiplicityAbsorption.delta₀
  rhoCutoff_le_balancingBoundaryAbsorption :
    rhoCutoff ≤ seed.balancingBoundaryAbsorption.delta₀
  rhoCutoff_le_balancingAbsorption :
    rhoCutoff ≤ seed.balancingAbsorption.delta₀
  rhoCutoff_le_traceAbsorption :
    rhoCutoff ≤ seed.traceAbsorption.delta₀
  rhoCutoff_le_critical : rhoCutoff ≤ seed.critical.delta₀
  robustSmallCutoff : ℝ
  robustSmallCutoff_pos : 0 < robustSmallCutoff
  rhoCutoff_le_robustSmallCutoff : rhoCutoff ≤ robustSmallCutoff
  robustScale_small : ∀ rho : ℝ, 0 < rho → rho ≤ rhoCutoff →
    Real.rpow rho seed.robustExponent ≤ 1 / 10000
  robustScale_small_discrete : ∀ rho : ℝ, 0 < rho → rho ≤ rhoCutoff →
    Real.rpow rho (1 - discreteLoss) ≤ 1 / 10000
  cordobaLogCutoff : ℝ
  cordobaLogCutoff_pos : 0 < cordobaLogCutoff
  rhoCutoff_le_cordobaLogCutoff : rhoCutoff ≤ cordobaLogCutoff
  cordobaLog : ∀ rho : ℝ, 0 < rho → rho ≤ rhoCutoff →
    ∀ k : ℕ, 0 < k → (k : ℝ) ≤ 100 / rho ^ 3 →
      Real.rpow rho seed.epsilon₁ *
        (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108
  cordobaAxisCutoff : ℝ
  cordobaAxisCutoff_pos : 0 < cordobaAxisCutoff
  rhoCutoff_le_cordobaAxisCutoff : rhoCutoff ≤ cordobaAxisCutoff
  cordobaAxis : ∀ rho : ℝ, 0 < rho → rho ≤ rhoCutoff →
    4 * (6 * rho) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow rho (1 - seed.epsilon₃)) ^ 2
  fineCutoff : ℝ
  fineCutoff_pos : 0 < fineCutoff
  fineCutoff_le_alignedAbsorption :
    fineCutoff ≤ seed.alignedAbsorption.delta₀

/-- Freeze all family-independent scale thresholds carried by a three-budget
four-call loss seed. -/
theorem proposition63_four_call_frozen_seed_cutoff
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss) :
    Nonempty (Proposition63FourCallFrozenSeedCutoffData seed) := by
  rcases pure_wz2_exists_delta₀_rpow_le
      (threshold := (1 / 10000 : ℝ)) (s := seed.robustExponent)
      (by norm_num) seed.robustExponent_pos with
    ⟨robustSmallCutoff, robustSmallCutoffPos, robustSmallCutoffOne,
      robustSmall⟩
  rcases cordoba_log_absorption_exists seed.epsilon₁_pos with
    ⟨cordobaLogCutoff, cordobaLogCutoffPos, cordobaLogCutoffOne,
      cordobaLog⟩
  have epsilon₁_lt_half : seed.epsilon₁ < 1 / 2 := by
    rw [seed.epsilon₁_eq]
    linarith [seed.paperAngularExponent_le_one]
  rcases cordoba_ax_condition_exists seed.epsilon₁_pos epsilon₁_lt_half with
    ⟨cordobaAxisCutoff, cordobaAxisCutoffPos, cordobaAxisCutoffOne,
      cordobaAxis⟩
  have epsilon₃_eq : seed.epsilon₃ = 1 - 2 * seed.epsilon₁ :=
    seed.epsilon₃_eq
  let scheduleCutoff : ℝ :=
    min seed.schedule.first.delta₀ <|
    min seed.schedule.second.delta₀ <|
    min seed.schedule.third.delta₀ seed.schedule.fourth.delta₀
  let reentryCutoff : ℝ :=
    min seed.rhoAbsorption.delta₀ <|
    min seed.firstStageAbsorption.delta₀ <|
      seed.secondReentryAbsorption.delta₀
  let gridCrossCutoff : ℝ :=
    min seed.firstGridAbsorption.delta₀ <|
    min seed.secondGridAbsorption.delta₀ <|
    min seed.firstCrossAbsorption.delta₀ <|
      seed.secondCrossAbsorption.delta₀
  let boundaryRetentionCutoff : ℝ :=
    min seed.firstBoundaryAbsorption.delta₀ <|
    min seed.secondBoundaryAbsorption.delta₀ <|
    min seed.outerRetentionAbsorption.delta₀ <|
      seed.parentRetentionAbsorption.delta₀
  let tailCutoff : ℝ :=
    min seed.firstRestoreAbsorption.delta₀ <|
    min seed.secondRestoreAbsorption.delta₀ <|
    min seed.multiplicityAbsorption.delta₀ <|
    min seed.balancingBoundaryAbsorption.delta₀ <|
    min seed.balancingAbsorption.delta₀ <|
      seed.traceAbsorption.delta₀
  let extraCutoff : ℝ :=
    min seed.critical.delta₀ <|
    min robustSmallCutoff <| min cordobaLogCutoff cordobaAxisCutoff
  let rhoCutoff : ℝ := min scheduleCutoff <| min reentryCutoff <|
    min gridCrossCutoff <| min boundaryRetentionCutoff <|
      min tailCutoff extraCutoff
  have scheduleCutoffPos : 0 < scheduleCutoff := by
    dsimp only [scheduleCutoff]
    exact lt_min seed.schedule.first.delta₀_pos <|
      lt_min seed.schedule.second.delta₀_pos <|
        lt_min seed.schedule.third.delta₀_pos seed.schedule.fourth.delta₀_pos
  have reentryCutoffPos : 0 < reentryCutoff := by
    dsimp only [reentryCutoff]
    exact lt_min seed.rhoAbsorption.delta₀_pos <|
      lt_min seed.firstStageAbsorption.delta₀_pos
        seed.secondReentryAbsorption.delta₀_pos
  have gridCrossCutoffPos : 0 < gridCrossCutoff := by
    dsimp only [gridCrossCutoff]
    exact lt_min seed.firstGridAbsorption.delta₀_pos <|
      lt_min seed.secondGridAbsorption.delta₀_pos <|
        lt_min seed.firstCrossAbsorption.delta₀_pos
          seed.secondCrossAbsorption.delta₀_pos
  have boundaryRetentionCutoffPos : 0 < boundaryRetentionCutoff := by
    dsimp only [boundaryRetentionCutoff]
    exact lt_min seed.firstBoundaryAbsorption.delta₀_pos <|
      lt_min seed.secondBoundaryAbsorption.delta₀_pos <|
        lt_min seed.outerRetentionAbsorption.delta₀_pos
          seed.parentRetentionAbsorption.delta₀_pos
  have tailCutoffPos : 0 < tailCutoff := by
    dsimp only [tailCutoff]
    exact lt_min seed.firstRestoreAbsorption.delta₀_pos <|
      lt_min seed.secondRestoreAbsorption.delta₀_pos <|
        lt_min seed.multiplicityAbsorption.delta₀_pos <|
          lt_min seed.balancingBoundaryAbsorption.delta₀_pos <|
            lt_min seed.balancingAbsorption.delta₀_pos
              seed.traceAbsorption.delta₀_pos
  have extraCutoffPos : 0 < extraCutoff := by
    dsimp only [extraCutoff]
    exact lt_min seed.critical.delta₀_pos <|
      lt_min robustSmallCutoffPos <|
        lt_min cordobaLogCutoffPos cordobaAxisCutoffPos
  have rhoCutoffPos : 0 < rhoCutoff := by
    dsimp only [rhoCutoff]
    exact lt_min scheduleCutoffPos <| lt_min reentryCutoffPos <|
      lt_min gridCrossCutoffPos <| lt_min boundaryRetentionCutoffPos <|
        lt_min tailCutoffPos extraCutoffPos
  have rhoCutoffOne : rhoCutoff ≤ 1 := by
    exact (min_le_left scheduleCutoff
      (min reentryCutoff (min gridCrossCutoff
        (min boundaryRetentionCutoff (min tailCutoff extraCutoff))))).trans <|
      (min_le_left seed.schedule.first.delta₀
        (min seed.schedule.second.delta₀
          (min seed.schedule.third.delta₀ seed.schedule.fourth.delta₀))).trans
        seed.schedule.first.delta₀_le_one
  have rhoLeSchedule : rhoCutoff ≤ scheduleCutoff := by
    exact min_le_left _ _
  have rhoLeReentry : rhoCutoff ≤ reentryCutoff := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have rhoLeGridCross : rhoCutoff ≤ gridCrossCutoff := by
    exact (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have rhoLeBoundaryRetention : rhoCutoff ≤ boundaryRetentionCutoff := by
    exact (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  have rhoLeTail : rhoCutoff ≤ tailCutoff := by
    exact (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)
  have rhoLeExtra : rhoCutoff ≤ extraCutoff := by
    exact (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨{
    rhoCutoff := rhoCutoff
    rhoCutoff_pos := rhoCutoffPos
    rhoCutoff_le_one := rhoCutoffOne
    rhoCutoff_le_first := rhoLeSchedule.trans (by dsimp only [scheduleCutoff]; simp)
    rhoCutoff_le_second := rhoLeSchedule.trans (by dsimp only [scheduleCutoff]; simp)
    rhoCutoff_le_third := rhoLeSchedule.trans (by dsimp only [scheduleCutoff]; simp)
    rhoCutoff_le_fourth := rhoLeSchedule.trans (by dsimp only [scheduleCutoff]; simp)
    rhoCutoff_le_rhoAbsorption := rhoLeReentry.trans (by dsimp only [reentryCutoff]; simp)
    rhoCutoff_le_firstStageAbsorption := rhoLeReentry.trans (by dsimp only [reentryCutoff]; simp)
    rhoCutoff_le_secondReentryAbsorption := rhoLeReentry.trans (by dsimp only [reentryCutoff]; simp)
    rhoCutoff_le_firstGridAbsorption := rhoLeGridCross.trans (by dsimp only [gridCrossCutoff]; simp)
    rhoCutoff_le_secondGridAbsorption := rhoLeGridCross.trans (by dsimp only [gridCrossCutoff]; simp)
    rhoCutoff_le_firstCrossAbsorption := rhoLeGridCross.trans (by dsimp only [gridCrossCutoff]; simp)
    rhoCutoff_le_secondCrossAbsorption := rhoLeGridCross.trans (by dsimp only [gridCrossCutoff]; simp)
    rhoCutoff_le_firstBoundaryAbsorption := rhoLeBoundaryRetention.trans (by dsimp only [boundaryRetentionCutoff]; simp)
    rhoCutoff_le_secondBoundaryAbsorption := rhoLeBoundaryRetention.trans (by dsimp only [boundaryRetentionCutoff]; simp)
    rhoCutoff_le_outerRetentionAbsorption := rhoLeBoundaryRetention.trans (by dsimp only [boundaryRetentionCutoff]; simp)
    rhoCutoff_le_parentRetentionAbsorption := rhoLeBoundaryRetention.trans (by dsimp only [boundaryRetentionCutoff]; simp)
    rhoCutoff_le_firstRestoreAbsorption := rhoLeTail.trans (by dsimp only [tailCutoff]; simp)
    rhoCutoff_le_secondRestoreAbsorption := rhoLeTail.trans (by dsimp only [tailCutoff]; simp)
    rhoCutoff_le_multiplicityAbsorption := rhoLeTail.trans (by dsimp only [tailCutoff]; simp)
    rhoCutoff_le_balancingBoundaryAbsorption := by
      exact rhoLeTail.trans (by dsimp only [tailCutoff]; simp)
    rhoCutoff_le_balancingAbsorption := rhoLeTail.trans (by dsimp only [tailCutoff]; simp)
    rhoCutoff_le_traceAbsorption := rhoLeTail.trans (by dsimp only [tailCutoff]; simp)
    rhoCutoff_le_critical := rhoLeExtra.trans (by dsimp only [extraCutoff]; simp)
    robustSmallCutoff := robustSmallCutoff
    robustSmallCutoff_pos := robustSmallCutoffPos
    rhoCutoff_le_robustSmallCutoff := rhoLeExtra.trans (by dsimp only [extraCutoff]; simp)
    robustScale_small := by
      intro rho hrho hrhoCutoff
      exact robustSmall rho hrho
        (hrhoCutoff.trans <| rhoLeExtra.trans (by dsimp only [extraCutoff]; simp))
    robustScale_small_discrete := by
      intro rho hrho hrhoCutoff
      rw [← seed.robustExponent_eq]
      exact robustSmall rho hrho
        (hrhoCutoff.trans <| rhoLeExtra.trans (by dsimp only [extraCutoff]; simp))
    cordobaLogCutoff := cordobaLogCutoff
    cordobaLogCutoff_pos := cordobaLogCutoffPos
    rhoCutoff_le_cordobaLogCutoff := rhoLeExtra.trans (by dsimp only [extraCutoff]; simp)
    cordobaLog := by
      intro rho hrho hrhoCutoff k hk hkUpper
      exact cordobaLog rho hrho
        (hrhoCutoff.trans <| rhoLeExtra.trans (by dsimp only [extraCutoff]; simp)) k hk hkUpper
    cordobaAxisCutoff := cordobaAxisCutoff
    cordobaAxisCutoff_pos := cordobaAxisCutoffPos
    rhoCutoff_le_cordobaAxisCutoff := rhoLeExtra.trans (by dsimp only [extraCutoff]; simp)
    cordobaAxis := by
      intro rho hrho hrhoCutoff
      exact cordobaAxis rho hrho
        (hrhoCutoff.trans <| rhoLeExtra.trans (by dsimp only [extraCutoff]; simp))
        seed.epsilon₃ epsilon₃_eq
    fineCutoff := seed.alignedAbsorption.delta₀
    fineCutoff_pos := seed.alignedAbsorption.delta₀_pos
    fineCutoff_le_alignedAbsorption := le_rfl
  }⟩

end Kakeya.Assouad.PureWZ2
