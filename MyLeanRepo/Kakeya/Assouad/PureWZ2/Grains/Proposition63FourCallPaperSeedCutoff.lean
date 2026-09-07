import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallFrozenSeedCutoff
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPaperCoarseAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63PaperTerminalPullbackAbsorption

/-!
# Paper-exponent cutoffs for a frozen Proposition 6.3 four-call seed

This private extension retains the complete legacy cutoff and shrinks its
coarse scale to cover the two paper-angular cross absorptions.  The additional
Córdoba axis estimate is proved from the abstract interval
`0 < paperAngularExponent < 1`; it does not use the historical relation between
`epsilon₁` and `epsilon₃`.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- A Córdoba axis cutoff for any angular exponent strictly between zero and
one. -/
private theorem cordoba_axis_condition_exists_of_angular_exponent
    {angularExponent : ℝ}
    (hAngularPos : 0 < angularExponent)
    (hAngularOne : angularExponent < 1) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ 1 ∧
      ∀ rho : ℝ, 0 < rho → rho ≤ cutoff →
        4 * (6 * rho) ^ 2 ≤
          (3 / 4 : ℝ) * (Real.rpow rho (1 - angularExponent)) ^ 2 := by
  have hHalfPos : 0 < (1 - angularExponent) / 2 := by linarith
  have hHalfLt : (1 - angularExponent) / 2 < 1 / 2 := by linarith
  rcases cordoba_ax_condition_exists hHalfPos hHalfLt with
    ⟨cutoff, hCutoffPos, hCutoffOne, hAxis⟩
  refine ⟨cutoff, hCutoffPos, hCutoffOne, ?_⟩
  intro rho hRhoPos hRhoCutoff
  exact hAxis rho hRhoPos hRhoCutoff angularExponent (by ring)

/-- A private family-free cutoff extending every legacy frozen-seed bound by
the paper-angular power, axis, and cross-call bounds.  Every field of
`legacy` remains available at `rhoCutoff` through `rhoCutoff_le_legacy`. -/
structure Proposition63FourCallPaperSeedCutoffData
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss)
    (coarseCoefficient : NNReal) where
  legacy : Proposition63FourCallFrozenSeedCutoffData seed
  coarseAbsorption : Proposition63FourCallPaperCoarseAbsorptionData
    (proposition63FourCallPaperCoarseCoefficient coarseCoefficient)
    seed.schedule.fourth.normalizationLoss seed.fourthKernel.internalLoss
    seed.epsilon₁ seed.paperAngularExponent seed.floorLoss
    seed.paperCandidateLoss seed.finalLoss
  terminalAbsorption : Proposition63PaperTerminalPullbackAbsorptionData
    seed.schedule.first.normalizationLoss seed.schedule.firstOutputLoss
    seed.sourceWitnessCandidateLoss seed.goodCellCandidateLoss
  rhoCutoff : ℝ
  rhoCutoff_pos : 0 < rhoCutoff
  rhoCutoff_le_one : rhoCutoff ≤ 1
  rhoCutoff_le_legacy : rhoCutoff ≤ legacy.rhoCutoff
  rhoCutoff_le_coarseAbsorption :
    rhoCutoff ≤ coarseAbsorption.delta₀
  rhoCutoff_le_terminalAbsorption :
    rhoCutoff ≤ terminalAbsorption.delta₀
  rhoCutoff_le_ancestorDensityLiftAbsorption :
    rhoCutoff ≤ seed.ancestorDensityLiftAbsorption.delta₀
  rhoCutoff_le_ancestorReentryAbsorption :
    rhoCutoff ≤ seed.ancestorReentryAbsorption.delta₀
  rhoCutoff_le_nestedCandidateLiftAbsorption :
    rhoCutoff ≤ seed.nestedCandidateLiftAbsorption.delta₀
  rhoCutoff_le_sourceWitnessCandidateLiftAbsorption :
    rhoCutoff ≤ seed.sourceWitnessCandidateLiftAbsorption.delta₀
  rhoCutoff_le_internalFourthBoundaryAbsorption :
    rhoCutoff ≤ seed.internalFourthBoundaryAbsorption.delta₀
  rhoCutoff_le_paperFirstCrossAbsorption :
    rhoCutoff ≤ seed.paperFirstCrossAbsorption.delta₀
  rhoCutoff_le_paperSecondCrossAbsorption :
    rhoCutoff ≤ seed.paperSecondCrossAbsorption.delta₀
  paperRobustSmallCutoff : ℝ
  paperRobustSmallCutoff_pos : 0 < paperRobustSmallCutoff
  rhoCutoff_le_paperRobustSmallCutoff :
    rhoCutoff ≤ paperRobustSmallCutoff
  paperRobustScale_small : ∀ rho : ℝ, 0 < rho → rho ≤ rhoCutoff →
    Real.rpow rho seed.paperAngularExponent ≤ 1 / 10000
  paperCordobaAxisCutoff : ℝ
  paperCordobaAxisCutoff_pos : 0 < paperCordobaAxisCutoff
  rhoCutoff_le_paperCordobaAxisCutoff :
    rhoCutoff ≤ paperCordobaAxisCutoff
  paperCordobaAxis : ∀ rho : ℝ, 0 < rho → rho ≤ rhoCutoff →
    4 * (6 * rho) ^ 2 ≤
      (3 / 4 : ℝ) *
        (Real.rpow rho (1 - seed.paperAngularExponent)) ^ 2

/-- Freeze the complete legacy cutoff together with all new paper-angular
thresholds before any tube family or shading is introduced. -/
theorem proposition63_four_call_paper_seed_cutoff
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss)
    (coarseCoefficient : NNReal) :
    Nonempty (Proposition63FourCallPaperSeedCutoffData
      seed coarseCoefficient) := by
  rcases proposition63_four_call_frozen_seed_cutoff seed with ⟨legacy⟩
  have coarseCoefficient_finite :
      proposition63FourCallPaperCoarseCoefficient coarseCoefficient ≠ ⊤ := by
    unfold proposition63FourCallPaperCoarseCoefficient
    finiteness
  rcases seed.paperCoarseAbsorption
      (proposition63FourCallPaperCoarseCoefficient coarseCoefficient)
      coarseCoefficient_finite with
    ⟨coarseAbsorption⟩
  have terminalLinearBudget :
      seed.schedule.first.normalizationLoss +
          seed.sourceWitnessCandidateLoss +
          2 * seed.schedule.firstOutputLoss <
        seed.goodCellCandidateLoss := by
    rw [seed.sourceWitnessCandidateLoss_eq,
      seed.goodCellCandidateLoss_eq]
    have firstNormalizationLt :
        seed.schedule.first.normalizationLoss <
          seed.schedule.firstOutputLoss :=
      seed.schedule.first.normalizationLoss_lt_output
    have firstOutputEq :
        seed.schedule.firstOutputLoss =
          seed.schedule.second.sourceLoss / 16 :=
      seed.schedule.firstOutputLoss_eq
    have secondSourceLtThird :
        seed.schedule.second.sourceLoss <
          seed.schedule.third.sourceLoss / 32 := by
      calc
        seed.schedule.second.sourceLoss ≤
            seed.schedule.second.normalizationLoss / 2 :=
          seed.schedule.second.sourceLoss_le_half
        _ < seed.schedule.secondOutputLoss / 2 := by
          linarith [seed.schedule.second.normalizationLoss_lt_output]
        _ = seed.schedule.third.sourceLoss / 32 := by
          rw [seed.schedule.secondOutputLoss_eq]
          ring
    have thirdSourceLtFourth :
        seed.schedule.third.sourceLoss <
          seed.schedule.fourth.sourceLoss / 32 := by
      calc
        seed.schedule.third.sourceLoss ≤
            seed.schedule.third.normalizationLoss / 2 :=
          seed.schedule.third.sourceLoss_le_half
        _ < seed.schedule.thirdOutputLoss / 2 := by
          linarith [seed.schedule.third.normalizationLoss_lt_output]
        _ = seed.schedule.fourth.sourceLoss / 32 := by
          rw [seed.schedule.thirdOutputLoss_eq]
          ring
    have fourthSourceLtOutput :
        seed.schedule.fourth.sourceLoss < outputLoss / 2 := by
      exact seed.schedule.fourth.sourceLoss_le_half.trans_lt <|
        (div_lt_div_of_pos_right
          seed.schedule.fourth.normalizationLoss_lt_output (by norm_num))
    have outputPos : 0 < outputLoss := by
      linarith only [seed.schedule.fourth.sourceLoss_pos,
        fourthSourceLtOutput]
    have firstOutputTiny :
        48 * seed.schedule.firstOutputLoss < outputLoss := by
      calc
        48 * seed.schedule.firstOutputLoss =
            3 * seed.schedule.second.sourceLoss := by
          rw [firstOutputEq]
          ring
        _ < 3 * (seed.schedule.third.sourceLoss / 32) := by gcongr
        _ < 3 * ((seed.schedule.fourth.sourceLoss / 32) / 32) := by gcongr
        _ < 3 * ((outputLoss / 2) / 32 / 32) := by gcongr
        _ < outputLoss := by linarith only [outputPos]
    linarith only [firstNormalizationLt, firstOutputTiny]
  have terminalStickyNonnegative :
      0 ≤ seed.schedule.firstOutputLoss :=
    seed.schedule.firstOutputLoss_pos.le
  have terminalCoarsePowerNonnegative :
      0 ≤ seed.sourceWitnessCandidateLoss +
        2 * seed.schedule.firstOutputLoss := by
    have sourceWitnessPos : 0 < seed.sourceWitnessCandidateLoss := by
      rw [seed.sourceWitnessCandidateLoss_eq]
      have outputPos : 0 < outputLoss :=
        seed.schedule.firstOutputLoss_pos.trans <|
          seed.schedule.firstOutputLoss_lt_secondSource.trans_le
            seed.sourceWitnessLoss_le_output
      positivity
    positivity
  rcases proposition63_paper_terminal_pullback_absorption_of_linear_budget
      seed.schedule.first.normalizationLoss seed.schedule.firstOutputLoss
      seed.sourceWitnessCandidateLoss seed.goodCellCandidateLoss
      terminalStickyNonnegative terminalCoarsePowerNonnegative
      terminalLinearBudget with
    ⟨terminalAbsorption⟩
  rcases pure_wz2_exists_delta₀_rpow_le
      (threshold := (1 / 10000 : ℝ))
      (s := seed.paperAngularExponent) (by norm_num)
      seed.paperAngularExponent_pos with
    ⟨paperRobustSmallCutoff, hPaperRobustPos, _hPaperRobustOne,
      hPaperRobust⟩
  have hPaperAngularOne : seed.paperAngularExponent < 1 := by
    have hSum := seed.paper_epsilon_sum_lt_one
    linarith [seed.epsilon₁_pos]
  rcases cordoba_axis_condition_exists_of_angular_exponent
      seed.paperAngularExponent_pos hPaperAngularOne with
    ⟨paperCordobaAxisCutoff, hPaperAxisPos, _hPaperAxisOne, hPaperAxis⟩
  let paperCutoff : ℝ :=
    min coarseAbsorption.delta₀ <|
    min terminalAbsorption.delta₀ <|
    min seed.ancestorDensityLiftAbsorption.delta₀ <|
    min seed.ancestorReentryAbsorption.delta₀ <|
    min seed.nestedCandidateLiftAbsorption.delta₀ <|
    min seed.sourceWitnessCandidateLiftAbsorption.delta₀ <|
    min seed.internalFourthBoundaryAbsorption.delta₀ <|
    min seed.paperFirstCrossAbsorption.delta₀ <|
    min seed.paperSecondCrossAbsorption.delta₀ <|
      min paperRobustSmallCutoff paperCordobaAxisCutoff
  let rhoCutoff : ℝ := min legacy.rhoCutoff paperCutoff
  have hPaperCutoffPos : 0 < paperCutoff := by
    dsimp only [paperCutoff]
    exact lt_min coarseAbsorption.delta₀_pos <|
      lt_min terminalAbsorption.delta₀_pos <|
      lt_min seed.ancestorDensityLiftAbsorption.delta₀_pos <|
      lt_min seed.ancestorReentryAbsorption.delta₀_pos <|
      lt_min seed.nestedCandidateLiftAbsorption.delta₀_pos <|
      lt_min seed.sourceWitnessCandidateLiftAbsorption.delta₀_pos <|
      lt_min seed.internalFourthBoundaryAbsorption.delta₀_pos <|
      lt_min seed.paperFirstCrossAbsorption.delta₀_pos <|
      lt_min seed.paperSecondCrossAbsorption.delta₀_pos <|
        lt_min hPaperRobustPos hPaperAxisPos
  have hRhoCutoffPos : 0 < rhoCutoff := by
    dsimp only [rhoCutoff]
    exact lt_min legacy.rhoCutoff_pos hPaperCutoffPos
  have hRhoLeLegacy : rhoCutoff ≤ legacy.rhoCutoff := by
    exact min_le_left _ _
  have hRhoLePaper : rhoCutoff ≤ paperCutoff := by
    exact min_le_right _ _
  refine ⟨{
    legacy := legacy
    coarseAbsorption := coarseAbsorption
    terminalAbsorption := terminalAbsorption
    rhoCutoff := rhoCutoff
    rhoCutoff_pos := hRhoCutoffPos
    rhoCutoff_le_one := hRhoLeLegacy.trans legacy.rhoCutoff_le_one
    rhoCutoff_le_legacy := hRhoLeLegacy
    rhoCutoff_le_coarseAbsorption :=
      hRhoLePaper.trans (by dsimp only [paperCutoff]; simp)
    rhoCutoff_le_terminalAbsorption :=
      hRhoLePaper.trans (by dsimp only [paperCutoff]; simp)
    rhoCutoff_le_ancestorDensityLiftAbsorption :=
      hRhoLePaper.trans (by dsimp only [paperCutoff]; simp)
    rhoCutoff_le_ancestorReentryAbsorption :=
      hRhoLePaper.trans (by dsimp only [paperCutoff]; simp)
    rhoCutoff_le_nestedCandidateLiftAbsorption :=
      hRhoLePaper.trans (by dsimp only [paperCutoff]; simp)
    rhoCutoff_le_sourceWitnessCandidateLiftAbsorption :=
      hRhoLePaper.trans (by dsimp only [paperCutoff]; simp)
    rhoCutoff_le_internalFourthBoundaryAbsorption :=
      hRhoLePaper.trans (by dsimp only [paperCutoff]; simp)
    rhoCutoff_le_paperFirstCrossAbsorption :=
      hRhoLePaper.trans (by dsimp only [paperCutoff]; simp)
    rhoCutoff_le_paperSecondCrossAbsorption :=
      hRhoLePaper.trans (by dsimp only [paperCutoff]; simp)
    paperRobustSmallCutoff := paperRobustSmallCutoff
    paperRobustSmallCutoff_pos := hPaperRobustPos
    rhoCutoff_le_paperRobustSmallCutoff :=
      hRhoLePaper.trans (by dsimp only [paperCutoff]; simp)
    paperRobustScale_small := by
      intro rho hRhoPos hRhoCutoff
      exact hPaperRobust rho hRhoPos <| hRhoCutoff.trans <|
        hRhoLePaper.trans (by dsimp only [paperCutoff]; simp)
    paperCordobaAxisCutoff := paperCordobaAxisCutoff
    paperCordobaAxisCutoff_pos := hPaperAxisPos
    rhoCutoff_le_paperCordobaAxisCutoff :=
      hRhoLePaper.trans (by dsimp only [paperCutoff]; simp)
    paperCordobaAxis := by
      intro rho hRhoPos hRhoCutoff
      exact hPaperAxis rho hRhoPos <| hRhoCutoff.trans <|
        hRhoLePaper.trans (by dsimp only [paperCutoff]; simp)
  }⟩

/-- Reuse a coefficient-independent paper seed base with a new coarse
absorption.  The returned cutoff is the minimum of the frozen base cutoff and
the supplied coefficient-aware cutoff. -/
def Proposition63FourCallPaperSeedCutoffData.withCoarseAbsorption
    {sigma outputLoss discreteLoss : ℝ}
    {seed : Proposition63FourCallInnerLossSeed sigma outputLoss discreteLoss}
    (base : Proposition63FourCallPaperSeedCutoffData seed 1)
    (coarseCoefficient : NNReal)
    (coarseAbsorption : Proposition63FourCallPaperCoarseAbsorptionData
      (proposition63FourCallPaperCoarseCoefficient coarseCoefficient)
      seed.schedule.fourth.normalizationLoss seed.fourthKernel.internalLoss
      seed.epsilon₁ seed.paperAngularExponent seed.floorLoss
      seed.paperCandidateLoss seed.finalLoss) :
    Proposition63FourCallPaperSeedCutoffData seed coarseCoefficient where
  legacy := base.legacy
  coarseAbsorption := coarseAbsorption
  terminalAbsorption := base.terminalAbsorption
  rhoCutoff := min base.rhoCutoff coarseAbsorption.delta₀
  rhoCutoff_pos := lt_min base.rhoCutoff_pos coarseAbsorption.delta₀_pos
  rhoCutoff_le_one := (min_le_left _ _).trans base.rhoCutoff_le_one
  rhoCutoff_le_legacy :=
    (min_le_left _ _).trans base.rhoCutoff_le_legacy
  rhoCutoff_le_coarseAbsorption := min_le_right _ _
  rhoCutoff_le_terminalAbsorption :=
    (min_le_left _ _).trans base.rhoCutoff_le_terminalAbsorption
  rhoCutoff_le_ancestorDensityLiftAbsorption :=
    (min_le_left _ _).trans base.rhoCutoff_le_ancestorDensityLiftAbsorption
  rhoCutoff_le_ancestorReentryAbsorption :=
    (min_le_left _ _).trans base.rhoCutoff_le_ancestorReentryAbsorption
  rhoCutoff_le_nestedCandidateLiftAbsorption :=
    (min_le_left _ _).trans base.rhoCutoff_le_nestedCandidateLiftAbsorption
  rhoCutoff_le_sourceWitnessCandidateLiftAbsorption :=
    (min_le_left _ _).trans
      base.rhoCutoff_le_sourceWitnessCandidateLiftAbsorption
  rhoCutoff_le_internalFourthBoundaryAbsorption :=
    (min_le_left _ _).trans base.rhoCutoff_le_internalFourthBoundaryAbsorption
  rhoCutoff_le_paperFirstCrossAbsorption :=
    (min_le_left _ _).trans base.rhoCutoff_le_paperFirstCrossAbsorption
  rhoCutoff_le_paperSecondCrossAbsorption :=
    (min_le_left _ _).trans base.rhoCutoff_le_paperSecondCrossAbsorption
  paperRobustSmallCutoff := base.paperRobustSmallCutoff
  paperRobustSmallCutoff_pos := base.paperRobustSmallCutoff_pos
  rhoCutoff_le_paperRobustSmallCutoff :=
    (min_le_left _ _).trans base.rhoCutoff_le_paperRobustSmallCutoff
  paperRobustScale_small := by
    intro rho rho_pos rho_le
    exact base.paperRobustScale_small rho rho_pos
      (rho_le.trans (min_le_left _ _))
  paperCordobaAxisCutoff := base.paperCordobaAxisCutoff
  paperCordobaAxisCutoff_pos := base.paperCordobaAxisCutoff_pos
  rhoCutoff_le_paperCordobaAxisCutoff :=
    (min_le_left _ _).trans base.rhoCutoff_le_paperCordobaAxisCutoff
  paperCordobaAxis := by
    intro rho rho_pos rho_le
    exact base.paperCordobaAxis rho rho_pos
      (rho_le.trans (min_le_left _ _))

/-- Canonical coefficient-independent base used by the outer M9 envelope. -/
noncomputable def proposition63FourCallPaperSeedBaseCutoff
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed sigma outputLoss discreteLoss) :
    Proposition63FourCallPaperSeedCutoffData seed 1 :=
  Classical.choice (proposition63_four_call_paper_seed_cutoff seed 1)

end Kakeya.Assouad.PureWZ2
