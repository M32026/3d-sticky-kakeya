import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPaperScalarBounds
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63PaperLineHitCandidate

/-!
# Coarse-scale restoration for the paper four-call tail

This file deliberately stops before the ancestry pullback.  It restores the
all-good-line `paperOuterCandidate` as an interval-local-grain state on the
coarse `rho` family itself.  Consequently the Lemma 4.3 loss below contains
only the intrinsic coarse mass ledger; neither the root cardinality nor the
fine pullback cost is charged to it.

The exact final and cover choices are runtime choices.  Their size is exposed
separately through the uniform estimate from `PaperScalarBounds`; that estimate
is not used as a fixed-`rho` substitute for a uniform delta cutoff.
-/

noncomputable section

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

namespace Proposition63NestedPointCoverData.FullGrainCells

/-- Restore the all-good paper candidate locally at the coarse scale.

The theorem is intentionally a coarse-family receipt.  Any later passage back
to the original fine family must be supplied by a separate ancestry theorem.
The final conjunct records the genuinely uniform bound for the exact natural
cover choice.
-/
theorem paperOuterCandidate_coarse_restore_of_exact_choices
    {rho sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss tauScale currentLoss outputLoss
      incidence epsilon₁ angular : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss rho}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant : ENNReal}
    {coefficient : NNReal}
    (finalChoice : Proposition63FourCallFinalConstantChoice rho sigma
      normalizationLoss sqrtStickyLoss (Real.sqrt rho) epsilon₁ angular
      incidence coefficient)
    (coverChoice : Proposition63FourCallCoverBudgetChoice
      (proposition63FourCallCoverRequirement coefficient
        finalChoice.finalConstant rho (Real.sqrt rho) sigma))
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := rho)
      (tauScale := tauScale) (sqrtScale := Real.sqrt rho)
      initialNormalized planeMap tauConstant
      (finalChoice.finalConstant *
        Kakeya.realRpowENN (Real.sqrt rho / rho) (1 - sigma)))
    {lineVolume : ℝ}
    (full : data.FullGrainCells lineVolume coverChoice.coverBudget)
    (rho_pos : 0 < rho) (rho_le_one : rho ≤ 1)
    (incidence_nonneg : 0 ≤ incidence) (incidence_le : incidence ≤ rho)
    (coefficient_one : 1 ≤ (coefficient : ℝ))
    (current_extremal : WZ2PaperCroppedIsExtremal sigma currentLoss
      initialNormalized.croppedFamily data.current)
    (current_cwa : WZ2PaperConvexWolffBound
      initialNormalized.croppedFamily
      (Kakeya.realRpowENN rho (-currentLoss)))
    (constant leftFactor rightFactor : ENNReal)
    (covering : PureWZ2IntervalCoveringAt
      (full.paperOuterCandidate rho_pos) planeMap rho
      (Real.toNNReal rho) (Real.toNNReal tauScale) constant)
    (left_bound : leftFactor ≤
      ((data.cells.cellMass / 2) /
        (2 * (coverChoice.coverBudget : ENNReal))) *
        (data.secondRetainedFactor *
          ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
          data.firstRetainedFactor))
    (right_bound :
      (data.reentry.regularized.regularizationLoss *
        data.prepared.preparationLoss) *
        (4 * (ENNReal.ofReal (4 * (2 * Real.sqrt rho) ^ 2) *
          ENNReal.ofReal (4 * rho))) ≤ rightFactor)
    (left_pos : 0 < leftFactor) (left_finite : leftFactor ≠ ⊤)
    (right_finite : rightFactor ≠ ⊤)
    (current_le_output : currentLoss ≤ outputLoss)
    (output_pos : 0 < outputLoss)
    (restore_power : proposition63Lemma43MassLoss leftFactor rightFactor *
      Kakeya.realRpowENN rho outputLoss ≤
        Kakeya.realRpowENN rho currentLoss) :
    ∃ restored : PureWZ2IntervalLocalGrainData
        (sigma := sigma) (outputLoss := outputLoss)
        (source := data.current) planeMap rho (Real.toNNReal rho)
        (Real.toNNReal tauScale) constant,
      restored.shading = full.paperOuterCandidate rho_pos ∧
      leftFactor * data.current.mass ≤ rightFactor * restored.shading.mass ∧
      (coverChoice.coverBudget : ENNReal) ≤
        (1605264998400 : ENNReal) * (coefficient : ENNReal) ^ 3 *
          Kakeya.realRpowENN rho
            (-(proposition63FourCallPaperFinalExponent sigma normalizationLoss
              sqrtStickyLoss epsilon₁ angular)) + 2 := by
  rcases full.paperOuterCandidate_intervalLocalGrain rho_pos rho_pos
      currentLoss current_extremal current_cwa constant covering leftFactor
      rightFactor left_bound right_bound left_pos left_finite right_finite
      current_le_output output_pos restore_power with
    ⟨restored, restored_eq⟩
  refine ⟨restored, restored_eq, ?_, ?_⟩
  · rw [restored_eq]
    calc
      leftFactor * data.current.mass ≤
          (((data.cells.cellMass / 2) /
              (2 * (coverChoice.coverBudget : ENNReal))) *
            (data.secondRetainedFactor *
              ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
              data.firstRetainedFactor)) * data.current.mass :=
        mul_le_mul_left left_bound _
      _ ≤ ((data.reentry.regularized.regularizationLoss *
              data.prepared.preparationLoss) *
            (4 * (ENNReal.ofReal (4 * (2 * Real.sqrt rho) ^ 2) *
              ENNReal.ofReal (4 * rho)))) *
          (full.paperOuterCandidate rho_pos).mass :=
        full.paperOuterCandidate_mass_ledger rho_pos rho_pos
      _ ≤ rightFactor * (full.paperOuterCandidate rho_pos).mass :=
        mul_le_mul_left right_bound _
  · exact proposition63_four_call_exact_cover_budget_upper rho_pos rho_le_one
      incidence_nonneg incidence_le coefficient_one finalChoice coverChoice

end Proposition63NestedPointCoverData.FullGrainCells

end Kakeya.Assouad.PureWZ2
