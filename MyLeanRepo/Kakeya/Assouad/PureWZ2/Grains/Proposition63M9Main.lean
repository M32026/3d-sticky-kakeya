import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9NestedPreGrainSource
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9FinalScaleCutoff

/-! # Proposition 6.3 M9: unconditional paper-ordered producer -/

noncomputable section
namespace Kakeya.Assouad

open PureWZ2

/-- The `outputLoss ≤ 1` branch of Proposition 6.3.  The construction uses
the repaired robust-kappa/q two-call middle, the whole-cell global grain, and
the power-scale mild-rescaling quotient tail. -/
theorem pure_wz2_strategy3_multiscale_main
    (_h_subunit : PureWZ2SubunitPackageStatement)
    (_h_extraction : PureWZ2CriticalExtractionStatement)
    (_h_sticky : PureWZ2PropStickyStatement)
    (sigma : ℝ)
    (hcrit : PureWZ2CriticalPackage sigma)
    (outputLoss delta₀ : ℝ)
    (hloss_pos : 0 < outputLoss)
    (houtputLoss_le_one : outputLoss ≤ 1)
    (hdelta₀_pos : 0 < delta₀) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ delta₀ ∧
      Nonempty (PureWZ2GrainConfiguration sigma outputLoss delta) := by
  rcases PureWZ2.proposition63_m9_nested_schedule hcrit hloss_pos with
    ⟨nested⟩
  let p := nested.outer.preGrainLoss
  have pPos : 0 < p := nested.outer.preGrain_pos
  have pOne : p < 1 := by
    exact nested.outer.preGrain_lt_sigma_quarter.trans <| by
      linarith [hcrit.sigma_lt_one]
  have tailSourceLossPos : 0 < 4 * p := by positivity
  rcases PureWZ2.proposition63_m9_robust_tail_schedule
      (4 * p) tailSourceLossPos (1 : NNReal) (1 : NNReal) with
    ⟨tailIndex⟩
  have tailArithmetic :=
    PureWZ2.proposition63_m9_production_power_tail_losses pPos
      nested.outer.eightyFour_preGrain_lt_output
  rcases PureWZ2.exists_proposition63_m9_power_source_and_robust_tail_cutoff
      (4 * p) p outputLoss (16 * p) tailIndex.levelCount
      tailSourceLossPos pPos.le pOne tailIndex.levelCount_loss (by ring)
      tailArithmetic.1 houtputLoss_le_one tailArithmetic.2.1 with
    ⟨tailCutoff, tailCutoffPos, _tailCutoffOne, runTail⟩
  rcases PureWZ2.exists_proposition63_m9_final_scale_cutoff pOne
      hdelta₀_pos with
    ⟨finalCutoff, finalCutoffPos, _finalCutoffOne, finalScaleLe⟩
  let sourceCutoff := min tailCutoff finalCutoff
  have sourceCutoffPos : 0 < sourceCutoff :=
    lt_min tailCutoffPos finalCutoffPos
  rcases PureWZ2.proposition63_m9_nested_preGrain_source hcrit nested
      sourceCutoffPos with ⟨source⟩
  have sourceLeTail : source.delta ≤ tailCutoff :=
    source.delta_le_cutoff.trans (min_le_left _ _)
  have sourceLeFinal : source.delta ≤ finalCutoff :=
    source.delta_le_cutoff.trans (min_le_right _ _)
  let tailExtremal := source.tailExtremal pPos
  let tailPreGrain := source.tailPreGrain pPos
  have commonScale : (source.tailLipschitz : ℝ) =
      PureWZ2.proposition63M9PowerScale source.delta p := by
    unfold PureWZ2.Proposition63M9NestedPreGrainSourceData.tailLipschitz
      PureWZ2.proposition63M9PowerScale
    exact Real.coe_toNNReal _
      (Real.rpow_nonneg source.delta_pos.le _)
  rcases runTail source.delta_pos sourceLeTail source.shading tailExtremal
      source.lineClass source.essentiallyDistinct source.midpoint_le_three
      tailPreGrain (by rw [commonScale]) (by rw [commonScale])
      hcrit.sigma_pos hcrit.sigma_lt_one with
    ⟨hscale, hscaleDeltaSmall, sourceData, sourceSchedule, certificates⟩
  have finalPositive : 0 <
      PureWZ2.proposition63M9PowerScale source.delta p * source.delta :=
    mul_pos (PureWZ2.proposition63M9PowerScale_pos source.delta_pos)
      source.delta_pos
  have finalLe :
      PureWZ2.proposition63M9PowerScale source.delta p * source.delta ≤
        delta₀ :=
    finalScaleLe source.delta_pos sourceLeFinal
  refine ⟨PureWZ2.proposition63M9PowerScale source.delta p * source.delta,
    finalPositive, finalLe, ?_⟩
  exact PureWZ2.proposition63_m9_robust_quotient_tail sourceData sourceSchedule
    (fun targetData => Classical.choice (certificates targetData))

end Kakeya.Assouad
end
