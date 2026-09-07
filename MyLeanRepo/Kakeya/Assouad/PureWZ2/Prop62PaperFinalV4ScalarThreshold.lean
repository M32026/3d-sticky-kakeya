import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalLossHierarchy
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26DeltaBudget

/-!
# Proposition 6.2 V4 fixed-grid density threshold

This module isolates the first scalar socket in the nearby-source assembly.
After `sourceLoss < stableLoss` has been selected, one uniform source-scale
threshold pays the factor two lost by the fixed-grid boundary removal:

`delta ^ stableLoss ≤ (1 / 2) * delta ^ sourceLoss`.

The losses are fixed before the threshold, and the runtime scale is
quantified only afterwards.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open Kakeya.Assouad

/--
A uniform threshold for the density loss incurred by the fixed-grid
boundary removal.
-/
structure NearbyFixedGridDensityThresholdReceipt
    (sourceLoss stableLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one_hundred : delta₀ ≤ 1 / 100
  fixed_grid_density :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      Kakeya.realRpowENN delta stableLoss ≤
        (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta sourceLoss

/--
Choose the fixed-grid density threshold after the source and stable losses,
but before the runtime scale.
-/
theorem nearby_fixed_grid_density_threshold
    (sourceLoss stableLoss : ℝ)
    (source_stable : sourceLoss < stableLoss) :
    Nonempty
      (NearbyFixedGridDensityThresholdReceipt
        sourceLoss stableLoss) := by
  have gap_pos : 0 < stableLoss - sourceLoss := by
    linarith
  rcases
      exists_delta_rpow_le_single
        (stableLoss - sourceLoss) (1 / 2)
        gap_pos (by norm_num) (by norm_num)
    with ⟨powerDelta, powerDelta_pos, powerDelta_le_one, power_bound⟩
  let delta₀ : ℝ := min powerDelta (1 / 100)
  refine
    ⟨{
      delta₀ := delta₀
      delta₀_pos := by
        dsimp only [delta₀]
        positivity
      delta₀_le_one_hundred := by
        exact min_le_right _ _
      fixed_grid_density := ?_
    }⟩
  intro delta delta_pos delta_le
  have delta_le_power : delta ≤ powerDelta :=
    delta_le.trans (min_le_left _ _)
  have half_power :
      Real.rpow delta (stableLoss - sourceLoss) ≤ 1 / 2 :=
    power_bound delta delta_pos delta_le_power
  exact
    pure_wz2_pruning_power_bound delta_pos <| by
      nlinarith

namespace NearbyFixedGridDensityThresholdReceipt

/--
Shrink a fixed-grid density receipt to any further positive threshold.
This is the operation used when the final assembly takes the minimum of all
independently selected scalar and producer thresholds.
-/
noncomputable def shrink
    {sourceLoss stableLoss upper : ℝ}
    (receipt :
      NearbyFixedGridDensityThresholdReceipt
        sourceLoss stableLoss)
    (upper_pos : 0 < upper) :
    NearbyFixedGridDensityThresholdReceipt
      sourceLoss stableLoss where
  delta₀ := min receipt.delta₀ upper
  delta₀_pos := lt_min receipt.delta₀_pos upper_pos
  delta₀_le_one_hundred :=
    (min_le_left _ _).trans receipt.delta₀_le_one_hundred
  fixed_grid_density := by
    intro delta delta_pos delta_le
    exact
      receipt.fixed_grid_density delta_pos
        (delta_le.trans (min_le_left _ _))

end NearbyFixedGridDensityThresholdReceipt

/--
Specialization to the final loss hierarchy.  Its conclusion has exactly the
function type required by `NearbyScalarInputs.fixed_grid_density`.
-/
theorem WZ2PaperFinalLossHierarchyData.nearbyFixedGridDensityThreshold
    {outputLoss structuralLoss : ℝ}
    (hierarchy :
      WZ2PaperFinalLossHierarchyData
        outputLoss structuralLoss) :
    Nonempty
      (NearbyFixedGridDensityThresholdReceipt
        hierarchy.sourceLoss hierarchy.stableLoss) :=
  nearby_fixed_grid_density_threshold
    hierarchy.sourceLoss hierarchy.stableLoss
    hierarchy.source_stable

/--
Direct existential form for callers that assemble one common `delta₀`
without retaining the receipt record.
-/
theorem WZ2PaperFinalLossHierarchyData.exists_fixedGridDensityThreshold
    {outputLoss structuralLoss : ℝ}
    (hierarchy :
      WZ2PaperFinalLossHierarchyData
        outputLoss structuralLoss) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 / 100 ∧
      ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
        Kakeya.realRpowENN delta hierarchy.stableLoss ≤
          (1 / 2 : ENNReal) *
            Kakeya.realRpowENN delta hierarchy.sourceLoss := by
  rcases
      nearby_fixed_grid_density_threshold
        hierarchy.sourceLoss hierarchy.stableLoss
        hierarchy.source_stable
    with
    ⟨receipt⟩
  exact
    ⟨receipt.delta₀, receipt.delta₀_pos,
      receipt.delta₀_le_one_hundred,
      receipt.fixed_grid_density⟩

end Kakeya.Assouad.Prop62PaperAudit.V4

end
