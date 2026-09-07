import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.BalancedSafeWindowBlocks
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalGoodBlocks

/-!
# Popular safe balanced source windows

This is the paper-order block selection for the source-slope Lemma-24 graph.
The carrier is first restricted to a safe phase of genuine balanced side-`rho`
cells.  Only then are the `sqrt rho` blocks tested against the local graph
threshold.  Thus every block supply is its exact cell count times the first
balanced cell mass; no extra source-volume averaging is paid.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

def pureWZ2GoodBalancedSafeBlocks
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (safe : PureWZ2BalancedSafeBlockFamilyData prepared)
    (volumeLoss : ℝ) : Finset {block // block ∈ safe.blocks} :=
  safe.blocks.attach.filter fun block =>
    pureWZ2SourceHorizontalBlockThreshold
        rho delta sigma inputLoss volumeLoss ≤
      MeasureTheory.volume (safe.blockWindow block).shading.union *
        twoScale.fine.balanced.cellMass

theorem pureWZ2GoodBalancedSafeBlock_budget
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    (hblock : block ∈
      pureWZ2GoodBalancedSafeBlocks safe volumeLoss) :
    pureWZ2SourceHorizontalBlockThreshold
        rho delta sigma inputLoss volumeLoss ≤
      MeasureTheory.volume (safe.blockWindow block).shading.union *
        twoScale.fine.balanced.cellMass :=
  (Finset.mem_filter.mp hblock).2

/-- Good safe windows retain half of the selected-phase volume supply. -/
theorem pureWZ2GoodBalancedSafeBlocks_half
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (safe : PureWZ2BalancedSafeBlockFamilyData prepared)
    (hsmall :
      2 * ((safe.blocks.card : ENNReal) *
          pureWZ2SourceHorizontalBlockThreshold
            rho delta sigma inputLoss volumeLoss) ≤
        ∑ block ∈ safe.blocks.attach,
          MeasureTheory.volume (safe.blockWindow block).shading.union *
            twoScale.fine.balanced.cellMass) :
    (∑ block ∈ safe.blocks.attach,
        MeasureTheory.volume (safe.blockWindow block).shading.union *
          twoScale.fine.balanced.cellMass) ≤
      2 * ∑ block ∈ pureWZ2GoodBalancedSafeBlocks safe volumeLoss,
        MeasureTheory.volume (safe.blockWindow block).shading.union *
          twoScale.fine.balanced.cellMass := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hthresholdTop : pureWZ2SourceHorizontalBlockThreshold
      rho delta sigma inputLoss volumeLoss ≠ ⊤ := by
    unfold pureWZ2SourceHorizontalBlockThreshold
    exact ENNReal.mul_ne_top (by simp [Kakeya.realRpowENN])
      (ENNReal.mul_ne_top
        (pureWZ2SourceHorizontalVolumeCost_ne_top _ _ _ _)
        (by rw [wz1PaperGridCube_volume_exact hrho]
            exact ENNReal.ofReal_ne_top))
  have hraw := finset_good_weighted_supply_retains_half
      safe.blocks.attach
      (fun block =>
        MeasureTheory.volume (safe.blockWindow block).shading.union)
      twoScale.fine.balanced.cellMass
      (pureWZ2SourceHorizontalBlockThreshold
        rho delta sigma inputLoss volumeLoss)
      hthresholdTop
      (by simpa using hsmall)
  refine hraw.trans ?_
  apply mul_le_mul_left'
  apply Finset.sum_le_sum_of_subset
  · intro block hblock
    simpa [pureWZ2GoodBalancedSafeBlocks] using hblock

theorem pureWZ2GoodBalancedSafeBlocks_nonempty
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (safe : PureWZ2BalancedSafeBlockFamilyData prepared)
    (hsmall :
      2 * ((safe.blocks.card : ENNReal) *
          pureWZ2SourceHorizontalBlockThreshold
            rho delta sigma inputLoss volumeLoss) ≤
        ∑ block ∈ safe.blocks.attach,
          MeasureTheory.volume (safe.blockWindow block).shading.union *
            twoScale.fine.balanced.cellMass) :
    (pureWZ2GoodBalancedSafeBlocks safe volumeLoss).Nonempty := by
  have hhalf := safe |> pureWZ2GoodBalancedSafeBlocks_half (hsmall := hsmall)
  have hleftPos : 0 <
      ∑ block ∈ safe.blocks.attach,
        MeasureTheory.volume (safe.blockWindow block).shading.union *
          twoScale.fine.balanced.cellMass := by
    rcases safe.blocks_nonempty with ⟨block, hblock⟩
    let first : {block // block ∈ safe.blocks} := ⟨block, hblock⟩
    have hvolume : 0 < MeasureTheory.volume
        (safe.blockWindow first).shading.union := by
      rw [(safe.blockWindow first).volume_eq]
      exact ENNReal.mul_pos
        (by exact_mod_cast
          (safe.blockWindow first).cells_nonempty.card_ne_zero)
        twoScale.coarse.balanced.cellMass_pos.ne'
    have hterm : 0 < MeasureTheory.volume
        (safe.blockWindow first).shading.union *
          twoScale.fine.balanced.cellMass :=
      ENNReal.mul_pos hvolume.ne'
        twoScale.fine.balanced.cellMass_pos.ne'
    have hsingle : MeasureTheory.volume
          (safe.blockWindow first).shading.union *
            twoScale.fine.balanced.cellMass ≤
        ∑ block ∈ safe.blocks.attach,
          MeasureTheory.volume (safe.blockWindow block).shading.union *
            twoScale.fine.balanced.cellMass := by
      exact Finset.single_le_sum
        (fun block _ => (show (0 : ENNReal) ≤
          MeasureTheory.volume (safe.blockWindow block).shading.union *
            twoScale.fine.balanced.cellMass from bot_le))
        (Finset.mem_attach safe.blocks first)
    exact hterm.trans_le hsingle
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hhalf
  simp only [Finset.sum_empty, mul_zero] at hhalf
  exact (not_le_of_gt hleftPos) hhalf

end Kakeya.Assouad
