import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCarrierBlocks
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalMultiWindowAssembly

/-!
# Separation of source-horizontal outputs from distant source blocks

The final trapezoid core produced from one source block stays within a fixed
five-`sqrt rho` enlargement of that block.  Taking one residue class modulo
64 therefore gives more than the `sqrt (1280 rho)` separation required by
the public Pure one-scale output.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- The final scale is bounded by `36 * sqrt rho`. -/
theorem pureWZ2SourceHorizontalFinalScale_sqrt_le
    {rho : ℝ} (hrho : 0 < rho) :
    Real.sqrt (pureWZ2SourceHorizontalFinalScale rho) ≤
      36 * Real.sqrt rho := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · rw [pureWZ2SourceHorizontalFinalScale]
    have hrootSquare : (Real.sqrt rho) ^ 2 = rho :=
      Real.sq_sqrt hrho.le
    nlinarith

/-- Rich trapezoid cores coming from equally shifted source blocks at distance
at least 64 are separated at the final public one-scale parameter.  The common
shift is the phase offset of the balanced safe-window decomposition and
cancels from the separation estimate. -/
theorem pureWZ2SourceHorizontalShiftedBlockCores_separated
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {firstPipeline secondPipeline : PureWZ2SourceHorizontalPipelineData
      (normalEta := normalEta) twoScale}
    (firstRich : PureWZ2SourceHorizontalRichPipelineData
      (finalLoss := finalLoss) (theoremEta := theoremEta) firstPipeline)
    (secondRich : PureWZ2SourceHorizontalRichPipelineData
      (finalLoss := finalLoss) (theoremEta := theoremEta) secondPipeline)
    (shift : ℝ) (firstBlock secondBlock : ℤ)
    (hfirstLeft : firstPipeline.window.left =
      pureWZ2SourceCarrierBlockLeft rho firstBlock + shift)
    (hsecondLeft : secondPipeline.window.left =
      pureWZ2SourceCarrierBlockLeft rho secondBlock + shift)
    (hblocks : (64 : ℤ) ≤ |firstBlock - secondBlock|) :
    ∀ z ∈ firstRich.richTrapezoid.trapezoid.core,
      ∀ w ∈ secondRich.richTrapezoid.trapezoid.core,
        Real.sqrt (pureWZ2SourceHorizontalFinalScale rho) ≤ |z - w| := by
  have hrho : 0 < rho := firstPipeline.line.rho_pos
  let root := Real.sqrt rho
  have hroot : 0 < root := Real.sqrt_pos.mpr hrho
  have hscale := pureWZ2SourceHorizontalFinalScale_sqrt_le hrho
  intro z hz w hw
  have hzWindow := firstRich.richTrapezoid.core_height_window z hz
  have hwWindow := secondRich.richTrapezoid.core_height_window w hw
  rw [hfirstLeft] at hzWindow
  rw [hsecondLeft] at hwWindow
  simp only [pureWZ2SourceCarrierBlockLeft] at hzWindow hwWindow
  change Real.sqrt (pureWZ2SourceHorizontalFinalScale rho) ≤ |z - w|
  by_cases horder : firstBlock < secondBlock
  · have hdiffInt : (64 : ℤ) ≤ secondBlock - firstBlock := by
      rw [abs_of_nonpos (sub_nonpos.mpr horder.le)] at hblocks
      simpa using hblocks
    have hdiffReal : (64 : ℝ) ≤ (secondBlock : ℝ) - firstBlock := by
      exact_mod_cast hdiffInt
    have hwz : 59 * root ≤ w - z := by
      dsimp only [root] at hroot ⊢
      nlinarith [hzWindow.2, hwWindow.1]
    have hwzNonneg : 0 ≤ w - z :=
      (mul_pos (by norm_num) hroot).le.trans hwz
    rw [abs_sub_comm, abs_of_nonneg hwzNonneg]
    exact hscale.trans (by
      dsimp only [root] at hwz ⊢
      nlinarith [Real.sqrt_pos.mpr hrho])
  · have hreverse : secondBlock < firstBlock := by
      have hne : firstBlock ≠ secondBlock := by
        intro heq
        rw [heq, sub_self, abs_zero] at hblocks
        norm_num at hblocks
      omega
    have hdiffInt : (64 : ℤ) ≤ firstBlock - secondBlock := by
      rw [abs_of_nonneg (sub_nonneg.mpr hreverse.le)] at hblocks
      exact hblocks
    have hdiffReal : (64 : ℝ) ≤ (firstBlock : ℝ) - secondBlock := by
      exact_mod_cast hdiffInt
    have hzw : 59 * root ≤ z - w := by
      dsimp only [root] at hroot ⊢
      nlinarith [hzWindow.1, hwWindow.2]
    have hzwNonneg : 0 ≤ z - w :=
      (mul_pos (by norm_num) hroot).le.trans hzw
    rw [abs_of_nonneg hzwNonneg]
    exact hscale.trans (by
      dsimp only [root] at hzw ⊢
      nlinarith [Real.sqrt_pos.mpr hrho])

/-- Unshifted compatibility form of the block-core separation estimate. -/
theorem pureWZ2SourceHorizontalBlockCores_separated
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {firstPipeline secondPipeline : PureWZ2SourceHorizontalPipelineData
      (normalEta := normalEta) twoScale}
    (firstRich : PureWZ2SourceHorizontalRichPipelineData
      (finalLoss := finalLoss) (theoremEta := theoremEta) firstPipeline)
    (secondRich : PureWZ2SourceHorizontalRichPipelineData
      (finalLoss := finalLoss) (theoremEta := theoremEta) secondPipeline)
    (firstBlock secondBlock : ℤ)
    (hfirstLeft : firstPipeline.window.left =
      pureWZ2SourceCarrierBlockLeft rho firstBlock)
    (hsecondLeft : secondPipeline.window.left =
      pureWZ2SourceCarrierBlockLeft rho secondBlock)
    (hblocks : (64 : ℤ) ≤ |firstBlock - secondBlock|) :
    ∀ z ∈ firstRich.richTrapezoid.trapezoid.core,
      ∀ w ∈ secondRich.richTrapezoid.trapezoid.core,
        Real.sqrt (pureWZ2SourceHorizontalFinalScale rho) ≤ |z - w| := by
  apply pureWZ2SourceHorizontalShiftedBlockCores_separated
    firstRich secondRich 0 firstBlock secondBlock
  · simpa using hfirstLeft
  · simpa using hsecondLeft
  · exact hblocks

end Kakeya.Assouad
