import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalFiniteSliceGlobalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalScalarBudget
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperGlobalADVolumeUpper

/-!
# Global scalar budget for the direct half-offset terminal

The finite-slice argument supplies the literal raw global-AD constant below.
This module keeps its finite part separate from its source-scale loss, then
uses the already-proved source-to-target bridge.  In particular, the choice
of `epsilon`, `sourceLoss`, and `outputLoss` remains at the caller: the only
strict numerical requirement is
`sourceLoss < (1 - 2 * epsilon) * outputLoss`.

The slope envelope used by the finite-slice proof is
`lambda * (2 + 400 * rho⁻¹ ^ 2) + 2`; its `rho` provenance is the fixed
identity `rho = delta ^ epsilon / 50` in the common source assembly.
Since this envelope occurs in all three cover directions, its exact
source-power charge is `6 * epsilon`, in addition to the original terminal
source global-AD loss.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

namespace PureWZ2DirectCommonYSourceAssembly

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)

namespace TerminalGeometry

/-- The source loss forced by the literal finite-slice cover.  The existing
source global-AD contributes `technicalLoss`; the three-dimensional cover of
the `rho⁻²` slope envelope contributes exactly `6 * epsilon`, using
`rho = delta ^ epsilon / 50`. -/
def finiteSliceGlobalSourceLoss : ℝ :=
  commonSource.halfOffsetAssembly.technicalLoss + 6 * epsilon

/-- The strict loss gap required after accounting for the whole finite-slice
slope envelope.  This is deliberately an equality-level bookkeeping
definition rather than a choice of `epsilon` or `outputLoss`. -/
def FiniteSliceGlobalPowerGap (outputLoss : ℝ) : Prop :=
  finiteSliceGlobalSourceLoss commonSource <
    (1 - 2 * epsilon) * outputLoss

/-- The exact global-AD constant produced by the finite-slice transport.
The cover factor contains the slope envelope
`lambda * (2 + 400 * rho⁻¹ ^ 2) + 2`; all remaining factors are the fixed
finite height window and the source global-AD power. -/
def finiteSliceGlobalADRawConstant : ENNReal :=
  ((2 * (Nat.ceil
      (((finiteSliceAbsorbableSlopeBound commonSource + 3) *
          Real.sqrt 3) + 1) + 1) : ENNReal) ^ 3 *
    (((2 * finiteSliceHeightCellRadius + 1 : ℕ) : ENNReal) *
      Kakeya.realRpowENN delta
        (-commonSource.halfOffsetAssembly.technicalLoss)))

/-- A runtime-independent coefficient for the finite-slice global-AD cover.
The factor `50 ^ 6` is exactly the cost of substituting
`rho = delta ^ epsilon / 50` into the third power of `rho⁻²`. -/
def finiteSliceGlobalFiniteConstant : ENNReal :=
  ENNReal.ofReal ((2 *
      (((402 * pureWZ2DirectHalfOffsetTerminalLambda + 5) *
        Real.sqrt 3) + 3)) ^ 3 * 50 ^ 6) *
    ((2 * finiteSliceHeightCellRadius + 1 : ℕ) : ENNReal)

theorem finiteSliceGlobalFiniteConstant_ne_top :
    finiteSliceGlobalFiniteConstant ≠ ⊤ := by
  unfold finiteSliceGlobalFiniteConstant
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top

theorem cubicalShading_global_ad_finiteSlice_raw
    (terminal : commonSource.TerminalGeometry)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (safePublicSlope commonSource terminal z))
          (horizontalSlice terminal.cubicalShading.union z))
        terminal.targetDelta (1 - sigma)
        (finiteSliceGlobalADRawConstant commonSource) := by
  intro z hz
  simpa [finiteSliceGlobalADRawConstant] using
    (cubicalShading_global_ad_finiteSlice commonSource terminal
      hsigma hsigmaOne z hz)

/-- Turn an explicit source-scale receipt for the literal finite-slice raw
constant into global AD for the actual terminal cubical shading. -/
private theorem cubicalShading_global_ad_of_raw_scalar_budget
    (terminal : commonSource.TerminalGeometry)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (outputLoss : ℝ)
    (htargetOne : 1 ≤ Kakeya.realRpowENN terminal.targetDelta (-outputLoss))
    (htargetTop : Kakeya.realRpowENN terminal.targetDelta (-outputLoss) ≠ ⊤)
    (hraw : finiteSliceGlobalADRawConstant commonSource ≤
      Kakeya.realRpowENN terminal.targetDelta (-outputLoss)) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (safePublicSlope commonSource terminal z))
          (horizontalSlice terminal.cubicalShading.union z))
        terminal.targetDelta (1 - sigma)
        (Kakeya.realRpowENN terminal.targetDelta (-outputLoss)) := by
  intro z hz
  exact (cubicalShading_global_ad_finiteSlice commonSource terminal
    hsigma hsigmaOne z hz).weaken_constant hraw htargetOne htargetTop

/-- Pre-runtime absorption of a fixed finite source coefficient.  The raw
receipt is deliberately an argument: proving it is where the substitution
`rho = delta ^ epsilon / 50` records the slope-envelope loss.  Once it has
been established, no runtime parameter occurs in the threshold. -/
theorem exists_delta_for_cubicalShading_global_ad_scalar_budget
    (sourceLoss outputLoss : ℝ)
    (globalFiniteConstant : ENNReal)
    (hglobalFinite : globalFiniteConstant ≠ ⊤)
    (hepsilon : 0 < epsilon)
    (houtputLoss : 0 ≤ outputLoss)
    (hgap : sourceLoss < (1 - 2 * epsilon) * outputLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {sigma delta : ℝ}
        (commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta),
        0 < delta → delta ≤ delta₀ →
        globalFiniteConstant * Kakeya.realRpowENN delta (-sourceLoss) ≤
          Kakeya.realRpowENN commonSource.halfOffsetLineClassTargetDelta
            (-outputLoss) := by
  exact exists_delta_for_halfOffsetLineClass_constant_source_negative_le_target_negative
    epsilon sourceLoss outputLoss globalFiniteConstant hglobalFinite
    hepsilon houtputLoss hgap

/-- The public pre-runtime source-to-target threshold with the actual
finite-slice exponent charge.  Its fixed coefficient is independent of the
runtime common source; the only strict condition is
`technicalLoss + 6 * epsilon < (1 - 2 * epsilon) * outputLoss`. -/
theorem exists_delta_for_finiteSliceGlobal_source_to_target
    (technicalLoss outputLoss : ℝ)
    (globalFiniteConstant : ENNReal)
    (hglobalFinite : globalFiniteConstant ≠ ⊤)
    (hepsilon : 0 < epsilon)
    (houtputLoss : 0 ≤ outputLoss)
    (hgap : technicalLoss + 6 * epsilon <
      (1 - 2 * epsilon) * outputLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {sigma delta : ℝ}
        (commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta),
        commonSource.halfOffsetAssembly.technicalLoss = technicalLoss →
        0 < delta → delta ≤ delta₀ →
        globalFiniteConstant *
            Kakeya.realRpowENN delta
              (-(finiteSliceGlobalSourceLoss commonSource)) ≤
          Kakeya.realRpowENN commonSource.halfOffsetLineClassTargetDelta
            (-outputLoss) := by
  rcases exists_delta_for_cubicalShading_global_ad_scalar_budget
      (epsilon := epsilon) (technicalLoss + 6 * epsilon) outputLoss
      globalFiniteConstant hglobalFinite hepsilon houtputLoss hgap with
    ⟨delta₀, hdelta₀, hdelta₀One, hthreshold⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro logExponent sigma delta commonSource htechnical hdelta hdeltaSmall
  simpa [finiteSliceGlobalSourceLoss, htechnical] using
    hthreshold commonSource hdelta hdeltaSmall

/-- Final scalar absorption interface for the literal terminal global AD.
The strict gap displayed here is minimal for the existing source-to-target
bridge: `sourceLoss < (1 - 2 * epsilon) * outputLoss`. -/
private theorem cubicalShading_global_ad_of_source_scalar_receipt
    (terminal : commonSource.TerminalGeometry)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (outputLoss : ℝ)
    (htargetOne : 1 ≤ Kakeya.realRpowENN terminal.targetDelta (-outputLoss))
    (htargetTop : Kakeya.realRpowENN terminal.targetDelta (-outputLoss) ≠ ⊤)
    (hraw : finiteSliceGlobalADRawConstant commonSource ≤
      Kakeya.realRpowENN terminal.targetDelta (-outputLoss)) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (safePublicSlope commonSource terminal z))
          (horizontalSlice terminal.cubicalShading.union z))
        terminal.targetDelta (1 - sigma)
        (Kakeya.realRpowENN terminal.targetDelta (-outputLoss)) :=
  cubicalShading_global_ad_of_raw_scalar_budget commonSource terminal
    hsigma hsigmaOne outputLoss htargetOne htargetTop hraw

/-- Combine the explicit raw source-scale receipt with the pre-runtime
threshold.  `globalFiniteConstant` is fixed before runtime; the source loss
must include the `rho⁻²` contribution of the finite-slice slope envelope
(three cover dimensions hence a `6 * epsilon` contribution after
`rho = delta ^ epsilon / 50`). -/
private theorem cubicalShading_global_ad_after_source_scalar_absorption
    (terminal : commonSource.TerminalGeometry)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (sourceLoss outputLoss : ℝ)
    (globalFiniteConstant : ENNReal)
    (hrawSource : finiteSliceGlobalADRawConstant commonSource ≤
      globalFiniteConstant * Kakeya.realRpowENN delta (-sourceLoss))
    (hsourceTarget : globalFiniteConstant *
        Kakeya.realRpowENN delta (-sourceLoss) ≤
      Kakeya.realRpowENN terminal.targetDelta (-outputLoss))
    (htargetOne : 1 ≤ Kakeya.realRpowENN terminal.targetDelta (-outputLoss))
    (htargetTop : Kakeya.realRpowENN terminal.targetDelta (-outputLoss) ≠ ⊤) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (safePublicSlope commonSource terminal z))
          (horizontalSlice terminal.cubicalShading.union z))
        terminal.targetDelta (1 - sigma)
        (Kakeya.realRpowENN terminal.targetDelta (-outputLoss)) := by
  apply cubicalShading_global_ad_of_raw_scalar_budget commonSource terminal
    hsigma hsigmaOne outputLoss htargetOne htargetTop
  exact hrawSource.trans hsourceTarget

/-- The terminal volume upper bound after a separately checked final scalar
receipt.  This is the direct call-site wrapper for
`pureWZ2_paperShading_volume_le_of_global_ad`; it keeps the extra volume
factor visible rather than silently charging it to the AD constant. -/
private theorem cubicalShading_volume_upper_of_global_scalar_budget
    (terminal : commonSource.TerminalGeometry)
    (outputLoss : ℝ)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (slopeBound : ℝ) (hslopeBound : 0 ≤ slopeBound)
    (hslope : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |safePublicSlope commonSource terminal z| ≤ slopeBound)
    (htargetTop : Kakeya.realRpowENN terminal.targetDelta (-outputLoss) ≠ ⊤)
    (hglobal : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (safePublicSlope commonSource terminal z))
          (horizontalSlice terminal.cubicalShading.union z))
        terminal.targetDelta (1 - sigma)
        (Kakeya.realRpowENN terminal.targetDelta (-outputLoss)))
    (hfinal : 8 *
        (Kakeya.realRpowENN terminal.targetDelta (-outputLoss) *
          Kakeya.realRpowENN ((2 * (1 + slopeBound)) / terminal.targetDelta)
            (1 - sigma) * ENNReal.ofReal (2 * terminal.targetDelta)) ≤
      Kakeya.realRpowENN terminal.targetDelta (sigma - outputLoss)) :
    volume terminal.cubicalShading.union ≤
      Kakeya.realRpowENN terminal.targetDelta (sigma - outputLoss) := by
  apply (pureWZ2_paperShading_volume_le_of_global_ad
    terminal.cubicalShading (safePublicSlope commonSource terminal)
    commonSource.halfOffsetLineClassTargetDelta_pos
    (commonSource.halfOffsetLineClassTargetDelta_small.le.trans (by norm_num))
    hsigma hsigmaOne htargetTop hslopeBound hslope hglobal).trans
  exact hfinal

end TerminalGeometry

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad
