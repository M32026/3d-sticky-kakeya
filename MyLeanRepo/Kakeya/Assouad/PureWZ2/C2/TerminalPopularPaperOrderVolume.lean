import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularExactTrapezoid
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularOuterHeightSchedule

/-!
# Conditional volume retention for one terminal paper-order chain

This file keeps the two losses separate.  `graphLoss` pays the outer-height,
parent-weight and fixed-line graph ledger, subject to an explicit lower bound
by the selected parent-weight floor.  `heightLoss` pays the graph-current
height popularity and Alternative-A refill.  No cancellation identifies the
parent-weight floor with the balanced coarse-cell mass.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

namespace PureWZ2TerminalPopularPaperOrderChain

/-- The source window reaches the outer-popular graph when its explicit finite
selection cost is bounded by the positive selected parent-weight floor.  This
is a conditional algebra lemma; producing the bound requires the missing
weighted fixed-slice receipt. -/
theorem graph_volume_lower
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    (chain : PureWZ2TerminalPopularPaperOrderChain
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) window)
    (graphLoss : ℝ)
    (hscalar :
      ((2 * chain.heightData.popular.bins : ℕ) : ENNReal) *
          (2 * (chain.weightClass.bins : ENNReal)) *
          pureWZ2TerminalPopularGraphVolumeCost delta sigma inputLoss *
          Kakeya.realRpowENN delta graphLoss ≤
        chain.weightClass.weightFloor) :
    Kakeya.realRpowENN delta graphLoss * volume window.shading.union ≤
      volume chain.prep.shadow.union := by
  have hwindowCarrier := chain.heightData.source_volume_retention
  have hwindowCarrier' : volume window.shading.union ≤
      ((2 * chain.heightData.popular.bins : ℕ) : ENNReal) *
        volume chain.carrier.shading.union := by
    calc
      volume window.shading.union ≤
          ((2 * chain.heightData.popular.bins : ℕ) : ENNReal) *
            chain.heightData.graphWindow.volumeSupply := hwindowCarrier
      _ = ((2 * chain.heightData.popular.bins : ℕ) : ENNReal) *
          volume chain.carrier.shading.union := by
        rw [chain.heightData.graphWindow_supply,
          ← chain.heightData.graphWindow_shading, ← chain.carrier.volume_eq]
  have hcarrierRestricted := chain.restricted.retained_volume
  have hrestrictedGraph := chain.prep.volume_supply_mul_floor_le
  have hrestrictedSupply : chain.restrictedPrepared.volumeSupply =
      volume chain.restricted.shading.union := by
    rw [chain.restrictedPrepared.volume_eq,
      pureWZ2PartialActiveCellShading_union]
  apply (ENNReal.mul_le_mul_iff_right
    chain.weightClass.weightFloor_pos.ne'
    chain.weightClass.weightFloor_ne_top).mp
  calc
    chain.weightClass.weightFloor *
        (Kakeya.realRpowENN delta graphLoss * volume window.shading.union) ≤
      chain.weightClass.weightFloor *
        (Kakeya.realRpowENN delta graphLoss *
          (((2 * chain.heightData.popular.bins : ℕ) : ENNReal) *
            volume chain.carrier.shading.union)) := by gcongr
    _ ≤ chain.weightClass.weightFloor *
        (Kakeya.realRpowENN delta graphLoss *
          (((2 * chain.heightData.popular.bins : ℕ) : ENNReal) *
            (2 * (chain.weightClass.bins : ENNReal) *
              volume chain.restricted.shading.union))) := by gcongr
    _ = (((2 * chain.heightData.popular.bins : ℕ) : ENNReal) *
          (2 * (chain.weightClass.bins : ENNReal)) *
          Kakeya.realRpowENN delta graphLoss) *
        (chain.restrictedPrepared.volumeSupply *
          chain.weightClass.weightFloor) := by
      rw [hrestrictedSupply]
      ring
    _ ≤ (((2 * chain.heightData.popular.bins : ℕ) : ENNReal) *
          (2 * (chain.weightClass.bins : ENNReal)) *
          Kakeya.realRpowENN delta graphLoss) *
        (pureWZ2TerminalPopularGraphVolumeCost delta sigma inputLoss *
          volume chain.prep.shadow.union) := by gcongr
    _ = (((2 * chain.heightData.popular.bins : ℕ) : ENNReal) *
          (2 * (chain.weightClass.bins : ENNReal)) *
          pureWZ2TerminalPopularGraphVolumeCost delta sigma inputLoss *
          Kakeya.realRpowENN delta graphLoss) *
        volume chain.prep.shadow.union := by ring
    _ ≤ chain.weightClass.weightFloor *
        volume chain.prep.shadow.union := by gcongr

/-- Once the dependent graph chain exists, refill its interior rich heights on
the original terminal source window.  This is the post-Lemma-23 one-window
shape needed by R4.1; the graph-volume premise needed to construct `chain` is
deliberately separate. -/
theorem window_volume_retention
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    (chain : PureWZ2TerminalPopularPaperOrderChain
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) window)
    (localMassLoss : ℝ)
    (hheightScalar :
      16 * Kakeya.realRpowENN delta localMassLoss *
          (chain.heightData.popular.bins : ENNReal) *
          (chain.heightData.popular.heightIndices.card : ENNReal) ≤
        pureWZ2TerminalPopularRichFloor delta outputLoss) :
    2 * Kakeya.realRpowENN delta localMassLoss *
        volume window.shading.union ≤
      volume chain.outerHeightLift.shading.union :=
  chain.outerHeightLift.source_window_volume_retention
    chain.richFloor_four hheightScalar

end PureWZ2TerminalPopularPaperOrderChain

end Kakeya.Assouad

end
