import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleExactPreparedGraph
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.BoundedGridLogCost

/-!
# Uniform finite-grid cost for the exact terminal graph

The exact terminal construction records its height-bin and residue-cell
losses before any ready graph is chosen.  Both ranges lie in the same
bounded `delta` grid, so their quadratic logarithmic cost is absorbed by an
arbitrary positive power at one source-scale threshold.
-/

noncomputable section

namespace Kakeya.Assouad

theorem pureWZ2_terminalExact_extraCost_schedule
    {extraLoss : ℝ} (hextraLoss : 0 < extraLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {sigma inputLoss delta stickyLoss eta : ℝ}
        {logExponent : ℕ}
        {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
        {terminal : PureWZ2TerminalScaleStickyData
          source stickyLoss logExponent}
        {terminalSource : PureWZ2TerminalPreparedSource source terminal}
        {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
        {window : PureWZ2TerminalWindow prepared}
        {line : PureWZ2HorizontalFixedBinCore
          window.windowed source.globalGrains.slope}
        {parents : PureWZ2TerminalFixedBinParentData line}
        {selection : PureWZ2TerminalBinParentYSelection parents}
        {residue : PureWZ2TerminalBinParentYResidueData selection}
        {retained : PureWZ2TerminalBinRetainedShadingData residue}
        {sources : PureWZ2TerminalBinSourceFamily retained}
        {band : PureWZ2TerminalBinFixedBandSelection sources}
        {phase : PureWZ2TerminalBinHeightPhaseSelection band}
        {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
        {prep : PureWZ2TerminalBinExactGraphPreparation anchored}
        {graphParents : PureWZ2TerminalExactGraphParentData prep}
        {localCells : PureWZ2TerminalExactLocalCellData
          (eta := eta) graphParents}
        (preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells),
        0 < delta → delta ≤ delta₀ →
          (preparedGraph.graph.residue.extraCost : ℝ) ≤
            Real.rpow delta (-extraLoss) := by
  rcases pureWZ2_boundedGrid_logCost_schedule hextraLoss with
    ⟨delta₀, hdelta₀, hdelta₀One, hschedule⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro sigma inputLoss delta stickyLoss eta logExponent source terminal
    terminalSource prepared window line parents selection residue retained
    sources band phase anchored prep graphParents localCells preparedGraph
    hdelta hdeltaSmall
  have hdeltaOne : delta ≤ 1 := hdeltaSmall.trans hdelta₀One
  have hcellsSubset : prep.windowed.global.cells ⊆
      wz1Lemma23BoundedCells delta hdelta := by
    classical
    exact prep.windowed.global.cells_active.trans
      (Finset.filter_subset _ _)
  have hcard : prep.windowed.global.cells.card ≤
      (wz1Lemma23BoundedCells delta hdelta).card :=
    Finset.card_le_card hcellsSubset
  have hrawCard : preparedGraph.rawResidue.cells.card ≤
      (wz1Lemma23BoundedCells delta hdelta).card :=
    (Finset.card_le_card preparedGraph.rawResidue.cells_subset).trans hcard
  have hrawNonempty : preparedGraph.rawResidue.cells.Nonempty := by
    rw [preparedGraph.raw_residue_eq]
    exact preparedGraph.popularSource.cells_nonempty
  have hboundedNonempty :
      (wz1Lemma23BoundedCells delta hdelta).Nonempty :=
    hrawNonempty.mono
      (preparedGraph.rawResidue.cells_subset.trans hcellsSubset)
  have hrawLogNat : Nat.log 2 preparedGraph.rawResidue.cells.card + 1 ≤
      Nat.log 2 (wz1Lemma23BoundedCells delta hdelta).card + 1 :=
    Nat.add_le_add_right (Nat.log_mono_right hrawCard) 1
  have hheightCard :
      (wz1Lemma23BoundedHeightIndices delta hdelta).card ≤
        (wz1Lemma23BoundedCells delta hdelta).card :=
    Finset.card_image_le
  have hbinsArg :
      2 * (wz1Lemma23BoundedHeightIndices delta hdelta).card ≤
        4 * (wz1Lemma23BoundedCells delta hdelta).card := by
    have hcellsPos : 0 < (wz1Lemma23BoundedCells delta hdelta).card :=
      hboundedNonempty.card_pos
    omega
  have hbinsLog :
      Nat.log 2 (2 * (wz1Lemma23BoundedHeightIndices delta hdelta).card) ≤
        Nat.log 2 (4 * (wz1Lemma23BoundedCells delta hdelta).card) :=
    Nat.log_mono_right hbinsArg
  have hcellsNe : (wz1Lemma23BoundedCells delta hdelta).card ≠ 0 :=
    hboundedNonempty.card_ne_zero
  have hfourEq :
      4 * (wz1Lemma23BoundedCells delta hdelta).card =
        (wz1Lemma23BoundedCells delta hdelta).card * 2 * 2 := by
    ring
  have hbinsNat : preparedGraph.heightPopular.bins ≤
      Nat.log 2 (wz1Lemma23BoundedCells delta hdelta).card + 3 := by
    rw [preparedGraph.heightPopular.bins_eq]
    calc
      Nat.log 2
          (2 * (wz1Lemma23BoundedHeightIndices delta hdelta).card) + 1 ≤
          Nat.log 2
            (4 * (wz1Lemma23BoundedCells delta hdelta).card) + 1 := by
        omega
      _ = Nat.log 2 (wz1Lemma23BoundedCells delta hdelta).card + 3 := by
        rw [hfourEq]
        calc
          Nat.log 2
                ((wz1Lemma23BoundedCells delta hdelta).card * 2 * 2) + 1 =
              Nat.log 2
                ((wz1Lemma23BoundedCells delta hdelta).card * 2) + 1 + 1 := by
            rw [Nat.log_mul_base (by omega)
              (Nat.mul_ne_zero hcellsNe (by omega))]
          _ = Nat.log 2 (wz1Lemma23BoundedCells delta hdelta).card +
                1 + 1 + 1 := by
            rw [Nat.log_mul_base (by omega) hcellsNe]
          _ = _ := by omega
  let L : ℝ := Real.log (1 / delta) + 1
  have hlog := wz1Lemma23BoundedCells_log_bound hdelta hdeltaOne
  have hrawLogReal :
      (Nat.log 2 preparedGraph.rawResidue.cells.card + 1 : ℝ) ≤
        20 * L := by
    have hcast :
        (Nat.log 2 preparedGraph.rawResidue.cells.card + 1 : ℝ) ≤
          (Nat.log 2 (wz1Lemma23BoundedCells delta hdelta).card + 1 : ℕ) := by
      exact_mod_cast hrawLogNat
    exact hcast.trans (by simpa [L] using hlog)
  have hLone : 1 ≤ L := by
    dsimp only [L]
    have hlogNonneg : 0 ≤ Real.log (1 / delta) := by
      apply Real.log_nonneg
      exact one_le_one_div hdelta hdeltaOne
    linarith
  have hbinsReal : (preparedGraph.heightPopular.bins : ℝ) ≤ 23 * L := by
    have hnat : (preparedGraph.heightPopular.bins : ℝ) ≤
        (Nat.log 2 (wz1Lemma23BoundedCells delta hdelta).card + 3 : ℕ) := by
      exact_mod_cast hbinsNat
    calc
      (preparedGraph.heightPopular.bins : ℝ) ≤
          (Nat.log 2 (wz1Lemma23BoundedCells delta hdelta).card + 3 : ℕ) :=
        hnat
      _ ≤ 20 * L + 2 := by
        norm_num only [Nat.cast_add, Nat.cast_ofNat]
        linarith [hlog]
      _ ≤ 23 * L := by nlinarith
  apply hschedule delta hdelta hdeltaSmall
      preparedGraph.heightPopular.bins
      (Nat.log 2 preparedGraph.rawResidue.cells.card + 1)
      preparedGraph.graph.residue.extraCost hbinsReal
      (by simpa [L, Nat.cast_add, Nat.cast_one] using hrawLogReal)
  rw [preparedGraph.extraCost_eq]

end Kakeya.Assouad

end
