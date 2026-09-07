import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleRetainedShading
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleSources

/-!
# Genuine terminal coarse sources before choosing a graph scale

Every selected side-`sqrt delta` parent receives the self-centered genuine
source constructed from the balanced terminal shading.  This package is
deliberately independent of the auxiliary Lemma-23 graph scale.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2TerminalBinSourceFamily
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedBinParentData line}
    {selection : PureWZ2TerminalBinParentYSelection parents}
    {residue : PureWZ2TerminalBinParentYResidueData selection}
    (retained : PureWZ2TerminalBinRetainedShadingData residue) where
  sourceFor : ∀ parent, parent ∈ residue.selected →
    PureWZ2TerminalCoarseSourceData terminalSource
  sourceFor_cell : ∀ parent (hparent : parent ∈ residue.selected),
    (sourceFor parent hparent).cell = parent
  anchor_mem : ∀ parent (hparent : parent ∈ residue.selected),
    (sourceFor parent hparent).anchor ∈ retained.shading.union
  anchor_mem_parent : ∀ parent (hparent : parent ∈ residue.selected),
    (sourceFor parent hparent).anchor ∈
      wz1PaperGridCube terminal.sqrtRequested.1 parent
  coarse_source_subset : ∀ parent (hparent : parent ∈ residue.selected),
    (sourceFor parent hparent).coarseSource ⊆
      retained.shading.union ∩
        Metric.closedBall (sourceFor parent hparent).anchor
          terminal.sqrtRequested.1

/-- Backwards-compatible source family on the largest global bin. -/
abbrev PureWZ2TerminalSourceFamily
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedLineParentData line}
    {selection : PureWZ2TerminalParentYSelection parents}
    {residue : PureWZ2TerminalParentYResidueData selection}
    (retained : PureWZ2TerminalRetainedShadingData residue) :=
  PureWZ2TerminalBinSourceFamily retained

theorem PureWZ2TerminalBinRetainedShadingData.sourcesBin
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedBinParentData line}
    {selection : PureWZ2TerminalBinParentYSelection parents}
    {residue : PureWZ2TerminalBinParentYResidueData selection}
    (retained : PureWZ2TerminalBinRetainedShadingData residue) :
    Nonempty (PureWZ2TerminalBinSourceFamily retained) := by
  have hsourceExists :
      ∀ parent (hparent : parent ∈ residue.selected),
        ∃ data : PureWZ2TerminalCoarseSourceData terminalSource,
          data.cell = parent := by
    intro parent hparent
    have hactive : parent ∈ terminal.sticky.balanced.activeCells :=
      parents.parents_subset
        (selection.selected_subset (residue.selected_subset hparent))
    exact terminalSource.coarseSourceAt parent hactive
  let sourceFor : ∀ parent, parent ∈ residue.selected →
      PureWZ2TerminalCoarseSourceData terminalSource := fun parent hparent =>
    Classical.choose (hsourceExists parent hparent)
  have hsourceCell : ∀ parent (hparent : parent ∈ residue.selected),
      (sourceFor parent hparent).cell = parent := by
    intro parent hparent
    exact Classical.choose_spec (hsourceExists parent hparent)
  have hanchor : ∀ parent (hparent : parent ∈ residue.selected),
      (sourceFor parent hparent).anchor ∈ retained.shading.union := by
    intro parent hparent
    let data := sourceFor parent hparent
    have hfull : data.anchor ∈ data.fullSource :=
      data.centers_subset data.anchor_mem
    rw [data.fullSource_eq] at hfull
    rw [retained.union_eq]
    refine ⟨?_, ?_⟩
    · rw [← terminalSource.shading_eq]
      exact hfull.1
    · rw [retained.selectedRegion_eq]
      refine Set.mem_iUnion₂.mpr ⟨parent, hparent, ?_⟩
      simpa only [data, hsourceCell parent hparent] using hfull.2
  have hanchorParent : ∀ parent (hparent : parent ∈ residue.selected),
      (sourceFor parent hparent).anchor ∈
        wz1PaperGridCube terminal.sqrtRequested.1 parent := by
    intro parent hparent
    let data := sourceFor parent hparent
    have hfull : data.anchor ∈ data.fullSource :=
      data.centers_subset data.anchor_mem
    rw [data.fullSource_eq] at hfull
    simpa only [data, hsourceCell parent hparent] using hfull.2
  have hcoarse : ∀ parent (hparent : parent ∈ residue.selected),
      (sourceFor parent hparent).coarseSource ⊆
        retained.shading.union ∩
          Metric.closedBall (sourceFor parent hparent).anchor
            terminal.sqrtRequested.1 := by
    intro parent hparent point hpoint
    let data := sourceFor parent hparent
    have hsource := data.coarseSource_subset hpoint
    refine ⟨?_, hsource.2⟩
    rw [retained.union_eq]
    refine ⟨?_, ?_⟩
    · rw [← terminalSource.shading_eq]
      exact hsource.1
    · rw [retained.selectedRegion_eq]
      refine Set.mem_iUnion₂.mpr ⟨parent, hparent, ?_⟩
      rw [data.coarseSource_eq, data.fullSource_eq] at hpoint
      simpa only [data, hsourceCell parent hparent] using hpoint.1.2
  exact ⟨{
    sourceFor := sourceFor
    sourceFor_cell := hsourceCell
    anchor_mem := hanchor
    anchor_mem_parent := hanchorParent
    coarse_source_subset := hcoarse
  }⟩

/-- Compatibility wrapper for the former largest-bin terminal chain. -/
theorem PureWZ2TerminalRetainedShadingData.sources
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedLineParentData line}
    {selection : PureWZ2TerminalParentYSelection parents}
    {residue : PureWZ2TerminalParentYResidueData selection}
    (retained : PureWZ2TerminalRetainedShadingData residue) :
    Nonempty (PureWZ2TerminalSourceFamily retained) :=
  retained.sourcesBin

end Kakeya.Assouad
