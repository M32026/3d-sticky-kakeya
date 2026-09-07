import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineResidueShading
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SecondStageSources

/-!
# Actual second-stage sources on the fixed-line y-residue shading
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

structure PureWZ2HorizontalFixedLineResidueSourceFamily
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    (residueShading :
      PureWZ2HorizontalFixedLineResidueShadingData residue) where
  sourceFor :
    ∀ parent, parent ∈ residue.selected →
      PureWZ2SecondStageSourceData twoScale
  sourceFor_cell :
    ∀ parent (hparent : parent ∈ residue.selected),
      (sourceFor parent hparent).cell = parent
  anchor_mem :
    ∀ parent (hparent : parent ∈ residue.selected),
      (sourceFor parent hparent).anchor ∈ residueShading.shading.union
  anchor_mem_parent :
    ∀ parent (hparent : parent ∈ residue.selected),
      (sourceFor parent hparent).anchor ∈
        wz1PaperGridCube twoScale.sqrtRequested.1 parent
  coarse_source_subset :
    ∀ parent (hparent : parent ∈ residue.selected),
      (sourceFor parent hparent).coarseSource ⊆
        residueShading.shading.union ∩
          Metric.closedBall (sourceFor parent hparent).anchor
            twoScale.sqrtRequested.1

theorem PureWZ2HorizontalFixedLineResidueShadingData.sources
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    (residueShading :
      PureWZ2HorizontalFixedLineResidueShadingData residue) :
    Nonempty (PureWZ2HorizontalFixedLineResidueSourceFamily residueShading) := by
  have hparentActive :
      ∀ parent ∈ residue.selected,
        parent ∈ twoScale.fine.balanced.activeCells := by
    intro parent hparent
    exact parents.parents_subset
      (selection.selected_subset (residue.selected_subset hparent))
  have hsourceExists :
      ∀ parent (hparent : parent ∈ residue.selected),
        ∃ data : PureWZ2SecondStageSourceData twoScale, data.cell = parent := by
    intro parent hparent
    exact twoScale.secondStageSourceAt parent (hparentActive parent hparent)
  let sourceFor :
      ∀ parent, parent ∈ residue.selected →
        PureWZ2SecondStageSourceData twoScale := fun parent hparent =>
    Classical.choose (hsourceExists parent hparent)
  have hsourceCell :
      ∀ parent (hparent : parent ∈ residue.selected),
        (sourceFor parent hparent).cell = parent := by
    intro parent hparent
    exact Classical.choose_spec (hsourceExists parent hparent)
  have hanchor :
      ∀ parent (hparent : parent ∈ residue.selected),
        (sourceFor parent hparent).anchor ∈ residueShading.shading.union := by
    intro parent hparent
    let data := sourceFor parent hparent
    have hanchorFull : data.anchor ∈ data.fullSource :=
      data.centers_subset data.anchor_mem
    rw [data.fullSource_eq] at hanchorFull
    rw [residueShading.union_eq]
    refine ⟨hanchorFull.1, ?_⟩
    rw [residueShading.selectedRegion_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨parent, hparent, by
        change data.anchor ∈ wz1PaperGridCube twoScale.sqrtRequested.1 parent
        have hanchorCell := hanchorFull.2
        have hcellData : data.cell = parent := hsourceCell parent hparent
        rwa [hcellData] at hanchorCell⟩
  have hanchorParent :
      ∀ parent (hparent : parent ∈ residue.selected),
        (sourceFor parent hparent).anchor ∈
          wz1PaperGridCube twoScale.sqrtRequested.1 parent := by
    intro parent hparent
    let data := sourceFor parent hparent
    have hanchorFull : data.anchor ∈ data.fullSource :=
      data.centers_subset data.anchor_mem
    rw [data.fullSource_eq] at hanchorFull
    have hanchorCell := hanchorFull.2
    have hcellData : data.cell = parent := hsourceCell parent hparent
    rwa [hcellData] at hanchorCell
  have hcoarse :
      ∀ parent (hparent : parent ∈ residue.selected),
        (sourceFor parent hparent).coarseSource ⊆
          residueShading.shading.union ∩
            Metric.closedBall (sourceFor parent hparent).anchor
              twoScale.sqrtRequested.1 := by
    intro parent hparent point hpoint
    let data := sourceFor parent hparent
    have hpointDef :
        point ∈ data.fullSource ∩
          Metric.closedBall data.anchor twoScale.sqrtRequested.1 := by
      rwa [← data.coarseSource_eq]
    have hfull := hpointDef.1
    rw [data.fullSource_eq] at hfull
    rw [residueShading.union_eq]
    refine ⟨⟨hfull.1, ?_⟩, hpointDef.2⟩
    rw [residueShading.selectedRegion_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨parent, hparent, by
        have hpointCell := hfull.2
        have hcellData : data.cell = parent := hsourceCell parent hparent
        rwa [hcellData] at hpointCell⟩
  exact
    ⟨{ sourceFor := sourceFor
       sourceFor_cell := hsourceCell
       anchor_mem := hanchor
       anchor_mem_parent := hanchorParent
       coarse_source_subset := hcoarse }⟩

end Kakeya.Assouad
