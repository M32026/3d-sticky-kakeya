import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalGraphParents
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CoarseCellWitness

/-!
# Original fine witnesses on the source-slope residue

Every retained residue parent carries one selected side-`rho` cell.  The first
sticky balancing data supplies a genuine point of the original source shading
in that cell.  This module records all of its source, pullback, residue, and
plane-map provenance.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2SourceHorizontalFixedBinFineWitnessData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    (retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue) where
  coarseWitnesses : PureWZ2CoarseCellWitnessData twoScale
  cell_active : ∀ parent ∈ residue.selected,
    retained.cellFor parent ∈ coarseWitnesses.activeCells
  witness : (ℤ × ℤ × ℤ) → Point3
  witness_eq : ∀ parent ∈ residue.selected,
    witness parent = coarseWitnesses.witness (retained.cellFor parent)
  witness_mem_source : ∀ parent ∈ residue.selected,
    witness parent ∈ source.shading.union
  witness_mem_pullback : ∀ parent ∈ residue.selected,
    witness parent ∈ pullback.shading.union
  witness_mem_retained : ∀ parent ∈ residue.selected,
    witness parent ∈ retained.shading.union
  witness_mem_rhoCell : ∀ parent ∈ residue.selected,
    witness parent ∈ wz1PaperGridCube rho (retained.cellFor parent)
  witness_mem_parent : ∀ parent ∈ residue.selected,
    witness parent ∈
      wz1PaperGridCube twoScale.sqrtRequested.1 parent
  normal : (ℤ × ℤ × ℤ) → Point3
  normal_eq : ∀ parent (hparent : parent ∈ residue.selected),
    normal parent = source.localGrains.planeMap
      ⟨witness parent, witness_mem_source parent hparent⟩
  normal_unit : ∀ parent ∈ residue.selected, ‖normal parent‖ = 1
  normal_vertical : ∀ parent ∈ residue.selected,
    |normal parent (2 : Fin 3)| ≤ 1 / 2
  normal_dist :
    ∀ first ∈ residue.selected, ∀ second ∈ residue.selected,
      dist (normal first) (normal second) ≤
        dist (witness first) (witness second)
  local_ad :
    ∀ parent (hparent : parent ∈ residue.selected),
      PureWZ2PaperADSet1
        (scalarProjection (normal parent)
          (source.shading.union ∩
            Metric.closedBall (witness parent)
              (Real.sqrt rho)))
        rho (1 - sigma)
        (Kakeya.realRpowENN delta (-inputLoss))

theorem PureWZ2SourceHorizontalFixedBinResidueShadingData.fineWitnessesFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    (retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue) :
    Nonempty (PureWZ2SourceHorizontalFixedBinFineWitnessData retained) := by
  rcases twoScale.coarseCellWitnesses with ⟨coarseWitnesses⟩
  have hactive : ∀ parent ∈ residue.selected,
      retained.cellFor parent ∈ coarseWitnesses.activeCells := by
    intro parent hparent
    rw [coarseWitnesses.activeCells_eq]
    exact pullback.selectedCells_subset
      (retained.cellFor_mem parent hparent)
  let witness : (ℤ × ℤ × ℤ) → Point3 := fun parent =>
    coarseWitnesses.witness (retained.cellFor parent)
  let normal : (ℤ × ℤ × ℤ) → Point3 := fun parent =>
    coarseWitnesses.normal (retained.cellFor parent)
  have hwitnessSource : ∀ parent (hparent : parent ∈ residue.selected),
      witness parent ∈ source.shading.union := by
    intro parent hparent
    exact ⟨coarseWitnesses.sourceIndex (retained.cellFor parent),
      coarseWitnesses.witness_mem_source
        (retained.cellFor parent) (hactive parent hparent)⟩
  have hwitnessCell : ∀ parent (hparent : parent ∈ residue.selected),
      witness parent ∈ wz1PaperGridCube rho (retained.cellFor parent) := by
    intro parent hparent
    exact coarseWitnesses.witness_mem_cell
      (retained.cellFor parent) (hactive parent hparent)
  have hwitnessPullback :
      ∀ parent (hparent : parent ∈ residue.selected),
        witness parent ∈ pullback.shading.union := by
    intro parent hparent
    rw [pullback.union_eq]
    constructor
    · rw [pullback.zeroExtension.union_eq]
      exact coarseWitnesses.witness_mem_refined
        (retained.cellFor parent) (hactive parent hparent)
    · rw [pullback.selectedRegion_eq]
      exact Set.mem_iUnion₂.mpr
        ⟨retained.cellFor parent, retained.cellFor_mem parent hparent,
          hwitnessCell parent hparent⟩
  have hwitnessRetained :
      ∀ parent (hparent : parent ∈ residue.selected),
        witness parent ∈ retained.shading.union := by
    intro parent hparent
    rw [retained.union_eq]
    refine ⟨hwitnessPullback parent hparent, ?_⟩
    rw [retained.selectedRegion_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨retained.cellFor parent, by
        rw [retained.selectedCells_eq]
        exact Finset.mem_filter.mpr
          ⟨retained.cellFor_mem parent hparent, by
            rw [retained.cellParent_cellFor parent hparent]
            exact hparent⟩,
        hwitnessCell parent hparent⟩
  have hwitnessParent :
      ∀ parent (hparent : parent ∈ residue.selected),
        witness parent ∈
          wz1PaperGridCube twoScale.sqrtRequested.1 parent := by
    intro parent hparent
    exact retained.cellFor_parent parent hparent (hwitnessCell parent hparent)
  have hnormalEq :
      ∀ parent (hparent : parent ∈ residue.selected),
        normal parent = source.localGrains.planeMap
          ⟨witness parent, hwitnessSource parent hparent⟩ := by
    intro parent hparent
    exact coarseWitnesses.normal_eq
      (retained.cellFor parent) (hactive parent hparent)
  exact ⟨{
    coarseWitnesses := coarseWitnesses
    cell_active := hactive
    witness := witness
    witness_eq := by intro parent hparent; rfl
    witness_mem_source := hwitnessSource
    witness_mem_pullback := hwitnessPullback
    witness_mem_retained := hwitnessRetained
    witness_mem_rhoCell := hwitnessCell
    witness_mem_parent := hwitnessParent
    normal := normal
    normal_eq := hnormalEq
    normal_unit := by
      intro parent hparent
      exact coarseWitnesses.normal_unit
        (retained.cellFor parent) (hactive parent hparent)
    normal_vertical := by
      intro parent hparent
      exact coarseWitnesses.normal_vertical
        (retained.cellFor parent) (hactive parent hparent)
    normal_dist := by
      intro first hfirst second hsecond
      exact coarseWitnesses.normal_dist
        (retained.cellFor first) (hactive first hfirst)
        (retained.cellFor second) (hactive second hsecond)
    local_ad := by
      intro parent hparent
      exact coarseWitnesses.fine_local_ad
        (retained.cellFor parent) (hactive parent hparent)
  }⟩

/-- Backwards-compatible fine-witness data on the maximal global bin. -/
abbrev PureWZ2SourceHorizontalFineWitnessData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    (retained : PureWZ2SourceHorizontalResidueShadingData residue) :=
  PureWZ2SourceHorizontalFixedBinFineWitnessData retained

/-- Compatibility wrapper for the former maximal-bin fine-witness API. -/
theorem PureWZ2SourceHorizontalResidueShadingData.fineWitnesses
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    (retained : PureWZ2SourceHorizontalResidueShadingData residue) :
    Nonempty (PureWZ2SourceHorizontalFineWitnessData retained) :=
  retained.fineWitnessesFixedBin

end Kakeya.Assouad
