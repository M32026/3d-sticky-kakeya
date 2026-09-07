import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderCarrier
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalPopularPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalGraphParents

/-!
# Paper-order preparation for the ordinary Lemma-24 graph

This module installs the pre-graph height-popular carrier in the exact-slice
preparation and rebuilds every dependent witness on that restricted graph
shadow. The graph slope remains the original source slope and the local
normals remain values of the original source plane map.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- All dependent data immediately before the finite Lemma-23 graph is
formed. -/
structure PureWZ2OrdinaryPaperOrderPreparationData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale) where
  graphRetained : PureWZ2SourceHorizontalResidueShadingData carriers.residue :=
    carriers.sourceRetained.withPopularGraph carriers.popularSourceCarrier
  graphRetained_eq : graphRetained =
    carriers.sourceRetained.withPopularGraph carriers.popularSourceCarrier
  prep : PureWZ2SourceHorizontalResiduePreparation graphRetained
  graphParents : PureWZ2SourceHorizontalGraphParentData prep
  fineWitnesses : PureWZ2SourceHorizontalFineWitnessData graphRetained
  original_slope_eq :
    prep.windowed.global.sourceSlope = source.globalGrains.slope
  graph_point_near_height_region :
    ∀ point ∈ prep.shadow.union,
      ∃ anchor ∈ carriers.outerPopular.popular.heightRegion,
        dist point anchor < 2 * delta
  graph_coarse_parent_region :
    prep.shadow.union ⊆ carriers.coarseCarrier.selectedRegion
  original_normal_eq :
    ∀ parent (hparent : parent ∈ carriers.residue.selected),
      fineWitnesses.normal parent = source.localGrains.planeMap
        ⟨fineWitnesses.witness parent,
          fineWitnesses.witness_mem_source parent hparent⟩

/-- Rebuild the exact-slice preparation after imposing the paper's pre-graph
height popularity. -/
theorem PureWZ2OrdinaryPaperOrderCarrierData.prepareGraph
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    Nonempty (PureWZ2OrdinaryPaperOrderPreparationData carriers) := by
  let graphRetained := carriers.sourceRetained.withPopularGraph
    carriers.popularSourceCarrier
  rcases carriers.sourceRetained.prepare hbridge hgraphOne hheightAbsorb with
    ⟨base⟩
  rcases carriers.popularSourceCarrier.installInPreparation base hbridge with
    ⟨prep⟩
  rcases prep.graphParents with ⟨graphParents⟩
  rcases graphRetained.fineWitnesses with ⟨fineWitnesses⟩
  have hnear : ∀ point ∈ prep.shadow.union,
      ∃ anchor ∈ carriers.outerPopular.popular.heightRegion,
        dist point anchor < 2 * delta := by
    intro point hpoint
    have hgraph :
        point ∈ carriers.popularSourceCarrier.graphShadow.union := by
      rw [prep.shadow_eq] at hpoint
      exact hpoint
    exact carriers.popularSourceCarrier.graphShadow_point_near_height_region
      point hgraph
  have hcoarseRegion : prep.shadow.union ⊆
      carriers.coarseCarrier.selectedRegion := by
    intro point hpoint
    have hsourceRetained : point ∈ carriers.sourceRetained.shading.union :=
      prep.shadow_union_subset hpoint
    rw [carriers.sourceRetained.union_eq] at hsourceRetained
    rw [carriers.coarseCarrier.selectedRegion_eq]
    rw [carriers.sourceRetained.selectedRegion_eq] at hsourceRetained
    rcases Set.mem_iUnion₂.mp hsourceRetained.2 with
      ⟨cell, hcell, hpointCell⟩
    have hcellData := Finset.mem_filter.mp (by
      rw [carriers.sourceRetained.selectedCells_eq] at hcell
      exact hcell)
    exact Set.mem_iUnion₂.mpr
      ⟨carriers.sourceRetained.cellParent cell, hcellData.2,
        carriers.sourceRetained.cell_parent cell hcellData.1 hpointCell⟩
  exact ⟨{
    graphRetained := graphRetained
    graphRetained_eq := rfl
    prep := prep
    graphParents := graphParents
    fineWitnesses := fineWitnesses
    original_slope_eq := prep.sourceSlope_eq
    graph_point_near_height_region := hnear
    graph_coarse_parent_region := hcoarseRegion
    original_normal_eq := fineWitnesses.normal_eq
  }⟩

end Kakeya.Assouad

end
