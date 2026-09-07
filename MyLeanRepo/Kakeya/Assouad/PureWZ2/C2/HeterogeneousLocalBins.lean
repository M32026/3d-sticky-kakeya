import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CoarseCellWitness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ActiveCellShadowGrains
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23HeterogeneousLocalBins
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment

/-!
# Pure coarse/fine adapter for the WZ1 Lemma-23 local bins

The first sticky coarse shading supplies the graph carrier.  Its active
side-`rho` cells also contain genuine points of the original fine shading,
chosen by `PureWZ2CoarseCellWitnessData`.  This module keeps those two roles
separate and packages exactly the additional layer selection needed by the
heterogeneous local-bin theorem.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
Paper-faithful coarse/fine input for the local-bin step.

The `coarseRepresentative`s lie in the first-stage `rho`-tube shading.  The
`fineWitness` selected for their owner cell lies in the original `delta`-tube
shading.  Only the latter supplies the normal and local AD certificate.
-/
structure PureWZ2Lemma23CoarseFineLocalBinData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    (witnesses : PureWZ2CoarseCellWitnessData twoScale)
    (graphScale : ℝ) (cells : Finset (ℤ × ℤ × ℤ))
    (g : ℝ → ℝ) where
  coarseRepresentative : (ℤ × ℤ × ℤ) → Point3
  coarse_representative_mem :
    ∀ idx ∈ cells,
      coarseRepresentative idx ∈
        twoScale.fine.refined.union
  coarse_representative_index :
    ∀ idx ∈ cells,
      wz1Lemma23CellIndex graphScale (coarseRepresentative idx) = idx
  ownerCell : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ)
  owner_active :
    ∀ idx ∈ cells, ownerCell idx ∈ witnesses.activeCells
  representative_mem_owner :
    ∀ idx ∈ cells,
      coarseRepresentative idx ∈
        wz1PaperGridCube rho (ownerCell idx)
  anchorCell : ℤ → (ℤ × ℤ × ℤ)
  anchor_active :
    ∀ y ∈ wz1Lemma23SnappedYLayers cells,
      anchorCell y ∈ witnesses.activeCells
  layer_fine_ball :
    ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
      ∀ idx (hidx : idx ∈ cells), idx.2.1 = y →
        dist
            (witnesses.witness (ownerCell idx))
            (witnesses.witness (anchorCell y)) ≤
          Real.sqrt graphScale
  normal_first :
    ∀ y ∈ wz1Lemma23SnappedYLayers cells,
      1 / 4 ≤
        |witnesses.normal (anchorCell y) (0 : Fin 3)|
  graph_eq :
    ∀ y ∈ wz1Lemma23SnappedYLayers cells,
      g (wz1Lemma23SnappedYValue graphScale y) =
        witnesses.normal (anchorCell y) (2 : Fin 3) /
          witnesses.normal (anchorCell y) (0 : Fin 3)

/--
Forget the paper-specific provenance while preserving the heterogeneous
coarse/fine roles required by the WZ1 local-bin count.
-/
def PureWZ2Lemma23CoarseFineLocalBinData.toHeterogeneousInput
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {witnesses : PureWZ2CoarseCellWitnessData twoScale}
    {graphScale : ℝ} {cells : Finset (ℤ × ℤ × ℤ)} {g : ℝ → ℝ}
    (data : PureWZ2Lemma23CoarseFineLocalBinData
      witnesses graphScale cells g)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hrhoGraph : rho ≤ graphScale)
    (hgraphOne : graphScale ≤ 1) :
    WZ1Lemma23HeterogeneousLocalBinInput
      graphScale sigma
        (10 * Kakeya.realRpowENN delta (-inputLoss)) cells g := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact source.extremal.delta_pos.trans_le
      twoScale.rhoRequested.property.1
  exact
    { fineCarrier := source.shading.union
      coarseRepresentative := data.coarseRepresentative
      fineWitness := fun idx =>
        witnesses.witness (data.ownerCell idx)
      anchor := fun y =>
        witnesses.witness (data.anchorCell y)
      normal := fun y =>
        witnesses.normal (data.anchorCell y)
      fine_witness_mem := by
        intro idx hidx
        exact
          ⟨witnesses.sourceIndex (data.ownerCell idx),
            witnesses.witness_mem_source (data.ownerCell idx)
              (data.owner_active idx hidx)⟩
      coarse_representative_index :=
        data.coarse_representative_index
      coarse_fine_close := by
        intro idx hidx
        exact (le_of_lt
          (wz1_paper_grid_cube_diameter_lt_two_rho hrho
            (data.representative_mem_owner idx hidx)
            (witnesses.witness_mem_cell (data.ownerCell idx)
              (data.owner_active idx hidx)))).trans (by gcongr)
      fine_witness_in_anchor_ball := data.layer_fine_ball
      normal_unit := by
        intro y hy
        exact witnesses.normal_unit (data.anchorCell y)
          (data.anchor_active y hy)
      normal_vertical := by
        intro y hy
        exact witnesses.normal_vertical (data.anchorCell y)
          (data.anchor_active y hy)
      normal_first := data.normal_first
      graph_eq := data.graph_eq
      fine_local_ad := by
        intro y hy
        let cell := data.anchorCell y
        have hcell : cell ∈ witnesses.activeCells :=
          data.anchor_active y hy
        have hnormalUnit : ‖witnesses.normal cell‖ = 1 :=
          witnesses.normal_unit cell hcell
        have hdeltaGraph : delta ≤ graphScale := by
          exact twoScale.rhoRequested.property.1.trans (by
            simpa only [twoScale.rhoRequested_eq] using hrhoGraph)
        rw [witnesses.normal_eq cell hcell]
        exact hbridge.1 _ graphScale (1 - sigma)
          (Kakeya.realRpowENN delta (-inputLoss))
          (scalarProjection_paperShading_subset_Icc
            (source.localGrains.planeMap_unit
              ⟨witnesses.witness cell,
                ⟨witnesses.sourceIndex cell,
                  witnesses.witness_mem_source cell hcell⟩⟩)
            Set.inter_subset_left)
          (source.localGrains.local_ad graphScale hdeltaGraph hgraphOne
            ⟨witnesses.witness cell,
              ⟨witnesses.sourceIndex cell,
                witnesses.witness_mem_source cell hcell⟩⟩) }

/--
The Pure coarse/fine package directly yields the actual local-bin estimate.
-/
theorem PureWZ2Lemma23CoarseFineLocalBinData.local_bins_at
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {witnesses : PureWZ2CoarseCellWitnessData twoScale}
    {graphScale : ℝ} {cells : Finset (ℤ × ℤ × ℤ)} {g : ℝ → ℝ}
    (data : PureWZ2Lemma23CoarseFineLocalBinData
      witnesses graphScale cells g)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hrhoGraph : rho ≤ graphScale)
    (hgraphOne : graphScale ≤ 1)
    (y : ℤ) (hy : y ∈ wz1Lemma23SnappedYLayers cells) :
    ((wz1Lemma23SnappedLocalBinsAt graphScale g cells y).card : ENNReal) ≤
      35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
        Kakeya.realRpowENN
          (Real.sqrt graphScale / graphScale) (1 - sigma) := by
  have hgraph : 0 < graphScale :=
    (by
      rw [← twoScale.rhoRequested_eq] at hrhoGraph
      exact twoScale.coarseGrains.extremal.delta_pos.trans_le hrhoGraph)
  exact
    wz1_lemma23_actual_local_bins_at_heterogeneous
      (10 * Kakeya.realRpowENN delta (-inputLoss))
      cells g (data.toHeterogeneousInput hbridge hrhoGraph hgraphOne)
      hgraph hgraphOne y hy

end Kakeya.Assouad
