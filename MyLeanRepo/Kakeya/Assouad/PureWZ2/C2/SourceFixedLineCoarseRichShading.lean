import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseRichCells
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CoarseRegionSourcePullback
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRelativeMultiplicityHelpers

/-!
# Whole-cell genuine coarse shading selected by `Z_lin`

The selected objects are actual first-balanced side-`rho` cells.  Restricting
the genuine coarse carrier by their union preserves cubicality and the second
sticky factor-two point-multiplicity band.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2SourceFixedBinCoarseRichShading
    {sigma inputLoss delta rho middleLoss stickyLoss eta theoremEta epsilon : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale} {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared} {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line} {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection} {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue} {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate (eta := eta) fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData graphParents normalFirst}
    {sharp : PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph}
    {ready : PureWZ2SourceFixedBinCoarseReadyGraph (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceFixedBinCoarseAlternativeAHeightData ready epsilon}
    (richCells : PureWZ2SourceFixedBinCoarseRichCells
      (graphParents := graphParents) rich) where
  region : Set Point3 :=
    ⋃ cell ∈ richCells.cells, wz1PaperGridCube rho cell
  region_eq : region =
    ⋃ cell ∈ richCells.cells, wz1PaperGridCube rho cell
  shading : WZ1PaperTubeShading twoScale.coarse.coarse
  carrier_eq : ∀ index, shading.carrier index =
    carrier.shading.carrier index ∩ region
  subshading : PureWZ2PaperIsSubshading
    shading twoScale.coarseGrains.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  union_eq : shading.union = region
  constant_multiplicity : shading.HasConstantMultiplicity
    twoScale.fine.fineMultiplicity
    (2 * twoScale.fine.fineMultiplicity)
  volume_eq : volume shading.union =
    (richCells.cells.card : ENNReal) *
      volume (wz1PaperGridCube rho (0, 0, 0))
  mass_lower :
    (twoScale.fine.fineMultiplicity : ENNReal) *
        volume shading.union ≤ shading.mass
  mass_upper : shading.mass ≤
    (2 * twoScale.fine.fineMultiplicity : ENNReal) *
      volume shading.union
  graph_weighted_volume_lower :
    ((rich.heightIndices.card * preparedGraph.graph.residue.cells.card : ℕ) :
        ENNReal) * volume (wz1PaperGridCube rho (0, 0, 0)) ≤
      54 * (wz1Lemma23SnappedHeights
        preparedGraph.graph.residue.cells).card * volume shading.union
  graph_weighted_mass_lower :
    ((rich.heightIndices.card * preparedGraph.graph.residue.cells.card : ℕ) :
        ENNReal) *
        ((twoScale.fine.fineMultiplicity : ENNReal) *
          volume (wz1PaperGridCube rho (0, 0, 0))) ≤
      54 * (wz1Lemma23SnappedHeights
        preparedGraph.graph.residue.cells).card * shading.mass

abbrev PureWZ2SourceFixedLineCoarseRichShading
    {sigma inputLoss delta rho middleLoss stickyLoss eta theoremEta epsilon : ℝ} {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {original : PureWZ2SourceFixedLineCoarseOriginalSlopeData carriers.coarseCarrier carriers.fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedLineCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedLineCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalNormalFirstCertificate (eta := eta) carriers.fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedLineCoarsePreparedGraphData graphParents normalFirst}
    {sharp : PureWZ2SourceFixedLineCoarseSharpGeometry preparedGraph}
    {ready : PureWZ2SourceFixedLineCoarseReadyGraph (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceFixedLineCoarseAlternativeAHeightData ready epsilon}
    (richCells : PureWZ2SourceFixedLineCoarseRichCells (graphParents := graphParents) rich) : Type :=
  PureWZ2SourceFixedBinCoarseRichShading richCells

theorem PureWZ2SourceFixedBinCoarseRichCells.toRichShadingFixedBin
    {sigma inputLoss delta rho middleLoss stickyLoss eta theoremEta epsilon : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale} {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared} {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line} {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection} {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue} {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate (eta := eta) fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData graphParents normalFirst}
    {sharp : PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph}
    {ready : PureWZ2SourceFixedBinCoarseReadyGraph (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceFixedBinCoarseAlternativeAHeightData ready epsilon}
    (richCells : PureWZ2SourceFixedBinCoarseRichCells
      (graphParents := graphParents) rich) :
    Nonempty (PureWZ2SourceFixedBinCoarseRichShading richCells) := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  let region : Set Point3 :=
    ⋃ cell ∈ richCells.cells, wz1PaperGridCube rho cell
  have hregionMeasurable : MeasurableSet region :=
    MeasurableSet.biUnion richCells.cells.finite_toSet.countable
      (fun cell _ => wz1PaperGridCube_measurable cell)
  let shading : WZ1PaperTubeShading twoScale.coarse.coarse :=
    { carrier := fun index =>
        carrier.shading.carrier index ∩ region
      measurable_carrier := fun index =>
        (carrier.shading.measurable_carrier index).inter
          hregionMeasurable
      subset_body := fun index => Set.inter_subset_left.trans
        (carrier.shading.subset_body index) }
  have hunionInter : shading.union =
      carrier.shading.union ∩ region := by
    ext point
    constructor
    · rintro ⟨index, hpoint, hregion⟩
      exact ⟨⟨index, hpoint⟩, hregion⟩
    · rintro ⟨⟨index, hpoint⟩, hregion⟩
      exact ⟨index, hpoint, hregion⟩
  have hregionSubset : region ⊆ carrier.shading.union := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
    have hinter := carrier.whole_cells.inter_activeCell_eq
      twoScale.coarseGrains.extremal.delta_pos
      (richCells.cells_active_carrier hcell)
    have : point ∈ carrier.shading.union ∩
        wz1PaperGridCube twoScale.rhoRequested.1 cell := by
      rw [hinter]
      simpa only [twoScale.rhoRequested_eq] using hpointCell
    exact this.1
  have hunion : shading.union = region := by
    rw [hunionInter]
    exact Set.inter_eq_right.mpr hregionSubset
  have hsub : PureWZ2PaperIsSubshading
      shading twoScale.coarseGrains.shading := by
    intro index point hpoint
    exact carrier.subshading index hpoint.1
  have hwhole : WZ1PaperIsCubicalShading shading := by
    intro index point hpoint other hother
    have hcarrierOther := carrier.whole_cells
      index point hpoint.1 hother
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨cell, hcell, hpointCell⟩
    have hsame : wz1PaperGridIndex rho other = cell := by
      have hpointIndex :=
        (mem_wz1PaperGridCube rho cell point).mp hpointCell
      have hother' : other ∈ wz1PaperGridCube rho
          (wz1PaperGridIndex rho point) := by
        simpa only [twoScale.rhoRequested_eq] using hother
      have hotherIndex := (mem_wz1PaperGridCube rho
        (wz1PaperGridIndex rho point) other).mp hother'
      exact hotherIndex.trans hpointIndex
    exact ⟨hcarrierOther, Set.mem_iUnion₂.mpr
      ⟨cell, hcell, (mem_wz1PaperGridCube rho cell other).mpr hsame⟩⟩
  have hconstant : shading.HasConstantMultiplicity
      twoScale.fine.fineMultiplicity
      (2 * twoScale.fine.fineMultiplicity) := by
    have hcarrier := carrier.constantMultiplicityFixedBin
    intro point hpoint
    have hregion : point ∈ region := by
      rw [← hunion]
      exact hpoint
    have hcarrierPoint : point ∈
        carrier.shading.union := hregionSubset hregion
    have hmultiplicity : shading.pointMultiplicity point =
        carrier.shading.pointMultiplicity point :=
      wholeCellRestriction_pointMultiplicity_eq (fun _ => rfl) hpoint
    rw [hmultiplicity]
    exact hcarrier point hcarrierPoint
  have hvolume : volume shading.union =
      (richCells.cells.card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
    rw [hunion]
    exact wz1PaperGridCube_volume_biUnion hrho richCells.cells
  have hmassBounds := constant_multiplicity_mass_volume_generic hconstant
  have hownerNat : rich.heightIndices.card *
        preparedGraph.graph.residue.cells.card ≤
      54 * (wz1Lemma23SnappedHeights
        preparedGraph.graph.residue.cells).card * richCells.cells.card := by
    calc
      rich.heightIndices.card * preparedGraph.graph.residue.cells.card ≤
          preparedGraph.graph.residue.heightFiberCost *
            (wz1Lemma23SnappedHeights
              preparedGraph.graph.residue.cells).card *
                richCells.graphCells.card := richCells.graphCells_card_lower
      _ ≤ 2 * (wz1Lemma23SnappedHeights
            preparedGraph.graph.residue.cells).card *
              richCells.graphCells.card := by
        rw [ready.heightFiberCost_eq]
      _ ≤ 2 * (wz1Lemma23SnappedHeights
            preparedGraph.graph.residue.cells).card *
              (27 * richCells.cells.card) := by
        exact Nat.mul_le_mul_left
          (2 * (wz1Lemma23SnappedHeights
            preparedGraph.graph.residue.cells).card)
          richCells.graphCells_card
      _ = 54 * (wz1Lemma23SnappedHeights
            preparedGraph.graph.residue.cells).card *
              richCells.cells.card := by ring
  have howner :
      ((rich.heightIndices.card * preparedGraph.graph.residue.cells.card : ℕ) :
          ENNReal) ≤
        54 * (wz1Lemma23SnappedHeights
          preparedGraph.graph.residue.cells).card *
            (richCells.cells.card : ENNReal) := by
    exact_mod_cast hownerNat
  have hgraphVolume :
      ((rich.heightIndices.card * preparedGraph.graph.residue.cells.card : ℕ) :
          ENNReal) * volume (wz1PaperGridCube rho (0, 0, 0)) ≤
        54 * (wz1Lemma23SnappedHeights
          preparedGraph.graph.residue.cells).card * volume shading.union := by
    calc
      _ ≤ (54 * (wz1Lemma23SnappedHeights
            preparedGraph.graph.residue.cells).card *
              (richCells.cells.card : ENNReal)) *
            volume (wz1PaperGridCube rho (0, 0, 0)) := by gcongr
      _ = 54 * (wz1Lemma23SnappedHeights
            preparedGraph.graph.residue.cells).card *
              volume shading.union := by rw [hvolume]; ring
  have hgraphMass :
      ((rich.heightIndices.card * preparedGraph.graph.residue.cells.card : ℕ) :
          ENNReal) *
          ((twoScale.fine.fineMultiplicity : ENNReal) *
            volume (wz1PaperGridCube rho (0, 0, 0))) ≤
        54 * (wz1Lemma23SnappedHeights
          preparedGraph.graph.residue.cells).card * shading.mass := by
    calc
      _ = (twoScale.fine.fineMultiplicity : ENNReal) *
          (((rich.heightIndices.card *
              preparedGraph.graph.residue.cells.card : ℕ) : ENNReal) *
            volume (wz1PaperGridCube rho (0, 0, 0))) := by ring
      _ ≤ (twoScale.fine.fineMultiplicity : ENNReal) *
          (54 * (wz1Lemma23SnappedHeights
            preparedGraph.graph.residue.cells).card *
              volume shading.union) := by gcongr
      _ = 54 * (wz1Lemma23SnappedHeights
            preparedGraph.graph.residue.cells).card *
          ((twoScale.fine.fineMultiplicity : ENNReal) *
            volume shading.union) := by ring
      _ ≤ 54 * (wz1Lemma23SnappedHeights
            preparedGraph.graph.residue.cells).card * shading.mass := by
        exact mul_le_mul_left' hmassBounds.1 _
  exact ⟨{
    region := region
    region_eq := rfl
    shading := shading
    carrier_eq := fun _ => rfl
    subshading := hsub
    whole_cells := hwhole
    union_eq := hunion
    constant_multiplicity := hconstant
    volume_eq := hvolume
    mass_lower := hmassBounds.1
    mass_upper := hmassBounds.2
    graph_weighted_volume_lower := hgraphVolume
    graph_weighted_mass_lower := hgraphMass
  }⟩

theorem PureWZ2SourceFixedLineCoarseRichCells.toRichShading
    {sigma inputLoss delta rho middleLoss stickyLoss eta theoremEta epsilon : ℝ} {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {original : PureWZ2SourceFixedLineCoarseOriginalSlopeData carriers.coarseCarrier carriers.fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedLineCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedLineCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalNormalFirstCertificate (eta := eta) carriers.fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedLineCoarsePreparedGraphData graphParents normalFirst}
    {sharp : PureWZ2SourceFixedLineCoarseSharpGeometry preparedGraph}
    {ready : PureWZ2SourceFixedLineCoarseReadyGraph (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceFixedLineCoarseAlternativeAHeightData ready epsilon}
    (richCells : PureWZ2SourceFixedLineCoarseRichCells (graphParents := graphParents) rich) :
    Nonempty (PureWZ2SourceFixedLineCoarseRichShading richCells) :=
  PureWZ2SourceFixedBinCoarseRichCells.toRichShadingFixedBin richCells

/-- Pull the `Z_lin` coarse region back through the first balanced cover to
the original `delta` family, with the exact volume and indexed-mass cross
identities supplied by that cover. -/
theorem PureWZ2SourceFixedBinCoarseRichShading.pullbackToSourceFixedBin
    {sigma inputLoss delta rho middleLoss stickyLoss eta theoremEta epsilon : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate
      (eta := eta) fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData
      graphParents normalFirst}
    {sharp : PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph}
    {ready : PureWZ2SourceFixedBinCoarseReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceFixedBinCoarseAlternativeAHeightData ready epsilon}
    {richCells : PureWZ2SourceFixedBinCoarseRichCells
      (graphParents := graphParents) rich}
    (richShading : PureWZ2SourceFixedBinCoarseRichShading richCells) :
    Nonempty (PureWZ2SelectedCoarseRegionSourcePullbackData
      richShading.shading) :=
  pureWZ2_pullback_selected_coarse_region richShading.shading
    richShading.subshading richShading.whole_cells

theorem PureWZ2SourceFixedLineCoarseRichShading.pullbackToSource
    {sigma inputLoss delta rho middleLoss stickyLoss eta theoremEta epsilon : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {original : PureWZ2SourceFixedLineCoarseOriginalSlopeData
      carriers.coarseCarrier carriers.fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedLineCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedLineCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalNormalFirstCertificate
      (eta := eta) carriers.fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedLineCoarsePreparedGraphData
      graphParents normalFirst}
    {sharp : PureWZ2SourceFixedLineCoarseSharpGeometry preparedGraph}
    {ready : PureWZ2SourceFixedLineCoarseReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceFixedLineCoarseAlternativeAHeightData ready epsilon}
    {richCells : PureWZ2SourceFixedLineCoarseRichCells
      (graphParents := graphParents) rich}
    (richShading : PureWZ2SourceFixedLineCoarseRichShading richCells) :
    Nonempty (PureWZ2SelectedCoarseRegionSourcePullbackData
      richShading.shading) :=
  PureWZ2SourceFixedBinCoarseRichShading.pullbackToSourceFixedBin richShading

end Kakeya.Assouad

end
