import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineRichCells
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRelativeMultiplicityHelpers

/-!
# Whole-cell coarse shading carried by Alternative-A rich heights

The selected objects are genuine side-`rho` cells of the first sticky coarse
family.  The shading is a full spatial restriction of the fixed-line residue,
so the final factor-two multiplicity band is preserved.  Consequently the
weighted height count converts to both union volume and indexed mass without
another balanced-cell loss.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2HorizontalAlternativeARichShading
    {sigma inputLoss delta rho middleLoss outputLoss eta theoremEta epsilon : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    {residueShading : PureWZ2HorizontalFixedLineResidueShadingData residue}
    {prep : PureWZ2HorizontalFixedLineResiduePreparation residueShading}
    {graphParents : PureWZ2HorizontalFixedLineGraphParentData prep}
    {sources : PureWZ2HorizontalFixedLineResidueSourceFamily residueShading}
    {fullGrains : PureWZ2HorizontalFixedLineResidueFullGrainFamily
      (eta := eta) sources prep}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2HorizontalFixedLineSharpGeometry graph}
    {ready : PureWZ2HorizontalFixedLineReadyGraph
      (eta := eta) (theoremEta := theoremEta)
      (graphParents := graphParents) (sources := sources)
      (fullGrains := fullGrains) sharp}
    {rich : PureWZ2HorizontalAlternativeAHeightData ready epsilon}
    (richCells : PureWZ2HorizontalAlternativeARichCells
      (graphParents := graphParents) rich) where
  region : Set Point3 :=
    ⋃ cell ∈ richCells.cells, wz1PaperGridCube rho cell
  region_eq : region =
    ⋃ cell ∈ richCells.cells, wz1PaperGridCube rho cell
  shading : WZ1PaperTubeShading twoScale.coarse.coarse
  carrier_eq : ∀ index, shading.carrier index =
    residueShading.shading.carrier index ∩ region
  subshading :
    PureWZ2PaperIsSubshading shading twoScale.coarseGrains.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  union_eq : shading.union = region
  constant_multiplicity :
    shading.HasConstantMultiplicity
      twoScale.fine.fineMultiplicity
      (2 * twoScale.fine.fineMultiplicity)
  volume_eq : volume shading.union =
    (richCells.cells.card : ENNReal) *
      volume (wz1PaperGridCube rho (0, 0, 0))
  mass_lower :
    (twoScale.fine.fineMultiplicity : ENNReal) *
        volume shading.union ≤ shading.mass
  mass_upper :
    shading.mass ≤
      (2 * twoScale.fine.fineMultiplicity : ENNReal) *
        volume shading.union
  graph_weighted_volume_lower :
    ((rich.heightIndices.card * graph.residue.cells.card : ℕ) : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0)) ≤
      54 * (wz1Lemma23SnappedHeights graph.residue.cells).card *
        volume shading.union
  graph_weighted_mass_lower :
    ((rich.heightIndices.card * graph.residue.cells.card : ℕ) : ENNReal) *
        ((twoScale.fine.fineMultiplicity : ENNReal) *
          volume (wz1PaperGridCube rho (0, 0, 0))) ≤
      54 * (wz1Lemma23SnappedHeights graph.residue.cells).card *
        shading.mass

theorem PureWZ2HorizontalAlternativeARichCells.toRichShading
    {sigma inputLoss delta rho middleLoss outputLoss eta theoremEta epsilon : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    {residueShading : PureWZ2HorizontalFixedLineResidueShadingData residue}
    {prep : PureWZ2HorizontalFixedLineResiduePreparation residueShading}
    {graphParents : PureWZ2HorizontalFixedLineGraphParentData prep}
    {sources : PureWZ2HorizontalFixedLineResidueSourceFamily residueShading}
    {fullGrains : PureWZ2HorizontalFixedLineResidueFullGrainFamily
      (eta := eta) sources prep}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2HorizontalFixedLineSharpGeometry graph}
    {ready : PureWZ2HorizontalFixedLineReadyGraph
      (eta := eta) (theoremEta := theoremEta)
      (graphParents := graphParents) (sources := sources)
      (fullGrains := fullGrains) sharp}
    {rich : PureWZ2HorizontalAlternativeAHeightData ready epsilon}
    (richCells : PureWZ2HorizontalAlternativeARichCells
      (graphParents := graphParents) rich) :
    Nonempty (PureWZ2HorizontalAlternativeARichShading richCells) := by
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
        residueShading.shading.carrier index ∩ region
      measurable_carrier := fun index =>
        (residueShading.shading.measurable_carrier index).inter
          hregionMeasurable
      subset_body := fun index => Set.inter_subset_left.trans
        (residueShading.shading.subset_body index) }
  have hunionInter :
      shading.union = residueShading.shading.union ∩ region := by
    ext point
    constructor
    · rintro ⟨index, hpoint, hregion⟩
      exact ⟨⟨index, hpoint⟩, hregion⟩
    · rintro ⟨⟨index, hpoint⟩, hregion⟩
      exact ⟨index, hpoint, hregion⟩
  have hregionSubset : region ⊆ residueShading.shading.union := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
    have hactive := richCells.cells_subset hcell
    have hinter := residueShading.whole_cells.inter_activeCell_eq
      twoScale.coarseGrains.extremal.delta_pos hactive
    have : point ∈ residueShading.shading.union ∩
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
    exact residueShading.subshading index hpoint.1
  have hwhole : WZ1PaperIsCubicalShading shading := by
    intro index point hpoint other hother
    have hresidueOther :=
      residueShading.whole_cells index point hpoint.1 hother
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨cell, hcell, hpointCell⟩
    have hsame : wz1PaperGridIndex rho other = cell := by
      have hpointIndex := (mem_wz1PaperGridCube rho cell point).mp hpointCell
      have hother' : other ∈ wz1PaperGridCube rho
          (wz1PaperGridIndex rho point) := by
        simpa only [twoScale.rhoRequested_eq] using hother
      have hotherIndex := (mem_wz1PaperGridCube rho
        (wz1PaperGridIndex rho point) other).mp hother'
      exact hotherIndex.trans hpointIndex
    exact ⟨hresidueOther, Set.mem_iUnion₂.mpr
      ⟨cell, hcell, (mem_wz1PaperGridCube rho cell other).mpr hsame⟩⟩
  have hconstant : shading.HasConstantMultiplicity
      twoScale.fine.fineMultiplicity
      (2 * twoScale.fine.fineMultiplicity) := by
    have hresidue := residueShading.constantMultiplicity
    intro point hpoint
    have hregion : point ∈ region := by
      rw [← hunion]
      exact hpoint
    have hresiduePoint : point ∈ residueShading.shading.union :=
      hregionSubset hregion
    have hmultiplicity : shading.pointMultiplicity point =
        residueShading.shading.pointMultiplicity point := by
      exact wholeCellRestriction_pointMultiplicity_eq
        (fun _ => rfl) hpoint
    rw [hmultiplicity]
    exact hresidue point hresiduePoint
  have hvolume : volume shading.union =
      (richCells.cells.card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
    rw [hunion]
    exact wz1PaperGridCube_volume_biUnion hrho richCells.cells
  have hmassBounds := constant_multiplicity_mass_volume_generic hconstant
  have hownerNat :
      rich.heightIndices.card * graph.residue.cells.card ≤
        54 * (wz1Lemma23SnappedHeights graph.residue.cells).card *
          richCells.cells.card := by
    calc
      rich.heightIndices.card * graph.residue.cells.card ≤
          graph.residue.heightFiberCost *
            (wz1Lemma23SnappedHeights graph.residue.cells).card *
              richCells.graphCells.card := richCells.graphCells_card_lower
      _ ≤ 2 * (wz1Lemma23SnappedHeights graph.residue.cells).card *
            richCells.graphCells.card := by
        rw [ready.heightFiberCost_eq]
      _ ≤ 2 * (wz1Lemma23SnappedHeights graph.residue.cells).card *
            (27 * richCells.cells.card) := by
        exact Nat.mul_le_mul_left
          (2 * (wz1Lemma23SnappedHeights graph.residue.cells).card)
          richCells.graphCells_card
      _ = 54 * (wz1Lemma23SnappedHeights graph.residue.cells).card *
            richCells.cells.card := by ring
  have howner :
      ((rich.heightIndices.card * graph.residue.cells.card : ℕ) : ENNReal) ≤
        54 * (wz1Lemma23SnappedHeights graph.residue.cells).card *
          (richCells.cells.card : ENNReal) := by
    exact_mod_cast hownerNat
  have hgraphVolume :
      ((rich.heightIndices.card * graph.residue.cells.card : ℕ) : ENNReal) *
          volume (wz1PaperGridCube rho (0, 0, 0)) ≤
        54 * (wz1Lemma23SnappedHeights graph.residue.cells).card *
          volume shading.union := by
    calc
      _ ≤ (54 * (wz1Lemma23SnappedHeights graph.residue.cells).card *
            (richCells.cells.card : ENNReal)) *
          volume (wz1PaperGridCube rho (0, 0, 0)) := by gcongr
      _ = 54 * (wz1Lemma23SnappedHeights graph.residue.cells).card *
          volume shading.union := by rw [hvolume]; ring
  have hgraphMass :
      ((rich.heightIndices.card * graph.residue.cells.card : ℕ) : ENNReal) *
          ((twoScale.fine.fineMultiplicity : ENNReal) *
            volume (wz1PaperGridCube rho (0, 0, 0))) ≤
        54 * (wz1Lemma23SnappedHeights graph.residue.cells).card *
          shading.mass := by
    calc
      _ = (twoScale.fine.fineMultiplicity : ENNReal) *
          (((rich.heightIndices.card * graph.residue.cells.card : ℕ) : ENNReal) *
            volume (wz1PaperGridCube rho (0, 0, 0))) := by ring
      _ ≤ (twoScale.fine.fineMultiplicity : ENNReal) *
          (54 * (wz1Lemma23SnappedHeights graph.residue.cells).card *
            volume shading.union) := by gcongr
      _ = 54 * (wz1Lemma23SnappedHeights graph.residue.cells).card *
          ((twoScale.fine.fineMultiplicity : ENNReal) *
            volume shading.union) := by ring
      _ ≤ 54 * (wz1Lemma23SnappedHeights graph.residue.cells).card *
          shading.mass := by
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

end Kakeya.Assouad

end
