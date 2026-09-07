import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleExactAlternativeA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.StickyMultiplicity
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.MultiplicityBounds

/-!
# Whole source cells covering the rich terminal height volume

The Alternative-A graph is used only to select a set of genuine height
layers.  Weight is measured by the actual union volume of `prep.shadow` in
those layers.  We then enlarge that real set to all literal source `delta`
cells that meet it.  The resulting paper shading is cubical, stays on the
original source family, and retains both the genuine union-volume lower bound
and a corresponding indexed-mass lower bound.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2TerminalExactRichHeightCellData
    {sigma inputLoss delta stickyLoss eta theoremEta epsilon : ℝ}
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
    {retained : PureWZ2TerminalBinRetainedShadingData residue}
    {sources : PureWZ2TerminalBinSourceFamily retained}
    {band : PureWZ2TerminalBinFixedBandSelection sources}
    {phase : PureWZ2TerminalBinHeightPhaseSelection band}
    {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
    {prep : PureWZ2TerminalBinExactGraphPreparation anchored}
    {graphParents : PureWZ2TerminalExactGraphParentData prep}
    {localCells : PureWZ2TerminalExactLocalCellData (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
    {sharp : PureWZ2TerminalExactSharpGeometry preparedGraph}
    {first : PureWZ2TerminalExactReadyGraph
      (theoremEta := theoremEta) sharp}
    {ready : PureWZ2TerminalExactRefinedReadyGraph first}
    (rich : PureWZ2TerminalExactAlternativeAHeightData ready epsilon) where
  heightIndices_subset :
    rich.heightIndices ⊆ preparedGraph.heightPopular.heightIndices
  richRegion : Set Point3 :=
    ⋃ heightIndex ∈ rich.heightIndices,
      wz1Lemma23HeightSlab delta heightIndex
  richRegion_eq : richRegion =
    ⋃ heightIndex ∈ rich.heightIndices,
      wz1Lemma23HeightSlab delta heightIndex
  richSet : Set Point3 := prep.shadow.union ∩ richRegion
  richSet_eq : richSet = prep.shadow.union ∩ richRegion
  richSet_measurable : MeasurableSet richSet
  richSet_volume_eq : volume richSet =
    ∑ heightIndex ∈ rich.heightIndices,
      volume (prep.shadow.union ∩
        wz1Lemma23HeightSlab delta heightIndex)
  richSet_volume_lower :
    (rich.heightIndices.card : ENNReal) *
        preparedGraph.heightPopular.layerMass ≤ volume richSet
  cells : Finset (ℤ × ℤ × ℤ)
  cells_subset : cells ⊆
    wz1PaperActiveCells retained.shading source.extremal.delta_pos
  cells_nonempty : cells.Nonempty
  cells_meet : ∀ cell ∈ cells,
    (richSet ∩ wz1PaperGridCube delta cell).Nonempty
  region : Set Point3 := wz2RetainedCellsUnion delta cells
  region_eq : region = wz2RetainedCellsUnion delta cells
  richSet_subset_region : richSet ⊆ region
  shading : WZ1PaperTubeShading source.family :=
    wz2RefinedShading retained.shading cells
  shading_eq : shading = wz2RefinedShading retained.shading cells
  carrier_eq : ∀ index, shading.carrier index =
    retained.shading.carrier index ∩ region
  subshading : PureWZ2PaperIsSubshading shading retained.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  union_eq : shading.union = region
  constant_multiplicity :
    shading.HasConstantMultiplicity
      terminalSource.multiplicity (2 * terminalSource.multiplicity)
  volume_lower :
    (rich.heightIndices.card : ENNReal) *
        preparedGraph.heightPopular.layerMass ≤ volume shading.union
  multiplicity_mass_lower :
    (terminalSource.multiplicity : ENNReal) * volume shading.union ≤
      shading.mass
  mass_lower : volume shading.union ≤ shading.mass
  point_near_rich_height : ∀ point ∈ shading.union,
    ∃ richPoint ∈ rich.richF,
      |point (2 : Fin 3) -
        (wz1Lemma23CellCenter delta (rich.pathFor richPoint).2.1) 2| <
          3 * delta / 2

private lemma pureWZ2_paperShading_volume_le_mass
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) :
    volume shading.union ≤ shading.mass := by
  have hunion : shading.union =
      ⋃ index : Fin family.card, shading.carrier index := by
    ext point
    constructor
    · rintro ⟨index, hpoint⟩
      exact Set.mem_iUnion.mpr ⟨index, hpoint⟩
    · intro hpoint
      rcases Set.mem_iUnion.mp hpoint with ⟨index, hindex⟩
      exact ⟨index, hindex⟩
  rw [hunion]
  calc
    volume (⋃ index : Fin family.card, shading.carrier index) ≤
        ∑' index : Fin family.card, volume (shading.carrier index) :=
      MeasureTheory.measure_iUnion_le _
    _ = ∑ index : Fin family.card, volume (shading.carrier index) := by
      rw [tsum_fintype]
    _ = shading.mass := rfl

theorem PureWZ2TerminalExactAlternativeAHeightData.toRichHeightCells
    {sigma inputLoss delta stickyLoss eta theoremEta epsilon : ℝ}
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
    {retained : PureWZ2TerminalBinRetainedShadingData residue}
    {sources : PureWZ2TerminalBinSourceFamily retained}
    {band : PureWZ2TerminalBinFixedBandSelection sources}
    {phase : PureWZ2TerminalBinHeightPhaseSelection band}
    {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
    {prep : PureWZ2TerminalBinExactGraphPreparation anchored}
    {graphParents : PureWZ2TerminalExactGraphParentData prep}
    {localCells : PureWZ2TerminalExactLocalCellData (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
    {sharp : PureWZ2TerminalExactSharpGeometry preparedGraph}
    {first : PureWZ2TerminalExactReadyGraph
      (theoremEta := theoremEta) sharp}
    {ready : PureWZ2TerminalExactRefinedReadyGraph first}
    (rich : PureWZ2TerminalExactAlternativeAHeightData ready epsilon) :
    Nonempty (PureWZ2TerminalExactRichHeightCellData rich) := by
  have hgraphRaw : preparedGraph.graph.residue.cells ⊆
      preparedGraph.rawResidue.cells := by
    rw [preparedGraph.graph_residue_eq]
    exact preparedGraph.popularResidue.cells_subset
  have hgraphPopular : ∀ cell ∈ preparedGraph.graph.residue.cells,
      cell.2.2 ∈ preparedGraph.heightPopular.heightIndices := by
    intro cell hcell
    have hrawCell : cell ∈ preparedGraph.rawResidue.cells := hgraphRaw hcell
    rw [preparedGraph.raw_residue_eq] at hrawCell
    exact preparedGraph.popularSource.cells_popular_height cell hrawCell
  have hheightSubset :
      rich.heightIndices ⊆ preparedGraph.heightPopular.heightIndices := by
    intro heightIndex hheightIndex
    rw [rich.heightIndices_eq] at hheightIndex
    rcases Finset.mem_image.mp hheightIndex with
      ⟨point, hpoint, hheightEq⟩
    have hpopular := hgraphPopular (rich.pathFor point).2.1
      (rich.cell_mem point hpoint)
    rwa [← rich.heightIndex_eq point hpoint, hheightEq] at hpopular
  let richRegion : Set Point3 :=
    ⋃ heightIndex ∈ rich.heightIndices,
      wz1Lemma23HeightSlab delta heightIndex
  have hregionMeas : MeasurableSet richRegion :=
    MeasurableSet.biUnion rich.heightIndices.finite_toSet.countable
      (fun heightIndex _ => by
        change MeasurableSet ((fun point : Point3 => point 2) ⁻¹'
          wz1Lemma23HeightInterval delta heightIndex)
        exact measurableSet_Ico.preimage
          (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).measurable)
  let richSet := prep.shadow.union ∩ richRegion
  have hrichSetMeas : MeasurableSet richSet :=
    (measurableSet_shading_union prep.shadow).inter hregionMeas
  have hpartition : richSet =
      ⋃ heightIndex ∈ rich.heightIndices,
        prep.shadow.union ∩
          wz1Lemma23HeightSlab delta heightIndex := by
    ext point
    simp only [richSet, richRegion, Set.mem_inter_iff, Set.mem_iUnion]
    constructor
    · rintro ⟨hshadow, heightIndex, hheightIndex, hslab⟩
      exact ⟨heightIndex, hheightIndex, hshadow, hslab⟩
    · rintro ⟨heightIndex, hheightIndex, hshadow, hslab⟩
      exact ⟨hshadow, heightIndex, hheightIndex, hslab⟩
  have hdisjoint : (rich.heightIndices : Set ℤ).PairwiseDisjoint
      (fun heightIndex => prep.shadow.union ∩
        wz1Lemma23HeightSlab delta heightIndex) := by
    intro firstHeight _ secondHeight _ hne
    exact (wz1Lemma23_heightSlab_disjoint
      source.extremal.delta_pos hne).mono
        Set.inter_subset_right Set.inter_subset_right
  have hmeas : ∀ heightIndex ∈ rich.heightIndices, MeasurableSet
      (prep.shadow.union ∩
        wz1Lemma23HeightSlab delta heightIndex) := by
    intro heightIndex _
    exact (measurableSet_shading_union prep.shadow).inter (by
      change MeasurableSet ((fun point : Point3 => point 2) ⁻¹'
        wz1Lemma23HeightInterval delta heightIndex)
      exact measurableSet_Ico.preimage
        (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).measurable)
  have hvolumeEq : volume richSet =
      ∑ heightIndex ∈ rich.heightIndices,
        volume (prep.shadow.union ∩
          wz1Lemma23HeightSlab delta heightIndex) := by
    rw [hpartition]
    exact MeasureTheory.measure_biUnion_finset hdisjoint hmeas
  have hvolumeLower :
      (rich.heightIndices.card : ENNReal) *
          preparedGraph.heightPopular.layerMass ≤ volume richSet := by
    rw [hvolumeEq]
    calc
      (rich.heightIndices.card : ENNReal) *
          preparedGraph.heightPopular.layerMass =
        ∑ _heightIndex ∈ rich.heightIndices,
          preparedGraph.heightPopular.layerMass := by
            simp [Finset.sum_const]
      _ ≤ ∑ heightIndex ∈ rich.heightIndices,
          volume (prep.shadow.union ∩
            wz1Lemma23HeightSlab delta heightIndex) := by
        apply Finset.sum_le_sum
        intro heightIndex hheightIndex
        exact (preparedGraph.heightPopular.layer_volume_band heightIndex
          (hheightSubset hheightIndex)).1
  let ambientCells :=
    wz1PaperActiveCells retained.shading source.extremal.delta_pos
  let cells := ambientCells.filter fun cell =>
    (richSet ∩ wz1PaperGridCube delta cell).Nonempty
  have hcellsSubset : cells ⊆ ambientCells := Finset.filter_subset _ _
  have hrichSetSubset : richSet ⊆ wz2RetainedCellsUnion delta cells := by
    intro point hpoint
    have hretainedPoint : point ∈ retained.shading.union := by
      have hshadow : point ∈ prep.shadow.union := hpoint.1
      have hambient := prep.subshading.union_subset hshadow
      rwa [prep.ambient_union] at hambient
    have hactiveUnion := retained.whole_cells.union_eq_activeCells
      source.extremal.delta_pos
    rw [hactiveUnion] at hretainedPoint
    rcases Set.mem_iUnion₂.mp hretainedPoint with
      ⟨cell, hcell, hpointCell⟩
    exact Set.mem_iUnion₂.mpr ⟨cell, Finset.mem_filter.mpr
      ⟨hcell, ⟨point, hpoint, hpointCell⟩⟩, hpointCell⟩
  have hcellsNonempty : cells.Nonempty := by
    have hpositive : 0 < volume richSet := by
      have hheightNonempty : rich.heightIndices.Nonempty := by
        rw [rich.heightIndices_eq]
        exact rich.richF_nonempty.image rich.heightIndex
      have hheightPositive : 0 < (rich.heightIndices.card : ENNReal) := by
        exact_mod_cast (Finset.card_pos.mpr hheightNonempty)
      have hproduct : 0 < (rich.heightIndices.card : ENNReal) *
          preparedGraph.heightPopular.layerMass := by
        exact ENNReal.mul_pos hheightPositive.ne'
          preparedGraph.heightPopular.layerMass_pos.ne'
      exact hproduct.trans_le hvolumeLower
    by_contra hempty
    have hcellsEmpty : cells = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hsubsetEmpty : richSet ⊆ (∅ : Set Point3) := by
      simpa [hcellsEmpty, wz2RetainedCellsUnion] using hrichSetSubset
    have hsetEmpty : richSet = ∅ := by
      exact Set.Subset.antisymm hsubsetEmpty (Set.empty_subset richSet)
    rw [hsetEmpty] at hpositive
    simpa using hpositive
  let region := wz2RetainedCellsUnion delta cells
  let shading := wz2RefinedShading retained.shading cells
  have hunion : shading.union = region := by
    exact wz2RefinedShading_union_eq retained.whole_cells
      source.extremal.delta_pos hcellsSubset
  have hfinalVolume :
      (rich.heightIndices.card : ENNReal) *
          preparedGraph.heightPopular.layerMass ≤ volume shading.union := by
    rw [hunion]
    exact hvolumeLower.trans (measure_mono hrichSetSubset)
  have hambientMultiplicity :
      retained.zeroExtension.ambientShading.HasConstantMultiplicity
        terminalSource.multiplicity (2 * terminalSource.multiplicity) :=
    retained.zeroExtension.constantMultiplicity (by
      rw [← terminalSource.shading_eq]
      exact terminalSource.constant_multiplicity)
  have hretainedMultiplicity :
      retained.shading.HasConstantMultiplicity
        terminalSource.multiplicity (2 * terminalSource.multiplicity) := by
    intro point hpoint
    have hmultiplicity := wholeCellRestriction_pointMultiplicity_eq
      (fun index => retained.carrier_eq index) hpoint
    rw [hmultiplicity]
    exact hambientMultiplicity point (by
      rcases hpoint with ⟨index, hindex⟩
      rw [retained.carrier_eq] at hindex
      exact ⟨index, hindex.1⟩)
  have hconstant : shading.HasConstantMultiplicity
      terminalSource.multiplicity (2 * terminalSource.multiplicity) := by
    intro point hpoint
    have hmultiplicity := wholeCellRestriction_pointMultiplicity_eq
      (fun index => show shading.carrier index =
        retained.shading.carrier index ∩ region from rfl) hpoint
    rw [hmultiplicity]
    exact hretainedMultiplicity point (by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, hindex.1⟩)
  have hpointNear : ∀ point ∈ shading.union,
      ∃ richPoint ∈ rich.richF,
        |point (2 : Fin 3) -
          (wz1Lemma23CellCenter delta (rich.pathFor richPoint).2.1) 2| <
            3 * delta / 2 := by
    intro point hpoint
    rw [hunion] at hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨cell, hcell, hpointCell⟩
    have hmeet := (Finset.mem_filter.mp hcell).2
    rcases hmeet with ⟨witness, hwitnessRich, hwitnessCell⟩
    rcases Set.mem_iUnion₂.mp hwitnessRich.2 with
      ⟨heightIndex, hheightIndex, hwitnessSlab⟩
    rw [rich.heightIndices_eq] at hheightIndex
    rcases Finset.mem_image.mp hheightIndex with
      ⟨richPoint, hrichPoint, hheightEq⟩
    refine ⟨richPoint, hrichPoint, ?_⟩
    have hpointWitness :
        |point (2 : Fin 3) - witness (2 : Fin 3)| < delta := by
      rw [wz1PaperGridCube_eq_Ico source.extremal.delta_pos cell]
        at hpointCell hwitnessCell
      rw [abs_lt]
      constructor <;>
        linarith [hpointCell.2.2.2.2.1, hpointCell.2.2.2.2.2,
          hwitnessCell.2.2.2.2.1, hwitnessCell.2.2.2.2.2]
    have hmesh : gridSide (delta / 2) = delta / Real.sqrt 3 := by
      simp [gridSide]
      ring
    have hsqrtThree : 1 < Real.sqrt (3 : ℝ) := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
        Real.sqrt_nonneg (3 : ℝ)]
    have hsideSmall : gridSide (delta / 2) < delta := by
      rw [hmesh]
      exact div_lt_self source.extremal.delta_pos hsqrtThree
    have hwitnessCenter :
        |witness (2 : Fin 3) -
          wz1Lemma23SnappedBaseHeight delta heightIndex| < delta / 2 := by
      change witness (2 : Fin 3) ∈
        wz1Lemma23HeightInterval delta heightIndex at hwitnessSlab
      rw [wz1Lemma23HeightInterval] at hwitnessSlab
      have hcenterFormula :
          wz1Lemma23SnappedBaseHeight delta heightIndex =
            (heightIndex : ℝ) * gridSide (delta / 2) +
              gridSide (delta / 2) / 2 := by
        simp [wz1Lemma23SnappedBaseHeight]
        ring
      rw [hcenterFormula, abs_lt]
      rcases hwitnessSlab with ⟨hlower, hupper⟩
      constructor <;> linarith
    have hcenterEq :
        (wz1Lemma23CellCenter delta (rich.pathFor richPoint).2.1) 2 =
          wz1Lemma23SnappedBaseHeight delta heightIndex := by
      simp [wz1Lemma23CellCenter, wz1Lemma23SnappedBaseHeight, point3,
        ← hheightEq, rich.heightIndex_eq richPoint hrichPoint]
    rw [hcenterEq]
    have htriangle := abs_sub_le (point (2 : Fin 3))
      (witness (2 : Fin 3))
      (wz1Lemma23SnappedBaseHeight delta heightIndex)
    linarith
  exact ⟨{
    heightIndices_subset := hheightSubset
    richRegion := richRegion
    richRegion_eq := rfl
    richSet := richSet
    richSet_eq := rfl
    richSet_measurable := hrichSetMeas
    richSet_volume_eq := hvolumeEq
    richSet_volume_lower := hvolumeLower
    cells := cells
    cells_subset := hcellsSubset
    cells_nonempty := hcellsNonempty
    cells_meet := by
      intro cell hcell
      exact (Finset.mem_filter.mp hcell).2
    region := region
    region_eq := rfl
    richSet_subset_region := hrichSetSubset
    shading := shading
    shading_eq := rfl
    carrier_eq := by intro index; rfl
    subshading := wz2RefinedShading_subshading
    whole_cells := wz2RefinedShading_cubical retained.whole_cells
    union_eq := hunion
    constant_multiplicity := hconstant
    volume_lower := hfinalVolume
    multiplicity_mass_lower :=
      (constant_multiplicity_mass_volume_generic hconstant).1
    mass_lower := pureWZ2_paperShading_volume_le_mass shading
    point_near_rich_height := hpointNear }⟩

end Kakeya.Assouad
