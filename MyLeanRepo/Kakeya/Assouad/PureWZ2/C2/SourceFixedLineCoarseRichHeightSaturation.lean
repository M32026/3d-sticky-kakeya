import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseRichPipeline
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers

/-!
# Whole-cell saturation of the genuine-coarse rich height set

The internal height popularity in the genuine-coarse Lemma-23 graph is
measured by three-dimensional union volume.  After Alternative A chooses
`Z_lin`, we retain every genuine side-`rho` cell meeting those selected
height slabs.  This loses no union volume and makes the selected region
eligible for the exact first-balanced-cover pullback.

The resulting source pullback is contained in the existing source-family
height lift.  Thus its exact `mass_cross` identity can be used for the final
mass estimate without identifying a graph cell with a source cell and without
requiring the false exact inclusion into the outer source-popular heights.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Saturate the genuine-coarse part of the selected internal height layers
by complete first-sticky `rho` cells, then pull that region back to the
original source family. -/
structure PureWZ2SourceFixedBinCoarseRichHeightSaturationData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta : ℝ}
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
    {pipeline : PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
      (normalEta := normalEta) prep}
    {richOutput : PureWZ2SourceFixedBinCoarseRichPipelineAtPreparationData
      (finalLoss := finalLoss) (theoremEta := theoremEta) pipeline}
    (heightLift : PureWZ2SourceFixedBinCoarseHeightLift
      richOutput.richTrapezoid) where
  heightIndices_subset : richOutput.rich.heightIndices ⊆
    pipeline.preparedGraph.heightPopular.heightIndices
  richRegion : Set Point3 :=
    ⋃ heightIndex ∈ richOutput.rich.heightIndices,
      wz1Lemma23HeightSlab prep.graphScale heightIndex
  richRegion_eq : richRegion =
    ⋃ heightIndex ∈ richOutput.rich.heightIndices,
      wz1Lemma23HeightSlab prep.graphScale heightIndex
  richSet : Set Point3 := prep.shadow.union ∩ richRegion
  richSet_eq : richSet = prep.shadow.union ∩ richRegion
  richSet_measurable : MeasurableSet richSet
  richSet_volume_eq : volume richSet =
    ∑ heightIndex ∈ richOutput.rich.heightIndices,
      volume (prep.shadow.union ∩
        wz1Lemma23HeightSlab prep.graphScale heightIndex)
  richSet_volume_lower :
    (richOutput.rich.heightIndices.card : ENNReal) *
        pipeline.preparedGraph.heightPopular.layerMass ≤ volume richSet
  cells : Finset (ℤ × ℤ × ℤ)
  cells_subset : cells ⊆ wz1PaperActiveCells carrier.shading
    twoScale.coarseGrains.extremal.delta_pos
  cells_nonempty : cells.Nonempty
  cells_meet : ∀ cell ∈ cells,
    (richSet ∩ wz1PaperGridCube rho cell).Nonempty
  region : Set Point3 :=
    wz2RetainedCellsUnion twoScale.rhoRequested.1 cells
  region_eq : region =
    wz2RetainedCellsUnion twoScale.rhoRequested.1 cells
  richSet_subset_region : richSet ⊆ region
  shading : WZ1PaperTubeShading twoScale.coarse.coarse :=
    wz2RefinedShading carrier.shading cells
  shading_eq : shading = wz2RefinedShading carrier.shading cells
  carrier_eq : ∀ index, shading.carrier index =
    carrier.shading.carrier index ∩ region
  subshading : PureWZ2PaperIsSubshading
    shading twoScale.coarseGrains.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  union_eq : shading.union = region
  volume_lower :
    (richOutput.rich.heightIndices.card : ENNReal) *
        pipeline.preparedGraph.heightPopular.layerMass ≤ volume shading.union
  sourcePullback : PureWZ2SelectedCoarseRegionSourcePullbackData shading
  sourcePullback_sub_heightLift :
    PureWZ2PaperIsSubshading sourcePullback.shading heightLift.shading
  sourcePullback_mass_le : sourcePullback.shading.mass ≤ heightLift.shading.mass
  mass_cube_lower :
    ((richOutput.rich.heightIndices.card : ENNReal) *
        pipeline.preparedGraph.heightPopular.layerMass) *
          twoScale.coarse.balanced.incidenceMass ≤
      heightLift.shading.mass *
        volume (wz1PaperGridCube rho (0, 0, 0))
  mass_cross_lower :
    ((richOutput.rich.heightIndices.card : ENNReal) *
        pipeline.preparedGraph.heightPopular.layerMass) *
          twoScale.coarse.refined.mass ≤
      heightLift.shading.mass *
        volume twoScale.coarse.croppedCoarseShading.union

namespace PureWZ2SourceFixedBinCoarseRichPipelineAtPreparationData

/-- Construct the whole-cell saturation and its exact source pullback from the
same dependent rich pipeline. -/
theorem toRichHeightSaturation
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta : ℝ}
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
    {pipeline : PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
      (normalEta := normalEta) prep}
    (richOutput : PureWZ2SourceFixedBinCoarseRichPipelineAtPreparationData
      (finalLoss := finalLoss) (theoremEta := theoremEta) pipeline) :
    Nonempty (PureWZ2SourceFixedBinCoarseRichHeightSaturationData
      richOutput.heightLift) := by
  let rich := richOutput.rich
  let preparedGraph := pipeline.preparedGraph
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
  have hheightSubset : rich.heightIndices ⊆
      preparedGraph.heightPopular.heightIndices := by
    intro heightIndex hheightIndex
    rw [rich.heightIndices_eq] at hheightIndex
    rcases Finset.mem_image.mp hheightIndex with
      ⟨point, hpoint, hheightEq⟩
    have hpopular := hgraphPopular (rich.pathFor point).2.1
      (rich.cell_mem point hpoint)
    rwa [← rich.heightIndex_eq point hpoint, hheightEq] at hpopular
  let richRegion : Set Point3 :=
    ⋃ heightIndex ∈ rich.heightIndices,
      wz1Lemma23HeightSlab prep.graphScale heightIndex
  have hregionMeas : MeasurableSet richRegion :=
    MeasurableSet.biUnion rich.heightIndices.finite_toSet.countable
      (fun heightIndex _ => by
        change MeasurableSet ((fun point : Point3 => point 2) ⁻¹'
          wz1Lemma23HeightInterval prep.graphScale heightIndex)
        exact measurableSet_Ico.preimage
          (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).measurable)
  let richSet : Set Point3 := prep.shadow.union ∩ richRegion
  have hrichSetMeas : MeasurableSet richSet :=
    (measurableSet_shading_union prep.shadow).inter hregionMeas
  have hpartition : richSet =
      ⋃ heightIndex ∈ rich.heightIndices,
        prep.shadow.union ∩
          wz1Lemma23HeightSlab prep.graphScale heightIndex := by
    ext point
    simp only [richSet, richRegion, Set.mem_inter_iff, Set.mem_iUnion]
    constructor
    · rintro ⟨hshadow, heightIndex, hheightIndex, hslab⟩
      exact ⟨heightIndex, hheightIndex, hshadow, hslab⟩
    · rintro ⟨heightIndex, hheightIndex, hshadow, hslab⟩
      exact ⟨hshadow, heightIndex, hheightIndex, hslab⟩
  have hvolumeEq : volume richSet =
      ∑ heightIndex ∈ rich.heightIndices,
        volume (prep.shadow.union ∩
          wz1Lemma23HeightSlab prep.graphScale heightIndex) := by
    rw [hpartition]
    apply MeasureTheory.measure_biUnion_finset
    · intro first _ second _ hne
      exact (wz1Lemma23_heightSlab_disjoint prep.graphScale_pos hne).mono
        Set.inter_subset_right Set.inter_subset_right
    · intro heightIndex _
      exact (measurableSet_shading_union prep.shadow).inter (by
        change MeasurableSet ((fun point : Point3 => point 2) ⁻¹'
          wz1Lemma23HeightInterval prep.graphScale heightIndex)
        exact measurableSet_Ico.preimage
          (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).measurable)
  have hrichSetVolume :
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
            wz1Lemma23HeightSlab prep.graphScale heightIndex) := by
        exact Finset.sum_le_sum fun heightIndex hheightIndex =>
          (preparedGraph.heightPopular.layer_volume_band heightIndex
            (hheightSubset hheightIndex)).1
  let ambientCells := wz1PaperActiveCells carrier.shading
    twoScale.coarseGrains.extremal.delta_pos
  let cells := ambientCells.filter fun cell =>
    (richSet ∩ wz1PaperGridCube rho cell).Nonempty
  have hcellsSubset : cells ⊆ ambientCells := Finset.filter_subset _ _
  have hrichSetSubset : richSet ⊆
      wz2RetainedCellsUnion twoScale.rhoRequested.1 cells := by
    intro point hpoint
    have hcarrierPoint : point ∈ carrier.shading.union :=
      prep.shadow_union_subset hpoint.1
    have hactiveUnion := carrier.whole_cells.union_eq_activeCells
      twoScale.coarseGrains.extremal.delta_pos
    rw [hactiveUnion] at hcarrierPoint
    rcases Set.mem_iUnion₂.mp hcarrierPoint with
      ⟨cell, hcell, hpointCell⟩
    have hpointCellRho : point ∈ wz1PaperGridCube rho cell := by
      simpa only [twoScale.rhoRequested_eq] using hpointCell
    exact Set.mem_iUnion₂.mpr ⟨cell, Finset.mem_filter.mpr
      ⟨hcell, ⟨point, hpoint, hpointCellRho⟩⟩, hpointCell⟩
  have hcellsNonempty : cells.Nonempty := by
    have hheightNonempty : rich.heightIndices.Nonempty := by
      rw [rich.heightIndices_eq]
      exact rich.richF_nonempty.image rich.heightIndex
    have hheightPositive : 0 < (rich.heightIndices.card : ENNReal) := by
      exact_mod_cast hheightNonempty.card_pos
    have hsetPositive : 0 < volume richSet :=
      (ENNReal.mul_pos hheightPositive.ne'
        preparedGraph.heightPopular.layerMass_pos.ne').trans_le hrichSetVolume
    by_contra hempty
    have hcellsEmpty : cells = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hsubsetEmpty : richSet ⊆ (∅ : Set Point3) := by
      simpa [hcellsEmpty, wz2RetainedCellsUnion] using hrichSetSubset
    have hsetEmpty : richSet = ∅ :=
      Set.Subset.antisymm hsubsetEmpty (Set.empty_subset richSet)
    rw [hsetEmpty] at hsetPositive
    simpa using hsetPositive
  let region := wz2RetainedCellsUnion twoScale.rhoRequested.1 cells
  let shading := wz2RefinedShading carrier.shading cells
  have hunion : shading.union = region := by
    exact wz2RefinedShading_union_eq carrier.whole_cells
      twoScale.coarseGrains.extremal.delta_pos hcellsSubset
  have hsubCarrier : PureWZ2PaperIsSubshading shading carrier.shading :=
    wz2RefinedShading_subshading
  have hsub : PureWZ2PaperIsSubshading
      shading twoScale.coarseGrains.shading := by
    intro index point hpoint
    exact carrier.subshading index (hsubCarrier index hpoint)
  have hwhole : WZ1PaperIsCubicalShading shading :=
    wz2RefinedShading_cubical carrier.whole_cells
  have hvolumeLower :
      (rich.heightIndices.card : ENNReal) *
          preparedGraph.heightPopular.layerMass ≤ volume shading.union := by
    rw [hunion]
    exact hrichSetVolume.trans (measure_mono hrichSetSubset)
  rcases pureWZ2_pullback_selected_coarse_region shading hsub hwhole with
    ⟨sourcePullback⟩
  have hlineWindow : line.lineHeight ∈ Set.Ico
      (window.left - rho)
      (window.left + Real.sqrt rho + rho) := by
    have hraw := window.union_height_window
      line.lineAnchor line.lineAnchor_mem
    rw [line.lineAnchor_height] at hraw
    exact hraw
  let firstParent := Classical.choose residue.selected_nonempty
  have hfirstParent : firstParent ∈ residue.selected :=
    Classical.choose_spec residue.selected_nonempty
  have hlineParent : line.lineHeight ∈ Set.Ico
      ((carrier.commonParentHeight : ℝ) * twoScale.sqrtRequested.1)
      (((carrier.commonParentHeight : ℝ) + 1) *
        twoScale.sqrtRequested.1) := by
    rcases selection.selected_hit firstParent
        (residue.selected_subset hfirstParent) with
      ⟨cell, hcell, hcellParent⟩
    have hpointParent := parents.representative_mem_parent cell hcell
    rw [hcellParent, wz1PaperGridCube_eq_Ico
      twoScale.fine.coarse_extremal.delta_pos firstParent] at hpointParent
    have hheight := line.representative_height cell hcell
    have hparentHeight := carrier.parent_height_eq firstParent hfirstParent
    rw [hparentHeight] at hpointParent
    have hzParent : (line.representative cell) (2 : Fin 3) ∈
        Set.Ico
          ((carrier.commonParentHeight : ℝ) * twoScale.sqrtRequested.1)
          (((carrier.commonParentHeight : ℝ) + 1) *
            twoScale.sqrtRequested.1) :=
      ⟨hpointParent.2.2.2.2.1, hpointParent.2.2.2.2.2⟩
    rwa [hheight] at hzParent
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hrhoRoot : rho ≤ Real.sqrt rho := by
    nlinarith [Real.sqrt_nonneg rho, Real.sq_sqrt line.rho_pos.le]
  have hcarrierWindow : ∀ point ∈ carrier.shading.union,
      point 2 ∈ Set.Icc
        (window.left - 2 * Real.sqrt rho)
        (window.left + 3 * Real.sqrt rho) := by
    intro point hpoint
    have hparent := carrier.union_height point hpoint
    have hleftGap : line.lineHeight - Real.sqrt rho ≤ point 2 := by
      rw [← twoScale.sqrtRequested_eq]
      nlinarith [hlineParent.2, hparent.1]
    have hrightGap : point 2 ≤ line.lineHeight + Real.sqrt rho := by
      rw [← twoScale.sqrtRequested_eq]
      nlinarith [hlineParent.1, hparent.2]
    constructor <;> nlinarith [hlineWindow.1, hlineWindow.2]
  have hpullbackSub : PureWZ2PaperIsSubshading
      sourcePullback.shading richOutput.heightLift.shading := by
    intro index point hpoint
    have hsource : point ∈ source.shading.carrier index :=
      sourcePullback.subshading index hpoint
    have hsourceUnion : point ∈ source.shading.union := ⟨index, hsource⟩
    rw [source.cubical.union_eq_activeCells source.extremal.delta_pos]
      at hsourceUnion
    rcases Set.mem_iUnion₂.mp hsourceUnion with
      ⟨sourceCell, hsourceCell, hpointSourceCell⟩
    have hcondition : ∀ other ∈ wz1PaperGridCube delta sourceCell,
        other 2 ∈ richOutput.richTrapezoid.trapezoid.core ∧
          ∃ heightIndex ∈ rich.heightIndices,
            |other 2 - wz1Lemma23SnappedBaseHeight
              prep.graphScale heightIndex| ≤ prep.graphScale := by
      intro other hother
      have hcellEq : sourceCell = wz1PaperGridIndex delta point :=
        (mem_wz1PaperGridCube delta sourceCell point).mp
          hpointSourceCell |>.symm
      have hotherCanonical : other ∈
          wz1PaperGridCube delta (wz1PaperGridIndex delta point) := by
        rwa [← hcellEq]
      have hotherPullback : other ∈ sourcePullback.shading.carrier index :=
        sourcePullback.whole_cells index point hpoint hotherCanonical
      have hotherUnion : other ∈ sourcePullback.shading.union :=
        ⟨index, hotherPullback⟩
      have hotherSelected : other ∈ shading.union := by
        rw [sourcePullback.union_eq] at hotherUnion
        rw [sourcePullback.selectedRegion_eq_coarse] at hotherUnion
        exact hotherUnion.2
      have hotherCarrier : other ∈ carrier.shading.union :=
        hsubCarrier.union_subset hotherSelected
      have hcore : other 2 ∈
          richOutput.richTrapezoid.trapezoid.core := by
        apply richOutput.richTrapezoid.height_window_coverage
        exact hcarrierWindow other hotherCarrier
      rw [hunion] at hotherSelected
      rcases Set.mem_iUnion₂.mp hotherSelected with
        ⟨coarseCell, hcoarseCell, hotherCoarseCell⟩
      have hmeet := (Finset.mem_filter.mp hcoarseCell).2
      rcases hmeet with
        ⟨witness, ⟨hwitnessShadow, hwitnessRegion⟩, hwitnessCell⟩
      rcases Set.mem_iUnion₂.mp hwitnessRegion with
        ⟨heightIndex, hheightIndex, hwitnessSlab⟩
      have hsameCell :
          |other 2 - witness 2| < rho := by
        have hotherCellRho : other ∈ wz1PaperGridCube rho coarseCell := by
          simpa only [twoScale.rhoRequested_eq] using hotherCoarseCell
        rw [wz1PaperGridCube_eq_Ico line.rho_pos coarseCell]
          at hotherCellRho hwitnessCell
        rw [abs_lt]
        constructor <;>
          linarith [hotherCellRho.2.2.2.2.1,
            hotherCellRho.2.2.2.2.2, hwitnessCell.2.2.2.2.1,
            hwitnessCell.2.2.2.2.2]
      have hwitnessClose :
          |witness 2 - wz1Lemma23SnappedBaseHeight
            prep.graphScale heightIndex| ≤ prep.graphScale / 2 := by
        change witness 2 ∈ wz1Lemma23HeightInterval
          prep.graphScale heightIndex at hwitnessSlab
        rw [wz1Lemma23HeightInterval] at hwitnessSlab
        have hside : gridSide (prep.graphScale / 2) =
            prep.graphScale / Real.sqrt 3 := by
          simp [gridSide]
          ring
        rw [hside] at hwitnessSlab
        have hden : (2 : ℝ) ≤ 2 * Real.sqrt 3 := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
            Real.sqrt_nonneg (3 : ℝ)]
        have hhalf : prep.graphScale / (2 * Real.sqrt 3) ≤
            prep.graphScale / 2 :=
          div_le_div_of_nonneg_left prep.graphScale_pos.le (by norm_num) hden
        have hcenterLower :
            (heightIndex : ℝ) * (prep.graphScale / Real.sqrt 3) -
                ((heightIndex : ℝ) + 1 / 2) *
                  (prep.graphScale / Real.sqrt 3) =
              -(prep.graphScale / (2 * Real.sqrt 3)) := by ring
        have hcenterUpper :
            ((heightIndex : ℝ) + 1) *
                (prep.graphScale / Real.sqrt 3) -
              ((heightIndex : ℝ) + 1 / 2) *
                (prep.graphScale / Real.sqrt 3) =
              prep.graphScale / (2 * Real.sqrt 3) := by ring
        rw [wz1Lemma23SnappedBaseHeight, hside, abs_le]
        constructor
        · linarith [hwitnessSlab.1, hhalf, hcenterLower]
        · linarith [hwitnessSlab.2, hhalf, hcenterUpper]
      have hrhoHalf : rho ≤ prep.graphScale / 2 := by
        rw [prep.graphScale_eq]
        nlinarith [line.rho_pos]
      have hclose : |other 2 - wz1Lemma23SnappedBaseHeight
          prep.graphScale heightIndex| ≤ prep.graphScale := by
        calc
          _ ≤ |other 2 - witness 2| +
              |witness 2 - wz1Lemma23SnappedBaseHeight
                prep.graphScale heightIndex| := abs_sub_le _ _ _
          _ ≤ rho + prep.graphScale / 2 := by
            exact add_le_add hsameCell.le hwitnessClose
          _ ≤ prep.graphScale := by linarith
      exact ⟨hcore, heightIndex, hheightIndex, hclose⟩
    have hheightCell : sourceCell ∈ richOutput.heightLift.heightCells := by
      rw [richOutput.heightLift.heightCells_eq]
      exact Finset.mem_filter.mpr ⟨hsourceCell, hcondition⟩
    rw [richOutput.heightLift.carrier_eq]
    refine ⟨hsource, ?_⟩
    rw [richOutput.heightLift.region_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨sourceCell, hheightCell, hpointSourceCell⟩
  have hpullbackMass : sourcePullback.shading.mass ≤
      richOutput.heightLift.shading.mass := by
    apply Finset.sum_le_sum
    intro index _
    exact measure_mono (hpullbackSub index)
  have hpullbackCube : volume shading.union *
        twoScale.coarse.balanced.incidenceMass =
      sourcePullback.shading.mass *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
    calc
      volume shading.union * twoScale.coarse.balanced.incidenceMass =
          volume sourcePullback.selectedRegion *
            twoScale.coarse.balanced.incidenceMass := by
        rw [sourcePullback.selectedRegion_eq_coarse]
      _ = ((sourcePullback.selectedCells.card : ENNReal) *
            volume (wz1PaperGridCube rho (0, 0, 0))) *
          twoScale.coarse.balanced.incidenceMass := by
        rw [sourcePullback.coarse_region_volume_eq]
      _ = ((sourcePullback.selectedCells.card : ENNReal) *
            twoScale.coarse.balanced.incidenceMass) *
          volume (wz1PaperGridCube rho (0, 0, 0)) := by ring
      _ = sourcePullback.shading.mass *
          volume (wz1PaperGridCube rho (0, 0, 0)) := by
        rw [sourcePullback.mass_eq]
  have hmassCubeLower :
      ((rich.heightIndices.card : ENNReal) *
          preparedGraph.heightPopular.layerMass) *
            twoScale.coarse.balanced.incidenceMass ≤
        richOutput.heightLift.shading.mass *
          volume (wz1PaperGridCube rho (0, 0, 0)) := by
    calc
      _ ≤ volume shading.union *
          twoScale.coarse.balanced.incidenceMass := by gcongr
      _ = sourcePullback.shading.mass *
          volume (wz1PaperGridCube rho (0, 0, 0)) := hpullbackCube
      _ ≤ richOutput.heightLift.shading.mass *
          volume (wz1PaperGridCube rho (0, 0, 0)) := by gcongr
  have hmassCrossLower :
      ((rich.heightIndices.card : ENNReal) *
          preparedGraph.heightPopular.layerMass) *
            twoScale.coarse.refined.mass ≤
        richOutput.heightLift.shading.mass *
          volume twoScale.coarse.croppedCoarseShading.union := by
    calc
      _ ≤ volume shading.union * twoScale.coarse.refined.mass := by gcongr
      _ = sourcePullback.shading.mass *
          volume twoScale.coarse.croppedCoarseShading.union := by
        rw [sourcePullback.mass_cross]
        rw [sourcePullback.selectedRegion_eq_coarse]
      _ ≤ richOutput.heightLift.shading.mass *
          volume twoScale.coarse.croppedCoarseShading.union := by gcongr
  exact ⟨{
    heightIndices_subset := hheightSubset
    richRegion := richRegion
    richRegion_eq := rfl
    richSet := richSet
    richSet_eq := rfl
    richSet_measurable := hrichSetMeas
    richSet_volume_eq := hvolumeEq
    richSet_volume_lower := hrichSetVolume
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
    subshading := hsub
    whole_cells := hwhole
    union_eq := hunion
    volume_lower := hvolumeLower
    sourcePullback := sourcePullback
    sourcePullback_sub_heightLift := hpullbackSub
    sourcePullback_mass_le := hpullbackMass
    mass_cube_lower := hmassCubeLower
    mass_cross_lower := hmassCrossLower
  }⟩

end PureWZ2SourceFixedBinCoarseRichPipelineAtPreparationData

namespace PureWZ2SourceFixedBinCoarseRichHeightSaturationData

/-- The internal popular-height count is bounded by the common graph-window
height cap. -/
theorem popular_heights_le_cap
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta : ℝ}
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
    {pipeline : PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
      (normalEta := normalEta) prep}
    {richOutput : PureWZ2SourceFixedBinCoarseRichPipelineAtPreparationData
      (finalLoss := finalLoss) (theoremEta := theoremEta) pipeline}
    (saturation : PureWZ2SourceFixedBinCoarseRichHeightSaturationData
      richOutput.heightLift) :
    (pipeline.preparedGraph.heightPopular.heightIndices.card : ENNReal) ≤
      PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho := by
  have hsubset : pipeline.preparedGraph.heightPopular.heightIndices ⊆
      wz1Lemma23SnappedHeights prep.windowed.global.cells := by
    intro heightIndex hheight
    have hglobal : heightIndex ∈ prep.windowed.global.heightIndices := by
      rw [prep.windowed.global.heightIndices_eq]
      exact pipeline.preparedGraph.heightPopular.heightIndices_subset hheight
    have hlayerNonempty :
        (prep.windowed.global.layerCells heightIndex).Nonempty := by
      have hlayerPos : 0 < volume (prep.shadow.union ∩
          wz1Lemma23HeightSlab prep.graphScale heightIndex) :=
        pipeline.preparedGraph.heightPopular.layerMass_pos.trans_le
          (pipeline.preparedGraph.heightPopular.layer_volume_band
            heightIndex hheight).1
      by_contra hempty
      have hlayerEmpty := Finset.not_nonempty_iff_eq_empty.mp hempty
      have hbound := prep.windowed.global.layer_volume_bound
        heightIndex hglobal
      have harea := wz1_lemma23_exactSlice_area_le_two prep.shadow
        prep.graphScale_pos
        (by
          intro point hpoint
          have hcarrier : point ∈ carrier.shading.union :=
            prep.shadow_union_subset hpoint
          have hcoarse := carrier.subshading.union_subset hcarrier
          have hnorm := norm_le_two_of_mem_paperShading hcoarse
          simpa [Metric.mem_closedBall, dist_zero_right] using hnorm)
        (prep.windowed.global.selectedHeight heightIndex)
      rw [← prep.windowed.global.layerCells_eq heightIndex, hlayerEmpty]
        at harea
      norm_num at harea
      have hsidePos : 0 < ENNReal.ofReal
          (gridSide (prep.graphScale / 2)) := by
        apply ENNReal.ofReal_pos.mpr
        dsimp [gridSide]
        apply div_pos
        · nlinarith [prep.graphScale_pos]
        · exact Real.sqrt_pos.mpr (by norm_num)
      have hzero : volume (prep.shadow.union ∩
          wz1Lemma23HeightSlab prep.graphScale heightIndex) = 0 := by
        apply le_zero_iff.mp
        have hdiv : volume (prep.shadow.union ∩
              wz1Lemma23HeightSlab prep.graphScale heightIndex) /
              ENNReal.ofReal (gridSide (prep.graphScale / 2)) ≤ 0 :=
          hbound.trans harea.le
        have hmul := (ENNReal.div_le_iff hsidePos.ne'
          ENNReal.ofReal_ne_top).mp hdiv
        simpa using hmul
      exact (ne_of_gt hlayerPos) hzero
    rcases hlayerNonempty with ⟨cell, hcell⟩
    have hcellGlobal : cell ∈ prep.windowed.global.cells := by
      rw [prep.windowed.global.cells_eq]
      exact Finset.mem_biUnion.mpr ⟨heightIndex, hglobal, hcell⟩
    exact Finset.mem_image.mpr
      ⟨cell, hcellGlobal, prep.windowed.global.layer_height
        heightIndex hglobal cell hcell⟩
  have hreal := wz1Lemma23_height_layer_count
    prep.graphScale_pos prep.graphScale_one prep.windowed.global_cells_window
  have hcardReal :
      (pipeline.preparedGraph.heightPopular.heightIndices.card : ℝ) ≤
        3 / Real.sqrt prep.graphScale := by
    have hcast :
        (pipeline.preparedGraph.heightPopular.heightIndices.card : ℝ) ≤
          ((wz1Lemma23SnappedHeights
            prep.windowed.global.cells).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    exact hcast.trans hreal
  have henn := ENNReal.natCast_le_ofReal
    pipeline.preparedGraph.heightPopular.heightIndices_nonempty.card_ne_zero
      |>.mpr hcardReal
  simpa [PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap,
    prep.graphScale_eq] using henn

/-- The complete `Z_lin` height saturation converts the genuine graph volume
to source indexed mass by the first balanced cover's exact cross identity. -/
theorem graph_height_mass_cross_bound
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta extraLoss : ℝ}
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
    {pipeline : PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
      (normalEta := normalEta) prep}
    {richOutput : PureWZ2SourceFixedBinCoarseRichPipelineAtPreparationData
      (finalLoss := finalLoss) (theoremEta := theoremEta) pipeline}
    (saturation : PureWZ2SourceFixedBinCoarseRichHeightSaturationData
      richOutput.heightLift)
    (hextraPower :
      (pipeline.preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow prep.graphScale (-extraLoss)) :
    volume prep.shadow.union *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.refined.mass ≤
      PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss * richOutput.heightLift.shading.mass *
        volume twoScale.coarse.croppedCoarseShading.union := by
  let rich := richOutput.rich
  let heightPopular := pipeline.preparedGraph.heightPopular
  let floor := pureWZ2SourceHorizontalRichFloor rho finalLoss
  have hpopular : volume prep.shadow.union ≤
      2 * heightPopular.bins * volume heightPopular.shading.union := by
    have h := (ENNReal.div_le_iff (by norm_num) (by norm_num)).mp
      heightPopular.retained_volume
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hfloor : floor ≤ (rich.heightIndices.card : ENNReal) := by
    have hfloorEq : floor = Kakeya.realRpowENN
        richOutput.ready.ready.deltaGraph (finalLoss - 1) := by
      dsimp only [floor]
      unfold pureWZ2SourceHorizontalRichFloor
      rw [richOutput.ready.ready.deltaGraph_eq, prep.graphScale_eq]
    rw [hfloorEq]
    simpa [rich.heightIndices_card] using rich.richF_card
  have hpopularLayer : volume heightPopular.shading.union ≤
      2 * (heightPopular.heightIndices.card : ENNReal) *
        heightPopular.layerMass := by
    rw [heightPopular.volume_eq_sum]
    calc
      (∑ heightIndex ∈ heightPopular.heightIndices,
          volume (prep.shadow.union ∩
            wz1Lemma23HeightSlab prep.graphScale heightIndex)) ≤
        ∑ _heightIndex ∈ heightPopular.heightIndices,
          2 * heightPopular.layerMass := by
        exact Finset.sum_le_sum fun heightIndex hheight =>
          (heightPopular.layer_volume_band heightIndex hheight).2
      _ = 2 * (heightPopular.heightIndices.card : ENNReal) *
          heightPopular.layerMass := by
        simp [Finset.sum_const]
        ring
  have hweighted : floor * volume prep.shadow.union *
        twoScale.coarse.refined.mass ≤
      4 * heightPopular.bins *
        (heightPopular.heightIndices.card : ENNReal) *
          (richOutput.heightLift.shading.mass *
            volume twoScale.coarse.croppedCoarseShading.union) := by
    calc
      _ ≤ floor * (2 * heightPopular.bins *
          volume heightPopular.shading.union) *
            twoScale.coarse.refined.mass := by gcongr
      _ ≤ floor * (2 * heightPopular.bins *
          (2 * (heightPopular.heightIndices.card : ENNReal) *
            heightPopular.layerMass)) *
              twoScale.coarse.refined.mass := by gcongr
      _ ≤ (rich.heightIndices.card : ENNReal) *
          (2 * heightPopular.bins *
            (2 * (heightPopular.heightIndices.card : ENNReal) *
              heightPopular.layerMass)) *
                twoScale.coarse.refined.mass := by gcongr
      _ = 4 * heightPopular.bins *
          (heightPopular.heightIndices.card : ENNReal) *
            (((rich.heightIndices.card : ENNReal) *
              heightPopular.layerMass) *
                twoScale.coarse.refined.mass) := by ring
      _ ≤ 4 * heightPopular.bins *
          (heightPopular.heightIndices.card : ENNReal) *
            (richOutput.heightLift.shading.mass *
              volume twoScale.coarse.croppedCoarseShading.union) := by
        exact mul_le_mul_left' (by
          simpa [rich, heightPopular] using saturation.mass_cross_lower)
          (4 * heightPopular.bins *
            (heightPopular.heightIndices.card : ENNReal))
  have hbinsNat : 4 * heightPopular.bins ≤
      2 * pipeline.preparedGraph.graph.residue.extraCost := by
    rw [pipeline.preparedGraph.extraCost_eq]
    nlinarith
  have hbinsENN : (4 * heightPopular.bins : ENNReal) ≤
      2 * (pipeline.preparedGraph.graph.residue.extraCost : ENNReal) := by
    exact_mod_cast hbinsNat
  have hextraENN :
      (pipeline.preparedGraph.graph.residue.extraCost : ENNReal) ≤
        ENNReal.ofReal (Real.rpow prep.graphScale (-extraLoss)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hextraPower
  have hheight := saturation.popular_heights_le_cap
  have hcost :
      (4 * heightPopular.bins : ENNReal) *
          (heightPopular.heightIndices.card : ENNReal) ≤
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss := by
    calc
      _ ≤ (2 * (pipeline.preparedGraph.graph.residue.extraCost : ENNReal)) *
          (heightPopular.heightIndices.card : ENNReal) := by gcongr
      _ ≤ (2 * ENNReal.ofReal
          (Real.rpow prep.graphScale (-extraLoss))) *
          PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho := by
        gcongr
      _ = PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss := by
        rw [prep.graphScale_eq]
        unfold PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  calc
    volume prep.shadow.union * floor * twoScale.coarse.refined.mass =
        floor * volume prep.shadow.union *
          twoScale.coarse.refined.mass := by ring
    _ ≤ (4 * heightPopular.bins : ENNReal) *
          (heightPopular.heightIndices.card : ENNReal) *
            (richOutput.heightLift.shading.mass *
              volume twoScale.coarse.croppedCoarseShading.union) := hweighted
    _ ≤ PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss *
        (richOutput.heightLift.shading.mass *
          volume twoScale.coarse.croppedCoarseShading.union) := by gcongr
    _ = _ := by ring

/-- Cube-balanced form of the same estimate.  Keeping the physical cell
volume until the final density cancellation avoids the spurious fixed
`rho^3` loss. -/
theorem graph_height_mass_cube_bound
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta extraLoss : ℝ}
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
    {pipeline : PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
      (normalEta := normalEta) prep}
    {richOutput : PureWZ2SourceFixedBinCoarseRichPipelineAtPreparationData
      (finalLoss := finalLoss) (theoremEta := theoremEta) pipeline}
    (saturation : PureWZ2SourceFixedBinCoarseRichHeightSaturationData
      richOutput.heightLift)
    (hextraPower :
      (pipeline.preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow prep.graphScale (-extraLoss)) :
    volume prep.shadow.union *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass ≤
      PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss * richOutput.heightLift.shading.mass *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
  let rich := richOutput.rich
  let heightPopular := pipeline.preparedGraph.heightPopular
  let floor := pureWZ2SourceHorizontalRichFloor rho finalLoss
  have hpopular : volume prep.shadow.union ≤
      2 * heightPopular.bins * volume heightPopular.shading.union := by
    have h := (ENNReal.div_le_iff (by norm_num) (by norm_num)).mp
      heightPopular.retained_volume
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hfloor : floor ≤ (rich.heightIndices.card : ENNReal) := by
    have hfloorEq : floor = Kakeya.realRpowENN
        richOutput.ready.ready.deltaGraph (finalLoss - 1) := by
      dsimp only [floor]
      unfold pureWZ2SourceHorizontalRichFloor
      rw [richOutput.ready.ready.deltaGraph_eq, prep.graphScale_eq]
    rw [hfloorEq]
    simpa [rich.heightIndices_card] using rich.richF_card
  have hpopularLayer : volume heightPopular.shading.union ≤
      2 * (heightPopular.heightIndices.card : ENNReal) *
        heightPopular.layerMass := by
    rw [heightPopular.volume_eq_sum]
    calc
      (∑ heightIndex ∈ heightPopular.heightIndices,
          volume (prep.shadow.union ∩
            wz1Lemma23HeightSlab prep.graphScale heightIndex)) ≤
        ∑ _heightIndex ∈ heightPopular.heightIndices,
          2 * heightPopular.layerMass := by
        exact Finset.sum_le_sum fun heightIndex hheight =>
          (heightPopular.layer_volume_band heightIndex hheight).2
      _ = 2 * (heightPopular.heightIndices.card : ENNReal) *
          heightPopular.layerMass := by simp [Finset.sum_const]; ring
  have hweighted : floor * volume prep.shadow.union *
        twoScale.coarse.balanced.incidenceMass ≤
      4 * heightPopular.bins *
        (heightPopular.heightIndices.card : ENNReal) *
          (richOutput.heightLift.shading.mass *
            volume (wz1PaperGridCube rho (0, 0, 0))) := by
    calc
      _ ≤ floor * (2 * heightPopular.bins *
          volume heightPopular.shading.union) *
            twoScale.coarse.balanced.incidenceMass := by gcongr
      _ ≤ floor * (2 * heightPopular.bins *
          (2 * (heightPopular.heightIndices.card : ENNReal) *
            heightPopular.layerMass)) *
              twoScale.coarse.balanced.incidenceMass := by gcongr
      _ ≤ (rich.heightIndices.card : ENNReal) *
          (2 * heightPopular.bins *
            (2 * (heightPopular.heightIndices.card : ENNReal) *
              heightPopular.layerMass)) *
                twoScale.coarse.balanced.incidenceMass := by gcongr
      _ = 4 * heightPopular.bins *
          (heightPopular.heightIndices.card : ENNReal) *
            (((rich.heightIndices.card : ENNReal) *
              heightPopular.layerMass) *
                twoScale.coarse.balanced.incidenceMass) := by ring
      _ ≤ 4 * heightPopular.bins *
          (heightPopular.heightIndices.card : ENNReal) *
            (richOutput.heightLift.shading.mass *
              volume (wz1PaperGridCube rho (0, 0, 0))) := by
        exact mul_le_mul_left' (by
          simpa [rich, heightPopular] using saturation.mass_cube_lower)
          (4 * heightPopular.bins *
            (heightPopular.heightIndices.card : ENNReal))
  have hbinsNat : 4 * heightPopular.bins ≤
      2 * pipeline.preparedGraph.graph.residue.extraCost := by
    rw [pipeline.preparedGraph.extraCost_eq]
    nlinarith
  have hbinsENN : (4 * heightPopular.bins : ENNReal) ≤
      2 * (pipeline.preparedGraph.graph.residue.extraCost : ENNReal) := by
    exact_mod_cast hbinsNat
  have hextraENN :
      (pipeline.preparedGraph.graph.residue.extraCost : ENNReal) ≤
        ENNReal.ofReal (Real.rpow prep.graphScale (-extraLoss)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hextraPower
  have hheight := saturation.popular_heights_le_cap
  have hcost :
      (4 * heightPopular.bins : ENNReal) *
          (heightPopular.heightIndices.card : ENNReal) ≤
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss := by
    calc
      _ ≤ (2 * (pipeline.preparedGraph.graph.residue.extraCost : ENNReal)) *
          (heightPopular.heightIndices.card : ENNReal) := by gcongr
      _ ≤ (2 * ENNReal.ofReal
          (Real.rpow prep.graphScale (-extraLoss))) *
          PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho := by
        gcongr
      _ = PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss := by
        rw [prep.graphScale_eq]
        unfold PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  calc
    volume prep.shadow.union * floor *
          twoScale.coarse.balanced.incidenceMass =
        floor * volume prep.shadow.union *
          twoScale.coarse.balanced.incidenceMass := by ring
    _ ≤ (4 * heightPopular.bins : ENNReal) *
          (heightPopular.heightIndices.card : ENNReal) *
            (richOutput.heightLift.shading.mass *
              volume (wz1PaperGridCube rho (0, 0, 0))) := hweighted
    _ ≤ PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss *
        (richOutput.heightLift.shading.mass *
          volume (wz1PaperGridCube rho (0, 0, 0))) := by gcongr
    _ = _ := by ring

end PureWZ2SourceFixedBinCoarseRichHeightSaturationData

end Kakeya.Assouad

end
