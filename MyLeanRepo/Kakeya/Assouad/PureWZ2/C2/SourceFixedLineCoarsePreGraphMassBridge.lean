import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseHeightLift
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceWindowHeightPopularity

/-!
# Pre-graph source-mass bridge for a fixed-bin coarse graph

The coarse graph chooses rich heights, but the retained mass is measured on
the original source family.  The whole-cell outer-popular envelope is kept
distinct from the partial popular shading throughout.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- A rich height selected from a graph whose shadow lies in the outer-popular
height region is itself one of the outer-popular heights. -/
theorem PureWZ2SourceFixedBinCoarseAlternativeAHeightData.heightIndices_subset_outerPopular
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      sourceWindow (256 * rho)}
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
    (rich : PureWZ2SourceFixedBinCoarseAlternativeAHeightData ready finalLoss)
    (hscale : prep.graphScale = 256 * rho)
    (hcarrier : prep.shadow.union ⊆ outerPopular.popular.heightRegion) :
    rich.heightIndices ⊆ outerPopular.popular.heightIndices := by
  intro heightIndex hheightIndex
  rw [rich.heightIndices_eq] at hheightIndex
  rcases Finset.mem_image.mp hheightIndex with
    ⟨point, hpoint, hheightEq⟩
  let cell := (rich.pathFor point).2.1
  have hcellGraph : cell ∈ preparedGraph.graph.residue.cells :=
    rich.cell_mem point hpoint
  have hcellGlobal : cell ∈ prep.windowed.global.cells :=
    preparedGraph.graph.residue.cells_subset hcellGraph
  have hrepresentative : graphParents.representative cell ∈ prep.shadow.union :=
    graphParents.representative_mem cell hcellGlobal
  have hpopularRegion := hcarrier hrepresentative
  rw [outerPopular.popular.heightRegion_eq] at hpopularRegion
  rcases Set.mem_iUnion₂.mp hpopularRegion with
    ⟨popularHeight, hpopularHeight, hslab⟩
  have hfloorPopular := (wz1Lemma23_mem_heightSlab_iff
    outerPopular.popular.graphScale_pos popularHeight
      (graphParents.representative cell)).mp hslab
  have hcellHeight := congrArg
    (fun index : ℤ × ℤ × ℤ => index.2.2)
    (graphParents.representative_index cell hcellGlobal)
  have hfloorCell :
      Int.floor
          (graphParents.representative cell (2 : Fin 3) /
            gridSide ((256 * rho) / 2)) = cell.2.2 := by
    rw [← hscale]
    simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using hcellHeight
  have hheightCell : rich.heightIndex point = cell.2.2 :=
    rich.heightIndex_eq point hpoint
  have heq : heightIndex = popularHeight :=
    hheightEq.symm.trans
      (hheightCell.trans (hfloorCell.symm.trans hfloorPopular))
  rwa [heq]

/-- Every selected graph-height layer carries its original-source mass into
the complete-cell height lift. -/
theorem PureWZ2SourceFixedBinCoarseHeightLift.mass_lower_of_window_layers
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
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
    {rich : PureWZ2SourceFixedBinCoarseAlternativeAHeightData ready finalLoss}
    {richCells : PureWZ2SourceFixedBinCoarseRichCells
      (graphParents := graphParents) rich}
    {richShading : PureWZ2SourceFixedBinCoarseRichShading richCells}
    {richTrapezoid : PureWZ2SourceFixedBinCoarseRichTrapezoid richShading}
    (heightLift : PureWZ2SourceFixedBinCoarseHeightLift richTrapezoid)
    (layerMass : ENNReal)
    (hlayer : ∀ heightIndex ∈ rich.heightIndices,
      layerMass ≤ volume (window.shading.union ∩
        wz1Lemma23HeightSlab prep.graphScale heightIndex)) :
    (twoScale.coarse.fineMultiplicity : ENNReal) *
        ((rich.heightIndices.card : ENNReal) * layerMass) ≤
      heightLift.shading.mass := by
  let richRegion : Set Point3 :=
    ⋃ heightIndex ∈ rich.heightIndices,
      wz1Lemma23HeightSlab prep.graphScale heightIndex
  have hregionMeasurable : MeasurableSet richRegion :=
    MeasurableSet.biUnion rich.heightIndices.finite_toSet.countable
      (fun heightIndex _ => by
        change MeasurableSet ((fun point : Point3 => point 2) ⁻¹'
          wz1Lemma23HeightInterval prep.graphScale heightIndex)
        exact measurableSet_Ico.preimage
          (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).measurable)
  let region : Set Point3 := window.shading.union ∩ richRegion
  have hregionMeasurable' : MeasurableSet region :=
    (measurableSet_shading_union window.shading).inter hregionMeasurable
  let paperRich : WZ1PaperTubeShading source.family :=
    { carrier := fun index =>
        pullback.zeroExtension.ambientShading.carrier index ∩ region
      measurable_carrier := fun index =>
        (pullback.zeroExtension.ambientShading.measurable_carrier index).inter
          hregionMeasurable'
      subset_body := fun index => Set.inter_subset_left.trans
        (pullback.zeroExtension.ambientShading.subset_body index) }
  have hwindowAmbient : window.shading.union ⊆
      pullback.zeroExtension.ambientShading.union := by
    intro point hpoint
    have hprepared : point ∈ prepared.shadow.union :=
      window.subshading.union_subset hpoint
    have hpullback : point ∈ pullback.shading.union := by
      rwa [prepared.shadow_union] at hprepared
    rcases hpullback with ⟨index, hindex⟩
    rw [pullback.carrier_eq] at hindex
    exact ⟨index, hindex.1⟩
  have hunion : paperRich.union = region := by
    apply Set.Subset.antisymm
    · rintro point ⟨_index, _hambient, hregion⟩
      exact hregion
    · intro point hpoint
      rcases hwindowAmbient hpoint.1 with ⟨index, hindex⟩
      exact ⟨index, hindex, hpoint⟩
  have hconstant : paperRich.HasConstantMultiplicity
      twoScale.coarse.fineMultiplicity
      (2 * twoScale.coarse.fineMultiplicity) := by
    have hambient := pullback.zeroExtension.constantMultiplicity
      twoScale.coarse.refined_multiplicity_band
    intro point hpoint
    have hpointAmbient : point ∈
        pullback.zeroExtension.ambientShading.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, hindex.1⟩
    have hmultiplicity := wholeCellRestriction_pointMultiplicity_eq
      (fun index => show paperRich.carrier index =
        pullback.zeroExtension.ambientShading.carrier index ∩ region from rfl)
      hpoint
    rw [hmultiplicity]
    exact hambient point hpointAmbient
  have hpaperSub : PureWZ2PaperIsSubshading
      paperRich heightLift.shading := by
    intro index point hpoint
    have hregion : point ∈ region := hpoint.2
    have hwindow : point ∈ window.shading.union := hregion.1
    have hrichRegion : point ∈ richRegion := hregion.2
    rcases Set.mem_iUnion₂.mp hrichRegion with
      ⟨heightIndex, hheightIndex, hpointSlab⟩
    rcases pullback.zeroExtension.carrier_support index point hpoint.1 with
      ⟨selectedIndex, hindex, hselected⟩
    have hsource : point ∈ source.shading.carrier index := by
      subst index
      exact twoScale.coarse.subshading selectedIndex hselected
    have hsourceUnion : point ∈ source.shading.union := ⟨index, hsource⟩
    rw [source.cubical.union_eq_activeCells source.extremal.delta_pos]
      at hsourceUnion
    rcases Set.mem_iUnion₂.mp hsourceUnion with
      ⟨cell, hcell, hpointCell⟩
    have hpointClose : |point 2 -
        wz1Lemma23SnappedBaseHeight prep.graphScale heightIndex| ≤
          prep.graphScale / 2 := by
      change point 2 ∈ wz1Lemma23HeightInterval
        prep.graphScale heightIndex at hpointSlab
      have hside : gridSide (prep.graphScale / 2) =
          prep.graphScale / Real.sqrt 3 := by
        simp [gridSide]
        ring
      rw [wz1Lemma23HeightInterval, hside] at hpointSlab
      rw [wz1Lemma23SnappedBaseHeight, hside]
      rw [abs_le]
      constructor
      · have hhalf : prep.graphScale / (2 * Real.sqrt 3) ≤
            prep.graphScale / 2 := by
          have hden : (2 : ℝ) ≤ 2 * Real.sqrt 3 := by
            nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
              Real.sqrt_nonneg (3 : ℝ)]
          exact div_le_div_of_nonneg_left prep.graphScale_pos.le
            (by norm_num) hden
        have hcenter : ((heightIndex : ℝ) + 1 / 2) *
              (prep.graphScale / Real.sqrt 3) -
            (heightIndex : ℝ) * (prep.graphScale / Real.sqrt 3) =
              prep.graphScale / (2 * Real.sqrt 3) := by ring
        linarith [hpointSlab.1, hhalf, hcenter]
      · have hhalf : prep.graphScale / (2 * Real.sqrt 3) ≤
            prep.graphScale / 2 := by
          have hden : (2 : ℝ) ≤ 2 * Real.sqrt 3 := by
            nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
              Real.sqrt_nonneg (3 : ℝ)]
          exact div_le_div_of_nonneg_left prep.graphScale_pos.le
            (by norm_num) hden
        have hcenterUpper :
            ((heightIndex : ℝ) + 1) *
                (prep.graphScale / Real.sqrt 3) -
              ((heightIndex : ℝ) + 1 / 2) *
                (prep.graphScale / Real.sqrt 3) =
              prep.graphScale / (2 * Real.sqrt 3) := by ring
        linarith [hpointSlab.2, hhalf, hcenterUpper]
    have hcellCondition : ∀ other ∈ wz1PaperGridCube delta cell,
        other 2 ∈ richTrapezoid.trapezoid.core ∧
          ∃ selectedHeight ∈ rich.heightIndices,
            |other 2 - wz1Lemma23SnappedBaseHeight
              prep.graphScale selectedHeight| ≤ prep.graphScale := by
      intro other hother
      have hotherClose : |other 2 - point 2| ≤ delta := by
        have hpointBounds := hpointCell
        have hotherBounds := hother
        rw [wz1PaperGridCube_eq_Ico source.extremal.delta_pos cell]
          at hpointBounds hotherBounds
        rw [abs_le]
        constructor <;>
          linarith [hpointBounds.2.2.2.2.1, hpointBounds.2.2.2.2.2,
            hotherBounds.2.2.2.2.1, hotherBounds.2.2.2.2.2]
      have hdeltaRho : delta ≤ rho := by
        rw [← twoScale.rhoRequested_eq]
        exact twoScale.rhoRequested.property.1
      have hrhoGraph : rho ≤ prep.graphScale / 2 := by
        rw [prep.graphScale_eq]
        nlinarith [line.rho_pos]
      have hrhoRoot : rho ≤ Real.sqrt rho := by
        have hrhoOne : rho ≤ 1 := by
          rw [← twoScale.rhoRequested_eq]
          exact twoScale.rhoRequested.property.2
        nlinarith [Real.sqrt_nonneg rho, Real.sq_sqrt line.rho_pos.le]
      have hpointWindow := window.union_height_window point hwindow
      have hotherWindow : other 2 ∈ Set.Icc
          (window.left - 2 * Real.sqrt rho)
          (window.left + 3 * Real.sqrt rho) := by
        rw [abs_le] at hotherClose
        constructor <;>
          nlinarith [hpointWindow.1, hpointWindow.2, hdeltaRho, hrhoRoot]
      have hcellEq : cell = wz1PaperGridIndex delta point :=
        (mem_wz1PaperGridCube delta cell point).mp hpointCell |>.symm
      refine ⟨richTrapezoid.height_window_coverage
          (other 2) hotherWindow, heightIndex, hheightIndex, ?_⟩
      calc
        |other 2 - wz1Lemma23SnappedBaseHeight
            prep.graphScale heightIndex| ≤
          |other 2 - point 2| +
            |point 2 - wz1Lemma23SnappedBaseHeight
              prep.graphScale heightIndex| := abs_sub_le _ _ _
        _ ≤ delta + prep.graphScale / 2 := by gcongr
        _ ≤ prep.graphScale := by linarith
    have hheightCell : cell ∈ heightLift.heightCells := by
      rw [heightLift.heightCells_eq]
      exact Finset.mem_filter.mpr ⟨hcell, hcellCondition⟩
    rw [heightLift.carrier_eq]
    refine ⟨hsource, ?_⟩
    rw [heightLift.region_eq]
    exact Set.mem_iUnion₂.mpr ⟨cell, hheightCell, hpointCell⟩
  have hvolume : (rich.heightIndices.card : ENNReal) * layerMass ≤
      volume paperRich.union := by
    rw [hunion]
    have hpartition : region =
        ⋃ heightIndex ∈ rich.heightIndices,
          window.shading.union ∩
            wz1Lemma23HeightSlab prep.graphScale heightIndex := by
      ext point
      simp [region, richRegion]
    rw [hpartition]
    rw [MeasureTheory.measure_biUnion_finset]
    · calc
        (rich.heightIndices.card : ENNReal) * layerMass =
            ∑ _heightIndex ∈ rich.heightIndices, layerMass := by
          simp [Finset.sum_const]
        _ ≤ ∑ heightIndex ∈ rich.heightIndices,
            volume (window.shading.union ∩
              wz1Lemma23HeightSlab prep.graphScale heightIndex) :=
          Finset.sum_le_sum hlayer
    · intro first _ second _ hne
      exact (wz1Lemma23_heightSlab_disjoint prep.graphScale_pos hne).mono
        Set.inter_subset_right Set.inter_subset_right
    · intro heightIndex _
      exact (measurableSet_shading_union window.shading).inter (by
        change MeasurableSet ((fun point : Point3 => point 2) ⁻¹'
          wz1Lemma23HeightInterval prep.graphScale heightIndex)
        exact measurableSet_Ico.preimage
          (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).measurable)
  calc
    (twoScale.coarse.fineMultiplicity : ENNReal) *
          ((rich.heightIndices.card : ENNReal) * layerMass) ≤
        (twoScale.coarse.fineMultiplicity : ENNReal) *
          volume paperRich.union := by gcongr
    _ ≤ paperRich.mass :=
      (constant_multiplicity_mass_volume_generic hconstant).1
    _ ≤ heightLift.shading.mass := by
      apply Finset.sum_le_sum
      intro index _
      exact measure_mono (hpaperSub index)

/-- Specialization to the whole-cell envelope of the outer-popular source
window.  Only set inclusion is used between the partial popular shading and
its complete-cell envelope. -/
theorem PureWZ2SourceFixedBinCoarseHeightLift.mass_lower_of_outer_popular
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      sourceWindow (256 * rho)}
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
    {rich : PureWZ2SourceFixedBinCoarseAlternativeAHeightData ready finalLoss}
    {richCells : PureWZ2SourceFixedBinCoarseRichCells
      (graphParents := graphParents) rich}
    {richShading : PureWZ2SourceFixedBinCoarseRichShading richCells}
    {richTrapezoid : PureWZ2SourceFixedBinCoarseRichTrapezoid richShading}
    (heightLift : PureWZ2SourceFixedBinCoarseHeightLift richTrapezoid)
    (hwindow : window.shading.union = outerPopular.windowed.shading.union)
    (hscale : prep.graphScale = 256 * rho)
    (hheightSubset : rich.heightIndices ⊆
      outerPopular.popular.heightIndices) :
    (twoScale.coarse.fineMultiplicity : ENNReal) *
        ((rich.heightIndices.card : ENNReal) *
          outerPopular.popular.layerMass) ≤ heightLift.shading.mass := by
  apply heightLift.mass_lower_of_window_layers outerPopular.popular.layerMass
  intro heightIndex hheightIndex
  have hband := outerPopular.popular.layer_volume_band heightIndex
    (hheightSubset hheightIndex)
  apply hband.1.trans
  apply measure_mono
  intro point hpoint
  have hpointSlab : point ∈
      wz1Lemma23HeightSlab prep.graphScale heightIndex := by
    simpa only [hscale] using hpoint.2
  refine ⟨?_, hpointSlab⟩
  rw [hwindow, outerPopular.windowed_shading]
  apply outerPopular.popular_subset
  rw [outerPopular.popular.union_eq]
  refine ⟨hpoint.1, ?_⟩
  rw [outerPopular.popular.heightRegion_eq]
  exact Set.mem_iUnion₂.mpr
    ⟨heightIndex, hheightSubset hheightIndex, hpoint.2⟩

end Kakeya.Assouad

end
