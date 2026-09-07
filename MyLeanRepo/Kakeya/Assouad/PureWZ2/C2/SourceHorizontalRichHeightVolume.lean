import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalHeightLift

/-!
# Source-volume retained by the Alternative-A rich heights

The graph selects a subset of the already source-volume-popular height
layers.  Since those layers have union volume in one factor-two band, the
number of rich heights gives a relative lower bound for the genuine source
height restriction.  This is the weighted-height step in WZ Lemma 24.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2SourceAlternativeARichHeightVolume
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {heightPopular : PureWZ2SourceHorizontalHeightPopularShadow
      retained prep.shadow prep.graphScale}
    {popularSource : PureWZ2SourceHorizontalPopularResidueData heightPopular}
    {rawResidue : WZ1Lemma23YResiduePackage prep.windowed.global}
    {popularResidue : WZ1Lemma23HeightPopularResidueData rawResidue}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {graphParents : PureWZ2SourceHorizontalGraphParentData prep}
    {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
    {ready : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceAlternativeAHeightData ready finalLoss}
    {richCells : PureWZ2SourceAlternativeARichCells
      (graphParents := graphParents) rich}
    {richShading : PureWZ2SourceAlternativeARichShading richCells}
    {richTrapezoid : PureWZ2SourceAlternativeARichTrapezoid richShading}
    (heightLift : PureWZ2SourceAlternativeAHeightLift richTrapezoid) where
  graph_residue_eq : graph.residue = popularResidue.residue
  raw_residue_eq : rawResidue = popularSource.residue
  heightIndices_subset : rich.heightIndices ⊆ heightPopular.heightIndices
  richRegion : Set Point3 :=
    ⋃ heightIndex ∈ rich.heightIndices,
      wz1Lemma23HeightSlab prep.graphScale heightIndex
  richRegion_eq : richRegion =
    ⋃ heightIndex ∈ rich.heightIndices,
      wz1Lemma23HeightSlab prep.graphScale heightIndex
  richHeightShading : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily retained.shading source.extremal.delta_pos)
  richHeight_carrier_eq : ∀ index, richHeightShading.carrier index =
    prep.shadow.carrier index ∩ richRegion
  richHeight_sub_heightLift :
    richHeightShading.union ⊆ heightLift.shading.union
  richHeight_volume_eq : volume richHeightShading.union =
    ∑ heightIndex ∈ rich.heightIndices,
      volume (prep.shadow.union ∩
        wz1Lemma23HeightSlab prep.graphScale heightIndex)
  paperRichShading : WZ1PaperTubeShading source.family
  paperRich_carrier_eq : ∀ index, paperRichShading.carrier index =
    retained.shading.carrier index ∩ richRegion
  paperRich_union_eq :
    paperRichShading.union = richHeightShading.union
  paperRich_sub_heightLift :
    PureWZ2PaperIsSubshading paperRichShading heightLift.shading
  paperRich_constantMultiplicity :
    paperRichShading.HasConstantMultiplicity
      twoScale.coarse.fineMultiplicity
      (2 * twoScale.coarse.fineMultiplicity)
  volume_lower :
    (rich.heightIndices.card : ENNReal) * heightPopular.layerMass ≤
      volume heightLift.shading.union
  relative_volume_lower :
    (rich.heightIndices.card : ENNReal) *
        volume heightPopular.shading.union ≤
      2 * (heightPopular.heightIndices.card : ENNReal) *
        volume heightLift.shading.union
  mass_lower :
    (twoScale.coarse.fineMultiplicity : ENNReal) *
        ((rich.heightIndices.card : ENNReal) * heightPopular.layerMass) ≤
      heightLift.shading.mass

theorem PureWZ2SourceAlternativeAHeightLift.richHeightVolume
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {heightPopular : PureWZ2SourceHorizontalHeightPopularShadow
      retained prep.shadow prep.graphScale}
    {popularSource : PureWZ2SourceHorizontalPopularResidueData heightPopular}
    {rawResidue : WZ1Lemma23YResiduePackage prep.windowed.global}
    {popularResidue : WZ1Lemma23HeightPopularResidueData rawResidue}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {graphParents : PureWZ2SourceHorizontalGraphParentData prep}
    {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
    {ready : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceAlternativeAHeightData ready finalLoss}
    {richCells : PureWZ2SourceAlternativeARichCells
      (graphParents := graphParents) rich}
    {richShading : PureWZ2SourceAlternativeARichShading richCells}
    {richTrapezoid : PureWZ2SourceAlternativeARichTrapezoid richShading}
    (heightLift : PureWZ2SourceAlternativeAHeightLift richTrapezoid)
    (hgraph : graph.residue = popularResidue.residue)
    (hraw : rawResidue = popularSource.residue)
    (hshadow : prep.shadow.union = retained.shading.union) :
    Nonempty (PureWZ2SourceAlternativeARichHeightVolume
      (heightPopular := heightPopular) (popularSource := popularSource)
      (popularResidue := popularResidue) heightLift) := by
  have hgraphRaw : graph.residue.cells ⊆ rawResidue.cells := by
    rw [hgraph]
    exact popularResidue.cells_subset
  have hgraphPopular : ∀ cell ∈ graph.residue.cells,
      cell.2.2 ∈ heightPopular.heightIndices := by
    intro cell hcell
    have hrawCell : cell ∈ rawResidue.cells := hgraphRaw hcell
    rw [hraw] at hrawCell
    exact popularSource.cells_popular_height cell hrawCell
  have hheightSubset : rich.heightIndices ⊆ heightPopular.heightIndices := by
    intro heightIndex hheightIndex
    rw [rich.heightIndices_eq] at hheightIndex
    rcases Finset.mem_image.mp hheightIndex with ⟨point, hpoint, hheightEq⟩
    have hcell := rich.cell_mem point hpoint
    have hpopular := hgraphPopular (rich.pathFor point).2.1 hcell
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
  let richHeightShading : Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily retained.shading source.extremal.delta_pos) :=
    { carrier := fun index => prep.shadow.carrier index ∩ richRegion
      measurable_carrier := fun index =>
        (prep.shadow.measurable_carrier index).inter hregionMeas
      subset_body := fun index => Set.inter_subset_left.trans
        (prep.shadow.subset_body index) }
  have hunion : richHeightShading.union = prep.shadow.union ∩ richRegion := by
    ext point
    constructor
    · rintro ⟨index, hpoint, hregion⟩
      exact ⟨⟨index, hpoint⟩, hregion⟩
    · rintro ⟨⟨index, hpoint⟩, hregion⟩
      exact ⟨index, hpoint, hregion⟩
  have hsubLift : richHeightShading.union ⊆ heightLift.shading.union := by
    intro point hpoint
    rw [hunion] at hpoint
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨heightIndex, hheightIndex, hpointSlab⟩
    have hretained : point ∈ retained.shading.union := by
      exact prep.shadow_union_subset hpoint.1
    have hcore : point 2 ∈ richTrapezoid.trapezoid.core := by
      apply richTrapezoid.retained_height_coverage (point 2)
      apply Set.nonempty_iff_ne_empty.mp
      exact ⟨point, hretained, rfl⟩
    have hclose : |point 2 -
        wz1Lemma23SnappedBaseHeight prep.graphScale heightIndex| ≤
          prep.graphScale / 2 := by
      have hinterval := hpointSlab
      change point 2 ∈ wz1Lemma23HeightInterval
        prep.graphScale heightIndex at hinterval
      rw [wz1Lemma23SnappedBaseHeight]
      have hside : gridSide (prep.graphScale / 2) =
          prep.graphScale / Real.sqrt 3 := by
        simp [gridSide]
        ring
      rw [wz1Lemma23HeightInterval, hside] at hinterval
      have hsqrt3 : 1 < Real.sqrt (3 : ℝ) := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
          Real.sqrt_nonneg (3 : ℝ)]
      have hsidePos : 0 < prep.graphScale / Real.sqrt 3 := by
        exact div_pos prep.graphScale_pos (Real.sqrt_pos.mpr (by norm_num))
      have hsideLe : prep.graphScale / Real.sqrt 3 < prep.graphScale := by
        exact div_lt_self prep.graphScale_pos hsqrt3
      have hcenterLower :
          (heightIndex : ℝ) * (prep.graphScale / Real.sqrt 3) -
              ((heightIndex : ℝ) + 1 / 2) *
                (prep.graphScale / Real.sqrt 3) =
            -(prep.graphScale / (2 * Real.sqrt 3)) := by ring
      have hcenterUpper :
          ((heightIndex : ℝ) + 1) * (prep.graphScale / Real.sqrt 3) -
              ((heightIndex : ℝ) + 1 / 2) *
                (prep.graphScale / Real.sqrt 3) =
            prep.graphScale / (2 * Real.sqrt 3) := by ring
      rw [abs_le]
      rw [hside]
      constructor
      · have hhalf : prep.graphScale / (2 * Real.sqrt 3) ≤
            prep.graphScale / 2 := by
          have hden : (2 : ℝ) ≤ 2 * Real.sqrt 3 := by nlinarith
          exact div_le_div_of_nonneg_left prep.graphScale_pos.le
            (by norm_num) hden
        have hcenter : ((heightIndex : ℝ) + 1 / 2) *
              (prep.graphScale / Real.sqrt 3) -
            (heightIndex : ℝ) * (prep.graphScale / Real.sqrt 3) =
              prep.graphScale / (2 * Real.sqrt 3) := by ring
        linarith [hinterval.1, hhalf, hcenter]
      · have hhalf : prep.graphScale / (2 * Real.sqrt 3) ≤
            prep.graphScale / 2 := by
          have hden : (2 : ℝ) ≤ 2 * Real.sqrt 3 := by nlinarith
          exact div_le_div_of_nonneg_left prep.graphScale_pos.le
            (by norm_num) hden
        linarith [hinterval.2, hhalf, hcenterUpper]
    have hsource : point ∈ source.shading.union :=
      retained.subshading.union_subset hretained
    have hsourceCells := hsource
    rw [source.cubical.union_eq_activeCells source.extremal.delta_pos]
      at hsourceCells
    rcases Set.mem_iUnion₂.mp hsourceCells with ⟨cell, hcell, hpointCell⟩
    have hcellCondition : ∀ other ∈ wz1PaperGridCube delta cell,
        other 2 ∈ richTrapezoid.trapezoid.core ∧
          ∃ selectedHeight ∈ rich.heightIndices,
            |other 2 - wz1Lemma23SnappedBaseHeight
              prep.graphScale selectedHeight| ≤ prep.graphScale := by
      intro other hother
      have hotherRetained : other ∈ retained.shading.union := by
        -- `retained` is a whole-cell restriction and contains `point`.
        rcases hretained with ⟨index, hpointCarrier⟩
        exact ⟨index, retained.whole_cells index point hpointCarrier (by
          have hcellEq : cell = wz1PaperGridIndex delta point :=
            (mem_wz1PaperGridCube delta cell point).mp hpointCell |>.symm
          rw [← hcellEq]
          exact hother)⟩
      have hotherCore : other 2 ∈ richTrapezoid.trapezoid.core := by
        apply richTrapezoid.retained_height_coverage (other 2)
        apply Set.nonempty_iff_ne_empty.mp
        exact ⟨other, hotherRetained, rfl⟩
      have hdeltaGraph : delta ≤ prep.graphScale :=
        prep.sourceScale_le_graphScale
      have hdeltaRho : delta ≤ rho := by
        rw [← twoScale.rhoRequested_eq]
        exact twoScale.rhoRequested.property.1
      have hrhoGraph : rho ≤ prep.graphScale / 2 := by
        rw [prep.graphScale_eq]
        nlinarith [line.rho_pos]
      have hheightClose : |other 2 - point 2| ≤ delta := by
        rw [wz1PaperGridCube_eq_Ico source.extremal.delta_pos cell]
          at hpointCell hother
        rw [abs_le]
        constructor <;>
          linarith [hpointCell.2.2.2.2.1, hpointCell.2.2.2.2.2,
            hother.2.2.2.2.1, hother.2.2.2.2.2]
      refine ⟨hotherCore, heightIndex, hheightIndex, ?_⟩
      calc
        |other 2 - wz1Lemma23SnappedBaseHeight
            prep.graphScale heightIndex| ≤
          |other 2 - point 2| +
            |point 2 - wz1Lemma23SnappedBaseHeight
              prep.graphScale heightIndex| := abs_sub_le _ _ _
        _ ≤ delta + prep.graphScale / 2 := by gcongr
        _ ≤ prep.graphScale := by linarith [hdeltaRho, hrhoGraph]
    have hheightCell : cell ∈ heightLift.heightCells :=
      by
        rw [heightLift.heightCells_eq]
        exact Finset.mem_filter.mpr ⟨hcell, hcellCondition⟩
    rcases hsource with ⟨sourceIndex, hpointSource⟩
    exact ⟨sourceIndex, by
      rw [heightLift.carrier_eq]
      refine ⟨hpointSource, ?_⟩
      rw [heightLift.region_eq]
      exact Set.mem_iUnion₂.mpr ⟨cell, hheightCell, hpointCell⟩⟩
  have hvolume : volume richHeightShading.union =
      ∑ heightIndex ∈ rich.heightIndices,
        volume (prep.shadow.union ∩
          wz1Lemma23HeightSlab prep.graphScale heightIndex) := by
    rw [hunion]
    have hregion : prep.shadow.union ∩ richRegion =
        ⋃ heightIndex ∈ rich.heightIndices,
          prep.shadow.union ∩
            wz1Lemma23HeightSlab prep.graphScale heightIndex := by
      ext point
      simp [richRegion]
    rw [hregion]
    apply MeasureTheory.measure_biUnion_finset
    · intro first hfirst second hsecond hne
      exact (wz1Lemma23_heightSlab_disjoint prep.graphScale_pos hne).mono
        Set.inter_subset_right Set.inter_subset_right
    · intro heightIndex _
      exact (measurableSet_shading_union prep.shadow).inter (by
        change MeasurableSet ((fun point : Point3 => point 2) ⁻¹'
          wz1Lemma23HeightInterval prep.graphScale heightIndex)
        exact measurableSet_Ico.preimage
          (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).measurable)
  have hlowerRich : (rich.heightIndices.card : ENNReal) *
      heightPopular.layerMass ≤ volume richHeightShading.union := by
    calc
      (rich.heightIndices.card : ENNReal) * heightPopular.layerMass =
          ∑ _heightIndex ∈ rich.heightIndices, heightPopular.layerMass := by
        simp [Finset.sum_const]
      _ ≤ ∑ heightIndex ∈ rich.heightIndices,
          volume (prep.shadow.union ∩
            wz1Lemma23HeightSlab prep.graphScale heightIndex) := by
        exact Finset.sum_le_sum fun heightIndex hheight =>
          (heightPopular.layer_volume_band heightIndex
            (hheightSubset hheight)).1
      _ = volume richHeightShading.union := hvolume.symm
  have hlower : (rich.heightIndices.card : ENNReal) *
      heightPopular.layerMass ≤ volume heightLift.shading.union :=
    hlowerRich.trans (measure_mono hsubLift)
  have hpopularUpper : volume heightPopular.shading.union ≤
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
  have hrelative : (rich.heightIndices.card : ENNReal) *
        volume heightPopular.shading.union ≤
      2 * (heightPopular.heightIndices.card : ENNReal) *
        volume heightLift.shading.union := by
    calc
      (rich.heightIndices.card : ENNReal) *
          volume heightPopular.shading.union ≤
        (rich.heightIndices.card : ENNReal) *
          (2 * (heightPopular.heightIndices.card : ENNReal) *
            heightPopular.layerMass) := by gcongr
      _ = 2 * (heightPopular.heightIndices.card : ENNReal) *
          ((rich.heightIndices.card : ENNReal) *
            heightPopular.layerMass) := by ring
      _ ≤ 2 * (heightPopular.heightIndices.card : ENNReal) *
          volume heightLift.shading.union := by gcongr
  let paperRichShading : WZ1PaperTubeShading source.family :=
    { carrier := fun index => retained.shading.carrier index ∩ richRegion
      measurable_carrier := fun index =>
        (retained.shading.measurable_carrier index).inter hregionMeas
      subset_body := fun index => Set.inter_subset_left.trans
        (retained.shading.subset_body index) }
  have hpaperUnion : paperRichShading.union = richHeightShading.union := by
    rw [hunion]
    ext point
    constructor
    · rintro ⟨index, hretainedPoint, hregion⟩
      exact ⟨by rw [hshadow]; exact ⟨index, hretainedPoint⟩, hregion⟩
    · rintro ⟨hshadowPoint, hregion⟩
      have hretainedPoint : point ∈ retained.shading.union := by
        exact prep.shadow_union_subset hshadowPoint
      rcases hretainedPoint with ⟨index, hindex⟩
      exact ⟨index, hindex, hregion⟩
  have hpaperSub : PureWZ2PaperIsSubshading
      paperRichShading heightLift.shading := by
    intro index point hpoint
    have hpaperUnionPoint : point ∈ paperRichShading.union :=
      ⟨index, hpoint⟩
    have hrichHeightPoint : point ∈ richHeightShading.union := by
      rwa [← hpaperUnion]
    have hliftPoint : point ∈ heightLift.shading.union :=
      hsubLift hrichHeightPoint
    rcases hliftPoint with ⟨_liftIndex, hliftCarrier⟩
    rw [heightLift.carrier_eq] at hliftCarrier ⊢
    exact ⟨retained.subshading index hpoint.1, hliftCarrier.2⟩
  have hpaperConstant : paperRichShading.HasConstantMultiplicity
      twoScale.coarse.fineMultiplicity
      (2 * twoScale.coarse.fineMultiplicity) := by
    have hambient := retained.constantMultiplicity
    intro point hpoint
    have hmultiplicity := wholeCellRestriction_pointMultiplicity_eq
      (fun index => show paperRichShading.carrier index =
        retained.shading.carrier index ∩ richRegion from rfl) hpoint
    rw [hmultiplicity]
    exact hambient point (by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, hindex.1⟩)
  have hmassLower :
      (twoScale.coarse.fineMultiplicity : ENNReal) *
          ((rich.heightIndices.card : ENNReal) *
            heightPopular.layerMass) ≤ heightLift.shading.mass := by
    calc
      (twoScale.coarse.fineMultiplicity : ENNReal) *
          ((rich.heightIndices.card : ENNReal) *
            heightPopular.layerMass) ≤
        (twoScale.coarse.fineMultiplicity : ENNReal) *
          volume richHeightShading.union := by gcongr
      _ = (twoScale.coarse.fineMultiplicity : ENNReal) *
          volume paperRichShading.union := by rw [hpaperUnion]
      _ ≤ paperRichShading.mass :=
        (constant_multiplicity_mass_volume_generic hpaperConstant).1
      _ ≤ heightLift.shading.mass := by
        apply Finset.sum_le_sum
        intro index _
        exact measure_mono (hpaperSub index)
  exact ⟨{
    graph_residue_eq := hgraph
    raw_residue_eq := hraw
    heightIndices_subset := hheightSubset
    richRegion := richRegion
    richRegion_eq := rfl
    richHeightShading := richHeightShading
    richHeight_carrier_eq := fun _ => rfl
    richHeight_sub_heightLift := hsubLift
    richHeight_volume_eq := hvolume
    paperRichShading := paperRichShading
    paperRich_carrier_eq := fun _ => rfl
    paperRich_union_eq := hpaperUnion
    paperRich_sub_heightLift := hpaperSub
    paperRich_constantMultiplicity := hpaperConstant
    volume_lower := hlower
    relative_volume_lower := hrelative
    mass_lower := hmassLower
  }⟩

end Kakeya.Assouad
