import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularAlternativeA

/-!
# Spatial volume on rich heights of the outer-popular terminal graph

This is the exact current-shadow receipt needed before lifting the rich height
region back to the sticky-selected paper family.  It retains the actual-cycle
provenance of every selected height and measures every layer against
`prep.shadow.union`, not against a larger complete-parent carrier.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2TerminalPopularRichHeightVolumeData
    {sigma inputLoss delta stickyLoss eta theoremEta epsilon : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
    {restrictedPrepared :
      PureWZ2TerminalPopularParentRestrictedPreparedData restricted}
    {line : PureWZ2HorizontalFixedBinCore
      restrictedPrepared.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalPopularRestrictedFixedBinParentData line}
    {selection : PureWZ2TerminalPopularRestrictedParentSelectionData parents}
    {selectedCarrier :
      PureWZ2TerminalPopularSelectedParentCarrierData selection}
    {sources : PureWZ2TerminalPopularCoarseSourceFamily selection}
    {localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources}
    {prep : PureWZ2TerminalPopularGraphPreparation localized}
    {graphParents : PureWZ2TerminalPopularGraphParentData prep}
    {localCells : PureWZ2TerminalPopularLocalCellData
      (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalPopularPreparedGraphData localCells}
    {sharp : PureWZ2TerminalPopularSharpGeometry preparedGraph}
    {first : PureWZ2TerminalPopularReadyGraph
      (theoremEta := theoremEta) sharp}
    {ready : PureWZ2CommonRefinedReadyGraph
      delta theoremEta first.common first.ready}
    (rich : PureWZ2TerminalPopularAlternativeAHeightData ready epsilon) where
  heightIndices_subset :
    rich.heightIndices ⊆ preparedGraph.heightPopular.heightIndices
  heightIndices_subset_outerPopular :
    rich.heightIndices ⊆ heightData.popular.heightIndices
  heightSlab_inter_commonCore : ∀ heightIndex ∈ rich.heightIndices,
    (wz1Lemma23HeightInterval delta heightIndex ∩
      Set.Icc
        ((selection.commonParentHeight : ℝ) * terminal.sqrtRequested.1)
        (((selection.commonParentHeight : ℝ) + 1) *
          terminal.sqrtRequested.1)).Nonempty
  richRegion : Set Point3 :=
    ⋃ heightIndex ∈ rich.heightIndices,
      wz1Lemma23HeightSlab delta heightIndex
  richRegion_eq : richRegion =
    ⋃ heightIndex ∈ rich.heightIndices,
      wz1Lemma23HeightSlab delta heightIndex
  richRegion_measurable : MeasurableSet richRegion
  richSet : Set Point3 := prep.shadow.union ∩ richRegion
  richSet_eq : richSet = prep.shadow.union ∩ richRegion
  richSet_measurable : MeasurableSet richSet
  richSet_subset_selectedCarrier : richSet ⊆ selectedCarrier.shading.union
  richSet_subset_terminalSource : richSet ⊆ terminalSource.shading.union
  richSet_volume_eq : volume richSet =
    ∑ heightIndex ∈ rich.heightIndices,
      volume (prep.shadow.union ∩
        wz1Lemma23HeightSlab delta heightIndex)
  layer_volume_lower : ∀ heightIndex ∈ rich.heightIndices,
    preparedGraph.heightPopular.layerMass ≤
      volume (prep.shadow.union ∩
        wz1Lemma23HeightSlab delta heightIndex)
  richSet_volume_lower :
    (rich.heightIndices.card : ENNReal) *
        preparedGraph.heightPopular.layerMass ≤ volume richSet

theorem PureWZ2TerminalPopularAlternativeAHeightData.toRichHeightVolume
    {sigma inputLoss delta stickyLoss eta theoremEta epsilon : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
    {restrictedPrepared :
      PureWZ2TerminalPopularParentRestrictedPreparedData restricted}
    {line : PureWZ2HorizontalFixedBinCore
      restrictedPrepared.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalPopularRestrictedFixedBinParentData line}
    {selection : PureWZ2TerminalPopularRestrictedParentSelectionData parents}
    {selectedCarrier :
      PureWZ2TerminalPopularSelectedParentCarrierData selection}
    {sources : PureWZ2TerminalPopularCoarseSourceFamily selection}
    {localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources}
    {prep : PureWZ2TerminalPopularGraphPreparation localized}
    {graphParents : PureWZ2TerminalPopularGraphParentData prep}
    {localCells : PureWZ2TerminalPopularLocalCellData
      (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalPopularPreparedGraphData localCells}
    {sharp : PureWZ2TerminalPopularSharpGeometry preparedGraph}
    {first : PureWZ2TerminalPopularReadyGraph
      (theoremEta := theoremEta) sharp}
    {ready : PureWZ2CommonRefinedReadyGraph
      delta theoremEta first.common first.ready}
    (rich : PureWZ2TerminalPopularAlternativeAHeightData ready epsilon) :
    Nonempty (PureWZ2TerminalPopularRichHeightVolumeData rich) := by
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
  have hgraphOuterPopular : ∀ cell ∈ preparedGraph.graph.residue.cells,
      cell.2.2 ∈ heightData.popular.heightIndices := by
    intro cell hcell
    have hglobalCell : cell ∈ prep.windowed.global.cells :=
      preparedGraph.graph.residue.cells_subset hcell
    have hactive := prep.windowed.global.cells_active hglobalCell
    rw [wz1Lemma23_mem_active_iff] at hactive
    rcases hactive.2 with ⟨point, hpointShadow, hpointCell⟩
    have hambient := prep.subshading.union_subset hpointShadow
    have hselected : point ∈ selectedCarrier.shading.union := by
      rwa [prep.ambient_union] at hambient
    have houterRegion := selectedCarrier.height_region hselected
    rw [heightData.popular.heightRegion_eq] at houterRegion
    rcases Set.mem_iUnion₂.mp houterRegion with
      ⟨outerHeight, houterHeight, hpointSlab⟩
    have hfloorOuter := (wz1Lemma23_mem_heightSlab_iff
      source.extremal.delta_pos outerHeight point).mp hpointSlab
    have hcellHeight := congrArg
      (fun index : ℤ × ℤ × ℤ => index.2.2) hpointCell
    have hfloorCell :
        Int.floor (point (2 : Fin 3) / gridSide (delta / 2)) =
          cell.2.2 := by
      simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using hcellHeight
    have : cell.2.2 = outerHeight := hfloorCell.symm.trans hfloorOuter
    rwa [this]
  have hheightSubsetOuter :
      rich.heightIndices ⊆ heightData.popular.heightIndices := by
    intro heightIndex hheightIndex
    rw [rich.heightIndices_eq] at hheightIndex
    rcases Finset.mem_image.mp hheightIndex with
      ⟨point, hpoint, hheightEq⟩
    have houter := hgraphOuterPopular (rich.pathFor point).2.1
      (rich.cell_mem point hpoint)
    rwa [← rich.heightIndex_eq point hpoint, hheightEq] at houter
  have hslabInterCore : ∀ heightIndex ∈ rich.heightIndices,
      (wz1Lemma23HeightInterval delta heightIndex ∩
        Set.Icc
          ((selection.commonParentHeight : ℝ) * terminal.sqrtRequested.1)
          (((selection.commonParentHeight : ℝ) + 1) *
            terminal.sqrtRequested.1)).Nonempty := by
    intro heightIndex hheightIndex
    rw [rich.heightIndices_eq] at hheightIndex
    rcases Finset.mem_image.mp hheightIndex with
      ⟨richPoint, hrichPoint, hheightEq⟩
    let cell := (rich.pathFor richPoint).2.1
    have hcellGraph : cell ∈ preparedGraph.graph.residue.cells :=
      rich.cell_mem richPoint hrichPoint
    have hcellGlobal : cell ∈ prep.windowed.global.cells :=
      preparedGraph.graph.residue.cells_subset hcellGraph
    have hcellActive := prep.windowed.global.cells_active hcellGlobal
    rw [wz1Lemma23_mem_active_iff] at hcellActive
    rcases hcellActive.2 with ⟨point, hpointShadow, hpointCell⟩
    have hpointIndex : wz1Lemma23CellIndex delta point = cell := hpointCell
    have hfloorCell :
        Int.floor (point (2 : Fin 3) / gridSide (delta / 2)) =
          cell.2.2 := by
      simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using
        congrArg (fun index : ℤ × ℤ × ℤ => index.2.2) hpointIndex
    have hheightCell : heightIndex = cell.2.2 := by
      exact hheightEq.symm.trans (rich.heightIndex_eq richPoint hrichPoint)
    have hpointSlab : point ∈ wz1Lemma23HeightSlab delta heightIndex := by
      rw [wz1Lemma23_mem_heightSlab_iff source.extremal.delta_pos]
      rwa [hheightCell]
    have hselected := prep.shadow_selectedRegion hpointShadow
    rw [selection.selectedRegion_eq] at hselected
    rcases Set.mem_iUnion₂.mp hselected with
      ⟨parent, hparent, hpointParent⟩
    rw [wz1PaperGridCube_eq_Ico terminal.sticky.coarse_extremal.delta_pos]
      at hpointParent
    rw [selection.parent_height_eq parent hparent] at hpointParent
    exact ⟨point (2 : Fin 3), hpointSlab, hpointParent.2.2.2.2.1,
      hpointParent.2.2.2.2.2.le⟩
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
  have hrichSelected : richSet ⊆ selectedCarrier.shading.union := by
    intro point hpoint
    have hambient := prep.subshading.union_subset hpoint.1
    rwa [prep.ambient_union] at hambient
  have hrichTerminal : richSet ⊆ terminalSource.shading.union := by
    intro point hpoint
    exact prep.shadow_terminal hpoint.1
  have hpartition : richSet =
      ⋃ heightIndex ∈ rich.heightIndices,
        prep.shadow.union ∩ wz1Lemma23HeightSlab delta heightIndex := by
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
  have hlayerLower : ∀ heightIndex ∈ rich.heightIndices,
      preparedGraph.heightPopular.layerMass ≤
        volume (prep.shadow.union ∩
          wz1Lemma23HeightSlab delta heightIndex) := by
    intro heightIndex hheightIndex
    exact (preparedGraph.heightPopular.layer_volume_band heightIndex
      (hheightSubset hheightIndex)).1
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
        exact Finset.sum_le_sum hlayerLower
  exact ⟨{
    heightIndices_subset := hheightSubset
    heightIndices_subset_outerPopular := hheightSubsetOuter
    heightSlab_inter_commonCore := hslabInterCore
    richRegion := richRegion
    richRegion_eq := rfl
    richRegion_measurable := hregionMeas
    richSet := richSet
    richSet_eq := rfl
    richSet_measurable := hrichSetMeas
    richSet_subset_selectedCarrier := hrichSelected
    richSet_subset_terminalSource := hrichTerminal
    richSet_volume_eq := hvolumeEq
    layer_volume_lower := hlayerLower
    richSet_volume_lower := hvolumeLower }⟩

/-- Return the rich height region to the original sticky-selected family.
This changes only the indexing of the carrier: its union is exactly the
current-shadow rich set and its multiplicity is the original terminal
multiplicity on that set. -/
structure PureWZ2TerminalPopularSelectedHeightLift
    {sigma inputLoss delta stickyLoss eta theoremEta epsilon : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
    {restrictedPrepared :
      PureWZ2TerminalPopularParentRestrictedPreparedData restricted}
    {line : PureWZ2HorizontalFixedBinCore
      restrictedPrepared.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalPopularRestrictedFixedBinParentData line}
    {selection : PureWZ2TerminalPopularRestrictedParentSelectionData parents}
    {selectedCarrier :
      PureWZ2TerminalPopularSelectedParentCarrierData selection}
    {sources : PureWZ2TerminalPopularCoarseSourceFamily selection}
    {localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources}
    {prep : PureWZ2TerminalPopularGraphPreparation localized}
    {graphParents : PureWZ2TerminalPopularGraphParentData prep}
    {localCells : PureWZ2TerminalPopularLocalCellData
      (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalPopularPreparedGraphData localCells}
    {sharp : PureWZ2TerminalPopularSharpGeometry preparedGraph}
    {first : PureWZ2TerminalPopularReadyGraph
      (theoremEta := theoremEta) sharp}
    {ready : PureWZ2CommonRefinedReadyGraph
      delta theoremEta first.common first.ready}
    {rich : PureWZ2TerminalPopularAlternativeAHeightData ready epsilon}
    (richVolume : PureWZ2TerminalPopularRichHeightVolumeData rich) where
  shading : WZ1PaperTubeShading terminal.sticky.selected.family
  carrier_eq : ∀ index, shading.carrier index =
    terminalSource.shading.carrier index ∩ richVolume.richSet
  subshading : PureWZ2PaperIsSubshading shading terminalSource.shading
  union_eq : shading.union = richVolume.richSet
  constant_multiplicity : shading.HasConstantMultiplicity
    terminalSource.multiplicity (2 * terminalSource.multiplicity)
  volume_lower :
    (rich.heightIndices.card : ENNReal) *
        preparedGraph.heightPopular.layerMass ≤ volume shading.union
  multiplicity_mass_lower :
    (terminalSource.multiplicity : ENNReal) * volume shading.union ≤
      shading.mass

def PureWZ2TerminalPopularRichHeightVolumeData.toSelectedHeightLift
    {sigma inputLoss delta stickyLoss eta theoremEta epsilon : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
    {restrictedPrepared :
      PureWZ2TerminalPopularParentRestrictedPreparedData restricted}
    {line : PureWZ2HorizontalFixedBinCore
      restrictedPrepared.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalPopularRestrictedFixedBinParentData line}
    {selection : PureWZ2TerminalPopularRestrictedParentSelectionData parents}
    {selectedCarrier :
      PureWZ2TerminalPopularSelectedParentCarrierData selection}
    {sources : PureWZ2TerminalPopularCoarseSourceFamily selection}
    {localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources}
    {prep : PureWZ2TerminalPopularGraphPreparation localized}
    {graphParents : PureWZ2TerminalPopularGraphParentData prep}
    {localCells : PureWZ2TerminalPopularLocalCellData
      (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalPopularPreparedGraphData localCells}
    {sharp : PureWZ2TerminalPopularSharpGeometry preparedGraph}
    {first : PureWZ2TerminalPopularReadyGraph
      (theoremEta := theoremEta) sharp}
    {ready : PureWZ2CommonRefinedReadyGraph
      delta theoremEta first.common first.ready}
    {rich : PureWZ2TerminalPopularAlternativeAHeightData ready epsilon}
    (richVolume : PureWZ2TerminalPopularRichHeightVolumeData rich) :
    PureWZ2TerminalPopularSelectedHeightLift richVolume := by
  let shading : WZ1PaperTubeShading terminal.sticky.selected.family := {
    carrier := fun index =>
      terminalSource.shading.carrier index ∩ richVolume.richSet
    measurable_carrier := fun index =>
      (terminalSource.shading.measurable_carrier index).inter
        richVolume.richSet_measurable
    subset_body := fun index => Set.inter_subset_left.trans
      (terminalSource.shading.subset_body index)
  }
  have hsub : PureWZ2PaperIsSubshading shading terminalSource.shading :=
    fun _ => Set.inter_subset_left
  have hunion : shading.union = richVolume.richSet := by
    apply Set.Subset.antisymm
    · rintro point ⟨_index, _hsource, hrich⟩
      exact hrich
    · intro point hrich
      rcases richVolume.richSet_subset_terminalSource hrich with
        ⟨index, hsource⟩
      exact ⟨index, hsource, hrich⟩
  have hconstant : shading.HasConstantMultiplicity
      terminalSource.multiplicity (2 * terminalSource.multiplicity) := by
    intro point hpoint
    have hmultiplicity : shading.pointMultiplicity point =
        terminalSource.shading.pointMultiplicity point := by
      unfold Kakeya.Streamlined.Shading.pointMultiplicity
      congr 1
      ext index
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, by rw [← hunion]; exact hpoint⟩
    rw [hmultiplicity]
    exact terminalSource.constant_multiplicity point
      (hsub.union_subset hpoint)
  exact {
    shading := shading
    carrier_eq := fun _ => rfl
    subshading := hsub
    union_eq := hunion
    constant_multiplicity := hconstant
    volume_lower := by rw [hunion]; exact richVolume.richSet_volume_lower
    multiplicity_mass_lower :=
      (constant_multiplicity_mass_volume_generic hconstant).1
  }

end Kakeya.Assouad
