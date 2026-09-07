import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalRichCells

/-!
# Whole-cell source shading carried by Alternative-A rich cells

This is the carrier-faithful pullback step.  It retains the actual balanced
`rho`-cells selected by the rich height set, but every source carrier is still
cut only by complete original `delta`-cells.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2SourceAlternativeARichShading
    {sigma inputLoss delta rho middleLoss outputLoss theoremEta epsilon : ℝ}
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
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {graphParents : PureWZ2SourceHorizontalGraphParentData prep}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
    {ready : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceAlternativeAHeightData ready epsilon}
    (richCells : PureWZ2SourceAlternativeARichCells
      (graphParents := graphParents) rich) where
  region : Set Point3 :=
    ⋃ cell ∈ richCells.cells, wz1PaperGridCube rho cell
  region_eq : region =
    ⋃ cell ∈ richCells.cells, wz1PaperGridCube rho cell
  region_measurable : MeasurableSet region
  shading : WZ1PaperTubeShading source.family
  carrier_eq : ∀ index, shading.carrier index =
    pullback.shading.carrier index ∩ region
  subshading : PureWZ2PaperIsSubshading shading source.shading
  subshading_retained :
    PureWZ2PaperIsSubshading shading retained.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  union_eq : shading.union = pullback.shading.union ∩ region
  volume_eq : MeasureTheory.volume shading.union =
    (richCells.cells.card : ENNReal) *
      twoScale.coarse.balanced.cellMass
  mass_eq : shading.mass =
    (richCells.cells.card : ENNReal) *
      twoScale.coarse.balanced.incidenceMass
  rich_volume_lower :
    (rich.richF.card : ENNReal) *
        twoScale.coarse.balanced.cellMass ≤
      5 * MeasureTheory.volume shading.union
  rich_mass_lower :
    (rich.richF.card : ENNReal) *
        twoScale.coarse.balanced.incidenceMass ≤
      5 * shading.mass
  graph_weighted_volume_lower :
    ((rich.heightIndices.card * graph.residue.cells.card : ℕ) : ENNReal) *
        twoScale.coarse.balanced.cellMass ≤
      54 *
        (wz1Lemma23SnappedHeights graph.residue.cells).card *
          MeasureTheory.volume shading.union
  graph_weighted_mass_lower :
    ((rich.heightIndices.card * graph.residue.cells.card : ℕ) : ENNReal) *
        twoScale.coarse.balanced.incidenceMass ≤
      54 *
        (wz1Lemma23SnappedHeights graph.residue.cells).card *
          shading.mass

theorem PureWZ2SourceAlternativeARichCells.toRichShading
    {sigma inputLoss delta rho middleLoss outputLoss theoremEta epsilon : ℝ}
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
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {graphParents : PureWZ2SourceHorizontalGraphParentData prep}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
    {ready : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceAlternativeAHeightData ready epsilon}
    (richCells : PureWZ2SourceAlternativeARichCells
      (graphParents := graphParents) rich) :
    Nonempty (PureWZ2SourceAlternativeARichShading richCells) := by
  have hcellsPullback : richCells.cells ⊆ pullback.selectedCells := by
    intro cell hcell
    exact retained.selectedCells_subset (richCells.cells_subset hcell)
  let region : Set Point3 :=
    ⋃ cell ∈ richCells.cells, wz1PaperGridCube rho cell
  have hregionMeasurable : MeasurableSet region :=
    MeasurableSet.biUnion richCells.cells.finite_toSet.countable
      (fun cell _ => wz1PaperGridCube_measurable cell)
  let shading : WZ1PaperTubeShading source.family :=
    { carrier := fun index => pullback.shading.carrier index ∩ region
      measurable_carrier := fun index =>
        (pullback.shading.measurable_carrier index).inter hregionMeasurable
      subset_body := fun index => Set.inter_subset_left.trans
        (pullback.shading.subset_body index) }
  have hunion : shading.union = pullback.shading.union ∩ region := by
    ext point
    constructor
    · rintro ⟨index, hsource, hregion⟩
      exact ⟨⟨index, hsource⟩, hregion⟩
    · rintro ⟨⟨index, hsource⟩, hregion⟩
      exact ⟨index, hsource, hregion⟩
  have hsub : PureWZ2PaperIsSubshading shading source.shading := by
    intro index point hpoint
    exact pullback.subshading index hpoint.1
  have hsubRetained :
      PureWZ2PaperIsSubshading shading retained.shading := by
    intro index point hpoint
    rw [retained.carrier_eq]
    refine ⟨hpoint.1, ?_⟩
    rw [retained.selectedRegion_eq]
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨cell, hcell, hpointCell⟩
    exact Set.mem_iUnion₂.mpr
      ⟨cell, richCells.cells_subset hcell, hpointCell⟩
  have hwhole : WZ1PaperIsCubicalShading shading := by
    intro index point hpoint other hother
    have hpullOther := pullback.whole_cells index point hpoint.1 hother
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨selectedCell, hselectedCell, hpointSelected⟩
    have hpointPullback : point ∈ pullback.shading.carrier index := hpoint.1
    rw [pullback.carrier_eq] at hpointPullback
    rcases pullback.zeroExtension.carrier_support index point hpointPullback.1 with
      ⟨selectedIndex, _heq, hselectedFine⟩
    rcases twoScale.coarse.balanced.fine_cell_nested
        selectedIndex point hselectedFine with
      ⟨nestedCell, _hnestedActive, hnested⟩
    have hpointNested : point ∈ wz1PaperGridCube rho nestedCell := by
      rw [← twoScale.rhoRequested_eq]
      exact hnested ((mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) point).mpr rfl)
    have hcellEq : nestedCell = selectedCell :=
      ((mem_wz1PaperGridCube rho nestedCell point).mp hpointNested).symm.trans
        ((mem_wz1PaperGridCube rho selectedCell point).mp hpointSelected)
    exact ⟨hpullOther, Set.mem_iUnion₂.mpr
      ⟨selectedCell, hselectedCell, by
        rw [← hcellEq, ← twoScale.rhoRequested_eq]
        exact hnested hother⟩⟩
  have hcellVolume : ∀ cell ∈ richCells.cells,
      MeasureTheory.volume
          (shading.union ∩ wz1PaperGridCube rho cell) =
        twoScale.coarse.balanced.cellMass := by
    intro cell hcell
    rw [hunion]
    have hcellRegion : wz1PaperGridCube rho cell ⊆ region := by
      intro point hpoint
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpoint⟩
    rw [show (pullback.shading.union ∩ region) ∩
        wz1PaperGridCube rho cell =
      pullback.shading.union ∩ wz1PaperGridCube rho cell by
        ext point; simp only [Set.mem_inter_iff]; aesop]
    exact pullback.cell_mass cell (hcellsPullback hcell)
  have hcellMass : ∀ cell ∈ richCells.cells,
      (∑ sourceIndex : Fin source.family.card,
        MeasureTheory.volume
          (shading.carrier sourceIndex ∩
            wz1PaperGridCube rho cell)) =
        twoScale.coarse.balanced.incidenceMass := by
    intro cell hcell
    calc
      (∑ sourceIndex : Fin source.family.card,
          MeasureTheory.volume
            (shading.carrier sourceIndex ∩
              wz1PaperGridCube rho cell)) =
          ∑ sourceIndex : Fin source.family.card,
            MeasureTheory.volume
              (pullback.shading.carrier sourceIndex ∩
                wz1PaperGridCube rho cell) := by
        apply Finset.sum_congr rfl
        intro sourceIndex _
        rw [show shading.carrier sourceIndex =
          pullback.shading.carrier sourceIndex ∩ region from rfl]
        congr 1
        ext point
        constructor
        · rintro ⟨⟨hsource, _⟩, hpointCell⟩
          exact ⟨hsource, hpointCell⟩
        · rintro ⟨hsource, hpointCell⟩
          exact ⟨⟨hsource, Set.mem_iUnion₂.mpr
            ⟨cell, hcell, hpointCell⟩⟩, hpointCell⟩
      _ = twoScale.coarse.balanced.incidenceMass :=
        pullback.cell_incidence_mass cell (hcellsPullback hcell)
  have hvolume : MeasureTheory.volume shading.union =
      (richCells.cells.card : ENNReal) *
        twoScale.coarse.balanced.cellMass := by
    have hpartition : shading.union =
        ⋃ cell ∈ richCells.cells,
          shading.union ∩ wz1PaperGridCube rho cell := by
      rw [hunion]
      ext point
      constructor
      · rintro ⟨hpull, hregion⟩
        rcases Set.mem_iUnion₂.mp hregion with ⟨cell, hcell, hpointCell⟩
        exact Set.mem_iUnion₂.mpr ⟨cell, hcell, ⟨hpull, hregion⟩, hpointCell⟩
      · rintro hpoint
        rcases Set.mem_iUnion₂.mp hpoint with
          ⟨_cell, _hcell, hsource, _hpointCell⟩
        exact hsource
    rw [hpartition]
    have hdisjoint : (richCells.cells : Set (ℤ × ℤ × ℤ)).PairwiseDisjoint
        (fun cell => shading.union ∩ wz1PaperGridCube rho cell) := by
      intro first _ second _ hne
      exact (wz1PaperGridCube_disjoint hne).mono
        Set.inter_subset_right Set.inter_subset_right
    have hmeas : ∀ cell ∈ richCells.cells, MeasurableSet
        (shading.union ∩ wz1PaperGridCube rho cell) := by
      intro cell _
      exact (measurableSet_shading_union shading).inter
        (wz1PaperGridCube_measurable cell)
    rw [MeasureTheory.measure_biUnion_finset hdisjoint hmeas]
    calc
      (∑ cell ∈ richCells.cells,
          volume (shading.union ∩ wz1PaperGridCube rho cell)) =
          ∑ _cell ∈ richCells.cells,
            twoScale.coarse.balanced.cellMass := by
        apply Finset.sum_congr rfl
        exact hcellVolume
      _ = (richCells.cells.card : ENNReal) *
          twoScale.coarse.balanced.cellMass := by simp [Finset.sum_const]
  have hmass : shading.mass =
      (richCells.cells.card : ENNReal) *
        twoScale.coarse.balanced.incidenceMass := by
    have carrierPartition : ∀ sourceIndex : Fin source.family.card,
        shading.carrier sourceIndex =
          ⋃ cell ∈ richCells.cells,
            shading.carrier sourceIndex ∩ wz1PaperGridCube rho cell := by
      intro sourceIndex
      ext point
      constructor
      · intro hpoint
        rcases Set.mem_iUnion₂.mp hpoint.2 with
          ⟨cell, hcell, hpointCell⟩
        exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpoint, hpointCell⟩
      · intro hpoint
        rcases Set.mem_iUnion₂.mp hpoint with
          ⟨_cell, _hcell, hsource, _hpointCell⟩
        exact hsource
    have carrierVolume : ∀ sourceIndex : Fin source.family.card,
        MeasureTheory.volume (shading.carrier sourceIndex) =
          ∑ cell ∈ richCells.cells, MeasureTheory.volume
            (shading.carrier sourceIndex ∩ wz1PaperGridCube rho cell) := by
      intro sourceIndex
      calc
        MeasureTheory.volume (shading.carrier sourceIndex) =
            MeasureTheory.volume (⋃ cell ∈ richCells.cells,
              shading.carrier sourceIndex ∩ wz1PaperGridCube rho cell) :=
          congrArg MeasureTheory.volume (carrierPartition sourceIndex)
        _ = _ := by
          apply MeasureTheory.measure_biUnion_finset
          · intro first _ second _ hne
            exact (wz1PaperGridCube_disjoint hne).mono
              Set.inter_subset_right Set.inter_subset_right
          · intro cell _
            exact (shading.measurable_carrier sourceIndex).inter
              (wz1PaperGridCube_measurable cell)
    calc
      shading.mass = ∑ sourceIndex : Fin source.family.card,
          ∑ cell ∈ richCells.cells, MeasureTheory.volume
            (shading.carrier sourceIndex ∩ wz1PaperGridCube rho cell) := by
        apply Finset.sum_congr rfl
        intro sourceIndex _
        exact carrierVolume sourceIndex
      _ = ∑ cell ∈ richCells.cells,
          ∑ sourceIndex : Fin source.family.card, MeasureTheory.volume
            (shading.carrier sourceIndex ∩ wz1PaperGridCube rho cell) := by
        rw [Finset.sum_comm]
      _ = ∑ _cell ∈ richCells.cells,
          twoScale.coarse.balanced.incidenceMass := by
        apply Finset.sum_congr rfl
        exact hcellMass
      _ = (richCells.cells.card : ENNReal) *
          twoScale.coarse.balanced.incidenceMass := by simp [Finset.sum_const]
  have hcard : (rich.richF.card : ENNReal) ≤
      5 * (richCells.cells.card : ENNReal) := by
    exact_mod_cast richCells.cells_card
  have hrichVolume :
      (rich.richF.card : ENNReal) *
          twoScale.coarse.balanced.cellMass ≤
        5 * MeasureTheory.volume shading.union := by
    calc
      _ ≤ (5 * (richCells.cells.card : ENNReal)) *
          twoScale.coarse.balanced.cellMass := by gcongr
      _ = 5 * MeasureTheory.volume shading.union := by rw [hvolume]; ring
  have hrichMass :
      (rich.richF.card : ENNReal) *
          twoScale.coarse.balanced.incidenceMass ≤
        5 * shading.mass := by
    calc
      _ ≤ (5 * (richCells.cells.card : ENNReal)) *
          twoScale.coarse.balanced.incidenceMass := by gcongr
      _ = 5 * shading.mass := by rw [hmass]; ring
  have hgraphOwnerNat :
      rich.heightIndices.card * graph.residue.cells.card ≤
        54 * (wz1Lemma23SnappedHeights graph.residue.cells).card *
          richCells.cells.card := by
    calc
      rich.heightIndices.card * graph.residue.cells.card ≤
          graph.residue.heightFiberCost *
            (wz1Lemma23SnappedHeights graph.residue.cells).card *
              richCells.graphCells.card :=
        richCells.graphCells_card_lower
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
  have hgraphOwner :
      ((rich.heightIndices.card * graph.residue.cells.card : ℕ) : ENNReal) ≤
        54 * (wz1Lemma23SnappedHeights graph.residue.cells).card *
          (richCells.cells.card : ENNReal) := by
    exact_mod_cast hgraphOwnerNat
  have hgraphVolume :
      ((rich.heightIndices.card * graph.residue.cells.card : ℕ) : ENNReal) *
          twoScale.coarse.balanced.cellMass ≤
        54 * (wz1Lemma23SnappedHeights graph.residue.cells).card *
          MeasureTheory.volume shading.union := by
    calc
      _ ≤ (54 * (wz1Lemma23SnappedHeights graph.residue.cells).card *
            (richCells.cells.card : ENNReal)) *
          twoScale.coarse.balanced.cellMass := by gcongr
      _ = 54 * (wz1Lemma23SnappedHeights graph.residue.cells).card *
          MeasureTheory.volume shading.union := by rw [hvolume]; ring
  have hgraphMass :
      ((rich.heightIndices.card * graph.residue.cells.card : ℕ) : ENNReal) *
          twoScale.coarse.balanced.incidenceMass ≤
        54 * (wz1Lemma23SnappedHeights graph.residue.cells).card *
          shading.mass := by
    calc
      _ ≤ (54 * (wz1Lemma23SnappedHeights graph.residue.cells).card *
            (richCells.cells.card : ENNReal)) *
          twoScale.coarse.balanced.incidenceMass := by gcongr
      _ = 54 * (wz1Lemma23SnappedHeights graph.residue.cells).card *
          shading.mass := by rw [hmass]; ring
  exact ⟨{
    region := region
    region_eq := rfl
    region_measurable := hregionMeasurable
    shading := shading
    carrier_eq := fun _ => rfl
    subshading := hsub
    subshading_retained := hsubRetained
    whole_cells := hwhole
    union_eq := hunion
    volume_eq := hvolume
    mass_eq := hmass
    rich_volume_lower := hrichVolume
    rich_mass_lower := hrichMass
    graph_weighted_volume_lower := hgraphVolume
    graph_weighted_mass_lower := hgraphMass
  }⟩

/-- The rich whole-cell restriction keeps the same point-multiplicity band as
the sticky pullback.  This is the constant-multiplicity refinement used before
the Corollary-5.6 popularity thinning. -/
theorem PureWZ2SourceAlternativeARichShading.constantMultiplicity
    {sigma inputLoss delta rho middleLoss outputLoss theoremEta epsilon : ℝ}
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
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {graphParents : PureWZ2SourceHorizontalGraphParentData prep}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
    {ready : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp}
    {rich : PureWZ2SourceAlternativeAHeightData ready epsilon}
    {richCells : PureWZ2SourceAlternativeARichCells
      (graphParents := graphParents) rich}
    (richShading : PureWZ2SourceAlternativeARichShading richCells) :
    richShading.shading.HasConstantMultiplicity
      twoScale.coarse.fineMultiplicity
      (2 * twoScale.coarse.fineMultiplicity) := by
  have hambient := pullback.zeroExtension.constantMultiplicity
    twoScale.coarse.refined_multiplicity_band
  intro point hpoint
  have hpullback : point ∈ pullback.shading.union := by
    rcases hpoint with ⟨index, hindex⟩
    rw [richShading.carrier_eq] at hindex
    exact ⟨index, hindex.1⟩
  have hrichMultiplicity := wholeCellRestriction_pointMultiplicity_eq
    richShading.carrier_eq hpoint
  have hpullbackMultiplicity := wholeCellRestriction_pointMultiplicity_eq
    pullback.carrier_eq hpullback
  rw [hrichMultiplicity, hpullbackMultiplicity]
  exact hambient point (by
    rcases hpullback with ⟨index, hindex⟩
    rw [pullback.carrier_eq] at hindex
    exact ⟨index, hindex.1⟩)

end Kakeya.Assouad
