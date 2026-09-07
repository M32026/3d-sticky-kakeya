import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseCarrier
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalPopularCarrier

/-!
# Outer-popular restriction of the genuine coarse carrier

The source and genuine first-sticky coarse carriers are different indexed
families, but the fixed-bin construction selects the same spatial
side-`sqrt rho` parents.  This file records the exact set-theoretic bridge and
then restricts the ordinary active-cell shadow of the genuine coarse carrier
to the source-popular height region.

The restricted shadow is intentionally partial at the side-`rho` scale.  Its
union is the genuine coarse union intersected with the source height region;
no false whole-cell or unchanged-volume claim is made.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The original-family residue selected from a fixed bin is spatially
contained in the genuine first-sticky coarse carrier selected by the same
side-`sqrt rho` parents. -/
theorem PureWZ2SourceHorizontalFixedBinResidueShadingData.union_subset_coarseCarrier
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
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
    (retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue)
    (coarseCarrier : PureWZ2SourceFixedBinCoarseCarrierData residue) :
    retained.shading.union ⊆ coarseCarrier.shading.union := by
  intro point hpoint
  rw [retained.union_eq] at hpoint
  rcases Set.mem_iUnion₂.mp (by
      rw [retained.selectedRegion_eq] at hpoint
      exact hpoint.2) with ⟨cell, hcell, hpointCell⟩
  have hcellData : cell ∈ pullback.selectedCells ∧
      retained.cellParent cell ∈ residue.selected := by
    rw [retained.selectedCells_eq] at hcell
    exact Finset.mem_filter.mp hcell
  have hfineActive : cell ∈ wz1PaperActiveCells twoScale.fine.refined
      twoScale.coarseGrains.extremal.delta_pos := by
    rw [pullback.selectedCells_eq] at hcellData
    exact hcellData.1
  have hfine : point ∈ twoScale.fine.refined.union := by
    rw [twoScale.fine.refined_cubical.union_eq_activeCells
      twoScale.coarseGrains.extremal.delta_pos]
    exact Set.mem_iUnion₂.mpr ⟨cell, hfineActive, by
      simpa only [twoScale.rhoRequested_eq] using hpointCell⟩
  have hparent : point ∈ coarseCarrier.selectedRegion := by
    rw [coarseCarrier.selectedRegion_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨retained.cellParent cell, hcellData.2,
        retained.cell_parent cell hcellData.1 hpointCell⟩
  rw [coarseCarrier.union_eq]
  exact ⟨hfine, hparent⟩

/-- The genuine coarse active-cell shadow cut by the already selected source
height region.  This is the paper-faithful spatial input `E ⊆ R² × Z_S` for
the later Lemma-23 graph. -/
structure PureWZ2SourceFixedBinPopularCoarseCarrierData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      sourceWindow (256 * rho))
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    (retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue)
    (coarseCarrier : PureWZ2SourceFixedBinCoarseCarrierData residue) where
  ambientShadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily coarseCarrier.shading
      twoScale.coarseGrains.extremal.delta_pos) :=
    pureWZ2ActiveCellShading coarseCarrier.shading
      twoScale.coarseGrains.extremal.delta_pos
  ambientShadow_eq : ambientShadow =
    pureWZ2ActiveCellShading coarseCarrier.shading
      twoScale.coarseGrains.extremal.delta_pos
  shading : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily coarseCarrier.shading
      twoScale.coarseGrains.extremal.delta_pos)
  carrier_eq : ∀ index, shading.carrier index =
    ambientShadow.carrier index ∩ outerPopular.popular.heightRegion
  subshading : IsSubshading shading ambientShadow
  union_eq : shading.union =
    coarseCarrier.shading.union ∩ outerPopular.popular.heightRegion
  height_region : shading.union ⊆ outerPopular.popular.heightRegion
  source_subset :
    (retained.shading.union ∩ outerPopular.popular.shading.union) ⊆
      shading.union
  source_volume_lower :
    volume (retained.shading.union ∩
      outerPopular.popular.shading.union) ≤ volume shading.union

/-- Build the exact pointwise source-height restriction of a fixed-bin
genuine coarse carrier. -/
theorem PureWZ2SourceFixedBinCoarseCarrierData.restrictToOuterPopular
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      sourceWindow (256 * rho))
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    (retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue)
    (coarseCarrier : PureWZ2SourceFixedBinCoarseCarrierData residue) :
    Nonempty (PureWZ2SourceFixedBinPopularCoarseCarrierData
      outerPopular retained coarseCarrier) := by
  let ambientShadow := pureWZ2ActiveCellShading coarseCarrier.shading
    twoScale.coarseGrains.extremal.delta_pos
  let shading : Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily coarseCarrier.shading
        twoScale.coarseGrains.extremal.delta_pos) :=
    { carrier := fun index => ambientShadow.carrier index ∩
        outerPopular.popular.heightRegion
      measurable_carrier := fun index =>
        (ambientShadow.measurable_carrier index).inter
          outerPopular.popular.heightRegion_measurable
      subset_body := fun index => Set.inter_subset_left.trans
        (ambientShadow.subset_body index) }
  have hambientUnion : ambientShadow.union = coarseCarrier.shading.union :=
    pureWZ2ActiveCellShading_union coarseCarrier.shading
      twoScale.coarseGrains.extremal.delta_pos coarseCarrier.whole_cells
  have hunion : shading.union =
      coarseCarrier.shading.union ∩ outerPopular.popular.heightRegion := by
    ext point
    constructor
    · rintro ⟨index, hambient, hheight⟩
      exact ⟨by rw [← hambientUnion]; exact ⟨index, hambient⟩, hheight⟩
    · rintro ⟨hcoarse, hheight⟩
      have hambient : point ∈ ambientShadow.union := by
        rwa [hambientUnion]
      rcases hambient with ⟨index, hindex⟩
      exact ⟨index, hindex, hheight⟩
  have hsourceSubset :
      retained.shading.union ∩ outerPopular.popular.shading.union ⊆
        shading.union := by
    rintro point ⟨hretained, hpopular⟩
    rw [hunion]
    refine ⟨retained.union_subset_coarseCarrier coarseCarrier hretained, ?_⟩
    rw [outerPopular.popular.union_eq] at hpopular
    exact hpopular.2
  exact ⟨{
    ambientShadow := ambientShadow
    ambientShadow_eq := rfl
    shading := shading
    carrier_eq := fun _ => rfl
    subshading := fun _ => Set.inter_subset_left
    union_eq := hunion
    height_region := by rw [hunion]; exact Set.inter_subset_right
    source_subset := hsourceSubset
    source_volume_lower := measure_mono hsourceSubset
  }⟩

/--
The whole-`rho`-cell envelope of the source whole-cell envelope.

This is the quantitative alternative to `PureWZ2SourceFixedBinPopularCoarseCarrierData`:
it keeps every genuine coarse cell which meets the complete source-`delta`-cell
envelope of the source-popular height region.  Consequently it contains the
corresponding pointwise intersection and is a union of complete coarse cells.
Its points need not lie in the height region itself; the final field records
the two successive cell-diameter errors in the bounded-neighbour replacement.
-/
structure PureWZ2SourceFixedBinPopularCoarseCellEnvelopeData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      sourceWindow (256 * rho))
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    (retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue)
    (coarseCarrier : PureWZ2SourceFixedBinCoarseCarrierData residue) where
  ambientShadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily coarseCarrier.shading
      twoScale.coarseGrains.extremal.delta_pos) :=
    pureWZ2ActiveCellShading coarseCarrier.shading
      twoScale.coarseGrains.extremal.delta_pos
  ambientShadow_eq : ambientShadow =
    pureWZ2ActiveCellShading coarseCarrier.shading
      twoScale.coarseGrains.extremal.delta_pos
  selected : Finset
      (Fin (pureWZ2ActiveCellFamily coarseCarrier.shading
        twoScale.coarseGrains.extremal.delta_pos).card) :=
    Finset.univ.filter fun index =>
      (ambientShadow.carrier index ∩
        outerPopular.shading.union).Nonempty
  selected_eq : selected = Finset.univ.filter fun index =>
    (ambientShadow.carrier index ∩ outerPopular.shading.union).Nonempty
  shading : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily coarseCarrier.shading
      twoScale.coarseGrains.extremal.delta_pos)
  carrier_eq : ∀ index, shading.carrier index =
    if index ∈ selected then ambientShadow.carrier index else ∅
  subshading : IsSubshading shading ambientShadow
  selected_carrier_cell : ∀ index ∈ selected, shading.carrier index =
    wz1PaperGridCube twoScale.rhoRequested.1
      (((wz1PaperActiveCells coarseCarrier.shading
        twoScale.coarseGrains.extremal.delta_pos).equivFin.symm index).1)
  parentCellIndex : (ℤ × ℤ × ℤ) →
    Fin (pureWZ2ActiveCellFamily coarseCarrier.shading
      twoScale.coarseGrains.extremal.delta_pos).card
  parentCellIndex_mem : ∀ parent ∈ residue.selected,
    parentCellIndex parent ∈ selected
  parentCellIndex_cell : ∀ parent ∈ residue.selected,
    ((wz1PaperActiveCells coarseCarrier.shading
      twoScale.coarseGrains.extremal.delta_pos).equivFin.symm
        (parentCellIndex parent)).1 = retained.cellFor parent
  parentCellIndex_injective : Set.InjOn parentCellIndex residue.selected
  selected_parent_card : residue.selected.card ≤ selected.card
  parent_cells_volume_lower :
    (residue.selected.card : ENNReal) *
        volume (wz1PaperGridCube twoScale.rhoRequested.1 (0, 0, 0)) ≤
      volume shading.union
  union_eq : shading.union =
    ⋃ index ∈ selected, ambientShadow.carrier index
  source_envelope_intersection_subset :
    coarseCarrier.shading.union ∩ outerPopular.shading.union ⊆
      shading.union
  source_subset :
    retained.shading.union ∩ outerPopular.shading.union ⊆
      shading.union
  source_volume_lower :
    volume (retained.shading.union ∩
      outerPopular.shading.union) ≤ volume shading.union
  point_near_source_envelope : ∀ point ∈ shading.union,
    ∃ anchor ∈ outerPopular.shading.union,
      dist point anchor < 2 * rho
  point_near_height_region : ∀ point ∈ shading.union,
    ∃ anchor ∈ outerPopular.popular.heightRegion,
      dist point anchor < 2 * rho + 2 * delta

/-- If the source window is already supported on a prescribed collection of
side-`rho` cells, then the whole-cell coarse envelope constructed from that
window cannot introduce a new cell.  The coarse carrier may temporarily range
over complete second-cover parent fibres, but membership in `selected` gives a
point of the same literal grid cell in the source window, which identifies the
cell uniquely. -/
theorem PureWZ2SourceFixedBinPopularCoarseCellEnvelopeData.activeCells_subset_of_sourceWindow_cells
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
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
    {coarseCarrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    (envelope : PureWZ2SourceFixedBinPopularCoarseCellEnvelopeData
      outerPopular retained coarseCarrier)
    (cells : Finset (ℤ × ℤ × ℤ))
    (hsourceWindow : sourceWindow.shading.union ⊆
      wz2RetainedCellsUnion rho cells) :
    ∀ index ∈ envelope.selected,
      ((wz1PaperActiveCells coarseCarrier.shading
        twoScale.coarseGrains.extremal.delta_pos).equivFin.symm index).1 ∈
          cells := by
  intro index hindex
  rw [envelope.selected_eq] at hindex
  rcases (Finset.mem_filter.mp hindex).2 with
    ⟨point, hpointAmbient, hpointOuter⟩
  let cell := ((wz1PaperActiveCells coarseCarrier.shading
    twoScale.coarseGrains.extremal.delta_pos).equivFin.symm index).1
  have hpointCell : point ∈ wz1PaperGridCube rho cell := by
    rw [envelope.ambientShadow_eq] at hpointAmbient
    change point ∈ wz1PaperGridCube twoScale.rhoRequested.1 cell at hpointAmbient
    simpa only [twoScale.rhoRequested_eq] using hpointAmbient
  have hpointWindow : point ∈ sourceWindow.shading.union :=
    outerPopular.subshading_window.union_subset hpointOuter
  have hpointCells := hsourceWindow hpointWindow
  rw [wz2RetainedCellsUnion] at hpointCells
  rcases Set.mem_iUnion₂.mp hpointCells with
    ⟨owner, howner, hpointOwner⟩
  have heq : owner = cell :=
    ((mem_wz1PaperGridCube rho owner point).mp hpointOwner).symm.trans
      ((mem_wz1PaperGridCube rho cell point).mp hpointCell)
  rwa [heq] at howner

/-- Union-level form of
`activeCells_subset_of_sourceWindow_cells`.  Once the source fixed-line window
is supported on `cells`, the complete-cell coarse envelope remains supported
on exactly that ambient literal cell population. -/
theorem PureWZ2SourceFixedBinPopularCoarseCellEnvelopeData.union_subset_cells
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
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
    {coarseCarrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    (envelope : PureWZ2SourceFixedBinPopularCoarseCellEnvelopeData
      outerPopular retained coarseCarrier)
    (cells : Finset (ℤ × ℤ × ℤ))
    (hsourceWindow : sourceWindow.shading.union ⊆
      wz2RetainedCellsUnion rho cells) :
    envelope.shading.union ⊆ wz2RetainedCellsUnion rho cells := by
  intro point hpoint
  rw [envelope.union_eq] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint with
    ⟨index, hindex, hpointAmbient⟩
  let cell := ((wz1PaperActiveCells coarseCarrier.shading
    twoScale.coarseGrains.extremal.delta_pos).equivFin.symm index).1
  have hcell : cell ∈ cells :=
    envelope.activeCells_subset_of_sourceWindow_cells
      cells hsourceWindow index hindex
  rw [wz2RetainedCellsUnion]
  refine Set.mem_iUnion₂.mpr ⟨cell, hcell, ?_⟩
  rw [envelope.ambientShadow_eq] at hpointAmbient
  change point ∈ wz1PaperGridCube twoScale.rhoRequested.1 cell at hpointAmbient
  simpa only [twoScale.rhoRequested_eq] using hpointAmbient

/-- Any active side-`rho` cell of a whole-cell coarse envelope already occurs
in the source pullback that supplied its outer-popular source window.  This is
the no-ambient-reentry bridge used by the synchronized regional argument. -/
theorem PureWZ2SourceFixedBinPopularCoarseCellEnvelopeData.activeCells_subset_pullback
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
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
    {coarseCarrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    (envelope : PureWZ2SourceFixedBinPopularCoarseCellEnvelopeData
      outerPopular retained coarseCarrier) :
    ∀ index ∈ envelope.selected,
      ((wz1PaperActiveCells coarseCarrier.shading
        twoScale.coarseGrains.extremal.delta_pos).equivFin.symm index).1 ∈
          pullback.selectedCells := by
  intro index _
  let cell := ((wz1PaperActiveCells coarseCarrier.shading
    twoScale.coarseGrains.extremal.delta_pos).equivFin.symm index).1
  have hcellCoarse :
      cell ∈ wz1PaperActiveCells coarseCarrier.shading
        twoScale.coarseGrains.extremal.delta_pos := by
    exact ((wz1PaperActiveCells coarseCarrier.shading
      twoScale.coarseGrains.extremal.delta_pos).equivFin.symm index).2
  rw [mem_wz1PaperActiveCells] at hcellCoarse
  rcases hcellCoarse.2 with ⟨point, hpointCoarse, hpointCell⟩
  have hpointFine : point ∈ twoScale.fine.refined.union := by
    rw [coarseCarrier.union_eq] at hpointCoarse
    exact hpointCoarse.1
  rw [pullback.selectedCells_eq, mem_wz1PaperActiveCells]
  exact ⟨hcellCoarse.1, point, hpointFine, hpointCell⟩

/--
Select all complete genuine coarse cells meeting the source whole-cell
envelope of the popular height region.  Unlike the pointwise intersection,
this construction never loses a fraction of a selected coarse cell.
-/
theorem PureWZ2SourceFixedBinCoarseCarrierData.envelopeOuterPopularCells
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      sourceWindow (256 * rho))
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    (retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue)
    (coarseCarrier : PureWZ2SourceFixedBinCoarseCarrierData residue)
    (hwindowOuter : window.shading.union ⊆ outerPopular.shading.union) :
    Nonempty (PureWZ2SourceFixedBinPopularCoarseCellEnvelopeData
      outerPopular retained coarseCarrier) := by
  let hbase : 0 < twoScale.rhoRequested.1 :=
    twoScale.coarseGrains.extremal.delta_pos
  let ambientShadow := pureWZ2ActiveCellShading coarseCarrier.shading hbase
  let selected : Finset
      (Fin (pureWZ2ActiveCellFamily coarseCarrier.shading hbase).card) :=
    Finset.univ.filter fun index =>
      (ambientShadow.carrier index ∩
        outerPopular.shading.union).Nonempty
  let shading : Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily coarseCarrier.shading hbase) :=
    { carrier := fun index =>
        if index ∈ selected then ambientShadow.carrier index else ∅
      measurable_carrier := fun index => by
        by_cases hindex : index ∈ selected
        · simp only [hindex, if_true]
          exact ambientShadow.measurable_carrier index
        · simp only [hindex, if_false]
          exact MeasurableSet.empty
      subset_body := fun index => by
        by_cases hindex : index ∈ selected
        · simpa only [hindex, if_true] using ambientShadow.subset_body index
        · simp only [hindex, if_false, Set.empty_subset] }
  have hambientUnion : ambientShadow.union = coarseCarrier.shading.union :=
    pureWZ2ActiveCellShading_union coarseCarrier.shading hbase
      coarseCarrier.whole_cells
  have hunion : shading.union =
      ⋃ index ∈ selected, ambientShadow.carrier index := by
    ext point
    constructor
    · rintro ⟨index, hpoint⟩
      by_cases hindex : index ∈ selected
      · exact Set.mem_iUnion₂.mpr ⟨index, hindex, by
          simpa [shading, hindex] using hpoint⟩
      · simp [shading, hindex] at hpoint
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with ⟨index, hindex, hpointCarrier⟩
      refine ⟨index, ?_⟩
      change point ∈
        if index ∈ selected then ambientShadow.carrier index else ∅
      simp only [hindex, if_true]
      exact hpointCarrier
  have henvelopeIntersectionSubset :
      coarseCarrier.shading.union ∩ outerPopular.shading.union ⊆
        shading.union := by
    rintro point ⟨hcoarse, houter⟩
    have hambient : point ∈ ambientShadow.union := by
      rwa [hambientUnion]
    rcases hambient with ⟨index, hpointCarrier⟩
    rw [hunion]
    exact Set.mem_iUnion₂.mpr ⟨index, Finset.mem_filter.mpr
      ⟨Finset.mem_univ index, ⟨point, hpointCarrier, houter⟩⟩,
        hpointCarrier⟩
  have hsourceSubset :
      retained.shading.union ∩ outerPopular.shading.union ⊆
        shading.union := by
    rintro point ⟨hretained, houter⟩
    exact henvelopeIntersectionSubset
      ⟨retained.union_subset_coarseCarrier coarseCarrier hretained, houter⟩
  have hcellForActive : ∀ parent (hparent : parent ∈ residue.selected),
      retained.cellFor parent ∈
        wz1PaperActiveCells coarseCarrier.shading hbase := by
    intro parent hparent
    apply (mem_wz1PaperActiveCells coarseCarrier.shading hbase _).mpr
    refine ⟨?_, ?_⟩
    · let representative := line.representative (retained.sliceCellFor parent)
      have hindex :
          wz1PaperGridIndex twoScale.rhoRequested.1 representative =
            retained.cellFor parent := by
        rw [twoScale.rhoRequested_eq]
        exact (mem_wz1PaperGridCube rho (retained.cellFor parent)
          representative).mp
            (retained.sliceRepresentative_mem_cellFor parent hparent)
      have hcoarse : representative ∈
          twoScale.coarseGrains.shading.union := by
        apply coarseCarrier.subshading.union_subset
        apply retained.union_subset_coarseCarrier coarseCarrier
        exact retained.sliceRepresentative_mem parent hparent
      rcases hcoarse with ⟨coarseIndex, hcoarseIndex⟩
      rw [← hindex]
      exact paper_point_gridIndex_in_window hbase
        (twoScale.coarseGrains.shading.subset_body
          coarseIndex hcoarseIndex).2
    · let representative := line.representative (retained.sliceCellFor parent)
      have hcoarse : representative ∈ coarseCarrier.shading.union := by
        apply retained.union_subset_coarseCarrier coarseCarrier
        exact retained.sliceRepresentative_mem parent hparent
      exact ⟨representative, hcoarse, by
        simpa only [twoScale.rhoRequested_eq] using
          retained.sliceRepresentative_mem_cellFor parent hparent⟩
  let parentCellIndex : (ℤ × ℤ × ℤ) →
      Fin (pureWZ2ActiveCellFamily coarseCarrier.shading hbase).card :=
    fun parent =>
      if hparent : parent ∈ residue.selected then
        (wz1PaperActiveCells coarseCarrier.shading hbase).equivFin
          ⟨retained.cellFor parent, hcellForActive parent hparent⟩
      else
        (wz1PaperActiveCells coarseCarrier.shading hbase).equivFin
          ⟨retained.cellFor (Classical.choose residue.selected_nonempty),
            hcellForActive _ (Classical.choose_spec residue.selected_nonempty)⟩
  have hparentIndexCell : ∀ parent (hparent : parent ∈ residue.selected),
      ((wz1PaperActiveCells coarseCarrier.shading hbase).equivFin.symm
        (parentCellIndex parent)).1 = retained.cellFor parent := by
    intro parent hparent
    simp only [parentCellIndex, dif_pos hparent, Equiv.symm_apply_apply]
  have hparentIndexMem : ∀ parent (hparent : parent ∈ residue.selected),
      parentCellIndex parent ∈ selected := by
    intro parent hparent
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    let representative := line.representative (retained.sliceCellFor parent)
    refine ⟨representative, ?_, ?_⟩
    · change representative ∈ wz1PaperGridCube twoScale.rhoRequested.1
        (((wz1PaperActiveCells coarseCarrier.shading hbase).equivFin.symm
          (parentCellIndex parent)).1)
      rw [hparentIndexCell parent hparent]
      simpa only [twoScale.rhoRequested_eq] using
        retained.sliceRepresentative_mem_cellFor parent hparent
    · have hwindow := line.representative_mem
        (retained.sliceCellFor parent)
        (retained.sliceCellFor_mem parent hparent)
      exact hwindowOuter hwindow
  have hparentIndexInjective :
      Set.InjOn parentCellIndex residue.selected := by
    intro first hfirst second hsecond heq
    have hcellEq : retained.cellFor first = retained.cellFor second := by
      rw [← hparentIndexCell first hfirst, ← hparentIndexCell second hsecond, heq]
    exact retained.cellFor_injective hfirst hsecond hcellEq
  have hparentCard : residue.selected.card ≤ selected.card := by
    rw [← Finset.card_image_of_injOn hparentIndexInjective]
    exact Finset.card_le_card (by
      intro index hindex
      rcases Finset.mem_image.mp hindex with ⟨parent, hparent, rfl⟩
      exact hparentIndexMem parent hparent)
  let parentCells := residue.selected.image retained.cellFor
  have hparentCellsCard : parentCells.card = residue.selected.card := by
    exact Finset.card_image_of_injOn retained.cellFor_injective
  have hparentCellsSubset :
      (⋃ cell ∈ parentCells, wz1PaperGridCube rho cell) ⊆
        shading.union := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
    rcases Finset.mem_image.mp hcell with ⟨parent, hparent, rfl⟩
    rw [hunion]
    refine Set.mem_iUnion₂.mpr
      ⟨parentCellIndex parent, hparentIndexMem parent hparent, ?_⟩
    change point ∈ wz1PaperGridCube twoScale.rhoRequested.1
      (((wz1PaperActiveCells coarseCarrier.shading hbase).equivFin.symm
        (parentCellIndex parent)).1)
    rw [hparentIndexCell parent hparent, twoScale.rhoRequested_eq]
    exact hpointCell
  have hparentVolume :
      (residue.selected.card : ENNReal) *
          volume (wz1PaperGridCube twoScale.rhoRequested.1 (0, 0, 0)) ≤
        volume shading.union := by
    calc
      (residue.selected.card : ENNReal) *
            volume (wz1PaperGridCube twoScale.rhoRequested.1 (0, 0, 0)) =
          volume (⋃ cell ∈ parentCells, wz1PaperGridCube rho cell) := by
        rw [wz1PaperGridCube_volume_biUnion line.rho_pos, hparentCellsCard,
          twoScale.rhoRequested_eq]
      _ ≤ volume shading.union := measure_mono hparentCellsSubset
  have hnearEnvelope : ∀ point ∈ shading.union,
      ∃ anchor ∈ outerPopular.shading.union,
        dist point anchor < 2 * rho := by
    intro point hpoint
    rw [hunion] at hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨index, hindex, hpointCarrier⟩
    have hselected := (Finset.mem_filter.mp hindex).2
    rcases hselected with ⟨anchor, hanchorCarrier, hanchorOuter⟩
    refine ⟨anchor, hanchorOuter, ?_⟩
    have hdist := wz1_paper_grid_cube_diameter_lt_two_rho hbase
      hpointCarrier hanchorCarrier
    simpa only [twoScale.rhoRequested_eq] using hdist
  have hnearHeight : ∀ point ∈ shading.union,
      ∃ anchor ∈ outerPopular.popular.heightRegion,
        dist point anchor < 2 * rho + 2 * delta := by
    intro point hpoint
    rcases hnearEnvelope point hpoint with
      ⟨sourceAnchor, hsourceAnchor, hcoarseDistance⟩
    rcases outerPopular.shading_point_near_height_region
        sourceAnchor hsourceAnchor with
      ⟨heightAnchor, hheightAnchor, hsourceDistance⟩
    refine ⟨heightAnchor, hheightAnchor, ?_⟩
    exact lt_of_le_of_lt (dist_triangle point sourceAnchor heightAnchor)
      (add_lt_add hcoarseDistance hsourceDistance)
  exact ⟨{
    ambientShadow := ambientShadow
    ambientShadow_eq := rfl
    selected := selected
    selected_eq := rfl
    shading := shading
    carrier_eq := fun _ => rfl
    subshading := by
      intro index
      by_cases hindex : index ∈ selected
      · simpa [shading, hindex]
      · simp [shading, hindex]
    selected_carrier_cell := by
      intro index hindex
      change (if index ∈ selected then ambientShadow.carrier index else ∅) = _
      simp only [hindex, if_true]
      rfl
    parentCellIndex := parentCellIndex
    parentCellIndex_mem := hparentIndexMem
    parentCellIndex_cell := hparentIndexCell
    parentCellIndex_injective := hparentIndexInjective
    selected_parent_card := hparentCard
    parent_cells_volume_lower := hparentVolume
    union_eq := hunion
    source_envelope_intersection_subset := henvelopeIntersectionSubset
    source_subset := hsourceSubset
    source_volume_lower := measure_mono hsourceSubset
    point_near_source_envelope := hnearEnvelope
    point_near_height_region := hnearHeight
  }⟩

theorem PureWZ2SourceFixedBinPopularCoarseCellEnvelopeData.union_subset_coarse
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
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
    {coarseCarrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    (envelope : PureWZ2SourceFixedBinPopularCoarseCellEnvelopeData
      outerPopular retained coarseCarrier) :
    envelope.shading.union ⊆ coarseCarrier.shading.union := by
  intro point hpoint
  have hambient := envelope.subshading.union_subset hpoint
  have hunion : envelope.ambientShadow.union =
      coarseCarrier.shading.union := by
    rw [envelope.ambientShadow_eq]
    exact pureWZ2ActiveCellShading_union coarseCarrier.shading
      twoScale.coarseGrains.extremal.delta_pos coarseCarrier.whole_cells
  rwa [hunion] at hambient

end Kakeya.Assouad

end
