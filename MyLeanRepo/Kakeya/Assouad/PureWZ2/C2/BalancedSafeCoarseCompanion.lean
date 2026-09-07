import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.BalancedSafeWindowBlocks
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CoarseRegionSourcePullback
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CoarseGlobalPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceWindowHeightPopularity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalParents
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarsePopularCarrier
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarsePreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarsePipeline
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseRichHeightSaturation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseEnvelopeHeightBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalFineWitnesses
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.FixedLineCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalGlobalBinFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.DenseCubicalImageContainment
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperActiveCellLogBound

/-!
# Genuine-coarse companions of balanced safe source blocks

Every safe source block is indexed by a literal set of side-`rho` cells.
This module uses exactly that same cell set to restrict the second sticky
fine shading, viewed on the genuine first-sticky coarse family.  The resulting
source/coarse pair retains the exact two-cover cross identity needed before
any fixed-line, global-bin, or rich-height choice.

In particular, the physical side-`rho` cube remains a common factor.  No
standalone `rho ^ 3` lower bound and no comparison between unrelated unions
is introduced.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The active cells stored by the second sticky balanced cover are physical
active cells of its cropped coarse shading. -/
theorem PureWZ2OneScaleTwoScaleStickyData.fine_balanced_activeCells_subset
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent) :
    twoScale.fine.balanced.activeCells ⊆
      wz1PaperActiveCells twoScale.fine.croppedCoarseShading
        twoScale.fine.coarse_extremal.delta_pos := by
  intro cell hcell
  let point : Point3 := cellCorner twoScale.sqrtRequested.1 cell
  have hpointCell : point ∈
      wz1PaperGridCube twoScale.sqrtRequested.1 cell :=
    cellCorner_mem_gridCube twoScale.fine.coarse_extremal.delta_pos cell
  have hpointUnion : point ∈ twoScale.fine.croppedCoarseShading.union := by
    rw [twoScale.fine.balanced.coarse_union_eq]
    exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointCell⟩
  rcases hpointUnion with ⟨index, hpointCarrier⟩
  have hpointBody := twoScale.fine.croppedCoarseShading.subset_body
    index hpointCarrier
  have hwindow : wz1PaperGridIndex twoScale.sqrtRequested.1 point ∈
      wz1PaperGridIndicesInWindow twoScale.sqrtRequested.1
        twoScale.fine.coarse_extremal.delta_pos :=
    paper_point_gridIndex_in_window
      twoScale.fine.coarse_extremal.delta_pos hpointBody.2
  have hindex : wz1PaperGridIndex twoScale.sqrtRequested.1 point = cell :=
    (mem_wz1PaperGridCube twoScale.sqrtRequested.1 cell point).mp hpointCell
  rw [hindex] at hwindow
  rw [mem_wz1PaperActiveCells]
  exact ⟨hwindow, ⟨point, ⟨index, hpointCarrier⟩, hpointCell⟩⟩

/-- The genuine-coarse restriction indexed by the exact cells of one safe
source block. -/
structure PureWZ2BalancedSafeCoarseCompanionData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (safe : PureWZ2BalancedSafeBlockFamilyData prepared)
    (block : {block // block ∈ safe.blocks}) where
  zeroExtension :
    WZ2PaperSubfamilyZeroExtensionData
      twoScale.fine.selected twoScale.fine.refined
  shading : WZ1PaperTubeShading twoScale.coarse.coarse
  carrier_eq : ∀ index, shading.carrier index =
    zeroExtension.ambientShading.carrier index ∩
      wz2RetainedCellsUnion twoScale.rhoRequested.1
        (safe.blockWindow block).cells
  subshading : PureWZ2PaperIsSubshading
    shading twoScale.coarseGrains.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  union_eq : shading.union =
    wz2RetainedCellsUnion twoScale.rhoRequested.1
      (safe.blockWindow block).cells
  volume_eq : volume shading.union =
    ((safe.blockWindow block).cells.card : ENNReal) *
      volume (wz1PaperGridCube rho (0, 0, 0))
  sourcePullback : PureWZ2SelectedCoarseRegionSourcePullbackData shading
  sourcePullback_selectedCells : sourcePullback.selectedCells =
    (safe.blockWindow block).cells
  sourcePullback_mass_eq : sourcePullback.shading.mass =
    ((safe.blockWindow block).cells.card : ENNReal) *
      twoScale.coarse.balanced.incidenceMass
  block_volume_cross :
    volume (safe.blockWindow block).shading.union *
        volume (wz1PaperGridCube rho (0, 0, 0)) =
      volume shading.union * twoScale.coarse.balanced.cellMass
  block_source_unit_cross :
    volume (safe.blockWindow block).shading.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          volume (wz1PaperGridCube rho (0, 0, 0)) ≤
      volume shading.union * twoScale.coarse.balanced.incidenceMass
  block_volume_mul_multiplicity_le_source_mass :
    volume (safe.blockWindow block).shading.union *
        (twoScale.coarse.fineMultiplicity : ENNReal) ≤
      sourcePullback.shading.mass

/-- Construct the coarse companion without changing the safe phase or block
selection. -/
theorem PureWZ2BalancedSafeBlockFamilyData.coarseCompanion
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (safe : PureWZ2BalancedSafeBlockFamilyData prepared)
    (block : {block // block ∈ safe.blocks}) :
    Nonempty (PureWZ2BalancedSafeCoarseCompanionData safe block) := by
  let cells := (safe.blockWindow block).cells
  have hcellsPullback : cells ⊆ pullback.selectedCells := by
    intro cell hcell
    change cell ∈ (safe.blockWindow block).cells at hcell
    rw [(safe.blockWindow block).cells_eq,
      pureWZ2BalancedSafeWindowCells] at hcell
    exact (Finset.mem_filter.mp hcell).1
  have hcellsFine : cells ⊆ wz1PaperActiveCells twoScale.fine.refined
      twoScale.coarseGrains.extremal.delta_pos := by
    intro cell hcell
    rw [← pullback.selectedCells_eq]
    exact hcellsPullback hcell
  rcases wz2_paper_subfamily_zero_extension
      twoScale.fine.selected twoScale.fine.refined with
    ⟨zeroExtension⟩
  have hzeroCubical : WZ1PaperIsCubicalShading
      zeroExtension.ambientShading :=
    zeroExtension.cubical twoScale.fine.refined_cubical
  have hcellsAmbient : cells ⊆
      wz1PaperActiveCells zeroExtension.ambientShading
        twoScale.coarseGrains.extremal.delta_pos := by
    intro cell hcell
    have hfine := hcellsFine hcell
    rw [mem_wz1PaperActiveCells] at hfine ⊢
    refine ⟨hfine.1, ?_⟩
    rcases hfine.2 with ⟨point, hpoint, hpointCell⟩
    rw [← zeroExtension.union_eq] at hpoint
    exact ⟨point, hpoint, hpointCell⟩
  let shading : WZ1PaperTubeShading twoScale.coarse.coarse :=
    wz2RefinedShading zeroExtension.ambientShading cells
  have hunion : shading.union =
      wz2RetainedCellsUnion twoScale.rhoRequested.1 cells := by
    exact wz2RefinedShading_union_eq hzeroCubical
      twoScale.coarseGrains.extremal.delta_pos hcellsAmbient
  have hsub : PureWZ2PaperIsSubshading
      shading twoScale.coarseGrains.shading := by
    intro index point hpoint
    have hzero : point ∈ zeroExtension.ambientShading.carrier index :=
      hpoint.1
    rcases zeroExtension.carrier_support index point hzero with
      ⟨selectedIndex, heq, hselected⟩
    subst index
    exact twoScale.fine.subshading selectedIndex hselected
  have hwhole : WZ1PaperIsCubicalShading shading :=
    wz2RefinedShading_cubical hzeroCubical
  have hvolume : volume shading.union =
      (cells.card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
    rw [hunion]
    have hraw := wz1PaperGridCube_volume_biUnion
      twoScale.coarseGrains.extremal.delta_pos cells
    simpa only [wz2RetainedCellsUnion, twoScale.rhoRequested_eq] using hraw
  rcases pureWZ2_pullback_selected_coarse_region shading hsub hwhole with
    ⟨sourcePullback⟩
  have hsourceCells : sourcePullback.selectedCells = cells := by
    rw [sourcePullback.selectedCells_eq]
    apply Finset.Subset.antisymm
    · intro cell hcell
      rw [mem_wz1PaperActiveCells] at hcell
      rcases hcell.2 with ⟨point, hpointShading, hpointCell⟩
      rw [hunion, wz2RetainedCellsUnion] at hpointShading
      rcases Set.mem_iUnion₂.mp hpointShading with
        ⟨owner, howner, hpointOwner⟩
      have hcellEq : owner = cell :=
        ((mem_wz1PaperGridCube twoScale.rhoRequested.1 owner point).mp
          hpointOwner).symm.trans
        ((mem_wz1PaperGridCube twoScale.rhoRequested.1 cell point).mp
          hpointCell)
      rwa [hcellEq] at howner
    · intro cell hcell
      have hambient := hcellsAmbient hcell
      rw [mem_wz1PaperActiveCells] at hambient ⊢
      refine ⟨hambient.1, ?_⟩
      rcases hambient.2 with ⟨point, _hpointAmbient, hpointCell⟩
      refine ⟨point, ?_, hpointCell⟩
      rw [hunion, wz2RetainedCellsUnion]
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointCell⟩
  have hsourceMass : sourcePullback.shading.mass =
      (cells.card : ENNReal) *
        twoScale.coarse.balanced.incidenceMass := by
    rw [sourcePullback.mass_eq, hsourceCells]
  have hcross :
      volume (safe.blockWindow block).shading.union *
          volume (wz1PaperGridCube rho (0, 0, 0)) =
        volume shading.union * twoScale.coarse.balanced.cellMass := by
    rw [(safe.blockWindow block).volume_eq, hvolume]
    ring
  have hsourceUnit :
      volume (safe.blockWindow block).shading.union *
            (twoScale.coarse.fineMultiplicity : ENNReal) *
            volume (wz1PaperGridCube rho (0, 0, 0)) ≤
        volume shading.union * twoScale.coarse.balanced.incidenceMass := by
    calc
      _ = (volume (safe.blockWindow block).shading.union *
            volume (wz1PaperGridCube rho (0, 0, 0))) *
          (twoScale.coarse.fineMultiplicity : ENNReal) := by ring
      _ = (volume shading.union *
            twoScale.coarse.balanced.cellMass) *
          (twoScale.coarse.fineMultiplicity : ENNReal) := by rw [hcross]
      _ = volume shading.union *
          ((twoScale.coarse.fineMultiplicity : ENNReal) *
            twoScale.coarse.balanced.cellMass) := by ring
      _ ≤ volume shading.union *
          twoScale.coarse.balanced.incidenceMass := by
        exact mul_le_mul_left'
          twoScale.coarse.balanced_incidenceMass_band.1 _
  have hblockMass :
      volume (safe.blockWindow block).shading.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) ≤
        sourcePullback.shading.mass := by
    calc
      _ = ((safe.blockWindow block).cells.card : ENNReal) *
          (twoScale.coarse.balanced.cellMass *
            (twoScale.coarse.fineMultiplicity : ENNReal)) := by
        rw [(safe.blockWindow block).volume_eq]
        ring
      _ ≤ ((safe.blockWindow block).cells.card : ENNReal) *
          twoScale.coarse.balanced.incidenceMass := by
        apply mul_le_mul_left'
        simpa [mul_comm] using
          twoScale.coarse.balanced_incidenceMass_band.1
      _ = sourcePullback.shading.mass := by
        rw [hsourceMass]
  exact ⟨{
    zeroExtension := zeroExtension
    shading := shading
    carrier_eq := fun _ => rfl
    subshading := hsub
    whole_cells := hwhole
    union_eq := hunion
    volume_eq := by simpa [cells] using hvolume
    sourcePullback := sourcePullback
    sourcePullback_selectedCells := by simpa [cells] using hsourceCells
    sourcePullback_mass_eq := by simpa [cells] using hsourceMass
    block_volume_cross := hcross
    block_source_unit_cross := hsourceUnit
    block_volume_mul_multiplicity_le_source_mass := hblockMass
  }⟩

/-- The synchronized genuine-coarse companion on every safe block. -/
structure PureWZ2BalancedSafeCoarseCompanionFamilyData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (safe : PureWZ2BalancedSafeBlockFamilyData prepared) where
  companion : ∀ block : {block // block ∈ safe.blocks},
    PureWZ2BalancedSafeCoarseCompanionData safe block

theorem PureWZ2BalancedSafeBlockFamilyData.coarseCompanions
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (safe : PureWZ2BalancedSafeBlockFamilyData prepared) :
    Nonempty (PureWZ2BalancedSafeCoarseCompanionFamilyData safe) := by
  refine ⟨{ companion := ?_ }⟩
  intro block
  exact Classical.choice (safe.coarseCompanion block)

/-- The exact same-cell comparison in the orientation used by the regional
selection.  Both sides count the companion's literal side-`rho` cells; the
first balanced-cover incidence mass and physical cube volume are the only
conversion factors. -/
theorem PureWZ2BalancedSafeCoarseCompanionData.sourcePullback_mass_mul_cube
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block) :
    data.sourcePullback.shading.mass *
          volume (wz1PaperGridCube rho (0, 0, 0)) =
      volume data.shading.union *
        twoScale.coarse.balanced.incidenceMass := by
  rw [data.sourcePullback_mass_eq, data.volume_eq]
  ring

/-- The exact first-cover pullback of a safe block has the same spatial union
as the active-cell block shading.  The two shadings have different index
families, so this equality is recorded explicitly before applying source-side
popularity. -/
theorem PureWZ2BalancedSafeCoarseCompanionData.sourcePullback_union_eq_blockWindow
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block) :
    data.sourcePullback.shading.union =
      (safe.blockWindow block).shading.union := by
  have hblockCells : (safe.blockWindow block).cells ⊆
      pullback.selectedCells := by
    intro cell hcell
    rw [(safe.blockWindow block).cells_eq,
      pureWZ2BalancedSafeWindowCells] at hcell
    exact (Finset.mem_filter.mp hcell).1
  have hregionSubset : (safe.blockWindow block).region ⊆
      pullback.selectedRegion := by
    intro point hpoint
    rw [(safe.blockWindow block).region_eq] at hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
    rw [pullback.selectedRegion_eq]
    exact Set.mem_iUnion₂.mpr ⟨cell, hblockCells hcell, hpointCell⟩
  have hselectedRegion : data.sourcePullback.selectedRegion =
      (safe.blockWindow block).region := by
    calc
      data.sourcePullback.selectedRegion = data.shading.union :=
        data.sourcePullback.selectedRegion_eq_coarse
      _ = wz2RetainedCellsUnion twoScale.rhoRequested.1
          (safe.blockWindow block).cells := data.union_eq
      _ = (safe.blockWindow block).region := by
        rw [(safe.blockWindow block).region_eq]
        simp only [wz2RetainedCellsUnion, twoScale.rhoRequested_eq]
  rw [data.sourcePullback.union_eq,
    data.sourcePullback.zeroExtension.union_eq, hselectedRegion,
    (safe.blockWindow block).union_eq, prepared.shadow_union,
    pullback.union_eq, pullback.zeroExtension.union_eq]
  ext point
  constructor
  · rintro ⟨hsource, hblock⟩
    exact ⟨⟨hsource, hregionSubset hblock⟩, hblock⟩
  · rintro ⟨⟨hsource, _hselected⟩, hblock⟩
    exact ⟨hsource, hblock⟩

/-- The exact first-cover pullback of a safe block inherits the first sticky
factor-two multiplicity band. -/
theorem PureWZ2BalancedSafeCoarseCompanionData.sourcePullback_constantMultiplicity
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block) :
    data.sourcePullback.shading.HasConstantMultiplicity
      twoScale.coarse.fineMultiplicity
      (2 * twoScale.coarse.fineMultiplicity) := by
  have hambient := data.sourcePullback.zeroExtension.constantMultiplicity
    twoScale.coarse.refined_multiplicity_band
  intro point hpoint
  have hmultiplicity := wholeCellRestriction_pointMultiplicity_eq
    data.sourcePullback.carrier_eq hpoint
  rw [hmultiplicity]
  apply hambient point
  rcases hpoint with ⟨index, hindex⟩
  rw [data.sourcePullback.carrier_eq index] at hindex
  exact ⟨index, hindex.1⟩

/-- Restrict the exact source-family pullback of one safe block to the same
outer-popular union used to select its fixed slice. -/
def PureWZ2BalancedSafeCoarseCompanionData.outerPopularSourcePullback
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)) :
    WZ1PaperTubeShading source.family where
  carrier index := data.sourcePullback.shading.carrier index ∩
    outerPopular.popular.shading.union
  measurable_carrier index :=
    (data.sourcePullback.shading.measurable_carrier index).inter
      (measurableSet_shading_union outerPopular.popular.shading)
  subset_body index := Set.inter_subset_left.trans
    (data.sourcePullback.shading.subset_body index)

/-- Restrict the exact source-family pullback to the complete source-cell
envelope of the outer-popular height set.  This is the carrier on which the
subsequent fixed-line selection is actually performed. -/
def PureWZ2BalancedSafeCoarseCompanionData.outerPopularEnvelopeSourcePullback
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)) :
    WZ1PaperTubeShading source.family where
  carrier index := data.sourcePullback.shading.carrier index ∩
    outerPopular.shading.union
  measurable_carrier index :=
    (data.sourcePullback.shading.measurable_carrier index).inter
      (measurableSet_shading_union outerPopular.shading)
  subset_body index := Set.inter_subset_left.trans
    (data.sourcePullback.shading.subset_body index)

/-- Complete side-`rho` cells of the same companion which meet the
outer-popular source envelope.  Unlike a pointwise height cut, this is a
cubical coarse subshading and can therefore be pulled back exactly. -/
structure PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)) where
  cells : Finset (ℤ × ℤ × ℤ) :=
    (safe.blockWindow block).cells.filter fun cell =>
      (wz1PaperGridCube rho cell ∩ outerPopular.shading.union).Nonempty
  cells_eq : cells =
    (safe.blockWindow block).cells.filter fun cell =>
      (wz1PaperGridCube rho cell ∩ outerPopular.shading.union).Nonempty
  cells_nonempty : cells.Nonempty
  shading : WZ1PaperTubeShading twoScale.coarse.coarse :=
    wz2RefinedShading data.shading cells
  shading_eq : shading = wz2RefinedShading data.shading cells
  subshading : PureWZ2PaperIsSubshading shading data.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  union_eq : shading.union = wz2RetainedCellsUnion rho cells
  activeCells_eq :
    wz1PaperActiveCells shading
      twoScale.coarseGrains.extremal.delta_pos = cells
  volume_eq : volume shading.union =
    (cells.card : ENNReal) * volume (wz1PaperGridCube rho (0, 0, 0))
  source_envelope_subset : outerPopular.shading.union ⊆ shading.union
  sourcePullback : PureWZ2SelectedCoarseRegionSourcePullbackData shading
  sourcePullback_selectedCells : sourcePullback.selectedCells = cells
  sourceEnvelopePullback_sub_sourcePullback :
    PureWZ2PaperIsSubshading
      (data.outerPopularEnvelopeSourcePullback outerPopular)
      sourcePullback.shading
  sourcePullback_mass_cross :
    sourcePullback.shading.mass *
          volume (wz1PaperGridCube rho (0, 0, 0)) =
      volume shading.union * twoScale.coarse.balanced.incidenceMass

/-- The second-cover parent assignment restricted to the exact outer-popular
envelope cells.  It is defined from genuine points of `fine.refined`, hence
every stored parent and containment belongs to the actual second sticky
balanced cover. -/
structure PureWZ2BalancedSafeOuterPopularCoarseParentData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular) where
  witness : (ℤ × ℤ × ℤ) → Point3
  witness_mem_refined : ∀ cell ∈ envelope.cells,
    witness cell ∈ twoScale.fine.refined.union
  witness_mem_cell : ∀ cell ∈ envelope.cells,
    witness cell ∈ wz1PaperGridCube rho cell
  fineIndex : (ℤ × ℤ × ℤ) →
    Fin twoScale.fine.selected.family.card
  witness_mem_carrier : ∀ cell ∈ envelope.cells,
    witness cell ∈ twoScale.fine.refined.carrier (fineIndex cell)
  parentCell : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ)
  parent_active : ∀ cell ∈ envelope.cells,
    parentCell cell ∈ twoScale.fine.balanced.activeCells
  cell_parent : ∀ cell ∈ envelope.cells,
    wz1PaperGridCube rho cell ⊆
      wz1PaperGridCube twoScale.sqrtRequested.1 (parentCell cell)
  parents : Finset (ℤ × ℤ × ℤ) := envelope.cells.image parentCell
  parents_eq : parents = envelope.cells.image parentCell
  parents_nonempty : parents.Nonempty
  parents_subset : parents ⊆ twoScale.fine.balanced.activeCells
  cellsForParent : (ℤ × ℤ × ℤ) → Finset (ℤ × ℤ × ℤ) :=
    fun parent => envelope.cells.filter fun cell => parentCell cell = parent
  cellsForParent_eq : ∀ parent, cellsForParent parent =
    envelope.cells.filter fun cell => parentCell cell = parent
  cell_count_partition : envelope.cells.card =
    ∑ parent ∈ parents, (cellsForParent parent).card

/-- Dyadic regularization of the number of synchronized side-`rho` cells
below each genuine second-cover parent. -/
structure PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    (parents : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope) where
  bins : ℕ
  bins_eq : bins = Nat.log 2 (2 * parents.parents.card) + 1
  selectedParents : Finset (ℤ × ℤ × ℤ)
  selectedParents_nonempty : selectedParents.Nonempty
  selectedParents_subset : selectedParents ⊆ parents.parents
  weightFloor : ENNReal
  weightFloor_pos : 0 < weightFloor
  half_le_weightFloor : (1 / 2 : ENNReal) ≤ weightFloor
  one_le_two_mul_weightFloor : (1 : ENNReal) ≤ 2 * weightFloor
  weight_band : ∀ parent ∈ selectedParents,
    weightFloor ≤ (parents.cellsForParent parent).card ∧
      ((parents.cellsForParent parent).card : ENNReal) ≤ 2 * weightFloor
  retained_weight : (envelope.cells.card : ENNReal) ≤
    2 * (bins : ENNReal) *
      ∑ parent ∈ selectedParents,
        ((parents.cellsForParent parent).card : ENNReal)

/-- The dyadic parent-weight bin count is bounded by the physical active-cell
logarithm of the second sticky cover. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData.bins_le_activeCellLog
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parents : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    (weightClass : PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
      data outerPopular envelope parents) :
    weightClass.bins ≤
      Nat.log 2 (2 * twoScale.fine.balanced.activeCells.card) + 1 := by
  rw [weightClass.bins_eq]
  apply Nat.add_le_add_right
  apply Nat.log_mono_right
  gcongr
  exact parents.parents_subset

/-- Rewrite the preceding combinatorial bound using the physical cropped-grid
logarithmic envelope at scale `sqrt rho`. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData.bins_le_logEnvelope
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parents : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    (weightClass : PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
      data outerPopular envelope parents) :
    (weightClass.bins : ENNReal) ≤
      2 * ENNReal.ofReal
        (wz2PaperBoundaryLogCoefficient *
          (1 + Real.log twoScale.sqrtRequested.1⁻¹)) := by
  have hcard : twoScale.fine.balanced.activeCells.card ≤
      (wz1PaperActiveCells twoScale.fine.croppedCoarseShading
        twoScale.fine.coarse_extremal.delta_pos).card :=
    Finset.card_le_card twoScale.fine_balanced_activeCells_subset
  let activeCount := (wz1PaperActiveCells
    twoScale.fine.croppedCoarseShading
      twoScale.fine.coarse_extremal.delta_pos).card
  have hactiveNonempty : 0 < activeCount := by
    apply Finset.card_pos.mpr
    exact parents.parents_nonempty.mono
      (parents.parents_subset.trans
        twoScale.fine_balanced_activeCells_subset)
  have hlogDouble : Nat.log 2 (2 * activeCount) + 1 =
      (Nat.log 2 activeCount + 1) + 1 := by
    rw [show 2 * activeCount = activeCount * 2 by omega,
      Nat.log_mul_base (by omega) hactiveNonempty.ne']
  have hlogNat : weightClass.bins ≤
      (Nat.log 2 activeCount + 1) + 1 := by
    rw [hlogDouble.symm]
    exact weightClass.bins_le_activeCellLog.trans (by
      apply Nat.add_le_add_right
      apply Nat.log_mono_right
      exact Nat.mul_le_mul_left 2 hcard)
  have hphysical :
      ((Nat.log 2
        (wz1PaperActiveCells twoScale.fine.croppedCoarseShading
          twoScale.fine.coarse_extremal.delta_pos).card + 1 : ℕ) :
        ENNReal) ≤
      ENNReal.ofReal
        (wz2PaperBoundaryLogCoefficient *
          (1 + Real.log twoScale.sqrtRequested.1⁻¹)) :=
    wz2_paper_active_cell_log_bound_ennreal
      twoScale.fine.coarse_extremal.delta_pos
      twoScale.fine.coarse_extremal.delta_le_one
      twoScale.fine.croppedCoarseShading
  have honePhysical : (1 : ENNReal) ≤
      ENNReal.ofReal
        (wz2PaperBoundaryLogCoefficient *
          (1 + Real.log twoScale.sqrtRequested.1⁻¹)) := by
    calc
      (1 : ENNReal) ≤ ((Nat.log 2 activeCount + 1 : ℕ) : ENNReal) := by
        exact_mod_cast (show 1 ≤ Nat.log 2 activeCount + 1 by omega)
      _ ≤ _ := hphysical
  have hlogCast : (weightClass.bins : ENNReal) ≤
      ((Nat.log 2 activeCount + 1 : ℕ) : ENNReal) + 1 := by
    exact_mod_cast hlogNat
  calc
    (weightClass.bins : ENNReal) ≤
        ((Nat.log 2 activeCount + 1 : ℕ) : ENNReal) + 1 := hlogCast
    _ ≤ ENNReal.ofReal
          (wz2PaperBoundaryLogCoefficient *
            (1 + Real.log twoScale.sqrtRequested.1⁻¹)) +
        ENNReal.ofReal
          (wz2PaperBoundaryLogCoefficient *
            (1 + Real.log twoScale.sqrtRequested.1⁻¹)) :=
      add_le_add hphysical honePhysical
    _ = _ := by ring

/-- Construct the genuine second-cover parent partition without leaving the
outer-popular envelope's exact side-`rho` cell population. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData.toCoarseParents
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular) :
    Nonempty (PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope) := by
  have hwitnessExists :
      ∀ cell (hcell : cell ∈ envelope.cells),
        ∃ point, point ∈ twoScale.fine.refined.union ∧
          point ∈ wz1PaperGridCube rho cell := by
    intro cell hcell
    have hblockCell : cell ∈ (safe.blockWindow block).cells := by
      rw [envelope.cells_eq] at hcell
      exact (Finset.mem_filter.mp hcell).1
    have hpullbackCell : cell ∈ pullback.selectedCells := by
      rw [(safe.blockWindow block).cells_eq,
        pureWZ2BalancedSafeWindowCells] at hblockCell
      exact (Finset.mem_filter.mp hblockCell).1
    rw [pullback.selectedCells_eq, mem_wz1PaperActiveCells] at hpullbackCell
    rcases hpullbackCell.2 with ⟨point, hpointRefined, hpointCell⟩
    exact ⟨point, hpointRefined, by
      simpa only [twoScale.rhoRequested_eq] using hpointCell⟩
  let witness : (ℤ × ℤ × ℤ) → Point3 := fun cell =>
    if hcell : cell ∈ envelope.cells then
      Classical.choose (hwitnessExists cell hcell)
    else 0
  have hwitness :
      ∀ cell (hcell : cell ∈ envelope.cells),
        witness cell ∈ twoScale.fine.refined.union ∧
          witness cell ∈ wz1PaperGridCube rho cell := by
    intro cell hcell
    simp only [witness, dif_pos hcell]
    exact Classical.choose_spec (hwitnessExists cell hcell)
  let fineIndex : (ℤ × ℤ × ℤ) →
      Fin twoScale.fine.selected.family.card := fun cell =>
    if hcell : cell ∈ envelope.cells then
      Classical.choose (hwitness cell hcell).1
    else ⟨0, twoScale.fine.selected_nonempty⟩
  have hwitnessCarrier :
      ∀ cell (hcell : cell ∈ envelope.cells),
        witness cell ∈ twoScale.fine.refined.carrier (fineIndex cell) := by
    intro cell hcell
    simp only [fineIndex, dif_pos hcell]
    exact Classical.choose_spec (hwitness cell hcell).1
  have hnestedExists :
      ∀ cell (hcell : cell ∈ envelope.cells),
        ∃ parent ∈ twoScale.fine.balanced.activeCells,
          wz1PaperGridCube twoScale.rhoRequested.1
              (wz1PaperGridIndex twoScale.rhoRequested.1 (witness cell)) ⊆
            wz1PaperGridCube twoScale.sqrtRequested.1 parent := by
    intro cell hcell
    exact twoScale.fine.balanced.fine_cell_nested
      (fineIndex cell) (witness cell) (hwitnessCarrier cell hcell)
  let parentCell : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) := fun cell =>
    if hcell : cell ∈ envelope.cells then
      Classical.choose (hnestedExists cell hcell)
    else (0, 0, 0)
  have hparentActive :
      ∀ cell (hcell : cell ∈ envelope.cells),
        parentCell cell ∈ twoScale.fine.balanced.activeCells := by
    intro cell hcell
    simp only [parentCell, dif_pos hcell]
    exact (Classical.choose_spec (hnestedExists cell hcell)).1
  have hindexEq :
      ∀ cell (hcell : cell ∈ envelope.cells),
        wz1PaperGridIndex twoScale.rhoRequested.1 (witness cell) = cell := by
    intro cell hcell
    rw [twoScale.rhoRequested_eq]
    exact (mem_wz1PaperGridCube rho cell (witness cell)).mp
      (hwitness cell hcell).2
  have hnested :
      ∀ cell (hcell : cell ∈ envelope.cells),
        wz1PaperGridCube rho cell ⊆
          wz1PaperGridCube twoScale.sqrtRequested.1 (parentCell cell) := by
    intro cell hcell
    have hraw := (Classical.choose_spec (hnestedExists cell hcell)).2
    simp only [parentCell, dif_pos hcell]
    have hsource :
        wz1PaperGridCube rho cell =
          wz1PaperGridCube twoScale.rhoRequested.1
            (wz1PaperGridIndex twoScale.rhoRequested.1 (witness cell)) := by
      rw [hindexEq cell hcell]
      congr 1
      exact twoScale.rhoRequested_eq.symm
    rw [hsource]
    exact hraw
  let parents := envelope.cells.image parentCell
  have hparentsNonempty : parents.Nonempty :=
    envelope.cells_nonempty.image parentCell
  have hparentsSubset : parents ⊆ twoScale.fine.balanced.activeCells := by
    intro parent hparent
    rcases Finset.mem_image.mp hparent with ⟨cell, hcell, rfl⟩
    exact hparentActive cell hcell
  let cellsForParent : (ℤ × ℤ × ℤ) → Finset (ℤ × ℤ × ℤ) :=
    fun parent => envelope.cells.filter fun cell => parentCell cell = parent
  have hmaps : Set.MapsTo parentCell
      (envelope.cells : Set (ℤ × ℤ × ℤ))
      (envelope.cells.image parentCell : Set (ℤ × ℤ × ℤ)) :=
    fun cell hcell => Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
  have hpartition : envelope.cells.card =
      ∑ parent ∈ parents, (cellsForParent parent).card := by
    simpa [parents, cellsForParent] using
      Finset.card_eq_sum_card_fiberwise hmaps
  exact ⟨{
    witness := witness
    witness_mem_refined := fun cell hcell => (hwitness cell hcell).1
    witness_mem_cell := fun cell hcell => (hwitness cell hcell).2
    fineIndex := fineIndex
    witness_mem_carrier := hwitnessCarrier
    parentCell := parentCell
    parent_active := hparentActive
    cell_parent := hnested
    parents := parents
    parents_eq := rfl
    parents_nonempty := hparentsNonempty
    parents_subset := hparentsSubset
    cellsForParent := cellsForParent
    cellsForParent_eq := fun _ => rfl
    cell_count_partition := hpartition
  }⟩

/-- Regularize the exact number of envelope cells below each second-cover
parent.  This is the missing weighted-to-unweighted bridge needed by the
fixed-line parent count. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseParentData.regularizeWeight
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    (parents : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope) :
    Nonempty (PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
      data outerPopular envelope parents) := by
  let parentType := {parent // parent ∈ parents.parents}
  let weight : parentType → ENNReal := fun parent =>
    (parents.cellsForParent parent.1).card
  let total : ENNReal := envelope.cells.card
  have htotal : total = ∑ parent : parentType, weight parent := by
    rw [show total = (envelope.cells.card : ENNReal) by rfl,
      parents.cell_count_partition]
    simpa [parentType, weight] using
      (Finset.sum_attach parents.parents fun parent =>
        ((parents.cellsForParent parent).card : ENNReal)).symm
  have htotalTop : total ≠ ⊤ := by
    simp [total]
  have htotalPos : 0 < total := by
    dsimp only [total]
    exact_mod_cast envelope.cells_nonempty.card_pos
  rcases ennreal_dyadic_bin weight total htotal htotalTop htotalPos with
    ⟨bins, selected, hbins, hselected, hretained, _hthreshold,
      weightFloor, hweightFloor, hweightBand⟩
  let selectedParents := selected.image Subtype.val
  have hselectedInjective : Set.InjOn
      (Subtype.val : parentType → (ℤ × ℤ × ℤ)) selected :=
    fun _ _ _ _ h => Subtype.ext h
  have hselectedSubset : selectedParents ⊆ parents.parents := by
    intro parent hparent
    rcases Finset.mem_image.mp hparent with ⟨parentIndex, _hindex, rfl⟩
    exact parentIndex.property
  have hselectedSum :
      (∑ parent ∈ selectedParents,
          ((parents.cellsForParent parent).card : ENNReal)) =
        ∑ parent ∈ selected, weight parent := by
    exact Finset.sum_image hselectedInjective
  have hretained' : (envelope.cells.card : ENNReal) ≤
      2 * (bins : ENNReal) *
        ∑ parent ∈ selectedParents,
          ((parents.cellsForParent parent).card : ENNReal) := by
    rw [show (envelope.cells.card : ENNReal) = total by rfl,
      hselectedSum]
    have htwo : total ≤
        2 * ((∑ parent ∈ selected, weight parent) * bins) := by
      calc
        total = total / 2 + total / 2 :=
          (ENNReal.add_halves total).symm
        _ ≤ (∑ parent ∈ selected, weight parent) * bins +
            (∑ parent ∈ selected, weight parent) * bins := by
          exact add_le_add hretained hretained
        _ = 2 * ((∑ parent ∈ selected, weight parent) * bins) := by ring
    simpa [mul_comm, mul_left_comm, mul_assoc] using htwo
  have hhalfLeWeightFloor : (1 / 2 : ENNReal) ≤ weightFloor := by
    rcases hselected with ⟨parentIndex, hparentIndex⟩
    have hparentWeightOne : (1 : ENNReal) ≤ weight parentIndex := by
      have hparent : parentIndex.1 ∈
          envelope.cells.image parents.parentCell := by
        simpa only [parents.parents_eq] using parentIndex.property
      rcases Finset.mem_image.mp hparent with ⟨cell, hcell, heq⟩
      have hcellFiber : cell ∈ parents.cellsForParent parentIndex.1 := by
        rw [parents.cellsForParent_eq]
        exact Finset.mem_filter.mpr ⟨hcell, heq⟩
      dsimp only [weight]
      exact_mod_cast (show (parents.cellsForParent parentIndex.1).Nonempty from
        ⟨cell, hcellFiber⟩).card_pos
    have hbandUpper := (hweightBand parentIndex hparentIndex).2
    apply (ENNReal.div_le_iff (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)).mpr
    calc
      (1 : ENNReal) ≤ weight parentIndex := hparentWeightOne
      _ ≤ 2 * weightFloor := hbandUpper
      _ = weightFloor * 2 := mul_comm _ _
  have honeLeTwoWeightFloor : (1 : ENNReal) ≤ 2 * weightFloor := by
    rcases hselected with ⟨parentIndex, hparentIndex⟩
    have hparentWeightOne : (1 : ENNReal) ≤ weight parentIndex := by
      have hparent : parentIndex.1 ∈
          envelope.cells.image parents.parentCell := by
        simpa only [parents.parents_eq] using parentIndex.property
      rcases Finset.mem_image.mp hparent with ⟨cell, hcell, heq⟩
      have hcellFiber : cell ∈ parents.cellsForParent parentIndex.1 := by
        rw [parents.cellsForParent_eq]
        exact Finset.mem_filter.mpr ⟨hcell, heq⟩
      dsimp only [weight]
      exact_mod_cast (show (parents.cellsForParent parentIndex.1).Nonempty from
        ⟨cell, hcellFiber⟩).card_pos
    exact le_trans hparentWeightOne (hweightBand parentIndex hparentIndex).2
  exact ⟨{
    bins := bins
    bins_eq := by
      simpa [parentType, Fintype.card_subtype] using hbins
    selectedParents := selectedParents
    selectedParents_nonempty := hselected.image _
    selectedParents_subset := hselectedSubset
    weightFloor := weightFloor
    weightFloor_pos := hweightFloor
    half_le_weightFloor := hhalfLeWeightFloor
    one_le_two_mul_weightFloor := honeLeTwoWeightFloor
    weight_band := by
      intro parent hparent
      rcases Finset.mem_image.mp hparent with
        ⟨parentIndex, hparentIndex, heq⟩
      subst parent
      simpa [weight] using hweightBand parentIndex hparentIndex
    retained_weight := hretained'
  }⟩

/-- One finite fiber of an outer-popular envelope's exact side-`rho` cells.
The source pullback is rebuilt from that literal cell subset, so the selected
weight and original-family mass keep the same first-cover provenance. -/
structure PureWZ2BalancedSafeOuterPopularCoarseCellFiberData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    {β : Type*} [Fintype β] [DecidableEq β]
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    (color : (ℤ × ℤ × ℤ) → β) where
  target : β
  cells : Finset (ℤ × ℤ × ℤ) :=
    envelope.cells.filter fun cell => color cell = target
  cells_eq : cells = envelope.cells.filter fun cell => color cell = target
  cells_nonempty : cells.Nonempty
  shading : WZ1PaperTubeShading twoScale.coarse.coarse :=
    wz2RefinedShading envelope.shading cells
  shading_eq : shading = wz2RefinedShading envelope.shading cells
  subshading : PureWZ2PaperIsSubshading shading envelope.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  union_eq : shading.union = wz2RetainedCellsUnion rho cells
  activeCells_eq :
    wz1PaperActiveCells shading
      twoScale.coarseGrains.extremal.delta_pos = cells
  volume_eq : volume shading.union =
    (cells.card : ENNReal) * volume (wz1PaperGridCube rho (0, 0, 0))
  sourcePullback : PureWZ2SelectedCoarseRegionSourcePullbackData shading
  sourcePullback_selectedCells : sourcePullback.selectedCells = cells
  sourcePullback_mass_eq : sourcePullback.shading.mass =
    (cells.card : ENNReal) * twoScale.coarse.balanced.incidenceMass
  retained_mass : envelope.sourcePullback.shading.mass ≤
    (Fintype.card β : ENNReal) * sourcePullback.shading.mass

/-- An arbitrary nonempty literal subset of the synchronized envelope cells,
with its genuine-coarse shading and exact first-cover pullback. -/
structure PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    (cells : Finset (ℤ × ℤ × ℤ)) where
  cells_subset : cells ⊆ envelope.cells
  cells_nonempty : cells.Nonempty
  shading : WZ1PaperTubeShading twoScale.coarse.coarse :=
    wz2RefinedShading envelope.shading cells
  shading_eq : shading = wz2RefinedShading envelope.shading cells
  subshading : PureWZ2PaperIsSubshading shading envelope.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  union_eq : shading.union = wz2RetainedCellsUnion rho cells
  activeCells_eq :
    wz1PaperActiveCells shading
      twoScale.coarseGrains.extremal.delta_pos = cells
  volume_eq : volume shading.union =
    (cells.card : ENNReal) * volume (wz1PaperGridCube rho (0, 0, 0))
  sourcePullback : PureWZ2SelectedCoarseRegionSourcePullbackData shading
  sourcePullback_selectedCells : sourcePullback.selectedCells = cells
  sourcePullback_mass_eq : sourcePullback.shading.mass =
    (cells.card : ENNReal) * twoScale.coarse.balanced.incidenceMass

/-- The literal side-`rho` cells below a regularized class of genuine
second-cover parents, together with the exact first-cover pullback and its
retained indexed mass. -/
structure PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    (parents : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope)
    (weightClass : PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
      data outerPopular envelope parents) where
  cells : Finset (ℤ × ℤ × ℤ) :=
    weightClass.selectedParents.biUnion parents.cellsForParent
  cells_eq : cells =
    weightClass.selectedParents.biUnion parents.cellsForParent
  cells_nonempty : cells.Nonempty
  cells_subset : cells ⊆ envelope.cells
  cells_card_eq : cells.card =
    ∑ parent ∈ weightClass.selectedParents,
      (parents.cellsForParent parent).card
  restriction : PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
    data outerPopular envelope cells
  retained_mass : envelope.sourcePullback.shading.mass ≤
    2 * (weightClass.bins : ENNReal) *
      restriction.sourcePullback.shading.mass

/-- The complete synchronized side-`rho` fibres below an arbitrary nonempty
subfamily of a regularized parent class.  The dyadic weight band converts
parent cardinality to literal-cell cardinality in both directions, while the
stored restriction preserves the exact first-cover pullback. -/
structure PureWZ2BalancedSafeOuterPopularCoarseParentSubfamilyRestrictionData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parents : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parents}
    (selectedParents : Finset (ℤ × ℤ × ℤ)) where
  selectedParents_nonempty : selectedParents.Nonempty
  selectedParents_subset : selectedParents ⊆ weightClass.selectedParents
  cells : Finset (ℤ × ℤ × ℤ) :=
    selectedParents.biUnion parents.cellsForParent
  cells_eq : cells = selectedParents.biUnion parents.cellsForParent
  cells_card_eq : cells.card =
    ∑ parent ∈ selectedParents, (parents.cellsForParent parent).card
  cellRestriction :
    PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
      data outerPopular envelope cells
  weight_lower :
    (selectedParents.card : ENNReal) * weightClass.weightFloor ≤
      (cells.card : ENNReal)
  weight_upper :
    (cells.card : ENNReal) ≤
      (selectedParents.card : ENNReal) * (2 * weightClass.weightFloor)

/-- A finite label fibre selected inside an already materialized synchronized
cell restriction.  Unlike `selectCellFiber` on the ambient envelope, this
constructor cannot choose a label supported only on cells discarded by an
earlier parent-weight regularization. -/
structure PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionFiberData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {baseCells : Finset (ℤ × ℤ × ℤ)}
    (base : PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
      data outerPopular envelope baseCells)
    {β : Type*} [Fintype β] [DecidableEq β]
    (color : (ℤ × ℤ × ℤ) → β) where
  target : β
  cells : Finset (ℤ × ℤ × ℤ) :=
    baseCells.filter fun cell => color cell = target
  cells_eq : cells = baseCells.filter fun cell => color cell = target
  cells_nonempty : cells.Nonempty
  selectedRestriction :
    PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
      data outerPopular envelope cells
  retained_mass : base.sourcePullback.shading.mass ≤
    (Fintype.card β : ENNReal) *
      selectedRestriction.sourcePullback.shading.mass

/-- The source-side window carried by a synchronized coarse-cell restriction.
The ordinary shadow keeps the original active-cell family, while its union
and volume supply are exactly those of the restriction's first-cover
pullback. -/
structure PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {cells : Finset (ℤ × ℤ × ℤ)}
    (restriction : PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
      data outerPopular envelope cells) where
  shadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily pullback.shading source.extremal.delta_pos)
  carrier_eq : ∀ index, shadow.carrier index =
    (safe.blockWindow block).shading.carrier index ∩
      restriction.sourcePullback.shading.union
  subshading : IsSubshading shadow prepared.shadow
  union_eq : shadow.union = restriction.sourcePullback.shading.union
  window : PureWZ2SourceCarrierWindow prepared
  window_left : window.left = (safe.blockWindow block).window.left
  window_shading : window.shading = shadow
  window_supply : window.volumeSupply =
    volume restriction.sourcePullback.shading.union

/-- Original-source global-slope package on the genuine-coarse restriction.
The exact-slice certificate is deliberately explicit: its producer is the
coarse-to-source same-cell transport, while this record fixes the carrier on
which the subsequent Fubini and all-global-bin construction runs. -/
structure PureWZ2BalancedSafeOuterPopularCoarseOriginalGlobalData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {cells : Finset (ℤ × ℤ × ℤ)}
    (restriction : PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
      data outerPopular envelope cells) where
  shadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily restriction.shading
      twoScale.coarseGrains.extremal.delta_pos) :=
    pureWZ2ActiveCellShading restriction.shading
      twoScale.coarseGrains.extremal.delta_pos
  windowed : WZ1Lemma23WindowedGlobalSlicePackage
    (delta := twoScale.rhoRequested.1)
    (rho := twoScale.rhoRequested.1) (sigma := sigma) shadow
    (10 * Kakeya.realRpowENN rho (-middleLoss))
  sourceSlope_eq : windowed.global.sourceSlope = source.globalGrains.slope
  shadow_union : shadow.union = restriction.shading.union
  exactAD : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
    IsADSet1
      (scalarProjection
        (globalGrainDirection (source.globalGrains.slope z))
        (horizontalSlice restriction.shading.union z))
      rho (1 - sigma)
      (10 * Kakeya.realRpowENN rho (-middleLoss))

/-- The fixed line chosen directly from the genuine-coarse restriction.  Its
slice-area lower bound starts from the coarse whole-cell volume, not from the
source pullback volume. -/
structure PureWZ2BalancedSafeOuterPopularCoarseFixedLineData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {cells : Finset (ℤ × ℤ × ℤ)}
    {restriction : PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
      data outerPopular envelope cells}
    (global : PureWZ2BalancedSafeOuterPopularCoarseOriginalGlobalData
      restriction) where
  line : PureWZ2HorizontalFixedLineCore
    global.windowed source.globalGrains.slope
  line_shadow : global.shadow.union = restriction.shading.union

/-- All nonempty global-bin fibres of the restriction-native coarse fixed
line.  The exact slice partition is recorded before any graph-good choice. -/
structure PureWZ2BalancedSafeOuterPopularCoarseGlobalBinFamilyData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {cells : Finset (ℤ × ℤ × ℤ)}
    {restriction : PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
      data outerPopular envelope cells}
    {global : PureWZ2BalancedSafeOuterPopularCoarseOriginalGlobalData
      restriction}
    (fixedLine : PureWZ2BalancedSafeOuterPopularCoarseFixedLineData global) where
  core : ∀ bin : {bin // bin ∈ fixedLine.line.globalBins},
    PureWZ2HorizontalFixedBinCore
      global.windowed source.globalGrains.slope
  lineBin_eq : ∀ bin, (core bin).lineBin = bin.1
  heavyCells_eq : ∀ bin, (core bin).heavyCells =
    pureWZ2HorizontalGlobalBinCells fixedLine.line bin.1
  slice_card : fixedLine.line.sliceCells.card =
    ∑ bin : {bin // bin ∈ fixedLine.line.globalBins},
      (core bin).heavyCells.card
  rhoCell : ∀ bin : {bin // bin ∈ fixedLine.line.globalBins},
    (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) := fun bin cell =>
      wz1PaperGridIndex twoScale.rhoRequested.1
        ((core bin).representative cell)
  rhoCell_eq : ∀ bin cell, rhoCell bin cell =
    wz1PaperGridIndex twoScale.rhoRequested.1
      ((core bin).representative cell)
  rhoCell_mem : ∀ bin cell, cell ∈ (core bin).heavyCells →
    rhoCell bin cell ∈ cells
  representative_mem_rhoCell : ∀ bin cell, cell ∈ (core bin).heavyCells →
    (core bin).representative cell ∈
      wz1PaperGridCube twoScale.rhoRequested.1 (rhoCell bin cell)

/-- The original-source exact slice and its genuine second-cover parents,
selected only after restricting to the synchronized side-`rho` cell set. -/
structure PureWZ2BalancedSafeOuterPopularCoarseRestrictedFixedLineData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {cells : Finset (ℤ × ℤ × ℤ)}
    (restriction : PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
      data outerPopular envelope cells)
    (sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        restriction) where
  line : PureWZ2SourceHorizontalFixedLineData sourceWindow.window
  sourceParents : PureWZ2SourceHorizontalFixedBinParentData line.toFixedBinData
  rhoCell_mem : ∀ cell ∈ line.heavyCells,
    sourceParents.rhoCell cell ∈ cells
  parent_eq : ∀ cell (hcell : cell ∈ line.heavyCells),
    sourceParents.parentCell cell =
      parentData.parentCell (sourceParents.rhoCell cell)
  parents_subset : sourceParents.parents ⊆ parentData.parents

/-- All original-source global-bin fibres on one exact Fubini slice, with
their literal side-`rho` owners and genuine second-cover parents identified
inside the same synchronized coarse-cell restriction.  This is the
source-line alternative to transporting an unavailable exact-AD certificate
to the genuine-coarse shading. -/
structure PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {cells : Finset (ℤ × ℤ × ℤ)}
    (restriction : PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
      data outerPopular envelope cells)
    (sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        restriction) where
  line : PureWZ2SourceHorizontalFixedLineData sourceWindow.window
  core : ∀ bin : {bin // bin ∈ line.globalBins},
    PureWZ2SourceHorizontalFixedBinData sourceWindow.window
  lineBin_eq : ∀ bin, (core bin).lineBin = bin.1
  heavyCells_eq : ∀ bin, (core bin).heavyCells =
    pureWZ2SourceHorizontalGlobalBinCells line bin.1
  sourceParents : ∀ bin,
    PureWZ2SourceHorizontalFixedBinParentData (core bin)
  rhoCell_mem : ∀ bin cell, cell ∈ (core bin).heavyCells →
    (sourceParents bin).rhoCell cell ∈ cells
  parent_eq : ∀ bin cell (hcell : cell ∈ (core bin).heavyCells),
    (sourceParents bin).parentCell cell =
      parentData.parentCell ((sourceParents bin).rhoCell cell)
  parents_subset : ∀ bin,
    (sourceParents bin).parents ⊆ parentData.parents
  slice_card : line.sliceCells.card =
    ∑ bin : {bin // bin ∈ line.globalBins}, (core bin).heavyCells.card

/-- One source-selected global bin continued onto the complete synchronized
side-`rho` fibres of its selected second-cover parents.  All fields are kept
in one dependent record so the restricted graph preparation cannot be paired
with a carrier, parent family, or exact-slice certificate chosen elsewhere. -/
structure PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    (weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass)
    (sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction)
    (sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow)
    (bin : {bin // bin ∈ sourceBins.line.globalBins}) where
  selection : PureWZ2SourceHorizontalFixedBinYSelection
    (sourceBins.sourceParents bin)
  residue : PureWZ2SourceHorizontalFixedBinYResidueData selection
  retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue
  retained_graphShadow_union : retained.graphShadow.union = retained.shading.union
  coarseCarrier : PureWZ2SourceFixedBinCoarseCarrierData residue
  fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained
  original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
    coarseCarrier fineWitnesses.coarseWitnesses
  parentRestriction :
    PureWZ2BalancedSafeOuterPopularCoarseParentSubfamilyRestrictionData
      (weightClass := weightClass) residue.selected
  cells_active_in_carrier : parentRestriction.cells ⊆
    wz1PaperActiveCells coarseCarrier.shading
      twoScale.coarseGrains.extremal.delta_pos
  restrictedPreparation :
    PureWZ2SourceFixedBinCoarseCellRestrictionPreparationData
      original parentRestriction.cells
  prep_union_eq : restrictedPreparation.prep.shadow.union =
    parentRestriction.cellRestriction.shading.union

/-- The graph-good prefix built on one exact synchronized bin preparation.
The preparation remains an index, so all graph cells, internal popular
heights, and later `Z_lin` data are tied to the complete parent-fibre cell
restriction selected above. -/
structure PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinGraphData
    {sigma inputLoss delta rho middleLoss outputLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    {sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction}
    {sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow}
    {bin : {bin // bin ∈ sourceBins.line.globalBins}}
    (sync :
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
        weightRestriction sourceWindow sourceBins bin) where
  pipeline : PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
    (normalEta := normalEta) sync.restrictedPreparation.prep
  graph_input_union : sync.restrictedPreparation.prep.shadow.union =
    sync.parentRestriction.cellRestriction.shading.union

/-- The complete rich-height tail constructed from one synchronized graph
input.  Besides storing the dependent rich and saturation witnesses, this
record certifies that both the saturated coarse cells and their exact
first-cover pullback stay inside the complete parent fibres selected before
the graph argument. -/
structure PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinRichData
    {sigma inputLoss delta rho middleLoss outputLoss normalEta finalLoss
      theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    {sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction}
    {sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow}
    {bin : {bin // bin ∈ sourceBins.line.globalBins}}
    {sync :
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
        weightRestriction sourceWindow sourceBins bin}
    (graph : PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinGraphData
      (normalEta := normalEta) sync) where
  richOutput : PureWZ2SourceFixedBinCoarseRichPipelineAtPreparationData
    (finalLoss := finalLoss) (theoremEta := theoremEta) graph.pipeline
  saturation : PureWZ2SourceFixedBinCoarseRichHeightSaturationData
    richOutput.heightLift
  saturation_cells_subset : saturation.cells ⊆
    sync.parentRestriction.cells
  sourcePullback_selectedCells_eq :
    saturation.sourcePullback.selectedCells = saturation.cells
  sourcePullback_selectedCells_subset :
    saturation.sourcePullback.selectedCells ⊆
      sync.parentRestriction.cells

/-- The second exact-slice decomposition, now run on the literal coarse-cell
restriction selected by one source global bin.  Every nested global bin is
materialized as the image of its Lemma-23 cells in the paper `rho` grid, and
its graph preparation is obtained by monotone restriction of the same
original-slope certificate stored by `sync`. -/
structure PureWZ2BalancedSafeOuterPopularCoarseNestedGlobalBinFamilyData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    {sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction}
    {sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow}
    {bin : {bin // bin ∈ sourceBins.line.globalBins}}
    (sync :
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
        weightRestriction sourceWindow sourceBins bin) where
  global : PureWZ2BalancedSafeOuterPopularCoarseOriginalGlobalData
    sync.parentRestriction.cellRestriction
  fixedLine : PureWZ2BalancedSafeOuterPopularCoarseFixedLineData global
  bins : PureWZ2BalancedSafeOuterPopularCoarseGlobalBinFamilyData fixedLine
  cells : ∀ nestedBin : {nestedBin // nestedBin ∈ fixedLine.line.globalBins},
    Finset (ℤ × ℤ × ℤ) := fun nestedBin =>
      ((bins.core nestedBin).heavyCells.image (bins.rhoCell nestedBin))
  cells_eq : ∀ nestedBin, cells nestedBin =
    (bins.core nestedBin).heavyCells.image (bins.rhoCell nestedBin)
  cells_nonempty : ∀ nestedBin, (cells nestedBin).Nonempty
  cells_subset : ∀ nestedBin, cells nestedBin ⊆
    sync.parentRestriction.cells
  heavyCells_card_le : ∀ nestedBin,
    (bins.core nestedBin).heavyCells.card ≤ 125 * (cells nestedBin).card
  slice_card_le_sum_cells : fixedLine.line.sliceCells.card ≤
    125 * ∑ nestedBin : {nestedBin //
      nestedBin ∈ fixedLine.line.globalBins}, (cells nestedBin).card
  restriction : ∀ nestedBin,
    PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
      data outerPopular envelope (cells nestedBin)
  preparation : ∀ nestedBin,
    PureWZ2SourceFixedBinCoarseCellRestrictionPreparationData
      sync.original (cells nestedBin)
  prep_union_eq : ∀ nestedBin,
    (preparation nestedBin).prep.shadow.union =
      (restriction nestedBin).shading.union

/-- A nonempty collection of nested coarse global bins whose exact graph
preparations pass the common volume threshold. -/
structure PureWZ2BalancedSafeOuterPopularCoarseNestedGoodBinData
    {sigma inputLoss delta rho middleLoss outputLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    {sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction}
    {sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow}
    {bin : {bin // bin ∈ sourceBins.line.globalBins}}
    {sync :
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
        weightRestriction sourceWindow sourceBins bin}
    (nested :
      PureWZ2BalancedSafeOuterPopularCoarseNestedGlobalBinFamilyData sync) where
  selected : Finset {nestedBin //
    nestedBin ∈ nested.fixedLine.line.globalBins}
  selected_nonempty : selected.Nonempty
  volume_lower : ∀ nestedBin ∈ selected,
    Kakeya.realRpowENN (nested.preparation nestedBin).prep.graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      volume (nested.preparation nestedBin).prep.shadow.union
  total_volume_le :
    (∑ nestedBin : {nestedBin //
        nestedBin ∈ nested.fixedLine.line.globalBins},
        volume (nested.preparation nestedBin).prep.shadow.union) ≤
      2 * ∑ nestedBin ∈ selected,
        volume (nested.preparation nestedBin).prep.shadow.union

/-- The graph, `Z_lin`, whole-cell saturation, and exact source pullback for
every retained nested coarse global bin. -/
structure PureWZ2BalancedSafeOuterPopularCoarseNestedRichFamilyData
    {sigma inputLoss delta rho middleLoss outputLoss normalEta finalLoss
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    {sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction}
    {sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow}
    {bin : {bin // bin ∈ sourceBins.line.globalBins}}
    {sync :
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
        weightRestriction sourceWindow sourceBins bin}
    {nested :
      PureWZ2BalancedSafeOuterPopularCoarseNestedGlobalBinFamilyData sync}
    (good : PureWZ2BalancedSafeOuterPopularCoarseNestedGoodBinData
      (volumeLoss := volumeLoss) nested) where
  pipeline : ∀ nestedBin : {nestedBin // nestedBin ∈ good.selected},
    PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
      (normalEta := normalEta) (nested.preparation nestedBin.1).prep
  rich : ∀ nestedBin : {nestedBin // nestedBin ∈ good.selected},
    PureWZ2SourceFixedBinCoarseRichPipelineAtPreparationData
      (finalLoss := finalLoss) (theoremEta := theoremEta)
      (pipeline nestedBin)
  saturation : ∀ nestedBin : {nestedBin // nestedBin ∈ good.selected},
    PureWZ2SourceFixedBinCoarseRichHeightSaturationData
      (rich nestedBin).heightLift

/-- The geometric cost of a second exact-slice Fubini decomposition of a
side-`rho` cubical carrier.  The factor `125` is the exact finite-fibre cost
between the Lemma-23 diameter grid and the literal paper grid. -/
def pureWZ2BalancedSafeNestedCoarseVolumeCost (rho : ℝ) : ENNReal :=
  125 * ENNReal.ofReal (Real.sqrt rho + 2 * rho) *
    (ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi) /
      volume (wz1PaperGridCube rho (0, 0, 0))

/-- The dimensional form of the nested coarse Fubini cost.  The normalized
cost above is used to compare three-dimensional graph volumes; after the
rich-height pullback contributes one physical side-`rho` cube, this is the
cost that remains. -/
def pureWZ2BalancedSafeNestedCoarseRawVolumeCost (rho : ℝ) : ENNReal :=
  125 * ENNReal.ofReal (Real.sqrt rho + 2 * rho) *
    (ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi)

/-- The dimensional cost of the source exact-slice decomposition after all
source global bins are retained and each selected second-cover parent is
replaced by its complete regularized side-`rho` cell fibre. -/
def pureWZ2BalancedSafeSourceBinRawVolumeCost
    (rho delta : ℝ) : ENNReal :=
  ENNReal.ofReal (Real.sqrt rho + 2 * rho) *
    (ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi) *
    (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) * 23040

/-- The source-bin Fubini cost normalized by one physical side-`rho` cube. -/
def pureWZ2BalancedSafeSourceBinVolumeCost
    (rho delta : ℝ) : ENNReal :=
  pureWZ2BalancedSafeSourceBinRawVolumeCost rho delta /
    volume (wz1PaperGridCube rho (0, 0, 0))

/-- All dependent choices below one synchronized outer-popular block.  The
second exact-slice decomposition, its graph-volume threshold, and every
`Z_lin` height lift are selected once for each source global bin. -/
structure PureWZ2BalancedSafeOuterPopularCoarseNestedBlockRichFamilyData
    {sigma inputLoss delta rho middleLoss outputLoss normalEta finalLoss
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    (weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass)
    (sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction)
    (sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow) where
  sync : ∀ bin : {bin // bin ∈ sourceBins.line.globalBins},
    PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
      weightRestriction sourceWindow sourceBins bin
  nested : ∀ bin : {bin // bin ∈ sourceBins.line.globalBins},
    PureWZ2BalancedSafeOuterPopularCoarseNestedGlobalBinFamilyData (sync bin)
  good : ∀ bin : {bin // bin ∈ sourceBins.line.globalBins},
    PureWZ2BalancedSafeOuterPopularCoarseNestedGoodBinData
      (volumeLoss := volumeLoss) (nested bin)
  rich : ∀ bin : {bin // bin ∈ sourceBins.line.globalBins},
    PureWZ2BalancedSafeOuterPopularCoarseNestedRichFamilyData
      (normalEta := normalEta) (finalLoss := finalLoss)
      (theoremEta := theoremEta) (good bin)

/-- A cell-weighted finite selection whose label factors through the genuine
second-cover parent map.  Storing both views makes it impossible for a later
parent selection to enlarge the selected side-`rho` cell population. -/
structure PureWZ2BalancedSafeOuterPopularCoarseParentFiberData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    {β : Type*} [Fintype β] [DecidableEq β]
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    (parents : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope)
    (color : (ℤ × ℤ × ℤ) → β) where
  fiber : PureWZ2BalancedSafeOuterPopularCoarseCellFiberData
    data outerPopular envelope (fun cell => color (parents.parentCell cell))
  selectedParents : Finset (ℤ × ℤ × ℤ) :=
    parents.parents.filter fun parent => color parent = fiber.target
  selectedParents_eq : selectedParents =
    parents.parents.filter fun parent => color parent = fiber.target
  selectedParents_nonempty : selectedParents.Nonempty
  selectedParents_subset : selectedParents ⊆ parents.parents
  cells_eq_biUnion : fiber.cells =
    selectedParents.biUnion parents.cellsForParent

/-- The concrete mod-512 parent-height selection used before constructing
the local graph.  Its retained cell mass is the exact first-cover mass of a
union of complete fibres of the restricted parent map. -/
structure PureWZ2BalancedSafeOuterPopularCoarseParentYResidueData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    (parents : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope) where
  residue : Fin 512
  parentFiber : PureWZ2BalancedSafeOuterPopularCoarseParentFiberData
    data outerPopular envelope parents (fun parent =>
      (⟨(parent.2.1 % (512 : ℤ)).toNat, by
        have hnonneg : 0 ≤ parent.2.1 % (512 : ℤ) :=
          Int.emod_nonneg _ (by norm_num)
        have hlt : parent.2.1 % (512 : ℤ) < (512 : ℤ) :=
          Int.emod_lt_of_pos _ (by norm_num)
        omega⟩ : Fin 512))
  target_eq : parentFiber.fiber.target = residue
  residue_eq : ∀ parent ∈ parentFiber.selectedParents,
    parent.2.1 % (512 : ℤ) = (residue : ℤ)
  y_separated : ∀ first ∈ parentFiber.selectedParents,
    ∀ second ∈ parentFiber.selectedParents,
      first.2.1 = second.2.1 ∨
        (512 : ℤ) ≤ |first.2.1 - second.2.1|

/-- A simultaneous parent-height and y-residue selection, weighted by all
side-`rho` envelope cells below each parent.  This supplies the common
second-parent height required by the local graph without first discarding
all but one representative cell per parent. -/
structure PureWZ2BalancedSafeOuterPopularCoarseParentHeightYData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    (parents : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope) where
  heightValues : Finset ℤ := parents.parents.image fun parent => parent.2.2
  heightValues_eq : heightValues =
    parents.parents.image fun parent => parent.2.2
  heightValues_nonempty : heightValues.Nonempty
  heightLabel : (ℤ × ℤ × ℤ) → {height // height ∈ heightValues}
  heightLabel_eq : ∀ parent ∈ parents.parents,
    (heightLabel parent).1 = parent.2.2
  residueLabel : (ℤ × ℤ × ℤ) → Fin 512 := fun parent =>
    (⟨(parent.2.1 % (512 : ℤ)).toNat, by
      have hnonneg : 0 ≤ parent.2.1 % (512 : ℤ) :=
        Int.emod_nonneg _ (by norm_num)
      have hlt : parent.2.1 % (512 : ℤ) < (512 : ℤ) :=
        Int.emod_lt_of_pos _ (by norm_num)
      omega⟩ : Fin 512)
  parentFiber : PureWZ2BalancedSafeOuterPopularCoarseParentFiberData
    data outerPopular envelope parents (fun parent =>
      (heightLabel parent, residueLabel parent))
  commonParentHeight : ℤ := parentFiber.fiber.target.1.1
  residue : Fin 512 := parentFiber.fiber.target.2
  parent_height_eq : ∀ parent ∈ parentFiber.selectedParents,
    parent.2.2 = commonParentHeight
  residue_eq : ∀ parent ∈ parentFiber.selectedParents,
    parent.2.1 % (512 : ℤ) = (residue : ℤ)
  y_separated : ∀ first ∈ parentFiber.selectedParents,
    ∀ second ∈ parentFiber.selectedParents,
      first.2.1 = second.2.1 ∨
        (512 : ℤ) ≤ |first.2.1 - second.2.1|

namespace PureWZ2BalancedSafeCoarseCompanionData

variable
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {block : {block // block ∈ safe.blocks}}

/-- Saturate the source outer-popular envelope by complete side-`rho` cells
inside the exact same-cell coarse companion, and pull those cells back through
the first balanced cover. -/
theorem outerPopularCoarseEnvelope
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)) :
    Nonempty (PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular) := by
  let cells := (safe.blockWindow block).cells.filter fun cell =>
    (wz1PaperGridCube rho cell ∩ outerPopular.shading.union).Nonempty
  let shading : WZ1PaperTubeShading twoScale.coarse.coarse :=
    wz2RefinedShading data.shading cells
  have hbase : 0 < twoScale.rhoRequested.1 :=
    twoScale.coarseGrains.extremal.delta_pos
  have houterBlock : outerPopular.shading.union ⊆
      (safe.blockWindow block).shading.union := by
    intro point hpoint
    have hwindow := outerPopular.subshading_window.union_subset hpoint
    rw [(safe.blockWindow block).window_shading] at hwindow
    exact hwindow
  have hblockCoarse : (safe.blockWindow block).shading.union ⊆
      data.shading.union := by
    rw [← data.sourcePullback_union_eq_blockWindow]
    intro point hpoint
    rw [data.sourcePullback.union_eq] at hpoint
    rw [data.sourcePullback.selectedRegion_eq_coarse] at hpoint
    exact hpoint.2
  have hcellsActive : cells ⊆ wz1PaperActiveCells data.shading hbase := by
    intro cell hcell
    rcases (Finset.mem_filter.mp hcell).2 with
      ⟨point, hpointCell, hpointOuter⟩
    have hpointData : point ∈ data.shading.union :=
      hblockCoarse (houterBlock hpointOuter)
    apply (mem_wz1PaperActiveCells data.shading hbase cell).mpr
    refine ⟨?_, ⟨point, hpointData, ?_⟩⟩
    · rcases hpointData with ⟨index, hindex⟩
      have hcellIndex : wz1PaperGridIndex twoScale.rhoRequested.1 point = cell := by
        apply (mem_wz1PaperGridCube twoScale.rhoRequested.1 cell point).mp
        simpa only [twoScale.rhoRequested_eq] using hpointCell
      rw [← hcellIndex]
      exact paper_point_gridIndex_in_window hbase
        (data.shading.subset_body index hindex).2
    · simpa only [twoScale.rhoRequested_eq] using hpointCell
  have hsubData : PureWZ2PaperIsSubshading shading data.shading :=
    wz2RefinedShading_subshading
  have hsub : PureWZ2PaperIsSubshading
      shading twoScale.coarseGrains.shading := by
    intro index point hpoint
    exact data.subshading index (hsubData index hpoint)
  have hwhole : WZ1PaperIsCubicalShading shading :=
    wz2RefinedShading_cubical data.whole_cells
  have hunion : shading.union = wz2RetainedCellsUnion rho cells := by
    have hraw := wz2RefinedShading_union_eq data.whole_cells hbase hcellsActive
    simpa only [twoScale.rhoRequested_eq] using hraw
  have hvolume : volume shading.union =
      (cells.card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
    rw [hunion]
    exact wz1PaperGridCube_volume_biUnion
      (by simpa only [twoScale.rhoRequested_eq] using hbase) cells
  have hsourceEnvelope : outerPopular.shading.union ⊆ shading.union := by
    intro point hpoint
    have hpointBlock := houterBlock hpoint
    rw [(safe.blockWindow block).union_eq,
      (safe.blockWindow block).region_eq] at hpointBlock
    rcases Set.mem_iUnion₂.mp hpointBlock.2 with
      ⟨cell, hcellBlock, hpointCell⟩
    rw [hunion, wz2RetainedCellsUnion]
    exact Set.mem_iUnion₂.mpr ⟨cell, Finset.mem_filter.mpr
      ⟨hcellBlock, ⟨point, hpointCell, hpoint⟩⟩, hpointCell⟩
  have hcellsNonempty : cells.Nonempty := by
    by_contra hempty
    have hcellsEmpty : cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    have hzero : volume shading.union = 0 := by
      rw [hvolume, hcellsEmpty]
      simp
    have hpositive : 0 < volume shading.union :=
      outerPopular.volume_pos.trans_le (measure_mono hsourceEnvelope)
    exact (ne_of_gt hpositive) hzero
  have hactiveCells :
      wz1PaperActiveCells shading
          twoScale.coarseGrains.extremal.delta_pos = cells := by
    apply Finset.Subset.antisymm
    · intro cell hcell
      rw [mem_wz1PaperActiveCells] at hcell
      rcases hcell.2 with ⟨point, hpointShading, hpointCell⟩
      rw [hunion, wz2RetainedCellsUnion] at hpointShading
      rcases Set.mem_iUnion₂.mp hpointShading with
        ⟨owner, howner, hpointOwner⟩
      have hpointCellRho : point ∈ wz1PaperGridCube rho cell := by
        simpa only [twoScale.rhoRequested_eq] using hpointCell
      have hownerEq : owner = cell :=
        ((mem_wz1PaperGridCube rho owner point).mp
          hpointOwner).symm.trans
        ((mem_wz1PaperGridCube rho cell point).mp hpointCellRho)
      rwa [hownerEq] at howner
    · intro cell hcell
      rw [mem_wz1PaperActiveCells]
      have hactiveData := hcellsActive hcell
      rw [mem_wz1PaperActiveCells] at hactiveData
      refine ⟨hactiveData.1, ?_⟩
      rcases (Finset.mem_filter.mp hcell).2 with
        ⟨point, hpointCell, hpointOuter⟩
      have hpointEnvelope : point ∈ shading.union :=
        hsourceEnvelope hpointOuter
      exact ⟨point, hpointEnvelope, by
        simpa only [twoScale.rhoRequested_eq] using hpointCell⟩
  rcases pureWZ2_pullback_selected_coarse_region shading hsub hwhole with
    ⟨sourcePullback⟩
  have hpullbackSub : PureWZ2PaperIsSubshading
      (data.outerPopularEnvelopeSourcePullback outerPopular)
      sourcePullback.shading := by
    intro index point hpoint
    change point ∈ data.sourcePullback.shading.carrier index ∩
      outerPopular.shading.union at hpoint
    rw [sourcePullback.carrier_eq]
    constructor
    · rcases data.sourcePullback.zeroExtension.carrier_support
          index point (by
            rw [data.sourcePullback.carrier_eq] at hpoint
            exact hpoint.1.1) with ⟨selectedIndex, heq, hselected⟩
      rw [← heq, sourcePullback.zeroExtension.carrier_embedding]
      exact hselected
    · rw [sourcePullback.selectedRegion_eq_coarse]
      exact hsourceEnvelope hpoint.2
  exact ⟨{
    cells := cells
    cells_eq := rfl
    cells_nonempty := hcellsNonempty
    shading := shading
    shading_eq := rfl
    subshading := hsubData
    whole_cells := hwhole
    union_eq := hunion
    activeCells_eq := hactiveCells
    volume_eq := hvolume
    source_envelope_subset := hsourceEnvelope
    sourcePullback := sourcePullback
    sourcePullback_selectedCells := by
      rw [sourcePullback.selectedCells_eq, hactiveCells]
    sourceEnvelopePullback_sub_sourcePullback := hpullbackSub
    sourcePullback_mass_cross := sourcePullback.mass_mul_cube
  }⟩

/-- The common spatial restriction has exactly the already selected
outer-popular union. -/
theorem outerPopularSourcePullback_union_eq
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)) :
    (data.outerPopularSourcePullback outerPopular).union =
      outerPopular.popular.shading.union := by
  have hpopularBlock : outerPopular.popular.shading.union ⊆
      (safe.blockWindow block).shading.union := by
    intro point hpoint
    have hwindow := outerPopular.popular.subshading.union_subset hpoint
    rw [(safe.blockWindow block).window_shading] at hwindow
    exact hwindow
  have hpopularSource : outerPopular.popular.shading.union ⊆
      data.sourcePullback.shading.union := by
    rw [data.sourcePullback_union_eq_blockWindow]
    exact hpopularBlock
  ext point
  constructor
  · rintro ⟨_index, hsource, hpopular⟩
    exact hpopular
  · intro hpopular
    rcases hpopularSource hpopular with ⟨index, hsource⟩
    exact ⟨index, hsource, hpopular⟩

/-- The envelope restriction has exactly the complete-cell outer-popular
union.  The equality uses the exact block/source-pullback union proved above. -/
theorem outerPopularEnvelopeSourcePullback_union_eq
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)) :
    (data.outerPopularEnvelopeSourcePullback outerPopular).union =
      outerPopular.shading.union := by
  have henvelopeBlock : outerPopular.shading.union ⊆
      (safe.blockWindow block).shading.union := by
    intro point hpoint
    have hwindow := outerPopular.subshading_window.union_subset hpoint
    rw [(safe.blockWindow block).window_shading] at hwindow
    exact hwindow
  have henvelopeSource : outerPopular.shading.union ⊆
      data.sourcePullback.shading.union := by
    rw [data.sourcePullback_union_eq_blockWindow]
    exact henvelopeBlock
  ext point
  constructor
  · rintro ⟨_index, _hsource, henvelope⟩
    exact henvelope
  · intro henvelope
    rcases henvelopeSource henvelope with ⟨index, hsource⟩
    exact ⟨index, hsource, henvelope⟩

/-- The pointwise outer-popular restriction is a subshading of its complete
source-cell envelope on the same original tube family. -/
theorem outerPopularSourcePullback_sub_envelope
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)) :
    PureWZ2PaperIsSubshading
      (data.outerPopularSourcePullback outerPopular)
      (data.outerPopularEnvelopeSourcePullback outerPopular) := by
  intro index point hpoint
  exact ⟨hpoint.1, outerPopular.popular_subset hpoint.2⟩

/-- The complete-cell envelope restriction inherits the first-sticky
factor-two multiplicity band. -/
theorem outerPopularEnvelopeSourcePullback_constantMultiplicity
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)) :
    (data.outerPopularEnvelopeSourcePullback outerPopular).HasConstantMultiplicity
      twoScale.coarse.fineMultiplicity
      (2 * twoScale.coarse.fineMultiplicity) := by
  intro point hpoint
  have hmultiplicity := wholeCellRestriction_pointMultiplicity_eq
    (fun _ => rfl) hpoint
  rw [hmultiplicity]
  exact data.sourcePullback_constantMultiplicity point (by
    rcases hpoint with ⟨index, hindex⟩
    exact ⟨index, hindex.1⟩)

/-- Outer union-volume popularity on a safe block gives the corresponding
indexed source-mass retention on its exact first-cover pullback. -/
theorem outerPopularSourcePullback_mass_retention
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)) :
    data.sourcePullback.shading.mass ≤
      2 * (2 * outerPopular.popular.bins : ENNReal) *
        (data.outerPopularSourcePullback outerPopular).mass := by
  have htarget :
      (data.outerPopularSourcePullback outerPopular).HasConstantMultiplicity
        twoScale.coarse.fineMultiplicity
        (2 * twoScale.coarse.fineMultiplicity) := by
    intro point hpoint
    have hmultiplicity := wholeCellRestriction_pointMultiplicity_eq
      (fun _ => rfl) hpoint
    rw [hmultiplicity]
    exact data.sourcePullback_constantMultiplicity point
      (by
        rcases hpoint with ⟨index, hindex⟩
        exact ⟨index, hindex.1⟩)
  apply constant_multiplicity_mass_le_of_union_volume_le
    data.sourcePullback_constantMultiplicity htarget
  calc
    volume data.sourcePullback.shading.union =
        volume (safe.blockWindow block).window.shading.union := by
      rw [data.sourcePullback_union_eq_blockWindow,
        (safe.blockWindow block).window_shading]
    _ ≤ (2 * outerPopular.popular.bins : ENNReal) *
        outerPopular.popularWindow.volumeSupply := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        outerPopular.source_volume_retention
    _ = (2 * outerPopular.popular.bins : ENNReal) *
        volume (data.outerPopularSourcePullback outerPopular).union := by
      rw [outerPopular.popularWindow_supply,
        data.outerPopularSourcePullback_union_eq outerPopular]

/-- The exact first-cover source mass is retained, up to the outer dyadic
height cost, by the complete source-cell envelope used for the fixed-line
selection. -/
theorem outerPopularEnvelopeSourcePullback_mass_retention
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)) :
    data.sourcePullback.shading.mass ≤
      2 * (2 * outerPopular.popular.bins : ENNReal) *
        (data.outerPopularEnvelopeSourcePullback outerPopular).mass := by
  apply constant_multiplicity_mass_le_of_union_volume_le
    data.sourcePullback_constantMultiplicity
    (data.outerPopularEnvelopeSourcePullback_constantMultiplicity outerPopular)
  calc
    volume data.sourcePullback.shading.union =
        volume (safe.blockWindow block).window.shading.union := by
      rw [data.sourcePullback_union_eq_blockWindow,
        (safe.blockWindow block).window_shading]
    _ ≤ (2 * outerPopular.popular.bins : ENNReal) *
        outerPopular.windowed.volumeSupply := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        outerPopular.source_volume_retention_windowed
    _ = (2 * outerPopular.popular.bins : ENNReal) *
        volume (data.outerPopularEnvelopeSourcePullback outerPopular).union := by
      rw [outerPopular.windowed_supply,
        data.outerPopularEnvelopeSourcePullback_union_eq outerPopular]

/-- The whole-cell coarse saturation retains the block's indexed source mass
after paying only the outer height-popularity factor. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData.block_source_mass_le
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular) :
    data.sourcePullback.shading.mass ≤
      2 * (2 * outerPopular.popular.bins : ENNReal) *
        envelope.sourcePullback.shading.mass := by
  calc
    data.sourcePullback.shading.mass ≤
        2 * (2 * outerPopular.popular.bins : ENNReal) *
          (data.outerPopularEnvelopeSourcePullback outerPopular).mass :=
      data.outerPopularEnvelopeSourcePullback_mass_retention outerPopular
    _ ≤ 2 * (2 * outerPopular.popular.bins : ENNReal) *
        envelope.sourcePullback.shading.mass := by
      gcongr
      exact Finset.sum_le_sum fun index _ =>
        measure_mono
          (envelope.sourceEnvelopePullback_sub_sourcePullback index)

/-- Restrict the synchronized outer-popular envelope to any nonempty literal
subset of its side-`rho` cells.  The resulting carrier is still cubical and
its source pullback uses exactly the same first-cover cell population. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData.restrictCells
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    (cells : Finset (ℤ × ℤ × ℤ))
    (hsubset : cells ⊆ envelope.cells)
    (hnonempty : cells.Nonempty) :
    Nonempty (PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
      data outerPopular envelope cells) := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  let shading : WZ1PaperTubeShading twoScale.coarse.coarse :=
    wz2RefinedShading envelope.shading cells
  have hcellsActive : cells ⊆ wz1PaperActiveCells envelope.shading
      twoScale.coarseGrains.extremal.delta_pos := by
    intro cell hcell
    rw [mem_wz1PaperActiveCells]
    have hcellEnvelope := hsubset hcell
    have hcellBase : cell ∈
        wz1PaperGridIndicesInWindow
          twoScale.rhoRequested.1
          twoScale.coarseGrains.extremal.delta_pos := by
      rw [envelope.cells_eq] at hcellEnvelope
      have hblockCell := (Finset.mem_filter.mp hcellEnvelope).1
      rw [(safe.blockWindow block).cells_eq,
        pureWZ2BalancedSafeWindowCells] at hblockCell
      have hpullback := (Finset.mem_filter.mp hblockCell).1
      rw [pullback.selectedCells_eq] at hpullback
      exact (mem_wz1PaperActiveCells twoScale.fine.refined
        twoScale.coarseGrains.extremal.delta_pos cell).mp hpullback |>.1
    have hintersection :
        (envelope.shading.union ∩
          wz1PaperGridCube twoScale.rhoRequested.1 cell).Nonempty := by
      let point := cellCorner rho cell
      have hpointCell : point ∈ wz1PaperGridCube rho cell :=
        cellCorner_mem_gridCube hrho cell
      have hpointEnvelope : point ∈ envelope.shading.union := by
        rw [envelope.union_eq, wz2RetainedCellsUnion]
        exact Set.mem_iUnion₂.mpr ⟨cell, hcellEnvelope, hpointCell⟩
      exact ⟨point, hpointEnvelope, by
        simpa only [twoScale.rhoRequested_eq] using hpointCell⟩
    exact ⟨hcellBase, hintersection⟩
  have hsub : PureWZ2PaperIsSubshading shading envelope.shading :=
    wz2RefinedShading_subshading
  have hwhole : WZ1PaperIsCubicalShading shading :=
    wz2RefinedShading_cubical envelope.whole_cells
  have hunion : shading.union = wz2RetainedCellsUnion rho cells := by
    have hraw := wz2RefinedShading_union_eq envelope.whole_cells
      twoScale.coarseGrains.extremal.delta_pos hcellsActive
    simpa only [twoScale.rhoRequested_eq] using hraw
  have hactiveCells :
      wz1PaperActiveCells shading
          twoScale.coarseGrains.extremal.delta_pos = cells := by
    apply Finset.Subset.antisymm
    · intro cell hcell
      rw [mem_wz1PaperActiveCells] at hcell
      rcases hcell.2 with ⟨point, hpointShading, hpointCell⟩
      rw [hunion, wz2RetainedCellsUnion] at hpointShading
      rcases Set.mem_iUnion₂.mp hpointShading with
        ⟨owner, howner, hpointOwner⟩
      have hpointCellRho : point ∈ wz1PaperGridCube rho cell := by
        simpa only [twoScale.rhoRequested_eq] using hpointCell
      have hownerEq : owner = cell :=
        ((mem_wz1PaperGridCube rho owner point).mp hpointOwner).symm.trans
          ((mem_wz1PaperGridCube rho cell point).mp hpointCellRho)
      rwa [hownerEq] at howner
    · intro cell hcell
      rw [mem_wz1PaperActiveCells]
      have hactiveEnvelope := hcellsActive hcell
      rw [mem_wz1PaperActiveCells] at hactiveEnvelope
      refine ⟨hactiveEnvelope.1, ?_⟩
      let point := cellCorner rho cell
      have hpointCell : point ∈ wz1PaperGridCube rho cell :=
        cellCorner_mem_gridCube hrho cell
      have hpointShading : point ∈ shading.union := by
        rw [hunion, wz2RetainedCellsUnion]
        exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointCell⟩
      exact ⟨point, hpointShading, by
        simpa only [twoScale.rhoRequested_eq] using hpointCell⟩
  have hvolume : volume shading.union =
      (cells.card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
    rw [hunion]
    exact wz1PaperGridCube_volume_biUnion hrho cells
  have hsubCoarse : PureWZ2PaperIsSubshading
      shading twoScale.coarseGrains.shading := by
    intro index point hpoint
    exact data.subshading index (envelope.subshading index (hsub index hpoint))
  rcases pureWZ2_pullback_selected_coarse_region shading hsubCoarse hwhole with
    ⟨sourcePullback⟩
  have hselectedCells : sourcePullback.selectedCells = cells := by
    rw [sourcePullback.selectedCells_eq, hactiveCells]
  exact ⟨{
    cells_subset := hsubset
    cells_nonempty := hnonempty
    shading := shading
    shading_eq := rfl
    subshading := hsub
    whole_cells := hwhole
    union_eq := hunion
    activeCells_eq := hactiveCells
    volume_eq := hvolume
    sourcePullback := sourcePullback
    sourcePullback_selectedCells := hselectedCells
    sourcePullback_mass_eq := by
      rw [sourcePullback.mass_eq, hselectedCells]
  }⟩

/-- Select one fibre of a finite joint label inside an already materialized
synchronized cell restriction.  Both the selected genuine-coarse carrier and
its source pullback are rebuilt from the filtered literal cell set, so this
operation cannot reintroduce an envelope cell discarded by an earlier
selection. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData.selectCellFiber
    {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    {baseCells : Finset (ℤ × ℤ × ℤ)}
    (base : PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
      data outerPopular envelope baseCells)
    (color : (ℤ × ℤ × ℤ) → β) :
    Nonempty (PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionFiberData
      base color) := by
  let weight : (ℤ × ℤ × ℤ) → ENNReal := fun _ =>
    twoScale.coarse.balanced.incidenceMass
  rcases finset_ennreal_weighted_fiber_retention
      baseCells weight color with ⟨target, hretained⟩
  let cells := baseCells.filter fun cell => color cell = target
  have hbaseMassPos : 0 < base.sourcePullback.shading.mass := by
    rw [base.sourcePullback_mass_eq]
    exact ENNReal.mul_pos
      (by exact_mod_cast base.cells_nonempty.card_ne_zero)
      twoScale.coarse.balanced.incidenceMass_pos.ne'
  have htotalPos : 0 < ∑ cell ∈ baseCells, weight cell := by
    simpa [weight, Finset.sum_const, base.sourcePullback_mass_eq] using
      hbaseMassPos
  have hselectedMassPos : 0 < ∑ cell ∈ cells, weight cell := by
    by_contra hnot
    have hzero : (∑ cell ∈ cells, weight cell) = 0 :=
      nonpos_iff_eq_zero.mp (not_lt.mp hnot)
    have hleZero := hretained
    rw [show baseCells.filter (fun cell => color cell = target) = cells by rfl,
      hzero, mul_zero] at hleZero
    exact (not_le_of_gt htotalPos) hleZero
  have hcellsNonempty : cells.Nonempty := by
    by_contra hempty
    have hcellsEmpty : cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    rw [hcellsEmpty] at hselectedMassPos
    simpa using hselectedMassPos
  have hcellsSubset : cells ⊆ envelope.cells :=
    (Finset.filter_subset _ _).trans base.cells_subset
  let selectedRestriction := Classical.choice
    (PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData.restrictCells
      data outerPopular envelope cells hcellsSubset hcellsNonempty)
  have hmass : base.sourcePullback.shading.mass ≤
      (Fintype.card β : ENNReal) *
        selectedRestriction.sourcePullback.shading.mass := by
    rw [base.sourcePullback_mass_eq,
      selectedRestriction.sourcePullback_mass_eq]
    simpa [weight, cells, Finset.sum_const] using hretained
  exact ⟨{
    target := target
    cells := cells
    cells_eq := rfl
    cells_nonempty := hcellsNonempty
    selectedRestriction := selectedRestriction
    retained_mass := hmass
  }⟩

/-- Every original-slope projection value on an exact slice of a synchronized
coarse-cell restriction is within `5 * rho` of the original source projection
on the corresponding `rho`-slab.  The witness is chosen in the very same
literal side-`rho` cell, so this statement introduces neither an ambient-cell
enlargement nor an identification of the source and coarse grain slopes. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData.originalSlope_exactSlice_subset_sourceRhoSlab_thickening
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    {cells : Finset (ℤ × ℤ × ℤ)}
    (restriction : PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
      data outerPopular envelope cells) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      scalarProjection
          (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice restriction.shading.union z) ⊆
        Metric.cthickening (5 * rho)
          (globalGrainProjection source.globalGrains.slope
            (globalGrainSlab source.shading.union z rho)) := by
  let witnesses : PureWZ2CoarseCellWitnessData twoScale :=
    Classical.choice twoScale.coarseCellWitnesses
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  intro z hz value hvalue
  rcases hvalue with ⟨point, hpoint, rfl⟩
  rw [restriction.union_eq, wz2RetainedCellsUnion] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint.1 with
    ⟨cell, hcell, hpointCell⟩
  have hcellActive : cell ∈ witnesses.activeCells := by
    rw [witnesses.activeCells_eq]
    have hrestriction : point ∈ restriction.shading.union := by
      rw [restriction.union_eq, wz2RetainedCellsUnion]
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointCell⟩
    have henvelope : point ∈ envelope.shading.union :=
      restriction.subshading.union_subset hrestriction
    have hcompanion : point ∈ data.shading.union :=
      envelope.subshading.union_subset henvelope
    have hcoarseGrains : point ∈ twoScale.coarseGrains.shading.union :=
      data.subshading.union_subset hcompanion
    have hcoarse : point ∈ twoScale.coarse.croppedCoarseShading.union :=
      twoScale.coarseGrains.subshading.union_subset hcoarseGrains
    rw [twoScale.coarse.balanced.coarse_union_eq] at hcoarse
    rcases Set.mem_iUnion₂.mp hcoarse with
      ⟨activeCell, hactiveCell, hpointActiveCell⟩
    have hpointCell' : point ∈ wz1PaperGridCube rho activeCell := by
      simpa only [twoScale.rhoRequested_eq] using hpointActiveCell
    have hcellEq : activeCell = cell :=
      ((mem_wz1PaperGridCube rho activeCell point).mp hpointCell').symm.trans
        ((mem_wz1PaperGridCube rho cell point).mp hpointCell)
    rwa [hcellEq] at hactiveCell
  let sourcePoint := witnesses.witness cell
  have hsource : sourcePoint ∈ source.shading.union :=
    ⟨witnesses.sourceIndex cell,
      witnesses.witness_mem_source cell hcellActive⟩
  have hsourceCell : sourcePoint ∈ wz1PaperGridCube rho cell :=
    witnesses.witness_mem_cell cell hcellActive
  have hx : |point 0 - sourcePoint 0| ≤ rho :=
    (pureWZ2_same_grid_cell_coord_lt hrho hsourceCell hpointCell 0).le
  have hy : |point 1 - sourcePoint 1| ≤ rho :=
    (pureWZ2_same_grid_cell_coord_lt hrho hsourceCell hpointCell 1).le
  have hzclose : |point 2 - sourcePoint 2| ≤ rho :=
    (pureWZ2_same_grid_cell_coord_lt hrho hsourceCell hpointCell 2).le
  have hsourceBox := shading_union_subset_axisBox hsource
  have hsourceHeight : sourcePoint 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    simpa [Kakeya.Streamlined.axisBox, abs_le] using hsourceBox.2.2
  have hsourceY : |sourcePoint 1| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hsourceBox.2.1
  have hsourceSlab : sourcePoint ∈
      globalGrainSlab source.shading.union z rho := by
    refine ⟨⟨hsource, ?_⟩, hsourceHeight⟩
    rw [hpoint.2] at hzclose
    exact ⟨by linarith [abs_le.mp hzclose],
      by linarith [abs_le.mp hzclose]⟩
  let sourceValue := inner ℝ sourcePoint
    (globalGrainDirection (source.globalGrains.slope (sourcePoint 2)))
  have hsourceValue : sourceValue ∈
      globalGrainProjection source.globalGrains.slope
        (globalGrainSlab source.shading.union z rho) :=
    ⟨sourcePoint, hsourceSlab, rfl⟩
  have hslopeClose :
      |source.globalGrains.slope z -
          source.globalGrains.slope (sourcePoint 2)| ≤ rho := by
    have hlip := source.globalGrains.slope_lipschitz.dist_le_mul
      z hz (sourcePoint 2) hsourceHeight
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
    have hheight : |z - sourcePoint 2| ≤ rho := by
      rw [hpoint.2] at hzclose
      exact hzclose
    exact hlip.trans hheight
  have hslope : |source.globalGrains.slope z| ≤ 3 :=
    source.globalGrains.slope_bound z hz
  have hformula :
      inner ℝ point (globalGrainDirection (source.globalGrains.slope z)) -
          sourceValue =
        (point 0 - sourcePoint 0) +
          source.globalGrains.slope z * (point 1 - sourcePoint 1) +
          (source.globalGrains.slope z -
            source.globalGrains.slope (sourcePoint 2)) * sourcePoint 1 := by
    dsimp only [sourceValue]
    simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    ring
  have hclose :
      |inner ℝ point (globalGrainDirection (source.globalGrains.slope z)) -
          sourceValue| ≤ 5 * rho := by
    rw [hformula]
    calc
      |(point 0 - sourcePoint 0) +
          source.globalGrains.slope z * (point 1 - sourcePoint 1) +
          (source.globalGrains.slope z -
            source.globalGrains.slope (sourcePoint 2)) * sourcePoint 1| ≤
        |point 0 - sourcePoint 0| +
          |source.globalGrains.slope z| * |point 1 - sourcePoint 1| +
          |source.globalGrains.slope z -
            source.globalGrains.slope (sourcePoint 2)| * |sourcePoint 1| := by
          calc
            _ ≤ |(point 0 - sourcePoint 0) +
                  source.globalGrains.slope z * (point 1 - sourcePoint 1)| +
                |(source.globalGrains.slope z -
                  source.globalGrains.slope (sourcePoint 2)) * sourcePoint 1| :=
              abs_add_le _ _
            _ ≤ (|point 0 - sourcePoint 0| +
                  |source.globalGrains.slope z *
                    (point 1 - sourcePoint 1)|) +
                |(source.globalGrains.slope z -
                  source.globalGrains.slope (sourcePoint 2)) * sourcePoint 1| := by
              gcongr
              exact abs_add_le _ _
            _ = _ := by rw [abs_mul, abs_mul]
      _ ≤ rho + 3 * rho + rho * 1 := by gcongr
      _ = 5 * rho := by ring
  exact Metric.mem_cthickening_of_dist_le _ sourceValue (5 * rho) _
    hsourceValue (by simpa [Real.dist_eq] using hclose)

/-- Convert original-source AD on the side-`rho` height slab into exact-slice
AD on a synchronized genuine-coarse restriction.  The factor `144` is the
literal generalized-thickening cost for radius `5 * rho` at base scale
`rho`; the caller supplies only its scalar absorption into the one-scale
global constant. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData.originalSlope_exactAD_of_sourceRhoSlabAD
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    {cells : Finset (ℤ × ℤ × ℤ)}
    (restriction : PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
      data outerPopular envelope cells)
    {C : ENNReal}
    (hsourceRhoSlabAD : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (globalGrainProjection source.globalGrains.slope
          (globalGrainSlab source.shading.union z rho))
        rho (1 - sigma) C)
    (hconstant :
      144 * C ≤ 10 * Kakeya.realRpowENN rho (-middleLoss)) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection
          (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice restriction.shading.union z))
        rho (1 - sigma)
        (10 * Kakeya.realRpowENN rho (-middleLoss)) := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  intro z hz
  have hbounded :
      scalarProjection
          (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice restriction.shading.union z) ⊆
        Set.Icc (-4 : ℝ) 4 := by
    rintro value ⟨point, hpoint, rfl⟩
    have henvelope : point ∈ envelope.shading.union :=
      restriction.subshading.union_subset hpoint.1
    have hcompanion : point ∈ data.shading.union :=
      envelope.subshading.union_subset henvelope
    have hbox := shading_union_subset_axisBox
      (data.subshading.union_subset hcompanion)
    have hzero : |point 0| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.1
    have hone : |point 1| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
    have hslope := source.globalGrains.slope_bound z hz
    have hformula :
        inner ℝ point (globalGrainDirection (source.globalGrains.slope z)) =
          point 0 + source.globalGrains.slope z * point 1 := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    change inner ℝ point
        (globalGrainDirection (source.globalGrains.slope z)) ∈
      Set.Icc (-4 : ℝ) 4
    rw [hformula]
    apply abs_le.mp
    calc
      |point 0 + source.globalGrains.slope z * point 1| ≤
          |point 0| + |source.globalGrains.slope z| * |point 1| := by
        calc
          _ ≤ |point 0| +
              |source.globalGrains.slope z * point 1| := abs_add_le _ _
          _ = _ := by rw [abs_mul]
      _ ≤ 1 + 3 * 1 := by gcongr
      _ = 4 := by norm_num
  have hsubset :=
    PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData.originalSlope_exactSlice_subset_sourceRhoSlab_thickening
      data outerPopular envelope restriction z hz
  have hthick := IsADSet1.generalized_thickening
    (ε := 5 * rho) (hsourceRhoSlabAD z hz) hsubset hbounded hrho
      (by positivity)
  have hratio : (5 * rho) / rho = (5 : ℝ) := by
    field_simp [hrho.ne']
  rw [hratio] at hthick
  norm_num at hthick
  exact hthick.mono_constant hconstant

/-- Build the original-slope global-slice package on the literal
genuine-coarse restriction from its transported exact-slice certificate.
The active height window is inherited from the safe block's interior cell
margin; no source-family volume is used. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData.prepareOriginalGlobal
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    {cells : Finset (ℤ × ℤ × ℤ)}
    (restriction : PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
      data outerPopular envelope cells)
    (hexact : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection
          (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice restriction.shading.union z))
        rho (1 - sigma)
        (10 * Kakeya.realRpowENN rho (-middleLoss))) :
    Nonempty (PureWZ2BalancedSafeOuterPopularCoarseOriginalGlobalData
      restriction) := by
  let hbase : 0 < twoScale.rhoRequested.1 :=
    twoScale.coarseGrains.extremal.delta_pos
  let shadow := pureWZ2ActiveCellShading restriction.shading hbase
  have hshadowUnion : shadow.union = restriction.shading.union :=
    pureWZ2ActiveCellShading_union restriction.shading hbase
      restriction.whole_cells
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact hbase
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hball : shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hrestriction : point ∈ restriction.shading.union := by
      rwa [hshadowUnion] at hpoint
    have henvelope : point ∈ envelope.shading.union :=
      restriction.subshading.union_subset hrestriction
    have hcompanion : point ∈ data.shading.union :=
      envelope.subshading.union_subset henvelope
    have hcoarse := data.subshading.union_subset hcompanion
    have hnorm := norm_le_two_of_mem_paperShading hcoarse
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hcoord : ∀ point ∈ shadow.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hrestriction : point ∈ restriction.shading.union := by
      rwa [hshadowUnion] at hpoint
    have henvelope : point ∈ envelope.shading.union :=
      restriction.subshading.union_subset hrestriction
    have hcompanion : point ∈ data.shading.union :=
      envelope.subshading.union_subset henvelope
    have hbox := shading_union_subset_axisBox
      (data.subshading.union_subset hcompanion)
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hexactShadow : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection
          (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice shadow.union z))
        twoScale.rhoRequested.1 (1 - sigma)
        (10 * Kakeya.realRpowENN rho (-middleLoss)) := by
    intro z hz
    have h := hexact z hz
    rw [hshadowUnion]
    simpa only [twoScale.rhoRequested_eq] using h
  have hCtop :
      (10 * Kakeya.realRpowENN rho (-middleLoss) : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  rcases wz1_lemma23_global_slice_package_of_exact_paper_window
      shadow hbase le_rfl twoScale.rhoRequested.property.2 hball hcoord
      source.globalGrains.slope source.globalGrains.slope_lipschitz
      source.globalGrains.slope_bound
      (10 * Kakeya.realRpowENN rho (-middleLoss)) hCtop
      hexactShadow with
    ⟨globalPackage, hsourceSlope⟩
  have hactiveWindow : WZ1Lemma23ActiveCellHeightWindow shadow hbase := by
    refine ⟨(safe.blockWindow block).window.left, ?_⟩
    intro graphCell hgraphCell
    rw [wz1Lemma23_mem_active_iff] at hgraphCell
    rcases hgraphCell.2 with ⟨point, hpointShadow, hpointGraphCell⟩
    have hpointRestriction : point ∈ restriction.shading.union := by
      rw [← hshadowUnion]
      exact hpointShadow
    rw [restriction.union_eq, wz2RetainedCellsUnion] at hpointRestriction
    rcases Set.mem_iUnion₂.mp hpointRestriction with
      ⟨paperCell, hpaperCell, hpointPaperCell⟩
    have hpaperCellEnvelope : paperCell ∈ envelope.cells :=
      restriction.cells_subset hpaperCell
    have hpaperCellBlock : paperCell ∈ (safe.blockWindow block).cells := by
      rw [envelope.cells_eq] at hpaperCellEnvelope
      exact (Finset.mem_filter.mp hpaperCellEnvelope).1
    have hsafeRaw : pureWZ2PaperCellCenterHeight rho paperCell ∈
        Set.Icc
          (pureWZ2BalancedWindowPhaseLeftAt rho safe.phase block.1 + rho)
          (pureWZ2BalancedWindowPhaseLeftAt rho safe.phase block.1 +
            Real.sqrt rho - rho) := by
      rw [(safe.blockWindow block).cells_eq,
        pureWZ2BalancedSafeWindowCells] at hpaperCellBlock
      exact (Finset.mem_filter.mp hpaperCellBlock).2
    have hsafe : pureWZ2PaperCellCenterHeight rho paperCell ∈
        Set.Icc ((safe.blockWindow block).window.left + rho)
          ((safe.blockWindow block).window.left + Real.sqrt rho - rho) := by
      simpa [(safe.blockWindow block).window_left] using hsafeRaw
    have hpaperBounds := hpointPaperCell
    rw [wz1PaperGridCube_eq_Ico hrho paperCell] at hpaperBounds
    have hpointPaperCenter :
        |point (2 : Fin 3) - pureWZ2PaperCellCenterHeight rho paperCell| ≤
          rho / 2 := by
      rw [abs_le]
      constructor
      · calc
          -(rho / 2) = (paperCell.2.2 : ℝ) * rho -
              pureWZ2PaperCellCenterHeight rho paperCell := by
                dsimp only [pureWZ2PaperCellCenterHeight]
                ring
          _ ≤ point (2 : Fin 3) -
              pureWZ2PaperCellCenterHeight rho paperCell :=
            sub_le_sub_right hpaperBounds.2.2.2.2.1 _
      · calc
          point (2 : Fin 3) -
                pureWZ2PaperCellCenterHeight rho paperCell ≤
              ((paperCell.2.2 : ℝ) + 1) * rho -
                pureWZ2PaperCellCenterHeight rho paperCell :=
            sub_le_sub_right hpaperBounds.2.2.2.2.2.le _
          _ = rho / 2 := by
            dsimp only [pureWZ2PaperCellCenterHeight]
            ring
    have hgraphCenter :
        |point (2 : Fin 3) -
            (wz1Lemma23SnappedPoint twoScale.rhoRequested.1 graphCell)
              (2 : Fin 3)| ≤ twoScale.rhoRequested.1 / 2 :=
      ((wz1_lemma23_snapped_cell_geometry
        twoScale.rhoRequested.1 hbase twoScale.rhoRequested.property.2).2.1
        graphCell point hpointGraphCell).1 (2 : Fin 3)
    rw [twoScale.rhoRequested_eq] at hgraphCenter
    rw [abs_le] at hpointPaperCenter hgraphCenter
    rw [twoScale.rhoRequested_eq]
    exact ⟨by linarith [hsafe.1], by linarith [hsafe.2]⟩
  let windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := twoScale.rhoRequested.1)
      (rho := twoScale.rhoRequested.1) (sigma := sigma) shadow
      (10 * Kakeya.realRpowENN rho (-middleLoss)) :=
    { global := globalPackage
      active_height_window := hactiveWindow }
  exact ⟨{
    shadow := shadow
    windowed := windowed
    sourceSlope_eq := by simpa [windowed] using hsourceSlope
    shadow_union := hshadowUnion
    exactAD := by
      intro z hz
      simpa only [twoScale.rhoRequested_eq] using hexact z hz
  }⟩

/-- Construct the restriction-native original-slope Lemma-23 package from a
single source `rho`-slab AD certificate and its explicit constant budget. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData.prepareOriginalGlobalOfSourceRhoSlabAD
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    {cells : Finset (ℤ × ℤ × ℤ)}
    (restriction : PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
      data outerPopular envelope cells)
    {C : ENNReal}
    (hsourceRhoSlabAD : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (globalGrainProjection source.globalGrains.slope
          (globalGrainSlab source.shading.union z rho))
        rho (1 - sigma) C)
    (hconstant :
      144 * C ≤ 10 * Kakeya.realRpowENN rho (-middleLoss)) :
    Nonempty (PureWZ2BalancedSafeOuterPopularCoarseOriginalGlobalData
      restriction) :=
  PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData.prepareOriginalGlobal
    data outerPopular envelope restriction
      (PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData.originalSlope_exactAD_of_sourceRhoSlabAD
        data outerPopular envelope restriction hsourceRhoSlabAD hconstant)

/-- Select the horizontal line by Fubini directly on the coarse whole-cell
restriction.  Consequently its slice-area lower bound starts from
`volume restriction.shading.union`. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseOriginalGlobalData.selectFixedLine
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {cells : Finset (ℤ × ℤ × ℤ)}
    {restriction : PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
      data outerPopular envelope cells}
    (global : PureWZ2BalancedSafeOuterPopularCoarseOriginalGlobalData
      restriction) :
    Nonempty (PureWZ2BalancedSafeOuterPopularCoarseFixedLineData global) := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hcoord : ∀ point ∈ global.shadow.union,
      ∀ coordinate : Fin 3, |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hrestriction : point ∈ restriction.shading.union := by
      rwa [global.shadow_union] at hpoint
    have henvelope := restriction.subshading.union_subset hrestriction
    have hcompanion := envelope.subshading.union_subset henvelope
    have hbox := shading_union_subset_axisBox
      (data.subshading.union_subset hcompanion)
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  rcases global.windowed.active_height_window with ⟨left, hcenterWindow⟩
  have hheight : ∀ point ∈ global.shadow.union,
      point (2 : Fin 3) ∈
        Set.Ico (left - rho) (left + Real.sqrt rho + rho) := by
    intro point hpoint
    have hbase : 0 < twoScale.rhoRequested.1 :=
      twoScale.coarseGrains.extremal.delta_pos
    have hball : global.shadow.union ⊆
        Metric.closedBall (0 : Point3) 2 := by
      intro q hq
      have hrestriction : q ∈ restriction.shading.union := by
        rwa [global.shadow_union] at hq
      have henvelope := restriction.subshading.union_subset hrestriction
      have hcompanion := envelope.subshading.union_subset henvelope
      have hnorm := norm_le_two_of_mem_paperShading
        (data.subshading.union_subset hcompanion)
      simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
    have hactive := wz1Lemma23_index_mem_active_two hbase hball hpoint
    have hcenter := hcenterWindow _ hactive
    have hpointCenter :=
      ((wz1_lemma23_snapped_cell_geometry twoScale.rhoRequested.1 hbase
        twoScale.rhoRequested.property.2).2.1
        (wz1Lemma23CellIndex twoScale.rhoRequested.1 point) point rfl).1
          (2 : Fin 3)
    rw [twoScale.rhoRequested_eq] at hcenter hpointCenter
    rw [abs_le] at hpointCenter
    exact ⟨by linarith [hcenter.1, hpointCenter.2],
      by linarith [hcenter.2, hpointCenter.1]⟩
  have hvolume : 0 < volume restriction.shading.union := by
    rw [restriction.volume_eq]
    have hcube : 0 < volume (wz1PaperGridCube rho (0, 0, 0)) := by
      rw [wz1PaperGridCube_volume_exact hrho]
      exact ENNReal.ofReal_pos.mpr (pow_pos hrho 3)
    exact ENNReal.mul_pos
      (by exact_mod_cast restriction.cells_nonempty.card_ne_zero) hcube.ne'
  have hline := pureWZ2_selectHorizontalFixedLineCore
    global.windowed source.globalGrains.slope
    (by simpa only [twoScale.rhoRequested_eq] using hrho) le_rfl
    (by simpa only [twoScale.rhoRequested_eq] using hrhoOne)
    global.sourceSlope_eq hcoord left
    (by simpa only [twoScale.rhoRequested_eq] using hheight)
    (by
      intro z hz
      have h := global.exactAD z hz
      rw [global.shadow_union]
      simpa only [twoScale.rhoRequested_eq] using h)
    (by simpa [global.shadow_union] using hvolume)
  rcases hline with ⟨line⟩
  exact ⟨{ line := line, line_shadow := global.shadow_union }⟩

/-- Expose every global-bin fibre of the restriction-native fixed line and
prove that every such cell is one of the restriction's literal side-`rho`
cells. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseFixedLineData.toGlobalBins
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {cells : Finset (ℤ × ℤ × ℤ)}
    {restriction : PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
      data outerPopular envelope cells}
    {global : PureWZ2BalancedSafeOuterPopularCoarseOriginalGlobalData
      restriction}
    (fixedLine : PureWZ2BalancedSafeOuterPopularCoarseFixedLineData global) :
    Nonempty (PureWZ2BalancedSafeOuterPopularCoarseGlobalBinFamilyData
      fixedLine) := by
  let core : ∀ bin : {bin // bin ∈ fixedLine.line.globalBins},
      PureWZ2HorizontalFixedBinCore
        global.windowed source.globalGrains.slope := fun bin =>
    Classical.choose (fixedLine.line.coreAtGlobalBin bin.1 bin.2)
  have hlineBin : ∀ bin, (core bin).lineBin = bin.1 := by
    intro bin
    exact (Classical.choose_spec
      (fixedLine.line.coreAtGlobalBin bin.1 bin.2)).1
  have hheavy : ∀ bin, (core bin).heavyCells =
      pureWZ2HorizontalGlobalBinCells fixedLine.line bin.1 := by
    intro bin
    exact (Classical.choose_spec
      (fixedLine.line.coreAtGlobalBin bin.1 bin.2)).2
  have hslice : fixedLine.line.sliceCells.card =
      ∑ bin : {bin // bin ∈ fixedLine.line.globalBins},
        (core bin).heavyCells.card := by
    calc
      fixedLine.line.sliceCells.card =
          ∑ bin ∈ fixedLine.line.globalBins,
            (pureWZ2HorizontalGlobalBinCells fixedLine.line bin).card :=
        fixedLine.line.card_eq_sum_globalBinCells
      _ = ∑ bin : {bin // bin ∈ fixedLine.line.globalBins},
          (pureWZ2HorizontalGlobalBinCells fixedLine.line bin.1).card := by
        exact Finset.sum_subtype fixedLine.line.globalBins (fun _ => Iff.rfl) _
      _ = ∑ bin : {bin // bin ∈ fixedLine.line.globalBins},
          (core bin).heavyCells.card := by
        apply Finset.sum_congr rfl
        intro bin _
        rw [hheavy bin]
  let rhoCell : ∀ bin : {bin // bin ∈ fixedLine.line.globalBins},
      (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) := fun bin cell =>
    wz1PaperGridIndex twoScale.rhoRequested.1
      ((core bin).representative cell)
  have hrhoCellMem : ∀ bin cell, cell ∈ (core bin).heavyCells →
      rhoCell bin cell ∈ cells := by
    intro bin cell hcell
    have hrepresentative := (core bin).representative_mem cell hcell
    have hrestriction : (core bin).representative cell ∈
        restriction.shading.union := by
      rw [← global.shadow_union]
      exact hrepresentative
    rw [restriction.union_eq, wz2RetainedCellsUnion] at hrestriction
    rcases Set.mem_iUnion₂.mp hrestriction with
      ⟨owner, howner, hpointOwner⟩
    have hpointCell : (core bin).representative cell ∈
        wz1PaperGridCube twoScale.rhoRequested.1 (rhoCell bin cell) := by
      exact (mem_wz1PaperGridCube twoScale.rhoRequested.1
        (rhoCell bin cell) _).mpr rfl
    have hpointOwnerBase : (core bin).representative cell ∈
        wz1PaperGridCube twoScale.rhoRequested.1 owner := by
      simpa only [twoScale.rhoRequested_eq] using hpointOwner
    have heq : owner = rhoCell bin cell :=
      ((mem_wz1PaperGridCube twoScale.rhoRequested.1 owner _).mp
        hpointOwnerBase).symm.trans
      ((mem_wz1PaperGridCube twoScale.rhoRequested.1
        (rhoCell bin cell) _).mp hpointCell)
    rwa [heq] at howner
  exact ⟨{
    core := core
    lineBin_eq := hlineBin
    heavyCells_eq := hheavy
    slice_card := hslice
    rhoCell := rhoCell
    rhoCell_eq := fun _ _ => rfl
    rhoCell_mem := hrhoCellMem
    representative_mem_rhoCell := by
      intro bin cell hcell
      exact (mem_wz1PaperGridCube twoScale.rhoRequested.1
        (rhoCell bin cell) _).mpr rfl
  }⟩

/-- Repackage an exact first-cover pullback of selected synchronized cells as
an original-source window.  The ordinary shadow is indexed by the ambient
safe block, but its union and volume supply are exactly the selected
pullback, so subsequent Fubini choices cannot regain discarded cells. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData.toSourceWindow
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    {cells : Finset (ℤ × ℤ × ℤ)}
    (restriction : PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
      data outerPopular envelope cells) :
    Nonempty
      (PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        restriction) := by
  let region := restriction.sourcePullback.shading.union
  let blockShading := (safe.blockWindow block).shading
  let shadow : Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily pullback.shading source.extremal.delta_pos) :=
    { carrier := fun index => blockShading.carrier index ∩ region
      measurable_carrier := fun index =>
        (blockShading.measurable_carrier index).inter
          (measurableSet_shading_union restriction.sourcePullback.shading)
      subset_body := fun index => Set.inter_subset_left.trans
        (blockShading.subset_body index) }
  have hcellsBlock : cells ⊆ (safe.blockWindow block).cells := by
    intro cell hcell
    have hcellEnvelope := restriction.cells_subset hcell
    rw [envelope.cells_eq] at hcellEnvelope
    exact (Finset.mem_filter.mp hcellEnvelope).1
  have hregionBlock : restriction.sourcePullback.selectedRegion ⊆
      (safe.blockWindow block).region := by
    intro point hpoint
    rw [restriction.sourcePullback.selectedRegion_eq] at hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
    have hcell' : cell ∈ cells := by
      rwa [restriction.sourcePullback_selectedCells] at hcell
    rw [(safe.blockWindow block).region_eq]
    exact Set.mem_iUnion₂.mpr ⟨cell, hcellsBlock hcell', hpointCell⟩
  have hsourceSubsetBlock : region ⊆ blockShading.union := by
    intro point hpoint
    have hpoint' : point ∈ restriction.sourcePullback.shading.union := by
      simpa only [region] using hpoint
    have hpullback : point ∈ pullback.shading.union := by
      rw [restriction.sourcePullback.union_eq,
        restriction.sourcePullback.zeroExtension.union_eq] at hpoint'
      rw [pullback.union_eq, pullback.zeroExtension.union_eq]
      exact ⟨hpoint'.1, by
        have hblockRegion := hregionBlock hpoint'.2
        rw [(safe.blockWindow block).region_eq] at hblockRegion
        rcases Set.mem_iUnion₂.mp hblockRegion with
          ⟨cell, hcell, hpointCell⟩
        rw [pullback.selectedRegion_eq]
        have hcellPullback : cell ∈ pullback.selectedCells := by
          rw [(safe.blockWindow block).cells_eq,
            pureWZ2BalancedSafeWindowCells] at hcell
          exact (Finset.mem_filter.mp hcell).1
        exact Set.mem_iUnion₂.mpr ⟨cell, hcellPullback, hpointCell⟩⟩
    have hprepared : point ∈ prepared.shadow.union := by
      rwa [prepared.shadow_union]
    have hblockRegion : point ∈ (safe.blockWindow block).region := by
      have hpoint'' : point ∈ restriction.sourcePullback.shading.union := by
        simpa only [region] using hpoint
      rw [restriction.sourcePullback.union_eq] at hpoint''
      exact hregionBlock hpoint''.2
    rw [(safe.blockWindow block).union_eq]
    exact ⟨hprepared, hblockRegion⟩
  have hshadowUnion : shadow.union = region := by
    ext point
    constructor
    · rintro ⟨_index, _hblock, hregion⟩
      exact hregion
    · intro hregion
      rcases hsourceSubsetBlock hregion with ⟨index, hblock⟩
      exact ⟨index, hblock, hregion⟩
  have hsubBlock : IsSubshading shadow blockShading :=
    fun _ => Set.inter_subset_left
  have hsubPrepared : IsSubshading shadow prepared.shadow :=
    fun index => (hsubBlock index).trans
      ((safe.blockWindow block).subshading index)
  have hactive :
      ∀ cell ∈ wz1Lemma23ActiveCells shadow rho
          (source.extremal.delta_pos.trans_le (by
            rw [← twoScale.rhoRequested_eq]
            exact twoScale.rhoRequested.property.1)),
        (wz1Lemma23SnappedPoint rho cell) (2 : Fin 3) ∈
          Set.Icc (safe.blockWindow block).window.left
            ((safe.blockWindow block).window.left + Real.sqrt rho) := by
    intro cell hcell
    have hblockActive : cell ∈ wz1Lemma23ActiveCells blockShading rho
        (source.extremal.delta_pos.trans_le (by
          rw [← twoScale.rhoRequested_eq]
          exact twoScale.rhoRequested.property.1)) := by
      rw [wz1Lemma23_mem_active_iff] at hcell ⊢
      refine ⟨hcell.1, ?_⟩
      rcases hcell.2 with ⟨point, hpointShadow, hpointCell⟩
      exact ⟨point, hsubBlock.union_subset hpointShadow, hpointCell⟩
    simpa only [(safe.blockWindow block).window_left] using
      (safe.blockWindow block).active_cell_window cell hblockActive
  have hvolumePos : 0 < volume region := by
    dsimp only [region]
    rw [restriction.sourcePullback.volume_eq,
      restriction.sourcePullback_selectedCells]
    exact ENNReal.mul_pos
      (by exact_mod_cast restriction.cells_nonempty.card_ne_zero)
      twoScale.coarse.balanced.cellMass_pos.ne'
  have hvolumeTop : volume region ≠ ⊤ := by
    dsimp only [region]
    rw [restriction.sourcePullback.volume_eq,
      restriction.sourcePullback_selectedCells]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      twoScale.coarse.balanced.cellMass_ne_top
  rcases prepared.ofSubshading
      (safe.blockWindow block).window.left shadow hsubPrepared hactive
      (volume region) hvolumePos hvolumeTop
      (by rw [hshadowUnion]) with
    ⟨window, hleft, hwindowShading, hsupply⟩
  exact ⟨{
    shadow := shadow
    carrier_eq := fun _ => rfl
    subshading := hsubPrepared
    union_eq := hshadowUnion
    window := window
    window_left := hleft
    window_shading := hwindowShading
    window_supply := hsupply
  }⟩

/-- Run the original-slope Fubini selection inside an exact synchronized
cell restriction and identify every resulting second-cover parent with the
parent already assigned to that same literal `rho` cell. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData.selectFixedLine
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    (parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope)
    {cells : Finset (ℤ × ℤ × ℤ)}
    (restriction : PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
      data outerPopular envelope cells)
    (sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        restriction) :
    Nonempty (PureWZ2BalancedSafeOuterPopularCoarseRestrictedFixedLineData
      (parentData := parentData) restriction sourceWindow) := by
  have hwindowVolume : 0 < volume sourceWindow.window.shading.union := by
    exact sourceWindow.window.volumeSupply_pos.trans_le
      sourceWindow.window.volume_lower
  let line := Classical.choice
    (sourceWindow.window.selectHorizontalFixedLine hwindowVolume)
  let sourceParents := Classical.choice line.toFixedBinData.toParents
  have hlinePointInPullback : ∀ sourceCell ∈ line.heavyCells,
      line.representative sourceCell ∈
        restriction.sourcePullback.shading.union := by
    intro sourceCell hsourceCell
    have hwindow := line.representative_mem sourceCell hsourceCell
    rw [sourceWindow.window_shading, sourceWindow.union_eq] at hwindow
    exact hwindow
  have hrhoCellMem : ∀ sourceCell ∈ line.heavyCells,
      sourceParents.rhoCell sourceCell ∈ cells := by
    intro sourceCell hsourceCell
    have hpoint := hlinePointInPullback sourceCell hsourceCell
    rw [restriction.sourcePullback.union_eq,
      restriction.sourcePullback.selectedRegion_eq] at hpoint
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨cell, hcell, hpointCell⟩
    have hchosenCell := sourceParents.representative_mem_rhoCell
      sourceCell hsourceCell
    have heq : cell = sourceParents.rhoCell sourceCell :=
      ((mem_wz1PaperGridCube rho cell _).mp hpointCell).symm.trans
        ((mem_wz1PaperGridCube rho
          (sourceParents.rhoCell sourceCell) _).mp hchosenCell)
    have hcell' : cell ∈ cells := by
      rwa [restriction.sourcePullback_selectedCells] at hcell
    rwa [← heq]
  have hparentEq : ∀ sourceCell (hsourceCell : sourceCell ∈ line.heavyCells),
      sourceParents.parentCell sourceCell =
        parentData.parentCell (sourceParents.rhoCell sourceCell) := by
    intro sourceCell hsourceCell
    let rhoCell := sourceParents.rhoCell sourceCell
    let point := sourceParents.finePoint sourceCell
    have hpointCell : point ∈ wz1PaperGridCube rho rhoCell :=
      sourceParents.fine_point_mem_rhoCell sourceCell hsourceCell
    have hsourceParent : wz1PaperGridCube rho rhoCell ⊆
        wz1PaperGridCube twoScale.sqrtRequested.1
          (sourceParents.parentCell sourceCell) :=
      sourceParents.rho_cell_nested sourceCell hsourceCell
    have hsyncParent : wz1PaperGridCube rho rhoCell ⊆
        wz1PaperGridCube twoScale.sqrtRequested.1
          (parentData.parentCell rhoCell) :=
      parentData.cell_parent rhoCell (restriction.cells_subset
        (hrhoCellMem sourceCell hsourceCell))
    exact ((mem_wz1PaperGridCube twoScale.sqrtRequested.1
      (sourceParents.parentCell sourceCell) point).mp
        (hsourceParent hpointCell)).symm.trans
      ((mem_wz1PaperGridCube twoScale.sqrtRequested.1
        (parentData.parentCell rhoCell) point).mp
          (hsyncParent hpointCell))
  have hparentsSubset : sourceParents.parents ⊆ parentData.parents := by
    intro parent hparent
    rcases sourceParents.parent_hit parent hparent with
      ⟨sourceCell, hsourceCell, hcellParent⟩
    rw [← hcellParent, hparentEq sourceCell hsourceCell,
      parentData.parents_eq]
    exact Finset.mem_image.mpr
      ⟨sourceParents.rhoCell sourceCell,
        restriction.cells_subset (hrhoCellMem sourceCell hsourceCell), rfl⟩
  exact ⟨{
    line := line
    sourceParents := sourceParents
    rhoCell_mem := hrhoCellMem
    parent_eq := hparentEq
    parents_subset := hparentsSubset
  }⟩

/-- Keep every global-bin fibre of the source exact slice and identify its
literal side-`rho` owner and genuine second-cover parent inside the same
synchronized restriction. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData.toSourceGlobalBins
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    (parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope)
    {cells : Finset (ℤ × ℤ × ℤ)}
    (restriction : PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
      data outerPopular envelope cells)
    (sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        restriction) :
    Nonempty
      (PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) restriction sourceWindow) := by
  have hwindowVolume : 0 < volume sourceWindow.window.shading.union :=
    sourceWindow.window.volumeSupply_pos.trans_le
      sourceWindow.window.volume_lower
  let line : PureWZ2SourceHorizontalFixedLineData sourceWindow.window :=
    Classical.choice
      (sourceWindow.window.selectHorizontalFixedLine hwindowVolume)
  let core : ∀ bin : {bin // bin ∈ line.globalBins},
      PureWZ2SourceHorizontalFixedBinData sourceWindow.window := fun bin =>
    Classical.choose (line.coreAtGlobalBin bin.1 bin.2)
  let sourceParents : ∀ bin,
      PureWZ2SourceHorizontalFixedBinParentData (core bin) := fun bin =>
    Classical.choice ((core bin).toParents)
  have hlineBin : ∀ bin, (core bin).lineBin = bin.1 := by
    intro bin
    exact (Classical.choose_spec
      (line.coreAtGlobalBin bin.1 bin.2)).1
  have hheavy : ∀ bin, (core bin).heavyCells =
      pureWZ2SourceHorizontalGlobalBinCells line bin.1 := by
    intro bin
    exact (Classical.choose_spec
      (line.coreAtGlobalBin bin.1 bin.2)).2
  have hrhoCellMem : ∀ bin cell, cell ∈ (core bin).heavyCells →
      (sourceParents bin).rhoCell cell ∈ cells := by
    intro bin sourceCell hsourceCell
    have hwindow := (core bin).representative_mem sourceCell hsourceCell
    rw [sourceWindow.window_shading, sourceWindow.union_eq] at hwindow
    rw [restriction.sourcePullback.union_eq,
      restriction.sourcePullback.selectedRegion_eq] at hwindow
    rcases Set.mem_iUnion₂.mp hwindow.2 with
      ⟨cell, hcell, hpointCell⟩
    have hchosenCell := (sourceParents bin).representative_mem_rhoCell
      sourceCell hsourceCell
    have heq : cell = (sourceParents bin).rhoCell sourceCell :=
      ((mem_wz1PaperGridCube rho cell _).mp hpointCell).symm.trans
        ((mem_wz1PaperGridCube rho
          ((sourceParents bin).rhoCell sourceCell) _).mp hchosenCell)
    have hcell' : cell ∈ cells := by
      rwa [restriction.sourcePullback_selectedCells] at hcell
    rwa [← heq]
  have hparentEq : ∀ bin sourceCell
      (hsourceCell : sourceCell ∈ (core bin).heavyCells),
      (sourceParents bin).parentCell sourceCell =
        parentData.parentCell ((sourceParents bin).rhoCell sourceCell) := by
    intro bin sourceCell hsourceCell
    let rhoCell := (sourceParents bin).rhoCell sourceCell
    let point := (sourceParents bin).finePoint sourceCell
    have hpointCell : point ∈ wz1PaperGridCube rho rhoCell :=
      (sourceParents bin).fine_point_mem_rhoCell sourceCell hsourceCell
    have hsourceParent : wz1PaperGridCube rho rhoCell ⊆
        wz1PaperGridCube twoScale.sqrtRequested.1
          ((sourceParents bin).parentCell sourceCell) :=
      (sourceParents bin).rho_cell_nested sourceCell hsourceCell
    have hsyncParent : wz1PaperGridCube rho rhoCell ⊆
        wz1PaperGridCube twoScale.sqrtRequested.1
          (parentData.parentCell rhoCell) :=
      parentData.cell_parent rhoCell (restriction.cells_subset
        (hrhoCellMem bin sourceCell hsourceCell))
    exact ((mem_wz1PaperGridCube twoScale.sqrtRequested.1
      ((sourceParents bin).parentCell sourceCell) point).mp
        (hsourceParent hpointCell)).symm.trans
      ((mem_wz1PaperGridCube twoScale.sqrtRequested.1
        (parentData.parentCell rhoCell) point).mp
          (hsyncParent hpointCell))
  have hparentsSubset : ∀ bin,
      (sourceParents bin).parents ⊆ parentData.parents := by
    intro bin parent hparent
    rcases (sourceParents bin).parent_hit parent hparent with
      ⟨sourceCell, hsourceCell, hcellParent⟩
    rw [← hcellParent, hparentEq bin sourceCell hsourceCell,
      parentData.parents_eq]
    exact Finset.mem_image.mpr
      ⟨(sourceParents bin).rhoCell sourceCell,
        restriction.cells_subset
          (hrhoCellMem bin sourceCell hsourceCell), rfl⟩
  have hslice : line.sliceCells.card =
      ∑ bin : {bin // bin ∈ line.globalBins},
        (core bin).heavyCells.card := by
    calc
      line.sliceCells.card =
          ∑ bin ∈ line.globalBins,
            (pureWZ2SourceHorizontalGlobalBinCells line bin).card :=
        line.card_eq_sum_globalBinCells
      _ = ∑ bin : {bin // bin ∈ line.globalBins},
          (pureWZ2SourceHorizontalGlobalBinCells line bin.1).card := by
        exact Finset.sum_subtype line.globalBins (fun _ => Iff.rfl) _
      _ = ∑ bin : {bin // bin ∈ line.globalBins},
          (core bin).heavyCells.card := by
        apply Finset.sum_congr rfl
        intro bin _
        rw [hheavy bin]
  exact ⟨{
    line := line
    core := core
    lineBin_eq := hlineBin
    heavyCells_eq := hheavy
    sourceParents := sourceParents
    rhoCell_mem := hrhoCellMem
    parent_eq := hparentEq
    parents_subset := hparentsSubset
    slice_card := hslice
  }⟩

/-- A whole-cell envelope constructed after entering the exact source
pullback window cannot leave the synchronized coarse-cell restriction.  This
is the precise no-ambient-reentry statement needed before reusing the
fixed-bin graph preparation. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData.fixedBinEnvelope_union_subset
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    {cells : Finset (ℤ × ℤ × ℤ)}
    (restriction : PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
      data outerPopular envelope cells)
    (sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        restriction)
    {innerPopular : PureWZ2SourceWindowHeightPopularData
      sourceWindow.window (256 * rho)}
    {line : PureWZ2SourceHorizontalFixedBinData innerPopular.windowed}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {coarseCarrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    (fixedEnvelope : PureWZ2SourceFixedBinPopularCoarseCellEnvelopeData
      innerPopular retained coarseCarrier) :
    fixedEnvelope.shading.union ⊆ restriction.shading.union := by
  have hwindowCells : sourceWindow.window.shading.union ⊆
      wz2RetainedCellsUnion rho cells := by
    intro point hpoint
    rw [sourceWindow.window_shading, sourceWindow.union_eq] at hpoint
    rw [restriction.sourcePullback.union_eq,
      restriction.sourcePullback.selectedRegion_eq] at hpoint
    rw [restriction.sourcePullback_selectedCells] at hpoint
    exact hpoint.2
  have henvelopeCells : fixedEnvelope.shading.union ⊆
      wz2RetainedCellsUnion rho cells :=
    fixedEnvelope.union_subset_cells
      cells hwindowCells
  intro point hpoint
  rw [restriction.union_eq]
  exact henvelopeCells hpoint

/-- Every source-slice representative selected inside a regularized
synchronized window belongs to one of that restriction's literal side-`rho`
cells. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData.rhoCell_mem_restriction
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    (restriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass)
    (sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        restriction.restriction)
    {line : PureWZ2SourceHorizontalFixedBinData sourceWindow.window}
    (sourceParents : PureWZ2SourceHorizontalFixedBinParentData line) :
    ∀ sourceCell ∈ line.heavyCells,
      sourceParents.rhoCell sourceCell ∈ restriction.cells := by
  intro sourceCell hsourceCell
  have hwindow := line.representative_mem sourceCell hsourceCell
  rw [sourceWindow.window_shading, sourceWindow.union_eq] at hwindow
  rw [restriction.restriction.sourcePullback.union_eq,
    restriction.restriction.sourcePullback.selectedRegion_eq] at hwindow
  rcases Set.mem_iUnion₂.mp hwindow.2 with
    ⟨cell, hcell, hpointCell⟩
  have hchosenCell := sourceParents.representative_mem_rhoCell
    sourceCell hsourceCell
  have heq : cell = sourceParents.rhoCell sourceCell :=
    ((mem_wz1PaperGridCube rho cell _).mp hpointCell).symm.trans
      ((mem_wz1PaperGridCube rho
        (sourceParents.rhoCell sourceCell) _).mp hchosenCell)
  have hcell' : cell ∈ restriction.cells := by
    rwa [restriction.restriction.sourcePullback_selectedCells] at hcell
  rwa [← heq]

/-- The parent selected by the source fixed-line construction is the parent
already assigned to the same synchronized side-`rho` cell. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData.sourceParent_eq
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    (parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope)
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    (restriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass)
    (sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        restriction.restriction)
    {line : PureWZ2SourceHorizontalFixedBinData sourceWindow.window}
    (sourceParents : PureWZ2SourceHorizontalFixedBinParentData line) :
    ∀ sourceCell (hsourceCell : sourceCell ∈ line.heavyCells),
      sourceParents.parentCell sourceCell =
        parentData.parentCell (sourceParents.rhoCell sourceCell) := by
  intro sourceCell hsourceCell
  let rhoCell := sourceParents.rhoCell sourceCell
  let point := sourceParents.finePoint sourceCell
  have hpointCell : point ∈ wz1PaperGridCube rho rhoCell :=
    sourceParents.fine_point_mem_rhoCell sourceCell hsourceCell
  have hsourceParent : wz1PaperGridCube rho rhoCell ⊆
      wz1PaperGridCube twoScale.sqrtRequested.1
        (sourceParents.parentCell sourceCell) :=
    sourceParents.rho_cell_nested sourceCell hsourceCell
  have hrhoCell : rhoCell ∈ restriction.cells :=
    PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData.rhoCell_mem_restriction
      data outerPopular envelope restriction sourceWindow sourceParents
      sourceCell hsourceCell
  have hsyncParent : wz1PaperGridCube rho rhoCell ⊆
      wz1PaperGridCube twoScale.sqrtRequested.1
        (parentData.parentCell rhoCell) :=
    parentData.cell_parent rhoCell
      (restriction.restriction.cells_subset hrhoCell)
  exact ((mem_wz1PaperGridCube twoScale.sqrtRequested.1
    (sourceParents.parentCell sourceCell) point).mp
      (hsourceParent hpointCell)).symm.trans
    ((mem_wz1PaperGridCube twoScale.sqrtRequested.1
      (parentData.parentCell rhoCell) point).mp
        (hsyncParent hpointCell))

/-- All parents hit by a fixed global-bin fibre remain in the dyadically
regularized parent class which defined the synchronized restriction. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData.sourceParents_subset_weightClass
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    (parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope)
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    (restriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass)
    (sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        restriction.restriction)
    {line : PureWZ2SourceHorizontalFixedBinData sourceWindow.window}
    (sourceParents : PureWZ2SourceHorizontalFixedBinParentData line) :
    sourceParents.parents ⊆ weightClass.selectedParents := by
  intro parent hparent
  rcases sourceParents.parent_hit parent hparent with
    ⟨sourceCell, hsourceCell, hcellParent⟩
  have hrhoCell : sourceParents.rhoCell sourceCell ∈ restriction.cells :=
    PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData.rhoCell_mem_restriction
      data outerPopular envelope restriction sourceWindow sourceParents
      sourceCell hsourceCell
  have hparentEq :=
    PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData.sourceParent_eq
      data outerPopular envelope parentData restriction sourceWindow
      sourceParents sourceCell hsourceCell
  have hrhoCell' :
      sourceParents.rhoCell sourceCell ∈
        weightClass.selectedParents.biUnion parentData.cellsForParent := by
    simpa only [restriction.cells_eq] using hrhoCell
  rcases Finset.mem_biUnion.mp hrhoCell' with
    ⟨selectedParent, hselectedParent, hcellFiber⟩
  rw [parentData.cellsForParent_eq] at hcellFiber
  have hsyncParent := (Finset.mem_filter.mp hcellFiber).2
  rw [← hcellParent, hparentEq, hsyncParent]
  exact hselectedParent

/-- Materialize a dyadically regularized parent class as the union of all of
its synchronized side-`rho` fibres.  Distinct parent fibres are disjoint, so
the weight retained by `regularizeWeight` is exactly the selected cell count. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData.restrictCells
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    (parents : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope)
    (weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parents) :
    Nonempty
      (PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parents weightClass) := by
  let cells := weightClass.selectedParents.biUnion parents.cellsForParent
  have hfiberNonempty : ∀ parent ∈ weightClass.selectedParents,
      (parents.cellsForParent parent).Nonempty := by
    intro parent hparent
    have hparentAll := weightClass.selectedParents_subset hparent
    rw [parents.parents_eq] at hparentAll
    rcases Finset.mem_image.mp hparentAll with
      ⟨cell, hcell, hcellParent⟩
    refine ⟨cell, ?_⟩
    rw [parents.cellsForParent_eq]
    exact Finset.mem_filter.mpr ⟨hcell, hcellParent⟩
  have hcellsNonempty : cells.Nonempty := by
    rcases weightClass.selectedParents_nonempty with ⟨parent, hparent⟩
    rcases hfiberNonempty parent hparent with ⟨cell, hcell⟩
    exact ⟨cell, Finset.mem_biUnion.mpr ⟨parent, hparent, hcell⟩⟩
  have hcellsSubset : cells ⊆ envelope.cells := by
    intro cell hcell
    rcases Finset.mem_biUnion.mp hcell with
      ⟨parent, _hparent, hcellParent⟩
    rw [parents.cellsForParent_eq] at hcellParent
    exact (Finset.mem_filter.mp hcellParent).1
  have hfibersDisjoint : ∀ first ∈ weightClass.selectedParents,
      ∀ second ∈ weightClass.selectedParents, first ≠ second →
        Disjoint (parents.cellsForParent first)
          (parents.cellsForParent second) := by
    intro first _hfirst second _hsecond hne
    rw [Finset.disjoint_left]
    intro cell hcellFirst hcellSecond
    rw [parents.cellsForParent_eq] at hcellFirst hcellSecond
    have hfirstEq := (Finset.mem_filter.mp hcellFirst).2
    have hsecondEq := (Finset.mem_filter.mp hcellSecond).2
    exact hne (hfirstEq.symm.trans hsecondEq)
  have hcellsCard : cells.card =
      ∑ parent ∈ weightClass.selectedParents,
        (parents.cellsForParent parent).card := by
    dsimp only [cells]
    rw [Finset.card_biUnion hfibersDisjoint]
  let restriction := Classical.choice
    (PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData.restrictCells
      data outerPopular envelope cells hcellsSubset hcellsNonempty)
  have hretainedMass : envelope.sourcePullback.shading.mass ≤
      2 * (weightClass.bins : ENNReal) *
        restriction.sourcePullback.shading.mass := by
    rw [envelope.sourcePullback.mass_eq,
      envelope.sourcePullback_selectedCells,
      restriction.sourcePullback.mass_eq,
      restriction.sourcePullback_selectedCells, hcellsCard]
    have hweighted := mul_le_mul_right' weightClass.retained_weight
      twoScale.coarse.balanced.incidenceMass
    simpa [mul_assoc] using hweighted
  exact ⟨{
    cells := cells
    cells_eq := rfl
    cells_nonempty := hcellsNonempty
    cells_subset := hcellsSubset
    cells_card_eq := hcellsCard
    restriction := restriction
    retained_mass := hretainedMass
  }⟩

/-- A cell in the regularized restriction is assigned to one of the selected
parents defining that restriction. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData.cell_parent_selected
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parents : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parents}
    (restriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parents weightClass)
    {cell : ℤ × ℤ × ℤ} (hcell : cell ∈ restriction.cells) :
    parents.parentCell cell ∈ weightClass.selectedParents := by
  rw [restriction.cells_eq] at hcell
  rcases Finset.mem_biUnion.mp hcell with
    ⟨parent, hparent, hcellParent⟩
  rw [parents.cellsForParent_eq] at hcellParent
  have heq := (Finset.mem_filter.mp hcellParent).2
  rwa [heq]

/-- Materialize all synchronized cell fibres below a chosen nonempty
subfamily of a regularized parent class. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData.restrictParentSubfamily
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    (parents : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope)
    (weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parents)
    (selectedParents : Finset (ℤ × ℤ × ℤ))
    (hnonempty : selectedParents.Nonempty)
    (hsubset : selectedParents ⊆ weightClass.selectedParents) :
    Nonempty
      (PureWZ2BalancedSafeOuterPopularCoarseParentSubfamilyRestrictionData
        (weightClass := weightClass) selectedParents) := by
  let cells := selectedParents.biUnion parents.cellsForParent
  have hfiberNonempty : ∀ parent ∈ selectedParents,
      (parents.cellsForParent parent).Nonempty := by
    intro parent hparent
    have hparentAll := weightClass.selectedParents_subset (hsubset hparent)
    rw [parents.parents_eq] at hparentAll
    rcases Finset.mem_image.mp hparentAll with
      ⟨cell, hcell, hcellParent⟩
    refine ⟨cell, ?_⟩
    rw [parents.cellsForParent_eq]
    exact Finset.mem_filter.mpr ⟨hcell, hcellParent⟩
  have hcellsNonempty : cells.Nonempty := by
    rcases hnonempty with ⟨parent, hparent⟩
    rcases hfiberNonempty parent hparent with ⟨cell, hcell⟩
    exact ⟨cell, Finset.mem_biUnion.mpr ⟨parent, hparent, hcell⟩⟩
  have hcellsSubset : cells ⊆ envelope.cells := by
    intro cell hcell
    rcases Finset.mem_biUnion.mp hcell with
      ⟨parent, _hparent, hcellParent⟩
    rw [parents.cellsForParent_eq] at hcellParent
    exact (Finset.mem_filter.mp hcellParent).1
  have hfibersDisjoint : ∀ first ∈ selectedParents,
      ∀ second ∈ selectedParents, first ≠ second →
        Disjoint (parents.cellsForParent first)
          (parents.cellsForParent second) := by
    intro first _hfirst second _hsecond hne
    rw [Finset.disjoint_left]
    intro cell hcellFirst hcellSecond
    rw [parents.cellsForParent_eq] at hcellFirst hcellSecond
    have hfirstEq := (Finset.mem_filter.mp hcellFirst).2
    have hsecondEq := (Finset.mem_filter.mp hcellSecond).2
    exact hne (hfirstEq.symm.trans hsecondEq)
  have hcellsCard : cells.card =
      ∑ parent ∈ selectedParents, (parents.cellsForParent parent).card := by
    dsimp only [cells]
    rw [Finset.card_biUnion hfibersDisjoint]
  let cellRestriction := Classical.choice
    (PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData.restrictCells
      data outerPopular envelope cells hcellsSubset hcellsNonempty)
  have hcast :
      ((↑(∑ parent ∈ selectedParents,
          (parents.cellsForParent parent).card) : ENNReal)) =
        ∑ parent ∈ selectedParents,
          ((parents.cellsForParent parent).card : ENNReal) := by
    norm_cast
  have hlower :
      (selectedParents.card : ENNReal) * weightClass.weightFloor ≤
        (cells.card : ENNReal) := by
    rw [hcellsCard, hcast]
    calc
      (selectedParents.card : ENNReal) * weightClass.weightFloor =
          ∑ _parent ∈ selectedParents, weightClass.weightFloor := by
        simp [Finset.sum_const]
      _ ≤ ∑ parent ∈ selectedParents,
          ((parents.cellsForParent parent).card : ENNReal) := by
        exact Finset.sum_le_sum fun parent hparent =>
          (weightClass.weight_band parent (hsubset hparent)).1
  have hupper : (cells.card : ENNReal) ≤
      (selectedParents.card : ENNReal) *
        (2 * weightClass.weightFloor) := by
    rw [hcellsCard, hcast]
    calc
      (∑ parent ∈ selectedParents,
          ((parents.cellsForParent parent).card : ENNReal)) ≤
          ∑ _parent ∈ selectedParents,
            2 * weightClass.weightFloor := by
        exact Finset.sum_le_sum fun parent hparent =>
          (weightClass.weight_band parent (hsubset hparent)).2
      _ = (selectedParents.card : ENNReal) *
          (2 * weightClass.weightFloor) := by
        simp [Finset.sum_const]
  exact ⟨{
    selectedParents_nonempty := hnonempty
    selectedParents_subset := hsubset
    cells := cells
    cells_eq := rfl
    cells_card_eq := hcellsCard
    cellRestriction := cellRestriction
    weight_lower := hlower
    weight_upper := hupper
  }⟩

/-- Every parent in the synchronized parent image has a nonempty literal
cell fibre. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseParentData.cellsForParent_nonempty
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    (parents : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope)
    {parent : ℤ × ℤ × ℤ} (hparent : parent ∈ parents.parents) :
    (parents.cellsForParent parent).Nonempty := by
  rw [parents.parents_eq] at hparent
  rcases Finset.mem_image.mp hparent with ⟨cell, hcell, hcellParent⟩
  refine ⟨cell, ?_⟩
  rw [parents.cellsForParent_eq]
  exact Finset.mem_filter.mpr ⟨hcell, hcellParent⟩

/-- Run a second, coarse-scale exact-slice decomposition inside the complete
parent fibres selected by one source global bin.  The map from Lemma-23 cells
to literal paper cells has fibres of size at most `5^3 = 125`; this is the
only grid-overlap cost in the nested decomposition. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData.toNestedGlobalBins
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    {sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction}
    {sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow}
    {bin : {bin // bin ∈ sourceBins.line.globalBins}}
    (sync :
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
        weightRestriction sourceWindow sourceBins bin)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    Nonempty
      (PureWZ2BalancedSafeOuterPopularCoarseNestedGlobalBinFamilyData
        sync) := by
  have hexact : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection
          (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice
            sync.parentRestriction.cellRestriction.shading.union z))
        rho (1 - sigma)
        (10 * Kakeya.realRpowENN rho (-middleLoss)) := by
    intro z hz
    apply (sync.original.original_slope_exactADFixedBin z hz).mono
    rintro value ⟨point, hpoint, rfl⟩
    exact ⟨point, ⟨by
      apply sync.restrictedPreparation.prep.shadow_union_subset
      rw [sync.prep_union_eq]
      exact hpoint.1, hpoint.2⟩, rfl⟩
  let global := Classical.choice
    (PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData.prepareOriginalGlobal
      data outerPopular envelope sync.parentRestriction.cellRestriction hexact)
  let fixedLine := Classical.choice
    (PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseOriginalGlobalData.selectFixedLine
      global)
  let bins := Classical.choice
    (PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseFixedLineData.toGlobalBins
      fixedLine)
  let cells : ∀ nestedBin : {nestedBin //
      nestedBin ∈ fixedLine.line.globalBins}, Finset (ℤ × ℤ × ℤ) :=
    fun nestedBin =>
      (bins.core nestedBin).heavyCells.image (bins.rhoCell nestedBin)
  have hcellsNonempty : ∀ nestedBin, (cells nestedBin).Nonempty := by
    intro nestedBin
    exact (bins.core nestedBin).heavyCells_nonempty.image _
  have hcellsSubset : ∀ nestedBin, cells nestedBin ⊆
      sync.parentRestriction.cells := by
    intro nestedBin cell hcell
    rcases Finset.mem_image.mp hcell with ⟨graphCell, hgraphCell, rfl⟩
    exact bins.rhoCell_mem nestedBin graphCell hgraphCell
  have hheavyCard : ∀ nestedBin,
      (bins.core nestedBin).heavyCells.card ≤
        125 * (cells nestedBin).card := by
    intro nestedBin
    let core := bins.core nestedBin
    let owner := bins.rhoCell nestedBin
    have hrho : 0 < rho := by
      rw [← twoScale.rhoRequested_eq]
      exact twoScale.coarseGrains.extremal.delta_pos
    have hmeshPos : 0 < gridSide (twoScale.rhoRequested.1 / 2) := by
      simp only [gridSide]
      have hrhoRequested : 0 < twoScale.rhoRequested.1 :=
        twoScale.coarseGrains.extremal.delta_pos
      positivity
    have hrhoMesh : rho <
        2 * gridSide (twoScale.rhoRequested.1 / 2) := by
      rw [twoScale.rhoRequested_eq]
      simp only [gridSide]
      have hsqrtThreePos : 0 < Real.sqrt (3 : ℝ) := by positivity
      have hsqrtThreeLtTwo : Real.sqrt (3 : ℝ) < 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
          Real.sqrt_nonneg (3 : ℝ)]
      have hmul := mul_lt_mul_of_pos_left hsqrtThreeLtTwo hrho
      rw [show 2 * (2 * (rho / 2) / Real.sqrt 3) =
          2 * rho / Real.sqrt 3 by ring]
      exact (lt_div_iff₀ hsqrtThreePos).2 (by simpa [mul_comm] using hmul)
    have hownerFiber : ∀ ownerCell ∈ core.heavyCells.image owner,
        (core.heavyCells.filter fun cell => owner cell = ownerCell).card ≤
          125 := by
      intro ownerCell hownerCell
      rcases Finset.mem_image.mp hownerCell with
        ⟨baseCell, hbaseCell, rfl⟩
      let fiber := core.heavyCells.filter fun cell =>
        owner cell = owner baseCell
      let allowed : Finset (ℤ × ℤ × ℤ) :=
        (Finset.Icc (baseCell.1 - 2) (baseCell.1 + 2)).product
          ((Finset.Icc (baseCell.2.1 - 2) (baseCell.2.1 + 2)).product
            (Finset.Icc (baseCell.2.2 - 2) (baseCell.2.2 + 2)))
      have hfiberSubset : fiber ⊆ allowed := by
        intro cell hcell
        have hcellData := Finset.mem_filter.mp hcell
        have hcellRep := bins.representative_mem_rhoCell
          nestedBin cell hcellData.1
        have hbaseRep := bins.representative_mem_rhoCell
          nestedBin baseCell hbaseCell
        change core.representative cell ∈
          wz1PaperGridCube twoScale.rhoRequested.1 (owner cell) at hcellRep
        change core.representative baseCell ∈
          wz1PaperGridCube twoScale.rhoRequested.1 (owner baseCell) at hbaseRep
        rw [hcellData.2] at hcellRep
        have hcellRepRho : core.representative cell ∈
            wz1PaperGridCube rho (owner baseCell) := by
          simpa only [twoScale.rhoRequested_eq] using hcellRep
        have hbaseRepRho : core.representative baseCell ∈
            wz1PaperGridCube rho (owner baseCell) := by
          simpa only [twoScale.rhoRequested_eq] using hbaseRep
        rw [wz1PaperGridCube_eq_Ico hrho (owner baseCell)] at hcellRepRho
        rw [wz1PaperGridCube_eq_Ico hrho (owner baseCell)] at hbaseRepRho
        simp only [Set.mem_setOf_eq] at hcellRepRho hbaseRepRho
        have hxCoord :
            |core.representative cell (0 : Fin 3) -
              core.representative baseCell (0 : Fin 3)| < rho := by
          have hwidth :
              (((owner baseCell).1 : ℝ) + 1) * rho -
                  ((owner baseCell).1 : ℝ) * rho = rho := by ring
          rw [abs_lt]
          exact ⟨by linarith, by linarith⟩
        have hyCoord :
            |core.representative cell (1 : Fin 3) -
              core.representative baseCell (1 : Fin 3)| < rho := by
          have hwidth :
              (((owner baseCell).2.1 : ℝ) + 1) * rho -
                  ((owner baseCell).2.1 : ℝ) * rho = rho := by ring
          rw [abs_lt]
          exact ⟨by linarith, by linarith⟩
        have hzCoord :
            |core.representative cell (2 : Fin 3) -
              core.representative baseCell (2 : Fin 3)| < rho := by
          have hwidth :
              (((owner baseCell).2.2 : ℝ) + 1) * rho -
                  ((owner baseCell).2.2 : ℝ) * rho = rho := by ring
          rw [abs_lt]
          exact ⟨by linarith, by linarith⟩
        have hcoordClose : ∀ coordinate : Fin 3,
            |core.representative cell coordinate -
              core.representative baseCell coordinate| < rho := by
          intro coordinate
          fin_cases coordinate
          · exact hxCoord
          · exact hyCoord
          · exact hzCoord
        have hcellIndex := core.representative_index cell hcellData.1
        have hbaseIndex := core.representative_index baseCell hbaseCell
        have hindexClose : ∀ coordinate : Fin 3,
            |(match coordinate with
                | 0 => cell.1
                | 1 => cell.2.1
                | 2 => cell.2.2) -
              (match coordinate with
                | 0 => baseCell.1
                | 1 => baseCell.2.1
                | 2 => baseCell.2.2)| ≤ 2 := by
          intro coordinate
          have hratio :
              |core.representative cell coordinate /
                    gridSide (twoScale.rhoRequested.1 / 2) -
                core.representative baseCell coordinate /
                    gridSide (twoScale.rhoRequested.1 / 2)| < 2 := by
            rw [← sub_div, abs_div, abs_of_pos hmeshPos]
            apply (div_lt_iff₀ hmeshPos).2
            exact (hcoordClose coordinate).trans hrhoMesh
          have hfloor := wz1_abs_floor_sub_lt_le
            (x := core.representative cell coordinate /
              gridSide (twoScale.rhoRequested.1 / 2))
            (y := core.representative baseCell coordinate /
              gridSide (twoScale.rhoRequested.1 / 2))
            (N := 2) (by norm_num) hratio
          fin_cases coordinate
          · have hcellIndex0 :
                ⌊core.representative cell 0 /
                    gridSide (twoScale.rhoRequested.1 / 2)⌋ = cell.1 := by
              simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using
                congrArg Prod.fst hcellIndex
            have hbaseIndex0 :
                ⌊core.representative baseCell 0 /
                    gridSide (twoScale.rhoRequested.1 / 2)⌋ = baseCell.1 := by
              simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using
                congrArg Prod.fst hbaseIndex
            simpa [hcellIndex0, hbaseIndex0] using hfloor
          · have hcellIndex1 :
                ⌊core.representative cell 1 /
                    gridSide (twoScale.rhoRequested.1 / 2)⌋ = cell.2.1 := by
              simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using
                congrArg (fun index : ℤ × ℤ × ℤ => index.2.1) hcellIndex
            have hbaseIndex1 :
                ⌊core.representative baseCell 1 /
                    gridSide (twoScale.rhoRequested.1 / 2)⌋ =
                  baseCell.2.1 := by
              simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using
                congrArg (fun index : ℤ × ℤ × ℤ => index.2.1) hbaseIndex
            simpa [hcellIndex1, hbaseIndex1] using hfloor
          · have hcellIndex2 :
                ⌊core.representative cell 2 /
                    gridSide (twoScale.rhoRequested.1 / 2)⌋ = cell.2.2 := by
              simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using
                congrArg (fun index : ℤ × ℤ × ℤ => index.2.2) hcellIndex
            have hbaseIndex2 :
                ⌊core.representative baseCell 2 /
                    gridSide (twoScale.rhoRequested.1 / 2)⌋ =
                  baseCell.2.2 := by
              simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using
                congrArg (fun index : ℤ × ℤ × ℤ => index.2.2) hbaseIndex
            simpa [hcellIndex2, hbaseIndex2] using hfloor
        have hx := abs_le.mp (by simpa using hindexClose (0 : Fin 3))
        have hy := abs_le.mp (by simpa using hindexClose (1 : Fin 3))
        have hz := abs_le.mp (by simpa using hindexClose (2 : Fin 3))
        dsimp only [allowed]
        apply Finset.mem_product.mpr
        constructor
        · rw [Finset.mem_Icc]
          omega
        · apply Finset.mem_product.mpr
          constructor
          · rw [Finset.mem_Icc]
            omega
          · rw [Finset.mem_Icc]
            omega
      calc
        fiber.card ≤ allowed.card := Finset.card_le_card hfiberSubset
        _ = 125 := by
          have hcardFive (index : ℤ) :
              (Finset.Icc (index - 2) (index + 2)).card = 5 := by
            simp [Int.card_Icc] <;> omega
          simp [allowed, hcardFive]
    exact Finset.card_le_mul_card_image core.heavyCells 125 hownerFiber
  have hsliceCard : fixedLine.line.sliceCells.card ≤
      125 * ∑ nestedBin : {nestedBin //
        nestedBin ∈ fixedLine.line.globalBins}, (cells nestedBin).card := by
    rw [bins.slice_card, Finset.mul_sum]
    exact Finset.sum_le_sum fun nestedBin _ => hheavyCard nestedBin
  let restriction : ∀ nestedBin,
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
        data outerPopular envelope (cells nestedBin) := fun nestedBin =>
    Classical.choice
      (PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData.restrictCells
        data outerPopular envelope (cells nestedBin)
          ((hcellsSubset nestedBin).trans
            sync.parentRestriction.cellRestriction.cells_subset)
          (hcellsNonempty nestedBin))
  have hcellsActive : ∀ nestedBin, cells nestedBin ⊆
      wz1PaperActiveCells sync.coarseCarrier.shading
        twoScale.coarseGrains.extremal.delta_pos := by
    intro nestedBin cell hcell
    exact sync.cells_active_in_carrier (hcellsSubset nestedBin hcell)
  let preparation : ∀ nestedBin,
      PureWZ2SourceFixedBinCoarseCellRestrictionPreparationData
        sync.original (cells nestedBin) := fun nestedBin =>
    Classical.choice
      (sync.original.prepareCellRestrictionFixedBin (cells nestedBin)
        (hcellsActive nestedBin) (hcellsNonempty nestedBin)
        hgraphOne hheightAbsorb)
  have hprepUnion : ∀ nestedBin,
      (preparation nestedBin).prep.shadow.union =
        (restriction nestedBin).shading.union := by
    intro nestedBin
    rw [(preparation nestedBin).prep_shadow,
      (preparation nestedBin).union_eq,
      (restriction nestedBin).union_eq]
  exact ⟨{
    global := global
    fixedLine := fixedLine
    bins := bins
    cells := cells
    cells_eq := fun _ => rfl
    cells_nonempty := hcellsNonempty
    cells_subset := hcellsSubset
    heavyCells_card_le := hheavyCard
    slice_card_le_sum_cells := hsliceCard
    restriction := restriction
    preparation := preparation
    prep_union_eq := hprepUnion
  }⟩

/-- The whole synchronized coarse restriction is controlled by the sum of
the literal paper-cell volumes entering its nested global-bin preparations.
The physical `rho`-cube remains explicit for the later exact cancellation
against `graph_height_mass_cube_bound`. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseNestedGlobalBinFamilyData.aggregate_graph_volume_supply_le
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    {sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction}
    {sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow}
    {bin : {bin // bin ∈ sourceBins.line.globalBins}}
    {sync :
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
        weightRestriction sourceWindow sourceBins bin}
    (nested :
      PureWZ2BalancedSafeOuterPopularCoarseNestedGlobalBinFamilyData sync) :
    volume sync.parentRestriction.cellRestriction.shading.union ≤
      pureWZ2BalancedSafeNestedCoarseVolumeCost rho *
        ∑ nestedBin : {nestedBin //
          nestedBin ∈ nested.fixedLine.line.globalBins},
          volume (nested.preparation nestedBin).prep.shadow.union := by
  let sliceThickness : ENNReal :=
    ENNReal.ofReal (Real.sqrt rho + 2 * rho)
  let sliceDisk : ENNReal :=
    ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi
  let cubeVolume : ENNReal :=
    volume (wz1PaperGridCube rho (0, 0, 0))
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hsliceThicknessPos : 0 < sliceThickness := by
    apply ENNReal.ofReal_pos.mpr
    positivity
  have hwindowToSlice :
      volume sync.parentRestriction.cellRestriction.shading.union ≤
        volume (wz1Lemma23PlanarSlice nested.global.shadow.union
          nested.fixedLine.line.lineHeight) * sliceThickness := by
    rw [← nested.global.shadow_union]
    apply (ENNReal.div_le_iff hsliceThicknessPos.ne'
      ENNReal.ofReal_ne_top).mp
    simpa only [sliceThickness, twoScale.rhoRequested_eq] using
      nested.fixedLine.line.slice_area_lower
  have hball : nested.global.shadow.union ⊆
      Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    rw [nested.global.shadow_union] at hpoint
    have henvelope :=
      sync.parentRestriction.cellRestriction.subshading.union_subset hpoint
    have hcompanion := envelope.subshading.union_subset henvelope
    have hcoarse := data.subshading.union_subset hcompanion
    have hnorm := norm_le_two_of_mem_paperShading hcoarse
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hsliceArea :
      volume (wz1Lemma23PlanarSlice nested.global.shadow.union
          nested.fixedLine.line.lineHeight) ≤
        (nested.fixedLine.line.sliceCells.card : ENNReal) * sliceDisk := by
    have hraw := wz1_lemma23_exactSlice_area_le_two nested.global.shadow
      (by simpa only [twoScale.rhoRequested_eq] using hrho) hball
      nested.fixedLine.line.lineHeight
    simpa [nested.fixedLine.line.sliceCells_eq, sliceDisk,
      twoScale.rhoRequested_eq] using hraw
  have hcount :
      (nested.fixedLine.line.sliceCells.card : ENNReal) ≤
        125 * ∑ nestedBin : {nestedBin //
          nestedBin ∈ nested.fixedLine.line.globalBins},
          ((nested.cells nestedBin).card : ENNReal) := by
    exact_mod_cast nested.slice_card_le_sum_cells
  have hcellVolumes :
      (∑ nestedBin : {nestedBin //
          nestedBin ∈ nested.fixedLine.line.globalBins},
          ((nested.cells nestedBin).card : ENNReal)) * cubeVolume =
        ∑ nestedBin : {nestedBin //
          nestedBin ∈ nested.fixedLine.line.globalBins},
          volume (nested.preparation nestedBin).prep.shadow.union := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro nestedBin _
    rw [nested.prep_union_eq nestedBin,
      (nested.restriction nestedBin).volume_eq]
  have hcubePos : 0 < cubeVolume := by
    dsimp only [cubeVolume]
    rw [wz1PaperGridCube_volume_exact hrho]
    exact ENNReal.ofReal_pos.mpr (pow_pos hrho 3)
  have hcubeTop : cubeVolume ≠ ⊤ := by
    dsimp only [cubeVolume]
    rw [wz1PaperGridCube_volume_exact hrho]
    exact ENNReal.ofReal_ne_top
  have hcancel : cubeVolume⁻¹ * cubeVolume = 1 :=
    ENNReal.inv_mul_cancel hcubePos.ne' hcubeTop
  calc
    volume sync.parentRestriction.cellRestriction.shading.union ≤
        volume (wz1Lemma23PlanarSlice nested.global.shadow.union
          nested.fixedLine.line.lineHeight) * sliceThickness *
          1 := by simpa using hwindowToSlice
    _ ≤ (((nested.fixedLine.line.sliceCells.card : ENNReal) * sliceDisk) *
          sliceThickness) * 1 := by gcongr
    _ ≤ ((125 * ∑ nestedBin : {nestedBin //
          nestedBin ∈ nested.fixedLine.line.globalBins},
          ((nested.cells nestedBin).card : ENNReal)) * sliceDisk *
        sliceThickness) * 1 := by gcongr
    _ = pureWZ2BalancedSafeNestedCoarseVolumeCost rho *
        ((∑ nestedBin : {nestedBin //
          nestedBin ∈ nested.fixedLine.line.globalBins},
          ((nested.cells nestedBin).card : ENNReal)) * cubeVolume) := by
      rw [show pureWZ2BalancedSafeNestedCoarseVolumeCost rho =
          125 * sliceThickness * sliceDisk * cubeVolume⁻¹ by
        simp [pureWZ2BalancedSafeNestedCoarseVolumeCost, sliceThickness,
          sliceDisk, cubeVolume, div_eq_mul_inv]]
      calc
        _ = 125 * sliceThickness * sliceDisk *
              (∑ nestedBin : {nestedBin //
                nestedBin ∈ nested.fixedLine.line.globalBins},
                ((nested.cells nestedBin).card : ENNReal)) := by ac_rfl
        _ = (125 * sliceThickness * sliceDisk *
              (∑ nestedBin : {nestedBin //
                nestedBin ∈ nested.fixedLine.line.globalBins},
                ((nested.cells nestedBin).card : ENNReal))) *
              cubeVolume⁻¹ * cubeVolume :=
          (ENNReal.inv_mul_cancel_right hcubePos.ne' hcubeTop).symm
        _ = _ := by ac_rfl
    _ = pureWZ2BalancedSafeNestedCoarseVolumeCost rho *
        ∑ nestedBin : {nestedBin //
          nestedBin ∈ nested.fixedLine.line.globalBins},
          volume (nested.preparation nestedBin).prep.shadow.union := by
      rw [hcellVolumes]

/-- Select all nested bins above the common graph-volume threshold.  The
aggregate estimate shows that these bins retain at least half of the total
nested graph volume. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseNestedGlobalBinFamilyData.selectGoodBins
    {volumeLoss : ℝ}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    {sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction}
    {sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow}
    {bin : {bin // bin ∈ sourceBins.line.globalBins}}
    {sync :
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
        weightRestriction sourceWindow sourceBins bin}
    (nested :
      PureWZ2BalancedSafeOuterPopularCoarseNestedGlobalBinFamilyData sync)
    (hscaled :
      2 * ((nested.fixedLine.line.globalBins.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss)) *
          pureWZ2BalancedSafeNestedCoarseVolumeCost rho ≤
        volume sync.parentRestriction.cellRestriction.shading.union) :
    Nonempty
      (PureWZ2BalancedSafeOuterPopularCoarseNestedGoodBinData
        (volumeLoss := volumeLoss) nested) := by
  let allBins := (Finset.univ : Finset {nestedBin //
    nestedBin ∈ nested.fixedLine.line.globalBins})
  let supply : {nestedBin // nestedBin ∈
      nested.fixedLine.line.globalBins} → ENNReal := fun nestedBin =>
    volume (nested.preparation nestedBin).prep.shadow.union
  let threshold := Kakeya.realRpowENN (256 * rho)
    (1 + sigma / 2 + volumeLoss)
  have haggregate :=
    PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseNestedGlobalBinFamilyData.aggregate_graph_volume_supply_le
      nested
  have hcostPos : 0 < pureWZ2BalancedSafeNestedCoarseVolumeCost rho := by
    unfold pureWZ2BalancedSafeNestedCoarseVolumeCost
    have hrho : 0 < rho := by
      rw [← twoScale.rhoRequested_eq]
      exact twoScale.coarseGrains.extremal.delta_pos
    apply ENNReal.div_pos
    · positivity
    · rw [wz1PaperGridCube_volume_exact hrho]
      exact ENNReal.ofReal_ne_top
  have hcostTop : pureWZ2BalancedSafeNestedCoarseVolumeCost rho ≠ ⊤ := by
    unfold pureWZ2BalancedSafeNestedCoarseVolumeCost
    have hrho : 0 < rho := by
      rw [← twoScale.rhoRequested_eq]
      exact twoScale.coarseGrains.extremal.delta_pos
    apply ENNReal.div_ne_top
    · repeat' apply ENNReal.mul_ne_top
      all_goals simp
    · rw [wz1PaperGridCube_volume_exact hrho]
      exact (ENNReal.ofReal_pos.mpr (pow_pos hrho 3)).ne'
  have hsumLower : 2 * ((allBins.card : ENNReal) * threshold) ≤
      ∑ nestedBin ∈ allBins, supply nestedBin := by
    apply (ENNReal.mul_le_mul_iff_right hcostPos.ne' hcostTop).mp
    calc
      pureWZ2BalancedSafeNestedCoarseVolumeCost rho *
          (2 * ((allBins.card : ENNReal) * threshold)) =
        2 * ((nested.fixedLine.line.globalBins.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss)) *
          pureWZ2BalancedSafeNestedCoarseVolumeCost rho := by
            simp [allBins, threshold]
            ring
      _ ≤ volume sync.parentRestriction.cellRestriction.shading.union := hscaled
      _ ≤ pureWZ2BalancedSafeNestedCoarseVolumeCost rho *
          ∑ nestedBin : {nestedBin //
            nestedBin ∈ nested.fixedLine.line.globalBins},
            volume (nested.preparation nestedBin).prep.shadow.union :=
        haggregate
      _ = pureWZ2BalancedSafeNestedCoarseVolumeCost rho *
          ∑ nestedBin ∈ allBins, supply nestedBin := by
        simp [allBins, supply]
  have hthresholdTop : threshold ≠ ⊤ := by
    simp [threshold, Kakeya.realRpowENN]
  have hhalf := finset_good_weighted_supply_retains_half
    allBins supply 1 threshold hthresholdTop (by
      simpa [Finset.sum_const] using hsumLower)
  let selected := allBins.filter fun nestedBin =>
    threshold ≤ supply nestedBin
  have htotalPos : 0 < ∑ nestedBin ∈ allBins, supply nestedBin := by
    have hthresholdPos : 0 < threshold := by
      apply ENNReal.ofReal_pos.mpr
      apply Real.rpow_pos_of_pos
      have hrho : 0 < rho := by
        rw [← twoScale.rhoRequested_eq]
        exact twoScale.coarseGrains.extremal.delta_pos
      positivity
    have hbinsPos : 0 < (allBins.card : ENNReal) := by
      have hbinsNonempty : allBins.Nonempty := by
        exact ⟨⟨nested.fixedLine.line.lineBin,
          nested.fixedLine.line.lineBin_mem⟩, by simp [allBins]⟩
      exact_mod_cast hbinsNonempty.card_pos
    have hleftPos : 0 < 2 * ((allBins.card : ENNReal) * threshold) := by
      positivity
    exact hleftPos.trans_le hsumLower
  have hselectedNonempty : selected.Nonempty := by
    by_contra hempty
    have hselectedEmpty : selected = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hleZero : (∑ nestedBin ∈ allBins, supply nestedBin) ≤ 0 := by
      simpa [selected, hselectedEmpty] using hhalf
    exact (not_le_of_gt htotalPos) hleZero
  exact ⟨{
    selected := selected
    selected_nonempty := hselectedNonempty
    volume_lower := by
      intro nestedBin hnestedBin
      have hgood := (Finset.mem_filter.mp hnestedBin).2
      simpa [threshold, supply,
        (nested.preparation nestedBin).prep.graphScale_eq] using hgood
    total_volume_le := by
      simpa [selected, allBins, supply, threshold,
        (nested.preparation _).prep.graphScale_eq] using hhalf
  }⟩

/-- Continue every retained nested bin through the existing preparation-
indexed graph and rich-height pipeline. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseNestedGoodBinData.toRichFamily
    {normalEta finalLoss theoremEta volumeLoss constantLoss extraLoss : ℝ}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    {sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction}
    {sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow}
    {bin : {bin // bin ∈ sourceBins.line.globalBins}}
    {sync :
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
        weightRestriction sourceWindow sourceBins bin}
    {nested :
      PureWZ2BalancedSafeOuterPopularCoarseNestedGlobalBinFamilyData sync}
    (good : PureWZ2BalancedSafeOuterPopularCoarseNestedGoodBinData
      (volumeLoss := volumeLoss) nested)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hnormalEta : 0 < normalEta)
    (hnormalEtaSigma : 4 * normalEta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + normalEta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * outputLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) normalEta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (hlocalizationAbsorb :
      Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) ≤
        Real.sqrt (4 * rho) / 14)
    (hlocalConstant :
      35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) ≤
        19 * (10 * Kakeya.realRpowENN rho (-middleLoss)))
    (hCOne : (1 : ENNReal) ≤
      10 * Kakeya.realRpowENN rho (-middleLoss))
    (hCpower :
      (10 * Kakeya.realRpowENN rho (-middleLoss)).toReal ≤
        Real.rpow (256 * rho) (-constantLoss))
    (hextraPower : ∀ nestedBin : {nestedBin // nestedBin ∈ good.selected},
      ∀ pipeline : PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
          (normalEta := normalEta)
          (nested.preparation nestedBin.1).prep,
        (pipeline.preparedGraph.graph.residue.extraCost : ℝ) ≤
          Real.rpow (nested.preparation nestedBin.1).prep.graphScale
            (-extraLoss))
    (hedgeAbsorb : ∀ nestedBin : {nestedBin // nestedBin ∈ good.selected},
      Real.rpow (wz1Lemma23Theorem22Scale
          (nested.preparation nestedBin.1).prep.graphScale)
          (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow (nested.preparation nestedBin.1).prep.graphScale
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss +
              4 * extraLoss))
    (hKatzTao : ∀ nestedBin : {nestedBin // nestedBin ∈ good.selected},
      (4 : ENNReal) ≤ Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale
          (nested.preparation nestedBin.1).prep.graphScale) (-theoremEta))
    (hprojection : ∀ nestedBin : {nestedBin // nestedBin ∈ good.selected},
      ∀ pipeline : PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
          (normalEta := normalEta)
          (nested.preparation nestedBin.1).prep,
      ∀ ready : PureWZ2SourceFixedBinCoarseReadyGraph
          (theoremEta := theoremEta) pipeline.sharp,
        WZ1Proposition8_9AlternativeAUnion
          ready.ready.deltaGraph finalLoss
          ready.common.F ready.common.G₁ ready.common.G₁)
    (hscaleOne : 5 * (256 * rho) ≤ 1)
    (hlengthLower :
      Real.rpow (5 * (256 * rho)) (1 / 2 + finalLoss) ≤
        twoScale.sqrtRequested.1) :
    Nonempty
      (PureWZ2BalancedSafeOuterPopularCoarseNestedRichFamilyData
        (normalEta := normalEta) (finalLoss := finalLoss)
        (theoremEta := theoremEta) good) := by
  have hpipeline : ∀ nestedBin : {nestedBin // nestedBin ∈ good.selected},
      Nonempty (PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
        (normalEta := normalEta)
        (nested.preparation nestedBin.1).prep) := fun nestedBin =>
    (nested.preparation nestedBin.1).prep.coarseGraphPipelineAtPreparationFixedBin
      hbridge hsigma hsigmaOne hnormalEta hnormalEtaSigma hcertificateOne
      hsourceFloor hlocalPower hglobalPower hPlanarSmall hrootSmall20
      hlocalizationAbsorb hlocalConstant
      ((by
          apply ENNReal.ofReal_pos.mpr
          apply Real.rpow_pos_of_pos
          exact (nested.preparation nestedBin.1).prep.graphScale_pos :
          0 < Kakeya.realRpowENN
            (nested.preparation nestedBin.1).prep.graphScale
              (1 + sigma / 2 + volumeLoss)).trans_le
        (good.volume_lower nestedBin.1 nestedBin.2))
  let pipeline : ∀ nestedBin : {nestedBin // nestedBin ∈ good.selected},
      PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
        (normalEta := normalEta)
        (nested.preparation nestedBin.1).prep := fun nestedBin =>
    Classical.choice (hpipeline nestedBin)
  have hrich : ∀ nestedBin : {nestedBin // nestedBin ∈ good.selected},
      Nonempty (PureWZ2SourceFixedBinCoarseRichPipelineAtPreparationData
        (finalLoss := finalLoss) (theoremEta := theoremEta)
        (pipeline nestedBin)) := fun nestedBin => by
    apply (pipeline nestedBin).toRichPipelineAtPreparationFixedBin
      hsigma hsigmaOne hCOne
      (by simpa [(nested.preparation nestedBin.1).prep.graphScale_eq] using
        hCpower)
      (good.volume_lower nestedBin.1 nestedBin.2)
      (hextraPower nestedBin (pipeline nestedBin))
      (hedgeAbsorb nestedBin) (hKatzTao nestedBin)
      (hprojection nestedBin (pipeline nestedBin))
    · simpa [(nested.preparation nestedBin.1).prep.graphScale_eq] using
        hscaleOne
    · simpa [(nested.preparation nestedBin.1).prep.graphScale_eq] using
        hlengthLower
  let rich : ∀ nestedBin : {nestedBin // nestedBin ∈ good.selected},
      PureWZ2SourceFixedBinCoarseRichPipelineAtPreparationData
        (finalLoss := finalLoss) (theoremEta := theoremEta)
        (pipeline nestedBin) := fun nestedBin =>
    Classical.choice (hrich nestedBin)
  let saturation : ∀ nestedBin : {nestedBin // nestedBin ∈ good.selected},
      PureWZ2SourceFixedBinCoarseRichHeightSaturationData
        (rich nestedBin).heightLift := fun nestedBin =>
    Classical.choice (rich nestedBin).toRichHeightSaturation
  exact ⟨{ pipeline := pipeline, rich := rich, saturation := saturation }⟩

/-- Sum the rich-height estimate over every retained nested bin and cancel
the common physical side-`rho` cube.  This is the quantitative endpoint of
the second coarse Fubini stage. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseNestedRichFamilyData.aggregate_heightLift_mass_bound
    {normalEta finalLoss theoremEta volumeLoss extraLoss : ℝ}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    {sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction}
    {sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow}
    {bin : {bin // bin ∈ sourceBins.line.globalBins}}
    {sync :
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
        weightRestriction sourceWindow sourceBins bin}
    {nested :
      PureWZ2BalancedSafeOuterPopularCoarseNestedGlobalBinFamilyData sync}
    {good : PureWZ2BalancedSafeOuterPopularCoarseNestedGoodBinData
      (volumeLoss := volumeLoss) nested}
    (richFamily :
      PureWZ2BalancedSafeOuterPopularCoarseNestedRichFamilyData
        (normalEta := normalEta) (finalLoss := finalLoss)
        (theoremEta := theoremEta) good)
    (hextraPower : ∀ nestedBin : {nestedBin // nestedBin ∈ good.selected},
      ((richFamily.pipeline nestedBin).preparedGraph.graph.residue.extraCost :
          ℝ) ≤
        Real.rpow (nested.preparation nestedBin.1).prep.graphScale
          (-extraLoss)) :
    volume sync.parentRestriction.cellRestriction.shading.union *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass ≤
      2 * pureWZ2BalancedSafeNestedCoarseRawVolumeCost rho *
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss *
        ∑ nestedBin : {nestedBin // nestedBin ∈ good.selected},
          (richFamily.rich nestedBin).heightLift.shading.mass := by
  let floor : ENNReal :=
    pureWZ2SourceHorizontalRichFloor rho finalLoss
  let incidenceMass : ENNReal :=
    twoScale.coarse.balanced.incidenceMass
  let heightCost : ENNReal :=
    PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
      rho extraLoss
  let cubeVolume : ENNReal :=
    volume (wz1PaperGridCube rho (0, 0, 0))
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hcubePos : 0 < cubeVolume := by
    dsimp only [cubeVolume]
    rw [wz1PaperGridCube_volume_exact hrho]
    exact ENNReal.ofReal_pos.mpr (pow_pos hrho 3)
  have hcubeTop : cubeVolume ≠ ⊤ := by
    dsimp only [cubeVolume]
    rw [wz1PaperGridCube_volume_exact hrho]
    exact ENNReal.ofReal_ne_top
  have hcostCube :
      pureWZ2BalancedSafeNestedCoarseVolumeCost rho * cubeVolume =
        pureWZ2BalancedSafeNestedCoarseRawVolumeCost rho := by
    unfold pureWZ2BalancedSafeNestedCoarseVolumeCost
      pureWZ2BalancedSafeNestedCoarseRawVolumeCost
    rw [div_eq_mul_inv]
    calc
      (125 * ENNReal.ofReal (Real.sqrt rho + 2 * rho) *
          (ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi) *
          cubeVolume⁻¹) * cubeVolume =
        (125 * ENNReal.ofReal (Real.sqrt rho + 2 * rho) *
          (ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi)) *
          (cubeVolume⁻¹ * cubeVolume) := by ac_rfl
      _ = _ := by
        rw [ENNReal.inv_mul_cancel hcubePos.ne' hcubeTop, mul_one]
  have hselectedVolumes :
      (∑ nestedBin ∈ good.selected,
          volume (nested.preparation nestedBin).prep.shadow.union) =
        ∑ nestedBin : {nestedBin // nestedBin ∈ good.selected},
          volume (nested.preparation nestedBin.1).prep.shadow.union := by
    exact Finset.sum_subtype good.selected (fun _ => Iff.rfl) _
  have hlocal :
      (∑ nestedBin : {nestedBin // nestedBin ∈ good.selected},
          volume (nested.preparation nestedBin.1).prep.shadow.union) *
            floor * incidenceMass ≤
        heightCost *
          (∑ nestedBin : {nestedBin // nestedBin ∈ good.selected},
            (richFamily.rich nestedBin).heightLift.shading.mass) *
          cubeVolume := by
    calc
      _ = ∑ nestedBin : {nestedBin // nestedBin ∈ good.selected},
          (volume (nested.preparation nestedBin.1).prep.shadow.union *
            floor * incidenceMass) := by
        rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ ∑ nestedBin : {nestedBin // nestedBin ∈ good.selected},
          (heightCost *
            (richFamily.rich nestedBin).heightLift.shading.mass *
            cubeVolume) := by
        exact Finset.sum_le_sum fun nestedBin _ => by
          simpa [heightCost, floor, incidenceMass] using
            (richFamily.saturation nestedBin).graph_height_mass_cube_bound
              (hextraPower nestedBin)
      _ = heightCost *
          (∑ nestedBin : {nestedBin // nestedBin ∈ good.selected},
            (richFamily.rich nestedBin).heightLift.shading.mass) *
          cubeVolume := by
        rw [Finset.mul_sum, Finset.sum_mul]
  calc
    volume sync.parentRestriction.cellRestriction.shading.union *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass ≤
        (pureWZ2BalancedSafeNestedCoarseVolumeCost rho *
          ∑ nestedBin : {nestedBin //
            nestedBin ∈ nested.fixedLine.line.globalBins},
            volume (nested.preparation nestedBin).prep.shadow.union) *
          floor * incidenceMass := by
      have h := mul_le_mul_right'
        (mul_le_mul_right'
          (PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseNestedGlobalBinFamilyData.aggregate_graph_volume_supply_le
            nested) floor) incidenceMass
      simpa only [mul_assoc] using h
    _ ≤ (pureWZ2BalancedSafeNestedCoarseVolumeCost rho *
          (2 * ∑ nestedBin ∈ good.selected,
            volume (nested.preparation nestedBin).prep.shadow.union)) *
          floor * incidenceMass := by
      have h := mul_le_mul_right'
        (mul_le_mul_right'
          (mul_le_mul_left' good.total_volume_le
            (pureWZ2BalancedSafeNestedCoarseVolumeCost rho)) floor)
        incidenceMass
      simpa only [mul_assoc] using h
    _ = 2 * pureWZ2BalancedSafeNestedCoarseVolumeCost rho *
        ((∑ nestedBin : {nestedBin // nestedBin ∈ good.selected},
          volume (nested.preparation nestedBin.1).prep.shadow.union) *
            floor * incidenceMass) := by
      rw [hselectedVolumes]
      ring
    _ ≤ 2 * pureWZ2BalancedSafeNestedCoarseVolumeCost rho *
        (heightCost *
          (∑ nestedBin : {nestedBin // nestedBin ∈ good.selected},
            (richFamily.rich nestedBin).heightLift.shading.mass) *
          cubeVolume) := by gcongr
    _ = 2 * pureWZ2BalancedSafeNestedCoarseRawVolumeCost rho *
        heightCost *
          ∑ nestedBin : {nestedBin // nestedBin ∈ good.selected},
            (richFamily.rich nestedBin).heightLift.shading.mass := by
      calc
        _ = (2 * pureWZ2BalancedSafeNestedCoarseVolumeCost rho *
            cubeVolume) * heightCost *
              ∑ nestedBin : {nestedBin // nestedBin ∈ good.selected},
                (richFamily.rich nestedBin).heightLift.shading.mass := by ring
        _ = 2 * (pureWZ2BalancedSafeNestedCoarseVolumeCost rho *
              cubeVolume) * heightCost *
              ∑ nestedBin : {nestedBin // nestedBin ∈ good.selected},
                (richFamily.rich nestedBin).heightLift.shading.mass := by ring
        _ = _ := by rw [hcostCube]

/-- Cardinal form of `aggregate_heightLift_mass_bound`.  Here the physical
side-`rho` cube is cancelled exactly, leaving the normalized nested Fubini
cost.  This is the form consumed by the preceding source-slice count. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseNestedRichFamilyData.aggregate_cell_heightLift_mass_bound
    {normalEta finalLoss theoremEta volumeLoss extraLoss : ℝ}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    {sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction}
    {sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow}
    {bin : {bin // bin ∈ sourceBins.line.globalBins}}
    {sync :
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
        weightRestriction sourceWindow sourceBins bin}
    {nested :
      PureWZ2BalancedSafeOuterPopularCoarseNestedGlobalBinFamilyData sync}
    {good : PureWZ2BalancedSafeOuterPopularCoarseNestedGoodBinData
      (volumeLoss := volumeLoss) nested}
    (richFamily :
      PureWZ2BalancedSafeOuterPopularCoarseNestedRichFamilyData
        (normalEta := normalEta) (finalLoss := finalLoss)
        (theoremEta := theoremEta) good)
    (hextraPower : ∀ nestedBin : {nestedBin // nestedBin ∈ good.selected},
      ((richFamily.pipeline nestedBin).preparedGraph.graph.residue.extraCost :
          ℝ) ≤
        Real.rpow (nested.preparation nestedBin.1).prep.graphScale
          (-extraLoss)) :
    (sync.parentRestriction.cells.card : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass ≤
      2 * pureWZ2BalancedSafeNestedCoarseVolumeCost rho *
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss *
        ∑ nestedBin : {nestedBin // nestedBin ∈ good.selected},
          (richFamily.rich nestedBin).heightLift.shading.mass := by
  let cubeVolume : ENNReal :=
    volume (wz1PaperGridCube rho (0, 0, 0))
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hcubePos : 0 < cubeVolume := by
    dsimp only [cubeVolume]
    rw [wz1PaperGridCube_volume_exact hrho]
    exact ENNReal.ofReal_pos.mpr (pow_pos hrho 3)
  have hcubeTop : cubeVolume ≠ ⊤ := by
    dsimp only [cubeVolume]
    rw [wz1PaperGridCube_volume_exact hrho]
    exact ENNReal.ofReal_ne_top
  have hscaled :
      ((sync.parentRestriction.cells.card : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass) * cubeVolume ≤
        (2 * pureWZ2BalancedSafeNestedCoarseVolumeCost rho *
          PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
            rho extraLoss *
          ∑ nestedBin : {nestedBin // nestedBin ∈ good.selected},
            (richFamily.rich nestedBin).heightLift.shading.mass) *
          cubeVolume := by
    calc
      ((sync.parentRestriction.cells.card : ENNReal) *
            pureWZ2SourceHorizontalRichFloor rho finalLoss *
            twoScale.coarse.balanced.incidenceMass) * cubeVolume =
        volume sync.parentRestriction.cellRestriction.shading.union *
          pureWZ2SourceHorizontalRichFloor rho finalLoss *
          twoScale.coarse.balanced.incidenceMass := by
        rw [sync.parentRestriction.cellRestriction.volume_eq]
        dsimp only [cubeVolume]
        ring
      _ ≤ 2 * pureWZ2BalancedSafeNestedCoarseRawVolumeCost rho *
          PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
            rho extraLoss *
          ∑ nestedBin : {nestedBin // nestedBin ∈ good.selected},
            (richFamily.rich nestedBin).heightLift.shading.mass :=
        PureWZ2BalancedSafeOuterPopularCoarseNestedRichFamilyData.aggregate_heightLift_mass_bound
          richFamily hextraPower
      _ = (2 * pureWZ2BalancedSafeNestedCoarseVolumeCost rho *
          PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
            rho extraLoss *
          ∑ nestedBin : {nestedBin // nestedBin ∈ good.selected},
            (richFamily.rich nestedBin).heightLift.shading.mass) *
            cubeVolume := by
        have hcostCube :
            pureWZ2BalancedSafeNestedCoarseVolumeCost rho * cubeVolume =
              pureWZ2BalancedSafeNestedCoarseRawVolumeCost rho := by
          unfold pureWZ2BalancedSafeNestedCoarseVolumeCost
            pureWZ2BalancedSafeNestedCoarseRawVolumeCost
          rw [div_eq_mul_inv]
          calc
            (125 * ENNReal.ofReal (Real.sqrt rho + 2 * rho) *
                (ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi) *
                cubeVolume⁻¹) * cubeVolume =
              (125 * ENNReal.ofReal (Real.sqrt rho + 2 * rho) *
                (ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi)) *
                (cubeVolume⁻¹ * cubeVolume) := by ac_rfl
            _ = _ := by
              rw [ENNReal.inv_mul_cancel hcubePos.ne' hcubeTop, mul_one]
        calc
          _ = 2 * (pureWZ2BalancedSafeNestedCoarseVolumeCost rho *
              cubeVolume) *
              PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
                rho extraLoss *
              ∑ nestedBin : {nestedBin // nestedBin ∈ good.selected},
                (richFamily.rich nestedBin).heightLift.shading.mass := by
            rw [hcostCube]
          _ = _ := by ring
  exact (ENNReal.mul_le_mul_iff_right hcubePos.ne' hcubeTop).mp
    (by simpa only [mul_assoc, mul_comm cubeVolume] using hscaled)

/-- Continue one source-selected global bin to a genuine-coarse graph
preparation on the complete synchronized cell fibres of its selected parents.
No ambient parent cell outside the regularized envelope is reintroduced. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData.prepareSynchronizedBin
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    (parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope)
    (weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData)
    (weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass)
    (sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction)
    (sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow)
    (bin : {bin // bin ∈ sourceBins.line.globalBins})
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    Nonempty
      (PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
        weightRestriction sourceWindow sourceBins bin) := by
  let selection := Classical.choice
    (sourceBins.sourceParents bin).selectOnePerYFixedBin
  let residue := Classical.choice selection.selectResidueFixedBin
  rcases residue.retainSourceShadingFixedBin with
    ⟨retained, hretainedGraph⟩
  let coarseCarrier := Classical.choice residue.retainCoarseCarrierFixedBin
  let fineWitnesses := Classical.choice retained.fineWitnessesFixedBin
  let original := Classical.choice
    (coarseCarrier.withCoarseGlobalGrainsFixedBin
      fineWitnesses.coarseWitnesses hbridge)
  have hselectedParents :
      residue.selected ⊆ weightClass.selectedParents := by
    intro parent hparent
    have hsourceParent : parent ∈ (sourceBins.sourceParents bin).parents :=
      selection.selected_subset (residue.selected_subset hparent)
    exact
      PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData.sourceParents_subset_weightClass
        data outerPopular envelope parentData weightRestriction sourceWindow
          (sourceBins.sourceParents bin) hsourceParent
  let parentRestriction := Classical.choice
    (PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData.restrictParentSubfamily
      data outerPopular envelope parentData weightClass residue.selected
        residue.selected_nonempty hselectedParents)
  have hcellsActive : parentRestriction.cells ⊆
      wz1PaperActiveCells coarseCarrier.shading
        twoScale.coarseGrains.extremal.delta_pos := by
    intro cell hcell
    have hcellRestriction : cell ∈ parentRestriction.cells := hcell
    have hactiveRestriction : cell ∈
        wz1PaperActiveCells parentRestriction.cellRestriction.shading
          twoScale.coarseGrains.extremal.delta_pos := by
      rw [parentRestriction.cellRestriction.activeCells_eq]
      exact hcellRestriction
    rw [mem_wz1PaperActiveCells] at hactiveRestriction ⊢
    refine ⟨hactiveRestriction.1, ?_⟩
    let point := cellCorner rho cell
    have hpointCell : point ∈ wz1PaperGridCube rho cell :=
      cellCorner_mem_gridCube (by
        rw [← twoScale.rhoRequested_eq]
        exact twoScale.coarseGrains.extremal.delta_pos) cell
    have hcellUnion : point ∈
        parentRestriction.cellRestriction.shading.union := by
      rw [parentRestriction.cellRestriction.union_eq,
        wz2RetainedCellsUnion]
      exact Set.mem_iUnion₂.mpr ⟨cell, hcellRestriction, hpointCell⟩
    have henvelope : point ∈ envelope.shading.union :=
      parentRestriction.cellRestriction.subshading.union_subset hcellUnion
    have hcompanion : point ∈ data.shading.union :=
      envelope.subshading.union_subset henvelope
    have hfine : point ∈ twoScale.fine.refined.union := by
      rcases hcompanion with ⟨index, hindex⟩
      rw [data.carrier_eq index] at hindex
      have hzero : point ∈ data.zeroExtension.ambientShading.union :=
        ⟨index, hindex.1⟩
      rwa [data.zeroExtension.union_eq] at hzero
    have hcellUnion' : cell ∈ parentRestriction.cells := hcell
    rw [parentRestriction.cells_eq] at hcellUnion'
    rcases Finset.mem_biUnion.mp hcellUnion' with
      ⟨parent, hparent, hcellParent⟩
    have hpointParent : point ∈
        wz1PaperGridCube twoScale.sqrtRequested.1 parent := by
      rw [parentData.cellsForParent_eq] at hcellParent
      have hparentEq := (Finset.mem_filter.mp hcellParent).2
      rw [← hparentEq]
      exact parentData.cell_parent cell
        ((Finset.mem_filter.mp hcellParent).1) hpointCell
    have hcoarse : point ∈ coarseCarrier.shading.union := by
      rw [coarseCarrier.union_eq]
      refine ⟨hfine, ?_⟩
      rw [coarseCarrier.selectedRegion_eq]
      exact Set.mem_iUnion₂.mpr ⟨parent, hparent, hpointParent⟩
    exact ⟨point, hcoarse, by
      simpa only [twoScale.rhoRequested_eq] using hpointCell⟩
  let restrictedPreparation := Classical.choice
    (original.prepareCellRestrictionFixedBin parentRestriction.cells
      hcellsActive parentRestriction.cellRestriction.cells_nonempty
      hgraphOne hheightAbsorb)
  have hprepUnion : restrictedPreparation.prep.shadow.union =
      parentRestriction.cellRestriction.shading.union := by
    rw [restrictedPreparation.prep_shadow, restrictedPreparation.union_eq,
      parentRestriction.cellRestriction.union_eq]
  exact ⟨{
    selection := selection
    residue := residue
    retained := retained
    retained_graphShadow_union := hretainedGraph
    coarseCarrier := coarseCarrier
    fineWitnesses := fineWitnesses
    original := original
    parentRestriction := parentRestriction
    cells_active_in_carrier := hcellsActive
    restrictedPreparation := restrictedPreparation
    prep_union_eq := hprepUnion
  }⟩

/-- Every point supplied to the synchronized genuine-coarse graph remains
within the same outer-popular source-height envelope.  Both witnesses are
forced by the selected side-`rho` cell; no post-graph callback is used. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData.graph_point_near_height_region
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    {sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction}
    {sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow}
    {bin : {bin // bin ∈ sourceBins.line.globalBins}}
    (sync :
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
        weightRestriction sourceWindow sourceBins bin) :
    ∀ point ∈ sync.restrictedPreparation.prep.shadow.union,
      ∃ anchor ∈ outerPopular.popular.heightRegion,
        dist point anchor < 2 * rho + 2 * delta := by
  intro point hpoint
  rw [sync.prep_union_eq,
    sync.parentRestriction.cellRestriction.union_eq,
    wz2RetainedCellsUnion] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint with
    ⟨cell, hcell, hpointCell⟩
  have hcellEnvelope :=
    sync.parentRestriction.cellRestriction.cells_subset hcell
  rw [envelope.cells_eq] at hcellEnvelope
  rcases (Finset.mem_filter.mp hcellEnvelope).2 with
    ⟨sourcePoint, hsourceCell, hsourcePopular⟩
  rcases outerPopular.shading_point_near_height_region
      sourcePoint hsourcePopular with
    ⟨anchor, hanchor, hsourceNear⟩
  refine ⟨anchor, hanchor, ?_⟩
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hcellNear : dist point sourcePoint < 2 * rho :=
    wz1_paper_grid_cube_diameter_lt_two_rho
      hrho hpointCell hsourceCell
  exact (dist_triangle point sourcePoint anchor).trans_lt
    (add_lt_add hcellNear hsourceNear)

/-- The source exact-slice cells in one global bin are controlled by the
complete synchronized cell fibres chosen for that bin.  The common dyadic
`weightFloor` is what converts the unweighted source-parent count into the
literal side-`rho` cell weight without choosing one representative cell per
parent. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData.heavyCells_mul_weightFloor_le
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    {sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction}
    {sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow}
    {bin : {bin // bin ∈ sourceBins.line.globalBins}}
    (sync :
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
        weightRestriction sourceWindow sourceBins bin) :
    ((sourceBins.core bin).heavyCells.card : ENNReal) *
        weightClass.weightFloor ≤
      (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) * 23040 *
        (sync.parentRestriction.cells.card : ENNReal) := by
  have hheavyNat : (sourceBins.core bin).heavyCells.card ≤
      pureWZ2SourceFixedLineParentFiberBound delta rho * 23040 *
        sync.residue.selected.card := by
    calc
      (sourceBins.core bin).heavyCells.card ≤
          pureWZ2SourceFixedLineParentFiberBound delta rho *
            (sourceBins.sourceParents bin).parents.card :=
        (sourceBins.sourceParents bin).heavy_card
      _ ≤ pureWZ2SourceFixedLineParentFiberBound delta rho *
          (45 * sync.selection.selected.card) := by
        gcongr
        exact sync.selection.parent_card
      _ ≤ pureWZ2SourceFixedLineParentFiberBound delta rho *
          (45 * (512 * sync.residue.selected.card)) := by
        gcongr
        exact sync.residue.card_fraction
      _ = pureWZ2SourceFixedLineParentFiberBound delta rho * 23040 *
          sync.residue.selected.card := by ring
  have hheavy : ((sourceBins.core bin).heavyCells.card : ENNReal) ≤
      (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) * 23040 *
        (sync.residue.selected.card : ENNReal) := by
    exact_mod_cast hheavyNat
  calc
    ((sourceBins.core bin).heavyCells.card : ENNReal) *
          weightClass.weightFloor ≤
        ((pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) *
          23040 * (sync.residue.selected.card : ENNReal)) *
            weightClass.weightFloor := by gcongr
    _ = (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) *
          23040 *
          ((sync.residue.selected.card : ENNReal) *
            weightClass.weightFloor) := by ring
    _ ≤ (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) *
          23040 * (sync.parentRestriction.cells.card : ENNReal) := by
      gcongr
      exact sync.parentRestriction.weight_lower

/-- Every synchronized source bin contains at least half of one physical
side-`rho` cube.  This follows from a nonempty selected-parent family and the
common dyadic weight floor; it does not choose a representative cell. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData.cube_volume_le_two_mul_volume
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    {sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction}
    {sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow}
    {bin : {bin // bin ∈ sourceBins.line.globalBins}}
    (sync :
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
        weightRestriction sourceWindow sourceBins bin) :
    volume (wz1PaperGridCube rho (0, 0, 0)) ≤
      2 * volume sync.parentRestriction.cellRestriction.shading.union := by
  have hcellCard : (1 : ENNReal) ≤
      (sync.parentRestriction.cells.card : ENNReal) := by
    exact_mod_cast
      sync.parentRestriction.cellRestriction.cells_nonempty.card_pos
  have honeCells : (1 : ENNReal) ≤
      2 * (sync.parentRestriction.cells.card : ENNReal) := by
    calc
      (1 : ENNReal) ≤ (sync.parentRestriction.cells.card : ENNReal) := hcellCard
      _ ≤ 2 * (sync.parentRestriction.cells.card : ENNReal) := by
        exact le_mul_of_one_le_left' (by norm_num)
  calc
    volume (wz1PaperGridCube rho (0, 0, 0)) =
        1 * volume (wz1PaperGridCube rho (0, 0, 0)) := by rw [one_mul]
    _ ≤ (2 * (sync.parentRestriction.cells.card : ENNReal)) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by gcongr
    _ = 2 * volume sync.parentRestriction.cellRestriction.shading.union := by
      rw [sync.parentRestriction.cellRestriction.volume_eq]
      ring

/-- A source-independent upper bound for the nested global-bin count, together
with one scalar cube budget, implies the pointwise budget required by the
nested good-bin selector. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData.nested_graph_budget_of_cost
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    {sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction}
    {sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow}
    {bin : {bin // bin ∈ sourceBins.line.globalBins}}
    (sync :
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
        weightRestriction sourceWindow sourceBins bin)
    (nested :
      PureWZ2BalancedSafeOuterPopularCoarseNestedGlobalBinFamilyData sync)
    (nestedBinCost : ENNReal)
    (hcount : (nested.fixedLine.line.globalBins.card : ENNReal) ≤
      nestedBinCost)
    {volumeLoss : ℝ}
    (hbudget :
      4 * (nestedBinCost *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss)) *
          pureWZ2BalancedSafeNestedCoarseVolumeCost rho ≤
        volume (wz1PaperGridCube rho (0, 0, 0))) :
    2 * ((nested.fixedLine.line.globalBins.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss)) *
        pureWZ2BalancedSafeNestedCoarseVolumeCost rho ≤
      volume sync.parentRestriction.cellRestriction.shading.union := by
  have hfour :
      4 * (((nested.fixedLine.line.globalBins.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss)) *
          pureWZ2BalancedSafeNestedCoarseVolumeCost rho) ≤
        2 * volume sync.parentRestriction.cellRestriction.shading.union := by
    calc
      _ ≤ 4 * (nestedBinCost *
            Kakeya.realRpowENN (256 * rho)
              (1 + sigma / 2 + volumeLoss)) *
            pureWZ2BalancedSafeNestedCoarseVolumeCost rho := by
        have h := mul_le_mul_left'
          (mul_le_mul_right'
            (mul_le_mul_right' hcount
              (Kakeya.realRpowENN (256 * rho)
                (1 + sigma / 2 + volumeLoss)))
            (pureWZ2BalancedSafeNestedCoarseVolumeCost rho)) 4
        simpa only [mul_assoc] using h
      _ ≤ volume (wz1PaperGridCube rho (0, 0, 0)) := hbudget
      _ ≤ 2 * volume sync.parentRestriction.cellRestriction.shading.union :=
        PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData.cube_volume_le_two_mul_volume
          sync
  apply (ENNReal.mul_le_mul_iff_left
    (show (2 : ENNReal) ≠ 0 by norm_num)
    (show (2 : ENNReal) ≠ ⊤ by norm_num)).mp
  convert hfour using 1 <;> ring

/-- Summing the preceding estimate over all source global bins preserves the
exact Fubini partition and bounds the whole source slice by the total number
of literal cells entering the synchronized graph preparations. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData.sliceCells_mul_weightFloor_le_sum
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    {sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction}
    (sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow)
    (sync : ∀ bin : {bin // bin ∈ sourceBins.line.globalBins},
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
        weightRestriction sourceWindow sourceBins bin) :
    (sourceBins.line.sliceCells.card : ENNReal) * weightClass.weightFloor ≤
      (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) * 23040 *
        ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
          ((sync bin).parentRestriction.cells.card : ENNReal) := by
  rw [show (sourceBins.line.sliceCells.card : ENNReal) =
      ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
        ((sourceBins.core bin).heavyCells.card : ENNReal) by
    exact_mod_cast sourceBins.slice_card]
  rw [Finset.sum_mul]
  calc
    (∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
        ((sourceBins.core bin).heavyCells.card : ENNReal) *
          weightClass.weightFloor) ≤
      ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
        (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) *
          23040 * ((sync bin).parentRestriction.cells.card : ENNReal) := by
      exact Finset.sum_le_sum fun bin _ =>
        PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData.heavyCells_mul_weightFloor_le
          (sync bin)
    _ = (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) * 23040 *
        ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
          ((sync bin).parentRestriction.cells.card : ENNReal) := by
      rw [Finset.mul_sum]

/-- Source-side Fubini, all global bins, and complete regularized parent
fibres combine before any graph-good selection.  Dividing by the common
physical side-`rho` cube is exact; the dyadic parent weight remains visible
for the next cancellation step. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData.source_volume_mul_weightFloor_le
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    {sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction}
    (sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow)
    (sync : ∀ bin : {bin // bin ∈ sourceBins.line.globalBins},
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
        weightRestriction sourceWindow sourceBins bin) :
    volume sourceWindow.window.shading.union * weightClass.weightFloor ≤
      pureWZ2BalancedSafeSourceBinVolumeCost rho delta *
        ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
          volume (sync bin).parentRestriction.cellRestriction.shading.union := by
  let sliceThickness : ENNReal :=
    ENNReal.ofReal (Real.sqrt rho + 2 * rho)
  let sliceDisk : ENNReal :=
    ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi
  let cubeVolume : ENNReal :=
    volume (wz1PaperGridCube rho (0, 0, 0))
  have hsliceThicknessPos : 0 < sliceThickness := by
    apply ENNReal.ofReal_pos.mpr
    have hrho : 0 < rho := sourceBins.line.rho_pos
    positivity
  have hwindowToSlice :
      volume sourceWindow.window.shading.union ≤
        volume (wz1Lemma23PlanarSlice sourceWindow.window.shading.union
          sourceBins.line.lineHeight) * sliceThickness := by
    apply (ENNReal.div_le_iff hsliceThicknessPos.ne'
      ENNReal.ofReal_ne_top).mp
    simpa only [sliceThickness] using sourceBins.line.slice_area_lower
  have hball : sourceWindow.window.shading.union ⊆
      Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hprepared : point ∈ prepared.shadow.union :=
      sourceWindow.window.subshading.union_subset hpoint
    have hpullback : point ∈ pullback.shading.union := by
      rwa [prepared.shadow_union] at hprepared
    have hsource := pullback.subshading.union_subset hpullback
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hsliceArea :
      volume (wz1Lemma23PlanarSlice sourceWindow.window.shading.union
          sourceBins.line.lineHeight) ≤
        (sourceBins.line.sliceCells.card : ENNReal) * sliceDisk := by
    have hraw := wz1_lemma23_exactSlice_area_le_two
      sourceWindow.window.shading source.extremal.delta_pos hball
      sourceBins.line.lineHeight
    simpa [sourceBins.line.sliceCells_eq, sliceDisk] using hraw
  have hcount :=
    PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData.sliceCells_mul_weightFloor_le_sum
      sourceBins sync
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hcubePos : 0 < cubeVolume := by
    dsimp only [cubeVolume]
    rw [wz1PaperGridCube_volume_exact hrho]
    exact ENNReal.ofReal_pos.mpr (pow_pos hrho 3)
  have hcubeTop : cubeVolume ≠ ⊤ := by
    dsimp only [cubeVolume]
    rw [wz1PaperGridCube_volume_exact hrho]
    exact ENNReal.ofReal_ne_top
  have hcellVolumes :
      (∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
          ((sync bin).parentRestriction.cells.card : ENNReal)) * cubeVolume =
        ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
          volume (sync bin).parentRestriction.cellRestriction.shading.union := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro bin _
    rw [(sync bin).parentRestriction.cellRestriction.volume_eq]
  have hraw :
      (volume sourceWindow.window.shading.union * weightClass.weightFloor) *
          cubeVolume ≤
        pureWZ2BalancedSafeSourceBinRawVolumeCost rho delta *
          (∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
            volume (sync bin).parentRestriction.cellRestriction.shading.union) := by
    calc
      (volume sourceWindow.window.shading.union * weightClass.weightFloor) *
            cubeVolume ≤
          ((volume (wz1Lemma23PlanarSlice sourceWindow.window.shading.union
              sourceBins.line.lineHeight) * sliceThickness) *
            weightClass.weightFloor) * cubeVolume := by gcongr
      _ ≤ ((((sourceBins.line.sliceCells.card : ENNReal) * sliceDisk) *
            sliceThickness) * weightClass.weightFloor) * cubeVolume := by gcongr
      _ = sliceThickness * sliceDisk *
          ((sourceBins.line.sliceCells.card : ENNReal) *
            weightClass.weightFloor) * cubeVolume := by ring
      _ ≤ sliceThickness * sliceDisk *
          ((pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) *
            23040 * ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
              ((sync bin).parentRestriction.cells.card : ENNReal)) *
            cubeVolume := by gcongr
      _ = pureWZ2BalancedSafeSourceBinRawVolumeCost rho delta *
          (∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
            volume (sync bin).parentRestriction.cellRestriction.shading.union) := by
        rw [← hcellVolumes]
        simp only [pureWZ2BalancedSafeSourceBinRawVolumeCost,
          sliceThickness, sliceDisk]
        ring
  have hcostCube :
      pureWZ2BalancedSafeSourceBinVolumeCost rho delta * cubeVolume =
        pureWZ2BalancedSafeSourceBinRawVolumeCost rho delta := by
    unfold pureWZ2BalancedSafeSourceBinVolumeCost
    rw [div_eq_mul_inv]
    exact ENNReal.inv_mul_cancel_right hcubePos.ne' hcubeTop
  have hscaled :
      (volume sourceWindow.window.shading.union * weightClass.weightFloor) *
        cubeVolume ≤
      pureWZ2BalancedSafeSourceBinRawVolumeCost rho delta *
        ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
          volume (sync bin).parentRestriction.cellRestriction.shading.union := hraw
  have hscaled' :
      (volume sourceWindow.window.shading.union * weightClass.weightFloor) *
        cubeVolume ≤
      (pureWZ2BalancedSafeSourceBinVolumeCost rho delta *
        ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
          volume (sync bin).parentRestriction.cellRestriction.shading.union) *
        cubeVolume := by
    calc
      _ ≤ pureWZ2BalancedSafeSourceBinRawVolumeCost rho delta *
          ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
            volume (sync bin).parentRestriction.cellRestriction.shading.union :=
        hscaled
      _ = (pureWZ2BalancedSafeSourceBinVolumeCost rho delta *
          ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
            volume (sync bin).parentRestriction.cellRestriction.shading.union) *
          cubeVolume := by
        calc
          _ = (pureWZ2BalancedSafeSourceBinVolumeCost rho delta * cubeVolume) *
              ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
                volume (sync bin).parentRestriction.cellRestriction.shading.union := by
            rw [hcostCube]
          _ = _ := by ring
  exact (ENNReal.mul_le_mul_iff_left
    (a := volume sourceWindow.window.shading.union * weightClass.weightFloor)
    (b := pureWZ2BalancedSafeSourceBinVolumeCost rho delta *
      ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
        volume (sync bin).parentRestriction.cellRestriction.shading.union)
    (c := cubeVolume) hcubePos.ne' hcubeTop).mp hscaled'

/-- The dyadic fibre floor is a bookkeeping device, not a geometric loss:
every selected parent contains at least one literal cell, so paying one
absolute factor of two removes it from the source-volume estimate. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData.source_volume_le_sum
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    {sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction}
    (sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow)
    (sync : ∀ bin : {bin // bin ∈ sourceBins.line.globalBins},
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
        weightRestriction sourceWindow sourceBins bin) :
    volume sourceWindow.window.shading.union ≤
      2 * pureWZ2BalancedSafeSourceBinVolumeCost rho delta *
        ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
          volume (sync bin).parentRestriction.cellRestriction.shading.union := by
  have hweighted :=
    PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData.source_volume_mul_weightFloor_le
      sourceBins sync
  calc
    volume sourceWindow.window.shading.union =
        volume sourceWindow.window.shading.union * 1 := by rw [mul_one]
    _ ≤ volume sourceWindow.window.shading.union *
        (2 * weightClass.weightFloor) := by
      gcongr
      exact weightClass.one_le_two_mul_weightFloor
    _ = 2 * (volume sourceWindow.window.shading.union *
        weightClass.weightFloor) := by ring
    _ ≤ 2 * (pureWZ2BalancedSafeSourceBinVolumeCost rho delta *
        ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
          volume (sync bin).parentRestriction.cellRestriction.shading.union) := by
      gcongr
    _ = _ := by ring

/-- The source window produced after outer popularity and parent-weight
regularization still carries a fixed inverse share of its regularized source
block.  Both the first-cover `cellMass` and multiplicity are cancelled only
after using their exact balanced identities. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData.block_volume_le_sourceWindow
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    (sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction) :
    volume (safe.blockWindow block).shading.union ≤
      2 * (2 * outerPopular.popular.bins : ENNReal) *
        (weightClass.bins : ENNReal) *
        volume sourceWindow.window.shading.union := by
  let cellMass : ENNReal := twoScale.coarse.balanced.cellMass
  have hcellPos : 0 < cellMass := twoScale.coarse.balanced.cellMass_pos
  have hcellTop : cellMass ≠ ⊤ := twoScale.coarse.balanced.cellMass_ne_top
  have hcount : (envelope.cells.card : ENNReal) ≤
      2 * (weightClass.bins : ENNReal) *
        (weightRestriction.cells.card : ENNReal) := by
    rw [weightRestriction.cells_card_eq]
    have hcast :
        ((↑(∑ parent ∈ weightClass.selectedParents,
            (parentData.cellsForParent parent).card) : ENNReal)) =
          ∑ parent ∈ weightClass.selectedParents,
            ((parentData.cellsForParent parent).card : ENNReal) := by
      norm_cast
    rw [hcast]
    exact weightClass.retained_weight
  have henvelopeVolume : volume envelope.sourcePullback.shading.union ≤
      2 * (weightClass.bins : ENNReal) *
        volume weightRestriction.restriction.sourcePullback.shading.union := by
    rw [envelope.sourcePullback.volume_eq,
      envelope.sourcePullback_selectedCells,
      weightRestriction.restriction.sourcePullback.volume_eq,
      weightRestriction.restriction.sourcePullback_selectedCells]
    have h := mul_le_mul_right' hcount cellMass
    simpa only [mul_assoc] using h
  have hpopularVolume : volume outerPopular.shading.union ≤
      2 * (weightClass.bins : ENNReal) *
        volume sourceWindow.window.shading.union := by
    calc
      volume outerPopular.shading.union =
          volume (data.outerPopularEnvelopeSourcePullback outerPopular).union := by
        rw [data.outerPopularEnvelopeSourcePullback_union_eq outerPopular]
      _ ≤ volume envelope.sourcePullback.shading.union :=
        measure_mono envelope.sourceEnvelopePullback_sub_sourcePullback.union_subset
      _ ≤ 2 * (weightClass.bins : ENNReal) *
          volume weightRestriction.restriction.sourcePullback.shading.union :=
        henvelopeVolume
      _ = 2 * (weightClass.bins : ENNReal) *
          volume sourceWindow.window.shading.union := by
        rw [sourceWindow.window_shading, sourceWindow.union_eq]
  calc
    volume (safe.blockWindow block).shading.union =
        volume (safe.blockWindow block).window.shading.union := by
      rw [(safe.blockWindow block).window_shading]
    _ ≤ (2 * outerPopular.popular.bins : ENNReal) *
        outerPopular.windowed.volumeSupply := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        outerPopular.source_volume_retention_windowed
    _ = (2 * outerPopular.popular.bins : ENNReal) *
        volume outerPopular.shading.union := by
      rw [outerPopular.windowed_supply]
    _ ≤ (2 * outerPopular.popular.bins : ENNReal) *
        (2 * (weightClass.bins : ENNReal) *
          volume sourceWindow.window.shading.union) := by gcongr
    _ = _ := by ring

/-- Sum the nested rich-height estimates over all source global bins.  The
first-cover cell mass remains explicit: it is exactly the density conversion
between the source pullback's spatial volume and indexed mass, and is not
replaced by a scale power at this geometric stage. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseNestedBlockRichFamilyData.sourcePullback_mass_bound
    {normalEta finalLoss theoremEta volumeLoss extraLoss : ℝ}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    {sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction}
    {sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow}
    (family :
      PureWZ2BalancedSafeOuterPopularCoarseNestedBlockRichFamilyData
        (normalEta := normalEta) (finalLoss := finalLoss)
        (theoremEta := theoremEta) (volumeLoss := volumeLoss)
        weightRestriction sourceWindow sourceBins)
    (hextraPower : ∀ bin : {bin // bin ∈ sourceBins.line.globalBins},
      ∀ nestedBin : {nestedBin // nestedBin ∈ (family.good bin).selected},
        (((family.rich bin).pipeline nestedBin).preparedGraph.graph.residue.extraCost :
            ℝ) ≤
          Real.rpow
            ((family.nested bin).preparation nestedBin.1).prep.graphScale
            (-extraLoss)) :
    weightRestriction.restriction.sourcePullback.shading.mass *
          twoScale.coarse.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
      4 * pureWZ2BalancedSafeSourceBinVolumeCost rho delta *
        pureWZ2BalancedSafeNestedCoarseRawVolumeCost rho *
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss *
        ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
          ∑ nestedBin : {nestedBin //
              nestedBin ∈ (family.good bin).selected},
            ((family.rich bin).rich nestedBin).heightLift.shading.mass := by
  let floor : ENNReal :=
    pureWZ2SourceHorizontalRichFloor rho finalLoss
  let incidenceMass : ENNReal :=
    twoScale.coarse.balanced.incidenceMass
  let sourceCost : ENNReal :=
    pureWZ2BalancedSafeSourceBinVolumeCost rho delta
  let nestedCost : ENNReal :=
    pureWZ2BalancedSafeNestedCoarseRawVolumeCost rho
  let heightCost : ENNReal :=
    PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
      rho extraLoss
  have hsource :=
    PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData.source_volume_le_sum
      sourceBins family.sync
  have hlocal :
      (∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
          volume (family.sync bin).parentRestriction.cellRestriction.shading.union) *
            floor * incidenceMass ≤
        2 * nestedCost * heightCost *
          ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
            ∑ nestedBin : {nestedBin //
                nestedBin ∈ (family.good bin).selected},
              ((family.rich bin).rich nestedBin).heightLift.shading.mass := by
    calc
      _ = ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
          (volume (family.sync bin).parentRestriction.cellRestriction.shading.union *
            floor * incidenceMass) := by
        rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
          (2 * nestedCost * heightCost *
            ∑ nestedBin : {nestedBin //
                nestedBin ∈ (family.good bin).selected},
              ((family.rich bin).rich nestedBin).heightLift.shading.mass) := by
        exact Finset.sum_le_sum fun bin _ => by
          simpa [floor, incidenceMass, nestedCost, heightCost] using
            PureWZ2BalancedSafeOuterPopularCoarseNestedRichFamilyData.aggregate_heightLift_mass_bound
              (family.rich bin) (hextraPower bin)
      _ = 2 * nestedCost * heightCost *
          ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
            ∑ nestedBin : {nestedBin //
                nestedBin ∈ (family.good bin).selected},
              ((family.rich bin).rich nestedBin).heightLift.shading.mass := by
        rw [Finset.mul_sum]
  calc
    weightRestriction.restriction.sourcePullback.shading.mass *
          twoScale.coarse.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss =
        volume sourceWindow.window.shading.union * floor * incidenceMass := by
      rw [PureWZ2SelectedCoarseRegionSourcePullbackData.mass_mul_cellMass,
        sourceWindow.window_shading, sourceWindow.union_eq]
      ring
    _ ≤ (2 * sourceCost *
          ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
            volume (family.sync bin).parentRestriction.cellRestriction.shading.union) *
          floor * incidenceMass := by
      exact mul_le_mul_right' (mul_le_mul_right' (by
        simpa [sourceCost] using hsource) floor) incidenceMass
    _ = 2 * sourceCost *
        ((∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
          volume (family.sync bin).parentRestriction.cellRestriction.shading.union) *
            floor * incidenceMass) := by ring
    _ ≤ 2 * sourceCost *
        (2 * nestedCost * heightCost *
          ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
            ∑ nestedBin : {nestedBin //
                nestedBin ∈ (family.good bin).selected},
              ((family.rich bin).rich nestedBin).heightLift.shading.mass) := by
      gcongr
    _ = _ := by
      simp only [sourceCost, nestedCost, heightCost, floor, incidenceMass]
      ring

/-- Block-level endpoint of the synchronized nested construction.  It pays
outer source-height popularity and parent-weight regularization exactly once,
then feeds the resulting source pullback into the all-bin/nested rich ledger. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseNestedBlockRichFamilyData.block_source_mass_bound
    {normalEta finalLoss theoremEta volumeLoss extraLoss : ℝ}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    {sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction}
    {sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow}
    (family :
      PureWZ2BalancedSafeOuterPopularCoarseNestedBlockRichFamilyData
        (normalEta := normalEta) (finalLoss := finalLoss)
        (theoremEta := theoremEta) (volumeLoss := volumeLoss)
        weightRestriction sourceWindow sourceBins)
    (hextraPower : ∀ bin : {bin // bin ∈ sourceBins.line.globalBins},
      ∀ nestedBin : {nestedBin // nestedBin ∈ (family.good bin).selected},
        (((family.rich bin).pipeline nestedBin).preparedGraph.graph.residue.extraCost :
            ℝ) ≤
          Real.rpow
            ((family.nested bin).preparation nestedBin.1).prep.graphScale
            (-extraLoss)) :
    data.sourcePullback.shading.mass *
          twoScale.coarse.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
      16 * (2 * outerPopular.popular.bins : ENNReal) *
        (weightClass.bins : ENNReal) *
        pureWZ2BalancedSafeSourceBinVolumeCost rho delta *
        pureWZ2BalancedSafeNestedCoarseRawVolumeCost rho *
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss *
        ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
          ∑ nestedBin : {nestedBin //
              nestedBin ∈ (family.good bin).selected},
            ((family.rich bin).rich nestedBin).heightLift.shading.mass := by
  have hretained : data.sourcePullback.shading.mass ≤
      4 * (2 * outerPopular.popular.bins : ENNReal) *
        (weightClass.bins : ENNReal) *
        weightRestriction.restriction.sourcePullback.shading.mass := by
    calc
      data.sourcePullback.shading.mass ≤
          2 * (2 * outerPopular.popular.bins : ENNReal) *
            envelope.sourcePullback.shading.mass :=
        PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData.block_source_mass_le
          data outerPopular envelope
      _ ≤ 2 * (2 * outerPopular.popular.bins : ENNReal) *
          (2 * (weightClass.bins : ENNReal) *
            weightRestriction.restriction.sourcePullback.shading.mass) := by
        gcongr
        exact weightRestriction.retained_mass
      _ = 4 * (2 * outerPopular.popular.bins : ENNReal) *
          (weightClass.bins : ENNReal) *
          weightRestriction.restriction.sourcePullback.shading.mass := by ring
  calc
    data.sourcePullback.shading.mass *
          twoScale.coarse.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
        (4 * (2 * outerPopular.popular.bins : ENNReal) *
          (weightClass.bins : ENNReal) *
          weightRestriction.restriction.sourcePullback.shading.mass) *
          twoScale.coarse.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss := by
      exact mul_le_mul_right'
        (mul_le_mul_right' hretained
          twoScale.coarse.balanced.cellMass)
        (pureWZ2SourceHorizontalRichFloor rho finalLoss)
    _ = 4 * (2 * outerPopular.popular.bins : ENNReal) *
        (weightClass.bins : ENNReal) *
        (weightRestriction.restriction.sourcePullback.shading.mass *
          twoScale.coarse.balanced.cellMass *
          pureWZ2SourceHorizontalRichFloor rho finalLoss) := by ring
    _ ≤ 4 * (2 * outerPopular.popular.bins : ENNReal) *
        (weightClass.bins : ENNReal) *
        (4 * pureWZ2BalancedSafeSourceBinVolumeCost rho delta *
          pureWZ2BalancedSafeNestedCoarseRawVolumeCost rho *
          PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
            rho extraLoss *
          ∑ bin : {bin // bin ∈ sourceBins.line.globalBins},
            ∑ nestedBin : {nestedBin //
                nestedBin ∈ (family.good bin).selected},
              ((family.rich bin).rich nestedBin).heightLift.shading.mass) := by
      exact mul_le_mul_left'
        (PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseNestedBlockRichFamilyData.sourcePullback_mass_bound
          family hextraPower)
        (4 * (2 * outerPopular.popular.bins : ENNReal) *
          (weightClass.bins : ENNReal))
    _ = _ := by ring

/-- Run the graph-good prefix on the exact synchronized cell restriction
stored by `prepareSynchronizedBin`. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData.toGraphPipeline
    {normalEta : ℝ}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    {sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction}
    {sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow}
    {bin : {bin // bin ∈ sourceBins.line.globalBins}}
    (sync :
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
        weightRestriction sourceWindow sourceBins bin)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hnormalEta : 0 < normalEta)
    (hnormalEtaSigma : 4 * normalEta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + normalEta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * outputLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) normalEta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (hlocalizationAbsorb :
      Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) ≤
        Real.sqrt (4 * rho) / 14)
    (hlocalConstant :
      35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) ≤
        19 * (10 * Kakeya.realRpowENN rho (-middleLoss)))
    (hvolumePos : 0 < MeasureTheory.volume
      sync.restrictedPreparation.prep.shadow.union) :
    Nonempty
      (PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinGraphData
        (normalEta := normalEta) sync) := by
  rcases PureWZ2SourceFixedBinCoarsePreparationData.coarseGraphPipelineAtPreparationFixedBin
        sync.restrictedPreparation.prep hbridge hsigma hsigmaOne hnormalEta
        hnormalEtaSigma hcertificateOne hsourceFloor hlocalPower hglobalPower
        hPlanarSmall hrootSmall20 hlocalizationAbsorb hlocalConstant hvolumePos with
    ⟨pipeline⟩
  exact ⟨{
    pipeline := pipeline
    graph_input_union := sync.prep_union_eq
  }⟩

/-- Continue the synchronized graph through Alternative A, internal height
popularity, `Z_lin`, whole-cell saturation, and the exact first-cover
pullback.  The final cell set is proved to be a literal subset of the
complete parent fibres fixed before graph preparation. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinGraphData.toRichSaturation
    {normalEta finalLoss theoremEta volumeLoss constantLoss extraLoss : ℝ}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    {sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction}
    {sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow}
    {bin : {bin // bin ∈ sourceBins.line.globalBins}}
    {sync :
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
        weightRestriction sourceWindow sourceBins bin}
    (graph : PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinGraphData
      (normalEta := normalEta) sync)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCOne : (1 : ENNReal) ≤
      10 * Kakeya.realRpowENN rho (-middleLoss))
    (hCpower :
      (10 * Kakeya.realRpowENN rho (-middleLoss)).toReal ≤
        Real.rpow sync.restrictedPreparation.prep.graphScale (-constantLoss))
    (hvolume : Kakeya.realRpowENN
        sync.restrictedPreparation.prep.graphScale
          (1 + sigma / 2 + volumeLoss) ≤
      MeasureTheory.volume sync.restrictedPreparation.prep.shadow.union)
    (hextraPower :
      (graph.pipeline.preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow sync.restrictedPreparation.prep.graphScale (-extraLoss))
    (hedgeAbsorb :
      Real.rpow (wz1Lemma23Theorem22Scale
          sync.restrictedPreparation.prep.graphScale) (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow sync.restrictedPreparation.prep.graphScale
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss +
              4 * extraLoss))
    (hKatzTao : (4 : ENNReal) ≤
      Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale
          sync.restrictedPreparation.prep.graphScale) (-theoremEta))
    (hprojection : ∀ ready : PureWZ2SourceFixedBinCoarseReadyGraph
        (theoremEta := theoremEta) graph.pipeline.sharp,
      WZ1Proposition8_9AlternativeAUnion
        ready.ready.deltaGraph finalLoss
        ready.common.F ready.common.G₁ ready.common.G₁)
    (hscaleOne :
      5 * sync.restrictedPreparation.prep.graphScale ≤ 1)
    (hlengthLower :
      Real.rpow (5 * sync.restrictedPreparation.prep.graphScale)
          (1 / 2 + finalLoss) ≤
        twoScale.sqrtRequested.1) :
    Nonempty
      (PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinRichData
        (finalLoss := finalLoss) (theoremEta := theoremEta) graph) := by
  rcases graph.pipeline.toRichPipelineAtPreparationFixedBin
      hsigma hsigmaOne hCOne hCpower hvolume hextraPower hedgeAbsorb
      hKatzTao hprojection hscaleOne hlengthLower with ⟨richOutput⟩
  rcases richOutput.toRichHeightSaturation with ⟨saturation⟩
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hcellsSubset : saturation.cells ⊆
      sync.parentRestriction.cells := by
    intro cell hcell
    rcases saturation.cells_meet cell hcell with
      ⟨point, ⟨hpointRichSet, hpointCell⟩⟩
    rw [saturation.richSet_eq] at hpointRichSet
    have hpointRestriction : point ∈
        sync.parentRestriction.cellRestriction.shading.union := by
      rw [← sync.prep_union_eq]
      exact hpointRichSet.1
    rw [sync.parentRestriction.cellRestriction.union_eq,
      wz2RetainedCellsUnion] at hpointRestriction
    rcases Set.mem_iUnion₂.mp hpointRestriction with
      ⟨owner, howner, hpointOwner⟩
    have hownerEq : owner = cell :=
      ((mem_wz1PaperGridCube rho owner point).mp hpointOwner).symm.trans
        ((mem_wz1PaperGridCube rho cell point).mp hpointCell)
    rwa [hownerEq] at howner
  have hselectedCells : saturation.sourcePullback.selectedCells =
      saturation.cells := by
    rw [saturation.sourcePullback.selectedCells_eq]
    apply Finset.Subset.antisymm
    · intro cell hcell
      rw [mem_wz1PaperActiveCells] at hcell
      rcases hcell.2 with ⟨point, hpointShading, hpointCell⟩
      rw [saturation.union_eq, saturation.region_eq,
        wz2RetainedCellsUnion] at hpointShading
      rcases Set.mem_iUnion₂.mp hpointShading with
        ⟨owner, howner, hpointOwner⟩
      have hownerEq : owner = cell :=
        ((mem_wz1PaperGridCube twoScale.rhoRequested.1 owner point).mp
          hpointOwner).symm.trans
        ((mem_wz1PaperGridCube twoScale.rhoRequested.1 cell point).mp
          hpointCell)
      rwa [hownerEq] at howner
    · intro cell hcell
      rw [mem_wz1PaperActiveCells]
      have hactive := saturation.cells_subset hcell
      rw [mem_wz1PaperActiveCells] at hactive
      refine ⟨hactive.1, ?_⟩
      let point := cellCorner rho cell
      have hpointCell : point ∈ wz1PaperGridCube rho cell :=
        cellCorner_mem_gridCube hrho cell
      have hpointShading : point ∈ saturation.shading.union := by
        rw [saturation.union_eq, saturation.region_eq,
          wz2RetainedCellsUnion]
        exact Set.mem_iUnion₂.mpr ⟨cell, hcell, by
          simpa only [twoScale.rhoRequested_eq] using hpointCell⟩
      exact ⟨point, hpointShading, by
        simpa only [twoScale.rhoRequested_eq] using hpointCell⟩
  exact ⟨{
    richOutput := richOutput
    saturation := saturation
    saturation_cells_subset := hcellsSubset
    sourcePullback_selectedCells_eq := hselectedCells
    sourcePullback_selectedCells_subset := by
      rw [hselectedCells]
      exact hcellsSubset
  }⟩

/-- Every final Alternative-A height of the synchronized rich producer is
assigned to one of the three adjacent heights of the source-popular
envelope selected before graph construction. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinRichData.heightIndices_near_outerPopular
    {normalEta finalLoss theoremEta : ℝ}
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parentData : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    {weightClass :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
        data outerPopular envelope parentData}
    {weightRestriction :
      PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
        data outerPopular envelope parentData weightClass}
    {sourceWindow :
      PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
        weightRestriction.restriction}
    {sourceBins :
      PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
        (parentData := parentData) weightRestriction.restriction sourceWindow}
    {bin : {bin // bin ∈ sourceBins.line.globalBins}}
    {sync :
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData
        weightRestriction sourceWindow sourceBins bin}
    {graph :
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinGraphData
        (normalEta := normalEta) sync}
    (rich :
      PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinRichData
        (finalLoss := finalLoss) (theoremEta := theoremEta) graph) :
    ∀ heightIndex ∈ rich.richOutput.rich.heightIndices,
      ∃ popularHeight ∈ outerPopular.popular.heightIndices,
        |heightIndex - popularHeight| ≤ (1 : ℤ) :=
  rich.richOutput.rich.heightIndices_near_outerPopular
    (PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseSynchronizedBinPreparationData.graph_point_near_height_region
      sync)

/-- Select one fiber of any finite joint label on the envelope cells.  Since
every selected side-`rho` cell carries the same first-cover incidence mass,
the elementary weighted pigeonhole inequality converts without loss of
provenance to indexed source mass. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData.selectCellFiber
    {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    (color : (ℤ × ℤ × ℤ) → β) :
    Nonempty (PureWZ2BalancedSafeOuterPopularCoarseCellFiberData
      data outerPopular envelope color) := by
  let weight : (ℤ × ℤ × ℤ) → ENNReal := fun _ =>
    twoScale.coarse.balanced.incidenceMass
  rcases finset_ennreal_weighted_fiber_retention
      envelope.cells weight color with ⟨target, hretained⟩
  let cells := envelope.cells.filter fun cell => color cell = target
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  let shading : WZ1PaperTubeShading twoScale.coarse.coarse :=
    wz2RefinedShading envelope.shading cells
  have hcellsEnvelope : cells ⊆ envelope.cells := Finset.filter_subset _ _
  have hcellsActive : cells ⊆ wz1PaperActiveCells envelope.shading
      twoScale.coarseGrains.extremal.delta_pos := by
    intro cell hcell
    rw [mem_wz1PaperActiveCells]
    have hcellEnvelope := hcellsEnvelope hcell
    have hcellBase : cell ∈
        wz1PaperGridIndicesInWindow
          twoScale.rhoRequested.1
          twoScale.coarseGrains.extremal.delta_pos := by
      rw [envelope.cells_eq] at hcellEnvelope
      have hblockCell := (Finset.mem_filter.mp hcellEnvelope).1
      rw [(safe.blockWindow block).cells_eq,
        pureWZ2BalancedSafeWindowCells] at hblockCell
      have hpullback := (Finset.mem_filter.mp hblockCell).1
      rw [pullback.selectedCells_eq] at hpullback
      exact (mem_wz1PaperActiveCells twoScale.fine.refined
        twoScale.coarseGrains.extremal.delta_pos cell).mp hpullback |>.1
    have hintersection :
        (envelope.shading.union ∩
          wz1PaperGridCube twoScale.rhoRequested.1 cell).Nonempty := by
      let point := cellCorner rho cell
      have hpointCell : point ∈ wz1PaperGridCube rho cell :=
        cellCorner_mem_gridCube hrho cell
      have hpointEnvelope : point ∈ envelope.shading.union := by
        rw [envelope.union_eq, wz2RetainedCellsUnion]
        exact Set.mem_iUnion₂.mpr ⟨cell, hcellEnvelope, hpointCell⟩
      exact ⟨point, hpointEnvelope, by
        simpa only [twoScale.rhoRequested_eq] using hpointCell⟩
    exact ⟨hcellBase, hintersection⟩
  have hsub : PureWZ2PaperIsSubshading shading envelope.shading :=
    wz2RefinedShading_subshading
  have hwhole : WZ1PaperIsCubicalShading shading :=
    wz2RefinedShading_cubical envelope.whole_cells
  have hunion : shading.union = wz2RetainedCellsUnion rho cells := by
    have hraw := wz2RefinedShading_union_eq envelope.whole_cells
      twoScale.coarseGrains.extremal.delta_pos hcellsActive
    simpa only [twoScale.rhoRequested_eq] using hraw
  have hselectedMassPos : 0 <
      ∑ cell ∈ cells, weight cell := by
    have hsourceMassPos : 0 < envelope.sourcePullback.shading.mass := by
      rw [envelope.sourcePullback.mass_eq,
        envelope.sourcePullback_selectedCells]
      exact ENNReal.mul_pos
        (by
          exact_mod_cast envelope.cells_nonempty.card_ne_zero)
        twoScale.coarse.balanced.incidenceMass_pos.ne'
    have htotalPos : 0 < ∑ cell ∈ envelope.cells, weight cell := by
      simpa [weight, Finset.sum_const,
        envelope.sourcePullback.mass_eq,
        envelope.sourcePullback_selectedCells] using hsourceMassPos
    by_contra hnot
    have hzero : (∑ cell ∈ cells, weight cell) = 0 :=
      not_lt.mp hnot |> nonpos_iff_eq_zero.mp
    have hleZero := hretained
    rw [show envelope.cells.filter (fun cell => color cell = target) = cells
        by rfl, hzero, mul_zero] at hleZero
    exact (not_le_of_gt htotalPos) hleZero
  have hcellsNonempty : cells.Nonempty := by
    by_contra hempty
    have hcellsEmpty : cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    rw [hcellsEmpty] at hselectedMassPos
    simpa using hselectedMassPos
  have hactiveCells :
      wz1PaperActiveCells shading
          twoScale.coarseGrains.extremal.delta_pos = cells := by
    apply Finset.Subset.antisymm
    · intro cell hcell
      rw [mem_wz1PaperActiveCells] at hcell
      rcases hcell.2 with ⟨point, hpointShading, hpointCell⟩
      rw [hunion, wz2RetainedCellsUnion] at hpointShading
      rcases Set.mem_iUnion₂.mp hpointShading with
        ⟨owner, howner, hpointOwner⟩
      have hpointCellRho : point ∈ wz1PaperGridCube rho cell := by
        simpa only [twoScale.rhoRequested_eq] using hpointCell
      have hownerEq : owner = cell :=
        ((mem_wz1PaperGridCube rho owner point).mp hpointOwner).symm.trans
          ((mem_wz1PaperGridCube rho cell point).mp hpointCellRho)
      rwa [hownerEq] at howner
    · intro cell hcell
      rw [mem_wz1PaperActiveCells]
      have hactiveEnvelope := hcellsActive hcell
      rw [mem_wz1PaperActiveCells] at hactiveEnvelope
      refine ⟨hactiveEnvelope.1, ?_⟩
      let point := cellCorner rho cell
      have hpointCell : point ∈ wz1PaperGridCube rho cell :=
        cellCorner_mem_gridCube hrho cell
      have hpointShading : point ∈ shading.union := by
        rw [hunion, wz2RetainedCellsUnion]
        exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointCell⟩
      exact ⟨point, hpointShading, by
        simpa only [twoScale.rhoRequested_eq] using hpointCell⟩
  have hvolume : volume shading.union =
      (cells.card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
    rw [hunion]
    exact wz1PaperGridCube_volume_biUnion hrho cells
  have hsubCoarse : PureWZ2PaperIsSubshading
      shading twoScale.coarseGrains.shading := by
    intro index point hpoint
    exact data.subshading index (envelope.subshading index (hsub index hpoint))
  rcases pureWZ2_pullback_selected_coarse_region shading hsubCoarse hwhole with
    ⟨sourcePullback⟩
  have hselectedCells : sourcePullback.selectedCells = cells := by
    rw [sourcePullback.selectedCells_eq, hactiveCells]
  have hsourceMass : envelope.sourcePullback.shading.mass ≤
      (Fintype.card β : ENNReal) * sourcePullback.shading.mass := by
    rw [envelope.sourcePullback.mass_eq,
      envelope.sourcePullback_selectedCells, sourcePullback.mass_eq]
    rw [hselectedCells]
    simpa [weight, cells, Finset.sum_const] using hretained
  exact ⟨{
    target := target
    cells := cells
    cells_eq := rfl
    cells_nonempty := hcellsNonempty
    shading := shading
    shading_eq := rfl
    subshading := hsub
    whole_cells := hwhole
    union_eq := hunion
    activeCells_eq := hactiveCells
    volume_eq := hvolume
    sourcePullback := sourcePullback
    sourcePullback_selectedCells := hselectedCells
    sourcePullback_mass_eq := by
      rw [sourcePullback.mass_eq, hselectedCells]
    retained_mass := hsourceMass
  }⟩

/-- Select a finite parent label with the exact first-cover incidence weight
of all envelope cells in that parent fibre. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseParentData.selectParentFiber
    {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    (parents : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope)
    (color : (ℤ × ℤ × ℤ) → β) :
    Nonempty (PureWZ2BalancedSafeOuterPopularCoarseParentFiberData
      data outerPopular envelope parents color) := by
  let cellColor : (ℤ × ℤ × ℤ) → β := fun cell =>
    color (parents.parentCell cell)
  let fiber := Classical.choice
    (PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData.selectCellFiber
      data outerPopular envelope cellColor)
  let selectedParents := parents.parents.filter fun parent =>
    color parent = fiber.target
  have hselectedParentsNonempty : selectedParents.Nonempty := by
    rcases fiber.cells_nonempty with ⟨cell, hcell⟩
    have hcellEnvelope : cell ∈ envelope.cells := by
      rw [fiber.cells_eq] at hcell
      exact (Finset.mem_filter.mp hcell).1
    refine ⟨parents.parentCell cell, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · rw [parents.parents_eq]
      exact Finset.mem_image.mpr ⟨cell, hcellEnvelope, rfl⟩
    · rw [fiber.cells_eq] at hcell
      exact (Finset.mem_filter.mp hcell).2
  have hcellsEq : fiber.cells =
      selectedParents.biUnion parents.cellsForParent := by
    ext cell
    constructor
    · intro hcell
      rw [fiber.cells_eq] at hcell
      have hcellEnvelope := (Finset.mem_filter.mp hcell).1
      have hcolor := (Finset.mem_filter.mp hcell).2
      apply Finset.mem_biUnion.mpr
      refine ⟨parents.parentCell cell, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨?_, hcolor⟩
        rw [parents.parents_eq]
        exact Finset.mem_image.mpr ⟨cell, hcellEnvelope, rfl⟩
      · rw [parents.cellsForParent_eq]
        exact Finset.mem_filter.mpr ⟨hcellEnvelope, rfl⟩
    · intro hcell
      rcases Finset.mem_biUnion.mp hcell with ⟨parent, hparent, hcellParent⟩
      have hparentData := Finset.mem_filter.mp hparent
      rw [parents.cellsForParent_eq] at hcellParent
      have hcellData := Finset.mem_filter.mp hcellParent
      rw [fiber.cells_eq]
      apply Finset.mem_filter.mpr
      refine ⟨hcellData.1, ?_⟩
      change color (parents.parentCell cell) = fiber.target
      rw [hcellData.2]
      exact hparentData.2
  exact ⟨{
    fiber := fiber
    selectedParents := selectedParents
    selectedParents_eq := rfl
    selectedParents_nonempty := hselectedParentsNonempty
    selectedParents_subset := Finset.filter_subset _ _
    cells_eq_biUnion := hcellsEq
  }⟩

/-- Select one separated parent y-residue while retaining the exact weighted
side-`rho` cell mass, rather than the number or volume of ambient parents. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseParentData.selectYResidue
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    (parents : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope) :
    Nonempty (PureWZ2BalancedSafeOuterPopularCoarseParentYResidueData
      data outerPopular envelope parents) := by
  let color : (ℤ × ℤ × ℤ) → Fin 512 := fun parent =>
    ⟨(parent.2.1 % (512 : ℤ)).toNat, by
      have hnonneg : 0 ≤ parent.2.1 % (512 : ℤ) :=
        Int.emod_nonneg _ (by norm_num)
      have hlt : parent.2.1 % (512 : ℤ) < (512 : ℤ) :=
        Int.emod_lt_of_pos _ (by norm_num)
      omega⟩
  let parentFiber := Classical.choice
    (PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseParentData.selectParentFiber
      data outerPopular envelope parents color)
  let residue := parentFiber.fiber.target
  have hresidue : ∀ parent ∈ parentFiber.selectedParents,
      parent.2.1 % (512 : ℤ) = (residue : ℤ) := by
    intro parent hparent
    rw [parentFiber.selectedParents_eq] at hparent
    have hlabel := (Finset.mem_filter.mp hparent).2
    have hnonneg : 0 ≤ parent.2.1 % (512 : ℤ) :=
      Int.emod_nonneg _ (by norm_num)
    have hcast : ((color parent : ℕ) : ℤ) =
        parent.2.1 % (512 : ℤ) := by
      simp [color, Int.toNat_of_nonneg hnonneg]
    have hcastEq := congrArg (fun value : Fin 512 => (value : ℤ)) hlabel
    rwa [hcast] at hcastEq
  have hseparated : ∀ first ∈ parentFiber.selectedParents,
      ∀ second ∈ parentFiber.selectedParents,
        first.2.1 = second.2.1 ∨
          (512 : ℤ) ≤ |first.2.1 - second.2.1| := by
    intro first hfirst second hsecond
    by_cases heq : first.2.1 = second.2.1
    · exact Or.inl heq
    · right
      have hmod : (first.2.1 - second.2.1) % (512 : ℤ) = 0 := by
        rw [Int.sub_emod, hresidue first hfirst, hresidue second hsecond]
        simp
      have hdiv : (512 : ℤ) ∣ first.2.1 - second.2.1 := by
        rwa [Int.dvd_iff_emod_eq_zero]
      exact Int.le_abs_of_dvd (sub_ne_zero.mpr heq) hdiv
  exact ⟨{
    residue := residue
    parentFiber := parentFiber
    target_eq := rfl
    residue_eq := hresidue
    y_separated := hseparated
  }⟩

/-- Select the second-parent height and the mod-512 y-residue in one
cell-weighted step. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseParentData.selectHeightY
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    (parents : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope) :
    Nonempty (PureWZ2BalancedSafeOuterPopularCoarseParentHeightYData
      data outerPopular envelope parents) := by
  let heightValues := parents.parents.image fun parent => parent.2.2
  have hheightValuesNonempty : heightValues.Nonempty :=
    parents.parents_nonempty.image fun parent => parent.2.2
  let defaultHeight := Classical.choose hheightValuesNonempty
  have hdefaultHeight : defaultHeight ∈ heightValues :=
    Classical.choose_spec hheightValuesNonempty
  letI : Nonempty {height // height ∈ heightValues} :=
    ⟨⟨defaultHeight, hdefaultHeight⟩⟩
  let heightLabel : (ℤ × ℤ × ℤ) → {height // height ∈ heightValues} :=
    fun parent => if hparent : parent ∈ parents.parents then
      ⟨parent.2.2, Finset.mem_image.mpr ⟨parent, hparent, rfl⟩⟩
    else ⟨defaultHeight, hdefaultHeight⟩
  have hheightLabel : ∀ parent (hparent : parent ∈ parents.parents),
      (heightLabel parent).1 = parent.2.2 := by
    intro parent hparent
    simp [heightLabel, hparent]
  let residueLabel : (ℤ × ℤ × ℤ) → Fin 512 := fun parent =>
    ⟨(parent.2.1 % (512 : ℤ)).toNat, by
      have hnonneg : 0 ≤ parent.2.1 % (512 : ℤ) :=
        Int.emod_nonneg _ (by norm_num)
      have hlt : parent.2.1 % (512 : ℤ) < (512 : ℤ) :=
        Int.emod_lt_of_pos _ (by norm_num)
      omega⟩
  let color : (ℤ × ℤ × ℤ) →
      {height // height ∈ heightValues} × Fin 512 := fun parent =>
    (heightLabel parent, residueLabel parent)
  let parentFiber := Classical.choice
    (PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseParentData.selectParentFiber
      data outerPopular envelope parents color)
  let commonParentHeight := parentFiber.fiber.target.1.1
  let residue := parentFiber.fiber.target.2
  have hparentHeight : ∀ parent ∈ parentFiber.selectedParents,
      parent.2.2 = commonParentHeight := by
    intro parent hparent
    rw [parentFiber.selectedParents_eq] at hparent
    have hlabel := (Finset.mem_filter.mp hparent).2
    have hparentMem := (Finset.mem_filter.mp hparent).1
    have hfirst := congrArg Prod.fst hlabel
    change heightLabel parent = parentFiber.fiber.target.1 at hfirst
    have hvalue := congrArg Subtype.val hfirst
    rw [hheightLabel parent hparentMem] at hvalue
    exact hvalue
  have hresidue : ∀ parent ∈ parentFiber.selectedParents,
      parent.2.1 % (512 : ℤ) = (residue : ℤ) := by
    intro parent hparent
    rw [parentFiber.selectedParents_eq] at hparent
    have hlabel := (Finset.mem_filter.mp hparent).2
    have hsecond := congrArg Prod.snd hlabel
    change residueLabel parent = residue at hsecond
    have hnonneg : 0 ≤ parent.2.1 % (512 : ℤ) :=
      Int.emod_nonneg _ (by norm_num)
    have hcast : ((residueLabel parent : ℕ) : ℤ) =
        parent.2.1 % (512 : ℤ) := by
      simp [residueLabel, Int.toNat_of_nonneg hnonneg]
    have hcastEq := congrArg (fun value : Fin 512 => (value : ℤ)) hsecond
    rwa [hcast] at hcastEq
  have hseparated : ∀ first ∈ parentFiber.selectedParents,
      ∀ second ∈ parentFiber.selectedParents,
        first.2.1 = second.2.1 ∨
          (512 : ℤ) ≤ |first.2.1 - second.2.1| := by
    intro first hfirst second hsecond
    by_cases heq : first.2.1 = second.2.1
    · exact Or.inl heq
    · right
      have hmod : (first.2.1 - second.2.1) % (512 : ℤ) = 0 := by
        rw [Int.sub_emod, hresidue first hfirst, hresidue second hsecond]
        simp
      have hdiv : (512 : ℤ) ∣ first.2.1 - second.2.1 := by
        rwa [Int.dvd_iff_emod_eq_zero]
      exact Int.le_abs_of_dvd (sub_ne_zero.mpr heq) hdiv
  exact ⟨{
    heightValues := heightValues
    heightValues_eq := rfl
    heightValues_nonempty := hheightValuesNonempty
    heightLabel := heightLabel
    heightLabel_eq := hheightLabel
    residueLabel := residueLabel
    parentFiber := parentFiber
    commonParentHeight := commonParentHeight
    residue := residue
    parent_height_eq := hparentHeight
    residue_eq := hresidue
    y_separated := hseparated
  }⟩

/-- Every cell retained by the simultaneous height/residue choice lies below
one of the selected genuine second-cover parents. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseParentHeightYData.cell_parent_selected
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parents : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    (selection : PureWZ2BalancedSafeOuterPopularCoarseParentHeightYData
      data outerPopular envelope parents)
    {cell : ℤ × ℤ × ℤ}
    (hcell : cell ∈ selection.parentFiber.fiber.cells) :
    parents.parentCell cell ∈ selection.parentFiber.selectedParents := by
  rw [selection.parentFiber.selectedParents_eq]
  apply Finset.mem_filter.mpr
  rw [selection.parentFiber.fiber.cells_eq] at hcell
  have hcellEnvelope := (Finset.mem_filter.mp hcell).1
  refine ⟨?_, ?_⟩
  · rw [parents.parents_eq]
    exact Finset.mem_image.mpr ⟨cell, hcellEnvelope, rfl⟩
  · exact (Finset.mem_filter.mp hcell).2

/-- The selected coarse shading stays inside the union of its selected
second-cover parents.  In particular no ambient parent fibre is reintroduced. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseParentHeightYData.union_subset_selectedParents
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parents : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    (selection : PureWZ2BalancedSafeOuterPopularCoarseParentHeightYData
      data outerPopular envelope parents) :
    selection.parentFiber.fiber.shading.union ⊆
      ⋃ parent ∈ selection.parentFiber.selectedParents,
        wz1PaperGridCube twoScale.sqrtRequested.1 parent := by
  intro point hpoint
  rw [selection.parentFiber.fiber.union_eq, wz2RetainedCellsUnion] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
  let parent := parents.parentCell cell
  have hparent : parent ∈ selection.parentFiber.selectedParents :=
    PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseParentHeightYData.cell_parent_selected
      selection hcell
  have hcellEnvelope : cell ∈ envelope.cells := by
    rw [selection.parentFiber.fiber.cells_eq] at hcell
    exact (Finset.mem_filter.mp hcell).1
  apply Set.mem_iUnion₂.mpr
  refine ⟨parent, hparent, ?_⟩
  exact parents.cell_parent cell hcellEnvelope hpointCell

/-- All points of the selected coarse shading lie in one actual
side-`sqrt(rho)` parent-height slab. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseParentHeightYData.union_height
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parents : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    (selection : PureWZ2BalancedSafeOuterPopularCoarseParentHeightYData
      data outerPopular envelope parents) :
    ∀ point ∈ selection.parentFiber.fiber.shading.union,
      point (2 : Fin 3) ∈ Set.Ico
        ((selection.commonParentHeight : ℝ) * twoScale.sqrtRequested.1)
        (((selection.commonParentHeight : ℝ) + 1) *
          twoScale.sqrtRequested.1) := by
  intro point hpoint
  have hparentRegion :=
    PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseParentHeightYData.union_subset_selectedParents
      selection hpoint
  rcases Set.mem_iUnion₂.mp hparentRegion with
    ⟨parent, hparent, hpointParent⟩
  have hroot : 0 < twoScale.sqrtRequested.1 :=
    twoScale.fine.coarse_extremal.delta_pos
  rw [wz1PaperGridCube_eq_Ico hroot parent] at hpointParent
  rw [← selection.parent_height_eq parent hparent]
  exact ⟨hpointParent.2.2.2.2.1, hpointParent.2.2.2.2.2⟩

/-- Exact source-mass retention of the simultaneous second-parent height and
y-residue selection. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseParentHeightYData.envelope_mass_le
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parents : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    (selection : PureWZ2BalancedSafeOuterPopularCoarseParentHeightYData
      data outerPopular envelope parents) :
    envelope.sourcePullback.shading.mass ≤
      ((selection.heightValues.card * 512 : ℕ) : ENNReal) *
        selection.parentFiber.fiber.sourcePullback.shading.mass := by
  simpa using selection.parentFiber.fiber.retained_mass

/-- Materialize the simultaneous parent-height/y-residue fiber through the
generic literal-cell restriction producer.  This is the carrier boundary used
by later fixed-line and graph constructions: no ambient parent cells can be
reintroduced past this point. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseParentHeightYData.restrictCells
    {data : PureWZ2BalancedSafeCoarseCompanionData safe block}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho)}
    {envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular}
    {parents : PureWZ2BalancedSafeOuterPopularCoarseParentData
      data outerPopular envelope}
    (selection : PureWZ2BalancedSafeOuterPopularCoarseParentHeightYData
      data outerPopular envelope parents) :
    Nonempty (PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionData
      data outerPopular envelope selection.parentFiber.fiber.cells) := by
  apply PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData.restrictCells
    data outerPopular envelope selection.parentFiber.fiber.cells
  · intro cell hcell
    rw [selection.parentFiber.fiber.cells_eq] at hcell
    exact (Finset.mem_filter.mp hcell).1
  · exact selection.parentFiber.fiber.cells_nonempty

/-- Compose source outer-height retention with an arbitrary finite joint
cell label.  This is the exact block-level bookkeeping used before installing
the geometric labels for global bin, graph goodness, internal popularity, and
`Z_lin`. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseCellFiberData.block_source_mass_le
    {β : Type*} [Fintype β] [DecidableEq β]
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    (color : (ℤ × ℤ × ℤ) → β)
    (fiber : PureWZ2BalancedSafeOuterPopularCoarseCellFiberData
      data outerPopular envelope color) :
    data.sourcePullback.shading.mass ≤
      2 * (2 * outerPopular.popular.bins : ENNReal) *
        (Fintype.card β : ENNReal) * fiber.sourcePullback.shading.mass := by
  calc
    data.sourcePullback.shading.mass ≤
        2 * (2 * outerPopular.popular.bins : ENNReal) *
          envelope.sourcePullback.shading.mass :=
      PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData.block_source_mass_le
        data outerPopular envelope
    _ ≤ 2 * (2 * outerPopular.popular.bins : ENNReal) *
        ((Fintype.card β : ENNReal) *
          fiber.sourcePullback.shading.mass) := by
      exact mul_le_mul_left' fiber.retained_mass
        (2 * (2 * outerPopular.popular.bins : ENNReal))
    _ = 2 * (2 * outerPopular.popular.bins : ENNReal) *
        (Fintype.card β : ENNReal) *
          fiber.sourcePullback.shading.mass := by ring

/-- The whole-cell outer-popular envelope, reindexed on the ordinary active
cell family used by the coarse Lemma-23 pipeline.  The reindexing changes no
spatial set and uses the actual envelope volume as its window supply. -/
structure PureWZ2BalancedSafeOuterPopularCoarseEnvelopeWindowData
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    (coarsePrepared : PureWZ2Lemma23PreparedCoarse twoScale) where
  shadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily twoScale.fine.refined
      twoScale.coarseGrains.extremal.delta_pos)
  carrier_eq : ∀ index, shadow.carrier index =
    coarsePrepared.shadow.carrier index ∩ envelope.shading.union
  subshading : IsSubshading shadow coarsePrepared.shadow
  union_eq : shadow.union = envelope.shading.union
  window : PureWZ2Lemma23WindowedCoarse coarsePrepared
  window_left : window.left = (safe.blockWindow block).window.left
  window_shading : window.shading = shadow
  window_supply : window.volumeSupply = volume envelope.shading.union

/-- Install the exact synchronized envelope as one coarse Lemma-23 window.
The safe-block margin controls every auxiliary snapped cell meeting the full
coarse cells, so no second height selection is made here. -/
theorem PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData.toCoarseWindow
    (data : PureWZ2BalancedSafeCoarseCompanionData safe block)
    (outerPopular : PureWZ2SourceWindowHeightPopularData
      (safe.blockWindow block).window (256 * rho))
    (envelope : PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      data outerPopular)
    (coarsePrepared : PureWZ2Lemma23PreparedCoarse twoScale) :
    Nonempty (PureWZ2BalancedSafeOuterPopularCoarseEnvelopeWindowData
      data outerPopular envelope coarsePrepared) := by
  let region := envelope.shading.union
  let shadow : Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily twoScale.fine.refined
        twoScale.coarseGrains.extremal.delta_pos) :=
    { carrier := fun index => coarsePrepared.shadow.carrier index ∩ region
      measurable_carrier := fun index =>
        (coarsePrepared.shadow.measurable_carrier index).inter
          (measurableSet_shading_union envelope.shading)
      subset_body := fun index => Set.inter_subset_left.trans
        (coarsePrepared.shadow.subset_body index) }
  have henvelopeFine : envelope.shading.union ⊆
      twoScale.fine.refined.union := by
    intro point hpoint
    have hcompanion : point ∈ data.shading.union :=
      envelope.subshading.union_subset hpoint
    rcases hcompanion with ⟨index, hindex⟩
    rw [data.carrier_eq index] at hindex
    have hzero : point ∈ data.zeroExtension.ambientShading.union :=
      ⟨index, hindex.1⟩
    rwa [data.zeroExtension.union_eq] at hzero
  have henvelopePrepared : envelope.shading.union ⊆
      coarsePrepared.shadow.union := by
    rw [coarsePrepared.shadow_union]
    exact henvelopeFine
  have hshadowUnion : shadow.union = envelope.shading.union := by
    change shadow.union = region
    ext point
    constructor
    · rintro ⟨index, hprepared, hregion⟩
      exact hregion
    · intro hregion
      rcases henvelopePrepared hregion with ⟨index, hprepared⟩
      exact ⟨index, hprepared, hregion⟩
  have hsub : IsSubshading shadow coarsePrepared.shadow :=
    fun _ => Set.inter_subset_left
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hactive :
      ∀ graphCell ∈ wz1Lemma23ActiveCells shadow rho hrho,
        (wz1Lemma23SnappedPoint rho graphCell) (2 : Fin 3) ∈
          Set.Icc (safe.blockWindow block).window.left
            ((safe.blockWindow block).window.left + Real.sqrt rho) := by
    intro graphCell hgraphCell
    rw [wz1Lemma23_mem_active_iff] at hgraphCell
    rcases hgraphCell.2 with ⟨point, hpointShadow, hpointGraphCell⟩
    have hpointEnvelope : point ∈ envelope.shading.union := by
      rw [← hshadowUnion]
      exact hpointShadow
    rw [envelope.union_eq, wz2RetainedCellsUnion] at hpointEnvelope
    rcases Set.mem_iUnion₂.mp hpointEnvelope with
      ⟨paperCell, hpaperCell, hpointPaperCell⟩
    have hpaperCellBlock : paperCell ∈ (safe.blockWindow block).cells := by
      rw [envelope.cells_eq] at hpaperCell
      exact (Finset.mem_filter.mp hpaperCell).1
    have hsafeRaw : pureWZ2PaperCellCenterHeight rho paperCell ∈
        Set.Icc
          (pureWZ2BalancedWindowPhaseLeftAt rho safe.phase block.1 + rho)
          (pureWZ2BalancedWindowPhaseLeftAt rho safe.phase block.1 +
            Real.sqrt rho - rho) := by
      rw [(safe.blockWindow block).cells_eq,
        pureWZ2BalancedSafeWindowCells] at hpaperCellBlock
      exact (Finset.mem_filter.mp hpaperCellBlock).2
    have hsafe : pureWZ2PaperCellCenterHeight rho paperCell ∈
        Set.Icc
          ((safe.blockWindow block).window.left + rho)
          ((safe.blockWindow block).window.left + Real.sqrt rho - rho) := by
      simpa [(safe.blockWindow block).window_left] using hsafeRaw
    have hpaperBounds := hpointPaperCell
    rw [wz1PaperGridCube_eq_Ico hrho paperCell] at hpaperBounds
    have hpointPaperCenter :
        |point (2 : Fin 3) - pureWZ2PaperCellCenterHeight rho paperCell| ≤
          rho / 2 := by
      rw [abs_le]
      constructor
      · calc
          -(rho / 2) =
              (paperCell.2.2 : ℝ) * rho -
                pureWZ2PaperCellCenterHeight rho paperCell := by
                  dsimp only [pureWZ2PaperCellCenterHeight]
                  ring
          _ ≤ point (2 : Fin 3) -
                pureWZ2PaperCellCenterHeight rho paperCell :=
              sub_le_sub_right hpaperBounds.2.2.2.2.1 _
      · calc
          point (2 : Fin 3) -
                pureWZ2PaperCellCenterHeight rho paperCell ≤
              ((paperCell.2.2 : ℝ) + 1) * rho -
                pureWZ2PaperCellCenterHeight rho paperCell :=
              sub_le_sub_right hpaperBounds.2.2.2.2.2.le _
          _ = rho / 2 := by
              dsimp only [pureWZ2PaperCellCenterHeight]
              ring
    have hgraphCenter :
        |point (2 : Fin 3) -
            (wz1Lemma23SnappedPoint rho graphCell) (2 : Fin 3)| ≤
          rho / 2 :=
      ((wz1_lemma23_snapped_cell_geometry rho hrho hrhoOne).2.1
        graphCell point hpointGraphCell).1 (2 : Fin 3)
    rw [abs_le] at hpointPaperCenter hgraphCenter
    exact ⟨by linarith [hsafe.1], by linarith [hsafe.2]⟩
  have hvolumePos : 0 < volume envelope.shading.union :=
    outerPopular.volume_pos.trans_le
      (measure_mono envelope.source_envelope_subset)
  have hvolumeTop : volume envelope.shading.union ≠ ⊤ := by
    rw [envelope.volume_eq]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (wz1PaperGridCube_volume_ne_top hrho (0, 0, 0))
  rcases coarsePrepared.ofSubshading
      (safe.blockWindow block).window.left shadow hsub
      (by simpa only [twoScale.rhoRequested_eq] using hactive)
      (volume envelope.shading.union) hvolumePos hvolumeTop
      (by rw [hshadowUnion]) with
    ⟨window, hleft, hwindowShading, hsupply⟩
  exact ⟨{
    shadow := shadow
    carrier_eq := fun _ => rfl
    subshading := hsub
    union_eq := hshadowUnion
    window := window
    window_left := hleft
    window_shading := hwindowShading
    window_supply := hsupply
  }⟩

end PureWZ2BalancedSafeCoarseCompanionData

namespace PureWZ2BalancedSafeCoarseCompanionFamilyData

variable
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}

/-- The outer-popular whole-cell coarse envelope, with its exact source
pullback, on every safe block. -/
structure OuterPopularEnvelopeFamilyData
    (data : PureWZ2BalancedSafeCoarseCompanionFamilyData safe)
    (outerPopular : ∀ block : {block // block ∈ safe.blocks},
      PureWZ2SourceWindowHeightPopularData
        (safe.blockWindow block).window (256 * rho)) where
  envelope : ∀ block : {block // block ∈ safe.blocks},
    PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
      (data.companion block)
      (outerPopular block)

/-- Construct all same-cell outer-popular envelopes without reselecting a
block or a first-cover companion. -/
theorem outerPopularEnvelopes
    (data : PureWZ2BalancedSafeCoarseCompanionFamilyData safe)
    (outerPopular : ∀ block : {block // block ∈ safe.blocks},
      PureWZ2SourceWindowHeightPopularData
        (safe.blockWindow block).window (256 * rho)) :
    Nonempty (data.OuterPopularEnvelopeFamilyData outerPopular) := by
  have henvelope : ∀ block : {block // block ∈ safe.blocks},
      Nonempty (PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData
        (data.companion block) (outerPopular block)) := fun block =>
    (data.companion block).outerPopularCoarseEnvelope (outerPopular block)
  exact ⟨{ envelope := fun block => Classical.choice (henvelope block) }⟩

namespace OuterPopularEnvelopeFamilyData

variable
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {companions : PureWZ2BalancedSafeCoarseCompanionFamilyData safe}
    {outerPopular : ∀ block : {block // block ∈ safe.blocks},
      PureWZ2SourceWindowHeightPopularData
        (safe.blockWindow block).window (256 * rho)}

/-- Summed indexed-mass retention on any chosen family of safe blocks.  This
is the first synchronized weight ledger: every term is the exact first-cover
pullback of the whole-cell outer-popular envelope in that same block. -/
theorem source_mass_le_sum
    (data : companions.OuterPopularEnvelopeFamilyData outerPopular)
    (blocks : Finset {block // block ∈ safe.blocks})
    (outerCost : ENNReal)
    (houterCost : ∀ block ∈ blocks,
      (2 * (outerPopular block).popular.bins : ENNReal) ≤ outerCost) :
    (∑ block ∈ blocks,
        (companions.companion block).sourcePullback.shading.mass) ≤
      2 * outerCost * ∑ block ∈ blocks,
        (data.envelope block).sourcePullback.shading.mass := by
  calc
    (∑ block ∈ blocks,
        (companions.companion block).sourcePullback.shading.mass) ≤
      ∑ block ∈ blocks,
        2 * (2 * (outerPopular block).popular.bins : ENNReal) *
          (data.envelope block).sourcePullback.shading.mass := by
      exact Finset.sum_le_sum fun block _ =>
        PureWZ2BalancedSafeCoarseCompanionData.PureWZ2BalancedSafeOuterPopularCoarseEnvelopeData.block_source_mass_le
          (companions.companion block) (outerPopular block)
          (data.envelope block)
    _ ≤ ∑ block ∈ blocks,
        2 * outerCost *
          (data.envelope block).sourcePullback.shading.mass := by
      gcongr with block hblock
      exact houterCost block hblock
    _ = 2 * outerCost * ∑ block ∈ blocks,
        (data.envelope block).sourcePullback.shading.mass := by
      rw [Finset.mul_sum]

end OuterPopularEnvelopeFamilyData

/-- The safe phase retains half of the original source mass after translating
each block through its exact same-cell coarse companion. -/
theorem aggregate_source_mass_lower
    (data : PureWZ2BalancedSafeCoarseCompanionFamilyData safe) :
    volume prepared.shadow.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) ≤
      2 * ∑ block : {block // block ∈ safe.blocks},
        (data.companion block).sourcePullback.shading.mass := by
  have hhalf := safe.volume_half
  calc
    volume prepared.shadow.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) ≤
        (2 * ∑ block : {block // block ∈ safe.blocks},
          volume (safe.blockWindow block).shading.union) *
            (twoScale.coarse.fineMultiplicity : ENNReal) := by gcongr
    _ = 2 * ∑ block : {block // block ∈ safe.blocks},
          volume (safe.blockWindow block).shading.union *
            (twoScale.coarse.fineMultiplicity : ENNReal) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ 2 * ∑ block : {block // block ∈ safe.blocks},
          (data.companion block).sourcePullback.shading.mass := by
      gcongr with block
      exact
        PureWZ2BalancedSafeCoarseCompanionData.block_volume_mul_multiplicity_le_source_mass
          (data.companion block)

end PureWZ2BalancedSafeCoarseCompanionFamilyData

end Kakeya.Assouad

end
