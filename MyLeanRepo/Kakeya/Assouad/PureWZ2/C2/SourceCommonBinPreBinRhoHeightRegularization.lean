import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CommonBinRhoHeightUniformization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CommonBinRhoHeightLogCost
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinStandardSlabSourceMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CoarseRegionSourcePullback

/-!
# Source-height regularization before common-bin selection

The paper first regularizes the complete genuine side-`rho` fibres in one
standard side-`sqrt rho` slab.  Only afterwards are the common-bin label and
the local graph selected.  This module packages that pre-bin refinement.

The retained family consists of complete height fibres of
`standardSqrtSlabRhoCells`.  It is realized simultaneously as a genuine
first-sticky coarse cubical shading and as its exact pullback to the original
source family.  The cardinality, coarse volume, source union volume, and
indexed source mass therefore all have the same logarithmic retention factor.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Complete source-height uniformization on one occupied standard slab,
performed before any reference height or common-bin label is chosen. -/
structure PureWZ2StandardSlabPreBinRhoHeightRegularizedData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale)
    (heightIndex : {heightIndex // heightIndex ∈
      pullback.standardSqrtSlabIndices}) where
  uniform :
    CommonBinRhoHeightUniformData
      (pullback.standardSqrtSlabRhoCells heightIndex.1)
  cells : Finset (ℤ × ℤ × ℤ) := uniform.cells
  cells_eq : cells = uniform.cells
  cells_subset_standard :
    cells ⊆ pullback.standardSqrtSlabRhoCells heightIndex.1
  cells_subset_selected : cells ⊆ pullback.selectedCells
  cells_nonempty : cells.Nonempty
  heightIndices : Finset ℤ := uniform.heightIndices
  heightIndices_eq : heightIndices = uniform.heightIndices
  heightIndices_nonempty : heightIndices.Nonempty
  cells_eq_height_filter :
    cells =
      (pullback.standardSqrtSlabRhoCells heightIndex.1).filter fun cell =>
        cell.2.2 ∈ heightIndices
  heightFiberCount : ℕ := uniform.heightFiberCount
  heightFiberCount_pos : 0 < heightFiberCount
  height_fiber_lower :
    ∀ height ∈ heightIndices,
      heightFiberCount ≤
        (cells.filter fun cell => cell.2.2 = height).card
  height_fiber_upper :
    ∀ height ∈ heightIndices,
      (cells.filter fun cell => cell.2.2 = height).card ≤
        2 * heightFiberCount
  logarithmicCost : ℕ := uniform.logarithmicCost
  logarithmicCost_eq :
    logarithmicCost =
      Nat.log 2 (pullback.standardSqrtSlabRhoCells heightIndex.1).card + 1
  card_retention :
    (pullback.standardSqrtSlabRhoCells heightIndex.1).card ≤
      logarithmicCost * cells.card
  zeroExtension :
    WZ2PaperSubfamilyZeroExtensionData
      twoScale.fine.selected twoScale.fine.refined
  coarseShading : WZ1PaperTubeShading twoScale.coarse.coarse
  coarseShading_eq :
    coarseShading = wz2RefinedShading zeroExtension.ambientShading cells
  coarseShading_sub :
    PureWZ2PaperIsSubshading coarseShading twoScale.coarseGrains.shading
  coarseShading_cubical : WZ1PaperIsCubicalShading coarseShading
  coarseShading_union :
    coarseShading.union = wz2RetainedCellsUnion rho cells
  coarseShading_volume :
    volume coarseShading.union =
      (cells.card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0))
  sourcePullback :
    PureWZ2SelectedCoarseRegionSourcePullbackData coarseShading
  sourcePullback_selectedCells : sourcePullback.selectedCells = cells
  source_volume :
    volume sourcePullback.shading.union =
      (cells.card : ENNReal) * twoScale.coarse.balanced.cellMass
  source_mass :
    sourcePullback.shading.mass =
      (cells.card : ENNReal) * twoScale.coarse.balanced.incidenceMass
  source_coarse_cross :
    sourcePullback.shading.mass *
          volume (wz1PaperGridCube rho (0, 0, 0)) =
      volume coarseShading.union *
        twoScale.coarse.balanced.incidenceMass
  source_density_cross :
    sourcePullback.shading.mass * twoScale.coarse.balanced.cellMass =
      volume sourcePullback.shading.union *
        twoScale.coarse.balanced.incidenceMass
  sourceWeight_retention :
    pullback.standardSqrtSlabSourceWeight heightIndex.1 ≤
      logarithmicCost * sourcePullback.shading.mass
  sourceVolume_retention :
    volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) ≤
      logarithmicCost * volume sourcePullback.shading.union
  coarseVolume_retention :
    volume (pullback.standardSqrtSlabCoarseRegion heightIndex.1) ≤
      logarithmicCost * volume coarseShading.union

/-- Family-free envelope for the one dyadic source-height regularization
cost. -/
def pureWZ2CommonBinPreBinHeightCost (rho : ℝ) : ENNReal :=
  ENNReal.ofReal
    (wz2PaperBoundaryLogCoefficient * (1 + Real.log rho⁻¹))

theorem pureWZ2CommonBinPreBinHeightCost_pos
    {rho : ℝ} (hrho : 0 < rho) (hrhoOne : rho ≤ 1) :
    0 < pureWZ2CommonBinPreBinHeightCost rho := by
  have hboundary : (1 : ℝ) ≤ wz2PaperBoundaryLogCoefficient := by
    unfold wz2PaperBoundaryLogCoefficient
    have hnonneg : 0 ≤ 5 * Real.log 163 / Real.log 2 :=
      div_nonneg
        (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))
        (Real.log_nonneg (by norm_num))
    exact (show (1 : ℝ) ≤ 5 * Real.log 163 / Real.log 2 + 2 by
      linarith).trans (le_max_left _ _)
  have hlog : 0 ≤ Real.log rho⁻¹ :=
    Real.log_nonneg ((one_le_inv₀ hrho).mpr hrhoOne)
  unfold pureWZ2CommonBinPreBinHeightCost
  exact ENNReal.ofReal_pos.mpr (mul_pos (lt_of_lt_of_le zero_lt_one hboundary)
    (by linarith))

theorem pureWZ2CommonBinPreBinHeightCost_ne_top (rho : ℝ) :
    pureWZ2CommonBinPreBinHeightCost rho ≠ ⊤ :=
  ENNReal.ofReal_ne_top

theorem pureWZ2CommonBinPreBinHeightCost_le_boundaryFactor
    (rho : ℝ) :
    pureWZ2CommonBinPreBinHeightCost rho ≤
      42 * ENNReal.ofReal (1 + Real.log rho⁻¹) := by
  have hboundaryNonneg : 0 ≤ wz2PaperBoundaryLogCoefficient := by
    unfold wz2PaperBoundaryLogCoefficient
    exact le_max_of_le_right (by positivity)
  have hboundary :
      ENNReal.ofReal wz2PaperBoundaryLogCoefficient ≤ 42 := by
    rw [show (42 : ENNReal) = ENNReal.ofReal (42 : ℝ) by norm_num]
    exact ENNReal.ofReal_mono wz2PaperBoundaryLogCoefficient_le_fortyTwo
  unfold pureWZ2CommonBinPreBinHeightCost
  rw [ENNReal.ofReal_mul hboundaryNonneg]
  gcongr

namespace PureWZ2StandardSlabPreBinRhoHeightRegularizedData

variable
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {heightIndex : {heightIndex // heightIndex ∈
      pullback.standardSqrtSlabIndices}}
    (data : PureWZ2StandardSlabPreBinRhoHeightRegularizedData
      pullback heightIndex)

theorem logarithmicCost_le_heightCost (hrhoOne : rho ≤ 1) :
    (data.logarithmicCost : ENNReal) ≤
      pureWZ2CommonBinPreBinHeightCost rho := by
  have hrho : 0 < twoScale.rhoRequested.1 :=
    twoScale.coarseGrains.extremal.delta_pos
  have hcard :
      (pullback.standardSqrtSlabRhoCells heightIndex.1).card ≤
        (wz1PaperActiveCells twoScale.fine.refined hrho).card := by
    apply Finset.card_le_card
    intro cell hcell
    rw [← pullback.selectedCells_eq]
    exact pullback.standardSqrtSlabRhoCells_subset heightIndex.1 hcell
  rw [data.logarithmicCost_eq]
  simpa [pureWZ2CommonBinPreBinHeightCost, twoScale.rhoRequested_eq] using
    commonBin_rhoHeight_logarithmicCostBoundaryENN_le
      hrho (by simpa only [twoScale.rhoRequested_eq] using hrhoOne)
      twoScale.fine.refined
      (pullback.standardSqrtSlabRhoCells heightIndex.1).card hcard

/-- The complete pre-bin height family lies in the one standard
side-`sqrt rho` slab from which it was selected.  Thus its number of
side-`rho` height labels has the paper's single half-power bound. -/
theorem heightIndices_card_mul_rho_le :
    (data.heightIndices.card : ℝ) * rho ≤
      Real.sqrt rho + 2 * rho := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hroot : 0 < twoScale.sqrtRequested.1 :=
    twoScale.fine.coarse_extremal.delta_pos
  let lower : ℤ :=
    Int.floor
      ((heightIndex.1 : ℝ) * twoScale.sqrtRequested.1 / rho)
  let upper : ℤ :=
    Int.floor
      (((heightIndex.1 : ℝ) + 1) * twoScale.sqrtRequested.1 / rho)
  have hsubset : data.heightIndices ⊆ Finset.Icc lower upper := by
    intro height hheight
    rw [data.heightIndices_eq, data.uniform.heightIndices_eq,
      ← data.cells_eq] at hheight
    rcases Finset.mem_image.mp hheight with
      ⟨cell, hcell, hcellHeight⟩
    have hslab :
        cell ∈ pullback.standardSqrtSlabRhoCells heightIndex.1 :=
      data.cells_subset_standard hcell
    let point := cellCorner rho cell
    have hpointCell :
        point ∈ wz1PaperGridCube rho cell :=
      cellCorner_mem_gridCube hrho cell
    have hpointParent :
        point ∈
          wz1PaperGridCube twoScale.sqrtRequested.1
            (pullback.standardSecondParent cell) :=
      pullback.standardSqrtSlabRhoCell_subset_parent
        hslab hpointCell
    rw [wz1PaperGridCube_eq_Ico hroot] at hpointParent
    have hparentHeight :=
      pullback.standardSqrtSlabRhoCell_parent_height hslab
    have hlowerProduct :
        (heightIndex.1 : ℝ) * twoScale.sqrtRequested.1 ≤
          (height : ℝ) * rho := by
      calc
        (heightIndex.1 : ℝ) * twoScale.sqrtRequested.1 =
            ((pullback.standardSecondParent cell).2.2 : ℝ) *
              twoScale.sqrtRequested.1 := by rw [hparentHeight]
        _ ≤ point (2 : Fin 3) := hpointParent.2.2.2.2.1
        _ = (height : ℝ) * rho := by
          simp [point, cellCorner, wz1PaperGridCubeTranslation,
            hcellHeight]
    have hupperProduct :
        (height : ℝ) * rho <
          ((heightIndex.1 : ℝ) + 1) *
            twoScale.sqrtRequested.1 := by
      calc
        (height : ℝ) * rho = point (2 : Fin 3) := by
          simp [point, cellCorner, wz1PaperGridCubeTranslation,
            hcellHeight]
        _ < (((pullback.standardSecondParent cell).2.2 : ℝ) + 1) *
              twoScale.sqrtRequested.1 := hpointParent.2.2.2.2.2
        _ = ((heightIndex.1 : ℝ) + 1) *
              twoScale.sqrtRequested.1 := by rw [hparentHeight]
    have hlowerReal :
        (heightIndex.1 : ℝ) * twoScale.sqrtRequested.1 / rho ≤
          (height : ℝ) :=
      (div_le_iff₀ hrho).2 hlowerProduct
    have hupperReal :
        (height : ℝ) ≤
          ((heightIndex.1 : ℝ) + 1) *
              twoScale.sqrtRequested.1 / rho :=
      ((lt_div_iff₀ hrho).2 hupperProduct).le
    rw [Finset.mem_Icc]
    constructor
    · change
        Int.floor
            ((heightIndex.1 : ℝ) *
              twoScale.sqrtRequested.1 / rho) ≤ height
      have hfloor := Int.floor_mono hlowerReal
      simpa using hfloor
    · exact Int.le_floor.mpr hupperReal
  have hcardNat :
      data.heightIndices.card ≤ (Finset.Icc lower upper).card :=
    Finset.card_le_card hsubset
  have hlowerUpper : lower ≤ upper + 1 := by
    rcases data.heightIndices_nonempty with ⟨height, hheight⟩
    have hmem := hsubset hheight
    rw [Finset.mem_Icc] at hmem
    omega
  have hcardInt :
      ((Finset.Icc lower upper).card : ℤ) = upper + 1 - lower :=
    Int.card_Icc_of_le lower upper hlowerUpper
  have hcardReal :
      (data.heightIndices.card : ℝ) ≤ (upper : ℝ) + 1 - lower := by
    have hcast :
        (data.heightIndices.card : ℤ) ≤
          (Finset.Icc lower upper).card := by
      exact_mod_cast hcardNat
    rw [hcardInt] at hcast
    exact_mod_cast hcast
  have hupperFloor :
      (upper : ℝ) ≤
        ((heightIndex.1 : ℝ) + 1) *
          twoScale.sqrtRequested.1 / rho :=
    Int.floor_le _
  have hlowerFloor :
      (heightIndex.1 : ℝ) * twoScale.sqrtRequested.1 / rho <
        (lower : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hquotient :
      ((heightIndex.1 : ℝ) + 1) *
            twoScale.sqrtRequested.1 / rho -
          (heightIndex.1 : ℝ) * twoScale.sqrtRequested.1 / rho =
        twoScale.sqrtRequested.1 / rho := by
    ring
  have hcardBound :
      (data.heightIndices.card : ℝ) ≤
        twoScale.sqrtRequested.1 / rho + 2 := by
    rw [← hquotient]
    linarith
  have hmul := mul_le_mul_of_nonneg_right hcardBound hrho.le
  have hcancel :
      twoScale.sqrtRequested.1 / rho * rho =
        twoScale.sqrtRequested.1 := by
    field_simp [hrho.ne']
  rw [add_mul, hcancel] at hmul
  simpa only [twoScale.sqrtRequested_eq] using hmul

theorem heightIndices_card_le_three_sqrt_inv
    (hrhoOne : rho ≤ 1) :
    (data.heightIndices.card : ENNReal) ≤
      3 * Kakeya.realRpowENN rho (-(1 / 2 : ℝ)) := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hrootPos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  have hrhoRoot : rho ≤ Real.sqrt rho := by
    nlinarith [Real.sq_sqrt hrho.le, Real.sqrt_nonneg rho]
  have hreal :
      (data.heightIndices.card : ℝ) ≤ 3 / Real.sqrt rho := by
    apply (le_div_iff₀ hrootPos).2
    have hmul := data.heightIndices_card_mul_rho_le
    have hrootSq : Real.sqrt rho * Real.sqrt rho = rho := by
      nlinarith [Real.sq_sqrt hrho.le]
    calc
      (data.heightIndices.card : ℝ) * Real.sqrt rho =
          ((data.heightIndices.card : ℝ) * rho) /
            Real.sqrt rho := by
        field_simp [hrootPos.ne', hrho.ne']
        nlinarith
      _ ≤ (Real.sqrt rho + 2 * rho) / Real.sqrt rho := by
        gcongr
      _ ≤ (3 * Real.sqrt rho) / Real.sqrt rho := by
        gcongr
        nlinarith
      _ = 3 := by field_simp [hrootPos.ne']
  have henn := ENNReal.ofReal_mono hreal
  rw [ENNReal.ofReal_natCast] at henn
  have hinv :
      ENNReal.ofReal (3 / Real.sqrt rho) =
        3 * Kakeya.realRpowENN rho (-(1 / 2 : ℝ)) := by
    have hrealInv :
        (Real.sqrt rho)⁻¹ = Real.rpow rho (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      exact (Real.rpow_neg hrho.le (1 / 2 : ℝ)).symm
    rw [show 3 / Real.sqrt rho = 3 * (Real.sqrt rho)⁻¹ by ring,
      hrealInv, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    rfl
  rwa [hinv] at henn

end PureWZ2StandardSlabPreBinRhoHeightRegularizedData

/-- Construct the pre-bin source-height regularization from the literal full
standard-slab cell family. -/
theorem PureWZ2TwoScaleCellPullbackData.preBinRhoHeightRegularization
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale)
    (heightIndex : {heightIndex // heightIndex ∈
      pullback.standardSqrtSlabIndices}) :
    Nonempty
      (PureWZ2StandardSlabPreBinRhoHeightRegularizedData
        pullback heightIndex) := by
  let slabCells := pullback.standardSqrtSlabRhoCells heightIndex.1
  rcases commonBin_rhoHeightUniformization slabCells
      (pullback.standardSqrtSlabRhoCells_nonempty heightIndex.2) with
    ⟨uniform⟩
  let cells := uniform.cells
  have hcellsStandard : cells ⊆ slabCells := uniform.cells_subset
  have hcellsSelected : cells ⊆ pullback.selectedCells := by
    intro cell hcell
    exact pullback.standardSqrtSlabRhoCells_subset heightIndex.1
      (hcellsStandard hcell)
  rcases wz2_paper_subfamily_zero_extension
      twoScale.fine.selected twoScale.fine.refined with
    ⟨zeroExtension⟩
  have hzeroCubical :
      WZ1PaperIsCubicalShading zeroExtension.ambientShading :=
    zeroExtension.cubical twoScale.fine.refined_cubical
  have hcellsActive :
      cells ⊆ wz1PaperActiveCells zeroExtension.ambientShading
        twoScale.coarseGrains.extremal.delta_pos := by
    intro cell hcell
    have hfine :
        cell ∈ wz1PaperActiveCells twoScale.fine.refined
          twoScale.coarseGrains.extremal.delta_pos := by
      rw [← pullback.selectedCells_eq]
      exact hcellsSelected hcell
    rw [mem_wz1PaperActiveCells] at hfine ⊢
    refine ⟨hfine.1, ?_⟩
    rcases hfine.2 with ⟨point, hpoint, hpointCell⟩
    rw [← zeroExtension.union_eq] at hpoint
    exact ⟨point, hpoint, hpointCell⟩
  let coarseShading : WZ1PaperTubeShading twoScale.coarse.coarse :=
    wz2RefinedShading zeroExtension.ambientShading cells
  have hcoarseUnionBase :
      coarseShading.union =
        wz2RetainedCellsUnion twoScale.rhoRequested.1 cells :=
    wz2RefinedShading_union_eq hzeroCubical
      twoScale.coarseGrains.extremal.delta_pos hcellsActive
  have hcoarseUnion :
      coarseShading.union = wz2RetainedCellsUnion rho cells := by
    simpa only [twoScale.rhoRequested_eq] using hcoarseUnionBase
  have hcoarseSub :
      PureWZ2PaperIsSubshading
        coarseShading twoScale.coarseGrains.shading := by
    intro index point hpoint
    rcases zeroExtension.carrier_support index point hpoint.1 with
      ⟨selectedIndex, heq, hselected⟩
    subst index
    exact twoScale.fine.subshading selectedIndex hselected
  have hcoarseCubical : WZ1PaperIsCubicalShading coarseShading :=
    wz2RefinedShading_cubical hzeroCubical
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hcoarseVolume :
      volume coarseShading.union =
        (cells.card : ENNReal) *
          volume (wz1PaperGridCube rho (0, 0, 0)) := by
    rw [hcoarseUnion]
    exact wz1PaperGridCube_volume_biUnion hrho cells
  rcases pureWZ2_pullback_selected_coarse_region
      coarseShading hcoarseSub hcoarseCubical with
    ⟨sourcePullback⟩
  have hsourceCells : sourcePullback.selectedCells = cells := by
    rw [sourcePullback.selectedCells_eq]
    apply Finset.Subset.antisymm
    · intro cell hcell
      rw [mem_wz1PaperActiveCells] at hcell
      rcases hcell.2 with ⟨point, hpointShading, hpointCell⟩
      rw [hcoarseUnionBase, wz2RetainedCellsUnion] at hpointShading
      rcases Set.mem_iUnion₂.mp hpointShading with
        ⟨owner, howner, hpointOwner⟩
      have hcellEq : owner = cell :=
        ((mem_wz1PaperGridCube twoScale.rhoRequested.1 owner point).mp
          hpointOwner).symm.trans
        ((mem_wz1PaperGridCube twoScale.rhoRequested.1 cell point).mp
          hpointCell)
      rwa [hcellEq] at howner
    · intro cell hcell
      have hambient := hcellsActive hcell
      rw [mem_wz1PaperActiveCells] at hambient ⊢
      refine ⟨hambient.1, ?_⟩
      rcases hambient.2 with
        ⟨point, _hpointAmbient, hpointCell⟩
      refine ⟨point, ?_, hpointCell⟩
      rw [hcoarseUnionBase, wz2RetainedCellsUnion]
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointCell⟩
  have hsourceVolume :
      volume sourcePullback.shading.union =
        (cells.card : ENNReal) * twoScale.coarse.balanced.cellMass := by
    rw [sourcePullback.volume_eq, hsourceCells]
  have hsourceMass :
      sourcePullback.shading.mass =
        (cells.card : ENNReal) *
          twoScale.coarse.balanced.incidenceMass := by
    rw [sourcePullback.mass_eq, hsourceCells]
  have hcardRetention :
      ((slabCells.card : ℕ) : ENNReal) ≤
        (uniform.logarithmicCost : ENNReal) * (cells.card : ENNReal) := by
    exact_mod_cast uniform.card_retention
  have hsourceWeightRetention :
      pullback.standardSqrtSlabSourceWeight heightIndex.1 ≤
        (uniform.logarithmicCost : ENNReal) *
          sourcePullback.shading.mass := by
    unfold PureWZ2TwoScaleCellPullbackData.standardSqrtSlabSourceWeight
    rw [hsourceMass]
    simpa only [slabCells, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_right hcardRetention
        twoScale.coarse.balanced.incidenceMass
  have hsourceVolumeRetention :
      volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) ≤
        (uniform.logarithmicCost : ENNReal) *
          volume sourcePullback.shading.union := by
    rw [pullback.standardSqrtSlabSourceRegion_volume, hsourceVolume]
    simpa only [slabCells, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_right hcardRetention
        twoScale.coarse.balanced.cellMass
  have hcoarseVolumeRetention :
      volume (pullback.standardSqrtSlabCoarseRegion heightIndex.1) ≤
        (uniform.logarithmicCost : ENNReal) *
          volume coarseShading.union := by
    rw [pullback.standardSqrtSlabCoarseRegion_volume, hcoarseVolume]
    simpa only [slabCells, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_right hcardRetention
        (volume (wz1PaperGridCube rho (0, 0, 0)))
  exact ⟨{
    uniform := uniform
    cells := cells
    cells_eq := rfl
    cells_subset_standard := hcellsStandard
    cells_subset_selected := hcellsSelected
    cells_nonempty := uniform.cells_nonempty
    heightIndices := uniform.heightIndices
    heightIndices_eq := rfl
    heightIndices_nonempty := uniform.heightIndices_nonempty
    cells_eq_height_filter := by
      simpa only [slabCells] using uniform.cells_eq_filter
    heightFiberCount := uniform.heightFiberCount
    heightFiberCount_pos := uniform.heightFiberCount_pos
    height_fiber_lower := uniform.height_fiber_lower
    height_fiber_upper := uniform.height_fiber_upper
    logarithmicCost := uniform.logarithmicCost
    logarithmicCost_eq := by
      simpa only [slabCells] using uniform.logarithmicCost_eq
    card_retention := by
      simpa only [slabCells] using uniform.card_retention
    zeroExtension := zeroExtension
    coarseShading := coarseShading
    coarseShading_eq := rfl
    coarseShading_sub := hcoarseSub
    coarseShading_cubical := hcoarseCubical
    coarseShading_union := hcoarseUnion
    coarseShading_volume := hcoarseVolume
    sourcePullback := sourcePullback
    sourcePullback_selectedCells := hsourceCells
    source_volume := hsourceVolume
    source_mass := hsourceMass
    source_coarse_cross := sourcePullback.mass_mul_cube
    source_density_cross := sourcePullback.mass_mul_cellMass
    sourceWeight_retention := hsourceWeightRetention
    sourceVolume_retention := hsourceVolumeRetention
    coarseVolume_retention := hcoarseVolumeRetention
  }⟩

end Kakeya.Assouad

end
