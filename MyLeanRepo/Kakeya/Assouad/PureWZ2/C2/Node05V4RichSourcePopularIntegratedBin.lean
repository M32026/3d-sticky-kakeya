import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSourceVolumePopularHeights
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinRichSpatialCells
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinOccupiedBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinSpatialCellIncidence
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CommonBinDistinctIncidence

/-!
# Integrated common-bin mass on a direct-rich source slab

This is the weighted fixed-bin step in WZ Lemma 5.4.  A reference height is
chosen from the literal source-popular set `Z_S`, but the bin itself is
selected by integrating over all of `Z_S`.  Consequently the later graph can
be formed inside one fixed spatial bin without discarding the source-height
mass needed after Theorem 5.2.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace PureWZ2Node05V4RichTwoScaleCellPullbackData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)

/-- Common-bin labels which are rich at at least one source-popular height. -/
def sourcePopularRichCommonBinLabels
    (heightIndex : ℤ) (referenceHeight : ℝ) (threshold : ENNReal) :
    Finset ℤ :=
  (pureWZ2OccupiedCommonBins
      (pullback.standardSqrtSlabSourceRegion heightIndex)
      current.grain.globalGrains.slope referenceHeight (Real.sqrt rho)).filter
    fun bin =>
      ∃ height,
        height ∈ pullback.sourcePopularHeights heightIndex ∧
        height ∈ Set.Icc (-1 : ℝ) 1 ∧
        threshold ≤ pureWZ2FixedCommonBinSliceMass
          (pullback.standardSqrtSlabSourceRegion heightIndex)
          current.grain.globalGrains.slope referenceHeight
          (Real.sqrt rho) height bin

/-- Integrated mass of one fixed common-bin label over the literal `Z_S`. -/
def sourcePopularIntegratedBinMass
    (heightIndex : ℤ) (referenceHeight : ℝ) (bin : ℤ) : ENNReal :=
  ∫⁻ height in pullback.sourcePopularHeights heightIndex,
    pureWZ2FixedCommonBinSliceMass
      (pullback.standardSqrtSlabSourceRegion heightIndex)
      current.grain.globalGrains.slope referenceHeight
      (Real.sqrt rho) height bin

/-- A source-popular height witnessing that one integrated label is rich. -/
def sourcePopularRichCommonBinWitnessHeight
    (heightIndex : ℤ) (referenceHeight : ℝ)
    (threshold : ENNReal) (bin : ℤ) : ℝ :=
  if hbin : bin ∈ pullback.sourcePopularRichCommonBinLabels
      heightIndex referenceHeight threshold then
    Classical.choose (Finset.mem_filter.mp hbin).2
  else 0

/-- Side-`sqrt rho` spatial cells carrying the rich label at its witness
height; the label width remains the fine source scale `delta`. -/
def sourcePopularRichCommonBinSpatialCells
    (heightIndex : ℤ) (referenceHeight : ℝ)
    (threshold : ENNReal) (bin : ℤ) : Finset WZ2PaperCellIndex :=
  pureWZ2PreCommonBinSpatialCellsAtHeight
    (pullback.standardSqrtSlabSourceRegion heightIndex)
    current.grain.globalGrains.slope referenceHeight
    (pullback.sourcePopularRichCommonBinWitnessHeight
      heightIndex referenceHeight threshold bin)
    (Real.sqrt rho) (Real.sqrt rho)
    (Real.sqrt_pos.mpr <| by
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos)
    bin

/-- Exact source points in one integrated fixed bin over `Z_S`. -/
def sourcePopularFixedBinHeightRegion
    (heightIndex : ℤ) (referenceHeight : ℝ) (bin : ℤ) : Set Point3 :=
  pureWZ2FixedCommonBinRegion
      (pullback.standardSqrtSlabSourceRegion heightIndex)
      current.grain.globalGrains.slope referenceHeight
      (Real.sqrt rho) bin ∩
    {point | point (2 : Fin 3) ∈
      pullback.sourcePopularHeights heightIndex}

theorem sourcePopularRichCommonBinWitnessHeight_spec
    (heightIndex : ℤ) (referenceHeight : ℝ) (threshold : ENNReal)
    {bin : ℤ}
    (hbin : bin ∈ pullback.sourcePopularRichCommonBinLabels
      heightIndex referenceHeight threshold) :
    pullback.sourcePopularRichCommonBinWitnessHeight
          heightIndex referenceHeight threshold bin ∈
        pullback.sourcePopularHeights heightIndex ∧
      pullback.sourcePopularRichCommonBinWitnessHeight
          heightIndex referenceHeight threshold bin ∈
        Set.Icc (-1 : ℝ) 1 ∧
      threshold ≤ pureWZ2FixedCommonBinSliceMass
        (pullback.standardSqrtSlabSourceRegion heightIndex)
        current.grain.globalGrains.slope referenceHeight (Real.sqrt rho)
        (pullback.sourcePopularRichCommonBinWitnessHeight
          heightIndex referenceHeight threshold bin) bin := by
  rw [sourcePopularRichCommonBinWitnessHeight, dif_pos hbin]
  exact Classical.choose_spec (Finset.mem_filter.mp hbin).2

/-- Family-free geometric bound for the number of integrated root-scale
labels. -/
theorem sourcePopularRichCommonBinLabels_card_le
    (heightIndex : ℤ) (referenceHeight : ℝ) (threshold : ENNReal) :
    ((pullback.sourcePopularRichCommonBinLabels
      heightIndex referenceHeight threshold).card : ENNReal) ≤
      ENNReal.ofReal (12 / Real.sqrt rho) := by
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hroot : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  let ambient : Finset ℤ := Finset.Icc
    (Int.floor ((-5 : ℝ) / Real.sqrt rho))
    (Int.floor ((5 : ℝ) / Real.sqrt rho))
  have hsubset :
      pullback.sourcePopularRichCommonBinLabels
        heightIndex referenceHeight threshold ⊆ ambient := by
    intro bin hbin
    have hoccupied := (Finset.mem_filter.mp hbin).1
    simpa [ambient, pureWZ2OccupiedCommonBins] using
      (Finset.mem_filter.mp hoccupied).1
  have hlowerUpper :
      Int.floor ((-5 : ℝ) / Real.sqrt rho) ≤
        Int.floor ((5 : ℝ) / Real.sqrt rho) + 1 := by
    have hreal : (-5 : ℝ) / Real.sqrt rho ≤ 5 / Real.sqrt rho :=
      div_le_div_of_nonneg_right (by norm_num) hroot.le
    have := Int.floor_mono hreal
    omega
  have hambientCard :
      (ambient.card : ℤ) =
        Int.floor ((5 : ℝ) / Real.sqrt rho) + 1 -
          Int.floor ((-5 : ℝ) / Real.sqrt rho) :=
    Int.card_Icc_of_le _ _ hlowerUpper
  have hcardReal :
      ((pullback.sourcePopularRichCommonBinLabels
        heightIndex referenceHeight threshold).card : ℝ) ≤
        12 / Real.sqrt rho := by
    have hcardAmbient :
        ((pullback.sourcePopularRichCommonBinLabels
          heightIndex referenceHeight threshold).card : ℝ) ≤
            (ambient.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    have hupper := Int.floor_le ((5 : ℝ) / Real.sqrt rho)
    have hlower := Int.lt_floor_add_one ((-5 : ℝ) / Real.sqrt rho)
    have hambientReal :
        (ambient.card : ℝ) =
          (Int.floor ((5 : ℝ) / Real.sqrt rho) : ℝ) + 1 -
            (Int.floor ((-5 : ℝ) / Real.sqrt rho) : ℝ) := by
      exact_mod_cast hambientCard
    rw [hambientReal] at hcardAmbient
    have hrootOne : Real.sqrt rho ≤ 1 :=
      Real.sqrt_le_one.mpr <| by
        rw [← pullback.rhoRequested_eq]
        exact rhoRequested.property.2
    have htwo : 2 ≤ 2 / Real.sqrt rho :=
      (le_div_iff₀ hroot).2 (by nlinarith)
    calc
      _ ≤ (Int.floor ((5 : ℝ) / Real.sqrt rho) : ℝ) + 1 -
          (Int.floor ((-5 : ℝ) / Real.sqrt rho) : ℝ) := hcardAmbient
      _ ≤ 5 / Real.sqrt rho + 2 - ((-5 : ℝ) / Real.sqrt rho) := by
        linarith
      _ = 10 / Real.sqrt rho + 2 := by ring
      _ ≤ 12 / Real.sqrt rho := by
        rw [show 12 / Real.sqrt rho =
          10 / Real.sqrt rho + 2 / Real.sqrt rho by ring]
        gcongr
  have henn := ENNReal.ofReal_mono hcardReal
  simpa using henn

/-- A rich side-`delta` bin meets at least `K` distinct side-`sqrt rho`
spatial cells at its source-popular witness height. -/
theorem sourcePopularRichCommonBinSpatialCells_card_lower
    (heightIndex : ℤ) (referenceHeight : ℝ)
    (threshold : ENNReal) (K : ℕ)
    (hK :
      (K : ENNReal) *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho ≤ threshold)
    {bin : ℤ}
    (hbin : bin ∈ pullback.sourcePopularRichCommonBinLabels
      heightIndex referenceHeight threshold) :
    K ≤ (pullback.sourcePopularRichCommonBinSpatialCells
      heightIndex referenceHeight threshold bin).card := by
  let height := pullback.sourcePopularRichCommonBinWitnessHeight
    heightIndex referenceHeight threshold bin
  let cells := pullback.sourcePopularRichCommonBinSpatialCells
    heightIndex referenceHeight threshold bin
  let cellWeight : WZ2PaperCellIndex → ENNReal := fun parent =>
    pureWZ2PreCommonBinSpatialCellSliceMassAtHeight
      (pullback.standardSqrtSlabSourceRegion heightIndex)
      current.grain.globalGrains.slope referenceHeight height
      (Real.sqrt rho) (Real.sqrt rho) bin parent
  let binMass :=
    pureWZ2FixedCommonBinSliceMass
      (pullback.standardSqrtSlabSourceRegion heightIndex)
      current.grain.globalGrains.slope referenceHeight
      (Real.sqrt rho) height bin
  let cellCap :=
    PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
      sigma inputLoss delta rho
  have hwitness := pullback.sourcePopularRichCommonBinWitnessHeight_spec
    heightIndex referenceHeight threshold hbin
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hdecomposition :
      binMass = ∑ parent ∈ cells, cellWeight parent := by
    simpa [binMass, cells, cellWeight, height,
      sourcePopularRichCommonBinSpatialCells] using
      pureWZ2PreCommonBin_sliceMassAtHeight_eq_sum_spatialCells
        (pullback.measurableSet_standardSqrtSlabSourceRegion heightIndex)
        current.grain.globalGrains.slope referenceHeight height
        (Real.sqrt_pos.mpr hrho) bin
        (fun point hpoint => by
          have hsource :=
            pullback.subshading.union_subset
              (pullback.standardSqrtSlabSourceRegion_subset_source
                heightIndex hpoint)
          exact norm_le_two_of_mem_paperShading hsource)
  have hcellUpper :
      ∀ parent ∈ cells, cellWeight parent ≤ cellCap := by
    intro parent _hparent
    have hdeltaRho : delta ≤ rho := by
      rw [← pullback.rhoRequested_eq]
      exact rhoRequested.property.1
    have hrhoRoot : rho ≤ Real.sqrt rho := by
      rw [Real.le_sqrt hrho.le hrho.le]
      have hrhoOne : rho ≤ 1 := by
        rw [← pullback.rhoRequested_eq]
        exact rhoRequested.property.2
      nlinarith
    have hsubset :
        wz1Lemma23PlanarSlice
            (pureWZ2FixedCommonBinRegion
                (pullback.standardSqrtSlabSourceRegion heightIndex)
                current.grain.globalGrains.slope referenceHeight
                (Real.sqrt rho) bin ∩
              wz1PaperGridCube (Real.sqrt rho) parent)
            height ⊆
          wz1Lemma23PlanarSlice
            (current.grain.shading.union ∩
              wz1PaperGridCube (Real.sqrt rho) parent)
            height := by
      intro point hpoint
      have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
      apply wz1Lemma23_mem_planarSlice_iff.mpr
      exact ⟨pullback.subshading.union_subset
        (pullback.standardSqrtSlabSourceRegion_subset_source
          heightIndex hlift.1.1), hlift.2⟩
    calc
      cellWeight parent ≤
          volume
            (wz1Lemma23PlanarSlice
              (current.grain.shading.union ∩
                wz1PaperGridCube (Real.sqrt rho) parent)
              height) := measure_mono hsubset
      _ ≤ cellCap := by
        simpa [cellCap,
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap] using
          current.grain.sourceCommonBinSpatialCellSliceBound
            hrho (hdeltaRho.trans hrhoRoot) parent height hwitness.2.1
  apply CommonBinRichSelection.cell_card_lower_of_rich
    cells cellWeight binMass threshold cellCap K
  · exact hwitness.2.2
  · exact le_of_eq hdecomposition
  · exact hcellUpper
  · simpa [cellCap] using hK
  · unfold cellCap
      PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
    have hdeltaLoss :
        0 < Kakeya.realRpowENN delta (-inputLoss) :=
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos current.grain.extremal.delta_pos _)
    have hdeltaSigma :
        0 < Kakeya.realRpowENN delta sigma :=
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos current.grain.extremal.delta_pos _)
    have hrhoPower :
        0 < Kakeya.realRpowENN rho (1 - sigma / 2) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hrho _)
    exact ENNReal.mul_pos
      (ENNReal.mul_pos
        (ENNReal.mul_pos (by norm_num) hdeltaLoss.ne').ne'
        hdeltaSigma.ne').ne'
      hrhoPower.ne'
  · unfold cellCap
      PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
      Kakeya.realRpowENN
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
        ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top

/-- Every witnessing side-`sqrt rho` cell of a rich integrated label is a
genuine second-cover parent in the same standard slab. -/
theorem sourcePopularRichCommonBinSpatialCells_subset_standardParents
    (heightIndex : ℤ) (referenceHeight : ℝ)
    (threshold : ENNReal) (bin : ℤ) :
    pullback.sourcePopularRichCommonBinSpatialCells
        heightIndex referenceHeight threshold bin ⊆
      pullback.standardSqrtSlabParents heightIndex := by
  intro parent hparent
  let witnessHeight :=
    pullback.sourcePopularRichCommonBinWitnessHeight
      heightIndex referenceHeight threshold bin
  rw [sourcePopularRichCommonBinSpatialCells,
    pureWZ2PreCommonBinSpatialCellsAtHeight, Finset.mem_filter] at hparent
  rcases hparent.2 with ⟨planarPoint, hplanarPoint⟩
  have hlift := wz1Lemma23_mem_planarSlice_iff.mp hplanarPoint
  let point : Point3 :=
    point3 (planarPoint 0) (planarPoint 1) witnessHeight
  have hpointSlab :
      point ∈ pullback.standardSqrtSlabSourceRegion heightIndex := by
    simpa [point, witnessHeight] using hlift.1.1
  have hpointParent :
      point ∈ wz1PaperGridCube (Real.sqrt rho) parent := by
    simpa [point, witnessHeight] using hlift.2
  change point ∈ pullback.shading.union ∩
      pureWZ2Node05RetainedCellRegion rho
        (pullback.standardSqrtSlabRhoCells heightIndex) at hpointSlab
  rcases Set.mem_iUnion₂.mp hpointSlab.2 with
    ⟨rhoCell, hrhoCell, hpointRhoCell⟩
  have hpointCanonical :
      point ∈ wz1PaperGridCube (Real.sqrt rho)
        (pullback.standardSecondParent rhoCell) := by
    have hraw :=
      pullback.standardSqrtSlabRhoCell_subset_parent
        hrhoCell hpointRhoCell
    simpa only [pullback.sqrtRequested_eq] using hraw
  have hparentEq :
      pullback.standardSecondParent rhoCell = parent :=
    ((mem_wz1PaperGridCube (Real.sqrt rho)
      (pullback.standardSecondParent rhoCell) point).mp
        hpointCanonical).symm.trans
      ((mem_wz1PaperGridCube (Real.sqrt rho) parent point).mp hpointParent)
  exact Finset.mem_image.mpr ⟨rhoCell, hrhoCell, hparentEq⟩

/-- One side-`sqrt rho` spatial parent is used by at most five distinct
integrated common-bin labels. -/
theorem sourcePopularRichCommonBin_cellDegree_le_five
    (heightIndex : ℤ) (referenceHeight : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (threshold : ENNReal) (parent : WZ2PaperCellIndex) :
    ((pullback.sourcePopularRichCommonBinLabels
        heightIndex referenceHeight threshold).filter fun bin =>
      parent ∈ pullback.sourcePopularRichCommonBinSpatialCells
        heightIndex referenceHeight threshold bin).card ≤ 5 := by
  let bins := pullback.sourcePopularRichCommonBinLabels
    heightIndex referenceHeight threshold
  have hsubset :
      (bins.filter fun bin =>
          parent ∈ pullback.sourcePopularRichCommonBinSpatialCells
            heightIndex referenceHeight threshold bin) ⊆
        pureWZ2CommonBinsMeetingSpatialCell bins
          current.grain.globalGrains.slope referenceHeight
          (Real.sqrt rho) parent := by
    intro bin hbin
    rw [Finset.mem_filter] at hbin
    rw [pureWZ2CommonBinsMeetingSpatialCell, Finset.mem_filter]
    refine ⟨hbin.1, ?_⟩
    have hactive := hbin.2
    rw [sourcePopularRichCommonBinSpatialCells,
      pureWZ2PreCommonBinSpatialCellsAtHeight, Finset.mem_filter] at hactive
    rcases hactive.2 with ⟨point, hpoint⟩
    have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
    have hregion := hlift.1
    rw [pureWZ2FixedCommonBinRegion] at hregion
    exact ⟨point3 (point 0) (point 1)
        (pullback.sourcePopularRichCommonBinWitnessHeight
          heightIndex referenceHeight threshold bin),
      hlift.2, hregion.2⟩
  calc
    ((pullback.sourcePopularRichCommonBinLabels
          heightIndex referenceHeight threshold).filter fun bin =>
        parent ∈ pullback.sourcePopularRichCommonBinSpatialCells
          heightIndex referenceHeight threshold bin).card =
        (bins.filter fun bin =>
          parent ∈ pullback.sourcePopularRichCommonBinSpatialCells
            heightIndex referenceHeight threshold bin).card := by rfl
    _ ≤ (pureWZ2CommonBinsMeetingSpatialCell bins
          current.grain.globalGrains.slope referenceHeight
          (Real.sqrt rho) parent).card :=
      Finset.card_le_card hsubset
    _ ≤ 5 :=
      commonBinsMeetingSpatialCell_card_le_five
        (Real.sqrt_pos.mpr <| by
          rw [← pullback.rhoRequested_eq]
          exact twoScale.first.publicSticky.coarse_extremal.delta_pos)
        bins current.grain.globalGrains.slope referenceHeight
        (current.grain.globalGrains.slope_bound referenceHeight hreference)
        parent

/-- V4-native distinct-label incidence on the full genuine coarse carrier:
`|R| * K * w_s ≤ 5 * G_S`. -/
theorem sourcePopularRichCommonBin_incidence
    (heightIndex : ℤ) (referenceHeight : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (threshold : ENNReal) (K : ℕ)
    (hK :
      (K : ENNReal) *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho ≤ threshold) :
    ((pullback.sourcePopularRichCommonBinLabels
        heightIndex referenceHeight threshold).card : ENNReal) * K *
        twoScale.secondBalancedCover.cellMass ≤
      5 * volume (pullback.standardSqrtSlabCoarseRegion heightIndex) := by
  let bins := pullback.sourcePopularRichCommonBinLabels
    heightIndex referenceHeight threshold
  let cells : ℤ → Finset WZ2PaperCellIndex :=
    pullback.sourcePopularRichCommonBinSpatialCells
      heightIndex referenceHeight threshold
  apply CommonBinDistinctIncidence.card_mul_cellMass_le_degree_mul_totalMass
    bins cells K 5 twoScale.secondBalancedCover.cellMass
    (volume (pullback.standardSqrtSlabCoarseRegion heightIndex))
  · intro bin hbin
    exact pullback.sourcePopularRichCommonBinSpatialCells_card_lower
      heightIndex referenceHeight threshold K hK hbin
  · intro parent _hparent
    simpa [bins, cells] using
      pullback.sourcePopularRichCommonBin_cellDegree_le_five
        heightIndex referenceHeight hreference threshold parent
  · have hsubset :
        (@Finset.biUnion ℤ WZ2PaperCellIndex
          (fun first second => Classical.propDecidable (first = second))
          bins cells) ⊆ pullback.standardSqrtSlabParents heightIndex := by
      intro parent hparent
      rcases
          (@Finset.mem_biUnion ℤ WZ2PaperCellIndex bins cells
            (fun first second => Classical.propDecidable (first = second))
            parent).mp hparent with ⟨bin, _hbin, hparent⟩
      exact
        pullback.sourcePopularRichCommonBinSpatialCells_subset_standardParents
          heightIndex referenceHeight threshold bin hparent
    have hcard :
        ((@Finset.biUnion ℤ WZ2PaperCellIndex
          (fun first second => Classical.propDecidable (first = second))
          bins cells).card : ENNReal) ≤
            (pullback.standardSqrtSlabParents heightIndex).card := by
      exact_mod_cast Finset.card_le_card hsubset
    calc
      ((@Finset.biUnion ℤ WZ2PaperCellIndex
          (fun first second => Classical.propDecidable (first = second))
          bins cells).card : ENNReal) *
          twoScale.secondBalancedCover.cellMass ≤
        ((pullback.standardSqrtSlabParents heightIndex).card : ENNReal) *
          twoScale.secondBalancedCover.cellMass := by gcongr
      _ = volume (pullback.standardSqrtSlabCoarseRegion heightIndex) :=
        pullback.standardSqrtSlab_parentMass_eq_coarseVolume heightIndex

/-- Participating first-cover side-`rho` cells in the integrated bin. -/
def sourcePopularFixedBinRhoCells
    (heightIndex : ℤ) (referenceHeight : ℝ) (bin : ℤ) :
    Finset WZ2PaperCellIndex :=
  (pullback.standardSqrtSlabRhoCells heightIndex).filter fun cell =>
    (pullback.sourcePopularFixedBinHeightRegion
        heightIndex referenceHeight bin ∩
      wz1PaperGridCube rho cell).Nonempty

/-- Complete side-`rho` cell envelope of the integrated fixed-bin source. -/
def sourcePopularFixedBinWholeCellEnvelope
    (heightIndex : ℤ) (referenceHeight : ℝ) (bin : ℤ) : Set Point3 :=
  pureWZ2Node05RetainedCellRegion rho
    (pullback.sourcePopularFixedBinRhoCells
      heightIndex referenceHeight bin)

theorem sourcePopularHeight_mem_paperRange
    {heightIndex : ℤ} {height : ℝ}
    (hheightIndex : heightIndex ∈ pullback.standardSqrtSlabIndices)
    (hheight : height ∈ pullback.sourcePopularHeights heightIndex) :
    height ∈ Set.Icc (-1 : ℝ) 1 := by
  have hthresholdPos :
      0 < pureWZ2SourceCommonBinPopularThreshold
        (pullback.standardSqrtSlabSourceRegion heightIndex)
        (Real.sqrt rho) := by
    unfold pureWZ2SourceCommonBinPopularThreshold
      pureWZ2CommonBinPopularThreshold
    exact ENNReal.div_pos
      (ENNReal.div_pos
        (pullback.standardSqrtSlabSourceRegion_volume_pos
          hheightIndex).ne'
        (by norm_num)).ne'
      ENNReal.ofReal_ne_top
  have hslicePos :
      0 < pureWZ2SourceCommonBinSliceMass
        (pullback.standardSqrtSlabSourceRegion heightIndex) height :=
    hthresholdPos.trans_le hheight.2
  rcases nonempty_of_measure_ne_zero hslicePos.ne' with
    ⟨planarPoint, hplanarPoint⟩
  have hlift := wz1Lemma23_mem_planarSlice_iff.mp hplanarPoint
  have hsource :=
    pullback.standardSqrtSlabSourceRegion_subset_source heightIndex hlift
  have hbox := shading_union_subset_axisBox hsource
  simpa [point3, Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2

theorem sourcePopularHeights_close
    {heightIndex : ℤ} {first second : ℝ}
    (hfirst : first ∈ pullback.sourcePopularHeights heightIndex)
    (hsecond : second ∈ pullback.sourcePopularHeights heightIndex) :
    |first - second| ≤ Real.sqrt rho := by
  rw [abs_le]
  constructor <;>
    linarith [hfirst.1.1, hfirst.1.2, hsecond.1.1, hsecond.1.2]

private theorem sourcePopularSlice_y_abs_le_one
    (heightIndex : ℤ) (height : ℝ) :
    ∀ point ∈ horizontalSlice
        (pullback.standardSqrtSlabSourceRegion heightIndex) height,
      |point (1 : Fin 3)| ≤ 1 := by
  intro point hpoint
  have hsource :=
    pullback.standardSqrtSlabSourceRegion_subset_source heightIndex hpoint.1
  have hbox := shading_union_subset_axisBox hsource
  simpa [Kakeya.Streamlined.axisBox] using hbox.2.1

private theorem sourcePopularSlice_projection_bounded
    (heightIndex : ℤ) (height : ℝ)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1) :
    scalarProjection
        (globalGrainDirection (current.grain.globalGrains.slope height))
        (horizontalSlice
          (pullback.standardSqrtSlabSourceRegion heightIndex) height) ⊆
      Set.Icc (-4 : ℝ) 4 := by
  rintro value ⟨point, hpoint, rfl⟩
  have hsource :=
    pullback.standardSqrtSlabSourceRegion_subset_source heightIndex hpoint.1
  have hbox := shading_union_subset_axisBox hsource
  have hslope := current.grain.globalGrains.slope_bound height hheight
  have hformula :
      inner ℝ point
          (globalGrainDirection
            (current.grain.globalGrains.slope height)) =
        point 0 + current.grain.globalGrains.slope height * point 1 := by
    simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
  have habs :
      |inner ℝ point
          (globalGrainDirection
            (current.grain.globalGrains.slope height))| ≤ 4 := by
    rw [hformula]
    calc
      |point 0 + current.grain.globalGrains.slope height * point 1| ≤
          |point 0| +
            |current.grain.globalGrains.slope height| * |point 1| := by
        simpa [abs_mul] using abs_add_le (point 0)
          (current.grain.globalGrains.slope height * point 1)
      _ ≤ 1 + 3 * 1 := by
        gcongr
        · simpa [Kakeya.Streamlined.axisBox] using hbox.1
        · simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
      _ = 4 := by norm_num
  exact abs_le.mp habs

private theorem sourcePopularSlice_ad_root
    (heightIndex : ℤ) (height : ℝ)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1) :
    IsADSet1
      (scalarProjection
        (globalGrainDirection (current.grain.globalGrains.slope height))
        (horizontalSlice
          (pullback.standardSqrtSlabSourceRegion heightIndex) height))
      (Real.sqrt rho) (1 - sigma)
      (2 * Kakeya.realRpowENN delta (-inputLoss)) := by
  have hpaper : PureWZ2PaperADSet1
      (scalarProjection
        (globalGrainDirection (current.grain.globalGrains.slope height))
        (horizontalSlice
          (pullback.standardSqrtSlabSourceRegion heightIndex) height))
      delta (1 - sigma) (Kakeya.realRpowENN delta (-inputLoss)) := by
    apply (current.grain.globalGrains.global_ad height hheight).mono
    rintro value ⟨point, hpoint, rfl⟩
    exact ⟨point,
      ⟨pullback.subshading.union_subset
        (pullback.standardSqrtSlabSourceRegion_subset_source
          heightIndex hpoint.1), hpoint.2⟩, rfl⟩
  have hdelta := hpaper.toIsADSet1
    (pullback.sourcePopularSlice_projection_bounded
      heightIndex height hheight)
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hdeltaRho : delta ≤ rho := by
    rw [← pullback.rhoRequested_eq]
    exact rhoRequested.property.1
  have hrhoSqrt : rho ≤ Real.sqrt rho := by
    rw [Real.le_sqrt hrho.le hrho.le]
    have hrhoOne : rho ≤ 1 := by
      rw [← pullback.rhoRequested_eq]
      exact rhoRequested.property.2
    nlinarith
  exact hdelta.coarsen_scale (Real.sqrt_pos.mpr hrho)
    (hdeltaRho.trans hrhoSqrt)
    (Real.sqrt_le_one.mpr
      (by rw [← pullback.rhoRequested_eq]; exact rhoRequested.property.2))

theorem sourcePopularCommonBinSlice_occupiedBound
    (heightIndex : ℤ) (referenceHeight height : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1)
    (hclose : |height - referenceHeight| ≤ Real.sqrt rho) :
    ((pureWZ2OccupiedCommonBins
      (horizontalSlice
        (pullback.standardSqrtSlabSourceRegion heightIndex) height)
      current.grain.globalGrains.slope referenceHeight
      (Real.sqrt rho)).card : ENNReal) ≤
      264 * Kakeya.realRpowENN delta (-inputLoss) *
        Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) := by
  have hbound := pureWZ2_fixed_common_bin_occupied_bound
    (horizontalSlice
      (pullback.standardSqrtSlabSourceRegion heightIndex) height)
    current.grain.globalGrains.slope
    current.grain.globalGrains.slope_lipschitz height referenceHeight
    hheight hreference hclose
    (pullback.sourcePopularSlice_y_abs_le_one heightIndex height)
    (pullback.sourcePopularSlice_ad_root heightIndex height hheight)
    (Real.sqrt_le_one.mpr
      (by rw [← pullback.rhoRequested_eq]; exact rhoRequested.property.2))
  calc
    _ ≤ 132 * (2 * Kakeya.realRpowENN delta (-inputLoss)) *
        Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) := hbound
    _ = _ := by ring

theorem sourcePopularCommonBinSliceMass_sum
    (heightIndex : ℤ) (referenceHeight height : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1)
    (hclose : |height - referenceHeight| ≤ Real.sqrt rho) :
    pureWZ2SourceCommonBinSliceMass
        (pullback.standardSqrtSlabSourceRegion heightIndex) height =
      ∑ bin ∈ pureWZ2OccupiedCommonBins
          (horizontalSlice
            (pullback.standardSqrtSlabSourceRegion heightIndex) height)
          current.grain.globalGrains.slope referenceHeight (Real.sqrt rho),
        pureWZ2FixedCommonBinSliceMass
          (pullback.standardSqrtSlabSourceRegion heightIndex)
          current.grain.globalGrains.slope referenceHeight
          (Real.sqrt rho) height bin := by
  simpa [pureWZ2SourceCommonBinSliceMass] using
    pureWZ2_fixed_common_bin_sliceMass_sum
      (pullback.measurableSet_standardSqrtSlabSourceRegion heightIndex)
      current.grain.globalGrains.slope referenceHeight
      (Real.sqrt rho) height
      (pureWZ2OccupiedCommonBins
        (horizontalSlice
          (pullback.standardSqrtSlabSourceRegion heightIndex) height)
        current.grain.globalGrains.slope referenceHeight (Real.sqrt rho))
      (fun point hpoint =>
        pureWZ2_fixed_common_bin_mem
          (horizontalSlice
            (pullback.standardSqrtSlabSourceRegion heightIndex) height)
          current.grain.globalGrains.slope
          current.grain.globalGrains.slope_lipschitz height referenceHeight
          hheight hreference hclose
          (pullback.sourcePopularSlice_y_abs_le_one heightIndex height)
          (pullback.sourcePopularSlice_ad_root heightIndex height hheight)
          (Real.sqrt_le_one.mpr
            (by rw [← pullback.rhoRequested_eq];
                exact rhoRequested.property.2))
          hpoint)

private theorem sourcePopularCommonBinSliceMass_ne_top
    (heightIndex : ℤ) (height : ℝ) :
    pureWZ2SourceCommonBinSliceMass
      (pullback.standardSqrtSlabSourceRegion heightIndex) height ≠ ⊤ := by
  have hsliceBall :
      wz1Lemma23PlanarSlice
          (pullback.standardSqrtSlabSourceRegion heightIndex) height ⊆
        Metric.closedBall (0 : Point2) 2 := by
    intro point hpoint
    have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
    have hsource :=
      pullback.subshading.union_subset
        (pullback.standardSqrtSlabSourceRegion_subset_source
          heightIndex hlift)
    have hbox := shading_union_subset_axisBox hsource
    have h0 : |point 0| ≤ 1 := by
      simpa [point3, Kakeya.Streamlined.axisBox] using hbox.1
    have h1 : |point 1| ≤ 1 := by
      simpa [point3, Kakeya.Streamlined.axisBox] using hbox.2.1
    rw [Metric.mem_closedBall, dist_zero_right]
    have hsq : ‖point‖ ^ 2 = point 0 ^ 2 + point 1 ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Fin.sum_univ_two]
    have h0sq : point 0 ^ 2 ≤ 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (point 0)]
    have h1sq : point 1 ^ 2 ≤ 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (point 1)]
    nlinarith [norm_nonneg point]
  exact ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
    (measure_mono hsliceBall)

theorem measurable_sourcePopularFixedCommonBinSliceMass
    (heightIndex : ℤ) (referenceHeight : ℝ) (bin : ℤ) :
    Measurable (fun height : ℝ =>
      pureWZ2FixedCommonBinSliceMass
        (pullback.standardSqrtSlabSourceRegion heightIndex)
        current.grain.globalGrains.slope referenceHeight
        (Real.sqrt rho) height bin) :=
  measurable_volume_wz1Lemma23PlanarSlice
    (pureWZ2FixedCommonBinRegion
      (pullback.standardSqrtSlabSourceRegion heightIndex)
      current.grain.globalGrains.slope referenceHeight
      (Real.sqrt rho) bin)
    (measurableSet_pureWZ2FixedCommonBinRegion
      (pullback.measurableSet_standardSqrtSlabSourceRegion heightIndex)
      current.grain.globalGrains.slope referenceHeight
      (Real.sqrt rho) bin)

/-- The whole source slab is controlled by the fixed-bin masses integrated
over `Z_S`; no single-slice mass is substituted for this weighted estimate. -/
theorem sourcePopularRichCommonBin_integratedMass
    (heightIndex :
      {heightIndex // heightIndex ∈ pullback.standardSqrtSlabIndices})
    (referenceHeight : ℝ)
    (hreference :
      referenceHeight ∈ pullback.sourcePopularHeights heightIndex.1)
    (B₀ threshold : ENNReal)
    (hB₀ :
      264 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hthresholdBudget :
      2 * B₀ * threshold ≤
        pureWZ2SourceCommonBinPopularThreshold
          (pullback.standardSqrtSlabSourceRegion heightIndex.1)
          (Real.sqrt rho)) :
    volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) ≤
      4 * ∑ bin ∈ pullback.sourcePopularRichCommonBinLabels
          heightIndex.1 referenceHeight threshold,
        pullback.sourcePopularIntegratedBinMass
          heightIndex.1 referenceHeight bin := by
  let E := pullback.standardSqrtSlabSourceRegion heightIndex.1
  let heights := pullback.sourcePopularHeights heightIndex.1
  let richLabels := pullback.sourcePopularRichCommonBinLabels
    heightIndex.1 referenceHeight threshold
  let sliceMass : ℝ → ENNReal :=
    pureWZ2SourceCommonBinSliceMass E
  let binMass : ℝ → ℤ → ENNReal := fun height bin =>
    pureWZ2FixedCommonBinSliceMass E
      current.grain.globalGrains.slope referenceHeight
      (Real.sqrt rho) height bin
  have hreferenceRange :=
    pullback.sourcePopularHeight_mem_paperRange heightIndex.2 hreference
  have hpointwise : ∀ height ∈ heights,
      sliceMass height ≤ 2 * ∑ bin ∈ richLabels, binMass height bin := by
    intro height hheight
    have hheightOriginal :
        height ∈ pullback.sourcePopularHeights heightIndex.1 := by
      simpa [heights] using hheight
    have hheightRange :=
      pullback.sourcePopularHeight_mem_paperRange
        heightIndex.2 hheightOriginal
    have hclose :=
      pullback.sourcePopularHeights_close hheightOriginal hreference
    let bins := pureWZ2OccupiedCommonBins
      (horizontalSlice E height) current.grain.globalGrains.slope
      referenceHeight (Real.sqrt rho)
    have htotalEq :
        sliceMass height = ∑ bin ∈ bins, binMass height bin := by
      simpa [bins, sliceMass, binMass, E] using
        pullback.sourcePopularCommonBinSliceMass_sum
          heightIndex.1 referenceHeight height hreferenceRange
          hheightRange hclose
    have hcard : (bins.card : ENNReal) ≤ B₀ := by
      simpa [bins, E] using
        (pullback.sourcePopularCommonBinSlice_occupiedBound
          heightIndex.1 referenceHeight height hreferenceRange
          hheightRange hclose).trans hB₀
    have hpoor :
        2 * ((bins.card : ENNReal) * threshold) ≤ sliceMass height := by
      calc
        _ ≤ 2 * (B₀ * threshold) := by gcongr
        _ = 2 * B₀ * threshold := by ring
        _ ≤ pureWZ2SourceCommonBinPopularThreshold E
            (Real.sqrt rho) := by simpa [E] using hthresholdBudget
        _ ≤ pureWZ2SourceCommonBinSliceMass E height := hheightOriginal.2
        _ = sliceMass height := rfl
    have hretained := CommonBinRichSelection.total_le_two_mul_rich_sum
      bins (binMass height) threshold (sliceMass height) htotalEq
      (by
        simpa [sliceMass, E] using
          pullback.sourcePopularCommonBinSliceMass_ne_top
            heightIndex.1 height)
      hpoor
    have hsubset : CommonBinRichSelection.richBins
        bins (binMass height) threshold ⊆ richLabels := by
      intro bin hbin
      have hbinData := Finset.mem_filter.mp hbin
      have hambient : bin ∈ pureWZ2OccupiedCommonBins E
          current.grain.globalGrains.slope referenceHeight
          (Real.sqrt rho) := by
        have hbinOccupied := hbinData.1
        dsimp only [bins] at hbinOccupied
        rw [pureWZ2OccupiedCommonBins, Finset.mem_filter] at hbinOccupied ⊢
        refine ⟨hbinOccupied.1, ?_⟩
        rcases hbinOccupied.2 with ⟨point, hpoint, hlabel⟩
        exact ⟨point, hpoint.1, hlabel⟩
      change bin ∈ pullback.sourcePopularRichCommonBinLabels
        heightIndex.1 referenceHeight threshold
      rw [sourcePopularRichCommonBinLabels, Finset.mem_filter]
      exact ⟨hambient, height, hheight, hheightRange, hbinData.2⟩
    exact hretained.trans <| mul_le_mul_right
      (Finset.sum_le_sum_of_subset hsubset) 2
  have hheightsMeas : MeasurableSet heights := by
    dsimp only [heights]
    exact measurableSet_pureWZ2SourceCommonBinPopularHeights E
      (pullback.measurableSet_standardSqrtSlabSourceRegion heightIndex.1)
      (pullback.sourcePopularSlabLeft heightIndex.1) (Real.sqrt rho)
  have hbinMassMeas : ∀ bin : ℤ,
      Measurable (fun height => binMass height bin) := by
    intro bin
    simpa [binMass, E] using
      pullback.measurable_sourcePopularFixedCommonBinSliceMass
        heightIndex.1 referenceHeight bin
  have hintegratedPointwise :
      (∫⁻ height in heights, sliceMass height) ≤
        2 * ∫⁻ height in heights,
          ∑ bin ∈ richLabels, binMass height bin := by
    calc
      _ ≤ ∫⁻ height in heights,
          2 * ∑ bin ∈ richLabels, binMass height bin :=
        setLIntegral_mono' hheightsMeas hpointwise
      _ = _ := MeasureTheory.lintegral_const_mul 2
        (Finset.measurable_sum richLabels fun bin _ => hbinMassMeas bin)
  have hsumIntegral :
      (∫⁻ height in heights,
        ∑ bin ∈ richLabels, binMass height bin) =
      ∑ bin ∈ richLabels,
        pullback.sourcePopularIntegratedBinMass
          heightIndex.1 referenceHeight bin := by
    rw [MeasureTheory.lintegral_finsetSum richLabels]
    · rfl
    · intro bin _
      exact hbinMassMeas bin
  have hpopularHalf :
      volume E / 2 ≤ ∫⁻ height in heights, sliceMass height := by
    simpa [E, heights, sliceMass] using
      pullback.sourcePopularRegion_half_volume heightIndex.1
      |>.trans_eq (pullback.sourcePopularRegion_volume heightIndex.1)
  calc
    volume E = volume E / 2 + volume E / 2 :=
      (ENNReal.add_halves _).symm
    _ ≤ (∫⁻ height in heights, sliceMass height) +
        ∫⁻ height in heights, sliceMass height := by gcongr
    _ = 2 * ∫⁻ height in heights, sliceMass height := by ring
    _ ≤ 2 * (2 * ∫⁻ height in heights,
        ∑ bin ∈ richLabels, binMass height bin) := by gcongr
    _ = 4 * ∑ bin ∈ richLabels,
        pullback.sourcePopularIntegratedBinMass
          heightIndex.1 referenceHeight bin := by rw [hsumIntegral]; ring
    _ = _ := rfl

/-- Select one fixed label only after the integrated `Z_S` mass has been
formed.  The selected label retains its exact source-average receipt. -/
theorem exists_sourcePopularIntegratedCommonBin
    (heightIndex :
      {heightIndex // heightIndex ∈ pullback.standardSqrtSlabIndices})
    (referenceHeight : ℝ)
    (hreference :
      referenceHeight ∈ pullback.sourcePopularHeights heightIndex.1)
    (B₀ threshold : ENNReal)
    (hB₀ :
      264 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hthresholdBudget :
      2 * B₀ * threshold ≤
        pureWZ2SourceCommonBinPopularThreshold
          (pullback.standardSqrtSlabSourceRegion heightIndex.1)
          (Real.sqrt rho)) :
    ∃ bin ∈ pullback.sourcePopularRichCommonBinLabels
        heightIndex.1 referenceHeight threshold,
      volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) ≤
        4 * ((pullback.sourcePopularRichCommonBinLabels
          heightIndex.1 referenceHeight threshold).card : ENNReal) *
          pullback.sourcePopularIntegratedBinMass
            heightIndex.1 referenceHeight bin := by
  have hretained := pullback.sourcePopularRichCommonBin_integratedMass
    heightIndex referenceHeight hreference B₀ threshold hB₀ hthresholdBudget
  exact CommonBinIntegratedAveraging.exists_label_of_total_le_sum
    (pullback.sourcePopularRichCommonBinLabels
      heightIndex.1 referenceHeight threshold)
    (pullback.sourcePopularIntegratedBinMass
      heightIndex.1 referenceHeight)
    (volume (pullback.standardSqrtSlabSourceRegion heightIndex.1)) 4
    (pullback.standardSqrtSlabSourceRegion_volume_pos heightIndex.2)
    hretained

theorem measurableSet_sourcePopularFixedBinHeightRegion
    (heightIndex : ℤ) (referenceHeight : ℝ) (bin : ℤ) :
    MeasurableSet
      (pullback.sourcePopularFixedBinHeightRegion
        heightIndex referenceHeight bin) := by
  apply
    (measurableSet_pureWZ2FixedCommonBinRegion
      (pullback.measurableSet_standardSqrtSlabSourceRegion heightIndex)
      current.grain.globalGrains.slope referenceHeight
      (Real.sqrt rho) bin).inter
  exact
    (measurableSet_pureWZ2SourceCommonBinPopularHeights
      (pullback.standardSqrtSlabSourceRegion heightIndex)
      (pullback.measurableSet_standardSqrtSlabSourceRegion heightIndex)
      (pullback.sourcePopularSlabLeft heightIndex)
      (Real.sqrt rho)).preimage (by fun_prop)

theorem sourcePopularFixedBinHeightRegion_volume
    (heightIndex : ℤ) (referenceHeight : ℝ) (bin : ℤ) :
    volume (pullback.sourcePopularFixedBinHeightRegion
        heightIndex referenceHeight bin) =
      pullback.sourcePopularIntegratedBinMass
        heightIndex referenceHeight bin := by
  let fixedRegion :=
    pureWZ2FixedCommonBinRegion
      (pullback.standardSqrtSlabSourceRegion heightIndex)
      current.grain.globalGrains.slope referenceHeight
      (Real.sqrt rho) bin
  let heights := pullback.sourcePopularHeights heightIndex
  let restricted :=
    pullback.sourcePopularFixedBinHeightRegion
      heightIndex referenceHeight bin
  have hheights : MeasurableSet heights :=
    measurableSet_pureWZ2SourceCommonBinPopularHeights
      (pullback.standardSqrtSlabSourceRegion heightIndex)
      (pullback.measurableSet_standardSqrtSlabSourceRegion heightIndex)
      (pullback.sourcePopularSlabLeft heightIndex) (Real.sqrt rho)
  have hslice : ∀ height : ℝ,
      wz1Lemma23PlanarSlice restricted height =
        if height ∈ heights then
          wz1Lemma23PlanarSlice fixedRegion height
        else ∅ := by
    intro height
    by_cases hheight : height ∈ heights
    · rw [if_pos hheight]
      ext point
      simp only [wz1Lemma23_mem_planarSlice_iff]
      constructor
      · exact fun hpoint => hpoint.1
      · intro hpoint
        exact ⟨hpoint, by simpa [point3] using hheight⟩
    · rw [if_neg hheight]
      ext point
      simp only [Set.notMem_empty, iff_false]
      rw [wz1Lemma23_mem_planarSlice_iff]
      exact fun hpoint => hheight (by simpa [point3] using hpoint.2)
  rw [wz1_lemma23_volume_eq_lintegral_planarSlice restricted
    (pullback.measurableSet_sourcePopularFixedBinHeightRegion
      heightIndex referenceHeight bin)]
  change
    (∫⁻ height : ℝ,
      volume (wz1Lemma23PlanarSlice restricted height)) =
    ∫⁻ height in heights,
      volume (wz1Lemma23PlanarSlice fixedRegion height)
  rw [← lintegral_indicator hheights]
  apply lintegral_congr
  intro height
  rw [hslice height]
  by_cases hheight : height ∈ heights
  · simp [hheight, fixedRegion, heights]
  · simp [hheight]

theorem sourcePopularFixedBinWholeCellEnvelope_volume
    (heightIndex : ℤ) (referenceHeight : ℝ) (bin : ℤ) :
    volume (pullback.sourcePopularFixedBinWholeCellEnvelope
        heightIndex referenceHeight bin) =
      ((pullback.sourcePopularFixedBinRhoCells
        heightIndex referenceHeight bin).card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
  unfold sourcePopularFixedBinWholeCellEnvelope
    pureWZ2Node05RetainedCellRegion
  exact wz1PaperGridCube_volume_biUnion
    (by
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos) _

end PureWZ2Node05V4RichTwoScaleCellPullbackData

end Kakeya.Assouad

end
