import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSourcePopularHeights
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinStandardSlabSecondCoverMass
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma18SpatialSelfCenteredCover
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalProjectionHeavyFiberInSource
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23FullGrainNormalBound
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalGraphExtension

/-!
# Proposition 6.4 local grains before common-bin selection

This module stops at Step 2 of WZ1 Lemma 5.3.  Starting from the two balanced
covers of WZ1 Lemma 5.4, it pulls every selected side-`sqrt rho` spatial cube
back to the same final `delta`-source shading.  Its source mass is obtained
from the second cover's `cellMass` and the first cover's exact cell identity.
The almost-full local projection fiber and its normal use only the P1 source
shading and P1 plane map.

No common-bin, four-cycle, or `richParents K children` object is imported or
constructed here.  In particular, the second-stage coarse shading is not an
AD carrier.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

attribute [local instance] Classical.propDecidable

namespace PureWZ2Node05V4RichTwoScaleCellPullbackData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
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

/-- The selected side-`rho` cells whose canonical second-cover parent is one
fixed side-`sqrt rho` spatial cube. -/
def preCommonBinRhoCells
    (parent : ℤ × ℤ × ℤ) : Finset (ℤ × ℤ × ℤ) :=
  pullback.selectedCells.filter fun cell =>
    pullback.standardSecondParent cell = parent

theorem preCommonBinRhoCells_subset
    (parent : ℤ × ℤ × ℤ) :
    pullback.preCommonBinRhoCells parent ⊆ pullback.selectedCells :=
  Finset.filter_subset _ _

/-- The exact final-`delta` source pullback of one side-`sqrt rho` cube. -/
def preCommonBinFinePullback
    (parent : ℤ × ℤ × ℤ) : Set Point3 :=
  pullback.selectedRhoCellsSourceRegion
    (pullback.preCommonBinRhoCells parent)

/-- The corresponding union of complete side-`rho` cells in the second
refined shading. -/
def preCommonBinCoarseRegion
    (parent : ℤ × ℤ × ℤ) : Set Point3 :=
  pullback.selectedRhoCellsCoarseRegion
    (pullback.preCommonBinRhoCells parent)

theorem preCommonBinCoarseRegion_eq_parent
    {parent : ℤ × ℤ × ℤ} :
    pullback.preCommonBinCoarseRegion parent =
      twoScale.fine.refined.union ∩
        wz1PaperGridCube sqrtRequested.1 parent := by
  have hrhoRequested : 0 < rhoRequested.1 :=
    twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact hrhoRequested
  ext point
  constructor
  · intro hpoint
    change point ∈ twoScale.fine.refined.union ∩
      wz2RetainedCellsUnion rho
        (pullback.preCommonBinRhoCells parent) at hpoint
    rcases Set.mem_iUnion₂.mp (by
      rw [wz2RetainedCellsUnion] at hpoint
      exact hpoint.2) with
      ⟨cell, hcell, hpointCell⟩
    have hcellData := Finset.mem_filter.mp hcell
    have hpointParent :
        point ∈ wz1PaperGridCube sqrtRequested.1
          (pullback.standardSecondParent cell) :=
      pullback.standardSecondParent_cell_subset hcellData.1 hpointCell
    exact ⟨hpoint.1, by simpa [hcellData.2] using hpointParent⟩
  · intro hpoint
    rcases hpoint.1 with ⟨index, hindex⟩
    let cell := wz1PaperGridIndex rhoRequested.1 point
    have hpointCellRequested :
        point ∈ wz1PaperGridCube rhoRequested.1 cell :=
      (mem_wz1PaperGridCube _ _ _).mpr rfl
    have hpointCell : point ∈ wz1PaperGridCube rho cell := by
      simpa only [← pullback.rhoRequested_eq] using hpointCellRequested
    have hcellActive :
        cell ∈ wz1PaperActiveCells twoScale.fine.refined
          hrhoRequested := by
      rw [mem_wz1PaperActiveCells]
      exact ⟨by
        apply paper_point_gridIndex_in_window hrhoRequested
        exact shading_union_subset_axisBox
          (show point ∈ twoScale.first.finalCoarseShading.union from
            ⟨twoScale.fine.selected.embedding index,
              twoScale.fine.subshading index hindex⟩),
        point, ⟨index, hindex⟩, hpointCellRequested⟩
    have hcellSelected : cell ∈ pullback.selectedCells := by
      rw [pullback.selectedCells_eq]
      exact hcellActive
    have hpointCanonical :
        point ∈ wz1PaperGridCube sqrtRequested.1
          (pullback.standardSecondParent cell) :=
      pullback.standardSecondParent_cell_subset hcellSelected hpointCell
    have hparentEq :
        pullback.standardSecondParent cell = parent := by
      have hcanonicalIndex :
          wz1PaperGridIndex sqrtRequested.1 point =
            pullback.standardSecondParent cell :=
        (mem_wz1PaperGridCube _ _ _).mp hpointCanonical
      have hparentIndex :
          wz1PaperGridIndex sqrtRequested.1 point = parent :=
        (mem_wz1PaperGridCube _ _ _).mp hpoint.2
      exact hcanonicalIndex.symm.trans hparentIndex
    change point ∈ twoScale.fine.refined.union ∩
      wz2RetainedCellsUnion rho
        (pullback.preCommonBinRhoCells parent)
    refine ⟨⟨index, hindex⟩, ?_⟩
    rw [wz2RetainedCellsUnion]
    exact Set.mem_iUnion₂.mpr
      ⟨cell, Finset.mem_filter.mpr ⟨hcellSelected, hparentEq⟩,
        hpointCell⟩

/-- The second balanced cover gives the exact coarse mass of every active
side-`sqrt rho` spatial cube. -/
theorem preCommonBinCoarseRegion_volume
    {parent : ℤ × ℤ × ℤ}
    (hparent : parent ∈ twoScale.second.terminal.balanced.activeCells) :
    volume (pullback.preCommonBinCoarseRegion parent) =
    twoScale.second.terminal.balanced.cellMass := by
  rw [pullback.preCommonBinCoarseRegion_eq_parent]
  exact twoScale.second.terminal.balanced.fine_cell_mass parent hparent

/-- The first balanced cover gives the exact final-source mass on the same
family of side-`rho` cells. -/
theorem preCommonBinFinePullback_volume
    (parent : ℤ × ℤ × ℤ) :
    volume (pullback.preCommonBinFinePullback parent) =
      ((pullback.preCommonBinRhoCells parent).card : ENNReal) *
        pullback.firstPostBalanced.cellMass :=
  pullback.selectedRhoCellsSourceRegion_volume _
    (pullback.preCommonBinRhoCells_subset parent)

/-- Division-free same-witness identity joining the second-cover cell mass to
the exact final-source pullback through the first cover. -/
theorem preCommonBinFinePullback_mass_cross
    {parent : ℤ × ℤ × ℤ}
    (hparent : parent ∈ twoScale.second.terminal.balanced.activeCells) :
    volume (pullback.preCommonBinFinePullback parent) *
          volume (wz1PaperGridCube rho (0, 0, 0)) =
      twoScale.second.terminal.balanced.cellMass *
          pullback.firstPostBalanced.cellMass := by
  have hcross :=
    pullback.selectedRhoCells_source_coarse_cross
      (pullback.preCommonBinRhoCells parent)
      (pullback.preCommonBinRhoCells_subset parent)
  have hcoarse := pullback.preCommonBinCoarseRegion_volume hparent
  change
    volume
        (pullback.selectedRhoCellsCoarseRegion
          (pullback.preCommonBinRhoCells parent)) =
      twoScale.second.terminal.balanced.cellMass at hcoarse
  rw [hcoarse] at hcross
  simpa only [preCommonBinFinePullback] using hcross

theorem preCommonBinRhoCells_nonempty
    {parent : ℤ × ℤ × ℤ}
    (hparent : parent ∈ twoScale.second.terminal.balanced.activeCells) :
    (pullback.preCommonBinRhoCells parent).Nonempty := by
  by_contra hempty
  have hcells :
      pullback.preCommonBinRhoCells parent = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  have hsourceZero :
      volume (pullback.preCommonBinFinePullback parent) = 0 := by
    rw [pullback.preCommonBinFinePullback_volume parent, hcells]
    simp
  have hcross := pullback.preCommonBinFinePullback_mass_cross hparent
  rw [hsourceZero] at hcross
  simp only [zero_mul] at hcross
  have hpositive :
      0 <
        twoScale.second.terminal.balanced.cellMass *
          pullback.firstPostBalanced.cellMass :=
    ENNReal.mul_pos
      twoScale.second.terminal.balanced.cellMass_pos.ne'
      pullback.firstPostBalanced.cellMass_pos.ne'
  exact hpositive.ne' hcross.symm

theorem preCommonBinFinePullback_nonempty
    {parent : ℤ × ℤ × ℤ}
    (hparent : parent ∈ twoScale.second.terminal.balanced.activeCells) :
    (pullback.preCommonBinFinePullback parent).Nonempty := by
  rcases pullback.preCommonBinRhoCells_nonempty hparent with
    ⟨cell, hcell⟩
  have hcellSelected :=
    pullback.preCommonBinRhoCells_subset parent hcell
  have hcellMass := pullback.cell_union_mass cell hcellSelected
  have hpositive :
      0 <
        volume
          (pullback.shading.union ∩ wz1PaperGridCube rho cell) := by
    rw [hcellMass]
    exact pullback.firstPostBalanced.cellMass_pos
  have hpieceNonempty :
      (pullback.shading.union ∩ wz1PaperGridCube rho cell).Nonempty := by
    by_contra hnone
    rw [Set.not_nonempty_iff_eq_empty.mp hnone] at hpositive
    have hemptyNotPositive :
        ¬ (0 < volume (∅ : Set Point3)) := by simp
    exact hemptyNotPositive hpositive
  rcases hpieceNonempty with ⟨point, hpoint⟩
  refine ⟨point, ?_⟩
  change point ∈ pullback.shading.union ∩
    wz2RetainedCellsUnion rho
      (pullback.preCommonBinRhoCells parent)
  exact ⟨hpoint.1, by
    rw [wz2RetainedCellsUnion]
    exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpoint.2⟩⟩

theorem preCommonBinFinePullback_subset_parent
    {parent : ℤ × ℤ × ℤ} :
    pullback.preCommonBinFinePullback parent ⊆
      wz1PaperGridCube sqrtRequested.1 parent := by
  intro point hpoint
  change point ∈ pullback.shading.union ∩
    wz2RetainedCellsUnion rho
      (pullback.preCommonBinRhoCells parent) at hpoint
  rw [wz2RetainedCellsUnion] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint.2 with
    ⟨cell, hcell, hpointCell⟩
  have hcellData := Finset.mem_filter.mp hcell
  have hpointParent :=
    pullback.standardSecondParent_cell_subset
      hcellData.1 hpointCell
  simpa [hcellData.2] using hpointParent

/-- The selected-rho-cell description is exactly the intersection of the
same final source pullback with the second-cover spatial cube. -/
theorem preCommonBinFinePullback_eq_parent
    (parent : ℤ × ℤ × ℤ) :
    pullback.preCommonBinFinePullback parent =
      pullback.shading.union ∩
        wz1PaperGridCube sqrtRequested.1 parent := by
  apply Set.Subset.antisymm
  · intro point hpoint
    exact
      ⟨hpoint.1,
        pullback.preCommonBinFinePullback_subset_parent hpoint⟩
  · intro point hpoint
    have hpullback : point ∈ pullback.retainedRegion := by
      rcases hpoint.1 with ⟨index, hindex⟩
      change point ∈ pullback.postSourceShading.carrier index at hindex
      rw [pullback.postSourceShading_eq] at hindex
      rcases pullback.zeroExtension.carrier_support index point hindex with
        ⟨selectedIndex, _heq, hselected⟩
      rw [pullback.postFirstFineShading_eq] at hselected
      rw [pullback.retainedRegion_eq]
      exact hselected.2
    rw [pullback.retainedRegion_eq] at hpullback
    rcases Set.mem_iUnion₂.mp hpullback with
      ⟨cell, hcell, hpointCell⟩
    have hpointCanonical :
        point ∈ wz1PaperGridCube sqrtRequested.1
          (pullback.standardSecondParent cell) :=
      pullback.standardSecondParent_cell_subset hcell hpointCell
    have hparentEq :
        pullback.standardSecondParent cell = parent := by
      have hcanonicalIndex :
          wz1PaperGridIndex sqrtRequested.1 point =
            pullback.standardSecondParent cell :=
        (mem_wz1PaperGridCube _ _ _).mp hpointCanonical
      have hparentIndex :
          wz1PaperGridIndex sqrtRequested.1 point = parent :=
        (mem_wz1PaperGridCube _ _ _).mp hpoint.2
      exact hcanonicalIndex.symm.trans hparentIndex
    change point ∈ pullback.shading.union ∩
      wz2RetainedCellsUnion rho
        (pullback.preCommonBinRhoCells parent)
    refine ⟨hpoint.1, ?_⟩
    rw [wz2RetainedCellsUnion]
    exact Set.mem_iUnion₂.mpr
      ⟨cell, Finset.mem_filter.mpr ⟨hcell, hparentEq⟩,
        hpointCell⟩

/-- The exact final-source shading over one side-`sqrt rho` spatial cube. -/
def preCommonBinFinePullbackShading
    (parent : ℤ × ℤ × ℤ) : WZ1PaperTubeShading current.grain.family where
  carrier index :=
    pullback.shading.carrier index ∩
      wz2RetainedCellsUnion rho
        (pullback.preCommonBinRhoCells parent)
  measurable_carrier index := by
    apply (pullback.shading.measurable_carrier index).inter
    rw [wz2RetainedCellsUnion]
    exact MeasurableSet.biUnion
      (pullback.preCommonBinRhoCells parent).finite_toSet.countable
      (fun cell _ => wz1PaperGridCube_measurable cell)
  subset_body index :=
    Set.inter_subset_left.trans (pullback.shading.subset_body index)

theorem preCommonBinFinePullbackShading_union
    (parent : ℤ × ℤ × ℤ) :
    (pullback.preCommonBinFinePullbackShading parent).union =
      pullback.preCommonBinFinePullback parent := by
  ext point
  constructor
  · rintro ⟨index, hsource, hregion⟩
    exact ⟨⟨index, hsource⟩, hregion⟩
  · rintro ⟨⟨index, hsource⟩, hregion⟩
    exact ⟨index, hsource, hregion⟩

theorem preCommonBinFinePullbackShading_sub_source
    (parent : ℤ × ℤ × ℤ) :
    PureWZ2PaperIsSubshading
      (pullback.preCommonBinFinePullbackShading parent)
      current.grain.shading := by
  intro index point hpoint
  exact pullback.subshading index hpoint.1

/-- Exact indexed source mass over one second-cover spatial cube, computed
cell-by-cell from the first balanced cover. -/
theorem preCommonBinFinePullbackShading_mass
    (parent : ℤ × ℤ × ℤ) :
    (pullback.preCommonBinFinePullbackShading parent).mass =
      ∑ cell ∈ pullback.preCommonBinRhoCells parent,
        wz2PaperCellIncidenceMass
          (rho := rho) pullback.postFirstFineShading cell := by
  let cells := pullback.preCommonBinRhoCells parent
  let shading := pullback.preCommonBinFinePullbackShading parent
  have hcarrierPartition :
      ∀ index : Fin current.grain.family.card,
        shading.carrier index =
          ⋃ cell ∈ cells,
            shading.carrier index ∩ wz1PaperGridCube rho cell := by
    intro index
    ext point
    constructor
    · intro hpoint
      change point ∈ pullback.shading.carrier index ∩
        wz2RetainedCellsUnion rho cells at hpoint
      rw [wz2RetainedCellsUnion] at hpoint
      rcases Set.mem_iUnion₂.mp hpoint.2 with
        ⟨cell, hcell, hpointCell⟩
      exact Set.mem_iUnion₂.mpr
        ⟨cell, hcell, hpoint, hpointCell⟩
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨_cell, _hcell, hsource, _hpointCell⟩
      exact hsource
  have hcarrierVolume :
      ∀ index : Fin current.grain.family.card,
        volume (shading.carrier index) =
          ∑ cell ∈ cells,
            volume
              (shading.carrier index ∩
                wz1PaperGridCube rho cell) := by
    intro index
    calc
      volume (shading.carrier index) =
          volume
            (⋃ cell ∈ cells,
              shading.carrier index ∩
                wz1PaperGridCube rho cell) :=
        congrArg volume (hcarrierPartition index)
      _ =
          ∑ cell ∈ cells,
            volume
              (shading.carrier index ∩
                wz1PaperGridCube rho cell) := by
        apply MeasureTheory.measure_biUnion_finset
        · intro first _ second _ hne
          exact (wz1PaperGridCube_disjoint hne).mono
            Set.inter_subset_right Set.inter_subset_right
        · intro cell _
          exact (shading.measurable_carrier index).inter
            (wz1PaperGridCube_measurable cell)
  have hcellMass :
      ∀ cell ∈ cells,
        (∑ index : Fin current.grain.family.card,
          volume
            (shading.carrier index ∩
              wz1PaperGridCube rho cell)) =
        wz2PaperCellIncidenceMass
          (rho := rho) pullback.postFirstFineShading cell := by
    intro cell hcell
    have hcellSelected :
        cell ∈ pullback.selectedCells :=
      pullback.preCommonBinRhoCells_subset parent hcell
    calc
      (∑ index : Fin current.grain.family.card,
          volume
            (shading.carrier index ∩
              wz1PaperGridCube rho cell)) =
          ∑ index : Fin current.grain.family.card,
            volume
              (pullback.shading.carrier index ∩
                wz1PaperGridCube rho cell) := by
        apply Finset.sum_congr rfl
        intro index _
        change volume
            ((pullback.shading.carrier index ∩
                wz2RetainedCellsUnion rho cells) ∩
              wz1PaperGridCube rho cell) = _
        congr 1
        ext point
        constructor
        · rintro ⟨⟨hsource, _⟩, hpointCell⟩
          exact ⟨hsource, hpointCell⟩
        · rintro ⟨hsource, hpointCell⟩
          exact
            ⟨⟨hsource, by
                rw [wz2RetainedCellsUnion]
                exact Set.mem_iUnion₂.mpr
                  ⟨cell, hcell, hpointCell⟩⟩,
              hpointCell⟩
      _ = wz2PaperCellIncidenceMass
          (rho := rho) pullback.postFirstFineShading cell :=
        pullback.cell_incidence_mass cell hcellSelected
  calc
    shading.mass =
        ∑ index : Fin current.grain.family.card,
          ∑ cell ∈ cells,
            volume
              (shading.carrier index ∩
                wz1PaperGridCube rho cell) := by
      apply Finset.sum_congr rfl
      intro index _
      exact hcarrierVolume index
    _ =
        ∑ cell ∈ cells,
          ∑ index : Fin current.grain.family.card,
            volume
              (shading.carrier index ∩
                wz1PaperGridCube rho cell) := by
      rw [Finset.sum_comm]
    _ =
        ∑ cell ∈ cells,
          wz2PaperCellIncidenceMass
            (rho := rho) pullback.postFirstFineShading cell := by
      apply Finset.sum_congr rfl
      exact hcellMass
    _ = _ := rfl

end PureWZ2Node05V4RichTwoScaleCellPullbackData

/-- An almost-full local projection grain inside the exact final-source
pullback of one second-cover spatial cube. -/
structure PureWZ2PreCommonBinCubeLocalGrainData
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
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
    (parent : ℤ × ℤ × ℤ) where
  parent_active : parent ∈ twoScale.second.terminal.balanced.activeCells
  root : ℝ := sqrtRequested.1
  root_eq : root = Real.sqrt rho
  root_pos : 0 < root
  fullSource : Set Point3 :=
    pullback.preCommonBinFinePullback parent
  fullSource_eq :
    fullSource = pullback.preCommonBinFinePullback parent
  fullSource_eq_parent :
    fullSource =
      pullback.shading.union ∩
        wz1PaperGridCube root parent
  fullSource_measurable : MeasurableSet fullSource
  fullSource_nonempty : fullSource.Nonempty
  fullSource_subset_parent :
    fullSource ⊆ wz1PaperGridCube root parent
  fullSource_volume_cross :
    volume fullSource *
          volume (wz1PaperGridCube rho (0, 0, 0)) =
      twoScale.second.terminal.balanced.cellMass *
        pullback.firstPostBalanced.cellMass
  shadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily pullback.shading
      current.grain.extremal.delta_pos) :=
    pureWZ2ActiveCellShading pullback.shading
      current.grain.extremal.delta_pos
  shadow_union : shadow.union = pullback.shading.union
  localPaper : PureWZ2LocalGrainData pullback.shading sigma
    (Kakeya.realRpowENN delta (-inputLoss))
  localGrains : WZ1LocalGrainData shadow sigma
    (10 * Kakeya.realRpowENN delta (-inputLoss))
  exactAD :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection
          (globalGrainDirection (current.grain.globalGrains.slope z))
          (horizontalSlice shadow.union z))
        rho (1 - sigma)
        (10 * Kakeya.realRpowENN delta (-inputLoss))
  centers : Finset Point3
  centers_subset : (centers : Set Point3) ⊆ fullSource
  centers_card : centers.card ≤ 512
  centers_nonempty : centers.Nonempty
  cover :
    fullSource ⊆ ⋃ center ∈ centers,
      Metric.closedBall center root
  anchor : Point3
  anchor_mem_centers : anchor ∈ centers
  anchor_mem_fullSource : anchor ∈ fullSource
  anchor_mem_pullback : anchor ∈ pullback.shading.union
  anchor_mem_source : anchor ∈ current.grain.shading.union
  anchor_mem_shadow : anchor ∈ shadow.union
  localSource : Set Point3 :=
    fullSource ∩ Metric.closedBall anchor root
  localSource_eq :
    localSource = fullSource ∩ Metric.closedBall anchor root
  localSource_measurable : MeasurableSet localSource
  localSource_nonempty : localSource.Nonempty
  localSource_subset :
    localSource ⊆
      shadow.union ∩ Metric.closedBall anchor (Real.sqrt rho)
  fullSource_average :
    volume fullSource ≤
      (centers.card : ENNReal) * volume localSource
  planeMap_eq_source :
    localGrains.planeMap anchor =
      current.grain.localGrains.planeMap
        ⟨anchor, anchor_mem_source⟩
  normal_vertical :
    |localGrains.planeMap anchor (2 : Fin 3)| ≤ 1 / 2
  fiber :
    WZ1Lemma23LocalProjectionHeavyFiberInSource
      (rho := rho) shadow
        (10 * Kakeya.realRpowENN delta (-inputLoss))
        localGrains anchor localSource
  heightLeft : ℝ := (parent.2.2 : ℝ) * root
  grain_height :
    ∀ point ∈ fiber.grain,
      point (2 : Fin 3) ∈
        Set.Ico heightLeft (heightLeft + Real.sqrt rho)
  height_window :
    Set.Ico heightLeft (heightLeft + Real.sqrt rho) ⊆
      Set.Icc (-1 : ℝ) 1

/-- Construct the local source and almost-full P1-normal projection fiber in
one genuine second-cover spatial cube. -/
theorem PureWZ2Node05V4RichTwoScaleCellPullbackData.preCommonBinCubeLocalGrain
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
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
    (hbridge : PureWZ2PaperADBridgeStatement)
    (parent : ℤ × ℤ × ℤ)
    (hparent : parent ∈ twoScale.second.terminal.balanced.activeCells) :
    Nonempty (PureWZ2PreCommonBinCubeLocalGrainData pullback parent) := by
  let root := sqrtRequested.1
  let fullSource := pullback.preCommonBinFinePullback parent
  have hroot : 0 < root := twoScale.fine.coarse_extremal.delta_pos
  have hrootEq : root = Real.sqrt rho := pullback.sqrtRequested_eq
  have hfullMeasurable : MeasurableSet fullSource := by
    dsimp only [fullSource]
    rw [← pullback.preCommonBinFinePullbackShading_union parent]
    exact measurableSet_shading_union _
  have hfullNonempty : fullSource.Nonempty :=
    pullback.preCommonBinFinePullback_nonempty hparent
  have hfullParent :
      fullSource ⊆ wz1PaperGridCube root parent := by
    dsimp only [fullSource, root]
    exact pullback.preCommonBinFinePullback_subset_parent
  let first := Classical.choose hfullNonempty
  have hfirst : first ∈ fullSource :=
    Classical.choose_spec hfullNonempty
  have hfullBall :
      fullSource ⊆ Metric.closedBall first (2 * root) := by
    intro point hpoint
    rw [Metric.mem_closedBall]
    exact le_of_lt
      (wz1_paper_grid_cube_diameter_lt_two_rho
        hroot (hfullParent hpoint) (hfullParent hfirst))
  rcases point3_subset_self_centered_sqrt_cover hroot hfullBall with
    ⟨centers, hcentersSubset, hcentersCard, hcover⟩
  have hcentersNonempty : centers.Nonempty := by
    rcases hfullNonempty with ⟨point, hpoint⟩
    rcases Set.mem_iUnion₂.mp (hcover hpoint) with
      ⟨center, hcenter, _⟩
    exact ⟨center, hcenter⟩
  let piece (center : Point3) : Set Point3 :=
    fullSource ∩ Metric.closedBall center root
  rcases Finset.exists_max_image centers
      (fun center => volume (piece center)) hcentersNonempty with
    ⟨anchor, hanchor, hmax⟩
  let localSource := piece anchor
  have hlocalMeasurable : MeasurableSet localSource :=
    hfullMeasurable.inter measurableSet_closedBall
  have hanchorFull : anchor ∈ fullSource :=
    hcentersSubset hanchor
  have hanchorLocal : anchor ∈ localSource := by
    exact ⟨hanchorFull, Metric.mem_closedBall_self hroot.le⟩
  have hlocalNonempty : localSource.Nonempty :=
    ⟨anchor, hanchorLocal⟩
  have hfullAverage :
      volume fullSource ≤
        (centers.card : ENNReal) * volume localSource := by
    have hpieceCover :
        fullSource ⊆ ⋃ center ∈ centers, piece center := by
      intro point hpoint
      rcases Set.mem_iUnion₂.mp (hcover hpoint) with
        ⟨center, hcenter, hpointBall⟩
      exact Set.mem_iUnion₂.mpr
        ⟨center, hcenter, hpoint, hpointBall⟩
    calc
      volume fullSource ≤
          ∑ center ∈ centers, volume (piece center) := by
        apply (measure_mono hpieceCover).trans
        exact measure_biUnion_finset_le centers piece
      _ ≤ ∑ _center ∈ centers, volume (piece anchor) :=
        Finset.sum_le_sum fun center hcenter => hmax center hcenter
      _ = (centers.card : ENNReal) * volume localSource := by
        simp [localSource, Finset.sum_const]
  let localPaper :=
    current.grain.localGrains.restrictWithConstant
      pullback.subshading le_rfl
      (by simp [Kakeya.realRpowENN] :
        Kakeya.realRpowENN delta (-inputLoss) ≠ ⊤)
  let shadow :=
    pureWZ2ActiveCellShading pullback.shading
      current.grain.extremal.delta_pos
  have hshadowUnion :
      shadow.union = pullback.shading.union :=
    pureWZ2ActiveCellShading_union pullback.shading
      current.grain.extremal.delta_pos pullback.whole_cells
  let localGrains :=
    localPaper.toActiveCellShadow current.grain.extremal.delta_pos
      pullback.whole_cells hbridge
  let restrictedGlobal :=
    current.grain.globalGrains.toPureWZ2LipschitzGlobalGrainData.restrict
      pullback.subshading le_rfl
      (by simp [Kakeya.realRpowENN] :
        Kakeya.realRpowENN delta (-inputLoss) ≠ ⊤)
  let globalPaper :=
    PureWZ2BoundedLipschitzGlobalGrainData.ofSlopeBound
      restrictedGlobal (by
        intro z hz
        exact current.grain.globalGrains.slope_bound z hz)
  have hanchorPullback : anchor ∈ pullback.shading.union := by
    exact hanchorFull.1
  have hanchorSource : anchor ∈ current.grain.shading.union :=
    pullback.subshading.union_subset hanchorPullback
  have hanchorShadow : anchor ∈ shadow.union := by
    rwa [hshadowUnion]
  have hdeltaRho : delta ≤ rho := by
    rw [← pullback.rhoRequested_eq]
    exact rhoRequested.property.1
  have hrho : 0 < rho :=
    current.grain.extremal.delta_pos.trans_le hdeltaRho
  have hrhoOne : rho ≤ 1 := by
    rw [← pullback.rhoRequested_eq]
    exact rhoRequested.property.2
  have hlocalSubset :
      localSource ⊆
        shadow.union ∩ Metric.closedBall anchor (Real.sqrt rho) := by
    intro point hpoint
    refine ⟨?_, ?_⟩
    · rw [hshadowUnion]
      exact hpoint.1.1
    · simpa only [root, hrootEq] using hpoint.2
  have hgraphCtop :
      (10 * Kakeya.realRpowENN delta (-inputLoss) : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN])
  rcases wz1_lemma23_local_projection_heavy_fiber_in_source
      shadow (10 * Kakeya.realRpowENN delta (-inputLoss))
      localGrains anchor localSource hanchorShadow
      hlocalMeasurable hlocalNonempty hlocalSubset
      hrho hdeltaRho hrhoOne hgraphCtop with
    ⟨fiber⟩
  have hexactDelta :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection (current.grain.globalGrains.slope z))
            (horizontalSlice shadow.union z))
          delta (1 - sigma)
          (10 * Kakeya.realRpowENN delta (-inputLoss)) := by
    intro z hz
    have hall :=
      globalPaper.activeCellShadow_exactAD
        current.grain.extremal.delta_pos pullback.whole_cells hbridge
        globalPaper.slope_bound
    have h := hall z hz
    have hslope :
        globalPaper.slope = current.grain.globalGrains.slope := rfl
    rw [hslope] at h
    simpa [shadow] using h
  have hexact :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection (current.grain.globalGrains.slope z))
            (horizontalSlice shadow.union z))
          rho (1 - sigma)
          (10 * Kakeya.realRpowENN delta (-inputLoss)) := by
    intro z hz
    exact (hexactDelta z hz).coarsen_scale hrho hdeltaRho hrhoOne
  let heightLeft := (parent.2.2 : ℝ) * root
  have hheight :
      ∀ point ∈ fiber.grain,
        point (2 : Fin 3) ∈
          Set.Ico heightLeft (heightLeft + Real.sqrt rho) := by
    intro point hpoint
    have hparentPoint :
        point ∈ wz1PaperGridCube root parent :=
      hfullParent (fiber.grain_in_source hpoint).1
    rw [wz1PaperGridCube_eq_Ico hroot parent] at hparentPoint
    have hz := hparentPoint.2.2.2.2
    change point (2 : Fin 3) ∈
      Set.Ico ((parent.2.2 : ℝ) * root)
        ((parent.2.2 : ℝ) * root + Real.sqrt rho)
    exact ⟨hz.1, by rw [← hrootEq]; linarith [hz.2]⟩
  have hheightWindow :
      Set.Ico heightLeft (heightLeft + Real.sqrt rho) ⊆
        Set.Icc (-1 : ℝ) 1 := by
    intro z hz
    let point : Point3 :=
      point3 (((parent.1 : ℝ) + 1 / 2) * root)
        (((parent.2.1 : ℝ) + 1 / 2) * root) z
    have hpointParent : point ∈ wz1PaperGridCube root parent := by
      rw [wz1PaperGridCube_eq_Ico hroot parent]
      change
        (parent.1 : ℝ) * root ≤ point 0 ∧
        point 0 < ((parent.1 : ℝ) + 1) * root ∧
        (parent.2.1 : ℝ) * root ≤ point 1 ∧
        point 1 < ((parent.2.1 : ℝ) + 1) * root ∧
        (parent.2.2 : ℝ) * root ≤ point 2 ∧
        point 2 < ((parent.2.2 : ℝ) + 1) * root
      have hp0 :
          point 0 = ((parent.1 : ℝ) + 1 / 2) * root := by
        simp [point, point3]
      have hp1 :
          point 1 = ((parent.2.1 : ℝ) + 1 / 2) * root := by
        simp [point, point3]
      have hp2 : point 2 = z := by simp [point, point3]
      rw [hp0, hp1, hp2]
      have hz' :
          z ∈ Set.Ico ((parent.2.2 : ℝ) * root)
            ((parent.2.2 : ℝ) * root + root) := by
        simpa only [heightLeft, hrootEq] using hz
      exact ⟨by linarith, by linarith, by linarith, by linarith,
        hz'.1, by
          rw [show ((parent.2.2 : ℝ) + 1) * root =
            (parent.2.2 : ℝ) * root + root by ring]
          exact hz'.2⟩
    have hcoarse :
        point ∈ twoScale.fine.croppedCoarseShading.union := by
      rw [twoScale.second.terminal.balanced.coarse_union_eq]
      exact Set.mem_iUnion₂.mpr
        ⟨parent, hparent, hpointParent⟩
    have hbox := shading_union_subset_axisBox hcoarse
    have hp2 : point 2 = z := by simp [point, point3]
    rw [← hp2]
    simpa [Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2
  have hplaneSource :
      localGrains.planeMap anchor =
        current.grain.localGrains.planeMap ⟨anchor, hanchorSource⟩ := by
    have hplane :=
      localPaper.toActiveCellShadow_planeMap_eq
        current.grain.extremal.delta_pos pullback.whole_cells hbridge
        anchor hanchorShadow
    rw [hplane]
    rfl
  exact ⟨{
    parent_active := hparent
    root := root
    root_eq := hrootEq
    root_pos := hroot
    fullSource := fullSource
    fullSource_eq := rfl
    fullSource_eq_parent := by
      simpa only [root] using
        pullback.preCommonBinFinePullback_eq_parent parent
    fullSource_measurable := hfullMeasurable
    fullSource_nonempty := hfullNonempty
    fullSource_subset_parent := hfullParent
    fullSource_volume_cross :=
      pullback.preCommonBinFinePullback_mass_cross hparent
    shadow := shadow
    shadow_union := hshadowUnion
    localPaper := localPaper
    localGrains := localGrains
    exactAD := hexact
    centers := centers
    centers_subset := hcentersSubset
    centers_card := hcentersCard
    centers_nonempty := hcentersNonempty
    cover := hcover
    anchor := anchor
    anchor_mem_centers := hanchor
    anchor_mem_fullSource := hanchorFull
    anchor_mem_pullback := hanchorPullback
    anchor_mem_source := hanchorSource
    anchor_mem_shadow := hanchorShadow
    localSource := localSource
    localSource_eq := rfl
    localSource_measurable := hlocalMeasurable
    localSource_nonempty := hlocalNonempty
    localSource_subset := hlocalSubset
    fullSource_average := hfullAverage
    planeMap_eq_source := hplaneSource
    normal_vertical := by
      rw [hplaneSource]
      exact current.grain.planeMap_vertical_bound
        ⟨anchor, hanchorSource⟩
    heightLeft := heightLeft
    grain_height := hheight
    height_window := hheightWindow
    fiber := fiber
  }⟩

/-- The fixed finite-cover and local-projection cost paid inside one
side-`sqrt rho` source cube. -/
def pureWZ2PreCommonBinLocalProjectionCost
    (delta rho sigma inputLoss : ℝ) : ENNReal :=
  512 *
    ((10 * Kakeya.realRpowENN delta (-inputLoss)) *
      Kakeya.realRpowENN
        (Real.sqrt rho / rho) (1 - sigma))

/-- Convert a division-free two-cover mass budget into the almost-full grain
lower bound.  This is the point where the second `cellMass`, the first
`cellMass`, and the exact final-source pullback are used together. -/
theorem PureWZ2PreCommonBinCubeLocalGrainData.grain_volume_of_balanced_budget
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {parent : ℤ × ℤ × ℤ}
    (data : PureWZ2PreCommonBinCubeLocalGrainData pullback parent)
    (target : ENNReal)
    (hbudget :
      target *
          (pureWZ2PreCommonBinLocalProjectionCost
            delta rho sigma inputLoss *
            volume (wz1PaperGridCube rho (0, 0, 0))) ≤
        twoScale.second.terminal.balanced.cellMass *
          pullback.firstPostBalanced.cellMass) :
    target ≤ volume data.fiber.grain := by
  let localCost : ENNReal :=
    (10 * Kakeya.realRpowENN delta (-inputLoss)) *
      Kakeya.realRpowENN
        (Real.sqrt rho / rho) (1 - sigma)
  let cost : ENNReal :=
    pureWZ2PreCommonBinLocalProjectionCost
      delta rho sigma inputLoss
  let cubeVolume : ENNReal :=
    volume (wz1PaperGridCube rho (0, 0, 0))
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hlocalCostPos : 0 < localCost := by
    dsimp only [localCost]
    have hdeltaPower :
        0 < Kakeya.realRpowENN delta (-inputLoss) :=
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos current.grain.extremal.delta_pos _)
    have hratio : 0 < Real.sqrt rho / rho := by positivity
    have hratioPower :
        0 <
          Kakeya.realRpowENN
            (Real.sqrt rho / rho) (1 - sigma) :=
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos hratio _)
    positivity
  have hcostPos : 0 < cost := by
    simpa [cost, localCost,
      pureWZ2PreCommonBinLocalProjectionCost] using
      (show 0 < (512 : ENNReal) * localCost by positivity)
  have hcostTop : cost ≠ ⊤ := by
    dsimp only [cost, pureWZ2PreCommonBinLocalProjectionCost]
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num)
          (by simp [Kakeya.realRpowENN]))
        (by simp [Kakeya.realRpowENN]))
  have hcubePos : 0 < cubeVolume := by
    dsimp only [cubeVolume]
    rw [wz1PaperGridCube_volume_exact hrho]
    exact ENNReal.ofReal_pos.mpr (pow_pos hrho 3)
  have hcubeTop : cubeVolume ≠ ⊤ := by
    dsimp only [cubeVolume]
    rw [wz1PaperGridCube_volume_exact hrho]
    exact ENNReal.ofReal_ne_top
  have hfactorPos : 0 < cost * cubeVolume :=
    ENNReal.mul_pos hcostPos.ne' hcubePos.ne'
  have hfactorTop : cost * cubeVolume ≠ ⊤ :=
    ENNReal.mul_ne_top hcostTop hcubeTop
  have hfullToGrain :
      volume data.fullSource ≤
        cost * volume data.fiber.grain := by
    calc
      volume data.fullSource ≤
          (data.centers.card : ENNReal) *
            volume data.localSource :=
        data.fullSource_average
      _ ≤ (512 : ENNReal) * volume data.localSource := by
        gcongr
        exact_mod_cast data.centers_card
      _ ≤ (512 : ENNReal) *
          (localCost * volume data.fiber.grain) := by
        gcongr
        simpa [localCost] using data.fiber.mass_retention
      _ = cost * volume data.fiber.grain := by
        simp only [cost, localCost,
          pureWZ2PreCommonBinLocalProjectionCost]
        ring
  apply
    (ENNReal.mul_le_mul_iff_right
      hfactorPos.ne' hfactorTop).mp
  calc
    (cost * cubeVolume) * target ≤
        twoScale.second.terminal.balanced.cellMass *
          pullback.firstPostBalanced.cellMass := by
      simpa [cost, cubeVolume, mul_comm] using hbudget
    _ = volume data.fullSource * cubeVolume := by
      simpa [cubeVolume] using data.fullSource_volume_cross.symm
    _ ≤ (cost * volume data.fiber.grain) * cubeVolume := by
      gcongr
    _ = (cost * cubeVolume) * volume data.fiber.grain := by ring

/-- View the constructed P1-normal fiber as the generalized full local grain
consumed by the closed normal-first argument. -/
def PureWZ2PreCommonBinCubeLocalGrainData.toFullLocalGrainInput
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {parent : ℤ × ℤ × ℤ}
    (data : PureWZ2PreCommonBinCubeLocalGrainData pullback parent)
    (hgrain :
      Kakeya.realRpowENN rho (2 + 2 * eta) ≤
        volume data.fiber.grain) :
    WZ1Lemma23FullLocalGrainInputGeneralized
      rho sigma eta
        (10 * Kakeya.realRpowENN delta (-inputLoss))
        current.grain.globalGrains.slope where
  grain := data.fiber.grain
  grain_measurable := data.fiber.grain_measurable
  grain_finite := data.fiber.grain_finite
  heightLeft := data.heightLeft
  grain_height := data.grain_height
  grain_volume := hgrain
  center := data.anchor
  normal := data.localGrains.planeMap data.anchor
  localProjectionCenter := data.fiber.center
  normal_unit :=
    data.localGrains.unit data.anchor data.anchor_mem_shadow
  normal_vertical := data.normal_vertical
  grain_square := data.fiber.grain_square
  grain_local_strip := data.fiber.grain_local_strip
  slope_small := fun z hz =>
    current.grain.globalGrains.slope_bound z (data.height_window hz)
  projected := fun z =>
    scalarProjection
      (globalGrainDirection (current.grain.globalGrains.slope z))
      (horizontalSlice data.shadow.union z)
  globalAD := fun z hz => data.exactAD z (data.height_window hz)
  global_projection_sub := by
    intro z _
    rintro value ⟨point, hpoint, rfl⟩
    have hlift :
        point3 (point 0) (point 1) z ∈ data.fiber.grain :=
      wz1Lemma23_mem_planarSlice_iff.mp hpoint
    have hshadow :
        point3 (point 0) (point 1) z ∈ data.shadow.union :=
      data.fiber.grain_in_shading hlift
    refine
      ⟨point3 (point 0) (point 1) z,
        ⟨hshadow, by simp [point3]⟩, ?_⟩
    change
      inner ℝ (point3 (point 0) (point 1) z)
          (globalGrainDirection (current.grain.globalGrains.slope z)) =
        point 0 + current.grain.globalGrains.slope z * point 1
    rw [PiLp.inner_apply]
    simp [Fin.sum_univ_succ, globalGrainDirection, point3]

/-- The almost-full P1 local grain forces the first normal component to be
large, exactly as in Step 1 of WZ1 Lemma 5.3. -/
theorem PureWZ2PreCommonBinCubeLocalGrainData.normal_first
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {parent : ℤ × ℤ × ℤ}
    (data : PureWZ2PreCommonBinCubeLocalGrainData pullback parent)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hconstantPower :
      10 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN rho (-eta))
    (hPlanarSmall : 32 * Real.rpow rho eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt rho ≤ 1)
    (habsorb :
      Real.rpow rho (1 - 4 * eta / sigma) ≤
        Real.sqrt rho / 14)
    (hgrain :
      Kakeya.realRpowENN rho (2 + 2 * eta) ≤
        volume data.fiber.grain) :
    1 / 4 ≤
      |data.localGrains.planeMap data.anchor (0 : Fin 3)| := by
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hrhoOne : rho ≤ 1 := by
    rw [← pullback.rhoRequested_eq]
    exact rhoRequested.property.2
  have hCtop :
      (10 * Kakeya.realRpowENN delta (-inputLoss) : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN])
  exact
    wz1_lemma23_full_grain_normal_first_component_generalized
      rho sigma eta
      (10 * Kakeya.realRpowENN delta (-inputLoss))
      current.grain.globalGrains.slope
      hrho hrhoOne hsigma hsigmaOne heta hetaSigma
      hCtop hconstantPower hPlanarSmall hrootSmall20 habsorb
      (data.toFullLocalGrainInput hgrain)

/--
The missing upstream geometric receipt between the two balanced covers and
Step 1 of Lemma 5.3.

This is the exact paper output that the still-missing aggregate producer must
construct.  Its finite `sample` indexes a bounded-residue, separated family of
distinct side-`sqrt rho` spatial cubes in one literal standard slab.  The
`aggregateFineShading` is the union of their pullbacks to the *same* final
`delta`-source, with both its indexed mass identity and the fixed residue loss
recorded.  The two final fields are the paper `K` and total-mass lower bounds.

There is deliberately no estimate for arbitrary pairs of points in different
cubes.  The only metric estimate needed downstream is proved for the final
maximal-source anchors from cube separation, common-height cube geometry, and
localization at the one fixed global-grain line.
-/
structure PureWZ2PreCommonBinGlobalGrainNeighborhoodData
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale) where
  heightIndex :
    {heightIndex // heightIndex ∈ pullback.standardSqrtSlabIndices}
  lineHeight : ℝ
  lineHeight_mem : lineHeight ∈ Set.Icc (-1 : ℝ) 1
  lineHeight_mem_slab :
    lineHeight ∈
      Set.Ico
        ((heightIndex.1 : ℝ) * Real.sqrt rho)
        ((heightIndex.1 : ℝ) * Real.sqrt rho +
          Real.sqrt rho)
  sourcePopularHeights : Set ℝ :=
    pullback.sourcePopularHeights heightIndex.1
  sourcePopularHeights_eq :
    sourcePopularHeights = pullback.sourcePopularHeights heightIndex.1
  sourcePopularHeights_measurable :
    MeasurableSet sourcePopularHeights
  sourcePopularHalfMass :
    volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) / 2 ≤
      ∫⁻ z in sourcePopularHeights,
        pureWZ2SourceCommonBinSliceMass
          (pullback.standardSqrtSlabSourceRegion heightIndex.1) z
  sourcePopularRegion : Set Point3 :=
    pullback.sourcePopularRegion heightIndex.1
  sourcePopularRegion_eq :
    sourcePopularRegion = pullback.sourcePopularRegion heightIndex.1
  sourcePopularRegion_measurable : MeasurableSet sourcePopularRegion
  sourcePopularRegion_half_volume :
    volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) / 2 ≤
      volume sourcePopularRegion
  lineHeight_mem_popular : lineHeight ∈ sourcePopularHeights
  lineLevel : ℝ
  sample : Finset ℝ
  sample_nonempty : sample.Nonempty
  cube : ℝ → (ℤ × ℤ × ℤ)
  cube_mem :
    ∀ y ∈ sample,
      cube y ∈
        pullback.standardSqrtSlabParents heightIndex.1
  cube_injective : Set.InjOn cube sample
  K : ℕ := sample.card
  K_eq : K = sample.card
  residueClass : ℤ
  residueClass_bounds : 0 ≤ residueClass ∧ residueClass < 512
  cube_y_bounded_residue :
    ∀ y ∈ sample, ∃ quotient : ℤ,
      (cube y).2.1 = residueClass + 512 * quotient
  sample_eq_cube_center_y :
    ∀ y ∈ sample,
      y =
        (((cube y).2.1 : ℝ) + 1 / 2) *
          sqrtRequested.1
  cube_separated :
    ∀ y₁ ∈ sample, ∀ y₂ ∈ sample, y₁ ≠ y₂ →
      500 * sqrtRequested.1 ≤ |y₁ - y₂|
  witness : ℝ → Point3
  witness_mem_pullback :
    ∀ y ∈ sample,
      witness y ∈ pullback.preCommonBinFinePullback (cube y)
  witness_height :
    ∀ y ∈ sample, witness y (2 : Fin 3) = lineHeight
  witness_near_global_grain :
    ∀ y ∈ sample,
      |inner ℝ (witness y)
          (globalGrainDirection
            (current.grain.globalGrains.slope lineHeight)) -
        lineLevel| ≤ delta
  pullback_global_line_localized :
    ∀ y ∈ sample,
      ∀ point ∈ pullback.preCommonBinFinePullback (cube y),
        |inner ℝ point
            (globalGrainDirection
              (current.grain.globalGrains.slope lineHeight)) -
          lineLevel| ≤ 14 * sqrtRequested.1
  aggregateFineShading : WZ1PaperTubeShading current.grain.family
  aggregate_sub_source :
    PureWZ2PaperIsSubshading aggregateFineShading current.grain.shading
  aggregate_union_eq :
    aggregateFineShading.union =
      ⋃ y ∈ sample,
        pullback.preCommonBinFinePullback (cube y)
  aggregate_mass_eq :
    aggregateFineShading.mass =
      ∑ y ∈ sample,
        (pullback.preCommonBinFinePullbackShading (cube y)).mass
  boundedResidueMassLoss : ENNReal := 512
  boundedResidueMassLoss_eq :
    boundedResidueMassLoss = 512
  neighborhoodFineShadingBeforeResidue :
    WZ1PaperTubeShading current.grain.family
  neighborhoodFineShadingBeforeResidue_sub_source :
    PureWZ2PaperIsSubshading
      neighborhoodFineShadingBeforeResidue current.grain.shading
  bounded_residue_mass_retention :
    boundedResidueMassLoss⁻¹ *
        neighborhoodFineShadingBeforeResidue.mass ≤
      aggregateFineShading.mass
  neighborhoodLoss : ℝ
  paper_K_lower :
    Kakeya.realRpowENN rho
        (-1 / 2 + neighborhoodLoss) ≤
      (K : ENNReal)
  paper_total_mass_lower :
    Kakeya.realRpowENN rho
        (1 + sigma / 2 + neighborhoodLoss) ≤
      aggregateFineShading.mass

namespace PureWZ2PreCommonBinGlobalGrainNeighborhoodData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    (neighborhood :
      PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback)

theorem cube_active
    {y : ℝ} (hy : y ∈ neighborhood.sample) :
    neighborhood.cube y ∈
      twoScale.second.terminal.balanced.activeCells :=
  pullback.standardSqrtSlabParents_subset_active
    neighborhood.heightIndex.1 (neighborhood.cube_mem y hy)

theorem cubes_card :
    (neighborhood.sample.image neighborhood.cube).card =
      neighborhood.K := by
  rw [Finset.card_image_of_injOn neighborhood.cube_injective]
  exact neighborhood.K_eq.symm

end PureWZ2PreCommonBinGlobalGrainNeighborhoodData

/-- The local-grain family and auxiliary graph obtained before any common-bin
or four-cycle selection. -/
structure PureWZ2PreCommonBinLocalGrainFamilyData
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    (neighborhood :
      PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback) where
  cubeData :
    ∀ y, y ∈ neighborhood.sample →
      PureWZ2PreCommonBinCubeLocalGrainData
        pullback (neighborhood.cube y)
  grain_volume :
    ∀ y (hy : y ∈ neighborhood.sample),
      Kakeya.realRpowENN rho (2 + 2 * eta) ≤
        volume (cubeData y hy).fiber.grain
  anchor : ℝ → Point3
  anchor_eq :
    ∀ y (hy : y ∈ neighborhood.sample),
      anchor y = (cubeData y hy).anchor
  anchor_mem_source :
    ∀ y (_hy : y ∈ neighborhood.sample),
      anchor y ∈ current.grain.shading.union
  normal : Point3 → Point3
  normal_eq_P1 :
    ∀ y (hy : y ∈ neighborhood.sample),
      normal (anchor y) =
        current.grain.localGrains.planeMap
          ⟨anchor y, anchor_mem_source y hy⟩
  normal_eq_cube :
    ∀ y (hy : y ∈ neighborhood.sample),
      normal (anchor y) =
        (cubeData y hy).localGrains.planeMap
          (cubeData y hy).anchor
  normal_vertical :
    ∀ y ∈ neighborhood.sample,
      |normal (anchor y) (2 : Fin 3)| ≤ 1 / 2
  normal_first :
    ∀ y ∈ neighborhood.sample,
      1 / 4 ≤ |normal (anchor y) (0 : Fin 3)|
  normal_dist :
    ∀ y₁ ∈ neighborhood.sample, ∀ y₂ ∈ neighborhood.sample,
      dist (normal (anchor y₁)) (normal (anchor y₂)) ≤
        dist (anchor y₁) (anchor y₂)
  anchor_dist :
    ∀ y₁ ∈ neighborhood.sample, ∀ y₂ ∈ neighborhood.sample,
      dist (anchor y₁) (anchor y₂) ≤
        4 * |y₁ - y₂|
  g : ℝ → ℝ
  /--
  WZ1 Lemma 5.3 writes `4` at absolute-constant precision.  From the literal
  frozen bounds `|Vₓ| ≥ 1/4` and
  `dist (anchor y₁) (anchor y₂) ≤ 4 |y₁-y₂|`, the quotient estimate gives the
  explicit absolute constant `64`.  The later AD argument uses only that this
  constant is absolute.
  -/
  g_lipschitz : LipschitzOnWith 64 g Set.univ
  g_bound : ∀ y, |g y| ≤ 2
  g_eq :
    ∀ y ∈ neighborhood.sample,
      g y =
        normal (anchor y) (2 : Fin 3) /
          normal (anchor y) (0 : Fin 3)

/-- Assemble the almost-full local grains and auxiliary `g` on the exact
global-neighborhood cube family. -/
theorem PureWZ2PreCommonBinGlobalGrainNeighborhoodData.localGrainFamily
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    (neighborhood :
      PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hconstantPower :
      10 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN rho (-eta))
    (hPlanarSmall : 32 * Real.rpow rho eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt rho ≤ 1)
    (habsorb :
      Real.rpow rho (1 - 4 * eta / sigma) ≤
        Real.sqrt rho / 14)
    (hbalancedBudget :
      Kakeya.realRpowENN rho (2 + 2 * eta) *
          (pureWZ2PreCommonBinLocalProjectionCost
            delta rho sigma inputLoss *
            volume (wz1PaperGridCube rho (0, 0, 0))) ≤
        twoScale.second.terminal.balanced.cellMass *
          pullback.firstPostBalanced.cellMass) :
    Nonempty
      (PureWZ2PreCommonBinLocalGrainFamilyData
        (eta := eta) neighborhood) := by
  let cubeData :
      ∀ y, y ∈ neighborhood.sample →
        PureWZ2PreCommonBinCubeLocalGrainData
          pullback (neighborhood.cube y) :=
    fun y hy =>
      Classical.choice
        (pullback.preCommonBinCubeLocalGrain
          hbridge (neighborhood.cube y)
          (neighborhood.cube_active hy))
  have hgrain :
      ∀ y (hy : y ∈ neighborhood.sample),
        Kakeya.realRpowENN rho (2 + 2 * eta) ≤
          volume (cubeData y hy).fiber.grain := by
    intro y hy
    exact (cubeData y hy).grain_volume_of_balanced_budget
      (Kakeya.realRpowENN rho (2 + 2 * eta))
      hbalancedBudget
  let anchor : ℝ → Point3 := fun y =>
    if hy : y ∈ neighborhood.sample then
      (cubeData y hy).anchor
    else 0
  have hanchorEq :
      ∀ y (hy : y ∈ neighborhood.sample),
        anchor y = (cubeData y hy).anchor := by
    intro y hy
    simp only [anchor, dif_pos hy]
  have hanchorSource :
      ∀ y (hy : y ∈ neighborhood.sample),
        anchor y ∈ current.grain.shading.union := by
    intro y hy
    rw [hanchorEq y hy]
    exact (cubeData y hy).anchor_mem_source
  let normal : Point3 → Point3 :=
    Classical.choose current.grain.localGrains.exists_ambient_extension
  have hnormalEqSource :
      ∀ point : {point : Point3 // point ∈ current.grain.shading.union},
        normal point = current.grain.localGrains.planeMap point :=
    (Classical.choose_spec
      current.grain.localGrains.exists_ambient_extension).2
  have hnormalEqP1 :
      ∀ y (hy : y ∈ neighborhood.sample),
        normal (anchor y) =
          current.grain.localGrains.planeMap
            ⟨anchor y, hanchorSource y hy⟩ := by
    intro y hy
    exact hnormalEqSource ⟨anchor y, hanchorSource y hy⟩
  have hnormalEqCube :
      ∀ y (hy : y ∈ neighborhood.sample),
        normal (anchor y) =
          (cubeData y hy).localGrains.planeMap
            (cubeData y hy).anchor := by
    intro y hy
    calc
      normal (anchor y) =
          current.grain.localGrains.planeMap
            ⟨anchor y, hanchorSource y hy⟩ :=
        hnormalEqP1 y hy
      _ =
          current.grain.localGrains.planeMap
            ⟨(cubeData y hy).anchor,
              (cubeData y hy).anchor_mem_source⟩ := by
        apply congrArg current.grain.localGrains.planeMap
        apply Subtype.ext
        exact hanchorEq y hy
      _ =
          (cubeData y hy).localGrains.planeMap
            (cubeData y hy).anchor :=
        (cubeData y hy).planeMap_eq_source.symm
  have hnormalVertical :
      ∀ y ∈ neighborhood.sample,
        |normal (anchor y) (2 : Fin 3)| ≤ 1 / 2 := by
    intro y hy
    rw [hnormalEqP1 y hy]
    exact current.grain.planeMap_vertical_bound
      ⟨anchor y, hanchorSource y hy⟩
  have hnormalFirst :
      ∀ y ∈ neighborhood.sample,
        1 / 4 ≤ |normal (anchor y) (0 : Fin 3)| := by
    intro y hy
    rw [hnormalEqCube y hy]
    exact (cubeData y hy).normal_first
      hsigma hsigmaOne heta hetaSigma hconstantPower
      hPlanarSmall hrootSmall20 habsorb (hgrain y hy)
  have hnormalDist :
      ∀ y₁ ∈ neighborhood.sample, ∀ y₂ ∈ neighborhood.sample,
        dist (normal (anchor y₁)) (normal (anchor y₂)) ≤
          dist (anchor y₁) (anchor y₂) := by
    intro y₁ hy₁ y₂ hy₂
    rw [hnormalEqP1 y₁ hy₁, hnormalEqP1 y₂ hy₂]
    have h :=
      current.grain.localGrains.planeMap_lipschitz.dist_le_mul
        ⟨anchor y₁, hanchorSource y₁ hy₁⟩
        ⟨anchor y₂, hanchorSource y₂ hy₂⟩
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq] using h
  have hanchorDist :
      ∀ y₁ ∈ neighborhood.sample, ∀ y₂ ∈ neighborhood.sample,
        dist (anchor y₁) (anchor y₂) ≤
          4 * |y₁ - y₂| := by
    intro y₁ hy₁ y₂ hy₂
    by_cases heq : y₁ = y₂
    · subst y₂
      simp
    · let first := (cubeData y₁ hy₁).anchor
      let second := (cubeData y₂ hy₂).anchor
      let root := sqrtRequested.1
      let d := |y₁ - y₂|
      have hroot : 0 < root :=
        twoScale.fine.coarse_extremal.delta_pos
      have hfirstPullback :
          first ∈
            pullback.preCommonBinFinePullback
              (neighborhood.cube y₁) := by
        rw [← (cubeData y₁ hy₁).fullSource_eq]
        exact (cubeData y₁ hy₁).anchor_mem_fullSource
      have hsecondPullback :
          second ∈
            pullback.preCommonBinFinePullback
              (neighborhood.cube y₂) := by
        rw [← (cubeData y₂ hy₂).fullSource_eq]
        exact (cubeData y₂ hy₂).anchor_mem_fullSource
      have hfirstCube :
          first ∈
            wz1PaperGridCube root (neighborhood.cube y₁) :=
        by
          simpa only [first, root, (cubeData y₁ hy₁).root_eq,
            pullback.sqrtRequested_eq] using
            (cubeData y₁ hy₁).fullSource_subset_parent
              ((cubeData y₁ hy₁).anchor_mem_fullSource)
      have hsecondCube :
          second ∈
            wz1PaperGridCube root (neighborhood.cube y₂) :=
        by
          simpa only [second, root, (cubeData y₂ hy₂).root_eq,
            pullback.sqrtRequested_eq] using
            (cubeData y₂ hy₂).fullSource_subset_parent
              ((cubeData y₂ hy₂).anchor_mem_fullSource)
      rw [wz1PaperGridCube_eq_Ico hroot] at hfirstCube hsecondCube
      have hseparation : 500 * root ≤ d := by
        exact neighborhood.cube_separated y₁ hy₁ y₂ hy₂ heq
      have hfirstY :
          |first 1 - y₁| ≤ root / 2 := by
        rw [neighborhood.sample_eq_cube_center_y y₁ hy₁]
        change
          |first 1 -
            (((neighborhood.cube y₁).2.1 : ℝ) + 1 / 2) * root| ≤
            root / 2
        rw [abs_le]
        constructor <;> linarith [hfirstCube.2.2.1,
          hfirstCube.2.2.2.1]
      have hsecondY :
          |second 1 - y₂| ≤ root / 2 := by
        rw [neighborhood.sample_eq_cube_center_y y₂ hy₂]
        change
          |second 1 -
            (((neighborhood.cube y₂).2.1 : ℝ) + 1 / 2) * root| ≤
            root / 2
        rw [abs_le]
        constructor <;> linarith [hsecondCube.2.2.1,
          hsecondCube.2.2.2.1]
      have hy : |first 1 - second 1| ≤ d + root := by
        calc
          |first 1 - second 1| =
              |(first 1 - y₁) + (y₁ - y₂) +
                (y₂ - second 1)| := by ring_nf
          _ ≤ |first 1 - y₁| + |y₁ - y₂| +
                |y₂ - second 1| := by
            calc
              _ ≤ |(first 1 - y₁) + (y₁ - y₂)| +
                    |y₂ - second 1| := abs_add_le _ _
              _ ≤ (|first 1 - y₁| + |y₁ - y₂|) +
                    |y₂ - second 1| := by
                gcongr
                exact abs_add_le _ _
          _ ≤ d + root := by
            rw [abs_sub_comm y₂ (second 1)]
            dsimp only [d]
            linarith
      have hfirstHeight :
          (neighborhood.cube y₁).2.2 =
            neighborhood.heightIndex.1 :=
        pullback.standardSqrtSlabParent_height
          (neighborhood.cube_mem y₁ hy₁)
      have hsecondHeight :
          (neighborhood.cube y₂).2.2 =
            neighborhood.heightIndex.1 :=
        pullback.standardSqrtSlabParent_height
          (neighborhood.cube_mem y₂ hy₂)
      have hz : |first 2 - second 2| ≤ root := by
        rw [hfirstHeight] at hfirstCube
        rw [hsecondHeight] at hsecondCube
        rw [abs_le]
        constructor <;> linarith [hfirstCube.2.2.2.2,
          hsecondCube.2.2.2.2]
      have hfirstLine :=
        neighborhood.pullback_global_line_localized
          y₁ hy₁ first hfirstPullback
      have hsecondLine :=
        neighborhood.pullback_global_line_localized
          y₂ hy₂ second hsecondPullback
      have hslope :
          |current.grain.globalGrains.slope neighborhood.lineHeight| ≤ 3 :=
        current.grain.globalGrains.slope_bound
          neighborhood.lineHeight neighborhood.lineHeight_mem
      have hprojection :
          |(first 0 +
                current.grain.globalGrains.slope neighborhood.lineHeight *
                  first 1) -
              (second 0 +
                current.grain.globalGrains.slope neighborhood.lineHeight *
                  second 1)| ≤
            28 * root := by
        have hfirstInner :
            inner ℝ first
                (globalGrainDirection
                  (current.grain.globalGrains.slope neighborhood.lineHeight)) =
              first 0 +
                current.grain.globalGrains.slope neighborhood.lineHeight *
                  first 1 := by
          simp [globalGrainDirection, PiLp.inner_apply,
            Fin.sum_univ_succ]
        have hsecondInner :
            inner ℝ second
                (globalGrainDirection
                  (current.grain.globalGrains.slope neighborhood.lineHeight)) =
              second 0 +
                current.grain.globalGrains.slope neighborhood.lineHeight *
                  second 1 := by
          simp [globalGrainDirection, PiLp.inner_apply,
            Fin.sum_univ_succ]
        rw [hfirstInner] at hfirstLine
        rw [hsecondInner] at hsecondLine
        have htriangle := abs_sub
          ((first 0 +
              current.grain.globalGrains.slope neighborhood.lineHeight * first 1) -
            neighborhood.lineLevel)
          ((second 0 +
              current.grain.globalGrains.slope neighborhood.lineHeight * second 1) -
            neighborhood.lineLevel)
        have hrearrange :
            ((first 0 +
                current.grain.globalGrains.slope neighborhood.lineHeight * first 1) -
              neighborhood.lineLevel) -
              ((second 0 +
                  current.grain.globalGrains.slope neighborhood.lineHeight *
                    second 1) -
                neighborhood.lineLevel) =
            (first 0 +
                current.grain.globalGrains.slope neighborhood.lineHeight * first 1) -
              (second 0 +
                current.grain.globalGrains.slope neighborhood.lineHeight *
                  second 1) := by
          ring
        rw [hrearrange] at htriangle
        exact htriangle.trans (by linarith [hfirstLine, hsecondLine])
      have hx : |first 0 - second 0| ≤ 3 * d + 31 * root := by
        have hsolve := abs_sub
          ((first 0 +
              current.grain.globalGrains.slope neighborhood.lineHeight * first 1) -
            (second 0 +
              current.grain.globalGrains.slope neighborhood.lineHeight * second 1))
          (current.grain.globalGrains.slope neighborhood.lineHeight *
            (first 1 - second 1))
        have hrearrange :
            ((first 0 +
                current.grain.globalGrains.slope neighborhood.lineHeight * first 1) -
              (second 0 +
                current.grain.globalGrains.slope neighborhood.lineHeight * second 1)) -
              current.grain.globalGrains.slope neighborhood.lineHeight *
                (first 1 - second 1) =
            first 0 - second 0 := by
          ring
        rw [hrearrange] at hsolve
        have hproduct :
            |current.grain.globalGrains.slope neighborhood.lineHeight *
                (first 1 - second 1)| ≤
              3 * (d + root) := by
          rw [abs_mul]
          exact mul_le_mul hslope hy (abs_nonneg _) (by positivity)
        linarith
      have hdNonneg : 0 ≤ d := abs_nonneg _
      have hx' : |first 0 - second 0| ≤ 1531 * d / 500 := by
        linarith [hx, hseparation]
      have hy' : |first 1 - second 1| ≤ 501 * d / 500 := by
        linarith [hy, hseparation]
      have hz' : |first 2 - second 2| ≤ d / 500 := by
        linarith [hz, hseparation]
      have hxSq :
          (first 0 - second 0) ^ 2 ≤ (1531 * d / 500) ^ 2 := by
        rw [sq_le_sq]
        simpa [abs_of_nonneg (by positivity : 0 ≤ 1531 * d / 500)]
          using hx'
      have hySq :
          (first 1 - second 1) ^ 2 ≤ (501 * d / 500) ^ 2 := by
        rw [sq_le_sq]
        simpa [abs_of_nonneg (by positivity : 0 ≤ 501 * d / 500)]
          using hy'
      have hzSq :
          (first 2 - second 2) ^ 2 ≤ (d / 500) ^ 2 := by
        rw [sq_le_sq]
        simpa [abs_of_nonneg (by positivity : 0 ≤ d / 500)]
          using hz'
      have hcoeff :
          (1531 * d / 500) ^ 2 + (501 * d / 500) ^ 2 +
              (d / 500) ^ 2 ≤
            (4 * d) ^ 2 := by
        nlinarith [sq_nonneg d]
      have hdistSq : dist first second ^ 2 ≤ (4 * d) ^ 2 := by
        rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_three]
        simpa [Real.dist_eq, sq_abs] using
          (add_le_add (add_le_add hxSq hySq) hzSq).trans hcoeff
      have hdistNonneg : 0 ≤ dist first second := dist_nonneg
      have htargetNonneg : 0 ≤ 4 * d := by positivity
      have hdist := (sq_le_sq₀ hdistNonneg htargetNonneg).mp hdistSq
      simpa only [first, second, d, hanchorEq y₁ hy₁,
        hanchorEq y₂ hy₂] using hdist
  rcases wz1_lemma23_local_graph_extension_of_distortion
      neighborhood.sample anchor normal
      hnormalVertical hnormalFirst hnormalDist hanchorDist with
    ⟨g, hgLip, hgBound, hgEq⟩
  exact ⟨{
    cubeData := cubeData
    grain_volume := hgrain
    anchor := anchor
    anchor_eq := hanchorEq
    anchor_mem_source := hanchorSource
    normal := normal
    normal_eq_P1 := hnormalEqP1
    normal_eq_cube := hnormalEqCube
    normal_vertical := hnormalVertical
    normal_first := hnormalFirst
    normal_dist := hnormalDist
    anchor_dist := hanchorDist
    g := g
    g_lipschitz := hgLip
    g_bound := hgBound
    g_eq := hgEq
  }⟩

end Kakeya.Assouad

end
