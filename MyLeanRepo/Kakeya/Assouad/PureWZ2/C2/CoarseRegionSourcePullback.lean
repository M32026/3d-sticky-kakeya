import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CoarseHorizontalBlockResidue
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperSubfamilyZeroExtension
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers

/-!
# Pull a selected coarse spatial region back to the original source family

Lemma 24 runs its local graph argument on the first-sticky coarse extremizer,
but its retained extremal collection is a refinement of the original
`delta`-family.  This module performs exactly that spatial pullback.

The selected region is the union of the genuine side-`rho` cells retained by
the coarse multi-window output.  The first balanced cover then restricts its
fine shading to those cells.  The two cross identities at the end record the
paper's "same relative density" cancellation; no coarse carrier is identified
with the original source carrier.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2SelectedCoarseRegionSourcePullbackData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (selected : WZ1PaperTubeShading twoScale.coarse.coarse) where
  zeroExtension :
    WZ2PaperSubfamilyZeroExtensionData
      twoScale.coarse.selected twoScale.coarse.refined
  selectedCells : Finset (ℤ × ℤ × ℤ)
  selectedCells_eq :
    selectedCells = wz1PaperActiveCells selected
      twoScale.coarseGrains.extremal.delta_pos
  selectedCells_subset :
    selectedCells ⊆ twoScale.coarse.balanced.activeCells
  selectedRegion : Set Point3
  selectedRegion_eq :
    selectedRegion =
      ⋃ cell ∈ selectedCells, wz1PaperGridCube rho cell
  selectedRegion_eq_coarse : selectedRegion = selected.union
  selectedRegion_measurable : MeasurableSet selectedRegion
  shading : WZ1PaperTubeShading source.family
  carrier_eq : ∀ index, shading.carrier index =
    zeroExtension.ambientShading.carrier index ∩ selectedRegion
  subshading : PureWZ2PaperIsSubshading shading source.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  union_eq :
    shading.union = zeroExtension.ambientShading.union ∩ selectedRegion
  volume_eq :
    volume shading.union =
      (selectedCells.card : ENNReal) *
        twoScale.coarse.balanced.cellMass
  mass_eq :
    shading.mass =
      (selectedCells.card : ENNReal) *
        twoScale.coarse.balanced.incidenceMass
  coarse_region_volume_eq :
    volume selectedRegion =
      (selectedCells.card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0))
  volume_cross :
    volume shading.union *
        volume twoScale.coarse.croppedCoarseShading.union =
      volume selectedRegion * volume twoScale.coarse.refined.union
  mass_cross :
    shading.mass *
        volume twoScale.coarse.croppedCoarseShading.union =
      volume selectedRegion * twoScale.coarse.refined.mass

/-- Backwards-compatible name for the pullback of a completed coarse
multi-window family. -/
abbrev PureWZ2CoarseRegionSourcePullbackData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2CoarseHorizontalWindowFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      twoScale) :=
  PureWZ2SelectedCoarseRegionSourcePullbackData family.shading

/-- Pull any cubical subshading of the genuine first-sticky coarse grain
carrier back to the original source family, preserving exact relative volume
and indexed mass. -/
theorem pureWZ2_pullback_selected_coarse_region
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (selected : WZ1PaperTubeShading twoScale.coarse.coarse)
    (hsub : PureWZ2PaperIsSubshading
      selected twoScale.coarseGrains.shading)
    (hcubical : WZ1PaperIsCubicalShading selected) :
    Nonempty (PureWZ2SelectedCoarseRegionSourcePullbackData selected) := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  let selectedCells := wz1PaperActiveCells selected
    twoScale.coarseGrains.extremal.delta_pos
  let selectedRegion : Set Point3 :=
    ⋃ cell ∈ selectedCells, wz1PaperGridCube rho cell
  have hcoarseRegion : selectedRegion = selected.union := by
    have hactive := hcubical.union_eq_activeCells
      twoScale.coarseGrains.extremal.delta_pos
    rw [hactive]
    simp only [selectedRegion, selectedCells, twoScale.rhoRequested_eq]
  have hselectedRegionMeasurable : MeasurableSet selectedRegion := by
    exact MeasurableSet.biUnion selectedCells.finite_toSet.countable
      (fun cell _ => wz1PaperGridCube_measurable cell)
  have hselectedSubset :
      selectedCells ⊆ twoScale.coarse.balanced.activeCells := by
    intro cell hcell
    rcases ((mem_wz1PaperActiveCells selected
      twoScale.coarseGrains.extremal.delta_pos cell).mp hcell).2 with
      ⟨point, hpointFamily, hpointCellBase⟩
    have hpointCoarseGrains : point ∈ twoScale.coarseGrains.shading.union :=
      hsub.union_subset hpointFamily
    have hpointCoarse :
        point ∈ twoScale.coarse.croppedCoarseShading.union :=
      twoScale.coarseGrains.subshading.union_subset hpointCoarseGrains
    rw [twoScale.coarse.balanced.coarse_union_eq] at hpointCoarse
    rcases Set.mem_iUnion₂.mp hpointCoarse with
      ⟨coarseCell, hcoarseCell, hpointCoarseCellBase⟩
    have hpointCell : point ∈ wz1PaperGridCube rho cell := by
      simpa only [twoScale.rhoRequested_eq] using hpointCellBase
    have hpointCoarseCell : point ∈ wz1PaperGridCube rho coarseCell := by
      simpa only [twoScale.rhoRequested_eq] using hpointCoarseCellBase
    have hcellEq : coarseCell = cell :=
      ((mem_wz1PaperGridCube rho coarseCell point).mp
        hpointCoarseCell).symm.trans
      ((mem_wz1PaperGridCube rho cell point).mp hpointCell)
    rwa [hcellEq] at hcoarseCell
  rcases wz2_paper_subfamily_zero_extension
      twoScale.coarse.selected twoScale.coarse.refined with
    ⟨zeroExtension⟩
  let shading : WZ1PaperTubeShading source.family :=
    { carrier := fun index =>
        zeroExtension.ambientShading.carrier index ∩ selectedRegion
      measurable_carrier := fun index =>
        (zeroExtension.ambientShading.measurable_carrier index).inter
          hselectedRegionMeasurable
      subset_body := fun index => Set.inter_subset_left.trans
        (zeroExtension.ambientShading.subset_body index) }
  have hunion :
      shading.union = zeroExtension.ambientShading.union ∩ selectedRegion := by
    ext point
    constructor
    · rintro ⟨index, hsource, hregion⟩
      exact ⟨⟨index, hsource⟩, hregion⟩
    · rintro ⟨⟨index, hsource⟩, hregion⟩
      exact ⟨index, hsource, hregion⟩
  have hsub : PureWZ2PaperIsSubshading shading source.shading := by
    intro index point hpoint
    rcases zeroExtension.carrier_support index point hpoint.1 with
      ⟨selectedIndex, heq, hselected⟩
    subst index
    exact twoScale.coarse.subshading selectedIndex hselected
  have hwhole : WZ1PaperIsCubicalShading shading := by
    intro index point hpoint other hother
    have hambientWhole :
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
          zeroExtension.ambientShading.carrier index :=
      zeroExtension.cubical twoScale.coarse.refined_cubical
        index point hpoint.1
    rcases zeroExtension.carrier_support index point hpoint.1 with
      ⟨selectedIndex, _heq, hselectedFine⟩
    rcases twoScale.coarse.balanced.fine_cell_nested
        selectedIndex point hselectedFine with
      ⟨coarseCell, _hcoarseCell, hnestedBase⟩
    have hnested :
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
          wz1PaperGridCube rho coarseCell := by
      simpa only [twoScale.rhoRequested_eq] using hnestedBase
    change point ∈
      zeroExtension.ambientShading.carrier index ∩ selectedRegion at hpoint
    rw [show selectedRegion =
        ⋃ cell ∈ selectedCells, wz1PaperGridCube rho cell by rfl] at hpoint
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨selectedCell, hselectedCell, hpointSelectedCell⟩
    have hpointNested : point ∈ wz1PaperGridCube rho coarseCell :=
      hnested ((mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) point).mpr rfl)
    have hcellEq : coarseCell = selectedCell :=
      ((mem_wz1PaperGridCube rho coarseCell point).mp hpointNested).symm.trans
        ((mem_wz1PaperGridCube rho selectedCell point).mp
          hpointSelectedCell)
    refine ⟨hambientWhole hother, ?_⟩
    exact Set.mem_iUnion₂.mpr
      ⟨selectedCell, hselectedCell, by rw [← hcellEq]; exact hnested hother⟩
  have hcellVolume :
      ∀ cell ∈ selectedCells,
        volume (shading.union ∩ wz1PaperGridCube rho cell) =
          twoScale.coarse.balanced.cellMass := by
    intro cell hcell
    have hcellRegion : wz1PaperGridCube rho cell ⊆ selectedRegion := by
      intro point hpoint
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpoint⟩
    have hinter :
        shading.union ∩ wz1PaperGridCube rho cell =
          zeroExtension.ambientShading.union ∩
            wz1PaperGridCube rho cell := by
      rw [hunion]
      ext point
      simp only [Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨hsource, _⟩, hpointCell⟩
        exact ⟨hsource, hpointCell⟩
      · rintro ⟨hsource, hpointCell⟩
        exact ⟨⟨hsource, hcellRegion hpointCell⟩, hpointCell⟩
    rw [hinter, zeroExtension.union_eq]
    simpa only [twoScale.rhoRequested_eq] using
      twoScale.coarse.balanced.fine_cell_mass cell
        (hselectedSubset hcell)
  have hcellMass :
      ∀ cell ∈ selectedCells,
        (∑ sourceIndex : Fin source.family.card,
          volume (shading.carrier sourceIndex ∩
            wz1PaperGridCube rho cell)) =
          twoScale.coarse.balanced.incidenceMass := by
    intro cell hcell
    have hsumAmbient :
        (∑ sourceIndex : Fin source.family.card,
          volume (zeroExtension.ambientShading.carrier sourceIndex ∩
            wz1PaperGridCube rho cell)) =
          ∑ selectedIndex : Fin twoScale.coarse.selected.family.card,
            volume (twoScale.coarse.refined.carrier selectedIndex ∩
              wz1PaperGridCube rho cell) := by
      let supported : Finset (Fin source.family.card) :=
        Finset.univ.map twoScale.coarse.selected.embedding
      calc
        (∑ sourceIndex : Fin source.family.card,
            volume (zeroExtension.ambientShading.carrier sourceIndex ∩
              wz1PaperGridCube rho cell)) =
            ∑ sourceIndex ∈ supported,
              volume (zeroExtension.ambientShading.carrier sourceIndex ∩
                wz1PaperGridCube rho cell) := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro sourceIndex _ hnot
          have hcarrier :
              zeroExtension.ambientShading.carrier sourceIndex = ∅ := by
            apply Set.not_nonempty_iff_eq_empty.mp
            rintro ⟨point, hpoint⟩
            rcases zeroExtension.carrier_support sourceIndex point hpoint with
              ⟨selectedIndex, heq, _⟩
            exact hnot (Finset.mem_map.mpr
              ⟨selectedIndex, Finset.mem_univ _, heq⟩)
          rw [hcarrier]
          simp
        _ = ∑ selectedIndex : Fin twoScale.coarse.selected.family.card,
              volume (twoScale.coarse.refined.carrier selectedIndex ∩
                wz1PaperGridCube rho cell) := by
          rw [Finset.sum_map]
          apply Finset.sum_congr rfl
          intro selectedIndex _
          rw [zeroExtension.carrier_embedding selectedIndex]
    calc
      (∑ sourceIndex : Fin source.family.card,
          volume (shading.carrier sourceIndex ∩
            wz1PaperGridCube rho cell)) =
          ∑ sourceIndex : Fin source.family.card,
            volume (zeroExtension.ambientShading.carrier sourceIndex ∩
              wz1PaperGridCube rho cell) := by
        apply Finset.sum_congr rfl
        intro sourceIndex _
        rw [show shading.carrier sourceIndex =
          zeroExtension.ambientShading.carrier sourceIndex ∩
            selectedRegion from rfl]
        congr 1
        ext point
        constructor
        · rintro ⟨⟨hsource, _⟩, hpointCell⟩
          exact ⟨hsource, hpointCell⟩
        · rintro ⟨hsource, hpointCell⟩
          exact ⟨⟨hsource, Set.mem_iUnion₂.mpr
            ⟨cell, hcell, hpointCell⟩⟩, hpointCell⟩
      _ = ∑ selectedIndex : Fin twoScale.coarse.selected.family.card,
            volume (twoScale.coarse.refined.carrier selectedIndex ∩
              wz1PaperGridCube rho cell) := hsumAmbient
      _ = twoScale.coarse.balanced.incidenceMass := by
        simpa only [twoScale.rhoRequested_eq] using
          twoScale.coarse.balanced.fine_cell_incidence_mass cell
            (hselectedSubset hcell)
  have hvolume : volume shading.union =
      (selectedCells.card : ENNReal) *
        twoScale.coarse.balanced.cellMass := by
    have hpartition : shading.union =
        ⋃ cell ∈ selectedCells,
          shading.union ∩ wz1PaperGridCube rho cell := by
      rw [hunion]
      ext point
      constructor
      · rintro ⟨hsource, hregion⟩
        rcases Set.mem_iUnion₂.mp hregion with
          ⟨cell, hcell, hpointCell⟩
        exact Set.mem_iUnion₂.mpr
          ⟨cell, hcell, ⟨hsource, hregion⟩, hpointCell⟩
      · rintro hpoint
        rcases Set.mem_iUnion₂.mp hpoint with
          ⟨_cell, _hcell, hsource, _hpointCell⟩
        exact hsource
    rw [hpartition]
    have hdisjoint : (selectedCells : Set (ℤ × ℤ × ℤ)).PairwiseDisjoint
        (fun cell => shading.union ∩ wz1PaperGridCube rho cell) := by
      intro first _ second _ hne
      exact (wz1PaperGridCube_disjoint hne).mono
        Set.inter_subset_right Set.inter_subset_right
    have hmeas : ∀ cell ∈ selectedCells, MeasurableSet
        (shading.union ∩ wz1PaperGridCube rho cell) := by
      intro cell _
      exact shading.union_measurable.inter (wz1PaperGridCube_measurable cell)
    rw [MeasureTheory.measure_biUnion_finset hdisjoint hmeas]
    calc
      (∑ cell ∈ selectedCells,
          volume (shading.union ∩ wz1PaperGridCube rho cell)) =
          ∑ _cell ∈ selectedCells,
            twoScale.coarse.balanced.cellMass := by
        apply Finset.sum_congr rfl
        exact hcellVolume
      _ = (selectedCells.card : ENNReal) *
          twoScale.coarse.balanced.cellMass := by
        simp [Finset.sum_const]
  have hmass : shading.mass =
      (selectedCells.card : ENNReal) *
        twoScale.coarse.balanced.incidenceMass := by
    have carrierPartition : ∀ sourceIndex : Fin source.family.card,
        shading.carrier sourceIndex =
          ⋃ cell ∈ selectedCells,
            shading.carrier sourceIndex ∩ wz1PaperGridCube rho cell := by
      intro sourceIndex
      ext point
      constructor
      · intro hpoint
        rcases Set.mem_iUnion₂.mp hpoint.2 with
          ⟨cell, hcell, hpointCell⟩
        exact Set.mem_iUnion₂.mpr
          ⟨cell, hcell, hpoint, hpointCell⟩
      · intro hpoint
        rcases Set.mem_iUnion₂.mp hpoint with
          ⟨_cell, _hcell, hsource, _hpointCell⟩
        exact hsource
    have carrierVolume : ∀ sourceIndex : Fin source.family.card,
        volume (shading.carrier sourceIndex) =
          ∑ cell ∈ selectedCells,
            volume (shading.carrier sourceIndex ∩
              wz1PaperGridCube rho cell) := by
      intro sourceIndex
      calc
        volume (shading.carrier sourceIndex) =
            volume (⋃ cell ∈ selectedCells,
              shading.carrier sourceIndex ∩ wz1PaperGridCube rho cell) :=
          congrArg volume (carrierPartition sourceIndex)
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
          ∑ cell ∈ selectedCells,
            volume (shading.carrier sourceIndex ∩
              wz1PaperGridCube rho cell) := by
        apply Finset.sum_congr rfl
        intro sourceIndex _
        exact carrierVolume sourceIndex
      _ = ∑ cell ∈ selectedCells,
          ∑ sourceIndex : Fin source.family.card,
            volume (shading.carrier sourceIndex ∩
              wz1PaperGridCube rho cell) := by
        rw [Finset.sum_comm]
      _ = ∑ _cell ∈ selectedCells,
          twoScale.coarse.balanced.incidenceMass := by
        apply Finset.sum_congr rfl
        exact hcellMass
      _ = (selectedCells.card : ENNReal) *
          twoScale.coarse.balanced.incidenceMass := by
        simp [Finset.sum_const]
  have hregionVolume : volume selectedRegion =
      (selectedCells.card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
    rw [show selectedRegion =
      ⋃ cell ∈ selectedCells, wz1PaperGridCube rho cell by rfl]
    exact wz1PaperGridCube_volume_biUnion hrho selectedCells
  have hfirstVolume := twoScale.coarse.balanced.fine_union_volume
  have hfirstMass := twoScale.coarse.balanced.fine_mass
  have hcoarseVolume :=
    twoScale.coarse.balanced.toWZ1PaperBalancedCoverData.coarse_union_volume
      twoScale.coarseGrains.extremal.delta_pos
  have hcoarseVolumeRho :
      volume twoScale.coarse.croppedCoarseShading.union =
        (twoScale.coarse.balanced.activeCells.card : ENNReal) *
          volume (wz1PaperGridCube rho (0, 0, 0)) := by
    rw [← twoScale.coarse.balanced.toWZ1PaperBalancedCoverData_activeCells]
    simpa only [twoScale.rhoRequested_eq] using hcoarseVolume
  have hvolumeCross :
      volume shading.union *
          volume twoScale.coarse.croppedCoarseShading.union =
        volume selectedRegion * volume twoScale.coarse.refined.union := by
    rw [hvolume, hcoarseVolumeRho, hregionVolume, hfirstVolume]
    ring
  have hmassCross :
      shading.mass *
          volume twoScale.coarse.croppedCoarseShading.union =
        volume selectedRegion * twoScale.coarse.refined.mass := by
    rw [hmass, hcoarseVolumeRho, hregionVolume, hfirstMass]
    ring
  exact ⟨{
    zeroExtension := zeroExtension
    selectedCells := selectedCells
    selectedCells_eq := rfl
    selectedCells_subset := hselectedSubset
    selectedRegion := selectedRegion
    selectedRegion_eq := rfl
    selectedRegion_eq_coarse := hcoarseRegion
    selectedRegion_measurable := hselectedRegionMeasurable
    shading := shading
    carrier_eq := fun _ => rfl
    subshading := hsub
    whole_cells := hwhole
    union_eq := hunion
    volume_eq := hvolume
    mass_eq := hmass
    coarse_region_volume_eq := hregionVolume
    volume_cross := hvolumeCross
    mass_cross := hmassCross
  }⟩

/-- Every exact first-cover pullback converts coarse whole-cell volume to
source indexed mass with the same physical side-cell factor. -/
theorem PureWZ2SelectedCoarseRegionSourcePullbackData.mass_mul_cube
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {selected : WZ1PaperTubeShading twoScale.coarse.coarse}
    (data : PureWZ2SelectedCoarseRegionSourcePullbackData selected) :
    data.shading.mass *
          volume (wz1PaperGridCube rho (0, 0, 0)) =
      volume selected.union *
        twoScale.coarse.balanced.incidenceMass := by
  rw [data.mass_eq, ← data.selectedRegion_eq_coarse,
    data.coarse_region_volume_eq]
  ring

/-- The source pullback has the same relative density in every retained
side-`rho` cell: its indexed mass times the first-cover cell mass equals its
spatial union volume times the first-cover incidence mass. -/
theorem PureWZ2SelectedCoarseRegionSourcePullbackData.mass_mul_cellMass
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {selected : WZ1PaperTubeShading twoScale.coarse.coarse}
    (data : PureWZ2SelectedCoarseRegionSourcePullbackData selected) :
    data.shading.mass * twoScale.coarse.balanced.cellMass =
      volume data.shading.union *
        twoScale.coarse.balanced.incidenceMass := by
  rw [data.mass_eq, data.volume_eq]
  ring

theorem PureWZ2CoarseHorizontalWindowFamilyData.pullbackToSource
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2CoarseHorizontalWindowFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      twoScale) :
    Nonempty (PureWZ2CoarseRegionSourcePullbackData family) :=
  pureWZ2_pullback_selected_coarse_region family.shading
    family.subshading family.cubical

end Kakeya.Assouad
