import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OneScaleTwoScaleSticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Section6CoverAdapter
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.StickyMultiplicity
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperSubfamilyZeroExtension
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers

/-!
# Pull back the second sticky cell selection to the original pure source

The second sticky output selects whole `rho`-cells in the actual coarse
shading of the first output.  The first balanced cover records that every
retained `delta`-cell is wholly nested in one of those `rho`-cells.  Hence the
second spatial selection can be pulled back without cutting fine cells and
without changing the first-stage balanced mass on any retained cell.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2TwoScaleCellPullbackData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent) where
  zeroExtension :
    WZ2PaperSubfamilyZeroExtensionData
      twoScale.coarse.selected twoScale.coarse.refined
  selectedCells : Finset (ℤ × ℤ × ℤ)
  selectedCells_eq :
    selectedCells =
      wz1PaperActiveCells twoScale.fine.refined
        twoScale.coarse.coarse_extremal.delta_pos
  selectedRegion : Set Point3
  selectedRegion_eq :
    selectedRegion =
      ⋃ cell ∈ selectedCells, wz1PaperGridCube rho cell
  selectedRegion_measurable : MeasurableSet selectedRegion
  shading : WZ1PaperTubeShading source.family
  carrier_eq :
    ∀ index,
      shading.carrier index =
        zeroExtension.ambientShading.carrier index ∩ selectedRegion
  subshading : PureWZ2PaperIsSubshading shading source.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  union_eq :
    shading.union =
      zeroExtension.ambientShading.union ∩ selectedRegion
  selectedCells_subset :
    selectedCells ⊆ twoScale.coarse.balanced.activeCells
  cell_mass :
    ∀ cell ∈ selectedCells,
      MeasureTheory.volume
          (shading.union ∩ wz1PaperGridCube rho cell) =
        twoScale.coarse.balanced.cellMass
  cell_incidence_mass :
    ∀ cell ∈ selectedCells,
      (∑ sourceIndex : Fin source.family.card,
        MeasureTheory.volume
          (shading.carrier sourceIndex ∩
            wz1PaperGridCube rho cell)) =
        twoScale.coarse.balanced.incidenceMass
  volume_eq :
    MeasureTheory.volume shading.union =
      (selectedCells.card : ENNReal) *
        twoScale.coarse.balanced.cellMass
  mass_eq :
    shading.mass =
      (selectedCells.card : ENNReal) *
        twoScale.coarse.balanced.incidenceMass
  balanced_volume_cross :
    MeasureTheory.volume shading.union *
        MeasureTheory.volume
          twoScale.coarse.croppedCoarseShading.union =
      MeasureTheory.volume twoScale.fine.refined.union *
        MeasureTheory.volume twoScale.coarse.refined.union
  balanced_mass_cross :
    shading.mass *
        MeasureTheory.volume
          twoScale.coarse.croppedCoarseShading.union =
      twoScale.coarse.refined.mass *
        MeasureTheory.volume twoScale.fine.refined.union
  selected_count_mul_coarse_volume :
    (selectedCells.card : ENNReal) *
        MeasureTheory.volume
          (wz1PaperGridCube rho (0, 0, 0)) =
      MeasureTheory.volume twoScale.fine.refined.union

theorem PureWZ2OneScaleTwoScaleStickyData.pullbackSelectedCells
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent) :
    Nonempty (PureWZ2TwoScaleCellPullbackData twoScale) := by
  have hrhoEq := twoScale.rhoRequested_eq
  have hrho : 0 < twoScale.rhoRequested.1 :=
    source.extremal.delta_pos.trans_le
      twoScale.rhoRequested.property.1
  rcases
      wz2_paper_subfamily_zero_extension
        twoScale.coarse.selected twoScale.coarse.refined with
    ⟨zeroExtension⟩
  let selectedCells :=
    wz1PaperActiveCells twoScale.fine.refined hrho
  let selectedRegion : Set Point3 :=
    ⋃ cell ∈ selectedCells,
      wz1PaperGridCube rho cell
  have hselectedRegionMeasurable : MeasurableSet selectedRegion := by
    exact
      MeasurableSet.biUnion (Finset.finite_toSet selectedCells).countable
        (fun cell _ => wz1PaperGridCube_measurable cell)
  let shading : WZ1PaperTubeShading source.family :=
    { carrier := fun index =>
        zeroExtension.ambientShading.carrier index ∩ selectedRegion
      measurable_carrier := fun index =>
        (zeroExtension.ambientShading.measurable_carrier index).inter
          hselectedRegionMeasurable
      subset_body := fun index =>
        Set.inter_subset_left.trans
          (zeroExtension.ambientShading.subset_body index) }
  have hselectedSubset :
      selectedCells ⊆ twoScale.coarse.balanced.activeCells := by
    intro cell hcell
    rcases
        ((mem_wz1PaperActiveCells twoScale.fine.refined hrho cell).mp
          hcell).2 with
      ⟨point, ⟨index, hpointFine⟩, hpointCell⟩
    have hpointCoarse :
        point ∈ twoScale.coarse.croppedCoarseShading.union :=
      ⟨twoScale.fine.selected.embedding index,
        twoScale.coarseGrains.subshading
          (twoScale.fine.selected.embedding index)
          (twoScale.fine.subshading index hpointFine)⟩
    rw [twoScale.coarse.balanced.coarse_union_eq] at hpointCoarse
    rcases Set.mem_iUnion₂.mp hpointCoarse with
      ⟨coarseCell, hcoarseCell, hpointCoarseCell⟩
    have hcellEq : coarseCell = cell :=
      ((mem_wz1PaperGridCube twoScale.rhoRequested.1 coarseCell point).mp
        hpointCoarseCell).symm.trans
      ((mem_wz1PaperGridCube twoScale.rhoRequested.1 cell point).mp
        hpointCell)
    rwa [hcellEq] at hcoarseCell
  have hunionEq :
      shading.union =
        zeroExtension.ambientShading.union ∩ selectedRegion := by
    ext point
    constructor
    · rintro ⟨index, hpointSource, hpointRegion⟩
      exact ⟨⟨index, hpointSource⟩, hpointRegion⟩
    · rintro ⟨⟨index, hpointSource⟩, hpointRegion⟩
      exact ⟨index, hpointSource, hpointRegion⟩
  have hsubshading :
      PureWZ2PaperIsSubshading shading source.shading := by
    intro index point hpoint
    rcases zeroExtension.carrier_support index point hpoint.1 with
      ⟨selectedIndex, heq, hselected⟩
    subst index
    exact twoScale.coarse.subshading selectedIndex hselected
  have hwhole : WZ1PaperIsCubicalShading shading := by
    intro index point hpoint
    have hambientWhole :
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
          zeroExtension.ambientShading.carrier index :=
      zeroExtension.cubical twoScale.coarse.refined_cubical
        index point hpoint.1
    rcases zeroExtension.carrier_support index point hpoint.1 with
      ⟨selectedIndex, heq, hselected⟩
    have hnested :=
      twoScale.coarse.balanced.fine_cell_nested
        selectedIndex point hselected
    rcases hnested with ⟨coarseCell, hcoarseCell, hnested⟩
    have hpointSelected : point ∈ selectedRegion := hpoint.2
    rcases Set.mem_iUnion₂.mp hpointSelected with
      ⟨selectedCell, hselectedCell, hpointSelectedCell⟩
    have hpointCoarseCell : point ∈ wz1PaperGridCube rho coarseCell := by
      rw [← hrhoEq]
      exact hnested ((mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) point).mpr rfl)
    have hcellEq : coarseCell = selectedCell := by
      exact
        ((mem_wz1PaperGridCube rho coarseCell point).mp
          hpointCoarseCell).symm.trans
        ((mem_wz1PaperGridCube rho selectedCell point).mp
          hpointSelectedCell)
    intro other hother
    refine ⟨hambientWhole hother, ?_⟩
    exact Set.mem_iUnion₂.mpr
      ⟨selectedCell, hselectedCell, by
        rw [← hcellEq]
        rw [← hrhoEq]
        exact hnested hother⟩
  have hcellMass :
      ∀ cell ∈ selectedCells,
        MeasureTheory.volume
            (shading.union ∩ wz1PaperGridCube rho cell) =
          twoScale.coarse.balanced.cellMass := by
    intro cell hcell
    have hcellCoarse : cell ∈ twoScale.coarse.balanced.activeCells :=
      hselectedSubset hcell
    have hinter :
        shading.union ∩ wz1PaperGridCube rho cell =
          zeroExtension.ambientShading.union ∩
            wz1PaperGridCube rho cell := by
      rw [hunionEq]
      ext point
      constructor
      · rintro ⟨⟨hsource, _⟩, hpointCell⟩
        exact ⟨hsource, hpointCell⟩
      · rintro ⟨hsource, hpointCell⟩
        refine ⟨⟨hsource, ?_⟩, hpointCell⟩
        exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointCell⟩
    rw [hinter, zeroExtension.union_eq]
    simpa [hrhoEq] using
      twoScale.coarse.balanced.fine_cell_mass cell hcellCoarse
  have hcellIncidenceMass :
      ∀ cell ∈ selectedCells,
        (∑ sourceIndex : Fin source.family.card,
          MeasureTheory.volume
            (shading.carrier sourceIndex ∩
              wz1PaperGridCube rho cell)) =
          twoScale.coarse.balanced.incidenceMass := by
    intro cell hcell
    have hcellCoarse := hselectedSubset hcell
    have hsumAmbient :
        (∑ sourceIndex : Fin source.family.card,
          MeasureTheory.volume
            (zeroExtension.ambientShading.carrier sourceIndex ∩
              wz1PaperGridCube rho cell)) =
          ∑ selectedIndex : Fin twoScale.coarse.selected.family.card,
            MeasureTheory.volume
              (twoScale.coarse.refined.carrier selectedIndex ∩
                wz1PaperGridCube rho cell) := by
      let supported : Finset (Fin source.family.card) :=
        Finset.univ.map twoScale.coarse.selected.embedding
      calc
        (∑ sourceIndex : Fin source.family.card,
            MeasureTheory.volume
              (zeroExtension.ambientShading.carrier sourceIndex ∩
                wz1PaperGridCube rho cell)) =
            ∑ sourceIndex ∈ supported,
              MeasureTheory.volume
                (zeroExtension.ambientShading.carrier sourceIndex ∩
                  wz1PaperGridCube rho cell) := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro sourceIndex _ hnot
          have hempty := zeroExtension.carrier_support
          have hcarrier :
              zeroExtension.ambientShading.carrier sourceIndex = ∅ := by
            apply Set.not_nonempty_iff_eq_empty.mp
            rintro ⟨point, hpoint⟩
            rcases hempty sourceIndex point hpoint with
              ⟨selectedIndex, heq, _⟩
            exact hnot (Finset.mem_map.mpr
              ⟨selectedIndex, Finset.mem_univ _, heq⟩)
          rw [hcarrier]
          simp
        _ =
            ∑ selectedIndex : Fin twoScale.coarse.selected.family.card,
              MeasureTheory.volume
                (twoScale.coarse.refined.carrier selectedIndex ∩
                  wz1PaperGridCube rho cell) := by
          rw [Finset.sum_map]
          apply Finset.sum_congr rfl
          intro selectedIndex _
          rw [zeroExtension.carrier_embedding selectedIndex]
    calc
      (∑ sourceIndex : Fin source.family.card,
          MeasureTheory.volume
            (shading.carrier sourceIndex ∩
              wz1PaperGridCube rho cell)) =
          ∑ sourceIndex : Fin source.family.card,
            MeasureTheory.volume
              (zeroExtension.ambientShading.carrier sourceIndex ∩
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
      _ =
          ∑ selectedIndex : Fin twoScale.coarse.selected.family.card,
            MeasureTheory.volume
              (twoScale.coarse.refined.carrier selectedIndex ∩
                wz1PaperGridCube rho cell) := hsumAmbient
      _ = twoScale.coarse.balanced.incidenceMass := by
        simpa [hrhoEq] using
          twoScale.coarse.balanced.fine_cell_incidence_mass
            cell hcellCoarse
  have hvolumeEq :
      MeasureTheory.volume shading.union =
        (selectedCells.card : ENNReal) *
          twoScale.coarse.balanced.cellMass := by
    rw [hunionEq]
    let firstBalanced :=
      twoScale.coarse.balanced.toWZ1PaperBalancedCoverData
    have hpartition :
        zeroExtension.ambientShading.union ∩ selectedRegion =
          ⋃ cell ∈ selectedCells,
            zeroExtension.ambientShading.union ∩
              wz1PaperGridCube rho cell := by
      ext point
      simp [selectedRegion]
    rw [hpartition]
    have hDisjoint :
        (selectedCells : Set (ℤ × ℤ × ℤ)).PairwiseDisjoint
          (fun cell =>
            zeroExtension.ambientShading.union ∩
              wz1PaperGridCube rho cell) := by
      intro first _ second _ hne
      exact
        (wz1PaperGridCube_disjoint hne).mono
          Set.inter_subset_right Set.inter_subset_right
    have hMeasurable :
        ∀ cell ∈ selectedCells,
          MeasurableSet
            (zeroExtension.ambientShading.union ∩
              wz1PaperGridCube rho cell) := by
      intro cell _
      exact zeroExtension.ambientShading.union_measurable.inter
        (wz1PaperGridCube_measurable cell)
    rw [MeasureTheory.measure_biUnion_finset hDisjoint hMeasurable]
    calc
      (∑ cell ∈ selectedCells,
          MeasureTheory.volume
            (zeroExtension.ambientShading.union ∩
              wz1PaperGridCube rho cell)) =
          ∑ _cell ∈ selectedCells,
            twoScale.coarse.balanced.cellMass := by
        apply Finset.sum_congr rfl
        intro cell hcell
        rw [zeroExtension.union_eq]
        simpa [hrhoEq] using
          twoScale.coarse.balanced.fine_cell_mass
            cell (hselectedSubset hcell)
      _ =
          (selectedCells.card : ENNReal) *
            twoScale.coarse.balanced.cellMass := by
        simp [Finset.sum_const]
  have hmassEq :
      shading.mass =
        (selectedCells.card : ENNReal) *
          twoScale.coarse.balanced.incidenceMass := by
    have carrierPartition :
        ∀ sourceIndex : Fin source.family.card,
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
    have carrierVolume :
        ∀ sourceIndex : Fin source.family.card,
          MeasureTheory.volume (shading.carrier sourceIndex) =
            ∑ cell ∈ selectedCells,
              MeasureTheory.volume
                (shading.carrier sourceIndex ∩
                  wz1PaperGridCube rho cell) := by
      intro sourceIndex
      calc
        MeasureTheory.volume (shading.carrier sourceIndex) =
            MeasureTheory.volume
              (⋃ cell ∈ selectedCells,
                shading.carrier sourceIndex ∩
                  wz1PaperGridCube rho cell) :=
          congrArg MeasureTheory.volume (carrierPartition sourceIndex)
        _ =
            ∑ cell ∈ selectedCells,
              MeasureTheory.volume
                (shading.carrier sourceIndex ∩
                  wz1PaperGridCube rho cell) := by
          apply MeasureTheory.measure_biUnion_finset
          · intro first _ second _ hne
            exact (wz1PaperGridCube_disjoint hne).mono
              Set.inter_subset_right Set.inter_subset_right
          · intro cell _
            exact (shading.measurable_carrier sourceIndex).inter
              (wz1PaperGridCube_measurable cell)
    calc
      shading.mass =
          ∑ sourceIndex : Fin source.family.card,
            ∑ cell ∈ selectedCells,
              MeasureTheory.volume
                (shading.carrier sourceIndex ∩
                  wz1PaperGridCube rho cell) := by
        apply Finset.sum_congr rfl
        intro sourceIndex _
        exact carrierVolume sourceIndex
      _ =
          ∑ cell ∈ selectedCells,
            ∑ sourceIndex : Fin source.family.card,
              MeasureTheory.volume
                (shading.carrier sourceIndex ∩
                  wz1PaperGridCube rho cell) := by
        rw [Finset.sum_comm]
      _ =
          ∑ _cell ∈ selectedCells,
            twoScale.coarse.balanced.incidenceMass := by
        apply Finset.sum_congr rfl
        exact hcellIncidenceMass
      _ =
          (selectedCells.card : ENNReal) *
            twoScale.coarse.balanced.incidenceMass := by
        simp [Finset.sum_const]
  have hselectedCountCoarseVolume :
      (selectedCells.card : ENNReal) *
          MeasureTheory.volume
            (wz1PaperGridCube rho (0, 0, 0)) =
        MeasureTheory.volume twoScale.fine.refined.union := by
    have hAtRequestedScale :
        (selectedCells.card : ENNReal) *
            MeasureTheory.volume
              (wz1PaperGridCube twoScale.rhoRequested.1 (0, 0, 0)) =
          MeasureTheory.volume twoScale.fine.refined.union := by
      have hunion :=
        twoScale.fine.refined_cubical.union_eq_activeCells hrho
      calc
        (selectedCells.card : ENNReal) *
              MeasureTheory.volume
                (wz1PaperGridCube twoScale.rhoRequested.1 (0, 0, 0)) =
            MeasureTheory.volume
              (⋃ cell ∈ selectedCells,
                wz1PaperGridCube twoScale.rhoRequested.1 cell) :=
          (wz1PaperGridCube_volume_biUnion hrho selectedCells).symm
        _ = MeasureTheory.volume twoScale.fine.refined.union :=
          congrArg MeasureTheory.volume hunion.symm
    simpa only [hrhoEq] using hAtRequestedScale
  have hfirstVolume := twoScale.coarse.balanced.fine_union_volume
  have hfirstMass := twoScale.coarse.balanced.fine_mass
  have hfirstCoarseVolume :=
    twoScale.coarse.balanced.toWZ1PaperBalancedCoverData.coarse_union_volume
      hrho
  have hfirstCoarseVolume' :
      MeasureTheory.volume
          twoScale.coarse.croppedCoarseShading.union =
        (twoScale.coarse.balanced.activeCells.card : ENNReal) *
          MeasureTheory.volume
            (wz1PaperGridCube rho (0, 0, 0)) := by
    rw [← twoScale.coarse.balanced.toWZ1PaperBalancedCoverData_activeCells]
    simpa only [hrhoEq] using hfirstCoarseVolume
  have hbalancedVolumeCross :
      MeasureTheory.volume shading.union *
          MeasureTheory.volume
            twoScale.coarse.croppedCoarseShading.union =
        MeasureTheory.volume twoScale.fine.refined.union *
          MeasureTheory.volume twoScale.coarse.refined.union := by
    rw [hvolumeEq, hfirstVolume, hfirstCoarseVolume',
      ← hselectedCountCoarseVolume]
    ring
  have hbalancedMassCross :
      shading.mass *
          MeasureTheory.volume
            twoScale.coarse.croppedCoarseShading.union =
        twoScale.coarse.refined.mass *
          MeasureTheory.volume twoScale.fine.refined.union := by
    rw [hmassEq, hfirstMass, hfirstCoarseVolume',
      ← hselectedCountCoarseVolume]
    ring
  exact
    ⟨{ zeroExtension := zeroExtension
       selectedCells := selectedCells
       selectedCells_eq := rfl
       selectedRegion := selectedRegion
       selectedRegion_eq := rfl
       selectedRegion_measurable := hselectedRegionMeasurable
       shading := shading
       carrier_eq := fun _ => rfl
       subshading := hsubshading
       whole_cells := hwhole
       union_eq := hunionEq
       selectedCells_subset := hselectedSubset
       cell_mass := hcellMass
       cell_incidence_mass := hcellIncidenceMass
       volume_eq := hvolumeEq
       mass_eq := hmassEq
       balanced_volume_cross := hbalancedVolumeCross
       balanced_mass_cross := hbalancedMassCross
       selected_count_mul_coarse_volume :=
         hselectedCountCoarseVolume }⟩

end Kakeya.Assouad
