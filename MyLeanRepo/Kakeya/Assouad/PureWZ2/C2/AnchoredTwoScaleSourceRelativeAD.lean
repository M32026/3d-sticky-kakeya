import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05AnchoredSynchronizedSecondOwnerCall
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperSubfamilyZeroExtension
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ADTransport
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicADTransfer

/-!
# Source-relative fine selection for anchored two-scale data

The second owner selects whole side-`rho` cells on an enlarged coarse
shading.  This module pulls exactly those cells back to the first owner's
genuine fine shading.  Hence the resulting carrier is a literal subshading of
the supplied source, while its cell mass and incidence mass are unchanged.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2AnchoredSourceRelativeFineSelection
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    (coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent)
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    (fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent) where
  zeroExtension :
    WZ2PaperSubfamilyZeroExtensionData coarse.selected coarse.refined
  selectedCells : Finset (ℤ × ℤ × ℤ)
  selectedCells_eq :
    selectedCells =
      wz1PaperActiveCells fine.refined coarse.coarse_extremal.delta_pos
  selectedRegion : Set Point3
  selectedRegion_eq :
    selectedRegion =
      ⋃ cell ∈ selectedCells,
        wz1PaperGridCube rhoRequested.1 cell
  selectedRegion_measurable : MeasurableSet selectedRegion
  shading : WZ1PaperTubeShading source.family
  carrier_eq : ∀ index, shading.carrier index =
    zeroExtension.ambientShading.carrier index ∩ selectedRegion
  union_eq :
    shading.union =
      zeroExtension.ambientShading.union ∩ selectedRegion
  subshading : PureWZ2PaperIsSubshading shading source.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  selectedCells_subset :
    selectedCells ⊆ coarse.balanced.activeCells
  cell_mass :
    ∀ cell ∈ selectedCells,
      MeasureTheory.volume
          (shading.union ∩ wz1PaperGridCube rhoRequested.1 cell) =
        coarse.balanced.cellMass
  cell_incidence_mass :
    ∀ cell ∈ selectedCells,
      (∑ sourceIndex : Fin source.family.card,
        MeasureTheory.volume
          (shading.carrier sourceIndex ∩
            wz1PaperGridCube rhoRequested.1 cell)) =
        coarse.balanced.incidenceMass

theorem pureWZ2_anchored_sourceRelativeFineSelection
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    (coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent)
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    (fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent) :
    Nonempty (PureWZ2AnchoredSourceRelativeFineSelection coarse fine) := by
  let rho := rhoRequested.1
  have hrho : 0 < rho := coarse.coarse_extremal.delta_pos
  rcases wz2_paper_subfamily_zero_extension coarse.selected coarse.refined with
    ⟨zeroExtension⟩
  let selectedCells := wz1PaperActiveCells fine.refined hrho
  let selectedRegion : Set Point3 :=
    ⋃ cell ∈ selectedCells, wz1PaperGridCube rho cell
  have hregionMeasurable : MeasurableSet selectedRegion :=
    MeasurableSet.biUnion selectedCells.finite_toSet.countable
      (fun cell _ => wz1PaperGridCube_measurable cell)
  let shading : WZ1PaperTubeShading source.family :=
    { carrier := fun index =>
        zeroExtension.ambientShading.carrier index ∩ selectedRegion
      measurable_carrier := fun index =>
        (zeroExtension.ambientShading.measurable_carrier index).inter
          hregionMeasurable
      subset_body := fun index =>
        Set.inter_subset_left.trans
          (zeroExtension.ambientShading.subset_body index) }
  have hselectedSubset :
      selectedCells ⊆ coarse.balanced.activeCells := by
    intro cell hcell
    rcases ((mem_wz1PaperActiveCells fine.refined hrho cell).mp hcell).2 with
      ⟨point, ⟨index, hpointFine⟩, hpointCell⟩
    have hpointCoarse :
        point ∈ coarse.croppedCoarseShading.union :=
      ⟨fine.selected.embedding index, fine.subshading index hpointFine⟩
    rw [coarse.balanced.coarse_union_eq] at hpointCoarse
    rcases Set.mem_iUnion₂.mp hpointCoarse with
      ⟨coarseCell, hcoarseCell, hpointCoarseCell⟩
    have hcellEq : coarseCell = cell :=
      ((mem_wz1PaperGridCube rho coarseCell point).mp
        hpointCoarseCell).symm.trans
      ((mem_wz1PaperGridCube rho cell point).mp hpointCell)
    rwa [hcellEq] at hcoarseCell
  have hunion :
      shading.union =
        zeroExtension.ambientShading.union ∩ selectedRegion := by
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
    exact coarse.subshading selectedIndex hselected
  have hwhole : WZ1PaperIsCubicalShading shading := by
    intro index point hpoint
    have hambientWhole :
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
          zeroExtension.ambientShading.carrier index :=
      zeroExtension.cubical coarse.refined_cubical index point hpoint.1
    rcases zeroExtension.carrier_support index point hpoint.1 with
      ⟨selectedIndex, _heq, hselected⟩
    rcases coarse.balanced.fine_cell_nested
        selectedIndex point hselected with
      ⟨coarseCell, _hcoarseCell, hnested⟩
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨selectedCell, hselectedCell, hpointSelectedCell⟩
    have hpointCoarseCell : point ∈ wz1PaperGridCube rho coarseCell :=
      hnested ((mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) point).mpr rfl)
    have hcellEq : coarseCell = selectedCell :=
      ((mem_wz1PaperGridCube rho coarseCell point).mp
        hpointCoarseCell).symm.trans
      ((mem_wz1PaperGridCube rho selectedCell point).mp
        hpointSelectedCell)
    intro other hother
    exact ⟨hambientWhole hother, Set.mem_iUnion₂.mpr
      ⟨selectedCell, hselectedCell, by
        rw [← hcellEq]
        exact hnested hother⟩⟩
  have hcellMass :
      ∀ cell ∈ selectedCells,
        MeasureTheory.volume
            (shading.union ∩ wz1PaperGridCube rho cell) =
          coarse.balanced.cellMass := by
    intro cell hcell
    have hcellCoarse := hselectedSubset hcell
    have hinter :
        shading.union ∩ wz1PaperGridCube rho cell =
          zeroExtension.ambientShading.union ∩
            wz1PaperGridCube rho cell := by
      rw [hunion]
      ext point
      constructor
      · rintro ⟨⟨hsource, _⟩, hpointCell⟩
        exact ⟨hsource, hpointCell⟩
      · rintro ⟨hsource, hpointCell⟩
        exact ⟨⟨hsource, Set.mem_iUnion₂.mpr
          ⟨cell, hcell, hpointCell⟩⟩, hpointCell⟩
    rw [hinter, zeroExtension.union_eq]
    exact coarse.balanced.fine_cell_mass cell hcellCoarse
  have hcellIncidence :
      ∀ cell ∈ selectedCells,
        (∑ sourceIndex : Fin source.family.card,
          MeasureTheory.volume
            (shading.carrier sourceIndex ∩
              wz1PaperGridCube rho cell)) =
          coarse.balanced.incidenceMass := by
    intro cell hcell
    have hcellCoarse := hselectedSubset hcell
    have hsumAmbient :
        (∑ sourceIndex : Fin source.family.card,
          MeasureTheory.volume
            (zeroExtension.ambientShading.carrier sourceIndex ∩
              wz1PaperGridCube rho cell)) =
          ∑ selectedIndex : Fin coarse.selected.family.card,
            MeasureTheory.volume
              (coarse.refined.carrier selectedIndex ∩
                wz1PaperGridCube rho cell) := by
      let supported : Finset (Fin source.family.card) :=
        Finset.univ.map coarse.selected.embedding
      calc
        _ = ∑ sourceIndex ∈ supported,
              MeasureTheory.volume
                (zeroExtension.ambientShading.carrier sourceIndex ∩
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
        _ = _ := by
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
      _ = _ := hsumAmbient
      _ = coarse.balanced.incidenceMass :=
        coarse.balanced.fine_cell_incidence_mass cell hcellCoarse
  exact ⟨{
    zeroExtension := zeroExtension
    selectedCells := selectedCells
    selectedCells_eq := rfl
    selectedRegion := selectedRegion
    selectedRegion_eq := rfl
    selectedRegion_measurable := hregionMeasurable
    shading := shading
    carrier_eq := fun _ => rfl
    union_eq := hunion
    subshading := hsub
    whole_cells := hwhole
    selectedCells_subset := hselectedSubset
    cell_mass := hcellMass
    cell_incidence_mass := hcellIncidence
  }⟩

namespace PureWZ2AnchoredSourceRelativeFineSelection

variable
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}

/-- The exact selected-cell pullback retains the balanced volume cell by
cell.  This is an equality, not hereditary AD or an arbitrary-subset bound. -/
theorem volume_eq
    (selection : PureWZ2AnchoredSourceRelativeFineSelection coarse fine) :
    MeasureTheory.volume selection.shading.union =
      (selection.selectedCells.card : ENNReal) *
        coarse.balanced.cellMass := by
  have hpartition :
      selection.shading.union =
        ⋃ cell ∈ selection.selectedCells,
          selection.shading.union ∩
            wz1PaperGridCube rhoRequested.1 cell := by
    ext point
    constructor
    · intro hpoint
      have hregion :
          point ∈ selection.selectedRegion := by
        rw [selection.union_eq] at hpoint
        exact hpoint.2
      rw [selection.selectedRegion_eq] at hregion
      rcases Set.mem_iUnion₂.mp hregion with ⟨cell, hcell, hpointCell⟩
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpoint, hpointCell⟩
    · rintro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨_cell, _hcell, hshading, _hpointCell⟩
      exact hshading
  rw [hpartition]
  have hdisjoint :
      (selection.selectedCells : Set (ℤ × ℤ × ℤ)).PairwiseDisjoint
        (fun cell =>
          selection.shading.union ∩
            wz1PaperGridCube rhoRequested.1 cell) := by
    intro first _ second _ hne
    exact (wz1PaperGridCube_disjoint hne).mono
      Set.inter_subset_right Set.inter_subset_right
  have hmeasurable :
      ∀ cell ∈ selection.selectedCells,
        MeasurableSet
          (selection.shading.union ∩
            wz1PaperGridCube rhoRequested.1 cell) := by
    intro cell _
    exact selection.shading.union_measurable.inter
      (wz1PaperGridCube_measurable cell)
  rw [MeasureTheory.measure_biUnion_finset hdisjoint hmeasurable]
  calc
    (∑ cell ∈ selection.selectedCells,
        MeasureTheory.volume
          (selection.shading.union ∩
            wz1PaperGridCube rhoRequested.1 cell)) =
        ∑ _cell ∈ selection.selectedCells,
          coarse.balanced.cellMass := by
            apply Finset.sum_congr rfl
            intro cell hcell
            exact selection.cell_mass cell hcell
    _ = (selection.selectedCells.card : ENNReal) *
          coarse.balanced.cellMass := by
            simp [Finset.sum_const]

/-- Indexed mass is preserved on the same selected cells. -/
theorem mass_eq
    (selection : PureWZ2AnchoredSourceRelativeFineSelection coarse fine) :
    selection.shading.mass =
      (selection.selectedCells.card : ENNReal) *
        coarse.balanced.incidenceMass := by
  have hcarrier :
      ∀ sourceIndex : Fin source.family.card,
        selection.shading.carrier sourceIndex =
          ⋃ cell ∈ selection.selectedCells,
            selection.shading.carrier sourceIndex ∩
              wz1PaperGridCube rhoRequested.1 cell := by
    intro sourceIndex
    ext point
    constructor
    · intro hpoint
      rw [selection.carrier_eq sourceIndex] at hpoint
      have hregion := hpoint.2
      rw [selection.selectedRegion_eq] at hregion
      rcases Set.mem_iUnion₂.mp hregion with
        ⟨cell, hcell, hpointCell⟩
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, by
        rw [selection.carrier_eq sourceIndex]
        exact hpoint, hpointCell⟩
    · rintro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨_cell, _hcell, hsource, _hpointCell⟩
      exact hsource
  have hcarrierVolume :
      ∀ sourceIndex : Fin source.family.card,
        MeasureTheory.volume (selection.shading.carrier sourceIndex) =
          ∑ cell ∈ selection.selectedCells,
            MeasureTheory.volume
              (selection.shading.carrier sourceIndex ∩
                wz1PaperGridCube rhoRequested.1 cell) := by
    intro sourceIndex
    calc
      MeasureTheory.volume (selection.shading.carrier sourceIndex) =
          MeasureTheory.volume
            (⋃ cell ∈ selection.selectedCells,
              selection.shading.carrier sourceIndex ∩
                wz1PaperGridCube rhoRequested.1 cell) :=
        congrArg MeasureTheory.volume (hcarrier sourceIndex)
      _ = _ := by
        apply MeasureTheory.measure_biUnion_finset
        · intro first _ second _ hne
          exact (wz1PaperGridCube_disjoint hne).mono
            Set.inter_subset_right Set.inter_subset_right
        · intro cell _
          exact (selection.shading.measurable_carrier sourceIndex).inter
            (wz1PaperGridCube_measurable cell)
  calc
    selection.shading.mass =
        ∑ sourceIndex : Fin source.family.card,
          ∑ cell ∈ selection.selectedCells,
            MeasureTheory.volume
              (selection.shading.carrier sourceIndex ∩
                wz1PaperGridCube rhoRequested.1 cell) := by
          apply Finset.sum_congr rfl
          intro sourceIndex _
          exact hcarrierVolume sourceIndex
    _ = ∑ cell ∈ selection.selectedCells,
          ∑ sourceIndex : Fin source.family.card,
            MeasureTheory.volume
              (selection.shading.carrier sourceIndex ∩
                wz1PaperGridCube rhoRequested.1 cell) := by
          rw [Finset.sum_comm]
    _ = ∑ _cell ∈ selection.selectedCells,
          coarse.balanced.incidenceMass := by
          apply Finset.sum_congr rfl
          intro cell hcell
          exact selection.cell_incidence_mass cell hcell
    _ = (selection.selectedCells.card : ENNReal) *
          coarse.balanced.incidenceMass := by
          simp [Finset.sum_const]

/-- The source-relative selected fine union inherits global AD literally from
the supplied source, then only weakens the base scale. -/
theorem global_ad
    (selection : PureWZ2AnchoredSourceRelativeFineSelection coarse fine)
    (constant_absorption :
      Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN rhoRequested.1 (-coarseLoss))
    (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    PureWZ2PaperADSet1
      (scalarProjection
        (globalGrainDirection (source.globalGrains.slope z))
        (horizontalSlice selection.shading.union z))
      rhoRequested.1 (1 - sigma)
      (Kakeya.realRpowENN rhoRequested.1 (-coarseLoss)) := by
  have hsub :
      horizontalSlice selection.shading.union z ⊆
        horizontalSlice source.shading.union z := by
    rintro point ⟨hpoint, rfl⟩
    exact ⟨selection.subshading.union_subset hpoint, rfl⟩
  have hrestricted := (source.globalGrains.global_ad z hz).mono
    (Set.image_mono hsub)
  have hscale := hrestricted.weaken_scale coarse.coarse_extremal.delta_pos
    rhoRequested.property.1
  exact hscale.mono_const constant_absorption
    (by simp [Kakeya.realRpowENN])

end PureWZ2AnchoredSourceRelativeFineSelection

end Kakeya.Assouad

end
