import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCropCellPruningStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCropBoundaryGeometry
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyBoundaryCellPruningGeometry
import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers

/-! # Delete coarse cells crossing the cropped paper window -/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

private theorem bad_coarse_cell_intersection_subset_boundary
    {rho : ℝ} (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    {cell : WZ2PaperCellIndex}
    (hbad :
      ¬ (wz1PaperGridCube rho cell ⊆
        Kakeya.Streamlined.axisBox 2 2 2)) :
    wz1PaperGridCube rho cell ∩
        Kakeya.Streamlined.axisBox 2 2 2 ⊆
      wz2PaperCropBoundaryRegion rho := by
  intro point hpoint
  have hpointCube := hpoint.1
  have hpointBox := hpoint.2
  rw [mem_gridCube_iff hrho] at hpointCube
  rcases Set.not_subset.mp hbad with
    ⟨outside, houtsideCube, houtsideBox⟩
  have houtsideCoordinates :=
    (mem_gridCube_iff hrho).mp houtsideCube
  have hpointBounds :
      |point 0| ≤ 1 ∧ |point 1| ≤ 1 ∧ |point 2| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hpointBox
  have houtsideDisjunction :
      ¬ |outside 0| ≤ 1 ∨
        ¬ |outside 1| ≤ 1 ∨
          ¬ |outside 2| ≤ 1 := by
    by_contra h
    push Not at h
    apply houtsideBox
    simpa [Kakeya.Streamlined.axisBox] using h
  rcases houtsideDisjunction with hzero | hone | htwo
  · refine ⟨hpointBox, 0, ?_⟩
    have hzero' : |outside 0| > 1 := lt_of_not_ge hzero
    by_cases houtsideNonneg : 0 ≤ outside 0
    · have hlowerPoint := (hpointCube 0).1
      have hupperOutside := (houtsideCoordinates 0).2
      rw [abs_of_nonneg houtsideNonneg] at hzero'
      have hpointLower : -1 ≤ point 0 := by
        exact (abs_le.mp hpointBounds.1).1
      have hpointUpper : point 0 ≤ 1 := by
        exact (abs_le.mp hpointBounds.1).2
      by_cases hp : 0 ≤ point 0
      · rw [abs_of_nonneg hp]
        linarith
      · rw [abs_of_neg (lt_of_not_ge hp)]
        linarith
    · have hupperPoint := (hpointCube 0).2
      have hlowerOutside := (houtsideCoordinates 0).1
      have houtsideNeg : outside 0 < 0 := lt_of_not_ge houtsideNonneg
      rw [abs_of_neg houtsideNeg] at hzero'
      have hpointUpper : point 0 ≤ 1 := by
        exact (abs_le.mp hpointBounds.1).2
      by_cases hp : 0 ≤ point 0
      · rw [abs_of_nonneg hp]
        linarith
      · rw [abs_of_neg (lt_of_not_ge hp)]
        linarith
  · refine ⟨hpointBox, 1, ?_⟩
    have hone' : |outside 1| > 1 := lt_of_not_ge hone
    by_cases houtsideNonneg : 0 ≤ outside 1
    · have hlowerPoint := (hpointCube 1).1
      have hupperOutside := (houtsideCoordinates 1).2
      rw [abs_of_nonneg houtsideNonneg] at hone'
      have hpointLower : -1 ≤ point 1 := by
        exact (abs_le.mp hpointBounds.2.1).1
      have hpointUpper : point 1 ≤ 1 := by
        exact (abs_le.mp hpointBounds.2.1).2
      by_cases hp : 0 ≤ point 1
      · rw [abs_of_nonneg hp]
        linarith
      · rw [abs_of_neg (lt_of_not_ge hp)]
        linarith
    · have hupperPoint := (hpointCube 1).2
      have hlowerOutside := (houtsideCoordinates 1).1
      have houtsideNeg : outside 1 < 0 := lt_of_not_ge houtsideNonneg
      rw [abs_of_neg houtsideNeg] at hone'
      have hpointUpper : point 1 ≤ 1 := by
        exact (abs_le.mp hpointBounds.2.1).2
      by_cases hp : 0 ≤ point 1
      · rw [abs_of_nonneg hp]
        linarith
      · rw [abs_of_neg (lt_of_not_ge hp)]
        linarith
  · refine ⟨hpointBox, 2, ?_⟩
    have htwo' : |outside 2| > 1 := lt_of_not_ge htwo
    by_cases houtsideNonneg : 0 ≤ outside 2
    · have hlowerPoint := (hpointCube 2).1
      have hupperOutside := (houtsideCoordinates 2).2
      rw [abs_of_nonneg houtsideNonneg] at htwo'
      have hpointLower : -1 ≤ point 2 := by
        exact (abs_le.mp hpointBounds.2.2).1
      have hpointUpper : point 2 ≤ 1 := by
        exact (abs_le.mp hpointBounds.2.2).2
      by_cases hp : 0 ≤ point 2
      · rw [abs_of_nonneg hp]
        linarith
      · rw [abs_of_neg (lt_of_not_ge hp)]
        linarith
    · have hupperPoint := (hpointCube 2).2
      have hlowerOutside := (houtsideCoordinates 2).1
      have houtsideNeg : outside 2 < 0 := lt_of_not_ge houtsideNonneg
      rw [abs_of_neg houtsideNeg] at htwo'
      have hpointUpper : point 2 ≤ 1 := by
        exact (abs_le.mp hpointBounds.2.2).2
      by_cases hp : 0 ≤ point 2
      · rw [abs_of_nonneg hp]
        linarith
      · rw [abs_of_neg (lt_of_not_ge hp)]
        linarith

theorem wz2_paper_crop_cell_pruning_from_boundary_mass :
    WZ2PaperCropCellPruningFromBoundaryMassStatement := by
  intro delta rho hdelta hrho hrhoOne fine shading coarseCells
    availableFineCells balanced multiplicityCap hMultiplicity hBoundarySmall
  let retainedCoarseCells :=
    balanced.retainedCoarseCells.filter fun cell =>
      wz1PaperGridCube rho cell ⊆
        Kakeya.Streamlined.axisBox 2 2 2
  let selectedFineCells := balanced.selectedFineCells
  let retainedFineCells :=
    retainedCoarseCells.biUnion selectedFineCells
  let refined :=
    wz2RefinedShading balanced.refined retainedFineCells
  let badCoarseCells :=
    balanced.retainedCoarseCells \ retainedCoarseCells
  let badRegion : Set Point3 :=
    ⋃ cell ∈ badCoarseCells,
      wz1PaperGridCube rho cell
  have hRetainedFineActive :
      ∀ fineCell ∈ retainedFineCells,
        fineCell ∈
          wz1PaperActiveCells balanced.refined hdelta := by
    intro fineCell hfine
    rcases Finset.mem_biUnion.mp hfine with
      ⟨cell, hcell, hfineCell⟩
    have hcellOld :
        cell ∈ balanced.retainedCoarseCells :=
      (Finset.mem_filter.mp hcell).1
    have hcontain :=
      balanced.fine_cell_containment cell hcellOld fineCell hfineCell
    let hpoint : Point3 :=
      cellCorner delta fineCell
    have hpointFine :
        hpoint ∈ wz1PaperGridCube delta fineCell :=
      cellCorner_mem_gridCube hdelta fineCell
    have hpointCoarse :
        hpoint ∈ wz1PaperGridCube rho cell :=
      hcontain hpointFine
    have hpointUnion : hpoint ∈ balanced.refined.union := by
      rw [balanced.refined_union_eq]
      exact Set.mem_iUnion₂.mpr
        ⟨fineCell, by
          rw [balanced.retainedFineCells_eq]
          exact Finset.mem_biUnion.mpr
            ⟨cell, hcellOld, hfineCell⟩,
          hpointFine⟩
    rw [mem_wz1PaperActiveCells]
    have hindex :
        wz1PaperGridIndex delta hpoint = fineCell :=
      (mem_wz1PaperGridCube delta fineCell hpoint).mp hpointFine
    exact
      ⟨by
          rw [← hindex]
          exact
            paper_point_gridIndex_in_window hdelta
              (shading_union_subset_axisBox hpointUnion),
        ⟨hpoint, hpointUnion, hpointFine⟩⟩
  have hRefinedUnion :
      refined.union =
        ⋃ fineCell ∈ retainedFineCells,
          wz1PaperGridCube delta fineCell :=
    wz2RefinedShading_union_eq
      balanced.refined_cubical hdelta hRetainedFineActive
  have hBadSubset :
      balanced.refined.union \ refined.union ⊆
        badRegion ∩ Kakeya.Streamlined.axisBox 2 2 2 := by
    intro point hpoint
    have hpointBox :
        point ∈ Kakeya.Streamlined.axisBox 2 2 2 := by
      exact shading_union_subset_axisBox hpoint.1
    rw [balanced.refined_union_eq] at hpoint
    rcases Set.mem_iUnion₂.mp hpoint.1 with
      ⟨fineCell, hfineOld, hpointFine⟩
    rw [balanced.retainedFineCells_eq] at hfineOld
    rcases Finset.mem_biUnion.mp hfineOld with
      ⟨cell, hcellOld, hfineCell⟩
    have hpointCoarse :=
      balanced.fine_cell_containment
        cell hcellOld fineCell hfineCell hpointFine
    have hcellBad : cell ∈ badCoarseCells := by
      apply Finset.mem_sdiff.mpr
      refine ⟨hcellOld, ?_⟩
      intro hcellRetained
      have hfineRetained : fineCell ∈ retainedFineCells :=
        Finset.mem_biUnion.mpr
          ⟨cell, hcellRetained, hfineCell⟩
      have hpointRefined : point ∈ refined.union := by
        rw [hRefinedUnion]
        exact Set.mem_iUnion₂.mpr
          ⟨fineCell, hfineRetained, hpointFine⟩
      exact hpoint.2 hpointRefined
    exact
      ⟨Set.mem_iUnion₂.mpr
          ⟨cell, hcellBad, hpointCoarse⟩,
        hpointBox⟩
  have hBadBoundary :
      badRegion ∩ Kakeya.Streamlined.axisBox 2 2 2 ⊆
        wz2PaperCropBoundaryRegion rho := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint.1 with
      ⟨cell, hcellBad, hpointCell⟩
    have hnotCrop :
        ¬ (wz1PaperGridCube rho cell ⊆
          Kakeya.Streamlined.axisBox 2 2 2) := by
      have hnotRetained :=
        (Finset.mem_sdiff.mp hcellBad).2
      intro hcrop
      apply hnotRetained
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_sdiff.mp hcellBad).1, hcrop⟩
    exact
      bad_coarse_cell_intersection_subset_boundary
        hrho hrhoOne hnotCrop ⟨hpointCell, hpoint.2⟩
  have hDeletedVolume :
      volume (balanced.refined.union \ refined.union) ≤
        ENNReal.ofReal (48 * rho) := by
    calc
      volume (balanced.refined.union \ refined.union) ≤
          volume (wz2PaperCropBoundaryRegion rho) :=
        measure_mono (hBadSubset.trans hBadBoundary)
      _ ≤ ENNReal.ofReal (48 * rho) :=
        wz2_paper_crop_boundary_region_volume hrho
  have hDeletedMassActual :
      balanced.refined.mass ≤
        refined.mass +
          ∑ index : Fin (wz1PaperBodyFamily fine).card,
            volume
              (balanced.refined.carrier index ∩
                (balanced.refined.union \ refined.union)) := by
    have hRefinedSub :
        ∀ index, refined.carrier index ⊆
          balanced.refined.carrier index :=
      wz2RefinedShading_subshading
    have hCarrierSplit :
        ∀ index,
          volume (balanced.refined.carrier index) =
            volume (refined.carrier index) +
              volume
                (balanced.refined.carrier index ∩
                  (balanced.refined.union \ refined.union)) := by
      intro index
      have hCarrierEq :
          balanced.refined.carrier index =
            refined.carrier index ∪
              (balanced.refined.carrier index ∩
                (balanced.refined.union \ refined.union)) := by
        ext point
        constructor
        · intro hpoint
          by_cases hrefined : point ∈ refined.union
          · have hretained :
                point ∈
                  wz2RetainedCellsUnion delta retainedFineCells := by
              rw [hRefinedUnion] at hrefined
              exact hrefined
            exact Or.inl ⟨hpoint, hretained⟩
          · exact Or.inr
              ⟨hpoint, ⟨⟨index, hpoint⟩, hrefined⟩⟩
        · rintro (hpoint | hpoint)
          · exact hRefinedSub index hpoint
          · exact hpoint.1
      have hDisjoint :
          Disjoint
            (refined.carrier index)
            (balanced.refined.carrier index ∩
              (balanced.refined.union \ refined.union)) := by
        rw [Set.disjoint_left]
        intro point hrefined hdeleted
        exact hdeleted.2.2 ⟨index, hrefined⟩
      calc
        volume (balanced.refined.carrier index) =
            volume
              (refined.carrier index ∪
                (balanced.refined.carrier index ∩
                  (balanced.refined.union \ refined.union))) :=
          congrArg volume hCarrierEq
        _ =
            volume (refined.carrier index) +
              volume
                (balanced.refined.carrier index ∩
                  (balanced.refined.union \ refined.union)) :=
          MeasureTheory.measure_union (μ := volume) hDisjoint
            ((balanced.refined.measurable_carrier index).inter
              ((measurableSet_shading_union balanced.refined).diff
                (measurableSet_shading_union refined)))
    dsimp only [Kakeya.Streamlined.Shading.mass]
    have hSum :=
      Finset.sum_le_sum
        (fun index (_ : index ∈
            (Finset.univ :
              Finset (Fin (wz1PaperBodyFamily fine).card))) =>
          (hCarrierSplit index).le)
    simpa [Kakeya.Streamlined.Shading.mass,
      Finset.sum_add_distrib] using hSum
  have hDeletedMassBoundary :
      balanced.refined.mass ≤
        refined.mass +
          ∑ index : Fin fine.card,
            volume
              (balanced.refined.carrier index ∩
                wz2PaperCropBoundaryRegion rho) := by
    calc
      balanced.refined.mass ≤
          refined.mass +
            ∑ index : Fin fine.card,
              volume
                (balanced.refined.carrier index ∩
                  (balanced.refined.union \ refined.union)) :=
        hDeletedMassActual
      _ ≤
          refined.mass +
            ∑ index : Fin fine.card,
              volume
                (balanced.refined.carrier index ∩
                  wz2PaperCropBoundaryRegion rho) := by
        gcongr
        exact hBadSubset.trans hBadBoundary
  have hDeletedMass :
      balanced.refined.mass ≤
        refined.mass +
          multiplicityCap * ENNReal.ofReal (48 * rho) := by
    have hSplit :
        ∑ index : Fin fine.card,
              volume
                (balanced.refined.carrier index ∩
                  (balanced.refined.union \ refined.union)) ≤
            multiplicityCap *
              volume (balanced.refined.union \ refined.union) := by
      have hSourcePointwise :
          ∀ point ∈ balanced.refined.union \ refined.union,
            (balanced.refined.pointMultiplicity point : ENNReal) ≤
              multiplicityCap :=
        fun point _ => hMultiplicity point
      have hDeletedMassUpper :=
        setLIntegral_mono' (μ := volume)
          ((measurableSet_shading_union balanced.refined).diff
            (measurableSet_shading_union refined))
          hSourcePointwise
      rw [setLIntegral_const] at hDeletedMassUpper
      calc
        (∑ index : Fin fine.card,
            volume
              (balanced.refined.carrier index ∩
                (balanced.refined.union \ refined.union))) =
            ∫⁻ point in balanced.refined.union \ refined.union,
              (balanced.refined.pointMultiplicity point : ENNReal) := by
          exact
            sum_volume_inter_eq_setLIntegral_pointMultiplicity
              balanced.refined
              ((measurableSet_shading_union balanced.refined).diff
                (measurableSet_shading_union refined))
        _ ≤ multiplicityCap *
              volume (balanced.refined.union \ refined.union) :=
          hDeletedMassUpper
    calc
      balanced.refined.mass ≤
          refined.mass +
            ∑ index : Fin fine.card,
              volume
                (balanced.refined.carrier index ∩
                  (balanced.refined.union \ refined.union)) :=
        hDeletedMassActual
      _ ≤
          refined.mass +
            multiplicityCap *
              volume (balanced.refined.union \ refined.union) := by
        gcongr
      _ ≤
          refined.mass +
            multiplicityCap * ENNReal.ofReal (48 * rho) := by
        gcongr
  have hRetainedNonempty : retainedCoarseCells.Nonempty := by
    by_contra hempty
    have hRetainedEmpty : retainedCoarseCells = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hFineEmpty : retainedFineCells = ∅ := by
      simp [retainedFineCells, hRetainedEmpty]
    have hRefinedMass : refined.mass = 0 := by
      have hUnionEmpty :
          wz2RetainedCellsUnion delta retainedFineCells = ∅ := by
        simp [wz2RetainedCellsUnion, hFineEmpty]
      change
        (∑ index : Fin fine.card,
          volume
            (balanced.refined.carrier index ∩
              wz2RetainedCellsUnion delta retainedFineCells)) = 0
      rw [hUnionEmpty]
      simp
    rw [hRefinedMass, zero_add] at hDeletedMassBoundary
    exact (not_le_of_gt hBoundarySmall) hDeletedMassBoundary
  let croppedBalancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) refined retainedCoarseCells selectedFineCells :=
    { level := balanced.level
      retainedCoarseCells := retainedCoarseCells
      retainedCoarseCells_subset := fun _ h => h
      retainedCoarseCells_nonempty := hRetainedNonempty
      selectedFineCells := selectedFineCells
      selectedFineCells_subset := by
        intro cell hcell
        exact fun _ h => h
      selectedFineCells_card := by
        intro cell hcell
        exact balanced.selectedFineCells_card cell
          (Finset.mem_filter.mp hcell).1
      availableFineCells_band := by
        intro cell hcell
        have hcard :=
          balanced.selectedFineCells_card cell
            (Finset.mem_filter.mp hcell).1
        rw [hcard]
        constructor
        · exact le_rfl
        · calc
            2 ^ balanced.level <
                2 * 2 ^ balanced.level := by
              have hpos : 0 < 2 ^ balanced.level :=
                Nat.pow_pos (by norm_num)
              omega
            _ = 2 ^ (balanced.level + 1) := by
              rw [pow_succ]
              ring
      retainedFineCells := retainedFineCells
      retainedFineCells_eq := rfl
      retainedFineCells_count := by
        have hEq :
            (∑ cell ∈ retainedCoarseCells,
                (selectedFineCells cell).card) =
              retainedFineCells.card := by
          change
            (∑ cell ∈ retainedCoarseCells,
                (selectedFineCells cell).card) =
              (retainedCoarseCells.biUnion selectedFineCells).card
          symm
          apply Finset.card_biUnion
          intro first hfirst second hsecond hne
          change
            Disjoint
              (selectedFineCells first)
              (selectedFineCells second)
          rw [Finset.disjoint_left]
          intro fineCell hfirstMem hsecondMem
          have hcontainFirst :=
            balanced.fine_cell_containment first
              (Finset.mem_filter.mp hfirst).1 fineCell hfirstMem
          have hcontainSecond :=
            balanced.fine_cell_containment second
              (Finset.mem_filter.mp hsecond).1 fineCell hsecondMem
          let point : Point3 := cellCorner delta fineCell
          have hp : point ∈ wz1PaperGridCube delta fineCell :=
            cellCorner_mem_gridCube hdelta fineCell
          exact
            Set.disjoint_left.mp
              (wz1PaperGridCube_disjoint hne)
              (hcontainFirst hp) (hcontainSecond hp)
        rw [hEq]
        exact Nat.le_mul_of_pos_left _ (by omega)
      refined := refined
      refined_carrier_eq := by
        intro index
        change refined.carrier index =
          refined.carrier index ∩
            wz2RetainedCellsUnion delta retainedFineCells
        apply Set.Subset.antisymm
        · intro point hpoint
          exact ⟨hpoint, hpoint.2⟩
        · exact Set.inter_subset_left
      refined_subshading := by intro; exact Set.Subset.rfl
      refined_cubical :=
        wz2RefinedShading_cubical balanced.refined_cubical
      refined_union_eq := by
        change refined.union =
          ⋃ fineCell ∈ retainedFineCells,
            wz1PaperGridCube delta fineCell
        exact hRefinedUnion
      cellMass := balanced.cellMass
      cellMass_eq := balanced.cellMass_eq
      cellMass_pos := balanced.cellMass_pos
      cellMass_ne_top := balanced.cellMass_ne_top
      fine_cell_mass := by
        intro cell hcell
        change
          volume (refined.union ∩ wz1PaperGridCube rho cell) =
            balanced.cellMass
        rw [hRefinedUnion]
        change
          volume
              (wz2RetainedCellsUnion delta retainedFineCells ∩
                wz1PaperGridCube rho cell) =
            balanced.cellMass
        rw [wz2RefinedUnion_inter_coarseCube
          (by rfl)
          (fun coarseCell hcoarse fineCell hfine =>
            balanced.fine_cell_containment coarseCell
              (Finset.mem_filter.mp hcoarse).1 fineCell hfine)
          hcell]
        rw [wz1PaperGridCube_volume_biUnion hdelta]
        rw [balanced.selectedFineCells_card cell
          (Finset.mem_filter.mp hcell).1,
          balanced.cellMass_eq]
      fine_cell_containment := by
        intro cell hcell fineCell hfine
        exact balanced.fine_cell_containment cell
          (Finset.mem_filter.mp hcell).1 fineCell hfine }
  exact
    ⟨{
      retainedCoarseCells := retainedCoarseCells
      retainedCoarseCells_eq := rfl
      retainedCoarseCells_nonempty := hRetainedNonempty
      selectedFineCells := selectedFineCells
      selectedFineCells_eq := fun _ => rfl
      retainedFineCells := retainedFineCells
      retainedFineCells_eq := rfl
      refined := refined
      refined_eq := rfl
      refined_subshading := wz2RefinedShading_subshading
      refined_cubical :=
        wz2RefinedShading_cubical balanced.refined_cubical
      refined_union_eq := hRefinedUnion
      croppedBalancing := croppedBalancing
      croppedBalancing_refined_eq := rfl
      crop := by
        intro cell hcell
        exact (Finset.mem_filter.mp hcell).2
      source_mass_le_boundary := hDeletedMassBoundary
      source_mass_le := hDeletedMass
    }⟩

theorem wz2_paper_crop_boundary_mass_le_of_multiplicity_cap
    {delta rho : ℝ}
    (hrho : 0 < rho)
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine)
    (multiplicityCap : ENNReal)
    (hMultiplicity :
      ∀ point,
        (shading.pointMultiplicity point : ENNReal) ≤
          multiplicityCap) :
    (∑ index : Fin fine.card,
        volume
          (shading.carrier index ∩
            wz2PaperCropBoundaryRegion rho)) ≤
      multiplicityCap * ENNReal.ofReal (48 * rho) := by
  have hMeasurable :
      MeasurableSet (wz2PaperCropBoundaryRegion rho) := by
    simp only [wz2PaperCropBoundaryRegion, Set.setOf_and]
    apply (Kakeya.Streamlined.measurableSet_axisBox 2 2 2).inter
    have hExists :
        {point : Point3 |
            ∃ coordinate : Fin 3,
              1 - rho < |point coordinate|} =
          ⋃ coordinate : Fin 3,
            {point : Point3 |
              1 - rho < |point coordinate|} := by
      ext point
      simp
    rw [hExists]
    apply MeasurableSet.iUnion
    intro coordinate
    change
      MeasurableSet
        ((fun point : Point3 => |point coordinate|) ⁻¹'
          Set.Ioi (1 - rho))
    have hContinuous :
        Continuous (fun point : Point3 => |point coordinate|) := by
      exact continuous_abs.comp
        (PiLp.continuous_apply
          (p := 2) (β := fun _ : Fin 3 => ℝ) coordinate)
    exact measurableSet_Ioi.preimage hContinuous.measurable
  calc
    (∑ index : Fin fine.card,
        volume
          (shading.carrier index ∩
            wz2PaperCropBoundaryRegion rho)) =
        ∫⁻ point in wz2PaperCropBoundaryRegion rho,
          (shading.pointMultiplicity point : ENNReal) := by
      exact
        sum_volume_inter_eq_setLIntegral_pointMultiplicity
          shading hMeasurable
    _ ≤
        multiplicityCap *
          volume (wz2PaperCropBoundaryRegion rho) := by
      have hIntegral :=
        setLIntegral_mono' (μ := volume) hMeasurable
          (fun point _ => hMultiplicity point)
      rw [setLIntegral_const] at hIntegral
      exact hIntegral
    _ ≤
        multiplicityCap * ENNReal.ofReal (48 * rho) := by
      gcongr
      exact wz2_paper_crop_boundary_region_volume hrho

theorem wz2_paper_crop_cell_pruning :
    WZ2PaperCropCellPruningStatement := by
  intro delta rho hdelta hrho hrhoOne fine shading coarseCells
    availableFineCells balanced multiplicityCap hMultiplicity hSmall
  apply
    wz2_paper_crop_cell_pruning_from_boundary_mass
      hdelta hrho hrhoOne shading coarseCells availableFineCells
      balanced multiplicityCap hMultiplicity
  exact
    (wz2_paper_crop_boundary_mass_le_of_multiplicity_cap
      hrho balanced.refined multiplicityCap hMultiplicity).trans_lt
      hSmall

end Kakeya.Assouad

end
