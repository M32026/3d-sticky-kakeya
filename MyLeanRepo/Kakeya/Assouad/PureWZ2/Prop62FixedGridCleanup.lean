import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FixedGridBoundaryMass
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PaperShadingMassFinite

/-!
# Proposition 6.2 fixed-grid cleanup

This is the whole-cell deletion conclusion of
`WZ2_prop62.tex`, Lemma `prop62-fixed-grid`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

def pureWZ2Prop62CoarseParent
    (delta rho : ℝ) (cell : WZ2PaperCellIndex) :
    WZ2PaperCellIndex :=
  wz1PaperGridIndex rho (cellCorner delta cell)

def pureWZ2Prop62SafeFineCells
    {delta rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (hdelta : 0 < delta) :
    Finset WZ2PaperCellIndex :=
  (wz1PaperActiveCells shading hdelta).filter fun cell =>
    wz1PaperGridCube delta cell ⊆
        wz1PaperGridCube rho
          (pureWZ2Prop62CoarseParent delta rho cell) ∧
      wz1PaperGridCube rho
          (pureWZ2Prop62CoarseParent delta rho cell) ⊆
        Kakeya.Streamlined.axisBox 2 2 2

theorem pureWZ2_prop62_bad_coarse_cell_subset_boundary
    {rho : ℝ}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
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
      have hpointLower : -1 ≤ point 0 :=
        (abs_le.mp hpointBounds.1).1
      by_cases hp : 0 ≤ point 0
      · rw [abs_of_nonneg hp]
        linarith
      · rw [abs_of_neg (lt_of_not_ge hp)]
        linarith
    · have hupperPoint := (hpointCube 0).2
      have hlowerOutside := (houtsideCoordinates 0).1
      have houtsideNeg : outside 0 < 0 := lt_of_not_ge houtsideNonneg
      rw [abs_of_neg houtsideNeg] at hzero'
      have hpointUpper : point 0 ≤ 1 :=
        (abs_le.mp hpointBounds.1).2
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
      have hpointLower : -1 ≤ point 1 :=
        (abs_le.mp hpointBounds.2.1).1
      by_cases hp : 0 ≤ point 1
      · rw [abs_of_nonneg hp]
        linarith
      · rw [abs_of_neg (lt_of_not_ge hp)]
        linarith
    · have hupperPoint := (hpointCube 1).2
      have hlowerOutside := (houtsideCoordinates 1).1
      have houtsideNeg : outside 1 < 0 := lt_of_not_ge houtsideNonneg
      rw [abs_of_neg houtsideNeg] at hone'
      have hpointUpper : point 1 ≤ 1 :=
        (abs_le.mp hpointBounds.2.1).2
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
      have hpointLower : -1 ≤ point 2 :=
        (abs_le.mp hpointBounds.2.2).1
      by_cases hp : 0 ≤ point 2
      · rw [abs_of_nonneg hp]
        linarith
      · rw [abs_of_neg (lt_of_not_ge hp)]
        linarith
    · have hupperPoint := (hpointCube 2).2
      have hlowerOutside := (houtsideCoordinates 2).1
      have houtsideNeg : outside 2 < 0 := lt_of_not_ge houtsideNonneg
      rw [abs_of_neg houtsideNeg] at htwo'
      have hpointUpper : point 2 ≤ 1 :=
        (abs_le.mp hpointBounds.2.2).2
      by_cases hp : 0 ≤ point 2
      · rw [abs_of_nonneg hp]
        linarith
      · rw [abs_of_neg (lt_of_not_ge hp)]
        linarith

structure PureWZ2Prop62FixedGridCleanupData
    {delta rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (hdelta : 0 < delta) where
  retainedFineCells : Finset WZ2PaperCellIndex
  retainedFineCells_eq :
    retainedFineCells =
      pureWZ2Prop62SafeFineCells (rho := rho) shading hdelta
  refined : WZ1PaperTubeShading family
  refined_eq :
    refined = wz2RefinedShading shading retainedFineCells
  subshading :
    ∀ index, refined.carrier index ⊆ shading.carrier index
  cubical : WZ1PaperIsCubicalShading refined
  mass_retention :
    shading.mass / 2 ≤ refined.mass
  parent :
    WZ2PaperCellIndex → WZ2PaperCellIndex
  parent_eq :
    parent = pureWZ2Prop62CoarseParent delta rho
  parent_containment :
    ∀ cell ∈ retainedFineCells,
      wz1PaperGridCube delta cell ⊆
        wz1PaperGridCube rho (parent cell)
  parent_crop :
    ∀ cell ∈ retainedFineCells,
      wz1PaperGridCube rho (parent cell) ⊆
        Kakeya.Streamlined.axisBox 2 2 2
  parent_unique :
    ∀ cell ∈ retainedFineCells,
      ∀ candidate,
        wz1PaperGridCube delta cell ⊆
            wz1PaperGridCube rho candidate →
          candidate = parent cell

theorem pureWZ2_prop62_fixed_grid_cleanup
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    (hcubical : WZ1PaperIsCubicalShading shading)
    {C : ENNReal}
    (hcwa : WZ2PaperConvexWolffBound family C)
    (hsmall :
      (15 : ENNReal) *
            C *
            (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
            pureWZ2Prop62FixedGridPlaneConstant *
            ENNReal.ofReal (delta / rho) *
            (wz1PaperBodyFamily family).mass +
          6 *
            C *
            (pureWZ2Prop62OuterDirectionLevelCount rho : ENNReal) *
            pureWZ2Prop62OuterFaceConstant *
            ENNReal.ofReal rho *
            (wz1PaperBodyFamily family).mass ≤
        shading.mass / 2) :
    Nonempty
      (PureWZ2Prop62FixedGridCleanupData
        (rho := rho) shading hdelta) := by
  let activeCells := wz1PaperActiveCells shading hdelta
  let retainedFineCells :=
    pureWZ2Prop62SafeFineCells (rho := rho) shading hdelta
  let deletedFineCells := activeCells \ retainedFineCells
  let retainedUnion :=
    wz2RetainedCellsUnion delta retainedFineCells
  let deletedRegion : Set Point3 :=
    ⋃ cell ∈ deletedFineCells, wz1PaperGridCube delta cell
  let refined := wz2RefinedShading shading retainedFineCells
  have hactiveUnion :
      shading.union =
        ⋃ cell ∈ activeCells, wz1PaperGridCube delta cell :=
    hcubical.union_eq_activeCells hdelta
  have hpartition :
      activeCells = retainedFineCells ∪ deletedFineCells := by
    rw [Finset.union_sdiff_of_subset]
    exact Finset.filter_subset _ _
  have hretainedDeleted :
      retainedUnion ∪ deletedRegion =
        ⋃ cell ∈ activeCells, wz1PaperGridCube delta cell := by
    rw [hpartition]
    ext point
    simp [retainedUnion, deletedRegion, wz2RetainedCellsUnion]
  have hdeletedSubset :
      deletedRegion ⊆
        wz2PaperGridBoundaryRegion delta rho ∪
          wz2PaperCropBoundaryRegion rho := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨cell, hcellDeleted, hpointCell⟩
    have hcellActive : cell ∈ activeCells :=
      (Finset.mem_sdiff.mp hcellDeleted).1
    have hcellNotRetained :=
      (Finset.mem_sdiff.mp hcellDeleted).2
    have hnotSafe :
        ¬ (wz1PaperGridCube delta cell ⊆
              wz1PaperGridCube rho
                (pureWZ2Prop62CoarseParent delta rho cell) ∧
            wz1PaperGridCube rho
                (pureWZ2Prop62CoarseParent delta rho cell) ⊆
              Kakeya.Streamlined.axisBox 2 2 2) := by
      intro hsafe
      apply hcellNotRetained
      change
        cell ∈
          pureWZ2Prop62SafeFineCells (rho := rho) shading hdelta
      exact Finset.mem_filter.mpr ⟨hcellActive, hsafe⟩
    by_cases hparentContainment :
        wz1PaperGridCube delta cell ⊆
          wz1PaperGridCube rho
            (pureWZ2Prop62CoarseParent delta rho cell)
    · apply Or.inr
      have hbadParent :
          ¬ (wz1PaperGridCube rho
              (pureWZ2Prop62CoarseParent delta rho cell) ⊆
            Kakeya.Streamlined.axisBox 2 2 2) := by
        intro hcrop
        exact hnotSafe ⟨hparentContainment, hcrop⟩
      have hpointParent := hparentContainment hpointCell
      have hpointBox :
          point ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
        wz1PaperActiveCell_subset_axisBox
          hcubical hdelta hcellActive hpointCell
      exact
        pureWZ2_prop62_bad_coarse_cell_subset_boundary
          hrho hrhoOne hbadParent ⟨hpointParent, hpointBox⟩
    · apply Or.inl
      have hcrossingData :=
        crossing_cell_slab hcubical hdelta hrho
          hcellActive hparentContainment
      rcases hcrossingData with
        ⟨coordinate, boundary, hcellSlab, hboundary⟩
      have hboundaryMem :
          boundary ∈ wz2PaperBoundaryIndicesInWindow rho := by
        simp only [wz2PaperBoundaryIndicesInWindow, Finset.mem_Icc]
        have habs : |(boundary : ℝ)| ≤ 1 / rho := by
          have hmul :
              |(boundary : ℝ)| * rho ≤ 1 := by
            simpa [abs_mul, abs_of_pos hrho] using hboundary
          calc
            |(boundary : ℝ)| =
                (|(boundary : ℝ)| * rho) / rho := by
              field_simp [hrho.ne']
            _ ≤ 1 / rho := by gcongr
        have habs' := abs_le.mp habs
        constructor
        · have hceil :
              1 / rho ≤ (⌈1 / rho⌉ : ℝ) :=
            Int.le_ceil _
          exact_mod_cast
            (by linarith : -(⌈1 / rho⌉ : ℝ) ≤ boundary)
        · have hceil :
              1 / rho ≤ (⌈1 / rho⌉ : ℝ) :=
            Int.le_ceil _
          exact_mod_cast
            (by linarith : (boundary : ℝ) ≤ ⌈1 / rho⌉)
      exact Set.mem_iUnion.mpr
        ⟨coordinate,
          Set.mem_iUnion₂.mpr
            ⟨boundary, hboundaryMem, by
              have hslabPoint := hcellSlab hpointCell
              have habs :
                  |point coordinate - (boundary : ℝ) * rho| <
                    delta :=
                hslabPoint.1
              change
                (boundary : ℝ) * rho - delta ≤ point coordinate ∧
                  point coordinate ≤
                    (boundary : ℝ) * rho + delta
              rw [abs_lt] at habs
              constructor <;> linarith⟩⟩
  have hcarrierCover :
      ∀ index,
        shading.carrier index ⊆ retainedUnion ∪ deletedRegion := by
    intro index point hpoint
    have hpointUnion : point ∈ shading.union := ⟨index, hpoint⟩
    rw [hactiveUnion, ← hretainedDeleted] at hpointUnion
    exact hpointUnion
  have hdisjoint : Disjoint retainedUnion deletedRegion := by
    rw [Set.disjoint_left]
    intro point hretained hdeleted
    rcases Set.mem_iUnion₂.mp hretained with
      ⟨first, hfirst, hpointFirst⟩
    rcases Set.mem_iUnion₂.mp hdeleted with
      ⟨second, hsecond, hpointSecond⟩
    have hne : first ≠ second := by
      intro heq
      apply (Finset.mem_sdiff.mp hsecond).2
      rwa [← heq]
    exact Set.disjoint_left.mp
      (wz1PaperGridCube_disjoint hne) hpointFirst hpointSecond
  have hmassSplit :
      shading.mass =
        refined.mass +
          ∑ index : Fin family.card,
            volume (shading.carrier index ∩ deletedRegion) := by
    have hcarrierSplit :
        ∀ index : Fin family.card,
          volume (shading.carrier index) =
            volume (refined.carrier index) +
              volume (shading.carrier index ∩ deletedRegion) := by
      intro index
      have heq :
          shading.carrier index =
            refined.carrier index ∪
              (shading.carrier index ∩ deletedRegion) := by
        ext point
        constructor
        · intro hpoint
          rcases hcarrierCover index hpoint with hretained | hdeleted
          · exact Or.inl ⟨hpoint, hretained⟩
          · exact Or.inr ⟨hpoint, hdeleted⟩
        · rintro (hpoint | hpoint)
          · exact hpoint.1
          · exact hpoint.1
      have hsetsDisjoint :
          Disjoint
            (refined.carrier index)
            (shading.carrier index ∩ deletedRegion) := by
        rw [Set.disjoint_left]
        intro point hrefined hdeleted
        exact Set.disjoint_left.mp hdisjoint hrefined.2 hdeleted.2
      calc
        volume (shading.carrier index) =
            volume
              (refined.carrier index ∪
                (shading.carrier index ∩ deletedRegion)) :=
          congrArg volume heq
        _ =
            volume (refined.carrier index) +
              volume (shading.carrier index ∩ deletedRegion) :=
          MeasureTheory.measure_union (μ := volume) hsetsDisjoint
            ((shading.measurable_carrier index).inter <|
              MeasurableSet.iUnion fun cell =>
                MeasurableSet.iUnion fun _ =>
                  wz1PaperGridCube_measurable cell)
    change
      (∑ index : Fin family.card, volume (shading.carrier index)) =
        (∑ index : Fin family.card, volume (refined.carrier index)) +
          ∑ index : Fin family.card,
            volume (shading.carrier index ∩ deletedRegion)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun index _ => hcarrierSplit index
  have hdeletedMass :
      (∑ index : Fin family.card,
          volume (shading.carrier index ∩ deletedRegion)) ≤
        (15 : ENNReal) *
              C *
              (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
              pureWZ2Prop62FixedGridPlaneConstant *
              ENNReal.ofReal (delta / rho) *
              (wz1PaperBodyFamily family).mass +
            6 *
              C *
              (pureWZ2Prop62OuterDirectionLevelCount rho : ENNReal) *
              pureWZ2Prop62OuterFaceConstant *
              ENNReal.ofReal rho *
              (wz1PaperBodyFamily family).mass := by
    calc
      (∑ index : Fin family.card,
          volume (shading.carrier index ∩ deletedRegion)) ≤
        ∑ index : Fin family.card,
          volume
            (shading.carrier index ∩
              (wz2PaperGridBoundaryRegion delta rho ∪
                wz2PaperCropBoundaryRegion rho)) := by
          exact Finset.sum_le_sum fun index _ =>
            measure_mono
              (Set.inter_subset_inter_right _ hdeletedSubset)
      _ ≤
        ∑ index : Fin family.card,
          (volume
              (shading.carrier index ∩
                wz2PaperGridBoundaryRegion delta rho) +
            volume
              (shading.carrier index ∩
                wz2PaperCropBoundaryRegion rho)) := by
        exact Finset.sum_le_sum fun index _ => by
          have hset :
              shading.carrier index ∩
                  (wz2PaperGridBoundaryRegion delta rho ∪
                    wz2PaperCropBoundaryRegion rho) =
                (shading.carrier index ∩
                  wz2PaperGridBoundaryRegion delta rho) ∪
                (shading.carrier index ∩
                  wz2PaperCropBoundaryRegion rho) := by
            ext point
            simp only [Set.mem_inter_iff, Set.mem_union]
            tauto
          rw [hset]
          exact measure_union_le _ _
      _ =
        (∑ index : Fin family.card,
            volume
              (shading.carrier index ∩
                wz2PaperGridBoundaryRegion delta rho)) +
          ∑ index : Fin family.card,
            volume
              (shading.carrier index ∩
                wz2PaperCropBoundaryRegion rho) := by
        rw [Finset.sum_add_distrib]
      _ ≤
        (15 : ENNReal) *
              C *
              (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
              pureWZ2Prop62FixedGridPlaneConstant *
              ENNReal.ofReal (delta / rho) *
              (wz1PaperBodyFamily family).mass +
            6 *
              C *
              (pureWZ2Prop62OuterDirectionLevelCount rho : ENNReal) *
              pureWZ2Prop62OuterFaceConstant *
              ENNReal.ofReal rho *
              (wz1PaperBodyFamily family).mass :=
        add_le_add
          (pureWZ2_prop62_grid_boundary_mass
            hdelta hdeltaSmall hrho hrhoOne hline shading hcwa)
          (pureWZ2_prop62_outer_boundary_mass
            hdelta hdeltaSmall hrho hrhoOne hdeltaRho
            hline shading hcwa)
  have hsourceUpper :
      shading.mass ≤ refined.mass + shading.mass / 2 := by
    calc
      shading.mass =
          refined.mass +
            ∑ index : Fin family.card,
              volume (shading.carrier index ∩ deletedRegion) :=
        hmassSplit
      _ ≤
          refined.mass +
            ((15 : ENNReal) *
                C *
                (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
                pureWZ2Prop62FixedGridPlaneConstant *
                ENNReal.ofReal (delta / rho) *
                (wz1PaperBodyFamily family).mass +
              6 *
                C *
                (pureWZ2Prop62OuterDirectionLevelCount rho : ENNReal) *
                pureWZ2Prop62OuterFaceConstant *
                ENNReal.ofReal rho *
                (wz1PaperBodyFamily family).mass) := by
        gcongr
      _ ≤ refined.mass + shading.mass / 2 := by
        gcongr
  have hmassRetention :
      shading.mass / 2 ≤ refined.mass := by
    have hmassTop := wz1PaperTubeShading_mass_ne_top shading
    have hhalfTop :
        shading.mass / 2 ≠ ⊤ :=
      ne_top_of_le_ne_top hmassTop ENNReal.half_le_self
    apply ENNReal.le_of_add_le_add_right hhalfTop
    simpa only [ENNReal.add_halves, add_comm] using hsourceUpper
  have hcubicalRefined :
      WZ1PaperIsCubicalShading refined :=
    wz2RefinedShading_cubical hcubical
  let parent :=
    pureWZ2Prop62CoarseParent delta rho
  exact
    ⟨{
      retainedFineCells := retainedFineCells
      retainedFineCells_eq := rfl
      refined := refined
      refined_eq := rfl
      subshading := wz2RefinedShading_subshading
      cubical := hcubicalRefined
      mass_retention := hmassRetention
      parent := parent
      parent_eq := rfl
      parent_containment := by
        intro cell hcell
        exact (Finset.mem_filter.mp hcell).2.1
      parent_crop := by
        intro cell hcell
        exact (Finset.mem_filter.mp hcell).2.2
      parent_unique := by
        intro cell hcell candidate hcandidate
        let point := cellCorner delta cell
        have hpoint :
            point ∈ wz1PaperGridCube delta cell :=
          cellCorner_mem_gridCube hdelta cell
        have hfirst :
            wz1PaperGridIndex rho point = candidate :=
          (mem_wz1PaperGridCube rho candidate point).mp
            (hcandidate hpoint)
        have hsecond :
            wz1PaperGridIndex rho point = parent cell := by
          rfl
        exact hfirst.symm.trans hsecond
    }⟩

end Kakeya.Assouad

end
