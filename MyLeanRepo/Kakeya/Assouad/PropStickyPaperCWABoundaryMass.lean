import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBoundarySlowTubes
import MyLeanRepo.Kakeya.Assouad.PropStickyBoundaryCellPruning

/-!
# CWA-aware mass bound for fixed-origin boundary-cell pruning

For each coordinate and each coarse-grid hyperplane, split the tubes meeting
the boundary into slow and fast coordinate directions.  Slow tubes lie in one
common convex strip and are counted by top-level CWA.  Fast tubes are summed
using the periodic paper-tube slab-volume bound.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

def wz2PaperBoundaryIndicesInWindow (rho : ℝ) : Finset ℤ :=
  Finset.Icc (-⌈1 / rho⌉) ⌈1 / rho⌉

def wz2PaperCoordinateGridBoundaryRegion
    (delta rho : ℝ) (coordinate : Fin 3) : Set Point3 :=
  ⋃ boundary ∈ wz2PaperBoundaryIndicesInWindow rho,
    coordinateSlab coordinate
      ((boundary : ℝ) * rho - delta)
      ((boundary : ℝ) * rho + delta)

def wz2PaperGridBoundaryRegion
    (delta rho : ℝ) : Set Point3 :=
  ⋃ coordinate : Fin 3,
    wz2PaperCoordinateGridBoundaryRegion delta rho coordinate

theorem wz2_paper_crossing_region_subset_grid_boundary
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (crossingFineCells : Finset WZ2PaperCellIndex)
    (hcrossing :
      ∀ cell ∈ crossingFineCells,
        cell ∈ wz1PaperActiveCells shading hdelta ∧
          ¬ (wz1PaperGridCube delta cell ⊆
            wz1PaperGridCube rho
              (wz1PaperGridIndex rho
                (cellCorner delta cell)))) :
    (⋃ cell ∈ crossingFineCells,
        wz1PaperGridCube delta cell) ⊆
      wz2PaperGridBoundaryRegion delta rho := by
  intro point hpoint
  rcases Set.mem_iUnion₂.mp hpoint with
    ⟨cell, hcell, hpointCell⟩
  rcases
      crossing_cell_slab hcubical hdelta hrho
        (hcrossing cell hcell).1
        (hcrossing cell hcell).2 with
    ⟨coordinate, boundary, hcellSlab, hboundary⟩
  have hbound :
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
      exact_mod_cast (by linarith : -(⌈1 / rho⌉ : ℝ) ≤ boundary)
    · have hceil :
          1 / rho ≤ (⌈1 / rho⌉ : ℝ) :=
        Int.le_ceil _
      exact_mod_cast (by linarith : (boundary : ℝ) ≤ ⌈1 / rho⌉)
  exact Set.mem_iUnion.mpr
    ⟨coordinate,
      Set.mem_iUnion₂.mpr
        ⟨boundary, hbound, by
          have hslabPoint := hcellSlab hpointCell
          have habs :
              |point coordinate - (boundary : ℝ) * rho| < delta := by
            exact hslabPoint.1
          change
            (boundary : ℝ) * rho - delta ≤ point coordinate ∧
              point coordinate ≤
                (boundary : ℝ) * rho + delta
          rw [abs_lt] at habs
          constructor <;> linarith⟩⟩

theorem wz2_paper_fast_coordinate_boundary_mass
    {delta rho speed : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hdeltaRho : 50 * delta ≤ rho)
    (hspeed : 0 < speed)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    (coordinate : Fin 3) :
    let fast :=
      (Finset.univ : Finset (Fin family.card)).filter fun index =>
        speed ≤
          |wz1PaperDirection (family.tube index) coordinate|
    (∑ index ∈ fast,
        volume
          (shading.carrier index ∩
            wz2PaperCoordinateGridBoundaryRegion
              delta rho coordinate)) ≤
      family.enncard *
        ENNReal.ofReal
          (4000000 * delta ^ 3 *
            ((1 / rho) + (1 / speed))) := by
  dsimp only
  let fast :=
    (Finset.univ : Finset (Fin family.card)).filter fun index =>
      speed ≤
        |wz1PaperDirection (family.tube index) coordinate|
  have hterm :
      ∀ index ∈ fast,
        volume
            (shading.carrier index ∩
              wz2PaperCoordinateGridBoundaryRegion
                delta rho coordinate) ≤
          ENNReal.ofReal
            (4000000 * delta ^ 3 *
              ((1 / rho) + (1 / speed))) := by
    intro index hindex
    have hfast :
        speed ≤
          |wz1PaperDirection (family.tube index) coordinate| :=
      (Finset.mem_filter.mp hindex).2
    have hsubset :
        shading.carrier index ∩
            wz2PaperCoordinateGridBoundaryRegion
              delta rho coordinate ⊆
          wz1PaperTubeCarrier (family.tube index) ∩
            wz2PaperPeriodicBoundaryRegion delta rho coordinate
              (wz2PaperRelevantBoundaryIndices
                (rho := rho) (family.tube index) coordinate) := by
      intro point hpoint
      refine
        ⟨shading.subset_body index hpoint.1, ?_⟩
      rcases Set.mem_iUnion₂.mp hpoint.2 with
        ⟨boundary, hboundary, hpointSlab⟩
      have hboundaryRelevant :=
        wz2_paper_boundary_index_mem_relevant
          hdelta hrho (family.tube index) (hline index)
          coordinate boundary
          (shading.subset_body index hpoint.1)
          hpointSlab
      exact Set.mem_iUnion₂.mpr
        ⟨boundary, hboundaryRelevant, hpointSlab⟩
    have hvolume :=
      wz2_paper_tube_periodic_boundary_volume_of_speed
        hdelta hdeltaSmall hrho hdeltaRho
        (family.tube index) (hline index) coordinate
        hspeed hfast
    have hdirectionOne :
        |wz1PaperDirection (family.tube index) coordinate| ≤ 1 := by
      calc
        |wz1PaperDirection (family.tube index) coordinate|
            ≤ ‖wz1PaperDirection (family.tube index)‖ :=
          coord_abs_le_norm _ coordinate
        _ = 1 := wz1PaperDirection_norm _
    exact (measure_mono hsubset).trans <|
      hvolume.trans <| ENNReal.ofReal_mono <| by
        gcongr
  calc
    (∑ index ∈ fast,
        volume
          (shading.carrier index ∩
            wz2PaperCoordinateGridBoundaryRegion
              delta rho coordinate))
        ≤
      ∑ _index ∈ fast,
        ENNReal.ofReal
          (4000000 * delta ^ 3 *
            ((1 / rho) + (1 / speed))) := by
      exact Finset.sum_le_sum fun index hindex =>
        hterm index hindex
    _ =
      (fast.card : ENNReal) *
        ENNReal.ofReal
          (4000000 * delta ^ 3 *
            ((1 / rho) + (1 / speed))) := by
      simp [Finset.sum_const]
    _ ≤
      family.enncard *
        ENNReal.ofReal
          (4000000 * delta ^ 3 *
            ((1 / rho) + (1 / speed))) := by
      gcongr
      change (fast.card : ENNReal) ≤ (family.card : ENNReal)
      exact_mod_cast (by
        simpa [Fintype.card_fin] using
          Finset.card_le_univ fast)

theorem wz2_paper_slow_coordinate_boundary_mass
    {delta rho speed : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hspeed : 0 < speed)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    (coordinate : Fin 3)
    {C : ENNReal}
    (hcwa : WZ2PaperConvexWolffBound family C) :
    let slow :=
      (Finset.univ : Finset (Fin family.card)).filter fun index =>
        |wz1PaperDirection (family.tube index) coordinate| ≤ speed
    (∑ index ∈ slow,
        volume
          (shading.carrier index ∩
            wz2PaperCoordinateGridBoundaryRegion
              delta rho coordinate)) ≤
      (wz2PaperBoundaryIndicesInWindow rho).card *
        ((C *
            ENNReal.ofReal
              (16 * (4 * speed + 49 * delta)) *
            family.enncard) *
          (55296 * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2)) := by
  dsimp only
  let boundaries := wz2PaperBoundaryIndicesInWindow rho
  let slow :=
    (Finset.univ : Finset (Fin family.card)).filter fun index =>
      |wz1PaperDirection (family.tube index) coordinate| ≤ speed
  have hpointwise :
      ∀ index ∈ slow,
        volume
            (shading.carrier index ∩
              wz2PaperCoordinateGridBoundaryRegion
                delta rho coordinate) ≤
          ∑ boundary ∈ boundaries,
            volume
              (shading.carrier index ∩
                coordinateSlab coordinate
                  ((boundary : ℝ) * rho - delta)
                  ((boundary : ℝ) * rho + delta)) := by
    intro index hindex
    have hsubset :
        shading.carrier index ∩
            wz2PaperCoordinateGridBoundaryRegion
              delta rho coordinate ⊆
          ⋃ boundary ∈ boundaries,
            (shading.carrier index ∩
              coordinateSlab coordinate
                ((boundary : ℝ) * rho - delta)
                ((boundary : ℝ) * rho + delta)) := by
      intro point hpoint
      rcases Set.mem_iUnion₂.mp hpoint.2 with
        ⟨boundary, hboundary, hpointSlab⟩
      exact Set.mem_iUnion₂.mpr
        ⟨boundary, hboundary, hpoint.1, hpointSlab⟩
    exact
      (measure_mono hsubset).trans
        (MeasureTheory.measure_biUnion_finset_le boundaries _)
  calc
    (∑ index ∈ slow,
        volume
          (shading.carrier index ∩
            wz2PaperCoordinateGridBoundaryRegion
              delta rho coordinate))
        ≤
      ∑ index ∈ slow,
        ∑ boundary ∈ boundaries,
          volume
            (shading.carrier index ∩
              coordinateSlab coordinate
                ((boundary : ℝ) * rho - delta)
                ((boundary : ℝ) * rho + delta)) := by
      exact Finset.sum_le_sum fun index hindex =>
        hpointwise index hindex
    _ =
      ∑ boundary ∈ boundaries,
        ∑ index ∈ slow,
          volume
            (shading.carrier index ∩
              coordinateSlab coordinate
                ((boundary : ℝ) * rho - delta)
                ((boundary : ℝ) * rho + delta)) := by
      exact Finset.sum_comm
    _ ≤
      ∑ _boundary ∈ boundaries,
        ((C *
            ENNReal.ofReal
              (16 * (4 * speed + 49 * delta)) *
            family.enncard) *
          (55296 * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2)) := by
      apply Finset.sum_le_sum
      intro boundary hboundary
      let meetingSlow :=
        wz2PaperSlowBoundaryTubeIndices
          family coordinate ((boundary : ℝ) * rho) speed
      have hsubsetSlow :
          (slow.filter fun index =>
            (wz1PaperTubeCarrier (family.tube index) ∩
              coordinateSlab coordinate
                ((boundary : ℝ) * rho - delta)
                ((boundary : ℝ) * rho + delta)).Nonempty) ⊆
            meetingSlow := by
        intro index hindex
        have hslow := (Finset.mem_filter.mp hindex).1
        have hmeet := (Finset.mem_filter.mp hindex).2
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,
            (Finset.mem_filter.mp hslow).2, hmeet⟩
      calc
        (∑ index ∈ slow,
            volume
              (shading.carrier index ∩
                coordinateSlab coordinate
                  ((boundary : ℝ) * rho - delta)
                  ((boundary : ℝ) * rho + delta)))
            ≤
          ∑ index ∈ meetingSlow,
            volume (shading.carrier index) := by
          let activeSlow :=
            slow.filter fun index =>
              (wz1PaperTubeCarrier (family.tube index) ∩
                coordinateSlab coordinate
                  ((boundary : ℝ) * rho - delta)
                  ((boundary : ℝ) * rho + delta)).Nonempty
          calc
            (∑ index ∈ slow,
                volume
                  (shading.carrier index ∩
                    coordinateSlab coordinate
                      ((boundary : ℝ) * rho - delta)
                      ((boundary : ℝ) * rho + delta)))
                =
              ∑ index ∈ activeSlow,
                volume
                  (shading.carrier index ∩
                    coordinateSlab coordinate
                      ((boundary : ℝ) * rho - delta)
                      ((boundary : ℝ) * rho + delta)) := by
                symm
                apply Finset.sum_subset
                · exact Finset.filter_subset _ _
                · intro index hindex hnot
                  have hnoMeet :
                      ¬ (wz1PaperTubeCarrier (family.tube index) ∩
                        coordinateSlab coordinate
                          ((boundary : ℝ) * rho - delta)
                          ((boundary : ℝ) * rho + delta)).Nonempty := by
                    intro hmeet
                    exact hnot
                      (Finset.mem_filter.mpr ⟨hindex, hmeet⟩)
                  have hempty :
                      shading.carrier index ∩
                        coordinateSlab coordinate
                          ((boundary : ℝ) * rho - delta)
                          ((boundary : ℝ) * rho + delta) = ∅ := by
                    apply Set.not_nonempty_iff_eq_empty.mp
                    intro hnonempty
                    rcases hnonempty with
                      ⟨point, hpointShade, hpointSlab⟩
                    exact hnoMeet
                      ⟨point, shading.subset_body index hpointShade,
                        hpointSlab⟩
                  rw [hempty]
                  simp
            _ ≤
              ∑ index ∈ activeSlow,
                volume (shading.carrier index) := by
                  exact Finset.sum_le_sum fun index _ =>
                    measure_mono Set.inter_subset_left
            _ ≤
              ∑ index ∈ meetingSlow,
                volume (shading.carrier index) := by
                  apply Finset.sum_le_sum_of_subset_of_nonneg
                  · exact hsubsetSlow
                  · intro index _ _
                    exact bot_le
        _ ≤
          ((C *
              ENNReal.ofReal
                (16 * (4 * speed + 49 * delta)) *
              family.enncard) *
            (55296 * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN delta 2)) :=
          wz2_paper_slow_boundary_shading_mass
            hdelta hdeltaSmall hspeed hline shading coordinate hcwa
    _ =
      (wz2PaperBoundaryIndicesInWindow rho).card *
        ((C *
            ENNReal.ofReal
              (16 * (4 * speed + 49 * delta)) *
            family.enncard) *
          (55296 * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2)) := by
      simp [boundaries, Finset.sum_const]

theorem wz2_paper_coordinate_boundary_mass
    {delta rho speed : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hdeltaRho : 50 * delta ≤ rho)
    (hspeed : 0 < speed)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    (coordinate : Fin 3)
    {C : ENNReal}
    (hcwa : WZ2PaperConvexWolffBound family C) :
    (∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            wz2PaperCoordinateGridBoundaryRegion
              delta rho coordinate)) ≤
      (wz2PaperBoundaryIndicesInWindow rho).card *
          ((C *
              ENNReal.ofReal
                (16 * (4 * speed + 49 * delta)) *
              family.enncard) *
            (55296 * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN delta 2)) +
        family.enncard *
          ENNReal.ofReal
            (4000000 * delta ^ 3 *
              ((1 / rho) + (1 / speed))) := by
  let weight : Fin family.card → ENNReal := fun index =>
    volume
      (shading.carrier index ∩
        wz2PaperCoordinateGridBoundaryRegion
          delta rho coordinate)
  let slow :=
    (Finset.univ : Finset (Fin family.card)).filter fun index =>
      |wz1PaperDirection (family.tube index) coordinate| ≤ speed
  let notSlow :=
    (Finset.univ : Finset (Fin family.card)).filter fun index =>
      ¬ |wz1PaperDirection (family.tube index) coordinate| ≤ speed
  let fast :=
    (Finset.univ : Finset (Fin family.card)).filter fun index =>
      speed ≤ |wz1PaperDirection (family.tube index) coordinate|
  have hpartition :
      (∑ index : Fin family.card, weight index) =
        (∑ index ∈ slow, weight index) +
          ∑ index ∈ notSlow, weight index := by
    simpa [slow, notSlow] using
      (Finset.sum_filter_add_sum_filter_not
        (Finset.univ : Finset (Fin family.card))
        (fun index =>
          |wz1PaperDirection (family.tube index) coordinate| ≤ speed)
        weight).symm
  have hnotSlowSubset : notSlow ⊆ fast := by
    intro index hindex
    have hnot :=
      (Finset.mem_filter.mp hindex).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, le_of_not_ge hnot⟩
  have hnotSlowLe :
      (∑ index ∈ notSlow, weight index) ≤
        ∑ index ∈ fast, weight index := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact hnotSlowSubset
    · intro index _ _
      exact bot_le
  have hslow :=
    wz2_paper_slow_coordinate_boundary_mass
      hdelta hdeltaSmall hrho hspeed hline shading coordinate hcwa
  have hfast :=
    wz2_paper_fast_coordinate_boundary_mass
      hdelta hdeltaSmall hrho hdeltaRho hspeed
      hline shading coordinate
  change (∑ index : Fin family.card, weight index) ≤ _
  calc
    (∑ index : Fin family.card, weight index)
        =
      (∑ index ∈ slow, weight index) +
        ∑ index ∈ notSlow, weight index := hpartition
    _ ≤
      (∑ index ∈ slow, weight index) +
        ∑ index ∈ fast, weight index :=
      add_le_add_right hnotSlowLe _
    _ ≤
      (wz2PaperBoundaryIndicesInWindow rho).card *
          ((C *
              ENNReal.ofReal
                (16 * (4 * speed + 49 * delta)) *
              family.enncard) *
            (55296 * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN delta 2)) +
        family.enncard *
          ENNReal.ofReal
            (4000000 * delta ^ 3 *
              ((1 / rho) + (1 / speed))) := by
      exact add_le_add hslow hfast

theorem wz2_paper_grid_boundary_mass
    {delta rho speed : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hdeltaRho : 50 * delta ≤ rho)
    (hspeed : 0 < speed)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    {C : ENNReal}
    (hcwa : WZ2PaperConvexWolffBound family C) :
    (∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            wz2PaperGridBoundaryRegion delta rho)) ≤
      ∑ _coordinate : Fin 3,
        ((wz2PaperBoundaryIndicesInWindow rho).card *
            ((C *
                ENNReal.ofReal
                  (16 * (4 * speed + 49 * delta)) *
                family.enncard) *
              (55296 * Kakeya.deltaTubeVolume 1 *
                Kakeya.realRpowENN delta 2)) +
          family.enncard *
            ENNReal.ofReal
              (4000000 * delta ^ 3 *
                ((1 / rho) + (1 / speed)))) := by
  have hpointwise :
      ∀ index : Fin family.card,
        volume
            (shading.carrier index ∩
              wz2PaperGridBoundaryRegion delta rho) ≤
          ∑ coordinate : Fin 3,
            volume
              (shading.carrier index ∩
                wz2PaperCoordinateGridBoundaryRegion
                  delta rho coordinate) := by
    intro index
    have hsubset :
        shading.carrier index ∩
            wz2PaperGridBoundaryRegion delta rho ⊆
          ⋃ coordinate : Fin 3,
            (shading.carrier index ∩
              wz2PaperCoordinateGridBoundaryRegion
                delta rho coordinate) := by
      intro point hpoint
      rcases Set.mem_iUnion.mp hpoint.2 with
        ⟨coordinate, hcoordinate⟩
      exact Set.mem_iUnion.mpr
        ⟨coordinate, hpoint.1, hcoordinate⟩
    exact
      (measure_mono hsubset).trans
        (MeasureTheory.measure_iUnion_fintype_le _ _)
  calc
    (∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            wz2PaperGridBoundaryRegion delta rho))
        ≤
      ∑ index : Fin family.card,
        ∑ coordinate : Fin 3,
          volume
            (shading.carrier index ∩
              wz2PaperCoordinateGridBoundaryRegion
                delta rho coordinate) := by
      exact Finset.sum_le_sum fun index _ =>
        hpointwise index
    _ =
      ∑ coordinate : Fin 3,
        ∑ index : Fin family.card,
          volume
            (shading.carrier index ∩
              wz2PaperCoordinateGridBoundaryRegion
                delta rho coordinate) := Finset.sum_comm
    _ ≤
      ∑ _coordinate : Fin 3,
        ((wz2PaperBoundaryIndicesInWindow rho).card *
            ((C *
                ENNReal.ofReal
                  (16 * (4 * speed + 49 * delta)) *
                family.enncard) *
              (55296 * Kakeya.deltaTubeVolume 1 *
                Kakeya.realRpowENN delta 2)) +
          family.enncard *
            ENNReal.ofReal
              (4000000 * delta ^ 3 *
                ((1 / rho) + (1 / speed)))) := by
      exact Finset.sum_le_sum fun coordinate _ =>
        wz2_paper_coordinate_boundary_mass
          hdelta hdeltaSmall hrho hdeltaRho hspeed
          hline shading coordinate hcwa

theorem wz2_paper_crossing_shading_mass_upper
    {delta rho speed : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hdeltaRho : 50 * delta ≤ rho)
    (hspeed : 0 < speed)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    (hcubical : WZ1PaperIsCubicalShading shading)
    {C : ENNReal}
    (hcwa : WZ2PaperConvexWolffBound family C)
    (crossingFineCells : Finset WZ2PaperCellIndex)
    (hcrossing :
      ∀ cell ∈ crossingFineCells,
        cell ∈ wz1PaperActiveCells shading hdelta ∧
          ¬ (wz1PaperGridCube delta cell ⊆
            wz1PaperGridCube rho
              (wz1PaperGridIndex rho
                (cellCorner delta cell)))) :
    (∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            ⋃ cell ∈ crossingFineCells,
              wz1PaperGridCube delta cell)) ≤
      ∑ _coordinate : Fin 3,
        ((wz2PaperBoundaryIndicesInWindow rho).card *
            ((C *
                ENNReal.ofReal
                  (16 * (4 * speed + 49 * delta)) *
                family.enncard) *
              (55296 * Kakeya.deltaTubeVolume 1 *
                Kakeya.realRpowENN delta 2)) +
          family.enncard *
            ENNReal.ofReal
              (4000000 * delta ^ 3 *
                ((1 / rho) + (1 / speed)))) := by
  have hcrossingSubset :=
    wz2_paper_crossing_region_subset_grid_boundary
      hcubical hdelta hrho crossingFineCells hcrossing
  calc
    (∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            ⋃ cell ∈ crossingFineCells,
              wz1PaperGridCube delta cell))
        ≤
      ∑ index : Fin family.card,
        volume
          (shading.carrier index ∩
            wz2PaperGridBoundaryRegion delta rho) := by
      exact Finset.sum_le_sum fun index _ =>
        measure_mono
          (Set.inter_subset_inter_right _ hcrossingSubset)
    _ ≤
      ∑ _coordinate : Fin 3,
        ((wz2PaperBoundaryIndicesInWindow rho).card *
            ((C *
                ENNReal.ofReal
                  (16 * (4 * speed + 49 * delta)) *
                family.enncard) *
              (55296 * Kakeya.deltaTubeVolume 1 *
                Kakeya.realRpowENN delta 2)) +
          family.enncard *
            ENNReal.ofReal
              (4000000 * delta ^ 3 *
                ((1 / rho) + (1 / speed)))) :=
      wz2_paper_grid_boundary_mass
        hdelta hdeltaSmall hrho hdeltaRho hspeed
        hline shading hcwa

theorem wz2_paper_cwa_boundary_cell_pruning
    {delta rho speed : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hdeltaRho : delta ≤ rho)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hperiodicScale : 50 * delta ≤ rho)
    (hspeed : 0 < speed)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    (hcubical : WZ1PaperIsCubicalShading shading)
    {C : ENNReal}
    (hcwa : WZ2PaperConvexWolffBound family C)
    (multiplicityCap : ENNReal)
    (hcap :
      ∀ point,
        (shading.pointMultiplicity point : ENNReal) ≤
          multiplicityCap)
    (habsorb :
      (∑ _coordinate : Fin 3,
          ((wz2PaperBoundaryIndicesInWindow rho).card *
              ((C *
                  ENNReal.ofReal
                    (16 * (4 * speed + 49 * delta)) *
                  family.enncard) *
                (55296 * Kakeya.deltaTubeVolume 1 *
                  Kakeya.realRpowENN delta 2)) +
            family.enncard *
              ENNReal.ofReal
                (4000000 * delta ^ 3 *
                  ((1 / rho) + (1 / speed))))) <
        shading.mass) :
    Nonempty
      (WZ2PaperBoundaryCellPruningData
        (rho := rho) shading hdelta multiplicityCap) := by
  let crossingFineCells :=
    wz2PaperBoundaryCrossingFineCells
      (rho := rho) shading hdelta
  have hcrossing :
      ∀ cell ∈ crossingFineCells,
        cell ∈ wz1PaperActiveCells shading hdelta ∧
          ¬ (wz1PaperGridCube delta cell ⊆
            wz1PaperGridCube rho
              (wz1PaperGridIndex rho
                (cellCorner delta cell))) := by
    intro cell hcell
    have hsplit := Finset.mem_sdiff.mp hcell
    refine ⟨hsplit.1, ?_⟩
    rw [wz2PaperBoundarySafeFineCells, Finset.mem_filter] at hsplit
    intro hcontain
    exact hsplit.2 ⟨hsplit.1, hcontain⟩
  have hcrossingMass :
      (∑ index : Fin family.card,
          volume
            (shading.carrier index ∩
              wz2PaperBoundaryCrossingRegion
                (rho := rho) shading hdelta)) <
        shading.mass := by
    apply
      (wz2_paper_crossing_shading_mass_upper
        hdelta hdeltaSmall hrho hperiodicScale hspeed
        hline shading hcubical hcwa crossingFineCells
        hcrossing).trans_lt
    exact habsorb
  exact
    wz2_paper_boundary_cell_pruning_of_crossing_mass
      hdelta hdeltaRho hrho hrhoOne
      shading hcubical multiplicityCap hcap hcrossingMass

end Kakeya.Assouad

end
