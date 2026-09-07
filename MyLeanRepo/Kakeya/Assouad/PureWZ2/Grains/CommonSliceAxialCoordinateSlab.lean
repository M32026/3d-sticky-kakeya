import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSliceCoordinateSlab
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoordinateSlabVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCanonicalDilatedDirection
import MyLeanRepo.Kakeya.Assouad.WZ1.HorizontalChartNormalization.Basic

/-!
# Parent-axial slabs for Proposition 6.3

The longitudinal coordinate is the third coordinate of the frozen literal
unit-rescaling map.  Thus these slabs become exact horizontal slabs after
unit rescaling, as required in `wz2_63.tex`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

def proposition63AxialCoordinate
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (point : Point3) : ℝ :=
  (wz2PaperLiteralUnitRescalingMap anchor hrho point) (2 : Fin 3)

def proposition63AxialSlab
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (Delta : ℝ) (index : ℤ) : Set Point3 :=
  {point | proposition63AxialCoordinate anchor hrho point ∈
    Set.Ico ((index : ℝ) * Delta) (((index : ℝ) + 1) * Delta)}

lemma proposition63AxialCoordinate_eq
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (point : Point3) :
    proposition63AxialCoordinate anchor hrho point =
      (1 / 100 : ℝ) * inner ℝ
        (point - wz1TubeAxisZeroPoint anchor)
        (wz1PaperDirection anchor) := by
  exact wz2PaperLiteralUnitRescalingMap_coord2 anchor hrho point

lemma proposition63AxialSlab_measurable
    {rho Delta : ℝ} (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (index : ℤ) : MeasurableSet
      (proposition63AxialSlab anchor hrho Delta index) := by
  change MeasurableSet
    ((proposition63AxialCoordinate anchor hrho) ⁻¹'
      Set.Ico ((index : ℝ) * Delta) (((index : ℝ) + 1) * Delta))
  apply measurableSet_Ico.preimage
  rw [show proposition63AxialCoordinate anchor hrho = fun point =>
      (1 / 100 : ℝ) * inner ℝ
        (point - wz1TubeAxisZeroPoint anchor)
        (wz1PaperDirection anchor) by
    funext point
    exact proposition63AxialCoordinate_eq anchor hrho point]
  fun_prop

def proposition63OrientedSlab (normal : Point3) (a b : ℝ) : Set Point3 :=
  {point | a ≤ inner ℝ point normal ∧ inner ℝ point normal ≤ b}

/-- Rotate an arbitrary unit normal to the third coordinate and apply the
existing explicit-speed tube-slab bound. -/
lemma deltaTube_oriented_slab_volume_upper_of_speed
    {delta a b : ℝ} (hdelta : 0 < delta) (hab : a < b)
    {tube : Kakeya.DeltaTube delta}
    {normal : Point3} (hnormal : ‖normal‖ = 1)
    {speed : ℝ} (hspeed : 0 < speed)
    (hdirection : speed ≤ |inner ℝ tube.direction normal|) :
    volume (tube.carrier ∩ proposition63OrientedSlab normal a b) ≤
      ENNReal.ofReal
        (Real.pi * delta ^ 2 *
          ((b - a + 2 * delta) / speed + 2 * delta)) := by
  let rotation := householderToE3 normal hnormal
  let rotated := transportTube rotation tube
  have hrotatedDirection : rotated.direction (2 : Fin 3) =
      inner ℝ tube.direction normal := by
    dsimp only [rotated, transportTube]
    rw [show (rotation tube.direction) (2 : Fin 3) =
        inner ℝ (rotation tube.direction) e3 by
      simp [e3, EuclideanSpace.inner_single_right]]
    exact (householderToE3_symmetric normal hnormal tube.direction e3).trans
      (by rw [householderToE3_sends_e3_to_d])
  have hslabImage : rotation '' proposition63OrientedSlab normal a b =
      coordinateSlab (2 : Fin 3) a b := by
    ext point
    constructor
    · rintro ⟨source, hsource, rfl⟩
      change a ≤ (rotation source) 2 ∧ (rotation source) 2 ≤ b
      rw [show (rotation source) (2 : Fin 3) =
          inner ℝ source normal by
        rw [show (rotation source) (2 : Fin 3) =
            inner ℝ (rotation source) e3 by
          simp [e3, EuclideanSpace.inner_single_right],
          householderToE3_symmetric, householderToE3_sends_e3_to_d]]
      exact hsource
    · intro hpoint
      refine ⟨rotation.symm point, ?_, rotation.apply_symm_apply point⟩
      change a ≤ inner ℝ (rotation.symm point) normal ∧
        inner ℝ (rotation.symm point) normal ≤ b
      have hcoord : inner ℝ (rotation.symm point) normal = point 2 := by
        calc
          inner ℝ (rotation.symm point) normal =
              inner ℝ (rotation (rotation.symm point))
                (rotation normal) :=
            (rotation.inner_map_map (rotation.symm point) normal).symm
          _ = inner ℝ point e3 := by
            rw [rotation.apply_symm_apply,
              householderToE3_sends_d_to_e3]
          _ = point 2 := by
            simp [e3, EuclideanSpace.inner_single_right]
      rwa [hcoord]
  have hintersectionImage : rotation ''
      (tube.carrier ∩ proposition63OrientedSlab normal a b) =
      rotated.carrier ∩ coordinateSlab (2 : Fin 3) a b := by
    rw [Set.image_inter rotation.injective,
      ← transportTube_carrier rotation tube, hslabImage]
  have hvolume : volume
      (tube.carrier ∩ proposition63OrientedSlab normal a b) =
      volume (rotated.carrier ∩ coordinateSlab (2 : Fin 3) a b) := by
    rw [← hintersectionImage, volume_image]
  rw [hvolume]
  exact tube_coordinate_slab_volume_upper_of_speed hdelta hab
    (2 : Fin 3) hspeed (by simpa [hrotatedDirection] using hdirection)

/-- One cropped paper tube contributes `O(delta^2 Delta)` to one slab in
the frozen rescaled longitudinal coordinate. -/
theorem proposition63_single_tube_axial_slab_volume
    {delta rho Delta : ℝ}
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1) (hDelta : 0 < Delta)
    (tube : Kakeya.DeltaTube delta) (anchor : Kakeya.DeltaTube rho)
    (htubeLine : WZ1PaperTubeInLineClass tube)
    (hcover : WZ1PaperTubeCovers tube anchor) (index : ℤ) :
    volume (wz1PaperTubeCarrier tube ∩
        proposition63AxialSlab anchor hrho Delta index) ≤
      commonSliceSingleTubeBound delta (100 * Delta) := by
  have hdilated : WZ2PaperDilatedTubeCovers 2 tube anchor := by
    exact hcover.trans (by linarith)
  have hspeed : (1 / 2 : ℝ) ≤
      |inner ℝ (wz1PaperDirection tube) (wz1PaperDirection anchor)| :=
    (hdilated.inner_direction_ge_half hrhoOne).trans (le_abs_self _)
  have hcarrier : wz1PaperTubeCarrier tube ⊆
      Metric.cthickening (24 * delta) (wz2PaperAxisCoreSegment tube) :=
    (wz2_paper_tube_carrier_geometry hdelta tube htubeLine).2
  have hsegments : Metric.cthickening (24 * delta)
      (wz2PaperAxisCoreSegment tube) ⊆
      ⋃ segment : Fin 4, Metric.cthickening (24 * delta)
        (wz2PaperAxisUnitSegment tube segment) :=
    wz2PaperAxisCore_thickening_subset (by positivity) tube
  let c := inner ℝ (wz1TubeAxisZeroPoint anchor)
    (wz1PaperDirection anchor)
  let a := 100 * ((index : ℝ) * Delta) + c
  let b := 100 * (((index : ℝ) + 1) * Delta) + c
  have hab : a < b := by dsimp [a, b]; nlinarith
  have hslab : proposition63AxialSlab anchor hrho Delta index ⊆
      proposition63OrientedSlab (wz1PaperDirection anchor) a b := by
    intro point hpoint
    rw [proposition63AxialSlab, Set.mem_setOf_eq,
      proposition63AxialCoordinate_eq] at hpoint
    change a ≤ inner ℝ point (wz1PaperDirection anchor) ∧
      inner ℝ point (wz1PaperDirection anchor) ≤ b
    dsimp [a, b, c]
    rw [inner_sub_left] at hpoint
    constructor <;> nlinarith [hpoint.1, hpoint.2]
  have hsubset : wz1PaperTubeCarrier tube ∩
      proposition63AxialSlab anchor hrho Delta index ⊆
      ⋃ segment : Fin 4, Metric.cthickening (24 * delta)
        (wz2PaperAxisUnitSegment tube segment) ∩
          proposition63OrientedSlab (wz1PaperDirection anchor) a b := by
    rintro point ⟨hpoint, hpointSlab⟩
    rcases Set.mem_iUnion.mp (hsegments (hcarrier hpoint)) with
      ⟨segment, hsegment⟩
    exact Set.mem_iUnion.mpr ⟨segment, hsegment, hslab hpointSlab⟩
  let bound := ENNReal.ofReal
    (Real.pi * (24 * delta) ^ 2 *
      (((b - a) + 2 * (24 * delta)) / (1 / 2 : ℝ) +
        2 * (24 * delta)))
  have hterm : ∀ segment : Fin 4, volume
      (Metric.cthickening (24 * delta)
        (wz2PaperAxisUnitSegment tube segment) ∩
          proposition63OrientedSlab (wz1PaperDirection anchor) a b) ≤
      bound := by
    intro segment
    let segmentTube : Kakeya.DeltaTube (24 * delta) :=
      { base := wz1TubeAxisZeroPoint tube +
          ((segment : ℕ) - 2 : ℤ) • wz1PaperDirection tube
        direction := wz1PaperDirection tube
        direction_unit := wz1PaperDirection_norm tube }
    change volume (segmentTube.carrier ∩
      proposition63OrientedSlab (wz1PaperDirection anchor) a b) ≤ bound
    exact deltaTube_oriented_slab_volume_upper_of_speed
      (by positivity) hab (wz1PaperDirection_norm anchor)
      (by norm_num : (0 : ℝ) < 1 / 2) (by simpa [segmentTube] using hspeed)
  calc
    volume (wz1PaperTubeCarrier tube ∩
        proposition63AxialSlab anchor hrho Delta index) ≤
      volume (⋃ segment : Fin 4, Metric.cthickening (24 * delta)
        (wz2PaperAxisUnitSegment tube segment) ∩
          proposition63OrientedSlab (wz1PaperDirection anchor) a b) :=
      measure_mono hsubset
    _ ≤ ∑ segment : Fin 4, volume
        (Metric.cthickening (24 * delta)
          (wz2PaperAxisUnitSegment tube segment) ∩
            proposition63OrientedSlab (wz1PaperDirection anchor) a b) :=
      MeasureTheory.measure_iUnion_fintype_le _ _
    _ ≤ ∑ _segment : Fin 4, bound := Finset.sum_le_sum fun segment _ => hterm segment
    _ = 4 * bound := by simp [Finset.sum_const]
    _ = commonSliceSingleTubeBound delta (100 * Delta) := by
      simp only [commonSliceSingleTubeBound, bound, a, b]
      congr 2
      ring_nf

end Kakeya.Assouad.PureWZ2

end
