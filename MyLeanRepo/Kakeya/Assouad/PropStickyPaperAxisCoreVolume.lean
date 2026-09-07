import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometryStatements
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling

/-!
# Volume of the finite paper-axis capsule

The length-four paper-axis core is covered by four unit axis segments.  Its
closed `24 * delta` neighborhood therefore has volume at most four canonical
tube volumes at that radius.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric

def wz2PaperAxisUnitSegment
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (index : Fin 4) : Set Point3 :=
  Kakeya.unitSegment
    (wz1TubeAxisZeroPoint tube +
      ((index : ℕ) - 2 : ℤ) • wz1PaperDirection tube)
    (wz1PaperDirection tube)

lemma wz2PaperAxisCoreSegment_subset_iUnion
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    wz2PaperAxisCoreSegment tube ⊆
      ⋃ index : Fin 4, wz2PaperAxisUnitSegment tube index := by
  rintro point ⟨parameter, hparameter, rfl⟩
  by_cases hfirst : parameter ≤ 1
  · apply Set.mem_iUnion.mpr
    refine ⟨(0 : Fin 4), parameter, ⟨hparameter.1, hfirst⟩, ?_⟩
    simp [wz2PaperAxisUnitSegment]
    module
  · by_cases hsecond : parameter ≤ 2
    · apply Set.mem_iUnion.mpr
      refine ⟨(1 : Fin 4), parameter - 1,
        ⟨by linarith, by linarith⟩, ?_⟩
      simp [wz2PaperAxisUnitSegment]
      module
    · by_cases hthird : parameter ≤ 3
      · apply Set.mem_iUnion.mpr
        refine ⟨(2 : Fin 4), parameter - 2,
          ⟨by linarith, by linarith⟩, ?_⟩
        simp [wz2PaperAxisUnitSegment]
      · apply Set.mem_iUnion.mpr
        refine ⟨(3 : Fin 4), parameter - 3,
          ⟨by linarith, by linarith [hparameter.2]⟩, ?_⟩
        simp [wz2PaperAxisUnitSegment]
        module

lemma wz2PaperAxisCoreSegment_compact
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    IsCompact (wz2PaperAxisCoreSegment tube) := by
  exact isCompact_Icc.image (by fun_prop)

lemma wz2PaperAxisCore_thickening_subset
    {delta radius : ℝ}
    (hradius : 0 ≤ radius)
    (tube : Kakeya.DeltaTube delta) :
    Metric.cthickening radius (wz2PaperAxisCoreSegment tube) ⊆
      ⋃ index : Fin 4,
        Metric.cthickening radius
          (wz2PaperAxisUnitSegment tube index) := by
  intro point hpoint
  have hcoreCompact :=
    wz2PaperAxisCoreSegment_compact tube
  rw [hcoreCompact.cthickening_eq_biUnion_closedBall hradius] at hpoint
  rcases Set.mem_iUnion.mp hpoint with ⟨axisPoint, hpoint⟩
  rcases Set.mem_iUnion.mp hpoint with ⟨haxisPoint, hpointBall⟩
  have haxisUnion :=
    wz2PaperAxisCoreSegment_subset_iUnion tube haxisPoint
  rcases Set.mem_iUnion.mp haxisUnion with ⟨index, haxisSegment⟩
  apply Set.mem_iUnion.mpr
  refine ⟨index, ?_⟩
  have hsegmentCompact :
      IsCompact (wz2PaperAxisUnitSegment tube index) :=
    isCompact_Icc.image (by fun_prop)
  rw [hsegmentCompact.cthickening_eq_biUnion_closedBall hradius]
  exact Set.mem_iUnion₂.mpr ⟨axisPoint, haxisSegment, hpointBall⟩

theorem wz2PaperAxisCoreSegment_thickening_volume_le
    {delta : ℝ} (hdelta : 0 < delta)
    (tube : Kakeya.DeltaTube delta) :
    volume
        (Metric.cthickening (24 * delta)
          (wz2PaperAxisCoreSegment tube)) ≤
      4 * Kakeya.deltaTubeVolume (24 * delta) := by
  have hradius : 0 ≤ 24 * delta := by positivity
  calc
    volume
        (Metric.cthickening (24 * delta)
          (wz2PaperAxisCoreSegment tube))
        ≤ volume
            (⋃ index : Fin 4,
              Metric.cthickening (24 * delta)
                (wz2PaperAxisUnitSegment tube index)) :=
      measure_mono
        (wz2PaperAxisCore_thickening_subset
          hradius tube)
    _ ≤ ∑ index : Fin 4,
          volume
            (Metric.cthickening (24 * delta)
              (wz2PaperAxisUnitSegment tube index)) :=
      MeasureTheory.measure_iUnion_fintype_le _ _
    _ = ∑ _index : Fin 4,
          Kakeya.deltaTubeVolume (24 * delta) := by
      apply Finset.sum_congr rfl
      intro index _
      let segmentTube : Kakeya.DeltaTube (24 * delta) :=
        { base :=
            wz1TubeAxisZeroPoint tube +
              ((index : ℕ) - 2 : ℤ) •
                wz1PaperDirection tube
          direction := wz1PaperDirection tube
          direction_unit := wz1PaperDirection_norm tube }
      change segmentTube.volume =
        Kakeya.deltaTubeVolume (24 * delta)
      exact tube_volume_scaling.1 (24 * delta) segmentTube
    _ = 4 * Kakeya.deltaTubeVolume (24 * delta) := by
      simp [Finset.sum_const]

/-- Quadratic absolute upper bound for the finite paper-axis capsule. -/
theorem wz2PaperAxisCoreSegment_thickening_volume_quadratic
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (tube : Kakeya.DeltaTube delta) :
    volume
        (Metric.cthickening (24 * delta)
          (wz2PaperAxisCoreSegment tube)) ≤
      55296 * Kakeya.deltaTubeVolume 1 *
        Kakeya.realRpowENN delta 2 := by
  let segmentTube : Kakeya.DeltaTube (24 * delta) :=
    { base := 0
      direction := EuclideanSpace.single (0 : Fin 3) 1
      direction_unit := by simp }
  have hradius : 0 < 24 * delta := by positivity
  have hradiusOne : 24 * delta ≤ 1 := by
    linarith
  have hscale :
      Kakeya.deltaTubeVolume (24 * delta) ≤
        24 * Kakeya.realRpowENN (24 * delta) 2 *
          Kakeya.deltaTubeVolume 1 := by
    have hvolume :=
      tube_volume_scaling.2.2
        (24 * delta) hradius hradiusOne segmentTube
    rw [tube_volume_scaling.1 (24 * delta) segmentTube] at hvolume
    exact hvolume
  have hrpow :
      Kakeya.realRpowENN (24 * delta) 2 =
        576 * Kakeya.realRpowENN delta 2 := by
    simp only [Kakeya.realRpowENN]
    have hreal :
        Real.rpow (24 * delta) 2 =
          576 * Real.rpow delta 2 := by
      calc
        Real.rpow (24 * delta) 2 =
            (24 * delta) ^ 2 := Real.rpow_two _
        _ = 576 * delta ^ 2 := by ring
        _ = 576 * Real.rpow delta 2 := by
          congr 1
          exact (Real.rpow_two delta).symm
    rw [hreal]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 576)]
    norm_num
  calc
    volume
        (Metric.cthickening (24 * delta)
          (wz2PaperAxisCoreSegment tube))
        ≤ 4 * Kakeya.deltaTubeVolume (24 * delta) :=
      wz2PaperAxisCoreSegment_thickening_volume_le hdelta tube
    _ ≤ 4 *
        (24 * Kakeya.realRpowENN (24 * delta) 2 *
          Kakeya.deltaTubeVolume 1) := by
      gcongr
    _ = 55296 * Kakeya.deltaTubeVolume 1 *
        Kakeya.realRpowENN delta 2 := by
      rw [hrpow]
      ring

/--
The frozen carrier-geometry statement implies the convexity and uniform
quadratic volume bound needed by the normalized Convex-Wolff cardinality core.
-/
theorem wz2PaperTubeCarrier_convex_and_volume_quadratic
    (hgeometry : WZ2PaperTubeCarrierGeometryStatement)
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube) :
    Convex ℝ (wz1PaperTubeCarrier tube) ∧
      volume (wz1PaperTubeCarrier tube) ≤
        55296 * Kakeya.deltaTubeVolume 1 *
          Kakeya.realRpowENN delta 2 := by
  rcases hgeometry hdelta tube hline with
    ⟨hconvex, hcontained⟩
  refine ⟨hconvex, ?_⟩
  exact
    (measure_mono hcontained).trans
      (wz2PaperAxisCoreSegment_thickening_volume_quadratic
        hdelta hdeltaSmall tube)

end Kakeya.Assouad

end
