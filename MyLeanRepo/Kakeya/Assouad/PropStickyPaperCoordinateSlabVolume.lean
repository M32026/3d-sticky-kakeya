import MyLeanRepo.Kakeya.Assouad.PropStickyPaperAxisCoreVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometry
import MyLeanRepo.Kakeya.Assouad.VerticalTubeTopBoundaryVolumeProof

/-!
# Paper-tube volume inside one coordinate slab

The cropped full-line paper carrier lies in the `24 * delta` neighborhood of
four consecutive unit axis segments.  Apply the explicit-speed unit-tube slab
bound to those four segments.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

theorem wz2_paper_tube_coordinate_slab_volume
    {delta a b speed : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hab : a < b)
    (hspeed : 0 < speed)
    (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube)
    (coordinate : Fin 3)
    (hdirection :
      speed ≤ |wz1PaperDirection tube coordinate|) :
    volume
        (wz1PaperTubeCarrier tube ∩
          coordinateSlab coordinate a b) ≤
      4 *
        ENNReal.ofReal
          (Real.pi * (24 * delta) ^ 2 *
            ((b - a + 2 * (24 * delta)) / speed +
              2 * (24 * delta))) := by
  have hcarrier :
      wz1PaperTubeCarrier tube ⊆
        Metric.cthickening (24 * delta)
          (wz2PaperAxisCoreSegment tube) :=
    (wz2_paper_tube_carrier_geometry
      hdelta tube hline).2
  have hsegments :
      Metric.cthickening (24 * delta)
          (wz2PaperAxisCoreSegment tube) ⊆
        ⋃ index : Fin 4,
          Metric.cthickening (24 * delta)
            (wz2PaperAxisUnitSegment tube index) :=
    wz2PaperAxisCore_thickening_subset
      (by positivity) tube
  have hsubset :
      wz1PaperTubeCarrier tube ∩
          coordinateSlab coordinate a b ⊆
        ⋃ index : Fin 4,
          Metric.cthickening (24 * delta)
              (wz2PaperAxisUnitSegment tube index) ∩
            coordinateSlab coordinate a b := by
    intro point hpoint
    have hpointSegments := hsegments (hcarrier hpoint.1)
    rcases Set.mem_iUnion.mp hpointSegments with
      ⟨index, hpointTube⟩
    exact Set.mem_iUnion.mpr
      ⟨index, hpointTube, hpoint.2⟩
  let bound : ENNReal :=
    ENNReal.ofReal
      (Real.pi * (24 * delta) ^ 2 *
        ((b - a + 2 * (24 * delta)) / speed +
          2 * (24 * delta)))
  have hterm :
      ∀ index : Fin 4,
        volume
            (Metric.cthickening (24 * delta)
                (wz2PaperAxisUnitSegment tube index) ∩
              coordinateSlab coordinate a b) ≤
          bound := by
    intro index
    let segmentTube : Kakeya.DeltaTube (24 * delta) :=
      { base :=
          wz1TubeAxisZeroPoint tube +
            ((index : ℕ) - 2 : ℤ) •
              wz1PaperDirection tube
        direction := wz1PaperDirection tube
        direction_unit := wz1PaperDirection_norm tube }
    change
      volume
          (segmentTube.carrier ∩
            coordinateSlab coordinate a b) ≤
        bound
    exact
      tube_coordinate_slab_volume_upper_of_speed
        (by positivity) hab coordinate hspeed
        (by simpa [segmentTube] using hdirection)
  calc
    volume
        (wz1PaperTubeCarrier tube ∩
          coordinateSlab coordinate a b)
        ≤
      volume
        (⋃ index : Fin 4,
          Metric.cthickening (24 * delta)
              (wz2PaperAxisUnitSegment tube index) ∩
            coordinateSlab coordinate a b) :=
      measure_mono hsubset
    _ ≤
        ∑ index : Fin 4,
          volume
            (Metric.cthickening (24 * delta)
                (wz2PaperAxisUnitSegment tube index) ∩
              coordinateSlab coordinate a b) :=
      MeasureTheory.measure_iUnion_fintype_le _ _
    _ ≤ ∑ _index : Fin 4, bound := by
      exact Finset.sum_le_sum fun index _ => hterm index
    _ = 4 * bound := by
      simp [Finset.sum_const]
    _ =
        4 *
          ENNReal.ofReal
            (Real.pi * (24 * delta) ^ 2 *
              ((b - a + 2 * (24 * delta)) / speed +
                2 * (24 * delta))) := rfl

end Kakeya.Assouad

end
