import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSliceSlabMass
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoordinateSlabVolume

/-!
# Coordinate-slab geometry for the common-slice refinement

At fine radius `delta`, one longitudinal interval of width `Delta` meets at
most `O(Delta * delta^2)` volume of each vertical-chart paper tube.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- Half-open height slab of exact width `Delta`. -/
def commonSliceHeightSlab (Delta : ℝ) (index : ℤ) : Set Point3 :=
  {point | point (2 : Fin 3) ∈
    Set.Ico ((index : ℝ) * Delta) (((index : ℝ) + 1) * Delta)}

/-- Closed-slab geometric bound used for one half-open common-slice slab. -/
def commonSliceSingleTubeBound (delta Delta : ℝ) : ENNReal :=
  4 * ENNReal.ofReal
    (Real.pi * (24 * delta) ^ 2 *
      ((Delta + 2 * (24 * delta)) / (1 / 2 : ℝ) +
        2 * (24 * delta)))

lemma commonSliceHeightSlab_subset_coordinateSlab
    {Delta : ℝ} (index : ℤ) :
    commonSliceHeightSlab Delta index ⊆
      coordinateSlab (2 : Fin 3)
        ((index : ℝ) * Delta) (((index : ℝ) + 1) * Delta) := by
  intro point hpoint
  exact ⟨hpoint.1, hpoint.2.le⟩

/-- One paper tube contributes at most the explicit `O(Delta * delta^2)`
quantity to one common-slice height slab. -/
theorem commonSlice_single_tube_height_slab_volume
    {delta Delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hDelta : 0 < Delta)
    (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube)
    (index : ℤ) :
    volume (wz1PaperTubeCarrier tube ∩
        commonSliceHeightSlab Delta index) ≤
      commonSliceSingleTubeBound delta Delta := by
  have hab : (index : ℝ) * Delta < ((index : ℝ) + 1) * Delta := by
    nlinarith
  have hclosed := wz2_paper_tube_coordinate_slab_volume
    hdelta hdeltaSmall hab (by norm_num : (0 : ℝ) < 1 / 2)
    tube hline (2 : Fin 3) (by
      rw [abs_of_nonneg ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans hline.1)]
      exact hline.1)
  calc
    volume (wz1PaperTubeCarrier tube ∩
        commonSliceHeightSlab Delta index) ≤
      volume (wz1PaperTubeCarrier tube ∩
        coordinateSlab (2 : Fin 3)
          ((index : ℝ) * Delta) (((index : ℝ) + 1) * Delta)) := by
      exact measure_mono (Set.inter_subset_inter_right _
        (commonSliceHeightSlab_subset_coordinateSlab index))
    _ ≤ commonSliceSingleTubeBound delta Delta := by
      convert hclosed using 1 <;> simp [commonSliceSingleTubeBound] <;> ring

/-- The total shaded mass in a height slab is bounded by the number of
meeting tubes times the single-tube slab bound. -/
theorem commonSlice_height_slab_mass_le_meetingCount
    {delta Delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (hline : WZ1PaperIsLineClass family)
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hDelta : 0 < Delta)
    (index : ℤ) :
    commonSliceSlabMass shading (commonSliceHeightSlab Delta index) ≤
      commonSliceSingleTubeBound delta Delta *
        (commonSliceMeetingCount
          (fun tube : Fin family.card => fun _ : Unit =>
            commonSliceSlabMeets shading
              (commonSliceHeightSlab Delta index) tube) () : ENNReal) := by
  apply commonSliceSlabMass_le_meetingCount
  intro tube _hmeets
  calc
    volume (shading.carrier tube ∩ commonSliceHeightSlab Delta index) ≤
      volume (wz1PaperTubeCarrier (family.tube tube) ∩
        commonSliceHeightSlab Delta index) := by
      exact measure_mono (Set.inter_subset_inter_left _
        (shading.subset_body tube))
    _ ≤ commonSliceSingleTubeBound delta Delta :=
      commonSlice_single_tube_height_slab_volume
        hdelta hdeltaSmall hDelta (family.tube tube) (hline tube) index

end Kakeya.Assouad.PureWZ2

end
