import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierVolumeLower
import MyLeanRepo.Kakeya.Assouad.PropStickyStatements
import MyLeanRepo.Kakeya.Assouad.PureWZ2.BodyCWAFromVolumeFloor
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound

/-!
# A family-free coarse top-level CWA bound

For the first Proposition 6.3 chart we only need a finite top-level
Convex--Wolff constant before regularizing its ordinary trace.  The crude
constant `delta⁻²` is available for every line-class paper tube family: if a
convex set contains any indexed paper tube, its volume is at least the
ordinary tube volume and hence at least `delta²`; the contained count is at
most the total indexed cardinality.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- Every line-class family has the crude top-level CWA constant
`delta⁻²`.  This estimate is independent of support and of all runtime
selection densities. -/
theorem wz2_paper_lineClass_trivial_topLevelCWA
    {delta : ℝ}
    (delta_pos : 0 < delta)
    (delta_small : delta ≤ 1 / 12)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (line_class : WZ1PaperIsLineClass family) :
    WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-2 : ℝ)) := by
  have volume_floor : ∀ index,
      Kakeya.realRpowENN delta 2 ≤
        ((wz1PaperBodyFamily family).body index).volume := by
    intro index
    change Kakeya.realRpowENN delta 2 ≤
      volume (wz1PaperTubeCarrier (family.tube index))
    calc
      Kakeya.realRpowENN delta 2 = ENNReal.ofReal (delta ^ 2) := by
        simp [Kakeya.realRpowENN, Real.rpow_two]
      _ ≤ Kakeya.deltaTubeVolume delta := canonical_volume_lower delta_pos
      _ ≤ volume (wz1PaperTubeCarrier (family.tube index)) :=
        wz2PaperTubeCarrier_volume_lower delta_pos delta_small
          (family.tube index) (line_class index)
  have floor_zero : Kakeya.realRpowENN delta 2 ≠ 0 := by
    simp [Kakeya.realRpowENN, delta_pos.ne']
  have floor_top : Kakeya.realRpowENN delta 2 ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have cwa : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta 2)⁻¹ :=
    wz2PaperBodyConvexWolffBound_of_volume_floor
      (wz1PaperBodyFamily family) (Kakeya.realRpowENN delta 2)
      floor_zero floor_top volume_floor
  rw [pure_wz2_realRpowENN_inv delta_pos] at cwa
  exact cwa

end Kakeya.Assouad.PureWZ2

end
