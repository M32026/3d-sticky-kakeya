import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperInfrastructure

/-!
# Restricting a dense cubicalization by whole fine cells

If a whole-cell subset of a dense cubicalization is retained, intersecting
the original ordinary source with that subset and applying the same dense
cubicalization recovers the subset exactly.  A positive restricted ordinary
mass is essential: the empty source makes the density threshold zero and
would select every cell contained in the paper tube.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Whole-cell restriction commutes exactly with the Section 6 dense
cubicalization, provided the restricted ordinary source has positive mass. -/
lemma pureWZ2DenseCubicalization_inter_whole_cells
    {delta : ℝ}
    (tube : Kakeya.DeltaTube delta)
    (ordinary cropped : Set Point3)
    (hdelta : 0 < delta)
    (hcropped : cropped ⊆
      pureWZ2DenseCubicalization tube ordinary)
    (hwhole : ∀ point ∈ cropped,
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆ cropped)
    (hpositive : 0 < volume (ordinary ∩ cropped)) :
    pureWZ2DenseCubicalization tube (ordinary ∩ cropped) = cropped := by
  ext point
  constructor
  · intro hpoint
    by_contra hpointCropped
    have hempty :
        (ordinary ∩ cropped) ∩
            wz1PaperGridCube delta (wz1PaperGridIndex delta point) = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨other, hother⟩
      have hgrid : wz1PaperGridIndex delta other =
          wz1PaperGridIndex delta point :=
        (mem_wz1PaperGridCube delta
          (wz1PaperGridIndex delta point) other).mp hother.2
      have hpointCell : point ∈
          wz1PaperGridCube delta (wz1PaperGridIndex delta other) :=
        (mem_wz1PaperGridCube delta
          (wz1PaperGridIndex delta other) point).mpr hgrid.symm
      exact hpointCropped (hwhole other hother.1.2 hpointCell)
    have htubeFinite : volume tube.carrier ≠ ⊤ :=
      wz2_paper_ordinary_tube_volume_ne_top tube hdelta
    have hinvPositive : 0 < (volume tube.carrier)⁻¹ :=
      ENNReal.inv_pos.mpr htubeFinite
    have hcubePositive : 0 <
        volume (wz1PaperGridCube delta
          (wz1PaperGridIndex delta point)) :=
      wz1PaperGridCube_volume_pos hdelta _
    have hfactorPositive : 0 <
        (100 : ENNReal)⁻¹ * volume (ordinary ∩ cropped) *
          (volume tube.carrier)⁻¹ *
          volume (wz1PaperGridCube delta
            (wz1PaperGridIndex delta point)) := by
      have hhundred : 0 < (100 : ENNReal)⁻¹ :=
        ENNReal.inv_pos.mpr (by norm_num)
      exact ENNReal.mul_pos
        (ENNReal.mul_pos
          (ENNReal.mul_pos hhundred.ne' hpositive.ne').ne'
          hinvPositive.ne').ne'
        hcubePositive.ne'
    have hzero : volume
        ((ordinary ∩ cropped) ∩
          wz1PaperGridCube delta
            (wz1PaperGridIndex delta point)) = 0 := by
      rw [hempty]
      exact measure_empty
    have hle := hpoint.2
    rw [hzero] at hle
    exact (not_lt_of_ge hle) hfactorPositive
  · intro hpoint
    have hold := hcropped hpoint
    refine ⟨hold.1, ?_⟩
    have hsourceMass : volume (ordinary ∩ cropped) ≤ volume ordinary :=
      measure_mono Set.inter_subset_left
    have hcellSubset :
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
          cropped := hwhole point hpoint
    have hintersection :
        (ordinary ∩ cropped) ∩
            wz1PaperGridCube delta (wz1PaperGridIndex delta point) =
          ordinary ∩
            wz1PaperGridCube delta (wz1PaperGridIndex delta point) := by
      ext other
      simp only [Set.mem_inter_iff]
      constructor
      · intro hother
        exact ⟨hother.1.1, hother.2⟩
      · intro hother
        exact ⟨⟨hother.1, hcellSubset hother.2⟩, hother.2⟩
    calc
      (100 : ENNReal)⁻¹ * volume (ordinary ∩ cropped) *
            (volume tube.carrier)⁻¹ *
            volume (wz1PaperGridCube delta
              (wz1PaperGridIndex delta point))
          ≤ (100 : ENNReal)⁻¹ * volume ordinary *
            (volume tube.carrier)⁻¹ *
            volume (wz1PaperGridCube delta
              (wz1PaperGridIndex delta point)) := by
              gcongr
      _ ≤ volume
          (ordinary ∩ wz1PaperGridCube delta
            (wz1PaperGridIndex delta point)) := hold.2
      _ = volume
          ((ordinary ∩ cropped) ∩
            wz1PaperGridCube delta
              (wz1PaperGridIndex delta point)) := by
              rw [hintersection]

end Kakeya.Assouad.PureWZ2

end
