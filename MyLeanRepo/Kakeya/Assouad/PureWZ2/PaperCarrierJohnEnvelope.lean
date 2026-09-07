import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometry
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperAxisCoreVolume
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.EllipsoidProps

/-!
# A cropped paper tube inside a fixed John enlargement

If an ordinary line-class tube lies in an ellipsoid, then its cropped
full-line paper carrier lies in the factor-70 homothety of the same
ellipsoid.  The three contributions in John coordinates are `1 + 20 + 48`:
the base point, the finite length-four paper axis core, and the `24 * delta`
capsule error.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

lemma wz2PaperTubeCarrier_subset_ellipsoid_homothety_seventy
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube)
    (hbase : ‖tube.base‖ ≤ 4)
    (center : Point3) (linear : Point3 ≃ₗ[ℝ] Point3)
    (hcarrier : tube.carrier ⊆ JohnEllipsoid.ellipsoid center linear) :
    wz1PaperTubeCarrier tube ⊆
      AffineMap.homothety center (70 : ℝ) ''
        JohnEllipsoid.ellipsoid center linear := by
  intro point hpoint
  have hgeom :=
    (wz2_paper_tube_carrier_geometry hdelta tube hline).2 hpoint
  rcases exists_dist_le_of_mem_cthickening_closed
      (wz2PaperAxisCoreSegment_compact tube).isClosed
      (by positivity : 0 ≤ 24 * delta) hgeom with
    ⟨axisPoint, haxisPoint, hpointAxis⟩
  have hbaseCarrier : tube.base ∈ tube.carrier := by
    exact Metric.mem_cthickening_of_dist_le
      tube.base tube.base delta
      (Kakeya.unitSegment tube.base tube.direction)
      ⟨0, by norm_num, by simp⟩ (by simp [hdelta.le])
  have hendCarrier : tube.base + tube.direction ∈ tube.carrier := by
    exact Metric.mem_cthickening_of_dist_le
      (tube.base + tube.direction) (tube.base + tube.direction) delta
      (Kakeya.unitSegment tube.base tube.direction)
      ⟨1, by norm_num, by simp⟩ (by simp [hdelta.le])
  have hbaseEllipsoid := hcarrier hbaseCarrier
  have hendEllipsoid := hcarrier hendCarrier
  have hbaseJohn : ‖linear.symm (tube.base - center)‖ ≤ 1 :=
    (JohnEllipsoid.ellipsoid_mem_iff center linear tube.base).mp hbaseEllipsoid
  have hendJohn :
      ‖linear.symm (tube.base + tube.direction - center)‖ ≤ 1 :=
    (JohnEllipsoid.ellipsoid_mem_iff center linear
      (tube.base + tube.direction)).mp hendEllipsoid
  have hdirectionJohn : ‖linear.symm tube.direction‖ ≤ 2 := by
    have hid : linear.symm tube.direction =
        linear.symm (tube.base + tube.direction - center) -
          linear.symm (tube.base - center) := by
      rw [← map_sub]
      congr 1
      abel
    rw [hid]
    exact (norm_sub_le _ _).trans (by linarith)
  have hdirTwo : (1 / 2 : ℝ) ≤ |tube.direction (2 : Fin 3)| :=
    hline.vertical
  have hdirTwoPos : 0 < |tube.direction (2 : Fin 3)| := by linarith
  have hbaseTwo : |tube.base (2 : Fin 3)| ≤ 4 := by
    exact (PiLp.norm_apply_le tube.base (2 : Fin 3)).trans hbase
  rw [wz2PaperAxisCoreSegment_eq] at haxisPoint
  rcases haxisPoint with ⟨parameter, hparameter, haxisEq⟩
  have hparameterBound : |parameter| ≤ 2 := abs_le.mpr hparameter
  have hratio :
      |tube.base (2 : Fin 3) / tube.direction (2 : Fin 3)| ≤ 8 := by
    rw [abs_div]
    calc
      |tube.base (2 : Fin 3)| / |tube.direction (2 : Fin 3)|
          ≤ 4 / |tube.direction (2 : Fin 3)| := by gcongr
      _ ≤ 4 / (1 / 2 : ℝ) := by
            apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hdirTwo
      _ = 8 := by norm_num
  have horiented :
      wz1PaperDirection tube = tube.direction ∨
        wz1PaperDirection tube = -tube.direction := by
    unfold wz1PaperDirection
    split_ifs <;> simp
  have haxisBaseJohn :
      ‖linear.symm (axisPoint - tube.base)‖ ≤ 20 := by
    have hzero : wz1TubeAxisZeroPoint tube - tube.base =
        -(tube.base (2 : Fin 3) / tube.direction (2 : Fin 3)) •
          tube.direction := by
      simp [wz1TubeAxisZeroPoint]
    have hdecomp : axisPoint - tube.base =
        (wz1TubeAxisZeroPoint tube - tube.base) +
          parameter • wz1PaperDirection tube := by
      rw [haxisEq]
      abel
    rw [hdecomp, map_add, hzero, map_smul, map_smul]
    have horientedNorm :
        ‖linear.symm (wz1PaperDirection tube)‖ =
          ‖linear.symm tube.direction‖ := by
      rcases horiented with h | h
      · rw [h]
      · rw [h, map_neg, norm_neg]
    calc
      ‖(-(tube.base (2 : Fin 3) / tube.direction (2 : Fin 3))) •
            linear.symm tube.direction +
          parameter • linear.symm (wz1PaperDirection tube)‖
          ≤ ‖(-(tube.base (2 : Fin 3) / tube.direction (2 : Fin 3))) •
              linear.symm tube.direction‖ +
            ‖parameter • linear.symm (wz1PaperDirection tube)‖ :=
              norm_add_le _ _
      _ = |tube.base (2 : Fin 3) / tube.direction (2 : Fin 3)| *
              ‖linear.symm tube.direction‖ +
            |parameter| * ‖linear.symm tube.direction‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_neg, horientedNorm]
      _ ≤ 8 * 2 + 2 * 2 := by gcongr
      _ = 20 := by norm_num
  let errorPoint : Point3 :=
    tube.base + (1 / 24 : ℝ) • (point - axisPoint)
  have herrorDistance : dist errorPoint tube.base ≤ delta := by
    rw [dist_eq_norm]
    have hid : errorPoint - tube.base =
        (1 / 24 : ℝ) • (point - axisPoint) := by
      simp [errorPoint]
    rw [hid, norm_smul, Real.norm_eq_abs]
    norm_num
    have hdistNorm : ‖point - axisPoint‖ ≤ 24 * delta := by
      simpa [dist_eq_norm] using hpointAxis
    linarith
  have herrorCarrier : errorPoint ∈ tube.carrier := by
    exact Metric.mem_cthickening_of_dist_le
      errorPoint tube.base delta
      (Kakeya.unitSegment tube.base tube.direction)
      ⟨0, by norm_num, by simp⟩ herrorDistance
  have herrorEllipsoid := hcarrier herrorCarrier
  have herrorJohn : ‖linear.symm (errorPoint - center)‖ ≤ 1 :=
    (JohnEllipsoid.ellipsoid_mem_iff center linear errorPoint).mp
      herrorEllipsoid
  have hpointAxisJohn :
      ‖linear.symm (point - axisPoint)‖ ≤ 48 := by
    have hid : linear.symm (point - axisPoint) =
        (24 : ℝ) •
          (linear.symm (errorPoint - center) -
            linear.symm (tube.base - center)) := by
      rw [← map_sub, ← map_smul]
      congr 1
      simp [errorPoint]
    have hsub :
        ‖linear.symm (errorPoint - center) -
          linear.symm (tube.base - center)‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by linarith)
    rw [hid]
    calc
      ‖(24 : ℝ) •
          (linear.symm (errorPoint - center) -
            linear.symm (tube.base - center))‖ =
          24 * ‖linear.symm (errorPoint - center) -
            linear.symm (tube.base - center)‖ := by
              rw [norm_smul, Real.norm_eq_abs]
              norm_num
      _ ≤ 24 * 2 := by gcongr
      _ = 48 := by norm_num
  have hpointJohn : ‖linear.symm (point - center)‖ ≤ 69 := by
    have hid : point - center =
        (tube.base - center) + (axisPoint - tube.base) +
          (point - axisPoint) := by abel
    rw [hid, map_add, map_add]
    calc
      ‖linear.symm (tube.base - center) +
          linear.symm (axisPoint - tube.base) +
          linear.symm (point - axisPoint)‖
          ≤ ‖linear.symm (tube.base - center)‖ +
              ‖linear.symm (axisPoint - tube.base)‖ +
              ‖linear.symm (point - axisPoint)‖ := by
                exact (norm_add_le _ _).trans (by
                  gcongr
                  exact norm_add_le _ _)
      _ ≤ 1 + 20 + 48 := by gcongr
      _ = 69 := by norm_num
  let sourcePoint : Point3 :=
    center + (1 / 70 : ℝ) • (point - center)
  have hsourceJohn : ‖linear.symm (sourcePoint - center)‖ ≤ 1 := by
    have hid : linear.symm (sourcePoint - center) =
        (1 / 70 : ℝ) • linear.symm (point - center) := by
      rw [← map_smul]
      simp [sourcePoint]
    rw [hid]
    calc
      ‖(1 / 70 : ℝ) • linear.symm (point - center)‖ =
          (1 / 70 : ℝ) * ‖linear.symm (point - center)‖ := by
            rw [norm_smul, Real.norm_eq_abs]
            norm_num
      _ ≤ (1 / 70 : ℝ) * 69 := by gcongr
      _ ≤ 1 := by norm_num
  have hsource : sourcePoint ∈ JohnEllipsoid.ellipsoid center linear :=
    (JohnEllipsoid.ellipsoid_mem_iff center linear sourcePoint).mpr
      hsourceJohn
  refine ⟨sourcePoint, hsource, ?_⟩
  simp only [AffineMap.homothety_apply]
  simp [sourcePoint]

end Kakeya.Assouad

end
