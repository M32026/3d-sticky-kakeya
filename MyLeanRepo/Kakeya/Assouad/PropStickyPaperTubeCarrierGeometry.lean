import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometryStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometryHelpers

/-!
# Finite-capsule geometry for one cropped paper tube
-/

noncomputable section

namespace Kakeya.Assouad

open Metric

lemma paper_axis_dist
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) (t1 t2 : ℝ) :
    dist
        (wz1TubeAxisZeroPoint tube +
          t1 • wz1PaperDirection tube)
        (wz1TubeAxisZeroPoint tube +
          t2 • wz1PaperDirection tube) =
      |t1 - t2| := by
  have hnorm : ‖wz1PaperDirection tube‖ = 1 :=
    wz1PaperDirection_norm tube
  have h :
      dist
          (wz1TubeAxisZeroPoint tube +
            t1 • wz1PaperDirection tube)
          (wz1TubeAxisZeroPoint tube +
            t2 • wz1PaperDirection tube) =
        ‖(t1 - t2) • wz1PaperDirection tube‖ := by
    simp [dist_eq_norm, sub_smul]
  rw [h, norm_smul, hnorm, mul_one]
  simp [Real.norm_eq_abs]

theorem wz2_paper_tube_carrier_geometry :
    WZ2PaperTubeCarrierGeometryStatement :=
  fun {delta} hdelta_pos tube hline => by
    have hd2 :
        (1 / 2 : ℝ) ≤
          wz1PaperDirection tube (2 : Fin 3) :=
      hline.1
    have hz2 :
        wz1TubeAxisZeroPoint tube (2 : Fin 3) = 0 :=
      wz1TubeAxisZeroPoint_coord_two tube
        (WZ1PaperTubeInLineClass.vertical hline)
    have hline_closed : IsClosed (tubeAxisLine tube) :=
      isClosed_tubeAxisLine tube
    have hline_eq :
        tubeAxisLine tube =
          {p | ∃ t : ℝ,
            p = wz1TubeAxisZeroPoint tube +
              t • wz1PaperDirection tube} :=
      tubeAxisLine_eq_affineSpan tube hline.vertical
    have hcore_eq :
        wz2PaperAxisCoreSegment tube =
          {p | ∃ t : ℝ, t ∈ Set.Icc (-2) 2 ∧
            p = wz1TubeAxisZeroPoint tube +
              t • wz1PaperDirection tube} :=
      wz2PaperAxisCoreSegment_eq tube
    have hpos6 : 0 ≤ 6 * delta := by positivity
    constructor
    · exact convex_wz1PaperTubeCarrier tube
    · intro p hp
      have hthick :
          p ∈ Metric.cthickening
            (6 * delta) (tubeAxisLine tube) :=
        hp.1
      have hbox :
          p ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
        hp.2
      have hp2 : |p (2 : Fin 3)| ≤ 1 := by
        simpa [Kakeya.Streamlined.axisBox] using
          hbox.2.2
      rcases
          exists_dist_le_of_mem_cthickening_closed
            hline_closed hpos6 hthick with
        ⟨q, hq_line, hq_dist⟩
      have hq_set :
          q ∈ {p | ∃ t : ℝ,
            p = wz1TubeAxisZeroPoint tube +
              t • wz1PaperDirection tube} := by
        rw [← hline_eq]
        exact hq_line
      rcases hq_set with ⟨tq, hq_eq⟩
      let d := wz1PaperDirection tube
      let z := wz1TubeAxisZeroPoint tube
      let tr := (p (2 : Fin 3)) / (d (2 : Fin 3))
      let r := z + tr • d
      have hd2_pos : 0 < d (2 : Fin 3) := by
        linarith
      have hr2 : r (2 : Fin 3) = p (2 : Fin 3) := by
        simp [r, tr, z, hz2, hd2_pos.ne']
      have htr_abs : |tr| ≤ 2 := by
        have h1 :
            |tr| =
              |p (2 : Fin 3)| / d (2 : Fin 3) := by
          rw [abs_div, abs_of_pos hd2_pos]
        rw [h1]
        have h2 :
            |p (2 : Fin 3)| / d (2 : Fin 3) ≤
              1 / (1 / 2 : ℝ) := by
          gcongr <;> linarith
        linarith
      have htr_bounds : tr ∈ Set.Icc (-2 : ℝ) 2 :=
        ⟨by linarith [abs_le.mp htr_abs],
          by linarith [abs_le.mp htr_abs]⟩
      have hr_core :
          r ∈ wz2PaperAxisCoreSegment tube := by
        rw [hcore_eq]
        exact ⟨tr, htr_bounds, rfl⟩
      have hqr_dist : dist q r = |tq - tr| := by
        rw [hq_eq]
        exact paper_axis_dist tube tq tr
      have hcoord_diff :
          |q (2 : Fin 3) - r (2 : Fin 3)| =
            |tq - tr| * d (2 : Fin 3) := by
        rw [hq_eq]
        have h1 :
            (z + tq • d) (2 : Fin 3) -
                r (2 : Fin 3) =
              (tq - tr) * d (2 : Fin 3) := by
          simp [r, z, hz2, smul_eq_mul]
          ring
        rw [h1, abs_mul, abs_of_pos hd2_pos]
      have hqr_dist2 :
          dist q r =
            |q (2 : Fin 3) - r (2 : Fin 3)| /
              d (2 : Fin 3) := by
        rw [hqr_dist, hcoord_diff]
        field_simp [hd2_pos.ne']
      have hcoord_eq :
          |q (2 : Fin 3) - r (2 : Fin 3)| =
            |q (2 : Fin 3) - p (2 : Fin 3)| := by
        rw [hr2]
      rw [hcoord_eq] at hqr_dist2
      have hcoord_bound :
          |q (2 : Fin 3) - p (2 : Fin 3)| ≤
            dist p q := by
        have h :
            |q (2 : Fin 3) - p (2 : Fin 3)| ≤
              dist q p :=
          abs_coord_sub_le_dist (2 : Fin 3)
        rw [dist_comm q p] at h
        exact h
      have hqr_bound : dist q r ≤ 12 * delta := by
        rw [hqr_dist2]
        have h3 :
            |q (2 : Fin 3) - p (2 : Fin 3)| /
                d (2 : Fin 3) ≤
              dist p q / d (2 : Fin 3) := by
          gcongr <;> linarith
        have h4 :
            dist p q / d (2 : Fin 3) ≤
              (6 * delta) / (1 / 2 : ℝ) := by
          gcongr <;> linarith
        linarith
      have hpr_bound : dist p r ≤ 24 * delta := by
        have h5 : dist p r ≤ dist p q + dist q r :=
          dist_triangle p q r
        linarith
      exact
        Metric.mem_cthickening_of_dist_le
          p r (24 * delta)
          (wz2PaperAxisCoreSegment tube)
          hr_core hpr_bound

end Kakeya.Assouad

end
