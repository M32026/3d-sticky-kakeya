import MyLeanRepo.Kakeya.Assouad.Statements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.Bounds
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SameHeightDiameter

/-!
WZ2 Section 7: after removing the common `c₀ z` drift, place each active
tube's positive-half-window twisted projection inside its assigned cinematic
graph neighborhood.
-/

namespace Kakeya.Assouad

theorem assigned_curve_projection_containment_from_vertical_chart :
    AssignedCurveProjectionContainmentFromVerticalChartStatement := by
  intro δ w hδ _hδ1 hw F hvert Z hZ f hf hf0
    c0 assign hassign i hi y hy
  rcases hy with ⟨x, hx, rfl⟩
  rcases hx with ⟨p, hp_in, rfl⟩
  let z : ℝ := p (2 : Fin 3)
  have hz_in : z ∈ Set.Icc (0 : ℝ) 1 := by
    have h1 : p ∈ Z.union := ⟨i, hp_in⟩
    have h2 : p ∈ horizontalSlab 0 1 := hZ h1
    simpa [horizontalSlab] using h2
  have h_p_in_tube : p ∈ (F.tube i).carrier :=
    Z.subset_body i hp_in
  set a := (tubeParams i).a with ha_def
  set b := (tubeParams i).b with hb_def
  set c := (tubeParams i).c with hc_def
  set d := (tubeParams i).d with hd_def
  have h_axis_dist :
      ‖p - point3 (a + c * z) (b + d * z) z‖ ≤ 3 * δ :=
    tubeCarrier_axisDistance hδ.le hvert i p h_p_in_tube z rfl
  have h_coord0 : |p 0 - (a + c * z)| ≤ 3 * δ := by
    have h :
        |(p - point3 (a + c * z) (b + d * z) z) 0| ≤
          ‖p - point3 (a + c * z) (b + d * z) z‖ :=
      euclidean_coord_le_norm _ _
    have h' :
        (p - point3 (a + c * z) (b + d * z) z) 0 =
          p 0 - (a + c * z) := by
      simp [point3]
    rw [h'] at h
    exact h.trans h_axis_dist
  have h_coord1 : |p 1 - (b + d * z)| ≤ 3 * δ := by
    have h :
        |(p - point3 (a + c * z) (b + d * z) z) 1| ≤
          ‖p - point3 (a + c * z) (b + d * z) z‖ :=
      euclidean_coord_le_norm _ _
    have h' :
        (p - point3 (a + c * z) (b + d * z) z) 1 =
          p 1 - (b + d * z) := by
      simp [point3]
    rw [h'] at h
    exact h.trans h_axis_dist
  have hz'_full : z ∈ Set.Icc (-1 : ℝ) 1 := by
    exact ⟨by linarith [hz_in.1], by linarith [hz_in.2]⟩
  have h_fz : |f z| ≤ 2 :=
    nonsingular_f_bound hf hf0 hz'_full
  have h_assign_c : |c - c0| ≤ w / 2 :=
    (hassign i hi).1
  have h_c2 :
      Kakeya.Cinematic.c2Distance
        (slopeCurve f a b d) (assign i) ≤ w :=
    (hassign i hi).2
  let hz' : Kakeya.Cinematic.UnitPoint := ⟨z, hz_in⟩
  have h_slope_value :
      (slopeCurve f a b d) hz' = cinematicEval f a b d z := by
    simp [slopeCurve_value, cinematicEval]
    ring
  have h_value_bound :
      |(slopeCurve f a b d) hz' - (assign i) hz'| ≤ w := by
    have h :
        |(slopeCurve f a b d) hz' - (assign i) hz'| ≤
          Kakeya.Cinematic.c2Distance
            (slopeCurve f a b d) (assign i) :=
      Kakeya.Cinematic.abs_value_sub_le_c2Distance
        (slopeCurve f a b d) (assign i) hz'
    exact h.trans h_c2
  have h_cinematic_bound :
      |cinematicEval f a b d z - (assign i) hz'| ≤ w := by
    rw [← h_slope_value]
    exact h_value_bound
  let horizontal := p 0 + f z * p 1 - c0 * z
  set e1 := p 0 - (a + c * z) with he1
  set e2 := p 1 - (b + d * z) with he2
  set e3 := cinematicEval f a b d z - (assign i) hz' with he3
  set e4 := (c - c0) * z with he4
  set e234 := f z * e2 + e3 + e4 with he234
  set e34 := e3 + e4 with he34
  have hb1 : |e1| ≤ 3 * δ := h_coord0
  have hb2 : |e2| ≤ 3 * δ := h_coord1
  have hb3 : |e3| ≤ w := h_cinematic_bound
  have hb4 : |e4| ≤ w / 2 := by
    have h : |e4| = |c - c0| * |z| := by
      simp [e4, abs_mul]
    rw [h]
    have h5 : |z| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hz_in.1, hz_in.2]
    calc
      |c - c0| * |z| ≤ (w / 2) * |z| := by gcongr
      _ ≤ (w / 2) * 1 := by gcongr
      _ = w / 2 := by ring
  have h_abs1 : |e1 + e234| ≤ |e1| + |e234| :=
    abs_add_le e1 e234
  have h_abs2 : |e234| ≤ |f z * e2| + |e34| := by
    have h_eq : e234 = f z * e2 + e34 := by
      simp [e234, e34]
      ring
    rw [h_eq]
    exact abs_add_le (f z * e2) e34
  have h_abs3 : |e34| ≤ |e3| + |e4| :=
    abs_add_le e3 e4
  have h_mul : |f z * e2| = |f z| * |e2| :=
    abs_mul (f z) e2
  have h_eq : horizontal - (assign i) hz' = e1 + e234 := by
    simp [horizontal, e1, e2, e3, e4, e234, cinematicEval]
    ring
  have h_main :
      |horizontal - (assign i) hz'| < 20 * (δ + w) := by
    rw [h_eq]
    have h_abs :
        |e1 + e234| ≤ |e1| + |f z| * |e2| + |e3| + |e4| := by
      calc
        |e1 + e234| ≤ |e1| + |e234| := h_abs1
        _ ≤ |e1| + (|f z * e2| + |e34|) := by
          linarith [h_abs2]
        _ = |e1| + |f z| * |e2| + |e34| := by
          rw [h_mul]
          ring
        _ ≤ |e1| + |f z| * |e2| + (|e3| + |e4|) := by
          linarith [h_abs3]
        _ = |e1| + |f z| * |e2| + |e3| + |e4| := by
          ring
    have h_total :
        |e1| + |f z| * |e2| + |e3| + |e4| ≤
          9 * δ + 3 * w / 2 := by
      calc
        |e1| + |f z| * |e2| + |e3| + |e4|
            ≤ 3 * δ + 2 * (3 * δ) + w + w / 2 := by
              gcongr
        _ = 9 * δ + 3 * w / 2 := by ring
    have h_strict :
        9 * δ + 3 * w / 2 < 20 * (δ + w) := by
      linarith
    exact lt_of_le_of_lt h_abs (lt_of_le_of_lt h_total h_strict)
  let g := assign i
  let r := 20 * (δ + w)
  let graph_point : ℝ × ℝ := (z, g hz')
  have h_graph_point_in :
      graph_point ∈ Kakeya.Cinematic.functionGraph g := by
    refine ⟨hz_in, rfl⟩
  have h_tp1 :
      (twistedProjection f p) (1 : Fin 2) = z := by
    have h :
        (twistedProjection f p) (1 : Fin 2) =
          p (2 : Fin 3) := by
      simp [twistedProjection]
    rw [h]
  have h_tp0 :
      (twistedProjection f p) (0 : Fin 2) =
        p 0 + f (p 2) * p 1 := by
    simp [twistedProjection]
  have h_shear_eq :
      cinematicShear c0 (twistedProjection f p) =
        (z, horizontal) := by
    have h :
        cinematicShear c0 (twistedProjection f p) =
          ((twistedProjection f p) (1 : Fin 2),
            (twistedProjection f p) (0 : Fin 2) -
              c0 * (twistedProjection f p) (1 : Fin 2)) := by
      rfl
    have h_fz_eq : f (p 2) = f z := by rfl
    rw [h, h_tp1, h_tp0, h_fz_eq]
  have h_dist :
      dist (cinematicShear c0 (twistedProjection f p))
        graph_point < r := by
    rw [h_shear_eq]
    have h :
        dist (z, horizontal) (z, g hz') =
          |horizontal - g hz'| := by
      simp [Prod.dist_eq, Real.dist_eq]
    rw [h]
    exact h_main
  exact Metric.mem_thickening_iff.mpr
    ⟨graph_point, h_graph_point_in, h_dist⟩

/-- Compatibility wrapper for the original basepoint-bounded API. -/
theorem assigned_curve_projection_containment :
    AssignedCurveProjectionContainmentStatement := by
  intro delta w hdelta hdelta_one hw F _hbase hvertical
  exact assigned_curve_projection_containment_from_vertical_chart
    hdelta hdelta_one hw F hvertical

end Kakeya.Assouad
