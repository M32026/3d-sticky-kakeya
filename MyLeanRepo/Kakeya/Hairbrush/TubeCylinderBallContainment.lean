import MyLeanRepo.Kakeya.Hairbrush.Basic
import MyLeanRepo.Kakeya.Hairbrush.CylinderTubeIntersection
import MyLeanRepo.Kakeya.Hairbrush.PlaneCovering.Basic
import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Ball containment for tube-infinite-cylinder intersection

Geometric lemma: the portion of a δ-tube U lying inside the infinite cylinder
of radius r around T's axis is contained in one ball of radius
`2δ + π*(r+3δ)/(2σ)`, when the angle between T and U is in `[σ, 2σ]`.
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Assouad

/--
The portion of U.carrier inside the r-cylinder around T's axis is contained
in a closed ball of radius `2*δ + π*(r+3*δ)/(2*σ)`, centered at a point
within δ of U's unit segment.
-/
lemma tube_cylinder_contained_in_closedBall
    {δ : ℝ} (hδ : 0 < δ)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (T U : Kakeya.DeltaTube δ)
    (h_angle1 : σ ≤ hairbrushAcuteAngle T U)
    (h_angle2 : hairbrushAcuteAngle T U ≤ 2 * σ)
    (h_inter : (T.carrier ∩ U.carrier).Nonempty)
    (r : ℝ) (hr : 0 ≤ r) :
    ∃ (x0 : Point3),
      Metric.infDist x0 (Kakeya.unitSegment U.base U.direction) ≤ δ ∧
      (U.carrier ∩ {y | ‖perpProj T.direction (y - T.base)‖ ≤ r}) ⊆
        Metric.closedBall x0 (2 * δ + Real.pi * (r + 3 * δ) / (2 * σ)) := by
  let θ : ℝ := hairbrushAcuteAngle T U
  let θ_full : ℝ := angleBetween T U
  let s : ℝ := Real.sin θ_full
  let c : ℝ := Real.cos θ_full
  let v : Point3 := U.direction
  let w : Point3 := T.direction

  have hθ1 : σ ≤ θ := h_angle1
  have hθ2 : θ ≤ 2 * σ := h_angle2
  have hθ_pos : 0 < θ := by linarith

  have h_inner_bound1 : -1 ≤ inner ℝ w v := by
    have h : |inner ℝ w v| ≤ ‖w‖ * ‖v‖ := abs_real_inner_le_norm _ _
    rw [T.direction_unit, U.direction_unit] at h
    have h' : |inner ℝ w v| ≤ 1 := by simpa using h
    exact (abs_le.mp h').1
  have h_inner_bound2 : inner ℝ w v ≤ 1 := by
    have h : |inner ℝ w v| ≤ ‖w‖ * ‖v‖ := abs_real_inner_le_norm _ _
    rw [T.direction_unit, U.direction_unit] at h
    have h' : |inner ℝ w v| ≤ 1 := by simpa using h
    exact (abs_le.mp h').2

  have h_c_eq : c = inner ℝ w v := by
    dsimp only [c, θ_full, angleBetween]
    exact Real.cos_arccos h_inner_bound1 h_inner_bound2

  have h_sin_eq : s = Real.sin θ := by
    have h1 : θ = min θ_full (Real.pi - θ_full) := by rfl
    by_cases h : θ_full ≤ Real.pi / 2
    · have h2 : θ = θ_full := by
        rw [h1]
        have h3 : θ_full ≤ Real.pi - θ_full := by linarith [Real.pi_pos]
        rw [min_eq_left h3]
      rw [h2]
    · have h2 : θ_full > Real.pi / 2 := by linarith
      have h3 : θ = Real.pi - θ_full := by
        rw [h1]
        have h4 : Real.pi - θ_full ≤ θ_full := by linarith [Real.pi_pos]
        rw [min_eq_right h4]
      rw [h3]
      rw [Real.sin_pi_sub]

  have hθ_eq_min : θ = min θ_full (Real.pi - θ_full) := by
    rfl
  have hθ_le_pi2 : θ ≤ Real.pi / 2 := by
    rw [hθ_eq_min]
    by_cases h : θ_full ≤ Real.pi / 2
    · have h2 : min θ_full (Real.pi - θ_full) ≤ θ_full := min_le_left _ _
      linarith
    · have h2 : θ_full > Real.pi / 2 := by linarith
      have h3 : min θ_full (Real.pi - θ_full) ≤ Real.pi - θ_full := min_le_right _ _
      linarith [Real.pi_pos]
  have hs_pos : 0 < s := by
    rw [h_sin_eq]
    exact Real.sin_pos_of_pos_of_lt_pi hθ_pos (by linarith [Real.pi_pos])

  have hs_lower : s ≥ 2 * σ / Real.pi := by
    rw [h_sin_eq]
    exact sin_angle_lower_bound hσ hσ1 hθ1 hθ2

  let w' : Point3 := (1 / s) • (v - c • w)

  have h_w'_perp_w : inner ℝ w w' = 0 := by
    have h1 : inner ℝ w w' = (1 / s) * (inner ℝ w v - c * inner ℝ w w) := by
      simp [w', inner_sub_right, inner_smul_right] <;> ring
    rw [h1]
    have h2 : inner ℝ w w = ‖w‖ ^ 2 := real_inner_self_eq_norm_sq w
    rw [h2, T.direction_unit, h_c_eq] <;> ring

  have h_w'_inner_v : inner ℝ v w' = s := by
    have h1 : inner ℝ v w' = (1 / s) * (inner ℝ v v - c * inner ℝ v w) := by
      simp [w', inner_sub_right, inner_smul_right] <;> ring
    rw [h1]
    have h2 : inner ℝ v v = 1 := by
      have h21 : inner ℝ v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
      rw [h21, U.direction_unit] <;> norm_num
    have h3 : inner ℝ v w = c := by
      have h31 : inner ℝ v w = inner ℝ w v := (real_inner_comm v w).symm
      rw [h31, ←h_c_eq]
    rw [h2, h3]
    have h4 : 1 - c * c = s ^ 2 := by
      have h5 : Real.sin θ_full ^ 2 + Real.cos θ_full ^ 2 = 1 := Real.sin_sq_add_cos_sq θ_full
      have h6 : s ^ 2 + c ^ 2 = 1 := by simpa [s, c] using h5
      linarith
    rw [show (1 / s) * (1 - c * c) = (1 / s) * s ^ 2 by rw [h4]]
    field_simp [hs_pos.ne'] <;> ring

  have h_w'_norm : ‖w'‖ = 1 := by
    have h_pos : 0 < 1 / s := by positivity
    have h1 : ‖w'‖ = (1 / s) * ‖v - c • w‖ := by
      rw [show w' = (1 / s) • (v - c • w) from rfl, norm_smul]
      have h_abs : ‖(1 / s : ℝ)‖ = 1 / s := by
        rw [Real.norm_eq_abs, abs_of_pos h_pos]
      rw [h_abs]
    rw [h1]
    have h_vv : inner ℝ v v = 1 := by
      have h : inner ℝ v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
      rw [h, U.direction_unit] <;> norm_num
    have h_ww : inner ℝ w w = 1 := by
      have h : inner ℝ w w = ‖w‖ ^ 2 := real_inner_self_eq_norm_sq w
      rw [h, T.direction_unit] <;> norm_num
    have h_vw : inner ℝ v w = c := by
      have h : inner ℝ v w = inner ℝ w v := (real_inner_comm v w).symm
      rw [h, ←h_c_eq]
    have h_wv : inner ℝ w v = c := by rw [←h_c_eq]
    have h2 : ‖v - c • w‖ ^ 2 = s ^ 2 := by
      have h3 : ‖v - c • w‖ ^ 2 = inner ℝ (v - c • w) (v - c • w) :=
        (real_inner_self_eq_norm_sq (v - c • w)).symm
      rw [h3]
      have h4 : inner ℝ (v - c • w) (v - c • w) =
          inner ℝ v v - c * inner ℝ v w - c * inner ℝ w v + c ^ 2 * inner ℝ w w := by
        have h5 : inner ℝ (v - c • w) (v - c • w) =
            inner ℝ v (v - c • w) - inner ℝ (c • w) (v - c • w) := by
          rw [inner_sub_left]
        rw [h5]
        have h6 : inner ℝ v (v - c • w) = inner ℝ v v - c * inner ℝ v w := by
          rw [inner_sub_right, inner_smul_right] <;> ring
        have h7 : inner ℝ (c • w) (v - c • w) = c * inner ℝ w v - c ^ 2 * inner ℝ w w := by
          have h71 : inner ℝ (c • w) (v - c • w) = (starRingEnd ℝ c) * inner ℝ w (v - c • w) := by
            rw [inner_smul_left]
          rw [h71]
          have h72 : starRingEnd ℝ c = c := by simp
          rw [h72]
          have h73 : inner ℝ w (v - c • w) = inner ℝ w v - c * inner ℝ w w := by
            rw [inner_sub_right, inner_smul_right] <;> simp
          rw [h73] <;> ring
        rw [h6, h7] <;> ring
      rw [h4, h_vv, h_vw, h_wv, h_ww]
      have h10 : s ^ 2 + c ^ 2 = 1 := by
        have h11 := Real.sin_sq_add_cos_sq θ_full
        simpa [s, c] using h11
      nlinarith
    have h2' : ‖v - c • w‖ = s := by
      have h_nonneg : 0 ≤ ‖v - c • w‖ := by positivity
      have h_s_nonneg : 0 ≤ s := by positivity
      nlinarith
    rw [h2']
    field_simp [hs_pos.ne'] <;> ring

  rcases h_inter with ⟨x0, hx0T, hx0U⟩

  have h_segU_comp : IsCompact (Kakeya.unitSegment U.base U.direction) :=
    isCompact_Icc.image (show Continuous (fun t : ℝ => U.base + t • U.direction) from by fun_prop)
  have h_segT_comp : IsCompact (Kakeya.unitSegment T.base T.direction) :=
    isCompact_Icc.image (show Continuous (fun t : ℝ => T.base + t • T.direction) from by fun_prop)

  have h_eqU : U.carrier = ⋃ a ∈ (Kakeya.unitSegment U.base U.direction), Metric.closedBall a δ := by
    have h_car : U.carrier = Metric.cthickening δ (Kakeya.unitSegment U.base U.direction) := by rfl
    rw [h_car]
    exact h_segU_comp.cthickening_eq_biUnion_closedBall hδ.le

  have h_eqT : T.carrier = ⋃ p ∈ (Kakeya.unitSegment T.base T.direction), Metric.closedBall p δ := by
    have h_car : T.carrier = Metric.cthickening δ (Kakeya.unitSegment T.base T.direction) := by rfl
    rw [h_car]
    exact h_segT_comp.cthickening_eq_biUnion_closedBall hδ.le

  have hx0U' : ∃ (a0 : Point3), a0 ∈ Kakeya.unitSegment U.base U.direction ∧ dist x0 a0 ≤ δ := by
    rw [h_eqU] at hx0U
    simpa [Set.mem_iUnion, Metric.mem_closedBall] using hx0U

  have hx0T' : ∃ (p0 : Point3), p0 ∈ Kakeya.unitSegment T.base T.direction ∧ dist x0 p0 ≤ δ := by
    rw [h_eqT] at hx0T
    simpa [Set.mem_iUnion, Metric.mem_closedBall] using hx0T

  rcases hx0U' with ⟨a0, ha0_seg, hxa0⟩
  rcases hx0T' with ⟨p0, hp0_seg, hxp0⟩

  have h_a0p0 : dist a0 p0 ≤ 2 * δ := by
    calc dist a0 p0
      ≤ dist a0 x0 + dist x0 p0 := dist_triangle a0 x0 p0
    _ = dist x0 a0 + dist x0 p0 := by rw [dist_comm a0 x0]
    _ ≤ δ + δ := by gcongr
    _ = 2 * δ := by ring

  rcases ha0_seg with ⟨α0, hα0_Icc, rfl⟩
  rcases hp0_seg with ⟨t0, ht0_Icc, rfl⟩
  let a0_pt : Point3 := U.base + α0 • v
  let p0_pt : Point3 := T.base + t0 • w

  have h_a0pt_seg : a0_pt ∈ Kakeya.unitSegment U.base U.direction := by
    exact ⟨α0, hα0_Icc, rfl⟩

  have h_infDist : Metric.infDist x0 (Kakeya.unitSegment U.base U.direction) ≤ δ := by
    have h1 : Metric.infDist x0 (Kakeya.unitSegment U.base U.direction) ≤ dist x0 a0_pt :=
      Metric.infDist_le_dist_of_mem h_a0pt_seg
    exact le_trans h1 hxa0

  have h_main : ∀ (y : Point3), y ∈ U.carrier ∩ {y | ‖perpProj w (y - T.base)‖ ≤ r} →
      dist y x0 ≤ 2 * δ + Real.pi * (r + 3 * δ) / (2 * σ) := by
    intro y hy
    have hyU : y ∈ U.carrier := hy.1
    have hy_cyl : ‖perpProj w (y - T.base)‖ ≤ r := hy.2

    have h1 : ∃ (a : Point3), a ∈ Kakeya.unitSegment U.base U.direction ∧ dist y a ≤ δ := by
      rw [h_eqU] at hyU
      simpa [Set.mem_iUnion, Metric.mem_closedBall] using hyU
    rcases h1 with ⟨a, ha_seg, hya⟩
    rcases ha_seg with ⟨α, hα_Icc, rfl⟩
    let a_pt : Point3 := U.base + α • v

    let p : Point3 := T.base + inner ℝ (y - T.base) w • w
    have h_yp : y - p = perpProj w (y - T.base) := by
      simp [p, perpProj] <;> abel
    have h_dist_yp : dist y p = ‖perpProj w (y - T.base)‖ := by
      rw [dist_eq_norm, h_yp]
    have h_dist_yp_le : dist y p ≤ r := by
      rw [h_dist_yp]; exact hy_cyl

    have h_dist_ap : dist a_pt p ≤ r + δ := by
      calc dist a_pt p
        ≤ dist a_pt y + dist y p := dist_triangle a_pt y p
      _ = dist y a_pt + dist y p := by rw [dist_comm a_pt y]
      _ ≤ δ + r := by gcongr
      _ = r + δ := by ring

    have h_p0p_scalar : ∃ (k : ℝ), p0_pt - p = k • w := by
      use t0 - inner ℝ (y - T.base) w
      have h : p0_pt - p = (t0 - inner ℝ (y - T.base) w) • w := by
        dsimp only [p0_pt, p]
        rw [sub_smul]
        <;> abel
      exact h

    rcases h_p0p_scalar with ⟨k, hk⟩

    have h_inner_p0p : inner ℝ (p0_pt - p) w' = 0 := by
      rw [hk, inner_smul_left, h_w'_perp_w] <;> simp [starRingEnd] <;> ring

    have h_a0a_scalar : a_pt - a0_pt = (α - α0) • v := by
      dsimp only [a_pt, a0_pt]
      have h : (U.base + α • v) - (U.base + α0 • v) = (α - α0) • v := by
        rw [sub_smul] <;> abel
      exact h

    have h_eq1 : inner ℝ (a_pt - p) w' = (α - α0) * s + inner ℝ (a0_pt - p0_pt) w' := by
      have h : a_pt - p = (a_pt - a0_pt) + (a0_pt - p0_pt) + (p0_pt - p) := by abel
      rw [h]
      simp [inner_add_left, h_a0a_scalar, inner_smul_left, h_w'_inner_v, h_inner_p0p, starRingEnd] <;> ring

    have h_abs : |α - α0| * s ≤ dist a_pt p + dist a0_pt p0_pt := by
      have h5 : (α - α0) * s = inner ℝ (a_pt - p) w' - inner ℝ (a0_pt - p0_pt) w' := by
        linarith [h_eq1]
      have h5' : |α - α0| * s = |inner ℝ (a_pt - p) w' - inner ℝ (a0_pt - p0_pt) w'| := by
        have h_abs_mul : |α - α0| * s = |(α - α0) * s| := by
          have h1 : |(α - α0) * s| = |α - α0| * |s| := abs_mul (α - α0) s
          have h2 : |s| = s := abs_of_pos hs_pos
          rw [h2] at h1
          exact h1.symm
        rw [h_abs_mul, h5]
      rw [h5']
      have h6 : |inner ℝ (a_pt - p) w' - inner ℝ (a0_pt - p0_pt) w'| ≤
          |inner ℝ (a_pt - p) w'| + |inner ℝ (a0_pt - p0_pt) w'| := by
        set x := inner ℝ (a_pt - p) w'
        set y := inner ℝ (a0_pt - p0_pt) w'
        have h61 : |x - y| ≤ |x| + |y| := by
          calc |x - y|
            = |x + (-y)| := by ring_nf
          _ ≤ |x| + |(-y)| := abs_add_le x (-y)
          _ = |x| + |y| := by simp
        exact h61
      have h7 : |inner ℝ (a_pt - p) w'| ≤ dist a_pt p := by
        calc |inner ℝ (a_pt - p) w'|
          ≤ ‖a_pt - p‖ * ‖w'‖ := abs_real_inner_le_norm _ _
        _ = ‖a_pt - p‖ := by rw [h_w'_norm] <;> ring
        _ = dist a_pt p := by rw [dist_eq_norm]
      have h8 : |inner ℝ (a0_pt - p0_pt) w'| ≤ dist a0_pt p0_pt := by
        calc |inner ℝ (a0_pt - p0_pt) w'|
          ≤ ‖a0_pt - p0_pt‖ * ‖w'‖ := abs_real_inner_le_norm _ _
        _ = ‖a0_pt - p0_pt‖ := by rw [h_w'_norm] <;> ring
        _ = dist a0_pt p0_pt := by rw [dist_eq_norm]
      linarith

    have h9 : |α - α0| * s ≤ r + 3 * δ := by
      calc |α - α0| * s
        ≤ dist a_pt p + dist a0_pt p0_pt := h_abs
      _ ≤ (r + δ) + (2 * δ) := by gcongr
      _ = r + 3 * δ := by ring

    have h10 : |α - α0| ≤ (r + 3 * δ) / s := by
      have h11 : |α - α0| * s ≤ r + 3 * δ := h9
      have h12 : 0 < s := hs_pos
      calc |α - α0|
        = (|α - α0| * s) / s := by field_simp [h12.ne'] <;> ring
      _ ≤ (r + 3 * δ) / s := by gcongr

    have h13 : |α - α0| ≤ Real.pi * (r + 3 * δ) / (2 * σ) := by
      have h14 : 1 / s ≤ Real.pi / (2 * σ) := by
        have h17 : s ≥ 2 * σ / Real.pi := hs_lower
        have h18 : 0 < 2 * σ / Real.pi := by positivity
        calc 1 / s
          ≤ 1 / (2 * σ / Real.pi) := by gcongr
        _ = Real.pi / (2 * σ) := by
          field_simp [hσ.ne', Real.pi_ne_zero] <;> ring
      have h15 : 0 ≤ r + 3 * δ := by linarith
      have h16 : (r + 3 * δ) / s ≤ (r + 3 * δ) * (Real.pi / (2 * σ)) := by
        calc (r + 3 * δ) / s
          = (r + 3 * δ) * (1 / s) := by ring
        _ ≤ (r + 3 * δ) * (Real.pi / (2 * σ)) := by gcongr
      have h17 : (r + 3 * δ) * (Real.pi / (2 * σ)) = Real.pi * (r + 3 * δ) / (2 * σ) := by ring
      rw [h17] at h16
      exact le_trans h10 h16

    have h14 : dist a_pt a0_pt = |α - α0| := by
      have h : a_pt - a0_pt = (α - α0) • v := h_a0a_scalar
      rw [dist_eq_norm, h, norm_smul]
      have h5 : ‖v‖ = 1 := U.direction_unit
      rw [h5]
      simp <;> ring

    have h15 : dist y x0 ≤ 2 * δ + |α - α0| := by
      have h_tri1 : dist y x0 ≤ dist y a_pt + dist a_pt x0 := dist_triangle y a_pt x0
      have h_tri2 : dist a_pt x0 ≤ dist a_pt a0_pt + dist a0_pt x0 := dist_triangle a_pt a0_pt x0
      have h : dist y x0 ≤ dist y a_pt + dist a_pt a0_pt + dist a0_pt x0 := by linarith
      have h' : dist a0_pt x0 ≤ δ := by
        have h_comm : dist a0_pt x0 = dist x0 a0_pt := dist_comm a0_pt x0
        rw [h_comm]; exact hxa0
      rw [h14] at *
      linarith

    linarith [h13]

  refine' ⟨x0, h_infDist, _⟩
  intro y hy
  have h : dist y x0 ≤ 2 * δ + Real.pi * (r + 3 * δ) / (2 * σ) := h_main y hy
  exact h

end Kakeya.Assouad
