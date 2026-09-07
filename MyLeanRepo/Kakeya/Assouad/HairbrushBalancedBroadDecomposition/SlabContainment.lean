import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import MyLeanRepo.Kakeya.AssertionD
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Slab containment for angled tubes

A tube whose direction lies within an acute angle `θ` of `v`, and whose base
projection onto a normal `n ⊥ v` lies within `θ/2` of an offset, is contained
in the slab of radius `3θ` with normal `n` and that offset.

This is the geometric core of spatio-directional fiber construction: each
direction-cap fiber is further subdivided by the transverse coordinate of
tube bases, and each resulting sub-family lives in one angled slab.
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Assouad

/-- Distance from a point to the affine hyperplane `{y | inner(y,n) = offset}`. -/
lemma dist_to_hyperplane {n : Point3} (hn : ‖n‖ = 1) {offset : ℝ} {x : Point3} :
    Metric.infDist x {y : Point3 | inner ℝ y n = offset} =
      |inner ℝ x n - offset| := by
  let H : Set Point3 := {y | inner ℝ y n = offset}
  let a : ℝ := inner ℝ x n - offset
  let z : Point3 := x - a • n
  have hinner_n : inner ℝ n n = (1 : ℝ) := by
    have h : inner ℝ n n = ‖n‖ ^ 2 := real_inner_self_eq_norm_sq n
    rw [h, hn] <;> norm_num
  have hz1 : inner ℝ z n = offset := by
    have h1 : inner ℝ z n = inner ℝ x n - inner ℝ (a • n) n := by
      rw [show z = x - a • n from rfl, inner_sub_left]
    have h2 : inner ℝ (a • n) n = a * inner ℝ n n := by
      rw [inner_smul_left] <;> simp
    rw [h1, h2, hinner_n] <;> ring
  have hz_in_H : z ∈ H := hz1
  have h_H_nonempty : H.Nonempty := ⟨z, hz_in_H⟩
  have hdist : dist x z = |a| := by
    have h1 : x - z = a • n := by simp [z] <;> abel
    rw [dist_eq_norm, h1, norm_smul, hn]
    <;> rw [Real.norm_eq_abs] <;> ring
  have h_le1 : Metric.infDist x H ≤ dist x z := Metric.infDist_le_dist_of_mem hz_in_H
  have h_le2 : ∀ (y : Point3), y ∈ H → |a| ≤ dist x y := by
    intro y hy
    have h2 : inner ℝ y n = offset := hy
    have h3 : inner ℝ (x - y) n = inner ℝ x n - inner ℝ y n := by rw [inner_sub_left]
    have h4 : |a| = |inner ℝ (x - y) n| := by
      rw [h3, h2] <;> ring
    rw [h4]
    have h5 : |inner ℝ (x - y) n| ≤ ‖x - y‖ * ‖n‖ := abs_real_inner_le_norm (x - y) n
    rw [hn] at h5
    simpa [dist_eq_norm] using h5
  have h_glb : IsGLB ((dist x ·) '' H) (Metric.infDist x H) :=
    isGLB_infDist h_H_nonempty
  have h_lower : ∀ (d : ℝ), d ∈ (dist x ·) '' H → |a| ≤ d := by
    intro d hd
    rcases hd with ⟨y, hy, rfl⟩
    exact h_le2 y hy
  have h6 : |a| ≤ Metric.infDist x H := h_glb.2 h_lower
  have h7 : Metric.infDist x H ≤ |a| := by
    rw [hdist] at h_le1
    exact h_le1
  exact le_antisymm h7 h6

/-- If `hairbrushAcuteDirectionAngle w v ≤ θ` with `θ ≤ 1` and `n ⊥ v`,
then `|inner(w,n)| ≤ θ`. -/
lemma acute_angle_implies_perp_inner_bound {w v n : Point3}
    (hw : ‖w‖ = 1) (hv : ‖v‖ = 1) (hn : ‖n‖ = 1)
    (hn_orth : inner ℝ v n = 0) {θ : ℝ} (hθ1 : θ ≤ 1)
    (h_angle : hairbrushAcuteDirectionAngle w v ≤ θ) :
    |inner ℝ w n| ≤ θ := by
  let c : ℝ := inner ℝ w v
  have hc1 : -1 ≤ c := by
    have h' : |inner ℝ w v| ≤ ‖w‖ * ‖v‖ := abs_real_inner_le_norm w v
    rw [hw, hv] at h'
    have h'' : -1 ≤ c := by linarith [abs_le.mp h']
    exact h''
  have hc2 : c ≤ 1 := by
    have h' : |inner ℝ w v| ≤ ‖w‖ * ‖v‖ := abs_real_inner_le_norm w v
    rw [hw, hv] at h'
    have h'' : c ≤ 1 := by linarith [abs_le.mp h']
    exact h''
  let α : ℝ := Real.arccos c
  have hα_nonneg : 0 ≤ α := Real.arccos_nonneg c
  have hα_le_pi : α ≤ Real.pi := Real.arccos_le_pi c
  have h_cos : Real.cos α = c := Real.cos_arccos hc1 hc2
  have h_min : min α (Real.pi - α) ≤ θ := h_angle
  by_cases h_case : α ≤ θ
  · -- Case 1: α ≤ θ, use w - v
    have h_norm_diff : ‖w - v‖ ≤ θ := by
      have h1 : ‖w - v‖ ^ 2 = 2 - 2 * Real.cos α := by
        have h2 : ‖w - v‖ ^ 2 = ‖w‖ ^ 2 - 2 * inner ℝ w v + ‖v‖ ^ 2 :=
          norm_sub_sq_real w v
        rw [h2, hw, hv, h_cos] <;> ring
      have h3 : ‖w - v‖ ^ 2 ≤ θ ^ 2 := by
        rw [h1]
        have h4 : 2 - 2 * Real.cos α ≤ α ^ 2 := by
          have h5 : Real.cos α ≥ 1 - α ^ 2 / 2 := Real.one_sub_sq_div_two_le_cos
          linarith
        have h6 : α ≤ θ := h_case
        nlinarith
      have h7 : 0 ≤ ‖w - v‖ := by positivity
      nlinarith
    have h8 : inner ℝ w n = inner ℝ (w - v) n := by
      rw [inner_sub_left, hn_orth] <;> ring
    rw [h8]
    have h9 : |inner ℝ (w - v) n| ≤ ‖w - v‖ * ‖n‖ := abs_real_inner_le_norm (w - v) n
    rw [hn] at h9
    linarith
  · -- Case 2: α > θ
    have hα_gt : α > θ := by linarith
    -- Since min α (π-α) ≤ θ and α > θ, we must have π-α ≤ α and π-α ≤ θ
    have hπminα_leα : Real.pi - α ≤ α := by
      by_contra h
      have h' : α < Real.pi - α := by linarith
      have h_min_eq : min α (Real.pi - α) = α := by
        rw [min_eq_left] <;> linarith
      rw [h_min_eq] at h_min
      linarith
    have h_case2 : Real.pi - α ≤ θ := by
      have h_min_eq : min α (Real.pi - α) = Real.pi - α := by
        rw [min_eq_right] <;> linarith
      rw [h_min_eq] at h_min
      exact h_min
    let β := Real.pi - α
    have hβ_nonneg : 0 ≤ β := by linarith [Real.pi_pos, hα_le_pi]
    have hβ_leθ : β ≤ θ := h_case2
    have h4 : Real.cos α = -Real.cos β := by
      have h5 : α = Real.pi - β := by linarith
      rw [h5, Real.cos_pi_sub]
    have h1 : ‖w + v‖ ^ 2 = 2 + 2 * Real.cos α := by
      have h2 : ‖w + v‖ ^ 2 = ‖w‖ ^ 2 + 2 * inner ℝ w v + ‖v‖ ^ 2 := by
        simp [norm_add_sq_real] <;> ring
      rw [h2, hw, hv, h_cos] <;> ring
    have h_norm_sum_sq : ‖w + v‖ ^ 2 ≤ θ ^ 2 := by
      rw [h1, h4]
      have h5 : 2 - 2 * Real.cos β ≤ β ^ 2 := by
        have h6 : Real.cos β ≥ 1 - β ^ 2 / 2 := Real.one_sub_sq_div_two_le_cos
        linarith
      have h7 : β ^ 2 ≤ θ ^ 2 := by gcongr
      nlinarith
    have h8 : 0 ≤ ‖w + v‖ := by positivity
    have h_norm_sum : ‖w + v‖ ≤ θ := by nlinarith
    have h11 : inner ℝ w n = inner ℝ (w + v) n := by
      have h12 : inner ℝ (w + v) n = inner ℝ w n + inner ℝ v n := by
        rw [inner_add_left]
      rw [h12, hn_orth] <;> ring
    rw [h11]
    have h13 : |inner ℝ (w + v) n| ≤ ‖w + v‖ * ‖n‖ := abs_real_inner_le_norm (w + v) n
    rw [hn] at h13
    linarith

/-- A tube is contained in an angled slab of radius `3θ`.

Given direction within `θ` of `v`, base projection within `θ/2` of `offset`
along a normal `n ⊥ v`, and `δ ≤ θ`, every point of the tube is within `3θ`
of the hyperplane `{x | inner(x,n) = offset}`. -/
lemma tube_contained_in_angled_slab {δ θ : ℝ} (hδ : 0 < δ) (hθ : δ ≤ θ) (hθ1 : θ ≤ 1)
    (T : Kakeya.DeltaTube δ) (hT_unit : T.IsInUnitBall)
    (v n : Point3) (hv : ‖v‖ = 1) (hn : ‖n‖ = 1) (hn_orth : inner ℝ v n = 0)
    (h_angle : hairbrushAcuteDirectionAngle T.direction v ≤ θ)
    (offset : ℝ) (h_base_in : |inner ℝ T.base n - offset| ≤ θ / 2) :
    T.carrier ⊆ (Kakeya.Slab.mk n offset (3 * θ) hn (by linarith)).carrier := by
  let S : Kakeya.Slab :=
    { normal := n
      offset := offset
      radius := 3 * θ
      normal_unit := hn
      radius_nonneg := by linarith }
  have h_radius_nonneg : 0 ≤ 3 * θ := by linarith
  have hinner_n : inner ℝ n n = (1 : ℝ) := by
    have h : inner ℝ n n = ‖n‖ ^ 2 := real_inner_self_eq_norm_sq n
    rw [h, hn] <;> norm_num
  have h_H_nonempty : S.hyperplane.Nonempty := by
    have h_off : inner ℝ (offset • n) n = offset := by
      have h1 : inner ℝ (offset • n) n = offset * inner ℝ n n := by
        simp [inner_smul_left]
      rw [h1, hinner_n] <;> ring
    refine ⟨offset • n, ?_⟩
    have h_goal : inner ℝ (offset • n) n = S.offset := by
      exact h_off
    simpa [S, Kakeya.Slab.hyperplane] using h_goal
  intro x hx
  have h_ball : x ∈ Kakeya.DeltaTube.unitBall := hT_unit hx
  -- Find nearest point y on the unit segment
  have h_seg_nonempty : (Kakeya.unitSegment T.base T.direction).Nonempty := by
    refine ⟨T.base, 0, by norm_num, ?_⟩
    simp
  have h_compact : IsCompact (Kakeya.unitSegment T.base T.direction) := by
    let f : ℝ → Point3 := fun t => T.base + t • T.direction
    have h_cont : Continuous f := by fun_prop
    have h : IsCompact (f '' Set.Icc (0 : ℝ) 1) := isCompact_Icc.image h_cont
    have h_eq : f '' Set.Icc (0 : ℝ) 1 = Kakeya.unitSegment T.base T.direction := by rfl
    rw [h_eq] at h; exact h
  rcases h_compact.exists_infEDist_eq_edist h_seg_nonempty x with ⟨y, hy, h_eq⟩
  have h_inf : infEDist x (Kakeya.unitSegment T.base T.direction) ≤ ENNReal.ofReal δ := hx
  rw [h_eq] at h_inf
  have h2 : edist x y = ENNReal.ofReal (dist x y) := by simp [edist_dist]
  rw [h2] at h_inf
  have hdist : dist x y ≤ δ := (ENNReal.ofReal_le_ofReal_iff hδ.le).mp h_inf
  rcases hy with ⟨t, ht, rfl⟩
  have h_t0 : 0 ≤ t := ht.1
  have h_t1 : t ≤ 1 := ht.2
  -- Bound direction inner product with normal
  have h_dir_bound : |inner ℝ T.direction n| ≤ θ :=
    acute_angle_implies_perp_inner_bound T.direction_unit hv hn hn_orth hθ1 h_angle
  -- Bound segment projection variation
  have h_seg_proj : |inner ℝ (T.base + t • T.direction) n - inner ℝ T.base n| ≤ θ := by
    have h11 : inner ℝ (T.base + t • T.direction) n =
        inner ℝ T.base n + inner ℝ (t • T.direction) n := by
      rw [inner_add_left]
    have h12 : inner ℝ (t • T.direction) n = t * inner ℝ T.direction n := by
      simp [inner_smul_left]
    have h1 : inner ℝ (T.base + t • T.direction) n - inner ℝ T.base n =
        t * inner ℝ T.direction n := by
      rw [h11, h12] <;> ring
    rw [h1]
    have h2 : |t * inner ℝ T.direction n| = |t| * |inner ℝ T.direction n| := by
      rw [abs_mul]
    rw [h2]
    have h3 : |t| ≤ 1 := by
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    calc
      |t| * |inner ℝ T.direction n| ≤ 1 * θ := by gcongr <;> linarith
      _ = θ := by ring
  -- Bound x projection relative to base
  have h_x_proj : |inner ℝ x n - inner ℝ T.base n| ≤ δ + θ := by
    let y_pt := T.base + t • T.direction
    have h4 : inner ℝ x n - inner ℝ T.base n =
        inner ℝ (x - y_pt) n +
        (inner ℝ y_pt n - inner ℝ T.base n) := by
      rw [inner_sub_left] <;> abel
    rw [h4]
    have h5 : |inner ℝ (x - y_pt) n| ≤ ‖x - y_pt‖ * ‖n‖ :=
      abs_real_inner_le_norm (x - y_pt) n
    rw [hn] at h5
    have h6 : ‖x - y_pt‖ = dist x y_pt := by simp [dist_eq_norm]
    rw [h6] at h5
    calc
      |inner ℝ (x - y_pt) n + (inner ℝ y_pt n - inner ℝ T.base n)|
        ≤ |inner ℝ (x - y_pt) n| + |inner ℝ y_pt n - inner ℝ T.base n| :=
          by simpa [Real.norm_eq_abs] using norm_add_le (inner ℝ (x - y_pt) n) (inner ℝ y_pt n - inner ℝ T.base n)
      _ ≤ dist x y_pt + θ := by gcongr <;> linarith
      _ ≤ δ + θ := by linarith
  -- Final bound
  have h_final : |inner ℝ x n - offset| ≤ 3 * θ := by
    calc
      |inner ℝ x n - offset|
        = |(inner ℝ x n - inner ℝ T.base n) + (inner ℝ T.base n - offset)| := by ring_nf
      _ ≤ |inner ℝ x n - inner ℝ T.base n| + |inner ℝ T.base n - offset| :=
          by simpa [Real.norm_eq_abs] using
            norm_add_le (inner ℝ x n - inner ℝ T.base n)
              (inner ℝ T.base n - offset)
      _ ≤ (δ + θ) + (θ / 2) := by gcongr
      _ ≤ 3 * θ := by linarith
  have h_hyperplane : S.hyperplane = {y : Point3 | inner ℝ y n = offset} := by
    ext z
    simp [S, Kakeya.Slab.hyperplane] <;> rfl
  have h_dist_eq : Metric.infDist x S.hyperplane = |inner ℝ x n - offset| := by
    rw [h_hyperplane]
    exact dist_to_hyperplane hn
  have h_cthick : x ∈ Metric.cthickening S.radius S.hyperplane := by
    have h7 : Metric.infDist x S.hyperplane ≤ S.radius := by
      rw [h_dist_eq] <;> exact h_final
    have h9 : ENNReal.ofReal (Metric.infDist x S.hyperplane) = Metric.infEDist x S.hyperplane := by
      rw [← ENNReal.ofReal_toReal (Metric.infEDist_ne_top h_H_nonempty)] <;> rfl
    have h8 : Metric.infEDist x S.hyperplane ≤ ENNReal.ofReal S.radius := by
      rw [← h9]
      exact ENNReal.ofReal_le_ofReal h7
    exact h8
  exact ⟨h_ball, h_cthick⟩

/-- A tube that intersects a set with bounded projection onto `w` is contained
in a slab perpendicular to `w`.

Given `z ∈ T.carrier ∩ Q`, where `Q`'s projection onto `w` lies within `L/2`
of a center `c`, and `T.direction` is within angle `θ` of `v` with `w ⊥ v`,
the entire tube lies in a slab of radius `L/2 + θ + 2δ` with normal `w`.

Proof: for any `x ∈ T.carrier`, write `x = base + t_x·dir + e_x` and
`z = base + t_z·dir + e_z` with `‖e_x‖, ‖e_z‖ ≤ δ` and `t_x, t_z ∈ [0,1]`.
Then `inner(x,w) - inner(z,w) = (t_x - t_z)·inner(dir,w) + inner(e_x - e_z,w)`,
where `|(t_x-t_z)·inner(dir,w)| ≤ θ` and `|inner(e_x-e_z,w)| ≤ 2δ`. -/
lemma tube_intersect_proj_bounded_set_implies_slab {δ θ L : ℝ}
    (hδ : 0 < δ) (hθ : δ ≤ θ) (hθ1 : θ ≤ 1) (hL : 0 ≤ L)
    (T : Kakeya.DeltaTube δ) (hT_unit : T.IsInUnitBall)
    (v w : Point3) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (h_perp : inner ℝ v w = 0)
    (h_angle : hairbrushAcuteDirectionAngle T.direction v ≤ θ)
    (Q : Set Point3)
    (hQ_proj : ∃ c : ℝ, ∀ x ∈ Q, |inner ℝ x w - c| ≤ L / 2)
    (h_intersect : T.carrier ∩ Q ≠ ∅) :
    ∃ (S : Kakeya.Slab), T.carrier ⊆ S.carrier ∧ S.radius ≤ L / 2 + θ + 2 * δ := by
  rcases hQ_proj with ⟨c, hc⟩
  have h_nonempty : (T.carrier ∩ Q).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr h_intersect
  rcases h_nonempty with ⟨z, hzT, hzQ⟩
  have hθ_pos : 0 < θ := by linarith

  -- Helper: nearest point on unit segment within δ
  have h_helper : ∀ (x : Point3), x ∈ T.carrier →
      ∃ (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧ dist x (T.base + t • T.direction) ≤ δ := by
    intro x hx
    have h_seg_nonempty : (Kakeya.unitSegment T.base T.direction).Nonempty := by
      refine ⟨T.base, 0, by norm_num, by simp⟩
    have h_compact : IsCompact (Kakeya.unitSegment T.base T.direction) := by
      let f : ℝ → Point3 := fun t => T.base + t • T.direction
      have h_cont : Continuous f := by fun_prop
      have h : IsCompact (f '' Set.Icc (0 : ℝ) 1) := isCompact_Icc.image h_cont
      have h_eq : f '' Set.Icc (0 : ℝ) 1 = Kakeya.unitSegment T.base T.direction := by rfl
      rw [h_eq] at h; exact h
    rcases h_compact.exists_infEDist_eq_edist h_seg_nonempty x with ⟨y, hy, h_eq⟩
    have h_inf : infEDist x (Kakeya.unitSegment T.base T.direction) ≤ ENNReal.ofReal δ := hx
    rw [h_eq] at h_inf
    have h2 : edist x y = ENNReal.ofReal (dist x y) := by simp [edist_dist]
    rw [h2] at h_inf
    have hdist : dist x y ≤ δ := (ENNReal.ofReal_le_ofReal_iff hδ.le).mp h_inf
    rcases hy with ⟨t, ht, rfl⟩
    exact ⟨t, ht.1, ht.2, hdist⟩

  -- Segment approximations for z and any x
  rcases h_helper z hzT with ⟨t_z, ht_z1, ht_z2, hdist_z⟩
  set y_z : Point3 := T.base + t_z • T.direction with hy_z_def

  have h_dir_bound : |inner ℝ T.direction w| ≤ θ :=
    acute_angle_implies_perp_inner_bound T.direction_unit hv hw h_perp hθ1 h_angle

  -- Bound |inner z w - c| ≤ L/2
  have h_z_c_bound : |inner ℝ z w - c| ≤ L / 2 := hc z hzQ

  -- Define slab with tighter radius
  set radius : ℝ := L / 2 + θ + 2 * δ with hradius_def
  have hradius_nonneg : 0 ≤ radius := by
    rw [hradius_def]; positivity
  let S : Kakeya.Slab :=
    { normal := w
      offset := c
      radius := radius
      normal_unit := hw
      radius_nonneg := hradius_nonneg }

  have h_H_nonempty : S.hyperplane.Nonempty := by
    have hinner_w : inner ℝ w w = (1 : ℝ) := by
      have h : inner ℝ w w = ‖w‖ ^ 2 := real_inner_self_eq_norm_sq w
      rw [h, hw] <;> norm_num
    have h2 : inner ℝ (c • w) w = c := by
      have h21 : inner ℝ (c • w) w = c * inner ℝ w w :=
        real_inner_smul_left w w c
      rw [h21, hinner_w] <;> ring
    have h : inner ℝ (c • w) S.normal = S.offset := by
      simpa [S] using h2
    exact ⟨c • w, h⟩

  -- Main bound: for any x in T.carrier, |inner x w - c| ≤ radius
  have h_main : ∀ (x : Point3), x ∈ T.carrier → |inner ℝ x w - c| ≤ radius := by
    intro x hx
    rcases h_helper x hx with ⟨t_x, ht_x1, ht_x2, hdist_x⟩
    set y_x : Point3 := T.base + t_x • T.direction with hy_x_def
    have h_tdiff_bound : |t_x - t_z| ≤ 1 := by
      have h1 : -1 ≤ t_x - t_z := by linarith
      have h2 : t_x - t_z ≤ 1 := by linarith
      exact abs_le.mpr ⟨h1, h2⟩
    have h_dir_term : |(t_x - t_z) * inner ℝ T.direction w| ≤ θ := by
      calc
        |(t_x - t_z) * inner ℝ T.direction w|
          = |t_x - t_z| * |inner ℝ T.direction w| := by rw [abs_mul]
        _ ≤ 1 * |inner ℝ T.direction w| := by
          exact mul_le_mul_of_nonneg_right h_tdiff_bound (abs_nonneg _)
        _ ≤ θ := by
          have h_eq : (1 : ℝ) * |inner ℝ T.direction w| = |inner ℝ T.direction w| := by ring
          rw [h_eq]
          exact h_dir_bound
    have h_err_term : |inner ℝ (x - y_x - (z - y_z)) w| ≤ 2 * δ := by
      have h_eq : x - y_x - (z - y_z) = (x - y_x) - (z - y_z) := by abel
      rw [h_eq]
      have h1 : |inner ℝ ((x - y_x) - (z - y_z)) w| ≤
          |inner ℝ (x - y_x) w| + |inner ℝ (z - y_z) w| := by
        have h2 : inner ℝ ((x - y_x) - (z - y_z)) w =
            inner ℝ (x - y_x) w - inner ℝ (z - y_z) w := by
          rw [inner_sub_left]
        rw [h2]
        have h3 : |inner ℝ (x - y_x) w - inner ℝ (z - y_z) w| ≤
            |inner ℝ (x - y_x) w| + |inner ℝ (z - y_z) w| := by
          calc
            |inner ℝ (x - y_x) w - inner ℝ (z - y_z) w|
              ≤ |inner ℝ (x - y_x) w| + |-(inner ℝ (z - y_z) w)| := abs_add_le _ _
            _ = |inner ℝ (x - y_x) w| + |inner ℝ (z - y_z) w| := by
              rw [abs_neg]
        exact h3
      have h3 : |inner ℝ (x - y_x) w| ≤ dist x y_x := by
        have h4 : |inner ℝ (x - y_x) w| ≤ ‖x - y_x‖ * ‖w‖ := abs_real_inner_le_norm (x - y_x) w
        have h5 : ‖x - y_x‖ = dist x y_x := by simp [dist_eq_norm]
        rw [h5, hw] at h4; simpa using h4
      have h6 : |inner ℝ (z - y_z) w| ≤ dist z y_z := by
        have h7 : |inner ℝ (z - y_z) w| ≤ ‖z - y_z‖ * ‖w‖ := abs_real_inner_le_norm (z - y_z) w
        have h8 : ‖z - y_z‖ = dist z y_z := by simp [dist_eq_norm]
        rw [h8, hw] at h7; simpa using h7
      linarith
    have h_xz_bound : |inner ℝ x w - inner ℝ z w| ≤ θ + 2 * δ := by
      have h_eq : inner ℝ x w - inner ℝ z w =
          (t_x - t_z) * inner ℝ T.direction w +
          inner ℝ (x - y_x - (z - y_z)) w := by
        simp [hy_x_def, hy_z_def, inner_sub_left, inner_add_left, inner_smul_left] <;> ring
      rw [h_eq]
      have h_sum : |(t_x - t_z) * inner ℝ T.direction w +
          inner ℝ (x - y_x - (z - y_z)) w| ≤
          |(t_x - t_z) * inner ℝ T.direction w| +
          |inner ℝ (x - y_x - (z - y_z)) w| := abs_add_le _ _
      linarith
    calc
      |inner ℝ x w - c|
        = |(inner ℝ x w - inner ℝ z w) + (inner ℝ z w - c)| := by ring_nf
      _ ≤ |inner ℝ x w - inner ℝ z w| + |inner ℝ z w - c| := abs_add_le _ _
      _ ≤ (θ + 2 * δ) + L / 2 := by gcongr
      _ = radius := by rw [hradius_def] <;> ring

  have h_containment : T.carrier ⊆ S.carrier := by
    intro x hx
    have h_ball : x ∈ Kakeya.DeltaTube.unitBall := hT_unit hx
    have h_final : |inner ℝ x w - c| ≤ radius := h_main x hx
    have h_hyperplane : S.hyperplane = {y : Point3 | inner ℝ y w = c} := by
      ext z; simp [S, Kakeya.Slab.hyperplane] <;> rfl
    have h_dist_eq : Metric.infDist x S.hyperplane = |inner ℝ x w - c| := by
      rw [h_hyperplane]; exact dist_to_hyperplane hw
    have h_cthick : x ∈ Metric.cthickening S.radius S.hyperplane := by
      have h7 : Metric.infDist x S.hyperplane ≤ S.radius := by
        rw [h_dist_eq]; exact h_final
      have h9 : ENNReal.ofReal (Metric.infDist x S.hyperplane) = Metric.infEDist x S.hyperplane := by
        rw [← ENNReal.ofReal_toReal (Metric.infEDist_ne_top h_H_nonempty)] <;> rfl
      have h8 : Metric.infEDist x S.hyperplane ≤ ENNReal.ofReal S.radius := by
        rw [← h9]; exact ENNReal.ofReal_le_ofReal h7
      exact h8
    exact ⟨h_ball, h_cthick⟩

  have h_radius_le : S.radius ≤ L / 2 + θ + 2 * δ := by
    have h : S.radius = radius := by rfl
    rw [h, hradius_def] <;> ring
  exact ⟨S, h_containment, h_radius_le⟩

end Kakeya.Assouad
