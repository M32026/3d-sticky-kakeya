import MyLeanRepo.Kakeya.AssertionD
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Intersection diameter bounds for δ-tubes

Two geometric lemmas used in the proof of nonessential tube axis alignment:

1. Transverse projection bound: a point in a δ-tube projects to within δ of the
   base's projection along any direction perpendicular to the tube axis.

2. Axial diameter bound: if two δ-tubes meet at angle θ, the projection of their
   intersection onto the axis of one tube has diameter at most
   2δ(1 + cos θ)/sin θ.
-/

noncomputable section

open Kakeya MeasureTheory Set

namespace Kakeya.Assouad

/--
For a point in a δ-tube, its projection onto any unit vector perpendicular to
the tube direction differs from the base's projection by at most δ.
-/
lemma tube_perpendicular_projection_bound {δ : ℝ} (hδ : 0 ≤ δ)
    (T : DeltaTube δ) (w : Point3) (hw : ‖w‖ = 1)
    (horth : inner ℝ T.direction w = 0)
    (x : Point3) (hx : x ∈ T.carrier) :
    |inner ℝ (x - T.base) w| ≤ δ := by
  have hcarrier : T.carrier = Metric.cthickening δ (unitSegment T.base T.direction) := by
    simp [DeltaTube.carrier]
  rw [hcarrier] at hx
  have hcompact : IsCompact (unitSegment T.base T.direction) := by
    exact isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))
  rw [hcompact.cthickening_eq_biUnion_closedBall hδ] at hx
  rcases Set.mem_iUnion₂.mp hx with ⟨p, hp_seg, hp_ball⟩
  rcases hp_seg with ⟨t, _ht, rfl⟩
  set p : Point3 := T.base + t • T.direction with hp_def
  have hdist : dist x p ≤ δ := by
    simpa [Metric.mem_closedBall, dist_comm] using hp_ball
  have hnorm : ‖x - p‖ ≤ δ := by simpa [dist_eq_norm] using hdist
  have hkey : inner ℝ (p - T.base) w = 0 := by
    have h : p - T.base = t • T.direction := by simp [hp_def] <;> abel
    rw [h]
    have h2 : inner ℝ (t • T.direction) w = t * inner ℝ T.direction w := by
      rw [inner_smul_left] <;> simp
    rw [h2, horth] <;> ring
  have hmain : inner ℝ (x - T.base) w = inner ℝ (x - p) w := by
    have h : x - T.base = (x - p) + (p - T.base) := by abel
    rw [h]
    have h2 : inner ℝ ((x - p) + (p - T.base)) w =
        inner ℝ (x - p) w + inner ℝ (p - T.base) w := by
      rw [inner_add_left]
    rw [h2, hkey, add_zero]
  rw [hmain]
  have hcs : |inner ℝ (x - p) w| ≤ ‖x - p‖ * ‖w‖ :=
    abs_real_inner_le_norm (x - p) w
  rw [hw] at hcs
  rw [mul_one] at hcs
  exact hcs.trans hnorm

/--
Transverse diameter bound: for any point in the intersection of two δ-tubes and
any unit vector perpendicular to U.direction, the transverse projection is
within δ of U.base's projection.
-/
lemma transverse_projection_bound {δ : ℝ} (hδ : 0 ≤ δ)
    (T U : DeltaTube δ) (w : Point3) (hw : ‖w‖ = 1)
    (horth : inner ℝ U.direction w = 0)
    (x : Point3) (hx : x ∈ T.carrier ∩ U.carrier) :
    |inner ℝ x w - inner ℝ U.base w| ≤ δ := by
  have h : |inner ℝ (x - U.base) w| ≤ δ :=
    tube_perpendicular_projection_bound hδ U w hw horth x hx.2
  have h2 : inner ℝ (x - U.base) w = inner ℝ x w - inner ℝ U.base w := by
    rw [inner_sub_left]
  rw [h2] at h
  exact h

/--
The axial diameter of the intersection of two δ-tubes at angle θ is bounded by
2δ(1 + cos θ)/sin θ.

Here `v` is either `U.direction` or `-U.direction`, chosen so that the angle
between `T.direction` and `v` is `θ ∈ [0, π/2]`.
-/
lemma intersection_axial_diameter_bound {δ : ℝ} (hδ : 0 ≤ δ)
    (T U : DeltaTube δ)
    (v : Point3)
    (h_v_choice : v = U.direction ∨ v = -U.direction)
    (θ : ℝ) (hθ_nonneg : 0 ≤ θ) (hθ_le : θ ≤ Real.pi / 2)
    (hcos : inner ℝ T.direction v = Real.cos θ)
    (hsin_pos : 0 < Real.sin θ)
    (x y : Point3)
    (hx : x ∈ T.carrier ∩ U.carrier)
    (hy : y ∈ T.carrier ∩ U.carrier) :
    |inner ℝ (x - y) v| ≤ 2 * δ * (1 + Real.cos θ) / Real.sin θ := by
  have hv : ‖v‖ = 1 := by
    cases h_v_choice with
    | inl h => rw [h]; exact U.direction_unit
    | inr h => rw [h]; rw [norm_neg]; exact U.direction_unit

  let e1 : Point3 := v
  let e2 : Point3 := (Real.sin θ)⁻¹ • (T.direction - Real.cos θ • e1)
  let w_perp : Point3 := -Real.sin θ • e1 + Real.cos θ • e2

  have hcos_nonneg : 0 ≤ Real.cos θ := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · have hpi : 0 < Real.pi := Real.pi_pos
      linarith
    · exact hθ_le

  -- ‖T.direction - cos θ • e1‖ = sin θ
  have h_norm_diff : ‖T.direction - Real.cos θ • e1‖ = Real.sin θ := by
    have h1 : ‖T.direction - Real.cos θ • e1‖ ^ 2 = (Real.sin θ) ^ 2 := by
      rw [norm_sub_sq_real T.direction (Real.cos θ • e1)]
      have h21 : inner ℝ T.direction (Real.cos θ • e1) =
          Real.cos θ * inner ℝ T.direction e1 := by
        rw [inner_smul_right] <;> simp
      have h22 : ‖Real.cos θ • e1‖ ^ 2 = (Real.cos θ)^2 * ‖e1‖ ^ 2 := by
        have h : ‖Real.cos θ • e1‖ ^ 2 = (‖Real.cos θ‖ * ‖e1‖) ^ 2 := by
          rw [norm_smul]
        rw [h]
        have h' : ‖Real.cos θ‖ = |Real.cos θ| := by simp
        rw [h']
        have hsq : (|Real.cos θ| * ‖e1‖) ^ 2 = |Real.cos θ| ^ 2 * ‖e1‖ ^ 2 := by ring
        rw [hsq]
        have hsq2 : |Real.cos θ| ^ 2 = (Real.cos θ)^2 := sq_abs (Real.cos θ)
        rw [hsq2] <;> ring
      rw [h21, h22, hcos]
      have h23 : ‖T.direction‖ ^ 2 = 1 := by rw [T.direction_unit] <;> norm_num
      have h24 : ‖e1‖ ^ 2 = 1 := by rw [hv] <;> norm_num
      rw [h23, h24] <;> nlinarith [Real.sin_sq_add_cos_sq θ]
    have h_nonneg : 0 ≤ ‖T.direction - Real.cos θ • e1‖ := by positivity
    have h_sin_nonneg : 0 ≤ Real.sin θ := by positivity
    nlinarith

  have he2_norm : ‖e2‖ = 1 := by
    have h : ‖e2‖ = |(Real.sin θ)⁻¹| * ‖T.direction - Real.cos θ • e1‖ := by
      simp [e2, norm_smul] <;> rfl
    rw [h]
    have hpos : 0 < (Real.sin θ)⁻¹ := by positivity
    rw [abs_of_pos hpos, h_norm_diff]
    <;> field_simp [hsin_pos.ne'] <;> norm_num

  -- inner e2 e1 = 0
  have he2_orth_e1 : inner ℝ e2 e1 = 0 := by
    have h : inner ℝ e2 e1 =
        (Real.sin θ)⁻¹ * inner ℝ (T.direction - Real.cos θ • e1) e1 := by
      rw [inner_smul_left] <;> simp
    rw [h]
    have h2 : inner ℝ (T.direction - Real.cos θ • e1) e1 =
        inner ℝ T.direction e1 - Real.cos θ * inner ℝ e1 e1 := by
      rw [inner_sub_left, inner_smul_left] <;> simp <;> ring
    rw [h2, hcos]
    have h3 : inner ℝ e1 e1 = ‖e1‖ ^ 2 := inner_self_eq_norm_sq_to_K (𝕜 := ℝ) e1
    rw [h3, hv] <;> field_simp [hsin_pos.ne'] <;> norm_num

  -- inner T.direction e2 = sin θ
  have hT_dir_e2 : inner ℝ T.direction e2 = Real.sin θ := by
    have h : inner ℝ T.direction e2 =
        (Real.sin θ)⁻¹ * inner ℝ T.direction (T.direction - Real.cos θ • e1) := by
      rw [inner_smul_right] <;> rfl
    rw [h]
    have h2 : inner ℝ T.direction (T.direction - Real.cos θ • e1) =
        inner ℝ T.direction T.direction - Real.cos θ * inner ℝ T.direction e1 := by
      rw [inner_sub_right, inner_smul_right] <;> ring
    rw [h2]
    have h3 : inner ℝ T.direction T.direction = ‖T.direction‖ ^ 2 :=
      inner_self_eq_norm_sq_to_K (𝕜 := ℝ) T.direction
    rw [h3, T.direction_unit, hcos]
    have h4 : (1 : ℝ) ^ 2 - Real.cos θ * Real.cos θ = (Real.sin θ) ^ 2 := by
      have h5 : (Real.sin θ)^2 + (Real.cos θ)^2 = 1 := Real.sin_sq_add_cos_sq θ
      nlinarith
    rw [h4]
    field_simp [hsin_pos.ne'] <;> ring

  -- ‖w_perp‖ = 1
  have hw_perp_norm : ‖w_perp‖ = 1 := by
    have h_e1_e2 : inner ℝ e1 e2 = 0 := by
      have h7 : inner ℝ e1 e2 = inner ℝ e2 e1 := (real_inner_comm e1 e2).symm
      rw [h7, he2_orth_e1] <;> ring
    have h1 : ‖w_perp‖ ^ 2 = 1 := by
      have h11 : inner ℝ w_perp w_perp = ‖w_perp‖ ^ 2 :=
        inner_self_eq_norm_sq_to_K (𝕜 := ℝ) w_perp
      have h12 : inner ℝ w_perp w_perp =
          (Real.sin θ)^2 * inner ℝ e1 e1 + (Real.cos θ)^2 * inner ℝ e2 e2 := by
        have h_exp : w_perp = -Real.sin θ • e1 + Real.cos θ • e2 := by rfl
        rw [h_exp]
        have h_a : inner ℝ (-Real.sin θ • e1 + Real.cos θ • e2)
            (-Real.sin θ • e1 + Real.cos θ • e2) =
            inner ℝ (-Real.sin θ • e1) (-Real.sin θ • e1) +
            inner ℝ (-Real.sin θ • e1) (Real.cos θ • e2) +
            inner ℝ (Real.cos θ • e2) (-Real.sin θ • e1) +
            inner ℝ (Real.cos θ • e2) (Real.cos θ • e2) := by
          have h1 : inner ℝ (-Real.sin θ • e1 + Real.cos θ • e2)
              (-Real.sin θ • e1 + Real.cos θ • e2) =
              inner ℝ (-Real.sin θ • e1) (-Real.sin θ • e1 + Real.cos θ • e2) +
              inner ℝ (Real.cos θ • e2) (-Real.sin θ • e1 + Real.cos θ • e2) := by
            rw [inner_add_left]
          rw [h1]
          have h2 : inner ℝ (-Real.sin θ • e1) (-Real.sin θ • e1 + Real.cos θ • e2) =
              inner ℝ (-Real.sin θ • e1) (-Real.sin θ • e1) +
              inner ℝ (-Real.sin θ • e1) (Real.cos θ • e2) := by
            rw [inner_add_right]
          have h3 : inner ℝ (Real.cos θ • e2) (-Real.sin θ • e1 + Real.cos θ • e2) =
              inner ℝ (Real.cos θ • e2) (-Real.sin θ • e1) +
              inner ℝ (Real.cos θ • e2) (Real.cos θ • e2) := by
            rw [inner_add_right]
          rw [h2, h3] <;> ring
        rw [h_a]
        have h_b1 : inner ℝ (-Real.sin θ • e1) (-Real.sin θ • e1) =
            (Real.sin θ)^2 * inner ℝ e1 e1 := by
          rw [real_inner_smul_left, real_inner_smul_right] <;> ring
        have h_b2 : inner ℝ (-Real.sin θ • e1) (Real.cos θ • e2) =
            -Real.sin θ * Real.cos θ * inner ℝ e1 e2 := by
          rw [real_inner_smul_left, real_inner_smul_right] <;> ring
        have h_b3 : inner ℝ (Real.cos θ • e2) (-Real.sin θ • e1) =
            -Real.cos θ * Real.sin θ * inner ℝ e2 e1 := by
          rw [real_inner_smul_left, real_inner_smul_right] <;> ring
        have h_b4 : inner ℝ (Real.cos θ • e2) (Real.cos θ • e2) =
            (Real.cos θ)^2 * inner ℝ e2 e2 := by
          rw [real_inner_smul_left, real_inner_smul_right] <;> ring
        rw [h_b1, h_b2, h_b3, h_b4, h_e1_e2, he2_orth_e1] <;> ring
      rw [← h11, h12]
      have h13 : inner ℝ e1 e1 = ‖e1‖ ^ 2 := inner_self_eq_norm_sq_to_K (𝕜 := ℝ) e1
      have h14 : inner ℝ e2 e2 = ‖e2‖ ^ 2 := inner_self_eq_norm_sq_to_K (𝕜 := ℝ) e2
      rw [h13, h14, hv, he2_norm] <;> nlinarith [Real.sin_sq_add_cos_sq θ]
    have h_nonneg : 0 ≤ ‖w_perp‖ := by positivity
    nlinarith

  -- inner T.direction w_perp = 0
  have hw_perp_orth_T : inner ℝ T.direction w_perp = 0 := by
    have h : inner ℝ T.direction w_perp =
        -Real.sin θ * inner ℝ T.direction e1 + Real.cos θ * inner ℝ T.direction e2 := by
      have h_exp : w_perp = -Real.sin θ • e1 + Real.cos θ • e2 := by rfl
      rw [h_exp]
      have h_a : inner ℝ T.direction (-Real.sin θ • e1 + Real.cos θ • e2) =
          inner ℝ T.direction (-Real.sin θ • e1) +
          inner ℝ T.direction (Real.cos θ • e2) := by
        rw [inner_add_right]
      rw [h_a]
      have h_b1 : inner ℝ T.direction (-Real.sin θ • e1) =
          -Real.sin θ * inner ℝ T.direction e1 := by
        rw [real_inner_smul_right] <;> ring
      have h_b2 : inner ℝ T.direction (Real.cos θ • e2) =
          Real.cos θ * inner ℝ T.direction e2 := by
        rw [real_inner_smul_right] <;> ring
      rw [h_b1, h_b2] <;> ring
    rw [h, hcos, hT_dir_e2] <;> ring

  -- inner U.direction e2 = 0
  have he2_orth_U : inner ℝ U.direction e2 = 0 := by
    have h_e1_e2 : inner ℝ e1 e2 = 0 := by
      have h7 : inner ℝ e1 e2 = inner ℝ e2 e1 := (real_inner_comm e1 e2).symm
      rw [h7, he2_orth_e1] <;> ring
    cases h_v_choice with
    | inl h =>
      have h5 : U.direction = e1 := by
        simpa [e1] using h.symm
      rw [h5]
      exact h_e1_e2
    | inr h =>
      have hU : U.direction = -e1 := by
        have h' : v = -U.direction := h
        have h'' : U.direction = -v := neg_eq_iff_eq_neg.mp h'.symm
        simpa [e1] using h''
      rw [hU]
      have h5 : inner ℝ (-e1) e2 = -inner ℝ e1 e2 := by
        rw [inner_neg_left]
      rw [h5, h_e1_e2] <;> ring

  let c : ℝ := inner ℝ (T.base - U.base) e2

  -- For a point z in the intersection, derive bounds on sin θ * inner (z - T.base) e1
  have h_main : ∀ (z : Point3), z ∈ T.carrier ∩ U.carrier →
      -Real.cos θ * c - δ * (Real.cos θ + 1) ≤ Real.sin θ * inner ℝ (z - T.base) e1 ∧
      Real.sin θ * inner ℝ (z - T.base) e1 ≤ -Real.cos θ * c + δ * (Real.cos θ + 1) := by
    intro z hz
    have hzT : z ∈ T.carrier := hz.1
    have hzU : z ∈ U.carrier := hz.2

    set a : ℝ := inner ℝ (z - T.base) e1 with ha_def
    set b : ℝ := inner ℝ (z - T.base) e2 with hb_def

    -- Bound from T
    have hT_bound : |inner ℝ (z - T.base) w_perp| ≤ δ :=
      tube_perpendicular_projection_bound hδ T w_perp hw_perp_norm hw_perp_orth_T z hzT

    have h_expand1 : inner ℝ (z - T.base) w_perp =
        -Real.sin θ * a + Real.cos θ * b := by
      have h : w_perp = -Real.sin θ • e1 + Real.cos θ • e2 := by rfl
      rw [h]
      have h2 : inner ℝ (z - T.base) (-Real.sin θ • e1 + Real.cos θ • e2) =
          inner ℝ (z - T.base) (-Real.sin θ • e1) + inner ℝ (z - T.base) (Real.cos θ • e2) := by
        rw [inner_add_right]
      rw [h2]
      have h3 : inner ℝ (z - T.base) (-Real.sin θ • e1) = -Real.sin θ * a := by
        rw [inner_smul_right, ha_def] <;> ring
      have h4 : inner ℝ (z - T.base) (Real.cos θ • e2) = Real.cos θ * b := by
        rw [inner_smul_right, hb_def] <;> ring
      rw [h3, h4] <;> ring
    rw [h_expand1] at hT_bound

    -- Bound from U
    have hU_bound : |inner ℝ (z - U.base) e2| ≤ δ :=
      tube_perpendicular_projection_bound hδ U e2 he2_norm he2_orth_U z hzU

    have h_expand2 : inner ℝ (z - U.base) e2 = b + c := by
      have h : z - U.base = (z - T.base) + (T.base - U.base) := by abel
      rw [h, inner_add_left, hb_def] <;> rfl
    rw [h_expand2] at hU_bound

    -- From hU_bound: -δ ≤ b + c ≤ δ
    have hb1 : -c - δ ≤ b := by
      have h : -δ ≤ b + c := (abs_le.mp hU_bound).1
      linarith
    have hb2 : b ≤ -c + δ := by
      have h : b + c ≤ δ := (abs_le.mp hU_bound).2
      linarith

    -- cos θ * b bounds (using cos θ ≥ 0)
    have hcb1 : -Real.cos θ * c - Real.cos θ * δ ≤ Real.cos θ * b := by
      have h : Real.cos θ * (-c - δ) ≤ Real.cos θ * b :=
        mul_le_mul_of_nonneg_left hb1 hcos_nonneg
      linarith
    have hcb2 : Real.cos θ * b ≤ -Real.cos θ * c + Real.cos θ * δ := by
      have h : Real.cos θ * b ≤ Real.cos θ * (-c + δ) :=
        mul_le_mul_of_nonneg_left hb2 hcos_nonneg
      linarith

    -- From hT_bound: -δ ≤ -sin θ * a + cos θ * b ≤ δ
    have hT1 : -δ ≤ -Real.sin θ * a + Real.cos θ * b := (abs_le.mp hT_bound).1
    have hT2 : -Real.sin θ * a + Real.cos θ * b ≤ δ := (abs_le.mp hT_bound).2

    constructor
    · linarith
    · linarith

  have hx_bounds := h_main x hx
  have hy_bounds := h_main y hy

  set ax : ℝ := inner ℝ (x - T.base) e1 with hax_def
  set ay : ℝ := inner ℝ (y - T.base) e1 with hay_def

  have h_ax_lower : -Real.cos θ * c - δ * (Real.cos θ + 1) ≤ Real.sin θ * ax := hx_bounds.1
  have h_ax_upper : Real.sin θ * ax ≤ -Real.cos θ * c + δ * (Real.cos θ + 1) := hx_bounds.2
  have h_ay_lower : -Real.cos θ * c - δ * (Real.cos θ + 1) ≤ Real.sin θ * ay := hy_bounds.1
  have h_ay_upper : Real.sin θ * ay ≤ -Real.cos θ * c + δ * (Real.cos θ + 1) := hy_bounds.2

  have h_diff : |Real.sin θ * (ax - ay)| ≤ 2 * δ * (Real.cos θ + 1) := by
    have h1 : -(2 * δ * (Real.cos θ + 1)) ≤ Real.sin θ * (ax - ay) := by linarith
    have h2 : Real.sin θ * (ax - ay) ≤ 2 * δ * (Real.cos θ + 1) := by linarith
    exact abs_le.mpr ⟨h1, h2⟩

  have h_final : |ax - ay| ≤ 2 * δ * (1 + Real.cos θ) / Real.sin θ := by
    have h3 : |Real.sin θ * (ax - ay)| = Real.sin θ * |ax - ay| := by
      rw [abs_mul, abs_of_pos hsin_pos]
    rw [h3] at h_diff
    have h4 : Real.sin θ * |ax - ay| ≤ 2 * δ * (Real.cos θ + 1) := h_diff
    have h5 : |ax - ay| ≤ (2 * δ * (Real.cos θ + 1)) / Real.sin θ := by
      calc
        |ax - ay| = (Real.sin θ * |ax - ay|) / Real.sin θ := by
          field_simp [hsin_pos.ne'] <;> ring
        _ ≤ (2 * δ * (Real.cos θ + 1)) / Real.sin θ := by
          gcongr
          <;> linarith
    simpa [add_comm] using h5

  have h6 : inner ℝ (x - y) v = ax - ay := by
    have h7 : x - y = (x - T.base) - (y - T.base) := by abel
    rw [h7, inner_sub_left] <;> rfl
  rw [h6]
  exact h_final

end Kakeya.Assouad
