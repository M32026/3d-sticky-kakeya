import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Tactic

/-!
# Tight direction inner product bound from tube containment

If a fine tube is contained in a coarse tube of radius `tau ≤ 1/4`, then their
directions have projective inner product at least `sqrt(1 - 4*tau^2)`.

This is stronger than the `4*tau` norm bound from
`direction_closeness_from_containment`, and is the key estimate needed for
the WZ1 narrow vertical cone theorem.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- Standard identity: ‖a + b‖^2 = ‖a‖^2 + ‖b‖^2 + 2 * inner a b. -/
private lemma norm_add_sq_real {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a b : E) :
    ‖a + b‖^2 = ‖a‖^2 + ‖b‖^2 + 2 * inner ℝ a b := by
  have h_expand : inner ℝ (a + b) (a + b) = inner ℝ a a + inner ℝ b b + 2 * inner ℝ a b := by
    have h11 : inner ℝ (a + b) (a + b) = inner ℝ a (a + b) + inner ℝ b (a + b) := by
      exact InnerProductSpace.add_left a b (a + b)
    have h12 : inner ℝ a (a + b) = inner ℝ a a + inner ℝ a b := by exact inner_add_right a a b
    have h13 : inner ℝ b (a + b) = inner ℝ b a + inner ℝ b b := by exact inner_add_right b a b
    have h14 : inner ℝ b a = inner ℝ a b := (real_inner_comm b a).symm
    linarith [h11, h12, h13, h14]
  have h1 : ‖a + b‖^2 = inner ℝ (a + b) (a + b) := by exact Eq.symm (real_inner_self_eq_norm_sq (a + b))
  have h2 : ‖a‖^2 = inner ℝ a a := by exact Eq.symm (real_inner_self_eq_norm_sq a)
  have h3 : ‖b‖^2 = inner ℝ b b := by exact Eq.symm (real_inner_self_eq_norm_sq b)
  linarith [h_expand, h1, h2, h3]

lemma direction_inner_product_bound
    {delta tau : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (T : Kakeya.DeltaTube delta)
    (U : Kakeya.DeltaTube tau)
    (h_cont : T.carrier ⊆ U.carrier)
    (htau_nonneg : 0 ≤ tau)
    (htau_small : tau ≤ 1 / 4) :
    ∃ (sign : ℝ), (sign = 1 ∨ sign = -1) ∧
      inner ℝ T.direction (sign • U.direction) ≥ Real.sqrt (1 - 4 * tau^2) := by
  let axisU := Kakeya.unitSegment U.base U.direction
  have h_compactU : IsCompact axisU := by
    apply IsCompact.image isCompact_Icc
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hU_eq : U.carrier = ⋃ y ∈ axisU, Metric.closedBall y tau :=
    h_compactU.cthickening_eq_biUnion_closedBall htau_nonneg
  have h_base_in_T : T.base ∈ T.carrier := by
    have h1 : T.base ∈ Kakeya.unitSegment T.base T.direction := by
      refine ⟨0, by norm_num, ?_⟩; simp
    exact Metric.mem_cthickening_of_dist_le T.base T.base delta _ h1 (by simp [hdelta_nonneg])
  have h_end_in_T : T.base + T.direction ∈ T.carrier := by
    have h1 : T.base + T.direction ∈ Kakeya.unitSegment T.base T.direction := by
      refine ⟨1, by norm_num, ?_⟩; simp
    exact Metric.mem_cthickening_of_dist_le (T.base + T.direction) (T.base + T.direction) delta _ h1 (by simp [hdelta_nonneg])
  have h_base_in_U : T.base ∈ U.carrier := h_cont h_base_in_T
  have h_end_in_U : T.base + T.direction ∈ U.carrier := h_cont h_end_in_T
  rcases Set.mem_iUnion₂.mp (by rw [←hU_eq]; exact h_base_in_U) with ⟨q0, hq0_seg, hq0_ball⟩
  have hq0_dist : dist T.base q0 ≤ tau := by simpa [Metric.mem_closedBall] using hq0_ball
  rcases Set.mem_iUnion₂.mp (by rw [←hU_eq]; exact h_end_in_U) with ⟨q1, hq1_seg, hq1_ball⟩
  have hq1_dist : dist (T.base + T.direction) q1 ≤ tau := by simpa [Metric.mem_closedBall] using hq1_ball
  rcases hq0_seg with ⟨t0, ht0, hq0_eq⟩
  rcases hq1_seg with ⟨t1, ht1, hq1_eq⟩
  set s : ℝ := t1 - t0 with hs_def
  have ht0_1 : 0 ≤ t0 := (Set.mem_Icc.mp ht0).1
  have ht0_2 : t0 ≤ 1 := (Set.mem_Icc.mp ht0).2
  have ht1_1 : 0 ≤ t1 := (Set.mem_Icc.mp ht1).1
  have ht1_2 : t1 ≤ 1 := (Set.mem_Icc.mp ht1).2
  have hs_ge_neg_one : -1 ≤ s := by linarith [hs_def]
  have hs_le_one : s ≤ 1 := by linarith [hs_def]
  have h_qdiff : q1 - q0 = s • U.direction := by
    have hq0_eq' : q0 = U.base + t0 • U.direction := hq0_eq.symm
    have hq1_eq' : q1 = U.base + t1 • U.direction := hq1_eq.symm
    rw [hq1_eq', hq0_eq']
    simp [sub_smul, hs_def] <;> abel
  have hq0_dist' : ‖T.base - q0‖ ≤ tau := by simpa [dist_eq_norm] using hq0_dist
  have hq1_dist' : ‖(T.base + T.direction) - q1‖ ≤ tau := by simpa [dist_eq_norm] using hq1_dist
  set w : Point3 := T.direction - s • U.direction with hw_def
  have hw_norm : ‖w‖ ≤ 2 * tau := by
    have h_eq : w = (T.base + T.direction) - q1 - (T.base - q0) := by
      simp only [hw_def]
      have h' : T.direction - s • U.direction = (T.base + T.direction) - q1 - (T.base - q0) := by
        have hq : q1 - q0 = s • U.direction := h_qdiff
        calc
          T.direction - s • U.direction
            = T.direction - (q1 - q0) := by rw [hq]
          _ = (T.base + T.direction) - q1 - (T.base - q0) := by abel
      exact h'
    rw [h_eq]
    have h2 : ‖(T.base + T.direction) - q1 - (T.base - q0)‖ ≤ ‖(T.base + T.direction) - q1‖ + ‖T.base - q0‖ := norm_sub_le _ _
    linarith
  have h_abs_s_lower : |s| ≥ 1 - 2 * tau := by
    have h1 : ‖s • U.direction‖ = |s| := by
      rw [norm_smul, U.direction_unit] <;> simp
    have h2 : ‖T.direction‖ ≤ ‖s • U.direction‖ + ‖w‖ := by
      calc ‖T.direction‖
          = ‖s • U.direction + w‖ := by simp [hw_def, sub_add_cancel]
        _ ≤ ‖s • U.direction‖ + ‖w‖ := norm_add_le _ _
    rw [T.direction_unit] at h2
    rw [h1] at h2
    linarith [hw_norm]
  set p : ℝ := Real.sqrt (1 - 4 * tau^2) with hp_def
  have hp2 : p^2 = 1 - 4 * tau^2 := by
    rw [hp_def, Real.sq_sqrt (by nlinarith)]
  have hw2 : ‖w‖^2 ≤ 4 * tau^2 := by
    have h_nonneg : 0 ≤ ‖w‖ := by positivity
    nlinarith [hw_norm]
  by_cases h_s_nonneg : 0 ≤ s
  · -- s ≥ 0, sign = 1
    have hs_pos : 0 < s := by
      by_contra h
      have h' : s = 0 := by linarith
      rw [h'] at h_abs_s_lower
      have h10 : |(0 : ℝ)| = 0 := by simp
      rw [h10] at h_abs_s_lower
      have h11 : tau ≥ 1 / 2 := by linarith
      linarith [htau_small]
    have h_inner : inner ℝ T.direction U.direction = (s^2 + 1 - ‖w‖^2) / (2 * s) := by
      have h1 : T.direction = s • U.direction + w := by simp [hw_def, sub_add_cancel]
      have h2 : ‖T.direction‖^2 = s^2 + ‖w‖^2 + 2 * s * inner ℝ w U.direction := by
        rw [h1, norm_add_sq_real (s • U.direction) w]
        have hU : ‖U.direction‖ = 1 := U.direction_unit
        simp [norm_smul, hU, inner_smul_left, real_inner_comm] <;> ring
      have hT1 : ‖T.direction‖^2 = 1 := by rw [T.direction_unit]; norm_num
      have h_eq : 2 * s * inner ℝ w U.direction = 1 - s^2 - ‖w‖^2 := by linarith [h2, hT1]
      have h3 : inner ℝ T.direction U.direction = s + inner ℝ w U.direction := by
        rw [h1]; have hU : ‖U.direction‖ = 1 := U.direction_unit; simp [inner_add_left, inner_smul_left, hU] <;> ring
      rw [h3]
      have h4 : inner ℝ w U.direction = (1 - s^2 - ‖w‖^2) / (2 * s) := by
        have h5 : inner ℝ w U.direction = (2 * s * inner ℝ w U.direction) / (2 * s) := by
          field_simp [hs_pos.ne'] <;> ring
        rw [h5, h_eq] <;> ring
      rw [h4]; field_simp [hs_pos.ne'] <;> ring
    have h_ineq : (s^2 + 1 - ‖w‖^2) / (2 * s) ≥ p := by
      have h6 : (s^2 + 1 - ‖w‖^2) - 2 * s * p ≥ 0 := by
        have h7 : (s^2 + 1 - ‖w‖^2) - 2 * s * p = (s - p)^2 + (4 * tau^2 - ‖w‖^2) := by
          have h10 : 1 - p^2 = 4 * tau^2 := by linarith [hp2]
          calc (s^2 + 1 - ‖w‖^2) - 2 * s * p
            = (s^2 - 2 * s * p + p^2) + (1 - p^2) - ‖w‖^2 := by ring
          _ = (s - p)^2 + (1 - p^2) - ‖w‖^2 := by ring
          _ = (s - p)^2 + (4 * tau^2 - ‖w‖^2) := by rw [h10] <;> ring
        rw [h7]
        have h8 : 0 ≤ (s - p)^2 := by positivity
        have h9 : 0 ≤ 4 * tau^2 - ‖w‖^2 := by linarith [hw2]
        linarith
      have h9 : 0 < 2 * s := by linarith
      have h11 : 2 * s * p ≤ s^2 + 1 - ‖w‖^2 := by linarith [h6]
      have h12 : (s^2 + 1 - ‖w‖^2) / (2 * s) ≥ (2 * s * p) / (2 * s) := by
        exact div_le_div_of_nonneg_right h11 (by linarith)
      have h13 : (2 * s * p) / (2 * s) = p := by field_simp [h9.ne'] <;> ring
      rw [h13] at h12; exact h12
    refine ⟨1, Or.inl rfl, ?_⟩
    have h14 : (1 : ℝ) • U.direction = U.direction := by simp
    rw [h14, h_inner]; exact h_ineq
  · -- s < 0, sign = -1
    have hs_neg : s < 0 := by linarith
    set s' : ℝ := -s with hs'_def
    have hs'_pos : 0 < s' := by linarith
    set w' : Point3 := T.direction - (-s') • U.direction with hw'_def
    have hw'_eq : w' = w := by
      simp [hw'_def, hw_def, hs'_def] <;> abel
    have hw'_norm : ‖w'‖ ≤ 2 * tau := by rw [hw'_eq]; exact hw_norm
    have hw'2 : ‖w'‖^2 ≤ 4 * tau^2 := by
      have h_nonneg : 0 ≤ ‖w'‖ := by positivity
      nlinarith [hw'_norm]
    have h_inner : inner ℝ T.direction (-U.direction) = (s'^2 + 1 - ‖w'‖^2) / (2 * s') := by
      have h1 : T.direction = (-s') • U.direction + w' := by simp [hw'_def, sub_add_cancel]
      have h2 : ‖T.direction‖^2 = s'^2 + ‖w'‖^2 - 2 * s' * inner ℝ w' U.direction := by
        rw [h1, norm_add_sq_real ((-s') • U.direction) w']
        have hU : ‖U.direction‖ = 1 := U.direction_unit
        simp [norm_smul, hU, inner_smul_left, real_inner_comm] <;> ring
      have hT1 : ‖T.direction‖^2 = 1 := by rw [T.direction_unit]; norm_num
      have h_eq : 2 * s' * inner ℝ w' U.direction = s'^2 + ‖w'‖^2 - 1 := by linarith [h2, hT1]
      have h3 : inner ℝ T.direction (-U.direction) = s' - inner ℝ w' U.direction := by
        rw [h1]; have hU : ‖U.direction‖ = 1 := U.direction_unit; simp [inner_add_left, inner_smul_left, hU] <;> ring
      rw [h3]
      have h4 : inner ℝ w' U.direction = (s'^2 + ‖w'‖^2 - 1) / (2 * s') := by
        have h5 : inner ℝ w' U.direction = (2 * s' * inner ℝ w' U.direction) / (2 * s') := by
          field_simp [hs'_pos.ne'] <;> ring
        rw [h5, h_eq] <;> ring
      rw [h4]; field_simp [hs'_pos.ne'] <;> ring
    have h_ineq : (s'^2 + 1 - ‖w'‖^2) / (2 * s') ≥ p := by
      have h6 : (s'^2 + 1 - ‖w'‖^2) - 2 * s' * p ≥ 0 := by
        have h7 : (s'^2 + 1 - ‖w'‖^2) - 2 * s' * p = (s' - p)^2 + (4 * tau^2 - ‖w'‖^2) := by
          have h10 : 1 - p^2 = 4 * tau^2 := by linarith [hp2]
          calc (s'^2 + 1 - ‖w'‖^2) - 2 * s' * p
            = (s'^2 - 2 * s' * p + p^2) + (1 - p^2) - ‖w'‖^2 := by ring
          _ = (s' - p)^2 + (1 - p^2) - ‖w'‖^2 := by ring
          _ = (s' - p)^2 + (4 * tau^2 - ‖w'‖^2) := by rw [h10] <;> ring
        rw [h7]
        have h8 : 0 ≤ (s' - p)^2 := by positivity
        have h9 : 0 ≤ 4 * tau^2 - ‖w'‖^2 := by linarith [hw'2]
        linarith
      have h9 : 0 < 2 * s' := by linarith
      have h11 : 2 * s' * p ≤ s'^2 + 1 - ‖w'‖^2 := by linarith [h6]
      have h12 : (s'^2 + 1 - ‖w'‖^2) / (2 * s') ≥ (2 * s' * p) / (2 * s') := by
        exact div_le_div_of_nonneg_right h11 (by linarith)
      have h13 : (2 * s' * p) / (2 * s') = p := by field_simp [h9.ne'] <;> ring
      rw [h13] at h12; exact h12
    refine ⟨-1, Or.inr rfl, ?_⟩
    have h14 : (-1 : ℝ) • U.direction = -U.direction := by simp
    rw [h14, h_inner]; exact h_ineq

/--
Tighter transverse direction bound from full carrier containment.

If `Tδ.carrier ⊆ Uρ.carrier` with `0 ≤ δ ≤ ρ`, then the component of
`T.direction` perpendicular to `U.direction` has norm at most `2*(ρ - δ)`.

Proof: project onto a unit vector `v` perpendicular to `U.direction` in the
direction of `T.direction`'s transverse component. The functional
`x ↦ inner(x,v)` is constant on `U`'s segment and 1-Lipschitz, so its range
on `Uρ.carrier` has diameter at most `2ρ`. The points `T.base - δ•v` and
`T.base + T.direction + δ•v` are both in `Tδ.carrier`, and their `v`-values
differ by `‖transverse‖ + 2δ`.
-/
lemma direction_transverse_bound_of_containment
    {delta rho : ℝ}
    (hdelta : 0 ≤ delta) (hrho : 0 ≤ rho) (hdelta_le_rho : delta ≤ rho)
    (T : Kakeya.DeltaTube delta) (U : Kakeya.DeltaTube rho)
    (h_cont : T.carrier ⊆ U.carrier) :
    ‖T.direction - inner ℝ T.direction U.direction • U.direction‖ ≤ 2 * (rho - delta) := by
  set P : Point3 := T.direction - inner ℝ T.direction U.direction • U.direction with hP
  set L : ℝ := ‖P‖ with hL
  by_cases hL0 : L = 0
  · have h_nonneg : 0 ≤ 2 * (rho - delta) := by linarith
    rw [hL0]
    exact h_nonneg
  · have hLpos : 0 < L := by
      have h1 : 0 ≤ L := norm_nonneg P
      exact lt_of_le_of_ne h1 (Ne.symm hL0)
    set v : Point3 := (1 / L) • P with hv
    have hv_norm : ‖v‖ = 1 := by
      rw [hv, norm_smul]
      rw [Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 1 / L by positivity)]
      field_simp [hLpos.ne'] <;> ring
    have hcomm : inner ℝ U.direction T.direction = inner ℝ T.direction U.direction :=
      real_inner_comm _ _
    have hP_perp : inner ℝ U.direction P = 0 := by
      rw [hP]
      simp [inner_sub_right, inner_smul_right, U.direction_unit, hcomm]
      <;> ring
    have hv_perp : inner ℝ U.direction v = 0 := by
      rw [hv, inner_smul_right]
      rw [hP_perp] <;> ring
    have hP_self : inner ℝ P P = L ^ 2 := by
      rw [real_inner_self_eq_norm_sq, hL]
    have hL2 : L ^ 2 = 1 - (inner ℝ T.direction U.direction) ^ 2 := by
      let b := (inner ℝ T.direction U.direction) • U.direction
      have hPb : P = T.direction - b := by
        simp [hP, b] <;> rfl
      have h_norm : ‖P‖ ^ 2 = ‖T.direction‖ ^ 2 - 2 * inner ℝ T.direction b + ‖b‖ ^ 2 := by
        rw [hPb]
        exact norm_sub_sq_real T.direction b
      have h_inner_b : inner ℝ T.direction b = (inner ℝ T.direction U.direction) ^ 2 := by
        simp [b, inner_smul_right] <;> ring
      have h_norm_b : ‖b‖ ^ 2 = (inner ℝ T.direction U.direction) ^ 2 := by
        simp [b, norm_smul, U.direction_unit] <;> ring
      have h1 : ‖T.direction‖ = 1 := T.direction_unit
      rw [hL]
      rw [h_norm, h_inner_b, h_norm_b, h1] <;> ring
    have hTP : inner ℝ T.direction P = L ^ 2 := by
      have h : inner ℝ T.direction P =
          inner ℝ T.direction T.direction -
            inner ℝ T.direction (inner ℝ T.direction U.direction • U.direction) := by
        rw [hP]
        simp [inner_sub_right]
        <;> rfl
      rw [h]
      have h2 : inner ℝ T.direction (inner ℝ T.direction U.direction • U.direction) =
          (inner ℝ T.direction U.direction) ^ 2 := by
        simp [inner_smul_right] <;> ring
      rw [h2]
      have h3 : inner ℝ T.direction T.direction = 1 := by
        rw [real_inner_self_eq_norm_sq, T.direction_unit] <;> norm_num
      rw [h3]
      linarith [hL2]
    have hv_T : inner ℝ T.direction v = L := by
      rw [hv, inner_smul_right, hTP]
      have h : (1 / L) * L ^ 2 = L := by
        field_simp [hLpos.ne'] <;> ring
      rw [h]
    let f : Point3 → ℝ := fun x => inner ℝ x v
    have h_segment_compact : IsCompact (Kakeya.unitSegment U.base U.direction) := by
      apply IsCompact.image isCompact_Icc
      exact continuous_const.add (continuous_id.smul continuous_const)
    have hU_eq : U.carrier = ⋃ y ∈ Kakeya.unitSegment U.base U.direction, Metric.closedBall y rho :=
      h_segment_compact.cthickening_eq_biUnion_closedBall hrho
    have h_range : ∀ x ∈ U.carrier, |f x - f U.base| ≤ rho := by
      intro x hx
      rw [hU_eq] at hx
      rcases Set.mem_iUnion₂.mp hx with ⟨y, hy, hball⟩
      have hdist : dist x y ≤ rho := by simpa [Metric.mem_closedBall] using hball
      rcases hy with ⟨t, ht, rfl⟩
      have hfy : f (U.base + t • U.direction) = f U.base := by
        have h : inner ℝ (U.base + t • U.direction) v = inner ℝ U.base v := by
          rw [inner_add_left, inner_smul_left, hv_perp] <;> ring
        exact h
      have h : |f x - f U.base| ≤ dist x (U.base + t • U.direction) := by
        calc
          |f x - f U.base|
            = |f x - f (U.base + t • U.direction)| := by rw [hfy]
          _ = |inner ℝ (x - (U.base + t • U.direction)) v| := by
              have h_eq : inner ℝ x v - inner ℝ (U.base + t • U.direction) v =
                  inner ℝ (x - (U.base + t • U.direction)) v := by
                exact (inner_sub_left x (U.base + t • U.direction) v).symm
              rw [h_eq]
          _ ≤ ‖x - (U.base + t • U.direction)‖ * ‖v‖ := by
              exact abs_real_inner_le_norm (x - (U.base + t • U.direction)) v
          _ = dist x (U.base + t • U.direction) * ‖v‖ := by rw [dist_eq_norm]
          _ = dist x (U.base + t • U.direction) := by rw [hv_norm] <;> ring
      exact h.trans hdist
    let x1 := T.base - delta • v
    let x2 := T.base + T.direction + delta • v
    have hx1_in_T : x1 ∈ T.carrier := by
      have h : ‖x1 - T.base‖ = delta := by
        have h1 : x1 - T.base = (-delta) • v := by
          simp [x1] <;> abel
        rw [h1, norm_smul]
        rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg hdelta, hv_norm] <;> ring
      have hdist : dist x1 T.base = delta := by
        rw [dist_eq_norm] <;> exact h
      exact Metric.mem_cthickening_of_dist_le x1 T.base delta
        (Kakeya.unitSegment T.base T.direction)
        ⟨0, by norm_num, by simp⟩ (by simpa using le_of_eq hdist)
    have hx2_in_T : x2 ∈ T.carrier := by
      have h : ‖x2 - (T.base + T.direction)‖ = delta := by
        have h1 : x2 - (T.base + T.direction) = delta • v := by
          simp [x2] <;> abel
        rw [h1, norm_smul]
        rw [Real.norm_eq_abs, abs_of_nonneg hdelta, hv_norm] <;> ring
      have hdist : dist x2 (T.base + T.direction) = delta := by
        rw [dist_eq_norm] <;> exact h
      exact Metric.mem_cthickening_of_dist_le x2 (T.base + T.direction) delta
        (Kakeya.unitSegment T.base T.direction)
        ⟨1, by norm_num, by simp⟩ (by simpa using le_of_eq hdist)
    have hx1_in_U : x1 ∈ U.carrier := h_cont hx1_in_T
    have hx2_in_U : x2 ∈ U.carrier := h_cont hx2_in_T
    have h1 : f x1 ≥ f U.base - rho := by
      have h := h_range x1 hx1_in_U
      have h' : -(rho) ≤ f x1 - f U.base := (abs_le.mp h).1
      linarith
    have h2 : f x2 ≤ f U.base + rho := by
      have h := h_range x2 hx2_in_U
      have h' : f x2 - f U.base ≤ rho := (abs_le.mp h).2
      linarith
    have hfx1 : f x1 = f T.base - delta := by
      have h : f x1 = inner ℝ (T.base - delta • v) v := by rfl
      rw [h]
      have h2 : inner ℝ (T.base - delta • v) v = inner ℝ T.base v - inner ℝ (delta • v) v := by
        exact inner_sub_left T.base (delta • v) v
      rw [h2]
      have h3 : inner ℝ (delta • v) v = delta * inner ℝ v v := by
        simp [inner_smul_left]
      rw [h3]
      have h4 : inner ℝ v v = 1 := by
        rw [real_inner_self_eq_norm_sq, hv_norm] <;> norm_num
      rw [h4] <;> ring
    have hfx2 : f x2 = f T.base + L + delta := by
      have h : f x2 = inner ℝ ((T.base + T.direction) + delta • v) v := by
        congr 1 <;> simp [x2] <;> abel
      rw [h]
      have h2 : inner ℝ ((T.base + T.direction) + delta • v) v =
          inner ℝ (T.base + T.direction) v + inner ℝ (delta • v) v := by
        exact inner_add_left (T.base + T.direction) (delta • v) v
      rw [h2]
      have h3 : inner ℝ (T.base + T.direction) v = inner ℝ T.base v + inner ℝ T.direction v := by
        exact inner_add_left T.base T.direction v
      rw [h3]
      have h4 : inner ℝ (delta • v) v = delta * inner ℝ v v := by
        simp [inner_smul_left]
      rw [h4]
      have h5 : inner ℝ v v = 1 := by
        rw [real_inner_self_eq_norm_sq, hv_norm] <;> norm_num
      rw [h5, hv_T] <;> ring
    rw [hfx1] at h1
    rw [hfx2] at h2
    linarith

end Kakeya.Assouad

end
