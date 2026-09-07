import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LocalGrainTransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ADTransfer
import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Transferred local grains under anisotropic rescaling

This module transfers `PureWZ2LocalGrainData` from the original geometry to the
anisotropically rescaled geometry.

## Main results

- `anisotropicRescalingInverse` and left/right inverse lemmas
- `sqrt_expand_identity`: algebraic helper
- `scalar_v01_lower_bound`: V0² + V1² ≥ 1/4 - 8δ from unit norm + small incidence
- `scalar_v1_minus_a_v0_lower_bound`: |V1 - a·V0| ≥ 1/16
- `dPhiInvT_norm_lower_bound`: ‖DΦ^{-T}·V‖ ≥ 25/8 ≥ 1
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

variable (g : SlopeFunction) (c d m : ℝ)

/-- The inverse of the anisotropic rescaling map. -/
def anisotropicRescalingInverse (q : Point3) : Point3 :=
  let a := g (c + (d - c) / 2)
  let b := m * (d - c) / 2
  let S := 2 / (d - c)
  point3
    (q 0 - a / b * q 1)
    (q 1 / b)
    (q 2 / S + c + 1 / S)

/-- Φ ∘ Φ^{-1} = id. -/
lemma anisotropicRescaling_left_inverse
    (hcd : c < d) (hm : 0 < m) (q : Point3) :
    anisotropicRescalingMap g c d m (anisotropicRescalingInverse g c d m q) = q := by
  set a : ℝ := g (c + (d - c) / 2) with ha_def
  set b : ℝ := m * (d - c) / 2 with hb_def
  set S : ℝ := 2 / (d - c) with hS_def
  have hb_pos : 0 < b := by rw [hb_def] <;> positivity
  have hS_pos : 0 < S := by rw [hS_def] <;> positivity
  have hdb : d - c ≠ 0 := by linarith
  ext i
  fin_cases i <;> simp [anisotropicRescalingMap, anisotropicRescalingInverse, point3]
    <;> field_simp [hb_pos.ne', hS_pos.ne', hdb] <;> ring

/-- Φ^{-1} ∘ Φ = id. -/
lemma anisotropicRescaling_right_inverse
    (hcd : c < d) (hm : 0 < m) (p : Point3) :
    anisotropicRescalingInverse g c d m (anisotropicRescalingMap g c d m p) = p := by
  set a : ℝ := g (c + (d - c) / 2) with ha_def
  set b : ℝ := m * (d - c) / 2 with hb_def
  set S : ℝ := 2 / (d - c) with hS_def
  have hb_pos : 0 < b := by rw [hb_def] <;> positivity
  have hS_pos : 0 < S := by rw [hS_def] <;> positivity
  have hdb : d - c ≠ 0 := by linarith
  ext i
  fin_cases i <;> simp [anisotropicRescalingMap, anisotropicRescalingInverse, point3]
    <;> field_simp [hb_pos.ne', hS_pos.ne', hdb] <;> ring

/-- Algebraic identity: (2 * (sqrt(3/4) * sqrt(x) + delta))^2 =
    3*x + 8*sqrt(3/4)*sqrt(x)*delta + 4*delta^2. -/
private lemma sqrt_expand_identity (x delta : ℝ) (hx : 0 ≤ x) :
    (2 * (Real.sqrt (3 / 4) * Real.sqrt x + delta)) ^ 2 =
    3 * x + 8 * Real.sqrt (3 / 4) * Real.sqrt x * delta + 4 * delta ^ 2 := by
  set a : ℝ := Real.sqrt (3 / 4) with ha
  set b : ℝ := Real.sqrt x with hb
  have ha2 : a ^ 2 = 3 / 4 := by
    rw [ha]
    exact Real.sq_sqrt (by norm_num)
  have hb2 : b ^ 2 = x := by
    rw [hb]
    exact Real.sq_sqrt hx
  have h1 : (2 * (a * b + delta)) ^ 2 = 4 * (a * b + delta) ^ 2 := by ring
  rw [h1]
  have h21 : (a * b + delta) ^ 2 = (a * b) ^ 2 + 2 * (a * b) * delta + delta ^ 2 := add_sq (a * b) delta
  rw [h21]
  have h22 : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by ring
  rw [h22, ha2, hb2] <;> ring

/-- Pure scalar lemma: from unit norm, vertical direction, and small incidence,
    derive V0^2 + V1^2 ≥ 1/4 - 8*delta. -/
private lemma scalar_v01_lower_bound
    (V0 V1 V2 dir0 dir1 dir2 delta : ℝ)
    (hV : V0^2 + V1^2 + V2^2 = 1)
    (hdir : dir0^2 + dir1^2 + dir2^2 = 1)
    (hdir_vert : 1/2 ≤ |dir2|)
    (h_inc : |dir0*V0 + dir1*V1 + dir2*V2| ≤ delta)
    (hdelta_small : delta ≤ 1/100) :
    V0^2 + V1^2 ≥ 1/4 - 8*delta := by
  have hdelta_nonneg : 0 ≤ delta := le_trans (abs_nonneg _) h_inc
  have hdir2_sq : dir2^2 ≥ 1/4 := by
    have h : dir2^2 = |dir2|^2 := by rw [sq_abs]
    rw [h]; nlinarith
  have hdir01_sq : dir0^2 + dir1^2 ≤ 3/4 := by nlinarith [hdir]
  have h2 : |dir2*V2| ≤ |dir0*V0 + dir1*V1| + delta := by
    calc |dir2*V2|
      = |(dir0*V0 + dir1*V1 + dir2*V2) - (dir0*V0 + dir1*V1)| := by ring_nf
    _ ≤ |dir0*V0 + dir1*V1 + dir2*V2| + |dir0*V0 + dir1*V1| := by exact abs_sub _ _
    _ ≤ delta + |dir0*V0 + dir1*V1| := by linarith [h_inc]
    _ = |dir0*V0 + dir1*V1| + delta := by ring
  have h_cs_sq : (dir0*V0 + dir1*V1)^2 ≤ (dir0^2 + dir1^2)*(V0^2 + V1^2) := by
    nlinarith [sq_nonneg (dir0*V1 - dir1*V0)]
  set x : ℝ := V0^2 + V1^2 with hx_def
  have hx_nonneg : 0 ≤ x := by positivity
  have h_cs_abs : |dir0*V0 + dir1*V1| ≤ Real.sqrt (dir0^2 + dir1^2) * Real.sqrt x := by
    have h1 : (dir0*V0 + dir1*V1)^2 ≤ (dir0^2 + dir1^2)*x := by
      simpa [hx_def] using h_cs_sq
    have h2 : |dir0*V0 + dir1*V1|^2 ≤ (Real.sqrt (dir0^2 + dir1^2) * Real.sqrt x)^2 := by
      have h3 : (Real.sqrt (dir0^2 + dir1^2) * Real.sqrt x)^2 = (dir0^2 + dir1^2)*x := by
        rw [←Real.sqrt_mul (by positivity), Real.sq_sqrt (by positivity)]
      rw [h3]
      simpa [sq_abs] using h1
    have h4 : 0 ≤ |dir0*V0 + dir1*V1| := by positivity
    have h5 : 0 ≤ Real.sqrt (dir0^2 + dir1^2) * Real.sqrt x := by positivity
    nlinarith
  have h4 : Real.sqrt (dir0^2 + dir1^2) ≤ Real.sqrt (3/4) := Real.sqrt_le_sqrt hdir01_sq
  have h_bound : |dir0*V0 + dir1*V1| ≤ Real.sqrt (3/4) * Real.sqrt x := by
    have hpos : 0 ≤ Real.sqrt x := by positivity
    calc |dir0*V0 + dir1*V1|
      ≤ Real.sqrt (dir0^2 + dir1^2) * Real.sqrt x := h_cs_abs
    _ ≤ Real.sqrt (3/4) * Real.sqrt x := by exact mul_le_mul_of_nonneg_right h4 hpos
  have hV2_bound : |V2| ≤ 2 * (Real.sqrt (3/4) * Real.sqrt x + delta) := by
    have h6 : |dir2*V2| = |dir2| * |V2| := by rw [abs_mul]
    rw [h6] at h2
    have h7 : (1/2:ℝ) * |V2| ≤ |dir2| * |V2| := by
      have h8 : (1/2:ℝ) ≤ |dir2| := hdir_vert
      have h9 : 0 ≤ |V2| := abs_nonneg _
      nlinarith
    have h10 : |V2| ≤ 2 * (|dir0*V0 + dir1*V1| + delta) := by linarith
    have h_sum : |dir0*V0 + dir1*V1| + delta ≤ Real.sqrt (3/4) * Real.sqrt x + delta := by
      linarith [h_bound]
    linarith
  have hV2_eq : V2^2 = 1 - x := by
    have h_eq : x + V2^2 = 1 := by
      rw [hx_def] <;> exact hV
    linarith
  have h_pos : 0 ≤ 2 * (Real.sqrt (3/4) * Real.sqrt x + delta) := by positivity
  have h_abs2 : |V2| ≤ |2 * (Real.sqrt (3/4) * Real.sqrt x + delta)| := by
    rw [abs_of_nonneg h_pos]
    exact hV2_bound
  have h5' : V2^2 ≤ (2 * (Real.sqrt (3/4) * Real.sqrt x + delta))^2 :=
    sq_le_sq.mpr h_abs2
  have h_key : 1 - x ≤ 3*x + 8*Real.sqrt (3/4)*Real.sqrt x*delta + 4*delta^2 := by
    rw [hV2_eq] at h5'
    have h_expand := sqrt_expand_identity x delta hx_nonneg
    rw [h_expand] at h5'
    exact h5'
  have h_sqrt34_le_one : Real.sqrt (3/4) ≤ 1 := by
    rw [Real.sqrt_le_left (by positivity)] <;> norm_num
  have hx_le_one : x ≤ 1 := by
    have hV2_nonneg : 0 ≤ V2^2 := by positivity
    have h_eq : x + V2^2 = 1 := by rw [hx_def] <;> exact hV
    linarith
  have hsqrtx_le_one : Real.sqrt x ≤ 1 := by
    rw [Real.sqrt_le_left (by positivity)] <;> linarith
  have h_product : Real.sqrt (3/4) * Real.sqrt x * delta ≤ delta := by
    have h1 : Real.sqrt (3/4) * Real.sqrt x ≤ 1 := by
      calc Real.sqrt (3/4) * Real.sqrt x
        ≤ 1 * Real.sqrt x := mul_le_mul_of_nonneg_right h_sqrt34_le_one (by positivity)
      _ = Real.sqrt x := by ring
      _ ≤ 1 := hsqrtx_le_one
    have h2 : Real.sqrt (3/4) * Real.sqrt x * delta ≤ 1 * delta :=
      mul_le_mul_of_nonneg_right h1 hdelta_nonneg
    rwa [one_mul] at h2
  have h9 : 1 - x ≤ 3*x + 8*delta + 4*delta^2 := by
    have h10 : 8*Real.sqrt (3/4)*Real.sqrt x*delta ≤ 8*delta := by
      have h101 : Real.sqrt (3/4)*Real.sqrt x*delta ≤ delta := h_product
      have h : 8 * (Real.sqrt (3/4)*Real.sqrt x*delta) ≤ 8 * delta :=
        mul_le_mul_of_nonneg_left h101 (by norm_num)
      simpa [mul_assoc] using h
    linarith [h_key, h10]
  have h11 : delta^2 ≤ delta := by nlinarith [hdelta_small, hdelta_nonneg]
  nlinarith

/-- Pure scalar lemma: from V0^2+V1^2 lower bound, grain perpendicularity, and
    narrow slab, derive |V1 - a*V0| ≥ 1/16. -/
private lemma scalar_v1_minus_a_v0_lower_bound
    (V0 V1 delta gz a : ℝ)
    (hV01 : V0^2 + V1^2 ≥ 1/4 - 8*delta)
    (hV01_le_one : V0^2 + V1^2 ≤ 1)
    (h_grain : |V0 + gz*V1| ≤ delta)
    (hg_bound : |gz| ≤ 1)
    (ha_bound : |a| ≤ 1)
    (h_g_close : |gz - a| ≤ 1/2)
    (hdelta_small : delta ≤ 1/100) :
    |V1 - a*V0| ≥ 1/16 := by
  have hdelta_nonneg : 0 ≤ delta := le_trans (abs_nonneg _) h_grain
  set e : ℝ := V0 + gz*V1 with he_def
  have he_abs : |e| ≤ delta := h_grain
  have hV0_eq : V0 = e - gz*V1 := by
    simp [he_def] <;> ring
  -- Step 1: |V1| ≥ 1/4 by contradiction
  have h18 : |V1| ≥ 1/4 := by
    by_contra h
    have h_lt : |V1| < 1/4 := by linarith [abs_nonneg V1]
    have hV1_sq : V1^2 < 1/16 := by
      have h1 : |V1|^2 < (1/4:ℝ)^2 := by gcongr
      have h2 : |V1|^2 = V1^2 := by rw [sq_abs]
      rw [h2] at h1
      have h3 : (1/4:ℝ)^2 = 1/16 := by norm_num
      rw [h3] at h1
      exact h1
    have hV0_abs : |V0| ≤ delta + 1/4 := by
      calc |V0|
        = |e - gz*V1| := by rw [hV0_eq]
      _ ≤ |e| + |gz*V1| := by exact abs_sub _ _
      _ = |e| + |gz| * |V1| := by
        have h_abs : |gz * V1| = |gz| * |V1| := abs_mul gz V1
        rw [h_abs]
      _ ≤ delta + 1*(1/4) := by gcongr <;> linarith
      _ = delta + 1/4 := by ring
    have hV0_sq : V0^2 ≤ (delta + 1/4)^2 := by
      have h : |V0|^2 ≤ (delta + 1/4)^2 := by gcongr
      have h2 : |V0|^2 = V0^2 := by rw [sq_abs]
      rw [h2] at h
      exact h
    have h_sum : V0^2 + V1^2 < (delta + 1/4)^2 + 1/16 := by linarith
    have h_contra : (delta + 1/4)^2 + 1/16 < 1/4 - 8*delta := by
      nlinarith [hdelta_small, hdelta_nonneg]
    linarith [hV01]
  -- Step 2: |1 + a*gz| ≥ 1/2
  have h25 : |1 + a*gz| ≥ 1/2 := by
    have h26 : 1 + a*gz = 1 + a^2 + a*(gz - a) := by ring
    rw [h26]
    have h27 : |a*(gz - a)| ≤ |a| * |gz - a| := by
      exact abs_mul a (gz - a) ▸ le_refl _
    have h28 : |a*(gz - a)| ≤ 1/2 := by
      calc |a*(gz - a)| ≤ |a| * |gz - a| := h27
           _ ≤ 1*(1/2) := by gcongr <;> linarith
           _ = 1/2 := by ring
    have h29 : 1 + a^2 ≥ 1 := by nlinarith
    have h29' : |1 + a^2| = 1 + a^2 := abs_of_nonneg (by linarith)
    have h30 : |1 + a^2 + a*(gz - a)| ≥ 1/2 := by
      have h31 : |1 + a^2 + a*(gz - a)| ≥ |1 + a^2| - |a*(gz - a)| := by
        have h_eq : |1 + a^2| = |(1 + a^2 + a*(gz - a)) - a*(gz - a)| := by ring_nf
        rw [h_eq]
        have h_tri : |(1 + a^2 + a*(gz - a)) - a*(gz - a)| ≤
            |1 + a^2 + a*(gz - a)| + |a*(gz - a)| := abs_sub _ _
        linarith
      linarith [h29', h28]
    exact h30
  -- Step 3: |V1 - a*V0| ≥ 1/16
  set y : ℝ := V1 - a*V0 with hy_def
  have h24 : y = V1*(1 + a*gz) - a*e := by
    rw [hy_def, hV0_eq] <;> ring
  have h32 : |y| ≥ |V1| * |1 + a*gz| - |a| * |e| := by
    rw [h24]
    have h_rev : |V1*(1 + a*gz) - a*e| ≥ |V1*(1 + a*gz)| - |a*e| := by
      let u := V1*(1 + a*gz)
      let v := a*e
      have h1 : |u| ≤ |u - v| + |v| := by
        calc |u| = |(u - v) + v| := by ring_nf
             _ ≤ |u - v| + |v| := by exact abs_add_le (u - v) v
      linarith
    have h1 : |V1 * (1 + a*gz)| = |V1| * |1 + a*gz| := abs_mul V1 (1 + a*gz)
    have h2 : |a * e| = |a| * |e| := abs_mul a e
    linarith
  have h33 : |y| ≥ 1/8 - delta := by
    have h_mul : |V1| * |1 + a*gz| ≥ 1/8 := by
      have h_pos1 : 0 ≤ |V1| := abs_nonneg V1
      have h_pos2 : 0 ≤ |1 + a*gz| := abs_nonneg (1 + a*gz)
      nlinarith [h18, h25]
    have h_sub : |a| * |e| ≤ delta := by
      have h_pos : 0 ≤ |a| := abs_nonneg a
      nlinarith [ha_bound, he_abs, abs_nonneg e]
    have h : |V1| * |1 + a*gz| - |a| * |e| ≥ 1/8 - delta := by linarith
    linarith [h32, h]
  have h34 : |y| ≥ 1/16 := by
    have h35 : 1/8 - delta ≥ 1/16 := by linarith [hdelta_small]
    linarith [h33, h35]
  exact h34

/-- Lower bound on ‖DΦ^{-T}·V‖ using grain perpendicularity and tube incidence.

Given V unit, a tube direction dir in the vertical chart with small incidence,
grain perpendicularity |V0 + g(z)·V1| ≤ delta, narrow slab |g(z)-g(center)| ≤ 1/2,
and b = m*(d-c)/2 ≤ 1/50, then ‖DΦ^{-T}·V‖ ≥ 25/8 ≥ 1. -/
lemma dPhiInvT_norm_lower_bound
    {delta : ℝ}
    {V : Point3} (hV_unit : ‖V‖ = 1)
    {dir : Point3} (hdir_unit : ‖dir‖ = 1)
    (hdir_vert : 1 / 2 ≤ |dir 2|)
    (h_incidence : |inner ℝ dir V| ≤ delta)
    {z : ℝ} (h_grain_perp : |V 0 + g z * V 1| ≤ delta)
    (hg_bound : |g z| ≤ 1)
    (hcd : c < d) (hm : 0 < m)
    (h_a_bound : |g (c + (d - c) / 2)| ≤ 1)
    (h_g_close : |g z - g (c + (d - c) / 2)| ≤ 1 / 2)
    (hdelta_small : delta ≤ 1 / 100)
    (hb_le : m * (d - c) / 2 ≤ 1 / 50) :
    1 ≤ ‖dPhiInvT g c d m V‖ := by
  set a : ℝ := g (c + (d - c) / 2) with ha_def
  set b : ℝ := m * (d - c) / 2 with hb_def
  have hb_pos : 0 < b := by rw [hb_def] <;> positivity
  have ha_bound : |a| ≤ 1 := by rw [ha_def] <;> exact h_a_bound
  have h_g_close' : |g z - a| ≤ 1 / 2 := by rw [ha_def] <;> exact h_g_close
  have hV : V 0 ^ 2 + V 1 ^ 2 + V 2 ^ 2 = 1 := by
    have h : ‖V‖ ^ 2 = V 0 ^ 2 + V 1 ^ 2 + V 2 ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq] <;> simp [Fin.sum_univ_succ] <;> ring
    have h' : ‖V‖ ^ 2 = 1 := by rw [hV_unit] <;> norm_num
    linarith
  have hdir : dir 0 ^ 2 + dir 1 ^ 2 + dir 2 ^ 2 = 1 := by
    have h : ‖dir‖ ^ 2 = dir 0 ^ 2 + dir 1 ^ 2 + dir 2 ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq] <;> simp [Fin.sum_univ_succ] <;> ring
    have h' : ‖dir‖ ^ 2 = 1 := by rw [hdir_unit] <;> norm_num
    linarith
  have h_inner_expand : inner ℝ dir V = dir 0 * V 0 + dir 1 * V 1 + dir 2 * V 2 := by
    simp [inner, Fin.sum_univ_succ] <;> ring
  have h_inc' : |dir 0 * V 0 + dir 1 * V 1 + dir 2 * V 2| ≤ delta := by
    rw [←h_inner_expand] <;> exact h_incidence
  have hV01_sq : V 0 ^ 2 + V 1 ^ 2 ≥ 1 / 4 - 8 * delta :=
    scalar_v01_lower_bound (V 0) (V 1) (V 2) (dir 0) (dir 1) (dir 2) delta
      hV hdir hdir_vert h_inc' hdelta_small
  have hV01_le_one : V 0 ^ 2 + V 1 ^ 2 ≤ 1 := by
    have h : V 2 ^ 2 ≥ 0 := by positivity
    linarith [hV]
  have hy : |V 1 - a * V 0| ≥ 1 / 16 :=
    scalar_v1_minus_a_v0_lower_bound (V 0) (V 1) delta (g z) a
      hV01_sq hV01_le_one h_grain_perp hg_bound ha_bound h_g_close' hdelta_small
  set W : Point3 := dPhiInvT g c d m V with hW_def
  have hW1 : W 1 = (V 1 - a * V 0) / b := by
    simp [hW_def, dPhiInvT, point3] <;> ring
  have h35 : |W 1| = |V 1 - a * V 0| / b := by
    rw [hW1, abs_div] <;> rw [abs_of_pos hb_pos]
  have h36 : |W 1| ≥ (1 / 16 : ℝ) / b := by
    rw [h35] <;> gcongr
  have h37 : |W 1| ≤ ‖W‖ :=
    PiLp.norm_apply_le W 1
  have h38 : ‖W‖ ≥ (1 / 16 : ℝ) / b := by linarith
  have h39 : (1 / 16 : ℝ) / b ≥ 25 / 8 := by
    have h40 : b ≤ 1 / 50 := hb_le
    have h41 : 0 < b := hb_pos
    calc (1 / 16 : ℝ) / b ≥ (1 / 16 : ℝ) / (1 / 50 : ℝ) := by gcongr
         _ = 25 / 8 := by norm_num
  linarith

end Kakeya.Assouad

end
