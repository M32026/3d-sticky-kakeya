import MyLeanRepo.Kakeya.Assouad.WZ1.LocalGrainCubeCountStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.CordobaL2
import MyLeanRepo.Kakeya.Assouad.WZ1.SeparatedPointsExtraction
import MyLeanRepo.Kakeya.Assouad.WZ1.ImprovedSeparatedPoints
import MyLeanRepo.Kakeya.Assouad.WZ1.PairwiseIntersection
import MyLeanRepo.Kakeya.Assouad.WZ1.SlabContainment
import MyLeanRepo.Kakeya.Assouad.WZ1.DirectionBound
import MyLeanRepo.Kakeya.Assouad.WZ1.CordobaAssemblyHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.CordobaLogAbsorptionStatement
import MyLeanRepo.Kakeya.Assouad.WZ1.CordobaSeparatedCardinality
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic

/-!
# WZ1 Lemma 17 Córdoba slab lower bound - full assembly

Uses C = 504*rho²*tau for uniform pairwise intersection bound.
-/

noncomputable section

namespace Kakeya.Assouad

open Kakeya.Streamlined Metric MeasureTheory Finset

/-- Perpendicular distance from a tube point to the tube axis line is ≤ δ. -/
lemma tube_perp_bound {δ : ℝ} (hδ_pos : 0 < δ) (T : DeltaTube δ) (z : Point3)
    (hz : z ∈ T.carrier) :
    ‖z - (T.base + inner ℝ (z - T.base) T.direction • T.direction)‖ ≤ δ := by
  let S : Set Point3 := unitSegment T.base T.direction
  have hS_compact : IsCompact S := by
    apply IsCompact.image (isCompact_Icc)
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hS_nonempty : S.Nonempty := by
    refine ⟨T.base + (0 : ℝ) • T.direction, ?_⟩
    exact ⟨0, by norm_num, by simp⟩
  have h1 : z ∈ Metric.cthickening δ S := hz
  have h2 : Metric.infEDist z S ≤ ENNReal.ofReal δ := Metric.mem_cthickening_iff.mp h1
  have h3 : Metric.infEDist z S ≠ ⊤ := Metric.infEDist_ne_top hS_nonempty
  have h4 : Metric.infDist z S ≤ δ := by
    have h5 : Metric.infDist z S = (Metric.infEDist z S).toReal := by rfl
    rw [h5]
    have h6 : (Metric.infEDist z S).toReal ≤ (ENNReal.ofReal δ).toReal :=
      ENNReal.toReal_mono (by simp) h2
    have h7 : (ENNReal.ofReal δ).toReal = δ := by
      simp [hδ_pos.le]
    rw [h7] at h6
    exact h6
  rcases hS_compact.exists_infDist_eq_dist hS_nonempty z with ⟨y_pt, hy_pt, h6⟩
  have hdist : dist z y_pt ≤ δ := by
    rw [← h6] <;> exact h4
  have h_y_img : ∃ (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 ∧ T.base + t • T.direction = y_pt := by
    simpa [S, unitSegment] using hy_pt
  rcases h_y_img with ⟨t, _ht, rfl⟩
  let y_pt' : Point3 := T.base + t • T.direction
  let a : ℝ := inner ℝ (z - T.base) T.direction
  let proj_z : Point3 := T.base + a • T.direction
  have h_orth : inner ℝ (z - proj_z) (proj_z - y_pt') = 0 := by
    have h1 : proj_z - y_pt' = (a - t) • T.direction := by
      have h11 : proj_z - y_pt' = a • T.direction - t • T.direction := by
        simp [proj_z, y_pt'] <;> abel
      rw [h11]
      rw [sub_smul]
    rw [h1]
    have h2 : inner ℝ (z - proj_z) ((a - t) • T.direction) =
        (a - t) * inner ℝ (z - proj_z) T.direction := by
      rw [inner_smul_right] <;> ring
    rw [h2]
    have h3 : inner ℝ (z - proj_z) T.direction = 0 := by
      have h4 : z - proj_z = (z - T.base) - a • T.direction := by
        simp [proj_z] <;> abel
      rw [h4]
      have h5 : inner ℝ ((z - T.base) - a • T.direction) T.direction =
          inner ℝ (z - T.base) T.direction - inner ℝ (a • T.direction) T.direction := by
        rw [inner_sub_left]
      rw [h5]
      have h6 : inner ℝ (a • T.direction) T.direction = a * inner ℝ T.direction T.direction := by
        simpa [inner_smul_left] using rfl
      have h7 : inner ℝ T.direction T.direction = 1 := by
        have h8 : inner ℝ T.direction T.direction = ‖T.direction‖ ^ 2 := by
          exact real_inner_self_eq_norm_sq T.direction
        rw [h8, T.direction_unit] <;> norm_num
      rw [h6, h7]
      <;> simp [a] <;> ring
    rw [h3] <;> ring
  have h_pyth : ‖z - y_pt'‖^2 = ‖z - proj_z‖^2 + ‖proj_z - y_pt'‖^2 := by
    have h_eq : z - y_pt' = (z - proj_z) + (proj_z - y_pt') := by abel
    rw [h_eq]
    have h := norm_add_sq_real (z - proj_z) (proj_z - y_pt')
    rw [h, h_orth] <;> ring
  have h_nonneg : 0 ≤ ‖proj_z - y_pt'‖^2 := by positivity
  have h2 : ‖z - proj_z‖^2 ≤ ‖z - y_pt'‖^2 := by
    rw [h_pyth] <;> linarith
  have h3 : 0 ≤ ‖z - proj_z‖ := by positivity
  have h4 : 0 ≤ ‖z - y_pt'‖ := by positivity
  have h5 : ‖z - y_pt'‖ ≤ δ := by
    simpa [dist_eq_norm] using hdist
  nlinarith

/-- Axial separation of two points in same tube: ≥ sep/2 when δ small enough. -/
lemma axial_separation_two_points
    {δ sep : ℝ} (hδ_pos : 0 < δ) (hsep_pos : 0 < sep)
    (u : Point3) (hu_unit : ‖u‖ = 1)
    (T : DeltaTube δ) (hT_dir : T.direction = u)
    (x y : Point3) (hx_in : x ∈ T.carrier) (hy_in : y ∈ T.carrier)
    (h_sep : sep ≤ dist x y)
    (h_small : 4 * δ^2 ≤ (3 / 4 : ℝ) * sep^2) :
    |inner ℝ (y - x) u| ≥ sep / 2 := by
  let v : Point3 := y - x
  let d : ℝ := inner ℝ v u
  let proj_x : Point3 := T.base + inner ℝ (x - T.base) u • u
  let proj_y : Point3 := T.base + inner ℝ (y - T.base) u • u
  have h_perp_x : ‖x - proj_x‖ ≤ δ := by
    simpa [proj_x, hT_dir] using tube_perp_bound hδ_pos T x hx_in
  have h_perp_y : ‖y - proj_y‖ ≤ δ := by
    simpa [proj_y, hT_dir] using tube_perp_bound hδ_pos T y hy_in
  have h_proj_diff : proj_y - proj_x = d • u := by
    have h11 : proj_y - proj_x =
        (inner ℝ (y - T.base) u) • u - (inner ℝ (x - T.base) u) • u := by
      dsimp only [proj_y, proj_x]
      abel
    have h12 : (inner ℝ (y - T.base) u) • u - (inner ℝ (x - T.base) u) • u =
        (inner ℝ (y - T.base) u - inner ℝ (x - T.base) u) • u := by
      rw [sub_smul]
    have h13 : inner ℝ (y - T.base) u - inner ℝ (x - T.base) u = inner ℝ (y - x) u := by
      have h14 : inner ℝ (y - T.base) u - inner ℝ (x - T.base) u =
          inner ℝ ((y - T.base) - (x - T.base)) u := by
        rw [← inner_sub_left]
      rw [h14]
      have h15 : (y - T.base) - (x - T.base) = y - x := by abel
      rw [h15]
    calc proj_y - proj_x
      = (inner ℝ (y - T.base) u) • u - (inner ℝ (x - T.base) u) • u := h11
    _ = (inner ℝ (y - T.base) u - inner ℝ (x - T.base) u) • u := h12
    _ = (inner ℝ (y - x) u) • u := by rw [h13]
    _ = d • u := by rfl
  let e : Point3 := v - d • u
  have h_e_eq : e = (y - proj_y) - (x - proj_x) := by
    dsimp only [e]
    have h1 : v - d • u = (y - x) - (proj_y - proj_x) := by
      rw [h_proj_diff] <;> rfl
    rw [h1] <;> abel
  have h_trans : ‖e‖ ≤ 2 * δ := by
    rw [h_e_eq]
    calc ‖(y - proj_y) - (x - proj_x)‖
      ≤ ‖y - proj_y‖ + ‖x - proj_x‖ := norm_sub_le _ _
    _ ≤ δ + δ := by gcongr
    _ = 2 * δ := by ring
  have h_orth : inner ℝ e u = 0 := by
    have h : inner ℝ (v - d • u) u = inner ℝ v u - inner ℝ (d • u) u := by
      rw [inner_sub_left]
    have h2 : inner ℝ (d • u) u = d * inner ℝ u u := by
      simpa [inner_smul_left] using rfl
    have h3 : inner ℝ u u = 1 := by
      have h4 : inner ℝ u u = ‖u‖ ^ 2 := by
        exact real_inner_self_eq_norm_sq u
      rw [h4, hu_unit] <;> norm_num
    dsimp only [e]
    rw [h, h2, h3] <;> simp [d] <;> ring
  have h_pyth : ‖v‖^2 = d^2 + ‖e‖^2 := by
    have h1 : v = d • u + e := by
      simp [e] <;> abel
    rw [h1]
    have h2 : inner ℝ (d • u) e = 0 := by
      have h21 : inner ℝ (d • u) e = d * inner ℝ u e := by
        simpa [inner_smul_left] using rfl
      rw [h21]
      have h22 : inner ℝ u e = inner ℝ e u := by
        exact real_inner_comm e u
      rw [h22, h_orth] <;> ring
    have h3 : ‖d • u + e‖^2 = ‖d • u‖^2 + ‖e‖^2 := by
      have h4 := norm_add_sq_eq_norm_sq_add_norm_sq_real h2
      have h5 : ‖d • u + e‖ * ‖d • u + e‖ = ‖d • u‖^2 + ‖e‖^2 := by
        rw [h4] <;> ring
      have h6 : ‖d • u + e‖^2 = ‖d • u + e‖ * ‖d • u + e‖ := by ring
      rw [h6, h5]
    rw [h3]
    have h7 : ‖d • u‖ = |d| := by
      have h71 : ‖d • u‖ = ‖d‖ * ‖u‖ := by
        simpa using norm_smul d u
      have h72 : ‖d‖ = |d| := by simp
      rw [h71, h72, hu_unit] <;> ring
    rw [h7]
    have h8 : |d|^2 = d^2 := by
      rw [sq_abs]
    rw [h8] <;> ring
  have h1 : ‖v‖^2 ≥ sep^2 := by
    have h2 : sep ≤ ‖v‖ := by
      have h3 : dist x y = ‖x - y‖ := by
        exact dist_eq_norm x y
      have h4 : ‖x - y‖ = ‖y - x‖ := by
        rw [norm_sub_rev]
      rw [h3, h4] at h_sep
      exact h_sep
    have h4 : 0 ≤ sep := by linarith
    have h5 : ‖v‖^2 ≥ sep^2 := by
      have h6 : 0 ≤ ‖v‖ := by positivity
      nlinarith
    exact h5
  have h_trans2 : ‖e‖^2 ≤ (2 * δ)^2 := by
    have h5 : ‖e‖ ≤ 2 * δ := h_trans
    have h6 : 0 ≤ ‖e‖ := by positivity
    nlinarith
  have h3 : d^2 ≥ sep^2 - (2 * δ)^2 := by
    have h7 : ‖v‖^2 = d^2 + ‖e‖^2 := h_pyth
    nlinarith
  have h4 : sep^2 - (2 * δ)^2 ≥ (sep / 2)^2 := by
    nlinarith [h_small]
  have h5 : d^2 ≥ (sep / 2)^2 := by linarith
  have h6 : |d| ≥ sep / 2 := by
    by_cases h7 : 0 ≤ d
    · have h8 : d ≥ sep / 2 := by nlinarith
      have h9 : |d| = d := abs_of_nonneg h7
      rw [h9] <;> linarith
    · have h8 : d < 0 := by linarith
      have h9 : d ≤ -sep / 2 := by nlinarith
      have h10 : |d| = -d := abs_of_neg h8
      rw [h10] <;> linarith
  exact h6

/-- Amplify log absorption from half-epsilon bracket 8+64 to full-epsilon bracket 8+1008. -/
lemma log_absorption_amplified
    {rho : ℝ} {k : ℕ} {epsilon₁ : ℝ}
    (hrho_pos : 0 < rho)
    (hk_pos : 0 < k)
    (h_log_half :
      Real.rpow rho (epsilon₁ / 2) * (8 + 64 * (1 + Real.log (k : ℝ))) ≤ 125 / 3)
    (hrho_amplified : Real.rpow rho (epsilon₁ / 2) ≤ 4 / 63) :
    Real.rpow rho epsilon₁ * (8 + 1008 * (1 + Real.log (k : ℝ))) ≤ 125 / 3 := by
  set A : ℝ := 8 + 64 * (1 + Real.log (k : ℝ)) with hA_def
  set B : ℝ := 8 + 1008 * (1 + Real.log (k : ℝ)) with hB_def
  set r : ℝ := Real.rpow rho (epsilon₁ / 2) with hr_def
  have hk_one : (k : ℝ) ≥ 1 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk_pos.ne')
  have hlog_nonneg : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk_one
  have hA_pos : 0 < A := by positivity
  have hB_pos : 0 < B := by positivity
  have hr_pos : 0 < r := Real.rpow_pos_of_pos hrho_pos _
  have hB_le : B ≤ (63 / 4 : ℝ) * A := by
    rw [hB_def, hA_def]
    have h : (63 / 4 : ℝ) * (8 + 64 * (1 + Real.log (k : ℝ))) =
        126 + 1008 * (1 + Real.log (k : ℝ)) := by ring
    rw [h] <;> linarith
  have hrpow_eps : Real.rpow rho epsilon₁ = r * r := by
    have h_sum : epsilon₁ / 2 + epsilon₁ / 2 = epsilon₁ := by ring
    have h : Real.rpow rho (epsilon₁ / 2 + epsilon₁ / 2) =
        Real.rpow rho (epsilon₁ / 2) * Real.rpow rho (epsilon₁ / 2) :=
      Real.rpow_add hrho_pos _ _
    rw [h_sum] at h <;> simpa [hr_def] using h
  rw [hrpow_eps]
  have h_main : r * r * B ≤ 125 / 3 := by
    calc
      r * r * B
        ≤ r * r * ((63 / 4 : ℝ) * A) := by gcongr
      _ = (63 / 4 : ℝ) * r * (r * A) := by ring
      _ ≤ (63 / 4 : ℝ) * r * (125 / 3) := by
          have h3 : r * A ≤ 125 / 3 := h_log_half
          have h4 : 0 ≤ (63 / 4 : ℝ) * r := by positivity
          nlinarith
      _ ≤ (63 / 4 : ℝ) * (4 / 63 : ℝ) * (125 / 3) := by
          have h5 : r ≤ 4 / 63 := hrho_amplified
          have h6 : 0 ≤ (125 / 3 : ℝ) := by norm_num
          nlinarith
      _ = 125 / 3 := by ring
  exact h_main

/-- Final arithmetic lemma for Córdoba slab lower bound with C = 504. -/
lemma cordoba_final_arithmetic_C504
    {rho tau epsilon₁ epsilon₃ : ℝ}
    {k : ℕ}
    (hrho_pos : 0 < rho)
    (hrho_le_one : rho ≤ 1)
    (htau_pos : 0 < tau)
    (heps₁_pos : 0 < epsilon₁)
    (heps₃_pos : 0 < epsilon₃)
    (hk_pos : 0 < k)
    (hk_lower : (k : ℝ) ≥ (5 : ℝ) / 24 * Real.rpow rho (2 * epsilon₁ - 1 + epsilon₃) * tau)
    (h_log : Real.rpow rho epsilon₁ * (8 + 1008 * (1 + Real.log (k : ℝ))) ≤ 125 / 3) :
    ENNReal.ofReal ((k : ℝ)^2 * (Real.rpow rho (2 + 2 * epsilon₁) * tau)^2) /
    ENNReal.ofReal ((k : ℝ) * (8 * rho^2 * tau) +
      2 * (504 * rho^2 * tau) * (k : ℝ) * (1 + Real.log (k : ℝ))) ≥
    Kakeya.realRpowENN rho (1 + 7 * epsilon₁ + epsilon₃) *
    ENNReal.ofReal (tau^2 / 200) := by
  set kR : ℝ := (k : ℝ) with hkR
  have hkR_pos : 0 < kR := by
    have h : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
    simpa [hkR] using h
  have hkR_one : 1 ≤ kR := by
    have h : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k from hk_pos)
    simpa [hkR] using h
  have hlog_nonneg : 0 ≤ Real.log kR := Real.log_nonneg hkR_one
  set V : ℝ := Real.rpow rho (2 + 2 * epsilon₁) * tau with hV
  set V' : ℝ := 8 * rho^2 * tau with hV'
  set C : ℝ := 504 * rho^2 * tau with hC
  have hV_pos : 0 < V := mul_pos (Real.rpow_pos_of_pos hrho_pos _) htau_pos
  have hV'_pos : 0 < V' := by rw [hV'] <;> positivity
  have hC_pos : 0 < C := by rw [hC] <;> positivity
  set D : ℝ := kR * V' + 2 * C * kR * (1 + Real.log kR) with hD
  have hD_pos : 0 < D := by positivity
  have h_rpow_div : ∀ (a b : ℝ),
      Real.rpow rho a / Real.rpow rho b = Real.rpow rho (a - b) := by
    intro a b
    have h_pos_b : 0 < Real.rpow rho b := Real.rpow_pos_of_pos hrho_pos _
    have h_add : Real.rpow rho ((a - b) + b) =
        Real.rpow rho (a - b) * Real.rpow rho b := Real.rpow_add hrho_pos (a - b) b
    have h_eq : (a - b) + b = a := by ring
    have h9 : Real.rpow rho a = Real.rpow rho (a - b) * Real.rpow rho b := by
      have h10 : Real.rpow rho ((a - b) + b) = Real.rpow rho a := by rw [h_eq]
      exact h10.symm.trans h_add
    rw [h9] <;> field_simp [h_pos_b.ne'] <;> ring
  have h_rpow_mul : ∀ (a b : ℝ),
      Real.rpow rho a * Real.rpow rho b = Real.rpow rho (a + b) := by
    intro a b; exact (Real.rpow_add hrho_pos a b).symm
  have hD_factor : D = kR * rho^2 * tau * (8 + 1008 * (1 + Real.log kR)) := by
    dsimp only [D, V', C] <;> ring
  have h_bracket : 8 + 1008 * (1 + Real.log kR) ≤ (125 / 3 : ℝ) / Real.rpow rho epsilon₁ := by
    have h_rpos : 0 < Real.rpow rho epsilon₁ := Real.rpow_pos_of_pos hrho_pos _
    calc
      8 + 1008 * (1 + Real.log kR)
        = (Real.rpow rho epsilon₁ * (8 + 1008 * (1 + Real.log kR))) / Real.rpow rho epsilon₁ := by
          field_simp [h_rpos.ne'] <;> ring
      _ ≤ (125 / 3 : ℝ) / Real.rpow rho epsilon₁ := by gcongr
  have h_exp2 : rho^2 = Real.rpow rho 2 := by simp
  have h_rpow2_pos : 0 < Real.rpow rho 2 := Real.rpow_pos_of_pos hrho_pos _
  have h_rpow2me1_pos : 0 < Real.rpow rho (2 - epsilon₁) := Real.rpow_pos_of_pos hrho_pos _
  have h_rpow4_pos : 0 < Real.rpow rho (4 + 4 * epsilon₁) := Real.rpow_pos_of_pos hrho_pos _
  have hD_le : D ≤ kR * (125 / 3 : ℝ) * Real.rpow rho (2 - epsilon₁) * tau := by
    have hpos : 0 ≤ kR * Real.rpow rho 2 * tau := by
      exact mul_nonneg (mul_nonneg hkR_pos.le h_rpow2_pos.le) htau_pos.le
    have h_goal : kR * rho^2 * tau * (8 + 1008 * (1 + Real.log kR)) ≤
        kR * (125 / 3 : ℝ) * Real.rpow rho (2 - epsilon₁) * tau := by
      calc
        kR * rho^2 * tau * (8 + 1008 * (1 + Real.log kR))
          = kR * Real.rpow rho 2 * tau * (8 + 1008 * (1 + Real.log kR)) := by rw [h_exp2]
        _ ≤ kR * Real.rpow rho 2 * tau * ((125 / 3 : ℝ) / Real.rpow rho epsilon₁) := by
          exact mul_le_mul_of_nonneg_left h_bracket hpos
        _ = kR * (125 / 3 : ℝ) * (Real.rpow rho 2 / Real.rpow rho epsilon₁) * tau := by ring
        _ = kR * (125 / 3 : ℝ) * Real.rpow rho (2 - epsilon₁) * tau := by
          rw [h_rpow_div 2 epsilon₁] <;> ring
    rw [hD_factor]; exact h_goal
  set N : ℝ := kR^2 * V^2 with hN
  have hN_pos : 0 < N := by positivity
  have hV2 : V^2 = Real.rpow rho (4 + 4 * epsilon₁) * tau^2 := by
    rw [hV]
    have h1 : (Real.rpow rho (2 + 2 * epsilon₁) * tau)^2 =
        (Real.rpow rho (2 + 2 * epsilon₁))^2 * tau^2 := by ring
    rw [h1]
    have h_sq : (Real.rpow rho (2 + 2 * epsilon₁))^2 =
        Real.rpow rho (2 + 2 * epsilon₁) * Real.rpow rho (2 + 2 * epsilon₁) := by ring
    rw [h_sq, h_rpow_mul (2 + 2 * epsilon₁) (2 + 2 * epsilon₁)] <;> ring
  have h_k_term : kR ≥ (5 : ℝ) / 24 * Real.rpow rho (2 * epsilon₁ - 1 + epsilon₃) * tau := hk_lower
  have h_part1 : kR * V^2 / D ≥ (3 : ℝ) / 125 * Real.rpow rho (2 + 5 * epsilon₁) * tau := by
    rw [hV2]
    have h_num_pos : 0 < kR * (Real.rpow rho (4 + 4 * epsilon₁) * tau^2) :=
      mul_pos hkR_pos (mul_pos h_rpow4_pos (pow_pos htau_pos 2))
    have h_denom'_pos : 0 < kR * (125 / 3 : ℝ) * Real.rpow rho (2 - epsilon₁) * tau :=
      mul_pos (mul_pos (mul_pos hkR_pos (by norm_num)) h_rpow2me1_pos) htau_pos
    calc
      kR * (Real.rpow rho (4 + 4 * epsilon₁) * tau^2) / D
        ≥ kR * (Real.rpow rho (4 + 4 * epsilon₁) * tau^2) /
            (kR * (125 / 3 : ℝ) * Real.rpow rho (2 - epsilon₁) * tau) := by
          exact div_le_div_of_nonneg_left h_num_pos.le hD_pos hD_le
      _ = (Real.rpow rho (4 + 4 * epsilon₁) * tau^2) /
            ((125 / 3 : ℝ) * Real.rpow rho (2 - epsilon₁) * tau) := by
          field_simp [hkR_pos.ne'] <;> ring
      _ = (3 : ℝ) / 125 * (Real.rpow rho (4 + 4 * epsilon₁) / Real.rpow rho (2 - epsilon₁)) * tau := by
          field_simp [h_rpow2me1_pos.ne'] <;> ring
      _ = (3 : ℝ) / 125 * Real.rpow rho ((4 + 4 * epsilon₁) - (2 - epsilon₁)) * tau := by
          rw [h_rpow_div (4 + 4 * epsilon₁) (2 - epsilon₁)] <;> ring
      _ = (3 : ℝ) / 125 * Real.rpow rho (2 + 5 * epsilon₁) * tau := by
          have h_exp : (4 + 4 * epsilon₁) - (2 - epsilon₁) = 2 + 5 * epsilon₁ := by ring
          rw [h_exp] <;> ring
  have h_main : N / D ≥
      (5 : ℝ) / 24 * Real.rpow rho (2 * epsilon₁ - 1 + epsilon₃) * tau *
        ((3 : ℝ) / 125 * Real.rpow rho (2 + 5 * epsilon₁) * tau) := by
    have hN2 : N = kR * (kR * V^2) := by ring
    rw [hN2]
    have h1 : kR * (kR * V^2) / D = kR * (kR * V^2 / D) := by
      field_simp [hD_pos.ne'] <;> ring
    rw [h1]
    have h2 : kR * (kR * V^2 / D) ≥ kR * ((3 : ℝ) / 125 * Real.rpow rho (2 + 5 * epsilon₁) * tau) := by
      exact mul_le_mul_of_nonneg_left h_part1 hkR_pos.le
    have h3 : kR * ((3 : ℝ) / 125 * Real.rpow rho (2 + 5 * epsilon₁) * tau) ≥
        (5 : ℝ) / 24 * Real.rpow rho (2 * epsilon₁ - 1 + epsilon₃) * tau *
          ((3 : ℝ) / 125 * Real.rpow rho (2 + 5 * epsilon₁) * tau) := by
      have h41 : 0 ≤ (3 : ℝ) / 125 := by norm_num
      have h42 : 0 < Real.rpow rho (2 + 5 * epsilon₁) := Real.rpow_pos_of_pos hrho_pos _
      have h4 : 0 ≤ (3 : ℝ) / 125 * Real.rpow rho (2 + 5 * epsilon₁) * tau := by
        exact mul_nonneg (mul_nonneg h41 h42.le) htau_pos.le
      exact mul_le_mul_of_nonneg_right h_k_term h4
    exact calc
      kR * (kR * V^2 / D)
        ≥ kR * ((3 : ℝ) / 125 * Real.rpow rho (2 + 5 * epsilon₁) * tau) := h2
      _ ≥ (5 : ℝ) / 24 * Real.rpow rho (2 * epsilon₁ - 1 + epsilon₃) * tau *
            ((3 : ℝ) / 125 * Real.rpow rho (2 + 5 * epsilon₁) * tau) := h3
  have h_ratio : N / D ≥ Real.rpow rho (1 + 7 * epsilon₁ + epsilon₃) * tau^2 / 200 := by
    have h_exp_eq : (2 * epsilon₁ - 1 + epsilon₃) + (2 + 5 * epsilon₁) = 1 + 7 * epsilon₁ + epsilon₃ := by ring
    have h_exp_final : Real.rpow rho (2 * epsilon₁ - 1 + epsilon₃) * Real.rpow rho (2 + 5 * epsilon₁) =
        Real.rpow rho (1 + 7 * epsilon₁ + epsilon₃) := by
      rw [h_rpow_mul (2 * epsilon₁ - 1 + epsilon₃) (2 + 5 * epsilon₁)]
      rw [h_exp_eq]
    have h_rhs_rearrange : (5 : ℝ) / 24 * Real.rpow rho (2 * epsilon₁ - 1 + epsilon₃) * tau *
          ((3 : ℝ) / 125 * Real.rpow rho (2 + 5 * epsilon₁) * tau) =
        ((5 : ℝ) / 24 * (3 : ℝ) / 125) *
          (Real.rpow rho (2 * epsilon₁ - 1 + epsilon₃) * Real.rpow rho (2 + 5 * epsilon₁)) * tau^2 := by
      ring
    calc
      N / D
        ≥ (5 : ℝ) / 24 * Real.rpow rho (2 * epsilon₁ - 1 + epsilon₃) * tau *
              ((3 : ℝ) / 125 * Real.rpow rho (2 + 5 * epsilon₁) * tau) := h_main
      _ = ((5 : ℝ) / 24 * (3 : ℝ) / 125) *
            (Real.rpow rho (2 * epsilon₁ - 1 + epsilon₃) * Real.rpow rho (2 + 5 * epsilon₁)) * tau^2 := h_rhs_rearrange
      _ = ((5 : ℝ) / 24 * (3 : ℝ) / 125) *
            Real.rpow rho (1 + 7 * epsilon₁ + epsilon₃) * tau^2 := by rw [h_exp_final]
      _ = Real.rpow rho (1 + 7 * epsilon₁ + epsilon₃) * tau^2 / 200 := by norm_num <;> ring
  have hN_nonneg : 0 ≤ N := hN_pos.le
  have h_ennreal_div : ENNReal.ofReal N / ENNReal.ofReal D = ENNReal.ofReal (N / D) := by
    have h1 : (ENNReal.ofReal D)⁻¹ = ENNReal.ofReal (1 / D) := by
      have h2 : ENNReal.ofReal (D⁻¹) = (ENNReal.ofReal D)⁻¹ := ENNReal.ofReal_inv_of_pos hD_pos
      have h3 : (D⁻¹ : ℝ) = 1 / D := by simp
      rw [h3] at h2; exact h2.symm
    calc
      ENNReal.ofReal N / ENNReal.ofReal D
        = ENNReal.ofReal N * (ENNReal.ofReal D)⁻¹ := by rfl
      _ = ENNReal.ofReal N * ENNReal.ofReal (1 / D) := by rw [h1]
      _ = ENNReal.ofReal (N * (1 / D)) := by rw [← ENNReal.ofReal_mul hN_nonneg]
      _ = ENNReal.ofReal (N / D) := by
        have h_eq : N * (1 / D) = N / D := by field_simp [hD_pos.ne'] <;> ring
        rw [h_eq]
  have h_rpow_nonneg : 0 ≤ Real.rpow rho (1 + 7 * epsilon₁ + epsilon₃) := (Real.rpow_pos_of_pos hrho_pos _).le
  have h_final2 : ENNReal.ofReal (Real.rpow rho (1 + 7 * epsilon₁ + epsilon₃) * tau^2 / 200) =
      Kakeya.realRpowENN rho (1 + 7 * epsilon₁ + epsilon₃) * ENNReal.ofReal (tau^2 / 200) := by
    simp only [Kakeya.realRpowENN]
    have h_eq : Real.rpow rho (1 + 7 * epsilon₁ + epsilon₃) * tau^2 / 200 =
        Real.rpow rho (1 + 7 * epsilon₁ + epsilon₃) * (tau^2 / 200) := by ring
    rw [h_eq, ENNReal.ofReal_mul h_rpow_nonneg]
  have h_final1 : ENNReal.ofReal (N / D) ≥
      ENNReal.ofReal (Real.rpow rho (1 + 7 * epsilon₁ + epsilon₃) * tau^2 / 200) :=
    ENNReal.ofReal_le_ofReal h_ratio
  rw [h_ennreal_div]
  rw [h_final2] at h_final1
  exact h_final1

/-- Pairwise intersection volume bound for m ≥ 64. -/
lemma pairwise_geometric_bound_m64
    {rho tau alpha sep_scale : ℝ}
    {m : ℕ}
    (hrho_pos : 0 < rho)
    (hrho_small : rho ≤ 1 / 1000)
    (htau_pos : 0 < tau)
    (halpha_pos : 0 < alpha)
    (hsep_pos : 0 < sep_scale)
    (halpha_sep : alpha * sep_scale = rho)
    (hm_large : m ≥ 64)
    (hm_pos : 0 < m)
    (u : Point3)
    (hu_unit : ‖u‖ = 1)
    (T_i T_j : DeltaTube rho)
    (p_i p_j : Point3)
    (hpi_Ti : p_i ∈ T_i.carrier)
    (hpj_Tj : p_j ∈ T_j.carrier)
    (S_i S_j : Set Point3)
    (hSi_sub : S_i ⊆ T_i.carrier ∩ Metric.closedBall p_i tau)
    (hSj_sub : S_j ⊆ T_j.carrier ∩ Metric.closedBall p_j tau)
    (d : ℝ)
    (hd_pos : 0 < d)
    (hd_lower : d ≥ (m : ℝ) * sep_scale / 2)
    (htau_le_half : tau ≤ 1 / 2)
    (h_trans_i : ‖wz1Cross u T_i.direction‖ ≥ alpha)
    (h_trans_j : ‖wz1Cross u T_j.direction‖ ≥ alpha)
    (h_sep : ‖p_j - p_i - d • u‖ ≤ 2 * rho) :
    volume (S_i ∩ S_j) ≤ ENNReal.ofReal (64 * rho^2 * tau / (m : ℝ)) := by
  by_cases h_nonempty : (S_i ∩ S_j).Nonempty
  · rcases h_nonempty with ⟨x, hx⟩
    have hxi_Ti : x ∈ T_i.carrier := (hSi_sub hx.1).1
    have hxj_Tj : x ∈ T_j.carrier := (hSj_sub hx.2).1
    have hxi_ball : dist x p_i ≤ tau := (hSi_sub hx.1).2
    have hxj_ball : dist x p_j ≤ tau := (hSj_sub hx.2).2
    let s_i : ℝ := inner ℝ (x - p_i) T_i.direction
    let e_i : Point3 := (x - p_i) - s_i • T_i.direction
    have hxi1 : x = p_i + s_i • T_i.direction + e_i := by
      simp [e_i, s_i] <;> abel
    let s_j : ℝ := inner ℝ (x - p_j) T_j.direction
    let e_j : Point3 := (x - p_j) - s_j • T_j.direction
    have hxj1 : x = p_j + s_j • T_j.direction + e_j := by
      simp [e_j, s_j] <;> abel
    have hsi_bound : |s_i| ≤ tau := by
      have h2 : |inner ℝ (x - p_i) T_i.direction| ≤ ‖x - p_i‖ * ‖T_i.direction‖ :=
        abs_real_inner_le_norm (x - p_i) T_i.direction
      rw [T_i.direction_unit] at h2
      have h3 : ‖x - p_i‖ ≤ tau := by simpa [dist_eq_norm] using hxi_ball
      linarith
    have hsj_bound : |s_j| ≤ tau := by
      have h2 : |inner ℝ (x - p_j) T_j.direction| ≤ ‖x - p_j‖ * ‖T_j.direction‖ :=
        abs_real_inner_le_norm (x - p_j) T_j.direction
      rw [T_j.direction_unit] at h2
      have h3 : ‖x - p_j‖ ≤ tau := by simpa [dist_eq_norm] using hxj_ball
      linarith
    have hei_bound : ‖e_i‖ ≤ 2 * rho := by
      let proj_x_i := T_i.base + inner ℝ (x - T_i.base) T_i.direction • T_i.direction
      let proj_p_i := T_i.base + inner ℝ (p_i - T_i.base) T_i.direction • T_i.direction
      have h_perp_x : ‖x - proj_x_i‖ ≤ rho := tube_perp_bound hrho_pos T_i x hxi_Ti
      have h_perp_p : ‖p_i - proj_p_i‖ ≤ rho := tube_perp_bound hrho_pos T_i p_i hpi_Ti
      have h_diff : proj_x_i - proj_p_i = s_i • T_i.direction := by
        let a := inner ℝ (x - T_i.base) T_i.direction
        let b := inner ℝ (p_i - T_i.base) T_i.direction
        have h1 : proj_x_i - proj_p_i = a • T_i.direction - b • T_i.direction := by
          dsimp only [proj_x_i, proj_p_i, a, b] <;> abel
        have h2 : a • T_i.direction - b • T_i.direction = (a - b) • T_i.direction := by
          rw [sub_smul]
        have h3 : a - b = inner ℝ (x - p_i) T_i.direction := by
          dsimp only [a, b]
          rw [← inner_sub_left] <;> abel
        calc proj_x_i - proj_p_i
          = a • T_i.direction - b • T_i.direction := h1
        _ = (a - b) • T_i.direction := h2
        _ = (inner ℝ (x - p_i) T_i.direction) • T_i.direction := by rw [h3]
        _ = s_i • T_i.direction := by rfl
      have h_e_eq : e_i = (x - proj_x_i) - (p_i - proj_p_i) := by
        have h1 : (x - proj_x_i) - (p_i - proj_p_i) = (x - p_i) - (proj_x_i - proj_p_i) := by abel
        rw [h1, h_diff] <;> rfl
      rw [h_e_eq]
      calc ‖(x - proj_x_i) - (p_i - proj_p_i)‖
        ≤ ‖x - proj_x_i‖ + ‖p_i - proj_p_i‖ := norm_sub_le _ _
      _ ≤ rho + rho := by gcongr
      _ = 2 * rho := by ring
    have hej_bound : ‖e_j‖ ≤ 2 * rho := by
      let proj_x_j := T_j.base + inner ℝ (x - T_j.base) T_j.direction • T_j.direction
      let proj_p_j := T_j.base + inner ℝ (p_j - T_j.base) T_j.direction • T_j.direction
      have h_perp_x : ‖x - proj_x_j‖ ≤ rho := tube_perp_bound hrho_pos T_j x hxj_Tj
      have h_perp_p : ‖p_j - proj_p_j‖ ≤ rho := tube_perp_bound hrho_pos T_j p_j hpj_Tj
      have h_diff : proj_x_j - proj_p_j = s_j • T_j.direction := by
        let a := inner ℝ (x - T_j.base) T_j.direction
        let b := inner ℝ (p_j - T_j.base) T_j.direction
        have h1 : proj_x_j - proj_p_j = a • T_j.direction - b • T_j.direction := by
          dsimp only [proj_x_j, proj_p_j, a, b] <;> abel
        have h2 : a • T_j.direction - b • T_j.direction = (a - b) • T_j.direction := by
          rw [sub_smul]
        have h3 : a - b = inner ℝ (x - p_j) T_j.direction := by
          dsimp only [a, b]
          rw [← inner_sub_left] <;> abel
        calc proj_x_j - proj_p_j
          = a • T_j.direction - b • T_j.direction := h1
        _ = (a - b) • T_j.direction := h2
        _ = (inner ℝ (x - p_j) T_j.direction) • T_j.direction := by rw [h3]
        _ = s_j • T_j.direction := by rfl
      have h_e_eq : e_j = (x - proj_x_j) - (p_j - proj_p_j) := by
        have h1 : (x - proj_x_j) - (p_j - proj_p_j) = (x - p_j) - (proj_x_j - proj_p_j) := by abel
        rw [h1, h_diff] <;> rfl
      rw [h_e_eq]
      calc ‖(x - proj_x_j) - (p_j - proj_p_j)‖
        ≤ ‖x - proj_x_j‖ + ‖p_j - proj_p_j‖ := norm_sub_le _ _
      _ ≤ rho + rho := by gcongr
      _ = 2 * rho := by ring
    have h_d_alpha : d * alpha ≥ (m : ℝ) * rho / 2 := by
      calc d * alpha
        ≥ ((m : ℝ) * sep_scale / 2) * alpha := by gcongr
      _ = (m : ℝ) * (alpha * sep_scale) / 2 := by ring
      _ = (m : ℝ) * rho / 2 := by rw [halpha_sep] <;> ring
    have h_large12 : d * alpha ≥ 12 * rho := by
      have h2 : (m : ℝ) ≥ 64 := by exact_mod_cast hm_large
      nlinarith
    have h_angle : ‖wz1Cross T_i.direction T_j.direction‖ ≥ d * alpha / (2 * tau) :=
      angle_from_separated_intersections hrho_pos htau_pos halpha_pos hd_pos
        u T_i.direction T_j.direction
        hu_unit T_i.direction_unit T_j.direction_unit
        p_i p_j x e_i e_j s_i s_j
        h_sep hxi1 hxj1 hei_bound hej_bound hsi_bound hsj_bound
        h_trans_i h_trans_j h_large12
    set c : ℝ := alpha / 2 with hc_def
    have hc_pos : 0 < c := by positivity
    have h_cross_lower : ‖wz1Cross T_i.direction T_j.direction‖ ≥ c * d / tau := by
      have h_eq : c * d / tau = d * alpha / (2 * tau) := by rw [hc_def] <;> ring
      rw [h_eq]; exact h_angle
    have h_cross_large : c * d / tau ≥ 32 * rho := by
      have h_eq : c * d / tau = d * alpha / (2 * tau) := by rw [hc_def] <;> ring
      rw [h_eq]
      have h5 : d * alpha ≥ 64 * rho * tau := by
        have h6 : d * alpha ≥ (m : ℝ) * rho / 2 := h_d_alpha
        have h7 : (m : ℝ) ≥ 64 := by exact_mod_cast hm_large
        have h8 : tau ≤ 1 / 2 := htau_le_half
        nlinarith
      have h9 : 0 < 2 * tau := by positivity
      calc d * alpha / (2 * tau)
        ≥ (64 * rho * tau) / (2 * tau) := by gcongr
      _ = 32 * rho := by field_simp [h9.ne'] <;> ring
    have h_subset : S_i ∩ S_j ⊆ T_i.carrier ∩ T_j.carrier ∩ Metric.ball p_i (3 * tau) := by
      intro y hy
      have h3 : y ∈ T_i.carrier := (hSi_sub hy.1).1
      have h4 : y ∈ T_j.carrier := (hSj_sub hy.2).1
      have h5 : dist y p_i ≤ tau := (hSi_sub hy.1).2
      have h6 : dist y p_i < 3 * tau := by linarith [htau_pos]
      exact ⟨⟨h3, h4⟩, h6⟩
    have h_volume : volume (T_i.carrier ∩ T_j.carrier ∩ Metric.ball p_i (3 * tau)) ≤
        ENNReal.ofReal (16 * rho^3 * tau / (c * d)) :=
      pairwise_tube_intersection_volume hrho_pos hrho_small htau_pos T_i T_j p_i
        hc_pos hd_pos h_cross_lower h_cross_large
    have h_cd_lower : c * d ≥ (m : ℝ) * rho / 4 := by
      rw [hc_def]
      calc (alpha / 2) * d
        ≥ (alpha / 2) * ((m : ℝ) * sep_scale / 2) := by gcongr
      _ = (m : ℝ) * (alpha * sep_scale) / 4 := by ring
      _ = (m : ℝ) * rho / 4 := by rw [halpha_sep] <;> ring
    have h_bound : 16 * rho^3 * tau / (c * d) ≤ 64 * rho^2 * tau / (m : ℝ) := by
      have h_cd_pos : 0 < c * d := mul_pos hc_pos hd_pos
      have h_m_pos' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
      calc 16 * rho^3 * tau / (c * d)
        ≤ 16 * rho^3 * tau / ((m : ℝ) * rho / 4) := by gcongr
      _ = 64 * rho^2 * tau / (m : ℝ) := by
        field_simp [h_cd_pos.ne', h_m_pos'.ne', hrho_pos.ne'] <;> ring
    calc volume (S_i ∩ S_j)
      ≤ volume (T_i.carrier ∩ T_j.carrier ∩ Metric.ball p_i (3 * tau)) :=
        measure_mono h_subset
    _ ≤ ENNReal.ofReal (16 * rho^3 * tau / (c * d)) := h_volume
    _ ≤ ENNReal.ofReal (64 * rho^2 * tau / (m : ℝ)) := ENNReal.ofReal_mono h_bound
  · have h0 : S_i ∩ S_j = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using h_nonempty
    rw [h0] <;> simp

theorem wz1_lemma17_cordoba_slab_lower :
    WZ1Lemma17CordobaFromLogAbsorptionStatement := by
  intro h_log_absorption
  intro epsilon₁ epsilon₂ epsilon₃ heps₁_pos heps₂_pos heps₃_pos
    heps₁_lt_eps₂ heps₂_lt_eps₃ heps_sum

  -- Get rho₀ from log absorption with epsilon = epsilon₁ / 2
  rcases h_log_absorption (epsilon₁ / 2) (by linarith) with
    ⟨rho_log, hrho_log_pos, hrho_log_le, h_log_bound⟩

  -- Additional rho₀ thresholds
  let rho_ax : ℝ := (3 / 16 : ℝ) ^ (1 / (2 * epsilon₃))
  let rho_amp : ℝ := (4 / 63 : ℝ) ^ (2 / epsilon₁)
  have hrho_ax_pos : 0 < rho_ax := by positivity
  have hrho_amp_pos : 0 < rho_amp := by positivity

  let rho₀ : ℝ := min rho_log (min (1 / 1000) (min rho_ax rho_amp))
  have hrho₀_pos : 0 < rho₀ := by positivity
  have hrho₀_le_thousand : rho₀ ≤ 1 / 1000 := by
    have h1 : rho₀ ≤ min (1 / 1000) (min rho_ax rho_amp) := by
      exact min_le_right _ _
    have h2 : min (1 / 1000) (min rho_ax rho_amp) ≤ 1 / 1000 := by
      exact min_le_left _ _
    exact h1.trans h2
  refine ⟨rho₀, hrho₀_pos, hrho₀_le_thousand, ?_⟩

  intro delta sigma F U Y rho first plane tau tauAtRho tauCover robustScale robustCover data
    hrho_pos hrho_small hrho_le_tau htau_sq_four htau_le_one h_tauAtRho
    q hq_union t ht

  have hrho_le_rho_log : rho.1 ≤ rho_log := by
    have h1 : rho₀ ≤ rho_log := by
      exact min_le_left _ _
    exact hrho_small.trans h1
  have hrho_le_ax : rho.1 ≤ rho_ax := by
    have h1 : rho₀ ≤ min (1 / 1000) (min rho_ax rho_amp) := by
      exact min_le_right _ _
    have h2 : min (1 / 1000) (min rho_ax rho_amp) ≤ min rho_ax rho_amp := by
      exact min_le_right _ _
    have h3 : min rho_ax rho_amp ≤ rho_ax := by
      exact min_le_left _ _
    exact hrho_small.trans (h1.trans (h2.trans h3))
  have hrho_le_amp : rho.1 ≤ rho_amp := by
    have h1 : rho₀ ≤ min (1 / 1000) (min rho_ax rho_amp) := by
      exact min_le_right _ _
    have h2 : min (1 / 1000) (min rho_ax rho_amp) ≤ min rho_ax rho_amp := by
      exact min_le_right _ _
    have h3 : min rho_ax rho_amp ≤ rho_amp := by
      exact min_le_right _ _
    exact hrho_small.trans (h1.trans (h2.trans h3))
  set rho' : ℝ := rho.1 with hrho'_def
  set tau' : ℝ := tau.1 with htau'_def
  have htau_pos : 0 < tau' := by linarith [hrho_pos, hrho_le_tau]
  have htau_sq : tau'^2 ≤ 4 * rho' := htau_sq_four
  have htau_le_half : tau' ≤ 1 / 2 := by
    have h1 : tau'^2 ≤ 4 * rho' := htau_sq
    have h2 : rho₀ ≤ 1 / 1000 := hrho₀_le_thousand
    have h3 : rho' ≤ 1 / 1000 := hrho_small.trans h2
    nlinarith [sq_nonneg (tau' - 1 / 2)]

  let L : ℝ := (plane.lipschitzConstant : ℝ)
  have hL_nonneg : 0 ≤ L := by exact_mod_cast NNReal.coe_nonneg _

  -- Axial separation condition
  have h_ax_condition : 4 * rho'^2 ≤ (3 / 4 : ℝ) * (Real.rpow rho' (1 - epsilon₃))^2 := by
    have h_eps3_pos' : 0 < 2 * epsilon₃ := by positivity
    have h1 : Real.rpow rho' (2 * epsilon₃) ≤ 3 / 16 := by
      have h2 : rho' ≤ rho_ax := hrho_le_ax
      have h3 : Real.rpow rho' (2 * epsilon₃) ≤ Real.rpow rho_ax (2 * epsilon₃) :=
        Real.rpow_le_rpow (by linarith) h2 (by linarith)
      have h4 : Real.rpow rho_ax (2 * epsilon₃) = 3 / 16 := by
        have h_base_nonneg : (0 : ℝ) ≤ (3 / 16 : ℝ) := by norm_num
        have h6 : (1 / (2 * epsilon₃)) * (2 * epsilon₃) = 1 := by field_simp [heps₃_pos.ne'] <;> ring
        have h7 : Real.rpow (Real.rpow ((3 / 16 : ℝ)) (1 / (2 * epsilon₃))) (2 * epsilon₃) =
            Real.rpow ((3 / 16 : ℝ)) 1 := by
          have h8 := (Real.rpow_mul (x := (3 / 16 : ℝ)) h_base_nonneg (1 / (2 * epsilon₃)) (2 * epsilon₃)).symm
          rw [h6] at h8
          exact h8
        have h9 : Real.rpow ((3 / 16 : ℝ)) 1 = (3 / 16 : ℝ) := by simp
        have h10 : Real.rpow rho_ax (2 * epsilon₃) = Real.rpow (Real.rpow ((3 / 16 : ℝ)) (1 / (2 * epsilon₃))) (2 * epsilon₃) := by
          rfl
        rw [h10, h7, h9]
      linarith
    have h_sep2 : (Real.rpow rho' (1 - epsilon₃))^2 = Real.rpow rho' (2 - 2 * epsilon₃) := by
      have h_sum : (1 - epsilon₃) + (1 - epsilon₃) = 2 - 2 * epsilon₃ := by ring
      have h : Real.rpow rho' (1 - epsilon₃) * Real.rpow rho' (1 - epsilon₃) =
          Real.rpow rho' ((1 - epsilon₃) + (1 - epsilon₃)) := by
        exact (Real.rpow_add hrho_pos (1 - epsilon₃) (1 - epsilon₃)).symm
      have h2 : (Real.rpow rho' (1 - epsilon₃))^2 =
          Real.rpow rho' (1 - epsilon₃) * Real.rpow rho' (1 - epsilon₃) := by ring
      rw [h2, h, h_sum]
    have h8 : Real.rpow rho' (2 - 2 * epsilon₃) = rho'^2 / Real.rpow rho' (2 * epsilon₃) := by
      have h_pos : 0 < Real.rpow rho' (2 * epsilon₃) := Real.rpow_pos_of_pos hrho_pos _
      have h9 : Real.rpow rho' (2 - 2 * epsilon₃) * Real.rpow rho' (2 * epsilon₃) =
          Real.rpow rho' 2 := by
        have h10 : (2 - 2 * epsilon₃) + (2 * epsilon₃) = 2 := by ring
        have h11 := Real.rpow_add hrho_pos (2 - 2 * epsilon₃) (2 * epsilon₃)
        rw [h10] at h11
        exact h11.symm
      have h12 : Real.rpow rho' 2 = rho'^2 := by simp
      rw [h12] at h9
      field_simp [h_pos.ne'] at h9 ⊢ <;> exact h9
    have h9 : 0 < Real.rpow rho' (2 * epsilon₃) := Real.rpow_pos_of_pos hrho_pos _
    have h10 : Real.rpow rho' (2 * epsilon₃) ≤ 3 / 16 := h1
    have h11 : (3 / 4 : ℝ) * (rho'^2 / Real.rpow rho' (2 * epsilon₃)) ≥ 4 * rho'^2 := by
      have h12 : Real.rpow rho' (2 * epsilon₃) ≤ 3 / 16 := h10
      have h13 : 0 < rho'^2 := by positivity
      have h14 : rho'^2 / Real.rpow rho' (2 * epsilon₃) ≥ rho'^2 / (3 / 16 : ℝ) := by
        gcongr
        <;> linarith
      have h15 : (3 / 4 : ℝ) * (rho'^2 / (3 / 16 : ℝ)) = 4 * rho'^2 := by
        field_simp <;> ring
      linarith
    rw [h_sep2, h8]
    exact h11

  -- q in coarse shading union
  rcases hq_union with ⟨i_q, hq_prop3⟩
  have hq_const : q ∈ data.constantShading.carrier i_q := data.propertyThree_subshading i_q hq_prop3
  have hq_prop1 : q ∈ data.propertyOne.carrier i_q := data.constant_subshading i_q hq_const
  have hq_tauCover : q ∈ tauCover.refined.carrier i_q := data.propertyOne_sub_tau i_q hq_prop1
  have hq_coarse : q ∈ first.coarseShading.carrier i_q := tauCover.subshading i_q hq_tauCover
  have hq_coarse_union : q ∈ first.coarseShading.union := ⟨i_q, hq_coarse⟩

  -- Cell normal at q
  let rep_q : Point3 := first.representative (first.cell q)
  have hrep_q_refined : rep_q ∈ first.refined.union := (first.cell_fine_witness q hq_coarse_union).1
  have hrep_q_Y : rep_q ∈ Y.union := union_subset_of_subshading first.subshading hrep_q_refined
  let n : Point3 := plane.planeMap rep_q
  have hn_unit : ‖n‖ = 1 := plane.unit rep_q hrep_q_Y

  -- Extract p_mid realizing t
  let S_proj : Set Point3 := data.propertyThree.union ∩ Metric.closedBall q tau'
  have h_unpack : ∃ (p_mid : Point3), p_mid ∈ S_proj ∧ inner ℝ p_mid n = t := by
    have h₁ : t ∈ (fun x : Point3 => inner ℝ x n) '' S_proj := ht
    simpa [Set.mem_image] using h₁
  rcases h_unpack with ⟨p_mid, hpmid_in, h_eq_t⟩
  have hpmid_union : p_mid ∈ data.propertyThree.union := hpmid_in.1
  have hpmid_ball : dist p_mid q ≤ tau' := hpmid_in.2

  -- Pick reference tube through p_mid
  rcases hpmid_union with ⟨i_ref, hp_mid_prop3⟩
  have hp_mid_const : p_mid ∈ data.constantShading.carrier i_ref := data.propertyThree_subshading i_ref hp_mid_prop3
  have hp_mid_prop1 : p_mid ∈ data.propertyOne.carrier i_ref := data.constant_subshading i_ref hp_mid_const
  have hp_mid_tauCover : p_mid ∈ tauCover.refined.carrier i_ref := data.propertyOne_sub_tau i_ref hp_mid_prop1
  have hp_mid_coarse : p_mid ∈ first.coarseShading.carrier i_ref := tauCover.subshading i_ref hp_mid_tauCover

  let T_ref : DeltaTube rho' := (U.coarse rho).tube i_ref
  let u : Point3 := T_ref.direction
  have hu_unit : ‖u‖ = 1 := T_ref.direction_unit
  have hp_mid_Tref : p_mid ∈ T_ref.carrier := data.propertyThree.subset_body i_ref hp_mid_prop3

  -- Direction bounds
  let C_i : ℝ := 10 * rho' + L * (tau' + 4 * rho')
  let C_j : ℝ := 10 * rho' + L * (2 * tau' + 4 * rho')
  have hCi_nonneg : 0 ≤ C_i := by positivity
  have hCj_nonneg : 0 ≤ C_j := by positivity

  have hdir_ref : |inner ℝ u n| ≤ C_i := by
    have h_bound : |inner ℝ u n| ≤ 10 * rho' + L * (dist p_mid q + 4 * rho') :=
      direction_bound_with_cell_normal first plane hrho_pos hp_mid_coarse hq_coarse_union
    have hdist : dist p_mid q ≤ tau' := hpmid_ball
    have h : 10 * rho' + L * (dist p_mid q + 4 * rho') ≤ C_i := by
      simp [C_i] <;> gcongr
    exact h_bound.trans h

  -- Extract separated points around p_mid
  let sep_scale : ℝ := Real.rpow rho' (1 - epsilon₃)
  have hsep_pos : 0 < sep_scale := Real.rpow_pos_of_pos hrho_pos _
  let S_ref : Set Point3 := data.propertyThree.carrier i_ref ∩ Metric.closedBall p_mid tau'
  have hS_ref_meas : MeasurableSet S_ref :=
    (data.propertyThree.measurable_carrier i_ref).inter Metric.isClosed_closedBall.measurableSet
  have hS_ref_sub : S_ref ⊆ T_ref.carrier ∩ Metric.closedBall p_mid tau' := by
    intro x hx
    have h1 : x ∈ data.propertyThree.carrier i_ref := hx.1
    have h2 : x ∈ T_ref.carrier := data.propertyThree.subset_body i_ref h1
    exact ⟨h2, hx.2⟩
  let V : ℝ := Real.rpow rho' (2 + 2 * epsilon₁) * tau'
  have hV_pos : 0 < V := mul_pos (Real.rpow_pos_of_pos hrho_pos _) htau_pos
  have h_vol_S_ref : volume S_ref ≥ ENNReal.ofReal V := by
    have h := data.propertyThree_full i_ref p_mid hp_mid_prop3
    have h_eq : Kakeya.realRpowENN rho' (2 + 2 * epsilon₁) * ENNReal.ofReal tau' =
        ENNReal.ofReal V := by
      unfold Kakeya.realRpowENN
      have h1 : 0 ≤ Real.rpow rho' (2 + 2 * epsilon₁) := Real.rpow_nonneg (by linarith) _
      rw [ENNReal.ofReal_mul h1]
    rw [h_eq] at h
    exact h

  rcases separated_points_from_tube_volume_slab hrho_pos T_ref p_mid tau' htau_pos
      S_ref hS_ref_meas hS_ref_sub sep_scale hsep_pos V hV_pos h_vol_S_ref with
    ⟨p, k, hk_lower, hp_in_S, hp_sep⟩

  have hk_pos : 0 < k := by
    have h1 : (k : ℝ) ≥ 5 * V / (24 * rho'^2 * sep_scale) := hk_lower
    have h2 : 0 < 5 * V / (24 * rho'^2 * sep_scale) := by positivity
    have h3 : (k : ℝ) > 0 := by linarith
    exact_mod_cast h3

  -- Packing bound
  have h_rho_le_one : rho' ≤ 1 := by
    have h1 : rho' ≤ rho₀ := hrho_small
    have h2 : rho₀ ≤ 1 / 1000 := hrho₀_le_thousand
    have h3 : (1 / 1000 : ℝ) ≤ 1 := by norm_num
    linarith
  have h_eps3_nonneg : 0 ≤ epsilon₃ := by linarith
  have h_eps3_lt_one : epsilon₃ < 1 := by linarith [heps_sum]
  have hk_upper : (k : ℝ) ≤ 100 * Real.rpow rho' (-3) :=
    cordoba_separated_cardinality_of_lt (epsilon := epsilon₃) hrho_pos h_rho_le_one
      h_eps3_nonneg h_eps3_lt_one
      p p_mid
      (fun m hm => by
        have h : dist (p m) p_mid ≤ tau' := (hp_in_S m hm).2
        have h' : tau' ≤ 1 := htau_le_one
        linarith)
      (fun m n hm hn hne => by
        have h : dist (p m) (p n) ≥ sep_scale := hp_sep m n hm hn hne
        have h' : sep_scale = Real.rpow rho' (1 - epsilon₃) := by rfl
        rw [h'] at h
        exact h)

  -- Select transverse tubes
  choose j_m hj1 hj_trans using fun (m : ℕ) (hm : m < k) =>
    data.transverse (p m) (⟨i_ref, (hp_in_S m hm).1⟩) i_ref (hp_in_S m hm).1

  -- Sort points by axial projection using Finset.orderIsoOfFin
  let s : Fin k → ℝ := fun i => inner ℝ (p i) u

  have h_s_inj : Function.Injective s := by
    intro i j h
    by_contra hne
    have hne' : i.val ≠ j.val := by
      intro h
      exact hne (Fin.ext h)
    have h_sep_points : dist (p i.val) (p j.val) ≥ sep_scale :=
      hp_sep i.val j.val i.is_lt j.is_lt hne'
    have h_ax : |inner ℝ (p j.val - p i.val) u| ≥ sep_scale / 2 :=
      axial_separation_two_points hrho_pos hsep_pos u hu_unit T_ref rfl
        (p i.val) (p j.val)
        (data.propertyThree.subset_body i_ref (hp_in_S i.val i.is_lt).1)
        (data.propertyThree.subset_body i_ref (hp_in_S j.val j.is_lt).1)
        h_sep_points h_ax_condition
    have h_sub : inner ℝ (p j.val - p i.val) u = inner ℝ (p j.val) u - inner ℝ (p i.val) u := by
      rw [inner_sub_left]
    have h_eq : inner ℝ (p j.val - p i.val) u = 0 := by
      rw [h_sub]
      have h9 : inner ℝ (p i.val) u = inner ℝ (p j.val) u := h
      linarith
    rw [h_eq] at h_ax
    have h_pos : 0 < sep_scale / 2 := by linarith
    linarith

  let S_finset : Finset ℝ := Finset.image s Finset.univ
  have hS_card : S_finset.card = k := by
    rw [Finset.card_image_of_injective _ h_s_inj] <;> simp
  let e_ord : Fin k ≃o S_finset := Finset.orderIsoOfFin S_finset hS_card

  let sorted_idx_fin (i : Fin k) : Fin k :=
    Classical.choose (Finset.mem_image.mp (e_ord i).2)
  have h_choice_spec : ∀ (i : Fin k),
      sorted_idx_fin i ∈ Finset.univ ∧ s (sorted_idx_fin i) = (e_ord i : ℝ) := by
    intro i
    exact Classical.choose_spec (Finset.mem_image.mp (e_ord i).2)
  let sorted_idx (i : Fin k) : ℕ := (sorted_idx_fin i).val
  have hsorted_idx_lt : ∀ (i : Fin k), sorted_idx i < k := by
    intro i
    exact (sorted_idx_fin i).is_lt
  have h_s_spec : ∀ (i : Fin k), s ⟨sorted_idx i, hsorted_idx_lt i⟩ = (e_ord i : ℝ) := by
    intro i
    have h_eq : ⟨sorted_idx i, hsorted_idx_lt i⟩ = sorted_idx_fin i := by
      apply Fin.ext
      rfl
    rw [h_eq]
    exact (h_choice_spec i).2

  let q_sorted (i : Fin k) : Point3 := p (sorted_idx i)

  have h_sorted_axially : ∀ (i j : Fin k), i ≤ j →
      inner ℝ (q_sorted i) u ≤ inner ℝ (q_sorted j) u := by
    intro i j hij
    have h1 : (e_ord i : ℝ) ≤ (e_ord j : ℝ) := e_ord.monotone hij
    have h2 : inner ℝ (q_sorted i) u = (e_ord i : ℝ) := by
      simpa [q_sorted, s] using h_s_spec i
    have h3 : inner ℝ (q_sorted j) u = (e_ord j : ℝ) := by
      simpa [q_sorted, s] using h_s_spec j
    linarith

  -- Consecutive axial gap
  have h_consec_gap : ∀ (a : Fin k), (h : a.val + 1 < k) →
      inner ℝ (q_sorted ⟨a.val + 1, h⟩ - q_sorted a) u ≥ sep_scale / 2 := by
    intro a h
    let b : Fin k := ⟨a.val + 1, h⟩
    have h_ab : a.val < b.val := by simp [b] <;> omega
    have hne : sorted_idx a ≠ sorted_idx b := by
      intro h_eq
      have h_fin_eq : (⟨sorted_idx a, hsorted_idx_lt a⟩ : Fin k) =
          ⟨sorted_idx b, hsorted_idx_lt b⟩ := by
        apply Fin.ext
        exact h_eq
      have h4 : s ⟨sorted_idx a, hsorted_idx_lt a⟩ = s ⟨sorted_idx b, hsorted_idx_lt b⟩ := by
        rw [h_fin_eq]
      have h5 : (e_ord a : ℝ) = (e_ord b : ℝ) := by
        rw [← h_s_spec a, ← h_s_spec b, h4]
      have h6 : a = b := by
        exact (e_ord.injective) (Subtype.ext h5)
      have h7 : a.val = b.val := congr_arg Fin.val h6
      simp [b] at h7 <;> linarith
    have h_sep_points : dist (q_sorted a) (q_sorted b) ≥ sep_scale :=
      hp_sep (sorted_idx a) (sorted_idx b) (hsorted_idx_lt a) (hsorted_idx_lt b) hne
    have h_ax : |inner ℝ (q_sorted b - q_sorted a) u| ≥ sep_scale / 2 :=
      axial_separation_two_points hrho_pos hsep_pos u hu_unit T_ref rfl
        (q_sorted a) (q_sorted b)
        (data.propertyThree.subset_body i_ref (hp_in_S (sorted_idx a) (hsorted_idx_lt a)).1)
        (data.propertyThree.subset_body i_ref (hp_in_S (sorted_idx b) (hsorted_idx_lt b)).1)
        h_sep_points h_ax_condition
    have h_nonneg : 0 ≤ inner ℝ (q_sorted b - q_sorted a) u := by
      have h_le : a ≤ b := by
        exact h_ab.le
      have h : inner ℝ (q_sorted a) u ≤ inner ℝ (q_sorted b) u := h_sorted_axially a b h_le
      have h_sub : inner ℝ (q_sorted b - q_sorted a) u =
          inner ℝ (q_sorted b) u - inner ℝ (q_sorted a) u := by
        rw [inner_sub_left]
      rw [h_sub]
      linarith
    have h_abs : |inner ℝ (q_sorted b - q_sorted a) u| = inner ℝ (q_sorted b - q_sorted a) u :=
      abs_of_nonneg h_nonneg
    rw [h_abs] at h_ax
    exact h_ax

  -- Axial separation for sorted points with index gap m
  have h_axial_gap : ∀ (i j : Fin k), i.val < j.val →
      inner ℝ (q_sorted j - q_sorted i) u ≥ ((j.val : ℝ) - (i.val : ℝ)) * sep_scale / 2 := by
    intro i j hij
    have h_j_lt_k : j.val < k := j.is_lt
    have h_ind : ∀ (n : ℕ), (hsum : i.val + n ≤ j.val) →
        inner ℝ (q_sorted ⟨i.val + n, Nat.lt_of_le_of_lt hsum h_j_lt_k⟩ - q_sorted i) u ≥
          (n : ℝ) * sep_scale / 2 := by
      intro n hsum
      induction n with
      | zero =>
        simp <;> linarith
      | succ n ih =>
        have hsum' : i.val + n ≤ j.val := by linarith
        set a : Fin k := ⟨i.val + n, Nat.lt_of_le_of_lt hsum' h_j_lt_k⟩ with ha_def
        have h_b_lt : i.val + n + 1 < k := Nat.lt_of_le_of_lt (by linarith) h_j_lt_k
        set b : Fin k := ⟨i.val + n + 1, h_b_lt⟩ with hb_def
        have h1 : inner ℝ (q_sorted b - q_sorted a) u ≥ sep_scale / 2 :=
          h_consec_gap a h_b_lt
        have h_eq : q_sorted b - q_sorted i = (q_sorted b - q_sorted a) + (q_sorted a - q_sorted i) := by abel
        have h2 : inner ℝ (q_sorted b - q_sorted i) u =
            inner ℝ (q_sorted b - q_sorted a) u + inner ℝ (q_sorted a - q_sorted i) u := by
          rw [h_eq, inner_add_left]
        rw [h2]
        have h3 := ih hsum'
        have h4 : (n.succ : ℝ) = (n : ℝ) + 1 := by simp
        rw [h4]
        linarith
    have h4 := h_ind (j.val - i.val) (by omega)
    have h5 : i.val + (j.val - i.val) = j.val := by omega
    have h6 : ⟨i.val + (j.val - i.val), Nat.lt_of_le_of_lt (by omega) h_j_lt_k⟩ = j := by
      apply Fin.ext
      omega
    rw [h6] at h4
    have h7 : ((j.val - i.val : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) := by
      rw [Nat.cast_sub (by omega)] <;> simp
    rw [h7] at h4
    exact h4

  -- Slab definition
  let W : ℝ := 20 * max 1 L * rho'
  let slab : Set Point3 := {x | |inner ℝ x n - t| ≤ W}

  -- Direction bound for each transverse tube
  have hdir_j : ∀ m hm, |inner ℝ ((U.coarse rho).tube (j_m m hm)).direction n| ≤ C_j := by
    intro m hm
    let p_m := p m
    have hpi_prop1_j : p_m ∈ data.propertyOne.carrier (j_m m hm) := hj1 m hm
    have hpi_tauCover_j : p_m ∈ tauCover.refined.carrier (j_m m hm) :=
      data.propertyOne_sub_tau (j_m m hm) hpi_prop1_j
    have hpi_coarse_j : p_m ∈ first.coarseShading.carrier (j_m m hm) :=
      tauCover.subshading (j_m m hm) hpi_tauCover_j
    have h_bound : |inner ℝ ((U.coarse rho).tube (j_m m hm)).direction n| ≤
        10 * rho' + L * (dist p_m q + 4 * rho') :=
      direction_bound_with_cell_normal first plane hrho_pos hpi_coarse_j hq_coarse_union
    have hdist_pm_mid : dist p_m p_mid ≤ tau' := (hp_in_S m hm).2
    have hdist_pm_q : dist p_m q ≤ 2 * tau' := by
      calc dist p_m q
        ≤ dist p_m p_mid + dist p_mid q := dist_triangle _ _ _
      _ ≤ tau' + tau' := by linarith
      _ = 2 * tau' := by ring
    have h : 10 * rho' + L * (dist p_m q + 4 * rho') ≤ C_j := by
      simp [C_j] <;> gcongr
    exact h_bound.trans h

  -- Define A_i
  let A (i : Fin k) : Set Point3 :=
    data.propertyOne.carrier (j_m (sorted_idx i) (hsorted_idx_lt i)) ∩
      Metric.closedBall (q_sorted i) tau'

  have hA_meas : ∀ i, MeasurableSet (A i) := by
    intro i
    exact (data.propertyOne.measurable_carrier (j_m (sorted_idx i) (hsorted_idx_lt i))).inter
      Metric.isClosed_closedBall.measurableSet

  -- Slab containment
  have h_slab_contain : ∀ i, A i ⊆ slab := by
    intro i x hx
    let p_i := q_sorted i
    have hx1 : x ∈ data.propertyOne.carrier (j_m (sorted_idx i) (hsorted_idx_lt i)) := hx.1
    have hx2 : dist x p_i ≤ tau' := hx.2
    let T_j := (U.coarse rho).tube (j_m (sorted_idx i) (hsorted_idx_lt i))
    have hx_T : x ∈ T_j.carrier :=
      data.propertyOne.subset_body (j_m (sorted_idx i) (hsorted_idx_lt i)) hx1
    have hpmid_Tref : p_i ∈ T_ref.carrier :=
      data.propertyThree.subset_body i_ref
        (hp_in_S (sorted_idx i) (hsorted_idx_lt i)).1
    have hpm_Tj : p_i ∈ T_j.carrier :=
      data.propertyOne.subset_body (j_m (sorted_idx i) (hsorted_idx_lt i))
        (hj1 (sorted_idx i) (hsorted_idx_lt i))
    have hdist_mid_pi : dist p_mid p_i ≤ tau' := by
      have h2 : dist (p (sorted_idx i)) p_mid ≤ tau' :=
        (hp_in_S (sorted_idx i) (hsorted_idx_lt i)).2
      have h3 : p (sorted_idx i) = q_sorted i := by rfl
      rw [h3] at h2
      have h4 : dist p_mid (q_sorted i) ≤ tau' := by
        rw [dist_comm] at h2; exact h2
      simpa [p_i] using h4
    have h_core : |inner ℝ (x - p_mid) n| ≤ (tau' + 2 * rho') * (C_i + C_j) + 4 * rho' :=
      slab_containment_core hrho_pos.le hn_unit hp_mid_Tref hpmid_Tref hpm_Tj hx_T
        hdist_mid_pi hx2 hCi_nonneg hCj_nonneg hdir_ref
        (hdir_j (sorted_idx i) (hsorted_idx_lt i))
    have h_num : (tau' + 2 * rho') * (C_i + C_j) + 4 * rho' ≤ W :=
      slab_containment_constant_four rho' tau' L hrho_pos
        (hrho_small.trans hrho₀_le_thousand)
        hrho_le_tau htau_sq hL_nonneg C_i C_j rfl rfl
    have h_final : |inner ℝ (x - p_mid) n| ≤ W := le_trans h_core h_num
    have h_eq : inner ℝ (x - p_mid) n = inner ℝ x n - t := by
      rw [inner_sub_left, h_eq_t]
    rw [h_eq] at h_final
    simpa [slab] using h_final

  -- Volume bounds
  let V' : ℝ := 8 * rho'^2 * tau'
  have hV'_nonneg : 0 ≤ V' := by positivity

  have h_vol_lower : ∀ i, volume (A i) ≥ ENNReal.ofReal V := by
    intro i
    have h := data.propertyOne_full (j_m (sorted_idx i) (hsorted_idx_lt i))
      (q_sorted i) (hj1 (sorted_idx i) (hsorted_idx_lt i))
    have h_eq : Kakeya.realRpowENN rho' (2 + 2 * epsilon₁) * ENNReal.ofReal tau' =
        ENNReal.ofReal V := by
      unfold Kakeya.realRpowENN
      have h1 : 0 ≤ Real.rpow rho' (2 + 2 * epsilon₁) := Real.rpow_nonneg (by linarith) _
      rw [ENNReal.ofReal_mul h1]
    rw [h_eq] at h
    exact h

  have h_vol_upper : ∀ i, volume (A i) ≤ ENNReal.ofReal V' := by
    intro i
    let T_j := (U.coarse rho).tube (j_m (sorted_idx i) (hsorted_idx_lt i))
    have h1 : A i ⊆ T_j.carrier ∩ Metric.closedBall (q_sorted i) tau' := by
      intro x hx
      have h2 : x ∈ data.propertyOne.carrier (j_m (sorted_idx i) (hsorted_idx_lt i)) := hx.1
      have h3 : x ∈ T_j.carrier :=
        data.propertyOne.subset_body (j_m (sorted_idx i) (hsorted_idx_lt i)) h2
      exact ⟨h3, hx.2⟩
    have h4 : volume (A i) ≤ volume (T_j.carrier ∩ Metric.closedBall (q_sorted i) tau') :=
      measure_mono h1
    have h5 : q_sorted i ∈ T_j.carrier :=
      data.propertyOne.subset_body (j_m (sorted_idx i) (hsorted_idx_lt i))
        (hj1 (sorted_idx i) (hsorted_idx_lt i))
    have h6 := tube_ball_intersection_volume_simple (hδ := hrho_pos) (hR := htau_pos.le) T_j (q_sorted i)
    exact h4.trans h6

  -- Pairwise intersection bound with C = 504
  let C_int : ℝ := 504 * rho'^2 * tau'

  have h_alpha_sep : (Real.rpow rho' epsilon₃) * sep_scale = rho' := by
    simp only [sep_scale]
    have h3 : Real.rpow rho' epsilon₃ * Real.rpow rho' (1 - epsilon₃) =
        Real.rpow rho' (epsilon₃ + (1 - epsilon₃)) :=
      (Real.rpow_add hrho_pos _ _).symm
    rw [h3]
    have h4 : epsilon₃ + (1 - epsilon₃) = 1 := by ring
    rw [h4] <;> simp

  have h_main_lt : ∀ (i j : Fin k), i.val < j.val →
      volume (A i ∩ A j) ≤ ENNReal.ofReal (C_int / ((j : ℝ) - (i : ℝ))) := by
    intro i j hij
    let m : ℕ := j.val - i.val
    have hm_pos : 0 < m := by omega
    have h_diff : (j : ℝ) - (i : ℝ) = (m : ℝ) := by
      rw [Nat.cast_sub (by omega)] <;> simp
    rw [h_diff]

    let T_i := (U.coarse rho).tube (j_m (sorted_idx i) (hsorted_idx_lt i))
    let T_jtube := (U.coarse rho).tube (j_m (sorted_idx j) (hsorted_idx_lt j))
    let p_i_pt := q_sorted i
    let p_j_pt := q_sorted j
    let alpha : ℝ := Real.rpow rho' epsilon₃
    have halpha_pos : 0 < alpha := Real.rpow_pos_of_pos hrho_pos _
    have h_alpha_sep2 : alpha * sep_scale = rho' := h_alpha_sep

    have h_vol_upper_pair : volume (A i ∩ A j) ≤ ENNReal.ofReal V' := by
      have h_sub : A i ∩ A j ⊆ A i := by simp
      exact (measure_mono h_sub).trans (h_vol_upper i)

    by_cases h_small : m < 64
    · -- Case m < 64: crude bound
      have h_m_le_63 : m ≤ 63 := by omega
      have h504_div : (8 : ℝ) ≤ 504 / (m : ℝ) := by
        have h_m_pos' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
        have h : (m : ℝ) ≤ 63 := by exact_mod_cast h_m_le_63
        calc (8 : ℝ) = 504 / 63 := by norm_num
        _ ≤ 504 / (m : ℝ) := by gcongr <;> linarith
      have h_bound : V' ≤ C_int / (m : ℝ) := by
        simp only [V', C_int]
        have h_rho2_tau_nonneg : 0 ≤ rho'^2 * tau' := by positivity
        have h : 8 * (rho'^2 * tau') ≤ (504 / (m : ℝ)) * (rho'^2 * tau') :=
          mul_le_mul_of_nonneg_right h504_div h_rho2_tau_nonneg
        have h_eq : (504 / (m : ℝ)) * (rho'^2 * tau') = 504 * rho'^2 * tau' / (m : ℝ) := by ring
        linarith
      exact h_vol_upper_pair.trans (ENNReal.ofReal_mono h_bound)

    · -- Case m ≥ 64: use standalone geometric bound
      have h_m_large : m ≥ 64 := by omega
      let d : ℝ := inner ℝ (p_j_pt - p_i_pt) u
      have h_d_lower : d ≥ (m : ℝ) * sep_scale / 2 := by
        have h_gap := h_axial_gap i j hij
        have h_d_eq : d = inner ℝ (p_j_pt - p_i_pt) u := by rfl
        have h_m_eq : (m : ℝ) = (j : ℝ) - (i : ℝ) := by
          have h_m_def : m = j.val - i.val := by rfl
          rw [h_m_def]
          rw [Nat.cast_sub (show i.val ≤ j.val from by omega)]
          <;> simp
        rw [h_d_eq, h_m_eq]
        exact h_gap
      have hd_pos : 0 < d := by
        have h2 : 0 < (m : ℝ) * sep_scale / 2 := by positivity
        linarith [h_d_lower]
      have h_trans_i : ‖wz1Cross u T_i.direction‖ ≥ alpha := by
        simpa [alpha] using hj_trans (sorted_idx i) (hsorted_idx_lt i)
      have h_trans_j : ‖wz1Cross u T_jtube.direction‖ ≥ alpha := by
        simpa [alpha] using hj_trans (sorted_idx j) (hsorted_idx_lt j)

      have hpi_Ti : p_i_pt ∈ T_i.carrier :=
        data.propertyOne.subset_body (j_m (sorted_idx i) (hsorted_idx_lt i))
          (hj1 (sorted_idx i) (hsorted_idx_lt i))
      have hpj_Tj : p_j_pt ∈ T_jtube.carrier :=
        data.propertyOne.subset_body (j_m (sorted_idx j) (hsorted_idx_lt j))
          (hj1 (sorted_idx j) (hsorted_idx_lt j))

      have hSi_sub : A i ⊆ T_i.carrier ∩ Metric.closedBall p_i_pt tau' := by
        intro x hx
        have h1 : x ∈ data.propertyOne.carrier (j_m (sorted_idx i) (hsorted_idx_lt i)) := hx.1
        have h2 : x ∈ T_i.carrier :=
          data.propertyOne.subset_body (j_m (sorted_idx i) (hsorted_idx_lt i)) h1
        exact ⟨h2, hx.2⟩
      have hSj_sub : A j ⊆ T_jtube.carrier ∩ Metric.closedBall p_j_pt tau' := by
        intro x hx
        have h1 : x ∈ data.propertyOne.carrier (j_m (sorted_idx j) (hsorted_idx_lt j)) := hx.1
        have h2 : x ∈ T_jtube.carrier :=
          data.propertyOne.subset_body (j_m (sorted_idx j) (hsorted_idx_lt j)) h1
        exact ⟨h2, hx.2⟩

      -- Separation bound: ‖p_j_pt - p_i_pt - d • u‖ ≤ 2 * rho'
      have h_sep_bound : ‖p_j_pt - p_i_pt - d • u‖ ≤ 2 * rho' := by
        let proj_i := T_ref.base + inner ℝ (p_i_pt - T_ref.base) u • u
        let proj_j := T_ref.base + inner ℝ (p_j_pt - T_ref.base) u • u
        have h_perp_i : ‖p_i_pt - proj_i‖ ≤ rho' := by
          simpa [proj_i] using tube_perp_bound hrho_pos T_ref p_i_pt
            (data.propertyThree.subset_body i_ref
              (hp_in_S (sorted_idx i) (hsorted_idx_lt i)).1)
        have h_perp_j : ‖p_j_pt - proj_j‖ ≤ rho' := by
          simpa [proj_j] using tube_perp_bound hrho_pos T_ref p_j_pt
            (data.propertyThree.subset_body i_ref
              (hp_in_S (sorted_idx j) (hsorted_idx_lt j)).1)
        have h_proj_diff : proj_j - proj_i = d • u := by
          have h_smul : ∀ (a b : ℝ), a • u - b • u = (a - b) • u := by
            intro a b
            have h : (a - b) • u = a • u - b • u := by
              rw [sub_smul]
            exact h.symm
          let a := inner ℝ (p_j_pt - T_ref.base) u
          let b := inner ℝ (p_i_pt - T_ref.base) u
          have h1 : proj_j - proj_i = a • u - b • u := by
            dsimp only [proj_i, proj_j, a, b] <;> abel
          have h2 : a - b = inner ℝ (p_j_pt - p_i_pt) u := by
            dsimp only [a, b]
            rw [← inner_sub_left] <;> abel
          calc proj_j - proj_i
            = a • u - b • u := h1
          _ = (a - b) • u := h_smul a b
          _ = (inner ℝ (p_j_pt - p_i_pt) u) • u := by rw [h2]
          _ = d • u := by rfl
        have h_e_eq : p_j_pt - p_i_pt - d • u = (p_j_pt - proj_j) - (p_i_pt - proj_i) := by
          have h_eq1 : p_j_pt - p_i_pt - d • u = (p_j_pt - p_i_pt) - (proj_j - proj_i) := by
            rw [h_proj_diff] <;> abel
          rw [h_eq1] <;> abel
        rw [h_e_eq]
        calc ‖(p_j_pt - proj_j) - (p_i_pt - proj_i)‖
          ≤ ‖p_j_pt - proj_j‖ + ‖p_i_pt - proj_i‖ := norm_sub_le _ _
        _ ≤ rho' + rho' := by gcongr
        _ = 2 * rho' := by ring

      have h_main_bound : volume (A i ∩ A j) ≤
          ENNReal.ofReal (64 * rho'^2 * tau' / (m : ℝ)) :=
        pairwise_geometric_bound_m64
          hrho_pos (hrho_small.trans hrho₀_le_thousand) htau_pos
          halpha_pos hsep_pos h_alpha_sep2 h_m_large hm_pos
          u hu_unit T_i T_jtube p_i_pt p_j_pt hpi_Ti hpj_Tj
          (A i) (A j) hSi_sub hSj_sub d hd_pos h_d_lower htau_le_half
          h_trans_i h_trans_j h_sep_bound

      have h64_le_504 : (64 : ℝ) * rho'^2 * tau' / (m : ℝ) ≤
          (504 : ℝ) * rho'^2 * tau' / (m : ℝ) := by
        have h_m_pos' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
        have h_rho2_tau_nonneg : 0 ≤ rho'^2 * tau' := by positivity
        gcongr <;> norm_num
      exact h_main_bound.trans (ENNReal.ofReal_mono h64_le_504)

  have h_pairwise : ∀ (i j : Fin k), i ≠ j →
      volume (A i ∩ A j) ≤ ENNReal.ofReal (C_int / |(i : ℝ) - (j : ℝ)|) := by
    intro i j hne
    by_cases h : i.val < j.val
    · have h1 : (i : ℝ) < (j : ℝ) := by exact_mod_cast h
      have h_neg : (i : ℝ) - (j : ℝ) < 0 := by linarith
      have h_abs : |(i : ℝ) - (j : ℝ)| = (j : ℝ) - (i : ℝ) := by
        rw [abs_of_neg h_neg] <;> ring
      rw [h_abs]
      exact h_main_lt i j h
    · by_cases h2 : j.val < i.val
      · have h3 : volume (A i ∩ A j) = volume (A j ∩ A i) := by
          rw [Set.inter_comm]
        rw [h3]
        have h1 : (j : ℝ) < (i : ℝ) := by exact_mod_cast h2
        have h_pos : (i : ℝ) - (j : ℝ) > 0 := by linarith
        have h4 : |(i : ℝ) - (j : ℝ)| = (i : ℝ) - (j : ℝ) := by
          rw [abs_of_pos h_pos]
        rw [h4]
        exact h_main_lt j i h2
      · exfalso
        apply hne
        apply Fin.ext
        omega

  -- Apply finite Córdoba L2
  have h_cordoba : volume (⋃ i, A i) ≥
      ENNReal.ofReal ((k : ℝ)^2 * V^2) /
      ENNReal.ofReal ((k : ℝ) * V' + 2 * C_int * (k : ℝ) * (1 + Real.log (k : ℝ))) :=
    finite_cordoba_l2 hk_pos A hA_meas V V' C_int
      hV_pos hV'_nonneg (by positivity) h_vol_lower h_vol_upper h_pairwise

  -- Log absorption amplification
  have h_log_half : Real.rpow rho' (epsilon₁ / 2) *
      (8 + 64 * (1 + Real.log (k : ℝ))) ≤ 125 / 3 :=
    h_log_bound rho' hrho_pos hrho_le_rho_log k
      (by exact_mod_cast hk_pos) hk_upper

  have hrho_amplified : Real.rpow rho' (epsilon₁ / 2) ≤ 4 / 63 := by
    have h1 : rho' ≤ rho_amp := hrho_le_amp
    have h2 : Real.rpow rho' (epsilon₁ / 2) ≤ Real.rpow rho_amp (epsilon₁ / 2) :=
      Real.rpow_le_rpow hrho_pos.le h1 (by linarith)
    have h3 : Real.rpow rho_amp (epsilon₁ / 2) = 4 / 63 := by
      simp only [rho_amp]
      have h4 : Real.rpow ((4 / 63 : ℝ) ^ (2 / epsilon₁)) (epsilon₁ / 2) =
          Real.rpow (4 / 63 : ℝ) ((2 / epsilon₁) * (epsilon₁ / 2)) := by
        have h_pos1 : 0 ≤ (4 / 63 : ℝ) := by norm_num
        have h : Real.rpow (4 / 63 : ℝ) ((2 / epsilon₁) * (epsilon₁ / 2)) =
            Real.rpow (Real.rpow (4 / 63 : ℝ) (2 / epsilon₁)) (epsilon₁ / 2) :=
          Real.rpow_mul h_pos1 (2 / epsilon₁) (epsilon₁ / 2)
        have h5 : Real.rpow (4 / 63 : ℝ) (2 / epsilon₁) = ((4 / 63 : ℝ) ^ (2 / epsilon₁)) := by rfl
        rw [h5] at h
        exact h.symm
      rw [h4]
      have h5 : (2 / epsilon₁) * (epsilon₁ / 2) = 1 := by
        field_simp [heps₁_pos.ne'] <;> ring
      rw [h5] <;> norm_num
    linarith

  have h_log_main : Real.rpow rho' epsilon₁ *
      (8 + 1008 * (1 + Real.log (k : ℝ))) ≤ 125 / 3 :=
    log_absorption_amplified hrho_pos hk_pos h_log_half hrho_amplified

  -- Final arithmetic
  have hk_lower' : (k : ℝ) ≥ (5 : ℝ) / 24 * Real.rpow rho' (2 * epsilon₁ - 1 + epsilon₃) * tau' := by
    have h2 : rho'^2 * sep_scale = Real.rpow rho' (2 + (1 - epsilon₃)) := by
      have h1 : rho'^2 = Real.rpow rho' 2 := by simp
      have h21 : sep_scale = Real.rpow rho' (1 - epsilon₃) := by rfl
      have h_add : Real.rpow rho' (2 + (1 - epsilon₃)) =
          Real.rpow rho' 2 * Real.rpow rho' (1 - epsilon₃) :=
        Real.rpow_add hrho_pos 2 (1 - epsilon₃)
      calc rho'^2 * sep_scale
        = Real.rpow rho' 2 * sep_scale := by rw [h1]
      _ = Real.rpow rho' 2 * Real.rpow rho' (1 - epsilon₃) := by rw [h21]
      _ = Real.rpow rho' (2 + (1 - epsilon₃)) := h_add.symm
    have h3 : Real.rpow rho' (2 + 2 * epsilon₁) / (rho'^2 * sep_scale) =
        Real.rpow rho' ((2 + 2 * epsilon₁) - (2 + (1 - epsilon₃))) := by
      rw [h2]
      exact (Real.rpow_sub hrho_pos (2 + 2 * epsilon₁) (2 + (1 - epsilon₃))).symm
    have h4 : (2 + 2 * epsilon₁) - (2 + (1 - epsilon₃)) = 2 * epsilon₁ - 1 + epsilon₃ := by ring
    have h_exp_eq : Real.rpow rho' (2 + 2 * epsilon₁) / (rho'^2 * sep_scale) =
        Real.rpow rho' (2 * epsilon₁ - 1 + epsilon₃) := by
      rw [h3, h4]
    have h_eq : 5 * V / (24 * rho'^2 * sep_scale) =
        (5 : ℝ) / 24 * Real.rpow rho' (2 * epsilon₁ - 1 + epsilon₃) * tau' := by
      have hV_def : V = Real.rpow rho' (2 + 2 * epsilon₁) * tau' := by rfl
      calc 5 * V / (24 * rho'^2 * sep_scale)
        = 5 * (Real.rpow rho' (2 + 2 * epsilon₁) * tau') / (24 * rho'^2 * sep_scale) := by rw [hV_def]
      _ = (5 : ℝ) / 24 * (Real.rpow rho' (2 + 2 * epsilon₁) / (rho'^2 * sep_scale)) * tau' := by ring
      _ = (5 : ℝ) / 24 * Real.rpow rho' (2 * epsilon₁ - 1 + epsilon₃) * tau' := by rw [h_exp_eq] <;> ring
    have h5 : (k : ℝ) ≥ 5 * V / (24 * rho'^2 * sep_scale) := hk_lower
    rw [h_eq] at h5
    exact h5

  have h_final : ENNReal.ofReal ((k : ℝ)^2 * V^2) /
      ENNReal.ofReal ((k : ℝ) * V' + 2 * C_int * (k : ℝ) * (1 + Real.log (k : ℝ))) ≥
      Kakeya.realRpowENN rho' (1 + 7 * epsilon₁ + epsilon₃) *
      ENNReal.ofReal (tau'^2 / 200) :=
    cordoba_final_arithmetic_C504 hrho_pos h_rho_le_one
      htau_pos heps₁_pos heps₃_pos hk_pos hk_lower' h_log_main

  -- Union containment in target set
  have h_union_sub : (⋃ i, A i) ⊆
      data.propertyOne.union ∩ Metric.closedBall q (3 * tau') ∩ slab := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
    have hx1 : x ∈ data.propertyOne.carrier (j_m (sorted_idx i) (hsorted_idx_lt i)) := hi.1
    have hx2 : dist x (q_sorted i) ≤ tau' := hi.2
    have hx_union : x ∈ data.propertyOne.union := ⟨_, hx1⟩
    have hdist_pi_mid : dist (q_sorted i) p_mid ≤ tau' := by
      have h2 : dist (p (sorted_idx i)) p_mid ≤ tau' :=
        (hp_in_S (sorted_idx i) (hsorted_idx_lt i)).2
      have h3 : p (sorted_idx i) = q_sorted i := by rfl
      rw [h3] at h2
      exact h2
    have hdist_mid_q : dist p_mid q ≤ tau' := hpmid_ball
    have h1 : dist x q ≤ dist x (q_sorted i) + dist (q_sorted i) q := dist_triangle _ _ _
    have h2 : dist (q_sorted i) q ≤ dist (q_sorted i) p_mid + dist p_mid q := dist_triangle _ _ _
    have h_a : dist x (q_sorted i) ≤ tau' := hx2
    have h_b : dist (q_sorted i) p_mid ≤ tau' := hdist_pi_mid
    have h_c : dist p_mid q ≤ tau' := hdist_mid_q
    have h_sum : dist x q ≤ dist x (q_sorted i) + dist (q_sorted i) p_mid + dist p_mid q := by
      have h_tri1 : dist x q ≤ dist x (q_sorted i) + dist (q_sorted i) q := dist_triangle _ _ _
      have h_tri2 : dist (q_sorted i) q ≤ dist (q_sorted i) p_mid + dist p_mid q := dist_triangle _ _ _
      have h : dist x (q_sorted i) + dist (q_sorted i) q ≤
          dist x (q_sorted i) + dist (q_sorted i) p_mid + dist p_mid q := by
        have h' : dist x (q_sorted i) + dist (q_sorted i) q ≤
            dist x (q_sorted i) + (dist (q_sorted i) p_mid + dist p_mid q) :=
          add_le_add_right h_tri2 (dist x (q_sorted i))
        simpa [add_assoc] using h'
      exact h_tri1.trans h
    have hx_ball : dist x q ≤ 3 * tau' := by
      have h : dist x q ≤ dist x (q_sorted i) + dist (q_sorted i) p_mid + dist p_mid q := h_sum
      have h' : dist x (q_sorted i) + dist (q_sorted i) p_mid + dist p_mid q ≤ tau' + tau' + tau' := by
        exact add_le_add (add_le_add h_a h_b) h_c
      have h'' : tau' + tau' + tau' = 3 * tau' := by ring
      rw [h''] at h'
      exact h.trans h'
    have hx_slab : x ∈ slab := h_slab_contain i hi
    exact ⟨⟨hx_union, hx_ball⟩, hx_slab⟩

  have h1 : volume (⋃ i, A i) ≤
      volume (data.propertyOne.union ∩ Metric.closedBall q (3 * tau') ∩ slab) :=
    measure_mono h_union_sub

  calc
    volume (data.propertyOne.union ∩ Metric.closedBall q (3 * tau') ∩ slab)
      ≥ volume (⋃ i, A i) := h1
    _ ≥ ENNReal.ofReal ((k : ℝ)^2 * V^2) /
          ENNReal.ofReal ((k : ℝ) * V' + 2 * C_int * (k : ℝ) * (1 + Real.log (k : ℝ))) := h_cordoba
    _ ≥ Kakeya.realRpowENN rho' (1 + 7 * epsilon₁ + epsilon₃) *
          ENNReal.ofReal (tau'^2 / 200) := h_final

end Kakeya.Assouad
