module

/-
  Polynomial Majorants and Heavy Lower Bound

  Provides helper lemmas for theorem6_1_main_assembly:
  1. `heavy_lower_bound_from_frontend`: Step 7 mass lower bound
  2. `C_point_poly_bound`: C_point ≤ 10^45 * n^15 (stripped of δ^{-εReg})
  3. `C_tube_poly_bound`: max 1 (10*A_C) ≤ 10^7
  4. `C_parent_poly_bound`: parent overhead ≤ 10^80 * n^22
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.HeavyParentUniformClean
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.B1InductionDataType
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.HeavyConfigHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.InductionConfigurations
open DirecretisedFurstenbergEstimate.Section6

/-- Heavy lower bound: P₀.card > 2 * C_geo_local * K_P * δ_n^{-u+heavySlack}. -/
lemma heavy_lower_bound_from_frontend
    {n : ℕ} {u rho_mass rho_sqrt heavySlack heavyMargin K_P : ℝ}
    {P0_card : ℕ}
    (hδn_pos : 0 < dyadicDelta n)
    (hδn_le_one : dyadicDelta n ≤ 1)
    (hP_mass_lower : (P0_card : ℝ) ≥ (dyadicDelta n)^(-u + rho_mass))
    (hK_P_nonneg : 0 ≤ K_P)
    (hK_P_bound : K_P ≤ (dyadicDelta n)^(-rho_sqrt))
    (hrho_sqrt_nonneg : 0 ≤ rho_sqrt)
    (hheavySlack_gt : heavySlack > rho_mass + rho_sqrt + heavyMargin)
    (hheavyMargin_pos : 0 < heavyMargin)
    (h_heavy_absorb : 2 * C_geo_local * (dyadicDelta n)^heavyMargin < 1) :
    (P0_card : ℝ) > 2 * C_geo_local * K_P * (dyadicDelta n)^(-u + heavySlack) := by
  set δ_n := dyadicDelta n with hδn_def
  have h0 : 0 ≤ δ_n := by linarith
  have h_exp_ge : -u + heavySlack - rho_sqrt ≥ -u + rho_mass + heavyMargin := by linarith
  have h_rpow_mono : δ_n^(-u + heavySlack - rho_sqrt) ≤ δ_n^(-u + rho_mass + heavyMargin) :=
    Real.rpow_le_rpow_of_exponent_ge hδn_pos hδn_le_one h_exp_ge
  have h_product : δ_n^(-u + rho_mass + heavyMargin) = δ_n^(heavyMargin) * δ_n^(-u + rho_mass) := by
    rw [← Real.rpow_add hδn_pos] <;> ring_nf
  have h_one_le : (1 : ℝ) ≤ δ_n^(-rho_sqrt) := by
    have h1 : -rho_sqrt ≤ 0 := by linarith
    have h2 : δ_n^(-rho_sqrt) ≥ 1 := by
      have h3 : δ_n ≤ 1 := hδn_le_one
      have h4 : δ_n^(0 : ℝ) ≤ δ_n^(-rho_sqrt) := Real.rpow_le_rpow_of_exponent_ge hδn_pos hδn_le_one h1
      simpa using h4
    exact h2
  have hK_term : K_P * δ_n^(-u + heavySlack) ≤ δ_n^(-rho_sqrt) * δ_n^(-u + heavySlack) := by
    have hpos : 0 ≤ δ_n^(-u + heavySlack) := by positivity
    have h : K_P ≤ δ_n^(-rho_sqrt) := hK_P_bound
    exact mul_le_mul_of_nonneg_right h hpos
  have h_sum_exp : δ_n^(-rho_sqrt) * δ_n^(-u + heavySlack) = δ_n^(-u + heavySlack - rho_sqrt) := by
    rw [← Real.rpow_add hδn_pos] <;> ring_nf
  have h_main : 2 * C_geo_local * K_P * δ_n^(-u + heavySlack) < δ_n^(-u + rho_mass) := by
    have h_goal1 : 2 * C_geo_local * K_P * δ_n^(-u + heavySlack) ≤
        2 * C_geo_local * (δ_n^(-rho_sqrt) * δ_n^(-u + heavySlack)) := by
      have h_nonneg : 0 ≤ 2 * C_geo_local := by positivity
      have h : (2 * C_geo_local) * (K_P * δ_n^(-u + heavySlack)) ≤
          (2 * C_geo_local) * (δ_n^(-rho_sqrt) * δ_n^(-u + heavySlack)) :=
        mul_le_mul_of_nonneg_left hK_term h_nonneg
      have h_eq1 : 2 * C_geo_local * K_P * δ_n^(-u + heavySlack) =
          (2 * C_geo_local) * (K_P * δ_n^(-u + heavySlack)) := by ring
      have h_eq2 : 2 * C_geo_local * (δ_n^(-rho_sqrt) * δ_n^(-u + heavySlack)) =
          (2 * C_geo_local) * (δ_n^(-rho_sqrt) * δ_n^(-u + heavySlack)) := by ring
      rw [h_eq1, h_eq2]
      exact h
    calc
      2 * C_geo_local * K_P * δ_n^(-u + heavySlack)
        ≤ 2 * C_geo_local * (δ_n^(-rho_sqrt) * δ_n^(-u + heavySlack)) := h_goal1
      _ = 2 * C_geo_local * δ_n^(-u + heavySlack - rho_sqrt) := by rw [h_sum_exp]
      _ ≤ 2 * C_geo_local * δ_n^(-u + rho_mass + heavyMargin) := by gcongr
      _ = 2 * C_geo_local * δ_n^(heavyMargin) * δ_n^(-u + rho_mass) := by rw [h_product] <;> ring
      _ < δ_n^(-u + rho_mass) := by
        have hpos : 0 < δ_n^(-u + rho_mass) := by positivity
        have h' : 2 * C_geo_local * δ_n^(heavyMargin) < 1 := h_heavy_absorb
        have h'' : 2 * C_geo_local * δ_n^(heavyMargin) * δ_n^(-u + rho_mass) < δ_n^(-u + rho_mass) := by
          calc
            2 * C_geo_local * δ_n^(heavyMargin) * δ_n^(-u + rho_mass)
              = (2 * C_geo_local * δ_n^(heavyMargin)) * δ_n^(-u + rho_mass) := by ring
            _ < 1 * δ_n^(-u + rho_mass) := by gcongr
            _ = δ_n^(-u + rho_mass) := by ring
        exact h''
  have h_final : (P0_card : ℝ) > 2 * C_geo_local * K_P * δ_n^(-u + heavySlack) := by
    calc (P0_card : ℝ)
      ≥ δ_n^(-u + rho_mass) := hP_mass_lower
    _ > 2 * C_geo_local * K_P * δ_n^(-u + heavySlack) := h_main
  exact h_final

-- Generous universal numeric bounds
private lemma h1 : (2700 : ℝ) * 3145728 ≤ 10^10 := by norm_num
private lemma h2 : (11 : ℝ)^14 ≤ 10^15 := by norm_num
private lemma h3 : (11 : ℝ)^7 ≤ 10^8 := by norm_num
private lemma h4 : (262144 : ℝ)^2 ≤ 10^11 := by norm_num
private lemma h5 : (1296 : ℝ) ≤ 10^4 := by norm_num

private lemma h_coeff_bound :
    (648 : ℝ) * 10^6 * 2 * (2700 * 3145728)^2 * 11^14 ≤ 10^45 := by norm_num

private lemma h_mul_bounds {a b c d : ℝ} (ha : a ≤ c) (hb : b ≤ d)
    (ha_pos : 0 ≤ a) (hb_pos : 0 ≤ b) : a * b ≤ c * d := by
  have h1 : a * b ≤ c * b := mul_le_mul_of_nonneg_right ha hb_pos
  have hc_pos : 0 ≤ c := by linarith
  have h2 : c * b ≤ c * d := mul_le_mul_of_nonneg_left hb hc_pos
  exact le_trans h1 h2

/-- Polynomial bound for C_point (stripped of δ^{-εReg}):
    A_P * 18 * numDyadicLevels(4^n) * 9 * K_global ≤ 10^45 * n^15
    for A_P ≤ 10^6, n ≥ 1. -/
lemma C_point_poly_bound
    {n : ℕ} {A_P K_B1 K_global : ℝ}
    (hn_pos : 0 < n)
    (hA_P_le : A_P ≤ 10^6)
    (hA_P_nonneg : 0 ≤ A_P)
    (hK_B1_nonneg : 0 ≤ K_B1)
    (hK_B1_bound : K_B1 ≤ 2700 * 3145728 * (4 * (n : ℝ) + 7)^7)
    (hK_global_nonneg : 0 ≤ K_global)
    (hK_global_bound : K_global ≤ 2 * K_B1^2) :
    A_P * 18 * (numDyadicLevels (4^n) : ℝ) * 9 * K_global ≤ (10 : ℝ)^45 * (n : ℝ)^15 := by
  have h_n_ge1 : (n : ℝ) ≥ 1 := by exact_mod_cast hn_pos
  have h_num4 : (numDyadicLevels (4^n) : ℝ) ≤ 4 * (n : ℝ) := by
    have h : numDyadicLevels (4^n) ≤ 2 * n + 2 := numDyadicLevels_le_linear (N := 4^n) (n := n) (by norm_num)
    have h' : (numDyadicLevels (4^n) : ℝ) ≤ 2 * (n : ℝ) + 2 := by exact_mod_cast h
    linarith
  have h2' : 4 * (n : ℝ) + 7 ≤ 11 * (n : ℝ) := by linarith
  have h_pow14 : (4 * (n : ℝ) + 7)^14 ≤ (11 * (n : ℝ))^14 := by
    gcongr
    <;> linarith
  have hK_global_raw : K_global ≤ 2 * (2700 * 3145728 : ℝ)^2 * (4 * (n : ℝ) + 7)^14 :=
    K_global_poly_bound hK_B1_nonneg hK_B1_bound hK_global_bound
  have hK_global_poly : K_global ≤ 2 * (2700 * 3145728 : ℝ)^2 * (11 : ℝ)^14 * (n : ℝ)^14 := by
    have h1 : 2 * (2700 * 3145728 : ℝ)^2 * (4 * (n : ℝ) + 7)^14 ≤
        2 * (2700 * 3145728 : ℝ)^2 * (11 * (n : ℝ))^14 := by
      gcongr
      <;> linarith
    have h' : (11 * (n : ℝ))^14 = (11 : ℝ)^14 * (n : ℝ)^14 := by ring
    calc K_global
      ≤ 2 * (2700 * 3145728 : ℝ)^2 * (4 * (n : ℝ) + 7)^14 := hK_global_raw
    _ ≤ 2 * (2700 * 3145728 : ℝ)^2 * (11 * (n : ℝ))^14 := h1
    _ = 2 * (2700 * 3145728 : ℝ)^2 * ((11 : ℝ)^14 * (n : ℝ)^14) := by rw [h']
    _ = 2 * (2700 * 3145728 : ℝ)^2 * (11 : ℝ)^14 * (n : ℝ)^14 := by ring
  have h_main1 : A_P * 18 * (numDyadicLevels (4^n) : ℝ) * 9 ≤ 648 * (10 : ℝ)^6 * (n : ℝ) := by
    have h1 : A_P ≤ (10 : ℝ)^6 := hA_P_le
    have h2 : (numDyadicLevels (4^n) : ℝ) ≤ 4 * (n : ℝ) := h_num4
    have h_pos : 0 ≤ A_P := hA_P_nonneg
    calc A_P * 18 * (numDyadicLevels (4^n) : ℝ) * 9
      = A_P * (numDyadicLevels (4^n) : ℝ) * (18 * 9) := by ring
    _ ≤ (10 : ℝ)^6 * (4 * (n : ℝ)) * (18 * 9) := by
        gcongr <;> assumption
    _ = 648 * (10 : ℝ)^6 * (n : ℝ) := by ring
  have h_pos648 : 0 ≤ 648 * (10 : ℝ)^6 * (n : ℝ) := by positivity
  have h_pos15 : 0 ≤ (n : ℝ)^15 := by positivity
  calc
    A_P * 18 * (numDyadicLevels (4^n) : ℝ) * 9 * K_global
      = (A_P * 18 * (numDyadicLevels (4^n) : ℝ) * 9) * K_global := by ring
    _ ≤ (648 * (10 : ℝ)^6 * (n : ℝ)) * K_global := by
        gcongr
        <;> assumption
    _ ≤ (648 * (10 : ℝ)^6 * (n : ℝ)) *
          (2 * (2700 * 3145728 : ℝ)^2 * (11 : ℝ)^14 * (n : ℝ)^14) := by
        gcongr
        <;> assumption
    _ = (648 * (10 : ℝ)^6 * 2 * (2700 * 3145728 : ℝ)^2 * (11 : ℝ)^14) * (n : ℝ)^15 := by ring
    _ ≤ (10 : ℝ)^45 * (n : ℝ)^15 := by
        have h : (648 * (10 : ℝ)^6 * 2 * (2700 * 3145728 : ℝ)^2 * (11 : ℝ)^14) ≤ (10 : ℝ)^45 := h_coeff_bound
        gcongr
        <;> assumption

/-- Polynomial bound for tube constant (stripped of δ^{-εReg}):
    max 1 (10 * A_C) ≤ 10^7 for A_C ≤ 10^6. -/
lemma C_tube_poly_bound
    {A_C : ℝ} (hA_C_le : A_C ≤ 10^6) (hA_C_nonneg : 0 ≤ A_C) :
    max 1 (10 * A_C) ≤ (10 : ℝ)^7 := by
  have h : 10 * A_C ≤ (10 : ℝ)^7 := by
    calc 10 * A_C
      ≤ 10 * (10 : ℝ)^6 := by gcongr
    _ = (10 : ℝ)^7 := by ring
  exact max_le (by norm_num) h

/-- Polynomial bound for parent overhead (stripped of δ^{-εReg}):
    262144^2 * 2592 * C_point_stripped * K_B1 * 8 ≤ 10^80 * n^22
    for C_point_stripped ≤ 10^45 * n^15 and n ≥ 1. -/
lemma C_parent_poly_bound
    {n : ℕ} {C_point_stripped K_B1 : ℝ}
    (hn_pos : 0 < n)
    (hC_point : C_point_stripped ≤ (10 : ℝ)^45 * (n : ℝ)^15)
    (hC_point_nonneg : 0 ≤ C_point_stripped)
    (hK_B1_nonneg : 0 ≤ K_B1)
    (hK_B1_bound : K_B1 ≤ 2700 * 3145728 * (4 * (n : ℝ) + 7)^7) :
    (262144 : ℝ)^2 * 2592 * C_point_stripped * K_B1 * 8 ≤ (10 : ℝ)^80 * (n : ℝ)^22 := by
  have h_n_ge1 : (n : ℝ) ≥ 1 := by exact_mod_cast hn_pos
  have h2' : 4 * (n : ℝ) + 7 ≤ 11 * (n : ℝ) := by linarith
  have hK_B1_poly : K_B1 ≤ (10 : ℝ)^10 * (11 * (n : ℝ))^7 := by
    calc K_B1
      ≤ 2700 * 3145728 * (4 * (n : ℝ) + 7)^7 := hK_B1_bound
    _ ≤ (10 : ℝ)^10 * (4 * (n : ℝ) + 7)^7 := by
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ (10 : ℝ)^10 * (11 * (n : ℝ))^7 := by
        have h_exp : (4 * (n : ℝ) + 7)^7 ≤ (11 * (n : ℝ))^7 := by
          gcongr <;> linarith
        exact mul_le_mul_of_nonneg_left h_exp (by positivity)
  have h2592_le : (2592 : ℝ) ≤ 10^4 := by norm_num
  have h8_le : (8 : ℝ) ≤ 10 := by norm_num
  have h_main : (262144 : ℝ)^2 * 2592 * C_point_stripped * K_B1 * 8 ≤
      (10 : ℝ)^11 * (10 : ℝ)^4 * ((10 : ℝ)^45 * (n : ℝ)^15) * ((10 : ℝ)^10 * (11 * (n : ℝ))^7) * (10 : ℝ) := by
    have h_pos1 : 0 ≤ (262144 : ℝ)^2 := by positivity
    have h_pos2 : 0 ≤ (2592 : ℝ) := by norm_num
    have h_pos3 : 0 ≤ C_point_stripped := hC_point_nonneg
    have h_pos4 : 0 ≤ K_B1 := hK_B1_nonneg
    have h_pos5 : 0 ≤ (8 : ℝ) := by norm_num
    have h_m1 : (262144 : ℝ)^2 * 2592 ≤ (10 : ℝ)^11 * (10 : ℝ)^4 := by
      exact mul_le_mul_of_nonneg_right h4 (by positivity) |>.trans (mul_le_mul_of_nonneg_left h2592_le (by positivity))
    have h_m2 : ((262144 : ℝ)^2 * 2592) * C_point_stripped ≤
        ((10 : ℝ)^11 * (10 : ℝ)^4) * ((10 : ℝ)^45 * (n : ℝ)^15) := by
      exact mul_le_mul h_m1 hC_point h_pos3 (by positivity)
    have h_m3 : (((262144 : ℝ)^2 * 2592) * C_point_stripped) * K_B1 ≤
        (((10 : ℝ)^11 * (10 : ℝ)^4) * ((10 : ℝ)^45 * (n : ℝ)^15)) * ((10 : ℝ)^10 * (11 * (n : ℝ))^7) := by
      exact mul_le_mul h_m2 hK_B1_poly h_pos4 (by positivity)
    have h_m4 : ((((262144 : ℝ)^2 * 2592) * C_point_stripped) * K_B1) * 8 ≤
        ((((10 : ℝ)^11 * (10 : ℝ)^4) * ((10 : ℝ)^45 * (n : ℝ)^15)) * ((10 : ℝ)^10 * (11 * (n : ℝ))^7)) * (10 : ℝ) := by
      exact mul_le_mul h_m3 h8_le h_pos5 (by positivity)
    have h_eq1 : (262144 : ℝ)^2 * 2592 * C_point_stripped * K_B1 * 8 =
        ((((262144 : ℝ)^2 * 2592) * C_point_stripped) * K_B1) * 8 := by ring
    have h_eq2 : ((((10 : ℝ)^11 * (10 : ℝ)^4) * ((10 : ℝ)^45 * (n : ℝ)^15)) * ((10 : ℝ)^10 * (11 * (n : ℝ))^7)) * (10 : ℝ) =
        (10 : ℝ)^11 * (10 : ℝ)^4 * ((10 : ℝ)^45 * (n : ℝ)^15) * ((10 : ℝ)^10 * (11 * (n : ℝ))^7) * (10 : ℝ) := by ring
    rw [h_eq1, h_eq2]
    exact h_m4
  have h_final : (10 : ℝ)^11 * (10 : ℝ)^4 * ((10 : ℝ)^45 * (n : ℝ)^15) * ((10 : ℝ)^10 * (11 * (n : ℝ))^7) * (10 : ℝ) ≤
      (10 : ℝ)^80 * (n : ℝ)^22 := by
    calc
      (10 : ℝ)^11 * (10 : ℝ)^4 * ((10 : ℝ)^45 * (n : ℝ)^15) * ((10 : ℝ)^10 * (11 * (n : ℝ))^7) * (10 : ℝ)
        = (10 : ℝ)^71 * 11^7 * (n : ℝ)^22 := by ring
      _ ≤ (10 : ℝ)^71 * (10 : ℝ)^8 * (n : ℝ)^22 := by gcongr; exact h3
      _ = (10 : ℝ)^79 * (n : ℝ)^22 := by ring
      _ ≤ (10 : ℝ)^80 * (n : ℝ)^22 := by
        have h : (10 : ℝ)^79 ≤ (10 : ℝ)^80 := by norm_num
        gcongr
  exact le_trans h_main h_final

/-- Generalized polynomial bound for C_point (stripped of δ^{-εReg}):
    A_P * 18 * numDyadicLevels(N) * 9 * K_global ≤ 10^45 * n^15
    for A_P ≤ 10^6, N ≤ 4^n, n ≥ 1. -/
lemma C_point_poly_bound_general
    {n N : ℕ} {A_P K_B1 K_global : ℝ}
    (hn_pos : 0 < n)
    (hN_pos : 0 < N)
    (hN_le : N ≤ 4^n)
    (hA_P_le : A_P ≤ 10^6)
    (hA_P_nonneg : 0 ≤ A_P)
    (hK_B1_nonneg : 0 ≤ K_B1)
    (hK_B1_bound : K_B1 ≤ 2700 * 3145728 * (4 * (n : ℝ) + 7)^7)
    (hK_global_nonneg : 0 ≤ K_global)
    (hK_global_bound : K_global ≤ 2 * K_B1^2) :
    A_P * 18 * (numDyadicLevels N : ℝ) * 9 * K_global ≤ (10 : ℝ)^45 * (n : ℝ)^15 := by
  have h_n_ge1_num : (n : ℝ) ≥ 1 := by exact_mod_cast hn_pos
  have h_num : (numDyadicLevels N : ℝ) ≤ 4 * (n : ℝ) := by
    have h1 : numDyadicLevels N ≤ 2 * n + 2 := numDyadicLevels_le_linear hN_le
    have h2 : (numDyadicLevels N : ℝ) ≤ 2 * (n : ℝ) + 2 := by exact_mod_cast h1
    have h3 : 2 * (n : ℝ) + 2 ≤ 4 * (n : ℝ) := by linarith
    exact le_trans h2 h3
  have h_n_ge1 : (n : ℝ) ≥ 1 := by exact_mod_cast hn_pos
  have h2' : 4 * (n : ℝ) + 7 ≤ 11 * (n : ℝ) := by linarith
  have hK_global_raw : K_global ≤ 2 * (2700 * 3145728 : ℝ)^2 * (4 * (n : ℝ) + 7)^14 :=
    K_global_poly_bound hK_B1_nonneg hK_B1_bound hK_global_bound
  have hK_global_poly : K_global ≤ 2 * (2700 * 3145728 : ℝ)^2 * (11 : ℝ)^14 * (n : ℝ)^14 := by
    have h1 : 2 * (2700 * 3145728 : ℝ)^2 * (4 * (n : ℝ) + 7)^14 ≤
        2 * (2700 * 3145728 : ℝ)^2 * (11 * (n : ℝ))^14 := by
      gcongr <;> linarith
    have h' : (11 * (n : ℝ))^14 = (11 : ℝ)^14 * (n : ℝ)^14 := by ring
    calc K_global
      ≤ 2 * (2700 * 3145728 : ℝ)^2 * (4 * (n : ℝ) + 7)^14 := hK_global_raw
    _ ≤ 2 * (2700 * 3145728 : ℝ)^2 * (11 * (n : ℝ))^14 := h1
    _ = 2 * (2700 * 3145728 : ℝ)^2 * ((11 : ℝ)^14 * (n : ℝ)^14) := by rw [h']
    _ = 2 * (2700 * 3145728 : ℝ)^2 * (11 : ℝ)^14 * (n : ℝ)^14 := by ring
  have h_main1 : A_P * 18 * (numDyadicLevels N : ℝ) * 9 ≤ 648 * (10 : ℝ)^6 * (n : ℝ) := by
    have h1 : A_P ≤ (10 : ℝ)^6 := hA_P_le
    have h_pos : 0 ≤ A_P := hA_P_nonneg
    calc A_P * 18 * (numDyadicLevels N : ℝ) * 9
      = A_P * (numDyadicLevels N : ℝ) * (18 * 9) := by ring
    _ ≤ (10 : ℝ)^6 * (4 * (n : ℝ)) * (18 * 9) := by gcongr <;> assumption
    _ = 648 * (10 : ℝ)^6 * (n : ℝ) := by ring
  calc
    A_P * 18 * (numDyadicLevels N : ℝ) * 9 * K_global
      = (A_P * 18 * (numDyadicLevels N : ℝ) * 9) * K_global := by ring
    _ ≤ (648 * (10 : ℝ)^6 * (n : ℝ)) * K_global := by gcongr <;> assumption
    _ ≤ (648 * (10 : ℝ)^6 * (n : ℝ)) *
          (2 * (2700 * 3145728 : ℝ)^2 * (11 : ℝ)^14 * (n : ℝ)^14) := by gcongr <;> assumption
    _ = (648 * (10 : ℝ)^6 * 2 * (2700 * 3145728 : ℝ)^2 * (11 : ℝ)^14) * (n : ℝ)^15 := by ring
    _ ≤ (10 : ℝ)^45 * (n : ℝ)^15 := by
      have h : (648 * (10 : ℝ)^6 * 2 * (2700 * 3145728 : ℝ)^2 * (11 : ℝ)^14) ≤ (10 : ℝ)^45 := h_coeff_bound
      gcongr <;> assumption

/-- Full point majorant (general N): C_P * 18 * numDyadicLevels(N) * 9 * K_global ≤
    δ_n^{-(εReg+pointLoss)} * 10^50 * n^16, for N ≤ 4^n.

    Premise hC_P_bound uses the full εReg+pointLoss exponent, matching the
    frontend regularity budget (rho_sqrt = εReg + pointLoss). -/
lemma point_majorant_general
    {n N : ℕ} {A_P C_P K_B1 K_global : ℝ}
    {εReg pointLoss : ℝ}
    (δ_n : ℝ)
    (hn_pos : 0 < n)
    (hN_pos : 0 < N)
    (hN_le : N ≤ 4^n)
    (hδn_pos : 0 < δ_n)
    (hδn_lt_one : δ_n < 1)
    (hεReg_pos : 0 < εReg)
    (hpointLoss_pos : 0 < pointLoss)
    (hA_P_le : A_P ≤ 10^6)
    (hA_P_nonneg : 0 ≤ A_P)
    (hK_B1_nonneg : 0 ≤ K_B1)
    (hK_B1_bound : K_B1 ≤ 2700 * 3145728 * (4 * (n : ℝ) + 7)^7)
    (hK_global_nonneg : 0 ≤ K_global)
    (hK_global_bound : K_global ≤ 2 * K_B1^2)
    (hC_P_bound : C_P ≤ A_P * δ_n^(-(εReg + pointLoss))) :
    C_P * 18 * (numDyadicLevels N : ℝ) * 9 * K_global ≤
    δ_n^(-(εReg + pointLoss)) * (10 : ℝ)^50 * (n : ℝ)^16 := by
  set X := A_P * 18 * (numDyadicLevels N : ℝ) * 9 * K_global with hX_def
  set E := δ_n^(-(εReg + pointLoss)) with hE_def
  have h_poly : X ≤ (10 : ℝ)^45 * (n : ℝ)^15 :=
    C_point_poly_bound_general hn_pos hN_pos hN_le hA_P_le hA_P_nonneg
      hK_B1_nonneg hK_B1_bound hK_global_nonneg hK_global_bound
  have h_posX : 0 ≤ X := by positivity
  have h_posE : 0 ≤ E := by positivity
  have h1 : C_P * 18 * (numDyadicLevels N : ℝ) * 9 * K_global ≤ E * X := by
    have h_pos_rest : 0 ≤ 18 * (numDyadicLevels N : ℝ) * 9 * K_global := by positivity
    calc C_P * 18 * (numDyadicLevels N : ℝ) * 9 * K_global
      = C_P * (18 * (numDyadicLevels N : ℝ) * 9 * K_global) := by ring
    _ ≤ (A_P * E) * (18 * (numDyadicLevels N : ℝ) * 9 * K_global) := by
        exact mul_le_mul_of_nonneg_right hC_P_bound h_pos_rest
    _ = E * X := by simp only [hX_def, hE_def] <;> ring
  have h_n_ge1 : (n : ℝ) ≥ 1 := by exact_mod_cast hn_pos
  have h4 : (10 : ℝ)^45 * (n : ℝ)^15 ≤ (10 : ℝ)^50 * (n : ℝ)^16 := by
    have h5 : (n : ℝ)^15 ≤ (n : ℝ)^16 := by
      have h6 : (n : ℝ)^15 ≥ 0 := by positivity
      have h7 : (n : ℝ)^15 ≤ (n : ℝ)^15 * (n : ℝ) := by nlinarith
      have h9 : (n : ℝ)^15 * (n : ℝ) = (n : ℝ)^16 := by ring
      rw [h9] at h7; exact h7
    have h10 : (10 : ℝ)^45 ≤ (10 : ℝ)^50 := by norm_num
    have h_step1 : (10 : ℝ)^45 * (n : ℝ)^15 ≤ (10 : ℝ)^50 * (n : ℝ)^15 :=
      mul_le_mul_of_nonneg_right h10 (by positivity)
    have h_step2 : (10 : ℝ)^50 * (n : ℝ)^15 ≤ (10 : ℝ)^50 * (n : ℝ)^16 :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    exact le_trans h_step1 h_step2
  have h2 : E * X ≤ E * ((10 : ℝ)^45 * (n : ℝ)^15) :=
    mul_le_mul_of_nonneg_left h_poly h_posE
  have h3 : E * ((10 : ℝ)^45 * (n : ℝ)^15) ≤ E * ((10 : ℝ)^50 * (n : ℝ)^16) :=
    mul_le_mul_of_nonneg_left h4 h_posE
  have h_final : C_P * 18 * (numDyadicLevels N : ℝ) * 9 * K_global ≤
      E * ((10 : ℝ)^50 * (n : ℝ)^16) := by
    calc C_P * 18 * (numDyadicLevels N : ℝ) * 9 * K_global
      ≤ E * X := h1
    _ ≤ E * ((10 : ℝ)^45 * (n : ℝ)^15) := h2
    _ ≤ E * ((10 : ℝ)^50 * (n : ℝ)^16) := h3
  have h_eq : E * ((10 : ℝ)^50 * (n : ℝ)^16) =
      δ_n^(-(εReg + pointLoss)) * (10 : ℝ)^50 * (n : ℝ)^16 := by
    simp only [hE_def] <;> ring
  rw [h_eq] at h_final
  exact h_final

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
