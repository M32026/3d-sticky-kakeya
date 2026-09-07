import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.TrivialCovering
import Mathlib.Tactic

/-!
# Hard regime large-scale AD bound

Helper lemmas for the hard regime local AD proof when ρ ≥ L_coarse.

## Main results

- `hard_regime_large_scale_key`: key inequality `3*x ≤ δ^(-outputLoss) * x^(1-σ)`
- `pureWz2_ad_from_key`: mechanical AD bound from the key inequality
-/

namespace Kakeya.Assouad.PureWZ2

open Real

/-- Key inequality for hard regime large-scale case (ρ ≥ L_coarse).

Proves `3*x ≤ δ^(-outputLoss) * x^(1-σ)` for `1 ≤ x ≤ 2/√ρ`
using `ρ ≥ L_coarse = δ^stickyLoss`, `outputLoss ≥ 3*stickyLoss`,
and `L_coarse ≤ 3^(-20/σ)`. -/
lemma hard_regime_large_scale_key
    {delta sigma outputLoss stickyLoss L_coarse rho C_P : ℝ}
    (hdelta_pos : 0 < delta)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hstickyLoss_pos : 0 < stickyLoss)
    (hstickyLoss_le_third : stickyLoss ≤ outputLoss / 3)
    (hL_coarse_def : L_coarse = delta ^ stickyLoss)
    (hL_le_C : L_coarse ≤ (3 : ℝ) ^ (-(20 / sigma)))
    (hrho_pos : 0 < rho)
    (h_large : L_coarse ≤ rho)
    {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2 / Real.sqrt rho) :
    3 * x ≤ (delta ^ (-outputLoss)) * (x ^ (1 - sigma)) := by
  have hx_pos : 0 < x := by linarith
  have hL_pos : 0 < L_coarse := by
    rw [hL_coarse_def]; exact Real.rpow_pos_of_pos hdelta_pos _
  have h1 : x ^ sigma ≤ (2 / Real.sqrt L_coarse) ^ sigma := by
    have h2 : 2 / Real.sqrt rho ≤ 2 / Real.sqrt L_coarse := by
      gcongr <;> exact Real.sqrt_le_sqrt h_large
    have h3 : x ≤ 2 / Real.sqrt L_coarse := hx2.trans h2
    exact Real.rpow_le_rpow (by linarith) h3 (by linarith)
  have hsqrt_pos : 0 < Real.sqrt L_coarse := Real.sqrt_pos.mpr hL_pos
  have h42 : (Real.sqrt L_coarse)^sigma = L_coarse ^ (sigma / 2) := by
    have h43 : Real.sqrt L_coarse = L_coarse ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
    rw [h43, ← Real.rpow_mul hL_pos.le] <;> ring
  have h_pos2 : 0 < L_coarse ^ (sigma / 2) := Real.rpow_pos_of_pos hL_pos _
  have h_neg1 : (-sigma / 2 : ℝ) = -(sigma / 2) := by ring
  have h_neg2 : L_coarse ^ (-sigma / 2) = (L_coarse ^ (sigma / 2))⁻¹ := by
    rw [h_neg1, Real.rpow_neg hL_pos.le]
  have h4 : (2 / Real.sqrt L_coarse) ^ sigma = (2 : ℝ)^sigma * L_coarse ^ (-sigma / 2) := by
    have h41 : (2 / Real.sqrt L_coarse) ^ sigma = (2 : ℝ)^sigma / (Real.sqrt L_coarse)^sigma :=
      Real.div_rpow (by norm_num) (Real.sqrt_nonneg L_coarse) sigma
    rw [h41, h42, h_neg2]
    <;> field_simp [h_pos2.ne'] <;> ring
  have h5 : 3 * x ^ sigma ≤ 3 * (2 : ℝ)^sigma * L_coarse ^ (-sigma / 2) := by
    calc 3 * x ^ sigma
      ≤ 3 * (2 / Real.sqrt L_coarse) ^ sigma := by gcongr
    _ = 3 * (2 : ℝ)^sigma * L_coarse ^ (-sigma / 2) := by rw [h4] <;> ring
  have h6 : L_coarse ^ (-sigma / 2) = delta ^ (-sigma * stickyLoss / 2) := by
    rw [hL_coarse_def, ← Real.rpow_mul hdelta_pos.le] <;> ring
  have h5' : 3 * x ^ sigma ≤ 3 * (2 : ℝ)^sigma * delta ^ (-sigma * stickyLoss / 2) := by
    rw [h6] at h5; exact h5
  set beta : ℝ := outputLoss - sigma * stickyLoss / 2 with hbeta_def
  have hbeta_pos : 0 < beta := by
    have h : outputLoss ≥ 3 * stickyLoss := by linarith [hstickyLoss_le_third]
    have h2 : sigma * stickyLoss / 2 < 3 * stickyLoss := by
      have h3 : sigma / 2 < 3 := by linarith
      nlinarith
    linarith
  have hdelta_small : delta ≤ (3 : ℝ) ^ (-(20 / (sigma * stickyLoss))) := by
    have h9 : delta ^ stickyLoss ≤ (3 : ℝ) ^ (-(20 / sigma)) := by
      rw [hL_coarse_def] at hL_le_C; exact hL_le_C
    have h10 : 0 < stickyLoss := hstickyLoss_pos
    have h12 : (delta ^ stickyLoss) ^ (1 / stickyLoss) ≤ ((3 : ℝ) ^ (-(20 / sigma))) ^ (1 / stickyLoss) :=
      Real.rpow_le_rpow (by positivity) h9 (by positivity)
    have h13 : (delta ^ stickyLoss) ^ (1 / stickyLoss) = delta := by
      rw [← Real.rpow_mul hdelta_pos.le]
      have h14 : stickyLoss * (1 / stickyLoss) = 1 := by field_simp [h10.ne'] <;> ring
      rw [h14] <;> simp
    have h15 : ((3 : ℝ) ^ (-(20 / sigma))) ^ (1 / stickyLoss) = (3 : ℝ) ^ (-(20 / (sigma * stickyLoss))) := by
      rw [← Real.rpow_mul (by norm_num)] <;> ring
    rw [h13, h15] at h12
    exact h12
  set B : ℝ := (3 : ℝ) ^ (-(20 / (sigma * stickyLoss))) with hB_def
  have hB_pos : 0 < B := by positivity
  have hB_lt_one : B < 1 := by
    have hpos : 0 < 20 / (sigma * stickyLoss) := by positivity
    have h_gt : (3 : ℝ) ^ (20 / (sigma * stickyLoss)) > 1 := Real.one_lt_rpow (by norm_num) hpos
    have h_eq : B = ((3 : ℝ) ^ (20 / (sigma * stickyLoss)))⁻¹ := by
      simp [hB_def, Real.rpow_neg] <;> ring
    rw [h_eq]
    have h_pos' : 0 < (3 : ℝ) ^ (20 / (sigma * stickyLoss)) := by positivity
    have h_mul : ((3 : ℝ) ^ (20 / (sigma * stickyLoss)))⁻¹ * ((3 : ℝ) ^ (20 / (sigma * stickyLoss))) = 1 := by
      field_simp [h_pos'.ne'] <;> ring
    have h9 : 1 < (3 : ℝ) ^ (20 / (sigma * stickyLoss)) := h_gt
    have h10 : 0 < ((3 : ℝ) ^ (20 / (sigma * stickyLoss)))⁻¹ := by positivity
    have h_lt : ((3 : ℝ) ^ (20 / (sigma * stickyLoss)))⁻¹ < 1 := by nlinarith
    exact h_lt
  have h16 : B ^ (-beta) ≤ delta ^ (-beta) := by
    have h19 : delta ^ beta ≤ B ^ beta := Real.rpow_le_rpow (by positivity) hdelta_small (by linarith)
    have h20 : B ^ (-beta) = (B ^ beta)⁻¹ := by
      rw [Real.rpow_neg hB_pos.le] <;> ring
    have h21 : delta ^ (-beta) = (delta ^ beta)⁻¹ := by
      rw [Real.rpow_neg hdelta_pos.le] <;> ring
    rw [h20, h21]
    gcongr
  have hbeta_ge : beta ≥ 5 / 2 * stickyLoss := by
    have h22 : outputLoss ≥ 3 * stickyLoss := by linarith [hstickyLoss_le_third]
    have h23 : sigma * stickyLoss / 2 ≤ stickyLoss / 2 := by
      have h24 : sigma ≤ 1 := by linarith
      have h25 : 0 ≤ stickyLoss := by linarith
      nlinarith
    dsimp only [beta]
    linarith
  have h20 : 20 * beta / (sigma * stickyLoss) ≥ 50 := by
    have h23 : 0 < sigma * stickyLoss := mul_pos hsigma_pos hstickyLoss_pos
    calc 20 * beta / (sigma * stickyLoss)
      ≥ 20 * (5 / 2 * stickyLoss) / (sigma * stickyLoss) := by gcongr
    _ = 50 / sigma := by field_simp [h23.ne'] <;> ring
    _ ≥ 50 := by
      have h24 : sigma ≤ 1 := by linarith
      field_simp [hsigma_pos.ne'] <;> linarith
  have h25 : (2 : ℝ)^sigma ≤ 2 := by
    have h26 : sigma ≤ 1 := by linarith
    have h27 : (2 : ℝ)^sigma ≤ (2 : ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h26
    have h28 : (2 : ℝ)^(1 : ℝ) = 2 := by simp
    rw [h28] at h27; exact h27
  have h28 : 3 * (2 : ℝ)^sigma ≤ 6 := by
    have h29 : 3 * (2 : ℝ)^sigma ≤ 3 * 2 := mul_le_mul_of_nonneg_left h25 (by norm_num)
    linarith
  have h29 : B ^ (-beta) = (3 : ℝ) ^ (20 * beta / (sigma * stickyLoss)) := by
    simp only [hB_def]
    have h_mul : ((3 : ℝ) ^ (-(20 / (sigma * stickyLoss)))) ^ (-beta) =
        (3 : ℝ) ^ ((-(20 / (sigma * stickyLoss))) * (-beta)) := by
      have h : (3 : ℝ) ^ ((-(20 / (sigma * stickyLoss))) * (-beta)) =
          ((3 : ℝ) ^ (-(20 / (sigma * stickyLoss)))) ^ (-beta) :=
        Real.rpow_mul (by norm_num) (-(20 / (sigma * stickyLoss))) (-beta)
      exact h.symm
    rw [h_mul]
    have h2 : (-(20 / (sigma * stickyLoss))) * (-beta) = 20 * beta / (sigma * stickyLoss) := by ring
    rw [h2]
  have h_base : (1 : ℝ) ≤ (3 : ℝ) := by norm_num
  have h30 : 3 * (2 : ℝ)^sigma ≤ delta ^ (-beta) := by
    calc 3 * (2 : ℝ)^sigma
      ≤ 6 := h28
    _ ≤ (3 : ℝ) ^ (50 : ℝ) := by norm_num
    _ ≤ (3 : ℝ) ^ (20 * beta / (sigma * stickyLoss)) := Real.rpow_le_rpow_of_exponent_le h_base (show (50 : ℝ) ≤ 20 * beta / (sigma * stickyLoss) from h20)
    _ = B ^ (-beta) := h29.symm
    _ ≤ delta ^ (-beta) := h16
  have h_main1 : 3 * (2 : ℝ)^sigma * delta ^ (-sigma * stickyLoss / 2) ≤ delta ^ (-outputLoss) := by
    have h_rpow_add : delta ^ (-beta) * delta ^ (-sigma * stickyLoss / 2) = delta ^ (-beta + (-sigma * stickyLoss / 2)) := by
      rw [← Real.rpow_add hdelta_pos] <;> ring
    have h_exp : -beta + (-sigma * stickyLoss / 2) = -outputLoss := by
      simp [hbeta_def] <;> ring
    have h_pos4 : 0 ≤ delta ^ (-sigma * stickyLoss / 2) := Real.rpow_nonneg hdelta_pos.le _
    have h : 3 * (2 : ℝ)^sigma * delta ^ (-sigma * stickyLoss / 2) ≤ delta ^ (-beta) * delta ^ (-sigma * stickyLoss / 2) :=
      mul_le_mul_of_nonneg_right h30 h_pos4
    rw [h_rpow_add, h_exp] at h
    exact h
  have h36 : 3 * x ^ sigma ≤ delta ^ (-outputLoss) := by
    calc 3 * x ^ sigma
      ≤ 3 * (2 : ℝ)^sigma * delta ^ (-sigma * stickyLoss / 2) := h5'
    _ ≤ delta ^ (-outputLoss) := h_main1
  have h38 : x ^ sigma * x ^ (1 - sigma) = x := by
    have h39 : x ^ sigma * x ^ (1 - sigma) = x ^ (sigma + (1 - sigma)) := by
      rw [← Real.rpow_add hx_pos] <;> ring
    rw [h39]
    have h40 : sigma + (1 - sigma) = 1 := by linarith
    rw [h40, Real.rpow_one]
  have h_pos3 : 0 ≤ x ^ (1 - sigma) := Real.rpow_nonneg hx_pos.le _
  have h37 : 3 * x ≤ delta ^ (-outputLoss) * x ^ (1 - sigma) := by
    calc 3 * x
      = 3 * (x ^ sigma * x ^ (1 - sigma)) := by rw [h38]
    _ = 3 * x ^ sigma * x ^ (1 - sigma) := by ring
    _ ≤ delta ^ (-outputLoss) * x ^ (1 - sigma) := mul_le_mul_of_nonneg_right h36 h_pos3
  exact h37

/-- Mechanical AD bound from a key inequality.

Given E contained in an interval of length `2*√rho` centered at `center`, and
`h_key : 3*x ≤ δ^(-outputLoss)*x^(1-σ)` for `1 ≤ x ≤ 2/√rho`, proves
`PureWZ2PaperADSet1 E rho (1-σ) C`. -/
lemma pureWz2_ad_from_key
    {delta rho sigma outputLoss : ℝ}
    {E : Set ℝ} {C : ENNReal}
    (hC_eq : C = Kakeya.realRpowENN delta (-outputLoss))
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (houtputLoss_nonneg : 0 ≤ outputLoss)
    (hrho_pos : 0 < rho)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (center : ℝ)
    (hE_sub : E ⊆ Set.Icc (center - Real.sqrt rho) (center + Real.sqrt rho))
    (h_key : ∀ (x : ℝ), 1 ≤ x → x ≤ 2 / Real.sqrt rho →
        3 * x ≤ (delta ^ (-outputLoss)) * (x ^ (1 - sigma))) :
    PureWZ2PaperADSet1 E rho (1 - sigma) C := by
  let L : ℝ := 2 * Real.sqrt rho
  have hL_pos : 0 < L := by positivity
  have hC_one : (1 : ENNReal) ≤ C := by
    rw [hC_eq, Kakeya.realRpowENN]
    have h2 : delta ^ outputLoss ≤ 1 := Real.rpow_le_one hdelta_pos.le hdelta_le_one houtputLoss_nonneg
    have h3 : (1 : ℝ) ≤ delta ^ (-outputLoss) := by
      have h4 : delta ^ (-outputLoss) = (delta ^ outputLoss)⁻¹ := by
        rw [Real.rpow_neg hdelta_pos.le] <;> ring
      rw [h4]
      have h5 : 0 < delta ^ outputLoss := Real.rpow_pos_of_pos hdelta_pos _
      have h6 : (delta ^ outputLoss)⁻¹ ≥ 1 := by
        calc (delta ^ outputLoss)⁻¹ ≥ (1 : ℝ)⁻¹ := by gcongr
          _ = 1 := by simp
      exact h6
    have h7 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
    rw [h7]; exact ENNReal.ofReal_le_ofReal h3
  have hC_top : C ≠ ⊤ := by
    rw [hC_eq, Kakeya.realRpowENN]; simp [ENNReal.ofReal_ne_top]
  refine' ⟨by linarith, by linarith, by linarith, hC_one, hC_top, _⟩
  intro r hr hdelta_le_r left length hlength_ge_r
  let T : Set ℝ := E ∩ Set.Icc left (left + length)
  have hT_sub_E : T ⊆ E := by intro x hx; exact hx.1
  have hr_pos : 0 < r := by linarith
  by_cases hL_le_r : L ≤ r
  · have h_center : T ⊆ Metric.closedBall center r := by
      intro y hy
      have h_y1 : center - Real.sqrt rho ≤ y := (hE_sub (hT_sub_E hy)).1
      have h_y2 : y ≤ center + Real.sqrt rho := (hE_sub (hT_sub_E hy)).2
      have h : dist y center ≤ r := by
        simp only [Real.dist_eq, abs_le]; constructor <;> linarith
      simpa [Metric.mem_closedBall] using h
    let r' : NNReal := ⟨r, hr⟩
    have h_iscover : Metric.IsCover r' T ({center} : Set ℝ) := by
      intro y hy
      have h_dist : dist y center ≤ r := h_center hy
      have h_edist : edist y center ≤ (r' : ENNReal) := by
        have h_edist_eq : edist y center = ENNReal.ofReal (dist y center) := by
          exact edist_dist y center
        rw [h_edist_eq]
        have h1 : (r' : ℝ) = r := NNReal.coe_mk r hr
        have hnonneg : 0 ≤ (r' : ℝ) := NNReal.coe_nonneg r'
        have h2 : (r' : ENNReal) = ENNReal.ofReal (r' : ℝ) := by
          simp [ENNReal.ofReal, NNReal.coe_nonneg]
        rw [h2, h1]
        exact ENNReal.ofReal_le_ofReal_iff hr |>.mpr h_dist
      exact ⟨center, by simp, h_edist⟩
    have hcov : (Metric.externalCoveringNumber r' T : ENNReal) ≤ 1 := by
      calc (Metric.externalCoveringNumber r' T : ENNReal)
        ≤ ({center} : Set ℝ).encard := by exact_mod_cast h_iscover.externalCoveringNumber_le_encard
      _ = 1 := by simp
    have h15 : 1 ≤ length / r := by
      calc 1 = r / r := by field_simp [hr_pos.ne'] <;> ring
        _ ≤ length / r := by gcongr
    have h16 : 0 ≤ 1 - sigma := by linarith
    have h17 : (1 : ℝ) ≤ Real.rpow (length / r) (1 - sigma) := by
      apply Real.one_le_rpow <;> linarith
    have h18 : (1 : ENNReal) ≤ Kakeya.realRpowENN (length / r) (1 - sigma) := by
      simp only [Kakeya.realRpowENN]; exact ENNReal.one_le_ofReal.mpr h17
    have h14 : (1 : ENNReal) ≤ C * Kakeya.realRpowENN (length / r) (1 - sigma) := by
      calc (1 : ENNReal)
        = 1 * 1 := by simp
      _ ≤ C * 1 := by gcongr <;> exact hC_one
      _ ≤ C * Kakeya.realRpowENN (length / r) (1 - sigma) := by gcongr <;> exact h18
    exact hcov.trans h14
  · have h_r_lt_L : r < L := by linarith
    have h6_div : L / rho = 2 / Real.sqrt rho := by
      dsimp only [L]
      have hsqrt_pos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho_pos
      have hsq : (Real.sqrt rho)^2 = rho := Real.sq_sqrt (by linarith)
      calc (2 * Real.sqrt rho) / rho
        = (2 * Real.sqrt rho) / (Real.sqrt rho)^2 := by rw [hsq]
      _ = 2 / Real.sqrt rho := by field_simp [hsqrt_pos.ne'] <;> ring
    by_cases hcase : length ≤ L
    · have hx1 : 1 ≤ length / r := by
        calc 1 = r / r := by field_simp [hr_pos.ne'] <;> ring
          _ ≤ length / r := by gcongr
      have hx2 : length / r ≤ 2 / Real.sqrt rho := by
        have h4 : length / r ≤ L / r := by gcongr
        have h5 : L / r ≤ L / rho := div_le_div_of_nonneg_left (by positivity) hrho_pos hdelta_le_r
        have h6 : L / rho = 2 / Real.sqrt rho := h6_div
        rw [h6] at h5; exact h4.trans h5
      have hT_sub2 : T ⊆ Set.Icc left (left + length) := by intro x hx; exact hx.2
      have hcov : (↑(Metric.externalCoveringNumber ⟨r, hr⟩ T) : ENNReal) ≤
          ENNReal.ofReal (length / r) + 2 :=
        externalCoveringNumber_subset_interval hr_pos (by linarith) hT_sub2
      have h9 : length / r + 2 ≤ 3 * (length / r) := by linarith
      have h10 := h_key (length / r) hx1 hx2
      have h_add : ENNReal.ofReal (length / r) + 2 = ENNReal.ofReal (length / r + 2) := by
        have h8 : 0 ≤ length / r := by positivity
        rw [ENNReal.ofReal_add h8 (by norm_num)] <;> simp
      have hC_def : C * Kakeya.realRpowENN (length / r) (1 - sigma) =
          ENNReal.ofReal ((delta ^ (-outputLoss)) * ((length / r) ^ (1 - sigma))) := by
        simp only [hC_eq, Kakeya.realRpowENN]
        have h_pos1 : 0 ≤ Real.rpow delta (-outputLoss) := Real.rpow_nonneg hdelta_pos.le _
        rw [← ENNReal.ofReal_mul h_pos1] <;> rfl
      have h_main : (↑(Metric.externalCoveringNumber ⟨r, hr⟩ T) : ENNReal) ≤
          C * Kakeya.realRpowENN (length / r) (1 - sigma) := by
        rw [hC_def]
        calc
          (↑(Metric.externalCoveringNumber ⟨r, hr⟩ T) : ENNReal)
            ≤ ENNReal.ofReal (length / r) + 2 := hcov
          _ = ENNReal.ofReal (length / r + 2) := h_add
          _ ≤ ENNReal.ofReal (3 * (length / r)) := ENNReal.ofReal_le_ofReal h9
          _ ≤ ENNReal.ofReal ((delta ^ (-outputLoss)) * ((length / r) ^ (1 - sigma))) :=
              ENNReal.ofReal_le_ofReal h10
      exact h_main
    · have hT_sub2 : T ⊆ Set.Icc (center - Real.sqrt rho) (center + Real.sqrt rho) := by
        intro x hx; exact hE_sub (hT_sub_E hx)
      have hcov : (↑(Metric.externalCoveringNumber ⟨r, hr⟩ T) : ENNReal) ≤
          ENNReal.ofReal (L / r) + 2 :=
        externalCoveringNumber_subset_interval (left := center - Real.sqrt rho) (length := L) hr_pos hL_pos.le (by
          have h_end : center - Real.sqrt rho + L = center + Real.sqrt rho := by
            have hL_eq : L = 2 * Real.sqrt rho := by rfl
            rw [hL_eq] <;> ring
          rw [h_end]
          exact hT_sub2)
      have hy1 : 1 ≤ L / r := by
        calc 1 = r / r := by field_simp [hr_pos.ne'] <;> ring
          _ ≤ L / r := by gcongr
      have hy2 : L / r ≤ 2 / Real.sqrt rho := by
        have h5 : L / r ≤ L / rho := div_le_div_of_nonneg_left (by positivity) hrho_pos hdelta_le_r
        have h6 : L / rho = 2 / Real.sqrt rho := h6_div
        rw [h6] at h5; exact h5
      have h9 : L / r + 2 ≤ 3 * (L / r) := by linarith
      have h10 := h_key (L / r) hy1 hy2
      have h_add : ENNReal.ofReal (L / r) + 2 = ENNReal.ofReal (L / r + 2) := by
        have h8 : 0 ≤ L / r := by positivity
        rw [ENNReal.ofReal_add h8 (by norm_num)] <;> simp
      have hC_def : C * Kakeya.realRpowENN (L / r) (1 - sigma) =
          ENNReal.ofReal ((delta ^ (-outputLoss)) * ((L / r) ^ (1 - sigma))) := by
        simp only [hC_eq, Kakeya.realRpowENN]
        have h_pos1 : 0 ≤ Real.rpow delta (-outputLoss) := Real.rpow_nonneg hdelta_pos.le _
        rw [← ENNReal.ofReal_mul h_pos1] <;> rfl
      have h_main : (↑(Metric.externalCoveringNumber ⟨r, hr⟩ T) : ENNReal) ≤
          C * Kakeya.realRpowENN (L / r) (1 - sigma) := by
        rw [hC_def]
        calc
          (↑(Metric.externalCoveringNumber ⟨r, hr⟩ T) : ENNReal)
            ≤ ENNReal.ofReal (L / r) + 2 := hcov
          _ = ENNReal.ofReal (L / r + 2) := h_add
          _ ≤ ENNReal.ofReal (3 * (L / r)) := ENNReal.ofReal_le_ofReal h9
          _ ≤ ENNReal.ofReal ((delta ^ (-outputLoss)) * ((L / r) ^ (1 - sigma))) :=
              ENNReal.ofReal_le_ofReal h10
      have h11 : C * Kakeya.realRpowENN (L / r) (1 - sigma) ≤
          C * Kakeya.realRpowENN (length / r) (1 - sigma) := by
        have h12 : L / r ≤ length / r := by
          have h121 : L < length := by linarith
          exact div_lt_div_of_pos_right h121 hr_pos |>.le
        have h13 : 0 ≤ 1 - sigma := by linarith
        have h14 : Kakeya.realRpowENN (L / r) (1 - sigma) ≤
            Kakeya.realRpowENN (length / r) (1 - sigma) := by
          simp only [Kakeya.realRpowENN]
          exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) h12 h13)
        exact mul_le_mul_left' h14 C
      exact h_main.trans h11

end Kakeya.Assouad.PureWZ2
