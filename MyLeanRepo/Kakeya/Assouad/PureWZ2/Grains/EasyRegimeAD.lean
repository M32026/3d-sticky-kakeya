import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.BoundedIntervalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.TrivialCovering
import Mathlib.Tactic

/-!
# Easy regime local AD bound

When `outputLoss > σ/2`, a direct interval covering bound suffices for all
query scales. This is extracted from `LocalADFromSticky` to keep that file
within memory limits.

## Main result

- `easy_regime_ad`: proves `PureWZ2PaperADSet1 E ρ (1-σ) C` in the easy regime.
-/

namespace Kakeya.Assouad.PureWZ2

open Real Metric Set ENNReal

/-- Easy regime AD bound: `outputLoss > σ/2`.

Given `E` contained in an interval of length `2√ρ`, and the easy-regime
smallness condition `3·2^σ ≤ (1/δ)^(outputLoss - σ/2)`, proves
`PureWZ2PaperADSet1 E ρ (1-σ) C`. -/
lemma easy_regime_ad
    {delta sigma outputLoss rho : ℝ}
    {E : Set ℝ} {C : ENNReal}
    (hC_eq : C = Kakeya.realRpowENN delta (-outputLoss))
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (houtputLoss_pos : 0 < outputLoss)
    (hrho_pos : 0 < rho)
    (hrho : delta ≤ rho)
    (hsmall_easy : 3 * (2 : ℝ)^sigma ≤ (1 / delta)^(outputLoss - sigma / 2))
    (h_half : sigma / 2 < outputLoss)
    (center : ℝ)
    (hE_contained : E ⊆ Set.Icc (center - Real.sqrt rho) (center + Real.sqrt rho)) :
    PureWZ2PaperADSet1 E rho (1 - sigma) C := by
  let L : ℝ := 2 * Real.sqrt rho
  have hL_pos : 0 < L := by positivity
  have hE_interval : E ⊆ Set.Icc (center - Real.sqrt rho) (center - Real.sqrt rho + L) := by
    have h_eq : center - Real.sqrt rho + L = center + Real.sqrt rho := by
      dsimp only [L] <;> ring
    rw [h_eq]
    exact hE_contained
  have h_key : ∀ (x : ℝ), 1 ≤ x → x ≤ 2 / Real.sqrt rho →
      3 * x ≤ (delta ^ (-outputLoss)) * (x ^ (1 - sigma)) := by
    intro x hx1 hx2
    exact local_ad_key_ineq hdelta_pos hrho_pos hrho hsigma_pos h_half hsmall_easy hx1 hx2
  refine' ⟨by linarith, by linarith, by linarith, _ , _ , _⟩
  · -- 1 ≤ C
    have h1 : 1 ≤ Real.rpow delta (-outputLoss) := by
      have h2 : Real.rpow delta (0 : ℝ) ≤ Real.rpow delta (-outputLoss) :=
        Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one (by linarith)
      have h3 : Real.rpow delta (0 : ℝ) = 1 := by simp
      rw [h3] at h2; exact h2
    simp only [hC_eq, Kakeya.realRpowENN]
    exact ENNReal.one_le_ofReal.mpr h1
  · -- C ≠ ⊤
    simp [hC_eq, Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
  · -- Covering bound
    intro r hr hdelta_le_r left length hlength_ge_r
    let T : Set ℝ := E ∩ Set.Icc left (left + length)
    have hT_sub : T ⊆ Set.Icc (center - Real.sqrt rho) (center - Real.sqrt rho + L) := by
      intro x hx
      exact hE_interval hx.1
    have hr_pos : 0 < r := by linarith
    by_cases hL_le_r : L ≤ r
    · -- L ≤ r: one ball suffices
      have h_center : T ⊆ Metric.closedBall center r := by
        intro y hy
        have h_y1 : center - Real.sqrt rho ≤ y := (hT_sub hy).1
        have h_y2 : y ≤ center - Real.sqrt rho + L := (hT_sub hy).2
        have h : dist y center ≤ r := by
          simp only [Real.dist_eq, abs_le]
          constructor <;> linarith [hL_le_r]
        simpa [Metric.mem_closedBall] using h
      let ε : NNReal := ⟨r, hr⟩
      have h_iscover : Metric.IsCover ε T ({center} : Set ℝ) := by
        intro z hz
        have h_dist : dist z center ≤ r := h_center hz
        have h_edist : edist z center ≤ (ε : ENNReal) := by
          rw [edist_dist]
          have h_coe : (↑ε : ENNReal) = ENNReal.ofReal (↑ε : ℝ) := by simp
          rw [h_coe]
          have h_eps : (↑ε : ℝ) = r := Subtype.coe_mk r hr
          rw [h_eps]
          exact ENNReal.ofReal_le_ofReal h_dist
        exact ⟨center, by simp, h_edist⟩
      have h_le : (Metric.externalCoveringNumber ε T : ENNReal) ≤ 1 := by
        calc (Metric.externalCoveringNumber ε T : ENNReal)
          ≤ ({center} : Set ℝ).encard := by exact_mod_cast h_iscover.externalCoveringNumber_le_encard
        _ = 1 := by simp
      have h13 : (1 : ENNReal) ≤ Kakeya.realRpowENN (length / r) (1 - sigma) := by
        simp only [Kakeya.realRpowENN]
        have h14 : 1 ≤ length / r := by
          calc 1 = r / r := by field_simp [hr_pos.ne'] <;> ring
            _ ≤ length / r := by gcongr
        have h15 : 0 ≤ 1 - sigma := by linarith
        have h16 : 1 ≤ Real.rpow (length / r) (1 - sigma) :=
          Real.one_le_rpow h14 h15
        exact ENNReal.one_le_ofReal.mpr h16
      have hC_one : (1 : ENNReal) ≤ C := by
        have h1 : 1 ≤ Real.rpow delta (-outputLoss) := by
          have h2 : Real.rpow delta (0 : ℝ) ≤ Real.rpow delta (-outputLoss) :=
            Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one (by linarith)
          have h3 : Real.rpow delta (0 : ℝ) = 1 := by simp
          rw [h3] at h2; exact h2
        simp only [hC_eq, Kakeya.realRpowENN]
        exact ENNReal.one_le_ofReal.mpr h1
      have h11 : (1 : ENNReal) ≤ C * Kakeya.realRpowENN (length / r) (1 - sigma) := by
        have h1 : (1 : ENNReal) ≤ C := hC_one
        have h2 : (1 : ENNReal) ≤ Kakeya.realRpowENN (length / r) (1 - sigma) := h13
        have h3 : (1 : ENNReal) * (1 : ENNReal) ≤ C * Kakeya.realRpowENN (length / r) (1 - sigma) := by gcongr
        simpa using h3
      exact h_le.trans h11
    · -- L > r: use interval covering bound
      have h_r_lt_L : r < L := by linarith
      have h_r_le_L : r ≤ L := h_r_lt_L.le
      have h_rho_le_r : rho ≤ r := hdelta_le_r
      have h6_div : L / rho = 2 / Real.sqrt rho := by
        have hsqrt_pos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho_pos
        have hsq : (Real.sqrt rho) ^ 2 = rho := Real.sq_sqrt hrho_pos.le
        have h : (2 * Real.sqrt rho) * Real.sqrt rho = 2 * rho := by
          calc (2 * Real.sqrt rho) * Real.sqrt rho
            = 2 * (Real.sqrt rho) ^ 2 := by ring
          _ = 2 * rho := by rw [hsq] <;> ring
        have hdiv : (2 * Real.sqrt rho) / rho = 2 / Real.sqrt rho := by
          rw [div_eq_div_iff hrho_pos.ne' hsqrt_pos.ne']
          exact h
        have hL : L = 2 * Real.sqrt rho := by rfl
        rw [hL]
        exact hdiv
      by_cases hcase : length ≤ L
      · -- length ≤ L
        have hx1 : 1 ≤ length / r := by
          calc 1 = r / r := by field_simp [hr_pos.ne'] <;> ring
            _ ≤ length / r := by gcongr
        have hx2 : length / r ≤ 2 / Real.sqrt rho := by
          have h4 : length / r ≤ L / r := by gcongr
          have h5 : L / r ≤ L / rho := by gcongr
          have h6 : L / rho = 2 / Real.sqrt rho := h6_div
          rw [h6] at h5
          exact h4.trans h5
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
        rw [hC_def]
        calc
          (↑(Metric.externalCoveringNumber ⟨r, hr⟩ T) : ENNReal)
            ≤ ENNReal.ofReal (length / r) + 2 := hcov
          _ = ENNReal.ofReal (length / r + 2) := h_add
          _ ≤ ENNReal.ofReal (3 * (length / r)) := ENNReal.ofReal_le_ofReal h9
          _ ≤ ENNReal.ofReal ((delta ^ (-outputLoss)) * ((length / r) ^ (1 - sigma))) :=
              ENNReal.ofReal_le_ofReal h10
      · -- length > L
        have hL_lt_length : L < length := by linarith
        have hy1 : 1 ≤ L / r := by
          calc 1 = r / r := by field_simp [hr_pos.ne'] <;> ring
            _ ≤ L / r := by gcongr
        have hy2 : L / r ≤ 2 / Real.sqrt rho := by
          have h5 : L / r ≤ L / rho := by gcongr
          have h6 : L / rho = 2 / Real.sqrt rho := h6_div
          rw [h6] at h5
          exact h5
        have hcov : (↑(Metric.externalCoveringNumber ⟨r, hr⟩ T) : ENNReal) ≤
            ENNReal.ofReal (L / r) + 2 :=
          externalCoveringNumber_subset_interval hr_pos hL_pos.le hT_sub
        have h9 : L / r + 2 ≤ 3 * (L / r) := by linarith
        have h10 := h_key (L / r) hy1 hy2
        have h11 : C * Kakeya.realRpowENN (L / r) (1 - sigma) ≤
            C * Kakeya.realRpowENN (length / r) (1 - sigma) := by
          have h12 : L / r ≤ length / r := by
            have h121 : L < length := hL_lt_length
            exact div_lt_div_of_pos_right h121 hr_pos |>.le
          have h13 : 0 ≤ 1 - sigma := by linarith
          have h14 : Kakeya.realRpowENN (L / r) (1 - sigma) ≤
              Kakeya.realRpowENN (length / r) (1 - sigma) := by
            simp only [Kakeya.realRpowENN]
            exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) h12 h13)
          exact mul_le_mul_left' h14 C
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
        exact h_main.trans h11

end Kakeya.Assouad.PureWZ2
