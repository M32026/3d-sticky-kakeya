import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HardRegimeHelper
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HAvgCombination
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.AbsorptionArithmetic
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolume
import Mathlib.Tactic

/-!
# Global hard case PropertyP reconstruction

Helper def to reconstruct PropertyP data from sticky data for the global AD
hard case. Contains all arithmetic proofs needed by `constructPropertyPFromSticky`.

This avoids duplicating ~200 lines of arithmetic in the target theorem.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

/-- Reconstruct PropertyP from sticky data with all arithmetic hypotheses.

This is a convenience wrapper around `constructPropertyPFromSticky` that
derives the arithmetic hypotheses from a small set of basic parameters. -/
noncomputable def reconstructPropertyPForGlobalAD
    {delta sigma outputLoss stickyLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (tau epsilon₁ epsilon₃ : ℝ)
    (K m : ℕ)
    (C_P : ℝ)
    (hC_P_def : C_P = (3 : ℝ) ^ (20 / sigma))
    (havg_L0_final : ℝ)
    (h_havg_main : outputLoss ≤ sigma / 2 → ∀ (L : ℝ), 0 < L → L ≤ havg_L0_final →
      (h_avg_m_val sigma stickyLoss L : ℝ) * L ^ (sigma - 3 * stickyLoss) < 1 / 8)
    -- Basic parameters
    (hdelta_pos : 0 < delta)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hstickyLoss_pos : 0 < stickyLoss)
    (hstickyLoss_half : stickyLoss ≤ 1 / 2)
    (h_out_le_half : outputLoss ≤ sigma / 2)
    (h_sticky_le_sigma4 : stickyLoss ≤ sigma / 4)
    (hL_pos : 0 < rho.1)
    (hL_small : rho.1 ≤ 1 / 10000)
    (hL_le_C : rho.1 ≤ 1 / C_P)
    (hL_coarse_le_L0 : rho.1 ≤ havg_L0_final)
    (htau_def : tau = rho.1 * Real.sqrt 3)
    (heps₁_def : epsilon₁ = (sigma - 2 * stickyLoss) / 20)
    (heps₃_def : epsilon₃ = 1 - 2 * epsilon₁)
    (hK_def : K = Nat.ceil (rho.1 ^ (-2 * epsilon₁)))
    (hm_def : m = 12 * max (2 * 4 * 601 ^ 3 * 12001 ^ 3) ((1600 * K + 1) ^ 5) + 12) :
    PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃) (tau := tau) := by
  let L : ℝ := rho.1

  -- Derived bounds
  have htau_pos : 0 < tau := by
    rw [htau_def]; positivity
  have hL_le_tau : L ≤ tau := by
    rw [htau_def]
    have h : 1 ≤ Real.sqrt 3 := by
      have h2 : (1 : ℝ) ≤ 3 := by norm_num
      have h3 : Real.sqrt 1 ≤ Real.sqrt 3 := Real.sqrt_le_sqrt h2
      have h4 : Real.sqrt 1 = 1 := by
        rw [Real.sqrt_one]
      linarith
    have h5 : L ≤ L * Real.sqrt 3 := by
      calc L = L * 1 := by ring
        _ ≤ L * Real.sqrt 3 := by gcongr
    exact h5
  have htau_large : L * Real.sqrt 3 ≤ tau := by
    rw [htau_def]
  have htau_sq : tau ^ 2 ≤ 4 * L := by
    rw [htau_def]
    have h4 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h5 : (L * Real.sqrt 3) ^ 2 = 3 * L ^ 2 := by
      rw [mul_pow, h4] <;> ring
    rw [h5]
    have h6 : 0 < L := hL_pos
    have h7 : 3 * L ≤ 4 := by linarith [hL_small]
    have h8 : 3 * L ^ 2 ≤ 4 * L := by
      calc 3 * L ^ 2 = (3 * L) * L := by ring
        _ ≤ 4 * L := by gcongr
    exact h8
  have htau_le_one : tau ≤ 1 := by
    rw [htau_def]
    have h2 : Real.sqrt 3 ≤ 2 := by rw [Real.sqrt_le_iff] <;> norm_num
    have h3 : L * Real.sqrt 3 ≤ L * 2 := by gcongr
    have h4 : L * 2 ≤ 1 := by linarith [hL_small]
    linarith

  -- K bounds
  have hK_one : 1 ≤ K := by
    have h_exp_nonpos : -2 * epsilon₁ ≤ 0 := by
      rw [heps₁_def]; linarith
    have h' : L ^ (0 : ℝ) ≤ L ^ (-2 * epsilon₁) :=
      Real.rpow_le_rpow_of_exponent_ge hL_pos (by linarith [hL_small]) h_exp_nonpos
    have h1 : L ^ (0 : ℝ) = 1 := Real.rpow_zero L
    rw [h1] at h'
    have hK_real : (K : ℝ) = Nat.ceil (L ^ (-2 * epsilon₁)) := by
      exact_mod_cast hK_def
    have h2 : (1 : ℝ) ≤ (K : ℝ) := by
      rw [hK_real]
      exact h'.trans (Nat.le_ceil _)
    exact_mod_cast h2
  have hKL_small : (K : ℝ) * L ≤ 1 / 2 := by
    have hK_real : (K : ℝ) = Nat.ceil (L ^ (-2 * epsilon₁)) := by exact_mod_cast hK_def
    have h1 : (K : ℝ) ≤ L ^ (-2 * epsilon₁) + 1 := by
      rw [hK_real]
      have h_nonneg : 0 ≤ L ^ (-2 * epsilon₁) := by positivity
      have h_lt : (Nat.ceil (L ^ (-2 * epsilon₁)) : ℝ) < L ^ (-2 * epsilon₁) + 1 :=
        Nat.ceil_lt_add_one h_nonneg
      exact h_lt.le
    have h2 : (K : ℝ) * L ≤ (L ^ (-2 * epsilon₁) + 1) * L := by gcongr
    have h3 : (L ^ (-2 * epsilon₁) + 1) * L = L ^ epsilon₃ + L := by
      have h4 : L ^ (-2 * epsilon₁) * L = L ^ epsilon₃ := by
        have h5 : L ^ ((-2 * epsilon₁) + 1) = L ^ (-2 * epsilon₁) * L := by
          rw [Real.rpow_add hL_pos, Real.rpow_one] <;> ring
        have h6 : (-2 * epsilon₁) + 1 = epsilon₃ := by
          rw [heps₃_def, heps₁_def] <;> ring
        rw [h6] at h5; exact h5.symm
      calc (L ^ (-2 * epsilon₁) + 1) * L
        = L ^ (-2 * epsilon₁) * L + L := by ring
      _ = L ^ epsilon₃ + L := by rw [h4]
    rw [h3] at h2
    have h4 : L ^ epsilon₃ ≤ 1 / 4 := by
      have h5 : epsilon₃ ≥ 9 / 10 := by
        rw [heps₃_def, heps₁_def]
        have h6 : sigma - 2 * stickyLoss < 1 := by linarith [hsigma_lt_one]
        linarith
      have h7 : L ^ epsilon₃ ≤ L ^ (9 / 10 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hL_pos (by linarith [hL_small]) h5
      have h8 : L ≤ 1 / 10000 := hL_small
      have h9 : L ^ (9 / 10 : ℝ) ≤ (1 / 10000 : ℝ) ^ (9 / 10 : ℝ) :=
        Real.rpow_le_rpow (by linarith) h8 (by linarith)
      have h10 : (1 / 10000 : ℝ) ^ (9 / 10 : ℝ) ≤ 1 / 4 := by
        have h11 : (1 / 10000 : ℝ) ^ (9 / 10 : ℝ) ≤ (1 / 10000 : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
        have h12 : (1 / 10000 : ℝ) ^ (1 / 2 : ℝ) = 1 / 100 := by
          have h13 : (1 / 10000 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (1 / 10000 : ℝ) := by
            rw [Real.sqrt_eq_rpow] <;> norm_num
          rw [h13]
          have h14 : Real.sqrt (1 / 10000 : ℝ) = 1 / 100 := by
            rw [Real.sqrt_eq_cases] <;> norm_num
          rw [h14]
        rw [h12] at h11
        linarith
      linarith
    have h5 : L ≤ 1 / 4 := by linarith [hL_small]
    linarith

  -- m bounds
  have hm_pos : 0 < m := by
    rw [hm_def]; positivity
  have hm_gt_packing : (2 * 4 * 601 ^ 3 * 12001 ^ 3 : ENNReal) < (m : ENNReal) := by
    have h : (2 * 4 * 601 ^ 3 * 12001 ^ 3 : ℕ) < m := by
      rw [hm_def] <;> omega
    exact_mod_cast h
  have hm_gt_general : ((1600 * K + 1)^5 : ENNReal) < (m : ENNReal) := by
    have h : ((1600 * K + 1)^5 : ℕ) < m := by
      rw [hm_def] <;> omega
    exact_mod_cast h

  -- epsilon bounds
  have heps₁_pos : 0 < epsilon₁ := by
    rw [heps₁_def]; linarith
  have heps₃_pos : 0 < epsilon₃ := by
    rw [heps₃_def, heps₁_def]; linarith
  have heps_sum : epsilon₁ + epsilon₃ < 1 := by
    rw [heps₃_def]; linarith

  -- Cell full bound
  have h_cell_full : Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤ Kakeya.realRpowENN L 3 := by
    have h_main_real : L ^ (2 + 2 * epsilon₁) * tau ≤ L ^ (3 : ℝ) :=
      cell_full_real_ineq L tau sigma stickyLoss epsilon₁ C_P
        hL_pos hL_le_C h_sticky_le_sigma4 hsigma_pos hC_P_def heps₁_def htau_def
    simp only [Kakeya.realRpowENN]
    have h16a : 0 ≤ Real.rpow L (2 + 2 * epsilon₁) := Real.rpow_nonneg hL_pos.le _
    have h17 : ENNReal.ofReal (Real.rpow L (2 + 2 * epsilon₁) * tau) =
        ENNReal.ofReal (Real.rpow L (2 + 2 * epsilon₁)) * ENNReal.ofReal tau :=
      ENNReal.ofReal_mul h16a
    have h18 : Real.rpow L (2 + 2 * epsilon₁) * tau ≤ Real.rpow L (3 : ℝ) := by
      simpa [Real.rpow_natCast] using h_main_real
    have h19 : ENNReal.ofReal (Real.rpow L (2 + 2 * epsilon₁) * tau) ≤
        ENNReal.ofReal (Real.rpow L (3 : ℝ)) :=
      ENNReal.ofReal_le_ofReal h18
    rw [←h17]
    exact h19

  -- kappa bound
  have h_kappa : Real.rpow L epsilon₃ ≤ (K : ℝ) * L := by
    have hK_real : (K : ℝ) = Nat.ceil (Real.rpow L (-2 * epsilon₁)) := by exact_mod_cast hK_def
    have h1 : epsilon₃ = 1 - 2 * epsilon₁ := by rw [heps₃_def]
    rw [h1]
    have h2 : Real.rpow L (1 - 2 * epsilon₁) = Real.rpow L (-2 * epsilon₁) * L := by
      have h3 : Real.rpow L ((-2 * epsilon₁) + 1) = Real.rpow L (-2 * epsilon₁) * Real.rpow L 1 :=
        Real.rpow_add hL_pos (-2 * epsilon₁) 1
      have h4 : Real.rpow L 1 = L := Real.rpow_one L
      rw [h4] at h3
      have h5 : (-2 * epsilon₁) + 1 = 1 - 2 * epsilon₁ := by ring
      rw [h5] at h3
      exact h3
    rw [h2]
    have h5 : Real.rpow L (-2 * epsilon₁) ≤ (K : ℝ) := by
      rw [hK_real]; exact Nat.le_ceil _
    have h6 : 0 ≤ L := by linarith
    nlinarith

  -- Volume upper bound
  have h_volume_ne_top : MeasureTheory.volume sticky.croppedCoarseShading.union ≠ ⊤ := by
    have h1 : MeasureTheory.volume sticky.croppedCoarseShading.union ≤ Kakeya.realRpowENN L (sigma - stickyLoss) :=
      sticky.coarse_extremal.volume_upper
    have h2 : Kakeya.realRpowENN L (sigma - stickyLoss) ≠ ⊤ := by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
    exact ne_top_of_le_ne_top h2 h1

  -- Mass upper bound
  have h_mass_ne_top : sticky.croppedCoarseShading.mass ≠ ⊤ := by
    have h_mult : ∀ p ∈ sticky.croppedCoarseShading.union,
        (sticky.croppedCoarseShading.pointMultiplicity p : ENNReal) ≤
          Kakeya.realRpowENN L (2 - sigma - stickyLoss) * sticky.coarse.enncard := by
      intro p _
      have h := sticky.coarse_multiplicity_upper p
      simpa [L] using h
    have h_mass_le : sticky.croppedCoarseShading.mass ≤
        (Kakeya.realRpowENN L (2 - sigma - stickyLoss) * sticky.coarse.enncard) *
          MeasureTheory.volume sticky.croppedCoarseShading.union :=
      mass_le_of_pointMultiplicity_le h_mult
    have h_exp_pos : 0 ≤ 2 - stickyLoss - stickyLoss := by linarith [hstickyLoss_half]
    have hL_pow_le : Kakeya.realRpowENN L (2 - sigma - stickyLoss) *
        Kakeya.realRpowENN L (sigma - stickyLoss) ≤ 1 := by
      have h_add : (2 - sigma - stickyLoss) + (sigma - stickyLoss) = 2 - 2 * stickyLoss := by ring
      have h_pos1 : 0 ≤ Real.rpow L (2 - sigma - stickyLoss) := Real.rpow_nonneg hL_pos.le _
      have h_pos2 : 0 ≤ Real.rpow L (sigma - stickyLoss) := Real.rpow_nonneg hL_pos.le _
      have h_eq1 : Kakeya.realRpowENN L (2 - sigma - stickyLoss) * Kakeya.realRpowENN L (sigma - stickyLoss) =
          ENNReal.ofReal (Real.rpow L (2 - sigma - stickyLoss) * Real.rpow L (sigma - stickyLoss)) := by
        simp only [Kakeya.realRpowENN]
        rw [← ENNReal.ofReal_mul h_pos1]
      rw [h_eq1]
      have h_eq2 : Real.rpow L (2 - sigma - stickyLoss) * Real.rpow L (sigma - stickyLoss) =
          Real.rpow L (2 - 2 * stickyLoss) := by
        have h : Real.rpow L ((2 - sigma - stickyLoss) + (sigma - stickyLoss)) =
            Real.rpow L (2 - sigma - stickyLoss) * Real.rpow L (sigma - stickyLoss) :=
          Real.rpow_add hL_pos (2 - sigma - stickyLoss) (sigma - stickyLoss)
        rw [h_add] at h
        exact h.symm
      rw [h_eq2]
      have h6 : Real.rpow L (2 - 2 * stickyLoss) ≤ 1 :=
        Real.rpow_le_one hL_pos.le (by linarith [hL_small]) (by linarith [hstickyLoss_half])
      simpa [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal h6
    have h_vol : MeasureTheory.volume sticky.croppedCoarseShading.union ≤ Kakeya.realRpowENN L (sigma - stickyLoss) :=
      sticky.coarse_extremal.volume_upper
    have h_fin : (Kakeya.realRpowENN L (2 - sigma - stickyLoss) * sticky.coarse.enncard) *
        MeasureTheory.volume sticky.croppedCoarseShading.union ≠ ⊤ := by
      apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
        · simp [Kakeya.Streamlined.TubeFamily.enncard] <;> exact ENNReal.natCast_ne_top _
      · exact ne_top_of_le_ne_top (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]) h_vol
    exact ne_top_of_le_ne_top h_fin h_mass_le

  -- h_avg bound
  have hL_coarse_le_24 : L ≤ 1 / 24 := by
    have h : L ≤ 1 / 10000 := hL_small
    linarith
  have h_eps_eq : epsilon₁ = (sigma - 2 * stickyLoss) / 20 := heps₁_def
  have hm_bound : (m : ℝ) * L ^ (sigma - 3 * stickyLoss) < 1 / 8 := by
    have h_eq : (m : ℝ) = (h_avg_m_val sigma stickyLoss L : ℝ) := by
      simp [hm_def, h_avg_m_val, hK_def, h_eps_eq] <;> rfl
    rw [h_eq]
    exact h_havg_main h_out_le_half L hL_pos hL_coarse_le_L0
  have h_avg_strong : (m : ENNReal) * MeasureTheory.volume sticky.croppedCoarseShading.union < (1 / 2 : ENNReal) * sticky.croppedCoarseShading.mass :=
    h_avg_from_sticky sticky.coarse_extremal sticky.cover m hL_pos hL_coarse_le_24 hm_bound
  -- Construct PropertyP
  exact constructPropertyPFromSticky
    delta sigma stickyLoss
    (sticky := sticky)
    tau epsilon₁ epsilon₃ K m
    hL_pos hL_small htau_pos hL_le_tau htau_large htau_sq htau_le_one
    hK_one hKL_small hm_pos hm_gt_packing hm_gt_general
    heps₁_pos heps₃_pos heps_sum
    h_mass_ne_top h_volume_ne_top h_avg_strong
    h_kappa h_cell_full

end Kakeya.Assouad.PureWZ2

end
