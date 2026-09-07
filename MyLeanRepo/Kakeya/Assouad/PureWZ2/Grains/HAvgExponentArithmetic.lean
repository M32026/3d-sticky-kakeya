import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exponent arithmetic for h_avg

Proves that for sufficiently small L,
`m * L^(σ - 3*loss) < 1/8`.

This is the key ingredient for combining with the mass lower bound
`mass ≥ (1/4) * L^(2*loss)` to prove `m * volume < mass / 2`,
which gives ≥ 1/2 mass retention for the high-multiplicity set.

Key exponent: `e = (σ + 2*stickyLoss - 6*loss)/2 > 0`.
When `e > 0`, `L^e → 0` as `L → 0`, so the product vanishes.

The exponent condition `6*loss < σ + 2*stickyLoss` follows from
`loss ≤ stickyLoss` and `stickyLoss < σ/4`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Real

/-- The multiplicity constant m as a function of L. -/
def h_avg_m_val (sigma stickyLoss L : ℝ) : ℕ :=
  let epsilon₁ := (sigma - 2 * stickyLoss) / 20
  let K := Nat.ceil (L ^ (-2 * epsilon₁))
  12 * max (2 * 4 * 601 ^ 3 * 12001 ^ 3) ((1600 * K + 1) ^ 5) + 12

/-- For 0 < L < 1 and e < 0, we have L^e > 1. -/
lemma rpow_ge_one_of_le_one'
    {L e : ℝ} (hL_pos : 0 < L) (hL_lt_one : L < 1) (he : e < 0) :
    1 < L ^ e := by
  have h1 : 0 < -e := by linarith
  have h2 : L ^ (-e) < 1 := Real.rpow_lt_one (by linarith) hL_lt_one h1
  have h3 : L ^ e = (L ^ (-e))⁻¹ := by
    rw [← Real.rpow_neg hL_pos.le] <;> ring_nf
  rw [h3]
  have h4 : 0 < L ^ (-e) := Real.rpow_pos_of_pos hL_pos _
  have h5 : 1 < (L ^ (-e))⁻¹ := by
    have h6 : (L ^ (-e))⁻¹ = 1 / (L ^ (-e)) := by simp
    rw [h6]
    have h7 : 1 / (L ^ (-e)) > 1 / 1 := by gcongr
    simpa using h7
  exact h5

/-- Exponent positivity: `6*loss < σ + 2*stickyLoss`. -/
lemma h_avg_exponent_pos
    (sigma stickyLoss loss : ℝ)
    (hsigma_pos : 0 < sigma)
    (hstickyLoss_pos : 0 < stickyLoss)
    (hloss_nonneg : 0 ≤ loss)
    (hloss_le_sticky : loss ≤ stickyLoss)
    (hstickyLoss_lt_quarter : stickyLoss < sigma / 4) :
    0 < (sigma + 2 * stickyLoss - 6 * loss) / 2 := by
  have h1 : 6 * loss ≤ 6 * stickyLoss := by gcongr
  have h2 : 6 * stickyLoss < sigma + 2 * stickyLoss := by linarith
  have h3 : 6 * loss < sigma + 2 * stickyLoss := by linarith
  linarith

/-- Main exponent arithmetic lemma.

Given `6*loss < σ + 2*stickyLoss`, for sufficiently small L:
`m * L^(σ - 3*loss) < 1/4`.
-/
lemma h_avg_exponent_arithmetic
    (sigma stickyLoss loss : ℝ)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hstickyLoss_pos : 0 < stickyLoss)
    (hstickyLoss_lt_half_sigma : stickyLoss < sigma / 2)
    (hloss_nonneg : 0 ≤ loss)
    (hexponent_pos : 0 < (sigma + 2 * stickyLoss - 6 * loss) / 2) :
    ∃ (L₀ : ℝ), 0 < L₀ ∧ L₀ ≤ 1 ∧
      ∀ (L : ℝ), 0 < L → L ≤ L₀ →
        (h_avg_m_val sigma stickyLoss L : ℝ) * L ^ (sigma - 3 * loss) < 1 / 8 := by
  set e : ℝ := (sigma + 2 * stickyLoss - 6 * loss) / 2 with he_def
  have he_pos : 0 < e := hexponent_pos
  set epsilon₁ : ℝ := (sigma - 2 * stickyLoss) / 20 with heps₁_def
  have heps₁_pos : 0 < epsilon₁ := by
    rw [heps₁_def]
    have h : 2 * stickyLoss < sigma := by linarith
    have h2 : sigma - 2 * stickyLoss > 0 := by linarith
    linarith
  set a : ℝ := (2 * 4 * 601 ^ 3 * 12001 ^ 3 : ℝ) with ha_def
  set C0 : ℝ := 12 * (a + 2) with hC0_def
  set C : ℝ := C0 * (3201 : ℝ)^5 with hC_def
  have hC_pos : 0 < C := by positivity
  -- Use 1/16 factor to get strict < 1/8
  set L₀ : ℝ := (1 / (16 * C)) ^ (1 / e) with hL₀_def
  have hL₀_pos : 0 < L₀ := by positivity
  have hL₀_lt_one : L₀ < 1 := by
    have h1 : 1 / (16 * C) < 1 := by
      dsimp only [C] <;> norm_num
    have h2 : 0 < 1 / e := by positivity
    exact Real.rpow_lt_one (by positivity) h1 h2
  have hL₀_one : L₀ ≤ 1 := hL₀_lt_one.le
  refine ⟨L₀, hL₀_pos, hL₀_one, ?_⟩
  intro L hL_pos hL_le
  have hL_lt_one : L < 1 := hL_le.trans_lt hL₀_lt_one
  set K : ℕ := Nat.ceil (L ^ (-2 * epsilon₁)) with hK_def
  have h_neg2eps : -2 * epsilon₁ < 0 := by linarith
  have hL_ge_one : 1 < L ^ (-2 * epsilon₁) :=
    rpow_ge_one_of_le_one' hL_pos hL_lt_one h_neg2eps
  have hK_bound : (K : ℝ) ≤ 2 * L ^ (-2 * epsilon₁) := by
    have h3 : (K : ℝ) < L ^ (-2 * epsilon₁) + 1 := by
      rw [hK_def]
      exact Nat.ceil_lt_add_one (by positivity)
    have h4 : 1 ≤ L ^ (-2 * epsilon₁) := hL_ge_one.le
    linarith
  have h1 : (1600 * (K : ℝ) + 1) ≤ 3201 * L ^ (-2 * epsilon₁) := by
    calc
      1600 * (K : ℝ) + 1
        ≤ 1600 * (2 * L ^ (-2 * epsilon₁)) + 1 := by gcongr <;> linarith
      _ = 3200 * L ^ (-2 * epsilon₁) + 1 := by ring
      _ ≤ 3201 * L ^ (-2 * epsilon₁) := by
        have h4 : 1 < L ^ (-2 * epsilon₁) := hL_ge_one
        nlinarith
  have h1' : ((1600 * K + 1 : ℕ) : ℝ) ≤ 3201 * L ^ (-2 * epsilon₁) := by
    exact_mod_cast h1
  have h5 : ((1600 * K + 1 : ℕ) : ℝ)^5 ≤ (3201 : ℝ)^5 * L ^ (-10 * epsilon₁) := by
    have h6 : ((1600 * K + 1 : ℕ) : ℝ)^5 ≤ (3201 * L ^ (-2 * epsilon₁))^5 := by gcongr
    have h7 : (3201 * L ^ (-2 * epsilon₁))^5 = (3201 : ℝ)^5 * (L ^ (-2 * epsilon₁))^5 := by ring
    have h8 : (L ^ (-2 * epsilon₁))^5 = L ^ (-10 * epsilon₁) := by
      have h81 : (L ^ (-2 * epsilon₁))^5 = (L ^ (-2 * epsilon₁)) ^ (5 : ℝ) := by norm_cast
      rw [h81]
      rw [← Real.rpow_mul hL_pos.le] <;> ring
    rw [h7, h8] at h6
    exact h6
  set b : ℝ := ((1600 * K + 1 : ℕ) : ℝ)^5 with hb_def
  have hb_ge_one : 1 ≤ b := by
    dsimp only [b]
    have h : (1600 * K + 1 : ℕ) ≥ 1 := by omega
    exact_mod_cast Nat.one_le_pow 5 _ h
  have h4 : ((h_avg_m_val sigma stickyLoss L : ℕ) : ℝ) ≤ C0 * b := by
    dsimp only [h_avg_m_val]
    have h1_nat : 12 * max (2 * 4 * 601 ^ 3 * 12001 ^ 3) ((1600 * K + 1) ^ 5) + 12 ≤
        12 * ((2 * 4 * 601 ^ 3 * 12001 ^ 3) + (1600 * K + 1) ^ 5) + 12 := by omega
    have h1 : ((12 * max (2 * 4 * 601 ^ 3 * 12001 ^ 3) ((1600 * K + 1) ^ 5) + 12 : ℕ) : ℝ) ≤
        12 * (((2 * 4 * 601 ^ 3 * 12001 ^ 3 : ℕ) : ℝ) + (((1600 * K + 1 : ℕ) : ℝ)^5)) + 12 := by
      exact_mod_cast h1_nat
    have h_b_eq : (((1600 * K + 1 : ℕ) : ℝ)^5) = b := by
      simpa [hb_def] using rfl
    have h_a_eq : ((2 * 4 * 601 ^ 3 * 12001 ^ 3 : ℕ) : ℝ) = a := by
      rw [ha_def] <;> norm_cast
    rw [h_a_eq, h_b_eq] at h1
    have h2 : 12 * (a + b) + 12 ≤ C0 * b := by
      dsimp only [C0]
      rw [ha_def]
      have h3 : 1 ≤ b := hb_ge_one
      nlinarith
    exact h1.trans h2
  have h9 : C0 * b ≤ C * L ^ (-10 * epsilon₁) := by
    rw [hC_def]
    have h10 : b ≤ (3201 : ℝ)^5 * L ^ (-10 * epsilon₁) := h5
    have hC0_nonneg : 0 ≤ C0 := by dsimp only [C0, a]; positivity
    have h11 : C0 * b ≤ C0 * ((3201 : ℝ)^5 * L ^ (-10 * epsilon₁)) :=
      mul_le_mul_of_nonneg_left h10 hC0_nonneg
    have h12 : C0 * ((3201 : ℝ)^5 * L ^ (-10 * epsilon₁)) = C * L ^ (-10 * epsilon₁) := by
      rw [hC_def] <;> ring
    rw [h12] at h11
    exact h11
  have h_m_bound : (h_avg_m_val sigma stickyLoss L : ℝ) ≤ C * L ^ (-10 * epsilon₁) :=
    h4.trans h9
  have h_exp_eq : -10 * epsilon₁ + (sigma - 3 * loss) = e := by
    rw [heps₁_def, he_def] <;> ring
  have h_rpow_add : L ^ (-10 * epsilon₁) * L ^ (sigma - 3 * loss) = L ^ e := by
    rw [← Real.rpow_add hL_pos, h_exp_eq]
  have h4' : (h_avg_m_val sigma stickyLoss L : ℝ) * L ^ (sigma - 3 * loss) ≤
      C * L ^ e := by
    calc
      (h_avg_m_val sigma stickyLoss L : ℝ) * L ^ (sigma - 3 * loss)
        ≤ (C * L ^ (-10 * epsilon₁)) * L ^ (sigma - 3 * loss) := by gcongr
      _ = C * (L ^ (-10 * epsilon₁) * L ^ (sigma - 3 * loss)) := by ring
      _ = C * L ^ e := by rw [h_rpow_add]
  have h5 : C * L ^ e < 1 / 8 := by
    have h6 : L ^ e ≤ L₀ ^ e := Real.rpow_le_rpow (by linarith) hL_le (by linarith)
    have h7 : L₀ ^ e = 1 / (16 * C) := by
      rw [hL₀_def]
      have h8 : ((1 / (16 * C)) ^ (1 / e)) ^ e = 1 / (16 * C) := by
        rw [← Real.rpow_mul (by positivity)]
        have h9 : (1 / e) * e = 1 := by field_simp [he_pos.ne'] <;> ring
        rw [h9] <;> simp
      exact h8
    rw [h7] at h6
    have h10 : C * L ^ e ≤ C * (1 / (16 * C)) := by gcongr
    have h11 : C * (1 / (16 * C)) = 1 / 16 := by
      field_simp [hC_pos.ne'] <;> ring
    rw [h11] at h10
    have h12 : C * L ^ e < 1 / 8 := by linarith
    exact h12
  exact h4'.trans_lt h5

end Kakeya.Assouad.PureWZ2

end
