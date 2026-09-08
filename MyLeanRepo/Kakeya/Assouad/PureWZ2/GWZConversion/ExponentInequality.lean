import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Exponent inequality for GWZ density restoration

For any finite constant `K`, positive `outputLoss`, and natural `logExponent`,
there exists `inputLoss < outputLoss` and `delta₀ > 0` such that for all
`0 < δ ≤ delta₀`:

```
K * δ^outputLoss ≤ (log(1/δ))^(-logExponent) * δ^inputLoss
```

This follows from the standard asymptotics that any negative power of `δ`
dominates any power of `log(1/δ)` as `δ → 0`.

This is the scaling lemma that lets the density-restoration pillar absorb the
family-mass ratio `K` from the selection pillar.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Parameterized exponent inequality: for any `inputLoss` strictly between 0 and
`outputLoss`, there exists `delta₀` such that the density-restoration scaling
holds for all `0 < δ ≤ delta₀`.
-/
lemma gwz_exponent_inequality_of_inputLoss
    (K : ENNReal) (hK : K ≠ ⊤)
    (outputLoss inputLoss : ℝ)
    (hinputLoss_pos : 0 < inputLoss)
    (hinputLoss_lt : inputLoss < outputLoss)
    (logExponent : ℕ) :
    ∃ (delta₀ : ℝ), 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ delta₀ →
        K * Kakeya.realRpowENN δ outputLoss ≤
          wz2PaperPureRefinementFraction δ logExponent *
          Kakeya.realRpowENN δ inputLoss := by
  set ε : ℝ := outputLoss - inputLoss with hε_def
  have hε_pos : 0 < ε := by
    rw [hε_def]; linarith

  by_cases hK0 : K = 0
  · refine ⟨1, by norm_num, by norm_num, ?_⟩
    intro δ hδ hδ1
    rw [hK0]; simp
  · have hK_pos : 0 < K := zero_lt_iff.mpr hK0
    let K_real : ℝ := K.toReal
    have hK_real_pos : 0 < K_real := ENNReal.toReal_pos hK_pos.ne' hK
    have hK_eq : K = ENNReal.ofReal K_real := by
      rw [ENNReal.ofReal_toReal hK]

    let r : ℝ := (logExponent : ℝ)
    have h_asymp : (fun x : ℝ => |Real.log x| ^ r) =o[nhdsWithin 0 (Set.Ioi 0)] (fun x : ℝ => x ^ (-ε)) :=
      isLittleO_abs_log_rpow_rpow_nhdsGT_zero r (by linarith)

    let c : ℝ := 1 / K_real
    have hc_pos : 0 < c := by positivity

    have h_raw : ∀ᶠ (x : ℝ) in nhdsWithin 0 (Set.Ioi 0),
        ‖(fun x : ℝ => |Real.log x| ^ r) x‖ ≤ c * ‖(fun x : ℝ => x ^ (-ε)) x‖ :=
      h_asymp.def hc_pos

    rcases eventually_nhdsWithin_iff.mp h_raw with h_eventually
    rcases eventually_nhds_iff.mp h_eventually with ⟨t, ht_mem, ht_open, ht_zero⟩
    rcases Metric.isOpen_iff.mp ht_open 0 ht_zero with ⟨δ₀, hδ₀_pos, hball⟩

    let δ₁ : ℝ := min (δ₀ / 2) (1 / 2)
    have hδ₁_pos : 0 < δ₁ := by positivity
    have hδ₁_one : δ₁ ≤ 1 := by
      have h : δ₁ ≤ 1 / 2 := min_le_right _ _
      linarith
    have hδ₁_lt_one : δ₁ < 1 := by
      have h : δ₁ ≤ 1 / 2 := min_le_right _ _
      linarith
    have hδ₁_lt_δ₀ : δ₁ < δ₀ := by
      have h : δ₁ ≤ δ₀ / 2 := min_le_left _ _
      linarith

    refine ⟨δ₁, hδ₁_pos, hδ₁_one, ?_⟩
    intro δ hδ hδ_small

    have hδ_lt_δ₀ : δ < δ₀ := by
      calc δ ≤ δ₁ := hδ_small
           _ < δ₀ := hδ₁_lt_δ₀
    have hδ_lt_one : δ < 1 := by
      calc δ ≤ δ₁ := hδ_small
           _ < 1 := hδ₁_lt_one
    have hδ_pos : 0 < δ := hδ

    have hδ_in_ball : δ ∈ Metric.ball (0 : ℝ) δ₀ := by
      simpa [Metric.mem_ball, abs_lt] using ⟨by linarith, by linarith⟩
    have hδ_in_t : δ ∈ t := hball hδ_in_ball
    have h_imp : δ ∈ Set.Ioi 0 → ‖(fun x : ℝ => |Real.log x| ^ r) δ‖ ≤ c * ‖(fun x : ℝ => x ^ (-ε)) δ‖ :=
      ht_mem δ hδ_in_t
    have hδ_in_Ioi : δ ∈ Set.Ioi 0 := hδ_pos
    have h_norm_ineq : ‖|Real.log δ| ^ r‖ ≤ c * ‖δ ^ (-ε)‖ := h_imp hδ_in_Ioi

    have h2 : ‖|Real.log δ| ^ r‖ = |Real.log δ| ^ r := by
      have h3 : 0 ≤ |Real.log δ| ^ r := by positivity
      simp [abs_of_nonneg h3]
    have h4 : ‖δ ^ (-ε)‖ = δ ^ (-ε) := by
      have h5 : 0 < δ ^ (-ε) := by positivity
      simp [abs_of_pos h5]
    rw [h2, h4] at h_norm_ineq
    have h_ineq : |Real.log δ| ^ r ≤ c * δ ^ (-ε) := h_norm_ineq

    have h_log_abs : |Real.log δ| = Real.log (1 / δ) := by
      have h1 : Real.log δ < 0 := Real.log_neg hδ_pos (by linarith)
      rw [abs_of_neg h1]
      have h2 : -Real.log δ = Real.log (1 / δ) := by
        rw [Real.log_div (by norm_num) (ne_of_gt hδ_pos), Real.log_one, zero_sub]
      exact h2

    rw [h_log_abs] at h_ineq
    have hr_eq : (Real.log (1 / δ)) ^ r = (Real.log (1 / δ)) ^ logExponent := by
      simp [r]
    rw [hr_eq] at h_ineq

    have h4 : K_real * (Real.log (1 / δ)) ^ logExponent ≤ δ ^ (-ε) := by
      have h5 : (Real.log (1 / δ)) ^ logExponent ≤ (1 / K_real) * δ ^ (-ε) := h_ineq
      have h6 : K_real * (Real.log (1 / δ)) ^ logExponent ≤ K_real * ((1 / K_real) * δ ^ (-ε)) := by
        gcongr
      have h7 : K_real * ((1 / K_real) * δ ^ (-ε)) = δ ^ (-ε) := by
        field_simp [hK_real_pos.ne']
      rw [h7] at h6
      exact h6

    have h_pos1 : 0 ≤ K_real := by linarith
    have h8 : ENNReal.ofReal (K_real * (Real.log (1 / δ)) ^ logExponent) ≤ ENNReal.ofReal (δ ^ (-ε)) :=
      ENNReal.ofReal_mono h4

    have h_pos_log : 0 ≤ Real.log (1 / δ) := by
      have h13 : 1 < 1 / δ := by
        apply one_lt_one_div hδ_pos
        linarith
      exact (Real.log_pos h13).le
    have h9 : ENNReal.ofReal (K_real * (Real.log (1 / δ)) ^ logExponent) =
        K * (ENNReal.ofReal (Real.log (1 / δ))) ^ logExponent := by
      rw [ENNReal.ofReal_mul h_pos1, ENNReal.ofReal_pow h_pos_log, hK_eq]

    rw [h9] at h8

    let L : ENNReal := ENNReal.ofReal (Real.log (1 / δ))
    have hL_pos : 0 < L := by
      apply ENNReal.ofReal_pos.mpr
      have h13 : 1 < 1 / δ := by
        apply one_lt_one_div hδ_pos
        linarith
      exact Real.log_pos h13
    have hL_ne_top : L ≠ ⊤ := ENNReal.ofReal_ne_top
    have hL_ne_zero : L ≠ 0 := hL_pos.ne'

    have h13 : K * L ^ logExponent * Kakeya.realRpowENN δ outputLoss ≤ Kakeya.realRpowENN δ inputLoss := by
      have h14 : K * L ^ logExponent ≤ Kakeya.realRpowENN δ (-ε) := h8
      have h15 : Kakeya.realRpowENN δ (-ε) * Kakeya.realRpowENN δ outputLoss = Kakeya.realRpowENN δ inputLoss := by
        simp only [Kakeya.realRpowENN]
        have h16 : Real.rpow δ (-ε) * Real.rpow δ outputLoss = Real.rpow δ ((-ε) + outputLoss) :=
          (Real.rpow_add hδ (-ε) outputLoss).symm
        have h17 : (-ε) + outputLoss = inputLoss := by
          rw [hε_def] <;> linarith
        have h_pos1 : 0 ≤ Real.rpow δ (-ε) := Real.rpow_nonneg hδ.le (-ε)
        rw [← ENNReal.ofReal_mul h_pos1, h16, h17]
      calc
        K * L ^ logExponent * Kakeya.realRpowENN δ outputLoss
          ≤ Kakeya.realRpowENN δ (-ε) * Kakeya.realRpowENN δ outputLoss := by gcongr
        _ = Kakeya.realRpowENN δ inputLoss := h15

    have h16 : (L ^ logExponent)⁻¹ * (K * L ^ logExponent * Kakeya.realRpowENN δ outputLoss) ≤
        (L ^ logExponent)⁻¹ * Kakeya.realRpowENN δ inputLoss := by gcongr

    have h17 : (L ^ logExponent) ≠ 0 := pow_ne_zero logExponent hL_ne_zero
    have h18 : (L ^ logExponent) ≠ ⊤ := ENNReal.pow_ne_top hL_ne_top

    have h19 : (L ^ logExponent)⁻¹ * (K * L ^ logExponent * Kakeya.realRpowENN δ outputLoss) =
        K * Kakeya.realRpowENN δ outputLoss := by
      have h_cancel : (L ^ logExponent)⁻¹ * (L ^ logExponent) = 1 :=
        ENNReal.inv_mul_cancel h17 h18
      have h_comm : (L ^ logExponent)⁻¹ * (K * L ^ logExponent * Kakeya.realRpowENN δ outputLoss) =
          K * ((L ^ logExponent)⁻¹ * (L ^ logExponent)) * Kakeya.realRpowENN δ outputLoss := by
        simp [mul_assoc, mul_comm, mul_left_comm]
      rw [h_comm, h_cancel]; simp

    rw [h19] at h16

    have h20 : (L ^ logExponent)⁻¹ = wz2PaperPureRefinementFraction δ logExponent := by
      simp [wz2PaperPureRefinementFraction, L, ENNReal.inv_pow]

    rw [h20] at h16
    exact h16

/--
Exponent inequality: for any finite `K`, positive `outputLoss`, and `logExponent`,
there exists `inputLoss < outputLoss` and `delta₀` such that the density-restoration
scaling holds for all `0 < δ ≤ delta₀`.

This is a simple wrapper around `gwz_exponent_inequality_of_inputLoss` that chooses
`inputLoss = outputLoss / 2`.
-/
lemma gwz_exponent_inequality
    (K : ENNReal) (hK : K ≠ ⊤)
    (outputLoss : ℝ) (houtputLoss : 0 < outputLoss)
    (logExponent : ℕ) :
    ∃ (inputLoss : ℝ), 0 < inputLoss ∧ inputLoss < outputLoss ∧
      ∃ (delta₀ : ℝ), 0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ (δ : ℝ), 0 < δ → δ ≤ delta₀ →
          K * Kakeya.realRpowENN δ outputLoss ≤
            wz2PaperPureRefinementFraction δ logExponent *
            Kakeya.realRpowENN δ inputLoss := by
  let inputLoss : ℝ := outputLoss / 2
  have hinputLoss_pos : 0 < inputLoss := half_pos houtputLoss
  have hinputLoss_lt : inputLoss < outputLoss := half_lt_self houtputLoss
  rcases gwz_exponent_inequality_of_inputLoss K hK outputLoss inputLoss
      hinputLoss_pos hinputLoss_lt logExponent with ⟨delta₀, hdelta₀_pos, hdelta₀_one, h⟩
  exact ⟨inputLoss, hinputLoss_pos, hinputLoss_lt, delta₀, hdelta₀_pos, hdelta₀_one, h⟩

end Kakeya.Assouad

end
