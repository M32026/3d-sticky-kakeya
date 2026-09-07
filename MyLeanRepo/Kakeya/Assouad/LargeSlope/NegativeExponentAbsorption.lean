import MyLeanRepo.Kakeya.Assouad.Statements

/-!
# Constant absorption for negative exponents

For any positive constant `C` and negative exponent `e`, there exists `delta₀ > 0`
such that for all `0 < delta ≤ delta₀`, `C < Real.rpow delta e`.

This is used in the final power absorption of the large-slope convex overload.
-/

namespace Kakeya.Assouad

/--
For any `C > 0` and `e < 0`, there exists `delta₀ > 0` such that for all
`0 < delta ≤ delta₀`, `C < Real.rpow delta e`.
-/
lemma exists_delta_absorb_constant {C e : ℝ} (hC : 0 < C) (he : e < 0) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ → C < Real.rpow delta e := by
  set f : ℝ := -e with hf_def
  have hf_pos : 0 < f := by linarith
  have hC_inv_pos : 0 < C⁻¹ := by positivity
  set delta_star : ℝ := Real.rpow C⁻¹ (1 / f) with hdelta_star_def
  have hdelta_star_pos : 0 < delta_star := Real.rpow_pos_of_pos hC_inv_pos (1 / f)
  have h_rpow_delta_star : Real.rpow delta_star f = C⁻¹ := by
    rw [hdelta_star_def]
    have h : Real.rpow (Real.rpow C⁻¹ (1 / f)) f = Real.rpow C⁻¹ ((1 / f) * f) := by
      exact (Real.rpow_mul (by positivity) (1 / f) f).symm
    rw [h]
    have h2 : (1 / f) * f = 1 := by field_simp [hf_pos.ne']
    rw [h2]; simp
  set delta₀ : ℝ := min (delta_star / 2) (1 / 2) with hdelta₀_def
  have hdelta₀_pos : 0 < delta₀ := by positivity
  have hdelta₀_le_one : delta₀ ≤ 1 := by
    rw [hdelta₀_def]; exact min_le_right _ _ |>.trans (by norm_num)
  have hdelta₀_lt_star : delta₀ < delta_star := by
    rw [hdelta₀_def]
    have h : min (delta_star / 2) (1 / 2) ≤ delta_star / 2 := min_le_left _ _
    have h2 : delta_star / 2 < delta_star := by linarith [hdelta_star_pos]
    linarith
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_le_one, ?_⟩
  intro delta hdelta hdelta_le
  have hdelta_lt_star : delta < delta_star := by
    calc delta ≤ delta₀ := hdelta_le
         _ < delta_star := hdelta₀_lt_star
  -- For f > 0, x^f is increasing in x, so delta < delta_star implies delta^f < delta_star^f
  have h_rpow_mono : Real.rpow delta f < Real.rpow delta_star f :=
    Real.rpow_lt_rpow hdelta.le hdelta_lt_star hf_pos
  rw [h_rpow_delta_star] at h_rpow_mono
  have h_e_eq : Real.rpow delta e = (Real.rpow delta f)⁻¹ := by
    have h : e = -f := by linarith
    rw [h]
    exact Real.rpow_neg hdelta.le f
  rw [h_e_eq]
  have h_pos : 0 < Real.rpow delta f := Real.rpow_pos_of_pos hdelta f
  have h_lt : Real.rpow delta f < C⁻¹ := h_rpow_mono
  have h_goal : C < (Real.rpow delta f)⁻¹ := by
    have h9 : (Real.rpow delta f)⁻¹ > (C⁻¹)⁻¹ := by
      gcongr
    have h10 : (C⁻¹)⁻¹ = C := by
      field_simp [hC.ne']
    rw [h10] at h9
    exact h9
  exact h_goal

/--
ENNReal version: for any finite `C` and negative `e`, there exists `delta₀ > 0`
such that for all `0 < delta ≤ delta₀`, `C < Kakeya.realRpowENN delta e`.
-/
lemma exists_delta_absorb_constant_ennreal {C : ENNReal} (hC : C ≠ ⊤) (e : ℝ) (he : e < 0) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ → C < Kakeya.realRpowENN delta e := by
  by_cases hC0 : C = 0
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    intro delta hdelta _
    have h_pos : 0 < Real.rpow delta e := Real.rpow_pos_of_pos hdelta e
    have h : 0 < Kakeya.realRpowENN delta e := by
      simp only [Kakeya.realRpowENN, ENNReal.ofReal_pos] <;> exact h_pos
    rw [hC0]; exact h
  · have hC_pos : 0 < C := bot_lt_iff_ne_bot.mpr hC0
    let C_real : ℝ := ENNReal.toReal C
    have hC_real_pos : 0 < C_real := ENNReal.toReal_pos hC0 hC
    rcases exists_delta_absorb_constant hC_real_pos he with
      ⟨delta₀, hdelta₀_pos, hdelta₀_one, hmain⟩
    refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
    intro delta hdelta hdelta_le
    have h1 : C_real < Real.rpow delta e := hmain delta hdelta hdelta_le
    have h2 : C = ENNReal.ofReal C_real := by
      rw [ENNReal.ofReal_toReal hC]
    rw [h2]
    have h3 : ENNReal.ofReal C_real < ENNReal.ofReal (Real.rpow delta e) := by
      exact ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hdelta e) |>.mpr h1
    simpa [Kakeya.realRpowENN] using h3

/--
The key exponent inequality for large-slope convex overload:
`25*eta + 36*eta/sigma + eta/1000 - epsilon*sigma < 0`
from `1000*eta ≤ epsilon*sigma^2`, `0 < sigma < 1`, `0 < eta`.
-/
lemma large_slope_exponent_negative
    {epsilon sigma eta : ℝ}
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (heta : 0 < eta) (h : 1000 * eta ≤ epsilon * sigma ^ 2) :
    25 * eta + 36 * eta / sigma + eta / 1000 - epsilon * sigma < 0 := by
  have h1 : epsilon * sigma ≥ 1000 * eta / sigma := by
    have h2 : 0 < sigma := hsigma
    calc
      epsilon * sigma
        = (epsilon * sigma ^ 2) / sigma := by field_simp [h2.ne'] <;> ring
      _ ≥ (1000 * eta) / sigma := by gcongr
      _ = 1000 * eta / sigma := by ring
  have h3 : 25 * eta + 36 * eta / sigma + eta / 1000 - epsilon * sigma ≤
      25 * eta + 36 * eta / sigma + eta / 1000 - 1000 * eta / sigma := by
    gcongr
  have h4 : 25 * eta + 36 * eta / sigma + eta / 1000 - 1000 * eta / sigma < 0 := by
    have h8 : 1 / sigma > 1 := one_lt_one_div hsigma hsigma1
    have h9 : 964 * eta / sigma > 964 * eta := by
      have h10 : 964 * eta / sigma = 964 * eta * (1 / sigma) := by
        field_simp [hsigma.ne'] <;> ring
      rw [h10]
      have h11 : 964 * eta > 0 := by positivity
      nlinarith
    have h12 : 25 * eta + eta / 1000 < 964 * eta := by
      have h13 : eta / 1000 < eta := by
        have h14 : eta / 1000 < eta / 1 := by gcongr <;> norm_num
        simpa using h14
      linarith
    have h14 : 25 * eta + 36 * eta / sigma + eta / 1000 - 1000 * eta / sigma =
        25 * eta + eta / 1000 - 964 * eta / sigma := by ring
    rw [h14]
    linarith
  linarith

/--
Card-cancellation exponent inequality for large-slope convex overload:
`loss + 13*eta + 36*eta/sigma - epsilon*sigma < 0`
from `1000*eta ≤ epsilon*sigma^2`, `0 < sigma < 1`, `0 < eta`, `loss ≤ eta`.
-/
lemma large_slope_exponent_negative_card
    {epsilon sigma eta loss : ℝ}
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (heta : 0 < eta) (hloss : loss ≤ eta)
    (h : 1000 * eta ≤ epsilon * sigma ^ 2) :
    loss + 13 * eta + 36 * eta / sigma - epsilon * sigma < 0 := by
  have h1 : epsilon * sigma ≥ 1000 * eta / sigma := by
    have h2 : 0 < sigma := hsigma
    calc
      epsilon * sigma
        = (epsilon * sigma ^ 2) / sigma := by field_simp [h2.ne'] <;> ring
      _ ≥ (1000 * eta) / sigma := by gcongr
      _ = 1000 * eta / sigma := by ring
  have h3 : loss + 13 * eta + 36 * eta / sigma - epsilon * sigma ≤
      eta + 13 * eta + 36 * eta / sigma - 1000 * eta / sigma := by
    gcongr
    <;> linarith
  have h4 : eta + 13 * eta + 36 * eta / sigma - 1000 * eta / sigma < 0 := by
    have h8 : 1 / sigma > 1 := one_lt_one_div hsigma hsigma1
    have h9 : 964 * eta / sigma > 964 * eta := by
      have h10 : 964 * eta / sigma = 964 * eta * (1 / sigma) := by
        field_simp [hsigma.ne'] <;> ring
      rw [h10]
      have h11 : 964 * eta > 0 := by positivity
      nlinarith
    have h12 : 14 * eta < 964 * eta := by
      have h13 : 0 < eta := heta
      linarith
    have h14 : eta + 13 * eta + 36 * eta / sigma - 1000 * eta / sigma =
        14 * eta - 964 * eta / sigma := by ring
    rw [h14]
    linarith
  linarith

end Kakeya.Assouad
