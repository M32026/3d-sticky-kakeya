import MyLeanRepo.Kakeya.Cinematic.Section5.PolynomialDyadicPieceRangeInputs

/-!
# Polynomially controlled dyadic piece-volume range

Proves `PolynomialDyadicPieceRangeStatement`: given polynomial bounds on the
number of pieces and retained mass, all non-tiny pieces fit into only
logarithmically many dyadic layers.

## Proof route

Set `a := countExponent + massExponent` and `b := Real.logb 2 (1 / delta)`.

- If `lower = ⊤`, take `L = 1`; then `2^L * lower = ⊤ > upper`.
- Otherwise, convert to `ℝ`. From `total = 2 * N * lower`, `N ≤ delta^{-countExponent}`,
  and `delta^massExponent < total`, derive `1 / lower < 2^{a*b + 1}`.
  Take `L := Nat.ceil (a * b + 1)`. Then `2^L * lower > 1 ≥ upper`, and
  `L ≤ a * b + 2 ≤ (a + 2) * (b + 1)`.

## Whiteprint node

`main` — Polynomially controlled dyadic piece-volume range.
-/

namespace Kakeya.Cinematic

theorem polynomial_dyadic_piece_range :
    PolynomialDyadicPieceRangeStatement := by
  intro delta countExponent massExponent N total lower upper
    hdelta_pos hdelta_le hcount_nonneg hmass_nonneg hN_pos
    hN_bound hmass_lt_total htotal_eq hupper_le_one

  set a : ℝ := countExponent + massExponent with ha_def
  set b : ℝ := Real.logb 2 (1 / delta) with hb_def

  have ha_nonneg : 0 ≤ a := by linarith
  have hone_le_invdelta : 2 ≤ 1 / delta := by
    have h3 : 1 / delta ≥ 2 := by
      calc
        1 / delta ≥ 1 / (1 / 2) := by gcongr
        _ = 2 := by norm_num
    exact h3
  have hb_ge_one : 1 ≤ b := by
    rw [hb_def]
    have h_pos : 0 < (1 / delta) := by positivity
    have h : Real.logb 2 (1 / delta) ≥ Real.logb 2 2 :=
      (Real.logb_le_logb (by norm_num) (by norm_num) h_pos).mpr hone_le_invdelta
    have h2 : Real.logb 2 2 = 1 := by
      rw [Real.logb_self_eq_one] <;> norm_num
    linarith
  have hb_nonneg : 0 ≤ b := by linarith

  by_cases hlower_top : lower = ⊤

  -- Case 1: lower = ⊤
  · refine' ⟨1, by norm_num, _ , _⟩
    · rw [hlower_top]
      have h : upper < (⊤ : ENNReal) := by
        exact lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top (by simp) hupper_le_one)
      simpa using h
    · have h : (1 : ℝ) ≤ (a + 2) * (b + 1) := by
        have h1 : 0 ≤ a := ha_nonneg
        have h2 : 1 ≤ b := hb_ge_one
        nlinarith
      exact_mod_cast h

  -- Case 2: lower ≠ ⊤
  · have hlower_ne_top : lower ≠ ⊤ := hlower_top

    have htotal_ne_top : total ≠ ⊤ := by
      rw [←htotal_eq]
      exact ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (by simp) hlower_ne_top)

    have hlower_pos : 0 < lower := by
      by_contra h
      have h' : lower = 0 := by simpa using h
      have htotal_zero : total = 0 := by
        rw [h'] at htotal_eq
        simpa using htotal_eq.symm
      rw [htotal_zero] at hmass_lt_total
      simpa using hmass_lt_total

    have hlower_toReal_pos : 0 < lower.toReal :=
      ENNReal.toReal_pos hlower_pos.ne' hlower_ne_top

    have htotal_toReal_eq :
        total.toReal = 2 * (N : ℝ) * lower.toReal := by
      have h1 : (2 * ((N : ENNReal) * lower)).toReal = 2 * (N : ℝ) * lower.toReal := by
        simp [ENNReal.toReal_mul, ENNReal.toReal_ofNat]
        <;> ring
      have h2 : total = 2 * ((N : ENNReal) * lower) := htotal_eq.symm
      rw [h2]
      exact h1

    have hmass_pos' : 0 < Real.rpow delta massExponent :=
      Real.rpow_pos_of_pos hdelta_pos massExponent

    have hmass_lt_toReal : Real.rpow delta massExponent < total.toReal := by
      have h_ne : (ENNReal.ofReal (Real.rpow delta massExponent)) ≠ ⊤ := by simp
      have h : (ENNReal.ofReal (Real.rpow delta massExponent)).toReal < total.toReal :=
        (ENNReal.toReal_lt_toReal h_ne htotal_ne_top).mpr hmass_lt_total
      have h3 : (ENNReal.ofReal (Real.rpow delta massExponent)).toReal = Real.rpow delta massExponent := by
        rw [ENNReal.toReal_ofReal (by linarith)]
      rw [h3] at h
      exact h

    have hupper_ne_top : upper ≠ ⊤ := ne_top_of_le_ne_top (by simp) hupper_le_one
    have hupper_toReal_le_one : upper.toReal ≤ 1 := by
      have h_one_ne_top : (1 : ENNReal) ≠ ⊤ := by simp
      have h : upper.toReal ≤ (1 : ENNReal).toReal :=
        (ENNReal.toReal_le_toReal hupper_ne_top h_one_ne_top).mpr hupper_le_one
      simpa using h

    set L : ℕ := Nat.ceil (a * b + 1) with hL_def

    have hL_pos : 0 < L := by
      rw [hL_def]
      have h : 0 < a * b + 1 := by positivity
      exact Nat.ceil_pos.mpr (by linarith)

    have hL_ge : (L : ℝ) ≥ a * b + 1 := by
      rw [hL_def]
      exact Nat.le_ceil (a * b + 1)

    have hdelta_rpow_neg_a :
        Real.rpow delta (-a) = (2 : ℝ) ^ (a * b) := by
      have h1 : Real.rpow delta (-a) = delta⁻¹ ^ a := Real.rpow_neg_eq_inv_rpow delta a
      have h1' : delta⁻¹ = 1 / delta := by ring
      rw [h1, h1']
      have h_pos : 0 < 1 / delta := by positivity
      have h7 : (1 / delta) = (2 : ℝ) ^ b := by
        rw [hb_def]
        rw [Real.rpow_logb] <;> norm_num <;> linarith
      rw [h7]
      have h8 : ((2 : ℝ) ^ b) ^ a = (2 : ℝ) ^ (b * a) := by
        rw [←Real.rpow_mul] <;> norm_num
      rw [h8]
      have h9 : b * a = a * b := by ring
      rw [h9]

    have h_rpow_div :
        Real.rpow delta (-countExponent) / Real.rpow delta massExponent =
        Real.rpow delta (-a) := by
      have h : Real.rpow delta (-countExponent - massExponent) =
                 Real.rpow delta (-countExponent) / Real.rpow delta massExponent :=
        Real.rpow_sub hdelta_pos (-countExponent) massExponent
      have h2 : -countExponent - massExponent = -a := by
        simp [ha_def] <;> ring
      rw [h2] at h
      exact h.symm

    have hcount_rpow_pos : 0 < Real.rpow delta (-countExponent) :=
      Real.rpow_pos_of_pos hdelta_pos (-countExponent)

    have htotal_toReal_pos : 0 < total.toReal := by
      have h : 0 < total := lt_of_le_of_lt (by simp) hmass_lt_total
      exact ENNReal.toReal_pos h.ne' htotal_ne_top

    have h_inv_lower_lt :
        1 / lower.toReal < (2 : ℝ) ^ (a * b + 1) := by
      have h1 : 1 / lower.toReal = 2 * (N : ℝ) / total.toReal := by
        have h2 : total.toReal = 2 * (N : ℝ) * lower.toReal := htotal_toReal_eq
        have h3 : 1 / lower.toReal = 2 * (N : ℝ) / total.toReal := by
          rw [h2]
          field_simp [hlower_toReal_pos.ne']
        exact h3
      rw [h1]
      have h_num : 2 * (N : ℝ) ≤ 2 * Real.rpow delta (-countExponent) := by
        gcongr
      have h_den : Real.rpow delta massExponent < total.toReal := hmass_lt_toReal
      have h3 : 2 * (N : ℝ) / total.toReal <
               (2 * Real.rpow delta (-countExponent)) / Real.rpow delta massExponent := by
        calc
          2 * (N : ℝ) / total.toReal
            ≤ (2 * Real.rpow delta (-countExponent)) / total.toReal := by
              gcongr
          _ < (2 * Real.rpow delta (-countExponent)) / Real.rpow delta massExponent := by
            apply div_lt_div_of_pos_left
            · positivity
            · exact hmass_pos'
            · exact h_den
      have h4 : (2 * Real.rpow delta (-countExponent)) / Real.rpow delta massExponent =
               2 * (Real.rpow delta (-countExponent) / Real.rpow delta massExponent) := by
        ring
      rw [h4] at h3
      rw [h_rpow_div] at h3
      rw [hdelta_rpow_neg_a] at h3
      have h7 : (2 : ℝ) ^ (a * b + 1) = 2 * (2 : ℝ) ^ (a * b) := by
        have h71 : (2 : ℝ) ^ (a * b + 1) = (2 : ℝ) ^ (a * b) * (2 : ℝ) ^ (1 : ℝ) := by
          rw [Real.rpow_add] <;> norm_num
        rw [h71]
        have h72 : (2 : ℝ) ^ (1 : ℝ) = 2 := by simp
        rw [h72] <;> ring
      rw [h7]
      exact h3

    have h_main_ineq : (1 : ℝ) < (2 : ℝ) ^ L * lower.toReal := by
      have h9 : (L : ℝ) ≥ a * b + 1 := hL_ge
      have h10 : (2 : ℝ) ^ (a * b + 1) ≤ (2 : ℝ) ^ (L : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) h9
      have h11 : (2 : ℝ) ^ (L : ℝ) = (2 : ℝ) ^ L := by
        norm_cast
      have h12 : (2 : ℝ) ^ L > 1 / lower.toReal := by
        rw [←h11]
        have h13 : (2 : ℝ) ^ (a * b + 1) > 1 / lower.toReal := h_inv_lower_lt
        linarith
      have h14 : (2 : ℝ) ^ L * lower.toReal > (1 / lower.toReal) * lower.toReal :=
        mul_lt_mul_of_pos_right h12 hlower_toReal_pos
      have h15 : (1 / lower.toReal) * lower.toReal = 1 := by
        field_simp [hlower_toReal_pos.ne']
      rw [h15] at h14
      exact h14

    have hL_bound : (L : ℝ) ≤ (a + 2) * (b + 1) := by
      rw [hL_def]
      have h_pos : 0 < Nat.ceil (a * b + 1) := hL_pos
      have h2 : (Nat.ceil (a * b + 1) - 1 : ℕ) < Nat.ceil (a * b + 1) := by omega
      have h3 : ((Nat.ceil (a * b + 1) - 1 : ℕ) : ℝ) < a * b + 1 :=
        (Nat.lt_ceil).mp h2
      have h4 : (Nat.ceil (a * b + 1) : ℝ) ≤ a * b + 2 := by
        simp [h_pos] at h3 <;> linarith
      have h5 : a * b + 2 ≤ (a + 2) * (b + 1) := by nlinarith
      linarith

    have h_ennreal_ineq : upper < (2 : ENNReal) ^ L * lower := by
      have hfin1 : ((2 : ENNReal) ^ L * lower) ≠ ⊤ :=
        ENNReal.mul_ne_top (by simp) hlower_ne_top
      have h5 : ((2 : ENNReal) ^ L * lower).toReal = (2 : ℝ) ^ L * lower.toReal := by
        simp [ENNReal.toReal_mul]
      have h6 : upper.toReal < ((2 : ENNReal) ^ L * lower).toReal := by
        rw [h5]
        have h7 : upper.toReal ≤ 1 := hupper_toReal_le_one
        linarith [h_main_ineq]
      exact (ENNReal.toReal_lt_toReal hupper_ne_top hfin1).mp h6

    exact ⟨L, hL_pos, h_ennreal_ineq, hL_bound⟩

end Kakeya.Cinematic
