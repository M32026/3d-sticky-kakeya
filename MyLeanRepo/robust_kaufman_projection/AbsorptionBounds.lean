module

/-
  Helper lemma: cardinality lower bound and absorption bounds
  for the inner refinement step of robust_kaufman_s_le_one.

  Extracted to keep proof terms small enough for the kernel.
-/

public import MyLeanRepo.robust_kaufman_projection.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section


open scoped ENNReal NNReal

namespace RobustKaufmanProjection.Dune

/-- Cardinality lower bound and absorption bounds for the inner refinement. -/
lemma cardinality_and_absorption_bounds
    {s t ρ δ : ℝ}
    (hs : 0 < s) (hst : s < t) (hρ : 0 < ρ) (hAρ : 12 * ρ < t - s)
    (h_s_le_one : s ≤ 1)
    (hδ : 0 < δ) (hδ_le_half : δ ≤ 1 / 2)
    (h_abs1' : (9 : ℝ) ≤ δ ^ (-(t - s + 10 * ρ)))
    (h_abs2' : 49 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) / 50 ≤ δ ^ (-4 * ρ))
    (h_abs3' : 882 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) ≤ δ ^ (-22 * ρ))
    {S_P S_P' : Finset EuclideanPlane} {P : Set EuclideanPlane}
    (hS_P_ncover : Ncover δ P ≤ (S_P.card : ENNReal))
    (hP_lower : ENNReal.ofReal (δ ^ (ρ - t)) ≤ Ncover δ P)
    (hS_P'_density : ENNReal.ofReal (δ ^ ρ) * (S_P.card : ENNReal) ≤ (9 : ENNReal) * (S_P'.card : ENNReal))
    (E_ref : ℝ)
    (hE_poly : E_ref ≤ δ ^ (-8 * ρ) / 100)
    (hS_P'_nonempty : S_P'.Nonempty) :
    (S_P'.card : ℝ) ≥ δ ^ (12 * ρ - s) ∧
    49 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) * (E_ref + δ^(-s)/(S_P'.card : ℝ)) ≤ δ ^ (-12 * ρ) ∧
    7 * (E_ref + δ^(-s)/(S_P'.card : ℝ)) ≤ δ ^ (-12 * ρ) / ((2 : ℝ)^(2*s+3) * (3 : ℝ)^s) := by
  have hδ_lt_one : δ < 1 := by linarith [hδ_le_half]
  -- hS_card
  have hSP_lower : ENNReal.ofReal (δ ^ (ρ - t)) ≤ (S_P.card : ENNReal) :=
    le_trans hP_lower hS_P_ncover
  have h_card_lower1 : ENNReal.ofReal (δ ^ (2 * ρ - t)) ≤ (9 : ENNReal) * (S_P'.card : ENNReal) := by
    have h_mul : ENNReal.ofReal (δ ^ ρ) * ENNReal.ofReal (δ ^ (ρ - t)) = ENNReal.ofReal (δ ^ (2 * ρ - t)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      have h_exp : δ ^ ρ * δ ^ (ρ - t) = δ ^ (2 * ρ - t) := by
        have h_e : ρ + (ρ - t) = 2 * ρ - t := by ring
        rw [← Real.rpow_add hδ, h_e]
      rw [h_exp]
    calc ENNReal.ofReal (δ ^ (2 * ρ - t))
      = ENNReal.ofReal (δ ^ ρ) * ENNReal.ofReal (δ ^ (ρ - t)) := by rw [h_mul]
    _ ≤ ENNReal.ofReal (δ ^ ρ) * (S_P.card : ENNReal) := by gcongr
    _ ≤ (9 : ENNReal) * (S_P'.card : ENNReal) := hS_P'_density
  have h_card_lower2 : δ ^ (2 * ρ - t) ≤ 9 * (S_P'.card : ℝ) := by
    have h9 : (9 : ENNReal) * (S_P'.card : ENNReal) = ENNReal.ofReal (9 * (S_P'.card : ℝ)) := by
      simp [ENNReal.ofReal_mul] <;> norm_cast <;> ring
    rw [h9] at h_card_lower1
    exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mp h_card_lower1
  have h_n_lower : (S_P'.card : ℝ) ≥ δ ^ (2 * ρ - t) / 9 := by linarith
  have h_pos_exp : 0 < δ ^ (t - s + 10 * ρ) := by positivity
  have h3 : δ ^ (-(t - s + 10 * ρ)) = 1 / δ ^ (t - s + 10 * ρ) := by
    rw [Real.rpow_neg (by positivity)] <;> field_simp
  have h4 : 9 ≤ 1 / δ ^ (t - s + 10 * ρ) := by
    rw [h3] at h_abs1'
    exact h_abs1'
  have h5 : 9 * δ ^ (t - s + 10 * ρ) ≤ 1 := by
    calc 9 * δ ^ (t - s + 10 * ρ)
      ≤ (1 / δ ^ (t - s + 10 * ρ)) * δ ^ (t - s + 10 * ρ) := by gcongr
    _ = 1 := by field_simp [h_pos_exp.ne'] <;> ring
  have h2 : δ ^ (t - s + 10 * ρ) ≤ 1 / 9 := by linarith
  have h4' : δ ^ (2 * ρ - t) / 9 ≥ δ ^ (12 * ρ - s) := by
    calc δ ^ (2 * ρ - t) / 9
      = δ ^ (2 * ρ - t) * (1 / 9) := by ring
    _ ≥ δ ^ (2 * ρ - t) * δ ^ (t - s + 10 * ρ) := by gcongr
    _ = δ ^ (12 * ρ - s) := by
      have h_e : (2 * ρ - t) + (t - s + 10 * ρ) = 12 * ρ - s := by ring
      rw [← Real.rpow_add hδ, h_e]
  have hS_card : (S_P'.card : ℝ) ≥ δ ^ (12 * ρ - s) := by linarith [h_n_lower]
  let n : ℝ := (S_P'.card : ℝ)
  have hn_pos : 0 < n := by
    dsimp only [n]
    have h : 0 < S_P'.card := hS_P'_nonempty.card_pos
    exact_mod_cast h
  have h_delta_s_n : δ ^ (-s) / n ≤ 9 * δ ^ (t - s - 2 * ρ) := by
    have h5 : δ ^ (-s) / n ≤ δ ^ (-s) / (δ ^ (2 * ρ - t) / 9) := by gcongr
    have h6 : δ ^ (-s) / (δ ^ (2 * ρ - t) / 9) = 9 * δ ^ (t - s - 2 * ρ) := by
      have h7 : 0 < δ ^ (2 * ρ - t) := by positivity
      have h8 : δ ^ (-s) / δ ^ (2 * ρ - t) = δ ^ (t - s - 2 * ρ) := by
        have h_pos2 : 0 < δ ^ (2 * ρ - t) := by positivity
        have h91 : δ ^ (-(2 * ρ - t)) = (δ ^ (2 * ρ - t))⁻¹ :=
          Real.rpow_neg (le_of_lt hδ) (2 * ρ - t)
        have h9 : δ ^ (-s) / δ ^ (2 * ρ - t) = δ ^ (-s) * δ ^ (-(2 * ρ - t)) := by
          have h92 : δ ^ (-s) / δ ^ (2 * ρ - t) = δ ^ (-s) * (δ ^ (2 * ρ - t))⁻¹ := by
            exact division_def (δ ^ (-s)) (δ ^ (2 * ρ - t))
          rw [h92, ← h91]
        rw [h9]
        have h10 : (-s) + (-(2 * ρ - t)) = t - s - 2 * ρ := by ring
        rw [← Real.rpow_add hδ, h10]
      calc δ ^ (-s) / (δ ^ (2 * ρ - t) / 9)
          = δ ^ (-s) * 9 / δ ^ (2 * ρ - t) := by field_simp [h7.ne'] <;> ring
        _ = 9 * (δ ^ (-s) / δ ^ (2 * ρ - t)) := by ring
        _ = 9 * δ ^ (t - s - 2 * ρ) := by rw [h8]
    rw [h6] at h5; exact h5
  have h_exp_gt : t - s - 2 * ρ > 10 * ρ := by
    have h : 12 * ρ < t - s := hAρ
    linarith
  have h8 : δ ^ (t - s - 2 * ρ) ≤ δ ^ (10 * ρ) :=
    Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) (by linarith)
  have h_delta_s_n2 : δ ^ (-s) / n ≤ 9 * δ ^ (10 * ρ) := by
    calc δ ^ (-s) / n
      ≤ 9 * δ ^ (t - s - 2 * ρ) := h_delta_s_n
    _ ≤ 9 * δ ^ (10 * ρ) := by exact mul_le_mul_of_nonneg_left h8 (by norm_num)
  let E' : ℝ := E_ref + δ ^ (-s) / n
  have hE'_bound : E' ≤ δ ^ (-8 * ρ) / 100 + 9 * δ ^ (10 * ρ) := by
    dsimp only [E']
    have h9 : E_ref ≤ δ ^ (-8 * ρ) / 100 := hE_poly
    linarith [h_delta_s_n2]
  let K_ncover : ℝ := (2 : ℝ)^(2*s+3) * (3 : ℝ)^s
  have hK_pos : 0 < K_ncover := by positivity
  have h2s_eq : (2 : ℝ)^(2*s+4) = 2 * (2 : ℝ)^(2*s+3) := by
    have h : (2*s+4) = (2*s+3) + 1 := by ring
    rw [h, Real.rpow_add (by norm_num)]
    have h2 : (2 : ℝ)^(1 : ℝ) = 2 := by norm_num
    rw [h2] <;> ring
  have h3s_ge : (3 : ℝ)^(2*s) ≥ (3 : ℝ)^s := by
    have h : s ≤ 2 * s := by linarith
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h
  have h3s_ge_one : (3 : ℝ)^s ≥ 1 := by
    have h : (3 : ℝ)^s ≥ (3 : ℝ)^(0 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    simpa using h
  have h_common1 : 7 * (2 : ℝ)^(2*s+3) * (3 : ℝ)^s ≤ 49 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) := by
    rw [h2s_eq]
    have h : (49 : ℝ) * (2 * (2 : ℝ)^(2*s+3)) * (3 : ℝ)^(2*s) =
        98 * (2 : ℝ)^(2*s+3) * (3 : ℝ)^(2*s) := by ring
    rw [h]
    have h2 : (3 : ℝ)^(2*s) = (3 : ℝ)^s * (3 : ℝ)^s := by
      have h_e : 2 * s = s + s := by ring
      rw [h_e, Real.rpow_add (by norm_num)] <;> ring
    rw [h2]
    have h3 : 0 < (2 : ℝ)^(2*s+3) := by positivity
    have h4 : 0 < (3 : ℝ)^s := by positivity
    nlinarith [h3s_ge_one]
  have h_ncover1 : 7 * (δ ^ (-8 * ρ) / 100) ≤ δ ^ (-12 * ρ) / (2 * K_ncover) := by
    have h10 : 7 * K_ncover / 50 ≤ 49 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) / 50 := by
      dsimp only [K_ncover]
      have h_common1' : 7 * ((2 : ℝ)^(2*s+3) * (3 : ℝ)^s) ≤ 49 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) := by
        simpa [mul_assoc] using h_common1
      exact div_le_div_of_nonneg_right h_common1' (by norm_num)
    have h11 : 7 * K_ncover / 50 ≤ δ ^ (-4 * ρ) := le_trans h10 h_abs2'
    have h14 : δ ^ (-4 * ρ) * δ ^ (-8 * ρ) = δ ^ (-12 * ρ) := by
      have h_e : (-4 * ρ) + (-8 * ρ) = -12 * ρ := by ring
      rw [← Real.rpow_add hδ, h_e]
    have h_eq1 : 7 * (δ ^ (-8 * ρ) / 100) = (7 * K_ncover / 50) * δ ^ (-8 * ρ) / (2 * K_ncover) := by
      field_simp [hK_pos.ne'] <;> ring
    have h_ineq : (7 * K_ncover / 50) * δ ^ (-8 * ρ) / (2 * K_ncover) ≤ (δ ^ (-4 * ρ)) * δ ^ (-8 * ρ) / (2 * K_ncover) := by gcongr
    have h_final : (δ ^ (-4 * ρ)) * δ ^ (-8 * ρ) / (2 * K_ncover) = δ ^ (-12 * ρ) / (2 * K_ncover) := by rw [h14]
    rw [h_eq1]
    exact le_trans h_ineq h_final.le
  have h_common2 : 126 * (2 : ℝ)^(2*s+3) * (3 : ℝ)^s ≤ 882 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) := by
    rw [h2s_eq]
    have h : (882 : ℝ) * (2 * (2 : ℝ)^(2*s+3)) * (3 : ℝ)^(2*s) =
        1764 * (2 : ℝ)^(2*s+3) * (3 : ℝ)^(2*s) := by ring
    rw [h]
    have h2 : (3 : ℝ)^(2*s) = (3 : ℝ)^s * (3 : ℝ)^s := by
      have h_e : 2 * s = s + s := by ring
      rw [h_e, Real.rpow_add (by norm_num)] <;> ring
    rw [h2]
    have h3 : 0 < (2 : ℝ)^(2*s+3) := by positivity
    have h4 : 0 < (3 : ℝ)^s := by positivity
    nlinarith [h3s_ge_one]
  have h_ncover2 : 7 * (9 * δ ^ (10 * ρ)) ≤ δ ^ (-12 * ρ) / (2 * K_ncover) := by
    have h10 : 126 * K_ncover ≤ 882 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) := by
      dsimp only [K_ncover]
      simpa [mul_assoc] using h_common2
    have h11 : 126 * K_ncover ≤ δ ^ (-22 * ρ) := le_trans h10 h_abs3'
    have h14 : δ ^ (-22 * ρ) * δ ^ (10 * ρ) = δ ^ (-12 * ρ) := by
      have h_e : (-22 * ρ) + (10 * ρ) = -12 * ρ := by ring
      rw [← Real.rpow_add hδ, h_e]
    have h_eq1 : 7 * (9 * δ ^ (10 * ρ)) = (126 * K_ncover) * δ ^ (10 * ρ) / (2 * K_ncover) := by
      field_simp [hK_pos.ne'] <;> ring
    have h_ineq : (126 * K_ncover) * δ ^ (10 * ρ) / (2 * K_ncover) ≤ (δ ^ (-22 * ρ)) * δ ^ (10 * ρ) / (2 * K_ncover) := by gcongr
    have h_final : (δ ^ (-22 * ρ)) * δ ^ (10 * ρ) / (2 * K_ncover) = δ ^ (-12 * ρ) / (2 * K_ncover) := by rw [h14]
    rw [h_eq1]
    exact le_trans h_ineq h_final.le
  have h_absorb_ncover7 : 7 * E' ≤ δ ^ (-12 * ρ) / K_ncover := by
    have h1 : 7 * E' ≤ 7 * (δ ^ (-8 * ρ) / 100 + 9 * δ ^ (10 * ρ)) := by gcongr
    have h2 : 7 * (δ ^ (-8 * ρ) / 100 + 9 * δ ^ (10 * ρ)) = 7 * (δ ^ (-8 * ρ) / 100) + 7 * (9 * δ ^ (10 * ρ)) := by ring
    have h3 : 7 * (δ ^ (-8 * ρ) / 100) + 7 * (9 * δ ^ (10 * ρ)) ≤ δ ^ (-12 * ρ) / (2 * K_ncover) + δ ^ (-12 * ρ) / (2 * K_ncover) := by
      gcongr <;> exact h_ncover1 <;> exact h_ncover2
    have h4 : δ ^ (-12 * ρ) / (2 * K_ncover) + δ ^ (-12 * ρ) / (2 * K_ncover) = δ ^ (-12 * ρ) / K_ncover := by ring
    rw [h2] at h1
    exact le_trans h1 (le_trans h3 h4.le)
  have h_sset1 : 49 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) * (δ ^ (-8 * ρ) / 100) ≤ δ ^ (-12 * ρ) / 2 := by
    have h10 : 49 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) / 50 ≤ δ ^ (-4 * ρ) := h_abs2'
    have h11 : 49 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) * (δ ^ (-8 * ρ) / 100) = (49 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) / 50) * δ ^ (-8 * ρ) / 2 := by ring
    rw [h11]
    have h12 : (49 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) / 50) * δ ^ (-8 * ρ) ≤ δ ^ (-12 * ρ) := by
      calc (49 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) / 50) * δ ^ (-8 * ρ)
        ≤ δ ^ (-4 * ρ) * δ ^ (-8 * ρ) := by gcongr
      _ = δ ^ (-12 * ρ) := by
        have h_exp : (-4 * ρ) + (-8 * ρ) = -12 * ρ := by ring
        rw [← Real.rpow_add hδ, h_exp]
    exact div_le_div_of_nonneg_right h12 (by norm_num)
  have h_sset2 : 49 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) * (9 * δ ^ (10 * ρ)) ≤ δ ^ (-12 * ρ) / 2 := by
    have h10 : 882 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) ≤ δ ^ (-22 * ρ) := h_abs3'
    have h11 : 49 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) * (9 * δ ^ (10 * ρ)) = (882 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s)) * δ ^ (10 * ρ) / 2 := by ring
    rw [h11]
    have h12 : (882 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s)) * δ ^ (10 * ρ) ≤ δ ^ (-12 * ρ) := by
      calc (882 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s)) * δ ^ (10 * ρ)
        ≤ δ ^ (-22 * ρ) * δ ^ (10 * ρ) := by gcongr
      _ = δ ^ (-12 * ρ) := by
        have h_exp : (-22 * ρ) + (10 * ρ) = -12 * ρ := by ring
        rw [← Real.rpow_add hδ, h_exp]
    exact div_le_div_of_nonneg_right h12 (by norm_num)
  have h_absorb_sset : 49 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) * E' ≤ δ ^ (-12 * ρ) := by
    have h13 : 49 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) * E' ≤
        49 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) * (δ ^ (-8 * ρ) / 100 + 9 * δ ^ (10 * ρ)) := by gcongr
    have h14 : 49 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) * (δ ^ (-8 * ρ) / 100 + 9 * δ ^ (10 * ρ)) =
        49 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) * (δ ^ (-8 * ρ) / 100) +
        49 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) * (9 * δ ^ (10 * ρ)) := by ring
    rw [h14] at h13
    linarith [h_sset1, h_sset2]
  exact ⟨hS_card, h_absorb_sset, h_absorb_ncover7⟩

end RobustKaufmanProjection.Dune
