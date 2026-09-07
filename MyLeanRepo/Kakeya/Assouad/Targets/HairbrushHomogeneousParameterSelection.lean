import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.Subunit.AsymptoticHelper

namespace Kakeya.Assouad

theorem hairbrush_homogeneous_parameter_selection :
    HairbrushHomogeneousParameterSelectionStatement := by
  intro eta stemLoss heta hstem
  set c : ℝ := (1 / 4 : ℝ) ^ (1 / eta) / 2 with hc_def
  have hc_pos : 0 < c := by positivity
  have h_two_c : 2 * c = (1 / 4 : ℝ) ^ (1 / eta) := by
    rw [hc_def] <;> ring
  have h_two_c_lt_one : 2 * c < 1 := by
    rw [h_two_c]
    have h1 : (1 / 4 : ℝ) < 1 := by norm_num
    have h2 : 0 < 1 / eta := by positivity
    exact Real.rpow_lt_one (by norm_num) h1 h2
  have h_two_c_le_one : 2 * c ≤ 1 := h_two_c_lt_one.le
  have h_c_le_half : c ≤ 1 / 2 := by linarith
  have h_base_pos : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have h_rpow_eta : Real.rpow (2 * c) eta = 1 / 4 := by
    rw [h_two_c]
    have h3 : Real.rpow ((1 / 4 : ℝ) ^ (1 / eta)) eta = (1 / 4 : ℝ) ^ ((1 / eta) * eta) :=
      (Real.rpow_mul h_base_pos (1 / eta) eta).symm
    rw [h3]
    have h4 : (1 / eta : ℝ) * eta = 1 := by
      field_simp [heta.ne'] <;> ring
    rw [h4]
    norm_num
  set scaleSeparation : ℝ := 1 / c with hscale_def
  have hscale_ge_one : 1 ≤ scaleSeparation := by
    rw [hscale_def]
    have h5 : c ≤ 1 / 2 := h_c_le_half
    have h6 : 0 < c := hc_pos
    calc 1 / c ≥ 1 / (1 / 2 : ℝ) := by gcongr
      _ = 2 := by norm_num
      _ ≥ 1 := by norm_num
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  set K : ℝ := (1000 * Real.pi) / c with hK_def
  have hK_pos : 0 < K := by positivity
  obtain ⟨delta₁, hdelta₁_pos, hdelta₁_le_one, hdelta₁_ineq⟩ :=
    Subunit.exists_delta₀_mul_pow_le_one K hK_pos stemLoss hstem
  set delta₀ : ℝ := min (1 / 1000) (min c delta₁) with hdelta₀_def
  have hdelta₀_pos : 0 < delta₀ := by
    rw [hdelta₀_def]
    positivity
  have hdelta₀_le_thousandth : delta₀ ≤ 1 / 1000 := by
    rw [hdelta₀_def]
    exact min_le_left _ _
  have hdelta₀_le_c : delta₀ ≤ c := by
    rw [hdelta₀_def]
    have h : min (1 / 1000) (min c delta₁) ≤ min c delta₁ := min_le_right _ _
    exact le_trans h (min_le_left _ _)
  have hdelta₀_le_delta₁ : delta₀ ≤ delta₁ := by
    rw [hdelta₀_def]
    have h : min (1 / 1000) (min c delta₁) ≤ min c delta₁ := min_le_right _ _
    exact le_trans h (min_le_right _ _)
  refine' ⟨scaleSeparation, delta₀, hscale_ge_one, hdelta₀_pos, hdelta₀_le_thousandth, _⟩
  intro δ hδ hδ_le_delta₀ theta htheta_ge_delta htheta_le_one
  by_cases h_easy : theta ≤ scaleSeparation * δ
  · exact Or.inl h_easy
  · -- Hard branch
    have h_hard : theta > scaleSeparation * δ := by linarith
    have h7 : scaleSeparation * δ = δ / c := by
      rw [hscale_def]
      field_simp [hc_pos.ne'] <;> ring
    have h_theta_gt : theta > δ / c := by
      rw [h7] at h_hard
      exact h_hard
    set angleScale : ℝ := c * theta with hangleScale_def
    have h_theta_pos : 0 < theta := by linarith
    have h_angleScale_pos : 0 < angleScale := by
      rw [hangleScale_def]
      exact mul_pos hc_pos h_theta_pos
    have h_angleScale_le_one : angleScale ≤ 1 := by
      rw [hangleScale_def]
      have h81 : c ≤ 1 / 2 := h_c_le_half
      have h82 : theta ≤ 1 := htheta_le_one
      have h83 : 0 ≤ theta := by linarith
      nlinarith
    have h_delta_le_angleScale : δ ≤ angleScale := by
      rw [hangleScale_def]
      have h93 : δ = c * (δ / c) := by
        field_simp [hc_pos.ne'] <;> ring
      rw [h93]
      exact (mul_lt_mul_of_pos_left h_theta_gt hc_pos).le
    have h_twice : 2 * angleScale ≤ theta := by
      rw [hangleScale_def]
      have h10 : 2 * (c * theta) ≤ theta := by
        have h11 : 2 * c ≤ 1 := h_two_c_le_one
        have h12 : 0 ≤ theta := by linarith
        nlinarith
      exact h10
    have h_theta_ne_zero : theta ≠ 0 := by linarith
    have h_transverse : Real.rpow (2 * angleScale / theta) eta ≤ 1 / 4 := by
      have h13 : 2 * angleScale / theta = 2 * c := by
        rw [hangleScale_def]
        field_simp [h_theta_ne_zero] <;> ring
      rw [h13]
      exact h_rpow_eta.le
    have hδ_le_c : δ ≤ c := by
      calc δ ≤ delta₀ := hδ_le_delta₀
           _ ≤ c := hdelta₀_le_c
    have h_angle_polynomial : Real.rpow δ 2 ≤ angleScale := by
      have h15 : Real.rpow δ 2 = δ ^ 2 := by
        simp
      rw [h15, hangleScale_def]
      have h16 : δ ^ 2 ≤ c * δ := by
        have h17 : δ ≤ c := hδ_le_c
        have h18 : 0 ≤ δ := by linarith
        nlinarith
      have h19 : c * δ ≤ c * theta := by
        exact mul_le_mul_of_nonneg_left htheta_ge_delta (by linarith)
      linarith
    have h_angle_polynomial_ENN :
        Kakeya.realRpowENN δ 2 ≤ ENNReal.ofReal angleScale := by
      have h20 : Kakeya.realRpowENN δ 2 = ENNReal.ofReal (Real.rpow δ 2) := by rfl
      rw [h20]
      exact ENNReal.ofReal_mono h_angle_polynomial
    have hδ_stem_ineq : K * Real.rpow δ stemLoss ≤ 1 :=
      hdelta₁_ineq δ hδ (by linarith)
    have h21 : Real.rpow δ stemLoss ≤ c / (1000 * Real.pi) := by
      have h22 : K * Real.rpow δ stemLoss ≤ 1 := hδ_stem_ineq
      have h23 : 0 < K := hK_pos
      have h241 : Real.rpow δ stemLoss = (K * Real.rpow δ stemLoss) / K := by
        field_simp [h23.ne'] <;> ring
      have h24 : Real.rpow δ stemLoss ≤ 1 / K := by
        have h242 : K * Real.rpow δ stemLoss ≤ 1 := h22
        have h243 : 0 < K := h23
        calc Real.rpow δ stemLoss
          = (K * Real.rpow δ stemLoss) / K := by field_simp [h243.ne'] <;> ring
        _ ≤ (1 : ℝ) / K := by
          exact div_le_div_of_nonneg_right h242 h243.le
      have h25 : 1 / K = c / (1000 * Real.pi) := by
        simp [hK_def] <;> field_simp [hc_pos.ne'] <;> ring
      rw [h25] at h24
      exact h24
    have h_stem_real : Real.rpow δ stemLoss * theta ≤ angleScale / (1000 * Real.pi) := by
      have h26 : Real.rpow δ stemLoss * theta ≤ (c / (1000 * Real.pi)) * theta :=
        mul_le_mul_of_nonneg_right h21 (by linarith)
      have h27 : (c / (1000 * Real.pi)) * theta = angleScale / (1000 * Real.pi) := by
        have h28 : (c / (1000 * Real.pi)) * theta = (c * theta) / (1000 * Real.pi) := by ring
        rw [h28, hangleScale_def] <;> ring
      calc Real.rpow δ stemLoss * theta
        ≤ (c / (1000 * Real.pi)) * theta := h26
      _ = angleScale / (1000 * Real.pi) := h27
    have h29 : 0 ≤ Real.rpow δ stemLoss := (Real.rpow_pos_of_pos hδ stemLoss).le
    have h31 : 0 ≤ angleScale := by positivity
    have h32_pos : 0 < 1000 * Real.pi := by positivity
    have h_stem_ENN :
        Kakeya.realRpowENN δ stemLoss * ENNReal.ofReal theta ≤
        ENNReal.ofReal angleScale / ENNReal.ofReal (1000 * Real.pi) := by
      have h33 : ENNReal.ofReal (Real.rpow δ stemLoss * theta) ≤
          ENNReal.ofReal (angleScale / (1000 * Real.pi)) :=
        ENNReal.ofReal_mono h_stem_real
      have h34 : ENNReal.ofReal (Real.rpow δ stemLoss * theta) =
          ENNReal.ofReal (Real.rpow δ stemLoss) * ENNReal.ofReal theta := by
        rw [ENNReal.ofReal_mul h29]
      have h35 : ENNReal.ofReal (angleScale / (1000 * Real.pi)) =
          ENNReal.ofReal angleScale / ENNReal.ofReal (1000 * Real.pi) := by
        exact ENNReal.ofReal_div_of_pos h32_pos
      rw [h34, h35] at h33
      simpa [Kakeya.realRpowENN] using h33
    exact Or.inr ⟨⟨angleScale, h_angleScale_pos, h_angleScale_le_one,
      h_delta_le_angleScale, h_twice, h_transverse, h_angle_polynomial_ENN,
      h_stem_ENN⟩⟩

end Kakeya.Assouad
