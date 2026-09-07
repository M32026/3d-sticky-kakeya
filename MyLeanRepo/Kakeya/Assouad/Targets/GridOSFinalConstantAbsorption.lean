import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSFinalConstantAbsorptionStatement

/-!
WZ2 Proposition 7.1: absorb the finite `6889` telescoping loss into the final
projection exponent.
-/

namespace Kakeya.Assouad

theorem grid_os_final_constant_absorption :
    GridOSFinalConstantAbsorptionStatement := by
  dsimp only [GridOSFinalConstantAbsorptionStatement]
  intro innerEpsilon targetEpsilon h_ie_pos h_ie_lt_one h_lt steps
  set p : ℝ := innerEpsilon + innerEpsilon ^ 2 * (2 - innerEpsilon) with hp_def
  have hgap_pos : 0 < targetEpsilon - p := by linarith
  set gap : ℝ := targetEpsilon - p with hgap_def
  have hgap_pos' : 0 < gap := hgap_pos
  set delta₀ : ℝ := min 1 (Real.rpow 6889 (-(steps : ℝ) / gap)) with hdelta₀_def
  have h6889_pos : (0 : ℝ) < 6889 := by norm_num
  have h6889_nonneg : (0 : ℝ) ≤ 6889 := by norm_num
  have hrpow_pos : 0 < Real.rpow 6889 (-(steps : ℝ) / gap) :=
    Real.rpow_pos_of_pos h6889_pos _
  have hdelta₀_pos : 0 < delta₀ := by
    rw [hdelta₀_def]
    exact lt_min (by norm_num) hrpow_pos
  have hdelta₀_le_one : delta₀ ≤ 1 := by
    rw [hdelta₀_def]
    exact min_le_left _ _
  refine' ⟨delta₀, hdelta₀_pos, hdelta₀_le_one, _⟩
  intro delta hdelta_pos hdelta_le V hV
  have h1 : delta ≤ Real.rpow 6889 (-(steps : ℝ) / gap) := by
    have h2 : delta ≤ delta₀ := hdelta_le
    rw [hdelta₀_def] at h2
    exact h2.trans (min_le_right _ _)
  have h3 : Real.rpow delta gap ≤ Real.rpow 6889 (-(steps : ℝ)) := by
    have h4 : Real.rpow delta gap ≤ Real.rpow (Real.rpow 6889 (-(steps : ℝ) / gap)) gap :=
      Real.rpow_le_rpow hdelta_pos.le h1 hgap_pos'.le
    have h5 : Real.rpow (Real.rpow 6889 (-(steps : ℝ) / gap)) gap =
        Real.rpow 6889 ((-(steps : ℝ) / gap) * gap) := by
      have h51 : Real.rpow (Real.rpow 6889 (-(steps : ℝ) / gap)) gap =
          (Real.rpow 6889 (-(steps : ℝ) / gap)) ^ gap := by rfl
      rw [h51]
      exact (Real.rpow_mul h6889_nonneg (-(steps : ℝ) / gap) gap).symm
    rw [h5] at h4
    have h6 : ((-(steps : ℝ) / gap) * gap) = -(steps : ℝ) := by
      field_simp [hgap_pos'.ne']
    rw [h6] at h4
    exact h4
  have h7 : (6889 : ℝ) ^ steps * Real.rpow delta gap ≤ 1 := by
    have h8 : Real.rpow 6889 (-(steps : ℝ)) = 1 / (6889 : ℝ) ^ steps := by
      simp [Real.rpow_neg h6889_pos.le]
    rw [h8] at h3
    have h9 : (0 : ℝ) < (6889 : ℝ) ^ steps := by positivity
    calc
      (6889 : ℝ) ^ steps * Real.rpow delta gap
        ≤ (6889 : ℝ) ^ steps * (1 / (6889 : ℝ) ^ steps) := by gcongr
      _ = 1 := by
        field_simp [h9.ne']
  have htarget_eq : targetEpsilon = p + gap := by
    simp [hgap_def]
  have h11 : Real.rpow delta targetEpsilon = Real.rpow delta p * Real.rpow delta gap := by
    have h111 : Real.rpow delta (p + gap) = Real.rpow delta p * Real.rpow delta gap :=
      Real.rpow_add hdelta_pos p gap
    rw [htarget_eq]
    exact h111
  have h10 : (6889 : ℝ) ^ steps * Real.rpow delta targetEpsilon ≤ Real.rpow delta p := by
    rw [h11]
    have h12 : (6889 : ℝ) ^ steps * (Real.rpow delta p * Real.rpow delta gap) =
        Real.rpow delta p * ((6889 : ℝ) ^ steps * Real.rpow delta gap) := by ring
    rw [h12]
    have h13 : 0 ≤ Real.rpow delta p := Real.rpow_nonneg hdelta_pos.le p
    nlinarith
  have h14 : (6889 : ENNReal) ^ steps * Kakeya.realRpowENN delta targetEpsilon ≤
      Kakeya.realRpowENN delta p := by
    have h15 : Kakeya.realRpowENN delta targetEpsilon = ENNReal.ofReal (Real.rpow delta targetEpsilon) := by
      rfl
    have h16 : Kakeya.realRpowENN delta p = ENNReal.ofReal (Real.rpow delta p) := by rfl
    rw [h15, h16]
    have h17 : ENNReal.ofReal ((6889 : ℝ) ^ steps * Real.rpow delta targetEpsilon) ≤
        ENNReal.ofReal (Real.rpow delta p) := ENNReal.ofReal_mono h10
    have h18 : ENNReal.ofReal ((6889 : ℝ) ^ steps * Real.rpow delta targetEpsilon) =
        ENNReal.ofReal ((6889 : ℝ) ^ steps) * ENNReal.ofReal (Real.rpow delta targetEpsilon) := by
      rw [ENNReal.ofReal_mul]
      positivity
    rw [h18] at h17
    have h19 : ENNReal.ofReal ((6889 : ℝ) ^ steps) = (6889 : ENNReal) ^ steps := by
      simp
    rw [h19] at h17
    exact h17
  set c : ENNReal := (6889 : ENNReal) ^ steps with hc_def
  have h20 : c * Kakeya.realRpowENN delta targetEpsilon ≤ c * V :=
    h14.trans hV
  have h21 : c ≠ 0 := by positivity
  have h22 : c ≠ ⊤ := by
    rw [hc_def]
    have h : (6889 : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    exact ENNReal.pow_ne_top h
  have h20' : c * Kakeya.realRpowENN delta targetEpsilon ≤ V * c := by
    have hcomm : V * c = c * V := by apply mul_comm
    rw [hcomm]
    exact h20
  have h23 : (c * Kakeya.realRpowENN delta targetEpsilon) / c ≤ V :=
    ENNReal.div_le_of_le_mul h20'
  have h24 : (c * Kakeya.realRpowENN delta targetEpsilon) / c =
      Kakeya.realRpowENN delta targetEpsilon := by
    have hcomm : c * Kakeya.realRpowENN delta targetEpsilon =
        Kakeya.realRpowENN delta targetEpsilon * c := by apply mul_comm
    rw [hcomm]
    exact ENNReal.mul_div_cancel_right h21 h22
  rw [h24] at h23
  exact h23

end Kakeya.Assouad
