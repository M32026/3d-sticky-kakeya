import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.FixedDepthPowerGridKRatioGate

/-!
# Fixed-depth power-grid K-ratio gate

Comparator-validated proof from issue/MR `#3985/#3990`.
-/

namespace Kakeya.Streamlined.RandomTranslation.WithShading

theorem fixed_depth_power_grid_k_ratio_gate :
    FixedDepthPowerGridKRatioGateStatement := by
  intro delta N hdelta_pos hdelta_le_one hN_pos grid
  set r : ℝ := Real.rpow delta (-(1 / (N : ℝ))) with hr_def
  have hN_pos' : (N : ℝ) > 0 := by exact_mod_cast hN_pos
  have hexp_nonpos : -(1 / (N : ℝ)) ≤ 0 := by
    have h1 : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    linarith
  have hr_ge_one : 1 ≤ r :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hdelta_pos hdelta_le_one hexp_nonpos
  have hr_pos : 0 < r := by linarith
  have h_rpow_enn :
      Kakeya.realRpowENN delta (-(1 / (N : ℝ))) =
        ENNReal.ofReal r := by
    simp [Kakeya.realRpowENN, hr_def]
  have htoReal :
      (Kakeya.realRpowENN delta
        (-(1 / (N : ℝ)))).toReal = r := by
    rw [h_rpow_enn, ENNReal.toReal_ofReal hr_pos.le]
  have h_exp3_eq :
      (-(1 / (N : ℝ))) * 3 = -(3 / (N : ℝ)) := by
    field_simp [hN_pos'.ne'] <;> ring
  have hr3_eq :
      r ^ 3 = Real.rpow delta (-(3 / (N : ℝ))) := by
    rw [hr_def]
    have h2 :
        (Real.rpow delta (-(1 / (N : ℝ)))) ^ 3 =
          Real.rpow delta ((-(1 / (N : ℝ))) * 3) :=
      (Real.rpow_mul_natCast
        hdelta_pos.le (-(1 / (N : ℝ))) 3).symm
    rw [h2, h_exp3_eq]
  set C : ℝ :=
    2 + Real.pi + 8 / 3 * Real.pi with hC
  have h_cVol_expand :
      2 * cVol r =
        Real.pi * r ^ 2 +
          (8 / 3 : ℝ) * Real.pi * r ^ 3 := by
    simp [cVol] <;> ring
  have h_r2_le_r3 : r ^ 2 ≤ r ^ 3 := by
    nlinarith [hr_ge_one]
  have h_main_ineq : 2 * cVol r ≤ C * r ^ 3 := by
    rw [h_cVol_expand]
    have h :
        Real.pi * r ^ 2 +
            (8 / 3 : ℝ) * Real.pi * r ^ 3 ≤
          (Real.pi + (8 / 3 : ℝ) * Real.pi) *
            r ^ 3 := by
      nlinarith [Real.pi_pos, h_r2_le_r3]
    have h2 :
        (Real.pi + (8 / 3 : ℝ) * Real.pi) *
            r ^ 3 ≤
          C * r ^ 3 := by
      gcongr
      linarith [Real.pi_pos]
    linarith
  have h_two_le : 2 ≤ C * r ^ 3 := by
    have h3 : r ^ 3 ≥ 1 := by
      nlinarith [hr_ge_one]
    have h4 : C ≥ 2 := by
      linarith [Real.pi_pos]
    nlinarith
  have h_max_le :
      max 2 (2 * cVol r) ≤ C * r ^ 3 :=
    max_le h_two_le h_main_ineq
  have hK_eq :
      fixedDepthPowerGridKRatio delta N =
        max 2 (2 * cVol r) := by
    dsimp only [fixedDepthPowerGridKRatio]
    rw [htoReal]
  have h_part1 :
      2 ≤ fixedDepthPowerGridKRatio delta N := by
    rw [hK_eq]
    exact le_max_left _ _
  have h_part2 :
      ENNReal.ofReal
          (fixedDepthPowerGridKRatio delta N) ≤
        ENNReal.ofReal C *
          Kakeya.realRpowENN delta
            (-(3 / (N : ℝ))) := by
    have h3 :
        ENNReal.ofReal
            (fixedDepthPowerGridKRatio delta N) ≤
          ENNReal.ofReal (C * r ^ 3) := by
      rw [hK_eq]
      exact ENNReal.ofReal_le_ofReal h_max_le
    have h4 :
        ENNReal.ofReal (C * r ^ 3) =
          ENNReal.ofReal C *
            ENNReal.ofReal (r ^ 3) := by
      rw [ENNReal.ofReal_mul] <;> positivity
    have h5 :
        ENNReal.ofReal (r ^ 3) =
          Kakeya.realRpowENN delta
            (-(3 / (N : ℝ))) := by
      simp [Kakeya.realRpowENN, hr3_eq]
    rw [h4, h5] at h3
    exact h3
  have h_part3 :
      ∀ i : Fin N,
        2 * ENNReal.ofReal
            (cVol
              ((grid.increasingScale
                    (Fin.succ i)).1 /
                (grid.increasingScale
                    (Fin.castSucc i)).1)) ≤
          ENNReal.ofReal
            (fixedDepthPowerGridKRatio delta N) := by
    intro i
    set succVal : ℝ :=
      (grid.increasingScale (Fin.succ i)).1
    set castVal : ℝ :=
      (grid.increasingScale (Fin.castSucc i)).1
    have hcast_pos : 0 < castVal := by
      have h : delta ≤ castVal :=
        (grid.increasingScale
          (Fin.castSucc i)).2.1
      linarith
    have hsucc_pos : 0 < succVal := by
      have h : delta ≤ succVal :=
        (grid.increasingScale (Fin.succ i)).2.1
      linarith
    have h1 :
        ENNReal.ofReal succVal =
          Kakeya.realRpowENN delta
              (-(1 / (N : ℝ))) *
            ENNReal.ofReal castVal :=
      grid.increasingScale_ratio i
    have h_r_eq :
        ENNReal.ofReal r =
          Kakeya.realRpowENN delta
            (-(1 / (N : ℝ))) := by
      simp [Kakeya.realRpowENN, hr_def]
    have h_mul :
        ENNReal.ofReal succVal =
          ENNReal.ofReal (r * castVal) := by
      have h2 :
          ENNReal.ofReal (r * castVal) =
            ENNReal.ofReal r *
              ENNReal.ofReal castVal := by
        rw [ENNReal.ofReal_mul] <;> positivity
      rw [h2, h_r_eq]
      exact h1
    have h_eq : succVal = r * castVal := by
      have h_toReal :
          (ENNReal.ofReal succVal).toReal =
            (ENNReal.ofReal
              (r * castVal)).toReal := by
        rw [h_mul]
      have hsucc_nonneg : 0 ≤ succVal := hsucc_pos.le
      have hproduct_nonneg : 0 ≤ r * castVal := by
        positivity
      rw [ENNReal.toReal_ofReal hsucc_nonneg,
        ENNReal.toReal_ofReal hproduct_nonneg]
        at h_toReal
      exact h_toReal
    have h_ratio_real : succVal / castVal = r := by
      field_simp [hcast_pos.ne']
      linarith
    have h7 :
        2 * cVol r ≤
          fixedDepthPowerGridKRatio delta N := by
      rw [hK_eq]
      exact le_max_right _ _
    have h8 :
        (2 : ENNReal) *
            ENNReal.ofReal (cVol r) =
          ENNReal.ofReal (2 * cVol r) := by
      have h9 :
          ENNReal.ofReal (2 * cVol r) =
            ENNReal.ofReal (2 : ℝ) *
              ENNReal.ofReal (cVol r) := by
        rw [ENNReal.ofReal_mul] <;> positivity
      rw [h9]
      simp
    have h9 :
        ENNReal.ofReal (2 * cVol r) ≤
          ENNReal.ofReal
            (fixedDepthPowerGridKRatio delta N) :=
      ENNReal.ofReal_le_ofReal h7
    rw [h_ratio_real, h8]
    exact h9
  exact ⟨h_part1, h_part2, h_part3⟩

end Kakeya.Streamlined.RandomTranslation.WithShading
