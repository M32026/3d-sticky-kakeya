import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulScaleAbsorption

/-!
# Small-volume regime for faithful short-curve assembly

When both the retained geometric set and the multiplicity are below their
absorption thresholds, the desired level-set estimate follows directly.
-/

namespace Kakeya.Cinematic

open MeasureTheory

lemma wz2_small_volume_case
    {E₀ E₂ : Set (ℝ × ℝ)}
    {epsilon epsilon' delta δ_vert logLoss C_abs : ℝ}
    {mu : ℕ}
    (hδ_vert_pos : 0 < δ_vert)
    (hdelta : 0 < delta)
    (hdelta_le_vert : delta ≤ δ_vert)
    (hdelta_le_one : delta ≤ 1)
    (hC_abs_pos : 0 < C_abs)
    (h_abs :
      logLoss * C_abs ≤
        Real.rpow δ_vert (-(epsilon - epsilon')))
    (h_retention :
      volume E₀ ≤ ENNReal.ofReal logLoss * volume E₂)
    (h_small_vol :
      volume E₂ ≤ ENNReal.ofReal (Real.rpow δ_vert epsilon'))
    (h_mu_small :
      Real.rpow (mu : ℝ) (3 / 2 : ℝ) ≤ C_abs)
    (hmu : 0 < mu)
    (hepsilon'_pos : 0 < epsilon')
    (hepsilon'_budget : 2 * epsilon' ≤ epsilon)
    (hlogLoss_ge1 : 1 ≤ logLoss) :
    volume E₀ ≤
      ENNReal.ofReal
        (Real.rpow delta (-epsilon) *
          Real.rpow (mu : ℝ) (-3 / 2 : ℝ)) := by
  have hepsilon : 0 < epsilon := by
    linarith
  set target : ℝ :=
    Real.rpow delta (-epsilon) *
      Real.rpow (mu : ℝ) (-3 / 2 : ℝ)
    with htarget_def
  have htarget_pos : 0 < target := by
    have h1 : 0 < Real.rpow delta (-epsilon) :=
      Real.rpow_pos_of_pos hdelta _
    have h2 : 0 < Real.rpow (mu : ℝ) (-3 / 2 : ℝ) :=
      Real.rpow_pos_of_pos (by exact_mod_cast hmu) _
    exact mul_pos h1 h2

  let gap : ℝ := epsilon - 2 * epsilon'
  have hgap_nonneg : 0 ≤ gap := by
    dsimp only [gap]
    linarith
  have htwo_epsilon'_pos : 0 < 2 * epsilon' := by
    positivity

  have h1 :
      volume E₀ ≤
        ENNReal.ofReal
          (logLoss * Real.rpow δ_vert epsilon') := by
    calc
      volume E₀ ≤ ENNReal.ofReal logLoss * volume E₂ :=
        h_retention
      _ ≤
          ENNReal.ofReal logLoss *
            ENNReal.ofReal (Real.rpow δ_vert epsilon') := by
        gcongr
      _ =
          ENNReal.ofReal
            (logLoss * Real.rpow δ_vert epsilon') := by
        rw [ENNReal.ofReal_mul (by linarith)]

  have h2 :
      logLoss * Real.rpow δ_vert epsilon' ≤
        Real.rpow δ_vert (-gap) / C_abs := by
    have h41 : (-(epsilon - epsilon')) + epsilon' = -gap := by
      dsimp only [gap]
      ring
    have h4' :
        Real.rpow δ_vert (-(epsilon - epsilon')) *
            Real.rpow δ_vert epsilon' =
            Real.rpow δ_vert (-gap) := by
      have h :
          Real.rpow δ_vert (-(epsilon - epsilon')) *
              Real.rpow δ_vert epsilon' =
            Real.rpow δ_vert
              ((-(epsilon - epsilon')) + epsilon') :=
        (Real.rpow_add hδ_vert_pos _ _).symm
      rw [h, h41]
    have h6 :
        logLoss ≤
          Real.rpow δ_vert (-(epsilon - epsilon')) / C_abs := by
      calc
        logLoss = (logLoss * C_abs) / C_abs := by
          field_simp [hC_abs_pos.ne']
        _ ≤
            Real.rpow δ_vert (-(epsilon - epsilon')) / C_abs := by
          gcongr
    have h7 : 0 ≤ Real.rpow δ_vert epsilon' :=
      Real.rpow_nonneg (by linarith) _
    have h8 :
        logLoss * Real.rpow δ_vert epsilon' ≤
          (Real.rpow δ_vert (-(epsilon - epsilon')) / C_abs) *
            Real.rpow δ_vert epsilon' :=
      mul_le_mul_of_nonneg_right h6 h7
    have h9 :
        (Real.rpow δ_vert (-(epsilon - epsilon')) / C_abs) *
            Real.rpow δ_vert epsilon' =
          (Real.rpow δ_vert (-(epsilon - epsilon')) *
              Real.rpow δ_vert epsilon') /
            C_abs := by
      ring
    rw [h9, h4'] at h8
    exact h8

  have h51 :
      Real.rpow δ_vert (-gap) ≤
        Real.rpow delta (-gap) := by
    have h4 :
        Real.rpow δ_vert (-gap) =
          (Real.rpow δ_vert gap)⁻¹ := by
      exact Real.rpow_neg hδ_vert_pos.le gap
    have h6 :
        Real.rpow delta (-gap) =
          (Real.rpow delta gap)⁻¹ := by
      exact Real.rpow_neg hdelta.le gap
    rw [h4, h6]
    have h7 :
        Real.rpow delta gap ≤
          Real.rpow δ_vert gap :=
      Real.rpow_le_rpow hdelta.le hdelta_le_vert
        hgap_nonneg
    have hpos2 : 0 < Real.rpow delta gap :=
      Real.rpow_pos_of_pos hdelta gap
    have h9 :
        (Real.rpow δ_vert gap)⁻¹ ≤
          (Real.rpow delta gap)⁻¹ := by
      have h10 :
          1 / Real.rpow δ_vert gap ≤
            1 / Real.rpow delta gap :=
        one_div_le_one_div_of_le hpos2 h7
      simpa [one_div] using h10
    exact h9

  have h52 :
      Real.rpow delta (-gap) ≤
        Real.rpow delta (-epsilon) := by
    have h9 :
        Real.rpow delta (-gap) =
          Real.rpow delta (-epsilon) *
            Real.rpow delta (2 * epsilon') := by
      have h10 : -gap = -epsilon + 2 * epsilon' := by
        dsimp only [gap]
        ring
      rw [h10]
      exact Real.rpow_add hdelta (-epsilon) (2 * epsilon')
    rw [h9]
    have h11 : Real.rpow delta (2 * epsilon') ≤ 1 :=
      Real.rpow_le_one hdelta.le hdelta_le_one
        htwo_epsilon'_pos.le
    have h12 : 0 ≤ Real.rpow delta (-epsilon) :=
      Real.rpow_nonneg hdelta.le _
    calc
      Real.rpow delta (-epsilon) *
          Real.rpow delta (2 * epsilon') ≤
          Real.rpow delta (-epsilon) * 1 := by
        gcongr
      _ = Real.rpow delta (-epsilon) := by ring

  have h5 :
      Real.rpow δ_vert (-gap) ≤
        Real.rpow delta (-epsilon) :=
    h51.trans h52

  have h8 :
      Real.rpow δ_vert (-gap) / C_abs ≤
        Real.rpow delta (-epsilon) *
          Real.rpow (mu : ℝ) (-3 / 2 : ℝ) := by
    have hmu_pos' : 0 < (mu : ℝ) := by exact_mod_cast hmu
    have h11 : 0 < Real.rpow (mu : ℝ) (3 / 2 : ℝ) :=
      Real.rpow_pos_of_pos hmu_pos' _
    have h12 :
        1 / C_abs ≤
          1 / Real.rpow (mu : ℝ) (3 / 2 : ℝ) := by
      gcongr
    have h13 :
        (Real.rpow (mu : ℝ) (3 / 2 : ℝ))⁻¹ =
          Real.rpow (mu : ℝ) (-3 / 2 : ℝ) := by
      have h131 :
          (Real.rpow (mu : ℝ) (3 / 2 : ℝ))⁻¹ =
            Real.rpow (mu : ℝ) (-(3 / 2 : ℝ)) :=
        (Real.rpow_neg hmu_pos'.le (3 / 2 : ℝ)).symm
      have h132 : (-(3 / 2 : ℝ)) = -3 / 2 := by norm_num
      rw [h131, h132]
    have h15 :
        1 / Real.rpow (mu : ℝ) (3 / 2 : ℝ) =
          Real.rpow (mu : ℝ) (-3 / 2 : ℝ) := by
      rw [show
        1 / Real.rpow (mu : ℝ) (3 / 2 : ℝ) =
          (Real.rpow (mu : ℝ) (3 / 2 : ℝ))⁻¹ by simp]
      exact h13
    have h16 :
        1 / C_abs ≤
          Real.rpow (mu : ℝ) (-3 / 2 : ℝ) :=
      h12.trans_eq h15
    have h17 : 0 ≤ Real.rpow delta (-epsilon) :=
      Real.rpow_nonneg hdelta.le _
    calc
      Real.rpow δ_vert (-gap) / C_abs =
          Real.rpow δ_vert (-gap) * (1 / C_abs) := by
        ring
      _ ≤ Real.rpow delta (-epsilon) * (1 / C_abs) := by
        gcongr
      _ ≤
          Real.rpow delta (-epsilon) *
            Real.rpow (mu : ℝ) (-3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left h16 h17

  have h10 : volume E₀ ≤ ENNReal.ofReal target := by
    calc
      volume E₀ ≤
          ENNReal.ofReal
            (logLoss * Real.rpow δ_vert epsilon') :=
        h1
      _ ≤
          ENNReal.ofReal
            (Real.rpow δ_vert (-gap) / C_abs) := by
        exact ENNReal.ofReal_le_ofReal h2
      _ ≤ ENNReal.ofReal target := by
        exact ENNReal.ofReal_le_ofReal h8
  simpa [htarget_def] using h10

end Kakeya.Cinematic
