import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Helper lemmas for WZ1 Proposition 8.9 wide coarse preparation

Independent arithmetic lemmas for the density, scale, and Frostman-constant
absorptions in the wide branch of PDF Proposition 8.9.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/--
Density bound: after all losses, the uniform density constant is at least
`realRpowENN scale alpha`.
-/
lemma wideCoarseDensityBound
    {delta eta alpha epsilon scale : ℝ}
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (heta_pos : 0 < eta)
    (halpha_pos : 0 < alpha)
    (hepsilon_pos : 0 < epsilon)
    (hscale_pos : 0 < scale)
    (hscale_le : scale ≤ Real.rpow delta (epsilon / 10))
    (heta_small : eta ≤ alpha * epsilon / 20)
    (hdelta_small : Real.rpow delta (alpha * epsilon / 20) ≤ 1 / (2 ^ 27 : ℝ)) :
    Kakeya.realRpowENN delta eta / (2 ^ 27 : ENNReal) ≥
      Kakeya.realRpowENN scale alpha := by
  set beta : ℝ := alpha * epsilon / 20 with hbeta_def
  have hbeta_pos : 0 < beta := by positivity
  have h1 : Real.rpow delta eta ≥ Real.rpow delta beta :=
    Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one (by linarith)
  have h22 : Real.rpow (Real.rpow delta (epsilon / 10)) alpha =
      Real.rpow delta (alpha * epsilon / 10) := by
    have h : Real.rpow delta ((epsilon / 10) * alpha) =
        Real.rpow (Real.rpow delta (epsilon / 10)) alpha :=
      Real.rpow_mul hdelta_pos.le (epsilon / 10) alpha
    have h' : (epsilon / 10) * alpha = alpha * epsilon / 10 := by ring
    rw [h'] at h
    exact h.symm
  have h2 : Real.rpow scale alpha ≤ Real.rpow delta (alpha * epsilon / 10) := by
    have h21 : Real.rpow scale alpha ≤ Real.rpow (Real.rpow delta (epsilon / 10)) alpha :=
      Real.rpow_le_rpow (by positivity) hscale_le halpha_pos.le
    rw [h22] at h21
    exact h21
  have h31 : Real.rpow delta (alpha * epsilon / 10) = (Real.rpow delta beta) ^ 2 := by
    have h_eq : alpha * epsilon / 10 = 2 * beta := by
      simp [hbeta_def] <;> ring
    rw [h_eq]
    have h_add : Real.rpow delta (2 * beta) = Real.rpow delta (beta + beta) := by ring_nf
    rw [h_add]
    have h : Real.rpow delta (beta + beta) = Real.rpow delta beta * Real.rpow delta beta :=
      Real.rpow_add hdelta_pos beta beta
    rw [h] <;> ring
  have h3 : Real.rpow delta beta / (2 ^ 27 : ℝ) ≥
      Real.rpow delta (alpha * epsilon / 10) := by
    rw [h31]
    have h4 : 0 ≤ Real.rpow delta beta := Real.rpow_nonneg hdelta_pos.le beta
    nlinarith
  have h_main_real : Real.rpow delta eta / (2 ^ 27 : ℝ) ≥
      Real.rpow scale alpha := by
    calc
      Real.rpow delta eta / (2 ^ 27 : ℝ)
        ≥ Real.rpow delta beta / (2 ^ 27 : ℝ) := by
          gcongr
          <;> linarith
      _ ≥ Real.rpow delta (alpha * epsilon / 10) := h3
      _ ≥ Real.rpow scale alpha := h2
  have hpos1 : 0 ≤ Real.rpow delta eta := Real.rpow_nonneg hdelta_pos.le eta
  have h27_pos : (0 : ℝ) < (2 ^ 27 : ℝ) := by norm_num
  have hdiv : ENNReal.ofReal (Real.rpow delta eta / (2 ^ 27 : ℝ)) =
      ENNReal.ofReal (Real.rpow delta eta) / ENNReal.ofReal ((2 ^ 27 : ℝ)) :=
    ENNReal.ofReal_div_of_pos h27_pos
  have hdiv' : ENNReal.ofReal (Real.rpow delta eta) / (2 ^ 27 : ENNReal) =
      ENNReal.ofReal (Real.rpow delta eta / (2 ^ 27 : ℝ)) := by
    rw [hdiv] <;> norm_cast
  have h_ennreal :
      ENNReal.ofReal (Real.rpow delta eta) / (2 ^ 27 : ENNReal) ≥
      ENNReal.ofReal (Real.rpow scale alpha) := by
    rw [hdiv']
    exact ENNReal.ofReal_le_ofReal h_main_real
  simpa [Kakeya.realRpowENN] using h_ennreal

/--
Scale bound: `delta / width < delta^(epsilon/10)` when
`width > delta^(1 - epsilon/10)`.
-/
lemma wideCoarseScaleBound
    {delta width epsilon : ℝ}
    (hdelta_pos : 0 < delta)
    (hwidth_pos : 0 < width)
    (hepsilon_pos : 0 < epsilon)
    (hwidth_lower : Real.rpow delta (1 - epsilon / 10) < width) :
    delta / width < Real.rpow delta (epsilon / 10) := by
  set r : ℝ := Real.rpow delta (1 - epsilon / 10) with hr_def
  have hr_pos : 0 < r := Real.rpow_pos_of_pos hdelta_pos _
  have h2 : delta / width < delta / r :=
    div_lt_div_of_pos_left hdelta_pos hr_pos hwidth_lower
  have h4 : Real.rpow delta (epsilon / 10) * r = delta := by
    have h5 : Real.rpow delta (epsilon / 10 + (1 - epsilon / 10)) =
        Real.rpow delta (epsilon / 10) * Real.rpow delta (1 - epsilon / 10) :=
      Real.rpow_add hdelta_pos _ _
    have h6 : epsilon / 10 + (1 - epsilon / 10) = 1 := by ring
    have h7 : Real.rpow delta (epsilon / 10 + (1 - epsilon / 10)) = delta := by
      rw [h6] <;> simp
    rw [h7] at h5
    have h5' : Real.rpow delta (epsilon / 10) * r = delta := by
      simpa [hr_def] using h5.symm
    exact h5'
  have h3 : delta / r = Real.rpow delta (epsilon / 10) := by
    field_simp [hr_pos.ne'] <;> linarith
  rw [h3] at h2
  exact h2

/--
Frostman constant bound: the coarse Frostman constant from anisotropic
rescaling is bounded by the target `realRpowENN scale (-projectionLambda)`.
-/
lemma wideCoarseFrostmanBound
    {delta scale workingLambda projectionLambda epsilon_r epsilon : ℝ}
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (hscale_pos : 0 < scale)
    (hscale_le_one : scale ≤ 1)
    (hscale_le_delta_pow : scale ≤ Real.rpow delta (epsilon / 10))
    (hworkingLambda_pos : 0 < workingLambda)
    (hprojectionLambda_pos : 0 < projectionLambda)
    (hepsilon_r_pos : 0 < epsilon_r)
    (hepsilon_pos : 0 < epsilon)
    (hsum : workingLambda ≤ (epsilon / 10) * (projectionLambda - epsilon_r)) :
    Kakeya.realRpowENN (1 / scale) epsilon_r *
      Kakeya.realRpowENN delta (-workingLambda) ≤
    Kakeya.realRpowENN scale (-projectionLambda) := by
  have hprod_pos : 0 < (epsilon / 10) * (projectionLambda - epsilon_r) := by
    have h : (0 : ℝ) < workingLambda := hworkingLambda_pos
    have h' : workingLambda ≤ (epsilon / 10) * (projectionLambda - epsilon_r) := hsum
    linarith
  have hdiff_pos : 0 < projectionLambda - epsilon_r := by
    have h_epos : 0 < epsilon / 10 := by positivity
    nlinarith
  set y : ℝ := -(epsilon / 10) * (projectionLambda - epsilon_r) with hy_def
  have hy_neg : y < 0 := by
    simp [hy_def] <;> linarith
  have h1 : Real.rpow (1 / scale) epsilon_r = Real.rpow scale (-epsilon_r) := by
    have h11 : (1 / scale) = scale⁻¹ := by
      field_simp [hscale_pos.ne']
    have h_inv_rpow : Real.rpow (scale⁻¹) epsilon_r = (Real.rpow scale epsilon_r)⁻¹ :=
      Real.inv_rpow hscale_pos.le epsilon_r
    have h_neg_rpow : Real.rpow scale (-epsilon_r) = (Real.rpow scale epsilon_r)⁻¹ :=
      Real.rpow_neg hscale_pos.le epsilon_r
    rw [h11, h_inv_rpow, h_neg_rpow]
  have hbase_pos : 0 < Real.rpow delta (epsilon / 10) :=
    Real.rpow_pos_of_pos hdelta_pos _
  have hbase_le_one : Real.rpow delta (epsilon / 10) ≤ 1 := by
    have h : Real.rpow delta (epsilon / 10) ≤ Real.rpow delta 0 :=
      Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one (by linarith)
    simpa using h
  have h21 : Real.rpow scale (-(projectionLambda - epsilon_r)) ≥
      Real.rpow (Real.rpow delta (epsilon / 10))
        (-(projectionLambda - epsilon_r)) := by
    set w : ℝ := projectionLambda - epsilon_r with hw_def
    have hw_pos : 0 < w := hdiff_pos
    have h_le : scale ≤ Real.rpow delta (epsilon / 10) := hscale_le_delta_pow
    have h_rpow_le : Real.rpow scale w ≤
        Real.rpow (Real.rpow delta (epsilon / 10)) w :=
      Real.rpow_le_rpow (by positivity) h_le hw_pos.le
    have h1 : Real.rpow scale (-w) = (Real.rpow scale w)⁻¹ :=
      Real.rpow_neg hscale_pos.le w
    have h2 : Real.rpow (Real.rpow delta (epsilon / 10)) (-w) =
        (Real.rpow (Real.rpow delta (epsilon / 10)) w)⁻¹ :=
      Real.rpow_neg hbase_pos.le w
    rw [h1, h2]
    have h_pos_w : 0 < Real.rpow scale w := Real.rpow_pos_of_pos hscale_pos w
    exact inv_anti₀ h_pos_w h_rpow_le
  have h22 : Real.rpow (Real.rpow delta (epsilon / 10))
      (-(projectionLambda - epsilon_r)) =
      Real.rpow delta y := by
    have h : Real.rpow delta ((epsilon / 10) * (-(projectionLambda - epsilon_r))) =
        Real.rpow (Real.rpow delta (epsilon / 10))
          (-(projectionLambda - epsilon_r)) :=
      Real.rpow_mul hdelta_pos.le (epsilon / 10) (-(projectionLambda - epsilon_r))
    have h' : (epsilon / 10) * (-(projectionLambda - epsilon_r)) = y := by
      simp [hy_def] <;> ring
    rw [h'] at h
    exact h.symm
  have h23 : -workingLambda ≥ y := by
    simp [hy_def] <;> linarith
  have h24 : Real.rpow delta (-workingLambda) ≤ Real.rpow delta y :=
    Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one h23
  have h2 : Real.rpow delta (-workingLambda) ≤
      Real.rpow scale (-(projectionLambda - epsilon_r)) := by
    calc
      Real.rpow delta (-workingLambda) ≤ Real.rpow delta y := h24
      _ = Real.rpow (Real.rpow delta (epsilon / 10))
          (-(projectionLambda - epsilon_r)) := h22.symm
      _ ≤ Real.rpow scale (-(projectionLambda - epsilon_r)) := h21
  have h_main_real :
      Real.rpow (1 / scale) epsilon_r * Real.rpow delta (-workingLambda) ≤
      Real.rpow scale (-projectionLambda) := by
    rw [h1]
    have h_mul : Real.rpow scale (-epsilon_r) * Real.rpow delta (-workingLambda) ≤
        Real.rpow scale (-epsilon_r) *
          Real.rpow scale (-(projectionLambda - epsilon_r)) :=
      mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hscale_pos.le _)
    have h_add :
        Real.rpow scale (-epsilon_r) *
            Real.rpow scale (-(projectionLambda - epsilon_r)) =
          Real.rpow scale ((-epsilon_r) + (-(projectionLambda - epsilon_r))) :=
      (Real.rpow_add hscale_pos _ _).symm
    have h_final :
        (-epsilon_r) + (-(projectionLambda - epsilon_r)) = -projectionLambda := by
      ring
    rw [h_add, h_final] at h_mul
    exact h_mul
  have hpos1 : 0 ≤ Real.rpow (1 / scale) epsilon_r :=
    Real.rpow_nonneg (by positivity) _
  have hpos2 : 0 ≤ Real.rpow delta (-workingLambda) :=
    Real.rpow_nonneg hdelta_pos.le _
  have h_mul_ofReal :
      ENNReal.ofReal
          (Real.rpow (1 / scale) epsilon_r *
            Real.rpow delta (-workingLambda)) =
        ENNReal.ofReal (Real.rpow (1 / scale) epsilon_r) *
          ENNReal.ofReal (Real.rpow delta (-workingLambda)) :=
    ENNReal.ofReal_mul hpos1
  simp only [Kakeya.realRpowENN]
  rw [←h_mul_ofReal]
  exact ENNReal.ofReal_le_ofReal h_main_real

end Kakeya.Assouad
