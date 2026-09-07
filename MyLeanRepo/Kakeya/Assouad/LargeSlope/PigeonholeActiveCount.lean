import MyLeanRepo.Kakeya.Assouad.Statements

/-!
# Helper lemmas for the active count lower bound and small-scale comparisons
-/

namespace Kakeya.Assouad

/--
Derive the active tube count lower bound from the pigeonhole inequality.
-/
lemma active_count_lower_bound
    {delta eta sigma rho : ℝ}
    (hdelta : 0 < delta) (_hdelta1 : delta ≤ 1)
    (_heta : 0 < eta) (_hsigma : 0 < sigma) (_hsigma1 : sigma < 1)
    (hrho : 0 < rho)
    {prismCount activeCount : ENNReal}
    (hprism_pos : 0 < prismCount) (hprism_ne_top : prismCount ≠ ⊤)
    (h1 : Kakeya.realRpowENN delta (12 * eta) * ENNReal.ofReal (Real.sqrt rho) ≤
          prismCount * ENNReal.ofReal (Real.sqrt rho * delta ^ 2) * activeCount)
    (hprism_upper : prismCount ≤
          Kakeya.realRpowENN delta (-(12 * eta)) *
          Kakeya.realRpowENN rho ((-1 + sigma) / 2)) :
    Kakeya.realRpowENN delta (24 * eta - 2) *
        Kakeya.realRpowENN rho ((1 - sigma) / 2) ≤ activeCount := by
  let d12 := Real.rpow delta (12 * eta)
  let d_12 := Real.rpow delta (-(12 * eta))
  let d24_2 := Real.rpow delta (24 * eta - 2)
  let d2 := Real.rpow delta 2
  let r_half := Real.rpow rho (1 / 2)
  let r_sigma_half := Real.rpow rho (sigma / 2)
  let r_1sigma_half := Real.rpow rho ((1 - sigma) / 2)
  let r_m1sigma_half := Real.rpow rho ((-1 + sigma) / 2)
  have hd12_pos : 0 < d12 := Real.rpow_pos_of_pos hdelta _
  have hd_12_pos : 0 < d_12 := Real.rpow_pos_of_pos hdelta _
  have hd24_2_pos : 0 < d24_2 := Real.rpow_pos_of_pos hdelta _
  have hd2_pos : 0 < d2 := Real.rpow_pos_of_pos hdelta _
  have hr_half_pos : 0 < r_half := Real.rpow_pos_of_pos hrho _
  have hr_sigma_half_pos : 0 < r_sigma_half := Real.rpow_pos_of_pos hrho _
  have hr_1sigma_half_pos : 0 < r_1sigma_half := Real.rpow_pos_of_pos hrho _
  have hr_m1sigma_half_pos : 0 < r_m1sigma_half := Real.rpow_pos_of_pos hrho _
  have hsqrt : Real.sqrt rho = r_half := Real.sqrt_eq_rpow rho
  -- Real arithmetic
  have hprod_real : d_12 * r_m1sigma_half * r_half * d2 =
      d_12 * d2 * r_sigma_half := by
    have h1 : r_m1sigma_half * r_half = r_sigma_half := by
      dsimp only [r_m1sigma_half, r_half, r_sigma_half]
      have h_add : Real.rpow rho (((-1 + sigma) / 2) + (1 / 2)) =
          Real.rpow rho ((-1 + sigma) / 2) * Real.rpow rho (1 / 2) :=
        Real.rpow_add hrho ((-1 + sigma) / 2) (1 / 2)
      have h_sum : ((-1 + sigma) / 2) + (1 / 2) = sigma / 2 := by ring
      rw [h_sum] at h_add
      exact h_add.symm
    have h_goal : d_12 * r_m1sigma_half * r_half * d2 = d_12 * d2 * (r_m1sigma_half * r_half) := by ring
    rw [h_goal, h1] <;> ring
  have htotal_real : d12 * r_half * (d_12 * d2 * r_sigma_half)⁻¹ = d24_2 * r_1sigma_half := by
    have h2 : d_12 * d2 = Real.rpow delta (-(12 * eta) + 2) := by
      dsimp only [d_12, d2]
      have h_add : Real.rpow delta ((-(12 * eta)) + 2) =
          Real.rpow delta (-(12 * eta)) * Real.rpow delta 2 :=
        Real.rpow_add hdelta (-(12 * eta)) 2
      exact h_add.symm
    have h3 : d12 * (d_12 * d2)⁻¹ = d24_2 := by
      rw [h2]
      dsimp only [d12, d24_2]
      have h_neg : (Real.rpow delta (-(12 * eta) + 2))⁻¹ = Real.rpow delta (-((-(12 * eta) + 2))) := by
        exact (Real.rpow_neg hdelta.le (-(12 * eta) + 2)).symm
      rw [h_neg]
      have h6 : Real.rpow delta (12 * eta) * Real.rpow delta (-((-(12 * eta) + 2))) =
          Real.rpow delta (12 * eta + (-((-(12 * eta) + 2)))) := by
        exact (Real.rpow_add hdelta (12 * eta) (-((-(12 * eta) + 2)))).symm
      rw [h6]
      have h7 : 12 * eta + (-((-(12 * eta) + 2))) = 24 * eta - 2 := by ring
      rw [h7]
    have h5 : r_half * r_sigma_half⁻¹ = r_1sigma_half := by
      dsimp only [r_half, r_sigma_half, r_1sigma_half]
      have h6 : (Real.rpow rho (sigma / 2))⁻¹ = Real.rpow rho (-(sigma / 2)) := by
        exact (Real.rpow_neg hrho.le (sigma / 2)).symm
      rw [h6]
      have h7 : Real.rpow rho (1 / 2) * Real.rpow rho (-(sigma / 2)) =
          Real.rpow rho (1 / 2 + (-(sigma / 2))) := by
        exact (Real.rpow_add hrho (1 / 2) (-(sigma / 2))).symm
      rw [h7]
      have h8 : 1 / 2 + (-(sigma / 2)) = (1 - sigma) / 2 := by ring
      rw [h8]
    calc
      d12 * r_half * (d_12 * d2 * r_sigma_half)⁻¹
        = d12 * (d_12 * d2)⁻¹ * (r_half * r_sigma_half⁻¹) := by ring
      _ = d24_2 * r_1sigma_half := by rw [h3, h5] <;> ring
  -- ENNReal conversions
  let total : ENNReal := Kakeya.realRpowENN delta (12 * eta) * ENNReal.ofReal (Real.sqrt rho)
  let cap : ENNReal := ENNReal.ofReal (Real.sqrt rho * delta ^ 2)
  let prod : ENNReal := prismCount * cap
  let upper : ENNReal := ENNReal.ofReal (d_12 * d2 * r_sigma_half)
  let desired : ENNReal := ENNReal.ofReal (d24_2 * r_1sigma_half)
  have htotal_eq : total = ENNReal.ofReal (d12 * r_half) := by
    have h : Kakeya.realRpowENN delta (12 * eta) = ENNReal.ofReal d12 := by
      simp [Kakeya.realRpowENN] <;> rfl
    rw [show total = Kakeya.realRpowENN delta (12 * eta) * ENNReal.ofReal (Real.sqrt rho) from rfl]
    rw [h, hsqrt]
    rw [← ENNReal.ofReal_mul (by positivity)]
    <;> rfl
  have hcap_eq : cap = ENNReal.ofReal (r_half * d2) := by
    have hdelta2 : delta ^ 2 = d2 := by
      dsimp only [d2]
      exact (Real.rpow_two delta).symm
    rw [show cap = ENNReal.ofReal (Real.sqrt rho * delta ^ 2) from rfl]
    have h : ENNReal.ofReal (Real.sqrt rho * delta ^ 2) =
        ENNReal.ofReal (Real.sqrt rho) * ENNReal.ofReal (delta ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
    rw [h, hsqrt, hdelta2]
    rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
  have hprod_ne_zero : prod ≠ 0 := by
    rw [show prod = prismCount * cap from rfl]
    apply mul_ne_zero hprism_pos.ne'
    have hprod_pos : 0 < r_half * d2 := mul_pos hr_half_pos hd2_pos
    have hcap_pos : 0 < cap := by
      rw [hcap_eq]
      exact ENNReal.ofReal_pos.mpr hprod_pos
    exact hcap_pos.ne'
  have hcap_ne_top : cap ≠ ⊤ := by
    exact ENNReal.ofReal_ne_top
  have hprod_ne_top : prod ≠ ⊤ := ENNReal.mul_ne_top hprism_ne_top hcap_ne_top
  have hupper_ne_zero : upper ≠ 0 := by
    simp [upper, ENNReal.ofReal_eq_zero] <;> positivity
  have hupper_ne_top : upper ≠ ⊤ := by simp [upper, ENNReal.ofReal_ne_top]
  -- total ≤ prod * activeCount → prod⁻¹ * total ≤ activeCount
  have h2 : prod⁻¹ * total ≤ activeCount := by
    have h_cap_match : cap = ENNReal.ofReal (Real.sqrt rho * delta ^ 2) := by
      exact rfl
    have h3 : total ≤ prod * activeCount := by
      have h_rhs : prismCount * ENNReal.ofReal (Real.sqrt rho * delta ^ 2) * activeCount =
          prod * activeCount := by
        dsimp only [prod, cap]
        <;> ring
      rw [h_rhs] at h1
      exact h1
    have h4 : prod⁻¹ * total ≤ prod⁻¹ * (prod * activeCount) := by gcongr
    have h5 : prod⁻¹ * (prod * activeCount) = activeCount :=
      ENNReal.inv_mul_cancel_left hprod_ne_zero hprod_ne_top
    rw [h5] at h4
    exact h4
  -- prod ≤ upper
  have hprod_upper2 : prod ≤ upper := by
    rw [show prod = prismCount * cap from rfl, hcap_eq]
    have h_prism2 : prismCount ≤ ENNReal.ofReal (d_12 * r_m1sigma_half) := by
      have h1 : Kakeya.realRpowENN delta (-(12 * eta)) = ENNReal.ofReal d_12 := by
        simp [Kakeya.realRpowENN] <;> rfl
      have h2 : Kakeya.realRpowENN rho ((-1 + sigma) / 2) = ENNReal.ofReal r_m1sigma_half := by
        simp [Kakeya.realRpowENN] <;> rfl
      have h3 : Kakeya.realRpowENN delta (-(12 * eta)) * Kakeya.realRpowENN rho ((-1 + sigma) / 2) =
          ENNReal.ofReal (d_12 * r_m1sigma_half) := by
        rw [h1, h2]
        rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
      rw [h3] at hprism_upper
      exact hprism_upper
    calc
      prismCount * ENNReal.ofReal (r_half * d2)
        ≤ ENNReal.ofReal (d_12 * r_m1sigma_half) * ENNReal.ofReal (r_half * d2) := by gcongr
      _ = ENNReal.ofReal ((d_12 * r_m1sigma_half) * (r_half * d2)) := by
        rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
      _ = upper := by
        rw [show upper = ENNReal.ofReal (d_12 * d2 * r_sigma_half) from rfl]
        congr 1
        have h_assoc : d_12 * r_m1sigma_half * (r_half * d2) = d_12 * r_m1sigma_half * r_half * d2 := by ring
        rw [h_assoc]
        exact hprod_real
  -- prod⁻¹ ≥ upper⁻¹
  have hprod_inv_ge : prod⁻¹ ≥ upper⁻¹ := ENNReal.inv_le_inv.mpr hprod_upper2
  -- upper⁻¹ * total = desired
  have hupper_inv_total : upper⁻¹ * total = desired := by
    rw [show upper = ENNReal.ofReal (d_12 * d2 * r_sigma_half) from rfl, htotal_eq]
    have h_upper_inv : (ENNReal.ofReal (d_12 * d2 * r_sigma_half))⁻¹ =
        ENNReal.ofReal ((d_12 * d2 * r_sigma_half)⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos (by positivity)]
    rw [h_upper_inv]
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [show desired = ENNReal.ofReal (d24_2 * r_1sigma_half) from rfl]
    congr 1
    have h_comm : (d_12 * d2 * r_sigma_half)⁻¹ * (d12 * r_half) =
        d12 * r_half * (d_12 * d2 * r_sigma_half)⁻¹ := by ring
    rw [h_comm]
    exact htotal_real
  -- Finish
  have h6 : upper⁻¹ * total ≤ prod⁻¹ * total := by gcongr
  rw [hupper_inv_total] at h6
  have hdesired_eq : desired = Kakeya.realRpowENN delta (24 * eta - 2) * Kakeya.realRpowENN rho ((1 - sigma) / 2) := by
    have h1 : Kakeya.realRpowENN delta (24 * eta - 2) = ENNReal.ofReal d24_2 := by
      simp [Kakeya.realRpowENN] <;> rfl
    have h2 : Kakeya.realRpowENN rho ((1 - sigma) / 2) = ENNReal.ofReal r_1sigma_half := by
      simp [Kakeya.realRpowENN] <;> rfl
    have h3 : ENNReal.ofReal d24_2 * ENNReal.ofReal r_1sigma_half =
        ENNReal.ofReal (d24_2 * r_1sigma_half) := by
      rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
    have h4 : desired = ENNReal.ofReal (d24_2 * r_1sigma_half) := by rfl
    rw [h4, ← h3, ← h1, ← h2]
  have h_final : Kakeya.realRpowENN delta (24 * eta - 2) * Kakeya.realRpowENN rho ((1 - sigma) / 2) ≤ activeCount := by
    rw [← hdesired_eq]
    exact h6.trans h2
  exact h_final

/--
Generalized active count lower bound with a cap factor `C ≥ 1`.

When the piece mass upper bound is `C * √ρ * δ²` instead of `√ρ * δ²`,
the active count is `C⁻¹` times the original bound.
-/
lemma active_count_lower_bound_with_factor
    {delta eta sigma rho : ℝ}
    (hdelta : 0 < delta) (_hdelta1 : delta ≤ 1)
    (_heta : 0 < eta) (_hsigma : 0 < sigma) (_hsigma1 : sigma < 1)
    (hrho : 0 < rho)
    (C : ℝ) (hC_pos : 0 < C)
    {prismCount activeCount : ENNReal}
    (hprism_pos : 0 < prismCount) (hprism_ne_top : prismCount ≠ ⊤)
    (h1 : Kakeya.realRpowENN delta (12 * eta) * ENNReal.ofReal (Real.sqrt rho) ≤
          prismCount * ENNReal.ofReal (C * Real.sqrt rho * delta ^ 2) * activeCount)
    (hprism_upper : prismCount ≤
          Kakeya.realRpowENN delta (-(12 * eta)) *
          Kakeya.realRpowENN rho ((-1 + sigma) / 2)) :
    ENNReal.ofReal C⁻¹ * Kakeya.realRpowENN delta (24 * eta - 2) *
        Kakeya.realRpowENN rho ((1 - sigma) / 2) ≤ activeCount := by
  let d12 := Real.rpow delta (12 * eta)
  let d_12 := Real.rpow delta (-(12 * eta))
  let d24_2 := Real.rpow delta (24 * eta - 2)
  let d2 := Real.rpow delta 2
  let r_half := Real.rpow rho (1 / 2)
  let r_sigma_half := Real.rpow rho (sigma / 2)
  let r_1sigma_half := Real.rpow rho ((1 - sigma) / 2)
  let r_m1sigma_half := Real.rpow rho ((-1 + sigma) / 2)
  have hd12_pos : 0 < d12 := Real.rpow_pos_of_pos hdelta _
  have hd_12_pos : 0 < d_12 := Real.rpow_pos_of_pos hdelta _
  have hd24_2_pos : 0 < d24_2 := Real.rpow_pos_of_pos hdelta _
  have hd2_pos : 0 < d2 := Real.rpow_pos_of_pos hdelta _
  have hr_half_pos : 0 < r_half := Real.rpow_pos_of_pos hrho _
  have hr_sigma_half_pos : 0 < r_sigma_half := Real.rpow_pos_of_pos hrho _
  have hr_1sigma_half_pos : 0 < r_1sigma_half := Real.rpow_pos_of_pos hrho _
  have hr_m1sigma_half_pos : 0 < r_m1sigma_half := Real.rpow_pos_of_pos hrho _
  have hsqrt : Real.sqrt rho = r_half := Real.sqrt_eq_rpow rho
  have hC_nonneg : 0 ≤ C := by linarith
  -- Real arithmetic
  have hprod_real : d_12 * r_m1sigma_half * r_half * d2 =
      d_12 * d2 * r_sigma_half := by
    have h1 : r_m1sigma_half * r_half = r_sigma_half := by
      dsimp only [r_m1sigma_half, r_half, r_sigma_half]
      have h_add : Real.rpow rho (((-1 + sigma) / 2) + (1 / 2)) =
          Real.rpow rho ((-1 + sigma) / 2) * Real.rpow rho (1 / 2) :=
        Real.rpow_add hrho ((-1 + sigma) / 2) (1 / 2)
      have h_sum : ((-1 + sigma) / 2) + (1 / 2) = sigma / 2 := by ring
      rw [h_sum] at h_add
      exact h_add.symm
    have h_goal : d_12 * r_m1sigma_half * r_half * d2 = d_12 * d2 * (r_m1sigma_half * r_half) := by ring
    rw [h_goal, h1] <;> ring
  have htotal_real : d12 * r_half * (d_12 * d2 * r_sigma_half)⁻¹ = d24_2 * r_1sigma_half := by
    have h2 : d_12 * d2 = Real.rpow delta (-(12 * eta) + 2) := by
      dsimp only [d_12, d2]
      have h_add : Real.rpow delta ((-(12 * eta)) + 2) =
          Real.rpow delta (-(12 * eta)) * Real.rpow delta 2 :=
        Real.rpow_add hdelta (-(12 * eta)) 2
      exact h_add.symm
    have h3 : d12 * (d_12 * d2)⁻¹ = d24_2 := by
      rw [h2]
      dsimp only [d12, d24_2]
      have h_neg : (Real.rpow delta (-(12 * eta) + 2))⁻¹ = Real.rpow delta (-((-(12 * eta) + 2))) := by
        exact (Real.rpow_neg hdelta.le (-(12 * eta) + 2)).symm
      rw [h_neg]
      have h6 : Real.rpow delta (12 * eta) * Real.rpow delta (-((-(12 * eta) + 2))) =
          Real.rpow delta (12 * eta + (-((-(12 * eta) + 2)))) := by
        exact (Real.rpow_add hdelta (12 * eta) (-((-(12 * eta) + 2)))).symm
      rw [h6]
      have h7 : 12 * eta + (-((-(12 * eta) + 2))) = 24 * eta - 2 := by ring
      rw [h7]
    have h5 : r_half * r_sigma_half⁻¹ = r_1sigma_half := by
      dsimp only [r_half, r_sigma_half, r_1sigma_half]
      have h6 : (Real.rpow rho (sigma / 2))⁻¹ = Real.rpow rho (-(sigma / 2)) := by
        exact (Real.rpow_neg hrho.le (sigma / 2)).symm
      rw [h6]
      have h7 : Real.rpow rho (1 / 2) * Real.rpow rho (-(sigma / 2)) =
          Real.rpow rho (1 / 2 + (-(sigma / 2))) := by
        exact (Real.rpow_add hrho (1 / 2) (-(sigma / 2))).symm
      rw [h7]
      have h8 : 1 / 2 + (-(sigma / 2)) = (1 - sigma) / 2 := by ring
      rw [h8]
    calc
      d12 * r_half * (d_12 * d2 * r_sigma_half)⁻¹
        = d12 * (d_12 * d2)⁻¹ * (r_half * r_sigma_half⁻¹) := by ring
      _ = d24_2 * r_1sigma_half := by rw [h3, h5] <;> ring
  -- ENNReal conversions
  let total : ENNReal := Kakeya.realRpowENN delta (12 * eta) * ENNReal.ofReal (Real.sqrt rho)
  let cap : ENNReal := ENNReal.ofReal (C * Real.sqrt rho * delta ^ 2)
  let prod : ENNReal := prismCount * cap
  let upper : ENNReal := ENNReal.ofReal (C * d_12 * d2 * r_sigma_half)
  let desired : ENNReal := ENNReal.ofReal (d24_2 * r_1sigma_half)
  have htotal_eq : total = ENNReal.ofReal (d12 * r_half) := by
    have h : Kakeya.realRpowENN delta (12 * eta) = ENNReal.ofReal d12 := by
      simp [Kakeya.realRpowENN] <;> rfl
    rw [show total = Kakeya.realRpowENN delta (12 * eta) * ENNReal.ofReal (Real.sqrt rho) from rfl]
    rw [h, hsqrt]
    rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
  have hcap_eq : cap = ENNReal.ofReal (C * r_half * d2) := by
    have hdelta2 : delta ^ 2 = d2 := by
      dsimp only [d2]
      exact (Real.rpow_two delta).symm
    rw [show cap = ENNReal.ofReal (C * Real.sqrt rho * delta ^ 2) from rfl]
    have h : ENNReal.ofReal (C * Real.sqrt rho * delta ^ 2) =
        ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt rho) * ENNReal.ofReal (delta ^ 2) := by
      rw [← ENNReal.ofReal_mul hC_nonneg, ← ENNReal.ofReal_mul (by positivity)] <;> ring
    rw [h, hsqrt, hdelta2]
    rw [← ENNReal.ofReal_mul hC_nonneg, ← ENNReal.ofReal_mul (by positivity)] <;> rfl
  have hprod_ne_zero : prod ≠ 0 := by
    rw [show prod = prismCount * cap from rfl]
    apply mul_ne_zero hprism_pos.ne'
    have hprod_pos : 0 < C * r_half * d2 := by positivity
    have hcap_pos : 0 < cap := by
      rw [hcap_eq]
      exact ENNReal.ofReal_pos.mpr hprod_pos
    exact hcap_pos.ne'
  have hcap_ne_top : cap ≠ ⊤ := by exact ENNReal.ofReal_ne_top
  have hprod_ne_top : prod ≠ ⊤ := ENNReal.mul_ne_top hprism_ne_top hcap_ne_top
  have hupper_ne_zero : upper ≠ 0 := by
    simp [upper, ENNReal.ofReal_eq_zero] <;> positivity
  have hupper_ne_top : upper ≠ ⊤ := by simp [upper, ENNReal.ofReal_ne_top]
  -- total ≤ prod * activeCount → prod⁻¹ * total ≤ activeCount
  have h2 : prod⁻¹ * total ≤ activeCount := by
    have h3 : total ≤ prod * activeCount := by
      have h_rhs : prismCount * ENNReal.ofReal (C * Real.sqrt rho * delta ^ 2) * activeCount =
          prod * activeCount := by
        dsimp only [prod, cap] <;> ring
      rw [h_rhs] at h1
      exact h1
    have h4 : prod⁻¹ * total ≤ prod⁻¹ * (prod * activeCount) := by gcongr
    have h5 : prod⁻¹ * (prod * activeCount) = activeCount :=
      ENNReal.inv_mul_cancel_left hprod_ne_zero hprod_ne_top
    rw [h5] at h4
    exact h4
  -- prod ≤ upper
  have hprod_upper2 : prod ≤ upper := by
    rw [show prod = prismCount * cap from rfl, hcap_eq]
    have h_prism2 : prismCount ≤ ENNReal.ofReal (d_12 * r_m1sigma_half) := by
      have h1 : Kakeya.realRpowENN delta (-(12 * eta)) = ENNReal.ofReal d_12 := by
        simp [Kakeya.realRpowENN] <;> rfl
      have h2 : Kakeya.realRpowENN rho ((-1 + sigma) / 2) = ENNReal.ofReal r_m1sigma_half := by
        simp [Kakeya.realRpowENN] <;> rfl
      have h3 : Kakeya.realRpowENN delta (-(12 * eta)) * Kakeya.realRpowENN rho ((-1 + sigma) / 2) =
          ENNReal.ofReal (d_12 * r_m1sigma_half) := by
        rw [h1, h2]
        rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
      rw [h3] at hprism_upper
      exact hprism_upper
    calc
      prismCount * ENNReal.ofReal (C * r_half * d2)
        ≤ ENNReal.ofReal (d_12 * r_m1sigma_half) * ENNReal.ofReal (C * r_half * d2) := by gcongr
      _ = ENNReal.ofReal ((d_12 * r_m1sigma_half) * (C * r_half * d2)) := by
        rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
      _ = upper := by
        rw [show upper = ENNReal.ofReal (C * d_12 * d2 * r_sigma_half) from rfl]
        congr 1
        have h_assoc : (d_12 * r_m1sigma_half) * (C * r_half * d2) =
            C * (d_12 * r_m1sigma_half * r_half * d2) := by ring
        rw [h_assoc, hprod_real] <;> ring
  -- prod⁻¹ ≥ upper⁻¹
  have hprod_inv_ge : prod⁻¹ ≥ upper⁻¹ := ENNReal.inv_le_inv.mpr hprod_upper2
  -- upper⁻¹ * total = C⁻¹ * desired
  have hupper_inv_total : upper⁻¹ * total = ENNReal.ofReal C⁻¹ * desired := by
    rw [show upper = ENNReal.ofReal (C * d_12 * d2 * r_sigma_half) from rfl, htotal_eq]
    have h_upper_inv : (ENNReal.ofReal (C * d_12 * d2 * r_sigma_half))⁻¹ =
        ENNReal.ofReal ((C * d_12 * d2 * r_sigma_half)⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos (by positivity)]
    rw [h_upper_inv]
    rw [← ENNReal.ofReal_mul (by positivity)]
    have h_comm : (C * d_12 * d2 * r_sigma_half)⁻¹ * (d12 * r_half) =
        C⁻¹ * (d12 * r_half * (d_12 * d2 * r_sigma_half)⁻¹) := by
      field_simp [hC_pos.ne'] <;> ring
    rw [h_comm, htotal_real]
    rw [← ENNReal.ofReal_mul (by positivity)]
    <;> rfl
  -- Finish
  have h6 : upper⁻¹ * total ≤ prod⁻¹ * total := by gcongr
  rw [hupper_inv_total] at h6
  have hdesired_eq : desired = Kakeya.realRpowENN delta (24 * eta - 2) * Kakeya.realRpowENN rho ((1 - sigma) / 2) := by
    have h1 : Kakeya.realRpowENN delta (24 * eta - 2) = ENNReal.ofReal d24_2 := by
      simp [Kakeya.realRpowENN] <;> rfl
    have h2 : Kakeya.realRpowENN rho ((1 - sigma) / 2) = ENNReal.ofReal r_1sigma_half := by
      simp [Kakeya.realRpowENN] <;> rfl
    have h3 : ENNReal.ofReal d24_2 * ENNReal.ofReal r_1sigma_half =
        ENNReal.ofReal (d24_2 * r_1sigma_half) := by
      rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
    have h4 : desired = ENNReal.ofReal (d24_2 * r_1sigma_half) := by rfl
    rw [h4, ← h3, ← h1, ← h2]
  rw [hdesired_eq] at h6
  have h_assoc : ENNReal.ofReal C⁻¹ * (Kakeya.realRpowENN delta (24 * eta - 2) * Kakeya.realRpowENN rho ((1 - sigma) / 2)) =
      ENNReal.ofReal C⁻¹ * Kakeya.realRpowENN delta (24 * eta - 2) * Kakeya.realRpowENN rho ((1 - sigma) / 2) := by
    ring
  rw [h_assoc] at h6
  exact h6.trans h2

/--
For sufficiently small delta, `2 * delta ≤ Real.sqrt rho * Real.rpow delta (-36 * eta / sigma)`.
-/
lemma delta_le_tau_helper
    {delta eta sigma rho : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (heta : 0 < eta) (hsigma : 0 < sigma)
    (hrho : 0 < rho) (hsqrt_rho_ge : 8 * Real.sqrt delta ≤ Real.sqrt rho) :
    2 * delta ≤ Real.sqrt rho * Real.rpow delta (-36 * eta / sigma) := by
  set e : ℝ := 36 * eta / sigma with he_def
  have he_pos : 0 < e := by positivity
  have h9 : Real.rpow delta (1 + e) ≤ Real.rpow delta (1 / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hdelta hdelta1.le (by linarith)
  have h10 : Real.rpow delta (1 / 2) = Real.sqrt delta :=
    (Real.sqrt_eq_rpow delta).symm
  have h_sqrt_nonneg : 0 ≤ Real.sqrt delta := Real.sqrt_nonneg delta
  have h11 : 2 * Real.rpow delta (1 + e) ≤ 8 * Real.sqrt delta := by
    calc
      2 * Real.rpow delta (1 + e) ≤ 2 * Real.rpow delta (1 / 2) := by gcongr
      _ = 2 * Real.sqrt delta := by rw [h10]
      _ ≤ 8 * Real.sqrt delta := by
        have h : 2 * Real.sqrt delta ≤ 8 * Real.sqrt delta := by
          nlinarith
        exact h
  have h12 : Real.rpow delta (1 + e) = delta * Real.rpow delta e := by
    have h_add : Real.rpow delta (1 + e) = Real.rpow delta 1 * Real.rpow delta e :=
      Real.rpow_add hdelta 1 e
    have h1 : Real.rpow delta 1 = delta := Real.rpow_one delta
    rw [h_add, h1] <;> ring
  have h13 : 2 * (delta * Real.rpow delta e) ≤ 8 * Real.sqrt delta := by
    have h14 : 2 * (delta * Real.rpow delta e) = 2 * Real.rpow delta (1 + e) := by
      rw [← h12] <;> ring
    rw [h14]
    exact h11
  have h13' : 2 * delta * Real.rpow delta e ≤ 8 * Real.sqrt delta := by
    have h : 2 * delta * Real.rpow delta e = 2 * (delta * Real.rpow delta e) := by ring
    rw [h]
    exact h13
  have h_pos_e : 0 < Real.rpow delta e := Real.rpow_pos_of_pos hdelta e
  have h14 : 2 * delta ≤ 8 * Real.sqrt delta * (Real.rpow delta e)⁻¹ := by
    calc
      2 * delta
        = (2 * delta * Real.rpow delta e) * (Real.rpow delta e)⁻¹ := by
          field_simp [h_pos_e.ne'] <;> ring
      _ ≤ (8 * Real.sqrt delta) * (Real.rpow delta e)⁻¹ := by gcongr
  have h15 : (Real.rpow delta e)⁻¹ = Real.rpow delta (-e) := by
    exact (Real.rpow_neg hdelta.le e).symm
  have h16 : 2 * delta ≤ 8 * Real.sqrt delta * Real.rpow delta (-e) := by
    rw [h15] at h14
    exact h14
  have h17 : -e = -36 * eta / sigma := by
    simp [he_def] <;> ring
  rw [h17] at h16
  have h18 : 2 * delta ≤ Real.sqrt rho * Real.rpow delta (-36 * eta / sigma) := by
    calc
      2 * delta ≤ 8 * Real.sqrt delta * Real.rpow delta (-36 * eta / sigma) := h16
      _ ≤ Real.sqrt rho * Real.rpow delta (-36 * eta / sigma) := by
        have h19 : 8 * Real.sqrt delta ≤ Real.sqrt rho := hsqrt_rho_ge
        have h20 : 0 ≤ Real.rpow delta (-36 * eta / sigma) := by
          exact Real.rpow_nonneg hdelta.le _
        nlinarith
  exact h18

/-- `sqrt rho ≤ sqrt rho * delta^(-36*eta/sigma)` since `delta < 1`. -/
lemma sqrt_rho_le_tau
    {delta eta sigma rho : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (heta : 0 < eta) (hsigma : 0 < sigma)
    (hrho : 0 < rho) :
    Real.sqrt rho ≤ Real.sqrt rho * Real.rpow delta (-36 * eta / sigma) := by
  have h1 : 1 ≤ Real.rpow delta (-36 * eta / sigma) := by
    have hpos : 0 < 36 * eta / sigma := by positivity
    have h_nonpos : -36 * eta / sigma ≤ 0 := by
      have h_eq : -36 * eta / sigma = -(36 * eta / sigma) := by ring
      rw [h_eq]
      exact neg_nonpos.mpr hpos.le
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdelta1.le h_nonpos
  have h4 : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
  nlinarith

end Kakeya.Assouad
