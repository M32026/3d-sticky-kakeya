module

/-
# Phase0 Constant Absorption Helpers

Helper lemmas for closing `hC_plan_bound` and `hC_Kauf_bound` sorrys
in IncidenceToRingProof.lean.

## Constants

- `planConstant s κ0`: numerical factor in C_plan ~ δ^{-5η_work} bound
- `kaufmanConstant τ κ0`: numerical factor in C_Kaufman ~ δ^{-η_work/2 - 2κ0·q_box} bound

## Threshold exponents

- Plan gap: `qPlan η_work - 5η_work = 501η_work/100 > 0`
- Kauf gap: `51η_work/100 > 0`

## Whiteprint
Helper for Phase0 absorption in incidence_to_ring_contradiction.
-/

public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV3
public import MyLeanRepo.Energy.RegularSetHasBoundedEnergy
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open ProductLikeIncidence.ProductReduction

namespace ProductLikeIncidence.ProductReduction

/-- Numerical constant for C_plan growth absorption. -/
def planConstant (s κ0 : ℝ) : ℝ :=
  1 + (9 * (1 - (2 : ℝ) ^ (2 * (κ0 - s)) + (2 : ℝ) ^ (2 * κ0))
    / (1 - (2 : ℝ) ^ (2 * (κ0 - s)))) * (4 * (49 : ℝ)^2 * (35 : ℝ)^8)

/-- Numerical constant for C_Kaufman growth absorption. -/
def kaufmanConstant (τ κ0 : ℝ) : ℝ :=
  1 + (3 * (2 : ℝ)^τ + 1) * τ / (τ - 2 * κ0)

/-- Helper: `(δ ^ x) ^ n = δ ^ (x * n)` for natural `n`. -/
lemma rpow_pow_nat {δ x : ℝ} {n : ℕ} (hδ_pos : 0 < δ) :
    (δ ^ x) ^ n = δ ^ (x * (n : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← Real.rpow_add hδ_pos]
    <;> simp [mul_add, mul_one] <;> ring

/-- Explicit C_Pbar bound: `C_Pbar ≤ 4·49²·35⁸ · δ^{-5η_work}`. -/
lemma C_Pbar_explicit_bound
    {δ η_work C C_work' c_mult : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hη_work_pos : 0 < η_work)
    (hC_ge1 : 1 ≤ C)
    (hC_work'_eq : C_work' = 35 * C)
    (hC_le_target : C ≤ δ ^ (-η_work / 2))
    (hc_mult_def : c_mult = δ ^ (η_work / 2) / (7 * C_work' ^ 2)) :
    4 * (49 * C_work'^4) / c_mult^2 ≤
      (4 * (49 : ℝ)^2 * (35 : ℝ)^8) * δ ^ (-5 * η_work) := by
  have hC_pos : 0 < C := by linarith
  have hC_work'_pos : 0 < C_work' := by
    rw [hC_work'_eq] <;> positivity
  have hC_work'_le : C_work' ≤ 35 * δ ^ (-η_work / 2) := by
    rw [hC_work'_eq]
    have h : C ≤ δ ^ (-η_work / 2) := hC_le_target
    have h' : 35 * C ≤ 35 * δ ^ (-η_work / 2) := by gcongr
    exact h'
  have h_rpow8 : (δ ^ (-η_work / 2)) ^ 8 = δ ^ (-4 * η_work) := by
    rw [rpow_pow_nat hδ_pos] <;> ring_nf
  have h1 : C_work' ^ 8 ≤ (35 : ℝ)^8 * δ ^ (-4 * η_work) := by
    have h1a : C_work' ^ 8 ≤ (35 * δ ^ (-η_work / 2)) ^ 8 := by
      gcongr <;> linarith
    have h1b : (35 * δ ^ (-η_work / 2)) ^ 8 = (35 : ℝ)^8 * (δ ^ (-η_work / 2)) ^ 8 := by
      rw [mul_pow]
    rw [h1b] at h1a
    rw [h_rpow8] at h1a
    exact h1a
  have h_rpow2 : (δ ^ (η_work / 2)) ^ 2 = δ ^ η_work := by
    rw [rpow_pow_nat hδ_pos] <;> ring_nf
  have h5 : c_mult ^ 2 = δ ^ η_work / (49 * C_work' ^ 4) := by
    rw [hc_mult_def]
    have h_div2 : (δ ^ (η_work / 2) / (7 * C_work' ^ 2)) ^ 2 =
        (δ ^ (η_work / 2)) ^ 2 / (7 * C_work' ^ 2) ^ 2 := by
      rw [div_pow] <;> positivity
    rw [h_div2, h_rpow2]
    <;> ring
  have h6 : 4 * (49 * C_work'^4) / c_mult^2 =
      4 * (49 : ℝ)^2 * C_work'^8 / δ ^ η_work := by
    rw [h5]
    field_simp [hδ_pos.ne'] <;> ring
  rw [h6]
  have h_div_rpow : δ ^ (-4 * η_work) / δ ^ η_work = δ ^ (-5 * η_work) := by
    have h_neg : (δ ^ η_work)⁻¹ = δ ^ (-η_work) := by
      rw [Real.rpow_neg (by positivity)] <;> ring
    have h : δ ^ (-4 * η_work) / δ ^ η_work = δ ^ (-4 * η_work) * (δ ^ η_work)⁻¹ := by ring
    rw [h, h_neg, ← Real.rpow_add hδ_pos] <;> ring_nf
  calc
    4 * (49 : ℝ)^2 * C_work'^8 / δ ^ η_work
      ≤ 4 * (49 : ℝ)^2 * ((35 : ℝ)^8 * δ ^ (-4 * η_work)) / δ ^ η_work := by
        gcongr
        <;> positivity
    _ = (4 * (49 : ℝ)^2 * (35 : ℝ)^8) * (δ ^ (-4 * η_work) / δ ^ η_work) := by ring
    _ = (4 * (49 : ℝ)^2 * (35 : ℝ)^8) * δ ^ (-5 * η_work) := by
      rw [h_div_rpow]

/-- Explicit C_plan bound from C_Pbar bound and constant absorption threshold. -/
lemma plan_bound_from_threshold
    {δ η_work s κ0 C_Pbar C_plan : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hη_work_pos : 0 < η_work)
    (hs_lt_one : s < 1) (hkappa_lt_s : κ0 < s) (hkappa_pos : 0 < κ0)
    (hC_Pbar_bound : C_Pbar ≤ (4 * (49 : ℝ)^2 * (35 : ℝ)^8) * δ ^ (-5 * η_work))
    (h_plan_absorb : planConstant s κ0 ≤ δ ^ (-(qPlan η_work - 5 * η_work)))
    (hC_plan_def : C_plan = robust_projection.energyBoundConstant C_Pbar s κ0) :
    C_plan ≤ δ ^ (-(qPlan η_work)) := by
  set K : ℝ := (9 * (1 - (2 : ℝ) ^ (2 * (κ0 - s)) + (2 : ℝ) ^ (2 * κ0))
    / (1 - (2 : ℝ) ^ (2 * (κ0 - s)))) with hK_def
  have hden_pos : 0 < 1 - (2 : ℝ) ^ (2 * (κ0 - s)) := by
    have h1 : 2 * (κ0 - s) < 0 := by linarith
    have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h_log : Real.log ((2 : ℝ) ^ (2 * (κ0 - s))) = (2 * (κ0 - s)) * Real.log 2 := by
      rw [Real.log_rpow (by norm_num)]
    have h_neg : (2 * (κ0 - s)) * Real.log 2 < 0 := by
      exact mul_neg_of_neg_of_pos h1 h_log2_pos
    have h_lt1 : (2 : ℝ) ^ (2 * (κ0 - s)) < 1 := by
      have h_pos' : 0 < (2 : ℝ) ^ (2 * (κ0 - s)) := by positivity
      have h : Real.log ((2 : ℝ) ^ (2 * (κ0 - s))) < Real.log 1 := by
        rw [h_log, Real.log_one] <;> exact h_neg
      exact (Real.log_lt_log_iff h_pos' (by norm_num)).mp h
    linarith
  have hnum_pos : 0 < 1 - (2 : ℝ) ^ (2 * (κ0 - s)) + (2 : ℝ) ^ (2 * κ0) := by
    have h3 : 0 < 1 - (2 : ℝ) ^ (2 * (κ0 - s)) := hden_pos
    have h4 : 0 < (2 : ℝ) ^ (2 * κ0) := by positivity
    linarith
  have hK_nonneg : 0 ≤ K := by
    rw [hK_def]
    have h_num : 0 ≤ 9 * (1 - (2 : ℝ) ^ (2 * (κ0 - s)) + (2 : ℝ) ^ (2 * κ0)) := by
      have h7 : 0 ≤ 1 - (2 : ℝ) ^ (2 * (κ0 - s)) + (2 : ℝ) ^ (2 * κ0) := by linarith [hnum_pos]
      exact mul_nonneg (by norm_num) h7
    have h_den : 0 ≤ 1 - (2 : ℝ) ^ (2 * (κ0 - s)) := by linarith
    exact div_nonneg h_num h_den
  have h1 : 1 ≤ δ ^ (-5 * η_work) := by
    have h2 : -5 * η_work ≤ (0 : ℝ) := by linarith
    have h3 : δ ^ (0 : ℝ) ≤ δ ^ (-5 * η_work) :=
      Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h2
    simpa using h3
  have h_main1 : robust_projection.energyBoundConstant C_Pbar s κ0 = 1 + K * C_Pbar := by
    simp [robust_projection.energyBoundConstant, hK_def] <;> ring
  have hC_plan_bound : C_plan ≤ planConstant s κ0 * δ ^ (-5 * η_work) := by
    rw [hC_plan_def, h_main1]
    dsimp only [planConstant]
    have h4 : K * C_Pbar ≤ K * ((4 * (49 : ℝ)^2 * (35 : ℝ)^8) * δ ^ (-5 * η_work)) := by
      gcongr
      <;> linarith
    have h5 : 1 + K * C_Pbar ≤
        (1 + K * (4 * (49 : ℝ)^2 * (35 : ℝ)^8)) * δ ^ (-5 * η_work) := by
      calc
        1 + K * C_Pbar ≤ 1 + K * ((4 * (49 : ℝ)^2 * (35 : ℝ)^8) * δ ^ (-5 * η_work)) := by
          gcongr
        _ = 1 + (K * (4 * (49 : ℝ)^2 * (35 : ℝ)^8)) * δ ^ (-5 * η_work) := by ring
        _ ≤ (1 + K * (4 * (49 : ℝ)^2 * (35 : ℝ)^8)) * δ ^ (-5 * η_work) := by
          have h6 : 1 ≤ δ ^ (-5 * η_work) := h1
          nlinarith
    simpa [planConstant] using h5
  calc C_plan
    ≤ planConstant s κ0 * δ ^ (-5 * η_work) := hC_plan_bound
  _ ≤ δ ^ (-(qPlan η_work - 5 * η_work)) * δ ^ (-5 * η_work) := by gcongr
  _ = δ ^ (-(qPlan η_work)) := by
    rw [← Real.rpow_add hδ_pos] <;> ring_nf

/-- Explicit C_Kaufman bound from R bound and constant absorption threshold. -/
lemma kauf_bound_from_threshold
    {δ η_work τ κ0 R q_box C C_ν C_Kaufman : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hη_work_pos : 0 < η_work) (hτ_pos : 0 < τ)
    (hkappa_pos : 0 < κ0) (h2kappa_lt_tau : 2 * κ0 < τ)
    (hC_ge1 : 1 ≤ C)
    (hq_box_pos : 0 < q_box)
    (hq_box_eq : q_box = qBox η_work τ)
    (hC_le_target : C ≤ δ ^ (-η_work / 2))
    (hR_pos : 0 < R)
    (h4R_le_qbox : 4 * R ≤ δ ^ (-q_box))
    (h_Kauf_absorb : kaufmanConstant τ κ0 ≤ δ ^ (-(51 * η_work / 100)))
    (hC_ν_def : C_ν = 3 * C * (2 : ℝ)^τ)
    (hC_Kauf_def : C_Kaufman = 1 + (C_ν + 1) * (2 * R * Real.sqrt 2)^(2 * κ0) * (1 + 2 * κ0 / (τ - 2 * κ0))) :
    C_Kaufman ≤ δ ^ (-(η_work + qKaufman η_work τ κ0 + qAbsorb η_work)) := by
  have hτ2κ_pos : 0 < τ - 2 * κ0 := by linarith
  have hτ2κ_ne : τ - 2 * κ0 ≠ 0 := hτ2κ_pos.ne'
  have h1 : 1 ≤ δ ^ (-η_work / 2) := by
    have h2 : -η_work / 2 ≤ (0 : ℝ) := by linarith
    have h3 : δ ^ (0 : ℝ) ≤ δ ^ (-η_work / 2) :=
      Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h2
    simpa using h3
  have h_pos2τ : 0 ≤ 3 * (2 : ℝ)^τ := by positivity
  have hCν_plus1 : C_ν + 1 ≤ (3 * (2 : ℝ)^τ + 1) * δ ^ (-η_work / 2) := by
    rw [hC_ν_def]
    have h4 : 3 * C * (2 : ℝ)^τ ≤ 3 * (2 : ℝ)^τ * δ ^ (-η_work / 2) := by
      have h41 : C ≤ δ ^ (-η_work / 2) := hC_le_target
      have h : (3 * (2 : ℝ)^τ) * C ≤ (3 * (2 : ℝ)^τ) * δ ^ (-η_work / 2) :=
        mul_le_mul_of_nonneg_left h41 h_pos2τ
      ring_nf at h ⊢ <;> exact h
    have h5 : 3 * C * (2 : ℝ)^τ + 1 ≤ (3 * (2 : ℝ)^τ + 1) * δ ^ (-η_work / 2) := by
      calc
        3 * C * (2 : ℝ)^τ + 1 ≤ 3 * (2 : ℝ)^τ * δ ^ (-η_work / 2) + 1 := by linarith
        _ ≤ 3 * (2 : ℝ)^τ * δ ^ (-η_work / 2) + δ ^ (-η_work / 2) := by
          have h6 : 1 ≤ δ ^ (-η_work / 2) := h1
          linarith
        _ = (3 * (2 : ℝ)^τ + 1) * δ ^ (-η_work / 2) := by ring
    exact h5
  have hR_simple : 2 * R * Real.sqrt 2 ≤ δ ^ (-q_box) := by
    have hR4 : R ≤ δ ^ (-q_box) / 4 := by linarith
    have h_posq : 0 < δ ^ (-q_box) := by positivity
    have h : 2 * R * Real.sqrt 2 ≤ 2 * (δ ^ (-q_box) / 4) * Real.sqrt 2 := by gcongr
    have h2 : 2 * (δ ^ (-q_box) / 4) * Real.sqrt 2 ≤ δ ^ (-q_box) := by
      have h3 : 0 ≤ δ ^ (-q_box) := by positivity
      have h4 : Real.sqrt 2 ≤ 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      nlinarith
    linarith
  have h_pos_base : 0 ≤ 2 * R * Real.sqrt 2 := by positivity
  have h3 : (2 * R * Real.sqrt 2) ^ (2 * κ0) ≤ (δ ^ (-q_box)) ^ (2 * κ0) :=
    Real.rpow_le_rpow h_pos_base hR_simple (by linarith)
  have h4 : (δ ^ (-q_box)) ^ (2 * κ0) = δ ^ (-2 * κ0 * q_box) := by
    have h41 : (δ ^ (-q_box)) ^ (2 * κ0) = δ ^ ((-q_box) * (2 * κ0)) := by
      rw [Real.rpow_mul hδ_pos.le]
    rw [h41]
    <;> ring_nf
  have hR_pow : (2 * R * Real.sqrt 2) ^ (2 * κ0) ≤ δ ^ (-2 * κ0 * q_box) := by
    rw [h4] at h3
    exact h3
  have h_factor_eq : 1 + 2 * κ0 / (τ - 2 * κ0) = τ / (τ - 2 * κ0) := by
    field_simp [hτ2κ_ne] <;> ring
  have h_exp_nonpos : -η_work / 2 - 2 * κ0 * q_box ≤ 0 := by
    have hq_pos : 0 < q_box := hq_box_pos
    have h1 : 0 ≤ 2 * κ0 * q_box := by positivity
    linarith
  have h9 : 1 ≤ δ ^ (-η_work / 2 - 2 * κ0 * q_box) := by
    have h10 : δ ^ (0 : ℝ) ≤ δ ^ (-η_work / 2 - 2 * κ0 * q_box) :=
      Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h_exp_nonpos
    simpa using h10
  set K_Kauf' : ℝ := (3 * (2 : ℝ)^τ + 1) * (τ / (τ - 2 * κ0)) with hK_Kauf'_def
  have h_pos_Cν : 0 ≤ C_ν + 1 := by
    rw [hC_ν_def] <;> positivity
  have h_pos_Rpow : 0 ≤ (2 * R * Real.sqrt 2)^(2 * κ0) := by positivity
  have h_pos_factor : 0 ≤ τ / (τ - 2 * κ0) := by positivity
  have h10 : (C_ν + 1) * (2 * R * Real.sqrt 2)^(2 * κ0) * (1 + 2 * κ0 / (τ - 2 * κ0)) ≤
      K_Kauf' * δ ^ (-η_work / 2 - 2 * κ0 * q_box) := by
    rw [h_factor_eq]
    calc
      (C_ν + 1) * (2 * R * Real.sqrt 2)^(2 * κ0) * (τ / (τ - 2 * κ0))
        ≤ ((3 * (2 : ℝ)^τ + 1) * δ ^ (-η_work / 2)) * (δ ^ (-2 * κ0 * q_box)) * (τ / (τ - 2 * κ0)) := by
          gcongr
          <;> linarith
      _ = K_Kauf' * (δ ^ (-η_work / 2) * δ ^ (-2 * κ0 * q_box)) := by
        rw [hK_Kauf'_def] <;> ring
      _ = K_Kauf' * δ ^ (-η_work / 2 - 2 * κ0 * q_box) := by
        rw [← Real.rpow_add hδ_pos] <;> ring_nf
  have h10' : (C_ν + 1) * (2 * R * Real.sqrt 2)^(2 * κ0) * (τ / (τ - 2 * κ0)) ≤
      K_Kauf' * δ ^ (-η_work / 2 - 2 * κ0 * q_box) := by
    have h10_eq : (C_ν + 1) * (2 * R * Real.sqrt 2)^(2 * κ0) * (1 + 2 * κ0 / (τ - 2 * κ0)) =
        (C_ν + 1) * (2 * R * Real.sqrt 2)^(2 * κ0) * (τ / (τ - 2 * κ0)) := by
      rw [h_factor_eq]
    rw [h10_eq] at h10
    exact h10
  have hC_Kauf_bound : C_Kaufman ≤ kaufmanConstant τ κ0 * δ ^ (-η_work / 2 - 2 * κ0 * q_box) := by
    rw [hC_Kauf_def, h_factor_eq]
    dsimp only [kaufmanConstant]
    have h11 : 1 + (C_ν + 1) * (2 * R * Real.sqrt 2)^(2 * κ0) * (τ / (τ - 2 * κ0)) ≤
          1 + K_Kauf' * δ ^ (-η_work / 2 - 2 * κ0 * q_box) := by
      linarith [h10']
    have h12 : 1 + K_Kauf' * δ ^ (-η_work / 2 - 2 * κ0 * q_box) ≤
          (1 + K_Kauf') * δ ^ (-η_work / 2 - 2 * κ0 * q_box) := by
      have h13 : 1 ≤ δ ^ (-η_work / 2 - 2 * κ0 * q_box) := h9
      nlinarith
    have h14 : (1 + K_Kauf') = kaufmanConstant τ κ0 := by
      dsimp only [kaufmanConstant, K_Kauf'] <;> ring
    rw [h14] at h12
    exact le_trans h11 h12
  have h_exp_eq : (-(51 * η_work / 100)) + (-η_work / 2 - 2 * κ0 * q_box) =
      -(η_work + qKaufman η_work τ κ0 + qAbsorb η_work) := by
    have hq : q_box = qBox η_work τ := hq_box_eq
    dsimp only [qKaufman, qAbsorb]
    rw [hq]
    <;> ring
  calc C_Kaufman
    ≤ kaufmanConstant τ κ0 * δ ^ (-η_work / 2 - 2 * κ0 * q_box) := hC_Kauf_bound
  _ ≤ δ ^ (-(51 * η_work / 100)) * δ ^ (-η_work / 2 - 2 * κ0 * q_box) := by gcongr
  _ = δ ^ (-(η_work + qKaufman η_work τ κ0 + qAbsorb η_work)) := by
    rw [← Real.rpow_add hδ_pos, h_exp_eq]

end ProductLikeIncidence.ProductReduction
