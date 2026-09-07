module

/-
# Extraction Numeric Conditions

Standalone lemmas for the two δ-smallness conditions needed by the endgame
extraction step:

1. `h_energy_small`: energy constant absorption — follows ALGEBRAICALLY from
   `4R ≤ δ^(-qBox)` because `qEnergy = 2κ0 · qBox`. No extra δ-smallness needed.

2. `h_extract_small`: logarithmic factor absorption for the extraction constant.
   Requires a δ-smallness hypothesis, which can be supplied by the outer δ₀.

## Usage in dune skeleton

Replace the sorrys at lines 770-773 of `IncidenceToRingProof.lean` with:

```lean
have h_energy_small := energy_small_from_qbox hδ_pos hδ_lt_one hη_work_pos hτ_pos hkappa_pos
  hR_ge1 h4R_le_qbox
have h_extract_small := extract_small_from_log_absorb hδ_pos hδ_lt_one
  hkappa_pos hR_ge1 h4R_le_qbox h_qbox_nonneg h_gap_half h_extract_log_absorb
```

And add `h_extract_log_absorb` to the theorem signature.

## Whiteprint node
Numeric conditions for Category B extraction constant bound.
-/

public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV3
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV4
public import MyLeanRepo.ProductLikeIncidence.V4NumericFills
public import MyLeanRepo.ProductLikeIncidence.LogAbsorbThreshold
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open ProductLikeIncidence.ProductReduction Real

namespace ProductLikeIncidence.ProductReduction

/-! ## 1. Energy constant absorption (algebraic, no δ-smallness) -/

/-- `h_energy_small` follows from `4R ≤ δ^(-qBox)` because `qEnergy = 2κ0 · qBox`.

Given `4R ≤ δ^(-qBox)`, we have `(4R)^(2κ0) ≤ δ^(-2κ0·qBox) = δ^(-qEnergy)`,
so `1/(4R)^(2κ0) ≥ δ^qEnergy`. And since `4R ≥ 1`, `(δ/(4R))^qEnergy ≤ δ^qEnergy`.
Therefore `(δ/(4R))^qEnergy ≤ 1/(4R)^(2κ0)`. -/
lemma energy_small_from_qbox
    {δ R η τ κ0 : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hη_pos : 0 < η)
    (hτ_pos : 0 < τ)
    (hκ_pos : 0 < κ0)
    (hR_ge1 : 1 ≤ R)
    (h4R_le_qbox : 4 * R ≤ δ ^ (-(qBox η τ))) :
    (δ / (4 * R)) ^ (qEnergy η τ κ0) ≤ 1 / (4 * R) ^ (2 * κ0) := by
  have hqBox_pos : 0 < qBox η τ := by
    dsimp only [qBox, qAbsorb]
    have h1 : 0 < 4 * η / τ := by positivity
    have h2 : 0 ≤ η / 100 := by positivity
    linarith
  have hqEnergy_pos : 0 < qEnergy η τ κ0 := by
    dsimp only [qEnergy]
    exact mul_pos (mul_pos (by linarith) hκ_pos) hqBox_pos
  have h4R_pos : 0 < 4 * R := by linarith
  have h4R_ge1 : 1 ≤ 4 * R := by linarith
  -- Step 1: (4R)^(2κ0) ≤ δ^(-qEnergy)
  have h1 : (4 * R) ^ (2 * κ0) ≤ δ ^ (-(qEnergy η τ κ0)) := by
    have h11 : (4 * R) ^ (2 * κ0) ≤ (δ ^ (-(qBox η τ))) ^ (2 * κ0) := by
      gcongr <;> linarith
    have h12 : (δ ^ (-(qBox η τ))) ^ (2 * κ0) = δ ^ (-(qEnergy η τ κ0)) := by
      have h_eq : qEnergy η τ κ0 = 2 * κ0 * qBox η τ := by
        dsimp only [qEnergy] <;> ring
      rw [h_eq]
      rw [← Real.rpow_mul hδ_pos.le] <;> ring_nf <;> rfl
    rw [h12] at h11
    exact h11
  -- Step 2: 1/(4R)^(2κ0) ≥ δ^qEnergy
  have h2 : 0 < (4 * R) ^ (2 * κ0) := by positivity
  have h3 : 0 < δ ^ (-(qEnergy η τ κ0)) := by positivity
  have h4 : δ ^ (qEnergy η τ κ0) ≤ 1 / (4 * R) ^ (2 * κ0) := by
    have h41 : (δ ^ (-(qEnergy η τ κ0)))⁻¹ = δ ^ (qEnergy η τ κ0) := by
      have h : δ ^ (-(qEnergy η τ κ0)) = (δ ^ (qEnergy η τ κ0))⁻¹ :=
        Real.rpow_neg hδ_pos.le (qEnergy η τ κ0)
      rw [h]
      field_simp [hδ_pos.ne'] <;> ring
    have h42 : (δ ^ (-(qEnergy η τ κ0)))⁻¹ ≤ ((4 * R) ^ (2 * κ0))⁻¹ := by
      gcongr
      <;> linarith
    have h43 : δ ^ (qEnergy η τ κ0) ≤ ((4 * R) ^ (2 * κ0))⁻¹ := by
      rw [←h41] <;> exact h42
    simpa using h43
  -- Step 3: (δ/(4R))^qEnergy ≤ δ^qEnergy
  have h5 : δ / (4 * R) ≤ δ := by
    have h51 : 1 ≤ 4 * R := by linarith
    have h : δ / (4 * R) ≤ δ / 1 := by gcongr
    simpa using h
  have h6 : (δ / (4 * R)) ^ (qEnergy η τ κ0) ≤ δ ^ (qEnergy η τ κ0) := by
    have h61 : 0 ≤ δ / (4 * R) := by positivity
    have h62 : 0 ≤ qEnergy η τ κ0 := by linarith
    exact Real.rpow_le_rpow h61 h5 h62
  exact le_trans h6 h4

/-! ## 2. Extraction constant logarithmic absorption -/

/-- The logarithmic absorption constant for the extraction bound. -/
def extractLogConstant (κ0 : ℝ) : ℝ :=
  64 * (10 * (3 : ℝ) ^ (2 * κ0) * (2 : ℝ) ^ κ0) *
    (4 * ((κ0 + 1) / Real.log 2 + 1) ^ 2)

/-- Simplified outer δ-smallness hypothesis for extraction.

Uses `δ` directly instead of `δ/(4R)`, so it can be added to the theorem
signature without knowing `R`. The log factor is bounded using `4R ≤ δ^(-qBox)`.
-/
def extractLogAbsorbHyp (δ εnc η τ κ0 q_norm_energy : ℝ) : Prop :=
  let q_box := qBox η τ
  let α := (εnc / 2) / (1 + q_box) - q_norm_energy
  extractLogConstant κ0 * (1 + q_box) ^ 2 * (Real.log (1 / δ)) ^ 2 ≤ δ ^ (-α)

/-- Derive the exact `h_extract_small` condition from the simplified outer hypothesis.

Uses:
- `δ/(4R) ≥ δ^(1+qBox)` from `4R ≤ δ^(-qBox)`, so `log(1/(δ/(4R))) ≤ (1+qBox)·log(1/δ)`
- `δ/(4R) ≤ δ` from `4R ≥ 1`, so `(δ/(4R))^(-α) ≥ δ^(-α)`
-/
lemma extract_small_from_log_absorb
    {δ R εnc η τ κ0 q_norm_energy : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hκ_pos : 0 < κ0)
    (hR_ge1 : 1 ≤ R)
    (h4R_le_qbox : 4 * R ≤ δ ^ (-(qBox η τ)))
    (hqBox_nonneg : 0 ≤ qBox η τ)
    (h_gap : (1 + qBox η τ) * q_norm_energy < εnc / 2)
    (h_outer : extractLogAbsorbHyp δ εnc η τ κ0 q_norm_energy) :
    extractLogConstant κ0 * (Real.log (1 / (δ / (4 * R)))) ^ 2 ≤
      (δ / (4 * R)) ^ (-((εnc / 2) / (1 + qBox η τ) - q_norm_energy)) := by
  set q_box : ℝ := qBox η τ with hq_box_def
  set α : ℝ := (εnc / 2) / (1 + q_box) - q_norm_energy with hα_def
  have h1_pos : 0 < 1 + q_box := by linarith
  have hα_pos : 0 < α := by
    have h2 : (1 + q_box) * q_norm_energy < εnc / 2 := h_gap
    have h3 : q_norm_energy < (εnc / 2) / (1 + q_box) := by
      have h4 : q_norm_energy = ((1 + q_box) * q_norm_energy) / (1 + q_box) := by
        field_simp [h1_pos.ne'] <;> ring
      rw [h4]
      gcongr
    linarith [hα_def]
  have h4R_pos : 0 < 4 * R := by linarith
  have h4R_ge1 : 1 ≤ 4 * R := by linarith
  set x : ℝ := δ / (4 * R) with hx_def
  have hx_pos : 0 < x := by positivity
  have hx_lt_one : x < 1 := by
    have h : x ≤ δ := by
      dsimp only [x]
      have h2 : 1 ≤ 4 * R := by linarith
      have h3 : δ / (4 * R) ≤ δ / 1 := by gcongr
      simpa using h3
    linarith
  -- Lower bound: x ≥ δ^(1+q_box)
  have h_x_lower : x ≥ δ ^ (1 + q_box) := by
    dsimp only [x]
    have h2 : 4 * R ≤ δ ^ (-q_box) := h4R_le_qbox
    have h3 : δ / (4 * R) ≥ δ / (δ ^ (-q_box)) := by gcongr
    have h4 : δ / (δ ^ (-q_box)) = δ ^ (1 + q_box) := by
      have h5 : δ / (δ ^ (-q_box)) = δ * (δ ^ (-q_box))⁻¹ := by ring
      rw [h5]
      have h6 : (δ ^ (-q_box))⁻¹ = δ ^ q_box := by
        have h61 : δ ^ (-q_box) = (δ ^ q_box)⁻¹ := Real.rpow_neg hδ_pos.le q_box
        rw [h61]
        field_simp [hδ_pos.ne'] <;> ring
      rw [h6]
      have h7 : δ * δ ^ q_box = δ ^ (1 + q_box) := by
        have h71 : δ ^ ((1 : ℝ) + q_box) = δ ^ (1 : ℝ) * δ ^ q_box := Real.rpow_add hδ_pos (1 : ℝ) q_box
        have h72 : δ ^ (1 : ℝ) = δ := by simp
        rw [h72] at h71
        exact h71.symm
      exact h7
    rw [h4] at h3
    exact h3
  -- Upper bound on log: log(1/x) ≤ (1+q_box) * log(1/δ)
  have h_log_bound : Real.log (1 / x) ≤ (1 + q_box) * Real.log (1 / δ) := by
    have h1 : 0 < 1 / x := by positivity
    have h2 : 0 < 1 / δ := by positivity
    have h3 : 1 / x ≤ 1 / (δ ^ (1 + q_box)) := by
      gcongr
      <;> linarith
    have h4 : Real.log (1 / x) ≤ Real.log (1 / (δ ^ (1 + q_box))) := Real.log_le_log h1 h3
    have h5 : 1 / (δ ^ (1 + q_box)) = (1 / δ) ^ (1 + q_box) := by
      have h51 : 1 / (δ ^ (1 + q_box)) = δ ^ (-(1 + q_box)) := by
        have h : (δ ^ (1 + q_box))⁻¹ = δ ^ (-(1 + q_box)) := by
          rw [← Real.rpow_neg hδ_pos.le] <;> ring
        simpa [one_div] using h
      have h52 : (1 / δ) ^ (1 + q_box) = δ ^ (-(1 + q_box)) := by
        have h_pos1 : 0 ≤ (1 : ℝ) / δ := by positivity
        have h_pos2 : 0 ≤ δ := by linarith
        have h : (1 / δ) ^ (1 + q_box) = 1 / (δ ^ (1 + q_box)) := by
          rw [Real.div_rpow] <;> norm_num <;> linarith
        rw [h]
        have h2 : 1 / (δ ^ (1 + q_box)) = δ ^ (-(1 + q_box)) := by
          have h3 : (δ ^ (1 + q_box))⁻¹ = δ ^ (-(1 + q_box)) := by
            rw [← Real.rpow_neg hδ_pos.le] <;> ring
          simpa [one_div] using h3
        exact h2
      rw [h51, h52]
    rw [h5] at h4
    have h6 : Real.log ((1 / δ) ^ (1 + q_box)) = (1 + q_box) * Real.log (1 / δ) := by
      rw [Real.log_rpow (by positivity)] <;> ring
    rw [h6] at h4
    exact h4
  -- Since both sides are nonnegative, square the bound
  have h_log2_bound : (Real.log (1 / x)) ^ 2 ≤ ((1 + q_box) * Real.log (1 / δ)) ^ 2 := by
    have h_log_nonneg : 0 ≤ Real.log (1 / x) := by
      have h_gt : 1 < 1 / x := by
        have h' : x < 1 := hx_lt_one
        have h'' : 0 < x := hx_pos
        exact one_lt_one_div h'' h'
      have h : 1 ≤ 1 / x := by linarith
      exact Real.log_nonneg h
    nlinarith
  -- Lower bound on x^(-α): x ≤ δ, so x^(-α) ≥ δ^(-α)
  have h_x_le_delta : x ≤ δ := by
    dsimp only [x]
    have h2 : 1 ≤ 4 * R := by linarith
    have h3 : δ / (4 * R) ≤ δ / 1 := by gcongr
    simpa using h3
  have h_rpow_bound : δ ^ (-α) ≤ x ^ (-α) := by
    have hα_pos' : 0 < α := hα_pos
    have h1 : x ^ α ≤ δ ^ α := Real.rpow_le_rpow (by positivity) h_x_le_delta (by linarith)
    have h2 : 0 < x ^ α := by positivity
    have h3 : 0 < δ ^ α := by positivity
    have h4 : (δ ^ α)⁻¹ ≤ (x ^ α)⁻¹ := by gcongr
    have h5 : δ ^ (-α) = (δ ^ α)⁻¹ := by
      rw [Real.rpow_neg hδ_pos.le] <;> ring
    have h6 : x ^ (-α) = (x ^ α)⁻¹ := by
      rw [Real.rpow_neg hx_pos.le] <;> ring
    rw [h5, h6]
    exact h4
  -- Main calculation
  have h_main : extractLogConstant κ0 * (Real.log (1 / x)) ^ 2 ≤
      extractLogConstant κ0 * ((1 + q_box) * Real.log (1 / δ)) ^ 2 := by
    have hC_pos : 0 ≤ extractLogConstant κ0 := by
      dsimp only [extractLogConstant] <;> positivity
    gcongr
  have h_outer' : extractLogConstant κ0 * (1 + q_box) ^ 2 * (Real.log (1 / δ)) ^ 2 ≤
      δ ^ (-α) := h_outer
  have h_eq : extractLogConstant κ0 * ((1 + q_box) * Real.log (1 / δ)) ^ 2 =
      extractLogConstant κ0 * (1 + q_box) ^ 2 * (Real.log (1 / δ)) ^ 2 := by ring
  calc
    extractLogConstant κ0 * (Real.log (1 / x)) ^ 2
      ≤ extractLogConstant κ0 * ((1 + q_box) * Real.log (1 / δ)) ^ 2 := h_main
    _ = extractLogConstant κ0 * (1 + q_box) ^ 2 * (Real.log (1 / δ)) ^ 2 := h_eq
    _ ≤ δ ^ (-α) := h_outer'
    _ ≤ x ^ (-α) := h_rpow_bound

/-! ## 3. Combined delivery lemma -/

/-- Combined numeric conditions for the endgame extraction step.

Given the V4 wire budget parameters and the outer δ-smallness hypothesis
`extractLogAbsorbHyp`, delivers both `h_energy_small` and `h_extract_small`
needed by the skeleton at lines 770-773.

Also delivers `h_gap_half`: the extraction gap bridge `(1+qBox)·q_norm < εnc/2`.
-/
lemma extraction_numeric_conditions
    {δ L_exp η_work ε κ0 p_projective τ rho_sel rho_sep εnc R : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hL_nonneg : 0 ≤ L_exp)
    (hη_work_pos : 0 < η_work)
    (hε_pos : 0 < ε)
    (hκ_pos : 0 < κ0)
    (hp_nonneg : 0 ≤ p_projective)
    (hτ_pos : 0 < τ)
    (hrho_sel_nonneg : 0 ≤ rho_sel)
    (hrho_sep_nonneg : 0 ≤ rho_sep)
    (hR_ge1 : 1 ≤ R)
    (h4R_le_qbox : 4 * R ≤ δ ^ (-(qBox η_work τ)))
    (h_qTotalV4_le_enc4 : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤ εnc / 4)
    (h_qbox_lt_one : qBox η_work τ < 1)
    (h_outer : extractLogAbsorbHyp δ εnc η_work τ κ0
        (qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep)) :
    let q_norm_energy := qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep
    let q_box := qBox η_work τ
    ( (δ / (4 * R)) ^ (qEnergy η_work τ κ0) ≤ 1 / (4 * R) ^ (2 * κ0) ) ∧
    ( extractLogConstant κ0 * (Real.log (1 / (δ / (4 * R)))) ^ 2 ≤
        (δ / (4 * R)) ^ (-((εnc / 2) / (1 + q_box) - q_norm_energy)) ) ∧
    ( (1 + q_box) * q_norm_energy < εnc / 2 ) := by
  set q_norm_energy : ℝ := qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep with hq_norm_def
  set q_box : ℝ := qBox η_work τ with hq_box_def
  have hqBox_nonneg : 0 ≤ q_box := by
    dsimp only [q_box, qBox, qAbsorb] <;> positivity
  have h_norm_pos : 0 < q_norm_energy := by
    dsimp only [q_norm_energy, qNormEnergyV3, qCoordEnergyV3, rhoExc,
      qKaufBase, qPlan, qKaufman, qEnergy, qBox, qAbsorb] <;> positivity
  have h_gap_half : (1 + q_box) * q_norm_energy < εnc / 2 :=
    extraction_gap_bridge_enc2 hL_nonneg hη_work_pos hε_pos hκ_pos hp_nonneg
      hτ_pos hrho_sel_nonneg hrho_sep_nonneg h_qTotalV4_le_enc4 h_qbox_lt_one h_norm_pos
  have h_energy_small : (δ / (4 * R)) ^ (qEnergy η_work τ κ0) ≤ 1 / (4 * R) ^ (2 * κ0) :=
    energy_small_from_qbox hδ_pos hδ_lt_one hη_work_pos hτ_pos hκ_pos hR_ge1 h4R_le_qbox
  have h_extract_small : extractLogConstant κ0 * (Real.log (1 / (δ / (4 * R)))) ^ 2 ≤
      (δ / (4 * R)) ^ (-((εnc / 2) / (1 + q_box) - q_norm_energy)) :=
    extract_small_from_log_absorb hδ_pos hδ_lt_one hκ_pos hR_ge1 h4R_le_qbox
      hqBox_nonneg h_gap_half h_outer
  exact ⟨h_energy_small, h_extract_small, h_gap_half⟩

/-- There exists `δ0 > 0` such that `extractLogAbsorbHyp` holds for all `0 < δ ≤ δ0`.

The constant is `C = extractLogConstant κ0 * (1 + qBox η τ)^2` and the
exponent is `α = (εnc/2)/(1 + qBox η τ) - q_norm_energy > 0` (from the gap
condition). Apply `log_pow_const_le_rpow`. -/
lemma exists_extract_log_absorb
    (εnc η τ κ0 q_norm_energy : ℝ)
    (hη_pos : 0 < η)
    (hτ_pos : 0 < τ)
    (hκ_pos : 0 < κ0)
    (hq_norm_nonneg : 0 ≤ q_norm_energy)
    (h_gap : (1 + qBox η τ) * q_norm_energy < εnc / 2) :
    ∃ (δ0 : ℝ), 0 < δ0 ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ δ0 →
      extractLogAbsorbHyp δ εnc η τ κ0 q_norm_energy := by
  let q_box : ℝ := qBox η τ
  let α : ℝ := (εnc / 2) / (1 + q_box) - q_norm_energy
  have hq_box_nonneg : 0 ≤ q_box := by
    dsimp only [q_box, qBox, qAbsorb] <;> positivity
  have h1_pos : 0 < 1 + q_box := by linarith
  have hα_pos : 0 < α := by
    dsimp only [α]
    have h : (1 + q_box) * q_norm_energy < εnc / 2 := h_gap
    have h2 : q_norm_energy < (εnc / 2) / (1 + q_box) := by
      have h4 : 0 < 1 + q_box := h1_pos
      calc
        q_norm_energy
          = ((1 + q_box) * q_norm_energy) / (1 + q_box) := by field_simp [h4.ne'] <;> ring
        _ < (εnc / 2) / (1 + q_box) := by gcongr
    linarith
  let C : ℝ := extractLogConstant κ0 * (1 + q_box) ^ 2
  have hC_pos : 0 < C := by
    dsimp only [C, extractLogConstant] <;> positivity
  rcases log_pow_const_le_rpow hC_pos hα_pos with ⟨δ0, hδ0_pos, h_main⟩
  refine ⟨δ0, hδ0_pos, ?_⟩
  intro δ hδ_pos hδ_le
  have h9 : C * (Real.log (1 / δ)) ^ 2 ≤ δ ^ (-α) := h_main δ hδ_pos hδ_le
  simpa [extractLogAbsorbHyp, q_box, α, C] using h9

end ProductLikeIncidence.ProductReduction

end
