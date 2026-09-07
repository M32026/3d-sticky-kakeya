module

/-
# Helper6 Absorption Bridges

Four standalone lemmas discharging the quantitative absorption hypotheses
required by `glue_h5_to_h6`.

## Bridges

1. `bridge_size_absorb` — size lower bound absorption
2. `bridge_reg_absorb` — delta-set regularity absorption
3. `bridge_graph_absorb` — graph density constant absorption
4. `bridge_sector_absorb` — sector translation constant absorption

Each lemma takes the V4 budget parameters and upstream constants as explicit
hypotheses and proves the exact condition required by `glue_h5_to_h6`.

## Integration with Dune's glue

Call each bridge with the corresponding variables from the glue context.
See docstrings for exact argument mappings.

## Whiteprint node
Helper for corrected H5→H6 absorption conditions.
-/

public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV4
public import MyLeanRepo.ProductLikeIncidence.V4NumericFills
public import MyLeanRepo.ProductLikeIncidence.V4BridgeHypotheses
public import MyLeanRepo.ProductLikeIncidence.Helper5AbsorptionCalibration
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Real ENNReal

namespace ProductLikeIncidence.ProductReduction

/-! ## 1. Size absorption -/

/-- **Size absorption bridge (V4-correct, qKV4 retention)**:
`c_ret / M_ret * δ^(-s + qInputV4) ≥ δ^(-s + qSizeLossV4)`.

Uses the actual Helper5 retention exponent `e = 32*qKV4 + qBox`.
Since glue uses `q_K := qKV4` (not base `qK`), the retention ratio carries
the full `qKV4` exponent, not just `qK`.

The gap identity is:
`qSizeLossV4 - qInputV4 - (32*qKV4 + qBox) = 2*qAbsorb + η_work/2 + η_work/20`

This gap is strictly positive and dominates `qAbsorb`, so the threshold
`δ^qAbsorb ≤ 1/C` absorbs the constant.

**Integration**: Pass the BSG retention ratio
`c_ret / M_ret ≥ δ^(32*qKV4 + qBox) / C` and the KBSG smallness threshold
`δ^qAbsorb ≤ 1/C`. -/
lemma bridge_size_absorb
    {δ s C c_ret M_ret : ℝ}
    {L_exp η_work ε κ0 p_projective τ rho_sel rho_sep : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hC_pos : 0 < C)
    (hL_nonneg : 0 ≤ L_exp)
    (hη_work_pos : 0 < η_work)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_nonneg : 0 ≤ p_projective)
    (hτ_pos : 0 < τ)
    (hrho_sel_nonneg : 0 ≤ rho_sel)
    (hrho_sep_nonneg : 0 ≤ rho_sep)
    (h_retention : c_ret / M_ret ≥
        δ^(32 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep + qBox η_work τ) / C)
    (h_qAbsorb_threshold : δ^(qAbsorb η_work) ≤ 1 / C) :
    c_ret / M_ret * δ^(-s + qInputV4 L_exp η_work rho_sel rho_sep) ≥
      δ^(-s + qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep) := by
  set e : ℝ := 32 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep + qBox η_work τ with he_def
  set q_input : ℝ := qInputV4 L_exp η_work rho_sel rho_sep with hq_input_def
  set q_size : ℝ := qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep with hq_size_def
  set gap : ℝ := q_size - q_input - e with hgap_def
  have hgap_eq : gap = 2 * qAbsorb η_work + η_work / 2 + η_work / 20 := by
    simp only [hgap_def, hq_size_def, hq_input_def, he_def]
    dsimp only [qSizeLossV4, qEffV4, qInputV4, qNormChunkV4, qGraphV4, qKV4, qDensityV4, qK, qBox, qAbsorb]
    <;> ring
  have he_pos : 0 < e := by
    rw [he_def]
    have h1 : 0 < qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by
      dsimp only [qKV4, qK, qDensityV4, qProjective, qAbsorb]
      have h11 : 0 < (L_exp + 2) * η_work := by positivity
      have h12 : 0 ≤ p_projective * ε / κ0 := by positivity
      have h13 : 0 ≤ 3 * rho_sel := by positivity
      have h14 : 0 ≤ 2 * rho_sep := by positivity
      have h15 : 0 < qAbsorb η_work := by dsimp only [qAbsorb]; positivity
      linarith
    have h2 : 0 ≤ qBox η_work τ := by dsimp only [qBox, qAbsorb]; positivity
    linarith
  have hgap_pos : 0 < gap := by
    rw [hgap_eq]
    have h2 : 0 < qAbsorb η_work := by dsimp only [qAbsorb]; positivity
    have h3 : 0 < η_work / 2 + η_work / 20 := by positivity
    linarith
  have hgap_ge_qAbsorb : qAbsorb η_work ≤ gap := by
    rw [hgap_eq]
    have h2 : 0 ≤ η_work / 2 + η_work / 20 := by positivity
    linarith
  have h_threshold : δ^gap ≤ 1 / C := by
    have h1 : gap ≥ qAbsorb η_work := hgap_ge_qAbsorb
    have h2 : δ^gap ≤ δ^(qAbsorb η_work) :=
      Real.rpow_le_rpow_of_exponent_ge hδ_pos (by linarith) h1
    exact le_trans h2 h_qAbsorb_threshold
  have hgap_eq' : q_size - q_input - e = gap := by
    simp [hgap_def]
  exact size_absorption_with_retention_exponent
    hδ_pos hδ_lt_one hC_pos he_pos hgap_pos hgap_eq' h_retention h_threshold

/-! ## 2. Regularity absorption -/

/-- **Regularity absorption bridge**: `2 * (C_BSG * R_ret) ≤ K_work * δ^(-εnc)`.

Wraps `v4_regularity_absorption` from `V4BridgeHypotheses`.

**Integration**: The threshold `δ^εnc ≤ K_work / (2 * C_BSG * R_ret)` follows
from the V4 budget smallness conditions (`h_small_bsg` or equivalent). -/
lemma bridge_reg_absorb
    {δ εnc C_BSG R_ret K_work : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hC_BSG_pos : 0 < C_BSG)
    (hR_ret_pos : 0 < R_ret)
    (hK_work_pos : 0 < K_work)
    (hεnc_pos : 0 < εnc)
    (h_threshold : δ ^ εnc ≤ K_work / (2 * C_BSG * R_ret)) :
    2 * (C_BSG * R_ret) ≤ K_work * δ ^ (-εnc) :=
  v4_regularity_absorption hδ_pos hδ_lt_one hC_BSG_pos hR_ret_pos
    hK_work_pos hεnc_pos h_threshold

/-! ## 3. Graph density absorption -/

/-- **Graph density absorption bridge**: `c_ret ≥ (2 / c_mult_dir) * c_proj`.

When `c_ret` and `c_proj` are calibrated to the same BSG density constant,
this is an equality. Specifically, if:
- `c_ret = δ^(22*q_K) / (16*3^22) / 4`
- `c_proj = (δ^(22*q_K) / (16*3^22)) * c_mult_dir / 8`

Then `(2/c_mult_dir) * c_proj = c_ret` exactly.

**Integration**: Pass the explicit definitions from Helper5 and the
popularity recalibration. If `c_proj` is only lower-bounded, use
`bridge_graph_absorb_lower` instead. -/
lemma bridge_graph_absorb
    {δ q_K c_mult_dir c_ret c_proj : ℝ}
    (hc_mult_dir_pos : 0 < c_mult_dir)
    (hc_ret_eq : c_ret = δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ)) / 4)
    (hc_proj_eq : c_proj = (δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ))) * c_mult_dir / 8) :
    c_ret ≥ (2 / c_mult_dir) * c_proj := by
  rw [hc_ret_eq, hc_proj_eq]
  have h : (2 / c_mult_dir) * ((δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ))) * c_mult_dir / 8) =
      δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ)) / 4 := by
    field_simp [hc_mult_dir_pos.ne']; ring
  exact h.le

/-- **Graph density absorption bridge (lower-bound version)**:

If `c_proj` is only known up to a lower bound, but `c_ret` is the full
popularity retention, use the explicit ratio.

Given `c_ret = D / 4` and `c_proj ≤ D * c_mult_dir / 8` where
`D = δ^(22*q_K)/(16*3^22)`, we get `(2/c_mult_dir)*c_proj ≤ D/4 = c_ret`. -/
lemma bridge_graph_absorb_lower
    {c_mult_dir c_ret c_proj D : ℝ}
    (hc_mult_dir_pos : 0 < c_mult_dir)
    (hD_pos : 0 < D)
    (hc_ret_eq : c_ret = D / 4)
    (hc_proj_le : c_proj ≤ D * c_mult_dir / 8) :
    c_ret ≥ (2 / c_mult_dir) * c_proj := by
  have h : (2 / c_mult_dir) * c_proj ≤ (2 / c_mult_dir) * (D * c_mult_dir / 8) := by
    gcongr
  have h2 : (2 / c_mult_dir) * (D * c_mult_dir / 8) = D / 4 := by
    field_simp [hc_mult_dir_pos.ne']; ring
  rw [h2] at h
  rw [hc_ret_eq]
  exact h

/-! ## 4. Sector translation absorption -/

/-- **Sector absorption bridge**: `C_ν * δ^τ ≤ δ^ε_mass / 2`.

Derivation from the monolith (lines 5426-5477):
1. `C_ν = 3 * C_Y * 2^τ`
2. `C_Y ≤ δ^(-η)` (from Phase0 budget)
3. So `C_ν * δ^τ ≤ 3 * 2^τ * δ^(τ - η)`
4. Need `ε_mass - τ + η ≤ -η_work` (from V4 budget: `4η_work < τ`, with `ε_mass = 3η_work/2 + η_work/100`)
5. Then `δ^(ε_mass - τ + η) ≥ δ^(-η_work) ≥ (2^20)^100 ≥ 6*2^τ`
6. So `3*2^τ * δ^(τ-η) ≤ δ^ε_mass / 2`

**Integration**: Pass the Phase0 `C_Y` bound, the V4 budget condition
`4η_work < τ`, and the KBSG box bound `δ^(-qAbsorb) ≥ 2^20`. -/
lemma bridge_sector_absorb
    {δ τ η η_work ε_mass C_Y C_ν : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hη_work_pos : 0 < η_work)
    (hη_work_eq_two : η_work = 2 * η)
    (hτ_le_one : τ ≤ 1)
    (h4η_work_lt_tau : 4 * η_work < τ)
    (hε_mass_def : ε_mass = 3 * η_work / 2 + η_work / 100)
    (hC_Y_le : C_Y ≤ δ ^ (-η))
    (hC_ν_eq : C_ν = 3 * C_Y * (2 : ℝ) ^ τ)
    (h_box_bound : (2 ^ 20 : ℝ) ≤ δ ^ (-(η_work / 100))) :
    C_ν * δ ^ τ ≤ δ ^ ε_mass / 2 := by
  have hδ_le_one : δ ≤ 1 := hδ_lt_one.le
  have hη_eq : η = η_work / 2 := by linarith
  have h1a : C_ν * δ ^ τ ≤ (3 * C_Y * (2 : ℝ) ^ τ) * δ ^ τ := by
    rw [hC_ν_eq]
  have h1b : (3 * C_Y * (2 : ℝ) ^ τ) * δ ^ τ ≤ 3 * (δ ^ (-η)) * (2 : ℝ) ^ τ * δ ^ τ := by
    gcongr
  have h1c : 3 * (δ ^ (-η)) * (2 : ℝ) ^ τ * δ ^ τ = 3 * (2 : ℝ) ^ τ * δ ^ (τ - η) := by
    have h_eq : δ ^ (-η) * δ ^ τ = δ ^ (τ - η) := by
      rw [← Real.rpow_add hδ_pos]; ring_nf
    have h_rearrange : 3 * (δ ^ (-η)) * (2 : ℝ) ^ τ * δ ^ τ = 3 * (2 : ℝ) ^ τ * (δ ^ (-η) * δ ^ τ) := by ring
    rw [h_rearrange, h_eq]
  have h1 : C_ν * δ ^ τ ≤ 3 * (2 : ℝ) ^ τ * δ ^ (τ - η) :=
    le_trans (le_trans h1a h1b) (le_of_eq h1c)
  have hE_bound : ε_mass - τ + η ≤ -η_work := by
    rw [hε_mass_def, hη_eq]
    linarith
  have h_pow100 : δ ^ (-η_work) = (δ ^ (-(η_work / 100))) ^ 100 := by
    have h61 : δ ^ (-η_work) = δ ^ (-(η_work / 100) * (100 : ℝ)) := by
      rw [show -(η_work / 100) * (100 : ℝ) = -η_work by ring]
    rw [h61]
    have h62 : δ ^ (-(η_work / 100) * (100 : ℝ)) = (δ ^ (-(η_work / 100))) ^ (100 : ℝ) := by
      rw [← Real.rpow_mul hδ_pos.le]
    rw [h62]
    norm_cast
  have h2 : δ ^ (ε_mass - τ + η) ≥ 6 * (2 : ℝ) ^ τ := by
    have h3 : δ ^ (ε_mass - τ + η) ≥ δ ^ (-η_work) :=
      Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one hE_bound
    have h4 : δ ^ (-η_work) ≥ (2 ^ 20 : ℝ) ^ 100 := by
      rw [h_pow100]
      have h7 : (2 ^ 20 : ℝ) ≤ δ ^ (-(η_work / 100)) := h_box_bound
      have h8 : (δ ^ (-(η_work / 100))) ^ 100 ≥ ((2 ^ 20 : ℝ)) ^ 100 := by gcongr
      exact h8
    have h9 : (2 ^ 20 : ℝ) ^ 100 ≥ 6 * (2 : ℝ) ^ τ := by
      have h10 : (2 : ℝ) ^ τ ≤ 2 := by
        have h11 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
        have h13 : (2 : ℝ) ^ τ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h11 hτ_le_one
        simpa using h13
      have h14 : 6 * (2 : ℝ) ^ τ ≤ 12 := by linarith
      have h15 : (2 ^ 20 : ℝ) ^ 100 ≥ 12 := by norm_num
      linarith
    linarith
  have h3 : 3 * (2 : ℝ) ^ τ * δ ^ (τ - η) ≤ δ ^ ε_mass / 2 := by
    have h4 : 6 * (2 : ℝ) ^ τ * δ ^ (τ - η) ≤ δ ^ (ε_mass - τ + η) * δ ^ (τ - η) := by
      gcongr
    have h5 : δ ^ (ε_mass - τ + η) * δ ^ (τ - η) = δ ^ ε_mass := by
      rw [← Real.rpow_add hδ_pos]; ring_nf
    have h6 : 6 * (2 : ℝ) ^ τ * δ ^ (τ - η) ≤ δ ^ ε_mass := by
      rw [h5] at h4
      exact h4
    linarith
  exact le_trans h1 h3

end ProductLikeIncidence.ProductReduction

end
