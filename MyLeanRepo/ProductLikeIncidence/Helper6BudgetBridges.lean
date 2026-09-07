module

/-
# Helper6 Budget Bridges

Discharges the three budget hypotheses required by `glue_H5_to_H6`:

1. `h_budget`: `εgain > q_graph_total + 2*q_diff + q_size + η + ζ_dir + η_proj`
2. `h_proj_budget`: `(L_exp - 1/2)*η < ζ_dir + η_proj`
3. `h_frostman_budget`: `C_ν * 8 * δ^(-ε_mass) * L_chart^τ ≤ K_work * δ^(-εnc)`

## Proof routes

### h_budget
From `εgain > qTotalV4` and the identity:
`qTotalV4 = qInitV3 + 2*ρ_sep + qGraphV4 + qAbsorb + 2*qDiffV4 + qSizeLossV4 + η_work + ζDir + ηProj + qNormEnergyV3`
Since all extra terms are non-negative and `η = η_work/2 < η_work`, we get
`qTotalV4 ≥ qGraphV4 + 2*qDiffV4 + qSizeLossV4 + η + ζDir + ηProj`.

### h_proj_budget
Trivial from definitions:
`ζDir + ηProj = qProjective + (L_exp*η + qProjective) = L_exp*η + 2*qProjective`
So `(L_exp - 1/2)*η < L_exp*η + 2*qProjective` since `-η/2 < 2*qProjective`.

### h_frostman_budget
Two variants:
- `helper6_frostman_budget_bridge`: simple variant via `frostman_budget_edir`, requires `ε_mass ≤ 3*η`
- `helper6_frostman_budget_bridge_v4`: generalized V4 variant, accepts the actual
  `ε_mass = 3*η_work/2 + η_work/100 > 3*η`, using V4 budget slack and box bound.

## Whiteprint node
Helper for V4 threshold wiring in `incidence_to_ring_contradiction`.
-/

public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV4
public import MyLeanRepo.ProductLikeIncidence.Phase7Budgets
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Real

namespace ProductLikeIncidence.ProductReduction

/-! ## 1. General budget condition -/

/-- **h_budget bridge**: From `εgain > qTotalV4`, derive
`εgain > qGraphV4 + 2*qDiffV4 + qSizeLossV4 + η + ζDir + ηProj`.

Uses the fact that `qTotalV4` contains additional non-negative terms beyond
the budget RHS, and `η < η_work`. -/
lemma helper6_budget_bridge
    {L_exp η_work ε κ0 p_projective τ rho_sel rho_sep η εgain : ℝ}
    (hL_nonneg : 0 ≤ L_exp)
    (hη_work_pos : 0 < η_work)
    (hη_pos : 0 < η)
    (hη_work_eq_two : η_work = 2 * η)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_pos : 0 < p_projective)
    (hτ_pos : 0 < τ)
    (hrho_sel_nonneg : 0 ≤ rho_sel)
    (hrho_sep_nonneg : 0 ≤ rho_sep)
    (h_εgain_gt_total : εgain > qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep) :
    εgain > qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep
      + 2 * qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
      + qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
      + η + ζDir p_projective ε κ0 + ηProj L_exp η ε κ0 p_projective := by
  have h1 : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≥
      qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep
      + 2 * qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
      + qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
      + η + ζDir p_projective ε κ0 + ηProj L_exp η ε κ0 p_projective := by
    have h_def : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep =
        qInitV3 η_work rho_sel + 2 * rho_sep
        + qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep
        + qAbsorb η_work
        + 2 * qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
        + qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
        + η_work + ζDir p_projective ε κ0
        + ηProj L_exp η_work ε κ0 p_projective
        + qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by
      rfl
    rw [h_def]
    have h2 : η ≤ η_work := by linarith
    have h3 : 0 ≤ qInitV3 η_work rho_sel := by dsimp only [qInitV3]; positivity
    have h4 : 0 ≤ 2 * rho_sep := by positivity
    have h5 : 0 ≤ qAbsorb η_work := by dsimp only [qAbsorb]; positivity
    have h6 : 0 ≤ qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by
      dsimp only [qNormEnergyV3, qCoordEnergyV3, rhoExc, qKaufBase,
        qPlan, qKaufman, qEnergy, qBox, qAbsorb]; positivity
    have h7 : 0 ≤ η_work - η := by linarith
    have h8 : ηProj L_exp η_work ε κ0 p_projective ≥ ηProj L_exp η ε κ0 p_projective := by
      dsimp only [ηProj, qProjective]
      have h9 : 0 ≤ L_exp * (η_work - η) := by positivity
      linarith
    linarith
  exact lt_of_le_of_lt h1 h_εgain_gt_total

/-! ## 2. Projection budget condition -/

/-- **h_proj_budget bridge**: Prove
`(L_exp - 1/2)*η < ζDir + ηProj` from positivity of `qProjective`.

Since `ζDir + ηProj = L_exp*η + 2*qProjective`, the inequality reduces to
`-η/2 < 2*qProjective`, which holds since `η > 0` and `qProjective > 0`. -/
lemma helper6_proj_budget_bridge
    {L_exp η ε κ0 p_projective : ℝ}
    (hη_pos : 0 < η)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_pos : 0 < p_projective) :
    (L_exp - 1 / 2 : ℝ) * η < ζDir p_projective ε κ0 + ηProj L_exp η ε κ0 p_projective := by
  have h1 : ζDir p_projective ε κ0 + ηProj L_exp η ε κ0 p_projective =
      L_exp * η + 2 * qProjective p_projective ε κ0 := by
    simp only [ζDir, ηProj, qProjective] <;> ring
  rw [h1]
  have h2 : 0 < 2 * qProjective p_projective ε κ0 := by
    simp only [qProjective] <;> positivity
  linarith

/-! ## 3. Frostman budget condition -/

/-- **h_frostman_budget bridge**: Derive the Frostman transport budget
`C_ν * 8 * δ^(-ε_mass) * L_chart^τ ≤ K_work * δ^(-εnc)`
from `frostman_budget_edir` with `ε_dir := ε_mass`.

Requires:
- `ε_mass ≤ 3*η`
- `C_Y ≤ δ^{-η}` and `C_ν ≤ 3*C_Y*2^τ`
- `εnc > 4*η`
- `δ^(εnc - 4*η) ≤ K_work / (24*2^τ*L_chart^τ)` -/
lemma helper6_frostman_budget_bridge
    {δ τ η εnc ε_mass C_Y C_ν L_chart K_work : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hη_pos : 0 < η)
    (hτ_pos : 0 < τ)
    (hε_mass_pos : 0 < ε_mass)
    (hε_mass_le_3η : ε_mass ≤ 3 * η)
    (hC_Y_le : C_Y ≤ δ ^ (-η))
    (hC_ν_pos : 0 < C_ν)
    (hC_ν_le : C_ν ≤ 3 * C_Y * (2 : ℝ) ^ τ)
    (hL_chart_ge_one : 1 ≤ L_chart)
    (hK_work_pos : 0 < K_work)
    (henc_gt_4eta : εnc > 4 * η)
    (hδ_small : δ ^ (εnc - 4 * η) ≤ K_work / (24 * (2 : ℝ) ^ τ * L_chart ^ τ)) :
    C_ν * (8 : ℝ) * δ ^ (-ε_mass) * L_chart ^ τ ≤ K_work * δ ^ (-εnc) :=
  frostman_budget_edir
    (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
    (hη_pos := hη_pos) (hτ_pos := hτ_pos)
    (h_edir_pos := hε_mass_pos) (h_edir_le_3eta := hε_mass_le_3η)
    (C_Y := C_Y) (hC_Y_le := hC_Y_le)
    (C_ν := C_ν) (hC_ν_pos := hC_ν_pos) (hC_ν_le := hC_ν_le)
    (L_chart := L_chart) (K_work := K_work)
    (hL_chart_ge_one := hL_chart_ge_one) (hK_work_pos := hK_work_pos)
    (henc_gt_4eta := henc_gt_4eta) (hδ_small := hδ_small)

/-- **Generalized V4 Frostman budget bridge**: Handles the actual V4 mass exponent
`ε_mass = 3*η_work/2 + η_work/100 > 3*η`, which exceeds the simple
`frostman_budget_edir` bound.

Uses V4 budget slack: `εnc/4 ≥ qTotalV4 ≥ 160*qKV4 ≥ 160*(9*η_work + qProjective)`,
so `εnc ≥ 5760*η_work + 640*qProjective`. Also `qKV4 ≥ 2*rho_sep`, so
`εnc ≥ 1280*rho_sep`, giving `2*tau*rho_sep ≤ 2*rho_sep ≤ εnc/640`.

The exponent gap `εnc - η - ε_mass - 2*τ*rho_sep` is at least `η_work/100`,
which the box bound absorbs. Since `τ ≤ 1`, `24*2^τ ≤ 48`, and
`48*δ^(η_work/100) ≤ 1 ≤ K_work`. -/
lemma helper6_frostman_budget_bridge_v4
    {δ τ η η_work ε εnc ε_mass C_Y C_ν L_chart K_work : ℝ}
    {L_exp p_projective κ0 rho_sel rho_sep : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hη_pos : 0 < η)
    (hη_work_pos : 0 < η_work)
    (hη_work_eq_two : η_work = 2 * η)
    (hτ_pos : 0 < τ)
    (hτ_le_one : τ ≤ 1)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_nonneg : 0 ≤ p_projective)
    (hL_exp_eq_seven : L_exp = 7)
    (hrho_sel_nonneg : 0 ≤ rho_sel)
    (hrho_sep_nonneg : 0 ≤ rho_sep)
    (hε_mass_eq : ε_mass = 3 * η_work / 2 + η_work / 100)
    (hC_Y_le : C_Y ≤ δ ^ (-η))
    (hC_ν_pos : 0 < C_ν)
    (hC_ν_le : C_ν ≤ 3 * C_Y * (2 : ℝ) ^ τ)
    (hL_chart_eq : L_chart = δ ^ (-2 * rho_sep))
    (hK_work_ge1 : 1 ≤ K_work)
    (h_qTotalV4_le_enc4 : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤ εnc / 4)
    (h_box_bound : (2 : ℝ) ^ 20 ≤ δ ^ (-(η_work / 100))) :
    C_ν * (8 : ℝ) * δ ^ (-ε_mass) * L_chart ^ τ ≤ K_work * δ ^ (-εnc) := by
  have hη_eq : η = η_work / 2 := by linarith
  have hqP_nonneg : 0 ≤ qProjective p_projective ε κ0 := by
    simp only [qProjective]; positivity
  have hqKV4_ge : qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep ≥
      9 * η_work + qProjective p_projective ε κ0 := by
    dsimp only [qKV4, qK, qDensityV4, qProjective]
    have h1 : 0 ≤ 3 * rho_sel := by positivity
    have h2 : 0 ≤ 2 * rho_sep := by positivity
    have h3 : 0 ≤ qAbsorb η_work := by dsimp only [qAbsorb]; positivity
    rw [hL_exp_eq_seven]; linarith
  have hqKV4_ge_rhosep : qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep ≥ 2 * rho_sep := by
    dsimp only [qKV4, qK, qDensityV4]
    have h1 : 0 ≤ (L_exp + 2) * η_work := by
      rw [hL_exp_eq_seven]; positivity
    have h2 : 0 ≤ qProjective p_projective ε κ0 := hqP_nonneg
    have h3 : 0 ≤ 3 * rho_sel := by positivity
    have h4 : 0 ≤ qAbsorb η_work := by dsimp only [qAbsorb]; positivity
    linarith
  have hqKAV4_nonneg : 0 ≤ qKAV4 L_exp η_work rho_sel rho_sep := by
    dsimp only [qKAV4, alphaProjectionV4, qMassV4, qAbsorb]
    have h1 : 0 ≤ L_exp * η_work := by positivity
    have h2 : 0 ≤ 2 * rho_sep := by positivity
    have h3 : 0 ≤ 3 * rho_sel := by positivity
    have h4 : 0 ≤ qAbsorb η_work := by dsimp only [qAbsorb]; positivity
    linarith
  have hqKV4_nonneg : 0 ≤ qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by
    dsimp only [qKV4, qK, qDensityV4, qProjective]
    have h1 : 0 ≤ (L_exp + 2) * η_work := by positivity
    have h2 : 0 ≤ p_projective * ε / κ0 := by positivity
    have h3 : 0 ≤ 3 * rho_sel := by positivity
    have h4 : 0 ≤ 2 * rho_sep := by positivity
    have h5 : 0 ≤ qAbsorb η_work := by dsimp only [qAbsorb]; positivity
    linarith
  have hqGraphV4_nonneg : 0 ≤ qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by
    dsimp only [qGraphV4]
    have h1 : 0 ≤ 22 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by positivity
    have h2 : 0 ≤ η_work / 2 + η_work / 20 := by positivity
    linarith
  have hqBox_nonneg : 0 ≤ qBox η_work τ := by
    dsimp only [qBox, qAbsorb]; positivity
  have hqNormChunkV4_nonneg : 0 ≤ qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
    dsimp only [qNormChunkV4]
    have h1 : 0 ≤ qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := hqGraphV4_nonneg
    have h2 : 0 ≤ qBox η_work τ := hqBox_nonneg
    have h3 : 0 ≤ qAbsorb η_work := by dsimp only [qAbsorb]; positivity
    linarith
  have hqDiff_ge : qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≥
      80 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by
    dsimp only [qDiffV4]
    have h1 : 0 ≤ 2 * qKAV4 L_exp η_work rho_sel rho_sep := by positivity
    have h2 : 0 ≤ qAbsorb η_work := by dsimp only [qAbsorb]; positivity
    have h3 : 0 ≤ qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := hqNormChunkV4_nonneg
    linarith
  have hqEffV4_nonneg : 0 ≤ qEffV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by
    dsimp only [qEffV4]; positivity
  have hqInputV4_nonneg : 0 ≤ qInputV4 L_exp η_work rho_sel rho_sep := by
    dsimp only [qInputV4, qFixedCoordinate, qAbsorb]
    have h1 : 0 ≤ (L_exp / 2 + 21 / 4) * η_work := by positivity
    have h2 : 0 ≤ 2 * rho_sep := by positivity
    have h3 : 0 ≤ 3 * qAbsorb η_work := by dsimp only [qAbsorb]; positivity
    have h4 : 0 ≤ (3 * rho_sel) / 2 := by positivity
    linarith
  have hqSizeLossV4_nonneg : 0 ≤ qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
    dsimp only [qSizeLossV4]
    have h1 : 0 ≤ qEffV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := hqEffV4_nonneg
    have h2 : 0 ≤ qInputV4 L_exp η_work rho_sel rho_sep := hqInputV4_nonneg
    have h3 : 0 ≤ qAbsorb η_work := by dsimp only [qAbsorb]; positivity
    have h4 : 0 ≤ qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := hqNormChunkV4_nonneg
    linarith
  have hqNormEnergyV3_nonneg : 0 ≤ qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by
    dsimp only [qNormEnergyV3, qCoordEnergyV3, rhoExc, qKaufBase,
      qPlan, qKaufman, qEnergy, qBox, qAbsorb]
    positivity
  have hqTotal_ge : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≥
      160 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by
    have h1 : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≥
        2 * qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
      dsimp only [qTotalV4]
      have h2 : 0 ≤ qInitV3 η_work rho_sel := by dsimp only [qInitV3, qInit, qAbsorb]; positivity
      have h3 : 0 ≤ (2 : ℝ) * rho_sep := by positivity
      have h4 : 0 ≤ qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := hqGraphV4_nonneg
      have h5 : 0 ≤ qAbsorb η_work := by dsimp only [qAbsorb]; positivity
      have h6 : 0 ≤ qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := hqSizeLossV4_nonneg
      have h7 : 0 ≤ η_work := by linarith [hη_work_pos]
      have h8 : 0 ≤ ζDir p_projective ε κ0 := by dsimp only [ζDir]; positivity
      have h9 : 0 ≤ ηProj L_exp η_work ε κ0 p_projective := by dsimp only [ηProj]; positivity
      have h10 : 0 ≤ qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep := hqNormEnergyV3_nonneg
      linarith
    linarith [hqDiff_ge]
  have h_enc_budget : εnc ≥ 5760 * η_work + 640 * (qProjective p_projective ε κ0) := by
    have h1 : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≥
        1440 * η_work + 160 * (qProjective p_projective ε κ0) := by
      calc qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
        ≥ 160 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := hqTotal_ge
      _ ≥ 160 * (9 * η_work + qProjective p_projective ε κ0) := by gcongr
      _ = 1440 * η_work + 160 * (qProjective p_projective ε κ0) := by ring
    have h2 : εnc / 4 ≥ qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := h_qTotalV4_le_enc4
    linarith
  have h_enc_ge_5760 : εnc ≥ 5760 * η_work := by
    have h3 : 0 ≤ 640 * (qProjective p_projective ε κ0) := by positivity
    linarith [h_enc_budget]
  have h_enc_ge_rhosep : εnc ≥ 1280 * rho_sep := by
    have h1 : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≥ 320 * rho_sep := by
      calc qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
        ≥ 160 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := hqTotal_ge
      _ ≥ 160 * (2 * rho_sep) := by gcongr
      _ = 320 * rho_sep := by ring
    have h2 : εnc / 4 ≥ qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := h_qTotalV4_le_enc4
    linarith
  have h_rhosep_bound : 2 * rho_sep ≤ εnc / 640 := by linarith [h_enc_ge_rhosep]
  set gap : ℝ := εnc - η - ε_mass - 2 * τ * rho_sep with hgap_def
  have h_gap_ge : gap ≥ η_work / 100 := by
    rw [hgap_def, hε_mass_eq, hη_eq]
    have h1 : 2 * τ * rho_sep ≤ 2 * rho_sep := by
      have h2 : τ ≤ 1 := hτ_le_one
      have h3 : 0 ≤ rho_sep := hrho_sep_nonneg
      nlinarith
    have h4 : 2 * rho_sep ≤ εnc / 640 := h_rhosep_bound
    nlinarith [h_enc_ge_5760]
  have hL_chart_pos : 0 < L_chart := by
    rw [hL_chart_eq]; positivity
  have h_pos1 : 0 ≤ (8 : ℝ) * δ ^ (-ε_mass) * L_chart ^ τ := by positivity
  have h_pos2 : 0 ≤ (3 : ℝ) * (2 : ℝ) ^ τ := by positivity
  have hCY : C_Y * ((8 : ℝ) * δ ^ (-ε_mass) * L_chart ^ τ) ≤
      (δ ^ (-η)) * ((8 : ℝ) * δ ^ (-ε_mass) * L_chart ^ τ) :=
    mul_le_mul_of_nonneg_right hC_Y_le h_pos1
  have hL_exp : L_chart ^ τ = δ ^ (-2 * τ * rho_sep) := by
    rw [hL_chart_eq]
    have h : (δ ^ (-2 * rho_sep)) ^ τ = δ ^ ((-2 * rho_sep) * τ) := by
      rw [← Real.rpow_mul hδ_pos.le (-2 * rho_sep) τ]
    rw [h]
    have h2 : (-2 * rho_sep) * τ = -2 * τ * rho_sep := by ring
    rw [h2]
  have h_eq1 : δ ^ (-η) * δ ^ (-ε_mass) = δ ^ (-η - ε_mass) := by
    rw [← Real.rpow_add hδ_pos] <;> ring_nf
  have h_eq : δ ^ (-η) * δ ^ (-ε_mass) * δ ^ (-2 * τ * rho_sep) =
      δ ^ (-η - ε_mass - 2 * τ * rho_sep) := by
    rw [h_eq1]
    rw [← Real.rpow_add hδ_pos] <;> ring_nf
  have h1 : C_ν * (8 : ℝ) * δ ^ (-ε_mass) * L_chart ^ τ ≤
      (24 : ℝ) * (2 : ℝ) ^ τ * δ ^ (-η - ε_mass - 2 * τ * rho_sep) := by
    calc C_ν * (8 : ℝ) * δ ^ (-ε_mass) * L_chart ^ τ
      = C_ν * ((8 : ℝ) * δ ^ (-ε_mass) * L_chart ^ τ) := by ring
    _ ≤ (3 * C_Y * (2 : ℝ) ^ τ) * ((8 : ℝ) * δ ^ (-ε_mass) * L_chart ^ τ) :=
      mul_le_mul_of_nonneg_right hC_ν_le h_pos1
    _ = (3 * (2 : ℝ) ^ τ) * (C_Y * ((8 : ℝ) * δ ^ (-ε_mass) * L_chart ^ τ)) := by ring
    _ ≤ (3 * (2 : ℝ) ^ τ) * ((δ ^ (-η)) * ((8 : ℝ) * δ ^ (-ε_mass) * L_chart ^ τ)) :=
      mul_le_mul_of_nonneg_left hCY h_pos2
    _ = (24 : ℝ) * (2 : ℝ) ^ τ * (δ ^ (-η) * δ ^ (-ε_mass) * L_chart ^ τ) := by ring
    _ = (24 : ℝ) * (2 : ℝ) ^ τ * (δ ^ (-η) * δ ^ (-ε_mass) * δ ^ (-2 * τ * rho_sep)) := by
      rw [hL_exp]
    _ = (24 : ℝ) * (2 : ℝ) ^ τ * δ ^ (-η - ε_mass - 2 * τ * rho_sep) := by
      rw [h_eq]
  have h2 : (24 : ℝ) * (2 : ℝ) ^ τ ≤ 48 := by
    have h3 : (2 : ℝ) ^ τ ≤ 2 := by
      have h4 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
      have h5 : τ ≤ (1 : ℝ) := hτ_le_one
      have h6 : (2 : ℝ) ^ τ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h4 h5
      simpa using h6
    calc (24 : ℝ) * (2 : ℝ) ^ τ
      ≤ (24 : ℝ) * (2 : ℝ) := by gcongr
    _ = 48 := by norm_num
  have h3 : δ ^ gap ≤ 1 / (48 : ℝ) := by
    have h4 : δ ^ gap ≤ δ ^ (η_work / 100) :=
      Real.rpow_le_rpow_of_exponent_ge hδ_pos (by linarith) h_gap_ge
    have h5 : δ ^ (η_work / 100) ≤ 1 / (2 ^ 20 : ℝ) := by
      have h6 : 0 < δ ^ (η_work / 100) := by positivity
      have h7 : δ ^ (-(η_work / 100)) = 1 / δ ^ (η_work / 100) := by
        rw [Real.rpow_neg hδ_pos.le] <;> ring
      have h8 : (2 ^ 20 : ℝ) ≤ δ ^ (-(η_work / 100)) := h_box_bound
      rw [h7] at h8
      have h9 : δ ^ (η_work / 100) ≤ 1 / (2 ^ 20 : ℝ) := by
        have h10 : 0 < δ ^ (η_work / 100) := h6
        have h11 : (2 ^ 20 : ℝ) ≤ 1 / δ ^ (η_work / 100) := h8
        calc δ ^ (η_work / 100)
          = 1 / (1 / δ ^ (η_work / 100)) := by field_simp [h10.ne'] <;> ring
        _ ≤ 1 / (2 ^ 20 : ℝ) := by gcongr
      exact h9
    have h9 : (1 : ℝ) / (2 ^ 20 : ℝ) ≤ 1 / (48 : ℝ) := by norm_num
    exact le_trans (le_trans h4 h5) h9
  have h4 : (24 : ℝ) * (2 : ℝ) ^ τ * δ ^ (-η - ε_mass - 2 * τ * rho_sep) ≤
      K_work * δ ^ (-εnc) := by
    have h5 : -η - ε_mass - 2 * τ * rho_sep = -εnc + gap := by
      rw [hgap_def] <;> ring
    rw [h5]
    have h6 : δ ^ (-εnc + gap) = δ ^ (-εnc) * δ ^ gap := by
      rw [← Real.rpow_add hδ_pos] <;> ring
    rw [h6]
    have h7 : (24 : ℝ) * (2 : ℝ) ^ τ * δ ^ gap ≤ 48 * δ ^ gap := by gcongr
    have h8 : 48 * δ ^ gap ≤ K_work := by
      have h9 : 48 * δ ^ gap ≤ 48 * (1 / (48 : ℝ)) := by gcongr
      have h10 : 48 * (1 / (48 : ℝ)) = 1 := by norm_num
      have h11 : 1 ≤ K_work := hK_work_ge1
      linarith
    have h12 : 0 ≤ δ ^ (-εnc) := by positivity
    calc (24 : ℝ) * (2 : ℝ) ^ τ * (δ ^ (-εnc) * δ ^ gap)
      = δ ^ (-εnc) * ((24 : ℝ) * (2 : ℝ) ^ τ * δ ^ gap) := by ring
    _ ≤ δ ^ (-εnc) * (48 * δ ^ gap) := by gcongr
    _ ≤ δ ^ (-εnc) * K_work := by gcongr
    _ = K_work * δ ^ (-εnc) := by ring
  exact le_trans h1 h4

end ProductLikeIncidence.ProductReduction
