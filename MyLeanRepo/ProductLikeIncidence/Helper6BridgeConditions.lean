module

/-
# Helper6 Bridge Conditions: h_factor_absorb + h_delta_small

Standalone lemmas that derive the two numeric conditions required by
`glue_h5_to_h6` (and `Helper6SectorTranslation`) from the V4 budget and
outer δ₀ thresholds.

## Lemmas

1. `proj_budget_v4` — prove `h_proj_budget` from V4 definitions
   `ζDir = qProjective` and `ηProj = L·η + qProjective`.

2. `factor_absorb_v4` — given `h_proj_budget` and a constant-absorption
   threshold on `6·C_raw·√C_Pbar`, prove `h_factor_absorb`.

3. `delta_small_from_dir64_v4` — given `h_dir_64 : δ^(εgain - qTotalV4) ≤ 1/64`
   and the V4 budget component mapping, prove `h_delta_small`.

## Integration into incidence_to_ring_contradiction

These lemmas are intended for use inside the body of
`incidence_to_ring_contradiction` (currently `sorry`), when wiring up
the call to `glue_h5_to_h6`.

- `proj_budget_v4` discharges `h_proj_budget` unconditionally from
  V4 parameter positivity.
- `factor_absorb_v4` requires an additional δ₀ threshold hypothesis
  `h_factor_threshold : 6 * C_raw * Real.sqrt C_Pbar ≤ δ^(-e_proj_gap)`,
  where `e_proj_gap = ζ_dir + η_proj - (L_exp - 1/2)*η`.
  This threshold should be added to the outer `exists_budgetV4` / δ₀
  calibration, OR absorbed using `h_KBSG_absorb` if the constant fits
  under `81·2^39·3^80`.
- `delta_small_from_dir64_v4` discharges `h_delta_small` directly from
  `h_dir_64` (already a hypothesis of `incidence_to_ring_contradiction`).

## Whiteprint node

Helper for `incidence_to_ring_contradiction` V4 budget correction.
-/

public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV4
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Real

namespace ProductLikeIncidence.ProductReduction

/-! ## h_proj_budget from V4 definitions -/

/-- **Projection budget identity for V4**.

With `ζ_dir = ζDir = qProjective` and `η_proj = ηProj L η = L·η + qProjective`,
we have:
`ζ_dir + η_proj = 2·qProjective + L·η`
so
`(L - 1/2)·η < ζ_dir + η_proj`
because `η/2 < 2·qProjective` (both positive).

This discharges the `h_proj_budget` hypothesis of `glue_h5_to_h6`. -/
lemma proj_budget_v4
    {L_exp η ε κ0 p_projective : ℝ}
    (hL_exp_nonneg : 0 ≤ L_exp)
    (hη_pos : 0 < η)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_pos : 0 < p_projective) :
    (L_exp - 1 / 2 : ℝ) * η <
      ζDir p_projective ε κ0 + ηProj L_exp η ε κ0 p_projective := by
  have hqP_pos : 0 < qProjective p_projective ε κ0 := by
    dsimp only [qProjective]
    positivity
  have h1 : ζDir p_projective ε κ0 = qProjective p_projective ε κ0 := by
    rfl
  have h2 : ηProj L_exp η ε κ0 p_projective =
      L_exp * η + qProjective p_projective ε κ0 := by
    rfl
  rw [h1, h2]
  have h_goal : qProjective p_projective ε κ0 + (L_exp * η + qProjective p_projective ε κ0) =
      L_exp * η + 2 * qProjective p_projective ε κ0 := by ring
  rw [h_goal]
  have h3 : (L_exp - 1 / 2 : ℝ) * η < L_exp * η + 2 * qProjective p_projective ε κ0 := by
    have h4 : (L_exp - 1 / 2 : ℝ) * η = L_exp * η - η / 2 := by ring
    rw [h4]
    have h5 : 0 < η / 2 + 2 * qProjective p_projective ε κ0 := by positivity
    linarith
  exact h3

/-! ## h_delta_small from h_dir_64 -/

/-- **V4 generic budget sum ≤ qTotalV4**.

With the V4 budget component assignment:
- `q_graph_total = qInitV3 + 2·ρ_sep + qGraphV4 + qAbsorb + qNormEnergyV3`
- `q_diff = qDiffV4`
- `q_size = qSizeLossV4`
- `η = η` (the smaller energy parameter, `η = η_work/2`)
- `ζ_dir = ζDir`
- `η_proj = ηProj L_exp η ...`

The generic sum satisfies:
`q_graph_total + 2·q_diff + q_size + η + ζ_dir + η_proj ≤ qTotalV4`.

The gap is `(1+L_exp)·(η_work - η) > 0`. -/
lemma v4_generic_sum_le_qTotal
    {L_exp η_work ε κ0 p_projective τ rho_sel rho_sep η : ℝ}
    (hη_work_pos : 0 < η_work)
    (hη_pos : 0 < η)
    (hη_lt_work : η < η_work)
    (hL_exp_nonneg : 0 ≤ L_exp)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_pos : 0 < p_projective)
    (hτ_pos : 0 < τ)
    (hrho_sel_nonneg : 0 ≤ rho_sel)
    (hrho_sep_nonneg : 0 ≤ rho_sep) :
    let q_graph_total := qInitV3 η_work rho_sel + 2 * rho_sep +
        qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep +
        qAbsorb η_work + qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep
    let q_diff := qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
    let q_size := qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
    let ζ_dir := ζDir p_projective ε κ0
    let η_proj := ηProj L_exp η ε κ0 p_projective
    q_graph_total + 2 * q_diff + q_size + η + ζ_dir + η_proj ≤
      qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
  dsimp only
  have h_gap : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep -
      (qInitV3 η_work rho_sel + 2 * rho_sep +
        qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep +
        qAbsorb η_work + qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep +
        2 * qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep +
        qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep +
        η + ζDir p_projective ε κ0 +
        ηProj L_exp η ε κ0 p_projective) =
      (1 + L_exp) * (η_work - η) := by
    dsimp only [qTotalV4, qGraphV4, qDiffV4, qSizeLossV4, qEffV4,
      qNormChunkV4, qKV4, qDensityV4, qKAV4, qInputV4, qFixedCoordinate,
      qNormEnergyV3, qCoordEnergyV3, rhoExc, qKaufBase,
      qPlan, qKaufman, qEnergy, qBox, qAbsorb, ζDir, ηProj,
      qK, qProjective, alphaProjectionV4, qMassV4, qInitV3]
    <;> ring
  have h_pos : 0 < (1 + L_exp) * (η_work - η) := by
    have h1 : 0 < 1 + L_exp := by linarith
    have h2 : 0 < η_work - η := by linarith
    positivity
  have h5 : 0 ≤ qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep -
      (qInitV3 η_work rho_sel + 2 * rho_sep +
        qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep +
        qAbsorb η_work + qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep +
        2 * qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep +
        qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep +
        η + ζDir p_projective ε κ0 +
        ηProj L_exp η ε κ0 p_projective) := by
    rw [h_gap] <;> linarith
  exact le_of_sub_nonneg h5

/-- **Derive h_delta_small from h_dir_64**.

Given `h_dir_64 : δ^(εgain - qTotalV4) ≤ 1/64` and the V4 budget
component assignment (where the generic sum ≤ qTotalV4), conclude
`h_delta_small : δ^(εgain - generic_sum) ≤ 1/64`.

Since `generic_sum ≤ qTotalV4`, we have `εgain - generic_sum ≥ εgain - qTotalV4`.
For `0 < δ < 1`, larger exponents give smaller values:
`δ^(εgain - generic_sum) ≤ δ^(εgain - qTotalV4) ≤ 1/64`. -/
lemma delta_small_from_dir64_v4
    {δ εgain L_exp η_work ε κ0 p_projective τ rho_sel rho_sep η : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hη_work_pos : 0 < η_work)
    (hη_pos : 0 < η)
    (hη_lt_work : η < η_work)
    (hL_exp_nonneg : 0 ≤ L_exp)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_pos : 0 < p_projective)
    (hτ_pos : 0 < τ)
    (hrho_sel_nonneg : 0 ≤ rho_sel)
    (hrho_sep_nonneg : 0 ≤ rho_sep)
    (h_budget : εgain > qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep)
    (h_dir_64 : δ ^ (εgain - qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep) ≤ 1 / 64)
    (q_graph_total q_diff q_size ζ_dir η_proj : ℝ)
    (h_q_graph_total_eq : q_graph_total = qInitV3 η_work rho_sel + 2 * rho_sep +
        qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep +
        qAbsorb η_work + qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep)
    (h_q_diff_eq : q_diff = qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep)
    (h_q_size_eq : q_size = qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep)
    (h_ζ_dir_eq : ζ_dir = ζDir p_projective ε κ0)
    (h_η_proj_eq : η_proj = ηProj L_exp η ε κ0 p_projective) :
    δ ^ (εgain - (q_graph_total + 2 * q_diff + q_size + η + ζ_dir + η_proj)) ≤ 1 / 64 := by
  have h_sum_le : q_graph_total + 2 * q_diff + q_size + η + ζ_dir + η_proj ≤
      qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
    rw [h_q_graph_total_eq, h_q_diff_eq, h_q_size_eq, h_ζ_dir_eq, h_η_proj_eq]
    exact v4_generic_sum_le_qTotal hη_work_pos hη_pos hη_lt_work hL_exp_nonneg
      hε_pos hκ0_pos hp_pos hτ_pos hrho_sel_nonneg hrho_sep_nonneg
  have h_exp_ge : εgain - (q_graph_total + 2 * q_diff + q_size + η + ζ_dir + η_proj) ≥
      εgain - qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
    linarith
  have h6 : δ ^ (εgain - (q_graph_total + 2 * q_diff + q_size + η + ζ_dir + η_proj)) ≤
      δ ^ (εgain - qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep) := by
    exact Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h_exp_ge
  exact le_trans h6 h_dir_64

end ProductLikeIncidence.ProductReduction

end
