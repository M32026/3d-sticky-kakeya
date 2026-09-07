module

/-
# Kaufman Absorption from WireBudgets_v3

Helper lemmas connecting WireBudgets_v3 exponents to the exact Kaufman
bridge's absorption condition.

## Key relationship (CORRECTED per operator audit)

WireBudgets_v3 defines:
  `qKaufBase = qPlan + η_work + qKaufman + qAbsorb`
  `rho_exc = qKaufBase + rho_sel`

The product `C_Kaufman * C_plan` is bounded by `δ^{-qKaufBase}`:
- `C_plan` ~ `δ^{-qPlan}` from C_Pbar regularity
- `C_Kaufman` ~ `δ^{-(η_work + qKaufman + qAbsorb)}` from C_ν (η_work),
  R^(2κ0) (qKaufman), and numerical constant absorption (qAbsorb)

For the exact Kaufman bridge, we need:
  `C_Kaufman * C_plan ≤ δ^{-rho_exc} * (c/8)`

Set `q_total = qKaufBase` and `q_extra = rho_sel`.
Then `rho_exc = q_total + q_extra`, and if `δ^{rho_sel} ≤ c/8`,
`kaufman_absorption_for_endgame` gives the result.

## Whiteprint node
`phase2_bourgain_pipeline/kaufman_absorption_v3`
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.Energy.KaufmanBadDirectionsExact
public import MyLeanRepo.Energy.KaufmanIntegrationHelper
public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Classical

namespace ProductLikeIncidence.ProductReduction

/-- **Kaufman absorption from WireBudgets_v3 bounds**.

Given a product bound `C_Kaufman * C_plan ≤ δ^{-q_total}` and an extra
exponent `q_extra` with `δ^{q_extra} ≤ c/8`, conclude:

  `C_Kaufman * C_plan ≤ δ^{-(q_total + q_extra)} * (c/8)`

Standard WireBudgets absorption: `q_extra` absorbs the `c/8` factor.

Typical instantiation: `q_total = qKaufBase`, `q_extra = rho_sel`,
so `rho_exc = qKaufBase + rho_sel`.
-/
lemma kaufman_absorption_v3
    {δ c C_Kaufman C_plan q_total q_extra : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hc_pos : 0 < c)
    (hC_product_nonneg : 0 ≤ C_Kaufman * C_plan)
    (h_product_bound : C_Kaufman * C_plan ≤ δ ^ (-q_total))
    (hq_extra_pos : 0 < q_extra)
    (hδ_small : δ ^ q_extra ≤ c / 8) :
    C_Kaufman * C_plan ≤ δ ^ (-(q_total + q_extra)) * (c / 8) :=
  robust_projection_main.kaufman_absorption_for_endgame
    (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
    (hc_pos := hc_pos)
    (hC_product_nonneg := hC_product_nonneg)
    (h_product_bound := h_product_bound)
    (hrho_exc_eq := by ring)
    (hq_extra_pos := hq_extra_pos)
    (hδ_small := hδ_small)

/-- **Product bound at qKaufBase**.

Given component bounds that include ALL loss factors:
- `C_plan ≤ δ^{-qPlan}`
- `C_Kaufman ≤ δ^{-(η_work + qKaufman + qAbsorb)}` (includes C_ν factor η_work,
  R^(2κ0) factor qKaufman, and numerical constant absorption qAbsorb)

Then:
  `C_Kaufman * C_plan ≤ δ^{-(qPlan + η_work + qKaufman + qAbsorb)} = δ^{-qKaufBase}`.

This is the corrected reference: every factor in the conclusion is present
in a hypothesis. No monotonicity gap.
-/
lemma kaufman_product_bound_qKaufBase
    {δ C_plan C_Kaufman η_work τ κ0 : ℝ}
    (hδ_pos : 0 < δ)
    (hC_plan_bound : C_plan ≤ δ ^ (-(qPlan η_work)))
    (hC_Kaufman_bound : C_Kaufman ≤
        δ ^ (-(η_work + qKaufman η_work τ κ0 + qAbsorb η_work)))
    (hC_plan_nonneg : 0 ≤ C_plan)
    (hC_Kaufman_nonneg : 0 ≤ C_Kaufman) :
    C_Kaufman * C_plan ≤
    δ ^ (-(qPlan η_work + η_work + qKaufman η_work τ κ0 + qAbsorb η_work)) := by
  have h1 : C_Kaufman * C_plan ≤
      δ ^ (-(η_work + qKaufman η_work τ κ0 + qAbsorb η_work)) *
      δ ^ (-(qPlan η_work)) := by
    gcongr <;> tauto
  have h2 : δ ^ (-(η_work + qKaufman η_work τ κ0 + qAbsorb η_work)) *
           δ ^ (-(qPlan η_work)) =
      δ ^ (-(qPlan η_work + η_work + qKaufman η_work τ κ0 + qAbsorb η_work)) := by
    rw [← Real.rpow_add hδ_pos] <;> ring_nf
  rw [h2] at h1
  exact h1

/-- **Convenience: absorption with q_extra = rho_sel**.

Instantiates `kaufman_absorption_v3` with `q_extra = rho_sel`.

Given:
- `h_product_bound : C_Kaufman * C_plan ≤ δ^{-qKaufBase}`
- `h_rho_sel_pos : 0 < rho_sel`
- `hδ_rho_sel_small : δ^{rho_sel} ≤ c/8`

Concludes:
- `C_Kaufman * C_plan ≤ δ^{-(qKaufBase + rho_sel)} * (c/8)`
- i.e. `C_Kaufman * C_plan ≤ δ^{-rho_exc} * (c/8)` when `rho_exc = qKaufBase + rho_sel`
-/
lemma kaufman_absorption_with_rho_sel
    {δ c C_Kaufman C_plan qKaufBase rho_sel : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hc_pos : 0 < c)
    (hC_product_nonneg : 0 ≤ C_Kaufman * C_plan)
    (h_product_bound : C_Kaufman * C_plan ≤ δ ^ (-qKaufBase))
    (h_rho_sel_pos : 0 < rho_sel)
    (hδ_rho_sel_small : δ ^ rho_sel ≤ c / 8) :
    C_Kaufman * C_plan ≤ δ ^ (-(qKaufBase + rho_sel)) * (c / 8) :=
  kaufman_absorption_v3
    (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
    (hc_pos := hc_pos)
    (hC_product_nonneg := hC_product_nonneg)
    (h_product_bound := h_product_bound)
    (hq_extra_pos := h_rho_sel_pos)
    (hδ_small := hδ_rho_sel_small)

end ProductLikeIncidence.ProductReduction
