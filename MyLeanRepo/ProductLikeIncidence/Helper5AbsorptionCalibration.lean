module

/-
# Helper5 Absorption Calibration from V4 Budgets

Derives the three absorption conditions required by Helper5 from the V4
budget parameters and a single δ-smallness threshold:

1. `h_absorb_ret`: δ^θ_num ≤ 1/3^10
2. `h_absorb_size`: δ^(qSizeLossV3 - q_input - 10*q_K) ≤ 1/3^10
3. `h_absorb_KBSG`: 81·2^39·3^80 ≤ δ^(-qAbsorb)

## Calibration

Set:
- `θ_num := qAbsorb η_work`
- `q_K := qKV4 ...`
- `q_input := qInputV4 ...`
- `qSizeLossV3 := qSizeLossV4 ...`

Then the size-loss gap is:
`qSizeLossV4 - qInputV4 - 10·qKV4 = qAbsorb + qNormChunkV4 ≥ qAbsorb`

So both `θ_num ≥ qAbsorb` and the size-loss exponent `≥ qAbsorb`, and
`unified_absorptions` discharges all three conditions from the single
KBSG smallness threshold.

## Whiteprint node
Helper for V4 threshold wiring in `incidence_to_ring_contradiction`.
-/

public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV4
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Real ENNReal

namespace ProductLikeIncidence.ProductReduction

/-- **V4 size-loss gap**: `qSizeLossV4 - qInputV4 - 10·qKV4 = qAbsorb + qNormChunkV4`.

This shows the gap is at least `qAbsorb`, which is needed for the
`h_absorb_size` condition in Helper5. -/
lemma v4_size_loss_gap_eq
    {L_exp η_work ε κ0 p_projective τ rho_sel rho_sep : ℝ} :
    qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
      - qInputV4 L_exp η_work rho_sel rho_sep
      - 10 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep
    = qAbsorb η_work + qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
  dsimp only [qSizeLossV4, qEffV4, qInputV4, qNormChunkV4, qKV4]
  ; ring

end ProductLikeIncidence.ProductReduction
