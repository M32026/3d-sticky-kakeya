module

/-
# Graph Absorption Proof — hc_proj_le

Proves the `hc_proj_le` hypothesis required by `bridge_graph_absorb_lower`:

```
c_proj ≤ D * c_endgame / 8
```

where:
- `c_proj = δ ^ q_graph_total`
- `D = δ^(22*q_K) / (16 * 3^22)`
- `c_endgame = δ^(η_work/2) / (14 * C_work'^2)`

## Proof outline

1. Rewrite target as:
   `δ^q_graph_total ≤ δ^(22*q_K + η_work/2) / (1792 * 3^22 * C_work'^2)`

2. Use `C_work' ≤ δ^(-η_work)` to get:
   `1/C_work'^2 ≥ δ^(2*η_work)`
   so RHS ≥ `δ^(22*q_K + 5*η_work/2) / (1792 * 3^22)`

3. Let `E := q_graph_total - 22*q_K - η_work/2`.
   By budget definitions:
   `E - 2*η_work = 3*rho_sel + 2*rho_sep + η_work/20 + qAbsorb η_work + qNormEnergyV3`
   which is `≥ qAbsorb η_work`.

4. Since `δ < 1` and `E - 2*η_work ≥ qAbsorb η_work`:
   `δ^(E - 2*η_work) ≤ δ^(qAbsorb η_work)`

5. From KBSG absorption:
   `δ^(qAbsorb η_work) ≤ 1/(81 * 2^39 * 3^80) ≤ 1/(1792 * 3^22)`

6. Therefore `δ^(E - 2*η_work) ≤ 1/(1792 * 3^22)`.
   Multiply by `δ^(22*q_K + 5*η_work/2)`:
   `δ^q_graph_total ≤ δ^(22*q_K + 5*η_work/2) / (1792 * 3^22)`

7. Combine with step 2 to conclude.
-/

public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV3
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV4
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Real

namespace ProductLikeIncidence.ProductReduction

/-- **Graph absorption: `hc_proj_le` proof**.

Given the V4 budget parameters and KBSG absorption bound, prove:
`δ ^ q_graph_total ≤ (δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ))) * c_endgame / 8`

where `c_endgame = δ ^ (η_work / 2) / (14 * C_work' ^ 2)` and
`C_work' ≤ δ ^ (-η_work)`.

This is the `hc_proj_le` hypothesis of `bridge_graph_absorb_lower`. -/
lemma graph_absorb_hc_proj_le
    {δ η_work ε τ κ0 L_exp p_projective rho_sel rho_sep : ℝ}
    {q_K q_graph_total C_work' c_endgame : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hη_work_pos : 0 < η_work)
    (hκ0_pos : 0 < κ0)
    (hτ_pos : 0 < τ)
    (hrho_sel_nonneg : 0 ≤ rho_sel)
    (hrho_sep_nonneg : 0 ≤ rho_sep)
    (hq_K_eq : q_K = qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep)
    (hq_graph_total_eq : q_graph_total =
        qInitV3 η_work rho_sel + 2 * rho_sep +
        qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep +
        qAbsorb η_work + qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep)
    (hc_endgame_eq : c_endgame = δ ^ (η_work / 2) / (14 * C_work' ^ 2))
    (hC_work'_pos : 0 < C_work')
    (hC_work'_le : C_work' ≤ δ ^ (-η_work))
    (hKBSG_absorb : (81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80 ≤ δ ^ (-(qAbsorb η_work))) :
    δ ^ q_graph_total ≤
      (δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ))) * c_endgame / 8 := by
  set D : ℝ := δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ)) with hD_def
  have hD_pos : 0 < D := by positivity

  -- Step 1: rewrite c_endgame
  have h1 : D * c_endgame / 8 =
      δ ^ (22 * q_K + η_work / 2) / (1792 * (3 ^ 22 : ℝ) * C_work' ^ 2) := by
    rw [hc_endgame_eq, hD_def]
    have h_pos1 : 0 < (14 : ℝ) * C_work' ^ 2 := by positivity
    have h_mul : δ ^ (22 * q_K) * δ ^ (η_work / 2) = δ ^ (22 * q_K + η_work / 2) := by
      rw [← Real.rpow_add hδ_pos]
    calc
      (δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ))) * (δ ^ (η_work / 2) / (14 * C_work' ^ 2)) / 8
        = (δ ^ (22 * q_K) * δ ^ (η_work / 2)) / ((16 * (3 ^ 22 : ℝ)) * (14 * C_work' ^ 2) * 8) := by
          field_simp [h_pos1.ne']
      _ = δ ^ (22 * q_K + η_work / 2) / (1792 * (3 ^ 22 : ℝ) * C_work' ^ 2) := by
          rw [h_mul]; ring

  -- Step 2: lower bound D * c_endgame / 8 using C_work' ≤ δ^(-η_work)
  have hC2 : C_work' ^ 2 ≤ δ ^ (-2 * η_work) := by
    have h21 : C_work' ≤ δ ^ (-η_work) := hC_work'_le
    have h22 : 0 ≤ C_work' := by linarith [hC_work'_pos]
    have h23 : C_work' ^ 2 ≤ (δ ^ (-η_work)) ^ 2 := by
      gcongr
    have h24 : (δ ^ (-η_work)) ^ 2 = δ ^ (-2 * η_work) := by
      have h25 : (δ ^ (-η_work)) ^ (2 : ℝ) = δ ^ ((-η_work) * (2 : ℝ)) := by
        rw [Real.rpow_mul hδ_pos.le]
      have h26 : (-η_work) * (2 : ℝ) = -2 * η_work := by ring
      simpa [h26] using h25
    rw [h24] at h23
    exact h23
  have h3 : 0 < C_work' ^ 2 := by positivity
  have h4 : (1 : ℝ) / (C_work' ^ 2) ≥ δ ^ (2 * η_work) := by
    have h41 : C_work' ^ 2 ≤ (δ ^ (2 * η_work))⁻¹ := by
      have h_neg : δ ^ (-2 * η_work) = (δ ^ (2 * η_work))⁻¹ := by
        simp [Real.rpow_neg, hδ_pos.le]
      rw [h_neg] at hC2
      exact hC2
    have h_pos : 0 < δ ^ (2 * η_work) := by positivity
    have h : (C_work' ^ 2)⁻¹ ≥ δ ^ (2 * η_work) := by
      calc (C_work' ^ 2)⁻¹ ≥ ((δ ^ (2 * η_work))⁻¹)⁻¹ := by gcongr
        _ = δ ^ (2 * η_work) := by
          field_simp [h_pos.ne']
    simpa [one_div] using h
  have h5 : D * c_endgame / 8 ≥ δ ^ (22 * q_K + 5 * η_work / 2) / (1792 * (3 ^ 22 : ℝ)) := by
    rw [h1]
    have h51 : δ ^ (22 * q_K + η_work / 2) / (1792 * (3 ^ 22 : ℝ) * C_work' ^ 2) =
        δ ^ (22 * q_K + η_work / 2) / (1792 * (3 ^ 22 : ℝ)) * (1 / C_work' ^ 2) := by
      field_simp [h3.ne']
    rw [h51]
    have h54 : δ ^ (22 * q_K + η_work / 2) / (1792 * (3 ^ 22 : ℝ)) * (1 / C_work' ^ 2) ≥
        δ ^ (22 * q_K + η_work / 2) / (1792 * (3 ^ 22 : ℝ)) * δ ^ (2 * η_work) := by
      gcongr
    have h55 : δ ^ (22 * q_K + η_work / 2) / (1792 * (3 ^ 22 : ℝ)) * δ ^ (2 * η_work) =
        δ ^ (22 * q_K + 5 * η_work / 2) / (1792 * (3 ^ 22 : ℝ)) := by
      have h_comm : δ ^ (22 * q_K + η_work / 2) / (1792 * (3 ^ 22 : ℝ)) * δ ^ (2 * η_work) =
          (δ ^ (22 * q_K + η_work / 2) * δ ^ (2 * η_work)) / (1792 * (3 ^ 22 : ℝ)) := by ring
      rw [h_comm]
      have h : δ ^ (22 * q_K + η_work / 2) * δ ^ (2 * η_work) =
          δ ^ (22 * q_K + 5 * η_work / 2) := by
        have h' : δ ^ (22 * q_K + η_work / 2) * δ ^ (2 * η_work) =
            δ ^ ((22 * q_K + η_work / 2) + (2 * η_work)) := by
          rw [← Real.rpow_add hδ_pos]
        have h_exp : (22 * q_K + η_work / 2) + (2 * η_work) = 22 * q_K + 5 * η_work / 2 := by ring
        rw [h', h_exp]
      rw [h]
    rw [h55] at h54
    exact h54

  -- Step 3: E = q_graph_total - 22*q_K - η_work/2
  set E : ℝ := q_graph_total - 22 * q_K - η_work / 2 with hE_def
  have hE_expand : E - 2 * η_work =
      3 * rho_sel + 2 * rho_sep + η_work / 20 + qAbsorb η_work +
      qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by
    rw [hE_def, hq_graph_total_eq, hq_K_eq]
    dsimp only [qGraphV4, qInitV3, qAbsorb]
    <;> ring

  -- Step 4: E - 2*η_work ≥ qAbsorb η_work
  have hE_ge : E - 2 * η_work ≥ qAbsorb η_work := by
    rw [hE_expand]
    dsimp only [qAbsorb]
    have h6 : 0 ≤ 3 * rho_sel + 2 * rho_sep + η_work / 20 +
        qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by
      have h7 : 0 ≤ 3 * rho_sel := by positivity
      have h8 : 0 ≤ 2 * rho_sep := by positivity
      have h9 : 0 ≤ η_work / 20 := by positivity
      have h10 : 0 ≤ qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by
        dsimp only [qNormEnergyV3, qCoordEnergyV3, qEnergy, rhoExc, qKaufBase,
          qKaufman, qBox, qPlan, qAbsorb] <;> positivity
      linarith
    linarith

  -- Step 5: δ^(E - 2*η_work) ≤ δ^qAbsorb ≤ 1/(81*2^39*3^80) ≤ 1/(1792*3^22)
  have hδ_le_one : δ ≤ 1 := hδ_lt_one.le
  have h6 : δ ^ (E - 2 * η_work) ≤ δ ^ (qAbsorb η_work) :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one hE_ge
  have h7 : δ ^ (qAbsorb η_work) ≤ 1 / ((81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80) := by
    have h_pos : 0 < δ ^ (qAbsorb η_work) := by positivity
    have h_inv : δ ^ (-(qAbsorb η_work)) = (δ ^ (qAbsorb η_work))⁻¹ := by
      rw [Real.rpow_neg hδ_pos.le]
    rw [h_inv] at hKBSG_absorb
    field_simp [h_pos.ne'] at hKBSG_absorb ⊢ <;> linarith
  have h8 : (1 : ℝ) / ((81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80) ≤
      1 / (1792 * (3 ^ 22 : ℝ)) := by
    gcongr <;> norm_num
  have h9 : δ ^ (E - 2 * η_work) ≤ 1 / (1792 * (3 ^ 22 : ℝ)) :=
    le_trans (le_trans h6 h7) h8

  -- Step 6: multiply by δ^(22*q_K + 5*η_work/2)
  have h10 : δ ^ q_graph_total ≤
      δ ^ (22 * q_K + 5 * η_work / 2) / (1792 * (3 ^ 22 : ℝ)) := by
    have h11 : q_graph_total = (22 * q_K + 5 * η_work / 2) + (E - 2 * η_work) := by
      rw [hE_def] <;> ring
    rw [h11]
    have h12 : δ ^ ((22 * q_K + 5 * η_work / 2) + (E - 2 * η_work)) =
        δ ^ (22 * q_K + 5 * η_work / 2) * δ ^ (E - 2 * η_work) := by
      rw [← Real.rpow_add hδ_pos]
    rw [h12]
    have h14 : δ ^ (22 * q_K + 5 * η_work / 2) * δ ^ (E - 2 * η_work) ≤
        δ ^ (22 * q_K + 5 * η_work / 2) * (1 / (1792 * (3 ^ 22 : ℝ))) := by
      have h141 : 0 < δ ^ (22 * q_K + 5 * η_work / 2) := by positivity
      exact mul_le_mul_of_nonneg_left h9 h141.le
    have h15 : δ ^ (22 * q_K + 5 * η_work / 2) * (1 / (1792 * (3 ^ 22 : ℝ))) =
        δ ^ (22 * q_K + 5 * η_work / 2) / (1792 * (3 ^ 22 : ℝ)) := by ring
    rw [h15] at h14
    exact h14

  -- Step 7: combine
  exact le_trans h10 h5

end ProductLikeIncidence.ProductReduction

end
