module

/-
# V4 Bridge Hypotheses — Discharge H5→H6 absorption conditions from V4 budget

This module provides lemmas that prove the hard numeric hypotheses
required by the H5→H6 bridges, using V4 budget conditions.

## Bridge hypotheses discharged

1. **Size lower bound absorption** (`h_absorb` in `bridge_size_lower_bound`):
   `c_ret / M_ret * δ^(-s + q_input) ≥ δ^(-s + q_size)`

2. **Delta-set regularity absorption** (`h_absorb` in `bridge_delta_set_absorption`):
   `2 * (C_BSG * R_ret) ≤ K_work * δ^(-εnc)`

## Sign convention

The size exponent is `-s + q`. For `0 < δ < 1`, a **larger** `q` gives a
**smaller** δ-power (weaker lower bound). A "size loss" means `q_size > q_input`.

The BSG extraction retains a `δ^e` fraction (e.g. `e = 10·qKV4`). To absorb
the constant factor, we need `q_size - q_input > e`; the surplus
`gap := q_size - q_input - e > 0` provides room for constant absorption.

## Whiteprint node
Helper for V4 threshold wiring in `incidence_to_ring_contradiction`.
-/

public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV4
public import MyLeanRepo.ProductLikeIncidence.V4NumericFills
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Real ENNReal

namespace ProductLikeIncidence.ProductReduction

/-! ## 1. Size lower bound absorption -/

/-- **Size absorption algebra**: From `δ^(q_size - q_input) ≤ c_ret / M_ret`,
prove `c_ret / M_ret * δ^(-s + q_input) ≥ δ^(-s + q_size)`.

This is pure exponent algebra: the retention ratio must dominate the
δ-power corresponding to the size budget gap. -/
lemma size_absorption_algebra
    {δ s q_input q_size c_ret M_ret : ℝ}
    (hδ_pos : 0 < δ)
    (h_threshold : δ ^ (q_size - q_input) ≤ c_ret / M_ret) :
    c_ret / M_ret * δ ^ (-s + q_input) ≥ δ ^ (-s + q_size) := by
  have h1 : δ ^ (-s + q_size) = δ ^ (-s + q_input) * δ ^ (q_size - q_input) := by
    have h2 : (-s + q_size) = (-s + q_input) + (q_size - q_input) := by ring
    rw [h2, Real.rpow_add hδ_pos]
  rw [h1]
  have h3 : 0 < δ ^ (-s + q_input) := by positivity
  have h4 : δ ^ (q_size - q_input) ≤ c_ret / M_ret := h_threshold
  nlinarith

/-- **Size absorption with retention exponent**:

If the retention ratio satisfies `c_ret / M_ret ≥ δ^e / C` (where `e > 0`
is the retention exponent and `C > 0` is a constant), and the target size
exponent exceeds the input by more than `e` (i.e.
`gap := q_size - q_input - e > 0`), then for sufficiently small δ the
absorption holds.

The threshold is `δ^gap ≤ 1/C`, which ensures `C ≤ δ^{-gap}`. -/
lemma size_absorption_with_retention_exponent
    {δ s q_input q_size e gap C c_ret M_ret : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hC_pos : 0 < C)
    (he_pos : 0 < e)
    (hgap_pos : 0 < gap)
    (hgap_eq : q_size - q_input - e = gap)
    (h_ratio : c_ret / M_ret ≥ δ^e / C)
    (h_threshold : δ^gap ≤ 1 / C) :
    c_ret / M_ret * δ^(-s + q_input) ≥ δ^(-s + q_size) := by
  have h_C_absorbed : C ≤ δ^(-gap) :=
    weaken_const_by_delta hδ_pos hδ_lt_one hC_pos hgap_pos h_threshold
  have _he_pos' : 0 < e := he_pos
  have h1 : δ^e / C ≤ c_ret / M_ret := h_ratio
  have h2 : δ^(q_size - q_input) ≤ δ^e / C := by
    have h3 : q_size - q_input = e + gap := by linarith
    rw [h3]
    have h4 : δ^(e + gap) = δ^e * δ^gap := by
      rw [Real.rpow_add hδ_pos]
    rw [h4]
    have h5 : δ^gap ≤ 1 / C := h_threshold
    have h6 : 0 < δ^e := by
      exact Real.rpow_pos_of_pos hδ_pos e
    have h7 : δ^e * δ^gap ≤ δ^e * (1 / C) := by gcongr
    have h8 : δ^e * (1 / C) = δ^e / C := by ring
    rw [h8] at h7
    exact h7
  have h7 : δ^(q_size - q_input) ≤ c_ret / M_ret := le_trans h2 h1
  exact size_absorption_algebra hδ_pos h7

/-! ## 2. Regularity (delta-set constant) absorption -/

/-- **Regularity absorption**: From `δ^εnc ≤ K_work / (2 * C_BSG * R_ret)`,
prove `2 * (C_BSG * R_ret) ≤ K_work * δ^{-εnc}`.

This discharges the `h_absorb` hypothesis of `bridge_delta_set_absorption`. -/
lemma v4_regularity_absorption
    {δ εnc C_BSG R_ret K_work : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hC_BSG_pos : 0 < C_BSG)
    (hR_ret_pos : 0 < R_ret)
    (hK_work_pos : 0 < K_work)
    (hεnc_pos : 0 < εnc)
    (h_threshold : δ ^ εnc ≤ K_work / (2 * C_BSG * R_ret)) :
    2 * (C_BSG * R_ret) ≤ K_work * δ ^ (-εnc) := by
  set C : ℝ := 2 * (C_BSG * R_ret) / K_work with hC_def
  have hC_pos : 0 < C := by positivity
  have h1 : δ ^ εnc ≤ 1 / C := by
    have h2 : 1 / C = K_work / (2 * (C_BSG * R_ret)) := by
      rw [hC_def]
      field_simp [hK_work_pos.ne']
    have h3 : δ ^ εnc ≤ K_work / (2 * (C_BSG * R_ret)) := by
      have h4 : K_work / (2 * C_BSG * R_ret) = K_work / (2 * (C_BSG * R_ret)) := by ring
      rw [h4] at h_threshold
      exact h_threshold
    rw [h2]
    exact h3
  have h3 : C ≤ δ ^ (-εnc) :=
    weaken_const_by_delta hδ_pos hδ_lt_one hC_pos hεnc_pos h1
  have h4 : 2 * (C_BSG * R_ret) = K_work * C := by
    simp [hC_def]
    field_simp
  rw [h4]
  exact mul_le_mul_of_nonneg_left h3 (by linarith)

/-! ## 3. Unified V4 budget discharge -/

/-- **Unified V4 bridge hypotheses**: Discharge both size and regularity
absorption conditions from V4 budget thresholds.

Given:
- Size retention ratio `c_ret / M_ret ≥ δ^e / C` with surplus gap
- Regularity threshold `δ^εnc ≤ K_work / (2 * C_BSG * R_ret)`

Produces both bridge hypotheses needed by the H5→H6 bridges. -/
lemma v4_discharge_bridge_hypotheses
    {δ s q_input q_size e gap εnc C : ℝ}
    {c_ret M_ret C_BSG R_ret K_work : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hC_pos : 0 < C)
    (he_pos : 0 < e)
    (hgap_pos : 0 < gap)
    (hgap_eq : q_size - q_input - e = gap)
    (h_ratio : c_ret / M_ret ≥ δ^e / C)
    (hC_BSG_pos : 0 < C_BSG)
    (hR_ret_pos : 0 < R_ret)
    (hK_work_pos : 0 < K_work)
    (hεnc_pos : 0 < εnc)
    (h_size_threshold : δ^gap ≤ 1 / C)
    (h_reg_threshold : δ^εnc ≤ K_work / (2 * C_BSG * R_ret)) :
    (c_ret / M_ret * δ^(-s + q_input) ≥ δ^(-s + q_size)) ∧
    (2 * (C_BSG * R_ret) ≤ K_work * δ^(-εnc)) := by
  have h_size : c_ret / M_ret * δ^(-s + q_input) ≥ δ^(-s + q_size) :=
    size_absorption_with_retention_exponent hδ_pos hδ_lt_one hC_pos he_pos
      hgap_pos hgap_eq h_ratio h_size_threshold
  have h_reg : 2 * (C_BSG * R_ret) ≤ K_work * δ^(-εnc) :=
    v4_regularity_absorption hδ_pos hδ_lt_one hC_BSG_pos hR_ret_pos hK_work_pos
      hεnc_pos h_reg_threshold
  exact ⟨h_size, h_reg⟩

/-! ## 4. V4-specific size transfer derivation -/

/-- **V4 size transfer**: Derive the size lower bound absorption from
Marlin-style V4 budget parameters.

Given:
- Retention factor lower bound: `c_ret / M_ret ≥ δ^(qNormChunkV4 - slack) / C`
- Box threshold: `δ^slack ≤ 1/C`
- Size jump: `q_size - q_input = qNormChunkV4`

Derive: `c_ret / M_ret * δ^(-s + q_input) ≥ δ^(-s + q_size)`.

This mirrors the Marlin monolith derivation (lines 3784-3899):
the popularity lemma loses `qNormChunkV4 - slack` with constant `1/C`,
and the box threshold absorbs the constant via `δ^slack ≤ 1/C`. -/
lemma v4_size_transfer
    {δ s q_input q_size qNormChunkV4 slack C c_ret M_ret : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hC_pos : 0 < C)
    (hslack_pos : 0 < slack)
    (hqNorm_pos : 0 < qNormChunkV4)
    (h_size_jump : q_size - q_input = qNormChunkV4)
    (h_retention : c_ret / M_ret ≥ δ^(qNormChunkV4 - slack) / C)
    (h_box_threshold : δ^slack ≤ 1 / C) :
    c_ret / M_ret * δ^(-s + q_input) ≥ δ^(-s + q_size) := by
  have h1 : c_ret / M_ret * δ^(-s + q_input) ≥
      δ^(qNormChunkV4 - slack) / C * δ^(-s + q_input) := by
    have h_pos : 0 ≤ δ^(-s + q_input) := by positivity
    exact mul_le_mul_of_nonneg_right h_retention h_pos
  have h2 : δ^(qNormChunkV4 - slack) / C * δ^(-s + q_input) =
      δ^(-s + q_size - slack) / C := by
    have h3 : qNormChunkV4 - slack + (-s + q_input) = -s + q_size - slack := by
      linarith [h_size_jump]
    have h4 : δ^(qNormChunkV4 - slack) * δ^(-s + q_input) = δ^(-s + q_size - slack) := by
      rw [← Real.rpow_add hδ_pos, h3]
    calc
      δ^(qNormChunkV4 - slack) / C * δ^(-s + q_input)
        = (δ^(qNormChunkV4 - slack) * δ^(-s + q_input)) / C := by ring
      _ = δ^(-s + q_size - slack) / C := by rw [h4]
  rw [h2] at h1
  have h4 : δ^(-s + q_size - slack) / C ≥ δ^(-s + q_size) := by
    have h5 : δ^(-s + q_size) = δ^(-s + q_size - slack) * δ^slack := by
      rw [← Real.rpow_add hδ_pos] <;> ring_nf
    rw [h5]
    have h6 : 0 ≤ δ^(-s + q_size - slack) := by positivity
    have h7 : δ^slack ≤ 1 / C := h_box_threshold
    have h7' : δ^slack ≤ C⁻¹ := by
      have h_eq : (1 / C) = C⁻¹ := by
        exact one_div C
      rw [h_eq] at h7
      exact h7
    exact mul_le_mul_of_nonneg_left h7' h6
  exact ge_trans h1 h4

end ProductLikeIncidence.ProductReduction
