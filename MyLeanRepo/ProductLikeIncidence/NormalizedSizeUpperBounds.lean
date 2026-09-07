module

/-
# Normalized Size Upper Bounds

Prove the Helper6-required upper bound
`Nδ(B_i_norm) ≤ K_work * δ^{-(s + ε_nc)}`
from Helper5's normalized-size transfer and an upstream bound on S_i.

## Proof route

The chain (matching monolith lines 4138–4280):

1. Helper5 gives `Nreal δ B_i_norm ≤ Nreal δ S_i`.
2. Upstream (Helper4 / Phase4–5 projection chain) gives
   `Nreal δ S_i ≤ C * δ^{-(s+a)}`, where `a = L_exp * η + η/2`
   and typically `C = 6` (3 from rounding covering × 2 from projective transport).
3. Absorb the slack `d = ε_nc - a ≥ η_work/100`:
   - `δ^d ≤ δ^(η_work/100) ≤ 1/C` (from the box bound threshold)
   - Therefore `C * δ^d ≤ 1 ≤ K_work`
   - So `C * δ^{-(s+a)} = C * δ^d * δ^{-(s+ε_nc)} ≤ K_work * δ^{-(s+ε_nc)}`

This module provides:
- `normalized_size_upper_absorption`: pure numeric absorption lemma
- `normalized_size_upper_bound`: full bound from Helper5 transfer + upstream S bound
- `normalized_size_upper_bounds_both`: convenience wrapper for B1, B2

## Dependencies
- `Nreal_mono_local` (RoundingWrapper.lean)
- `Real.rpow_le_rpow_of_exponent_ge`
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set Bornology ENNReal Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- **Numeric absorption**: Given `C * δ^d ≤ K_work` with `d = εnc - a`,
absorb the slack into the exponent:

`C * δ^{-(s+a)} ≤ K_work * δ^{-(s+εnc)}`.

This is the terminal step that converts the upstream projection-size bound
into the Helper6-required form. -/
lemma normalized_size_upper_absorption
    {δ s a εnc d K_work C : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hd_def : d = εnc - a)
    (hd_nonneg : 0 ≤ d)
    (hC_pos : 0 < C)
    (hK_work_pos : 0 < K_work)
    (h_absorb : C * δ ^ d ≤ K_work) :
    C * δ ^ (-(s + a)) ≤ K_work * δ ^ (-(s + εnc)) := by
  have h1 : δ ^ (-(s + a)) = δ ^ d * δ ^ (-(s + εnc)) := by
    rw [← Real.rpow_add hδ_pos]
    have h2 : d + (-(s + εnc)) = -(s + a) := by
      linarith [hd_def]
    rw [h2]
  rw [h1]
  have h3 : 0 ≤ δ ^ (-(s + εnc)) := by positivity
  nlinarith

/-- **Normalized size upper bound** for a single B_i_norm.

Given Helper5's transfer `Nreal δ B_norm ≤ Nreal δ S` and the upstream
bound `Nreal δ S ≤ C * δ^{-(s+a)}`, absorb the slack to conclude
`Nreal δ B_norm ≤ K_work * δ^{-(s+εnc)}`. -/
lemma normalized_size_upper_bound
    {δ s a εnc d K_work C : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    {B_norm S : Set ℝ}
    -- Helper5 transfer: normalized set is no larger than upstream S
    (hB_norm_transfer : Nreal δ B_norm ≤ Nreal δ S)
    -- Upstream size bound on S (from projection chain / Helper4)
    (hS_upper : Nreal δ S ≤ ENNReal.ofReal (C * δ ^ (-(s + a))))
    -- Numeric absorption
    (hd_def : d = εnc - a)
    (hd_nonneg : 0 ≤ d)
    (hC_pos : 0 < C)
    (hK_work_pos : 0 < K_work)
    (h_absorb : C * δ ^ d ≤ K_work) :
    Nreal δ B_norm ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))) := by
  have h_num : C * δ ^ (-(s + a)) ≤ K_work * δ ^ (-(s + εnc)) :=
    normalized_size_upper_absorption hδ_pos hδ_lt_one hd_def hd_nonneg hC_pos hK_work_pos h_absorb
  have h_main : Nreal δ B_norm ≤ ENNReal.ofReal (C * δ ^ (-(s + a))) :=
    le_trans hB_norm_transfer hS_upper
  have h_enn : ENNReal.ofReal (C * δ ^ (-(s + a))) ≤
      ENNReal.ofReal (K_work * δ ^ (-(s + εnc))) := by
    apply ENNReal.ofReal_le_ofReal
    exact h_num
  exact le_trans h_main h_enn

/-- **Box-bound absorption variant**: When the box bound gives
`δ^(η_work/100) ≤ 1/C` and `εnc ≥ a + η_work/100`, derive `C * δ^d ≤ 1`.

Use this with `normalized_size_upper_bound` when `K_work ≥ 1`. -/
lemma box_bound_absorption
    {δ a εnc η_work C : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hC_pos : 0 < C)
    (hη_work_pos : 0 < η_work)
    (h_enc_ge : εnc ≥ a + η_work / 100)
    (h_box : δ ^ (η_work / 100) ≤ 1 / C) :
    C * δ ^ (εnc - a) ≤ 1 := by
  set d : ℝ := εnc - a with hd_def
  have hd_ge : d ≥ η_work / 100 := by linarith
  have h1 : δ ^ d ≤ δ ^ (η_work / 100) :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le hd_ge
  have h2 : δ ^ d ≤ 1 / C := le_trans h1 h_box
  have h3 : 0 ≤ δ ^ d := by positivity
  have h4 : C * δ ^ d ≤ C * (1 / C) := by gcongr
  have h5 : C * (1 / C) = 1 := by
    field_simp [hC_pos.ne'] <;> ring
  rw [h5] at h4
  exact h4

/-- **Both normalized size upper bounds**: Convenience wrapper applying
`normalized_size_upper_bound` to B1_norm and B2_norm simultaneously. -/
lemma normalized_size_upper_bounds_both
    {δ s a εnc d K_work C : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    {B1_norm B2_norm S1 S2 : Set ℝ}
    (hB1_norm_transfer : Nreal δ B1_norm ≤ Nreal δ S1)
    (hB2_norm_transfer : Nreal δ B2_norm ≤ Nreal δ S2)
    (hS1_upper : Nreal δ S1 ≤ ENNReal.ofReal (C * δ ^ (-(s + a))))
    (hS2_upper : Nreal δ S2 ≤ ENNReal.ofReal (C * δ ^ (-(s + a))))
    (hd_def : d = εnc - a)
    (hd_nonneg : 0 ≤ d)
    (hC_pos : 0 < C)
    (hK_work_pos : 0 < K_work)
    (h_absorb : C * δ ^ d ≤ K_work) :
    Nreal δ B1_norm ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))) ∧
    Nreal δ B2_norm ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))) := by
  constructor
  · exact normalized_size_upper_bound
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hB_norm_transfer := hB1_norm_transfer)
      (hS_upper := hS1_upper)
      (hd_def := hd_def) (hd_nonneg := hd_nonneg)
      (hC_pos := hC_pos) (hK_work_pos := hK_work_pos)
      (h_absorb := h_absorb)
  · exact normalized_size_upper_bound
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hB_norm_transfer := hB2_norm_transfer)
      (hS_upper := hS2_upper)
      (hd_def := hd_def) (hd_nonneg := hd_nonneg)
      (hC_pos := hC_pos) (hK_work_pos := hK_work_pos)
      (h_absorb := h_absorb)

end ProductLikeIncidence.ProductReduction
