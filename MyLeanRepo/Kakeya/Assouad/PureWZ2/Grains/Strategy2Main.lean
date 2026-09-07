import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.BaseConfigWithSticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DirectionBinAssembly
import Mathlib.Tactic

/-!
# Strategy 2: Main theorem for outputLoss > 1

This module proves the grain configuration for `1 < outputLoss` using
direction bin pigeonholing.

## Proof structure

1. From the critical package, derive sticky data (`hNormAt`, `hStickyAt`)
2. Choose `loss_src < outputLoss - 1` to leave ε slack for the bin factor
3. Choose `delta₀'` small enough to satisfy:
   - `(2π+1) · δ^ε ≤ 1` (absorption condition)
   - `3 · 2^σ ≤ (1/δ)^(outputLoss - σ)` (global AD smallness)
4. Use `pure_wz2_grain_base_config_with_sticky_at` to get a base configuration
   at `loss_src`
5. Apply `direction_bin_grain_config` to obtain the grain configuration

## Dependencies

- `direction_bin_grain_config` in `DirectionBinAssembly.lean` — COMPLETE
- `pure_wz2_grain_base_config_with_sticky_at` in `BaseConfigWithSticky.lean`

## Whiteprint node

`PureWZ2/Grains/strategy2_main`
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set MeasureTheory Classical Real

attribute [local instance] Classical.propDecidable

/-- Strategy 2 main theorem: construct a grain configuration for outputLoss > 1.

Uses direction bin pigeonholing to restrict shading while keeping the full
family for CWA. The ε = outputLoss - 1 - loss_src slack absorbs the 2π+1
factor from the bin pigeonhole. -/
theorem pure_wz2_strategy2_main
    (h_subunit : PureWZ2SubunitPackageStatement)
    (h_extraction : PureWZ2CriticalExtractionStatement)
    (h_sticky : PureWZ2PropStickyStatement)
    (sigma : ℝ)
    (hcrit : PureWZ2CriticalPackage sigma)
    (outputLoss delta₀ : ℝ)
    (hloss_pos : 0 < outputLoss)
    (houtputLoss_gt_one : 1 < outputLoss)
    (hdelta₀_pos : 0 < delta₀) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ delta₀ ∧
      Nonempty (PureWZ2GrainConfiguration sigma outputLoss delta) := by
  -- Unpack Node 3 sticky data
  rcases h_sticky h_subunit h_extraction with ⟨capability⟩
  have h_sticky_from_crit : PureWZ2PropStickyFromCriticalStatement :=
    capability.toLegacyFromCritical
  rcases h_sticky_from_crit with
    ⟨nE, lE, hNormAt, hStickyAt, _realizationAt⟩

  -- Choose loss_src = (outputLoss - 1) / 2, so loss_src < outputLoss - 1
  let loss_src : ℝ := (outputLoss - 1) / 2
  have hloss_src_pos : 0 < loss_src := by
    dsimp only [loss_src]
    linarith [houtputLoss_gt_one]
  have hloss_src_lt : loss_src < outputLoss - 1 := by
    dsimp only [loss_src]
    linarith [houtputLoss_gt_one]

  -- Epsilon slack for absorbing the bin factor
  let epsilon : ℝ := outputLoss - 1 - loss_src
  have hepsilon_pos : 0 < epsilon := by linarith

  -- Need outputLoss - sigma > 0 for the global AD smallness threshold
  have hsigma_lt_one : sigma < 1 := hcrit.sigma_lt_one
  have hsigma_pos : 0 < sigma := hcrit.sigma_pos
  have houtputLoss_minus_sigma_pos : 0 < outputLoss - sigma := by linarith

  -- Threshold for absorption: (2π+1) * δ^ε ≤ 1
  -- ⟺ δ ≤ (1/(2π+1))^(1/ε)
  let threshold_absorb : ℝ := (1 / (2 * Real.pi + 1)) ^ (1 / epsilon)
  have hthreshold_absorb_pos : 0 < threshold_absorb := by
    apply Real.rpow_pos_of_pos
    · positivity

  -- Threshold for global AD: 3 * 2^σ ≤ (1/δ)^(outputLoss - σ)
  -- ⟺ δ ≤ (1/(3 * 2^σ))^(1/(outputLoss - σ))
  let threshold_small : ℝ := (1 / (3 * (2 : ℝ)^sigma)) ^ (1 / (outputLoss - sigma))
  have hthreshold_small_pos : 0 < threshold_small := by
    apply Real.rpow_pos_of_pos
    · positivity

  -- Choose delta₀' small enough for all conditions
  let delta₀' : ℝ := min delta₀ (min threshold_absorb (min threshold_small (1 / 2)))
  have hdelta₀'_pos : 0 < delta₀' := by positivity
  have hdelta₀'_le : delta₀' ≤ delta₀ := min_le_left _ _
  have hdelta₀'_le_absorb : delta₀' ≤ threshold_absorb := by
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hdelta₀'_le_small : delta₀' ≤ threshold_small := by
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hdelta₀'_le_half : delta₀' ≤ 1 / 2 := by
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))

  -- Step 1: Get base config at loss_src
  rcases pure_wz2_grain_base_config_with_sticky_at
      _realizationAt sigma hcrit
      loss_src loss_src delta₀'
      hloss_src_pos (le_refl loss_src) hloss_src_pos hdelta₀'_pos with
    ⟨_sourceLoss, _normalizationLoss, delta_n, _source, _normalized,
      ⟨family, shading, line_class, cubical, extremal, top_level_cwa⟩, hProvision,
      _sourceLoss_pos, _normalizationLoss_pos, hdelta_n_pos, hdelta_n_le,
      _hbase_family, _hbase_shading⟩
  let F := family
  let S := shading

  have hdelta_n_le_absorb : delta_n ≤ threshold_absorb :=
    hdelta_n_le.trans hdelta₀'_le_absorb
  have hdelta_n_le_small : delta_n ≤ threshold_small :=
    hdelta_n_le.trans hdelta₀'_le_small
  have hdelta_n_lt_one : delta_n < 1 := by
    linarith [hdelta_n_le.trans hdelta₀'_le_half]

  -- Verify absorption condition
  have h_absorb : (2 * Real.pi + 1) * delta_n ^ epsilon ≤ 1 := by
    have h1 : delta_n ≤ (1 / (2 * Real.pi + 1)) ^ (1 / epsilon) := hdelta_n_le_absorb
    have h2 : delta_n ^ epsilon ≤ ((1 / (2 * Real.pi + 1)) ^ (1 / epsilon)) ^ epsilon :=
      Real.rpow_le_rpow (by linarith) h1 (by linarith)
    have h3 : ((1 / (2 * Real.pi + 1)) ^ (1 / epsilon)) ^ epsilon = 1 / (2 * Real.pi + 1) := by
      rw [← Real.rpow_mul (by positivity)]
      have h4 : (1 / epsilon) * epsilon = 1 := by field_simp [hepsilon_pos.ne'] <;> ring
      rw [h4]
      simp
    rw [h3] at h2
    have h4 : (2 * Real.pi + 1) * delta_n ^ epsilon ≤ (2 * Real.pi + 1) * (1 / (2 * Real.pi + 1)) := by
      gcongr
    have h5 : (2 * Real.pi + 1) * (1 / (2 * Real.pi + 1)) = 1 := by
      field_simp [show (2 * Real.pi + 1 : ℝ) ≠ 0 by positivity] <;> ring
    rw [h5] at h4
    exact h4

  -- Verify global AD smallness condition
  have hsmall_global : 3 * (2 : ℝ)^sigma ≤ (1 / delta_n)^(outputLoss - sigma) := by
    have h1 : delta_n ≤ (1 / (3 * (2 : ℝ)^sigma)) ^ (1 / (outputLoss - sigma)) :=
      hdelta_n_le_small
    have h2 : 0 < delta_n := hdelta_n_pos
    have h3 : (1 / delta_n) ≥ 1 / ((1 / (3 * (2 : ℝ)^sigma)) ^ (1 / (outputLoss - sigma))) := by
      gcongr
    have h5 : 0 < (3 * (2 : ℝ)^sigma) := by positivity
    have h41 : (1 / (3 * (2 : ℝ)^sigma)) ^ (1 / (outputLoss - sigma)) =
        1 / ((3 * (2 : ℝ)^sigma) ^ (1 / (outputLoss - sigma))) := by
      have h42 : (1 / (3 * (2 : ℝ)^sigma)) = (3 * (2 : ℝ)^sigma) ^ (-1 : ℝ) := by
        have h43 : (3 * (2 : ℝ)^sigma) ^ (-1 : ℝ) = 1 / (3 * (2 : ℝ)^sigma) := by
          rw [Real.rpow_neg h5.le] <;> simp
        exact h43.symm
      rw [h42, ← Real.rpow_mul h5.le]
      have h44 : (-1 : ℝ) * (1 / (outputLoss - sigma)) = -(1 / (outputLoss - sigma)) := by ring
      rw [h44, Real.rpow_neg h5.le] <;> simp
    have h4 : 1 / ((1 / (3 * (2 : ℝ)^sigma)) ^ (1 / (outputLoss - sigma))) =
        (3 * (2 : ℝ)^sigma) ^ (1 / (outputLoss - sigma)) := by
      rw [h41]
      have h6 : 0 < (3 * (2 : ℝ)^sigma) ^ (1 / (outputLoss - sigma)) := by positivity
      field_simp [h6.ne']
    rw [h4] at h3
    have h6 : (1 / delta_n)^(outputLoss - sigma) ≥
        ((3 * (2 : ℝ)^sigma) ^ (1 / (outputLoss - sigma)))^(outputLoss - sigma) := by
      gcongr
    have h7 : ((3 * (2 : ℝ)^sigma) ^ (1 / (outputLoss - sigma)))^(outputLoss - sigma) =
        3 * (2 : ℝ)^sigma := by
      rw [← Real.rpow_mul (by positivity)]
      have h8 : (1 / (outputLoss - sigma)) * (outputLoss - sigma) = 1 := by
        field_simp [houtputLoss_minus_sigma_pos.ne'] <;> ring
      rw [h8]
      simp
    rw [h7] at h6
    exact h6

  -- Step 2: Apply direction bin grain configuration
  have hconfig : Nonempty (PureWZ2GrainConfiguration sigma outputLoss delta_n) :=
    direction_bin_grain_config
      (hsigma_pos := hsigma_pos)
      (hsigma_lt_one := hsigma_lt_one)
      (houtputLoss_gt_one := houtputLoss_gt_one)
      (hdelta_pos := hdelta_n_pos)
      (hdelta_lt_one := hdelta_n_lt_one)
      (hloss_src_lt := hloss_src_lt)
      (h_absorb := h_absorb)
      (hsmall_global := hsmall_global)
      (line_class := line_class)
      (cubical := cubical)
      (extremal_src := extremal)
      (top_cwa_src := top_level_cwa)

  -- Step 3: Return
  exact ⟨delta_n, hdelta_n_pos, hdelta_n_le.trans hdelta₀'_le, hconfig⟩

end Kakeya.Assouad

end
