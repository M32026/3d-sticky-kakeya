module

/-
# Helper4 → Helper5 Density Bridge Algebra

## The key calculation

Helper4 outputs graph density:
```
Nplane(Gamma) ≥ (c_dense_H4 / 4) * N(S1) * N(S2)
```
where `c_dense_H4 = ENNReal.ofReal (δ^D)` and
`D = 3·ρ_sel + 2·ρ_sep + qAbsorb + L·η_work`.

Helper5 requires:
```
Nplane(Gamma) ≥ ENNReal.ofReal c_dense_real * N(S1) * N(S2)
```
with `hc_dense_ge : c_dense_real ≥ δ^(q_K)`.

## Setting c_dense_real

Set `c_dense_real := δ^D / 4`. Then Helper4's output directly implies
Helper5's density input (up to ENNReal/ℝ conversion).

The remaining condition is Helper5's `hc_dense_ge`:
```
δ^D / 4 ≥ δ^(q_K)
```
Since `0 < δ < 1`, this is equivalent to:
```
δ^(q_K - D) ≤ 1/4
```

## V4 budget: q_K := qKV4

In the V4 integration, Helper5 is called with `q_K := qKV4`.

From WireBudgetsV4:
- `qKV4 = qK + qDensityV4`
- `qDensityV4 = 3·ρ_sel + 2·ρ_sep + qAbsorb`
- `qK = (L+2)·η + qProjective`

Therefore:
```
qKV4 - D
= (qK + qDensityV4) - (qDensityV4 + L·η)
= qK - L·η
= (L+2)·η + qProjective - L·η
= 2·η + qProjective
```

## Absorption condition

The exact condition is:
```
δ^(2·η_work + qProjective) ≤ 1/4
```

Since `2·η_work + qProjective > 0` (both terms positive), this holds for
sufficiently small δ. The V4 budget feasibility provides this smallness.

Note: `2·η + qProjective` is much larger than `qAbsorb = η/100`, so the
absorption has substantial slack.

## ENNReal conversion

Helper4's `c_dense_H4 : ENNReal` must be converted to a real. Since
`c_dense_H4 = ENNReal.ofReal (δ^D)` and `δ^D > 0`, we have
`(c_dense_H4 / 4).toReal = δ^D / 4`.

The bridge lemma below formalizes this.
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeSetBasics
public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV4
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Real

namespace ProductLikeIncidence.ProductReduction

/-- Density bridge: Helper4 output implies Helper5 density input.

Given Helper4's density at exponent D, produce `c_dense_real` satisfying
Helper5's requirement `c_dense_real ≥ δ^(q_K)`.

**Absorption condition:** `δ^(q_K - D) ≤ 1/4`.

In the V4 integration with `q_K := qKV4` and
`D = 3ρ_sel + 2ρ_sep + qAbsorb + L·η`, this becomes
`δ^(2η + qProjective) ≤ 1/4`. -/
lemma density_bridge_helper4_to_helper5
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    {D q_K : ℝ} (h_absorb : δ ^ (q_K - D) ≤ 1 / 4)
    {S1 S2 : Set ℝ}
    {Gamma : Set (EuclideanSpace ℝ (Fin 2))}
    -- Helper4 output
    (hGamma_density_H4 : ENat.toENNReal (dyadicCoveringNumber δ Gamma) ≥
        (ENNReal.ofReal (δ ^ D) / 4) * Nreal δ S1 * Nreal δ S2) :
    ∃ (c_dense_real : ℝ),
      0 < c_dense_real ∧
      c_dense_real ≥ δ ^ q_K ∧
      ENat.toENNReal (dyadicCoveringNumber δ Gamma) ≥
        ENNReal.ofReal c_dense_real * Nreal δ S1 * Nreal δ S2 := by
  set c_dense_real : ℝ := δ ^ D / 4 with hc_def
  have h_pos : 0 < δ ^ D := by positivity
  have h_cpos : 0 < c_dense_real := by
    rw [hc_def] <;> positivity
  have h_ge : c_dense_real ≥ δ ^ q_K := by
    rw [hc_def]
    have h1 : δ ^ D / 4 ≥ δ ^ q_K := by
      have h2 : δ ^ (q_K - D) ≤ 1 / 4 := h_absorb
      have h3 : δ ^ D > 0 := h_pos
      have h4 : δ ^ q_K = δ ^ D * δ ^ (q_K - D) := by
        have h5 : q_K = D + (q_K - D) := by ring
        rw [h5]
        rw [Real.rpow_add hδ_pos] <;> ring_nf
      rw [h4]
      have h6 : δ ^ D * δ ^ (q_K - D) ≤ δ ^ D * (1 / 4) := by
        gcongr
      linarith
    exact h1
  have h_density : ENat.toENNReal (dyadicCoveringNumber δ Gamma) ≥
      ENNReal.ofReal c_dense_real * Nreal δ S1 * Nreal δ S2 := by
    have h7 : ENNReal.ofReal c_dense_real = ENNReal.ofReal (δ ^ D) / 4 := by
      rw [hc_def]
      have h8 : ENNReal.ofReal (δ ^ D / 4) =
          ENNReal.ofReal (δ ^ D) / ENNReal.ofReal (4 : ℝ) :=
        ENNReal.ofReal_div_of_pos (by norm_num)
      rw [h8]
      <;> norm_cast
    rw [h7]
    exact hGamma_density_H4
  exact ⟨c_dense_real, h_cpos, h_ge, h_density⟩

/-- **Direct sumset algebra**: Combine a third-projection bound with a product
bound to get Helper5's `h_sumset` format.

This is the **direct route** (no capture lemma needed):

Given:
- `N(sum Γ) ≤ 3·δ^{-(Lη)}·√N(Pbar_param)`
- `N(Pbar_param) ≤ C_P2S · N(S1) · N(S2)`

Conclude:
`N(sum Γ) ≤ 3·√C_P2S·δ^{-(Lη)}·√(N(S1)·N(S2))`

All quantities are converted to real for the square-root step, then back to ENNReal. -/
lemma sumset_bridge_algebra
    {δ L_exp η : ℝ}
    (hδ_pos : 0 < δ)
    {Pbar : Set (EuclideanSpace ℝ (Fin 2))}
    {S1 S2 : Set ℝ}
    {Gamma : Set (EuclideanSpace ℝ (Fin 2))}
    (hPbar_ne_top : Nplane δ Pbar ≠ ⊤)
    (hS1_ne_top : Nreal δ S1 ≠ ⊤)
    (hS2_ne_top : Nreal δ S2 ≠ ⊤)
    {C_P2S : ℝ}
    (hC_P2S_pos : 0 < C_P2S)
    -- Helper4 bound
    (h_third : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) Gamma) ≤
        (3 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar).toReal)))
    -- Product bound in ENNReal
    (h_prod : Nplane δ Pbar ≤ ENNReal.ofReal C_P2S * Nreal δ S1 * Nreal δ S2) :
    Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) Gamma) ≤
      (3 : ENNReal) * ENNReal.ofReal (Real.sqrt C_P2S * δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((Nreal δ S1).toReal * (Nreal δ S2).toReal)) := by
  set A : ℝ := (Nplane δ Pbar).toReal
  set B : ℝ := (Nreal δ S1).toReal
  set C : ℝ := (Nreal δ S2).toReal
  have hB_nonneg : 0 ≤ B := by positivity
  have hC_nonneg : 0 ≤ C := by positivity
  have h_rhs_ne_top : ENNReal.ofReal C_P2S * Nreal δ S1 * Nreal δ S2 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS1_ne_top) hS2_ne_top
  have h4 : A ≤ C_P2S * B * C := by
    have h5 := ENNReal.toReal_mono h_rhs_ne_top h_prod
    have h6 : (ENNReal.ofReal C_P2S * Nreal δ S1 * Nreal δ S2).toReal = C_P2S * B * C := by
      simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC_P2S_pos.le] <;> ring
    rw [h6] at h5
    exact h5
  have h7 : Real.sqrt A ≤ Real.sqrt C_P2S * Real.sqrt (B * C) := by
    have h8 : Real.sqrt A ≤ Real.sqrt (C_P2S * B * C) := Real.sqrt_le_sqrt h4
    have h91 : 0 ≤ C_P2S * B := by positivity
    have h92 : Real.sqrt (C_P2S * B * C) = Real.sqrt (C_P2S * B) * Real.sqrt C := by
      rw [Real.sqrt_mul] <;> positivity
    have h93 : Real.sqrt (C_P2S * B) = Real.sqrt C_P2S * Real.sqrt B := by
      rw [Real.sqrt_mul] <;> positivity
    have h9 : Real.sqrt (C_P2S * B * C) = Real.sqrt C_P2S * Real.sqrt (B * C) := by
      have h95 : C_P2S * B * C = C_P2S * (B * C) := by ring
      rw [h95]
      rw [Real.sqrt_mul] <;> positivity
    rw [h9] at h8
    exact h8
  have h11 : (3 : ℝ) * δ ^ (-(L_exp * η)) * Real.sqrt A ≤
      (3 : ℝ) * Real.sqrt C_P2S * δ ^ (-(L_exp * η)) * Real.sqrt (B * C) := by
    calc
      (3 : ℝ) * δ ^ (-(L_exp * η)) * Real.sqrt A
        ≤ (3 : ℝ) * δ ^ (-(L_exp * η)) * (Real.sqrt C_P2S * Real.sqrt (B * C)) := by gcongr
      _ = (3 : ℝ) * Real.sqrt C_P2S * δ ^ (-(L_exp * η)) * Real.sqrt (B * C) := by ring
  have h15 : (3 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt A) =
      ENNReal.ofReal ((3 : ℝ) * δ ^ (-(L_exp * η)) * Real.sqrt A) := by
    have h151 : (3 : ENNReal) = ENNReal.ofReal (3 : ℝ) := by simp
    rw [h151]
    have h_pos3 : 0 ≤ (3 : ℝ) := by positivity
    have h_posd : 0 ≤ δ ^ (-(L_exp * η)) := by positivity
    have h_posA : 0 ≤ Real.sqrt A := by positivity
    have h_step1 : ENNReal.ofReal (3 : ℝ) * ENNReal.ofReal (δ ^ (-(L_exp * η))) =
        ENNReal.ofReal ((3 : ℝ) * δ ^ (-(L_exp * η))) :=
      Eq.symm (ENNReal.ofReal_mul (hp := h_pos3))
    have h_step2 : ENNReal.ofReal ((3 : ℝ) * δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt A) =
        ENNReal.ofReal (((3 : ℝ) * δ ^ (-(L_exp * η))) * Real.sqrt A) :=
      Eq.symm (ENNReal.ofReal_mul (hp := by positivity))
    rw [h_step1, h_step2]
    <;> rfl
  have h16 : (3 : ENNReal) * ENNReal.ofReal (Real.sqrt C_P2S * δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt (B * C)) =
      ENNReal.ofReal ((3 : ℝ) * Real.sqrt C_P2S * δ ^ (-(L_exp * η)) * Real.sqrt (B * C)) := by
    have h161 : (3 : ENNReal) = ENNReal.ofReal (3 : ℝ) := by simp
    rw [h161]
    have h_pos1 : 0 ≤ (3 : ℝ) := by positivity
    have h_pos2 : 0 ≤ Real.sqrt C_P2S * δ ^ (-(L_exp * η)) := by positivity
    have h_pos3 : 0 ≤ Real.sqrt (B * C) := by positivity
    have h_step1 : ENNReal.ofReal (3 : ℝ) * ENNReal.ofReal (Real.sqrt C_P2S * δ ^ (-(L_exp * η))) =
        ENNReal.ofReal ((3 : ℝ) * (Real.sqrt C_P2S * δ ^ (-(L_exp * η)))) :=
      Eq.symm (ENNReal.ofReal_mul (hp := h_pos1))
    have h_step2 : ENNReal.ofReal ((3 : ℝ) * (Real.sqrt C_P2S * δ ^ (-(L_exp * η)))) *
          ENNReal.ofReal (Real.sqrt (B * C)) =
        ENNReal.ofReal (((3 : ℝ) * (Real.sqrt C_P2S * δ ^ (-(L_exp * η)))) * Real.sqrt (B * C)) :=
      Eq.symm (ENNReal.ofReal_mul (hp := by positivity))
    rw [h_step1, h_step2]
    congr 1
    ring
  have h14 : (3 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt A) ≤
      (3 : ENNReal) * ENNReal.ofReal (Real.sqrt C_P2S * δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt (B * C)) := by
    rw [h15, h16]
    exact ENNReal.ofReal_le_ofReal h11
  have h_final : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) Gamma) ≤
      (3 : ENNReal) * ENNReal.ofReal (Real.sqrt C_P2S * δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt (B * C)) :=
    le_trans h_third h14
  simpa [B, C] using h_final

end ProductLikeIncidence.ProductReduction

/-!
## Missing Inputs Audit: Helper5 vs `incidence_to_ring_contradiction`

Helper5 (`bsg_extraction_helper`) requires ~40 inputs. Here is their
availability from the main theorem signature and upstream helpers.

### Directly available from `incidence_to_ring_contradiction` hypotheses

| Input | Source |
|-------|--------|
| δ, s, τ, κ0, η, η_work, ε, L_exp, p_projective | direct params |
| hδ_pos, hδ_dyadic, hδ_lt_one (from δ≤1 + C_work) | direct |
| hs_pos, hs_lt_one, hτ_pos, hκ0_pos, hκ0_lt_s | direct |
| hη_pos, hη_work_pos, hη_work_eq_two | direct |
| hL_exp_pos, hL_exp_eq_seven | direct |
| C, C_work, K_ring, K_diff, εnc, εgain | direct params |
| hC_ge1, hC_work_eq, hC_work_le | direct |
| Y, X, P, hY_sub, hY_delta, hXy_delta | direct |
| hP_bdd, h_fiber, hP_small | direct |
| Zf, Pz, P_cubes_fin, hZf, hPz, hP_cubes | direct |
| h_energy | direct |
| h_ring_spec | direct |
| rho_sel, rho_sep, hrho_sel_eq, hrho_sep_le | direct |
| h_frostman_gap | direct |
| h_KBSG_absorb, h_sumset_absorb, h_c_dense_exp_le | direct |
| h_extract_log_absorb, h_qTotalV4_le_enc4, h_qbox_lt_one | direct |

### Available from Helper0 (Phase0) output

| Input | Source |
|-------|--------|
| Pbar_param, Tbar, T_y_points | phase0_result_helper |
| C_work' (= 35*C), c_mult, C_Pbar, R, k_R | phase0_result_helper |
| Pz_trim, U_y | phase0_result_helper |
| 4*R ≤ δ^(-qBox) | phase0_result_helper |

### Available from Helper3 (Projective Normalization) output

| Input | Source |
|-------|--------|
| S1, S2 (rounded coordinate sets) | projective_normalization_helper |
| E3', E3'', round_fun | projective_normalization_helper |
| hS1_delta, hS2_delta (with C_extract) | projective_normalization_helper |
| hS1_grid, hS2_grid, hS1_sep, hS2_sep | projective_normalization_helper |
| hS1_finite, hS2_finite, hS1_nonempty, hS2_nonempty | projective_normalization_helper |
| hE3'_finite, hE3'_sub_Pbar | projective_normalization_helper |
| hE3''_sub, hE3''_half | projective_normalization_helper |
| hE3''_round, hE3''_mass | projective_normalization_helper |
| h_proj_x, h_proj_y, hS1_bound, hS2_bound | projective_normalization_helper |
| h_third_proj_E3' | projective_normalization_helper |
| h_occupancy (with M_G_real) | projective_normalization_helper |
| μE3' (IsProbabilityMeasure) | projective_normalization_helper |

### Available from Helper4 (Dense Graph) output

| Input | Source |
|-------|--------|
| Gamma | dense_graph_helper |
| hGamma_sub, hGamma_grid, hGamma_fin, hGamma_nonempty | dense_graph_helper |
| hGamma_density (c_dense/4 format) | dense_graph_helper |
| h_sumset (Pbar format) | dense_graph_helper |
| hGamma_witness, hGamma_separated | dense_graph_helper |

### Constructed via H4→H5 bridges (this file)

| Input | Bridge |
|-------|--------|
| c_dense_real (≥ δ^q_K) | density_bridge_helper4_to_helper5 |
| C_sum (≤ δ^(-q_K)) | bridge_sumset_h4_to_h5 |
| hGamma_dense in ofReal format | density_bridge_helper4_to_helper5 |
| h_sumset in sqrt(N1*N2) format | bridge_sumset_h4_to_h5 |

### Still need construction / upstream results

| Input | Status | Needed from |
|-------|--------|-------------|
| C_A (= C_extract) | **naming** | `let C_A := C_extract` in glue |
| q_K, qKA, qAbsorb, q_input, qSizeLossV3, qDiffV3, θ_num | **budget** | WireBudgetsV3/V4 definitions |
| K_A comparability (hS1_le_S2, hS2_le_S1) | **gap** | Phase3 size window + K_A_Wrapper |
| hK_A_le (K_A ≤ δ^(-qKA)) | **gap** | Phase3 size window calibration |
| hS1_lower, hS2_lower (|S_i| ≥ δ^(-s+q_input)) | **gap** | Energy lower bound + mass retention |
| hc_dense_real_ge (c_dense.toReal/8 ≥ δ^q_K) | **bridge** | density_bridge_with_constant_absorption (this file) |
| hC_sum_le (C_sum ≤ δ^(-q_K)) | **gap** | h_sumset_absorb condition from outer δ₀ |
| h_absorb_ret, h_absorb_KBSG, h_absorb_size | **available** | Direct from incidence_to_ring_contradiction |
| h_capture (N(E') ≥ 1/2 δ^η N(Pbar)) | **gap** | Phase3 size window capture lemma |
| h_trivial_product (N(E') ≤ C_triv N1 N2) | **gap** | Trivial product covering bound |
| C_triv (constant for trivial product) | **gap** | Construct from geometry |
| R_norm, hR_norm_pos, hR_norm_int | **gap** | From Pbar_param boundedness + grid |
| hS1_bdd, hS2_bdd (|x| ≤ R_norm+1) | **gap** | From S1,S2 ⊆ rounded E3' coordinates |
| hN1_top, hN2_top (Nreal ≠ ⊤) | **trivial** | S1,S2 finite → Nreal finite |

### Summary

- **~18 inputs** directly from main theorem
- **~14 inputs** from Helper3 output
- **~8 inputs** from Helper4 output
- **4 inputs** constructed via H4→H5 bridges (this file)
- **~10 inputs** still need upstream construction (K_A comparability,
  size lower bounds, capture/trivial product, R_norm, budget calibration)
-/
