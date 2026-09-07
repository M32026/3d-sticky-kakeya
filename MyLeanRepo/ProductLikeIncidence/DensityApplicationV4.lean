module

/-
# Density Application V4

Concrete density application lemmas for the V4 corrected budgets.
Uses M_G bounds from angle separation (ρ_sep) and absorbs fixed constants
into δ-powers.

## Main results
- `M_G_bound_rho_sep_direct`: M_G ≤ 1024·δ^{-2ρ_sep}
- `M_G_bound_rho_sep_absorbed`: M_G ≤ δ^{-(2ρ_sep+qAbsorb)}
- `density_prefactor_absorption_v4`: absorbs M_G + fixed constants
- `density_lower_bound_with_absorption_v4`: full density lower bound

## Whiteprint node
Density application for `incidence_to_ring_contradiction` V4 correction.
-/

public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV3
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV4
public import MyLeanRepo.ProductLikeIncidence.ProductDensityFromThreefold
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open ENNReal

namespace ProductLikeIncidence.ProductReduction

/-! ## M_G bound with ρ_sep -/

lemma M_G_bound_rho_sep_direct
    {δ rho_sep : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hrho_sep_pos : 0 < rho_sep)
    (C_inv : ℝ) (hC_inv_nonneg : 0 ≤ C_inv)
    (hC_inv : C_inv ≤ 4 * Real.sqrt 2 * δ ^ (-rho_sep))
    (h_small : δ ^ rho_sep ≤ 8 / 3) :
    (2 * C_inv * Real.sqrt 2 + 6) ^ 2 ≤ 1024 * δ ^ (-2 * rho_sep) := by
  have h_sqrt2_sq : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    have h : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h2 : Real.sqrt 2 * Real.sqrt 2 = (Real.sqrt 2) ^ 2 := by ring
    rw [h2]; exact h
  have h1 : 2 * C_inv * Real.sqrt 2 ≤ 16 * δ ^ (-rho_sep) := by
    have h1a : 2 * C_inv * Real.sqrt 2 ≤ 2 * (4 * Real.sqrt 2 * δ ^ (-rho_sep)) * Real.sqrt 2 := by gcongr
    have h1b : 2 * (4 * Real.sqrt 2 * δ ^ (-rho_sep)) * Real.sqrt 2 = 16 * δ ^ (-rho_sep) := by
      have h : 2 * (4 * Real.sqrt 2 * δ ^ (-rho_sep)) * Real.sqrt 2 =
          (2 * 4) * (Real.sqrt 2 * Real.sqrt 2) * δ ^ (-rho_sep) := by ring
      rw [h, h_sqrt2_sq] <;> ring
    rw [h1b] at h1a; exact h1a
  have h3 : 6 ≤ 16 * δ ^ (-rho_sep) := by
    have h4 : δ ^ (-rho_sep) = (δ ^ rho_sep)⁻¹ := by
      rw [Real.rpow_neg hδ_pos.le] <;> ring
    rw [h4]
    have h5 : 0 < δ ^ rho_sep := by positivity
    have h6 : (δ ^ rho_sep)⁻¹ ≥ 3 / 8 := by
      have h7 : δ ^ rho_sep ≤ 8 / 3 := h_small
      have h8 : (δ ^ rho_sep)⁻¹ ≥ (8 / 3 : ℝ)⁻¹ := by gcongr
      have h9 : (8 / 3 : ℝ)⁻¹ = 3 / 8 := by norm_num
      rw [h9] at h8; exact h8
    have h10 : 16 * (δ ^ rho_sep)⁻¹ ≥ 16 * (3 / 8 : ℝ) := by gcongr
    have h11 : 16 * (3 / 8 : ℝ) = 6 := by norm_num
    rw [h11] at h10; exact h10
  have h6 : 2 * C_inv * Real.sqrt 2 + 6 ≤ 32 * δ ^ (-rho_sep) := by linarith
  have h7 : 0 ≤ 2 * C_inv * Real.sqrt 2 + 6 := by positivity
  have h8 : (2 * C_inv * Real.sqrt 2 + 6) ^ 2 ≤ (32 * δ ^ (-rho_sep)) ^ 2 := by gcongr
  have h9 : (32 * δ ^ (-rho_sep)) ^ 2 = 1024 * δ ^ (-2 * rho_sep) := by
    have h10 : δ ^ (-rho_sep) * δ ^ (-rho_sep) = δ ^ (-2 * rho_sep) := by
      rw [← Real.rpow_add hδ_pos] <;> ring_nf
    nlinarith
  rw [h9] at h8; exact h8

lemma M_G_bound_rho_sep_absorbed
    {δ rho_sep qAbsorb_val : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hrho_sep_pos : 0 < rho_sep)
    (hqAbsorb_pos : 0 < qAbsorb_val)
    (C_inv : ℝ) (hC_inv_nonneg : 0 ≤ C_inv)
    (hC_inv : C_inv ≤ 4 * Real.sqrt 2 * δ ^ (-rho_sep))
    (h_small1 : δ ^ rho_sep ≤ 8 / 3)
    (h_small2 : δ ^ qAbsorb_val ≤ 1 / 1024) :
    (2 * C_inv * Real.sqrt 2 + 6) ^ 2 ≤
      δ ^ (-(2 * rho_sep + qAbsorb_val)) := by
  have h1 : (2 * C_inv * Real.sqrt 2 + 6) ^ 2 ≤ 1024 * δ ^ (-2 * rho_sep) :=
    M_G_bound_rho_sep_direct hδ_pos hδ_lt_one hrho_sep_pos C_inv hC_inv_nonneg hC_inv h_small1
  have h2 : 1024 * δ ^ (-2 * rho_sep) ≤ δ ^ (-(2 * rho_sep + qAbsorb_val)) := by
    have h3 : δ ^ (-(2 * rho_sep + qAbsorb_val)) = δ ^ (-2 * rho_sep) * δ ^ (-qAbsorb_val) := by
      rw [← Real.rpow_add hδ_pos] <;> ring_nf
    rw [h3]
    have h4 : 1024 ≤ δ ^ (-qAbsorb_val) := by
      have h5 : δ ^ (-qAbsorb_val) = (δ ^ qAbsorb_val)⁻¹ := by
        rw [Real.rpow_neg hδ_pos.le] <;> ring
      rw [h5]
      have h6 : 0 < δ ^ qAbsorb_val := by positivity
      have h7 : (δ ^ qAbsorb_val)⁻¹ ≥ 1024 := by
        have h8 : δ ^ qAbsorb_val ≤ 1 / 1024 := h_small2
        have h9 : (δ ^ qAbsorb_val)⁻¹ ≥ (1 / 1024 : ℝ)⁻¹ := by gcongr
        have h10 : (1 / 1024 : ℝ)⁻¹ = 1024 := by norm_num
        rw [h10] at h9; exact h9
      exact h7
    have h7 : 0 ≤ δ ^ (-2 * rho_sep) := by positivity
    nlinarith
  exact le_trans h1 h2

/-! ## Density prefactor absorption -/

lemma density_prefactor_absorption_v4
    {δ η rho_sep : ℝ}
    (hδ_pos : 0 < δ)
    (hη_pos : 0 < η)
    (hrho_sep_nonneg : 0 ≤ rho_sep)
    {C_fixed C1_real C2_real : ℝ}
    (hC_fixed_pos : 0 < C_fixed)
    (hC1_pos : 0 < C1_real)
    (hC2_pos : 0 < C2_real)
    {M_G_real : ℝ}
    (hM_G_pos : 0 < M_G_real)
    (hM_G_bound : M_G_real ≤ C_fixed * δ ^ (-2 * rho_sep))
    (hδ_small : δ ^ qAbsorb η ≤ 1 / (2 * C_fixed * C1_real * C2_real)) :
    (1 / 2 : ENNReal) / ENNReal.ofReal M_G_real / ENNReal.ofReal C1_real / ENNReal.ofReal C2_real ≥
      ENNReal.ofReal (δ ^ (2 * rho_sep + qAbsorb η)) := by
  have hqAbsorb_pos : 0 < qAbsorb η := by dsimp only [qAbsorb]; positivity
  have h_inv_bound : (M_G_real)⁻¹ ≥ (δ ^ (2 * rho_sep)) / C_fixed := by
    have h1 : 0 < C_fixed * δ ^ (-2 * rho_sep) := by positivity
    have h2 : M_G_real ≤ C_fixed * δ ^ (-2 * rho_sep) := hM_G_bound
    have h3 : (M_G_real)⁻¹ ≥ (C_fixed * δ ^ (-2 * rho_sep))⁻¹ := by gcongr
    have h41 : δ ^ (-2 * rho_sep) = (δ ^ (2 * rho_sep))⁻¹ := by
      have h_nonneg : 0 ≤ 2 * rho_sep := by positivity
      simpa [h_nonneg] using Real.rpow_neg hδ_pos.le (2 * rho_sep)
    have h4 : (C_fixed * δ ^ (-2 * rho_sep))⁻¹ = (δ ^ (2 * rho_sep)) / C_fixed := by
      rw [h41]; field_simp [hC_fixed_pos.ne'] <;> ring
    rw [h4] at h3; exact h3
  have h_main_real : (1 / 2 : ℝ) / M_G_real / C1_real / C2_real ≥
      δ ^ (2 * rho_sep + qAbsorb η) := by
    have h5 : (1 / 2 : ℝ) / M_G_real / C1_real / C2_real =
        (1 / 2 : ℝ) * (M_G_real)⁻¹ * (C1_real)⁻¹ * (C2_real)⁻¹ := by
      field_simp [hM_G_pos.ne', hC1_pos.ne', hC2_pos.ne'] <;> ring
    rw [h5]
    have h6 : (1 / 2 : ℝ) * (M_G_real)⁻¹ * (C1_real)⁻¹ * (C2_real)⁻¹ ≥
        (1 / 2 : ℝ) * ((δ ^ (2 * rho_sep)) / C_fixed) * (C1_real)⁻¹ * (C2_real)⁻¹ := by gcongr
    have h7 : (1 / 2 : ℝ) * ((δ ^ (2 * rho_sep)) / C_fixed) * (C1_real)⁻¹ * (C2_real)⁻¹ =
        δ ^ (2 * rho_sep) / (2 * C_fixed * C1_real * C2_real) := by
      field_simp [hC_fixed_pos.ne', hC1_pos.ne', hC2_pos.ne'] <;> ring
    rw [h7] at h6
    have h9 : 1 / (2 * C_fixed * C1_real * C2_real) ≥ δ ^ (qAbsorb η) := hδ_small
    have h10 : 0 ≤ δ ^ (2 * rho_sep) := by positivity
    have h11 : δ ^ (2 * rho_sep) * (1 / (2 * C_fixed * C1_real * C2_real)) ≥
        δ ^ (2 * rho_sep) * δ ^ (qAbsorb η) := mul_le_mul_of_nonneg_left h9 h10
    have h12 : δ ^ (2 * rho_sep) / (2 * C_fixed * C1_real * C2_real) =
        δ ^ (2 * rho_sep) * (1 / (2 * C_fixed * C1_real * C2_real)) := by
      field_simp [hC_fixed_pos.ne', hC1_pos.ne', hC2_pos.ne'] <;> ring
    have h13 : δ ^ (2 * rho_sep) * δ ^ (qAbsorb η) = δ ^ (2 * rho_sep + qAbsorb η) := by
      rw [← Real.rpow_add hδ_pos] <;> ring
    have h14 : (1 / 2 : ℝ) * (M_G_real)⁻¹ * (C1_real)⁻¹ * (C2_real)⁻¹ ≥
        δ ^ (2 * rho_sep) * (1 / (2 * C_fixed * C1_real * C2_real)) := by
      calc (1 / 2 : ℝ) * (M_G_real)⁻¹ * (C1_real)⁻¹ * (C2_real)⁻¹
        ≥ δ ^ (2 * rho_sep) / (2 * C_fixed * C1_real * C2_real) := h6
      _ = δ ^ (2 * rho_sep) * (1 / (2 * C_fixed * C1_real * C2_real)) := h12
    have h15 : δ ^ (2 * rho_sep) * (1 / (2 * C_fixed * C1_real * C2_real)) ≥
        δ ^ (2 * rho_sep + qAbsorb η) := by
      calc δ ^ (2 * rho_sep) * (1 / (2 * C_fixed * C1_real * C2_real))
        ≥ δ ^ (2 * rho_sep) * δ ^ (qAbsorb η) := h11
      _ = δ ^ (2 * rho_sep + qAbsorb η) := h13
    exact ge_trans h14 h15
  have h_ennreal_eq : ((1 / 2 : ENNReal) / ENNReal.ofReal M_G_real / ENNReal.ofReal C1_real / ENNReal.ofReal C2_real) =
      ENNReal.ofReal ((1 / 2 : ℝ) / M_G_real / C1_real / C2_real) := by
    have h_pos_all : 0 < (1 / 2 : ℝ) * M_G_real⁻¹ * C1_real⁻¹ * C2_real⁻¹ := by positivity
    have h_eq_real : (1 / 2 : ℝ) * M_G_real⁻¹ * C1_real⁻¹ * C2_real⁻¹ = (1 / 2 : ℝ) / M_G_real / C1_real / C2_real := by
      field_simp [hM_G_pos.ne', hC1_pos.ne', hC2_pos.ne']
    have h_step1 : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by simp
    have h_step2 : ∀ (x : ℝ), 0 < x → (ENNReal.ofReal x)⁻¹ = ENNReal.ofReal (x⁻¹) := by
      intro x hx; exact (ENNReal.ofReal_inv_of_pos hx).symm
    have h_div_eq : ((1 / 2 : ENNReal) / ENNReal.ofReal M_G_real / ENNReal.ofReal C1_real / ENNReal.ofReal C2_real) =
        (1 / 2 : ENNReal) * (ENNReal.ofReal M_G_real)⁻¹ * (ENNReal.ofReal C1_real)⁻¹ * (ENNReal.ofReal C2_real)⁻¹ := by
      simp only [div_eq_mul_inv]
    calc ((1 / 2 : ENNReal) / ENNReal.ofReal M_G_real / ENNReal.ofReal C1_real / ENNReal.ofReal C2_real)
      = (1 / 2 : ENNReal) * (ENNReal.ofReal M_G_real)⁻¹ * (ENNReal.ofReal C1_real)⁻¹ * (ENNReal.ofReal C2_real)⁻¹ := h_div_eq
    _ = ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (M_G_real⁻¹) * ENNReal.ofReal (C1_real⁻¹) * ENNReal.ofReal (C2_real⁻¹) := by
        rw [h_step1, h_step2 M_G_real hM_G_pos, h_step2 C1_real hC1_pos, h_step2 C2_real hC2_pos]
    _ = ENNReal.ofReal ((1 / 2 : ℝ) * M_G_real⁻¹ * C1_real⁻¹ * C2_real⁻¹) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal ((1 / 2 : ℝ) / M_G_real / C1_real / C2_real) := by rw [h_eq_real]
  rw [h_ennreal_eq]
  exact ENNReal.ofReal_le_ofReal h_main_real

lemma density_lower_bound_with_absorption_v4
    {δ η L_exp rho_sel rho_sep : ℝ}
    (hδ_pos : 0 < δ)
    (hη_pos : 0 < η)
    (hrho_sep_nonneg : 0 ≤ rho_sep)
    {C_fixed C1_real C2_real : ℝ}
    (hC_fixed_pos : 0 < C_fixed)
    (hC1_pos : 0 < C1_real)
    (hC2_pos : 0 < C2_real)
    {M_G_real : ℝ}
    (hM_G_pos : 0 < M_G_real)
    (hM_G_bound : M_G_real ≤ C_fixed * δ ^ (-2 * rho_sep))
    (hδ_small : δ ^ qAbsorb η ≤ 1 / (2 * C_fixed * C1_real * C2_real))
    {E' : Set (EuclideanSpace ℝ (Fin 2))}
    {S1 S2 : Set ℝ}
    (h_density_raw :
      ENat.toENNReal (dyadicCoveringNumber δ E') ≥
        (1 / 2 : ENNReal) / ENNReal.ofReal M_G_real / ENNReal.ofReal C1_real / ENNReal.ofReal C2_real *
        ENNReal.ofReal (δ ^ (3 * rho_sel + L_exp * η)) *
        Nreal δ S1 * Nreal δ S2)
    (_hrho_sel_nonneg : 0 ≤ rho_sel)
    (_hL_exp_nonneg : 0 ≤ L_exp) :
    ENat.toENNReal (dyadicCoveringNumber δ E') ≥
      ENNReal.ofReal (δ ^ (3 * rho_sel + 2 * rho_sep + qAbsorb η + L_exp * η)) *
        Nreal δ S1 * Nreal δ S2 := by
  have h_absorb : (1 / 2 : ENNReal) / ENNReal.ofReal M_G_real / ENNReal.ofReal C1_real / ENNReal.ofReal C2_real ≥
      ENNReal.ofReal (δ ^ (2 * rho_sep + qAbsorb η)) :=
    density_prefactor_absorption_v4 hδ_pos hη_pos hrho_sep_nonneg
      hC_fixed_pos hC1_pos hC2_pos hM_G_pos hM_G_bound hδ_small
  have h_exp_add : δ ^ (2 * rho_sep + qAbsorb η) * δ ^ (3 * rho_sel + L_exp * η) =
      δ ^ (3 * rho_sel + 2 * rho_sep + qAbsorb η + L_exp * η) := by
    have h_exp_eq : (2 * rho_sep + qAbsorb η) + (3 * rho_sel + L_exp * η) =
        3 * rho_sel + 2 * rho_sep + qAbsorb η + L_exp * η := by ring
    rw [← Real.rpow_add hδ_pos, h_exp_eq]
  calc ENat.toENNReal (dyadicCoveringNumber δ E')
    ≥ (1 / 2 : ENNReal) / ENNReal.ofReal M_G_real / ENNReal.ofReal C1_real / ENNReal.ofReal C2_real *
        ENNReal.ofReal (δ ^ (3 * rho_sel + L_exp * η)) * Nreal δ S1 * Nreal δ S2 := h_density_raw
  _ ≥ ENNReal.ofReal (δ ^ (2 * rho_sep + qAbsorb η)) *
        ENNReal.ofReal (δ ^ (3 * rho_sel + L_exp * η)) * Nreal δ S1 * Nreal δ S2 := by gcongr
  _ = ENNReal.ofReal (δ ^ (3 * rho_sel + 2 * rho_sep + qAbsorb η + L_exp * η)) * Nreal δ S1 * Nreal δ S2 := by
      have h_mul : ENNReal.ofReal (δ ^ (2 * rho_sep + qAbsorb η)) * ENNReal.ofReal (δ ^ (3 * rho_sel + L_exp * η)) =
          ENNReal.ofReal (δ ^ (3 * rho_sel + 2 * rho_sep + qAbsorb η + L_exp * η)) := by
        rw [← ENNReal.ofReal_mul (by positivity), h_exp_add]
      rw [h_mul]

/-! ## hc_dense_ge bridge (uses c_dense_exp_le_qKV4 from WireBudgetsV4) -/

/-- **V4 hc_dense_ge bridge**: c_dense_real ≥ δ^{qKV4}.

Given `c_dense_real ≥ δ^{effective_exp}` where `effective_exp = 3ρ_sel + 2ρ_sep + qAbsorb + L·η`,
and `effective_exp ≤ qKV4` (slack `2η + qProjective > 0`), since `0 < δ < 1` we get
`δ^{effective_exp} ≥ δ^{qKV4}`, hence `c_dense_real ≥ δ^{qKV4}`. -/
lemma hc_dense_ge_v4
    {δ η L ε κ0 p_projective rho_sel rho_sep : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hη_pos : 0 < η) (hε_pos : 0 < ε) (hκ0_pos : 0 < κ0)
    (hp_pos : 0 < p_projective)
    (c_dense_real : ℝ)
    (h_c_dense_lower : c_dense_real ≥ δ ^ (3 * rho_sel + 2 * rho_sep + qAbsorb η + L * η)) :
    c_dense_real ≥ δ ^ (qKV4 L η ε κ0 p_projective rho_sel rho_sep) := by
  set eff_exp : ℝ := 3 * rho_sel + 2 * rho_sep + qAbsorb η + L * η with heff_def
  have h_exp_le : eff_exp ≤ qKV4 L η ε κ0 p_projective rho_sel rho_sep :=
    c_dense_exp_le_qKV4 hη_pos hε_pos hκ0_pos hp_pos
  have h1 : c_dense_real ≥ δ ^ eff_exp := h_c_dense_lower
  have h2 : δ ^ (qKV4 L η ε κ0 p_projective rho_sel rho_sep) ≤ δ ^ eff_exp :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h_exp_le
  exact le_trans h2 h1

/-! ## Generalized density wrapper with projection factors Kx, Ky -/

/-- Generalized product density from threefold selection with projection factors.

Like `product_density_from_threefold_direct`, but allows constant factors
`Kx`, `Ky` in the projection bounds.  The conclusion divides by `Kx * Ky`
in addition to `C1 * C2`.

This is needed when projective normalization introduces a factor `C_q0 ≤ 2`
in each coordinate projection.  Absorbing `C_q0` into `Kx`, `Ky` (rather
than into the exponent `η`) avoids the double-charge of `ρ_sel`.
-/
lemma product_density_from_threefold_direct_K
    {δ ε η : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hε_pos : 0 < ε) (hη_pos : 0 < η)
    {E E3 E' : Set (EuclideanSpace ℝ (Fin 2))}
    (hE3_finite : E3.Finite)
    (hE'_sub : E' ⊆ E3)
    (hE'_card_lower : ENat.toENNReal E'.encard ≥ ENat.toENNReal E3.encard / 2)
    {M_G C1 C2 Kx Ky : ENNReal}
    (hM_G_pos : M_G ≠ 0) (hM_G_top : M_G ≠ ⊤)
    (hC1_pos : C1 ≠ 0) (hC1_top : C1 ≠ ⊤)
    (hC2_pos : C2 ≠ 0) (hC2_top : C2 ≠ ⊤)
    (hKx_pos : Kx ≠ 0) (hKx_top : Kx ≠ ⊤)
    (hKy_pos : Ky ≠ 0) (hKy_top : Ky ≠ ⊤)
    (h_occupancy : ∀ (Q : Set (EuclideanSpace ℝ (Fin 2))),
      Q ∈ dyadicCubes 2 δ → ENat.toENNReal (E3 ∩ Q).encard ≤ M_G)
    (hE3_size : ENat.toENNReal E3.encard ≥
      ENNReal.ofReal (δ ^ (3 * ε)) * ENat.toENNReal (dyadicCoveringNumber δ E))
    (h_proj_x : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0) E3) ≤
      Kx * ENNReal.ofReal (δ ^ (-η)) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ E)).toReal)))
    (h_proj_y : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 1) E3) ≤
      Ky * ENNReal.ofReal (δ ^ (-η)) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ E)).toReal)))
    {S1 S2 : Set ℝ}
    (hS1_bound : Nreal δ S1 ≤ C1 * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0) E3))
    (hS2_bound : Nreal δ S2 ≤ C2 * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 1) E3)) :
    ENat.toENNReal (dyadicCoveringNumber δ E') ≥
      (1 / 2 : ENNReal) / M_G / C1 / C2 / Kx / Ky *
      ENNReal.ofReal (δ ^ (3 * ε + 2 * η)) *
        Nreal δ S1 * Nreal δ S2 := by
  let N_E : ENNReal := ENat.toENNReal (dyadicCoveringNumber δ E)
  let N3 : ENNReal := ENat.toENNReal E3.encard

  have hE'_fin : E'.Finite := Set.Finite.subset hE3_finite hE'_sub

  have h_occ_E' : ∀ (Q : Set (EuclideanSpace ℝ (Fin 2))),
      Q ∈ dyadicCubes 2 δ → ENat.toENNReal (E' ∩ Q).encard ≤ M_G := by
    intro Q hQ
    have h_sub : E' ∩ Q ⊆ E3 ∩ Q := by intro x hx; exact ⟨hE'_sub hx.1, hx.2⟩
    have h1 : (E' ∩ Q).encard ≤ (E3 ∩ Q).encard := Set.encard_mono h_sub
    have h2 : ENat.toENNReal (E' ∩ Q).encard ≤ ENat.toENNReal (E3 ∩ Q).encard := by gcongr
    exact le_trans h2 (h_occupancy Q hQ)

  have h_occ_bound : ENat.toENNReal E'.encard ≤
      M_G * ENat.toENNReal (dyadicCoveringNumber δ E') :=
    bounded_occupancy_to_covering hδ_pos hE'_fin h_occ_E'

  have h_Nplane_lower : ENat.toENNReal (dyadicCoveringNumber δ E') ≥
      ENat.toENNReal E'.encard / M_G := by
    calc ENat.toENNReal E'.encard / M_G
        ≤ (M_G * ENat.toENNReal (dyadicCoveringNumber δ E')) / M_G := by gcongr
    _ = ENat.toENNReal (dyadicCoveringNumber δ E') := by
      rw [mul_comm]; exact ENNReal.mul_div_cancel_right hM_G_pos hM_G_top

  have hS1_le : Nreal δ S1 ≤ C1 * Kx *
      ENNReal.ofReal (δ ^ (-η)) * ENNReal.ofReal (Real.sqrt (N_E.toReal)) := by
    calc Nreal δ S1
      ≤ C1 * Nreal δ (Set.image (fun p => p 0) E3) := hS1_bound
    _ ≤ C1 * (Kx * ENNReal.ofReal (δ ^ (-η)) * ENNReal.ofReal (Real.sqrt (N_E.toReal))) := by gcongr
    _ = C1 * Kx * ENNReal.ofReal (δ ^ (-η)) * ENNReal.ofReal (Real.sqrt (N_E.toReal)) := by
      simp [mul_assoc] <;> rfl

  have hS2_le : Nreal δ S2 ≤ C2 * Ky *
      ENNReal.ofReal (δ ^ (-η)) * ENNReal.ofReal (Real.sqrt (N_E.toReal)) := by
    calc Nreal δ S2
      ≤ C2 * Nreal δ (Set.image (fun p => p 1) E3) := hS2_bound
    _ ≤ C2 * (Ky * ENNReal.ofReal (δ ^ (-η)) * ENNReal.ofReal (Real.sqrt (N_E.toReal))) := by gcongr
    _ = C2 * Ky * ENNReal.ofReal (δ ^ (-η)) * ENNReal.ofReal (Real.sqrt (N_E.toReal)) := by
      simp [mul_assoc] <;> rfl

  have hN3_top : N3 ≠ ⊤ := by
    let E3f := hE3_finite.toFinset
    have hE3f_coe : (E3f : Set _) = E3 := hE3_finite.coe_toFinset
    have h_encard : E3.encard = ↑E3f.card := by
      have h_coe : (E3f : Set _) = E3 := hE3f_coe
      simpa [h_coe] using Set.encard_coe_eq_coe_finsetCard E3f
    have h : N3 = (↑E3f.card : ENNReal) := by
      simp only [N3, h_encard] <;> norm_cast
    rw [h] <;> simp

  have hN_E_top : N_E ≠ ⊤ := by
    by_contra h
    have h_pos : 0 < δ ^ (3 * ε) := by positivity
    have h1 : ENNReal.ofReal (δ ^ (3 * ε)) * N_E = ⊤ := by
      rw [h]
      have h_pos2 : 0 < δ ^ (3 * ε) := by positivity
      have h_ne_zero : ENNReal.ofReal (δ ^ (3 * ε)) ≠ 0 := (ENNReal.ofReal_pos.mpr h_pos2).ne'
      exact mul_top h_ne_zero
    have h2 : N3 ≥ ENNReal.ofReal (δ ^ (3 * ε)) * N_E := hE3_size
    rw [h1] at h2
    have h3 : N3 = ⊤ := top_le_iff.mp h2
    exact hN3_top h3

  have h_nonneg : 0 ≤ N_E.toReal := by positivity
  have h_sqrt_sq : Real.sqrt (N_E.toReal) * Real.sqrt (N_E.toReal) = N_E.toReal := by
    have h1 : Real.sqrt (N_E.toReal) * Real.sqrt (N_E.toReal) = Real.sqrt ((N_E.toReal) ^ 2) := by
      rw [← Real.sqrt_mul h_nonneg] <;> ring_nf
    rw [h1, Real.sqrt_sq_eq_abs, abs_of_nonneg h_nonneg]

  have h_exp1 : δ ^ (-η) * δ ^ (-η) = δ ^ (-2 * η) := by
    rw [← Real.rpow_add hδ_pos] <;> ring_nf
  have h5 : ENNReal.ofReal (δ ^ (-η)) * ENNReal.ofReal (δ ^ (-η)) =
      ENNReal.ofReal (δ ^ (-2 * η)) := by
    rw [← ENNReal.ofReal_mul (by positivity), h_exp1]
  have h6 : ENNReal.ofReal (Real.sqrt (N_E.toReal)) * ENNReal.ofReal (Real.sqrt (N_E.toReal)) = N_E := by
    rw [← ENNReal.ofReal_mul (by positivity), h_sqrt_sq]
    exact ENNReal.ofReal_toReal hN_E_top

  have h_prod_le : Nreal δ S1 * Nreal δ S2 ≤
      C1 * C2 * Kx * Ky * ENNReal.ofReal (δ ^ (-2 * η)) * N_E := by
    calc Nreal δ S1 * Nreal δ S2
      ≤ (C1 * Kx * ENNReal.ofReal (δ ^ (-η)) * ENNReal.ofReal (Real.sqrt (N_E.toReal))) *
          (C2 * Ky * ENNReal.ofReal (δ ^ (-η)) * ENNReal.ofReal (Real.sqrt (N_E.toReal))) := by gcongr
    _ = C1 * C2 * Kx * Ky *
          (ENNReal.ofReal (δ ^ (-η)) * ENNReal.ofReal (δ ^ (-η))) *
          (ENNReal.ofReal (Real.sqrt (N_E.toReal)) * ENNReal.ofReal (Real.sqrt (N_E.toReal))) := by
      simp [mul_assoc, mul_comm, mul_left_comm] <;> rfl
    _ = C1 * C2 * Kx * Ky * ENNReal.ofReal (δ ^ (-2 * η)) * N_E := by
      rw [h5, h6] <;> simp [mul_assoc]

  let K_cancel := ENNReal.ofReal (δ ^ (2 * η)) / C1 / C2 / Kx / Ky

  have hK_cancel_pos : K_cancel ≠ 0 := by
    simp only [K_cancel, div_eq_mul_inv]
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
          · exact ENNReal.inv_ne_zero.mpr hC1_top
        · exact ENNReal.inv_ne_zero.mpr hC2_top
      · exact ENNReal.inv_ne_zero.mpr hKx_top
    · exact ENNReal.inv_ne_zero.mpr hKy_top

  have h_exp2 : δ ^ (2 * η) * δ ^ (-2 * η) = 1 := by
    have h : δ ^ (2 * η) * δ ^ (-2 * η) = δ ^ (2 * η + (-2 * η)) := by rw [← Real.rpow_add hδ_pos]
    rw [h] <;> ring_nf <;> simp
  have h_ab : ENNReal.ofReal (δ ^ (2 * η)) * ENNReal.ofReal (δ ^ (-2 * η)) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), h_exp2] <;> rw [ENNReal.ofReal_one]
  have h_c1 : C1⁻¹ * C1 = 1 := by
    rw [mul_comm]; exact ENNReal.mul_inv_cancel hC1_pos hC1_top
  have h_c2 : C2⁻¹ * C2 = 1 := by
    rw [mul_comm]; exact ENNReal.mul_inv_cancel hC2_pos hC2_top
  have h_kx : Kx⁻¹ * Kx = 1 := by
    rw [mul_comm]; exact ENNReal.mul_inv_cancel hKx_pos hKx_top
  have h_ky : Ky⁻¹ * Ky = 1 := by
    rw [mul_comm]; exact ENNReal.mul_inv_cancel hKy_pos hKy_top

  have hK_cancel : K_cancel * (C1 * C2 * Kx * Ky * ENNReal.ofReal (δ ^ (-2 * η))) = 1 := by
    simp only [K_cancel, div_eq_mul_inv]
    set a := ENNReal.ofReal (δ ^ (2 * η)) with ha
    set b := ENNReal.ofReal (δ ^ (-2 * η)) with hb
    have h4 : (a * C1⁻¹ * C2⁻¹ * Kx⁻¹ * Ky⁻¹) * (C1 * C2 * Kx * Ky * b) = a * b := by
      have h5 : (a * C1⁻¹ * C2⁻¹ * Kx⁻¹ * Ky⁻¹) * (C1 * C2 * Kx * Ky * b) =
          a * (C1⁻¹ * C1) * (C2⁻¹ * C2) * (Kx⁻¹ * Kx) * (Ky⁻¹ * Ky) * b := by
        simp [mul_assoc, mul_comm, mul_left_comm] <;> rfl
      rw [h5, h_c1, h_c2, h_kx, h_ky] <;> simp [mul_assoc]
    rw [h4, h_ab]

  have h_NE_lower : N_E ≥ K_cancel * Nreal δ S1 * Nreal δ S2 := by
    have h : K_cancel * (Nreal δ S1 * Nreal δ S2) ≤
        K_cancel * (C1 * C2 * Kx * Ky * ENNReal.ofReal (δ ^ (-2 * η)) * N_E) := by gcongr
    have h' : K_cancel * (C1 * C2 * Kx * Ky * ENNReal.ofReal (δ ^ (-2 * η)) * N_E) = N_E := by
      rw [← mul_assoc, hK_cancel, one_mul]
    rw [h'] at h
    have h_assoc : K_cancel * Nreal δ S1 * Nreal δ S2 = K_cancel * (Nreal δ S1 * Nreal δ S2) := by rw [mul_assoc]
    rw [h_assoc]; exact h

  have h_main : ENat.toENNReal (dyadicCoveringNumber δ E') ≥
      (1 / 2 : ENNReal) / M_G / C1 / C2 / Kx / Ky *
      ENNReal.ofReal (δ ^ (3 * ε + 2 * η)) *
        Nreal δ S1 * Nreal δ S2 := by
    have h_size : ENat.toENNReal E'.encard ≥ N3 / 2 := hE'_card_lower
    have hE3_size' : N3 ≥ ENNReal.ofReal (δ ^ (3 * ε)) * N_E := hE3_size
    have h_card_lower2 : ENat.toENNReal E'.encard ≥
        ENNReal.ofReal (δ ^ (3 * ε)) * N_E / 2 := by
      calc ENat.toENNReal E'.encard
          ≥ N3 / 2 := h_size
      _ ≥ (ENNReal.ofReal (δ ^ (3 * ε)) * N_E) / 2 := by gcongr
    have h_covering_lower : ENat.toENNReal (dyadicCoveringNumber δ E') ≥
        (ENNReal.ofReal (δ ^ (3 * ε)) * N_E) / 2 / M_G := by
      calc ENat.toENNReal (dyadicCoveringNumber δ E')
          ≥ ENat.toENNReal E'.encard / M_G := h_Nplane_lower
      _ ≥ ((ENNReal.ofReal (δ ^ (3 * ε)) * N_E) / 2) / M_G := by gcongr
    set a := ENNReal.ofReal (δ ^ (3 * ε)) with ha
    set b := ENNReal.ofReal (δ ^ (2 * η)) with hb
    set c := ENNReal.ofReal (δ ^ (3 * ε + 2 * η)) with hc
    set d := Nreal δ S1 * Nreal δ S2 with hd
    have h_exp3 : δ ^ (3 * ε) * δ ^ (2 * η) = δ ^ (3 * ε + 2 * η) := by
      rw [← Real.rpow_add hδ_pos] <;> ring
    have h_ab : a * b = c := by
      rw [← ENNReal.ofReal_mul (by positivity), h_exp3]
    have h_aK : a * K_cancel = c / C1 / C2 / Kx / Ky := by
      simp only [K_cancel, div_eq_mul_inv]
      have h_assoc2 : a * (b * C1⁻¹ * C2⁻¹ * Kx⁻¹ * Ky⁻¹) = (a * b) * C1⁻¹ * C2⁻¹ * Kx⁻¹ * Ky⁻¹ := by
        simp [mul_assoc]
      rw [h_assoc2, h_ab]
    calc ENat.toENNReal (dyadicCoveringNumber δ E')
        ≥ (a * N_E) / 2 / M_G := h_covering_lower
    _ = (1 / 2 : ENNReal) / M_G * a * N_E := by
      simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    _ ≥ (1 / 2 : ENNReal) / M_G * a * (K_cancel * d) := by
      have h_le : K_cancel * d ≤ N_E := by
        have h_eq : K_cancel * d = K_cancel * Nreal δ S1 * Nreal δ S2 := by
          simp only [d, mul_assoc]
        rw [h_eq]
        exact h_NE_lower
      have h : (1 / 2 : ENNReal) / M_G * a * (K_cancel * d) ≤
          (1 / 2 : ENNReal) / M_G * a * N_E :=
        mul_le_mul_left' h_le ((1 / 2 : ENNReal) / M_G * a)
      exact h
    _ = (1 / 2 : ENNReal) / M_G / C1 / C2 / Kx / Ky * c * Nreal δ S1 * Nreal δ S2 := by
      have h_step1 : (1 / 2 : ENNReal) / M_G * a * (K_cancel * d) =
          (1 / 2 : ENNReal) / M_G * (a * K_cancel) * d := by
        simp only [mul_assoc]
      rw [h_step1, h_aK, hd]
      simp only [div_eq_mul_inv]
      simp [mul_assoc, mul_comm, mul_left_comm]

  exact h_main

/-! ## Complete V4 density endgame -/

/-- **V4 density endgame**: complete proof of `h_density_E3''`.

Takes the size/occupancy/projection bounds for `E3'` and the half-mass subset `E3''`,
applies `product_density_from_threefold_direct_K` with Kx=Ky=2, C1=C2=3,
then absorbs the entire prefactor into `2ρ_sep + qAbsorb`.

The raw density exponent is `3ρ_sel + 2(L_exp·η)`. Since `η_work = 2η`,
this equals `3ρ_sel + L_exp·η_work`, matching the V4 budget.

The final exponent is `3ρ_sel + 2ρ_sep + qAbsorb + L_exp·η_work`,
exactly the `c_dense` exponent in the skeleton. -/
lemma density_endgame_V4
    {δ rho_sel rho_sep η η_work L_exp : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hrho_sel_pos : 0 < rho_sel) (hrho_sep_pos : 0 < rho_sep)
    (hη_pos : 0 < η) (hη_work_pos : 0 < η_work)
    (hη_work_eq_two : η_work = 2 * η)
    (hL_exp_pos : 0 < L_exp)
    -- M_G bound: M_G_real ≤ 1024 * δ^{-2ρ_sep}
    {M_G_real : ℝ} (hM_G_pos : 0 < M_G_real)
    (hM_G_bound1024 : M_G_real ≤ 1024 * δ ^ (-2 * rho_sep))
    -- Absorption threshold: δ^{qAbsorb} ≤ 1/(2·1024·6·6)
    (hδ_small_absorb : δ ^ qAbsorb η_work ≤ 1 / (2 * 1024 * 6 * 6))
    -- Sets
    {Pbar E3' E3'' : Set (EuclideanSpace ℝ (Fin 2))}
    {S1 S2 : Set ℝ}
    -- Finite
    (hE3'_finite : E3'.Finite)
    -- Size: |E3'| ≥ δ^{3ρ_sel} · N(Pbar)
    (hE3'_size : ENat.toENNReal E3'.encard ≥
        ENNReal.ofReal (δ ^ (3 * rho_sel)) * ENat.toENNReal (dyadicCoveringNumber δ Pbar))
    -- Half mass: |E3''| ≥ |E3'| / 2
    (hE3''_half : ENat.toENNReal E3''.encard ≥ ENat.toENNReal E3'.encard / 2)
    (hE3''_sub : E3'' ⊆ E3')
    -- Occupancy for E3'
    (h_occupancy : ∀ Q, Q ∈ dyadicCubes 2 δ →
        ENat.toENNReal (E3' ∩ Q).encard ≤ ENNReal.ofReal M_G_real)
    -- Projection bounds for E3' with factor 2 and exponent L_exp·η
    (h_proj_x : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0) E3') ≤
        (2 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal)))
    (h_proj_y : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 1) E3') ≤
        (2 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal)))
    -- S1, S2 rounding bounds with factor 3
    (hS1_bound : Nreal δ S1 ≤ (3 : ENNReal) * Nreal δ (Set.image (fun p => p 0) E3'))
    (hS2_bound : Nreal δ S2 ≤ (3 : ENNReal) * Nreal δ (Set.image (fun p => p 1) E3')) :
    ENNReal.ofReal (δ ^ (3 * rho_sel + 2 * rho_sep + qAbsorb η_work + L_exp * η_work)) *
      Nreal δ S1 * Nreal δ S2 ≤
    ENat.toENNReal (dyadicCoveringNumber δ E3'') := by
  set η_proj : ℝ := L_exp * η with hη_proj_def
  have hη_proj_pos : 0 < η_proj := by positivity
  set M_G : ENNReal := ENNReal.ofReal M_G_real with hM_G_def
  have hM_G_pos' : M_G ≠ 0 := by
    rw [hM_G_def]; positivity
  have hM_G_top' : M_G ≠ ⊤ := by
    rw [hM_G_def]; simp
  have hKx_pos : (2 : ENNReal) ≠ 0 := by norm_num
  have hKx_top : (2 : ENNReal) ≠ ⊤ := by simp
  have hKy_pos : (2 : ENNReal) ≠ 0 := by norm_num
  have hKy_top : (2 : ENNReal) ≠ ⊤ := by simp
  have hC1_pos : (3 : ENNReal) ≠ 0 := by norm_num
  have hC1_top : (3 : ENNReal) ≠ ⊤ := by simp
  have hC2_pos : (3 : ENNReal) ≠ 0 := by norm_num
  have hC2_top : (3 : ENNReal) ≠ ⊤ := by simp

  -- Step 1: Apply generalized wrapper
  have h_raw : ENat.toENNReal (dyadicCoveringNumber δ E3'') ≥
      (1 / 2 : ENNReal) / M_G / (3 : ENNReal) / (3 : ENNReal) / (2 : ENNReal) / (2 : ENNReal) *
      ENNReal.ofReal (δ ^ (3 * rho_sel + 2 * η_proj)) *
      Nreal δ S1 * Nreal δ S2 :=
    product_density_from_threefold_direct_K
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hε_pos := hrho_sel_pos) (hη_pos := hη_proj_pos)
      (hE3_finite := hE3'_finite)
      (hE'_sub := hE3''_sub)
      (hE'_card_lower := hE3''_half)
      (hM_G_pos := hM_G_pos') (hM_G_top := hM_G_top')
      (hC1_pos := hC1_pos) (hC1_top := hC1_top)
      (hC2_pos := hC2_pos) (hC2_top := hC2_top)
      (hKx_pos := hKx_pos) (hKx_top := hKx_top)
      (hKy_pos := hKy_pos) (hKy_top := hKy_top)
      (h_occupancy := h_occupancy)
      (hE3_size := hE3'_size)
      (h_proj_x := h_proj_x)
      (h_proj_y := h_proj_y)
      (hS1_bound := hS1_bound)
      (hS2_bound := hS2_bound)

  -- Step 2: Exponent equality: 3ρ_sel + 2η_proj = 3ρ_sel + L_exp·η_work
  have h_exp_eq : 3 * rho_sel + 2 * η_proj = 3 * rho_sel + L_exp * η_work := by
    rw [hη_proj_def, hη_work_eq_two] <;> ring

  -- Step 3: Effective real constants
  let C1_eff : ℝ := 6
  let C2_eff : ℝ := 6
  have hC1e_pos : 0 < C1_eff := by norm_num
  have hC2e_pos : 0 < C2_eff := by norm_num

  -- Step 4: Prefactor absorption via toReal
  let P1 : ENNReal := (1 / 2 : ENNReal) / M_G / (3 : ENNReal) / (3 : ENNReal) / (2 : ENNReal) / (2 : ENNReal)
  have hM_G_ne_top : M_G ≠ ⊤ := by rw [hM_G_def]; simp
  have hM_G_ne_zero : M_G ≠ 0 := by rw [hM_G_def]; positivity
  have hP1_ne_top : P1 ≠ ⊤ := by
    unfold P1
    have h1 : M_G⁻¹ ≠ ⊤ := by
      simpa [ENNReal.inv_eq_top] using hM_G_ne_zero
    have h2 : (1 / 2 : ENNReal) ≠ ⊤ := by simp
    have h3 : (3 : ENNReal)⁻¹ ≠ ⊤ := by simp
    have h4 : (2 : ENNReal)⁻¹ ≠ ⊤ := by simp
    simp only [div_eq_mul_inv]
    exact mul_ne_top (mul_ne_top (mul_ne_top (mul_ne_top (mul_ne_top h2 h1) h3) h3) h4) h4
  have hP1_eq : P1 = ENNReal.ofReal P1.toReal := by
    exact (ENNReal.ofReal_toReal hP1_ne_top).symm
  have h_real_ineq : P1.toReal ≥ δ ^ (2 * rho_sep + qAbsorb η_work) := by
    unfold P1
    have h_div : ∀ (x y : ENNReal), (x / y).toReal = x.toReal / y.toReal := ENNReal.toReal_div
    have hM : M_G.toReal = M_G_real := by
      have hM_G_def' : M_G = ENNReal.ofReal M_G_real := by exact hM_G_def
      rw [hM_G_def']
      have h_nonneg : 0 ≤ M_G_real := by linarith
      rw [ENNReal.toReal_ofReal h_nonneg]
    simp only [h_div, hM]
    <;> norm_num
    <;> have h1 : (1 / 2 : ℝ) / M_G_real / 36 ≥ δ ^ (2 * rho_sep) / 73728 := by
      have hM : M_G_real ≤ 1024 * δ ^ (-2 * rho_sep) := hM_G_bound1024
      have h_pos : 0 < M_G_real := hM_G_pos
      have h_inv : (M_G_real)⁻¹ ≥ (δ ^ (2 * rho_sep)) / 1024 := by
        have h2 : M_G_real ≤ 1024 * δ ^ (-2 * rho_sep) := hM
        have h3 : (M_G_real)⁻¹ ≥ (1024 * δ ^ (-2 * rho_sep))⁻¹ := by gcongr
        have h4 : δ ^ (-2 * rho_sep) = (δ ^ (2 * rho_sep))⁻¹ := by
          have h5 : 0 ≤ 2 * rho_sep := by positivity
          simpa [h5] using Real.rpow_neg hδ_pos.le (2 * rho_sep)
        rw [h4] at h3
        have h6 : (1024 * (δ ^ (2 * rho_sep))⁻¹)⁻¹ = (δ ^ (2 * rho_sep)) / 1024 := by
          field_simp <;> ring
        rw [h6] at h3; exact h3
      have h7 : (1 / 2 : ℝ) / M_G_real / 36 = (1 / 2 : ℝ) * (M_G_real)⁻¹ / 36 := by
        field_simp [h_pos.ne'] <;> ring
      rw [h7]
      have h8 : (1 / 2 : ℝ) * (M_G_real)⁻¹ / 36 ≥ (1 / 2 : ℝ) * ((δ ^ (2 * rho_sep)) / 1024) / 36 := by gcongr
      have h9 : (1 / 2 : ℝ) * ((δ ^ (2 * rho_sep)) / 1024) / 36 = δ ^ (2 * rho_sep) / 73728 := by ring
      linarith
    have h10 : (1 / 73728 : ℝ) ≥ δ ^ (qAbsorb η_work) := by
      have h11 : δ ^ (qAbsorb η_work) ≤ 1 / (2 * 1024 * 6 * 6) := hδ_small_absorb
      have h12 : (1 / (2 * 1024 * 6 * 6) : ℝ) = (1 / 73728 : ℝ) := by norm_num
      rw [h12] at h11; exact h11
    have h13 : 0 ≤ δ ^ (2 * rho_sep) := by positivity
    have h14 : δ ^ (2 * rho_sep) / 73728 ≥ δ ^ (2 * rho_sep) * δ ^ (qAbsorb η_work) := by
      have h15 : δ ^ (2 * rho_sep) / 73728 = δ ^ (2 * rho_sep) * (1 / 73728 : ℝ) := by ring
      rw [h15]
      exact mul_le_mul_of_nonneg_left h10 h13
    have h16 : δ ^ (2 * rho_sep) * δ ^ (qAbsorb η_work) = δ ^ (2 * rho_sep + qAbsorb η_work) := by
      rw [← Real.rpow_add hδ_pos] <;> ring
    linarith
  have h_prefactor_absorb : P1 ≥ ENNReal.ofReal (δ ^ (2 * rho_sep + qAbsorb η_work)) := by
    rw [hP1_eq]
    exact ENNReal.ofReal_le_ofReal h_real_ineq

  -- Step 5: Exponent equality
  have h_exp_eq : 3 * rho_sel + 2 * η_proj = 3 * rho_sel + L_exp * η_work := by
    rw [hη_proj_def, hη_work_eq_two] <;> ring
  have h_exp_rw : ENNReal.ofReal (δ ^ (3 * rho_sel + 2 * η_proj)) =
      ENNReal.ofReal (δ ^ (3 * rho_sel + L_exp * η_work)) := by
    rw [h_exp_eq]

  -- Step 6: Combine raw bound with prefactor absorption
  have h_final : ENat.toENNReal (dyadicCoveringNumber δ E3'') ≥
      ENNReal.ofReal (δ ^ (2 * rho_sep + qAbsorb η_work)) *
      ENNReal.ofReal (δ ^ (3 * rho_sel + L_exp * η_work)) *
      Nreal δ S1 * Nreal δ S2 := by
    calc ENat.toENNReal (dyadicCoveringNumber δ E3'')
      ≥ ((1 / 2 : ENNReal) / M_G / (3 : ENNReal) / (3 : ENNReal) / (2 : ENNReal) / (2 : ENNReal)) *
          ENNReal.ofReal (δ ^ (3 * rho_sel + 2 * η_proj)) * Nreal δ S1 * Nreal δ S2 := h_raw
    _ ≥ ENNReal.ofReal (δ ^ (2 * rho_sep + qAbsorb η_work)) *
          ENNReal.ofReal (δ ^ (3 * rho_sel + 2 * η_proj)) * Nreal δ S1 * Nreal δ S2 := by
        gcongr
    _ = ENNReal.ofReal (δ ^ (2 * rho_sep + qAbsorb η_work)) *
          ENNReal.ofReal (δ ^ (3 * rho_sel + L_exp * η_work)) * Nreal δ S1 * Nreal δ S2 := by
        rw [h_exp_rw]

  -- Step 7: Combine exponents
  have h_exp_add : δ ^ (2 * rho_sep + qAbsorb η_work) * δ ^ (3 * rho_sel + L_exp * η_work) =
      δ ^ (3 * rho_sel + 2 * rho_sep + qAbsorb η_work + L_exp * η_work) := by
    rw [← Real.rpow_add hδ_pos] <;> ring_nf
  have h_mul : ENNReal.ofReal (δ ^ (2 * rho_sep + qAbsorb η_work)) *
      ENNReal.ofReal (δ ^ (3 * rho_sel + L_exp * η_work)) =
      ENNReal.ofReal (δ ^ (3 * rho_sel + 2 * rho_sep + qAbsorb η_work + L_exp * η_work)) := by
    rw [← ENNReal.ofReal_mul (by positivity), h_exp_add]
  rw [h_mul] at h_final
  exact h_final

end ProductLikeIncidence.ProductReduction
