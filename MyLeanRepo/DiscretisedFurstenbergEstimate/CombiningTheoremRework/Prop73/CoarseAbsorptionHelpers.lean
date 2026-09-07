module

/-
  Coarse Absorption Helpers — Extracted from CIBW normal/good endpoints.

  Provides:
  - Generic coarse absorption combination lemma
  - Normal and good specializations
  - Polynomial domination bound `poly_bound1`
  - Square-root exponent bound `sqrt_bound`
  - Exact fixed-factor lemmas `normal_fixed_factor` and `good_fixed_factor`

  Whiteprint node: combining_theorem_rework / coarse_absorption_helpers
  Dependencies: none beyond Mathlib
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure

/-- Generic coarse absorption combination lemma.

    Given:
    - `L_m ≥ τ * L_k` with `L_k ≥ 1 > 0`, `τ > 0`
    - `τ^(C_P+8) * L_k^8 ≥ A` for some `A ≥ 0`
    - `Cb * δm^ε ≤ L_k^C_P` for some `Cb ≥ 0`, `δm > 0`

    Proves:
    `L_m^(C_P+8) ≥ A * Cb * δm^ε`

    This factors out the common final chain from both the normal and
    good coarse absorption endpoints in CIBW. -/
lemma coarse_absorption_generic
    {L_m L_k τ C_P A Cb δm ε : ℝ}
    (hLk_pos : 0 < L_k)
    (hLk_ge1 : 1 ≤ L_k)
    (hCP_nonneg : 0 ≤ C_P)
    (hτ_pos : 0 < τ)
    (hLm_ge : L_m ≥ τ * L_k)
    (hA_nonneg : 0 ≤ A)
    (hCb_nonneg : 0 ≤ Cb)
    (hδm_pos : 0 < δm)
    (h_main_poly : Real.rpow τ (C_P + 8) * L_k ^ 8 ≥ A)
    (hmax_cancel : Cb * Real.rpow δm ε ≤ Real.rpow L_k C_P) :
    Real.rpow L_m (C_P + 8) ≥ A * Cb * Real.rpow δm ε := by
  have h_exp_nonneg : 0 ≤ C_P + 8 := by linarith
  have h_base_pos : 0 ≤ τ * L_k := by positivity
  have h1 : Real.rpow L_m (C_P + 8) ≥ Real.rpow (τ * L_k) (C_P + 8) :=
    Real.rpow_le_rpow h_base_pos hLm_ge h_exp_nonneg
  have h2 : Real.rpow (τ * L_k) (C_P + 8) =
      Real.rpow τ (C_P + 8) * Real.rpow L_k (C_P + 8) := by
    have hτ_nonneg : 0 ≤ τ := by linarith
    have hLk_nonneg : 0 ≤ L_k := by linarith
    simpa [Real.rpow_mul] using Real.mul_rpow hτ_nonneg hLk_nonneg
  have h3 : Real.rpow L_k (C_P + 8) = Real.rpow L_k C_P * L_k ^ 8 := by
    have h3a : Real.rpow L_k (C_P + 8) =
        Real.rpow L_k C_P * Real.rpow L_k (8 : ℝ) :=
      Real.rpow_add hLk_pos C_P (8 : ℝ)
    have h3b : Real.rpow L_k (8 : ℝ) = L_k ^ (8 : ℕ) :=
      Real.rpow_natCast L_k 8
    rw [h3a, h3b]
  have h4 : Real.rpow L_m (C_P + 8) ≥
      Real.rpow τ (C_P + 8) * (Real.rpow L_k C_P * L_k ^ 8) := by
    calc
      Real.rpow L_m (C_P + 8)
        ≥ Real.rpow (τ * L_k) (C_P + 8) := h1
      _ = Real.rpow τ (C_P + 8) * Real.rpow L_k (C_P + 8) := h2
      _ = Real.rpow τ (C_P + 8) * (Real.rpow L_k C_P * L_k ^ 8) := by rw [h3]
  have hLk_CP_nonneg : 0 ≤ Real.rpow L_k C_P :=
    Real.rpow_nonneg hLk_pos.le C_P
  have h5 : Real.rpow τ (C_P + 8) * (Real.rpow L_k C_P * L_k ^ 8) ≥
      Real.rpow L_k C_P * A := by
    have h5a : Real.rpow τ (C_P + 8) * (Real.rpow L_k C_P * L_k ^ 8) =
        Real.rpow L_k C_P * (Real.rpow τ (C_P + 8) * L_k ^ 8) := by ring
    rw [h5a]
    exact mul_le_mul_of_nonneg_left h_main_poly hLk_CP_nonneg
  have h6 : Real.rpow L_k C_P * A ≥ A * Cb * Real.rpow δm ε := by
    have h6a : Real.rpow L_k C_P * A ≥ (Cb * Real.rpow δm ε) * A :=
      mul_le_mul_of_nonneg_right hmax_cancel hA_nonneg
    have h6b : (Cb * Real.rpow δm ε) * A = A * Cb * Real.rpow δm ε := by ring
    rw [h6b] at h6a
    exact h6a
  exact le_trans (le_trans h6 h5) h4

/-- Normal coarse absorption endpoint.

    Specializes `coarse_absorption_generic` with `ε = ε_N` and the
    normal-scale polynomial constant `A_normal`. -/
lemma coarse_absorption_normal
    {L_m L_k τ C_P A_normal Cb δm ε_N : ℝ}
    (hLk_pos : 0 < L_k)
    (hLk_ge1 : 1 ≤ L_k)
    (hCP_nonneg : 0 ≤ C_P)
    (hτ_pos : 0 < τ)
    (hLm_ge : L_m ≥ τ * L_k)
    (hA_normal_pos : 0 < A_normal)
    (hCb_nonneg : 0 ≤ Cb)
    (hδm_pos : 0 < δm)
    (h_main_poly : Real.rpow τ (C_P + 8) * L_k ^ 8 ≥ A_normal)
    (hmax_cancel : Cb * Real.rpow δm ε_N ≤ Real.rpow L_k C_P) :
    Real.rpow L_m (C_P + 8) ≥ A_normal * Cb * Real.rpow δm ε_N :=
  coarse_absorption_generic hLk_pos hLk_ge1 hCP_nonneg hτ_pos hLm_ge
    hA_normal_pos.le hCb_nonneg hδm_pos h_main_poly hmax_cancel

/-- Good coarse absorption endpoint.

    Specializes `coarse_absorption_generic` with `ε = 2 * ε_G + ε_N` and the
    good-scale polynomial constant `A_good`. -/
lemma coarse_absorption_good
    {L_m L_k τ C_P A_good Cb δm ε_G ε_N : ℝ}
    (hLk_pos : 0 < L_k)
    (hLk_ge1 : 1 ≤ L_k)
    (hCP_nonneg : 0 ≤ C_P)
    (hτ_pos : 0 < τ)
    (hLm_ge : L_m ≥ τ * L_k)
    (hA_good_pos : 0 < A_good)
    (hCb_nonneg : 0 ≤ Cb)
    (hδm_pos : 0 < δm)
    (h_main_poly : Real.rpow τ (C_P + 8) * L_k ^ 8 ≥ A_good)
    (hmax_cancel : Cb * Real.rpow δm (2 * ε_G + ε_N) ≤ Real.rpow L_k C_P) :
    Real.rpow L_m (C_P + 8) ≥ A_good * Cb * Real.rpow δm (2 * ε_G + ε_N) :=
  coarse_absorption_generic hLk_pos hLk_ge1 hCP_nonneg hτ_pos hLm_ge
    hA_good_pos.le hCb_nonneg hδm_pos h_main_poly hmax_cancel

/-- Polynomial bound: `5^7 * k^7 ≥ (4k + 7)^7` for `k ≥ 7`. -/
lemma poly_bound1 (k : ℕ) (hk : 7 ≤ k) :
    (5 : ℝ)^7 * (k : ℝ)^7 ≥ (4 * (k : ℝ) + 7)^7 := by
  have h1 : 5 * (k : ℝ) ≥ 4 * (k : ℝ) + 7 := by
    have h2 : (k : ℝ) ≥ 7 := by exact_mod_cast hk
    linarith
  have h3 : (5 : ℝ)^7 * (k : ℝ)^7 = (5 * (k : ℝ))^7 := by ring
  rw [h3]
  gcongr

/-- Bound: `2 * sqrt 2 ≥ (2 * sqrt 2)^s` for `0 < s < 1`. -/
lemma sqrt_bound (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    (2 * Real.sqrt 2) ≥ (2 * Real.sqrt 2)^s := by
  have h1 : 1 < (2 * Real.sqrt 2) := by
    have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h2 : s ≤ 1 := by linarith
  have h3 : (2 * Real.sqrt 2)^s ≤ (2 * Real.sqrt 2)^(1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) h2
  have h4 : (2 * Real.sqrt 2)^(1 : ℝ) = (2 * Real.sqrt 2) := by
    simp
  rw [h4] at h3
  exact h3

/-- Exact normal-case fixed-factor inequality.

    Uses `sqrt_bound` and `poly_bound1` to absorb the polynomial and
    square-root factors into the constant `K * 81 * 2700 * 3145728 * 13 *
    (2 * sqrt 2) * 2^s * 5^7 * k^7`. -/
lemma normal_fixed_factor
    (K s k : ℝ)
    (hcommon : 0 ≤ K * 81 * (2700 * 3145728) * 13 * Real.rpow 2 s)
    (hbase : Real.rpow (2 * Real.sqrt 2) s ≤ 2 * Real.sqrt 2)
    (hpoly : (4 * k + 7) ^ 7 ≤ 5 ^ 7 * k ^ 7)
    (hpoly_nonneg : 0 ≤ (4 * k + 7) ^ 7) :
    K * (81 * ((2700 : ℝ) * 3145728 * (4 * k + 7) ^ 7) *
          Real.rpow (2 * Real.sqrt 2) s) * 13 * Real.rpow 2 s ≤
      K * 81 * (2700 * 3145728) * 13 * (2 * Real.sqrt 2) *
        Real.rpow 2 s * 5 ^ 7 * k ^ 7 := by
  have hbase_nonneg : 0 ≤ 2 * Real.sqrt 2 := by positivity
  have hcore :
      Real.rpow (2 * Real.sqrt 2) s * (4 * k + 7) ^ 7 ≤
        (2 * Real.sqrt 2) * (5 ^ 7 * k ^ 7) :=
    mul_le_mul hbase hpoly hpoly_nonneg hbase_nonneg
  have hscaled := mul_le_mul_of_nonneg_left hcore hcommon
  calc
    K * (81 * ((2700 : ℝ) * 3145728 * (4 * k + 7) ^ 7) *
          Real.rpow (2 * Real.sqrt 2) s) * 13 * Real.rpow 2 s
        = (K * 81 * (2700 * 3145728) * 13 * Real.rpow 2 s) *
            (Real.rpow (2 * Real.sqrt 2) s * (4 * k + 7) ^ 7) := by ring
    _ ≤ (K * 81 * (2700 * 3145728) * 13 * Real.rpow 2 s) *
          ((2 * Real.sqrt 2) * (5 ^ 7 * k ^ 7)) := hscaled
    _ = K * 81 * (2700 * 3145728) * 13 * (2 * Real.sqrt 2) *
          Real.rpow 2 s * 5 ^ 7 * k ^ 7 := by ring

/-- Exact good-case fixed-factor inequality.

    Uses `poly_bound1` to absorb the polynomial factor into the constant
    `K * 81 * 2700 * 3145728 * 13 * (2 * sqrt 2) * 2^s * 5^7 * k^7`. -/
lemma good_fixed_factor
    (K s k : ℝ)
    (hcommon :
      0 ≤ K * 81 * (2700 * 3145728) * 13 *
        (2 * Real.sqrt 2) * Real.rpow 2 s)
    (hpoly : (4 * k + 7) ^ 7 ≤ 5 ^ 7 * k ^ 7) :
    K * (81 * ((2700 : ℝ) * 3145728 * (4 * k + 7) ^ 7) *
          (2 * Real.sqrt 2)) * 13 * Real.rpow 2 s ≤
      K * 81 * (2700 * 3145728) * 13 * (2 * Real.sqrt 2) *
        Real.rpow 2 s * 5 ^ 7 * k ^ 7 := by
  have hscaled := mul_le_mul_of_nonneg_left hpoly hcommon
  calc
    K * (81 * ((2700 : ℝ) * 3145728 * (4 * k + 7) ^ 7) *
          (2 * Real.sqrt 2)) * 13 * Real.rpow 2 s
        = (K * 81 * (2700 * 3145728) * 13 *
            (2 * Real.sqrt 2) * Real.rpow 2 s) * (4 * k + 7) ^ 7 := by ring
    _ ≤ (K * 81 * (2700 * 3145728) * 13 *
          (2 * Real.sqrt 2) * Real.rpow 2 s) * (5 ^ 7 * k ^ 7) := hscaled
    _ = K * 81 * (2700 * 3145728) * 13 * (2 * Real.sqrt 2) *
          Real.rpow 2 s * 5 ^ 7 * k ^ 7 := by ring

/-- Threshold scaling: given `C = B / D` and `C * x ≤ y`, prove `B * x ≤ D * y`. -/
lemma threshold_scale
    {D B C x y : ℝ}
    (hD : 0 < D)
    (hC : C = B / D)
    (hxy : C * x ≤ y) :
    B * x ≤ D * y := by
  have hDC : D * C = B := by
    rw [hC]
    field_simp [hD.ne']
  calc
    B * x = (D * C) * x := by rw [hDC]
    _ = D * (C * x) := by ring
    _ ≤ D * y := mul_le_mul_of_nonneg_left hxy hD.le

/-- Threshold scaling with log2: given `C = B / (τ^(C_P+8) * (log 2)^8)`
    and `C * k^7 ≤ k^8`, prove `B * k^7 ≤ τ^(C_P+8) * (k * log 2)^8`. -/
lemma threshold_scale_log2
    {τ C_P B C k : ℝ}
    (hτ : 0 < τ)
    (hC : C = B / (Real.rpow τ (C_P + 8) * (Real.log 2) ^ 8))
    (hk : C * k ^ 7 ≤ k ^ 8) :
    B * k ^ 7 ≤ Real.rpow τ (C_P + 8) * (k * Real.log 2) ^ 8 := by
  let D := Real.rpow τ (C_P + 8) * (Real.log 2) ^ 8
  have hD : 0 < D := by
    dsimp only [D]
    have hτr : 0 < Real.rpow τ (C_P + 8) :=
      Real.rpow_pos_of_pos hτ (C_P + 8)
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact mul_pos hτr (pow_pos hlog 8)
  have hscaled : B * k ^ 7 ≤ D * k ^ 8 :=
    threshold_scale hD hC hk
  calc
    B * k ^ 7 ≤ D * k ^ 8 := hscaled
    _ = Real.rpow τ (C_P + 8) * (k * Real.log 2) ^ 8 := by
      dsimp only [D]
      ring

/-- Absorb a coefficient into a power: `C * k^7 ≤ k^8` when `C ≤ k` and `0 ≤ k`. -/
lemma absorb_power
    {C k : ℝ}
    (hk : C ≤ k)
    (hk_nonneg : 0 ≤ k) :
    C * k ^ 7 ≤ k ^ 8 := by
  calc
    C * k ^ 7 ≤ k * k ^ 7 :=
      mul_le_mul_of_nonneg_right hk (pow_nonneg hk_nonneg 7)
    _ = k ^ 8 := by ring

/-- Non-negativity of the normal-case common factor. -/
lemma normal_common_nonneg
    (K s : ℝ)
    (hK : 0 < K) :
    0 ≤ K * 81 * (2700 * 3145728) * 13 * Real.rpow 2 s := by
  have hrpow : 0 ≤ Real.rpow 2 s :=
    (Real.rpow_pos_of_pos (by norm_num) s).le
  positivity

/-- Non-negativity of the good-case common factor. -/
lemma good_common_nonneg
    (K s : ℝ)
    (hK : 0 < K) :
    0 ≤ K * 81 * (2700 * 3145728) * 13 *
      (2 * Real.sqrt 2) * Real.rpow 2 s := by
  have hrpow : 0 ≤ Real.rpow 2 s :=
    (Real.rpow_pos_of_pos (by norm_num) s).le
  have hsqrt : 0 ≤ 2 * Real.sqrt 2 :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg 2)
  positivity

/-- `log 2 ≤ 1`. -/
lemma log_two_le_one : Real.log 2 ≤ 1 := by
  linarith [Real.log_two_lt_d9]

/-- Index bound: `k * log 2 ≤ k` for `k : ℕ`. -/
lemma index_log_two_le
    (k : ℕ) :
    (k : ℝ) * Real.log 2 ≤ (k : ℝ) := by
  exact mul_le_of_le_one_right (Nat.cast_nonneg k) log_two_le_one

/-- Tail index bound: `(k - m) * log 2 ≤ k` for `k, m : ℕ`. -/
lemma tail_index_log_two_le
    (k m : ℕ) :
    ((k - m : ℕ) : ℝ) * Real.log 2 ≤ (k : ℝ) := by
  calc
    ((k - m : ℕ) : ℝ) * Real.log 2
        ≤ ((k - m : ℕ) : ℝ) :=
      mul_le_of_le_one_right (Nat.cast_nonneg (k - m)) log_two_le_one
    _ ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k m

/-- First scale ratio: simplify the ratio `Δ 1 / Δ 0` from a Fin-indexed family. -/
lemma first_scale_ratio
    {n : ℕ} (hn : 0 < n) (Δ : Fin (n + 1) → ℝ) (R : ℝ)
    (h : Δ (Fin.succ (⟨0, hn⟩ : Fin n)) / Δ (Fin.castSucc (⟨0, hn⟩ : Fin n)) ≤ R) :
    Δ 1 / Δ 0 ≤ R := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hzero : (⟨0, hn⟩ : Fin n) = 0 := by ext; rfl
  have hsucc : Fin.succ (⟨0, hn⟩ : Fin n) = (1 : Fin (n + 1)) := by
    rw [hzero]; exact Fin.succ_zero_eq_one'
  have hcast : Fin.castSucc (⟨0, hn⟩ : Fin n) = (0 : Fin (n + 1)) := by
    rw [hzero]; rfl
  simpa only [hsucc, hcast] using h

end DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure
