import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperCV
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Paper absorption arithmetic for the broad mass budget

This module provides the real arithmetic and ENNReal bridge for the
h_absorb hypothesis of `paper_broad_mass_budget_main`, using the
Pure WZ2 paper parameters: τ = L^(σ-10η), N ≤ L^(σ/2-η-2), etc.

## Main results

- `paper_h_absorb_verification_core`: real arithmetic inequality
- `paper_h_absorb_ennreal_bridge`: lifts the real inequality to ENNReal
- `paper_absorption_Q_exists`: existence of a natural Q satisfying the threshold
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set ENNReal
open scoped ENNReal

attribute [local instance] Classical.propDecidable

/-- Real arithmetic core for the paper h_absorb verification.

Given:
- N ≤ L^(σ/2 - η - 2)
- M ≤ L^(2 - σ - η) * N
- mass ≥ N * L^(2 + η)
- τ = L^(σ - 10η)
- Q ≥ 4 * C^2 * L^(-3σ/2 + 3η)

Proves: 2 * M * C * (L^2 * N)^(3/2) ≤ √(Q * τ) * mass
-/
lemma paper_h_absorb_verification_core
    (L sigma eta : ℝ)
    (N : ℕ)
    (C M mass tau Q : ℝ)
    (hL_pos : 0 < L)
    (hL_lt_one : L < 1)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (heta_pos : 0 < eta)
    (heta_small : 10 * eta < sigma)
    (hN_pos : 0 < N)
    (hC_pos : 0 < C)
    (hM_nonneg : 0 ≤ M)
    (hmass_nonneg : 0 ≤ mass)
    (hQ_nonneg : 0 ≤ Q)
    (htau_pos : 0 < tau)
    (hN_bound : (N : ℝ) ≤ L ^ (sigma / 2 - eta - 2))
    (hM : M ≤ L ^ (2 - sigma - eta) * (N : ℝ))
    (hmass : (N : ℝ) * L ^ (2 + eta) ≤ mass)
    (htau_eq : tau = L ^ (sigma - 10 * eta))
    (hQ : 4 * C^2 * L ^ (-3 * sigma / 2 + 3 * eta) ≤ Q) :
    2 * M * C * (L^2 * (N : ℝ))^(3 / 2 : ℝ) ≤
      Real.sqrt (Q * tau) * mass := by
  set N' : ℝ := (N : ℝ) with hN'_def
  have hN'_pos : 0 < N' := by positivity
  have hN'_nonneg : 0 ≤ N' := by positivity
  have hL_nonneg : 0 ≤ L := by linarith

  -- Helper: N' * N'^(3/2) = N'^(5/2)
  have hN_mul_pow : N' * N'^(3 / 2 : ℝ) = N'^(5 / 2 : ℝ) := by
    have h1 : N' * N'^(3 / 2 : ℝ) = N'^(1 : ℝ) * N'^(3 / 2 : ℝ) := by
      have h11 : N'^(1 : ℝ) = N' := by simp
      rw [h11] <;> ring
    rw [h1]
    have h2 : N'^(1 : ℝ) * N'^(3 / 2 : ℝ) = N'^((1 : ℝ) + (3 / 2 : ℝ)) :=
      Eq.symm (Real.rpow_add hN'_pos (1 : ℝ) (3 / 2 : ℝ))
    rw [h2]
    have h3 : (1 : ℝ) + (3 / 2 : ℝ) = (5 / 2 : ℝ) := by norm_num
    rw [h3]

  have hN_pow_mul : N'^(5 / 2 : ℝ) = N' * N'^(3 / 2 : ℝ) :=
    Eq.symm hN_mul_pow

  -- N^(3/2) ≤ L^(3σ/4 - 3η/2 - 3)
  have hN32 : N'^(3 / 2 : ℝ) ≤ L^(3 * sigma / 4 - 3 * eta / 2 - 3) := by
    have h1 : N'^(3 / 2 : ℝ) ≤ (L^(sigma / 2 - eta - 2))^(3 / 2 : ℝ) :=
      Real.rpow_le_rpow hN'_nonneg hN_bound (by norm_num)
    have h2 : (L^(sigma / 2 - eta - 2))^(3 / 2 : ℝ) =
        L^((sigma / 2 - eta - 2) * (3 / 2 : ℝ)) :=
      Eq.symm (Real.rpow_mul hL_nonneg (sigma / 2 - eta - 2) (3 / 2 : ℝ))
    have h3 : (sigma / 2 - eta - 2) * (3 / 2 : ℝ) = 3 * sigma / 4 - 3 * eta / 2 - 3 := by ring
    rw [h2, h3] at h1
    exact h1

  -- (L^2 * N')^(3/2) = L^3 * N'^(3/2)
  have hL2N32 : (L^2 * N')^(3 / 2 : ℝ) = L^3 * N'^(3 / 2 : ℝ) := by
    have h_pos1 : 0 ≤ L^2 := by positivity
    rw [Real.mul_rpow h_pos1 hN'_nonneg]
    have hL2_cast : (L^2 : ℝ) = L^(2 : ℝ) := by norm_cast
    have h4 : (L^(2 : ℝ))^(3 / 2 : ℝ) = L^((2 : ℝ) * (3 / 2 : ℝ)) :=
      Eq.symm (Real.rpow_mul hL_nonneg (2 : ℝ) (3 / 2 : ℝ))
    have h5 : (2 : ℝ) * (3 / 2 : ℝ) = 3 := by norm_num
    have h61 : (L^2)^(3 / 2 : ℝ) = L^(3 : ℝ) := by
      rw [hL2_cast, h4, h5]
    have h62 : L^(3 : ℝ) = L^3 := by norm_cast
    have h6 : (L^2)^(3 / 2 : ℝ) = L^3 := by
      rw [h61, h62]
    rw [h6] <;> ring

  -- Step 1: LHS ≤ 2*C*L^(5-σ-η)*N^(5/2)
  have h1 : 2 * M * C * (L^2 * N')^(3 / 2 : ℝ) ≤
      2 * C * L^(5 - sigma - eta) * N'^(5 / 2 : ℝ) := by
    rw [hL2N32]
    have hL3_cast : L^3 = L^(3 : ℝ) := by norm_cast
    calc
      2 * M * C * (L^3 * N'^(3 / 2 : ℝ))
        ≤ 2 * (L^(2 - sigma - eta) * N') * C * (L^3 * N'^(3 / 2 : ℝ)) := by
          gcongr
      _ = 2 * C * (L^(2 - sigma - eta) * L^3) * (N' * N'^(3 / 2 : ℝ)) := by ring
      _ = 2 * C * L^(5 - sigma - eta) * (N' * N'^(3 / 2 : ℝ)) := by
        have h_exp : (2 - sigma - eta) + (3 : ℝ) = 5 - sigma - eta := by ring
        rw [hL3_cast, ← Real.rpow_add hL_pos, h_exp]
      _ = 2 * C * L^(5 - sigma - eta) * N'^(5 / 2 : ℝ) := by rw [hN_mul_pow]

  -- Step 2: LHS ≤ 2*C*N*L^(2 - σ/4 - 5η/2)
  have h2 : 2 * C * L^(5 - sigma - eta) * N'^(5 / 2 : ℝ) ≤
      2 * C * N' * L^(2 - sigma / 4 - 5 * eta / 2) := by
    rw [hN_pow_mul]
    have h3 : L^(5 - sigma - eta) * N'^(3 / 2 : ℝ) ≤
        L^(5 - sigma - eta) * L^(3 * sigma / 4 - 3 * eta / 2 - 3) := by gcongr
    have h4 : L^(5 - sigma - eta) * L^(3 * sigma / 4 - 3 * eta / 2 - 3) =
        L^(2 - sigma / 4 - 5 * eta / 2) := by
      have h_exp : (5 - sigma - eta) + (3 * sigma / 4 - 3 * eta / 2 - 3) = 2 - sigma / 4 - 5 * eta / 2 := by ring
      rw [← Real.rpow_add hL_pos, h_exp]
    calc
      2 * C * L^(5 - sigma - eta) * (N' * N'^(3 / 2 : ℝ))
        = 2 * C * N' * (L^(5 - sigma - eta) * N'^(3 / 2 : ℝ)) := by ring
      _ ≤ 2 * C * N' * (L^(5 - sigma - eta) * L^(3 * sigma / 4 - 3 * eta / 2 - 3)) := by gcongr
      _ = 2 * C * N' * L^(2 - sigma / 4 - 5 * eta / 2) := by rw [h4] <;> ring

  -- Step 3: √Q ≥ 2*C*L^(-3σ/4+3η/2)
  have hQ_pos : 0 < Q := by
    have h7 : 0 < 4 * C^2 * L^(-3 * sigma / 2 + 3 * eta) := by positivity
    linarith
  set X : ℝ := 2 * C * L^(-3 * sigma / 4 + 3 * eta / 2) with hX_def
  have hX_nonneg : 0 ≤ X := by positivity
  have hX2 : X^2 = 4 * C^2 * L^(-3 * sigma / 2 + 3 * eta) := by
    have h5 : (L^(-3 * sigma / 4 + 3 * eta / 2))^2 =
        L^((-3 * sigma / 4 + 3 * eta / 2) * 2) := by
      have h51 : (L^(-3 * sigma / 4 + 3 * eta / 2))^2 =
          (L^(-3 * sigma / 4 + 3 * eta / 2))^(2 : ℝ) := by norm_cast
      rw [h51]
      exact Eq.symm (Real.rpow_mul hL_nonneg (-3 * sigma / 4 + 3 * eta / 2) (2 : ℝ))
    have h6 : (-3 * sigma / 4 + 3 * eta / 2) * 2 = -3 * sigma / 2 + 3 * eta := by ring
    calc
      X^2
        = (2 * C)^2 * (L^(-3 * sigma / 4 + 3 * eta / 2))^2 := by
          simp only [hX_def] <;> ring
      _ = 4 * C^2 * L^((-3 * sigma / 4 + 3 * eta / 2) * 2) := by rw [h5] <;> ring
      _ = 4 * C^2 * L^(-3 * sigma / 2 + 3 * eta) := by rw [h6] <;> ring
  have h_sqrt_Q : Real.sqrt Q ≥ X := by
    have h6 : X^2 ≤ Q := by
      rw [hX2] <;> exact hQ
    exact Real.le_sqrt_of_sq_le h6

  -- √τ = L^((σ-10η)/2)
  have h_sqrt_tau : Real.sqrt tau = L^((sigma - 10 * eta) / 2) := by
    rw [htau_eq]
    have h_rpow : (L^(sigma - 10 * eta))^(1 / 2 : ℝ) =
        L^((sigma - 10 * eta) * (1 / 2 : ℝ)) :=
      Eq.symm (Real.rpow_mul hL_nonneg (sigma - 10 * eta) (1 / 2 : ℝ))
    have h_mul : (sigma - 10 * eta) * (1 / 2 : ℝ) = (sigma - 10 * eta) / 2 := by ring
    have h : Real.sqrt (L^(sigma - 10 * eta)) = L^((sigma - 10 * eta) / 2) := by
      rw [Real.sqrt_eq_rpow, h_rpow, h_mul]
    exact h

  -- Step 4: RHS ≥ √Q * N * L^(σ/2+2-4η)
  have h4 : Real.sqrt (Q * tau) * mass ≥
      Real.sqrt Q * N' * L^(sigma / 2 + 2 - 4 * eta) := by
    have h_sqrt_mul : Real.sqrt (Q * tau) = Real.sqrt Q * Real.sqrt tau := by
      rw [Real.sqrt_mul] <;> linarith
    have hL_exp : L^((sigma - 10 * eta) / 2) * L^(2 + eta) =
        L^(sigma / 2 + 2 - 4 * eta) := by
      have h_exp : ((sigma - 10 * eta) / 2) + (2 + eta) = sigma / 2 + 2 - 4 * eta := by ring
      rw [← Real.rpow_add hL_pos, h_exp]
    calc
      Real.sqrt (Q * tau) * mass
        = Real.sqrt Q * Real.sqrt tau * mass := by rw [h_sqrt_mul] <;> ring
      _ = Real.sqrt Q * L^((sigma - 10 * eta) / 2) * mass := by rw [h_sqrt_tau] <;> ring
      _ ≥ Real.sqrt Q * L^((sigma - 10 * eta) / 2) * (N' * L^(2 + eta)) := by gcongr
      _ = Real.sqrt Q * N' * (L^((sigma - 10 * eta) / 2) * L^(2 + eta)) := by ring
      _ = Real.sqrt Q * N' * L^(sigma / 2 + 2 - 4 * eta) := by rw [hL_exp] <;> ring

  -- L^(-3σ/4+3η/2) * L^(σ/2+2-4η) = L^(2-σ/4-5η/2)
  have hL_exp4 : L^(-3 * sigma / 4 + 3 * eta / 2) * L^(sigma / 2 + 2 - 4 * eta) =
      L^(2 - sigma / 4 - 5 * eta / 2) := by
    have h_exp : (-3 * sigma / 4 + 3 * eta / 2) + (sigma / 2 + 2 - 4 * eta) = 2 - sigma / 4 - 5 * eta / 2 := by ring
    rw [← Real.rpow_add hL_pos, h_exp]

  calc
    2 * M * C * (L^2 * N')^(3 / 2 : ℝ)
      ≤ 2 * C * L^(5 - sigma - eta) * N'^(5 / 2 : ℝ) := h1
    _ ≤ 2 * C * N' * L^(2 - sigma / 4 - 5 * eta / 2) := h2
    _ = X * N' * L^(sigma / 2 + 2 - 4 * eta) := by
      have h : X * N' * L^(sigma / 2 + 2 - 4 * eta) =
          2 * C * N' * (L^(-3 * sigma / 4 + 3 * eta / 2) * L^(sigma / 2 + 2 - 4 * eta)) := by
        simp only [hX_def] <;> ring
      rw [h, hL_exp4] <;> ring
    _ ≤ Real.sqrt Q * N' * L^(sigma / 2 + 2 - 4 * eta) := by gcongr
    _ ≤ Real.sqrt (Q * tau) * mass := h4

/-- Existence of a natural Q satisfying the paper absorption threshold.

For any real threshold, the Archimedean property gives a natural number Q
at least as large. -/
lemma paper_absorption_Q_exists
    (L C sigma eta : ℝ)
    (hL_pos : 0 < L)
    (hC_pos : 0 < C) :
    ∃ (Q : ℕ), 4 * C^2 * L^(-3 * sigma / 2 + 3 * eta) ≤ (Q : ℝ) := by
  have h_nonneg : 0 ≤ 4 * C^2 * L^(-3 * sigma / 2 + 3 * eta) := by positivity
  obtain ⟨Q, hQ⟩ := exists_nat_ge (4 * C^2 * L^(-3 * sigma / 2 + 3 * eta))
  exact ⟨Q, by exact_mod_cast hQ⟩

/-- ENNReal bridge: lift real paper h_absorb inequality to ENNReal format.

Given the real inequality
  `2 * M * C * (a * N)^(3/2) ≤ √(Q * τ) * mass`
and ENNReal values bounded by these reals, derive the ENNReal inequality
  `2 * M_enn * C_enn * (ofReal a * F_enncard)^(3/2) ≤ ((Q : ENNReal) * ofReal τ)^(1/2) * S_mass`
-/
lemma paper_h_absorb_ennreal_bridge
    (a : ℝ)
    (N : ℕ)
    (C M mass tau : ℝ)
    (Q : ℕ)
    (C_enn M_enn S_mass F_enncard : ENNReal)
    (ha_nonneg : 0 ≤ a)
    (hC_nonneg : 0 ≤ C)
    (hM_nonneg : 0 ≤ M)
    (hmass_nonneg : 0 ≤ mass)
    (htau_pos : 0 < tau)
    (hN_pos : 0 < N)
    (h_real : 2 * M * C * (a * (N : ℝ))^(3 / 2 : ℝ) ≤
        Real.sqrt ((Q : ℝ) * tau) * mass)
    (hC_enn : C_enn ≤ ENNReal.ofReal C)
    (hM_enn : M_enn ≤ ENNReal.ofReal M)
    (hcard : F_enncard ≤ (N : ENNReal))
    (hmass_enn : ENNReal.ofReal mass ≤ S_mass) :
    (2 : ENNReal) * M_enn * C_enn *
        (ENNReal.ofReal a * F_enncard)^(3 / 2 : ℝ) ≤
      (((Q : ENNReal) * ENNReal.ofReal tau)^(1 / 2 : ℝ)) * S_mass := by
  have htau_nonneg : 0 ≤ tau := by linarith
  have hQ_real_nonneg : 0 ≤ (Q : ℝ) := by positivity
  have h_prod_nonneg : 0 ≤ (Q : ℝ) * tau := by positivity

  -- (Q : ENNReal) * ofReal tau = ofReal ((Q : ℝ) * tau)
  have h1 : (Q : ENNReal) * ENNReal.ofReal tau =
      ENNReal.ofReal ((Q : ℝ) * tau) := by
    have hQ_cast : (Q : ENNReal) = ENNReal.ofReal (Q : ℝ) := by norm_cast
    rw [hQ_cast, ← ENNReal.ofReal_mul hQ_real_nonneg]

  -- ((Q : ENNReal) * ofReal tau)^(1/2) = ofReal (Real.sqrt ((Q : ℝ) * tau))
  have h2 : (((Q : ENNReal) * ENNReal.ofReal tau)^(1 / 2 : ℝ)) =
      ENNReal.ofReal (Real.sqrt ((Q : ℝ) * tau)) := by
    rw [h1]
    have h3 : (ENNReal.ofReal ((Q : ℝ) * tau))^(1 / 2 : ℝ) =
        ENNReal.ofReal (((Q : ℝ) * tau)^(1 / 2 : ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg h_prod_nonneg (by norm_num)
    rw [h3]
    have h4 : ((Q : ℝ) * tau)^(1 / 2 : ℝ) = Real.sqrt ((Q : ℝ) * tau) := by
      rw [Real.sqrt_eq_rpow]
    rw [h4]

  -- ofReal a * F_enncard ≤ ofReal a * (N : ENNReal)
  have h5 : ENNReal.ofReal a * F_enncard ≤
      ENNReal.ofReal a * (N : ENNReal) := by
    gcongr

  -- (ofReal a * F_enncard)^(3/2) ≤ (ofReal a * (N : ENNReal))^(3/2)
  have h6 : (ENNReal.ofReal a * F_enncard)^(3 / 2 : ℝ) ≤
      (ENNReal.ofReal a * (N : ENNReal))^(3 / 2 : ℝ) := by
    gcongr <;> norm_num

  -- ofReal a * (N : ENNReal) = ofReal (a * (N : ℝ))
  have h7 : ENNReal.ofReal a * (N : ENNReal) =
      ENNReal.ofReal (a * (N : ℝ)) := by
    have hN_cast : (N : ENNReal) = ENNReal.ofReal (N : ℝ) := by norm_cast
    rw [hN_cast, ← ENNReal.ofReal_mul ha_nonneg]

  -- (ofReal (a * N))^(3/2) = ofReal ((a * N)^(3/2))
  have h8 : (ENNReal.ofReal (a * (N : ℝ)))^(3 / 2 : ℝ) =
      ENNReal.ofReal ((a * (N : ℝ))^(3 / 2 : ℝ)) :=
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)

  let P := (a * (N : ℝ))^(3 / 2 : ℝ)
  have hP_nonneg : 0 ≤ P := by positivity

  -- Combine ofReal products step by step
  have h_eq1 : ENNReal.ofReal C * ENNReal.ofReal P = ENNReal.ofReal (C * P) := by
    rw [← ENNReal.ofReal_mul hC_nonneg]
  have h_eq2 : ENNReal.ofReal M * (ENNReal.ofReal C * ENNReal.ofReal P) =
      ENNReal.ofReal (M * C * P) := by
    rw [h_eq1, ← ENNReal.ofReal_mul hM_nonneg]
    have h_ring : M * (C * P) = M * C * P := by ring
    rw [h_ring]
  have h2cast : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_cast
  have h_eq3 : (2 : ENNReal) * (ENNReal.ofReal M * (ENNReal.ofReal C * ENNReal.ofReal P)) =
      ENNReal.ofReal (2 * M * C * P) := by
    rw [h2cast, h_eq2, ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h_ring : (2 : ℝ) * (M * C * P) = 2 * M * C * P := by ring
    rw [h_ring]
  have h_assoc : (2 : ENNReal) * ENNReal.ofReal M * ENNReal.ofReal C * ENNReal.ofReal P =
      (2 : ENNReal) * (ENNReal.ofReal M * (ENNReal.ofReal C * ENNReal.ofReal P)) := by ring

  have h_main_eq : (2 : ENNReal) * ENNReal.ofReal M * ENNReal.ofReal C *
      (ENNReal.ofReal a * (N : ENNReal))^(3 / 2 : ℝ) =
      ENNReal.ofReal (2 * M * C * P) := by
    have h10 : (ENNReal.ofReal a * (N : ENNReal))^(3 / 2 : ℝ) = ENNReal.ofReal P := by
      rw [h7, h8]
    rw [h10, h_assoc, h_eq3]

  -- LHS ≤ ofReal (2 * M * C * (a * N)^(3/2))
  have h9 : (2 : ENNReal) * M_enn * C_enn *
        (ENNReal.ofReal a * F_enncard)^(3 / 2 : ℝ) ≤
      ENNReal.ofReal (2 * M * C * P) := by
    calc
      (2 : ENNReal) * M_enn * C_enn * (ENNReal.ofReal a * F_enncard)^(3 / 2 : ℝ)
        ≤ (2 : ENNReal) * ENNReal.ofReal M * ENNReal.ofReal C *
            (ENNReal.ofReal a * (N : ENNReal))^(3 / 2 : ℝ) := by
          gcongr
      _ = ENNReal.ofReal (2 * M * C * P) := h_main_eq

  have h10 : ENNReal.ofReal (2 * M * C * P) ≤
      ENNReal.ofReal (Real.sqrt ((Q : ℝ) * tau) * mass) := by
    apply ENNReal.ofReal_le_ofReal
    exact h_real

  have h11 : ENNReal.ofReal (Real.sqrt ((Q : ℝ) * tau) * mass) =
      ENNReal.ofReal (Real.sqrt ((Q : ℝ) * tau)) * ENNReal.ofReal mass := by
    rw [← ENNReal.ofReal_mul (by positivity)]

  calc
    (2 : ENNReal) * M_enn * C_enn * (ENNReal.ofReal a * F_enncard)^(3 / 2 : ℝ)
      ≤ ENNReal.ofReal (2 * M * C * P) := h9
    _ ≤ ENNReal.ofReal (Real.sqrt ((Q : ℝ) * tau) * mass) := h10
    _ = ENNReal.ofReal (Real.sqrt ((Q : ℝ) * tau)) * ENNReal.ofReal mass := h11
    _ = (((Q : ENNReal) * ENNReal.ofReal tau)^(1 / 2 : ℝ)) * ENNReal.ofReal mass := by
        rw [h2]
    _ ≤ (((Q : ENNReal) * ENNReal.ofReal tau)^(1 / 2 : ℝ)) * S_mass := by
        gcongr

/-!
## Rescaled fiber version

On the rescaled fiber at scale `δ'`, the geometric packing bound gives
`δ'^2 · |F_fiber| ≤ K` where `K` is a constant (roughly the packing
constant times loss factors). Thus `(δ'^2 · |F_fiber|)^(3/2) ≤ K^(3/2)`,
making the CV term O(1). The h_absorb condition simplifies to
`4·M²·C²·K³ ≤ Q·τ·mass²`.
-/

/-- Real arithmetic core for the rescaled fiber h_absorb condition.

Given `δ'^2 · N ≤ K` and `4·M²·C²·K³ ≤ Q·τ·mass²`, prove:
  `2·M·C·(δ'^2·N)^(3/2) ≤ √(Q·τ)·mass`

This is much simpler than the full shading version because the CV
term `(δ'^2 · N)^(3/2)` is bounded by the constant `K^(3/2)`.
-/
lemma paper_h_absorb_fiber_core
    (delta' K M C mass tau : ℝ)
    (N : ℕ)
    (Q : ℕ)
    (hdelta'_pos : 0 < delta')
    (hK_nonneg : 0 ≤ K)
    (hM_nonneg : 0 ≤ M)
    (hC_pos : 0 < C)
    (hmass_pos : 0 < mass)
    (htau_pos : 0 < tau)
    (hN_pos : 0 < N)
    (hN_bound : delta'^2 * (N : ℝ) ≤ K)
    (hQ : 4 * M^2 * C^2 * K^3 ≤ (Q : ℝ) * tau * mass^2) :
    2 * M * C * (delta'^2 * (N : ℝ))^(3 / 2 : ℝ) ≤
      Real.sqrt ((Q : ℝ) * tau) * mass := by
  have hN'_nonneg : 0 ≤ (N : ℝ) := by positivity
  have hdelta2_nonneg : 0 ≤ delta'^2 := by positivity
  have h_prod_nonneg : 0 ≤ delta'^2 * (N : ℝ) := by positivity

  -- (δ'^2 * N)^(3/2) ≤ K^(3/2)
  have h1 : (delta'^2 * (N : ℝ))^(3 / 2 : ℝ) ≤ K^(3 / 2 : ℝ) :=
    Real.rpow_le_rpow h_prod_nonneg hN_bound (by norm_num)

  -- LHS ≤ 2 * M * C * K^(3/2)
  have h2 : 2 * M * C * (delta'^2 * (N : ℝ))^(3 / 2 : ℝ) ≤
      2 * M * C * K^(3 / 2 : ℝ) := by
    gcongr

  -- (K^(3/2))^2 = K^3
  have hK3 : (K^(3 / 2 : ℝ))^2 = K^3 := by
    have h_cast : (K^(3 / 2 : ℝ))^2 = (K^(3 / 2 : ℝ))^(2 : ℝ) := by norm_cast
    rw [h_cast]
    have h : (K^(3 / 2 : ℝ))^(2 : ℝ) = K^((3 / 2 : ℝ) * (2 : ℝ)) :=
      Eq.symm (Real.rpow_mul hK_nonneg (3 / 2 : ℝ) (2 : ℝ))
    rw [h]
    have h2' : (3 / 2 : ℝ) * (2 : ℝ) = 3 := by norm_num
    rw [h2'] <;> norm_cast

  -- Square of LHS bound
  have h5 : (2 * M * C * K^(3 / 2 : ℝ))^2 = 4 * M^2 * C^2 * K^3 := by
    calc
      (2 * M * C * K^(3 / 2 : ℝ))^2
        = (2 * M * C)^2 * (K^(3 / 2 : ℝ))^2 := by ring
      _ = 4 * M^2 * C^2 * (K^(3 / 2 : ℝ))^2 := by ring
      _ = 4 * M^2 * C^2 * K^3 := by rw [hK3] <;> ring

  -- Square of RHS
  have h6 : (Real.sqrt ((Q : ℝ) * tau) * mass)^2 = (Q : ℝ) * tau * mass^2 := by
    have hQtau_nonneg : 0 ≤ (Q : ℝ) * tau := by positivity
    have h_sqrt_sq : (Real.sqrt ((Q : ℝ) * tau))^2 = (Q : ℝ) * tau :=
      Real.sq_sqrt hQtau_nonneg
    nlinarith

  -- Both sides non-negative
  have h3 : 0 ≤ 2 * M * C * K^(3 / 2 : ℝ) := by positivity
  have h4 : 0 ≤ Real.sqrt ((Q : ℝ) * tau) * mass := by positivity

  -- Square inequality implies inequality
  have h7 : (2 * M * C * K^(3 / 2 : ℝ))^2 ≤
      (Real.sqrt ((Q : ℝ) * tau) * mass)^2 := by
    rw [h5, h6] <;> exact hQ
  have h8 : 2 * M * C * K^(3 / 2 : ℝ) ≤
      Real.sqrt ((Q : ℝ) * tau) * mass := by
    nlinarith [h3, h4, h7]

  exact le_trans h2 h8

/-- Existence of Q for the rescaled fiber absorption condition.

For any real threshold `4M²C²K³/(τ·mass²)`, the Archimedean property
gives a natural number Q at least as large.
-/
lemma paper_absorption_fiber_Q_exists
    (K M C mass tau : ℝ)
    (hK_nonneg : 0 ≤ K)
    (hM_nonneg : 0 ≤ M)
    (hC_pos : 0 < C)
    (hmass_pos : 0 < mass)
    (htau_pos : 0 < tau) :
    ∃ (Q : ℕ), 4 * M^2 * C^2 * K^3 ≤ (Q : ℝ) * tau * mass^2 := by
  have htau_mass2_pos : 0 < tau * mass^2 := by positivity
  set threshold : ℝ := (4 * M^2 * C^2 * K^3) / (tau * mass^2) with hthreshold_def
  have hthreshold_nonneg : 0 ≤ threshold := by positivity
  obtain ⟨Q, hQ⟩ := exists_nat_ge threshold
  have h9 : threshold ≤ (Q : ℝ) := by exact_mod_cast hQ
  have h10 : 4 * M^2 * C^2 * K^3 ≤ (Q : ℝ) * tau * mass^2 := by
    have h11 : threshold = (4 * M^2 * C^2 * K^3) / (tau * mass^2) := by rfl
    rw [h11] at h9
    have h12 : (4 * M^2 * C^2 * K^3) / (tau * mass^2) ≤ (Q : ℝ) := h9
    have h13 : 4 * M^2 * C^2 * K^3 ≤ (Q : ℝ) * (tau * mass^2) := by
      calc
        4 * M^2 * C^2 * K^3
          = ((4 * M^2 * C^2 * K^3) / (tau * mass^2)) * (tau * mass^2) := by
            field_simp [htau_mass2_pos.ne']
        _ ≤ (Q : ℝ) * (tau * mass^2) := by gcongr
    simpa [mul_assoc] using h13
  exact ⟨Q, h10⟩

end Kakeya.Assouad

end
