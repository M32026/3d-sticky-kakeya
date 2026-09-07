import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.Statements
import MyLeanRepo.Kakeya.Assouad.LargeSlope.Step4WitnessPart1
import MyLeanRepo.Kakeya.Assouad.LargeSlope.Step4WitnessGeometry
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Step 4 witness — Mass bounds and parameter inequalities

This module provides:

1. **Parameter inequalities** relating `delta^eta`, `delta^(12*eta)`, and `sqrt rho`,
   using the strengthened hypothesis `delta^alpha ≤ 1/64` where
   `alpha = 10*eta - eta/1000`.
2. **Pruning lemma** for finite families of measurable sets: discarding sets
   below a threshold loses at most `N * threshold` mass.
3. **Total mass retention** after piece-level pruning.

These support the `total_piece_mass`, `piece_mass_lower`, and
`piece_mass_upper` fields of `LargeSlopeStep4Witness`.
-/

namespace Kakeya.Assouad

open Metric Set Finset MeasureTheory

/-- `11 * eta > alpha` when `eta > 0`. -/
lemma step4_eta_gt_alpha {eta : ℝ} (heta_pos : 0 < eta) :
    11 * eta > 10 * eta - eta / 1000 := by
  linarith

/-- `11 * eta - eta / 1000 > alpha` when `eta > 0`. -/
lemma step4_eta2_gt_alpha {eta : ℝ} (heta_pos : 0 < eta) :
    11 * eta - eta / 1000 > 10 * eta - eta / 1000 := by
  linarith

/-- `12 * eta > alpha` when `eta > 0`. -/
lemma step4_12eta_gt_alpha {eta : ℝ} (heta_pos : 0 < eta) :
    12 * eta > 10 * eta - eta / 1000 := by
  linarith

/--
For `0 < delta ≤ 1` and `x ≤ y`, we have `delta^y ≤ delta^x`.
-/
lemma step4_rpow_decreasing {delta x y : ℝ} (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (hxy : x ≤ y) : Real.rpow delta y ≤ Real.rpow delta x :=
  Real.rpow_le_rpow_of_exponent_le_or_ge (Or.inr ⟨hdelta, hdelta_le_one, hxy⟩)

/--
If `0 < delta ≤ 1`, then `delta^(12*eta) ≤ delta^(11*eta)`.
-/
lemma step4_delta_12eta_le_11eta {delta eta : ℝ} (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (heta_pos : 0 < eta) : Real.rpow delta (12 * eta) ≤ Real.rpow delta (11 * eta) :=
  step4_rpow_decreasing hdelta hdelta_le_one (by linarith)

/--
If `0 < delta ≤ 1` and `delta^alpha ≤ 1/64`, then `delta^(12*eta) ≤ 1/64`,
because `12*eta > alpha` and `0 < delta ≤ 1` implies `delta^x` is decreasing in `x`.
-/
lemma step4_delta_12eta_le
    {delta eta : ℝ} (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (heta_pos : 0 < eta)
    (hdelta_alpha : Real.rpow delta (10 * eta - eta / 1000) ≤ 1 / 64) :
    Real.rpow delta (12 * eta) ≤ 1 / 64 := by
  have h1 : (10 * eta - eta / 1000 : ℝ) ≤ (12 * eta : ℝ) := by linarith
  have h2 : Real.rpow delta (12 * eta) ≤ Real.rpow delta (10 * eta - eta / 1000) :=
    step4_rpow_decreasing hdelta hdelta_le_one h1
  exact h2.trans hdelta_alpha

/--
If `0 < delta ≤ 1` and `delta^alpha ≤ 1/64`, then `delta^(11*eta) ≤ 1/64`,
because `11*eta > alpha` and `0 < delta ≤ 1` implies `delta^x` is decreasing in `x`.
-/
lemma step4_delta_11eta_le
    {delta eta : ℝ} (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (heta_pos : 0 < eta)
    (hdelta_alpha : Real.rpow delta (10 * eta - eta / 1000) ≤ 1 / 64) :
    Real.rpow delta (11 * eta) ≤ 1 / 64 := by
  have h1 : (10 * eta - eta / 1000 : ℝ) ≤ (11 * eta : ℝ) := by linarith
  have hlog : Real.log delta ≤ 0 := Real.log_nonpos (by linarith) hdelta_le_one
  have h9 : (11 * eta) * Real.log delta ≤ (10 * eta - eta / 1000) * Real.log delta := by nlinarith
  have h7 : 0 < Real.rpow delta (11 * eta) := Real.rpow_pos_of_pos hdelta _
  have h8 : 0 < Real.rpow delta (10 * eta - eta / 1000) := Real.rpow_pos_of_pos hdelta _
  have hlog1 : Real.log (Real.rpow delta (11 * eta)) = (11 * eta) * Real.log delta :=
    Real.log_rpow hdelta (11 * eta)
  have hlog2 : Real.log (Real.rpow delta (10 * eta - eta / 1000)) = (10 * eta - eta / 1000) * Real.log delta :=
    Real.log_rpow hdelta (10 * eta - eta / 1000)
  have hlog_le : Real.log (Real.rpow delta (11 * eta)) ≤ Real.log (Real.rpow delta (10 * eta - eta / 1000)) := by
    rw [hlog1, hlog2] <;> exact h9
  have h2 : Real.rpow delta (11 * eta) ≤ Real.rpow delta (10 * eta - eta / 1000) :=
    (Real.log_le_log_iff h7 h8).mp hlog_le
  exact h2.trans hdelta_alpha

/--
If `0 < delta ≤ 1` and `delta^alpha ≤ 1/64`, then
`delta^(11*eta - eta/1000) ≤ 1/64`.
-/
lemma step4_delta_11eta_minus_le
    {delta eta : ℝ} (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (heta_pos : 0 < eta)
    (hdelta_alpha : Real.rpow delta (10 * eta - eta / 1000) ≤ 1 / 64) :
    Real.rpow delta (11 * eta - eta / 1000) ≤ 1 / 64 := by
  have h1 : (10 * eta - eta / 1000 : ℝ) ≤ (11 * eta - eta / 1000 : ℝ) := by linarith
  have hlog : Real.log delta ≤ 0 := Real.log_nonpos (by linarith) hdelta_le_one
  have h9 : (11 * eta - eta / 1000) * Real.log delta ≤ (10 * eta - eta / 1000) * Real.log delta := by nlinarith
  have h7 : 0 < Real.rpow delta (11 * eta - eta / 1000) := Real.rpow_pos_of_pos hdelta _
  have h8 : 0 < Real.rpow delta (10 * eta - eta / 1000) := Real.rpow_pos_of_pos hdelta _
  have hlog1 : Real.log (Real.rpow delta (11 * eta - eta / 1000)) = (11 * eta - eta / 1000) * Real.log delta :=
    Real.log_rpow hdelta (11 * eta - eta / 1000)
  have hlog2 : Real.log (Real.rpow delta (10 * eta - eta / 1000)) = (10 * eta - eta / 1000) * Real.log delta :=
    Real.log_rpow hdelta (10 * eta - eta / 1000)
  have hlog_le : Real.log (Real.rpow delta (11 * eta - eta / 1000)) ≤ Real.log (Real.rpow delta (10 * eta - eta / 1000)) := by
    rw [hlog1, hlog2] <;> exact h9
  have h2 : Real.rpow delta (11 * eta - eta / 1000) ≤ Real.rpow delta (10 * eta - eta / 1000) :=
    (Real.log_le_log_iff h7 h8).mp hlog_le
  exact h2.trans hdelta_alpha

/--
Key mass inequality:
`delta^(11*eta) + delta^(11*eta - eta/1000) ≤ 1/16`.

Uses `delta^alpha ≤ 1/64`, so each term is ≤ `1/64`, and their sum ≤ `1/32 < 1/16`.
-/
lemma step4_mass_sum_le
    {delta eta : ℝ} (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (heta_pos : 0 < eta)
    (hdelta_alpha : Real.rpow delta (10 * eta - eta / 1000) ≤ 1 / 64) :
    Real.rpow delta (11 * eta) + Real.rpow delta (11 * eta - eta / 1000) ≤ 1 / 16 := by
  have h1 : Real.rpow delta (11 * eta) ≤ 1 / 64 :=
    step4_delta_11eta_le hdelta hdelta_le_one heta_pos hdelta_alpha
  have h2 : Real.rpow delta (11 * eta - eta / 1000) ≤ 1 / 64 :=
    step4_delta_11eta_minus_le hdelta hdelta_le_one heta_pos hdelta_alpha
  have h3 : Real.rpow delta (11 * eta) + Real.rpow delta (11 * eta - eta / 1000) ≤
      1 / 64 + 1 / 64 := by linarith
  linarith

/--
Total mass comparison:
`delta^(12*eta) * sqrt rho ≤ (1/2) * delta^eta * (b-a)`.

Since `sqrt rho = 8*(b-a)`, this reduces to `16 * delta^(12*eta) ≤ delta^eta`,
i.e. `delta^(11*eta) ≤ 1/16`, which follows from `delta^(11*eta) ≤ 1/64`.
-/
lemma step4_total_mass_comparison
    {delta eta b a rho : ℝ} (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (heta_pos : 0 < eta) (hba_pos : 0 < b - a)
    (hsqrt_rho : Real.sqrt rho = 8 * (b - a))
    (hdelta_alpha : Real.rpow delta (10 * eta - eta / 1000) ≤ 1 / 64) :
    ENNReal.ofReal (Real.rpow delta (12 * eta) * Real.sqrt rho) ≤
    (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta * ENNReal.ofReal (b - a) := by
  have h1 : Real.rpow delta (11 * eta) ≤ 1 / 64 :=
    step4_delta_11eta_le hdelta hdelta_le_one heta_pos hdelta_alpha
  have h2 : Real.rpow delta (12 * eta) * Real.sqrt rho ≤
      (1 / 2 : ℝ) * Real.rpow delta eta * (b - a) := by
    have h3 : Real.rpow delta (12 * eta) = Real.rpow delta eta * Real.rpow delta (11 * eta) := by
      have h31 : Real.rpow delta (eta + 11 * eta) = Real.rpow delta eta * Real.rpow delta (11 * eta) :=
        Real.rpow_add hdelta eta (11 * eta)
      have h32 : eta + 11 * eta = 12 * eta := by ring
      rw [h32] at h31
      exact h31
    have h4 : 0 ≤ Real.rpow delta eta := Real.rpow_nonneg hdelta.le _
    have h5 : 0 ≤ b - a := by linarith
    have h6 : 8 * Real.rpow delta (11 * eta) ≤ 1 / 2 := by
      have h7 : Real.rpow delta (11 * eta) ≤ 1 / 64 := h1
      nlinarith
    calc
      Real.rpow delta (12 * eta) * Real.sqrt rho
        = (Real.rpow delta eta * Real.rpow delta (11 * eta)) * Real.sqrt rho := by rw [h3]
      _ = (Real.rpow delta eta * Real.rpow delta (11 * eta)) * (8 * (b - a)) := by rw [hsqrt_rho]
      _ = Real.rpow delta eta * (8 * Real.rpow delta (11 * eta) * (b - a)) := by ring
      _ ≤ Real.rpow delta eta * ((1 / 2 : ℝ) * (b - a)) := by gcongr
      _ = (1 / 2 : ℝ) * Real.rpow delta eta * (b - a) := by ring
  have h5 : 0 ≤ Real.rpow delta (12 * eta) * Real.sqrt rho := by
    apply mul_nonneg
    · exact Real.rpow_nonneg hdelta.le _
    · exact Real.sqrt_nonneg _
  have h6 : 0 ≤ (1 / 2 : ℝ) * Real.rpow delta eta * (b - a) := by
    have h61 : 0 ≤ Real.rpow delta eta := Real.rpow_nonneg hdelta.le _
    have h62 : 0 ≤ b - a := by linarith
    positivity
  have h7 : ENNReal.ofReal (Real.rpow delta (12 * eta) * Real.sqrt rho) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) * Real.rpow delta eta * (b - a)) :=
    ENNReal.ofReal_le_ofReal h2
  have h9 : 0 ≤ Real.rpow delta eta := Real.rpow_nonneg hdelta.le _
  have h10 : 0 ≤ b - a := by linarith
  have h11 : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have h121 : ENNReal.ofReal ((1 / 2 : ℝ) * Real.rpow delta eta) =
      ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (Real.rpow delta eta) := by
    rw [← ENNReal.ofReal_mul h11]
  have h12 : ENNReal.ofReal ((1 / 2 : ℝ) * Real.rpow delta eta * (b - a)) =
      ENNReal.ofReal ((1 / 2 : ℝ) * Real.rpow delta eta) * ENNReal.ofReal (b - a) := by
    rw [← ENNReal.ofReal_mul (show 0 ≤ (1 / 2 : ℝ) * Real.rpow delta eta by positivity)]
  have h13 : Kakeya.realRpowENN delta eta = ENNReal.ofReal (Real.rpow delta eta) := by rfl
  have h14 : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) := by
    simp [div_eq_mul_inv] <;> norm_cast
  have h8 : ENNReal.ofReal ((1 / 2 : ℝ) * Real.rpow delta eta * (b - a)) =
      (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta * ENNReal.ofReal (b - a) := by
    calc
      ENNReal.ofReal ((1 / 2 : ℝ) * Real.rpow delta eta * (b - a))
        = ENNReal.ofReal ((1 / 2 : ℝ) * Real.rpow delta eta) * ENNReal.ofReal (b - a) := h12
      _ = (ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (Real.rpow delta eta)) * ENNReal.ofReal (b - a) := by
          rw [h121]
      _ = ((1 / 2 : ENNReal) * ENNReal.ofReal (Real.rpow delta eta)) * ENNReal.ofReal (b - a) := by
          rw [h14]
      _ = (1 / 2 : ENNReal) * (ENNReal.ofReal (Real.rpow delta eta)) * ENNReal.ofReal (b - a) := by ring
      _ = (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta * ENNReal.ofReal (b - a) := by
          rw [h13]
  rw [h8] at h7
  exact h7

/--
Cardinality bound for prism centers:
`4 * C * (2/√ρ)^(1-σ) ≤ δ^(-12η) * ρ^((-1+σ)/2)`.

Uses `C ≤ δ^(-η/100)`, `2^(1-σ) ≤ 2`, and `δ^(-1199η/100) ≥ 64 > 8`.
-/
lemma step4_cardinality_bound
    {delta eta sigma rho C : ℝ}
    (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (heta_pos : 0 < eta) (hsigma_pos : 0 < sigma) (hsigma_one : sigma ≤ 1)
    (hrho_pos : 0 < rho) (hC_nonneg : 0 ≤ C)
    (hC : C ≤ Real.rpow delta (-(eta / 100)))
    (hdelta_alpha : Real.rpow delta (10 * eta - eta / 1000) ≤ 1 / 64) :
    4 * C * Real.rpow (2 / Real.sqrt rho) (1 - sigma) ≤
    Real.rpow delta (-(12 * eta)) * Real.rpow rho ((-1 + sigma) / 2) := by
  have h1 : Real.rpow (2 / Real.sqrt rho) (1 - sigma) =
      Real.rpow 2 (1 - sigma) * Real.rpow rho ((-1 + sigma) / 2) := by
    have h_pos1 : 0 < (2 / Real.sqrt rho) := by positivity
    have h_pos2' : 0 < (2 : ℝ) := by norm_num
    have h_pos_rpow2 : 0 < Real.rpow 2 (1 - sigma) := Real.rpow_pos_of_pos h_pos2' _
    have h_pos_rpow_rho : 0 < Real.rpow rho ((-1 + sigma) / 2) := Real.rpow_pos_of_pos hrho_pos _
    have h_left : Real.log (Real.rpow (2 / Real.sqrt rho) (1 - sigma)) =
        (1 - sigma) * Real.log (2 / Real.sqrt rho) := by
      have h := Real.log_rpow h_pos1 (1 - sigma)
      simpa using h
    have h_r1 : Real.log (Real.rpow 2 (1 - sigma)) = (1 - sigma) * Real.log 2 := by
      have h := Real.log_rpow h_pos2' (1 - sigma)
      simpa using h
    have h_r2 : Real.log (Real.rpow rho ((-1 + sigma) / 2)) =
        ((-1 + sigma) / 2) * Real.log rho := by
      have h := Real.log_rpow hrho_pos ((-1 + sigma) / 2)
      simpa using h
    have h_right : Real.log (Real.rpow 2 (1 - sigma) * Real.rpow rho ((-1 + sigma) / 2)) =
        (1 - sigma) * Real.log 2 + ((-1 + sigma) / 2) * Real.log rho := by
      rw [Real.log_mul h_pos_rpow2.ne' h_pos_rpow_rho.ne', h_r1, h_r2]
      <;> ring
    have h_sqrt_pos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho_pos
    have h_log_sqrt : Real.log (2 / Real.sqrt rho) = Real.log 2 - (1 / 2 : ℝ) * Real.log rho := by
      rw [Real.log_div (by norm_num) h_sqrt_pos.ne', Real.log_sqrt (by linarith)] <;> ring
    have h_eq_log : Real.log (Real.rpow (2 / Real.sqrt rho) (1 - sigma)) =
        Real.log (Real.rpow 2 (1 - sigma) * Real.rpow rho ((-1 + sigma) / 2)) := by
      rw [h_left, h_right, h_log_sqrt] <;> ring
    have h_pos4 : 0 < Real.rpow (2 / Real.sqrt rho) (1 - sigma) := Real.rpow_pos_of_pos h_pos1 _
    have h_pos5 : 0 < Real.rpow 2 (1 - sigma) * Real.rpow rho ((-1 + sigma) / 2) :=
      mul_pos h_pos_rpow2 h_pos_rpow_rho
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr h_pos4) (Set.mem_Ioi.mpr h_pos5) h_eq_log
  have h2 : Real.rpow 2 (1 - sigma) ≤ 2 := by
    have h22 : 1 - sigma ≤ 1 := by linarith
    have h_base : (1 : ℝ) ≤ 2 := by norm_num
    have h : Real.rpow 2 (1 - sigma) ≤ Real.rpow 2 (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h_base h22
    have h_rpow1 : Real.rpow 2 (1 : ℝ) = 2 := by simp
    rw [h_rpow1] at h
    exact h
  have h_rho_pos' : 0 < Real.rpow rho ((-1 + sigma) / 2) :=
    Real.rpow_pos_of_pos hrho_pos _
  have h3 : 4 * C * Real.rpow (2 / Real.sqrt rho) (1 - sigma) ≤
      8 * C * Real.rpow rho ((-1 + sigma) / 2) := by
    rw [h1]
    calc
      4 * C * (Real.rpow 2 (1 - sigma) * Real.rpow rho ((-1 + sigma) / 2))
        = 4 * (C * Real.rpow 2 (1 - sigma)) * Real.rpow rho ((-1 + sigma) / 2) := by ring
      _ ≤ 4 * (C * 2) * Real.rpow rho ((-1 + sigma) / 2) := by
        gcongr
        <;> linarith
      _ = 8 * C * Real.rpow rho ((-1 + sigma) / 2) := by ring
  have h_deltapow_pos : 0 < Real.rpow delta (-(eta / 100)) :=
    Real.rpow_pos_of_pos hdelta _
  have h4 : 8 * Real.rpow delta (-(eta / 100)) ≤ Real.rpow delta (-(12 * eta)) := by
    have h43 : Real.rpow delta (1199 * eta / 100) ≤ 1 / 8 := by
      have h44 : (10 * eta - eta / 1000 : ℝ) ≤ (1199 * eta / 100 : ℝ) := by linarith
      have h45 : Real.rpow delta (1199 * eta / 100) ≤ Real.rpow delta (10 * eta - eta / 1000) :=
        step4_rpow_decreasing hdelta hdelta_le_one h44
      have h46 : Real.rpow delta (1199 * eta / 100) ≤ 1 / 64 := h45.trans hdelta_alpha
      linarith
    have h47 : 0 < Real.rpow delta (1199 * eta / 100) := Real.rpow_pos_of_pos hdelta _
    have h49 : 8 ≤ (Real.rpow delta (1199 * eta / 100))⁻¹ := by
      have h : (Real.rpow delta (1199 * eta / 100))⁻¹ ≥ (1 / 8 : ℝ)⁻¹ := by gcongr
      norm_num at h ⊢ <;> linarith
    have h48 : Real.rpow delta (-(1199 * eta / 100)) = (Real.rpow delta (1199 * eta / 100))⁻¹ :=
      Real.rpow_neg hdelta.le (1199 * eta / 100)
    have h_sum : -(eta / 100) + (-(1199 * eta / 100)) = -(12 * eta) := by ring
    have h41 : Real.rpow delta (-(eta / 100)) * Real.rpow delta (-(1199 * eta / 100)) =
        Real.rpow delta (-(12 * eta)) := by
      have h_rpow := Real.rpow_add hdelta (-(eta / 100)) (-(1199 * eta / 100))
      rw [h_sum] at h_rpow
      exact h_rpow.symm
    have h_goal : 8 * Real.rpow delta (-(eta / 100)) ≤
        Real.rpow delta (-(eta / 100)) * (Real.rpow delta (1199 * eta / 100))⁻¹ := by
      have h_comm : Real.rpow delta (-(eta / 100)) * 8 = 8 * Real.rpow delta (-(eta / 100)) := by ring
      have h : Real.rpow delta (-(eta / 100)) * 8 ≤
          Real.rpow delta (-(eta / 100)) * (Real.rpow delta (1199 * eta / 100))⁻¹ :=
        mul_le_mul_of_nonneg_left h49 h_deltapow_pos.le
      rw [h_comm] at h
      exact h
    rw [← h41, h48]
    exact h_goal
  have h5 : 8 * C * Real.rpow rho ((-1 + sigma) / 2) ≤
      Real.rpow delta (-(12 * eta)) * Real.rpow rho ((-1 + sigma) / 2) := by
    have hC' : C ≤ Real.rpow delta (-(eta / 100)) := hC
    have h8C : 8 * C ≤ 8 * Real.rpow delta (-(eta / 100)) :=
      mul_le_mul_of_nonneg_left hC' (by norm_num)
    have h_step1 : (8 * C) * Real.rpow rho ((-1 + sigma) / 2) ≤
        (8 * Real.rpow delta (-(eta / 100))) * Real.rpow rho ((-1 + sigma) / 2) :=
      mul_le_mul_of_nonneg_right h8C h_rho_pos'.le
    have h_step2 : (8 * Real.rpow delta (-(eta / 100))) * Real.rpow rho ((-1 + sigma) / 2) ≤
        Real.rpow delta (-(12 * eta)) * Real.rpow rho ((-1 + sigma) / 2) :=
      mul_le_mul_of_nonneg_right h4 h_rho_pos'.le
    simpa [mul_assoc] using h_step1.trans h_step2
  exact h3.trans h5

/--
General pruning lemma for a finite families of measurable sets.

Given sets `S i` for `i ∈ s`, a threshold `t`, define pruned sets
`S' i = if volume(S i) ≥ t then S i else ∅`.

Then:
1. Every nonempty pruned set has volume ≥ `t`.
2. The total pruned mass is at least the original mass minus `s.card * t`.
-/
lemma finite_family_pruning
    {α : Type*} [Fintype α] {β : Type*} [MeasurableSpace β] [MeasureTheory.MeasureSpace β]
    (s : Finset α) (S : α → Set β) (hS : ∀ i, MeasurableSet (S i))
    (t : ENNReal) :
    ∃ (S' : α → Set β),
      (∀ i, MeasurableSet (S' i)) ∧
      (∀ i, S' i ⊆ S i) ∧
      (∀ i, volume (S' i) ≠ 0 → t ≤ volume (S' i)) ∧
      (∑ i ∈ s, volume (S i)) ≤ (∑ i ∈ s, volume (S' i)) + (s.card : ENNReal) * t := by
  classical
  let S' : α → Set β := fun i =>
    if h : t ≤ volume (S i) then S i else (∅ : Set β)
  have h_meas : ∀ i, MeasurableSet (S' i) := by
    intro i
    by_cases h : t ≤ volume (S i)
    · simp [S', h] <;> exact hS i
    · simp [S', h] <;> exact MeasurableSet.empty
  have h_sub : ∀ i, S' i ⊆ S i := by
    intro i
    by_cases h : t ≤ volume (S i)
    · simp [S', h]
    · simp [S', h] <;> exact Set.empty_subset _
  have h_lower : ∀ i, volume (S' i) ≠ 0 → t ≤ volume (S' i) := by
    intro i hne
    by_cases h : t ≤ volume (S i)
    · simpa [S', h] using h
    · have h' : S' i = (∅ : Set β) := by simp [S', h]
      rw [h'] at hne
      simp at hne <;> tauto
  have h_discard : ∀ i ∈ s, volume (S i) ≤ volume (S' i) + t := by
    intro i _
    by_cases h : t ≤ volume (S i)
    · simp [S', h] <;> linarith
    · have h' : S' i = (∅ : Set β) := by simp [S', h]
      have h'' : volume (S i) < t := by
        by_contra h3; exact h (le_of_not_gt h3)
      rw [h']
      simp <;> exact h''.le
  have h_sum : (∑ i ∈ s, volume (S i)) ≤
      (∑ i ∈ s, volume (S' i)) + (s.card : ENNReal) * t := by
    calc
      (∑ i ∈ s, volume (S i))
        ≤ ∑ i ∈ s, (volume (S' i) + t) := by
          apply Finset.sum_le_sum
          intro i hi
          exact h_discard i hi
      _ = (∑ i ∈ s, volume (S' i)) + (s.card : ENNReal) * t := by
          rw [Finset.sum_add_distrib, Finset.sum_const]
          <;> simp [mul_comm] <;> ring
  exact ⟨S', h_meas, h_sub, h_lower, h_sum⟩

/--
Volume of a vertical cylinder in `Point3`: Euclidean 2D disk of radius `delta`
in the xy-plane times an interval `[zlo, zhi]` on the z-axis.
-/
lemma step4_cylinder_volume
    (c2 : EuclideanSpace ℝ (Fin 2)) (delta : ℝ) (hdelta : 0 ≤ delta)
    (zlo zhi : ℝ) (h : zlo ≤ zhi) :
    MeasureTheory.volume {p : Point3 |
      dist (WithLp.toLp 2 (fun i : Fin 2 => p (Fin.castSucc i))) c2 ≤ delta ∧
      zlo ≤ p 2 ∧ p 2 ≤ zhi} =
    ENNReal.ofReal (Real.pi * delta^2 * (zhi - zlo)) := by
  let e1 : Point3 ≃ᵐ (Fin 3 → ℝ) :=
    { toFun := WithLp.ofLp
      invFun := WithLp.toLp 2
      left_inv := WithLp.ofLp_toLp 2
      right_inv := WithLp.ofLp_toLp 2
      measurable_toFun := (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin 3 => ℝ)).measurable
      measurable_invFun := (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).measurable }
  have h1 : MeasurePreserving e1 volume volume := PiLp.volume_preserving_ofLp (ι := Fin 3)
  let α : Fin 3 → Type _ := fun _ => ℝ
  let e2 : (Fin 3 → ℝ) ≃ᵐ (ℝ × (Fin 2 → ℝ)) := MeasurableEquiv.piFinSuccAbove α (2 : Fin 3)
  have h2 : MeasurePreserving e2 volume volume := MeasureTheory.volume_preserving_piFinSuccAbove α (2 : Fin 3)
  let e : Point3 ≃ᵐ (ℝ × (Fin 2 → ℝ)) := e1.trans e2
  have he : MeasurePreserving e volume volume := h2.comp h1
  let D : Set (Fin 2 → ℝ) := {x | dist (WithLp.toLp 2 x) c2 ≤ delta}
  let C : Set Point3 := {p |
    dist (WithLp.toLp 2 (fun i : Fin 2 => p (Fin.castSucc i))) c2 ≤ delta ∧
    zlo ≤ p 2 ∧ p 2 ≤ zhi}
  have h_succAbove : ∀ (i : Fin 2), Fin.succAbove (2 : Fin 3) i = Fin.castSucc i := by
    intro i; fin_cases i <;> simp [Fin.succAbove]
  have h_e_eval : ∀ (p : Point3), e p = (p 2, fun i : Fin 2 => p (Fin.castSucc i)) := by
    intro p
    have h1 : (e2 (e1 p)).1 = (e1 p) 2 := by rfl
    have h1' : (e1 p) 2 = p 2 := by simp [e1]
    have h2 : (e2 (e1 p)).2 = (fun i : Fin 2 => (e1 p) (Fin.succAbove (2 : Fin 3) i)) := by rfl
    have h3 : ∀ i : Fin 2, (e1 p) (Fin.succAbove (2 : Fin 3) i) = p (Fin.castSucc i) := by
      intro i; rw [h_succAbove i] <;> rfl
    have h2' : (e2 (e1 p)).2 = (fun i : Fin 2 => p (Fin.castSucc i)) := by
      rw [h2]; funext i; exact h3 i
    have h_e_def : e p = e2 (e1 p) := by simp [e]
    exact Prod.ext (by rw [h_e_def, h1, h1']) h2'
  have hC_meas : MeasurableSet C := by
    have hf1 : Measurable (fun p : Point3 => WithLp.toLp 2 (fun i : Fin 2 => p (Fin.castSucc i))) := by fun_prop
    have hf2 : Measurable (fun p : Point3 => p 2) := by fun_prop
    have hball : MeasurableSet (Metric.closedBall c2 delta) := measurableSet_closedBall
    have h1 : MeasurableSet {p : Point3 | dist (WithLp.toLp 2 (fun i : Fin 2 => p (Fin.castSucc i))) c2 ≤ delta} := by
      have h_eq : {p : Point3 | dist (WithLp.toLp 2 (fun i : Fin 2 => p (Fin.castSucc i))) c2 ≤ delta} =
          (fun p : Point3 => WithLp.toLp 2 (fun i : Fin 2 => p (Fin.castSucc i))) ⁻¹' (Metric.closedBall c2 delta) := by
        ext p; simp [Metric.mem_closedBall]
      rw [h_eq]; exact hball.preimage hf1
    have h2 : MeasurableSet {p : Point3 | zlo ≤ p 2 ∧ p 2 ≤ zhi} := by
      have h_pre : MeasurableSet ((fun p : Point3 => p 2) ⁻¹' Set.Icc zlo zhi) :=
        isClosed_Icc.measurableSet.preimage hf2
      have h_eq : {p : Point3 | zlo ≤ p 2 ∧ p 2 ≤ zhi} = (fun p : Point3 => p 2) ⁻¹' Set.Icc zlo zhi := by
        ext x; simp [Set.mem_preimage, Set.mem_Icc]
      rw [h_eq]; exact h_pre
    exact h1.inter h2
  have h_image : e '' C = (Set.Icc zlo zhi) ×ˢ D := by
    ext ⟨z, x⟩
    simp only [Set.mem_image, Set.mem_prod, C, D, Set.mem_setOf_eq]
    constructor
    · rintro ⟨p, hp, h_eq⟩
      have h_main : e p = (p 2, fun i : Fin 2 => p (Fin.castSucc i)) := h_e_eval p
      have hz : (e p).1 = p 2 := by rw [h_main]
      have hx : (e p).2 = (fun i : Fin 2 => p (Fin.castSucc i)) := by rw [h_main]
      have hz' : z = p 2 := by
        have h : (e p).1 = z := by rw [h_eq] <;> rfl
        exact h.symm.trans hz
      have hx' : x = (fun i : Fin 2 => p (Fin.castSucc i)) := by
        have h : (e p).2 = x := by rw [h_eq] <;> rfl
        exact h.symm.trans hx
      rw [hz', hx']; exact ⟨⟨hp.2.1, hp.2.2⟩, hp.1⟩
    · rintro ⟨⟨hz1, hz2⟩, hx⟩
      let p : Point3 := WithLp.toLp 2 (fun i : Fin 3 => match i with | 0 => x 0 | 1 => x 1 | 2 => z)
      have hpeq : (fun i : Fin 2 => p (Fin.castSucc i)) = x := by
        funext i; fin_cases i <;> simp [p] <;> rfl
      have hp1 : dist (WithLp.toLp 2 (fun i : Fin 2 => p (Fin.castSucc i))) c2 ≤ delta := by rw [hpeq]; exact hx
      have hp2 : zlo ≤ p 2 ∧ p 2 ≤ zhi := by
        have h_p2 : p 2 = z := by simp [p]
        rw [h_p2] <;> exact ⟨hz1, hz2⟩
      have h_ep : e p = (z, x) := by
        rw [h_e_eval p]
        apply Prod.ext
        · simp [p]
        · exact hpeq
      exact ⟨p, ⟨hp1, hp2.1, hp2.2⟩, h_ep⟩
  have h_volC : volume C = volume (e '' C) := by
    have h_img_meas : MeasurableSet (e '' C) := e.measurableSet_image.mpr hC_meas
    have h7 : volume (e ⁻¹' (e '' C)) = volume (e '' C) :=
      he.measure_preimage h_img_meas.nullMeasurableSet
    have h6 : e ⁻¹' (e '' C) = C := e.preimage_image C
    rw [h6] at h7
    exact h7
  have h_toLp2 : MeasurePreserving (WithLp.toLp 2 : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2)) volume volume :=
    PiLp.volume_preserving_toLp (ι := Fin 2)
  have hD : volume D = volume (Metric.closedBall c2 delta) := by
    have hD1 : D = (WithLp.toLp 2) ⁻¹' (Metric.closedBall c2 delta) := by ext x; simp [D]
    rw [hD1]; exact h_toLp2.measure_preimage measurableSet_closedBall.nullMeasurableSet
  rw [h_volC, h_image]
  have h_vol_eq : (volume : Measure (ℝ × (Fin 2 → ℝ))) = (volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ)) :=
    Measure.volume_eq_prod ℝ (Fin 2 → ℝ)
  rw [h_vol_eq, MeasureTheory.Measure.prod_prod (Set.Icc zlo zhi) D, Real.volume_Icc, hD]
  rw [EuclideanSpace.volume_closedBall_fin_two c2 delta]
  have h1 : ENNReal.ofReal delta ^ 2 = ENNReal.ofReal (delta^2) := by
    have h_pow : ENNReal.ofReal delta ^ 2 = ENNReal.ofReal delta * ENNReal.ofReal delta := by
      simp [pow_two]
    rw [h_pow]
    have h_mul : ENNReal.ofReal delta * ENNReal.ofReal delta = ENNReal.ofReal (delta * delta) := by
      rw [← ENNReal.ofReal_mul hdelta]
    rw [h_mul]
    have hsq : delta * delta = delta^2 := by ring
    rw [hsq]
  rw [h1]
  have hpos1 : 0 ≤ zhi - zlo := by linarith
  have h4 : 0 ≤ (zhi - zlo) * delta^2 := by positivity
  have h_step1 : ENNReal.ofReal (zhi - zlo) * ENNReal.ofReal (delta^2) = ENNReal.ofReal ((zhi - zlo) * delta^2) := by
    rw [← ENNReal.ofReal_mul hpos1]
  have h_step2 : ENNReal.ofReal ((zhi - zlo) * delta^2) * ENNReal.ofReal Real.pi = ENNReal.ofReal (((zhi - zlo) * delta^2) * Real.pi) := by
    rw [← ENNReal.ofReal_mul h4]
  have h_assoc : ENNReal.ofReal (zhi - zlo) * (ENNReal.ofReal (delta^2) * ENNReal.ofReal Real.pi) =
      (ENNReal.ofReal (zhi - zlo) * ENNReal.ofReal (delta^2)) * ENNReal.ofReal Real.pi := by rw [mul_assoc]
  rw [h_assoc, h_step1, h_step2]
  apply congr_arg ENNReal.ofReal; ring
/-- The 2D norm of the xy-projection is at most the 3D norm. -/
lemma xy_proj_norm_le (w : Point3) :
    ‖(WithLp.toLp 2 (fun i : Fin 2 => w (Fin.castSucc i)))‖ ≤ ‖w‖ := by
  set x2 : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun i : Fin 2 => w (Fin.castSucc i)) with hx2
  have hx2_norm_sq : ‖x2‖ ^ 2 = ∑ i : Fin 2, (x2 i) ^ 2 :=
    EuclideanSpace.real_norm_sq_eq x2
  have hw_norm_sq : ‖w‖ ^ 2 = ∑ i : Fin 3, (w i) ^ 2 :=
    EuclideanSpace.real_norm_sq_eq w
  have h3 : ‖x2‖ ^ 2 = ∑ i : Fin 2, (w (Fin.castSucc i)) ^ 2 := by
    rw [hx2_norm_sq]
    <;> congr
    <;> funext i <;> simp [hx2]
  have h_sum2_eq : ∑ i : Fin 2, (w (Fin.castSucc i)) ^ 2 = (w 0)^2 + (w 1)^2 := by
    have h_univ2 : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
    rw [h_univ2]
    simp [Finset.sum_insert, Finset.sum_singleton, Fin.castSucc]
    <;> ring
  have h_sum3_eq : ∑ i : Fin 3, (w i) ^ 2 = (w 0)^2 + (w 1)^2 + (w 2)^2 := by
    have h_univ3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    rw [h_univ3]
    simp [Finset.sum_insert, Finset.sum_singleton]
    <;> ring
  have h_sum2 : ∑ i : Fin 2, (w (Fin.castSucc i)) ^ 2 ≤ ∑ i : Fin 3, (w i) ^ 2 := by
    rw [h_sum2_eq, h_sum3_eq]
    <;> linarith [sq_nonneg (w 2)]
  have h9 : ‖x2‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [h3, hw_norm_sq]
    exact h_sum2
  nlinarith [norm_nonneg x2, norm_nonneg w]

/--
Volume upper bound for a tube segment intersected with a horizontal slab.
-/
lemma tube_slab_volume_upper
    {delta a b : ℝ} (hdelta : 0 < delta) (hab : a < b)
    {T : Kakeya.DeltaTube delta}
    (hvert : (1 / 2 : ℝ) ≤ |T.direction (2 : Fin 3)|)
    (hba_small : b - a ≤ 1 / 16)
    (hdelta_le_sq : delta ≤ (b - a)^2) :
    MeasureTheory.volume (T.carrier ∩ horizontalSlab a b) ≤
    ENNReal.ofReal (delta^2 * 8 * (b - a)) := by
  let e3 : Point3 := EuclideanSpace.single 2 (1 : ℝ)
  let d := T.direction
  let b0 := T.base
  let K : Submodule ℝ Point3 := (Submodule.span ℝ {d - e3})ᗮ
  let A : Point3 ≃ₗᵢ[ℝ] Point3 := K.reflection

  have he3_norm : ‖e3‖ = 1 := by
    have h : ‖e3‖ ^ 2 = ∑ i : Fin 3, (e3 i)^2 := EuclideanSpace.real_norm_sq_eq e3
    have h2 : ∑ i : Fin 3, (e3 i)^2 = 1 := by
      have h_univ3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
      rw [h_univ3]
      simp [Finset.sum_insert, Finset.sum_singleton, e3, EuclideanSpace.single_apply]
      <;> norm_num
    have h3 : ‖e3‖ ^ 2 = 1 := by rw [h, h2]
    have h4 : 0 ≤ ‖e3‖ := norm_nonneg e3
    nlinarith

  have hA_dir : A d = e3 :=
    Submodule.reflection_sub (T.direction_unit.trans he3_norm.symm)

  let c := A b0
  let c2 : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun i : Fin 2 => c (Fin.castSucc i))
  let d2 := d (2 : Fin 3)
  have h_d2_ne_zero : d2 ≠ 0 := by
    intro h
    have hvert' : (1 / 2 : ℝ) ≤ |d2| := by simpa [d2, d] using hvert
    rw [h] at hvert'
    <;> norm_num at hvert'

  let S := T.carrier ∩ horizontalSlab a b

  have h_seg_compact : IsCompact (unitSegment b0 d) :=
    isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))

  have hT_meas : MeasurableSet T.carrier := by
    have h_closed : IsClosed (Metric.cthickening delta (unitSegment b0 d)) :=
      Metric.isClosed_cthickening
    have h_eq : T.carrier = Metric.cthickening delta (unitSegment b0 d) := by
      rfl
    rw [h_eq]
    exact h_closed.measurableSet

  have hSlab_meas : MeasurableSet (horizontalSlab a b) := by
    have h2 : Continuous (fun x : Point3 => x (2 : Fin 3)) := by fun_prop
    have h_eq : horizontalSlab a b = (fun x : Point3 => x (2 : Fin 3)) ⁻¹' Set.Icc a b := by
      ext x; simp [horizontalSlab]
    rw [h_eq]
    exact isClosed_Icc.measurableSet.preimage h2.measurable

  have hS_meas : MeasurableSet S := hT_meas.inter hSlab_meas

  let A_meas : Point3 ≃ᵐ Point3 := A.toMeasurableEquiv
  let S' := A '' S
  have h_preimg : A ⁻¹' S' = S := Set.preimage_image_eq S A.injective
  have h_vol : volume S = volume S' := by
    have h : volume (A ⁻¹' S') = volume S' :=
      A.measurePreserving.measure_preimage_emb A_meas.measurableEmbedding S'
    rw [h_preimg] at h
    exact h

  set tlo := if 0 < d2 then (a - delta - b0 (2 : Fin 3)) / d2 else (b + delta - b0 (2 : Fin 3)) / d2 with htlo
  set thi := if 0 < d2 then (b + delta - b0 (2 : Fin 3)) / d2 else (a - delta - b0 (2 : Fin 3)) / d2 with hthi
  set zlo := c (2 : Fin 3) + tlo - delta with hzlo
  set zhi := c (2 : Fin 3) + thi + delta with hzhi

  have h_t_bounds : ∀ (p : Point3), p ∈ S →
      ∃ (t : ℝ) (v : Point3), ‖v‖ ≤ delta ∧ p = b0 + t • d + v ∧ tlo ≤ t ∧ t ≤ thi := by
    intro p hp
    rcases tube_carrier_witness hdelta hp.1 with ⟨t, _ht, hdist⟩
    let v := p - (b0 + t • d)
    have hv_norm : ‖v‖ ≤ delta := by
      have h : dist p (b0 + t • d) ≤ delta := hdist
      simpa [dist_eq_norm] using h
    have hv_eq : p = b0 + t • d + v := by
      simp [v] <;> abel
    have h_p2 : a ≤ p (2 : Fin 3) ∧ p (2 : Fin 3) ≤ b := hp.2
    have h_v2 : |v (2 : Fin 3)| ≤ delta := by
      have h : |v (2 : Fin 3)| ≤ ‖v‖ := coord_abs_le_norm v 2
      linarith
    have h_lower : a - delta ≤ b0 (2 : Fin 3) + t * d2 := by
      have h_eq : b0 (2 : Fin 3) + t * d2 = p (2 : Fin 3) - v (2 : Fin 3) := by
        simp [v, d2] <;> ring
      rw [h_eq]
      linarith [abs_le.mp h_v2, h_p2.1]
    have h_upper : b0 (2 : Fin 3) + t * d2 ≤ b + delta := by
      have h_eq : b0 (2 : Fin 3) + t * d2 = p (2 : Fin 3) - v (2 : Fin 3) := by
        simp [v, d2] <;> ring
      rw [h_eq]
      linarith [abs_le.mp h_v2, h_p2.2]
    by_cases hpos : 0 < d2
    · have h_tlo' : tlo ≤ t := by
        rw [htlo, if_pos hpos]
        have h : (a - delta - b0 (2 : Fin 3)) ≤ t * d2 := by linarith
        have h' : (a - delta - b0 (2 : Fin 3)) / d2 ≤ (t * d2) / d2 := by gcongr
        have h'' : (t * d2) / d2 = t := by field_simp [hpos.ne'] <;> ring
        rw [h''] at h'; exact h'
      have h_thi' : t ≤ thi := by
        rw [hthi, if_pos hpos]
        have h : t * d2 ≤ b + delta - b0 (2 : Fin 3) := by linarith
        have h' : (t * d2) / d2 ≤ (b + delta - b0 (2 : Fin 3)) / d2 := by gcongr
        have h'' : (t * d2) / d2 = t := by field_simp [hpos.ne'] <;> ring
        rw [h''] at h'; exact h'
      exact ⟨t, v, hv_norm, hv_eq, h_tlo', h_thi'⟩
    · have hneg : d2 < 0 := by by_contra h; exact h_d2_ne_zero (by linarith)
      have h_tlo' : tlo ≤ t := by
        rw [htlo, if_neg (show ¬(0 < d2) from by linarith)]
        have h9 : (b + delta - b0 (2 : Fin 3)) - t * d2 ≥ 0 := by linarith
        have h10 : (b + delta - b0 (2 : Fin 3)) / d2 - t ≤ 0 := by
          have h11 : (b + delta - b0 (2 : Fin 3)) / d2 - t =
              ((b + delta - b0 (2 : Fin 3)) - t * d2) / d2 := by
            field_simp [hneg.ne] <;> ring
          rw [h11]
          apply div_nonpos_of_nonneg_of_nonpos h9
          <;> linarith
        linarith
      have h_thi' : t ≤ thi := by
        rw [hthi, if_neg (show ¬(0 < d2) from by linarith)]
        have h9 : t * d2 - (a - delta - b0 (2 : Fin 3)) ≥ 0 := by linarith
        have h10 : t - (a - delta - b0 (2 : Fin 3)) / d2 ≤ 0 := by
          have h11 : t - (a - delta - b0 (2 : Fin 3)) / d2 =
              (t * d2 - (a - delta - b0 (2 : Fin 3))) / d2 := by
            field_simp [hneg.ne] <;> ring
          rw [h11]
          apply div_nonpos_of_nonneg_of_nonpos h9
          <;> linarith
        linarith
      exact ⟨t, v, hv_norm, hv_eq, h_tlo', h_thi'⟩

  have h_thi_tlo_nonneg : 0 ≤ thi - tlo := by
    by_cases hpos : 0 < d2
    · rw [htlo, hthi, if_pos hpos, if_pos hpos]
      have h : (b + delta - b0 (2 : Fin 3)) / d2 - (a - delta - b0 (2 : Fin 3)) / d2 =
          (b - a + 2 * delta) / d2 := by
        field_simp [hpos.ne'] <;> ring
      rw [h]
      apply div_nonneg <;> linarith
    · have hneg : d2 < 0 := by by_contra h; exact h_d2_ne_zero (by linarith)
      rw [htlo, hthi, if_neg (show ¬(0 < d2) from by linarith), if_neg (show ¬(0 < d2) from by linarith)]
      have h_abs : |d2| = -d2 := abs_of_neg hneg
      have h2 : ((a - delta - b0 (2 : Fin 3)) / d2) - ((b + delta - b0 (2 : Fin 3)) / d2) =
          (b - a + 2 * delta) / |d2| := by
        rw [h_abs]; field_simp [hneg.ne] <;> ring
      rw [h2]
      apply div_nonneg <;> linarith

  have h_zlo_le_zhi : zlo ≤ zhi := by
    have h : zhi - zlo = thi - tlo + 2 * delta := by
      dsimp only [zlo, zhi]; ring
    have h' : 0 ≤ thi - tlo := h_thi_tlo_nonneg
    have h'' : 0 ≤ zhi - zlo := by
      rw [h]
      linarith [hdelta]
    exact sub_nonneg.mp h''

  have h_height : zhi - zlo ≤ 2 * (b - a) + 6 * delta := by
    have h_diff : zhi - zlo = thi - tlo + 2 * delta := by
      dsimp only [zlo, zhi]; ring
    rw [h_diff]
    by_cases hpos : 0 < d2
    · have h1 : thi - tlo = (b - a + 2 * delta) / d2 := by
        rw [htlo, hthi, if_pos hpos, if_pos hpos]
        field_simp [hpos.ne'] <;> ring
      rw [h1]
      have h3 : 1 / d2 ≤ 2 := by
        have h4 : |d2| = d2 := abs_of_pos hpos
        have h5 : 1 / |d2| ≤ 2 := by
          have h6 : 1 / |d2| ≤ 1 / (1 / 2 : ℝ) := by gcongr
          have h7 : (1 / (1 / 2 : ℝ)) = 2 := by norm_num
          rw [h7] at h6; exact h6
        rw [h4] at h5; exact h5
      have h5 : 0 ≤ b - a + 2 * delta := by linarith
      have h6 : (b - a + 2 * delta) / d2 ≤ 2 * (b - a + 2 * delta) := by
        calc (b - a + 2 * delta) / d2
            = (b - a + 2 * delta) * (1 / d2) := by ring
          _ ≤ (b - a + 2 * delta) * 2 := by gcongr
          _ = 2 * (b - a + 2 * delta) := by ring
      linarith
    · have hneg : d2 < 0 := by by_contra h; exact h_d2_ne_zero (by linarith)
      have h_abs : |d2| = -d2 := abs_of_neg hneg
      have h1 : thi - tlo = (b - a + 2 * delta) / |d2| := by
        rw [htlo, hthi, if_neg (show ¬(0 < d2) from by linarith), if_neg (show ¬(0 < d2) from by linarith), h_abs]
        field_simp [hneg.ne] <;> ring
      rw [h1]
      have h3 : 1 / |d2| ≤ 2 := by
        have h4 : 1 / |d2| ≤ 1 / (1 / 2 : ℝ) := by gcongr
        have h5 : (1 / (1 / 2 : ℝ)) = 2 := by norm_num
        rw [h5] at h4; exact h4
      have h4 : 0 ≤ b - a + 2 * delta := by linarith
      have h6 : (b - a + 2 * delta) / |d2| ≤ 2 * (b - a + 2 * delta) := by
        calc (b - a + 2 * delta) / |d2|
            = (b - a + 2 * delta) * (1 / |d2|) := by ring
          _ ≤ (b - a + 2 * delta) * 2 := by gcongr
          _ = 2 * (b - a + 2 * delta) := by ring
      linarith

  let Cyl : Set Point3 := {p |
    dist (WithLp.toLp 2 (fun i : Fin 2 => p (Fin.castSucc i))) c2 ≤ delta ∧
    zlo ≤ p (2 : Fin 3) ∧ p (2 : Fin 3) ≤ zhi}

  have h_contain : S' ⊆ Cyl := by
    intro q hq
    rcases hq with ⟨p, hp, rfl⟩
    rcases h_t_bounds p hp with ⟨t, v, hv_norm, hv_eq, htlo, hthi⟩
    let w := A v
    have hw_norm : ‖w‖ ≤ delta := by
      have h : ‖w‖ = ‖v‖ := A.norm_map v
      rw [h]; exact hv_norm
    have hq_eq : A p = c + t • e3 + w := by
      rw [hv_eq]
      simp [c, hA_dir, A.map_add, A.map_smul] <;> abel
    have h_xy : dist (WithLp.toLp 2 (fun i : Fin 2 => (A p) (Fin.castSucc i))) c2 ≤ delta := by
      have h1 : (fun i : Fin 2 => (A p) (Fin.castSucc i)) - (fun i : Fin 2 => c (Fin.castSucc i)) =
          (fun i : Fin 2 => w (Fin.castSucc i)) := by
        funext i
        have h_ne_two : (Fin.castSucc i : Fin 3) ≠ 2 := by
          fin_cases i <;> simp [Fin.castSucc] <;> decide
        rw [hq_eq]
        simp [e3, EuclideanSpace.single_apply, h_ne_two] <;> ring
      have h2 : dist (WithLp.toLp 2 (fun i : Fin 2 => (A p) (Fin.castSucc i))) c2 =
          ‖(WithLp.toLp 2 (fun i : Fin 2 => w (Fin.castSucc i)))‖ := by
        have h_c2 : c2 = WithLp.toLp 2 (fun i : Fin 2 => c (Fin.castSucc i)) := by rfl
        rw [h_c2, dist_eq_norm]
        have h3 : (WithLp.toLp 2 (fun i : Fin 2 => (A p) (Fin.castSucc i))) -
                 (WithLp.toLp 2 (fun i : Fin 2 => c (Fin.castSucc i))) =
                 WithLp.toLp 2 (fun i : Fin 2 => w (Fin.castSucc i)) := by
          have h4 : (WithLp.toLp 2 (fun i : Fin 2 => (A p) (Fin.castSucc i))) -
                   (WithLp.toLp 2 (fun i : Fin 2 => c (Fin.castSucc i))) =
                   WithLp.toLp 2 ((fun i : Fin 2 => (A p) (Fin.castSucc i)) - (fun i : Fin 2 => c (Fin.castSucc i))) := by
            simpa [WithLp.toLp_sub] using rfl
          rw [h4, h1]
        rw [h3]
      rw [h2]
      have h5 : ‖(WithLp.toLp 2 (fun i : Fin 2 => w (Fin.castSucc i)))‖ ≤ ‖w‖ := xy_proj_norm_le w
      linarith
    have h_z : zlo ≤ (A p) (2 : Fin 3) ∧ (A p) (2 : Fin 3) ≤ zhi := by
      have h3 : (A p) (2 : Fin 3) = c (2 : Fin 3) + t + w (2 : Fin 3) := by
        rw [hq_eq]
        simp [e3, EuclideanSpace.single_apply] <;> ring
      have h4 : |w (2 : Fin 3)| ≤ delta := by
        have h5 : |w (2 : Fin 3)| ≤ ‖w‖ := coord_abs_le_norm w 2
        linarith
      rw [h3, hzlo, hzhi]
      constructor <;> linarith [abs_le.mp h4]
    exact ⟨h_xy, h_z.1, h_z.2⟩

  have h_cyl_vol : volume Cyl = ENNReal.ofReal (Real.pi * delta^2 * (zhi - zlo)) :=
    step4_cylinder_volume c2 delta hdelta.le zlo zhi h_zlo_le_zhi

  have h_num : Real.pi * delta^2 * (zhi - zlo) ≤ delta^2 * 8 * (b - a) := by
    have h1 : 6 * delta ≤ (3 / 8 : ℝ) * (b - a) := by
      have h11 : delta ≤ (b - a)^2 := hdelta_le_sq
      have h12 : 0 < b - a := by linarith
      nlinarith
    have h2 : zhi - zlo ≤ (19 / 8 : ℝ) * (b - a) := by
      linarith [h_height, h1]
    have h3 : Real.pi ≤ 64 / 19 := by
      have h4 : Real.pi < 3.1416 := Real.pi_lt_d4
      linarith
    have h5 : Real.pi * (zhi - zlo) ≤ 8 * (b - a) := by
      calc Real.pi * (zhi - zlo)
          ≤ Real.pi * ((19 / 8 : ℝ) * (b - a)) := by gcongr
        _ = (Real.pi * (19 / 8 : ℝ)) * (b - a) := by ring
        _ ≤ ((64 / 19 : ℝ) * (19 / 8 : ℝ)) * (b - a) := by gcongr
        _ = 8 * (b - a) := by ring
    have h6 : 0 ≤ delta^2 := by positivity
    have h7 : Real.pi * delta^2 * (zhi - zlo) = delta^2 * (Real.pi * (zhi - zlo)) := by ring
    rw [h7]
    have h10 : delta ^ 2 * (Real.pi * (zhi - zlo)) ≤ delta ^ 2 * (8 * (b - a)) :=
      mul_le_mul_of_nonneg_left h5 h6
    have h9 : delta ^ 2 * (8 * (b - a)) = delta ^ 2 * 8 * (b - a) := by ring
    rw [h9] at h10
    exact h10

  calc
    volume S
      = volume S' := h_vol
    _ ≤ volume Cyl := measure_mono h_contain
    _ = ENNReal.ofReal (Real.pi * delta^2 * (zhi - zlo)) := h_cyl_vol
    _ ≤ ENNReal.ofReal (delta^2 * 8 * (b - a)) := ENNReal.ofReal_le_ofReal h_num

/--
Parameter choice lemma for Step 4.

Given `0 < epsilon ≤ 1/2` and `0 < sigma < 1`, choose `eta` and `delta₀` such that:
- `0 < eta`, `eta ≤ epsilon`, `1000 * eta ≤ epsilon * sigma^2`
- `0 < delta₀ ≤ 1`
- For all `0 < delta ≤ delta₀`:
  - `delta ≤ 1/256`
  - `delta^(10*eta - eta/1000) ≤ 1/64`
  - `8 * delta^(10*eta - eta/1000) ≤ 1/2`
  - `delta^epsilon ≤ 1/16`
- `delta^(2*eta - eta/1000) ≤ 1/64`

Chooses `eta = epsilon * sigma^2 / 2000` and
`delta₀ = min(1/256, (1/64)^(1/alpha), (1/16)^(1/epsilon), (1/64)^(1/beta))`
where `alpha = 10*eta - eta/1000` and `beta = 2*eta - eta/1000`.
-/
lemma step4_parameter_choice
    (epsilon sigma : ℝ)
    (hepsilon_pos : 0 < epsilon)
    (hepsilon_half : epsilon ≤ 1 / 2)
    (hsigma_pos : 0 < sigma)
    (hsigma_one : sigma < 1) :
    ∃ (eta delta₀ : ℝ),
      0 < eta ∧ eta ≤ epsilon ∧
      1000 * eta ≤ epsilon * sigma ^ 2 ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ delta₀ →
        (delta ≤ 1 / 256) ∧
        (Real.rpow delta (10 * eta - eta / 1000) ≤ 1 / 64) ∧
        (8 * Real.rpow delta (10 * eta - eta / 1000) ≤ 1 / 2) ∧
        (Real.rpow delta epsilon ≤ 1 / 16) ∧
        (Real.rpow delta (2 * eta - eta / 1000) ≤ 1 / 64) := by
  let eta : ℝ := epsilon * sigma ^ 2 / 2000
  have heta_pos : 0 < eta := by
    dsimp only [eta]
    positivity
  have heta_le_epsilon : eta ≤ epsilon := by
    dsimp only [eta]
    have h1 : sigma ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have h1000eta : 1000 * eta ≤ epsilon * sigma ^ 2 := by
    dsimp only [eta]
    nlinarith
  let alpha : ℝ := 10 * eta - eta / 1000
  have halpha_pos : 0 < alpha := by
    dsimp only [alpha]
    linarith [heta_pos]
  let beta : ℝ := 2 * eta - eta / 1000
  have hbeta_pos : 0 < beta := by
    dsimp only [beta]
    linarith [heta_pos]
  let d1 : ℝ := (1 / 64 : ℝ) ^ (1 / alpha)
  let d2 : ℝ := (1 / 16 : ℝ) ^ (1 / epsilon)
  let d3 : ℝ := (1 / 64 : ℝ) ^ (1 / beta)
  have hd1_pos : 0 < d1 := by positivity
  have hd2_pos : 0 < d2 := by positivity
  have hd3_pos : 0 < d3 := by positivity
  let delta₀ : ℝ := min (1 / 256) (min d1 (min d2 d3))
  have hdelta₀_pos : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀_le_one : delta₀ ≤ 1 := by
    have h : delta₀ ≤ 1 / 256 := by
      exact min_le_left _ _
    linarith
  have hdelta₀_le_256 : delta₀ ≤ 1 / 256 := by
    dsimp only [delta₀]
    exact min_le_left _ _
  have hdelta₀_le_d1 : delta₀ ≤ d1 := by
    dsimp only [delta₀]
    have h : min (1 / 256) (min d1 (min d2 d3)) ≤ min d1 (min d2 d3) := min_le_right _ _
    exact h.trans (min_le_left _ _)
  have hdelta₀_le_d2 : delta₀ ≤ d2 := by
    dsimp only [delta₀]
    have h : min (1 / 256) (min d1 (min d2 d3)) ≤ min d1 (min d2 d3) := min_le_right _ _
    have h2 : min d1 (min d2 d3) ≤ min d2 d3 := by
      exact min_le_right _ _
    have h3 : min d2 d3 ≤ d2 := min_le_left d2 d3
    exact le_trans (le_trans h h2) h3
  have hdelta₀_le_d3 : delta₀ ≤ d3 := by
    dsimp only [delta₀]
    have h : min (1 / 256) (min d1 (min d2 d3)) ≤ min d1 (min d2 d3) := min_le_right _ _
    have h2 : min d1 (min d2 d3) ≤ min d2 d3 := by
      exact min_le_right _ _
    have h3 : min d2 d3 ≤ d3 := min_le_right d2 d3
    exact le_trans (le_trans h h2) h3
  have h_main : ∀ (delta : ℝ), 0 < delta → delta ≤ delta₀ →
      (delta ≤ 1 / 256) ∧
      (Real.rpow delta (10 * eta - eta / 1000) ≤ 1 / 64) ∧
      (8 * Real.rpow delta (10 * eta - eta / 1000) ≤ 1 / 2) ∧
      (Real.rpow delta epsilon ≤ 1 / 16) ∧
      (Real.rpow delta (2 * eta - eta / 1000) ≤ 1 / 64) := by
    intro delta hdelta_pos hdelta_le
    have h1 : delta ≤ 1 / 256 := by
      calc delta ≤ delta₀ := hdelta_le
           _ ≤ 1 / 256 := hdelta₀_le_256
    have h2 : Real.rpow delta alpha ≤ 1 / 64 := by
      have h3 : delta ≤ d1 := hdelta_le.trans hdelta₀_le_d1
      have h4 : Real.rpow delta alpha ≤ Real.rpow d1 alpha :=
        Real.rpow_le_rpow (by linarith) h3 (by linarith)
      have h5 : Real.rpow d1 alpha = 1 / 64 := by
        dsimp only [d1]
        have h6 : Real.rpow ((1 / 64 : ℝ) ^ (1 / alpha)) alpha =
            Real.rpow (1 / 64 : ℝ) ((1 / alpha) * alpha) :=
          step4_real_rpow_rpow (by norm_num) (1 / alpha) alpha
        rw [h6]
        have h7 : (1 / alpha) * alpha = 1 := by field_simp [halpha_pos.ne']
        rw [h7]; norm_num
      rw [h5] at h4
      exact h4
    have h3 : 8 * Real.rpow delta alpha ≤ 1 / 2 := by
      have h4 : Real.rpow delta alpha ≤ 1 / 64 := h2
      linarith
    have h4 : Real.rpow delta epsilon ≤ 1 / 16 := by
      have h5 : delta ≤ d2 := hdelta_le.trans hdelta₀_le_d2
      have h6 : Real.rpow delta epsilon ≤ Real.rpow d2 epsilon :=
        Real.rpow_le_rpow (by linarith) h5 (by linarith)
      have h7 : Real.rpow d2 epsilon = 1 / 16 := by
        dsimp only [d2]
        have h8 : Real.rpow ((1 / 16 : ℝ) ^ (1 / epsilon)) epsilon =
            Real.rpow (1 / 16 : ℝ) ((1 / epsilon) * epsilon) :=
          step4_real_rpow_rpow (by norm_num) (1 / epsilon) epsilon
        rw [h8]
        have h9 : (1 / epsilon) * epsilon = 1 := by field_simp [hepsilon_pos.ne']
        rw [h9]; norm_num
      rw [h7] at h6
      exact h6
    have h2' : Real.rpow delta (10 * eta - eta / 1000) ≤ 1 / 64 := by
      have h_eq : alpha = 10 * eta - eta / 1000 := by rfl
      rw [h_eq] at h2
      exact h2
    have h3' : 8 * Real.rpow delta (10 * eta - eta / 1000) ≤ 1 / 2 := by
      have h_eq : alpha = 10 * eta - eta / 1000 := by rfl
      rw [h_eq] at h3
      exact h3
    have h5 : Real.rpow delta beta ≤ 1 / 64 := by
      have h6 : delta ≤ d3 := hdelta_le.trans hdelta₀_le_d3
      have h7 : Real.rpow delta beta ≤ Real.rpow d3 beta :=
        Real.rpow_le_rpow (by linarith) h6 (by linarith)
      have h8 : Real.rpow d3 beta = 1 / 64 := by
        dsimp only [d3]
        have h9 : Real.rpow ((1 / 64 : ℝ) ^ (1 / beta)) beta =
            Real.rpow (1 / 64 : ℝ) ((1 / beta) * beta) :=
          step4_real_rpow_rpow (by norm_num) (1 / beta) beta
        rw [h9]
        have h10 : (1 / beta) * beta = 1 := by field_simp [hbeta_pos.ne']
        rw [h10]; norm_num
      rw [h8] at h7
      exact h7
    have h5' : Real.rpow delta (2 * eta - eta / 1000) ≤ 1 / 64 := by
      have h_eq : beta = 2 * eta - eta / 1000 := by rfl
      rw [h_eq] at h5
      exact h5
    exact ⟨h1, h2', h3', h4, h5'⟩
  exact ⟨eta, delta₀, heta_pos, heta_le_epsilon, h1000eta, hdelta₀_pos, hdelta₀_le_one, h_main⟩

end Kakeya.Assouad
