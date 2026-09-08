import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.FixedDepthPowerGridKRatioGate.Proof
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.AllScaleBalancedFromDilatedCover
import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.FrostmanMonotonicity
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# All-scale uniformity power bound

Bounds the uniformity constant of an `AllScaleBalancedFromDilatedCoverPackage`
constructed from the fixed-depth power grid, given explicit bounds on the
conflict constant and fiber uniformity.

## Proof route

1. Each grid interval has ratio `r = δ^(-1/N)`, and `K_grid = max 2 (2*cVol r) ≥ r`.
2. Degree at each cut: `Nat.ceil(conflictConstant * r^4) ≤ conflictConstant * K_grid^4 + 1`.
3. With `conflictConstant ≤ C_conf * K_grid^7`, degree cut ≤ `C_conf * K_grid^11 + 1`.
4. K-ratio gate: `K_grid ≤ C_K * δ^(-3/N)`, so `K_grid^11 ≤ C_K^11 * δ^(-33/N)`.
5. Sum over `N` cuts: `degreeFactor ≤ degreeConst * δ^(-33/N)`.
6. Combine with `fiber_uniformity ≤ δ^(-ε)` and absorb the constant via
   `h_absorb` (obtained from `exists_delta_pow_bound`).

## Whiteprint

Supports node `node10_raw_socket` (A7b2 uniformity discharge).
-/

noncomputable section

open BigOperators Kakeya.Streamlined
open Kakeya.Streamlined.RandomTranslation
open Kakeya.Streamlined.RandomTranslation.WithShading

namespace Kakeya.Streamlined.RandomTranslation.WithShading

/-- Uniformity bound for the all-scale structure.

Given explicit bounds on `conflictConstant` and `fiber_uniformity`,
bound `uniformity ≤ δ^(-eta₁)`.

The caller must supply `h_absorb` to absorb the multiplicative constant.
This can be obtained from `exists_delta_pow_bound` with
`γ = eta₁ - 33/N - epsilon > 0`.
-/
lemma allScaleUniformityBound
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    {N : ℕ} (hN : 0 < N)
    {grid : FixedDepthPowerGrid delta N}
    (conflictConstant : ℝ) (hconflict_pos : 0 < conflictConstant)
    (degree : Fin N → ℕ)
    (hdegree_eq : ∀ i, degree i = Nat.ceil (conflictConstant *
      ((grid.increasingScale (Fin.succ i)).1 / (grid.increasingScale (Fin.castSucc i)).1)^4))
    (uniformity fiber_uniformity branchingLoss degreeFactor : ENNReal)
    (huniformity_eq : uniformity = branchingLoss * (degreeFactor * fiber_uniformity))
    (hdegreeFactor_eq : degreeFactor = ↑(allScaleBalancedFromDilatedCoverDegreeFactor degree))
    (eta₁ epsilon : ℝ) (_heta₁ : 0 < eta₁) (_hepsilon : 0 < epsilon)
    (hexp : (33 : ℝ) / (N : ℝ) + epsilon < eta₁)
    -- conflictConstant ≤ C_conf * K^7
    (C_conf : ENNReal) (_hC_pos : 0 < C_conf)
    (hconflict_le : (ENNReal.ofReal conflictConstant) ≤ C_conf * (ENNReal.ofReal (fixedDepthPowerGridKRatio delta N))^7)
    -- fiber_uniformity ≤ δ^(-ε)
    (hfiber : fiber_uniformity ≤ Kakeya.realRpowENN delta (-epsilon))
    -- constant absorption (from pow_absorb with a = 0, b = eta₁ - 33/N - epsilon)
    (h_absorb : branchingLoss * (C_conf * (ENNReal.ofReal (2 + Real.pi + 8 / 3 * Real.pi))^11 * (N : ENNReal) + ((N : ENNReal) + 1)) ≤
      Kakeya.realRpowENN delta (-(eta₁ - (33 / (N : ℝ)) - epsilon))) :
    uniformity ≤ Kakeya.realRpowENN delta (-eta₁) := by
  let K := fixedDepthPowerGridKRatio delta N
  let r : ℝ := Real.rpow delta (-(1 / (N : ℝ)))
  let C_K : ENNReal := ENNReal.ofReal (2 + Real.pi + 8 / 3 * Real.pi)
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hslack_pos : 0 < eta₁ - (33 / (N : ℝ)) - epsilon := by linarith

  -- r ≥ 1 since delta ≤ 1 and exponent is non-positive
  have hr_ge_one : 1 ≤ r := by
    have h3 : -(1 / (N : ℝ)) ≤ 0 := by
      have h4 : (0 : ℝ) < 1 / (N : ℝ) := by positivity
      linarith
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdelta_one h3
  have hr_nonneg : 0 ≤ r := by linarith

  have hr_enn : Kakeya.realRpowENN delta (-(1 / (N : ℝ))) = ENNReal.ofReal r := by
    simp [Kakeya.realRpowENN, r]

  -- Gate theorem gives K bound
  have hgate := fixed_depth_power_grid_k_ratio_gate (delta := delta) (N := N) hdelta hdelta_one hN grid
  have hK_le : (ENNReal.ofReal K) ≤ C_K * Kakeya.realRpowENN delta (-(3 / (N : ℝ))) := by
    have h := hgate.2.1
    simpa [C_K] using h

  -- ratio = r for every grid interval
  have hratio_eq : ∀ (i : Fin N),
      (grid.increasingScale (Fin.succ i)).1 / (grid.increasingScale (Fin.castSucc i)).1 = r := by
    intro i
    set succVal : ℝ := (grid.increasingScale (Fin.succ i)).1 with hsucc
    set castVal : ℝ := (grid.increasingScale (Fin.castSucc i)).1 with hcast
    have hcast_pos : 0 < castVal := by
      have h : delta ≤ castVal := (grid.increasingScale (Fin.castSucc i)).2.1
      linarith
    have hsucc_pos : 0 < succVal := by
      have h : delta ≤ succVal := (grid.increasingScale (Fin.succ i)).2.1
      linarith
    have h1 : ENNReal.ofReal succVal =
        Kakeya.realRpowENN delta (-(1 / (N : ℝ))) * ENNReal.ofReal castVal :=
      grid.increasingScale_ratio i
    have h_mul : ENNReal.ofReal succVal = ENNReal.ofReal (r * castVal) := by
      have h2 : ENNReal.ofReal (r * castVal) = ENNReal.ofReal r * ENNReal.ofReal castVal := by
        rw [ENNReal.ofReal_mul] <;> linarith
      rw [h2, ← hr_enn]
      exact h1
    have h_eq : succVal = r * castVal := by
      have h_toReal : (ENNReal.ofReal succVal).toReal = (ENNReal.ofReal (r * castVal)).toReal := by
        rw [h_mul]
      rw [ENNReal.toReal_ofReal hsucc_pos.le, ENNReal.toReal_ofReal (by positivity)] at h_toReal
      exact h_toReal
    field_simp [hcast_pos.ne'] <;> linarith

  -- r ≥ 1 implies 2 * cVol r ≥ r
  have h_cVol_ge : r ≤ 2 * cVol r := by
    have h5 : 2 * cVol r = (Real.pi + 8 / 3 * Real.pi * r) * r ^ 2 := by
      simp [cVol] <;> ring
    rw [h5]
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have h6 : 1 ≤ Real.pi + 8 / 3 * Real.pi * r := by nlinarith [hr_ge_one]
    have h7 : r ≤ r ^ 2 := by nlinarith [hr_ge_one]
    have h8 : r ^ 2 ≤ (Real.pi + 8 / 3 * Real.pi * r) * r ^ 2 := by
      have h9 : 0 ≤ r ^ 2 := by positivity
      nlinarith
    linarith

  -- K = max 2 (2 * cVol r), so K ≥ r
  have h_rpow_nonneg : 0 ≤ Real.rpow delta (-(1 / (N : ℝ))) := Real.rpow_nonneg hdelta.le _
  have h_r_toReal : (Kakeya.realRpowENN delta (-(1 / (N : ℝ)))).toReal = r := by
    have h1 : Kakeya.realRpowENN delta (-(1 / (N : ℝ))) = ENNReal.ofReal (Real.rpow delta (-(1 / (N : ℝ)))) := by
      simp [Kakeya.realRpowENN]
    rw [h1, ENNReal.toReal_ofReal h_rpow_nonneg]
    <;> rfl
  have hK_ge_r : r ≤ K := by
    have hK_eq : K = max 2 (2 * cVol r) := by
      unfold K fixedDepthPowerGridKRatio
      congr
      <;> exact h_r_toReal
    rw [hK_eq]
    exact le_max_of_le_right h_cVol_ge

  -- ratio ≤ K
  have hratio_le : ∀ (i : Fin N),
      (grid.increasingScale (Fin.succ i)).1 / (grid.increasingScale (Fin.castSucc i)).1 ≤ K := by
    intro i
    have h_eq := hratio_eq i
    rw [h_eq]
    exact hK_ge_r

  -- degree cut ≤ conflictConstant * ratio^4 + 1 ≤ C_conf * K^11 + 1
  have hdegree_le : ∀ (i : Fin N),
      (degree i : ENNReal) ≤ C_conf * (ENNReal.ofReal K)^11 + 1 := by
    intro i
    set ratio := (grid.increasingScale (Fin.succ i)).1 / (grid.increasingScale (Fin.castSucc i)).1 with hratio_def
    have hsucc_pos : 0 < (grid.increasingScale (Fin.succ i)).1 := by
      have h : delta ≤ (grid.increasingScale (Fin.succ i)).1 := (grid.increasingScale (Fin.succ i)).2.1
      linarith
    have hcast_pos : 0 < (grid.increasingScale (Fin.castSucc i)).1 := by
      have h : delta ≤ (grid.increasingScale (Fin.castSucc i)).1 := (grid.increasingScale (Fin.castSucc i)).2.1
      linarith
    have hratio_nonneg : 0 ≤ ratio := by
      rw [hratio_def] <;> positivity
    let x := conflictConstant * ratio^4
    have hx_nonneg : 0 ≤ x := by positivity
    have h21 : (Nat.ceil x : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hx_nonneg).le
    have h221 : (Nat.ceil x : ENNReal) = ENNReal.ofReal (Nat.ceil x) := by simp
    have h22 : (Nat.ceil x : ENNReal) ≤ ENNReal.ofReal (x + 1) := by
      rw [h221]
      exact ENNReal.ofReal_le_ofReal h21
    have h23 : ENNReal.ofReal (x + 1) = ENNReal.ofReal x + 1 := by
      have h : ENNReal.ofReal (x + 1) = ENNReal.ofReal x + ENNReal.ofReal (1 : ℝ) := by
        rw [ENNReal.ofReal_add] <;> positivity
      rw [h]
      have h2 : ENNReal.ofReal (1 : ℝ) = (1 : ENNReal) := by simp
      rw [h2]
    have hratio4 : ENNReal.ofReal (ratio^4) = (ENNReal.ofReal ratio)^4 := by
      rw [ENNReal.ofReal_pow] <;> positivity
    have h24 : ENNReal.ofReal x = ENNReal.ofReal conflictConstant * ENNReal.ofReal (ratio^4) := by
      rw [ENNReal.ofReal_mul] <;> positivity
    have h2 : (Nat.ceil x : ENNReal) ≤
        ENNReal.ofReal conflictConstant * (ENNReal.ofReal ratio)^4 + 1 := by
      rw [h23, h24, hratio4] at h22
      exact h22
    have h3 : (ENNReal.ofReal ratio)^4 ≤ (ENNReal.ofReal K)^4 := by
      have h4 : ratio ≤ K := hratio_le i
      gcongr
    have h4 : ENNReal.ofReal conflictConstant ≤ C_conf * (ENNReal.ofReal K)^7 := hconflict_le
    have h1 : (degree i : ENNReal) = (Nat.ceil x : ENNReal) := by
      rw [hdegree_eq i]
      <;> rfl
    rw [h1]
    calc
      (Nat.ceil x : ENNReal)
        ≤ ENNReal.ofReal conflictConstant * (ENNReal.ofReal ratio)^4 + 1 := h2
      _ ≤ ENNReal.ofReal conflictConstant * (ENNReal.ofReal K)^4 + 1 := by gcongr
      _ ≤ C_conf * (ENNReal.ofReal K)^7 * (ENNReal.ofReal K)^4 + 1 := by gcongr
      _ = C_conf * (ENNReal.ofReal K)^11 + 1 := by
        simp [pow_succ] <;> ring

  -- degreeFactor ≤ C_conf * K^11 * N + (N + 1)
  have hdegFactor :
      degreeFactor ≤ C_conf * (ENNReal.ofReal K)^11 * (N : ENNReal) + ((N : ENNReal) + 1) := by
    rw [hdegreeFactor_eq]
    have hsum : (∑ cut : Fin N, degree cut : ENNReal) ≤
        (N : ENNReal) * (C_conf * (ENNReal.ofReal K)^11 + 1) := by
      calc
        (∑ cut : Fin N, degree cut : ENNReal)
          ≤ ∑ cut : Fin N, (C_conf * (ENNReal.ofReal K)^11 + 1) := by
            apply Finset.sum_le_sum
            intro i _
            exact hdegree_le i
        _ = (N : ENNReal) * (C_conf * (ENNReal.ofReal K)^11 + 1) := by
          simp [Finset.sum_const, Finset.card_fin] <;> ring
    have h_main : (↑(allScaleBalancedFromDilatedCoverDegreeFactor degree) : ENNReal) ≤
        C_conf * (ENNReal.ofReal K)^11 * (N : ENNReal) + ((N : ENNReal) + 1) := by
      simp only [allScaleBalancedFromDilatedCoverDegreeFactor]
      calc
        (↑(1 + ∑ cut : Fin N, degree cut) : ENNReal)
          = 1 + (∑ cut : Fin N, degree cut : ENNReal) := by simp
        _ ≤ 1 + (N : ENNReal) * (C_conf * (ENNReal.ofReal K)^11 + 1) := by gcongr
        _ = C_conf * (ENNReal.ofReal K)^11 * (N : ENNReal) + ((N : ENNReal) + 1) := by ring
    exact h_main

  -- K^11 ≤ C_K^11 * δ^(-33/N)
  have hK11 : (ENNReal.ofReal K)^11 ≤ C_K^11 * Kakeya.realRpowENN delta (-(33 / (N : ℝ))) := by
    calc
      (ENNReal.ofReal K)^11
        ≤ (C_K * Kakeya.realRpowENN delta (-(3 / (N : ℝ))))^11 := by gcongr <;> exact hK_le
      _ = C_K^11 * (Kakeya.realRpowENN delta (-(3 / (N : ℝ))))^11 := by ring
      _ = C_K^11 * Kakeya.realRpowENN delta (-(33 / (N : ℝ))) := by
        have h1a : Kakeya.realRpowENN delta (-(3 / (N : ℝ))) =
            ENNReal.ofReal (Real.rpow delta (-(3 / (N : ℝ)))) := by
          simp [Kakeya.realRpowENN]
        have h_rpow3_nonneg : 0 ≤ Real.rpow delta (-(3 / (N : ℝ))) := Real.rpow_nonneg hdelta.le _
        have h1 : (Kakeya.realRpowENN delta (-(3 / (N : ℝ))))^11 =
            ENNReal.ofReal ((Real.rpow delta (-(3 / (N : ℝ))))^11) := by
          rw [h1a]
          rw [← ENNReal.ofReal_pow h_rpow3_nonneg 11]
        rw [h1]
        have h2a : Real.rpow delta ((-(3 / (N : ℝ))) * (11 : ℝ)) =
            (Real.rpow delta (-(3 / (N : ℝ))))^11 :=
          Real.rpow_mul_natCast hdelta.le (-(3 / (N : ℝ))) 11
        have h2 : (Real.rpow delta (-(3 / (N : ℝ))))^11 = Real.rpow delta (-(33 / (N : ℝ))) := by
          rw [← h2a] <;> ring_nf
        rw [h2]
        <;> simp [Kakeya.realRpowENN]

  let degreeConst : ENNReal := C_conf * C_K^11 * (N : ENNReal) + ((N : ENNReal) + 1)

  -- δ^(-33/N) ≥ 1 since δ ≤ 1
  have hdelta_pow_ge_one : (1 : ENNReal) ≤ Kakeya.realRpowENN delta (-(33 / (N : ℝ))) := by
    have h1 : -(33 / (N : ℝ)) ≤ 0 := by
      have h2 : (0 : ℝ) < 33 / (N : ℝ) := by positivity
      linarith
    have h3 : 1 ≤ Real.rpow delta (-(33 / (N : ℝ))) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdelta_one h1
    simpa [Kakeya.realRpowENN, ENNReal.one_le_ofReal] using h3

  -- degreeFactor ≤ degreeConst * δ^(-33/N)
  have hdegFactor2 : degreeFactor ≤ degreeConst * Kakeya.realRpowENN delta (-(33 / (N : ℝ))) := by
    calc
      degreeFactor
        ≤ C_conf * (ENNReal.ofReal K)^11 * (N : ENNReal) + ((N : ENNReal) + 1) := hdegFactor
      _ ≤ C_conf * (C_K^11 * Kakeya.realRpowENN delta (-(33 / (N : ℝ)))) * (N : ENNReal) + ((N : ENNReal) + 1) := by
          gcongr
      _ = (C_conf * C_K^11 * (N : ENNReal)) * Kakeya.realRpowENN delta (-(33 / (N : ℝ))) + ((N : ENNReal) + 1) := by ring
      _ ≤ (C_conf * C_K^11 * (N : ENNReal)) * Kakeya.realRpowENN delta (-(33 / (N : ℝ))) + ((N : ENNReal) + 1) * Kakeya.realRpowENN delta (-(33 / (N : ℝ))) := by
          have h6 : ((N : ENNReal) + 1) ≤ ((N : ENNReal) + 1) * Kakeya.realRpowENN delta (-(33 / (N : ℝ))) := by
            have h7 : (1 : ENNReal) ≤ Kakeya.realRpowENN delta (-(33 / (N : ℝ))) := hdelta_pow_ge_one
            simpa [mul_one] using mul_le_mul_of_nonneg_left h7 (by positivity)
          exact add_le_add le_rfl h6
      _ = degreeConst * Kakeya.realRpowENN delta (-(33 / (N : ℝ))) := by
          simp [degreeConst] <;> ring

  rw [huniformity_eq]
  calc
    branchingLoss * (degreeFactor * fiber_uniformity)
      ≤ branchingLoss * (degreeConst * Kakeya.realRpowENN delta (-(33 / (N : ℝ))) *
            Kakeya.realRpowENN delta (-epsilon)) := by gcongr
    _ = (branchingLoss * degreeConst) *
          (Kakeya.realRpowENN delta (-(33 / (N : ℝ))) *
            Kakeya.realRpowENN delta (-epsilon)) := by ring
    _ ≤ (branchingLoss * degreeConst) *
          Kakeya.realRpowENN delta (-((33 / (N : ℝ)) + epsilon)) := by
        have h_rpow_add : Kakeya.realRpowENN delta (-(33 / (N : ℝ))) * Kakeya.realRpowENN delta (-epsilon) =
            Kakeya.realRpowENN delta (-((33 / (N : ℝ)) + epsilon)) := by
          simp only [Kakeya.realRpowENN]
          set a := (-(33 / (N : ℝ))) with ha
          set b := (-epsilon) with hb
          have h_nonneg_a : 0 ≤ Real.rpow delta a := Real.rpow_nonneg hdelta.le _
          have h_mul : (Real.rpow delta a) * (Real.rpow delta b) = Real.rpow delta (a + b) :=
            (Real.rpow_add hdelta a b).symm
          have h_enn_mul : ENNReal.ofReal ((Real.rpow delta a) * (Real.rpow delta b)) =
              ENNReal.ofReal (Real.rpow delta a) * ENNReal.ofReal (Real.rpow delta b) :=
            ENNReal.ofReal_mul (p := Real.rpow delta a) (q := Real.rpow delta b) h_nonneg_a
          have h_sum : a + b = -((33 / (N : ℝ)) + epsilon) := by
            simp [ha, hb] <;> ring
          rw [← h_enn_mul, h_mul, h_sum]
        rw [h_rpow_add]
    _ ≤ Kakeya.realRpowENN delta (-(eta₁ - (33 / (N : ℝ)) - epsilon)) *
          Kakeya.realRpowENN delta (-((33 / (N : ℝ)) + epsilon)) := by gcongr
    _ = Kakeya.realRpowENN delta (-eta₁) := by
          have h_rpow_add2 : Kakeya.realRpowENN delta (-(eta₁ - (33 / (N : ℝ)) - epsilon)) *
              Kakeya.realRpowENN delta (-((33 / (N : ℝ)) + epsilon)) =
            Kakeya.realRpowENN delta (-eta₁) := by
            simp only [Kakeya.realRpowENN]
            set a := (-(eta₁ - (33 / (N : ℝ)) - epsilon)) with ha2
            set b := (-((33 / (N : ℝ)) + epsilon)) with hb2
            have h_nonneg_a2 : 0 ≤ Real.rpow delta a := Real.rpow_nonneg hdelta.le _
            have h_mul2 : (Real.rpow delta a) * (Real.rpow delta b) = Real.rpow delta (a + b) :=
              (Real.rpow_add hdelta a b).symm
            have h_enn_mul2 : ENNReal.ofReal ((Real.rpow delta a) * (Real.rpow delta b)) =
                ENNReal.ofReal (Real.rpow delta a) * ENNReal.ofReal (Real.rpow delta b) :=
              ENNReal.ofReal_mul (p := Real.rpow delta a) (q := Real.rpow delta b) h_nonneg_a2
            have h_sum2 : a + b = -eta₁ := by
              simp [ha2, hb2] <;> ring_nf
            rw [← h_enn_mul2, h_mul2, h_sum2]
          rw [h_rpow_add2]

end Kakeya.Streamlined.RandomTranslation.WithShading

end
