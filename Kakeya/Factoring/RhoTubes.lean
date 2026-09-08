/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.Pipeline
public import Kakeya.Mathlib.MeasureTheory.BoundedOverlap
public import Kakeya.Tube.IntersectionVolume

/-! # Two-scale factoring for dilated `ρ`-tubes (GWZ Lemma 5.11, dilate form)

This file states the tube case of the factoring and multiplicity proposition in the form the
`ρ`-tube pipeline actually needs: the outer family consists of the `c`-*dilates* of a family of
`ρ`-tubes rather than of the `ρ`-tubes themselves.

Two hypotheses of the original bundled statement
`ShadedBody.shadingMultiplicityEstimateForRhoTubes` are deliberately absent, and their absence is
load-bearing:

* no essential distinctness of the outer bodies, and
* no per-tube density (uniformity) hypothesis on the inner shading.

The Step 0 - Step 5 pipeline of `Kakeya/Factoring/Step0.lean` through
`Kakeya/Factoring/Step5.lean` needs neither, and no Frostman condition enters. What replaces them
is `Kakeya.Tube.volume_dilate_inter_cthickening_ge`: for a dilated `ρ`-tube the fullness of the
`2ρ`-neighbourhood of a shade is controlled by elementary capsule geometry, at the cost of the
explicit `c ^ n` factor carried by the loss constant.

## Main definitions and statements

* `ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C`: the assembled loss constant;
* `ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.one_le_C` and
  `ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox`: it is at least `1` and,
  for a fixed dimension and dilation factor, subpolynomial in `1 / δ` and in the inner cardinality;
* `ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate`: the estimate itself.
-/

@[expose] public section

open MeasureTheory Convexity Kakeya
open scoped NNReal ENNReal

namespace ShadedBody

section RhoTubesDilate

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*}

/-- The dimension/cardinality/scale packing ratio used by the self-pigeonholed Step 5 cover. -/
noncomputable def step5PackingRatio (n N : ℕ) (δ : NNReal) : NNReal :=
  (2 ^ n * Kakeya.step1UpperBdAtScale n (max 1 N)) /
    Kakeya.step1LowerBdAtScale n δ

/-- The packing loss used to compare the trimmed outer pointwise count with its average. -/
def rhoTubesOuterMultiplicityLoss (n : ℕ) : NNReal :=
  Kakeya.factoringStep5OverlapConstant n * 32 ^ n

/-- The fixed geometric loss used simultaneously for capsule fullness, outer multiplicity, and
the `4ρ` ball cover of the exact outer shading. -/
noncomputable def rhoTubesGeometricLoss (n : ℕ) : NNReal :=
  4 * max 1 (Kakeya.Tube.dilateFullness.C n) *
    max 1 (Tube.volume_le.C n / Tube.le_volume.c n) ^ 2 *
      max 1 (rhoTubesOuterMultiplicityLoss n)

/-- The bounded-overlap loss in the Step 5 ball estimate. -/
def rhoTubesBallLoss (n : ℕ) : NNReal :=
  2 * Kakeya.factoringStep5OverlapConstant n ^ 2 * 4 ^ n

/-- **Constant in `ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate`.**

It assembles, in order, the pigeonholing losses of the five steps of the factoring construction
with the fullness loss of the dilate:

* `2`, the Step 0 loss (`ShadedBody.FactorFamily.isCRefinement_step0` is a `2⁻¹` refinement);
* `Kakeya.factoringStep1Step2AtScaleConstant n N δ`, the chained Step 1 and Step 2 loss;
* `Kakeya.factoringStep3Constant N`, the Step 3 loss;
* `Kakeya.factoringStep5SelfPigeonholeConstant` at the overlap bound
  `Kakeya.factoringStep5OverlapConstant n`, evaluated at an explicit packing bound for the Step 5
  cover (Step 4 is a construction, not a pigeonholing, and loses nothing);
* `Kakeya.Tube.dilateFullness.C n`, the fullness loss of the capsule comparison, together with the
  factor `c ^ n` by which the dilation inflates the outer volume.

The outer `max 1` records that the loss is never a gain; it makes
`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.one_le_C` hold with no hypotheses on
`n`, `N`, `δ` or `c`. Only that bound and the subpolynomial estimate
`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox` are used downstream, never
the numerical value. -/
noncomputable def shadingMultiplicityEstimateForRhoTubesDilate.C (n N : ℕ) (δ c : ℝ≥0) : ℝ≥0 :=
  max 1
    (max (c ^ n *
      (2 * Kakeya.factoringStep1Step2AtScaleConstant n N δ *
        (Kakeya.factoringStep3Constant N : ℝ≥0) *
        ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
          (step5PackingRatio n N δ) *
        rhoTubesGeometricLoss n)) (rhoTubesBallLoss n))

/-- The loss constant of `ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate` is at least
`1`, so that its `ℝ≥0` inverse is at most `1` and the conclusions really are losses. -/
theorem shadingMultiplicityEstimateForRhoTubesDilate.one_le_C (n N : ℕ) (δ c : ℝ≥0) :
    1 ≤ shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c := by
  exact le_max_left 1 _

private lemma natLog_succ_le_rpow : ∀ η : ℝ, 0 < η → ∃ B : ℝ≥0, ∀ N : ℕ, 0 < N →
    ((Nat.log 2 N + 1 : ℕ) : ℝ≥0) ≤ B * (N : ℝ≥0) ^ η := by
  intro η hη
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let q : ℝ≥0 := ⟨1 / (η * Real.log 2), by positivity⟩
  refine ⟨1 + q, fun N hN ↦ ?_⟩
  have hN1 : (1 : ℝ≥0) ≤ (N : ℝ≥0) := by exact_mod_cast hN
  have hNpow : (1 : ℝ≥0) ≤ (N : ℝ≥0) ^ η := by
    simpa using NNReal.rpow_le_rpow hN1 hη.le
  have hlog : (Nat.log 2 N : ℝ) ≤ (N : ℝ) ^ η / (η * Real.log 2) := by
    calc
      (Nat.log 2 N : ℝ) ≤ Real.logb 2 N := Real.natLog_le_logb N 2
      _ = Real.log N / Real.log 2 := rfl
      _ ≤ ((N : ℝ) ^ η / η) / Real.log 2 := by
        gcongr
        exact Real.log_natCast_le_rpow_div N hη
      _ = (N : ℝ) ^ η / (η * Real.log 2) := by ring
  rw [← NNReal.coe_le_coe]
  push_cast [q, NNReal.coe_rpow]
  have hNpow' : (1 : ℝ) ≤ (N : ℝ) ^ η := by exact_mod_cast hNpow
  calc
    (Nat.log 2 N : ℝ) + 1 ≤ (N : ℝ) ^ η / (η * Real.log 2) + 1 := by linarith
    _ ≤ (N : ℝ) ^ η / (η * Real.log 2) + (N : ℝ) ^ η := by linarith
    _ = (1 + 1 / (η * Real.log 2)) * (N : ℝ) ^ η := by ring

private lemma fiberPigeonholeConstant_le_rpow (n : ℕ) :
    ∀ η : ℝ, 0 < η → ∃ A : ℝ≥0, ∀ N : ℕ, 0 < N → ∀ δ : ℝ≥0, 0 < δ → δ ≤ 1 →
      Kakeya.factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale n δ)
          (Kakeya.step1UpperBdAtScale n N) ≤ A * δ ^ (-η) * (N : ℝ≥0) ^ η := by
  intro η hη
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let q : ℝ := 1 / (η * Real.log 2)
  let a₀ : ℝ := 1 + n + Real.logb 2 (n.factorial : ℝ)
  have ha₀ : 0 ≤ a₀ := by
    have hfact : (1 : ℝ) ≤ n.factorial := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hlogfact : 0 ≤ Real.logb 2 (n.factorial : ℝ) :=
      Real.logb_nonneg one_lt_two hfact
    positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  let A : ℝ≥0 := ⟨a₀ + q + n * q, by positivity⟩
  refine ⟨A, fun N hN δ hδ hδ1 ↦ ?_⟩
  have hN1 : (1 : ℝ≥0) ≤ (N : ℝ≥0) := by exact_mod_cast hN
  have hNpow : (1 : ℝ≥0) ≤ (N : ℝ≥0) ^ η := by
    simpa using NNReal.rpow_le_rpow hN1 hη.le
  have hδpow : (1 : ℝ≥0) ≤ δ ^ (-η) := Kakeya.one_le_rpow_neg hη.le hδ hδ1
  have hlogN : Real.logb 2 (N : ℝ) ≤ q * (N : ℝ) ^ η := by
    calc
      Real.logb 2 (N : ℝ) = Real.log N / Real.log 2 := rfl
      _ ≤ ((N : ℝ) ^ η / η) / Real.log 2 := by
        gcongr
        exact Real.log_natCast_le_rpow_div N hη
      _ = q * (N : ℝ) ^ η := by simp only [q]; ring
  have hlogδ : Real.logb 2 (1 / (δ : ℝ)) ≤ q * (δ : ℝ) ^ (-η) := by
    calc
      Real.logb 2 (1 / (δ : ℝ))
          ≤ (δ : ℝ) ^ (-η) / (η * Real.log 2) :=
        Kakeya.logb_inv_le_rpow_neg_div (by exact_mod_cast hδ) hη
      _ = q * (δ : ℝ) ^ (-η) := by simp only [q]; ring
  have hF :
      (Kakeya.factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale n δ)
          (Kakeya.step1UpperBdAtScale n N) : ℝ) =
        a₀ + Real.logb 2 (N : ℝ) + n * Real.logb 2 (1 / (δ : ℝ)) := by
    have hratio := Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale_nonneg n
      (Nat.one_le_iff_ne_zero.mpr hN.ne') hδ hδ1
    have h := congrArg ENNReal.toReal
      (Kakeya.coe_factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale n δ)
        (Kakeya.step1UpperBdAtScale n N))
    rw [NNReal.coe_div] at hratio
    have hnonneg : 0 ≤ 1 + Real.logb 2
        ((Kakeya.step1UpperBdAtScale n N : ℝ) / (Kakeya.step1LowerBdAtScale n δ : ℝ)) := by
      linarith
    rw [ENNReal.toReal_ofReal hnonneg] at h
    simp only [ENNReal.coe_toReal] at h
    rw [h, ← NNReal.coe_div, Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale n
      (Nat.one_le_iff_ne_zero.mpr hN.ne') hδ]
    simp only [a₀]
    ring
  rw [← NNReal.coe_le_coe]
  push_cast [A, NNReal.coe_rpow]
  rw [hF]
  have hNpow' : (1 : ℝ) ≤ (N : ℝ) ^ η := by exact_mod_cast hNpow
  have hδpow' : (1 : ℝ) ≤ (δ : ℝ) ^ (-η) := by exact_mod_cast hδpow
  calc
    a₀ + Real.logb 2 (N : ℝ) + n * Real.logb 2 (1 / (δ : ℝ))
        ≤ a₀ + q * (N : ℝ) ^ η + n * (q * (δ : ℝ) ^ (-η)) := by gcongr
    _ ≤ a₀ * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η +
          q * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η +
          n * q * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by
      have ha₀term : a₀ ≤ a₀ * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by
        calc
          a₀ = a₀ * 1 * 1 := by ring
          _ ≤ a₀ * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by gcongr
      have hNterm : q * (N : ℝ) ^ η ≤
          q * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by
        calc
          q * (N : ℝ) ^ η = q * 1 * (N : ℝ) ^ η := by ring
          _ ≤ q * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by gcongr
      have hδterm : (n : ℝ) * (q * (δ : ℝ) ^ (-η)) ≤
          n * q * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by
        calc
          (n : ℝ) * (q * (δ : ℝ) ^ (-η)) = n * q * (δ : ℝ) ^ (-η) * 1 := by ring
          _ ≤ n * q * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by gcongr
      exact add_le_add (add_le_add ha₀term hNterm) hδterm
    _ = (a₀ + q + n * q) * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by ring

private lemma step5FiberConstant_eq (n N : ℕ) (δ : NNReal) (hN : 0 < N) :
    Kakeya.factoringStep1FiberPigeonholeConstant 1 (step5PackingRatio n N δ) =
      Kakeya.factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale n δ)
        (Kakeya.step1UpperBdAtScale n (2 ^ n * N)) := by
  have hratio : step5PackingRatio n N δ =
      Kakeya.step1UpperBdAtScale n (2 ^ n * N) /
        Kakeya.step1LowerBdAtScale n δ := by
    unfold step5PackingRatio
    rw [max_eq_right (Nat.one_le_iff_ne_zero.mpr hN.ne')]
    congr 1
    apply ENNReal.coe_injective
    rw [ENNReal.coe_mul, Kakeya.coe_step1UpperBdAtScale,
      Kakeya.coe_step1UpperBdAtScale]
    push_cast
    ring
  apply ENNReal.coe_injective
  rw [Kakeya.coe_factoringStep1FiberPigeonholeConstant,
    Kakeya.coe_factoringStep1FiberPigeonholeConstant]
  congr 2
  rw [hratio]
  push_cast
  norm_num

private lemma factoringLoss_eq (n N : ℕ) (δ : ℝ≥0) (hN : 0 < N) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    2 * Kakeya.factoringStep1Step2AtScaleConstant n N δ *
          (Kakeya.factoringStep3Constant N : ℝ≥0) *
          ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
            (step5PackingRatio n N δ) *
          rhoTubesGeometricLoss n =
      128 * Kakeya.factoringStep1FiberPigeonholeConstant
          (Kakeya.step1LowerBdAtScale n δ) (Kakeya.step1UpperBdAtScale n N) *
        (Kakeya.factoringStep1FiberPigeonholeConstant
          (Kakeya.step1LowerBdAtScale n δ)
            (Kakeya.step1UpperBdAtScale n (2 ^ n * N))) *
        ((Nat.log 2 N + 1 : ℕ) : ℝ≥0) ^ 4 *
        Kakeya.factoringStep5OverlapConstant n * rhoTubesGeometricLoss n := by
  have hratio := Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale_nonneg n
    (Nat.one_le_iff_ne_zero.mpr hN.ne') hδ hδ1
  have hF := congrArg ENNReal.toReal
    (Kakeya.coe_factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale n δ)
      (Kakeya.step1UpperBdAtScale n N))
  rw [NNReal.coe_div] at hratio
  have hnonneg : 0 ≤ 1 + Real.logb 2
      ((Kakeya.step1UpperBdAtScale n N : ℝ) / (Kakeya.step1LowerBdAtScale n δ : ℝ)) := by
    linarith
  rw [ENNReal.toReal_ofReal hnonneg] at hF
  simp only [ENNReal.coe_toReal] at hF
  have h12 : Kakeya.factoringStep1Step2AtScaleConstant n N δ =
      2 * Kakeya.factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale n δ)
        (Kakeya.step1UpperBdAtScale n N) * ((Nat.log 2 N + 1 : ℕ) : ℝ≥0) ^ 3 := by
    rw [← NNReal.coe_inj]
    push_cast
    rw [Kakeya.coe_factoringStep1Step2AtScaleConstant n
      (Nat.one_le_iff_ne_zero.mpr hN.ne') hδ hδ1, hF, ← NNReal.coe_div,
      Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale n
        (Nat.one_le_iff_ne_zero.mpr hN.ne') hδ]
    push_cast
    simp only [one_div]
    ring
  rw [h12, ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant,
    step5FiberConstant_eq n N δ hN, Kakeya.factoringStep3Constant]
  simp only [Kakeya.factoringStep2PointwiseConstant,
    Kakeya.MultiplicityFamily.scaleTripleConstant, Kakeya.dyadicPigeonholeNatConstant]
  push_cast
  ring

/-- For a fixed dimension and a fixed dilation factor, the loss constant of
`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate` is jointly subpolynomial in the inverse
discretization scale and in the inner-family cardinality: for every `ε > 0` one constant `Cε`
works uniformly for all `N ≥ 1` and all `0 < δ ≤ 1`, with the `c ^ n` dilation factor pulled out
explicitly.

Modelled on `ShadedBody.outerFactoringFamily_multDominated.C_leApprox_one`. The hypothesis
`1 ≤ c` is needed: the constant is bounded below by `1` while `c ^ n` degenerates for `c < 1`. -/
theorem shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox (n : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ≥0, ∀ N : ℕ, 0 < N → ∀ δ : ℝ≥0, 0 < δ → δ ≤ 1 →
      ∀ c : ℝ≥0, 1 ≤ c →
        shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c
          ≤ Cε * c ^ n * δ ^ (-ε) * (N : ℝ≥0) ^ ε := by
  intro ε hε
  let η : ℝ := ε / 6
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨A, hA⟩ := fiberPigeonholeConstant_le_rpow n η hη
  obtain ⟨B, hB⟩ := natLog_succ_le_rpow η hη
  let q : NNReal := ((2 ^ n : ℕ) : NNReal) ^ η
  let C₁ : ℝ≥0 := 128 * Kakeya.factoringStep5OverlapConstant n *
    rhoTubesGeometricLoss n * A ^ 2 * B ^ 4 * q
  let C₀ : ℝ≥0 := max C₁ (rhoTubesBallLoss n)
  refine ⟨max 1 C₀, ?_⟩
  intro N hN δ hδ hδ1 c hc
  have hN1 : (1 : ℝ≥0) ≤ (N : ℝ≥0) := by exact_mod_cast hN
  have hNpow : (1 : ℝ≥0) ≤ (N : ℝ≥0) ^ ε := by
    simpa using NNReal.rpow_le_rpow hN1 hε.le
  have hδpow : (1 : ℝ≥0) ≤ δ ^ (-ε) := Kakeya.one_le_rpow_neg hε.le hδ hδ1
  have hcpow : (1 : ℝ≥0) ≤ c ^ n := one_le_pow₀ hc
  have hF := hA N hN δ hδ hδ1
  have hN' : 0 < 2 ^ n * N := by positivity
  have hF' := hA (2 ^ n * N) hN' δ hδ hδ1
  have hL := hB N hN
  have hN'pow : (((2 ^ n * N : ℕ) : NNReal) ^ η) = q * (N : NNReal) ^ η := by
    simp only [Nat.cast_mul, q]
    rw [NNReal.mul_rpow]
  have hδexp : (δ ^ (-η)) ^ 2 ≤ δ ^ (-ε) := by
    rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
    apply NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1
    dsimp [η]
    linarith
  have hNexp : ((N : ℝ≥0) ^ η) ^ 6 = (N : ℝ≥0) ^ ε := by
    rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
    congr 2
    dsimp [η]
    ring
  have hloss :
      2 * Kakeya.factoringStep1Step2AtScaleConstant n N δ *
            (Kakeya.factoringStep3Constant N : ℝ≥0) *
            ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
              (step5PackingRatio n N δ) *
            rhoTubesGeometricLoss n ≤
        C₀ * δ ^ (-ε) * (N : ℝ≥0) ^ ε := by
    rw [factoringLoss_eq n N δ hN hδ hδ1]
    calc
      128 * Kakeya.factoringStep1FiberPigeonholeConstant
            (Kakeya.step1LowerBdAtScale n δ) (Kakeya.step1UpperBdAtScale n N) *
          Kakeya.factoringStep1FiberPigeonholeConstant
            (Kakeya.step1LowerBdAtScale n δ)
              (Kakeya.step1UpperBdAtScale n (2 ^ n * N)) *
          ((Nat.log 2 N + 1 : ℕ) : ℝ≥0) ^ 4 *
          Kakeya.factoringStep5OverlapConstant n * rhoTubesGeometricLoss n
          ≤ 128 * (A * δ ^ (-η) * (N : ℝ≥0) ^ η) *
            (A * δ ^ (-η) * ((2 ^ n * N : ℕ) : NNReal) ^ η) *
            (B * (N : ℝ≥0) ^ η) ^ 4 * Kakeya.factoringStep5OverlapConstant n *
              rhoTubesGeometricLoss n := by gcongr
      _ = C₁ * (δ ^ (-η)) ^ 2 * ((N : ℝ≥0) ^ η) ^ 6 := by
        simp only [C₁, hN'pow]
        ring
      _ ≤ C₀ * (δ ^ (-η)) ^ 2 * ((N : ℝ≥0) ^ η) ^ 6 := by
        gcongr
        exact le_max_left C₁ _
      _ ≤ C₀ * δ ^ (-ε) * ((N : ℝ≥0) ^ η) ^ 6 := by gcongr
      _ = C₀ * δ ^ (-ε) * (N : ℝ≥0) ^ ε := by rw [hNexp]
  rw [shadingMultiplicityEstimateForRhoTubesDilate.C]
  apply max_le
  · calc
      1 ≤ max 1 C₀ * 1 * 1 * 1 := by
        simp only [mul_one]
        exact le_max_left 1 C₀
      _ ≤ max 1 C₀ * c ^ n * δ ^ (-ε) * (N : ℝ≥0) ^ ε := by gcongr
  · apply max_le
    · calc
        c ^ n *
          (2 * Kakeya.factoringStep1Step2AtScaleConstant n N δ *
            (Kakeya.factoringStep3Constant N : ℝ≥0) *
            ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
              (step5PackingRatio n N δ) *
            rhoTubesGeometricLoss n)
            ≤ c ^ n * (C₀ * δ ^ (-ε) * (N : ℝ≥0) ^ ε) := by gcongr
        _ = C₀ * c ^ n * δ ^ (-ε) * (N : ℝ≥0) ^ ε := by ring
        _ ≤ max 1 C₀ * c ^ n * δ ^ (-ε) * (N : ℝ≥0) ^ ε := by
          gcongr
          exact le_max_right _ _
    · calc
        rhoTubesBallLoss n ≤ C₀ := le_max_right _ _
        _ = C₀ * 1 * 1 * 1 := by ring
        _ ≤ max 1 C₀ * c ^ n * δ ^ (-ε) * (N : ℝ≥0) ^ ε := by
          gcongr
          exact le_max_right _ _

/-! ### Completing the pipeline output on its active fibers -/

omit [Nontrivial E] in
private lemma isCRefinement_mono {s s' : Finset ι} {V V' : ι → ShadedBody E}
    {c c' : NNReal} (hcc : c' ≤ c) (h : IsCRefinement s' V' s V c) :
    IsCRefinement s' V' s V c' := by
  refine ⟨h.1, ?_⟩
  calc
    (c' : ENNReal) * ∑ i ∈ s, volume (V i).shade ≤
        (c : ENNReal) * ∑ i ∈ s, volume (V i).shade := by gcongr
    _ ≤ ∑ i ∈ s', volume (V' i).shade := h.2

open Classical in
/-- The Step 5 outer blocks whose selected fiber shading has positive measure.  Removing the
other blocks loses no shaded mass and is needed because the multiplicity conclusion is asserted
for every output fiber. -/
private noncomputable def activeOuterSet (G₅ : ShadedFactorFamily E ι κ) : Finset κ :=
  G₅.outerSet.filter fun j ↦ volume (iUnionShade (G₅.fiber j) G₅.innerBody) ≠ 0

open Classical in
/-- Complete the Step 5 inner family back to the whole input fiber.  Indices discarded by the
pipeline receive the empty shade, so this changes neither the selected union nor its mass. -/
private noncomputable def completedInnerBody (F : FactorFamily E ι κ)
    (G₅ : ShadedFactorFamily E ι κ) (i : ι) : ShadedBody E :=
  if i ∈ G₅.innerSet then G₅.innerBody i
  else (F.innerBody i).restrictShade ∅ MeasurableSet.empty

open Classical in
/-- The exact outer shading used in the dilated-tube application: the prescribed carrier,
intersected with the closed `2ρ`-neighbourhood of the completed selected fiber. -/
private noncomputable def rhoCompletedOuterBody (F : FactorFamily E ι κ)
    (G₅ : ShadedFactorFamily E ι κ) (K : κ → ConvexSpaceBody E) (ρ : NNReal) (j : κ) :
    ShadedBody E where
  toConvexSpaceBody := K j
  shade := (K j).carrier ∩ Metric.cthickening (2 * (ρ : ℝ))
    (iUnionShade {i ∈ F.innerSet | F.parent i ∈ activeOuterSet G₅ ∧ F.parent i = j}
      (completedInnerBody F G₅))
  measurableSet_shade := (K j).isCompact.isClosed.measurableSet.inter
    Metric.isClosed_cthickening.measurableSet
  shade_subset := Set.inter_subset_left

open Classical in
/-- The active-fiber completion of the pipeline output. -/
private noncomputable def completedPipelineFamily (F : FactorFamily E ι κ)
    (G₅ : ShadedFactorFamily E ι κ) (K : κ → ConvexSpaceBody E) (ρ : NNReal)
    (_houter : G₅.outerSet ⊆ F.outerSet) (_hparent : G₅.parent = F.parent)
    (hbody : ∀ i, (G₅.innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody)
    (hK : ∀ i ∈ F.innerSet, (F.innerBody i).toConvexSpaceBody ≤ K (F.parent i)) :
    ShadedFactorFamily E ι κ where
  innerSet := {i ∈ F.innerSet | F.parent i ∈ activeOuterSet G₅}
  innerBody := completedInnerBody F G₅
  outerSet := activeOuterSet G₅
  outerBody := rhoCompletedOuterBody F G₅ K ρ
  parent := F.parent
  parent_mem := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  inner_le_parent := by
    intro i hi
    unfold completedInnerBody rhoCompletedOuterBody
    by_cases hi₅ : i ∈ G₅.innerSet
    · simpa [hi₅, hbody] using hK i (Finset.mem_filter.mp hi).1
    · simpa [hi₅] using hK i (Finset.mem_filter.mp hi).1
  shade_subset_parent := by
    intro i hi x hxi
    have hia : F.parent i ∈ activeOuterSet G₅ := (Finset.mem_filter.mp hi).2
    have hxcarrier : x ∈ (F.innerBody i).carrier := by
      have hxcarrier' := (completedInnerBody F G₅ i).shade_subset hxi
      by_cases hi₅ : i ∈ G₅.innerSet
      · simpa [completedInnerBody, hi₅, hbody] using hxcarrier'
      · simpa [completedInnerBody, hi₅] using hxcarrier'
    refine ⟨hK i (Finset.mem_filter.mp hi).1 hxcarrier, ?_⟩
    apply Metric.self_subset_cthickening
    refine Set.mem_iUnion₂.mpr ⟨i, ?_, hxi⟩
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, hia, rfl⟩

omit [Nontrivial E] in
open Classical in
/-- A selected inner shade contributes its whole `2ρ` neighbourhood inside the prescribed
outer carrier to the completed outer shade. -/
private lemma inter_cthickening_shade_subset_rhoCompletedOuterBody
    (F : FactorFamily E ι κ) (G₅ : ShadedFactorFamily E ι κ)
    (K : κ → ConvexSpaceBody E) (ρ : NNReal) {j : κ} (hj : j ∈ activeOuterSet G₅)
    {i : ι} (hi₅ : i ∈ G₅.innerSet) (hiF : i ∈ F.innerSet)
    (hip : F.parent i = j) :
    (K j).carrier ∩ Metric.cthickening (2 * (ρ : ℝ)) (G₅.innerBody i).shade ⊆
      (rhoCompletedOuterBody F G₅ K ρ j).shade := by
  intro x hx
  refine ⟨hx.1, Metric.cthickening_subset_of_subset _ ?_ hx.2⟩
  exact Set.subset_iUnion₂_of_subset i (Finset.mem_filter.mpr ⟨hiF, hip ▸ hj, hip⟩)
    (by simp [completedInnerBody, hi₅])

/-- The cover cardinality is controlled by the explicit ratio used in the Step 5 loss. -/
private lemma card_le_step5PackingRatio {T : Finset E} {N : ℕ} {δ ρ : NNReal}
    (hδ : 0 < δ) (hρ : ρ ∈ Set.Icc δ 1)
    (hTsub : (T : Set E) ⊆ Metric.closedBall 0 1)
    (hTsep : Metric.IsSeparated (ρ : ENNReal) (T : Set E)) :
    (T.card : NNReal) ≤ step5PackingRatio (Module.finrank ℝ E) N δ := by
  let n := Module.finrank ℝ E
  have hpack := Metric.card_le_of_isSeparated_subset_closedBall (T := T) (hδ.trans_le hρ.1)
    (x := (0 : E)) (R := 1) (by norm_num) hTsub hTsep
  have hρr : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hδ.trans_le hρ.1
  have hδr : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hbase : 2 * (1 + (ρ : ℝ)) / (ρ : ℝ) ≤ 4 / (δ : ℝ) := by
    rw [div_le_div_iff₀ hρr hδr]
    have hδρ : (δ : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ.1
    have hρ1 : (ρ : ℝ) ≤ 1 := by exact_mod_cast hρ.2
    have hρ0 : (0 : ℝ) ≤ ρ := hρr.le
    nlinarith
  have hcard : (T.card : ℝ) ≤ (4 / (δ : ℝ)) ^ n :=
    hpack.trans (pow_le_pow_left₀ (by positivity) hbase n)
  rw [← NNReal.coe_le_coe]
  push_cast
  calc
    (T.card : ℝ) ≤ (4 / (δ : ℝ)) ^ n := hcard
    _ ≤ (step5PackingRatio n N δ : ℝ) := by
      rw [step5PackingRatio, mul_div_assoc,
        Kakeya.step1UpperBdAtScale_div_step1LowerBdAtScale n (max 1 N) hδ]
      push_cast
      rw [div_pow]
      have hfact : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
      have hN : (1 : ℝ) ≤ max 1 (N : ℝ) := le_max_left _ _
      have hinv : 0 ≤ ((δ : ℝ) ^ n)⁻¹ := by positivity
      rw [div_eq_mul_inv]
      calc
        (4 : ℝ) ^ n * ((δ : ℝ) ^ n)⁻¹ =
            ((2 : ℝ) ^ n * 2 ^ n) * ((δ : ℝ) ^ n)⁻¹ := by
              rw [← mul_pow]
              norm_num
        _ ≤ ((2 : ℝ) ^ n * 2 ^ n) *
            ((n.factorial : ℝ) * max 1 (N : ℝ) * ((δ : ℝ) ^ n)⁻¹) := by
              gcongr
              calc
                ((δ : ℝ) ^ n)⁻¹ = 1 * 1 * ((δ : ℝ) ^ n)⁻¹ := by ring
                _ ≤ (n.factorial : ℝ) * max 1 (N : ℝ) * ((δ : ℝ) ^ n)⁻¹ := by
                  gcongr
        _ = (2 : ℝ) ^ n *
            ((2 : ℝ) ^ n * n.factorial * max 1 (N : ℝ) * ((δ : ℝ) ^ n)⁻¹) := by ring

/-- Monotonicity of the self-pigeonholing loss in a cardinality upper bound. -/
private lemma step5SelfPigeonholeConstant_mono {n : ℕ} {M M' : NNReal}
    (hM : M ≤ M') (hM' : 1 ≤ M') :
    ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n M ≤
      ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n M' := by
  unfold ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant
  gcongr
  rw [← ENNReal.coe_le_coe]
  rw [Kakeya.coe_factoringStep1FiberPigeonholeConstant,
    Kakeya.coe_factoringStep1FiberPigeonholeConstant]
  apply ENNReal.ofReal_le_ofReal
  by_cases hM0 : M = 0
  · subst M
    have hlog : 0 ≤ Real.logb 2 (M' : ℝ) :=
      Real.logb_nonneg one_lt_two (by exact_mod_cast hM')
    simp only [NNReal.coe_zero, NNReal.coe_one, div_one, Real.logb_zero, add_zero]
    exact le_add_of_nonneg_right hlog
  · gcongr
    norm_num

omit [Nontrivial E] in
open Classical in
private lemma iUnionShade_completed_fiber (F : FactorFamily E ι κ)
    (G₅ : ShadedFactorFamily E ι κ) (hsub : G₅.innerSet ⊆ F.innerSet)
    (hparent : G₅.parent = F.parent) {j : κ} (hj : j ∈ activeOuterSet G₅) :
    iUnionShade {i ∈ F.innerSet | F.parent i ∈ activeOuterSet G₅ ∧ F.parent i = j}
        (completedInnerBody F G₅) = iUnionShade (G₅.fiber j) G₅.innerBody := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    have hp := (Finset.mem_filter.mp hi).2.2
    by_cases hi₅ : i ∈ G₅.innerSet
    · refine Set.mem_iUnion₂.mpr ⟨i, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨hi₅, by simpa [hparent] using hp⟩
      · simpa [completedInnerBody, hi₅] using hxi
    · simp [completedInnerBody, hi₅] at hxi
  · intro hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    have hi' := Finset.mem_filter.mp hi
    have hpF : F.parent i = j := by simpa [← hparent] using hi'.2
    refine Set.mem_iUnion₂.mpr ⟨i, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hsub hi'.1, hpF ▸ hj, hpF⟩
    · simpa [completedInnerBody, hi'.1] using hxi

omit [Nontrivial E] in
open Classical in
private lemma sum_volume_completed_fiber (F : FactorFamily E ι κ)
    (G₅ : ShadedFactorFamily E ι κ) (hsub : G₅.innerSet ⊆ F.innerSet)
    (hparent : G₅.parent = F.parent) {j : κ} (hj : j ∈ activeOuterSet G₅) :
    ∑ i ∈ {i ∈ F.innerSet | F.parent i ∈ activeOuterSet G₅ ∧ F.parent i = j},
        volume (completedInnerBody F G₅ i).shade =
      ∑ i ∈ G₅.fiber j, volume (G₅.innerBody i).shade := by
  let s := {i ∈ F.innerSet | F.parent i ∈ activeOuterSet G₅ ∧ F.parent i = j}
  have hsubfiber : G₅.fiber j ⊆ s := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    have hp : F.parent i = j := by simpa [← hparent] using hi'.2
    exact Finset.mem_filter.mpr ⟨hsub hi'.1, hp ▸ hj, hp⟩
  calc
    ∑ i ∈ s, volume (completedInnerBody F G₅ i).shade =
        ∑ i ∈ G₅.fiber j, volume (completedInnerBody F G₅ i).shade := by
      symm
      apply Finset.sum_subset hsubfiber
      intro i his hif
      have hiG : i ∉ G₅.innerSet := by
        intro hiG
        apply hif
        exact Finset.mem_filter.mpr ⟨hiG, by
          have hp := (Finset.mem_filter.mp his).2.2
          simpa [hparent] using hp⟩
      simp [completedInnerBody, hiG]
    _ = ∑ i ∈ G₅.fiber j, volume (G₅.innerBody i).shade := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [completedInnerBody, (Finset.mem_filter.mp hi).1]

omit [Nontrivial E] in
open Classical in
private lemma iUnionShade_completed_eq_active (F : FactorFamily E ι κ)
    (G₅ : ShadedFactorFamily E ι κ) (hsub : G₅.innerSet ⊆ F.innerSet)
    (hparent : G₅.parent = F.parent) :
    iUnionShade {i ∈ F.innerSet | F.parent i ∈ activeOuterSet G₅}
        (completedInnerBody F G₅) =
      ⋃ j ∈ activeOuterSet G₅, iUnionShade (G₅.fiber j) G₅.innerBody := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    have hp := (Finset.mem_filter.mp hi).2
    refine Set.mem_iUnion₂.mpr ⟨F.parent i, hp, ?_⟩
    rw [← iUnionShade_completed_fiber F G₅ hsub hparent hp]
    exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hi).1, hp, rfl⟩, hxi⟩
  · intro hx
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
    rw [← iUnionShade_completed_fiber F G₅ hsub hparent hj] at hxj
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxj
    exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2.1⟩, hxi⟩

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
open Classical in
private lemma iUnionShade_eq_biUnion_fiber (G₅ : ShadedFactorFamily E ι κ) :
    iUnionShade G₅.innerSet G₅.innerBody =
      ⋃ j ∈ G₅.outerSet, iUnionShade (G₅.fiber j) G₅.innerBody := by
  ext x
  change x ∈ iUnionShade G₅.innerSet G₅.innerBody ↔
    x ∈ ⋃ j ∈ G₅.outerSet, iUnionShade (G₅.fiber j) G₅.innerBody
  constructor
  · intro hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨G₅.parent i, G₅.parent_mem i hi,
      Set.mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩, hxi⟩⟩
  · intro hx
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxj
    exact Set.mem_iUnion₂.mpr ⟨i, (Finset.mem_filter.mp hi).1, hxi⟩

omit [Nontrivial E] in
open Classical in
private lemma iUnionShade_completed_ae_eq (F : FactorFamily E ι κ)
    (G₅ : ShadedFactorFamily E ι κ) (hsub : G₅.innerSet ⊆ F.innerSet)
    (hparent : G₅.parent = F.parent) :
    iUnionShade {i ∈ F.innerSet | F.parent i ∈ activeOuterSet G₅}
        (completedInnerBody F G₅) =ᵐ[volume] iUnionShade G₅.innerSet G₅.innerBody := by
  rw [iUnionShade_completed_eq_active F G₅ hsub hparent,
    iUnionShade_eq_biUnion_fiber G₅]
  let inactive := G₅.outerSet.filter fun j ↦ j ∉ activeOuterSet G₅
  let Z := ⋃ j ∈ inactive, iUnionShade (G₅.fiber j) G₅.innerBody
  have hZ : volume Z = 0 := by
    change volume (⋃ j ∈ (inactive : Set κ),
      iUnionShade (G₅.fiber j) G₅.innerBody) = 0
    apply (measure_biUnion_null_iff (Set.to_countable (inactive : Set κ))).2
    intro j hj
    change j ∈ inactive at hj
    obtain ⟨hjG, hja⟩ := Finset.mem_filter.mp hj
    by_contra hz
    exact hja (Finset.mem_filter.mpr ⟨hjG, hz⟩)
  have hAE : ∀ᵐ x, x ∉ Z := by
    rw [ae_iff]
    have hset : {x : E | ¬x ∉ Z} = Z := by ext x; simp
    rw [hset]
    exact hZ
  filter_upwards [hAE] with x hxZ
  apply propext
  constructor
  · intro hx
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨j, (Finset.mem_filter.mp hj).1, hxj⟩
  · intro hx
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
    by_cases hja : j ∈ activeOuterSet G₅
    · exact Set.mem_iUnion₂.mpr ⟨j, hja, hxj⟩
    · exact (hxZ (Set.mem_iUnion₂.mpr ⟨j,
        Finset.mem_filter.mpr ⟨hj, hja⟩, hxj⟩)).elim

omit [Nontrivial E] in
open Classical in
private lemma volume_iUnionShade_completed_inter_eq (F : FactorFamily E ι κ)
    (G₅ : ShadedFactorFamily E ι κ) (hsub : G₅.innerSet ⊆ F.innerSet)
    (hparent : G₅.parent = F.parent) (A : Set E) :
    volume (iUnionShade {i ∈ F.innerSet | F.parent i ∈ activeOuterSet G₅}
        (completedInnerBody F G₅) ∩ A) =
      volume (iUnionShade G₅.innerSet G₅.innerBody ∩ A) := by
  apply measure_congr
  exact (iUnionShade_completed_ae_eq F G₅ hsub hparent).inter
    (Filter.EventuallyEq.rfl : A =ᵐ[volume] A)

omit [Nontrivial E] in
open Classical in
private lemma sum_volume_completedInnerBody (F : FactorFamily E ι κ)
    (G₅ : ShadedFactorFamily E ι κ) (hsub : G₅.innerSet ⊆ F.innerSet)
    (hparent : G₅.parent = F.parent) :
    ∑ i ∈ {i ∈ F.innerSet | F.parent i ∈ activeOuterSet G₅},
        volume (completedInnerBody F G₅ i).shade =
      ∑ i ∈ G₅.innerSet, volume (G₅.innerBody i).shade := by
  let s₅ := {i ∈ G₅.innerSet | G₅.parent i ∈ activeOuterSet G₅}
  let s := {i ∈ F.innerSet | F.parent i ∈ activeOuterSet G₅}
  have hs₅s : s₅ ⊆ s := by
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hi₅, hp⟩
    exact Finset.mem_filter.mpr ⟨hsub hi₅, by simpa [hparent] using hp⟩
  calc
    ∑ i ∈ s, volume (completedInnerBody F G₅ i).shade =
        ∑ i ∈ s₅, volume (completedInnerBody F G₅ i).shade := by
      symm
      apply Finset.sum_subset hs₅s
      intro i his hi₅
      have hiG : i ∉ G₅.innerSet := by
        intro hiG
        apply hi₅
        exact Finset.mem_filter.mpr ⟨hiG, by
          have := (Finset.mem_filter.mp his).2
          simpa [hparent] using this⟩
      simp [completedInnerBody, hiG]
    _ = ∑ i ∈ s₅, volume (G₅.innerBody i).shade := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [completedInnerBody, (Finset.mem_filter.mp hi).1]
    _ = ∑ i ∈ G₅.innerSet, volume (G₅.innerBody i).shade := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi hiA
      have hparentmem := G₅.parent_mem i hi
      have hnotactive : G₅.parent i ∉ activeOuterSet G₅ := by
        intro ha
        exact hiA (Finset.mem_filter.mpr ⟨hi, ha⟩)
      have hzero : volume (iUnionShade (G₅.fiber (G₅.parent i)) G₅.innerBody) = 0 := by
        by_contra hz
        exact hnotactive (Finset.mem_filter.mpr ⟨hparentmem, hz⟩)
      apply le_antisymm
      · calc
          volume (G₅.innerBody i).shade ≤
              volume (iUnionShade (G₅.fiber (G₅.parent i)) G₅.innerBody) := by
            apply measure_mono
            exact Set.subset_iUnion₂_of_subset i
              (Finset.mem_filter.mpr ⟨hi, rfl⟩) (Set.Subset.refl _)
          _ = 0 := hzero
      · exact bot_le

omit [Nontrivial E] in
/-- Volume scaling for the positive dilations used below. -/
private lemma rho_volume_dilate_eq {ρ : NNReal} (Tρ : Tube ρ E) {c : ℝ} (hc : 0 < c) :
    volume (Kakeya.Tube.dilate Tρ c).carrier =
      ENNReal.ofReal (c ^ Module.finrank ℝ E) * volume Tρ.carrier := by
  rw [Kakeya.Tube.dilate_carrier, MeasureTheory.Measure.addHaar_image_homothety,
    abs_of_pos (pow_pos hc (Module.finrank ℝ E))]

/-- Equal-scale tube dilates have comparable volume by the explicit tube-volume constants. -/
private lemma volume_dilate_le_ratio_mul {ρ : NNReal} (hρ1 : ρ ≤ 1)
    {c : ℝ} (hc : 0 < c) (T₁ T₂ : Tube ρ E) :
    volume (Kakeya.Tube.dilate T₁ c).carrier ≤
      (Tube.volume_le.C (Module.finrank ℝ E) / Tube.le_volume.c (Module.finrank ℝ E) :
          NNReal) * volume (Kakeya.Tube.dilate T₂ c).carrier := by
  let n := Module.finrank ℝ E
  let q : ENNReal := (Tube.volume_le.C n / Tube.le_volume.c n : NNReal)
  let a : ENNReal := ENNReal.ofReal (c ^ n)
  let r : ENNReal := (ρ : ENNReal) ^ (n - 1)
  have hlow : (Tube.le_volume.c n : ENNReal) * r ≤ volume T₂.carrier := by
    simpa [n, r, ENNReal.coe_mul, ENNReal.coe_pow] using Tube.le_volume T₂
  have hupp : volume T₁.carrier ≤ (Tube.volume_le.C n : ENNReal) * r := by
    simpa [n, r, ENNReal.coe_mul, ENNReal.coe_pow] using Tube.volume_le hρ1 T₁
  have hclow0 : (Tube.le_volume.c n : ENNReal) ≠ 0 := by
    exact_mod_cast (Tube.le_volume.c_pos n).ne'
  have hclowtop : (Tube.le_volume.c n : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hbase : volume T₁.carrier ≤ q * volume T₂.carrier := by
    have hq : q = (Tube.volume_le.C n : ENNReal) / (Tube.le_volume.c n : ENNReal) := by
      simp [q, ENNReal.coe_div (Tube.le_volume.c_pos n).ne']
    rw [hq]
    rw [show (Tube.volume_le.C n : ENNReal) / (Tube.le_volume.c n : ENNReal) *
        volume T₂.carrier =
        ((Tube.volume_le.C n : ENNReal) * volume T₂.carrier) /
          (Tube.le_volume.c n : ENNReal) by
      rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]; ring]
    apply (ENNReal.le_div_iff_mul_le (Or.inl hclow0) (Or.inl hclowtop)).2
    calc
      volume T₁.carrier * (Tube.le_volume.c n : ENNReal)
          ≤ ((Tube.volume_le.C n : ENNReal) * r) * (Tube.le_volume.c n : ENNReal) := by gcongr
      _ = (Tube.volume_le.C n : ENNReal) * ((Tube.le_volume.c n : ENNReal) * r) := by ring
      _ ≤ (Tube.volume_le.C n : ENNReal) * volume T₂.carrier := by gcongr
  rw [rho_volume_dilate_eq T₁ hc, rho_volume_dilate_eq T₂ hc]
  simpa [a, q, mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_right hbase a

/-- Summing block estimates when both carrier weights are pairwise comparable. -/
private lemma sum_mul_sum_le_of_pairwise_comparable {J : Type*} (t : Finset J)
    (ht : t.Nonempty) (A K S O : J → ENNReal) (Q D : ENNReal)
    (hA : ∀ j ∈ t, ∀ j' ∈ t, A j ≤ 2 * A j')
    (hK : ∀ j ∈ t, ∀ j' ∈ t, K j ≤ Q * K j')
    (hblock : ∀ j ∈ t, S j * K j ≤ D * O j * A j) :
    (∑ j ∈ t, S j) * (∑ j ∈ t, K j) ≤
      4 * Q ^ 2 * D * (∑ j ∈ t, O j) * (∑ j ∈ t, A j) := by
  classical
  obtain ⟨j₀, hj₀⟩ := ht
  have hKsum : (∑ j ∈ t, K j) ≤ (t.card : ENNReal) * (Q * K j₀) := by
    calc
      (∑ j ∈ t, K j) ≤ ∑ _j ∈ t, Q * K j₀ :=
        Finset.sum_le_sum fun j hj ↦ hK j hj j₀ hj₀
      _ = (t.card : ENNReal) * (Q * K j₀) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hA₀ : (t.card : ENNReal) * A j₀ ≤ 2 * (∑ j ∈ t, A j) := by
    calc
      (t.card : ENNReal) * A j₀ = ∑ _j ∈ t, A j₀ := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ t, 2 * A j := Finset.sum_le_sum fun j hj ↦ hA j₀ hj₀ j hj
      _ = 2 * (∑ j ∈ t, A j) := by rw [Finset.mul_sum]
  have hS₀ : (∑ j ∈ t, S j) * K j₀ ≤
      2 * Q * D * (∑ j ∈ t, O j) * A j₀ := by
    rw [Finset.sum_mul]
    calc
      ∑ j ∈ t, S j * K j₀ ≤ ∑ j ∈ t, Q * (S j * K j) := by
        refine Finset.sum_le_sum fun j hj ↦ ?_
        calc
          S j * K j₀ ≤ S j * (Q * K j) := by gcongr; exact hK j₀ hj₀ j hj
          _ = Q * (S j * K j) := by ring
      _ ≤ ∑ j ∈ t, Q * (D * O j * A j) := by
        exact Finset.sum_le_sum fun j hj ↦ mul_le_mul_right (hblock j hj) Q
      _ ≤ ∑ j ∈ t, Q * (D * O j * (2 * A j₀)) := by
        refine Finset.sum_le_sum fun j hj ↦ ?_
        gcongr
        exact hA j hj j₀ hj₀
      _ = 2 * Q * D * (∑ j ∈ t, O j) * A j₀ := by
        simp_rw [show ∀ j, Q * (D * O j * (2 * A j₀)) =
          (2 * Q * D * A j₀) * O j by intro j; ring]
        rw [← Finset.mul_sum]
        ring
  calc
    (∑ j ∈ t, S j) * (∑ j ∈ t, K j)
        ≤ (∑ j ∈ t, S j) * ((t.card : ENNReal) * (Q * K j₀)) := by gcongr
    _ = (t.card : ENNReal) * Q * ((∑ j ∈ t, S j) * K j₀) := by ring
    _ ≤ (t.card : ENNReal) * Q *
        (2 * Q * D * (∑ j ∈ t, O j) * A j₀) := by gcongr
    _ = 2 * Q ^ 2 * D * (∑ j ∈ t, O j) * ((t.card : ENNReal) * A j₀) := by ring
    _ ≤ 2 * Q ^ 2 * D * (∑ j ∈ t, O j) *
        (2 * (∑ j ∈ t, A j)) := by gcongr
    _ = 4 * Q ^ 2 * D * (∑ j ∈ t, O j) * (∑ j ∈ t, A j) := by ring

/-- Clear the finite, positive carrier denominators in a family of density estimates and sum. -/
private lemma sum_mul_le_of_div_mul_le {I : Type*} (s : Finset I)
    (Y V : I → ENNReal) (K B : ENNReal)
    (hV0 : ∀ i ∈ s, V i ≠ 0) (hVtop : ∀ i ∈ s, V i ≠ ⊤)
    (h : ∀ i ∈ s, (Y i / V i) * K ≤ B) :
    (∑ i ∈ s, Y i) * K ≤ B * (∑ i ∈ s, V i) := by
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  calc
    Y i * K = V i * ((Y i / V i) * K) := by
      rw [← mul_assoc, mul_comm (V i) (Y i / V i), ENNReal.div_mul_cancel (hV0 i hi) (hVtop i hi)]
    _ ≤ V i * B := mul_le_mul_right (h i hi) (V i)
    _ = B * V i := mul_comm _ _

private lemma pipelineLoss_le_C (n N : ℕ) (δ c : NNReal) (hc : 1 ≤ c) :
    Kakeya.factoringStep1AtScaleConstant n N δ *
        (Kakeya.factoringStep2Step3Constant N : NNReal) *
        ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
          (step5PackingRatio n N δ) ≤
      shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c := by
  rw [shadingMultiplicityEstimateForRhoTubesDilate.C]
  refine le_max_of_le_right (le_max_of_le_left ?_)
  unfold Kakeya.factoringStep1Step2AtScaleConstant Kakeya.factoringStep2Step3Constant
  push_cast
  have hcpow : (1 : NNReal) ≤ c ^ n := one_le_pow₀ hc
  have hgeo : (1 : NNReal) ≤ rhoTubesGeometricLoss n := by
    unfold rhoTubesGeometricLoss
    calc
      1 ≤ (4 : NNReal) := by norm_num
      _ ≤ 4 * max 1 (Kakeya.Tube.dilateFullness.C n) := by
        simpa only [mul_one] using mul_le_mul_right (le_max_left (1 : NNReal)
          (Kakeya.Tube.dilateFullness.C n)) (4 : NNReal)
      _ ≤ 4 * max 1 (Kakeya.Tube.dilateFullness.C n) *
          max 1 (Tube.volume_le.C n / Tube.le_volume.c n) ^ 2 := by
        apply le_mul_of_one_le_right (by positivity)
        exact one_le_pow₀ (le_max_left (1 : NNReal) _)
      _ ≤ 4 * max 1 (Kakeya.Tube.dilateFullness.C n) *
          max 1 (Tube.volume_le.C n / Tube.le_volume.c n) ^ 2 *
            max 1 (rhoTubesOuterMultiplicityLoss n) := by
        apply le_mul_of_one_le_right (by positivity)
        exact le_max_left _ _
  calc
    Kakeya.factoringStep1AtScaleConstant n N δ *
          ((Kakeya.factoringStep2PigeonholeConstant N : NNReal) *
            Kakeya.factoringStep3Constant N) *
          ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
            (step5PackingRatio n N δ)
        ≤ 2 * (Kakeya.factoringStep1AtScaleConstant n N δ *
          ((Kakeya.factoringStep2PigeonholeConstant N : NNReal) *
            Kakeya.factoringStep3Constant N) *
          ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
            (step5PackingRatio n N δ)) := by
              exact le_mul_of_one_le_left (by positivity) (by norm_num)
    _ = 1 * (2 * (Kakeya.factoringStep1AtScaleConstant n N δ *
          (Kakeya.factoringStep2PigeonholeConstant N : NNReal)) *
          Kakeya.factoringStep3Constant N *
          ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
            (step5PackingRatio n N δ) * 1) := by
              ring
    _ ≤ c ^ n * (2 * (Kakeya.factoringStep1AtScaleConstant n N δ *
          (Kakeya.factoringStep2PigeonholeConstant N : NNReal)) *
          Kakeya.factoringStep3Constant N *
          ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
            (step5PackingRatio n N δ) * rhoTubesGeometricLoss n) := by gcongr
    _ = c ^ n *
        (2 * (Kakeya.factoringStep1AtScaleConstant n N δ *
          (Kakeya.factoringStep2PigeonholeConstant N : NNReal)) *
          Kakeya.factoringStep3Constant N *
          ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
            (step5PackingRatio n N δ) * rhoTubesGeometricLoss n) := rfl

private lemma pipelineGeometricLoss_le_C (n N : ℕ) (δ c : NNReal) :
    (Kakeya.factoringStep1AtScaleConstant n N δ *
        (Kakeya.factoringStep2Step3Constant N : NNReal) *
        ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
          (step5PackingRatio n N δ)) *
        (c ^ n * rhoTubesGeometricLoss n) ≤
      shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c := by
  rw [shadingMultiplicityEstimateForRhoTubesDilate.C]
  refine le_max_of_le_right (le_max_of_le_left ?_)
  unfold Kakeya.factoringStep1Step2AtScaleConstant Kakeya.factoringStep2Step3Constant
  push_cast
  calc
    (Kakeya.factoringStep1AtScaleConstant n N δ *
          ((Kakeya.factoringStep2PigeonholeConstant N : NNReal) *
            Kakeya.factoringStep3Constant N) *
          ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
            (step5PackingRatio n N δ)) *
          (c ^ n * rhoTubesGeometricLoss n)
        ≤ 2 * ((Kakeya.factoringStep1AtScaleConstant n N δ *
          ((Kakeya.factoringStep2PigeonholeConstant N : NNReal) *
            Kakeya.factoringStep3Constant N) *
          ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
            (step5PackingRatio n N δ)) *
          (c ^ n * rhoTubesGeometricLoss n)) := by
            exact le_mul_of_one_le_left (by positivity) (by norm_num)
    _ = c ^ n *
        (2 * (Kakeya.factoringStep1AtScaleConstant n N δ *
          (Kakeya.factoringStep2PigeonholeConstant N : NNReal)) *
          Kakeya.factoringStep3Constant N *
          ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
            (step5PackingRatio n N δ) * rhoTubesGeometricLoss n) := by ring

/-- Cross-multiplication for finite, nonzero `ENNReal` denominators. -/
private lemma ennreal_div_le_div_of_mul_le_mul {a b c d : ENNReal}
    (hb0 : b ≠ 0) (hbtop : b ≠ ⊤) (hd0 : d ≠ 0) (hdtop : d ≠ ⊤)
    (h : a * d ≤ c * b) : a / b ≤ c / d := by
  rw [ENNReal.div_le_iff hb0 hbtop]
  rw [show c / d * b = (c * b) / d by
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
    ring]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hd0) (Or.inl hdtop)).2 h

private lemma pipelineRefinementConstant_eq_inv (n N : ℕ) (δ : NNReal) :
    ShadedBody.Kakeya.factoringPipelineSelfRefinementConstant n N δ
        (step5PackingRatio n N δ) =
      (Kakeya.factoringStep1AtScaleConstant n N δ *
        (Kakeya.factoringStep2Step3Constant N : NNReal) *
        ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
          (step5PackingRatio n N δ))⁻¹ := by
  unfold ShadedBody.Kakeya.factoringPipelineSelfRefinementConstant
  rw [mul_inv]
  ring

open Classical in
private lemma ball_estimate_of_cover (U W : Set E) (S : Finset E) (r : NNReal) (x : E)
    (hr : 0 < r) (hU : MeasurableSet U)
    (hW : W ⊆ ⋃ z ∈ S, Metric.closedBall z (4 * (r : ℝ)))
    (hover : ∀ x, {z ∈ S | x ∈ Metric.closedBall z (r : ℝ)}.card ≤
      Kakeya.factoringStep5OverlapConstant (Module.finrank ℝ E))
    (hlocal : ∀ x, ∀ z ∈ S,
      volume (U ∩ Metric.ball x (r : ℝ)) ≤
        2 * Kakeya.factoringStep5OverlapConstant (Module.finrank ℝ E) *
          volume (U ∩ Metric.closedBall z (r : ℝ))) :
    volume W * (volume (U ∩ Metric.ball x (r : ℝ)) /
        volume (Metric.ball x (r : ℝ))) ≤
      (rhoTubesBallLoss (Module.finrank ℝ E) : ENNReal) * volume U := by
  let n := Module.finrank ℝ E
  let O : ENNReal := Kakeya.factoringStep5OverlapConstant n
  let B : ENNReal := volume (Metric.ball x (r : ℝ))
  let m : ENNReal := volume (U ∩ Metric.ball x (r : ℝ))
  have hB0 : B ≠ 0 := by
    simp only [B, InnerProductSpace.volume_ball]
    positivity
  have hBtop : B ≠ ⊤ := by
    simp only [B, InnerProductSpace.volume_ball]
    finiteness
  have hball : ∀ z : E, volume (Metric.closedBall z (4 * (r : ℝ))) =
      (4 ^ n : ℕ) * B := by
    intro z
    rw [InnerProductSpace.volume_closedBall]
    simp only [B, InnerProductSpace.volume_ball]
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4)]
    norm_num [n, mul_pow]
    ring
  have hWvol : volume W ≤ (S.card : ENNReal) * ((4 ^ n : ℕ) * B) := by
    calc
      volume W ≤ volume (⋃ z ∈ S, Metric.closedBall z (4 * (r : ℝ))) := measure_mono hW
      _ ≤ ∑ z ∈ S, volume (Metric.closedBall z (4 * (r : ℝ))) :=
        measure_biUnion_finset_le _ _
      _ = (S.card : ENNReal) * ((4 ^ n : ℕ) * B) := by
        simp_rw [hball]
        rw [Finset.sum_const, nsmul_eq_mul]
  have hsum : ∑ z ∈ S, volume (U ∩ Metric.closedBall z (r : ℝ)) ≤ O * volume U := by
    calc
      ∑ z ∈ S, volume (U ∩ Metric.closedBall z (r : ℝ)) ≤
          O * volume (⋃ z ∈ S, U ∩ Metric.closedBall z (r : ℝ)) := by
        apply MeasureTheory.sum_measure_le_mul_measure_biUnion_of_card_filter_le
        · intro z hz
          exact hU.inter Metric.isClosed_closedBall.measurableSet
        · intro y
          have hcard : {z ∈ S | y ∈ U ∩ Metric.closedBall z (r : ℝ)}.card ≤
              {z ∈ S | y ∈ Metric.closedBall z (r : ℝ)}.card := by
            apply Finset.card_le_card
            intro z hz
            simp only [Finset.mem_filter, Set.mem_inter_iff] at hz ⊢
            exact ⟨hz.1, hz.2.2⟩
          rw [Finset.filter_congr_decidable]
          simpa only [n] using hcard.trans (hover y)
      _ ≤ O * volume U := by
        gcongr
        intro y hy
        obtain ⟨z, hz, hy⟩ := Set.mem_iUnion₂.mp hy
        exact hy.1
  have hcardm : (S.card : ENNReal) * m ≤ 2 * O * ∑ z ∈ S,
      volume (U ∩ Metric.closedBall z (r : ℝ)) := by
    calc
      (S.card : ENNReal) * m = ∑ z ∈ S, m := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ z ∈ S, 2 * O * volume (U ∩ Metric.closedBall z (r : ℝ)) := by
        exact Finset.sum_le_sum fun z hz ↦ hlocal x z hz
      _ = 2 * O * ∑ z ∈ S, volume (U ∩ Metric.closedBall z (r : ℝ)) := by
        rw [Finset.mul_sum]
  have hcross : volume W * m ≤ (rhoTubesBallLoss n : ENNReal) * B * volume U := by
    calc
      volume W * m ≤ ((S.card : ENNReal) * ((4 ^ n : ℕ) * B)) * m := by gcongr
      _ = ((4 ^ n : ℕ) * B) * ((S.card : ENNReal) * m) := by ring
      _ ≤ ((4 ^ n : ℕ) * B) *
          (2 * O * ∑ z ∈ S, volume (U ∩ Metric.closedBall z (r : ℝ))) := by gcongr
      _ ≤ ((4 ^ n : ℕ) * B) * (2 * O * (O * volume U)) := by gcongr
      _ = (rhoTubesBallLoss n : ENNReal) * B * volume U := by
        simp only [rhoTubesBallLoss, O]
        push_cast
        ring
  change volume W * (m / B) ≤ _
  rw [← mul_div_assoc]
  apply (ENNReal.div_le_iff hB0 hBtop).2
  simpa [mul_assoc, mul_comm, mul_left_comm] using hcross

open Classical in
/-- A separated family of witness balls converts uniform local outer incidence into an average
outer multiplicity bound. -/
private lemma outerMultiplicity_lower_of_local_balls (t : Finset κ) (V : κ → ShadedBody E)
    (S : Finset E) (r : NNReal) (L : ℕ) (hr : 0 < r) (hL : 0 < L) (hS : S.Nonempty)
    (hsep : Metric.IsSeparated (r : ENNReal) (S : Set E))
    (hcover : iUnionShade t V ⊆ ⋃ z ∈ S, Metric.closedBall z (4 * (r : ℝ)))
    (hlocal : ∀ z ∈ S, ∃ J : Finset κ, J ⊆ t ∧ L ≤ J.card ∧
      ∀ j ∈ J, ∃ p : E,
        Metric.ball p ((r : ℝ) / 8) ⊆ (V j).shade ∩ Metric.ball z (2 * (r : ℝ))) :
    (L : ENNReal) ≤ (rhoTubesOuterMultiplicityLoss (Module.finrank ℝ E) : ENNReal) *
      multiplicity t V := by
  let n := Module.finrank ℝ E
  let v : ENNReal := volume (Metric.ball (0 : E) ((r : ℝ) / 8))
  let O : ENNReal := Kakeya.factoringStep5OverlapConstant n
  let W : Set E := iUnionShade t V
  have hv0 : v ≠ 0 := by
    dsimp only [v]
    simp only [InnerProductSpace.volume_ball]
    positivity
  have hvtop : v ≠ ⊤ := by
    dsimp only [v]
    simp only [InnerProductSpace.volume_ball]
    finiteness
  have hball4 : ∀ z : E, volume (Metric.closedBall z (4 * (r : ℝ))) =
      (32 ^ n : ℕ) * v := by
    intro z
    rw [show 4 * (r : ℝ) = 32 * ((r : ℝ) / 8) by ring]
    rw [InnerProductSpace.volume_closedBall]
    simp only [v, InnerProductSpace.volume_ball]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32)]
    norm_num [n, mul_pow]
    ring
  have hover : ∀ x : E,
      {z ∈ S | x ∈ Metric.ball z (2 * (r : ℝ))}.card ≤
        Kakeya.factoringStep5OverlapConstant n := by
    intro x
    let A : Finset E := {z ∈ S | x ∈ Metric.ball z (2 * (r : ℝ))}
    have hAS : (A : Set E) ⊆ (S : Set E) := by
      intro z hz
      exact (Finset.mem_filter.mp hz).1
    have hdist : ∀ z ∈ A, dist z x ≤ 2 * (r : ℝ) := by
      intro z hz
      exact le_of_lt (by simpa [Metric.mem_ball, dist_comm] using (Finset.mem_filter.mp hz).2)
    simpa only [A, Kakeya.factoringStep5OverlapConstant] using
      Metric.IsSeparated.card_le_pow_of_dist_le hr (hsep.subset hAS) hdist
  have hlocsum : ∀ z ∈ S, (L : ENNReal) * v ≤
      ∑ j ∈ t, volume ((V j).shade ∩ Metric.ball z (2 * (r : ℝ))) := by
    intro z hz
    obtain ⟨J, hJt, hLJ, hJ⟩ := hlocal z hz
    calc
      (L : ENNReal) * v ≤ (J.card : ENNReal) * v := by gcongr
      _ = ∑ j ∈ J, v := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ J, volume ((V j).shade ∩ Metric.ball z (2 * (r : ℝ))) := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨p, hp⟩ := hJ j hj
        calc
          v = volume (Metric.ball p ((r : ℝ) / 8)) := by
            rw [MeasureTheory.Measure.addHaar_ball_center volume p ((r : ℝ) / 8)]
          _ ≤ volume ((V j).shade ∩ Metric.ball z (2 * (r : ℝ))) := measure_mono hp
      _ ≤ ∑ j ∈ t, volume ((V j).shade ∩ Metric.ball z (2 * (r : ℝ))) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hJt (fun _ _ _ ↦ bot_le)
  have hsumlocal : (S.card : ENNReal) * ((L : ENNReal) * v) ≤
      O * ∑ j ∈ t, volume (V j).shade := by
    calc
      (S.card : ENNReal) * ((L : ENNReal) * v) = ∑ z ∈ S, (L : ENNReal) * v := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ z ∈ S, ∑ j ∈ t,
          volume ((V j).shade ∩ Metric.ball z (2 * (r : ℝ))) :=
        Finset.sum_le_sum fun z hz ↦ hlocsum z hz
      _ = ∑ j ∈ t, ∑ z ∈ S,
          volume ((V j).shade ∩ Metric.ball z (2 * (r : ℝ))) := by
        rw [Finset.sum_comm]
      _ ≤ ∑ j ∈ t, O * volume (V j).shade := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          ∑ z ∈ S, volume ((V j).shade ∩ Metric.ball z (2 * (r : ℝ))) ≤
              O * volume (⋃ z ∈ S, (V j).shade ∩ Metric.ball z (2 * (r : ℝ))) := by
            apply MeasureTheory.sum_measure_le_mul_measure_biUnion_of_card_filter_le
            · intro z _
              exact (V j).measurableSet_shade.inter Metric.isOpen_ball.measurableSet
            · intro x
              have hc : {z ∈ S | x ∈ (V j).shade ∩ Metric.ball z (2 * (r : ℝ))}.card ≤
                  {z ∈ S | x ∈ Metric.ball z (2 * (r : ℝ))}.card := by
                apply Finset.card_le_card
                intro z hz
                exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
                  (Finset.mem_filter.mp hz).2.2⟩
              exact_mod_cast hc.trans (hover x)
          _ ≤ O * volume (V j).shade := by
            gcongr
            intro x hx
            obtain ⟨z, _, hx⟩ := Set.mem_iUnion₂.mp hx
            exact hx.1
      _ = O * ∑ j ∈ t, volume (V j).shade := by rw [Finset.mul_sum]
  have hWvol : volume W ≤ (S.card : ENNReal) * ((32 ^ n : ℕ) * v) := by
    calc
      volume W ≤ volume (⋃ z ∈ S, Metric.closedBall z (4 * (r : ℝ))) := measure_mono hcover
      _ ≤ ∑ z ∈ S, volume (Metric.closedBall z (4 * (r : ℝ))) :=
        measure_biUnion_finset_le _ _
      _ = (S.card : ENNReal) * ((32 ^ n : ℕ) * v) := by
        simp_rw [hball4]
        rw [Finset.sum_const, nsmul_eq_mul]
  have hcross : (L : ENNReal) * volume W ≤
      (rhoTubesOuterMultiplicityLoss n : ENNReal) * ∑ j ∈ t, volume (V j).shade := by
    calc
      (L : ENNReal) * volume W ≤
          (L : ENNReal) * ((S.card : ENNReal) * ((32 ^ n : ℕ) * v)) := by gcongr
      _ = (32 ^ n : ℕ) * ((S.card : ENNReal) * ((L : ENNReal) * v)) := by ring
      _ ≤ (32 ^ n : ℕ) * (O * ∑ j ∈ t, volume (V j).shade) := by gcongr
      _ = (rhoTubesOuterMultiplicityLoss n : ENNReal) *
          ∑ j ∈ t, volume (V j).shade := by
        simp only [rhoTubesOuterMultiplicityLoss, O]
        push_cast
        ring
  have hW0 : volume W ≠ 0 := by
    obtain ⟨z, hz⟩ := hS
    obtain ⟨J, hJt, hLJ, hJ⟩ := hlocal z hz
    obtain ⟨j, hj⟩ : J.Nonempty := Finset.nonempty_of_ne_empty (by
      intro hJe
      subst J
      simp at hLJ
      omega)
    obtain ⟨p, hp⟩ := hJ j hj
    apply ne_of_gt
    calc
      0 < v := pos_iff_ne_zero.mpr hv0
      _ = volume (Metric.ball p ((r : ℝ) / 8)) := by
        rw [MeasureTheory.Measure.addHaar_ball_center volume p ((r : ℝ) / 8)]
      _ ≤ volume W := measure_mono ((hp.trans Set.inter_subset_left).trans
        (Set.subset_iUnion₂_of_subset j (hJt hj) (Set.Subset.refl _)))
  have hWtop : volume W ≠ ⊤ := volume_iUnion_shade_ne_top t V
  rw [multiplicity_eq_div]
  calc
    (L : ENNReal) ≤
        ((rhoTubesOuterMultiplicityLoss n : ENNReal) *
          ∑ j ∈ t, volume (V j).shade) / volume W :=
      (ENNReal.le_div_iff_mul_le (Or.inl hW0) (Or.inl hWtop)).2 hcross
    _ = (rhoTubesOuterMultiplicityLoss n : ENNReal) *
        ((∑ j ∈ t, volume (V j).shade) / volume W) := mul_div_assoc _ _ _

private lemma four_mul_pipeline_outerLoss_le_C (n N : ℕ) (δ c : NNReal) (hc : 1 ≤ c) :
    4 * (Kakeya.factoringStep1AtScaleConstant n N δ *
        (Kakeya.factoringStep2Step3Constant N : NNReal) *
        ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
          (step5PackingRatio n N δ)) * rhoTubesOuterMultiplicityLoss n ≤
      shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c := by
  apply (pipelineGeometricLoss_le_C n N δ c).trans'
  have hc' : (1 : NNReal) ≤ c ^ n := one_le_pow₀ hc
  have hloss : (4 : NNReal) * rhoTubesOuterMultiplicityLoss n ≤
      rhoTubesGeometricLoss n := by
    unfold rhoTubesGeometricLoss
    calc
      4 * rhoTubesOuterMultiplicityLoss n ≤
          4 * 1 * 1 ^ 2 * max 1 (rhoTubesOuterMultiplicityLoss n) := by
        simpa only [mul_one, one_pow] using mul_le_mul_right (le_max_right (1 : NNReal)
          (rhoTubesOuterMultiplicityLoss n)) (4 : NNReal)
      _ ≤ 4 * max 1 (Kakeya.Tube.dilateFullness.C n) *
          max 1 (Tube.volume_le.C n / Tube.le_volume.c n) ^ 2 *
            max 1 (rhoTubesOuterMultiplicityLoss n) := by
        gcongr <;> exact le_max_left _ _
  calc
    4 * (Kakeya.factoringStep1AtScaleConstant n N δ *
          (Kakeya.factoringStep2Step3Constant N : NNReal) *
          ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
            (step5PackingRatio n N δ)) * rhoTubesOuterMultiplicityLoss n =
        (Kakeya.factoringStep1AtScaleConstant n N δ *
          (Kakeya.factoringStep2Step3Constant N : NNReal) *
          ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
            (step5PackingRatio n N δ)) *
          (4 * rhoTubesOuterMultiplicityLoss n) := by ring
    _ ≤ (Kakeya.factoringStep1AtScaleConstant n N δ *
          (Kakeya.factoringStep2Step3Constant N : NNReal) *
          ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
            (step5PackingRatio n N δ)) *
          (c ^ n * rhoTubesGeometricLoss n) := by
      exact mul_le_mul_right (by simpa using mul_le_mul hc' hloss) _

set_option maxHeartbeats 800000 in
-- The explicit Step 5 covering and multiplicity bookkeeping is a large elaboration steps.
open Classical in
/-- **GWZ Lemma 5.11, dilate form.** The two-scale tube factoring estimate for an outer family of
`c`-dilates of `ρ`-tubes.

Setup: `F` packages a family of shaded `δ`-tubes as its inner family, recorded by the witness `T`,
and the `c`-dilates of a family of `ρ`-tubes as its outer family, recorded by the witness `Tρ`
together with `houter`. The parent map of `F` carries the partition
`𝕋 = ⋃_{T_ρ ∈ 𝕋_ρ} 𝕋[T_ρ]`, and `hball` confines the inner tubes to the unit ball.

Neither essential distinctness of the outer bodies nor any per-tube density hypothesis on the
inner shading is assumed, and no Frostman condition appears: for dilated tubes the fullness
transfer is elementary capsule geometry
(`Kakeya.Tube.volume_dilate_inter_cthickening_ge`), and the pigeonholing of Steps 0-5 needs
nothing more.

Conclusion: there is a fully shaded factor family `G` whose outer family is the selected subfamily
`𝕋_ρ'` with induced shading and whose inner family is the refinement `(𝕋', Y')`. The five
structural conjuncts identify `G` as a restriction of `F` that leaves the convex bodies alone; the
four remaining ones give the aggregate outer fullness lower bound, the refinement, the
multiplicity factorization (`boundMuTTYAcrossTwoScales`), the pointwise shading containment
(`pointwiseContainmenttube`), and the `ρ`-ball volume estimate (`boundVolumeAcrossTwoScales`).
All losses use the single constant
`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C`.

The proof is the Step 0 - Step 5 pipeline of `Kakeya/Factoring/Step0.lean` through
`Kakeya/Factoring/Step5.lean`, with the fullness input supplied by
`Kakeya.Tube.volume_dilate_inter_cthickening_ge`. -/
theorem shadingMultiplicityEstimateForRhoTubesDilate
    {δ ρ c : ℝ≥0} (hδ : 0 < δ) (hρ : ρ ∈ Set.Icc δ 1) (hc : 1 ≤ c)
    (F : FactorFamily E ι κ)
    (T : ι → ShadedTube δ E) (Tρ : κ → Tube ρ E)
    (hinner : ∀ i ∈ F.innerSet, F.innerBody i = (T i).toShadedBody)
    (houter : ∀ j ∈ F.outerSet, F.outerBody j = Kakeya.Tube.dilate (Tρ j) (c : ℝ))
    (hball : ∀ i ∈ F.innerSet, (F.innerBody i).carrier ⊆ Metric.closedBall 0 1) :
    ∃ G : ShadedFactorFamily E ι κ,
      -- `G` restricts `F` to the selected outer family without changing convex bodies.
      G.outerSet ⊆ F.outerSet ∧
      G.innerSet = {i ∈ F.innerSet | F.parent i ∈ G.outerSet} ∧
      G.parent = F.parent ∧
      (∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody = F.outerBody j) ∧
      (∀ i ∈ F.innerSet,
        (G.innerBody i).toConvexSpaceBody = (F.innerBody i).toConvexSpaceBody) ∧
      -- The selected outer family is nonempty as soon as the inner shading carries mass; the
      -- hypothesis cannot be dropped, since a null shading selects nothing.
      (0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade → G.outerSet.Nonempty) ∧
      -- `λ (𝕋_ρ', Y_{𝕋_ρ}') ⪆ λ (𝕋, Y)`, in aggregate fullness.
      (shadingMultiplicityEstimateForRhoTubesDilate.C
            (Module.finrank ℝ E) F.innerSet.card δ c)⁻¹ *
          fullness F.innerSet F.innerBody
        ≤ fullness G.outerSet G.outerBody ∧
      -- `(𝕋', Y')` is a `≈ 1` (here `⪆ 1`) refinement of `(𝕋, Y)`.
      IsCRefinement G.innerSet G.innerBody F.innerSet F.innerBody
        (shadingMultiplicityEstimateForRhoTubesDilate.C
          (Module.finrank ℝ E) F.innerSet.card δ c)⁻¹ ∧
      -- `boundMuTTYAcrossTwoScales`: `μ(𝕋, Y) ⪅ μ(𝕋_ρ', Y_{𝕋_ρ}') · μ(𝕋[T_ρ], Y')`.
      (∀ j ∈ G.outerSet,
        multiplicity F.innerSet F.innerBody
          ≤ (shadingMultiplicityEstimateForRhoTubesDilate.C
                (Module.finrank ℝ E) F.innerSet.card δ c : ENNReal)
            * multiplicity G.outerSet G.outerBody
            * multiplicity (G.fiber j) G.innerBody) ∧
      -- `pointwiseContainmenttube`: since each `δ`-tube has a unique parent, the pointwise
      -- containment `𝕋_{Y'}(x) ⊂ ⋃_{T_ρ ∈ 𝕋_ρ', x ∈ Y_{𝕋_ρ'}(T_ρ)} (𝕋[T_ρ])_{Y'}(x)` is the
      -- shading inclusion below.
      (∀ i ∈ G.innerSet,
        (G.innerBody i).shade ⊆ (G.outerBody (F.parent i)).shade) ∧
      -- `boundVolumeAcrossTwoScales`: for `x ∈ U(𝕋_ρ', Y_{𝕋_ρ}')`,
      -- `|U(𝕋, Y')| ⪆ |U(𝕋_ρ', Y_{𝕋_ρ}')| · |U(𝕋, Y') ∩ B(x, ρ)| / |B(x, ρ)|`.
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (shadingMultiplicityEstimateForRhoTubesDilate.C
              (Module.finrank ℝ E) F.innerSet.card δ c : ENNReal)⁻¹
          * volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade)
          * (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ Metric.ball x (ρ : ℝ))
              / volume (Metric.ball x (ρ : ℝ)))
          ≤ volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade))
      -- GWZ Definition 5.7, exposed: the outer shading contains the `2ρ`-neighbourhood, inside the
      -- outer carrier, of every selected inner shade of its fibre
      ∧ (∀ j ∈ G.outerSet, ∀ i ∈ G.innerSet, G.parent i = j →
          (G.outerBody j).carrier ∩ Metric.cthickening (2 * (ρ : ℝ)) (G.innerBody i).shade
            ⊆ (G.outerBody j).shade) := by
  let n := Module.finrank ℝ E
  let N := F.innerSet.card
  have hdisc : F.InnerIsDiscretizedAtScale δ :=
    { subset_unitBall := hball
      le_scale := by
        intro i hi
        rw [hinner i hi]
        exact Tube.le_ethickness_scale (T i).toTube }
  have hρpos : 0 < ρ := hδ.trans_le hρ.1
  have hρreal : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρpos
  let Ω := F.pipelineSet hδ hdisc (ρ : ℝ) hρreal
  have hΩ : MeasurableSet Ω := F.measurableSet_pipelineSet hδ hdisc (ρ : ℝ) hρreal
  obtain ⟨T₅, T₅', hT₅sub, hT₅sep, hT₅cover, hT₅overlap, hT₅'T₅, hT₅'pos, hT₅'sep,
      href₅, hballcomp⟩ :=
    exists_factoringPipelineSelf F hδ hdisc (ρ : ℝ) hρreal hΩ hρpos
  let G₅ := F.pipelineFamily hδ hdisc (ρ : ℝ) hρreal hΩ T₅' ρ
  have hT₅ball : (T₅ : Set E) ⊆ Metric.closedBall 0 1 := by
    refine hT₅sub.trans ?_
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    have hiF : i ∈ F.innerSet := by
      rw [FactorFamily.pipelineInnerSet] at hi
      exact F.innerSet_step0_subset (Finset.mem_filter.mp hi).1
    apply hball i hiF
    have hxcarrier := (step3InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
      (F.pipelineSet hδ hdisc (ρ : ℝ) hρreal) hΩ
      (F.pipelineExponent hδ hdisc (ρ : ℝ) hρreal) i).shade_subset hxi
    simpa using hxcarrier
  have hT₅card : (T₅.card : NNReal) ≤ step5PackingRatio n N δ := by
    exact card_le_step5PackingRatio hδ hρ hT₅ball hT₅sep
  have hratio1 : (1 : NNReal) ≤ step5PackingRatio n N δ := by
    rw [step5PackingRatio, mul_div_assoc,
      Kakeya.step1UpperBdAtScale_div_step1LowerBdAtScale n (max 1 N) hδ]
    have hfact : (1 : NNReal) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hN : (1 : NNReal) ≤ max 1 N := by exact_mod_cast le_max_left 1 N
    have hδ1 : δ ≤ 1 := hρ.1.trans hρ.2
    have hinv : (1 : NNReal) ≤ (δ ^ n)⁻¹ := by
      rw [one_le_inv₀ (pow_pos hδ n)]
      exact pow_le_one₀ δ.coe_nonneg hδ1
    calc
      1 ≤ (2 : NNReal) ^ n := one_le_pow₀ (by norm_num)
      _ ≤ 2 ^ n * (2 ^ n * 1 * 1 * 1) := by
        simpa using le_mul_of_one_le_right (by positivity : (0 : NNReal) ≤ 2 ^ n)
          (one_le_pow₀ (by norm_num : (1 : NNReal) ≤ 2))
      _ ≤ 2 ^ n * (2 ^ n * n.factorial * max 1 N * (δ ^ n)⁻¹) := by gcongr
  have hselfpos : 0 < ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n T₅.card := by
    unfold ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant
    have hFpos : 0 < Kakeya.factoringStep1FiberPigeonholeConstant 1 T₅.card := by
      cases hcard : T₅.card with
      | zero =>
          have heq : Kakeya.factoringStep1FiberPigeonholeConstant 1 T₅.card = 1 := by
            rw [← ENNReal.coe_inj]
            rw [Kakeya.coe_factoringStep1FiberPigeonholeConstant]
            simp [hcard]
          simpa [hcard] using congrArg (fun q : NNReal ↦ 0 < q) heq |>.mpr zero_lt_one
      | succ m =>
          exact lt_of_lt_of_le zero_lt_one
            (Kakeya.one_le_factoringStep1FiberPigeonholeConstant
              (show (1 : NNReal) ≤ (m + 1 : ℕ) by exact_mod_cast Nat.succ_pos m))
    have hO : (0 : NNReal) < Kakeya.factoringStep5OverlapConstant n := by
      unfold Kakeya.factoringStep5OverlapConstant
      positivity
    exact mul_pos (mul_pos (by norm_num) hO) (mul_pos (by norm_num) hFpos)
  have hcoef :
      (ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
        (step5PackingRatio n N δ))⁻¹ ≤
      (ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n T₅.card)⁻¹ :=
    inv_anti₀ hselfpos (step5SelfPigeonholeConstant_mono hT₅card hratio1)
  have href₅' := isCRefinement_mono hcoef href₅
  have hrefG₅ : IsCRefinement G₅.innerSet G₅.innerBody F.innerSet F.innerBody
      (ShadedBody.Kakeya.factoringPipelineSelfRefinementConstant n N δ
        (step5PackingRatio n N δ)) := by
    simpa [G₅, n, N] using
      F.pipelineFamily_isCRefinementSelf hδ hdisc (ρ : ℝ) hρreal hΩ T₅' ρ href₅'
  let K : κ → ConvexSpaceBody E := fun j ↦ Kakeya.Tube.dilate (Tρ j) (c : ℝ)
  have hK : ∀ i ∈ F.innerSet, (F.innerBody i).toConvexSpaceBody ≤ K (F.parent i) := by
    intro i hi
    rw [show K (F.parent i) = F.outerBody (F.parent i) by
      exact (houter (F.parent i) (F.parent_mem i hi)).symm]
    exact F.inner_le_parent i hi
  let G := completedPipelineFamily F G₅ K ρ
    (F.pipelineFamily_outerSet_subset hδ hdisc (ρ : ℝ) hρreal hΩ T₅' ρ)
    (F.pipelineFamily_parent hδ hdisc (ρ : ℝ) hρreal hΩ T₅' ρ)
    (F.pipelineFamily_innerBody_toConvexSpaceBody hδ hdisc (ρ : ℝ) hρreal hΩ T₅' ρ) hK
  refine ⟨G, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · intro j hj
    exact F.pipelineFamily_outerSet_subset hδ hdisc (ρ : ℝ) hρreal hΩ T₅' ρ
      ((Finset.mem_filter.mp hj).1)
  · intro j hj
    change K j = F.outerBody j
    exact houter j (F.pipelineFamily_outerSet_subset hδ hdisc (ρ : ℝ) hρreal hΩ T₅' ρ
      ((Finset.mem_filter.mp hj).1)) |>.symm
  · intro i hi
    change (completedInnerBody F G₅ i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody
    by_cases hi₅ : i ∈ G₅.innerSet
    · rw [completedInnerBody, if_pos hi₅]
      exact F.pipelineFamily_innerBody_toConvexSpaceBody hδ hdisc (ρ : ℝ) hρreal hΩ T₅' ρ i
    · simp [completedInnerBody, hi₅]
  · have hsub₅ : G₅.innerSet ⊆ F.innerSet := hrefG₅.1.1
    have hparent₅ : G₅.parent = F.parent :=
      F.pipelineFamily_parent hδ hdisc (ρ : ℝ) hρreal hΩ T₅' ρ
    have hsum : ∑ i ∈ G.innerSet, volume (G.innerBody i).shade =
        ∑ i ∈ G₅.innerSet, volume (G₅.innerBody i).shade := by
      simpa [G, completedPipelineFamily] using
        sum_volume_completedInnerBody F G₅ hsub₅ hparent₅
    have hδ1 : δ ≤ 1 := hρ.1.trans hρ.2
    have hnonempty : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade →
        G.outerSet.Nonempty := by
      intro hmass
      have hNpos : 0 < N := by
        by_contra hN0
        have he : F.innerSet = ∅ := Finset.card_eq_zero.mp (by simpa [N] using hN0)
        simp [he] at hmass
      have hA : 0 < Kakeya.factoringStep1AtScaleConstant n N δ := by
        have hN1 := Nat.one_le_iff_ne_zero.mpr hNpos.ne'
        have hl := Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale_nonneg
          n hN1 hδ hδ1
        rw [Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale n hN1 hδ] at hl
        rw [Kakeya.factoringStep1AtScaleConstant_eq n hN1 hδ]
        apply mul_pos (by norm_num)
        rw [Real.toNNReal_pos]
        linarith
      have hB : 0 < (Kakeya.factoringStep2Step3Constant N : NNReal) := by
        rw [Kakeya.factoringStep2Step3Constant_eq]
        positivity
      have hD : 0 < ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
          (step5PackingRatio n N δ) := by
        unfold ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant
        have hO : (0 : NNReal) < Kakeya.factoringStep5OverlapConstant n := by
          unfold Kakeya.factoringStep5OverlapConstant
          positivity
        have hF : 0 < Kakeya.factoringStep1FiberPigeonholeConstant 1
            (step5PackingRatio n N δ) := lt_of_lt_of_le zero_lt_one
          (Kakeya.one_le_factoringStep1FiberPigeonholeConstant hratio1)
        exact mul_pos (mul_pos (by norm_num) hO) (mul_pos (by norm_num) hF)
      have hRpos : 0 < ShadedBody.Kakeya.factoringPipelineSelfRefinementConstant n N δ
          (step5PackingRatio n N δ) := by
        rw [pipelineRefinementConstant_eq_inv]
        positivity
      have hsum₅ : 0 < ∑ i ∈ G₅.innerSet, volume (G₅.innerBody i).shade := by
        exact (ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr hRpos.ne') hmass.ne').trans_le hrefG₅.2
      obtain ⟨i, hi₅, hvi⟩ := Finset.sum_pos_iff.mp hsum₅
      refine ⟨G₅.parent i, ?_⟩
      change G₅.parent i ∈ activeOuterSet G₅
      apply Finset.mem_filter.mpr
      refine ⟨G₅.parent_mem i hi₅, ?_⟩
      have hmono : volume (G₅.innerBody i).shade ≤
          volume (iUnionShade (G₅.fiber (G₅.parent i)) G₅.innerBody) := by
        apply measure_mono
        exact Set.subset_iUnion₂_of_subset i
          (Finset.mem_filter.mpr ⟨hi₅, rfl⟩) (Set.Subset.refl _)
      exact ne_of_gt (hvi.trans_le hmono)
    refine ⟨hnonempty, ?_⟩
    have hrefG : IsCRefinement G.innerSet G.innerBody F.innerSet F.innerBody
        (ShadedBody.Kakeya.factoringPipelineSelfRefinementConstant n N δ
          (step5PackingRatio n N δ)) := by
      constructor
      · constructor
        · intro i hi
          exact (Finset.mem_filter.mp hi).1
        · intro i hi
          by_cases hi₅ : i ∈ G₅.innerSet
          · rw [show G.innerBody i = G₅.innerBody i by
                simp [G, completedPipelineFamily, completedInnerBody, hi₅]]
            exact hrefG₅.1.2 i hi₅
          · constructor
            · simp [G, completedPipelineFamily, completedInnerBody, hi₅]
            · simp [G, completedPipelineFamily, completedInnerBody, hi₅]
      · rw [hsum]
        exact hrefG₅.2
    have hrefFinal : IsCRefinement G.innerSet G.innerBody F.innerSet F.innerBody
        (shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c)⁻¹ := by
      by_cases hN0 : N = 0
      · have he : F.innerSet = ∅ := Finset.card_eq_zero.mp (by simpa [N] using hN0)
        refine ⟨hrefG.1, ?_⟩
        simp [he]
      · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
        have hA : 0 < Kakeya.factoringStep1AtScaleConstant n N δ := by
          have hl := Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale_nonneg
            n hN1 hδ hδ1
          rw [Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale n hN1 hδ] at hl
          rw [Kakeya.factoringStep1AtScaleConstant_eq n hN1 hδ]
          apply mul_pos (by norm_num)
          rw [Real.toNNReal_pos]
          linarith
        have hB : 0 < (Kakeya.factoringStep2Step3Constant N : NNReal) := by
          rw [Kakeya.factoringStep2Step3Constant_eq]
          positivity
        have hD : 0 < ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
            (step5PackingRatio n N δ) := by
          unfold ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant
          have hO : (0 : NNReal) < Kakeya.factoringStep5OverlapConstant n := by
            unfold Kakeya.factoringStep5OverlapConstant
            positivity
          have hF : 0 < Kakeya.factoringStep1FiberPigeonholeConstant 1
              (step5PackingRatio n N δ) := lt_of_lt_of_le zero_lt_one
            (Kakeya.one_le_factoringStep1FiberPigeonholeConstant hratio1)
          exact mul_pos (mul_pos (by norm_num) hO) (mul_pos (by norm_num) hF)
        have hCinv : (shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c)⁻¹ ≤
            ShadedBody.Kakeya.factoringPipelineSelfRefinementConstant n N δ
              (step5PackingRatio n N δ) := by
          rw [pipelineRefinementConstant_eq_inv]
          exact inv_anti₀ (by positivity) (pipelineLoss_le_C n N δ c hc)
        exact isCRefinement_mono hCinv hrefG
    refine ⟨?_, hrefFinal, ?_⟩
    · by_cases hmass0 : ∑ i ∈ F.innerSet, volume (F.innerBody i).shade = 0
      · have hfzero : fullness F.innerSet F.innerBody = 0 := by
          apply ENNReal.coe_injective
          calc
            (fullness F.innerSet F.innerBody : ENNReal) = fullness' F.innerSet F.innerBody :=
              coe_fullness F.innerSet F.innerBody
            _ = 0 := by simp [fullness', hmass0]
            _ = (0 : NNReal) := rfl
        rw [hfzero]
        simp
      · have ht : G.outerSet.Nonempty := hnonempty (pos_iff_ne_zero.mpr hmass0)
        let A : κ → ENNReal := fun j ↦ fiberVolume F (F.pipelineInnerSet hδ hdisc) j
        let KV : κ → ENNReal := fun j ↦ volume (K j).carrier
        let S : κ → ENNReal := fun j ↦
          ∑ i ∈ G₅.fiber j, volume (G₅.innerBody i).shade
        let O : κ → ENNReal := fun j ↦ volume (G.outerBody j).shade
        let Q : ENNReal :=
          (Tube.volume_le.C n / Tube.le_volume.c n : NNReal)
        let D : ENNReal := (Kakeya.Tube.dilateFullness.C n : ENNReal) *
          ENNReal.ofReal ((c : ℝ) ^ n)
        have hAcomp : ∀ j ∈ G.outerSet, ∀ j' ∈ G.outerSet, A j ≤ 2 * A j' := by
          intro j hj j' hj'
          exact F.pipelineFamily_fiberVolume_le_two_mul hδ hdisc (ρ : ℝ) hρreal hΩ T₅' ρ
            (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj').1
        have hKcomp : ∀ j ∈ G.outerSet, ∀ j' ∈ G.outerSet, KV j ≤ Q * KV j' := by
          intro j _ j' _
          exact volume_dilate_le_ratio_mul hρ.2 (by positivity) (Tρ j) (Tρ j')
        have hblock : ∀ j ∈ G.outerSet, S j * KV j ≤ D * O j * A j := by
          intro j hj
          have hjactive : j ∈ activeOuterSet G₅ := by simpa [G, completedPipelineFamily] using hj
          have hterm : ∀ i ∈ G₅.fiber j,
              (volume (G₅.innerBody i).shade / volume (T i).carrier) * KV j ≤
                D * O j := by
            intro i hi
            have hi₅ : i ∈ G₅.innerSet := (Finset.mem_filter.mp hi).1
            have hip : F.parent i = j := by
              simpa [hparent₅] using (Finset.mem_filter.mp hi).2
            have hiF : i ∈ F.innerSet := hsub₅ hi₅
            have hY : (G₅.innerBody i).shade ⊆ (T i).carrier := by
              have hcarr := hrefG₅.1.2 i hi₅
              calc
                (G₅.innerBody i).shade ⊆ (G₅.innerBody i).carrier :=
                  (G₅.innerBody i).shade_subset
                _ = (F.innerBody i).carrier := congrArg ConvexSpaceBody.carrier hcarr.1
                _ = (T i).carrier := congrArg (fun W : ShadedBody E ↦ W.carrier) (hinner i hiF)
            have hsubK : (T i).carrier ⊆ (K j).carrier := by
              have hb : (F.innerBody i).carrier = (T i).carrier :=
                congrArg (fun W : ShadedBody E ↦ W.carrier) (hinner i hiF)
              rw [← hb, ← hip]
              exact hK i hiF
            have hgeom := Kakeya.Tube.volume_dilate_inter_cthickening_ge hδ hρ.1 hρ.2 hc
              (T i).toTube (Tρ j) hsubK hY
            have hinter : (K j).carrier ∩ Metric.cthickening (2 * (ρ : ℝ))
                (G₅.innerBody i).shade ⊆ (G.outerBody j).shade := by
              simpa only [G, completedPipelineFamily] using
                inter_cthickening_shade_subset_rhoCompletedOuterBody
                  F G₅ K ρ hjactive hi₅ hiF hip
            exact hgeom.trans (mul_le_mul_right (measure_mono hinter)
              ((Kakeya.Tube.dilateFullness.C n : ENNReal) *
                ENNReal.ofReal ((c : ℝ) ^ n)))
          have hV0 : ∀ i ∈ G₅.fiber j, volume (T i).carrier ≠ 0 := by
            intro i hi
            apply ne_of_gt
            apply (pos_iff_ne_zero.mpr ?_).trans_le (Tube.le_volume (T i).toTube)
            exact mul_ne_zero (by exact_mod_cast (Tube.le_volume.c_pos n).ne')
              (pow_ne_zero _ (by exact_mod_cast hδ.ne'))
          have hVtop : ∀ i ∈ G₅.fiber j, volume (T i).carrier ≠ ⊤ := by
            intro i _
            exact (T i).toShadedBody.isCompact.measure_lt_top.ne
          have hs := sum_mul_le_of_div_mul_le (G₅.fiber j)
            (fun i ↦ volume (G₅.innerBody i).shade)
            (fun i ↦ volume (T i).carrier) (KV j) (D * O j) hV0 hVtop hterm
          have hfiber : G₅.fiber j =
              {i ∈ F.pipelineInnerSet hδ hdisc | F.parent i = j} := by
            ext q
            simp [G₅, ShadedFactorFamily.fiber]
          have hcar : ∑ i ∈ G₅.fiber j, volume (T i).carrier = A j := by
            rw [hfiber]
            rw [show A j = fiberVolume F (F.pipelineInnerSet hδ hdisc) j by rfl]
            rw [fiberVolume_eq_sum]
            apply Finset.sum_congr rfl
            intro i hi
            have hiP : i ∈ F.pipelineInnerSet hδ hdisc := (Finset.mem_filter.mp hi).1
            rw [FactorFamily.pipelineInnerSet] at hiP
            have hiF : i ∈ F.innerSet := F.innerSet_step0_subset (Finset.mem_filter.mp hiP).1
            exact congrArg volume (congrArg (fun W : ShadedBody E ↦ W.carrier)
              (hinner i hiF)).symm
          rw [hcar] at hs
          simpa only [S, KV, D, mul_assoc] using hs
        have hagg := sum_mul_sum_le_of_pairwise_comparable G.outerSet ht A KV S O Q D
          hAcomp hKcomp hblock
        have hSsum : ∑ j ∈ G.outerSet, S j =
            ∑ i ∈ G₅.innerSet, volume (G₅.innerBody i).shade := by
          have hall : ∑ j ∈ G₅.outerSet, S j =
              ∑ i ∈ G₅.innerSet, volume (G₅.innerBody i).shade := by
            simpa [S, ShadedFactorFamily.fiber] using
              (Finset.sum_fiberwise_of_maps_to G₅.parent_mem
                (fun i ↦ volume (G₅.innerBody i).shade))
          rw [← hall]
          apply Finset.sum_subset (by
            intro j hj
            exact (Finset.mem_filter.mp hj).1)
          intro j hj hja
          have hz : volume (iUnionShade (G₅.fiber j) G₅.innerBody) = 0 := by
            by_contra hnz
            exact hja (by
              change j ∈ activeOuterSet G₅
              exact Finset.mem_filter.mpr ⟨hj, hnz⟩)
          apply Finset.sum_eq_zero
          intro i hi
          exact measure_mono_null
            (Set.subset_iUnion₂_of_subset i hi (Set.Subset.refl _)) hz
        have hAsum : ∑ j ∈ G.outerSet, A j ≤
            ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier := by
          calc
            ∑ j ∈ G.outerSet, A j ≤ ∑ j ∈ G₅.outerSet, A j := by
              exact Finset.sum_le_sum_of_subset_of_nonneg
                (fun j hj ↦ (Finset.mem_filter.mp hj).1) (fun _ _ _ ↦ bot_le)
            _ = ∑ i ∈ F.pipelineInnerSet hδ hdisc,
                volume (F.innerBody i).carrier := by
              simp_rw [A, fiberVolume_eq_sum]
              exact Finset.sum_fiberwise_of_maps_to
                (fun i hi ↦ by
                  rw [← FactorFamily.pipelineFamily_innerSet F hδ hdisc (ρ : ℝ)
                    hρreal hΩ T₅' ρ] at hi
                  exact G₅.parent_mem i hi)
                (fun i ↦ volume (F.innerBody i).carrier)
            _ ≤ ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier := by
              exact Finset.sum_le_sum_of_subset_of_nonneg hrefG₅.1.1 (fun _ _ _ ↦ bot_le)
        have hcross :
            (∑ i ∈ G₅.innerSet, volume (G₅.innerBody i).shade) *
                (∑ j ∈ G.outerSet, volume (G.outerBody j).carrier) ≤
              4 * Q ^ 2 * D *
                (∑ j ∈ G.outerSet, volume (G.outerBody j).shade) *
                (∑ i ∈ F.innerSet, volume (F.innerBody i).carrier) := by
          calc
            _ = (∑ j ∈ G.outerSet, S j) * (∑ j ∈ G.outerSet, KV j) := by
              rw [hSsum]
              rfl
            _ ≤ 4 * Q ^ 2 * D * (∑ j ∈ G.outerSet, O j) *
                (∑ j ∈ G.outerSet, A j) := hagg
            _ ≤ 4 * Q ^ 2 * D *
                (∑ j ∈ G.outerSet, volume (G.outerBody j).shade) *
                (∑ i ∈ F.innerSet, volume (F.innerBody i).carrier) := by
              dsimp only [O]
              gcongr
        let P : NNReal := Kakeya.factoringStep1AtScaleConstant n N δ *
          (Kakeya.factoringStep2Step3Constant N : NNReal) *
          ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
            (step5PackingRatio n N δ)
        let H : ENNReal := 4 * Q ^ 2 * D
        let C₀ : NNReal := shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c
        let SF : ENNReal := ∑ i ∈ F.innerSet, volume (F.innerBody i).shade
        let CF : ENNReal := ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier
        let ST : ENNReal := ∑ i ∈ G₅.innerSet, volume (G₅.innerBody i).shade
        let OT : ENNReal := ∑ j ∈ G.outerSet, volume (G.outerBody j).shade
        let KT : ENNReal := ∑ j ∈ G.outerSet, volume (G.outerBody j).carrier
        have hNpos : 0 < N := by
          by_contra hN0
          have he : F.innerSet = ∅ := Finset.card_eq_zero.mp (by simpa [N] using hN0)
          exact hmass0 (by simp [he])
        have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hNpos.ne'
        have hApos : 0 < Kakeya.factoringStep1AtScaleConstant n N δ := by
          have hl := Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale_nonneg
            n hN1 hδ hδ1
          rw [Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale n hN1 hδ] at hl
          rw [Kakeya.factoringStep1AtScaleConstant_eq n hN1 hδ]
          apply mul_pos (by norm_num)
          rw [Real.toNNReal_pos]
          linarith
        have hBpos : 0 < (Kakeya.factoringStep2Step3Constant N : NNReal) := by
          rw [Kakeya.factoringStep2Step3Constant_eq]
          positivity
        have hDpos : 0 < ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
            (step5PackingRatio n N δ) := by
          unfold ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant
          have hOpos : (0 : NNReal) < Kakeya.factoringStep5OverlapConstant n := by
            unfold Kakeya.factoringStep5OverlapConstant
            positivity
          have hFpos : 0 < Kakeya.factoringStep1FiberPigeonholeConstant 1
              (step5PackingRatio n N δ) := lt_of_lt_of_le zero_lt_one
            (Kakeya.one_le_factoringStep1FiberPigeonholeConstant hratio1)
          exact mul_pos (mul_pos (by norm_num) hOpos) (mul_pos (by norm_num) hFpos)
        have hPpos : 0 < P := mul_pos (mul_pos hApos hBpos) hDpos
        have hgeopos : 0 < c ^ n * rhoTubesGeometricLoss n := by
          have hgeo1 : (1 : NNReal) ≤ rhoTubesGeometricLoss n := by
            unfold rhoTubesGeometricLoss
            calc
              1 ≤ (4 : NNReal) := by norm_num
              _ ≤ 4 * max 1 (Kakeya.Tube.dilateFullness.C n) := by
                simpa only [mul_one] using
                  mul_le_mul_right (le_max_left (1 : NNReal) _) (4 : NNReal)
              _ ≤ 4 * max 1 (Kakeya.Tube.dilateFullness.C n) *
                  max 1 (Tube.volume_le.C n / Tube.le_volume.c n) ^ 2 := by
                apply le_mul_of_one_le_right (by positivity)
                exact one_le_pow₀ (le_max_left (1 : NNReal) _)
              _ ≤ 4 * max 1 (Kakeya.Tube.dilateFullness.C n) *
                  max 1 (Tube.volume_le.C n / Tube.le_volume.c n) ^ 2 *
                    max 1 (rhoTubesOuterMultiplicityLoss n) := by
                apply le_mul_of_one_le_right (by positivity)
                exact le_max_left _ _
          exact mul_pos (pow_pos (zero_lt_one.trans_le hc) n) (zero_lt_one.trans_le hgeo1)
        have hPHC : P * (c ^ n * rhoTubesGeometricLoss n) ≤ C₀ := by
          exact pipelineGeometricLoss_le_C n N δ c
        have hcoefNN : C₀⁻¹ * (c ^ n * rhoTubesGeometricLoss n) ≤ P⁻¹ := by
          calc
            C₀⁻¹ * (c ^ n * rhoTubesGeometricLoss n) ≤
                (P * (c ^ n * rhoTubesGeometricLoss n))⁻¹ *
                  (c ^ n * rhoTubesGeometricLoss n) := by
              gcongr
            _ = P⁻¹ := by
              rw [mul_inv, mul_assoc, inv_mul_cancel₀ hgeopos.ne', mul_one]
        have hHgeo : H ≤ (c ^ n * rhoTubesGeometricLoss n : NNReal) := by
          dsimp only [H, Q, D]
          rw [show ENNReal.ofReal ((c : ℝ) ^ n) = (c ^ n : NNReal) by
            rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_coe_nnreal,
              ENNReal.coe_pow]]
          have hNN : (4 : NNReal) *
              (Tube.volume_le.C n / Tube.le_volume.c n) ^ 2 *
                (Kakeya.Tube.dilateFullness.C n * c ^ n) ≤
              c ^ n * rhoTubesGeometricLoss n := by
            unfold rhoTubesGeometricLoss
            calc
              (4 : NNReal) *
                  (Tube.volume_le.C n / Tube.le_volume.c n) ^ 2 *
                    (Kakeya.Tube.dilateFullness.C n * c ^ n)
                  = c ^ n * (4 * Kakeya.Tube.dilateFullness.C n *
                      (Tube.volume_le.C n / Tube.le_volume.c n) ^ 2) := by ring
              _ ≤ c ^ n * (4 * max 1 (Kakeya.Tube.dilateFullness.C n) *
                    max 1 (Tube.volume_le.C n / Tube.le_volume.c n) ^ 2) := by
                gcongr
                · exact le_max_right _ _
                · exact le_max_right _ _
              _ ≤ c ^ n * (4 * max 1 (Kakeya.Tube.dilateFullness.C n) *
                    max 1 (Tube.volume_le.C n / Tube.le_volume.c n) ^ 2 *
                      max 1 (rhoTubesOuterMultiplicityLoss n)) := by
                apply mul_le_mul_right
                apply le_mul_of_one_le_right (by positivity)
                exact le_max_left _ _
          exact_mod_cast hNN
        have hC₀pos : 0 < C₀ := zero_lt_one.trans_le
          (shadingMultiplicityEstimateForRhoTubesDilate.one_le_C n N δ c)
        have hcoef : (C₀ : ENNReal)⁻¹ * H ≤ (P : ENNReal)⁻¹ := by
          calc
            (C₀ : ENNReal)⁻¹ * H ≤
                (C₀ : ENNReal)⁻¹ * (c ^ n * rhoTubesGeometricLoss n : NNReal) := by
              gcongr
            _ ≤ (P : ENNReal)⁻¹ := by
              rw [← ENNReal.coe_inv hC₀pos.ne',
                ← ENNReal.coe_mul, ← ENNReal.coe_inv hPpos.ne']
              exact ENNReal.coe_le_coe.mpr hcoefNN
        have hrefmass : (P : ENNReal)⁻¹ * SF ≤ ST := by
          have hR : ShadedBody.Kakeya.factoringPipelineSelfRefinementConstant n N δ
              (step5PackingRatio n N δ) = P⁻¹ := by
            simpa only [P] using pipelineRefinementConstant_eq_inv n N δ
          rw [hR] at hrefG₅
          rw [← ENNReal.coe_inv hPpos.ne']
          exact hrefG₅.2
        have hCF0 : CF ≠ 0 := by
          intro hzero
          apply hmass0
          apply le_antisymm
          · calc
              SF ≤ CF := Finset.sum_le_sum fun i _ ↦ measure_mono (F.innerBody i).shade_subset
              _ = 0 := hzero
          · exact bot_le
        have hCFtop : CF ≠ ⊤ := by
          dsimp only [CF]
          exact ENNReal.sum_ne_top.mpr fun i _ ↦ (F.innerBody i).isCompact.measure_lt_top.ne
        have hKT0 : KT ≠ 0 := by
          obtain ⟨j, hj⟩ := ht
          apply ne_of_gt
          apply (Finset.single_le_sum (fun _ _ ↦ bot_le) hj).trans_lt'
          change 0 < volume (K j).carrier
          rw [rho_volume_dilate_eq (Tρ j) (by positivity)]
          apply ENNReal.mul_pos
          · exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity) n)).ne'
          · exact (lt_of_lt_of_le (by
                exact_mod_cast mul_pos (Tube.le_volume.c_pos n) (pow_pos hρpos (n - 1)))
              (Tube.le_volume (Tρ j))).ne'
        have hKTtop : KT ≠ ⊤ := by
          dsimp only [KT]
          exact ENNReal.sum_ne_top.mpr fun j _ ↦ (G.outerBody j).isCompact.measure_lt_top.ne
        have hH0 : H ≠ 0 := by
          dsimp only [H, Q, D]
          apply mul_ne_zero
          · exact mul_ne_zero (by norm_num) (pow_ne_zero _ (by
              exact_mod_cast (div_pos (Tube.volume_le.C_pos n) (Tube.le_volume.c_pos n)).ne'))
          · exact mul_ne_zero (by exact_mod_cast (Kakeya.Tube.dilateFullness.C_pos n).ne')
              (ENNReal.ofReal_pos.mpr (pow_pos (by positivity) n)).ne'
        have hHtop : H ≠ ⊤ := by
          dsimp only [H, Q, D]
          finiteness
        have hscaled : ((C₀ : ENNReal)⁻¹ * H * SF) * KT ≤ H * (OT * CF) := by
          calc
            ((C₀ : ENNReal)⁻¹ * H * SF) * KT ≤
                ((P : ENNReal)⁻¹ * SF) * KT := by gcongr
            _ ≤ ST * KT := by gcongr
            _ ≤ H * (OT * CF) := by
              simpa [H, ST, OT, KT, CF, mul_assoc] using hcross
        have hproduct : ((C₀ : ENNReal)⁻¹ * SF) * KT ≤ OT * CF := by
          apply (ENNReal.mul_le_mul_iff_right hH0 hHtop).1
          simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled
        have hquot : ((C₀ : ENNReal)⁻¹ * SF) / CF ≤ OT / KT :=
          ennreal_div_le_div_of_mul_le_mul hCF0 hCFtop hKT0 hKTtop hproduct
        have hfinal : (shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c)⁻¹ *
            fullness F.innerSet F.innerBody ≤ fullness G.outerSet G.outerBody := by
          apply ENNReal.coe_le_coe.mp
          calc
            (((shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c)⁻¹ *
                  fullness F.innerSet F.innerBody : NNReal) : ENNReal) =
                (C₀ : ENNReal)⁻¹ * (SF / CF) := by
              calc
                _ = ((shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c)⁻¹ :
                      NNReal) * (fullness F.innerSet F.innerBody : ENNReal) :=
                    ENNReal.coe_mul _ _
                _ = (C₀ : ENNReal)⁻¹ * (SF / CF) := by
                  rw [ENNReal.coe_inv hC₀pos.ne', coe_fullness]
            _ ≤ OT / KT := by simpa only [mul_div_assoc] using hquot
            _ = (fullness G.outerSet G.outerBody : ENNReal) := by
              rw [coe_fullness]
        simpa only [n, N] using hfinal
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro j hj
        let u := F.step0.innerSet
        let t' := (F.step1 hδ hdisc).outerSet
        let k := F.pipelineExponent hδ hdisc (ρ : ℝ) hρreal
        let l := F.pipelineOuterExponent hδ hdisc (ρ : ℝ) hρreal
        let Z : Set E := ⋃ q ∈ G₅.outerSet.filter (fun q ↦ q ∉ activeOuterSet G₅),
          iUnionShade (G₅.fiber q) G₅.innerBody
        have hZzero : volume Z = 0 := by
          change volume (⋃ q ∈ ((G₅.outerSet.filter
            (fun q ↦ q ∉ activeOuterSet G₅)) : Set κ),
              iUnionShade (G₅.fiber q) G₅.innerBody) = 0
          apply (measure_biUnion_null_iff
            (Set.to_countable ((G₅.outerSet.filter
              (fun q ↦ q ∉ activeOuterSet G₅)) : Set κ))).2
          intro q hq
          obtain ⟨hqG, hqnot⟩ := Finset.mem_filter.mp hq
          by_contra hne
          exact hqnot (Finset.mem_filter.mpr ⟨hqG, hne⟩)
        have hcoverW : iUnionShade G.outerSet G.outerBody ⊆
            ⋃ z ∈ T₅', Metric.closedBall z (4 * (ρ : ℝ)) := by
          intro y hy
          obtain ⟨q, hq, hyq⟩ := Set.mem_iUnion₂.mp hy
          change y ∈ (K q).carrier ∩ Metric.cthickening (2 * (ρ : ℝ))
            (iUnionShade {i ∈ F.innerSet |
              F.parent i ∈ activeOuterSet G₅ ∧ F.parent i = q}
              (completedInnerBody F G₅)) at hyq
          have hthick := Metric.cthickening_subset_iUnion_closedBall_of_lt
            (iUnionShade {i ∈ F.innerSet |
              F.parent i ∈ activeOuterSet G₅ ∧ F.parent i = q}
              (completedInnerBody F G₅))
            (show (0 : ℝ) < 3 * (ρ : ℝ) by positivity)
            (show 2 * (ρ : ℝ) < 3 * (ρ : ℝ) by linarith) hyq.2
          obtain ⟨z, hzfib, hyz⟩ := Set.mem_iUnion₂.mp hthick
          have hqactive : q ∈ activeOuterSet G₅ := by
            simpa [G, completedPipelineFamily] using hq
          have hz₅ : z ∈ iUnionShade (G₅.fiber q) G₅.innerBody := by
            rw [← iUnionShade_completed_fiber F G₅ hsub₅ hparent₅ hqactive]
            exact hzfib
          obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp hz₅
          have hzi' : z ∈ (step5InnerBody F F.step0.innerSet
              (F.step1 hδ hdisc).outerSet
              (F.pipelineSet hδ hdisc (ρ : ℝ) hρreal) hΩ
              (F.pipelineExponent hδ hdisc (ρ : ℝ) hρreal) T₅' ρ i).shade := by
            simpa [G₅, FactorFamily.pipelineFamily] using hzi
          rw [shade_step5InnerBody] at hzi'
          obtain ⟨z₀, hz₀, hzz₀⟩ := Set.mem_iUnion₂.mp hzi'.2
          refine Set.mem_iUnion₂.mpr ⟨z₀, hz₀, Metric.mem_closedBall.mpr ?_⟩
          calc
            dist y z₀ ≤ dist y z + dist z z₀ := dist_triangle _ _ _
            _ ≤ 3 * (ρ : ℝ) + (ρ : ℝ) := by
              gcongr
              · exact Metric.mem_closedBall.mp hyz
              · exact Metric.mem_closedBall.mp hzz₀
            _ = 4 * (ρ : ℝ) := by ring
        have hT₅'ne : T₅'.Nonempty := by
          have hjactive : j ∈ activeOuterSet G₅ := by
            simpa [G, completedPipelineFamily] using hj
          have hvolj : volume (iUnionShade (G₅.fiber j) G₅.innerBody) ≠ 0 :=
            (Finset.mem_filter.mp hjactive).2
          obtain ⟨y, hy⟩ := MeasureTheory.nonempty_of_measure_ne_zero hvolj
          obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
          have hyi' : y ∈ (step5InnerBody F F.step0.innerSet
              (F.step1 hδ hdisc).outerSet
              (F.pipelineSet hδ hdisc (ρ : ℝ) hρreal) hΩ
              (F.pipelineExponent hδ hdisc (ρ : ℝ) hρreal) T₅' ρ i).shade := by
            simpa [G₅, FactorFamily.pipelineFamily] using hyi
          rw [shade_step5InnerBody] at hyi'
          obtain ⟨z, hz, _⟩ := Set.mem_iUnion₂.mp hyi'.2
          exact ⟨z, hz⟩
        have hlocal : ∀ z ∈ T₅', ∃ J : Finset κ, J ⊆ G.outerSet ∧
            2 ^ l ≤ J.card ∧ ∀ q ∈ J, ∃ p : E,
              Metric.ball p ((ρ : ℝ) / 8) ⊆
                (G.outerBody q).shade ∩ Metric.ball z (2 * (ρ : ℝ)) := by
          intro z hz
          let A : Set E := iUnionShade G₅.innerSet G₅.innerBody ∩
            Metric.closedBall z (ρ : ℝ)
          have hA0 : volume A ≠ 0 := by
            simpa [A, G₅] using hT₅'pos z hz
          have hnotSub : ¬ A ⊆ Z := by
            intro hAZ
            exact hA0 (measure_mono_null hAZ hZzero)
          obtain ⟨y, hyA, hyZ⟩ := Set.not_subset.mp hnotSub
          have hyG₅ : y ∈ iUnionShade G₅.innerSet G₅.innerBody := hyA.1
          obtain ⟨i₀, hi₀, hyi₀⟩ := Set.mem_iUnion₂.mp hyG₅
          have hyi₀' : y ∈ (step5InnerBody F u t'
              (F.pipelineSet hδ hdisc (ρ : ℝ) hρreal) hΩ k T₅' ρ i₀).shade := by
            simpa [G₅, FactorFamily.pipelineFamily, u, t', k] using hyi₀
          rw [shade_step5InnerBody, shade_step3InnerBody] at hyi₀'
          have hyΩ : y ∈ F.pipelineSet hδ hdisc (ρ : ℝ) hρreal := hyi₀'.1.1.2
          have hySel : y ∈ step5Selection T₅' ρ := hyi₀'.2
          let J := MultiplicityFamily.dyadicLevel t'
            (fiberMultiplicity F {i ∈ u | F.parent i ∈ t'}) k y
          refine ⟨J, ?_, ?_, ?_⟩
          · intro q hq
            have hqt' : q ∈ t' := (Finset.mem_filter.mp hq).1
            have hqG₅ : q ∈ G₅.outerSet := by
              simpa [G₅, FactorFamily.pipelineFamily, t'] using hqt'
            have hqactive : q ∈ activeOuterSet G₅ := by
              apply Finset.mem_filter.mpr
              refine ⟨hqG₅, ?_⟩
              intro hzero
              have hyfiber : y ∈ iUnionShade (G₅.fiber q) G₅.innerBody := by
                have hpos : 0 < fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} q y :=
                  lt_of_lt_of_le (pow_pos (by omega) k) (Finset.mem_filter.mp hq).2.1
                change 0 < ({i ∈ {i ∈ {i ∈ u | F.parent i ∈ t'} | F.parent i = q} |
                  y ∈ (F.innerBody i).shade}).card at hpos
                obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
                have hi' := Finset.mem_filter.mp hi
                have hib := Finset.mem_filter.mp hi'.1
                have hip := hib.2
                refine Set.mem_iUnion₂.mpr ⟨i, ?_, ?_⟩
                · exact Finset.mem_filter.mpr ⟨by
                    simpa [G₅, FactorFamily.pipelineFamily, FactorFamily.pipelineInnerSet,
                      u, t'] using hib.1, by
                    simp [G₅, FactorFamily.pipelineFamily, hip]⟩
                · change y ∈ (step5InnerBody F u t'
                    (F.pipelineSet hδ hdisc (ρ : ℝ) hρreal) hΩ k T₅' ρ i).shade
                  rw [shade_step5InnerBody, shade_step3InnerBody]
                  refine ⟨⟨⟨hi'.2, hyΩ⟩, ?_⟩, hySel⟩
                  simpa [step3DyadicSet, hip] using (Finset.mem_filter.mp hq).2
              apply hyZ
              exact Set.mem_iUnion₂.mpr ⟨q,
                Finset.mem_filter.mpr ⟨hqG₅, fun ha ↦
                  (Finset.mem_filter.mp ha).2 hzero⟩, hyfiber⟩
            simpa [G, completedPipelineFamily] using hqactive
          · have hb := F.bounds_of_mem_pipelineSet hδ hdisc (ρ : ℝ) hρreal hyΩ
            simpa [J, l, k, t', u, FactorFamily.pipelineInnerSet] using hb.2.2.1
          · intro q hq
            have hqt' : q ∈ t' := (Finset.mem_filter.mp hq).1
            have hpos : 0 < fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} q y :=
              lt_of_lt_of_le (pow_pos (by omega) k) (Finset.mem_filter.mp hq).2.1
            change 0 < ({i ∈ {i ∈ {i ∈ u | F.parent i ∈ t'} | F.parent i = q} |
              y ∈ (F.innerBody i).shade}).card at hpos
            obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
            have hi' := Finset.mem_filter.mp hi
            have hib := Finset.mem_filter.mp hi'.1
            have hiu := (Finset.mem_filter.mp hib.1).1
            have hip := hib.2
            have hiF : i ∈ F.innerSet := F.innerSet_step0_subset hiu
            have hyK : y ∈ (K q).carrier := by
              change y ∈ K q
              simpa [hip] using hK i hiF ((F.innerBody i).shade_subset hi'.2)
            have hycapsule : y ∈ Metric.cthickening ((c : ℝ) * (ρ : ℝ))
                (segment ℝ (AffineMap.homothety (Tρ q).center (c : ℝ) (Tρ q).x)
                  (AffineMap.homothety (Tρ q).center (c : ℝ) (Tρ q).y)) := by
              rw [← Kakeya.Tube.dilate_carrier_eq_cthickening (Tρ q) (by positivity)]
              exact hyK
            obtain ⟨p, hp⟩ := Kakeya.exists_ball_subset_cthickening_inter_ball
              isCompact_segment hρreal (by
                have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
                nlinarith [mul_pos (lt_of_lt_of_le zero_lt_one hcR) hρreal]) hycapsule
            refine ⟨p, ?_⟩
            intro w hw
            have hwK : w ∈ (K q).carrier := by
              change w ∈ (Kakeya.Tube.dilate (Tρ q) (c : ℝ)).carrier
              rw [Kakeya.Tube.dilate_carrier_eq_cthickening (Tρ q) (by positivity)]
              exact (hp hw).1
            have hqactive : q ∈ activeOuterSet G₅ := by
              have hqG : q ∈ G.outerSet := by
                apply (show J ⊆ G.outerSet from ?_) hq
                intro q' hq'
                have hqt'' : q' ∈ t' := (Finset.mem_filter.mp hq').1
                have hqG₅ : q' ∈ G₅.outerSet := by
                  simpa [G₅, FactorFamily.pipelineFamily, t'] using hqt''
                apply Finset.mem_filter.mpr
                refine ⟨hqG₅, ?_⟩
                intro hzfiber
                have hyfiber : y ∈ iUnionShade (G₅.fiber q') G₅.innerBody := by
                  have hp' := (Finset.mem_filter.mp hq').2
                  have hpos' : 0 < fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} q' y :=
                    lt_of_lt_of_le (pow_pos (by omega) k) hp'.1
                  change 0 < ({a ∈ {a ∈ {a ∈ u | F.parent a ∈ t'} | F.parent a = q'} |
                    y ∈ (F.innerBody a).shade}).card at hpos'
                  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos'
                  have ha' := Finset.mem_filter.mp ha
                  have hab := Finset.mem_filter.mp ha'.1
                  have hap := hab.2
                  refine Set.mem_iUnion₂.mpr ⟨a, ?_, ?_⟩
                  · exact Finset.mem_filter.mpr ⟨by
                      simpa [G₅, FactorFamily.pipelineFamily,
                        FactorFamily.pipelineInnerSet, u, t'] using hab.1, by
                      simp [G₅, FactorFamily.pipelineFamily, hap]⟩
                  · change y ∈ (step5InnerBody F u t'
                      (F.pipelineSet hδ hdisc (ρ : ℝ) hρreal) hΩ k T₅' ρ a).shade
                    rw [shade_step5InnerBody, shade_step3InnerBody]
                    refine ⟨⟨⟨ha'.2, hyΩ⟩, ?_⟩, hySel⟩
                    simpa [step3DyadicSet, hap] using hp'
                exact hyZ (Set.mem_iUnion₂.mpr ⟨q',
                  Finset.mem_filter.mpr ⟨hqG₅, fun ha ↦
                    (Finset.mem_filter.mp ha).2 hzfiber⟩, hyfiber⟩)
              simpa [G, completedPipelineFamily] using hqG
            have hyfiber : y ∈ iUnionShade (G₅.fiber q) G₅.innerBody := by
              have hqG₅ : q ∈ G₅.outerSet := by
                simpa [G₅, FactorFamily.pipelineFamily, t'] using hqt'
              have hiG₅ : i ∈ G₅.innerSet := by
                simpa [G₅, FactorFamily.pipelineFamily, FactorFamily.pipelineInnerSet,
                  u, t'] using hib.1
              refine Set.mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hiG₅, by
                simp [G₅, FactorFamily.pipelineFamily, hip]⟩, ?_⟩
              change y ∈ (step5InnerBody F u t'
                (F.pipelineSet hδ hdisc (ρ : ℝ) hρreal) hΩ k T₅' ρ i).shade
              rw [shade_step5InnerBody, shade_step3InnerBody]
              refine ⟨⟨⟨hi'.2, hyΩ⟩, ?_⟩, hySel⟩
              simpa [step3DyadicSet, hip] using (Finset.mem_filter.mp hq).2
            have hwthick : w ∈ Metric.cthickening (2 * (ρ : ℝ))
                (iUnionShade {i ∈ F.innerSet |
                  F.parent i ∈ activeOuterSet G₅ ∧ F.parent i = q}
                  (completedInnerBody F G₅)) := by
              apply Metric.mem_cthickening_of_dist_le w y _ _
              · rw [iUnionShade_completed_fiber F G₅ hsub₅ hparent₅ hqactive]
                exact hyfiber
              · exact le_trans (le_of_lt (Metric.mem_ball.mp (hp hw).2)) (by linarith)
            constructor
            · change w ∈ (K q).carrier ∩ Metric.cthickening (2 * (ρ : ℝ))
                (iUnionShade {i ∈ F.innerSet |
                  F.parent i ∈ activeOuterSet G₅ ∧ F.parent i = q}
                  (completedInnerBody F G₅))
              exact ⟨hwK, hwthick⟩
            · apply Metric.mem_ball.mpr
              calc
                dist w z ≤ dist w y + dist y z := dist_triangle _ _ _
                _ < (ρ : ℝ) + (ρ : ℝ) := add_lt_add_of_lt_of_le
                  (Metric.mem_ball.mp (hp hw).2) (Metric.mem_closedBall.mp hyA.2)
                _ = 2 * (ρ : ℝ) := by ring
        have hlpos : 0 < 2 ^ l := pow_pos (by omega) l
        have houterLower : (2 ^ l : ENNReal) ≤
            (rhoTubesOuterMultiplicityLoss n : ENNReal) *
              multiplicity G.outerSet G.outerBody := by
          simpa [n] using outerMultiplicity_lower_of_local_balls G.outerSet G.outerBody
            T₅' ρ (2 ^ l) hρpos hlpos hT₅'ne hT₅'sep hcoverW hlocal
        have hglobal : multiplicity G₅.innerSet G₅.innerBody ≤
            (4 * (2 ^ k * 2 ^ l) : ℕ) := by
          apply multiplicity_le_of_pointwiseMultiplicity_le
          intro x hx
          exact_mod_cast (F.pipelineFamily_multiplicity hδ hdisc (ρ : ℝ) hρreal
            hΩ T₅' ρ hx).2.le
        have hjactive : j ∈ activeOuterSet G₅ := by
          simpa [G, completedPipelineFamily] using hj
        have hfiberUnion0 : volume (iUnionShade (G₅.fiber j) G₅.innerBody) ≠ 0 :=
          (Finset.mem_filter.mp hjactive).2
        have hfiberLower₅ : (2 ^ k : ENNReal) ≤
            multiplicity (G₅.fiber j) G₅.innerBody := by
          apply le_multiplicity_of_le_pointwiseMultiplicity _ _ hfiberUnion0
          intro x hx
          exact_mod_cast (F.pipelineFamily_fiber_multiplicity hδ hdisc (ρ : ℝ)
            hρreal hΩ T₅' ρ hx).1
        have hfiberEq : multiplicity (G₅.fiber j) G₅.innerBody =
            multiplicity (G.fiber j) G.innerBody := by
          rw [multiplicity_eq_div, multiplicity_eq_div]
          have hGfiber : G.fiber j =
              {i ∈ F.innerSet | F.parent i ∈ activeOuterSet G₅ ∧ F.parent i = j} := by
            ext i
            simp [G, completedPipelineFamily, ShadedFactorFamily.fiber, and_assoc]
          rw [hGfiber]
          have hGinner : G.innerBody = completedInnerBody F G₅ := rfl
          rw [hGinner]
          rw [sum_volume_completed_fiber F G₅ hsub₅ hparent₅ hjactive]
          congr 1
          exact congrArg volume
            (iUnionShade_completed_fiber F G₅ hsub₅ hparent₅ hjactive).symm
        have hfiberLower : (2 ^ k : ENNReal) ≤ multiplicity (G.fiber j) G.innerBody :=
          hfiberEq ▸ hfiberLower₅
        have hNpos' : 0 < N := by
          have hfiberNe : (G₅.fiber j).Nonempty := by
            by_contra he
            have he' : G₅.fiber j = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
            exact hfiberUnion0 (by simp [he', iUnionShade])
          obtain ⟨i, hi⟩ := hfiberNe
          have hiF : i ∈ F.innerSet := hsub₅ (Finset.mem_filter.mp hi).1
          simpa [N] using F.innerSet.card_pos.mpr ⟨i, hiF⟩
        have hN1' : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hNpos'.ne'
        have hApos' : 0 < Kakeya.factoringStep1AtScaleConstant n N δ := by
          have hl := Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale_nonneg
            n hN1' hδ hδ1
          rw [Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale n hN1' hδ] at hl
          rw [Kakeya.factoringStep1AtScaleConstant_eq n hN1' hδ]
          apply mul_pos (by norm_num)
          rw [Real.toNNReal_pos]
          linarith
        have hBpos' : 0 < (Kakeya.factoringStep2Step3Constant N : NNReal) := by
          rw [Kakeya.factoringStep2Step3Constant_eq]
          positivity
        have hDpos' : 0 < ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
            (step5PackingRatio n N δ) := by
          unfold ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant
          have hOpos : (0 : NNReal) < Kakeya.factoringStep5OverlapConstant n := by
            unfold Kakeya.factoringStep5OverlapConstant
            positivity
          have hFpos : 0 < Kakeya.factoringStep1FiberPigeonholeConstant 1
              (step5PackingRatio n N δ) := lt_of_lt_of_le zero_lt_one
            (Kakeya.one_le_factoringStep1FiberPigeonholeConstant hratio1)
          exact mul_pos (mul_pos (by norm_num) hOpos) (mul_pos (by norm_num) hFpos)
        have hP0' : Kakeya.factoringStep1AtScaleConstant n N δ *
            (Kakeya.factoringStep2Step3Constant N : NNReal) *
            ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
              (step5PackingRatio n N δ) ≠ 0 :=
          (mul_pos (mul_pos hApos' hBpos') hDpos').ne'
        have hrefMu : multiplicity F.innerSet F.innerBody ≤
            ((Kakeya.factoringPipelineSelfRefinementConstant n N δ
              (step5PackingRatio n N δ) : NNReal) : ENNReal)⁻¹ *
              multiplicity G₅.innerSet G₅.innerBody := by
          apply multiplicity_le_of_isCRefinement
          · rw [pipelineRefinementConstant_eq_inv]
            exact inv_ne_zero hP0'
          · exact hrefG₅
        have hPinv : ((Kakeya.factoringPipelineSelfRefinementConstant n N δ
              (step5PackingRatio n N δ) : NNReal) : ENNReal)⁻¹ =
            (Kakeya.factoringStep1AtScaleConstant n N δ *
              (Kakeya.factoringStep2Step3Constant N : NNReal) *
              ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
                (step5PackingRatio n N δ) : NNReal) := by
          rw [pipelineRefinementConstant_eq_inv]
          rw [ENNReal.coe_inv hP0']
          rw [inv_inv]
        rw [hPinv] at hrefMu
        calc
          multiplicity F.innerSet F.innerBody ≤
              (Kakeya.factoringStep1AtScaleConstant n N δ *
                (Kakeya.factoringStep2Step3Constant N : NNReal) *
                ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
                  (step5PackingRatio n N δ) : NNReal) *
                multiplicity G₅.innerSet G₅.innerBody := hrefMu
          _ ≤ (Kakeya.factoringStep1AtScaleConstant n N δ *
                (Kakeya.factoringStep2Step3Constant N : NNReal) *
                ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
                  (step5PackingRatio n N δ) : NNReal) *
              (4 * ((2 ^ k : ENNReal) * (2 ^ l : ENNReal))) := by
            gcongr
            simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hglobal
          _ ≤ (4 * (Kakeya.factoringStep1AtScaleConstant n N δ *
                (Kakeya.factoringStep2Step3Constant N : NNReal) *
                ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
                  (step5PackingRatio n N δ)) *
                rhoTubesOuterMultiplicityLoss n : NNReal) *
              multiplicity G.outerSet G.outerBody *
              multiplicity (G.fiber j) G.innerBody := by
            calc
              _ = (4 * (Kakeya.factoringStep1AtScaleConstant n N δ *
                    (Kakeya.factoringStep2Step3Constant N : NNReal) *
                    ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
                      (step5PackingRatio n N δ)) : NNReal) *
                    (2 ^ l : ENNReal) * (2 ^ k : ENNReal) := by
                push_cast
                ring
              _ ≤ (4 * (Kakeya.factoringStep1AtScaleConstant n N δ *
                    (Kakeya.factoringStep2Step3Constant N : NNReal) *
                    ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
                      (step5PackingRatio n N δ)) : NNReal) *
                    ((rhoTubesOuterMultiplicityLoss n : ENNReal) *
                      multiplicity G.outerSet G.outerBody) *
                    multiplicity (G.fiber j) G.innerBody := by gcongr
              _ = _ := by
                push_cast
                ring
          _ ≤ (shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c : NNReal) *
              multiplicity G.outerSet G.outerBody *
              multiplicity (G.fiber j) G.innerBody := by
            gcongr
            exact_mod_cast four_mul_pipeline_outerLoss_le_C n N δ c hc
      · intro i hi
        exact G.shade_subset_parent i hi
      · intro x hx
        let U : Set E := iUnionShade G.innerSet G.innerBody
        let W : Set E := iUnionShade G.outerSet G.outerBody
        have hUmeas : MeasurableSet U := measurableSet_iUnion_shade G.innerSet G.innerBody
        have hcoverW : W ⊆ ⋃ z ∈ T₅', Metric.closedBall z (4 * (ρ : ℝ)) := by
          intro y hy
          obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hy
          change y ∈ (K j).carrier ∩ Metric.cthickening (2 * (ρ : ℝ))
            (iUnionShade {i ∈ F.innerSet |
              F.parent i ∈ activeOuterSet G₅ ∧ F.parent i = j}
              (completedInnerBody F G₅)) at hyj
          have hthick := Metric.cthickening_subset_iUnion_closedBall_of_lt
            (iUnionShade {i ∈ F.innerSet |
              F.parent i ∈ activeOuterSet G₅ ∧ F.parent i = j}
              (completedInnerBody F G₅))
            (show (0 : ℝ) < 3 * (ρ : ℝ) by positivity)
            (show 2 * (ρ : ℝ) < 3 * (ρ : ℝ) by linarith) hyj.2
          obtain ⟨z, hzfib, hyz⟩ := Set.mem_iUnion₂.mp hthick
          have hjactive : j ∈ activeOuterSet G₅ := by simpa [G, completedPipelineFamily] using hj
          have hz₅ : z ∈ iUnionShade (G₅.fiber j) G₅.innerBody := by
            rw [← iUnionShade_completed_fiber F G₅ hsub₅ hparent₅ hjactive]
            exact hzfib
          obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp hz₅
          have hzi' : z ∈ (step5InnerBody F F.step0.innerSet
              (F.step1 hδ hdisc).outerSet
              (F.pipelineSet hδ hdisc (ρ : ℝ) hρreal) hΩ
              (F.pipelineExponent hδ hdisc (ρ : ℝ) hρreal) T₅' ρ i).shade := by
            simpa [G₅, FactorFamily.pipelineFamily] using hzi
          rw [shade_step5InnerBody] at hzi'
          obtain ⟨q, hq, hzq⟩ := Set.mem_iUnion₂.mp hzi'.2
          refine Set.mem_iUnion₂.mpr ⟨q, hq, Metric.mem_closedBall.mpr ?_⟩
          have hyz' := Metric.mem_closedBall.mp hyz
          have hzq' := Metric.mem_closedBall.mp hzq
          calc
            dist y q ≤ dist y z + dist z q := dist_triangle y z q
            _ ≤ 3 * (ρ : ℝ) + (ρ : ℝ) := by
              gcongr
            _ = 4 * (ρ : ℝ) := by ring
        have hlocal : ∀ y, ∀ z ∈ T₅',
            volume (U ∩ Metric.ball y (ρ : ℝ)) ≤
              2 * Kakeya.factoringStep5OverlapConstant n *
                volume (U ∩ Metric.closedBall z (ρ : ℝ)) := by
          intro y z hz
          rw [show volume (U ∩ Metric.ball y (ρ : ℝ)) =
              volume (iUnionShade G₅.innerSet G₅.innerBody ∩ Metric.ball y (ρ : ℝ)) by
                simpa [U, G, completedPipelineFamily] using
                  volume_iUnionShade_completed_inter_eq F G₅ hsub₅ hparent₅
                    (Metric.ball y (ρ : ℝ)),
            show volume (U ∩ Metric.closedBall z (ρ : ℝ)) =
              volume (iUnionShade G₅.innerSet G₅.innerBody ∩ Metric.closedBall z (ρ : ℝ)) by
                simpa [U, G, completedPipelineFamily] using
                  volume_iUnionShade_completed_inter_eq F G₅ hsub₅ hparent₅
                    (Metric.closedBall z (ρ : ℝ))]
          simpa only [G₅, n, FactorFamily.pipelineInnerSet, FactorFamily.pipelineFamily,
            step5ShadedFactorFamily_innerSet, step5ShadedFactorFamily_innerBody] using
            volume_iUnionShade_step5_inter_ball_le F F.step0.innerSet
            (F.step1 hδ hdisc).outerSet (F.pipelineSet hδ hdisc (ρ : ℝ) hρreal) hΩ
            (F.pipelineExponent hδ hdisc (ρ : ℝ) hρreal) hρpos hT₅'sep hballcomp y hz
        have hb := ball_estimate_of_cover U W T₅' ρ x hρpos hUmeas hcoverW
          (fun y ↦ by
            rw [Finset.filter_congr_decidable]
            refine (Finset.card_le_card ?_).trans (hT₅overlap y)
            intro z hz
            exact Finset.mem_filter.mpr ⟨hT₅'T₅ (Finset.mem_filter.mp hz).1,
              (Finset.mem_filter.mp hz).2⟩) hlocal
        have hballC : rhoTubesBallLoss n ≤
            shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c := by
          rw [shadingMultiplicityEstimateForRhoTubesDilate.C]
          exact le_max_of_le_right (le_max_right _ _)
        have hC0 : (shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c : ENNReal) ≠ 0 :=
          ENNReal.coe_ne_zero.mpr (ne_of_gt (zero_lt_one.trans_le
            (shadingMultiplicityEstimateForRhoTubesDilate.one_le_C n N δ c)))
        calc
          (shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c : ENNReal)⁻¹ *
                volume W * (volume (U ∩ Metric.ball x (ρ : ℝ)) /
                  volume (Metric.ball x (ρ : ℝ)))
              = (shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c : ENNReal)⁻¹ *
                (volume W * (volume (U ∩ Metric.ball x (ρ : ℝ)) /
                  volume (Metric.ball x (ρ : ℝ)))) := by ring
          _ ≤ (shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c : ENNReal)⁻¹ *
              ((rhoTubesBallLoss n : ENNReal) * volume U) := by gcongr
          _ ≤ (shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c : ENNReal)⁻¹ *
              ((shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c : ENNReal) * volume U) := by
                gcongr
          _ = volume U := ENNReal.inv_mul_cancel_left hC0 ENNReal.coe_ne_top
      · -- the exposed `2ρ`-thickness of the outer shading (GWZ Definition 5.7)
        intro j hj i hi hij
        have hjactive : j ∈ activeOuterSet G₅ := by simpa [G, completedPipelineFamily] using hj
        have hiF : i ∈ F.innerSet := (Finset.mem_filter.mp hi).1
        have hip : F.parent i = j := hij
        by_cases hi₅ : i ∈ G₅.innerSet
        · have hbody : G.innerBody i = G₅.innerBody i := by
            simp [G, completedPipelineFamily, completedInnerBody, hi₅]
          rw [hbody]
          exact inter_cthickening_shade_subset_rhoCompletedOuterBody F G₅ K ρ hjactive hi₅ hiF hip
        · have hempty : (G.innerBody i).shade = ∅ := by
            simp [G, completedPipelineFamily, completedInnerBody, hi₅]
          rw [hempty, Metric.cthickening_empty, Set.inter_empty]
          exact Set.empty_subset _

end RhoTubesDilate

end ShadedBody
