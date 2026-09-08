/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Asymptotics
public import Kakeya.Factoring.SelectScale

/-!
# Family-independent envelopes for the corrected Proposition 5.1 losses

The fixed-scale core records exact dyadic losses.  This file groups those losses into one
positive large coefficient and supplies the algebraic identities needed to absorb it at a
master scale.  The coefficient depends on a family only through its cardinality, the explicit
outer/inner volume-ratio exponent, and the selected scale.
-/

@[expose] public section

open Filter Topology
open scoped ENNReal NNReal

namespace ShadedBody

/-- Every fixed finite coefficient at least one is eventually dominated by an arbitrarily
small negative power of the master scale. -/
theorem eventually_const_le_coe_rpow_neg {C : ENNReal} (hC1 : 1 ≤ C) (hCtop : C ≠ ⊤)
    {e : ℝ} (he : 0 < e) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, 0 < δ ∧ δ ≤ 1 ∧ C ≤ (δ : ENNReal) ^ (-e) := by
  have hCpos : (0 : ENNReal) < C := zero_lt_one.trans_le hC1
  have htop : C ^ (-1 / e) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg' hCpos hCtop
  have hδ : (0 : NNReal) < min 1 (C ^ (-1 / e)).toNNReal :=
    lt_min zero_lt_one (by
      rw [← ENNReal.coe_pos, ENNReal.coe_toNNReal htop]
      exact ENNReal.rpow_pos hCpos hCtop)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ)]
    with δ (hδ0 : 0 < δ) hδlt
  have hsmall : (δ : ENNReal) ≤ C ^ (-1 / e) := by
    calc
      (δ : ENNReal) ≤ ((C ^ (-1 / e)).toNNReal : ENNReal) :=
        ENNReal.coe_le_coe.mpr (hδlt.le.trans (min_le_right _ _))
      _ = C ^ (-1 / e) := ENNReal.coe_toNNReal htop
  have hp := ENNReal.rpow_le_rpow hsmall he.le
  rw [← ENNReal.rpow_mul, div_mul_cancel₀ _ he.ne', ENNReal.rpow_neg_one] at hp
  rw [ENNReal.rpow_neg]
  exact ⟨hδ0, hδlt.le.trans (min_le_left _ _), ENNReal.le_inv_iff_le_inv.mp hp⟩

/-- Collect the seven fixed negative-power losses that occur in the outer Frostman transport. -/
theorem outerFrostman_loss_bound
    {δ fixed CF density scale pipeline : ENNReal} {η e : ℝ}
    (hδ0 : δ ≠ 0) (hδtop : δ ≠ ⊤)
    (hfixed : fixed ≤ δ ^ (-e))
    (hdensity : density ≤ δ ^ (-e))
    (hscale : scale ≤ δ ^ (-e))
    (hpipeline : pipeline ≤ δ ^ (-e)) :
    fixed * CF * density ^ 3 * scale ^ 2 * pipeline * δ ^ (-3 * η) ≤
      δ ^ (-(3 * η + 7 * e)) * CF := by
  have hp3 : (δ ^ (-e)) ^ (3 : ℕ) = δ ^ (-3 * e) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    ring
  have hp2 : (δ ^ (-e)) ^ (2 : ℕ) = δ ^ (-2 * e) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    ring
  calc
    fixed * CF * density ^ 3 * scale ^ 2 * pipeline * δ ^ (-3 * η) ≤
        δ ^ (-e) * CF * (δ ^ (-e)) ^ 3 * (δ ^ (-e)) ^ 2 *
          δ ^ (-e) * δ ^ (-3 * η) := by gcongr
    _ = CF * (δ ^ (-e) * δ ^ (-3 * e) * δ ^ (-2 * e) *
          δ ^ (-e) * δ ^ (-3 * η)) := by rw [hp3, hp2]; ring
    _ = CF * δ ^ (-(3 * η + 7 * e)) := by
      repeat' rw [← ENNReal.rpow_add _ _ hδ0 hδtop]
      congr 1
      ring
    _ = δ ^ (-(3 * η + 7 * e)) * CF := mul_comm _ _

/-- The dyadic selection of one outer scale between `δ` and a fixed upper endpoint has an
arbitrarily small power envelope. -/
theorem eventually_outerScaleSelectionConstant_le_rpow_neg
    (B : NNReal) (hB1 : 1 ≤ B) {e : ℝ} (he : 0 < e) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      (outerScaleSelectionConstant δ B : ENNReal) ≤ (δ : ENNReal) ^ (-e) := by
  let c : ℝ := 1 + Real.logb 2 (B : ℝ)
  have hc1 : 1 ≤ c := by
    dsimp [c]
    exact le_add_of_nonneg_right (Real.logb_nonneg (by norm_num) (by exact_mod_cast hB1))
  let C : ENNReal := Real.toNNReal c
  have hC1 : 1 ≤ C := by
    change ((1 : NNReal) : ENNReal) ≤ ((Real.toNNReal c : NNReal) : ENNReal)
    apply ENNReal.coe_le_coe.mpr
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by linarith)]
    exact hc1
  have hCtop : C ≠ ⊤ := by simp [C]
  have he2 : 0 < e / 2 := by positivity
  filter_upwards [eventually_const_le_coe_rpow_neg hC1 hCtop he2,
    ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg he2 1]
      with δ hconst hlog
  have hδ0 : 0 < (δ : ℝ) := by exact_mod_cast hconst.1
  have hδ1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hconst.2.1
  have hL1 : 1 ≤ 1 + Real.logb 2 (1 / (δ : ℝ)) := by
    exact le_add_of_nonneg_right (Real.logb_nonneg (by norm_num) ((one_le_div hδ0).2 hδ1))
  have hreal : 1 + Real.logb 2 ((B : ℝ) / δ) ≤
      c * (1 + Real.logb 2 (1 / (δ : ℝ))) := by
    rw [Real.logb_div (by positivity : (B : ℝ) ≠ 0) hδ0.ne',
      Real.logb_div one_ne_zero hδ0.ne', Real.logb_one, zero_sub]
    have hx : 0 ≤ Real.logb 2 (B : ℝ) :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast hB1)
    have hy : 0 ≤ -Real.logb 2 (δ : ℝ) :=
      neg_nonneg.mpr (Real.logb_nonpos (by norm_num) hδ0.le hδ1)
    dsimp [c]
    nlinarith [mul_nonneg hx hy]
  have hsel : (outerScaleSelectionConstant δ B : ENNReal) ≤
      C * ENNReal.ofReal (1 + Real.logb 2 (1 / (δ : ℝ))) := by
    rw [coe_outerScaleSelectionConstant]
    calc
      ENNReal.ofReal (1 + Real.logb 2 ((B : ℝ) / δ)) ≤
          ENNReal.ofReal (c * (1 + Real.logb 2 (1 / (δ : ℝ)))) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = C * ENNReal.ofReal (1 + Real.logb 2 (1 / (δ : ℝ))) := by
        rw [ENNReal.ofReal_mul (by linarith : 0 ≤ c)]
        change ENNReal.ofReal c * _ = ((Real.toNNReal c : NNReal) : ENNReal) * _
        rw [ENNReal.ofNNReal_toNNReal]
  calc
    (outerScaleSelectionConstant δ B : ENNReal) ≤
        C * ENNReal.ofReal (1 + Real.logb 2 (1 / (δ : ℝ))) := hsel
    _ ≤ (δ : ENNReal) ^ (-(e / 2)) * (δ : ENNReal) ^ (-(e / 2)) := by
      gcongr
      · exact hconst.2.2
      · simpa using hlog
    _ = (δ : ENNReal) ^ (-e) := by
      rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hconst.1.ne') ENNReal.coe_ne_top]
      congr 1
      ring

/-- A density pigeonhole over a polynomially bounded family and a subpolynomial dyadic
volume exponent has a subpolynomial loss.  The assumptions are kept in the form used by the
flat-prism adapter. -/
theorem eventually_outerDensitySelectionConstant_le_rpow_neg
    (m : ℕ) {e : ℝ} (he : 0 < e) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ card N : ℕ, 0 < card →
        (card : ℝ) ≤ (δ : ℝ) ^ (-(m : ℝ)) →
        ((N + 1 : ℕ) : ENNReal) ≤ (δ : ENNReal) ^ (-(e / 4)) →
        (outerDensitySelectionConstant card N : ENNReal) ≤
          (δ : ENNReal) ^ (-e) := by
  let A : ENNReal := max 1 ((m + 2 : ℕ) : ENNReal)
  have hA1 : 1 ≤ A := le_max_left _ _
  have hAtop : A ≠ ⊤ := by simp [A]
  have he4 : 0 < e / 4 := by positivity
  filter_upwards [eventually_const_le_coe_rpow_neg hA1 hAtop he4,
    ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg he4 1]
      with δ hA hlog
  intro card N hcard hcardδ hN
  have hδ0 : 0 < (δ : ℝ) := by exact_mod_cast hA.1
  have hδ1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hA.2.1
  have hcardR : 0 < (card : ℝ) := by exact_mod_cast hcard
  have hlogCard : Real.logb 2 (card : ℝ) ≤
      (m : ℝ) * Real.logb 2 (1 / (δ : ℝ)) := by
    calc
      Real.logb 2 (card : ℝ) ≤ Real.logb 2 ((δ : ℝ) ^ (-(m : ℝ))) :=
        Real.logb_le_logb_of_le (by norm_num) hcardR hcardδ
      _ = (-(m : ℝ)) * Real.logb 2 (δ : ℝ) := by
        rw [Real.logb_rpow_eq_mul_logb_of_pos hδ0]
      _ = (m : ℝ) * Real.logb 2 (1 / (δ : ℝ)) := by
        rw [one_div, Real.logb_inv]
        ring
  have harg : 1 + Real.logb 2
      ((card : ℝ) / ((((2 : NNReal) ^ N)⁻¹ : NNReal) : ℝ)) =
      1 + Real.logb 2 (card : ℝ) + N := by
    rw [Real.logb_div hcardR.ne' (by positivity :
      ((((2 : NNReal) ^ N)⁻¹ : NNReal) : ℝ) ≠ 0),
      show (((((2 : NNReal) ^ N)⁻¹ : NNReal) : ℝ)) = ((2 : ℝ) ^ N)⁻¹ by simp,
      Real.logb_inv, Real.logb_pow]
    norm_num
    ring
  have hL0 : 0 ≤ Real.logb 2 (1 / (δ : ℝ)) :=
    Real.logb_nonneg (by norm_num) ((one_le_div hδ0).2 hδ1)
  have hreal : 1 + Real.logb 2
      ((card : ℝ) / ((((2 : NNReal) ^ N)⁻¹ : NNReal) : ℝ)) ≤
      (m + 2 : ℕ) * (1 + Real.logb 2 (1 / (δ : ℝ))) + (N + 1) := by
    rw [harg]
    norm_num only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    nlinarith
  have hsel : (outerDensitySelectionConstant card N : ENNReal) ≤
      ((m + 2 : ℕ) : ENNReal) *
          ENNReal.ofReal (1 + Real.logb 2 (1 / (δ : ℝ))) + (N + 1 : ℕ) := by
    rw [outerDensitySelectionConstant, ENNReal.ofNNReal_toNNReal]
    calc
      ENNReal.ofReal (1 + Real.logb 2
          ((card : ℝ) / ((((2 : NNReal) ^ N)⁻¹ : NNReal) : ℝ))) ≤
          ENNReal.ofReal (((m + 2 : ℕ) : ℝ) *
            (1 + Real.logb 2 (1 / (δ : ℝ))) + ((N + 1 : ℕ) : ℝ)) :=
        ENNReal.ofReal_le_ofReal (by simpa using hreal)
      _ = ((m + 2 : ℕ) : ENNReal) *
          ENNReal.ofReal (1 + Real.logb 2 (1 / (δ : ℝ))) + (N + 1 : ℕ) := by
        rw [ENNReal.ofReal_add (by positivity : 0 ≤ ((m + 2 : ℕ) : ℝ) *
          (1 + Real.logb 2 (1 / (δ : ℝ)))), ENNReal.ofReal_mul (by positivity :
            0 ≤ ((m + 2 : ℕ) : ℝ)), ENNReal.ofReal_natCast,
          ENNReal.ofReal_natCast]
        positivity
  have hδpow1 : (1 : ENNReal) ≤ (δ : ENNReal) ^ (-(e / 4)) := by
    rw [ENNReal.rpow_neg]
    exact ENNReal.one_le_inv.mpr
      (ENNReal.rpow_le_one (by exact_mod_cast hA.2.1) he4.le)
  have hsum : (outerDensitySelectionConstant card N : ENNReal) ≤
      A * ((δ : ENNReal) ^ (-(e / 4)) + (δ : ENNReal) ^ (-(e / 4))) := by
    calc
      _ ≤ ((m + 2 : ℕ) : ENNReal) *
          ENNReal.ofReal (1 + Real.logb 2 (1 / (δ : ℝ))) + (N + 1 : ℕ) := hsel
      _ ≤ A * (δ : ENNReal) ^ (-(e / 4)) + (δ : ENNReal) ^ (-(e / 4)) := by
        exact add_le_add
          (mul_le_mul (le_max_right _ _)
            (by simpa using hlog) (by positivity) (by positivity)) hN
      _ ≤ A * ((δ : ENNReal) ^ (-(e / 4)) +
          (δ : ENNReal) ^ (-(e / 4))) := by
        calc
          A * (δ : ENNReal) ^ (-(e / 4)) + (δ : ENNReal) ^ (-(e / 4)) ≤
              A * (δ : ENNReal) ^ (-(e / 4)) +
                A * (δ : ENNReal) ^ (-(e / 4)) := by
            gcongr
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hA1
                (show (0 : ENNReal) ≤ (δ : ENNReal) ^ (-(e / 4)) from bot_le)
          _ = _ := by ring
  calc
    (outerDensitySelectionConstant card N : ENNReal) ≤
        A * ((δ : ENNReal) ^ (-(e / 4)) + (δ : ENNReal) ^ (-(e / 4))) := hsum
    _ ≤ (δ : ENNReal) ^ (-(e / 4)) *
        (2 * (δ : ENNReal) ^ (-(e / 4))) := by
      calc
        A * ((δ : ENNReal) ^ (-(e / 4)) + (δ : ENNReal) ^ (-(e / 4))) =
            A * (2 * (δ : ENNReal) ^ (-(e / 4))) := by ring
        _ ≤ (δ : ENNReal) ^ (-(e / 4)) *
            (2 * (δ : ENNReal) ^ (-(e / 4))) := by
          gcongr
          exact hA.2.2
    _ ≤ (δ : ENNReal) ^ (-(e / 4)) *
        ((δ : ENNReal) ^ (-(e / 4)) * (δ : ENNReal) ^ (-(e / 4))) := by
      gcongr
      calc
        (2 : ENNReal) ≤ A := by
          exact (show (2 : ENNReal) ≤ (m + 2 : ℕ) by exact_mod_cast Nat.le_add_left 2 m) |>.trans
            (le_max_right _ _)
        _ ≤ (δ : ENNReal) ^ (-(e / 4)) := hA.2.2
    _ = (δ : ENNReal) ^ (-(3 * e / 4)) := by
      repeat' rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hA.1.ne') ENNReal.coe_ne_top]
      congr 1
      ring
    _ ≤ (δ : ENNReal) ^ (-e) := by
      exact ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hA.2.1) (by linarith)

/-- The reciprocal of the uniform retained-mass coefficient in the fixed-scale core. -/
noncomputable def factoringCoreAtScaleUniformPipelineLoss
    (n M N : ℕ) (w : NNReal) : NNReal :=
  FactorFamily.weightedStep1AtScaleConstant n M N *
    (Kakeya.factoringStep2Step3Constant M : NNReal) *
      Kakeya.factoringStep5SelfPigeonholeConstant n
        (factoringCoreAtScaleCoverCardBound n w)

/-- The uniform refinement coefficient is exactly the reciprocal pipeline loss. -/
theorem factoringCoreAtScaleUniformRefinementConstant_eq_inv
    (n M N : ℕ) (w : NNReal) :
    factoringCoreAtScaleUniformRefinementConstant n M N w =
      (factoringCoreAtScaleUniformPipelineLoss n M N w)⁻¹ := by
  rw [factoringCoreAtScaleUniformRefinementConstant,
    Kakeya.factoringWeightedPipelineSelfRefinementConstant_eq]
  simp only [factoringCoreAtScaleUniformPipelineLoss, mul_inv]

/-- The uniform multiplicity-product loss is a fixed dimensional factor times the pipeline
loss. -/
theorem factoringCoreAtScaleUniformProductConstant_eq
    (n M N : ℕ) (w : NNReal) :
    factoringCoreAtScaleUniformProductConstant n M N w =
      4 * factoringCoreAtScaleUniformPipelineLoss n M N w *
        outerMultiplicityFromLocalBalls.C n := by
  rw [factoringCoreAtScaleUniformProductConstant,
    factoringCoreAtScaleUniformRefinementConstant_eq_inv]
  simp

/-- The inverse uniform fullness coefficient has only one extra linear volume-exponent loss
and two copies of the pipeline loss. -/
theorem inv_factoringCoreAtScaleUniformFullnessConstant_eq
    (n M N : ℕ) (w : NNReal) :
    (factoringCoreAtScaleUniformFullnessConstant n M N w)⁻¹ =
      (2 * 2 ^ 2 * lambdaInducedSingleWUniform.C * (N + 1)) *
        (factoringCoreAtScaleUniformPipelineLoss n M N w) ^ 2 := by
  rw [factoringCoreAtScaleUniformFullnessConstant,
    factoringCoreAtScaleUniformRefinementConstant_eq_inv]
  simp only [mul_inv, inv_inv, inv_pow]

private lemma natLog_succ_le_rpow : ∀ η : ℝ, 0 < η → ∃ B : NNReal, ∀ M : ℕ, 0 < M →
    ((Nat.log 2 M + 1 : ℕ) : NNReal) ≤ B * (M : NNReal) ^ η := by
  intro η hη
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let q : NNReal := ⟨1 / (η * Real.log 2), by positivity⟩
  refine ⟨1 + q, fun M hM ↦ ?_⟩
  have hM1 : (1 : NNReal) ≤ (M : NNReal) := by exact_mod_cast hM
  have hMpow : (1 : NNReal) ≤ (M : NNReal) ^ η := by
    simpa using NNReal.rpow_le_rpow hM1 hη.le
  have hlog : (Nat.log 2 M : ℝ) ≤ (M : ℝ) ^ η / (η * Real.log 2) := by
    calc
      (Nat.log 2 M : ℝ) ≤ Real.logb 2 M := Real.natLog_le_logb M 2
      _ = Real.log M / Real.log 2 := rfl
      _ ≤ ((M : ℝ) ^ η / η) / Real.log 2 := by
        gcongr
        exact Real.log_natCast_le_rpow_div M hη
      _ = (M : ℝ) ^ η / (η * Real.log 2) := by ring
  rw [← NNReal.coe_le_coe]
  push_cast [q, NNReal.coe_rpow]
  have hMpow' : (1 : ℝ) ≤ (M : ℝ) ^ η := by exact_mod_cast hMpow
  calc
    (Nat.log 2 M : ℝ) + 1 ≤ (M : ℝ) ^ η / (η * Real.log 2) + 1 := by
      linarith
    _ ≤ (M : ℝ) ^ η / (η * Real.log 2) + (M : ℝ) ^ η := by
      linarith
    _ = (1 + 1 / (η * Real.log 2)) * (M : ℝ) ^ η := by ring

private lemma fiberPigeonholeConstant_one_le_rpow :
    ∀ η : ℝ, 0 < η → ∃ A : NNReal, ∀ M : NNReal, 1 ≤ M →
      Kakeya.factoringStep1FiberPigeonholeConstant 1 M ≤ A * M ^ η := by
  intro η hη
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let q : NNReal := ⟨1 / (η * Real.log 2), by positivity⟩
  refine ⟨1 + q, fun M hM ↦ ?_⟩
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hMpow : (1 : NNReal) ≤ M ^ η := by
    simpa using NNReal.rpow_le_rpow hM hη.le
  have hlog : Real.logb 2 (M : ℝ) ≤ (M : ℝ) ^ η / (η * Real.log 2) := by
    calc
      Real.logb 2 (M : ℝ) = Real.log M / Real.log 2 := rfl
      _ ≤ ((M : ℝ) ^ η / η) / Real.log 2 := by
        gcongr
        exact Real.log_le_rpow_div (by positivity) hη
      _ = (M : ℝ) ^ η / (η * Real.log 2) := by ring
  have hlog0 : 0 ≤ Real.logb 2 (M : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hM)
  have harg0 : 0 ≤ 1 + Real.logb 2 ((M : ℝ) / ((1 : NNReal) : ℝ)) := by
    simpa using add_nonneg (by norm_num : (0 : ℝ) ≤ 1) hlog0
  rw [← NNReal.coe_le_coe]
  rw [Kakeya.factoringStep1FiberPigeonholeConstant, Real.coe_toNNReal _ harg0]
  push_cast [q, NNReal.coe_rpow]
  have hMpow' : (1 : ℝ) ≤ (M : ℝ) ^ η := by exact_mod_cast hMpow
  calc
    1 + Real.logb 2 ((M : ℝ) / (1 : ℝ)) ≤
        1 + (M : ℝ) ^ η / (η * Real.log 2) := by simpa using add_le_add_left hlog 1
    _ ≤ (M : ℝ) ^ η + (M : ℝ) ^ η / (η * Real.log 2) := by
      linarith
    _ = (1 + 1 / (η * Real.log 2)) * (M : ℝ) ^ η := by ring

private lemma one_le_volumeComparisonC_three :
    (1 : NNReal) ≤ Metric.volume_comparison.C 3 := by
  norm_num [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]

private lemma weightedStep1AtScaleConstant_three_le :
    ∀ η : ℝ, 0 < η → ∃ A : NNReal, ∀ M N : ℕ, 0 < M →
      FactorFamily.weightedStep1AtScaleConstant 3 M N ≤
        A * (N + 1 : ℕ) * (M : NNReal) ^ η := by
  intro η hη
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let q : NNReal := ⟨1 / (η * Real.log 2), by positivity⟩
  let c₀ : ℝ := 1 + Real.logb 2 (Metric.volume_comparison.C 3 : ℝ)
  have hc₀ : 0 ≤ c₀ := by
    dsimp [c₀]
    have := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast one_le_volumeComparisonC_three)
    exact add_nonneg (by norm_num) this
  let A : NNReal := ⟨2 * (c₀ + (q : ℝ) + 1), by positivity⟩
  refine ⟨A, fun M N hM ↦ ?_⟩
  have hM1 : (1 : NNReal) ≤ (M : NNReal) := by exact_mod_cast hM
  have hMpow : (1 : NNReal) ≤ (M : NNReal) ^ η := by
    simpa using NNReal.rpow_le_rpow hM1 hη.le
  have hlogM : Real.logb 2 (M : ℝ) ≤ (q : ℝ) * (M : ℝ) ^ η := by
    calc
      Real.logb 2 (M : ℝ) = Real.log M / Real.log 2 := rfl
      _ ≤ ((M : ℝ) ^ η / η) / Real.log 2 := by
        gcongr
        exact Real.log_natCast_le_rpow_div M hη
      _ = (q : ℝ) * (M : ℝ) ^ η := by
        have hq : (q : ℝ) = 1 / (η * Real.log 2) := rfl
        rw [hq]
        ring
  have hCpos : 0 < Metric.volume_comparison.C 3 := Metric.volume_comparison.C_pos 3
  have hratio :
      ((Kakeya.weightedStep1UpperBd M / Kakeya.weightedStep1LowerBd 3 N : NNReal) : ℝ) =
        (M : ℝ) * (Metric.volume_comparison.C 3 : ℝ) * 2 ^ N := by
    simp only [Kakeya.weightedStep1UpperBd, Kakeya.weightedStep1LowerBd]
    rw [NNReal.coe_div, NNReal.coe_inv, div_eq_mul_inv, inv_inv]
    push_cast
    ring
  have hlogratio : Real.logb 2
      (((Kakeya.weightedStep1UpperBd M / Kakeya.weightedStep1LowerBd 3 N : NNReal) : ℝ)) =
        Real.logb 2 (M : ℝ) + Real.logb 2 (Metric.volume_comparison.C 3 : ℝ) + N := by
    rw [hratio, Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by positivity) (by positivity), Real.logb_pow]
    norm_num
  have hnonneg : 0 ≤ 1 + Real.logb 2
      (((Kakeya.weightedStep1UpperBd M : NNReal) : ℝ) /
        (Kakeya.weightedStep1LowerBd 3 N : ℝ)) := by
    rw [← NNReal.coe_div, hlogratio]
    have hlogM0 : 0 ≤ Real.logb 2 (M : ℝ) :=
      Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by
        norm_cast)
    have hlogC0 := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast one_le_volumeComparisonC_three)
    positivity
  rw [FactorFamily.weightedStep1AtScaleConstant, Kakeya.factoringStep1PigeonholeConstant]
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_mul, NNReal.coe_natCast]
  rw [Kakeya.factoringStep1FiberPigeonholeConstant, Real.coe_toNNReal _ hnonneg]
  push_cast [A, q, NNReal.coe_rpow]
  rw [← NNReal.coe_div, hlogratio]
  have hMpow' : (1 : ℝ) ≤ (M : ℝ) ^ η := by exact_mod_cast hMpow
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by norm_num
  calc
    2 * (1 + (Real.logb 2 (M : ℝ) + Real.logb 2
        (Metric.volume_comparison.C 3 : ℝ) + (N : ℝ))) ≤
        2 * (c₀ + (q : ℝ) * (M : ℝ) ^ η + (N : ℝ)) := by
      dsimp [c₀]
      linarith
    _ ≤ 2 * (c₀ + (q : ℝ) + 1) * ((N : ℝ) + 1) * (M : ℝ) ^ η := by
      have hq0 : (0 : ℝ) ≤ q := by positivity
      have hN0 : (0 : ℝ) ≤ N := by positivity
      have hx0 : (0 : ℝ) ≤ (M : ℝ) ^ η := by positivity
      nlinarith [mul_nonneg hc₀ hx0, mul_nonneg hq0 hx0, mul_nonneg hN0 hx0,
        mul_nonneg (add_nonneg hc₀ (add_nonneg hq0 zero_le_one))
          (mul_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1) hx0)]

/-- The complete fixed-scale pipeline loss is jointly subpolynomial in the family cardinality
and inverse selected scale, with only a linear dependence on the explicit dyadic volume exponent. -/
theorem factoringCoreAtScaleUniformPipelineLoss_le (e : ℝ) (he : 0 < e) :
    ∃ C : NNReal, 1 ≤ C ∧ ∀ M N : ℕ, 0 < M → ∀ w : NNReal, 0 < w → w ≤ 1 →
      factoringCoreAtScaleUniformPipelineLoss 3 M N w ≤
        C * (N + 1 : ℕ) * (M : NNReal) ^ e * w ^ (-e) := by
  let η : ℝ := e / 5
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨A₁, hA₁⟩ := weightedStep1AtScaleConstant_three_le η hη
  obtain ⟨A₂, hA₂⟩ := natLog_succ_le_rpow η hη
  obtain ⟨A₅, hA₅⟩ := fiberPigeonholeConstant_one_le_rpow η hη
  let C₅ : NNReal := 8 * Kakeya.factoringStep5OverlapConstant 3 * A₅ * 64 ^ η
  let C₀ : NNReal := 4 * A₁ * A₂ ^ 4 * C₅
  refine ⟨max 1 C₀, le_max_left _ _, ?_⟩
  intro M N hM w hw hw1
  have hcover1 : 1 ≤ factoringCoreAtScaleCoverCardBound 3 w :=
    one_le_factoringCoreAtScaleCoverCardBound 3 hw
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hcover : factoringCoreAtScaleCoverCardBound 3 w ≤ 64 * w ^ (-(3 : ℝ)) := by
    rw [factoringCoreAtScaleCoverCardBound, ← NNReal.coe_le_coe,
      Real.coe_toNNReal _ (by positivity)]
    push_cast [NNReal.coe_rpow]
    have hbase : 2 * (1 + (w : ℝ)) / (w : ℝ) ≤ 4 / (w : ℝ) := by
      rw [div_le_div_iff_of_pos_right hwR]
      have hw1R : (w : ℝ) ≤ 1 := by exact_mod_cast hw1
      linarith
    calc
      (2 * (1 + (w : ℝ)) / (w : ℝ)) ^ 3 ≤ (4 / (w : ℝ)) ^ 3 := by
        gcongr
      _ = 64 * (w : ℝ) ^ (-(3 : ℝ)) := by
        rw [Real.rpow_neg (le_of_lt hwR)]
        field_simp [hwR.ne']
        norm_num
        ring
  have hcoverPow := NNReal.rpow_le_rpow hcover hη.le
  have hcoverPow' : (factoringCoreAtScaleCoverCardBound 3 w) ^ η ≤
      64 ^ η * w ^ (-(3 * η)) := by
    calc
      (factoringCoreAtScaleCoverCardBound 3 w) ^ η ≤ (64 * w ^ (-(3 : ℝ))) ^ η :=
        hcoverPow
      _ = 64 ^ η * w ^ (-(3 * η)) := by
        rw [NNReal.mul_rpow, ← NNReal.rpow_mul]
        congr 2
        ring
  have hwexp : w ^ (-(3 * η)) ≤ w ^ (-e) := by
    apply NNReal.rpow_le_rpow_of_exponent_ge hw hw1
    dsimp [η]
    linarith
  have hstep1 := hA₁ M N hM
  have hstep23 : (Kakeya.factoringStep2Step3Constant M : NNReal) ≤
      4 * A₂ ^ 4 * (M : NNReal) ^ (4 * η) := by
    rw [Kakeya.factoringStep2Step3Constant_eq]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    calc
      (4 : NNReal) * (((Nat.log 2 M + 1 : ℕ) : NNReal)) ^ 4 ≤
          4 * (A₂ * (M : NNReal) ^ η) ^ 4 := by
        gcongr
        exact hA₂ M hM
      _ = 4 * A₂ ^ 4 * (M : NNReal) ^ (4 * η) := by
        have hm : ((M : NNReal) ^ η) ^ 4 = (M : NNReal) ^ (4 * η) := by
          rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
          congr 1
          ring
        rw [mul_pow, hm]
        ring
  have hstep5 : Kakeya.factoringStep5SelfPigeonholeConstant 3
      (factoringCoreAtScaleCoverCardBound 3 w) ≤ C₅ * w ^ (-e) := by
    rw [Kakeya.factoringStep5SelfPigeonholeConstant]
    calc
      4 * Kakeya.factoringStep5OverlapConstant 3 *
          (2 * Kakeya.factoringStep1FiberPigeonholeConstant 1
            (factoringCoreAtScaleCoverCardBound 3 w)) =
          8 * Kakeya.factoringStep5OverlapConstant 3 *
            Kakeya.factoringStep1FiberPigeonholeConstant 1
              (factoringCoreAtScaleCoverCardBound 3 w) := by ring
      _ ≤
          8 * Kakeya.factoringStep5OverlapConstant 3 *
            (A₅ * (factoringCoreAtScaleCoverCardBound 3 w) ^ η) := by
        gcongr
        exact hA₅ _ hcover1
      _ ≤ 8 * Kakeya.factoringStep5OverlapConstant 3 *
          (A₅ * (64 ^ η * w ^ (-(3 * η)))) := by gcongr
      _ = C₅ * w ^ (-(3 * η)) := by dsimp [C₅]; ring
      _ ≤ C₅ * w ^ (-e) := by gcongr
  have hMexp : ((M : NNReal) ^ η) * (M : NNReal) ^ (4 * η) =
      (M : NNReal) ^ e := by
    rw [← NNReal.rpow_add (by exact_mod_cast hM.ne')]
    congr 1
    dsimp [η]
    ring
  calc
    factoringCoreAtScaleUniformPipelineLoss 3 M N w ≤
        (A₁ * (N + 1 : ℕ) * (M : NNReal) ^ η) *
          (4 * A₂ ^ 4 * (M : NNReal) ^ (4 * η)) * (C₅ * w ^ (-e)) := by
      dsimp only [factoringCoreAtScaleUniformPipelineLoss]
      gcongr
    _ = C₀ * (N + 1 : ℕ) * (M : NNReal) ^ e * w ^ (-e) := by
      rw [← hMexp]
      dsimp [C₀]
      ring
    _ ≤ max 1 C₀ * (N + 1 : ℕ) * (M : NNReal) ^ e * w ^ (-e) := by
      gcongr
      exact le_max_right _ _

/-- On a polynomially bounded family, at a selected scale between the master scale and one,
the complete fixed-scale pipeline loss is eventually bounded by any prescribed negative power
of the master scale.  The dyadic volume exponent is kept as an explicit hypothesis because its
logarithmic bound is supplied by the geometric adapter. -/
theorem eventually_factoringCoreAtScaleUniformPipelineLoss_le_rpow_neg
    {e : ℝ} (he : 0 < e) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ M N : ℕ, 0 < M →
        (M : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) →
        ((N + 1 : ℕ) : ENNReal) ≤ (δ : ENNReal) ^ (-(e / 4)) →
        ∀ w : NNReal, δ ≤ w → w ≤ 1 →
          (factoringCoreAtScaleUniformPipelineLoss 3 M N w : ENNReal) ≤
            (δ : ENNReal) ^ (-e) := by
  let e₀ : ℝ := e / 40
  have he₀ : 0 < e₀ := by dsimp [e₀]; positivity
  obtain ⟨C, hC1, hpipe⟩ := factoringCoreAtScaleUniformPipelineLoss_le e₀ he₀
  have he4 : 0 < e / 4 := by positivity
  filter_upwards [eventually_const_le_coe_rpow_neg (by exact_mod_cast hC1)
    ENNReal.coe_ne_top he4] with δ hδ
  intro M N hM hMcard hN w hδw hw1
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : δ ≤ 1 := hδ.2.1
  have hw0 : 0 < w := hδ0.trans_le hδw
  have hbase0 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hbaseTop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hMcardE : (M : ENNReal) ≤ (δ : ENNReal) ^ (-(7 : ℝ)) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hδ0.ne']
    exact_mod_cast hMcard
  have hMpow : ((M : ENNReal) ^ e₀) ≤
      (δ : ENNReal) ^ (-(7 * e₀)) := by
    calc
      (M : ENNReal) ^ e₀ ≤ ((δ : ENNReal) ^ (-(7 : ℝ))) ^ e₀ :=
        ENNReal.rpow_le_rpow hMcardE he₀.le
      _ = (δ : ENNReal) ^ (-(7 * e₀)) := by
        rw [← ENNReal.rpow_mul]
        congr 1
        ring
  have hwpow : (w : ENNReal) ^ (-e₀) ≤ (δ : ENNReal) ^ (-e₀) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.mpr
      (ENNReal.rpow_le_rpow (by exact_mod_cast hδw) he₀.le)
  have hraw := hpipe M N hM w hw0 hw1
  have hrawE : (factoringCoreAtScaleUniformPipelineLoss 3 M N w : ENNReal) ≤
      (C : ENNReal) * (N + 1 : ℕ) * (M : ENNReal) ^ e₀ *
        (w : ENNReal) ^ (-e₀) := by
    have hraw' := ENNReal.coe_le_coe.mpr hraw
    have hMnn0 : (M : NNReal) ≠ 0 := by exact_mod_cast hM.ne'
    simpa only [ENNReal.coe_mul, ENNReal.coe_natCast,
      ENNReal.coe_rpow_of_ne_zero hMnn0,
      ENNReal.coe_rpow_of_ne_zero hw0.ne'] using hraw'
  calc
    (factoringCoreAtScaleUniformPipelineLoss 3 M N w : ENNReal) ≤
        (C : ENNReal) * (N + 1 : ℕ) * (M : ENNReal) ^ e₀ *
          (w : ENNReal) ^ (-e₀) := hrawE
    _ ≤ (δ : ENNReal) ^ (-(e / 4)) * (δ : ENNReal) ^ (-(e / 4)) *
        (δ : ENNReal) ^ (-(7 * e₀)) * (δ : ENNReal) ^ (-e₀) := by
      exact mul_le_mul (mul_le_mul (mul_le_mul hδ.2.2 hN bot_le bot_le) hMpow bot_le bot_le)
        hwpow bot_le bot_le
    _ = (δ : ENNReal) ^ (-(e / 2 + 8 * e₀)) := by
      repeat' rw [← ENNReal.rpow_add _ _ hbase0 hbaseTop]
      congr 1
      ring
    _ ≤ (δ : ENNReal) ^ (-e) := by
      apply ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ1)
      dsimp [e₀]
      linarith

end ShadedBody
