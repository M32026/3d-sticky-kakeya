module

public import Kakeya.DimensionThree.MainLemma1.Factoring

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot

/-- The one-scale factoring loss is absorbed by any prescribed positive power, uniformly
over cardinalities satisfying the dimension-three geometric bound. -/
theorem eventually_factorOneScale_C_mul_rpow_le_one {a : ℝ} (ha : 0 < a) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal),
      ∀ σ : NNReal, δ ≤ σ -> σ ≤ 1 ->
        ∀ N : ℕ, 0 < N -> (N : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) ->
          (factorOneScale.C N σ : ENNReal) * (δ : ENNReal) ^ a ≤ 1 := by
  obtain ⟨Cε, hCε⟩ :=
    ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox 3 (a / 16) (by positivity)
  let K : NNReal := max 1 Cε
  have hK_pos : 0 < K := by
    dsimp [K]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hCεK : Cε ≤ K := by
    dsimp [K]
    exact le_max_right _ _
  have hK_ne : (K : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hK_pos)
  have hK_top : (K : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hKinv : 0 < (K : ENNReal)⁻¹ := by
    rw [ENNReal.inv_pos]
    exact hK_top
  filter_upwards [ENNReal.eventually_coe_rpow_le_of_pos (ρ := a / 2) (by positivity) hKinv,
      eventually_le_one_nhdsGT, self_mem_nhdsWithin] with δ hδpow hδ1 hδ0
  intro σ hδσ hσ1 N hN hNcard
  have hσ0 : 0 < σ := lt_of_lt_of_le hδ0 hδσ
  have hδne : δ ≠ 0 := ne_of_gt hδ0
  have hδE_ne : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδne
  have hδE_top : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hNcardNN : (N : NNReal) ≤ δ ^ (-(7 : ℝ)) := by
    exact_mod_cast hNcard
  have hNpow : (N : NNReal) ^ (a / 16) ≤ (δ ^ (-(7 : ℝ))) ^ (a / 16) := by
    exact NNReal.rpow_le_rpow hNcardNN (by positivity)
  have hNpow' : (N : NNReal) ^ (a / 16) ≤ δ ^ (-(7 : ℝ) * (a / 16)) := by
    rw [NNReal.rpow_mul δ (-(7 : ℝ)) (a / 16)]
    exact hNpow
  have hCsub : factorOneScale.C N σ
      ≤ Cε * σ ^ (-(a / 16)) * (N : NNReal) ^ (a / 16) := by
    simpa [factorOneScale.C] using hCε N hN σ hσ0 hσ1 1 le_rfl
  have hscale : σ ^ (-(a / 16)) ≤ δ ^ (-(a / 16)) :=
    NNReal.rpow_le_rpow_of_nonpos hδ0 hδσ (by linarith)
  have hC_le : factorOneScale.C N σ ≤ K * δ ^ (-(a / 2)) := by
    calc
      factorOneScale.C N σ
          ≤ Cε * σ ^ (-(a / 16)) * (N : NNReal) ^ (a / 16) := hCsub
      _ ≤ Cε * δ ^ (-(a / 16)) * (N : NNReal) ^ (a / 16) := by gcongr
      _ ≤ Cε * δ ^ (-(a / 16)) * δ ^ (-(7 : ℝ) * (a / 16)) := by
        simpa [mul_comm] using
          (mul_le_mul_of_nonneg_right hNpow'
            (mul_nonneg (by positivity) (by positivity) : 0 ≤ Cε * δ ^ (-(a / 16))))
      _ = Cε * (δ ^ (-(a / 16)) * δ ^ (-(7 : ℝ) * (a / 16))) := by ring
      _ = Cε * δ ^ (-(a / 2)) := by
        rw [← NNReal.rpow_add hδne (-(a / 16)) (-(7 : ℝ) * (a / 16))]
        congr 1
        ring
      _ ≤ K * δ ^ (-(a / 2)) := by
        exact mul_le_mul_of_nonneg_right hCεK (by positivity)
  have hC_leE : (factorOneScale.C N σ : ENNReal)
      ≤ (K : ENNReal) * (δ : ENNReal) ^ (-(a / 2)) := by
    have hcoerce : ((factorOneScale.C N σ : NNReal) : ENNReal)
        ≤ (((K * δ ^ (-(a / 2)) : NNReal) : ENNReal)) := by
      exact_mod_cast hC_le
    simpa [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hδne] using hcoerce
  calc
    (factorOneScale.C N σ : ENNReal) * (δ : ENNReal) ^ a
        ≤ (K : ENNReal) * (δ : ENNReal) ^ (-(a / 2)) * (δ : ENNReal) ^ a := by
          exact mul_le_mul_of_nonneg_right hC_leE (by positivity)
    _ = (K : ENNReal) * (δ : ENNReal) ^ (a / 2) := by
      rw [mul_assoc, ← ENNReal.rpow_add (x := (δ : ENNReal)) (-(a / 2)) a hδE_ne hδE_top]
      congr 1
      ring
    _ ≤ (K : ENNReal) * (K : ENNReal)⁻¹ := by
      exact mul_le_mul_of_nonneg_left hδpow (by positivity)
    _ = 1 := ENNReal.mul_inv_cancel hK_ne hK_top

/-- The product loss from the two factoring scales, together with the `2^4` uniformity loss,
is absorbed by any prescribed positive power of the external fine scale. -/
theorem eventually_factorTwoScales_C_mul_sixteen_rpow_le_one {a : ℝ} (ha : 0 < a) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal),
      ∀ τ : NNReal, δ ≤ τ -> τ ≤ 1 ->
        ∀ N₁ N₂ : ℕ, 0 < N₁ -> 0 < N₂ ->
          (N₁ : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) ->
          (N₂ : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) ->
          (factorTwoScales.C N₁ δ N₂ τ : ENNReal) * (2 : ENNReal) ^ 4
              * (δ : ENNReal) ^ a ≤ 1 := by
  have ha4 : 0 < a / 4 := by positivity
  let C : ENNReal := 16
  have hCne : C ≠ 0 := by norm_num [C]
  have hCtop : C ≠ ⊤ := by norm_num [C]
  have hCinv : 0 < C⁻¹ := by
    rw [ENNReal.inv_pos]
    exact hCtop
  filter_upwards [eventually_factorOneScale_C_mul_rpow_le_one ha4,
      ENNReal.eventually_coe_rpow_le_of_pos (ρ := a / 2) (by positivity) hCinv,
      self_mem_nhdsWithin] with δ hfac hconst hδ0
  intro τ hδτ hτ1 N₁ N₂ hN₁ hN₂ hcard₁ hcard₂
  have hδ1 : δ ≤ 1 := hδτ.trans hτ1
  have h₁ := hfac δ le_rfl hδ1 N₁ hN₁ hcard₁
  have h₂ := hfac τ hδτ hτ1 N₂ hN₂ hcard₂
  have h₃ : (16 : ENNReal) * (δ : ENNReal) ^ (a / 2) ≤ 1 := by
    calc
      (16 : ENNReal) * (δ : ENNReal) ^ (a / 2) ≤ C * C⁻¹ := by
        exact mul_le_mul_of_nonneg_left hconst (by positivity)
      _ = 1 := ENNReal.mul_inv_cancel hCne hCtop
  have hδne : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδ0)
  have hpow : (δ : ENNReal) ^ a =
      (δ : ENNReal) ^ (a / 4) * (δ : ENNReal) ^ (a / 4) *
        (δ : ENNReal) ^ (a / 2) := by
    rw [← ENNReal.rpow_add _ _ hδne ENNReal.coe_ne_top]
    rw [← ENNReal.rpow_add _ _ hδne ENNReal.coe_ne_top]
    congr 1
    ring
  calc
    (factorTwoScales.C N₁ δ N₂ τ : ENNReal) * (2 : ENNReal) ^ 4
          * (δ : ENNReal) ^ a
        = ((factorOneScale.C N₁ δ : ENNReal) * (δ : ENNReal) ^ (a / 4))
          * ((factorOneScale.C N₂ τ : ENNReal) * (δ : ENNReal) ^ (a / 4))
          * ((16 : ENNReal) * (δ : ENNReal) ^ (a / 2)) := by
            rw [factorTwoScales.C, ENNReal.coe_mul, hpow]
            norm_num
            ring
    _ ≤ 1 * 1 * 1 := by gcongr
    _ = 1 := by norm_num

end Kakeya.ml1Boot

#print axioms Kakeya.ml1Boot.eventually_factorOneScale_C_mul_rpow_le_one
#print axioms Kakeya.ml1Boot.eventually_factorTwoScales_C_mul_sixteen_rpow_le_one
