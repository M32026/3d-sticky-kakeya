module

/-
  SnapTube → SourceParent → DyadicTubeToA2: canonical bounds and provenance.

  Three standalone lemmas for the C_global_A2 construction:

  1. sourceParent_slope_bound: fine strip bound → coarse |slope| ≤ 1
  2. sourceParent_intercept_bound: fine |intercept| ≤ 3 → coarse |intercept| ≤ 3
  3. inParent_provenance_bound: InParent relation → dist ≤ 15·Δ

  Key chain:
    ℓ (source AffineLine)
      → snapTube n ℓ (fine DyadicTube n)
      → sourceParent hnm (coarse DyadicTube m)
      → dyadicTubeToA2 (coarse AffineLine)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.TypedDyadicInfrastructure
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_TypedQTTC_Adapter.Basic
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineLipschitzTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA.SnapTubeProvenance

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA (tubeSlope tubeIntercept InParent parentCell)
open DirecretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter
open DirecretisedFurstenbergEstimate.AppendixA.TypedDyadicInfrastructure
open DirecretisedFurstenbergEstimate.AppendixA.A2Helpers
  (coarse_slope_index_floor coarse_intercept_index_floor)
open DirecretisedFurstenbergEstimate.AppendixA.A2TypedQTTCAdapter
  (dyadicTubeToA2_getDirV_ne_zero floor_dyadic_bound_three)
open DiscretisedFurstenbergEstimate.InductionConfigurations (refinementFactor)
open AffineLineLipschitzTransfer (affineLineParams_antilipschitz)
open LemmaE (getDirV)

/-! ========================================================================
   Helper: refinement factor arithmetic
   ======================================================================== -/

private lemma refinementFactor_eq_pow {n m : ℕ} (hnm : m ≤ n) :
    (refinementFactor n m : ℤ) = 2 ^ (n - m) := by
  simp [refinementFactor] <;> omega

private lemma pow_div {n m : ℕ} (hnm : m ≤ n) :
    (2 ^ n : ℤ) = (2 ^ (n - m) : ℤ) * (2 ^ m : ℤ) := by
  have h : (n - m) + m = n := by omega
  have h2 : (2 ^ (n - m) : ℤ) * (2 ^ m : ℤ) = 2 ^ ((n - m) + m) := by
    rw [←pow_add]
  rw [h] at h2
  exact h2.symm

private lemma real_pow_div {n m : ℕ} (hnm : m ≤ n) :
    (2 ^ n : ℝ) = (2 ^ (n - m) : ℝ) * (2 ^ m : ℝ) := by
  have h : (n - m) + m = n := by omega
  have h2 : (2 ^ (n - m) : ℝ) * (2 ^ m : ℝ) = 2 ^ ((n - m) + m) := by
    rw [←pow_add]
  rw [h] at h2
  exact h2.symm

/-! ========================================================================
   1. Slope bound: fine strip → coarse |slope| ≤ 1
   ======================================================================== -/

/-- If fine tube T satisfies strip bound `-(2^n) ≤ T.a ∧ T.a < 2^n`,
    then coarse parent U has `|U.slope| ≤ 1`.

    Uses coarse_slope_index_floor: U.a = ⌊T.slope / Δ⌋.
    Since -1 ≤ T.slope < 1 and 1/Δ = 2^m is integral,
    floor gives -2^m ≤ U.a ≤ 2^m - 1, hence |U.slope| ≤ 1. -/
lemma sourceParent_slope_bound {n m : ℕ} (hnm : m ≤ n)
    (T : DyadicTube n) (U : DyadicTube m)
    (hU : sourceParent hnm T = U)
    (h_strip : -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ)) :
    |U.slope| ≤ 1 := by
  have hU_a : U.a = T.a / (refinementFactor n m : ℤ) := by
    rw [←hU] <;> rfl
  have h_floor : U.a = ⌊T.slope / dyadicDelta m⌋ := by
    rw [hU_a, ←coarse_slope_index_floor hnm T]
  have h_slope_ge : -1 ≤ T.slope := by
    have h1 : -(2 ^ n : ℤ) ≤ T.a := h_strip.1
    have h2 : (T.a : ℝ) ≥ -(2 ^ n : ℝ) := by exact_mod_cast h1
    have h3 : T.slope = (T.a : ℝ) * dyadicDelta n := by
      simp [DyadicTube.slope] <;> ring
    rw [h3]
    have h4 : dyadicDelta n = 1 / (2 ^ n : ℝ) := by simp [dyadicDelta] <;> ring
    rw [h4]
    have h5 : (T.a : ℝ) * (1 / (2 ^ n : ℝ)) ≥ -(2 ^ n : ℝ) * (1 / (2 ^ n : ℝ)) := by gcongr
    have h6 : -(2 ^ n : ℝ) * (1 / (2 ^ n : ℝ)) = -1 := by field_simp <;> ring
    rw [h6] at h5
    exact h5
  have h_slope_lt : T.slope < 1 := by
    have h1 : T.a < (2 ^ n : ℤ) := h_strip.2
    have h2 : (T.a : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast h1
    have h3 : T.slope = (T.a : ℝ) * dyadicDelta n := by
      simp [DyadicTube.slope] <;> ring
    rw [h3]
    have h4 : dyadicDelta n = 1 / (2 ^ n : ℝ) := by simp [dyadicDelta] <;> ring
    rw [h4]
    have h5 : (T.a : ℝ) * (1 / (2 ^ n : ℝ)) < (2 ^ n : ℝ) * (1 / (2 ^ n : ℝ)) := by gcongr
    have h6 : (2 ^ n : ℝ) * (1 / (2 ^ n : ℝ)) = 1 := by field_simp <;> ring
    rw [h6] at h5
    exact h5
  have h_main : |(U.a : ℝ) * dyadicDelta m| ≤ 1 := by
    rw [h_floor]
    let Δ := dyadicDelta m
    have hΔ_pos : 0 < Δ := dyadicDelta_pos m
    let N : ℕ := 2 ^ m
    have h_int : (1 : ℝ) / Δ = (N : ℝ) := by
      simp [Δ, dyadicDelta, N] <;> field_simp <;> ring_nf <;> norm_cast
    have h_div_le : T.slope / Δ ≤ (N : ℝ) := by
      have h1 : T.slope / Δ ≤ (1 : ℝ) / Δ := by gcongr
      rw [h_int] at h1; exact h1
    have h_div_ge : -(N : ℝ) ≤ T.slope / Δ := by
      have h1 : -(1 : ℝ) / Δ ≤ T.slope / Δ := by gcongr
      have h2 : -(1 : ℝ) / Δ = -(N : ℝ) := by
        have h3 : -(1 : ℝ) / Δ = -((1 : ℝ) / Δ) := by ring
        rw [h3, h_int] <;> ring
      rw [h2] at h1; exact h1
    have h_floor_le : (⌊T.slope / Δ⌋ : ℝ) ≤ (N : ℝ) := by
      have h1 : (⌊T.slope / Δ⌋ : ℝ) ≤ T.slope / Δ := Int.floor_le _
      linarith
    have h_floor_ge : -(N : ℝ) ≤ (⌊T.slope / Δ⌋ : ℝ) := by
      have h1 : T.slope / Δ < (⌊T.slope / Δ⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      have h2 : (⌊-(N : ℝ)⌋ : ℤ) = -(N : ℤ) := by
        have h3 : ⌊-(N : ℝ)⌋ = -⌈(N : ℝ)⌉ := by exact Int.floor_neg
        rw [h3]
        have h4 : ⌈(N : ℝ)⌉ = (N : ℤ) := by simp [Int.ceil_natCast]
        rw [h4] <;> rfl
      have h3 : (⌊-(N : ℝ)⌋ : ℝ) ≤ (⌊T.slope / Δ⌋ : ℝ) := by
        gcongr <;> linarith
      rw [h2] at h3 <;> exact_mod_cast h3
    have h5 : -(1 : ℝ) ≤ (⌊T.slope / Δ⌋ : ℝ) * Δ := by
      calc -(1 : ℝ)
        = (-(N : ℝ)) * Δ := by rw [show (-(N : ℝ)) * Δ = -((N : ℝ) * Δ) by ring, ←h_int] <;> field_simp [hΔ_pos.ne'] <;> ring
      _ ≤ (⌊T.slope / Δ⌋ : ℝ) * Δ := by gcongr
    have h6 : (⌊T.slope / Δ⌋ : ℝ) * Δ ≤ (1 : ℝ) := by
      calc (⌊T.slope / Δ⌋ : ℝ) * Δ
        ≤ ((N : ℝ)) * Δ := by gcongr
      _ = (1 : ℝ) := by rw [←h_int] <;> field_simp [hΔ_pos.ne'] <;> ring
    rw [abs_le] <;> constructor <;> linarith
  have h_uslope : U.slope = (U.a : ℝ) * dyadicDelta m := by
    simp [DyadicTube.slope] <;> ring
  rw [h_uslope]
  exact h_main

/-! ========================================================================
   2. Intercept bound: fine |intercept| ≤ 3 → coarse |intercept| ≤ 3
   ======================================================================== -/

/-- If fine tube T has `|T.intercept| ≤ 3`, then coarse parent U has
    `|U.intercept| ≤ 3`. Uses floor_dyadic_bound_three. -/
lemma sourceParent_intercept_bound {n m : ℕ} (hnm : m ≤ n)
    (T : DyadicTube n) (U : DyadicTube m)
    (hU : sourceParent hnm T = U)
    (h_intercept : |T.intercept| ≤ 3) :
    |U.intercept| ≤ 3 := by
  have hU_b : U.b = T.b / (refinementFactor n m : ℤ) := by
    rw [←hU] <;> rfl
  have h_floor : U.b = ⌊T.intercept / dyadicDelta m⌋ := by
    rw [hU_b, ←coarse_intercept_index_floor hnm T]
  have h1 : U.intercept = (U.b : ℝ) * dyadicDelta m := by
    simp [DyadicTube.intercept] <;> ring
  rw [h1, h_floor]
  exact floor_dyadic_bound_three T.intercept h_intercept

/-! ========================================================================
   3. Provenance bound
   ======================================================================== -/

/-- If `InParent Δ ℓ (dyadicTubeToA2 U)` and both lines have slope ≤ 1,
    intercept ≤ 3, and nonzero direction y-component, then
    `dist ℓ (dyadicTubeToA2 U) ≤ 15 * Δ`. -/
lemma inParent_provenance_bound {m : ℕ} {Δ : ℝ} (hΔ_pos : 0 < Δ)
    (hΔ_eq : Δ = dyadicDelta m)
    (ℓ : AffineLine) (U : DyadicTube m)
    (hInParent : InParent Δ hΔ_pos ℓ (dyadicTubeToA2 U))
    (h_slope_ℓ : |tubeSlope ℓ| ≤ 1)
    (h_intercept_ℓ : |tubeIntercept ℓ| ≤ 3)
    (h_dirV_ℓ : (getDirV ℓ) 1 ≠ 0)
    (h_slope_U : |tubeSlope (dyadicTubeToA2 U)| ≤ 1)
    (h_intercept_U : |tubeIntercept (dyadicTubeToA2 U)| ≤ 3) :
    dist ℓ (dyadicTubeToA2 U) ≤ 15 * Δ := by
  set ℓ_U := dyadicTubeToA2 U with hℓ_U
  have h_dirV_U : (getDirV ℓ_U) 1 ≠ 0 :=
    A2TypedQTTCAdapter.dyadicTubeToA2_getDirV_ne_zero U
  have hdm_pos : 0 < dyadicDelta m := dyadicDelta_pos m
  have h_parent_U : parentCell (dyadicDelta m) hdm_pos ℓ_U = (U.a, U.b) :=
    dyadicTube_parentCell U hdm_pos
  have h_parent_U' : parentCell Δ hΔ_pos ℓ_U = (U.a, U.b) := by
    subst hΔ_eq
    exact h_parent_U
  have h1 : parentCell Δ hΔ_pos ℓ = (U.a, U.b) := by
    rw [InParent] at hInParent
    rw [hInParent, h_parent_U']
  have h_floor_slope : ⌊tubeSlope ℓ / Δ⌋ = U.a := by
    have h2 : (parentCell Δ hΔ_pos ℓ).1 = U.a := by rw [h1] <;> simp
    simpa [parentCell] using h2
  have h_floor_intercept : ⌊tubeIntercept ℓ / Δ⌋ = U.b := by
    have h2 : (parentCell Δ hΔ_pos ℓ).2 = U.b := by rw [h1] <;> simp
    simpa [parentCell] using h2
  have h_slope_cell : (U.a : ℝ) * Δ ≤ tubeSlope ℓ ∧ tubeSlope ℓ < ((U.a : ℝ) + 1) * Δ := by
    have h3 : (U.a : ℝ) ≤ tubeSlope ℓ / Δ := by
      exact_mod_cast h_floor_slope ▸ Int.floor_le (tubeSlope ℓ / Δ)
    have h4 : tubeSlope ℓ / Δ < (U.a : ℝ) + 1 := by
      exact_mod_cast h_floor_slope ▸ Int.lt_floor_add_one (tubeSlope ℓ / Δ)
    have h5 : (U.a : ℝ) * Δ ≤ tubeSlope ℓ := by
      calc (U.a : ℝ) * Δ ≤ (tubeSlope ℓ / Δ) * Δ := by gcongr
        _ = tubeSlope ℓ := by field_simp [hΔ_pos.ne'] <;> ring
    have h6 : tubeSlope ℓ < ((U.a : ℝ) + 1) * Δ := by
      calc tubeSlope ℓ = (tubeSlope ℓ / Δ) * Δ := by field_simp [hΔ_pos.ne'] <;> ring
        _ < ((U.a : ℝ) + 1) * Δ := by gcongr
    exact ⟨h5, h6⟩
  have h_intercept_cell : (U.b : ℝ) * Δ ≤ tubeIntercept ℓ ∧ tubeIntercept ℓ < ((U.b : ℝ) + 1) * Δ := by
    have h3 : (U.b : ℝ) ≤ tubeIntercept ℓ / Δ := by
      exact_mod_cast h_floor_intercept ▸ Int.floor_le (tubeIntercept ℓ / Δ)
    have h4 : tubeIntercept ℓ / Δ < (U.b : ℝ) + 1 := by
      exact_mod_cast h_floor_intercept ▸ Int.lt_floor_add_one (tubeIntercept ℓ / Δ)
    have h5 : (U.b : ℝ) * Δ ≤ tubeIntercept ℓ := by
      calc (U.b : ℝ) * Δ ≤ (tubeIntercept ℓ / Δ) * Δ := by gcongr
        _ = tubeIntercept ℓ := by field_simp [hΔ_pos.ne'] <;> ring
    have h6 : tubeIntercept ℓ < ((U.b : ℝ) + 1) * Δ := by
      calc tubeIntercept ℓ = (tubeIntercept ℓ / Δ) * Δ := by field_simp [hΔ_pos.ne'] <;> ring
        _ < ((U.b : ℝ) + 1) * Δ := by gcongr
    exact ⟨h5, h6⟩
  have h_slope_U_eq : tubeSlope ℓ_U = (U.a : ℝ) * Δ := by
    rw [dyadicTubeToA2_slope U, hΔ_eq] <;> simp [DyadicTube.slope] <;> ring
  have h_intercept_U_eq : tubeIntercept ℓ_U = (U.b : ℝ) * Δ := by
    rw [dyadicTubeToA2_intercept U, hΔ_eq] <;> simp [DyadicTube.intercept] <;> ring
  have h_da : |tubeSlope ℓ - tubeSlope ℓ_U| < Δ := by
    rw [h_slope_U_eq]
    have h3 : 0 ≤ tubeSlope ℓ - (U.a : ℝ) * Δ := by linarith [h_slope_cell.1]
    have h4 : tubeSlope ℓ - (U.a : ℝ) * Δ < Δ := by linarith [h_slope_cell.2]
    rw [abs_of_nonneg h3] <;> linarith
  have h_db : |tubeIntercept ℓ - tubeIntercept ℓ_U| < Δ := by
    rw [h_intercept_U_eq]
    have h3 : 0 ≤ tubeIntercept ℓ - (U.b : ℝ) * Δ := by linarith [h_intercept_cell.1]
    have h4 : tubeIntercept ℓ - (U.b : ℝ) * Δ < Δ := by linarith [h_intercept_cell.2]
    rw [abs_of_nonneg h3] <;> linarith
  have h5 : |tubeSlope ℓ - tubeSlope ℓ_U| ^ 2 + |tubeIntercept ℓ - tubeIntercept ℓ_U| ^ 2 < 2 * Δ ^ 2 := by
    have ha : |tubeSlope ℓ - tubeSlope ℓ_U| < Δ := h_da
    have hb : |tubeIntercept ℓ - tubeIntercept ℓ_U| < Δ := h_db
    have ha2 : |tubeSlope ℓ - tubeSlope ℓ_U| ^ 2 < Δ ^ 2 := by
      have hpos : 0 ≤ |tubeSlope ℓ - tubeSlope ℓ_U| := by positivity
      gcongr <;> linarith
    have hb2 : |tubeIntercept ℓ - tubeIntercept ℓ_U| ^ 2 < Δ ^ 2 := by
      have hpos : 0 ≤ |tubeIntercept ℓ - tubeIntercept ℓ_U| := by positivity
      gcongr <;> linarith
    have hpos : 0 < Δ ^ 2 := by positivity
    nlinarith
  have h_sqrt2_gt_one : (1 : ℝ) < Real.sqrt 2 := by
    have h : (1 : ℝ) ^ 2 < (2 : ℝ) := by norm_num
    have h' : (1 : ℝ) < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt h
    exact h'
  have h_da2 : dist (tubeSlope ℓ) (tubeSlope ℓ_U) < Real.sqrt 2 * Δ := by
    have h : dist (tubeSlope ℓ) (tubeSlope ℓ_U) = |tubeSlope ℓ - tubeSlope ℓ_U| := by
      simp [Real.dist_eq]
    rw [h]
    calc |tubeSlope ℓ - tubeSlope ℓ_U| < Δ := h_da
      _ < Real.sqrt 2 * Δ := by
        have h9 : Δ < Real.sqrt 2 * Δ := by
          have h10 : (1 : ℝ) < Real.sqrt 2 := h_sqrt2_gt_one
          nlinarith
        exact h9
  have h_db2 : dist (tubeIntercept ℓ) (tubeIntercept ℓ_U) < Real.sqrt 2 * Δ := by
    have h : dist (tubeIntercept ℓ) (tubeIntercept ℓ_U) = |tubeIntercept ℓ - tubeIntercept ℓ_U| := by
      simp [Real.dist_eq]
    rw [h]
    calc |tubeIntercept ℓ - tubeIntercept ℓ_U| < Δ := h_db
      _ < Real.sqrt 2 * Δ := by
        have h9 : Δ < Real.sqrt 2 * Δ := by
          have h10 : (1 : ℝ) < Real.sqrt 2 := h_sqrt2_gt_one
          nlinarith
        exact h9
  have h_param_dist : dist (tubeSlope ℓ, tubeIntercept ℓ)
        (tubeSlope ℓ_U, tubeIntercept ℓ_U) < Real.sqrt 2 * Δ := by
    rw [Prod.dist_eq]
    rw [max_lt_iff]
    exact ⟨h_da2, h_db2⟩
  have h_antilip : dist ℓ ℓ_U ≤ 10 * dist (tubeSlope ℓ, tubeIntercept ℓ)
        (tubeSlope ℓ_U, tubeIntercept ℓ_U) :=
    affineLineParams_antilipschitz ℓ ℓ_U h_dirV_ℓ h_dirV_U
      h_slope_ℓ h_slope_U h_intercept_ℓ h_intercept_U
  calc dist ℓ ℓ_U
    ≤ 10 * dist (tubeSlope ℓ, tubeIntercept ℓ) (tubeSlope ℓ_U, tubeIntercept ℓ_U) := h_antilip
  _ ≤ 10 * (Real.sqrt 2 * Δ) := by gcongr <;> exact h_param_dist.le
  _ = (10 * Real.sqrt 2) * Δ := by ring
  _ ≤ 15 * Δ := by
    have h9 : 10 * Real.sqrt 2 ≤ 15 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    gcongr

end DirecretisedFurstenbergEstimate.AppendixA.SnapTubeProvenance
