module

/-
  A2 Helper lemmas extracted from lagoon's work on the Typed QTTC Adapter.

  Contains:
  1. affine_growth_bound - transfer BallGrowth from DyadicTube to AffineLine
  2. c2_bound_helper - absorb thinning factors into C₂ bound

  These are standalone lemmas with all hypotheses explicit, designed to
  be imported into the canonical A2 adapter.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_Thinning
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.TypedQTTC_Assembly
public import MyLeanRepo.DiscretisedFurstenbergEstimate.QTTC_Assembly
public import MyLeanRepo.DiscretisedFurstenbergEstimate.QuantitativeThickTubeCover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineLipschitzTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Bridge_SSetTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.TubesAndSlopes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section


namespace DirecretisedFurstenbergEstimate.AppendixA.A2Helpers

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA (tubeSlope tubeIntercept InParent parentCell pointFiber)
open DirecretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter
  (snapTube dyadicTubeToA2 dyadicTubeToA2_slope dyadicTubeToA2_intercept)
open DiscretisedFurstenbergEstimate.InductionConfigurations (refinementFactor)

/-- Convert perpendicular distance (cthickening) to algebraic distance.
    Wrapper around TubesAndSlopes.near_point_intercept_bound_affine.
    For a point p within δ of line ℓ (in x=a*y+b convention, |a|≤1),
    the algebraic residual |p 0 - a*p 1 - b| is at most 2*δ. -/
lemma perpendicular_to_algebraic_distance
    (p : EuclideanPlane) (ℓ : AffineLine) (δ : ℝ)
    (hδ_pos : 0 < δ)
    (h_v1_ne_zero : (LemmaE.getDirV ℓ) 1 ≠ 0)
    (h_slope_le_one : |tubeSlope ℓ| ≤ 1)
    (h_p_in_cthickening : p ∈ Metric.cthickening δ ℓ.1) :
    |p 0 - tubeSlope ℓ * p 1 - tubeIntercept ℓ| ≤ 2 * δ := by
  have h_main : |tubeIntercept ℓ - (p 0 - tubeSlope ℓ * p 1)| ≤ 2 * δ :=
    TubesAndSlopes.near_point_intercept_bound_affine hδ_pos h_slope_le_one h_v1_ne_zero h_p_in_cthickening
  have h_eq : |p 0 - tubeSlope ℓ * p 1 - tubeIntercept ℓ| =
      |tubeIntercept ℓ - (p 0 - tubeSlope ℓ * p 1)| := by
    have h : p 0 - tubeSlope ℓ * p 1 - tubeIntercept ℓ =
        -(tubeIntercept ℓ - (p 0 - tubeSlope ℓ * p 1)) := by ring
    rw [h, abs_neg]
  rw [h_eq]
  exact h_main

/-- Lifting bound: if two AffineLine images are within r of a common point,
    the DyadicTube distance is at most 88*r. -/
lemma dyadic_dist_lift_88 {m : ℕ}
    (h_dist_lift : ∀ (U1 U2 : DyadicTube m),
        |U1.slope| ≤ 1 → |U2.slope| ≤ 1 →
        |U1.intercept| ≤ 3 → |U2.intercept| ≤ 3 →
        U1.dist U2 ≤ 44 * dist (dyadicTubeToA2 U1) (dyadicTubeToA2 U2))
    (U U1 : DyadicTube m) (x : AffineLine) (r : ℝ)
    (hU_s : |U.slope| ≤ 1) (hU1_s : |U1.slope| ≤ 1)
    (hU_i : |U.intercept| ≤ 3) (hU1_i : |U1.intercept| ≤ 3)
    (hdistU : dist (dyadicTubeToA2 U) x ≤ r)
    (hdistU1 : dist (dyadicTubeToA2 U1) x ≤ r) :
    U.dist U1 ≤ 88 * r := by
  let a := dyadicTubeToA2 U
  let b := dyadicTubeToA2 U1
  have h_total : dist a b ≤ 2 * r := by
    have h : dist a b ≤ dist a x + dist x b := dist_triangle a x b
    have h' : dist x b = dist b x := dist_comm x b
    rw [h'] at h
    dsimp only [a, b] at hdistU hdistU1 ⊢
    linarith
  have h44 : U.dist U1 ≤ 44 * dist a b := h_dist_lift U U1 hU_s hU1_s hU_i hU1_i
  linarith

/-- Standalone growth bound for S-set transfer from dyadic tubes to AffineLines.
    Extracted from qttc_typed_parentCell to keep the theorem context small. -/
lemma affine_growth_bound {m : ℕ} {s C₂_typed C₂ Δ : ℝ}
    {C_thin : Finset (DyadicTube m)}
    {C'_affine : Finset AffineLine}
    (hC'_affine_eq : C'_affine = C_thin.image dyadicTubeToA2)
    (hC_slope : ∀ U ∈ C_thin, |U.slope| ≤ 1)
    (hC_intercept : ∀ U ∈ C_thin, |U.intercept| ≤ 3)
    (h_thin_growth : ∀ (x : DyadicTube m) (r : ℝ), Δ ≤ r →
      ((C_thin.filter fun y => y.dist x ≤ r).card : ℝ) ≤
        (C₂_typed * 1936) * r ^ s * (C_thin.card : ℝ))
    (hΔ_pos : 0 < Δ)
    (hs_nonneg : 0 ≤ s)
    (hC2_typed_one : 1 ≤ C₂_typed)
    (hC2_def : C₂ = C₂_typed * 1936 * (88 : ℝ)^s)
    (h_inj : Function.Injective (dyadicTubeToA2 : DyadicTube m → AffineLine))
    (h_dist_lift : ∀ (U1 U2 : DyadicTube m),
        |U1.slope| ≤ 1 → |U2.slope| ≤ 1 →
        |U1.intercept| ≤ 3 → |U2.intercept| ≤ 3 →
        U1.dist U2 ≤ 44 * dist (dyadicTubeToA2 U1) (dyadicTubeToA2 U2)) :
    ∀ (x : AffineLine) (r : ℝ), Δ ≤ r →
      ((C'_affine.filter fun y => dist y x ≤ r).card : ℝ) ≤
        C₂ * r ^ s * (C'_affine.card : ℝ) := by
  intro x r hr
  let F_filter := C'_affine.filter fun y => dist y x ≤ r
  by_cases h_empty : F_filter.Nonempty
  · rcases h_empty with ⟨c1, hc1⟩
    have hc1_in : c1 ∈ C'_affine := (Finset.mem_filter.mp hc1).1
    have hc1_img : c1 ∈ C_thin.image dyadicTubeToA2 := by
      rw [←hC'_affine_eq] <;> exact hc1_in
    rcases Finset.mem_image.mp hc1_img with ⟨U1, hU1, rfl⟩
    have hU1_s : |U1.slope| ≤ 1 := hC_slope U1 hU1
    have hU1_i : |U1.intercept| ≤ 3 := hC_intercept U1 hU1
    have hdist1 : dist (dyadicTubeToA2 U1) x ≤ r :=
      (Finset.mem_filter.mp hc1).2
    have h5 : ∀ c ∈ F_filter,
        ∃ U : DyadicTube m, U ∈ C_thin ∧ dyadicTubeToA2 U = c ∧
          U.dist U1 ≤ 88 * r := by
      intro c hc
      have hc_in : c ∈ C'_affine := (Finset.mem_filter.mp hc).1
      have hdist2 : dist c x ≤ r := (Finset.mem_filter.mp hc).2
      have hc_img : c ∈ C_thin.image dyadicTubeToA2 := by
        rw [←hC'_affine_eq] <;> exact hc_in
      rcases Finset.mem_image.mp hc_img with ⟨U, hU, rfl⟩
      have hU_s : |U.slope| ≤ 1 := hC_slope U hU
      have hU_i : |U.intercept| ≤ 3 := hC_intercept U hU
      have h_dist_bound : U.dist U1 ≤ 88 * r :=
        dyadic_dist_lift_88 h_dist_lift U U1 x r hU_s hU1_s hU_i hU1_i hdist2 hdist1
      exact ⟨U, hU, rfl, h_dist_bound⟩
    let S_dyadic := C_thin.filter fun y => y.dist U1 ≤ 88 * r
    have h6 : F_filter ⊆ S_dyadic.image dyadicTubeToA2 := by
      intro c hc
      rcases h5 c hc with ⟨U, hU, rfl, hdist⟩
      exact Finset.mem_image.mpr ⟨U, Finset.mem_filter.mpr ⟨hU, hdist⟩, rfl⟩
    have h7 : F_filter.card ≤ (S_dyadic.image dyadicTubeToA2).card :=
      Finset.card_le_card h6
    have h8 : (S_dyadic.image dyadicTubeToA2).card ≤ S_dyadic.card :=
      Finset.card_image_le
    have h9 : (F_filter.card : ℝ) ≤ (S_dyadic.card : ℝ) := by
      exact_mod_cast le_trans h7 h8
    have h10 : Δ ≤ 88 * r := by
      have h11 : 0 < r := lt_of_lt_of_le hΔ_pos hr
      have h12 : Δ ≤ r := hr
      have h13 : r ≤ 88 * r := by
        have h14 : 0 ≤ r := by linarith
        nlinarith
      linarith
    have h15 : (S_dyadic.card : ℝ) ≤ (C₂_typed * 1936) * (88 * r) ^ s * (C_thin.card : ℝ) :=
      h_thin_growth U1 (88 * r) h10
    have h_card_eq : (C'_affine.card : ℝ) = (C_thin.card : ℝ) := by
      rw [hC'_affine_eq]
      rw [Finset.card_image_of_injOn]
      <;> exact h_inj.injOn
    have hpow : (88 * r) ^ s = (88 : ℝ)^s * r ^ s := by
      rw [Real.mul_rpow (by norm_num) (by linarith)]
    calc (F_filter.card : ℝ)
      ≤ (S_dyadic.card : ℝ) := h9
    _ ≤ (C₂_typed * 1936) * (88 * r) ^ s * (C_thin.card : ℝ) := h15
    _ = C₂ * r ^ s * (C'_affine.card : ℝ) := by
      rw [hpow, h_card_eq, hC2_def] <;> ring
  · have h9 : F_filter = ∅ := Finset.not_nonempty_iff_eq_empty.mp h_empty
    have h10 : 0 ≤ C₂ * r ^ s * (C'_affine.card : ℝ) := by
      have h_rpos : 0 < r := lt_of_lt_of_le hΔ_pos hr
      have hC2_nonneg : 0 ≤ C₂ := by
        rw [hC2_def] <;> positivity
      have hrpow_nonneg : 0 ≤ r ^ s := by positivity
      positivity
    have h11 : (F_filter.card : ℝ) = 0 := by
      rw [h9] <;> simp
    rw [h11]
    exact h10

/-- Standalone C₂ bound lemma.
    Given typed QTTC bound C₂_typed ≤ A_typed * K_typed^A_typed * C₁_QTTC,
    prove C₂ ≤ A * K^A * C₁ after absorbing thinning factors. -/
lemma c2_bound_helper
    (s A_typed K_typed C₁ C₂_typed B D A K C₂ C₁_QTTC : ℝ)
    (hA_one : 1 ≤ A_typed)
    (hK_one : 1 ≤ K_typed)
    (hB_one : 1 ≤ B)
    (hD_one : 1 ≤ D)
    (hC1 : 1 ≤ C₁)
    (hs_nonneg : 0 ≤ s)
    (hD_eq : D = 2 * B)
    (hA_def : A = A_typed * D * 1936 * (88 : ℝ)^s * (40 : ℝ)^s)
    (hK_def : K = K_typed * D * 1936)
    (hC2_def : C₂ = C₂_typed * 1936 * (88 : ℝ)^s)
    (hC1_QTTC_def : C₁_QTTC = C₁ * (40 : ℝ)^s * B * D)
    (hC2_bound : C₂_typed ≤ A_typed * Real.rpow K_typed A_typed * C₁_QTTC) :
    C₂ ≤ A * Real.rpow K A * C₁ := by
  have h88 : 1 ≤ (88 : ℝ)^s := by
    have h : (1 : ℝ)^s ≤ (88 : ℝ)^s := Real.rpow_le_rpow (by norm_num) (by norm_num) hs_nonneg
    simpa using h
  have h40 : 1 ≤ (40 : ℝ)^s := by
    have h : (1 : ℝ)^s ≤ (40 : ℝ)^s := Real.rpow_le_rpow (by norm_num) (by norm_num) hs_nonneg
    simpa using h
  have h1936 : 1 ≤ (1936 : ℝ) := by norm_num
  have hD1936 : 1 ≤ D * 1936 := by
    calc 1 = 1 * 1 := by ring
    _ ≤ D * 1936 := by gcongr
  have h_factor : 1 ≤ D * 1936 * (88 : ℝ)^s * (40 : ℝ)^s := by
    calc 1 = 1 * 1 * 1 * 1 := by ring
    _ ≤ D * 1936 * (88 : ℝ)^s * (40 : ℝ)^s := by gcongr
  have hK_ge : K_typed ≤ K := by
    rw [hK_def]
    have h5 : 0 ≤ K_typed := by linarith
    have h6 : K_typed * 1 ≤ K_typed * (D * 1936) := mul_le_mul_of_nonneg_left hD1936 h5
    have h7 : K_typed * (D * 1936) = K_typed * D * 1936 := by ring
    rw [h7] at h6
    simpa using h6
  have hA_ge : A_typed ≤ A := by
    rw [hA_def]
    have h7 : 0 ≤ A_typed := by linarith
    have h8 : A_typed * 1 ≤ A_typed * (D * 1936 * (88 : ℝ)^s * (40 : ℝ)^s) :=
      mul_le_mul_of_nonneg_left h_factor h7
    have h9 : A_typed * (D * 1936 * (88 : ℝ)^s * (40 : ℝ)^s) = A_typed * D * 1936 * (88 : ℝ)^s * (40 : ℝ)^s := by ring
    rw [h9] at h8
    simpa using h8
  have hA_one' : 1 ≤ A := by
    rw [hA_def]
    calc 1 = 1 * 1 * 1 * 1 * 1 := by ring
    _ ≤ A_typed * D * 1936 * (88 : ℝ)^s * (40 : ℝ)^s := by gcongr <;> linarith
  have hB_nonneg : 0 ≤ B := by linarith
  have hB_le_D1936 : B ≤ D * 1936 := by
    rw [hD_eq]
    have h : B ≤ (2 * B) * 1936 := by
      calc B = 1 * B := by ring
      _ ≤ 3872 * B := by gcongr <;> norm_num
      _ = (2 * B) * 1936 := by ring
    exact h
  have hK_typed_nonneg : 0 ≤ K_typed := by linarith
  have h_rpow_K : Real.rpow K A = Real.rpow K_typed A * Real.rpow (D * 1936) A := by
    have h_pos2 : 0 ≤ D * 1936 := by linarith
    have h_eq : K = K_typed * (D * 1936) := by rw [hK_def] <;> ring
    rw [h_eq]
    exact Real.mul_rpow hK_typed_nonneg h_pos2
  have h_pos_rpowA : 0 ≤ Real.rpow K_typed A := Real.rpow_nonneg hK_typed_nonneg A
  have h_pos_rpowA_typed : 0 ≤ Real.rpow K_typed A_typed := Real.rpow_nonneg hK_typed_nonneg A_typed
  have h_pos_D1936 : 0 ≤ D * 1936 := by linarith
  have h1 : Real.rpow K_typed A_typed ≤ Real.rpow K_typed A :=
    Real.rpow_le_rpow_of_exponent_le hK_one hA_ge
  have h2 : D * 1936 ≤ Real.rpow (D * 1936) A := by
    have h3 : Real.rpow (D * 1936) 1 ≤ Real.rpow (D * 1936) A :=
      Real.rpow_le_rpow_of_exponent_le hD1936 hA_one'
    have h4 : Real.rpow (D * 1936) 1 = D * 1936 := by simp
    rw [h4] at h3
    exact h3
  have hA_nonneg : 0 ≤ A := by linarith
  have h_pos_rpow_D1936 : 0 ≤ Real.rpow (D * 1936) A := Real.rpow_nonneg (by linarith) A
  have h_rpow_factor : B * Real.rpow K_typed A_typed ≤ Real.rpow K A := by
    have h_step1 : B * Real.rpow K_typed A_typed ≤ (D * 1936) * Real.rpow K_typed A :=
      mul_le_mul hB_le_D1936 h1 h_pos_rpowA_typed h_pos_D1936
    have h_step2 : (D * 1936) * Real.rpow K_typed A ≤ Real.rpow K_typed A * Real.rpow (D * 1936) A := by
      have h : Real.rpow K_typed A * (D * 1936) ≤ Real.rpow K_typed A * Real.rpow (D * 1936) A :=
        mul_le_mul_of_nonneg_left h2 h_pos_rpowA
      ring_nf at h ⊢ <;> exact h
    have h_step3 : Real.rpow K_typed A * Real.rpow (D * 1936) A = Real.rpow K A := by
      rw [←h_rpow_K]
    rw [h_step3] at h_step2
    exact le_trans h_step1 h_step2
  have h20 : B * D * Real.rpow K_typed A_typed ≤ D * Real.rpow K A := by
    calc B * D * Real.rpow K_typed A_typed
      = D * (B * Real.rpow K_typed A_typed) := by ring
    _ ≤ D * Real.rpow K A := by gcongr
  have h23 : 0 ≤ A_typed * 1936 * (88 : ℝ)^s * (40 : ℝ)^s * C₁ := by positivity
  let X := A_typed * 1936 * (88 : ℝ)^s * (40 : ℝ)^s * C₁
  have h_main_ineq : A_typed * 1936 * (88 : ℝ)^s * (40 : ℝ)^s * B * D * C₁ * Real.rpow K_typed A_typed ≤
      A * C₁ * Real.rpow K A := by
    calc A_typed * 1936 * (88 : ℝ)^s * (40 : ℝ)^s * B * D * C₁ * Real.rpow K_typed A_typed
      = X * (B * D * Real.rpow K_typed A_typed) := by dsimp only [X] <;> ring
    _ ≤ X * (D * Real.rpow K A) := mul_le_mul_of_nonneg_left h20 h23
    _ = A * C₁ * Real.rpow K A := by
      dsimp only [X]
      rw [hA_def] <;> ring
  calc C₂
    = C₂_typed * 1936 * (88 : ℝ)^s := hC2_def
  _ ≤ (A_typed * Real.rpow K_typed A_typed * C₁_QTTC) * 1936 * (88 : ℝ)^s := by gcongr
  _ = A_typed * 1936 * (88 : ℝ)^s * (40 : ℝ)^s * B * D * C₁ * Real.rpow K_typed A_typed := by
    rw [hC1_QTTC_def] <;> ring
  _ ≤ A * C₁ * Real.rpow K A := h_main_ineq
  _ = A * Real.rpow K A * C₁ := by ring

/-! ========================================================================
   Dyadic scale arithmetic helpers (merged from fjord/A2_helpers.lean)
   ======================================================================== -/

/-- dyadicDelta n = dyadicDelta m / 2^(n-m) for m ≤ n. -/
lemma dyadicDelta_div_refinement {n m : ℕ} (hnm : m ≤ n) :
    dyadicDelta n = dyadicDelta m / (refinementFactor n m : ℝ) := by
  have h_sum : m + (n - m) = n := by omega
  have h_pos1 : (0 : ℝ) < (2 : ℝ)^m := by positivity
  have h_pos2 : (0 : ℝ) < (2 : ℝ)^(n - m) := by positivity
  have h_rf : (refinementFactor n m : ℝ) = (2 : ℝ)^(n - m) := by
    dsimp only [refinementFactor] <;> norm_cast
  calc dyadicDelta n
    = 1 / (2 : ℝ)^n := by rw [dyadicDelta]
  _ = 1 / ((2 : ℝ)^m * (2 : ℝ)^(n - m)) := by rw [← pow_add, h_sum]
  _ = (1 / (2 : ℝ)^m) / (2 : ℝ)^(n - m) := by
    field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
  _ = dyadicDelta m / (refinementFactor n m : ℝ) := by
    rw [dyadicDelta, h_rf]

/-- For a fine tube T at scale n, its slope divided by coarse scale dyadicDelta m
    equals its slope index divided by the refinement factor. -/
lemma fine_slope_div_coarse {n m : ℕ} (hnm : m ≤ n) (T : DyadicTube n) :
    T.slope / dyadicDelta m = (T.a : ℝ) / (refinementFactor n m : ℝ) := by
  have h_slope_def : T.slope = (T.a : ℝ) * dyadicDelta n := by rfl
  have h_delta : dyadicDelta n = dyadicDelta m / (refinementFactor n m : ℝ) :=
    dyadicDelta_div_refinement hnm
  rw [h_slope_def, h_delta]
  have h_pos1 : 0 < dyadicDelta m := dyadicDelta_pos m
  have h_pos2 : (0 : ℝ) < (refinementFactor n m : ℝ) := by
    have h : 0 < refinementFactor n m := by dsimp only [refinementFactor] <;> positivity
    exact_mod_cast h
  field_simp [h_pos1.ne', h_pos2.ne'] <;> ring

/-- For a fine tube T at scale n, its intercept divided by coarse scale dyadicDelta m
    equals its intercept index divided by the refinement factor. -/
lemma fine_intercept_div_coarse {n m : ℕ} (hnm : m ≤ n) (T : DyadicTube n) :
    T.intercept / dyadicDelta m = (T.b : ℝ) / (refinementFactor n m : ℝ) := by
  have h_int_def : T.intercept = (T.b : ℝ) * dyadicDelta n := by rfl
  have h_delta : dyadicDelta n = dyadicDelta m / (refinementFactor n m : ℝ) :=
    dyadicDelta_div_refinement hnm
  rw [h_int_def, h_delta]
  have h_pos1 : 0 < dyadicDelta m := dyadicDelta_pos m
  have h_pos2 : (0 : ℝ) < (refinementFactor n m : ℝ) := by
    have h : 0 < refinementFactor n m := by dsimp only [refinementFactor] <;> positivity
    exact_mod_cast h
  field_simp [h_pos1.ne', h_pos2.ne'] <;> ring

/-- For integer a and positive natural b, floor of real division equals integer division. -/
lemma floor_real_ediv (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ⌊(a : ℝ) / (b : ℝ)⌋ = a / (b : ℤ) := by
  have h : ⌊(a : ℝ) / (b : ℝ)⌋ = ⌊(a : ℝ)⌋ / b := Int.floor_div_natCast (a : ℝ) b
  rw [h]
  have h2 : ⌊(a : ℝ)⌋ = a := by simp
  rw [h2] <;> rfl

/-- The coarse parent's slope index is the floor of fine slope divided by coarse scale. -/
lemma coarse_slope_index_floor {n m : ℕ} (hnm : m ≤ n) (T : DyadicTube n) :
    ⌊T.slope / dyadicDelta m⌋ = T.a / (refinementFactor n m : ℤ) := by
  rw [fine_slope_div_coarse hnm T]
  have h_pos : 0 < refinementFactor n m := by dsimp only [refinementFactor] <;> positivity
  exact floor_real_ediv T.a (refinementFactor n m) h_pos

/-- The coarse parent's intercept index is the floor of fine intercept divided by coarse scale. -/
lemma coarse_intercept_index_floor {n m : ℕ} (hnm : m ≤ n) (T : DyadicTube n) :
    ⌊T.intercept / dyadicDelta m⌋ = T.b / (refinementFactor n m : ℤ) := by
  rw [fine_intercept_div_coarse hnm T]
  have h_pos : 0 < refinementFactor n m := by dsimp only [refinementFactor] <;> positivity
  exact floor_real_ediv T.b (refinementFactor n m) h_pos

end DirecretisedFurstenbergEstimate.AppendixA.A2Helpers
