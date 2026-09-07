module

/-
  Heavy Parent Uniformization Theorem — CLEAN

  Composes:
  1. Heavy parent removal (threshold τ) with point retention ≥ 1/2
  2. Point fiber uniformization (dyadic band [M, 2M))
  3. Correct regularity transfer via RetainedRegularityClean

  Exports BOTH fiber bounds:
    τ ≤ card(fiber) < 2*M
  where τ = δ_n^{-u/2+heavySlack}.

  NO contaminated imports. Uses:
  - RetainedRegularityClean (fjord)
  - PointFiberUniformization
  - GeometricIntersection (for squareContained_toSet_subset)

  Whiteprint node: combining_theorem_rework / heavy_parent_retention
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.PointFiberUniformization
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.RetainedRegularityClean
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.LocalRegularityTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.GeometricIntersection
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open InductionConfigurations
open DirecretisedFurstenbergEstimate.RegularIncidence

/-- Local C_geo = 9 (geometric packing factor). -/
abbrev C_geo_local : ℝ := 9

/-! ========================================================================
   Occupied parents bound (clean version)
   ======================================================================== -/

/-- Number of occupied coarse parents ≤ C_geo * Ncover(Δ, config.pointSet).
    Clean proof using finset_squares_ncover_lower_clean. -/
lemma occupied_parents_bound_clean
    {n m : ℕ} (hnm : m ≤ n)
    {s C : ℝ} {M : ℕ}
    (config : CombiningTheorem.NiceConfiguration n s C M) :
    ∃ (occupiedParents : Finset (DyadicSquare m)),
      (occupiedParents = config.P₀.image (InductionConfigurations.containingSquare hnm)) ∧
      (occupiedParents.card : ENNReal) ≤
        ENNReal.ofReal C_geo_local * Ncover (dyadicDelta m) config.pointSet := by
  let occupiedParents : Finset (DyadicSquare m) :=
    config.P₀.image (InductionConfigurations.containingSquare hnm)
  have h_intersect : ∀ Q ∈ occupiedParents,
      ((Q.toSet : Set Plane) ∩ config.pointSet).Nonempty := by
    intro Q hQ
    rcases Finset.mem_image.mp hQ with ⟨p, hp, rfl⟩
    let Q' := InductionConfigurations.containingSquare hnm p
    have h_cont : InductionConfigurations.squareContained hnm p Q' :=
      (InductionConfigurations.containingSquare_iff hnm p Q').mp rfl
    have h_sub : (p.toSet : Set Plane) ⊆ Q'.toSet :=
      InductionOnScales.squareContained_toSet_subset hnm h_cont
    have hp_nonempty : (p.toSet : Set Plane).Nonempty := p.toSet_nonempty
    have hp_in_pointSet : (p.toSet : Set Plane) ⊆ config.pointSet := by
      intro x hx
      simpa [NiceConfiguration.pointSet, Set.mem_iUnion₂] using ⟨p, hp, hx⟩
    rcases hp_nonempty with ⟨x, hx⟩
    exact ⟨x, h_sub hx, hp_in_pointSet hx⟩
  have h_bound : (occupiedParents.card : ENNReal) ≤
      (9 : ENNReal) * Ncover (dyadicDelta m) config.pointSet :=
    finset_intersecting_squares_bound_clean h_intersect
  have h9 : (9 : ENNReal) = ENNReal.ofReal C_geo_local := by
    norm_num [C_geo_local]
  rw [h9] at h_bound
  exact ⟨occupiedParents, rfl, h_bound⟩

/-! ========================================================================
   Polylog absorption lemmas
   ======================================================================== -/

/-- Polylog bound on numDyadicLevels in terms of log(1/δ). -/
lemma numDyadicLevels_polylog_bound
    (N_max : ℕ) (δ C_N D : ℝ)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hCN_ge_one : 1 ≤ C_N) (hD_pos : 0 < D)
    (hN_max_bound : (N_max : ℝ) ≤ C_N * δ ^ (-D)) :
    (numDyadicLevels N_max : ℝ) ≤
      2 * Real.log (C_N + 1) + 2 + 2 * D * Real.log (1 / δ) := by
  by_cases hN0 : N_max = 0
  · rw [hN0]
    have h1 : (numDyadicLevels 0 : ℝ) = 2 := by
      simp [numDyadicLevels] <;> omega
    rw [h1]
    have h_log_pos : 0 < Real.log (C_N + 1) := by
      apply Real.log_pos
      linarith
    have h_log2_pos : 0 < Real.log (1 / δ) := by
      apply Real.log_pos
      have h5 : 1 < 1 / δ := by
        apply one_lt_one_div hδ_pos
        exact hδ_lt_one
      exact h5
    have h_a : 0 ≤ 2 * Real.log (C_N + 1) := by
      have h_pos : 0 < Real.log (C_N + 1) := Real.log_pos (by linarith)
      linarith
    have h_b : 0 ≤ 2 * D * Real.log (1 / δ) := by positivity
    have h_goal : (2 : ℝ) ≤ 2 * Real.log (C_N + 1) + 2 + 2 * D * Real.log (1 / δ) := by linarith
    exact h_goal
  · have hN_pos : 0 < N_max := Nat.pos_of_ne_zero hN0
    have h1 : (numDyadicLevels N_max : ℝ) ≤ 2 * Real.log ((N_max : ℝ) + 1) + 2 :=
      numDyadicLevels_le_polylog N_max hN_pos
    have h21 : δ ^ (-D) ≥ 1 := by
      have h22 : δ ^ D < 1 := Real.rpow_lt_one (by linarith) (by linarith) hD_pos
      have h23 : δ ^ (-D) = (δ ^ D)⁻¹ := by
        have h24 : (-D) = -(D) := by ring
        rw [h24, Real.rpow_neg (by linarith)] <;> ring
      rw [h23]
      have h25 : 0 < δ ^ D := Real.rpow_pos_of_pos hδ_pos D
      have h26 : δ ^ D ≤ 1 := by linarith
      have h27 : (δ ^ D)⁻¹ ≥ 1 := by
        calc (δ ^ D)⁻¹ ≥ 1⁻¹ := by gcongr
             _ = 1 := by norm_num
      exact h27
    have h2 : (N_max : ℝ) + 1 ≤ (C_N + 1) * δ ^ (-D) := by
      have h3 : (N_max : ℝ) ≤ C_N * δ ^ (-D) := hN_max_bound
      have h4 : (1 : ℝ) ≤ (C_N + 1) * δ ^ (-D) := by
        have h5 : 1 ≤ C_N + 1 := by linarith
        have h6 : (C_N + 1) * δ ^ (-D) ≥ 1 * δ ^ (-D) := by gcongr
        linarith
      linarith
    have h3 : Real.log ((N_max : ℝ) + 1) ≤ Real.log ((C_N + 1) * δ ^ (-D)) :=
      Real.log_le_log (by linarith) h2
    have h4 : Real.log ((C_N + 1) * δ ^ (-D)) =
        Real.log (C_N + 1) + (-D) * Real.log δ := by
      rw [Real.log_mul (by linarith) (by positivity), Real.log_rpow (by linarith)] <;> ring
    have h5 : Real.log (1 / δ) = -Real.log δ := by
      rw [Real.log_div (by norm_num) hδ_pos.ne', Real.log_one, zero_sub]
    have h6 : Real.log ((N_max : ℝ) + 1) ≤ Real.log (C_N + 1) + D * Real.log (1 / δ) := by
      calc Real.log ((N_max : ℝ) + 1)
        ≤ Real.log ((C_N + 1) * δ ^ (-D)) := h3
      _ = Real.log (C_N + 1) + (-D) * Real.log δ := h4
      _ = Real.log (C_N + 1) + D * Real.log (1 / δ) := by rw [h5] <;> ring
    have h_final : (numDyadicLevels N_max : ℝ) ≤
        2 * Real.log (C_N + 1) + 2 + 2 * D * Real.log (1 / δ) := by
      calc (numDyadicLevels N_max : ℝ)
        ≤ 2 * Real.log ((N_max : ℝ) + 1) + 2 := h1
      _ ≤ 2 * (Real.log (C_N + 1) + D * Real.log (1 / δ)) + 2 := by gcongr
      _ = 2 * Real.log (C_N + 1) + 2 + 2 * D * Real.log (1 / δ) := by ring
    exact h_final

/-- Standalone polylog absorption: C * log(1/δ)^(-K) ≥ δ^α for small δ. -/
lemma polylog_lower_bound_absorption_local
    (C K α : ℝ) (hC : 0 < C) (hK : 0 ≤ K) (hα_pos : 0 < α) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      C * (Real.log (1 / δ)) ^ (-K) ≥ δ ^ α := by
  have h_tendsto : Filter.Tendsto (fun x : ℝ => x ^ K * Real.exp (-α * x))
      Filter.atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero K α hα_pos
  have h_exists : ∃ X : ℝ, ∀ x : ℝ, x ≥ X → x ^ K * Real.exp (-α * x) ≤ C := by
    have h1 : ∃ X0 : ℝ, ∀ x : ℝ, x ≥ X0 → dist (x ^ K * Real.exp (-α * x)) 0 < C :=
      Metric.tendsto_atTop.mp h_tendsto C hC
    rcases h1 with ⟨X0, hX0⟩
    let X := max X0 1
    have hX : ∀ x : ℝ, x ≥ X → dist (x ^ K * Real.exp (-α * x)) 0 < C := by
      intro x hx
      have h_ge : x ≥ X0 := le_trans (le_max_left X0 1) hx
      exact hX0 x h_ge
    refine ⟨X, fun x hx => ?_⟩
    have h2 : dist (x ^ K * Real.exp (-α * x)) 0 < C := hX x hx
    have h2' : |x ^ K * Real.exp (-α * x)| < C := by simpa [Real.dist_eq] using h2
    have h_x_pos' : 0 < x := by
      have h : x ≥ X := hx
      have h' : x ≥ 1 := le_trans (le_max_right X0 1) h
      linarith
    have h3 : 0 ≤ x ^ K := by positivity
    have h4 : 0 ≤ Real.exp (-α * x) := by positivity
    have h5 : 0 ≤ x ^ K * Real.exp (-α * x) := mul_nonneg h3 h4
    have h6 : |x ^ K * Real.exp (-α * x)| = x ^ K * Real.exp (-α * x) := abs_of_nonneg h5
    rw [h6] at h2'
    exact le_of_lt h2'
  rcases h_exists with ⟨X, hX⟩
  let δ₁ := Real.exp (-X)
  have hδ₁_pos : 0 < δ₁ := by positivity
  let δ₂ := Real.exp (-1)
  have hδ₂_pos : 0 < δ₂ := by positivity
  let δ₀ := min δ₁ δ₂
  have hδ₀_pos : 0 < δ₀ := lt_min hδ₁_pos hδ₂_pos
  use δ₀, hδ₀_pos
  intro δ hδ_pos hδ_lt
  have h_lt1 : δ < δ₁ := lt_of_lt_of_le hδ_lt (min_le_left _ _)
  have h_lt2 : δ < δ₂ := lt_of_lt_of_le hδ_lt (min_le_right _ _)
  set x := Real.log (1 / δ) with hx_def
  have h_x_ge_X : x ≥ X := by
    have h : δ < Real.exp (-X) := h_lt1
    have h2 : 1 / δ > Real.exp X := by
      have h3 : 1 / δ > 1 / Real.exp (-X) := by gcongr
      have h4 : 1 / Real.exp (-X) = Real.exp X := by
        have h5 : Real.exp (-X) = (Real.exp X)⁻¹ := by rw [Real.exp_neg]
        rw [h5]; field_simp
      rw [h4] at h3; exact h3
    have h5 : Real.log (1 / δ) > Real.log (Real.exp X) := Real.log_lt_log (by positivity) h2
    have h6 : Real.log (Real.exp X) = X := Real.log_exp X
    rw [h6] at h5; exact le_of_lt h5
  have h_x_ge_one : 1 ≤ x := by
    have h : δ < Real.exp (-1) := h_lt2
    have h2 : 1 / δ > Real.exp 1 := by
      have h3 : 1 / δ > 1 / Real.exp (-1) := by gcongr
      have h4 : 1 / Real.exp (-1) = Real.exp 1 := by
        have h5 : Real.exp (-1) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
        rw [h5]; field_simp
      rw [h4] at h3; exact h3
    have h5 : Real.log (1 / δ) > Real.log (Real.exp 1) := Real.log_lt_log (by positivity) h2
    have h6 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
    rw [h6] at h5; exact le_of_lt h5
  have h_x_pos : 0 < x := by linarith
  have h_main_ineq : x ^ K * Real.exp (-α * x) ≤ C := hX x h_x_ge_X
  have h_exp_eq : Real.exp (-α * x) = δ ^ α := by
    have h7 : -α * x = Real.log (δ ^ α) := by
      have h8 : Real.log (δ ^ α) = α * Real.log δ := by rw [Real.log_rpow (by linarith)]
      have h91 : Real.log (1 / δ) = -Real.log δ := by
        rw [Real.log_div (by norm_num) hδ_pos.ne', Real.log_one, zero_sub]
      have h9 : x = -Real.log δ := by rw [hx_def, h91]
      calc -α * x
        = -α * (-Real.log δ) := by rw [h9]
      _ = α * Real.log δ := by ring
      _ = Real.log (δ ^ α) := by rw [h8]
    have h10 : Real.exp (-α * x) = Real.exp (Real.log (δ ^ α)) := by rw [h7]
    have h11 : 0 < δ ^ α := Real.rpow_pos_of_pos hδ_pos α
    rw [h10, Real.exp_log h11]
  have h12 : x ^ K * δ ^ α ≤ C := by
    rw [h_exp_eq] at h_main_ineq; exact h_main_ineq
  have h13 : 0 < x ^ K := by positivity
  have h14 : C * x ^ (-K) ≥ δ ^ α := by
    have h15 : x ^ (-K) = (x ^ K)⁻¹ := by
      have h16 : (-K) = -(K) := by ring
      rw [h16, Real.rpow_neg (by linarith)] <;> ring
    rw [h15]
    calc C * (x ^ K)⁻¹
      ≥ (x ^ K * δ ^ α) * (x ^ K)⁻¹ := by gcongr
    _ = δ ^ α := by
      field_simp [h13.ne'] <;> ring
  simpa [hx_def] using h14

/-- Total retention absorption: 2 * L * δ^α ≤ 1 for small δ,
    given L ≤ A + B * log(1/δ). -/
lemma total_retention_absorption
    (A B α : ℝ) (hB_nonneg : 0 ≤ B) (hα_pos : 0 < α) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      (2 * (A + B * Real.log (1 / δ))) * δ ^ α ≤ 1 := by
  let A_abs := |A|
  let D := 2 * A_abs + 2 * B + 1
  have hD_pos : 0 < D := by
    have h1 : 0 ≤ A_abs := abs_nonneg A
    have h2 : 0 ≤ B := hB_nonneg
    dsimp only [D]
    linarith
  let C := 1 / D
  have hC_pos : 0 < C := by positivity
  have h_main := polylog_lower_bound_absorption_local C 1 α hC_pos (by norm_num) hα_pos
  rcases h_main with ⟨δ₁, hδ₁_pos, h1⟩
  let δ₀ := min δ₁ (Real.exp (-1))
  have hδ₀_pos : 0 < δ₀ := by positivity
  refine ⟨δ₀, hδ₀_pos, fun δ hδ_pos hδ_lt => ?_⟩
  have hδ_lt1 : δ < δ₁ := lt_of_lt_of_le hδ_lt (min_le_left _ _)
  have hδ_lt_exp : δ < Real.exp (-1) := lt_of_lt_of_le hδ_lt (min_le_right _ _)
  set x := Real.log (1 / δ) with hx_def
  have h_x_ge_one : 1 ≤ x := by
    have h7 : 1 / δ > Real.exp 1 := by
      have h8 : 1 / δ > 1 / Real.exp (-1) := by gcongr
      have h9 : 1 / Real.exp (-1) = Real.exp 1 := by
        have h10 : Real.exp (-1) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
        rw [h10]; field_simp
      rw [h9] at h8; exact h8
    have h10 : Real.log (1 / δ) > Real.log (Real.exp 1) := Real.log_lt_log (by positivity) h7
    have h11 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
    rw [h11] at h10; exact le_of_lt h10
  have h_x_pos : 0 < x := by linarith
  have h6 : C * x ^ (-1 : ℝ) ≥ δ ^ α := h1 δ hδ_pos hδ_lt1
  have h7 : C / x ≥ δ ^ α := by
    have h8 : x ^ (-1 : ℝ) = x⁻¹ := by
      have h9 : (-1 : ℝ) = -(1 : ℝ) := by ring
      rw [h9, Real.rpow_neg (by linarith)] <;> simp
    rw [h8] at h6
    exact h6
  have h9 : x * δ ^ α ≤ C := by
    have h10 : C / x ≥ δ ^ α := h7
    have h11 : C ≥ x * δ ^ α := by
      calc C
        = (C / x) * x := by field_simp [h_x_pos.ne'] <;> ring
      _ ≥ δ ^ α * x := by gcongr
      _ = x * δ ^ α := by ring
    exact h11
  by_cases h_neg : A + B * x < 0
  · have h12 : (2 * (A + B * x)) * δ ^ α ≤ 0 := by
      have h13 : 0 ≤ δ ^ α := Real.rpow_nonneg (by linarith) α
      nlinarith
    linarith
  · have h_nonneg : 0 ≤ A + B * x := by linarith
    have h14 : A + B * x ≤ A_abs + B * x := by
      have h15 : A ≤ A_abs := le_abs_self A
      linarith
    have h16 : A_abs + B * x ≤ (A_abs + B) * x := by
      have h17 : 0 ≤ A_abs := abs_nonneg A
      have h18 : A_abs ≤ A_abs * x := by nlinarith
      linarith
    have h19 : 2 * (A + B * x) ≤ 2 * (A_abs + B) * x := by
      calc 2 * (A + B * x)
        ≤ 2 * (A_abs + B * x) := by gcongr
      _ ≤ 2 * ((A_abs + B) * x) := by gcongr
      _ = 2 * (A_abs + B) * x := by ring
    have h20 : (2 * (A + B * x)) * δ ^ α ≤ (2 * (A_abs + B)) * (x * δ ^ α) := by
      have h201 : 2 * (A + B * x) ≤ 2 * (A_abs + B) * x := h19
      have h202 : 0 ≤ δ ^ α := Real.rpow_nonneg (by linarith) α
      calc
        (2 * (A + B * x)) * δ ^ α
          ≤ (2 * (A_abs + B) * x) * δ ^ α := by exact mul_le_mul_of_nonneg_right h201 h202
        _ = (2 * (A_abs + B)) * (x * δ ^ α) := by ring
    have h22 : (2 * (A_abs + B)) * (x * δ ^ α) ≤ (2 * (A_abs + B)) * C := by gcongr
    have h23 : (2 * (A_abs + B)) * C ≤ 1 := by
      dsimp only [C, D]
      have h24 : 0 ≤ A_abs := abs_nonneg A
      have h25 : 0 ≤ B := hB_nonneg
      have h26 : 2 * A_abs + 2 * B + 1 > 0 := by linarith
      field_simp [h26.ne']
      <;> nlinarith
    exact le_trans (le_trans h20 h22) h23

/-! ========================================================================
   Main heavy-parent uniformization theorem
   ======================================================================== -/

/-- Heavy parent filtering + fiber uniformization.

    Given a config with square-root regular point set, filters out light
    coarse parents (fiber < τ), then uniformizes the remaining heavy fibers
    to a dyadic band [M, 2M).

    Output:
    - P_uniform ⊆ config.P₀
    - |config.P₀| ≤ 2 * L * |P_uniform|  (L = numDyadicLevels(N_max))
    - Q_uniform = occupied parents of P_uniform
    - For all Q ∈ Q_uniform: τ ≤ fiber(Q) < 2*M
    - Degraded square-root regularity on P_uniform.pointSet
      with constant C_P * 18 * L.

    Clean imports only. -/
theorem heavy_parent_uniform_clean
    {n m : ℕ} (hnm : m ≤ n) (h_even : n = 2 * m)
    {s u C C_P K_P : ℝ} {M : ℕ}
    (config : CombiningTheorem.NiceConfiguration n s C M)
    (h_point_regular : IsSquareRootRegular (dyadicDelta n) u C_P K_P config.pointSet)
    (heavySlack : ℝ) (hSlack_pos : 0 < heavySlack)
    (hK_P_pos : 0 < K_P)
    (hP0_lower : (config.P₀.card : ℝ) >
        2 * C_geo_local * K_P * (dyadicDelta n)^(-u + heavySlack)) :
    ∃ (P_uniform : Finset (DyadicSquare n))
      (M_fiber : ℕ)
      (Q_uniform : Finset (DyadicSquare m)),
      P_uniform ⊆ config.P₀ ∧
      (config.P₀.card : ℝ) ≤
        2 * (numDyadicLevels config.P₀.card : ℝ) * (P_uniform.card : ℝ) ∧
      Q_uniform = P_uniform.image (InductionConfigurations.containingSquare hnm) ∧
      (∀ Q ∈ Q_uniform,
        (M_fiber : ℝ) ≤
          ((P_uniform.filter (fun p => squareContained hnm p Q)).card : ℝ) ∧
        (dyadicDelta n)^(-u / 2 + heavySlack) ≤
          ((P_uniform.filter (fun p => squareContained hnm p Q)).card : ℝ) ∧
        ((P_uniform.filter (fun p => squareContained hnm p Q)).card : ℝ) <
          2 * (M_fiber : ℝ)) ∧
      IsSquareRootRegular (dyadicDelta n) u
        (C_P * 18 * (numDyadicLevels config.P₀.card : ℝ)) K_P
        (⋃ p ∈ (P_uniform : Set (DyadicSquare n)), (p.toSet : Set Plane)) := by
  let δ_n := dyadicDelta n
  let Δ := dyadicDelta m
  have hδ_n_pos : 0 < δ_n := dyadicDelta_pos n
  have hΔ_pos : 0 < Δ := dyadicDelta_pos m
  have hnm' : m ≤ n := hnm
  have hδ_n_eq : δ_n = Δ^2 := by
    dsimp only [δ_n, Δ, dyadicDelta]
    have h1 : n = 2 * m := h_even
    have h2 : (2 : ℝ)^n = (2 : ℝ)^(2 * m) := by rw [h1]
    have h3 : (2 : ℝ)^(2 * m) = ((2 : ℝ)^m)^2 := by
      have h4 : (2 * m) = m + m := by ring
      rw [h4, pow_add] <;> ring
    rw [h2, h3] <;> field_simp <;> ring
  let τ : ℝ := δ_n^(-u / 2 + heavySlack)
  have hτ_pos : 0 < τ := Real.rpow_pos_of_pos hδ_n_pos _

  -- Step 1: Occupied parents bound
  rcases occupied_parents_bound_clean hnm' config with ⟨occupiedParents, h_occ_eq, h_occ_bound⟩

  let countInParent (Q : DyadicSquare m) : ℕ :=
    (config.P₀.filter (fun p => squareContained hnm' p Q)).card

  let lightParents := occupiedParents.filter (fun Q => (countInParent Q : ℝ) < τ)
  let heavyParents := occupiedParents.filter (fun Q => τ ≤ (countInParent Q : ℝ))

  have h_disj : Disjoint lightParents heavyParents := by
    rw [Finset.disjoint_left]
    intro Q h1 h2
    have h4 : τ ≤ (countInParent Q : ℝ) := (Finset.mem_filter.mp h2).2
    have h5 : (countInParent Q : ℝ) < τ := (Finset.mem_filter.mp h1).2
    exact not_le.mpr h5 h4

  have h_partition : ∀ Q ∈ occupiedParents, Q ∈ lightParents ∨ Q ∈ heavyParents := by
    intro Q hQ
    by_cases h : (countInParent Q : ℝ) < τ
    · exact Or.inl (Finset.mem_filter.mpr ⟨hQ, h⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hQ, by linarith⟩)

  have h_sqrt_bound : Ncover Δ config.pointSet ≤ ENNReal.ofReal (K_P * δ_n^(-u / 2)) := by
    have hΔ_eq : Δ = Real.sqrt δ_n := by
      rw [hδ_n_eq]
      rw [Real.sqrt_sq (by positivity)]
    rw [hΔ_eq]
    exact h_point_regular.2

  have h_occ_real : (occupiedParents.card : ℝ) ≤ C_geo_local * (K_P * δ_n^(-u / 2)) := by
    have h9 : (occupiedParents.card : ENNReal) ≤
        ENNReal.ofReal C_geo_local * Ncover Δ config.pointSet := h_occ_bound
    have h10 : Ncover Δ config.pointSet ≤ ENNReal.ofReal (K_P * δ_n^(-u / 2)) := h_sqrt_bound
    have h11 : (occupiedParents.card : ENNReal) ≤
        ENNReal.ofReal (C_geo_local * (K_P * δ_n^(-u / 2))) := by
      calc (occupiedParents.card : ENNReal)
        ≤ ENNReal.ofReal C_geo_local * Ncover Δ config.pointSet := h9
      _ ≤ ENNReal.ofReal C_geo_local * ENNReal.ofReal (K_P * δ_n^(-u / 2)) := by gcongr
      _ = ENNReal.ofReal (C_geo_local * (K_P * δ_n^(-u / 2))) := by
        have h_pos1 : 0 ≤ C_geo_local := by norm_num [C_geo_local]
        have h_pos2 : 0 ≤ K_P * δ_n^(-u / 2) := by
          have h_rpow_pos : 0 < δ_n^(-u / 2) := Real.rpow_pos_of_pos hδ_n_pos _
          exact mul_nonneg hK_P_pos.le h_rpow_pos.le
        rw [←ENNReal.ofReal_mul h_pos1] <;> rfl
    have h13 : 0 ≤ C_geo_local * (K_P * δ_n^(-u / 2)) := by
      have h_rpow_pos : 0 < δ_n^(-u / 2) := Real.rpow_pos_of_pos hδ_n_pos _
      have h : 0 ≤ K_P * δ_n^(-u / 2) := mul_nonneg hK_P_pos.le h_rpow_pos.le
      exact mul_nonneg (by norm_num [C_geo_local]) h
    have h14 : (occupiedParents.card : ENNReal) ≠ ⊤ := by exact ENNReal.natCast_ne_top occupiedParents.card
    have h15 : ENNReal.ofReal (C_geo_local * (K_P * δ_n^(-u / 2))) ≠ ⊤ := by exact ENNReal.ofReal_ne_top
    have h16 : ((occupiedParents.card : ENNReal).toReal) ≤
        (ENNReal.ofReal (C_geo_local * (K_P * δ_n^(-u / 2)))).toReal :=
      ENNReal.toReal_le_toReal h14 h15 |>.mpr h11
    have h17 : ((occupiedParents.card : ENNReal).toReal) = (occupiedParents.card : ℝ) := by simp
    have h_rpow_pos2 : 0 < δ_n^(-u / 2) := Real.rpow_pos_of_pos hδ_n_pos _
    have h14 : 0 ≤ K_P * δ_n^(-u / 2) := mul_nonneg hK_P_pos.le h_rpow_pos2.le
    have h18 : (ENNReal.ofReal (C_geo_local * (K_P * δ_n^(-u / 2)))).toReal =
        C_geo_local * (K_P * δ_n^(-u / 2)) := by simp [h13, h14]
    rw [h17, h18] at h16
    exact h16

  have h_containment_iff : ∀ (p : DyadicSquare n) (Q : DyadicSquare m),
      squareContained hnm' p Q ↔ InductionConfigurations.containingSquare hnm' p = Q :=
    fun p Q => (containingSquare_iff hnm' p Q).symm

  have h_sum_all : (config.P₀.card : ℝ) = ∑ Q ∈ occupiedParents, (countInParent Q : ℝ) := by
    have h_mapsTo : (config.P₀ : Set (DyadicSquare n)).MapsTo
        (InductionConfigurations.containingSquare hnm') (occupiedParents : Set (DyadicSquare m)) := by
      rw [h_occ_eq]
      intro p hp
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have h := Finset.card_eq_sum_card_fiberwise h_mapsTo
    have h_eq1 : ∀ q ∈ occupiedParents,
        (config.P₀.filter (fun p => InductionConfigurations.containingSquare hnm' p = q)).card = countInParent q := by
      intro q _
      have h_filter_eq : config.P₀.filter (fun p => InductionConfigurations.containingSquare hnm' p = q) =
          config.P₀.filter (fun p => squareContained hnm' p q) := by
        ext p
        simp only [Finset.mem_filter]
        <;> rw [containingSquare_iff hnm' p q]
      rw [h_filter_eq]
    have h_sum : ∑ Q ∈ occupiedParents, (countInParent Q : ℝ) = ∑ Q ∈ occupiedParents,
        ↑((config.P₀.filter (fun p => InductionConfigurations.containingSquare hnm' p = Q)).card) := by
      apply Finset.sum_congr rfl
      intro Q hQ
      exact_mod_cast (h_eq1 Q hQ).symm
    have h_cast : (config.P₀.card : ℝ) = ∑ Q ∈ occupiedParents,
        ↑((config.P₀.filter (fun p => InductionConfigurations.containingSquare hnm' p = Q)).card) := by
      exact_mod_cast h
    rw [h_cast, h_sum]

  have h_light_sum : ∑ Q ∈ lightParents, (countInParent Q : ℝ) ≤ (lightParents.card : ℝ) * τ := by
    have h4 : ∀ Q ∈ lightParents, (countInParent Q : ℝ) ≤ τ :=
      fun Q hQ => ((Finset.mem_filter.mp hQ).2).le
    calc ∑ Q ∈ lightParents, (countInParent Q : ℝ)
      ≤ ∑ Q ∈ lightParents, τ := Finset.sum_le_sum h4
    _ = (lightParents.card : ℝ) * τ := by rw [Finset.sum_const] <;> ring

  have h_light_half : ∑ Q ∈ lightParents, (countInParent Q : ℝ) < (config.P₀.card : ℝ) / 2 := by
    have h5 : (lightParents.card : ℝ) ≤ (occupiedParents.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have h10 : (lightParents.card : ℝ) * τ ≤ C_geo_local * K_P * δ_n^(-u + heavySlack) := by
      calc (lightParents.card : ℝ) * τ
        ≤ (occupiedParents.card : ℝ) * τ := by gcongr
      _ ≤ C_geo_local * (K_P * δ_n^(-u / 2)) * τ := by gcongr
      _ = C_geo_local * K_P * δ_n^(-u + heavySlack) := by
        dsimp only [τ]
        have h_exp : (-u / 2 : ℝ) + (-u / 2 + heavySlack) = -u + heavySlack := by ring
        have h_rpow : δ_n^(-u / 2) * δ_n^(-u / 2 + heavySlack) =
            δ_n^((-u / 2 : ℝ) + (-u / 2 + heavySlack)) :=
          (Real.rpow_add hδ_n_pos (-u / 2) (-u / 2 + heavySlack)).symm
        have h : C_geo_local * (K_P * δ_n^(-u / 2)) * τ =
            C_geo_local * K_P * (δ_n^(-u / 2) * δ_n^(-u / 2 + heavySlack)) := by ring
        rw [h, h_rpow, h_exp] <;> ring
    have h11 : C_geo_local * K_P * δ_n^(-u + heavySlack) < (config.P₀.card : ℝ) / 2 := by
      have h12 := hP0_lower
      have h13 : 0 < C_geo_local := by norm_num [C_geo_local]
      nlinarith
    exact lt_of_le_of_lt h_light_sum (lt_of_le_of_lt h10 h11)

  let P0_heavy : Finset (DyadicSquare n) :=
    config.P₀.filter (fun p => InductionConfigurations.containingSquare hnm' p ∈ heavyParents)

  have hP0_heavy_sub : P0_heavy ⊆ config.P₀ := Finset.filter_subset _ _

  have h_light_card : (P0_heavy.card : ℝ) = ∑ Q ∈ heavyParents, (countInParent Q : ℝ) := by
    have h_partition_heavy : P0_heavy = heavyParents.biUnion
        (fun Q => config.P₀.filter (fun p => InductionConfigurations.containingSquare hnm' p = Q)) := by
      ext p
      simp only [P0_heavy, Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · rintro ⟨hp, hQ⟩
        let Q := InductionConfigurations.containingSquare hnm' p
        exact ⟨Q, hQ, hp, rfl⟩
      · rintro ⟨Q, hQ, hp, h_eq⟩
        have hQ' : InductionConfigurations.containingSquare hnm' p ∈ heavyParents := by
          rw [h_eq] <;> exact hQ
        exact ⟨hp, hQ'⟩
    have h_disj_fibers : ∀ Q1 ∈ heavyParents, ∀ Q2 ∈ heavyParents, Q1 ≠ Q2 →
        Disjoint (config.P₀.filter (fun p => InductionConfigurations.containingSquare hnm' p = Q1))
                  (config.P₀.filter (fun p => InductionConfigurations.containingSquare hnm' p = Q2)) := by
      intro Q1 _ Q2 _ hne
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      have h1 : InductionConfigurations.containingSquare hnm' p = Q1 := (Finset.mem_filter.mp hp1).2
      have h2 : InductionConfigurations.containingSquare hnm' p = Q2 := (Finset.mem_filter.mp hp2).2
      rw [h1] at h2
      exact hne h2
    have h_card : P0_heavy.card = ∑ Q ∈ heavyParents,
        (config.P₀.filter (fun p => InductionConfigurations.containingSquare hnm' p = Q)).card := by
      rw [h_partition_heavy, Finset.card_biUnion h_disj_fibers]
    have h_cast : (P0_heavy.card : ℝ) = ∑ Q ∈ heavyParents,
        ↑((config.P₀.filter (fun p => InductionConfigurations.containingSquare hnm' p = Q)).card) := by
      rw [h_card, Nat.cast_sum] <;> rfl
    rw [h_cast]
    apply Finset.sum_congr rfl
    intro Q _
    have h_eq_filter : config.P₀.filter (fun p => InductionConfigurations.containingSquare hnm' p = Q) =
        config.P₀.filter (fun p => squareContained hnm' p Q) := by
      ext p
      simp only [Finset.mem_filter]
      <;> rw [containingSquare_iff hnm' p Q]
    rw [h_eq_filter] <;> rfl

  have h_heavy_mass : (P0_heavy.card : ℝ) > (config.P₀.card : ℝ) / 2 := by
    have h_sum_light : ∑ Q ∈ lightParents, (countInParent Q : ℝ) < (config.P₀.card : ℝ) / 2 := h_light_half
    have h_disj' : Disjoint lightParents heavyParents := h_disj
    have h_union : lightParents ∪ heavyParents = occupiedParents := by
      ext Q
      simp only [Finset.mem_union]
      constructor
      · rintro (h | h)
        · exact (Finset.mem_filter.mp h).1
        · exact (Finset.mem_filter.mp h).1
      · intro hQ
        exact h_partition Q hQ
    have h_sum_total : ∑ Q ∈ occupiedParents, (countInParent Q : ℝ) =
        (∑ Q ∈ lightParents, (countInParent Q : ℝ)) + (∑ Q ∈ heavyParents, (countInParent Q : ℝ)) := by
      rw [←Finset.sum_union h_disj', h_union]
    have h_eq_total : (config.P₀.card : ℝ) =
        (∑ Q ∈ lightParents, (countInParent Q : ℝ)) + (∑ Q ∈ heavyParents, (countInParent Q : ℝ)) := by
      linarith [h_sum_all, h_sum_total]
    linarith [h_light_card, h_eq_total]

  have h_retention : (config.P₀.card : ℝ) ≤ 2 * (P0_heavy.card : ℝ) := by
    have h : (P0_heavy.card : ℝ) > (config.P₀.card : ℝ) / 2 := h_heavy_mass
    linarith

  have hP0_heavy_nonempty : P0_heavy.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at h_heavy_mass
    simp at h_heavy_mass <;> linarith

  -- Step 2: Apply point fiber uniformization to P0_heavy
  let Q0_heavy : Finset (DyadicSquare m) :=
    P0_heavy.image (InductionConfigurations.containingSquare hnm')

  have hQ0_heavy_eq : Q0_heavy = heavyParents := by
    ext Q
    simp only [Q0_heavy, Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (Finset.mem_filter.mp hp).2
    · intro hQ
      have hQ' : Q ∈ occupiedParents := (Finset.mem_filter.mp hQ).1
      have h_count : (countInParent Q : ℝ) ≥ τ := (Finset.mem_filter.mp hQ).2
      have h_nonempty : (config.P₀.filter (fun p => squareContained hnm' p Q)).Nonempty := by
        by_contra h
        have h0 : (config.P₀.filter (fun p => squareContained hnm' p Q)).card = 0 := by
          simpa using h
        have h_count0 : (countInParent Q : ℝ) = 0 := by
          simpa [countInParent] using congr_arg (fun x : ℕ => (x : ℝ)) h0
        rw [h_count0] at h_count
        simp at h_count <;> linarith
      rcases h_nonempty with ⟨p, hp⟩
      have hsc : squareContained hnm' p Q := (Finset.mem_filter.mp hp).2
      have h_eq : InductionConfigurations.containingSquare hnm' p = Q :=
        (h_containment_iff p Q).mp hsc
      have hp_heavy : p ∈ P0_heavy := by
        simp only [P0_heavy, Finset.mem_filter]
        exact ⟨(Finset.mem_filter.mp hp).1, h_eq ▸ hQ⟩
      exact ⟨p, hp_heavy, h_eq⟩

  let N_max : ℕ := config.P₀.card
  have hN_max_pos : 0 < N_max := by
    have h_pos : 0 < (config.P₀.card : ℝ) := by
      have h_rhs_pos : 0 < 2 * C_geo_local * K_P * (dyadicDelta n)^(-u + heavySlack) := by positivity
      linarith [hP0_lower]
    exact_mod_cast h_pos

  have h_fiber_bound : ∀ Q ∈ Q0_heavy,
      (P0_heavy.filter (fun p => squareContained hnm' p Q)).card ≤ N_max := by
    intro Q _
    have h : P0_heavy.filter (fun p => squareContained hnm' p Q) ⊆ P0_heavy := Finset.filter_subset _ _
    have h2 : (P0_heavy.filter (fun p => squareContained hnm' p Q)).card ≤ P0_heavy.card := Finset.card_le_card h
    have h3 : P0_heavy.card ≤ config.P₀.card := Finset.card_le_card hP0_heavy_sub
    exact le_trans h2 h3

  have h_fiber_pos : ∀ Q ∈ Q0_heavy,
      0 < (P0_heavy.filter (fun p => squareContained hnm' p Q)).card := by
    intro Q hQ
    have hQ_heavy : Q ∈ heavyParents := by
      rw [hQ0_heavy_eq] at hQ; exact hQ
    have h_count : (countInParent Q : ℝ) ≥ τ := (Finset.mem_filter.mp hQ_heavy).2
    have h_filter_eq : P0_heavy.filter (fun p => squareContained hnm' p Q) =
        config.P₀.filter (fun p => squareContained hnm' p Q) := by
      apply Finset.ext
      intro p
      simp only [P0_heavy, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hp, _⟩, hsc⟩
        exact ⟨hp, hsc⟩
      · rintro ⟨hp, hsc⟩
        have h3 : InductionConfigurations.containingSquare hnm' p = Q :=
          (h_containment_iff p Q).mp hsc
        exact ⟨⟨hp, h3 ▸ hQ_heavy⟩, hsc⟩
    have h_eq : (P0_heavy.filter (fun p => squareContained hnm' p Q)).card = countInParent Q := by
      rw [h_filter_eq] <;> rfl
    rw [h_eq]
    have h_pos : 0 < (countInParent Q : ℝ) := by linarith [hτ_pos]
    exact_mod_cast h_pos

  have h_main := point_fiber_uniformization hnm' (rfl) h_fiber_pos N_max h_fiber_bound
  rcases h_main with ⟨M_fiber, Q_uniform, P_uniform, h_rest⟩
  have hQ_sub : Q_uniform ⊆ Q0_heavy := h_rest.1
  have hP_filter_eq : P_uniform = P0_heavy.filter (fun p => containingSquare hnm' p ∈ Q_uniform) := h_rest.2.1
  have hP_sub : P_uniform ⊆ P0_heavy := h_rest.2.2.1
  have h_uniform : ∀ Q ∈ Q_uniform, M_fiber ≤ (P_uniform.filter (fun p => squareContained hnm' p Q)).card ∧ (P_uniform.filter (fun p => squareContained hnm' p Q)).card < 2 * M_fiber := h_rest.2.2.2.1
  have hQ_density : (Q0_heavy.card : ℝ) ≤ (2 * (M_fiber : ℝ) * (numDyadicLevels N_max : ℝ)) * (Q_uniform.card : ℝ) := h_rest.2.2.2.2.1
  have hP_retention : (P_uniform.card : ℝ) ≥ (P0_heavy.card : ℝ) / (numDyadicLevels N_max : ℝ) := h_rest.2.2.2.2.2

  have hP_uniform_sub : P_uniform ⊆ config.P₀ := by
    exact Finset.Subset.trans hP_sub hP0_heavy_sub

  let L : ℝ := (numDyadicLevels N_max : ℝ)
  have hL_pos : 0 < L := by
    dsimp only [L]
    have h : 0 < numDyadicLevels N_max := by
      apply Nat.pos_of_ne_zero
      intro hz
      have h_def : numDyadicLevels N_max = Nat.log 2 N_max + 2 := by
        simp [numDyadicLevels, hN_max_pos.ne']
      rw [h_def] at hz
      exact False.elim (by linarith)
    exact_mod_cast h

  have h_heavy_retention : (P0_heavy.card : ℝ) ≤ L * (P_uniform.card : ℝ) := by
    have h : (P_uniform.card : ℝ) ≥ (P0_heavy.card : ℝ) / L := hP_retention
    have hLpos : (0 : ℝ) < L := hL_pos
    calc (P0_heavy.card : ℝ)
      = L * ((P0_heavy.card : ℝ) / L) := by field_simp [hLpos.ne'] <;> ring
    _ ≤ L * (P_uniform.card : ℝ) := by gcongr

  have h_global_ret : (config.P₀.card : ℝ) ≤ (2 * L) * (P_uniform.card : ℝ) := by
    calc (config.P₀.card : ℝ)
      ≤ 2 * (P0_heavy.card : ℝ) := h_retention
    _ ≤ 2 * (L * (P_uniform.card : ℝ)) := by gcongr
    _ = (2 * L) * (P_uniform.card : ℝ) := by ring

  have hQ_uniform_eq : Q_uniform = P_uniform.image (InductionConfigurations.containingSquare hnm') := by
    apply Finset.Subset.antisymm
    · intro Q hQ
      have h_fiber_nonempty : (P_uniform.filter (fun p => squareContained hnm' p Q)).Nonempty := by
        have h_card : 0 < (P_uniform.filter (fun p => squareContained hnm' p Q)).card := by
          have h1 : M_fiber ≤ (P_uniform.filter (fun p => squareContained hnm' p Q)).card := (h_uniform Q hQ).1
          have hM_pos : 0 < M_fiber := by
            by_contra hM
            have hM0 : M_fiber = 0 := by omega
            have h2 : (P_uniform.filter (fun p => squareContained hnm' p Q)).card < 2 * M_fiber := (h_uniform Q hQ).2
            rw [hM0] at h2
            omega
          exact lt_of_lt_of_le hM_pos h1
        exact Finset.card_pos.mp h_card
      rcases h_fiber_nonempty with ⟨p, hp⟩
      have hsc : squareContained hnm' p Q := (Finset.mem_filter.mp hp).2
      have h_eq : InductionConfigurations.containingSquare hnm' p = Q := (h_containment_iff p Q).mp hsc
      have hp' : p ∈ P_uniform := (Finset.mem_filter.mp hp).1
      exact Finset.mem_image.mpr ⟨p, hp', h_eq⟩
    · intro Q hQ
      rcases Finset.mem_image.mp hQ with ⟨p, hp, rfl⟩
      have h_in : InductionConfigurations.containingSquare hnm' p ∈ Q_uniform := by
        rw [hP_filter_eq] at hp
        exact (Finset.mem_filter.mp hp).2
      exact h_in

  -- Fiber bounds for Q_uniform
  have h_fiber_bounds : ∀ Q ∈ Q_uniform,
      (M_fiber : ℝ) ≤ ((P_uniform.filter (fun p => squareContained hnm' p Q)).card : ℝ) ∧
      τ ≤ ((P_uniform.filter (fun p => squareContained hnm' p Q)).card : ℝ) ∧
      ((P_uniform.filter (fun p => squareContained hnm' p Q)).card : ℝ) < 2 * (M_fiber : ℝ) := by
    intro Q hQ
    have h_uniform' : M_fiber ≤ (P_uniform.filter (fun p => squareContained hnm' p Q)).card ∧
        (P_uniform.filter (fun p => squareContained hnm' p Q)).card < 2 * M_fiber := h_uniform Q hQ
    have h_fiber_eq : (P_uniform.filter (fun p => squareContained hnm' p Q)).card =
        (P0_heavy.filter (fun p => squareContained hnm' p Q)).card := by
      have h_eq : P_uniform.filter (fun p => squareContained hnm' p Q) =
          P0_heavy.filter (fun p => squareContained hnm' p Q) := by
        apply Finset.ext
        intro p
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hp, hsc⟩
          exact ⟨hP_sub hp, hsc⟩
        · rintro ⟨hp, hsc⟩
          have h3 : InductionConfigurations.containingSquare hnm' p = Q :=
            (h_containment_iff p Q).mp hsc
          have h4 : p ∈ P_uniform := by
            rw [hP_filter_eq]
            simp only [Finset.mem_filter]
            exact ⟨hp, h3 ▸ hQ⟩
          exact ⟨h4, hsc⟩
      rw [h_eq]
    rw [h_fiber_eq]
    have h_heavy : Q ∈ Q0_heavy := by
      have h : Q_uniform ⊆ Q0_heavy := hQ_sub
      exact h hQ
    have hQ_heavy' : Q ∈ heavyParents := by
      rw [hQ0_heavy_eq] at h_heavy; exact h_heavy
    have h_count_ge : (countInParent Q : ℝ) ≥ τ := by
      exact (Finset.mem_filter.mp hQ_heavy').2
    have h_fiber_eq2 : (P0_heavy.filter (fun p => squareContained hnm' p Q)).card = countInParent Q := by
      have h_filter_eq : P0_heavy.filter (fun p => squareContained hnm' p Q) =
          config.P₀.filter (fun p => squareContained hnm' p Q) := by
        apply Finset.ext
        intro p
        simp only [P0_heavy, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hp, _⟩, hsc⟩
          exact ⟨hp, hsc⟩
        · rintro ⟨hp, hsc⟩
          have h3 : InductionConfigurations.containingSquare hnm' p = Q :=
            (h_containment_iff p Q).mp hsc
          exact ⟨⟨hp, h3 ▸ hQ_heavy'⟩, hsc⟩
      rw [h_filter_eq] <;> rfl
    have h_upper : ((P0_heavy.filter (fun p => squareContained hnm' p Q)).card : ℝ) < 2 * (M_fiber : ℝ) := by
      rw [←h_fiber_eq]
      exact_mod_cast h_uniform'.2
    have h_goal : (countInParent Q : ℝ) < 2 * (M_fiber : ℝ) := by
      rw [←h_fiber_eq2]
      exact h_upper
    have h_M_lower : (M_fiber : ℝ) ≤ (countInParent Q : ℝ) := by
      have h1 : M_fiber ≤ (P_uniform.filter (fun p => squareContained hnm' p Q)).card := h_uniform'.1
      have h2 : (P_uniform.filter (fun p => squareContained hnm' p Q)).card = countInParent Q := by
        rw [h_fiber_eq, h_fiber_eq2]
      rw [h2] at h1
      exact_mod_cast h1
    rw [h_fiber_eq2]
    exact ⟨h_M_lower, h_count_ge, h_goal⟩

  -- Step 3: Transfer regularity
  have hP_uniform_nonempty : P_uniform.Nonempty := by
    by_contra h
    have h_empty : P_uniform = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hP0_heavy_pos : 0 < (P0_heavy.card : ℝ) := by
      exact_mod_cast hP0_heavy_nonempty.card_pos
    have h_contra : (P0_heavy.card : ℝ) / L > 0 := div_pos hP0_heavy_pos hL_pos
    rw [h_empty] at hP_retention
    have h' : (0 : ℝ) ≥ (P0_heavy.card : ℝ) / L := by simpa using hP_retention
    linarith

  have h_reg_uniform : IsSquareRootRegular (dyadicDelta n) u
      (C_P * 9 * (2 * L)) K_P
      (⋃ p ∈ (P_uniform : Set (DyadicSquare n)), (p.toSet : Set Plane)) :=
    global_retained_regular_clean
      (hReg := h_point_regular)
      (P := P_uniform)
      (hP_sub := hP_uniform_sub)
      (K_global := 2 * L)
      (by positivity)
      h_global_ret
      hP_uniform_nonempty

  have h_const_eq : C_P * 9 * (2 * L) = C_P * 18 * L := by ring
  rw [h_const_eq] at h_reg_uniform

  exact ⟨P_uniform, M_fiber, Q_uniform,
    hP_uniform_sub, h_global_ret, hQ_uniform_eq, h_fiber_bounds, h_reg_uniform⟩

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
