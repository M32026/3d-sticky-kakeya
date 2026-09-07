module

/-
  Coarse Normal Bound — Polylog version

  Source-consumable coarse bound for a NORMAL first scale.

  Unlike CoarseNormalBoundHelper (which requires impossible power-smallness
  Δ^ε_N ≤ const/C_P), this version absorbs C_P_coarse into the log exponent
  via h_absorb: LΔ^(C_coarse - K_p5) ≥ K_p5 * C_P_coarse * 13 * 2^s * Δ^ε_N.

  This h_absorb follows from source data:
  - C_P_coarse ≤ log(1/δ)^C_P * Δ^(-ε_N)  (h_C_between_normal at j=0)
  - Δ ≤ δ^τ ⇒ log(1/δ) ≤ (1/τ) * log(1/Δ)
  - Choose C_coarse ≥ K_p5 + C_P + D_fixed with δ₀ smallness.

  Whiteprint node: combining_theorem_genuine / inductive_step (coarse bound)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformProp5
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformProp5Wrapper
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DirecretisedFurstenbergEstimate.FormatConversion.M2

/-- Coarse bound for a NORMAL first scale — polylog absorption version.

    C_coarse ≥ K_p5 absorbs the C_P_coarse polylog factor into the log exponent.
    h_absorb is the key absorption condition, provable from source data. -/
lemma coarse_normal_bound_polylog
    {m : ℕ} {s ε_N lam δ Δ_coarse : ℝ} {MΔ : ℕ}
    {CΔ C_P_coarse K_B1 K_p5 C_coarse C'_coarse : ℝ}
    {coarseConfig : CTMainConfig m s CΔ MΔ}
    -- uniform_prop5 constant
    (hK_p5_pos : 0 < K_p5)
    (hK_p5_ge1 : 1 ≤ K_p5)
    (hK_p5_spec : ∀ (C_P C_T M : ℝ),
      0 < C_P → 1 ≤ C_P → 0 < C_T → 1 ≤ C_T → 1 ≤ M → 2 ≤ m →
      ∀ (P : Finset (DSquare m)), P.Nonempty →
        IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ m) s C_P P →
        (∀ (x y : DSquare m), x ∈ P → y ∈ P → dist x y ≤ 3) →
        (∀ p ∈ P, ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1) →
        ∀ (Tp : TubeFamily m),
          (∀ p ∈ P, ∀ T ∈ Tp p, (T.toSet ∩ p.toSet).Nonempty) →
          (∀ p ∈ P, ∀ T ∈ Tp p, |T.slope| ≤ 1) →
          (∀ p ∈ P, IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ m) s C_T (Tp p)) →
          (∀ p ∈ P, (M : ℝ) / 2 < (Tp p).card ∧ (Tp p).card ≤ M) →
            let T := P.biUnion fun p => Tp p
            (T.card : ℝ) ≥ (1 / K_p5) * Real.log (1 / DiscretisedFurstenbergEstimate.δ m) ^ (-K_p5) *
              (1 / (C_P * C_T)) * M * (DiscretisedFurstenbergEstimate.δ m) ^ (-s) *
                (M * (DiscretisedFurstenbergEstimate.δ m) ^ s) ^ ((s - s) / (1 - s)))
    -- B1 bridge constant
    (hK_B1_ge1 : 1 ≤ K_B1)
    -- Actual coarse tube constant with B1 bound
    (hCΔ_pos : 0 < CΔ)
    (hCΔ_ge1 : 1 ≤ CΔ)
    (hCΔ_le : CΔ ≤ K_B1 * Real.rpow δ (-lam))
    -- Coarse exponents
    (hC_coarse_ge : C_coarse ≥ K_p5)
    (hC'_coarse_ge1 : 1 ≤ C'_coarse)
    -- scale data
    (hm_ge2 : 2 ≤ m)
    (hΔ_coarse_eq : Δ_coarse = dyadicDelta m)
    (hΔ_coarse_pos : 0 < Δ_coarse)
    (hΔ_coarse_lt_one : Δ_coarse < 1)
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hlam : 0 < lam)
    (hs : 0 < s)
    (hεN : 0 < ε_N)
    -- coarse S-set and geometric data
    (hCP_coarse_pos : 0 < C_P_coarse)
    (hCP_coarse_ge1 : 1 ≤ C_P_coarse)
    (hP_nonempty : coarseConfig.P₀.Nonempty)
    (hMΔ_pos : 0 < MΔ)
    (hP_set_coarse : IsFinsetDeltaSSet (dyadicDelta m) s C_P_coarse
      (finsetDyadicToDSquare coarseConfig.P₀))
    (h_slope_coarse : ∀ T ∈ coarseConfig.T₀, |T.slope| ≤ 1)
    (h_diam_coarse : ∀ (p q : DSquare m),
      p ∈ finsetDyadicToDSquare coarseConfig.P₀ →
      q ∈ finsetDyadicToDSquare coarseConfig.P₀ → dist p q ≤ 3)
    (h_unit_coarse : ∀ (p : DSquare m), p ∈ finsetDyadicToDSquare coarseConfig.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1)
    -- Polylog absorption:
    -- LΔ^(C_coarse - K_p5) ≥ K_p5 * C_P_coarse * 13 * 2^s * Δ^ε_N
    (h_absorb : Real.rpow (Real.log (1 / Δ_coarse)) (C_coarse - K_p5) ≥
       K_p5 * C_P_coarse * 13 * Real.rpow 2 s * Real.rpow Δ_coarse ε_N) :
    (coarseConfig.T₀.card : ℝ) ≥
      Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
      Real.rpow K_B1 (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
      Real.rpow Δ_coarse (-s + ε_N) := by
  classical
  set Lc : ℝ := Real.log (1 / Δ_coarse) with hLc_def
  set C_T : ℝ := 13 * CΔ * Real.rpow 2 s with hCT_def
  have hδ_eq : dyadicDelta m = Δ_coarse := hΔ_coarse_eq.symm
  have hδEI_eq : DiscretisedFurstenbergEstimate.δ m = dyadicDelta m := by
    simp [DiscretisedFurstenbergEstimate.δ, dyadicDelta] <;> ring
  have hLc_pos : 0 < Lc := by
    rw [hLc_def]
    apply Real.log_pos
    apply one_lt_one_div hΔ_coarse_pos hΔ_coarse_lt_one
  have hK_B1_pos : 0 < K_B1 := by linarith
  have h2s_pos : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s
  have hCT_pos : 0 < C_T := by
    rw [hCT_def]
    positivity
  have hCT_ge1 : 1 ≤ C_T := by
    rw [hCT_def]
    have h1 : 1 ≤ CΔ := hCΔ_ge1
    have h2 : 1 ≤ Real.rpow 2 s := by
      apply Real.one_le_rpow <;> norm_num <;> linarith
    nlinarith
  -- Step 1: Apply uniform_prop5 at t=s
  have h_main : (coarseConfig.T₀.card : ℝ) ≥
      (1 / K_p5) * Real.rpow (Real.log (1 / dyadicDelta m)) (-K_p5) *
        (1 / (C_P_coarse * C_T)) * (MΔ : ℝ) * (dyadicDelta m) ^ (-s) := by
    have h_wrapper := uniform_prop5_wrapper_with_K
      (t := s) (hK_pos := hK_p5_pos) (hK_spec := hK_p5_spec)
      (config := coarseConfig) (hn_ge_2 := hm_ge2) (hM_pos := hMΔ_pos)
      (hP_nonempty := hP_nonempty) (hCP := hCP_coarse_pos) (hCP_ge1 := hCP_coarse_ge1)
      (hC₁ := hCΔ_pos) (hC1_ge1 := hCΔ_ge1)
      (hs_nonneg := by linarith) (hP_set := hP_set_coarse)
      (h_slope := h_slope_coarse) (h_diam := h_diam_coarse) (h_unit := h_unit_coarse)
    convert h_wrapper using 1
    <;> simp [hCT_def, hδEI_eq] <;> ring
  rw [hδ_eq] at h_main
  -- Step 2: 1/C_T ≥ δ^lam / (13 * K_B1 * 2^s)
  have h_bound_CT : C_T ≤ 13 * K_B1 * Real.rpow δ (-lam) * Real.rpow 2 s := by
    rw [hCT_def]
    have h2 : CΔ ≤ K_B1 * Real.rpow δ (-lam) := hCΔ_le
    nlinarith
  have h_rpow_neg : Real.rpow δ (-lam) = (Real.rpow δ lam)⁻¹ := by
    have h : Real.rpow δ (-lam) = 1 / Real.rpow δ lam := by
      simpa [Real.rpow_neg hδ_pos.le] using rfl
    rw [h] <;> ring
  have h1_inv : (1 : ℝ) / C_T ≥
      Real.rpow δ lam / (13 * K_B1 * Real.rpow 2 s) := by
    have h_pos2 : 0 < 13 * K_B1 * Real.rpow δ (-lam) * Real.rpow 2 s := by
      have h1 : 0 < K_B1 := hK_B1_pos
      have h2 : 0 < Real.rpow δ (-lam) := Real.rpow_pos_of_pos hδ_pos _
      positivity
    have h3 : 1 / C_T ≥ 1 / (13 * K_B1 * Real.rpow δ (-lam) * Real.rpow 2 s) :=
      one_div_le_one_div_of_le (by positivity) h_bound_CT
    have h4 : 1 / (13 * K_B1 * Real.rpow δ (-lam) * Real.rpow 2 s) =
        Real.rpow δ lam / (13 * K_B1 * Real.rpow 2 s) := by
      rw [h_rpow_neg]
      field_simp [hK_B1_pos.ne', h2s_pos.ne'] <;> ring
    rw [h4] at h3
    exact h3
  -- Step 3: Weaken K_B1 and δ factors
  have hK_weaken : Real.rpow K_B1 (-C'_coarse) ≤ (1 / K_B1 : ℝ) := by
    have h6 : -C'_coarse ≤ -1 := by linarith
    have h7 : Real.rpow K_B1 (-C'_coarse) ≤ Real.rpow K_B1 (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hK_B1_ge1 h6
    have h8 : Real.rpow K_B1 (-1 : ℝ) = (Real.rpow K_B1 (1 : ℝ))⁻¹ := by
      simpa [Real.rpow_neg hK_B1_pos.le] using rfl
    have h9 : Real.rpow K_B1 (1 : ℝ) = K_B1 := by simp
    have h10 : Real.rpow K_B1 (-1 : ℝ) = 1 / K_B1 := by
      rw [h8, h9] <;> ring
    rw [h10] at h7
    exact h7
  have hδ_weaken : Real.rpow δ (C'_coarse * lam) ≤ Real.rpow δ lam := by
    have h7 : C'_coarse * lam ≥ lam := by
      have h8 : C'_coarse ≥ 1 := hC'_coarse_ge1
      nlinarith
    have h10 : 0 < δ := hδ_pos
    have h11 : δ < 1 := hδ_lt_one
    have h12 : Real.rpow δ (C'_coarse * lam) ≤ Real.rpow δ lam :=
      Real.rpow_le_rpow_of_exponent_ge h10 h11.le h7
    exact h12
  -- Step 4: Polylog absorption
  -- h_absorb: Lc^(C_coarse-K_p5) ≥ K_p5 * C_P_coarse * 13 * 2^s * Δ^ε_N
  -- Equivalently: 1/(K_p5*C_P_coarse*13*2^s) ≥ Lc^(-(C_coarse-K_p5)) * Δ^ε_N
  --                        = Lc^(K_p5-C_coarse) * Δ^ε_N
  have h_const_absorb : (1 : ℝ) / (K_p5 * C_P_coarse * 13 * Real.rpow 2 s) ≥
      Real.rpow Lc (K_p5 - C_coarse) * Real.rpow Δ_coarse ε_N := by
    set A : ℝ := K_p5 * C_P_coarse * 13 * Real.rpow 2 s with hA_def
    have hA_pos : 0 < A := by positivity
    set X : ℝ := Real.rpow Lc (C_coarse - K_p5) with hX_def
    have hX_pos : 0 < X := Real.rpow_pos_of_pos hLc_pos _
    set Y : ℝ := Real.rpow Δ_coarse ε_N with hY_def
    have hY_pos : 0 < Y := Real.rpow_pos_of_pos hΔ_coarse_pos _
    have h_absorb' : X ≥ A * Y := by
      simpa [hA_def, hX_def, hY_def] using h_absorb
    have h_main_goal : 1 / A ≥ X⁻¹ * Y := by
      have h : X ≥ A * Y := h_absorb'
      have h2 : X⁻¹ ≤ (A * Y)⁻¹ := by
        gcongr
      have h3 : (A * Y)⁻¹ = A⁻¹ * Y⁻¹ := by
        field_simp [hA_pos.ne', hY_pos.ne'] <;> ring
      rw [h3] at h2
      have h4 : X⁻¹ ≤ A⁻¹ * Y⁻¹ := h2
      have h5 : X⁻¹ * Y ≤ A⁻¹ := by
        calc
          X⁻¹ * Y ≤ (A⁻¹ * Y⁻¹) * Y := by gcongr
          _ = A⁻¹ := by
            field_simp [hY_pos.ne'] <;> ring
      simpa [hA_def] using h5
    have h6 : Real.rpow Lc (K_p5 - C_coarse) = X⁻¹ := by
      have h7 : K_p5 - C_coarse = -(C_coarse - K_p5) := by ring
      rw [h7]
      have h8 : Real.rpow Lc (-(C_coarse - K_p5)) = (Real.rpow Lc (C_coarse - K_p5))⁻¹ := by
        exact Real.rpow_neg hLc_pos.le (C_coarse - K_p5)
      exact h8
    rw [h6]
    exact h_main_goal
  -- Main absorption inequality:
  -- (1/K_p5) * Lc^(-K_p5) * (1/(C_P_coarse*C_T))
  --   ≥ Lc^(-C_coarse) * K_B1^(-C'_coarse) * δ^(C'_coarse*lam) * Δ^ε_N
  have h_absorb_main : (1 / K_p5) * Real.rpow Lc (-K_p5) * (1 / (C_P_coarse * C_T)) ≥
      Real.rpow Lc (-C_coarse) * Real.rpow K_B1 (-C'_coarse) *
        Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse ε_N := by
    have h_pos1 : 0 < (1 / K_p5) * Real.rpow Lc (-K_p5) * (1 / C_P_coarse) := by
      have h1 : 0 < (1 / K_p5) := by positivity
      have h2 : 0 < Real.rpow Lc (-K_p5) := Real.rpow_pos_of_pos hLc_pos _
      have h3 : 0 < (1 / C_P_coarse) := by positivity
      exact mul_pos (mul_pos h1 h2) h3
    have h_split2 : (1 / (C_P_coarse * C_T)) = (1 / C_P_coarse) * (1 / C_T) := by
      field_simp [hCP_coarse_pos.ne', hCT_pos.ne'] <;> ring
    have h_step1 : (1 / K_p5) * Real.rpow Lc (-K_p5) * (1 / (C_P_coarse * C_T)) ≥
        (1 / (K_p5 * C_P_coarse * 13 * Real.rpow 2 s)) *
          Real.rpow Lc (-K_p5) * (1 / K_B1) * Real.rpow δ lam := by
      rw [h_split2]
      have h_goal : (1 / K_p5) * Real.rpow Lc (-K_p5) * (1 / C_P_coarse) * (1 / C_T) ≥
          (1 / K_p5) * Real.rpow Lc (-K_p5) * (1 / C_P_coarse) *
            (Real.rpow δ lam / (13 * K_B1 * Real.rpow 2 s)) := by
        gcongr
        <;> exact h1_inv
      have h_eq : (1 / K_p5) * Real.rpow Lc (-K_p5) * (1 / C_P_coarse) *
            (Real.rpow δ lam / (13 * K_B1 * Real.rpow 2 s)) =
          (1 / (K_p5 * C_P_coarse * 13 * Real.rpow 2 s)) *
            Real.rpow Lc (-K_p5) * (1 / K_B1) * Real.rpow δ lam := by ring
      rw [h_eq] at h_goal
      have h_assoc : (1 / K_p5) * Real.rpow Lc (-K_p5) * (1 / C_P_coarse) * (1 / C_T) =
          (1 / K_p5) * Real.rpow Lc (-K_p5) * ((1 / C_P_coarse) * (1 / C_T)) := by ring
      rw [h_assoc] at h_goal
      exact h_goal
    -- Now absorb: Lc^(-K_p5) * const ≥ Lc^(-C_coarse) * K_B1^(-C'_coarse) * δ^(C'_coarse*lam) * Δ^ε_N
    -- We have: const = 1/(K_p5*C_P_coarse*13*2^s) * (1/K_B1) * δ^lam
    -- And: const ≥ Lc^(K_p5-C_coarse) * Δ^ε_N * (1/K_B1) * δ^lam  (from h_const_absorb)
    -- Then weaken (1/K_B1) to K_B1^(-C'_coarse), δ^lam to δ^(C'_coarse*lam)
    have h_posLcK : 0 < Real.rpow Lc (K_p5 - C_coarse) :=
      Real.rpow_pos_of_pos hLc_pos _
    have h_goal2 : (1 / (K_p5 * C_P_coarse * 13 * Real.rpow 2 s)) * (1 / K_B1) * Real.rpow δ lam ≥
        Real.rpow Lc (K_p5 - C_coarse) * Real.rpow K_B1 (-C'_coarse) *
          Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse ε_N := by
      set X1 := (1 / (K_p5 * C_P_coarse * 13 * Real.rpow 2 s)) with hX1_def
      set Y1 := Real.rpow Lc (K_p5 - C_coarse) * Real.rpow Δ_coarse ε_N with hY1_def
      set X2 := (1 / K_B1 : ℝ) with hX2_def
      set Y2 := Real.rpow K_B1 (-C'_coarse) with hY2_def
      set X3 := Real.rpow δ lam with hX3_def
      set Y3 := Real.rpow δ (C'_coarse * lam) with hY3_def
      have hY1_pos : 0 < Y1 := mul_pos h_posLcK (Real.rpow_pos_of_pos hΔ_coarse_pos _)
      have hY2_pos : 0 < Y2 := Real.rpow_pos_of_pos hK_B1_pos _
      have hY3_pos : 0 < Y3 := Real.rpow_pos_of_pos hδ_pos _
      have hX1_pos : 0 < X1 := by positivity
      have hX2_pos : 0 < X2 := by positivity
      have hX3_pos : 0 < X3 := Real.rpow_pos_of_pos hδ_pos _
      have h1 : X1 ≥ Y1 := h_const_absorb
      have h2 : X2 ≥ Y2 := hK_weaken
      have h3 : X3 ≥ Y3 := hδ_weaken
      have h4 : X1 * X2 ≥ Y1 * Y2 := mul_le_mul h1 h2 (by positivity) (by positivity)
      have h5 : X1 * X2 * X3 ≥ Y1 * Y2 * Y3 :=
        mul_le_mul h4 h3 (by positivity) (by positivity)
      have h6 : Y1 * Y2 * Y3 = Real.rpow Lc (K_p5 - C_coarse) * Real.rpow K_B1 (-C'_coarse) *
          Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse ε_N := by
        simp only [hY1_def, hY2_def, hY3_def] <;> ring
      rw [h6] at h5
      exact h5
    have h_posLc_negK : 0 < Real.rpow Lc (-K_p5) := Real.rpow_pos_of_pos hLc_pos _
    have h_product : Real.rpow Lc (-K_p5) * Real.rpow Lc (K_p5 - C_coarse) = Real.rpow Lc (-C_coarse) := by
      have h_add : Real.rpow Lc (-K_p5) * Real.rpow Lc (K_p5 - C_coarse) =
          Real.rpow Lc ((-K_p5) + (K_p5 - C_coarse)) :=
        (Real.rpow_add hLc_pos (-K_p5) (K_p5 - C_coarse)).symm
      rw [h_add]
      have h_sum : (-K_p5) + (K_p5 - C_coarse) = -C_coarse := by ring
      rw [h_sum]
    have h_final_absorb : (1 / (K_p5 * C_P_coarse * 13 * Real.rpow 2 s)) *
          Real.rpow Lc (-K_p5) * (1 / K_B1) * Real.rpow δ lam ≥
        Real.rpow Lc (-C_coarse) * Real.rpow K_B1 (-C'_coarse) *
          Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse ε_N := by
      have h5 : Real.rpow Lc (-K_p5) *
            ((1 / (K_p5 * C_P_coarse * 13 * Real.rpow 2 s)) * (1 / K_B1) * Real.rpow δ lam) ≥
          Real.rpow Lc (-K_p5) *
            (Real.rpow Lc (K_p5 - C_coarse) * Real.rpow K_B1 (-C'_coarse) *
              Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse ε_N) :=
        mul_le_mul_of_nonneg_left h_goal2 h_posLc_negK.le
      have h6 : Real.rpow Lc (-K_p5) *
            (Real.rpow Lc (K_p5 - C_coarse) * Real.rpow K_B1 (-C'_coarse) *
              Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse ε_N) =
          (Real.rpow Lc (-K_p5) * Real.rpow Lc (K_p5 - C_coarse)) *
            (Real.rpow K_B1 (-C'_coarse) * Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse ε_N) := by ring
      have h7 : (Real.rpow Lc (-K_p5) * Real.rpow Lc (K_p5 - C_coarse)) *
            (Real.rpow K_B1 (-C'_coarse) * Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse ε_N) =
          Real.rpow Lc (-C_coarse) * Real.rpow K_B1 (-C'_coarse) *
            Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse ε_N := by
        rw [h_product] <;> ring
      have h8 : (1 / (K_p5 * C_P_coarse * 13 * Real.rpow 2 s)) *
            Real.rpow Lc (-K_p5) * (1 / K_B1) * Real.rpow δ lam =
          Real.rpow Lc (-K_p5) *
            ((1 / (K_p5 * C_P_coarse * 13 * Real.rpow 2 s)) * (1 / K_B1) * Real.rpow δ lam) := by ring
      rw [h8]
      rw [h6, h7] at h5
      exact h5
    exact ge_trans h_step1 h_final_absorb
  -- Step 5: Final combine
  have h_pos_prod : 0 < (MΔ : ℝ) * Real.rpow Δ_coarse (-s) := by
    have h1 : 0 < (MΔ : ℝ) := by exact_mod_cast hMΔ_pos
    have h2 : 0 < Real.rpow Δ_coarse (-s) := Real.rpow_pos_of_pos hΔ_coarse_pos _
    exact mul_pos h1 h2
  have h_final : (coarseConfig.T₀.card : ℝ) ≥
      Real.rpow Lc (-C_coarse) * (MΔ : ℝ) *
      Real.rpow K_B1 (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
      Real.rpow Δ_coarse (-s + ε_N) := by
    calc
      (coarseConfig.T₀.card : ℝ)
        ≥ (1 / K_p5) * Real.rpow Lc (-K_p5) * (1 / (C_P_coarse * C_T)) *
            (MΔ : ℝ) * Real.rpow Δ_coarse (-s) := h_main
      _ = ((1 / K_p5) * Real.rpow Lc (-K_p5) * (1 / (C_P_coarse * C_T))) *
            ((MΔ : ℝ) * Real.rpow Δ_coarse (-s)) := by ring
      _ ≥ (Real.rpow Lc (-C_coarse) * Real.rpow K_B1 (-C'_coarse) *
               Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse ε_N) *
             ((MΔ : ℝ) * Real.rpow Δ_coarse (-s)) := by
        have h : (Real.rpow Lc (-C_coarse) * Real.rpow K_B1 (-C'_coarse) *
                   Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse ε_N) *
                 ((MΔ : ℝ) * Real.rpow Δ_coarse (-s)) ≤
            ((1 / K_p5) * Real.rpow Lc (-K_p5) * (1 / (C_P_coarse * C_T))) *
                 ((MΔ : ℝ) * Real.rpow Δ_coarse (-s)) :=
          mul_le_mul_of_nonneg_right h_absorb_main h_pos_prod.le
        exact h
      _ = Real.rpow Lc (-C_coarse) * (MΔ : ℝ) *
            Real.rpow K_B1 (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
            Real.rpow Δ_coarse (-s + ε_N) := by
        have h_add : Real.rpow Δ_coarse ε_N * Real.rpow Δ_coarse (-s) =
            Real.rpow Δ_coarse (-s + ε_N) := by
          have h : Real.rpow Δ_coarse ε_N * Real.rpow Δ_coarse (-s) =
              Real.rpow Δ_coarse (ε_N + (-s)) :=
            (Real.rpow_add hΔ_coarse_pos ε_N (-s)).symm
          rw [h]
          have h2 : ε_N + (-s) = -s + ε_N := by ring
          rw [h2]
        have h_main_eq : (Real.rpow Lc (-C_coarse) * Real.rpow K_B1 (-C'_coarse) *
                  Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse ε_N) *
                ((MΔ : ℝ) * Real.rpow Δ_coarse (-s)) =
            Real.rpow Lc (-C_coarse) * (MΔ : ℝ) * Real.rpow K_B1 (-C'_coarse) *
              Real.rpow δ (C'_coarse * lam) * (Real.rpow Δ_coarse ε_N * Real.rpow Δ_coarse (-s)) := by ring
        rw [h_main_eq, h_add] <;> ring
  exact h_final

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
