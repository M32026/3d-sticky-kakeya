module

/-
  Good coarse bound helper for inductive_step_core_v2.

  Extracts the m≥2 good first-scale case from core_v2 to avoid
  proof-context timeouts. Constructs the realized coarse S-set constant,
  weakens the fixed-degree polylog absorption hypotheses, and dispatches
  to coarse_source_good_only.

  Budget: C_coarse - K_p5 = C_P + 8 (degree-7 B1 factor + 1 margin).

  The improved incidence bound is taken as a hypothesis for now;
  juniper's GoodCaseImprovedIncidence will supply it.

  Whiteprint node: combining_theorem_rework / good_coarse_bound
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseSourceGood
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.RestructuredStatement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
attribute [local instance] Classical.decEq


noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DirecretisedFurstenbergEstimate.FormatConversion.M2
open DiscretisedFurstenbergEstimate.InductionConfigurations

/-- Coarse bound for m≥2 good first-scale.

    Constructs the realized S-set constant `C_P_coarse_value`, bounds it
    by `Poly(k) * max(C_between 0, 1) * (2√2)`, weakens the caller's
    fixed-degree absorption hypotheses, and dispatches to
    `coarse_source_good_only`. -/
lemma good_coarse_bound
    {n k m M MΔ : ℕ}
    {s t τ ε_G η ε_N ε_inc C_P lam δ Δ_coarse : ℝ}
    {K CΔ C'_coarse K_p5 C_coarse : ℝ}
    {config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M}
    {coarseConfig : CTNiceConfiguration m s CΔ MΔ}
    {scaleClass : Fin n → ScaleClass}
    {j0 : Fin n}
    {Δ : Fin (n + 1) → ℝ}
    {C_between : Fin n → ℝ}
    {N : Fin n → ℕ}
    (t_j : ℝ)
    (hcfg : CombiningConfig s t τ n ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    (hB1 : B1BridgeHypotheses k config)
    (P : Finset (DyadicSquare k))
    (hP_sub : P ⊆ config.P₀)
    (hP_nonempty' : P.Nonempty)
    (hnm : m ≤ k)
    (hcoarse_P_eq : coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hnm))
    (h_card_bound : (config.P₀.image (InductionConfigurations.containingSquare hnm)).card ≤ K * coarseConfig.P₀.card)
    (hj0 : j0.val = 0)
    (h_good : scaleClass j0 = ScaleClass.good t_j)
    (h_tj_ge_t : ∀ (j : Fin n) (t_j' : ℝ), scaleClass j = ScaleClass.good t_j' → t ≤ t_j')
    (hΔ0 : Δ 0 = 1)
    (hΔ1 : Δ 1 = Δ_coarse)
    (hΔ_coarse_eq : Δ_coarse = dyadicDelta m)
    -- Common parameters
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t)
    (hεG : 0 < ε_G) (hη : 0 < η) (hεN : 0 < ε_N)
    (hε_inc : 0 < ε_inc)
    (hτ_pos : 0 < τ) (hCP : 1 ≤ C_P)
    (hlam : 0 < lam)
    (hK_ge1 : 1 ≤ K) (hK_pos : 0 < K)
    (hK_bound : K ≤ (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7)
    (h_poly_K_le_δlam : (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 ≤ Real.rpow (dyadicDelta k) (-lam))
    (hCΔ_bounds1 : CΔ ≤ K * Real.rpow (dyadicDelta k) (-lam))
    (hCΔ_bounds2 : Real.rpow (dyadicDelta k) (-lam) ≤ K * CΔ)
    (hC_coarse_val : C_coarse = K_p5 + C_P + 8)
    (hC'_coarse_ge1 : 1 ≤ C'_coarse)
    (hK_p5_pos : 0 < K_p5) (hK_p5_ge1 : 1 ≤ K_p5)
    (hK_p5_spec_orig : ∀ (t : ℝ), s ≤ t → t ≤ 1 →
      ∀ (m : ℕ), 2 ≤ m →
      ∀ (C_P C_T M : ℝ), 0 < C_P → 1 ≤ C_P → 0 < C_T → 1 ≤ C_T → 1 ≤ M →
        ∀ (P : Finset (DSquare m)), P.Nonempty →
          IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ m) t C_P P →
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
                  (M * (DiscretisedFurstenbergEstimate.δ m) ^ s) ^ ((t - s) / (1 - s)))
    (hm_ge2 : 2 ≤ m)
    (hΔ_coarse_pos : 0 < Δ_coarse) (hΔ_coarse_lt_one : Δ_coarse < 1)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hδ_eq_dyadic : δ = dyadicDelta k)
    (hδ_le_delta : δ ≤ Δ_coarse)
    (hLbar_ge1 : 1 ≤ Real.log (1 / Δ_coarse))
    (hMΔ_pos : 0 < MΔ)
    (h_slope_coarse : ∀ T ∈ coarseConfig.T₀, |T.slope| ≤ 1)
    (h_exp_condition_v2 : (η + 2 * ε_G) * (1 - s) / (min t 1 - s) + η ≤ ε_inc)
    -- Improved incidence bound (to be supplied by juniper's GoodCaseImprovedIncidence)
    (h_improved_incidence_coarse : (coarseConfig.T₀.card : ENNReal) ≥
        ENNReal.ofReal (Real.rpow Δ_coarse (-(2 * s + ε_inc))))
    -- Good branch absorption (for large-M case)
    (h_absorb_good : Real.rpow (Real.log (1 / dyadicDelta m)) (C_P + 8) ≥
        K_p5 * (81 * ((2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7) *
          max (C_between ⟨0, by omega⟩) 1 * (2 * Real.sqrt 2)) * 13 * (2 : ℝ) ^ s *
        Real.rpow (dyadicDelta m) (2 * ε_G + ε_N))
    (PΔ : ℝ)
    (hPΔ_def : PΔ =
      (∏ j ∈ ({j0} : Finset (Fin n)).filter (fun j => (scaleClass j).isGood),
         Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η) *
      (∏ j ∈ ({j0} : Finset (Fin n)).filter (fun j => (scaleClass j).isBad),
         Δ (Fin.succ j) / Δ j.castSucc)) :
    (coarseConfig.T₀.card : ℝ) ≥
      Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
      Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
      Real.rpow Δ_coarse (-s + ε_N) * PΔ := by
  classical
  -- Define realized coarse S-set constant
  let C_P_coarse_value : ℝ := 81 * K * max (C_between j0) 1 * (2 * Real.sqrt 2)
  have hCP_coarse_ge1 : 1 ≤ C_P_coarse_value := by
    have hK_ge1' : 1 ≤ K := hK_ge1
    have hmax_ge1 : 1 ≤ max (C_between j0) 1 := le_max_right _ _
    have hbase_ge1 : 1 ≤ 2 * Real.sqrt 2 := by
      have h : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 2]
    have h_prod1 : 1 ≤ K * max (C_between j0) 1 := by
      calc (1 : ℝ)
        = 1 * 1 := by ring
      _ ≤ K * 1 := by gcongr
      _ ≤ K * max (C_between j0) 1 := by gcongr
    have h_prod2 : 1 ≤ K * max (C_between j0) 1 * (2 * Real.sqrt 2) := by
      calc (1 : ℝ)
        = 1 * 1 := by ring
      _ ≤ (K * max (C_between j0) 1) * 1 := by gcongr
      _ ≤ (K * max (C_between j0) 1) * (2 * Real.sqrt 2) := by gcongr
    have h_final : 1 ≤ 81 * (K * max (C_between j0) 1 * (2 * Real.sqrt 2)) := by
      have h81 : (1 : ℝ) ≤ 81 := by norm_num
      nlinarith
    have h_eq : 81 * (K * max (C_between j0) 1 * (2 * Real.sqrt 2)) = C_P_coarse_value := by
      dsimp only [C_P_coarse_value]; ring
    rw [←h_eq]; exact h_final
  have hCP_coarse_pos : 0 < C_P_coarse_value := by
    exact lt_of_lt_of_le (by norm_num) hCP_coarse_ge1
  have hCP_coarse_weaken : C_P_coarse_value ≥ 81 * K * max (C_between j0) 1 * (2 * Real.sqrt 2) :=
    le_refl C_P_coarse_value
  have hj0_eq : j0 = (⟨0, by omega⟩ : Fin n) := by
    apply Fin.ext; simp [hj0]
  -- Upper bound on C_P_coarse_value using K ≤ Poly(k)
  let Poly_k : ℝ := (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7
  have hK_poly : K ≤ Poly_k := hK_bound
  have h_j0_zero : j0 = (⟨0, by omega⟩ : Fin n) := hj0_eq
  have hCP_upper : C_P_coarse_value ≤
      81 * Poly_k * max (C_between (⟨0, by omega⟩ : Fin n)) 1 * (2 * Real.sqrt 2) := by
    have hK' : K ≤ Poly_k := hK_poly
    have hC : C_between j0 = C_between (⟨0, by omega⟩ : Fin n) := by
      exact congr_arg C_between h_j0_zero
    have h_main : 81 * K * max (C_between j0) 1 * (2 * Real.sqrt 2) ≤
        81 * Poly_k * max (C_between j0) 1 * (2 * Real.sqrt 2) := by
      gcongr <;> linarith
    have h_final : 81 * Poly_k * max (C_between j0) 1 * (2 * Real.sqrt 2) =
        81 * Poly_k * max (C_between (⟨0, by omega⟩ : Fin n)) 1 * (2 * Real.sqrt 2) := by
      rw [hC]
    exact h_final ▸ h_main
  -- Derive CΔ ≥ 1
  have hC1_pos : 0 < Real.rpow (dyadicDelta k) (-lam) := Real.rpow_pos_of_pos (dyadicDelta_pos k) _
  have hCΔ_ge1 : 1 ≤ CΔ :=
    coarse_CDelta_ge_one (by positivity) hC1_pos h_poly_K_le_δlam hCΔ_bounds2 hK_bound hK_pos
  have hCΔ_pos : 0 < CΔ := by linarith [hCΔ_ge1]
  have hCΔ_le' : CΔ ≤ K * Real.rpow δ (-lam) := by
    have h : CΔ ≤ K * Real.rpow (dyadicDelta k) (-lam) := hCΔ_bounds1
    have h2 : Real.rpow (dyadicDelta k) (-lam) = Real.rpow δ (-lam) := by
      rw [hδ_eq_dyadic]
    rw [h2] at h
    exact h
  -- C_coarse budget
  have hC_coarse_ge' : C_coarse ≥ K_p5 + 1 := by
    rw [hC_coarse_val]; linarith [hCP, hK_p5_ge1]
  have hC_coarse_pos' : 0 < C_coarse := by linarith [hC_coarse_ge']
  have hC_diff : C_coarse - K_p5 = C_P + 8 := by
    rw [hC_coarse_val]; ring
  -- Weaken good absorption from upper bound to realized value
  have h_good_absorb_core : Real.rpow (Real.log (1 / Δ_coarse)) (C_coarse - K_p5) ≥
      K_p5 * C_P_coarse_value * 13 * Real.rpow 2 s * Real.rpow Δ_coarse (2 * ε_G + ε_N) := by
    have hC : C_coarse - K_p5 = C_P + 8 := by rw [hC_coarse_val]; ring
    have hΔ : Δ_coarse = dyadicDelta m := hΔ_coarse_eq
    rw [hC, hΔ]
    set F : ℝ := K_p5 * 13 * (2 : ℝ) ^ s * Real.rpow (dyadicDelta m) (2 * ε_G + ε_N) with hF_def
    have hF_nonneg : 0 ≤ F := by
      rw [hF_def]
      have h1 : 0 ≤ K_p5 := by linarith
      have h2 : 0 ≤ (2 : ℝ) ^ s := Real.rpow_nonneg (by norm_num) s
      have h3 : 0 ≤ Real.rpow (dyadicDelta m) (2 * ε_G + ε_N) := Real.rpow_nonneg (by linarith) _
      positivity
    set U : ℝ := 81 * Poly_k * max (C_between (⟨0, by omega⟩ : Fin n)) 1 * (2 * Real.sqrt 2) with hU_def
    have h : K_p5 * C_P_coarse_value * 13 * (2 : ℝ) ^ s * Real.rpow (dyadicDelta m) (2 * ε_G + ε_N) ≤ U * F := by
      have h_eq1 : K_p5 * C_P_coarse_value * 13 * (2 : ℝ) ^ s * Real.rpow (dyadicDelta m) (2 * ε_G + ε_N) = C_P_coarse_value * F := by
        simp [hF_def]; ring
      rw [h_eq1]
      exact mul_le_mul_of_nonneg_right hCP_upper hF_nonneg
    have h_final : U * F = K_p5 * U * 13 * (2 : ℝ) ^ s * Real.rpow (dyadicDelta m) (2 * ε_G + ε_N) := by
      simp [hF_def, hU_def]; ring
    rw [h_final] at h
    exact le_trans h h_absorb_good
  have h_good_absorb : ∀ (t_j' : ℝ), scaleClass j0 = ScaleClass.good t_j' →
      Real.rpow (Real.log (1 / Δ_coarse)) (C_coarse - K_p5) ≥
        K_p5 * C_P_coarse_value * 13 * Real.rpow 2 s * Real.rpow Δ_coarse (2 * ε_G + ε_N) := by
    intro t_j' _
    exact h_good_absorb_core
  -- hK_p5_spec adapter: reorder so 2 ≤ m comes after 1 ≤ M
  have hK_p5_spec' : ∀ (t' : ℝ), s ≤ t' → t' ≤ 1 →
      ∀ (C_P' C_T' M' : ℝ), 0 < C_P' → 1 ≤ C_P' → 0 < C_T' → 1 ≤ C_T' → 1 ≤ M' → 2 ≤ m →
        ∀ (P' : Finset (DSquare m)), P'.Nonempty →
          IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ m) t' C_P' P' →
          (∀ (x y : DSquare m), x ∈ P' → y ∈ P' → dist x y ≤ 3) →
          (∀ p ∈ P', ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1) →
          ∀ (Tp : TubeFamily m),
            (∀ p ∈ P', ∀ T ∈ Tp p, (T.toSet ∩ p.toSet).Nonempty) →
            (∀ p ∈ P', ∀ T ∈ Tp p, |T.slope| ≤ 1) →
            (∀ p ∈ P', IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ m) s C_T' (Tp p)) →
            (∀ p ∈ P', (M' : ℝ) / 2 < (Tp p).card ∧ (Tp p).card ≤ M') →
              let T := P'.biUnion fun p => Tp p
              (T.card : ℝ) ≥ (1 / K_p5) * Real.log (1 / DiscretisedFurstenbergEstimate.δ m) ^ (-K_p5) *
                (1 / (C_P' * C_T')) * M' * (DiscretisedFurstenbergEstimate.δ m) ^ (-s) *
                  (M' * (DiscretisedFurstenbergEstimate.δ m) ^ s) ^ ((t' - s) / (1 - s)) := by
    intro t' ht1 ht2 C_P' C_T' M' hCP'_pos hCP'_ge1 hCT'_pos hCT'_ge1 hM'_ge1 h2m P' hP_nonempty hsset hdist hunit Tp h1 h2 h3 h4
    exact hK_p5_spec_orig t' ht1 ht2 m h2m C_P' C_T' M' hCP'_pos hCP'_ge1 hCT'_pos hCT'_ge1 hM'_ge1 P' hP_nonempty hsset hdist hunit Tp h1 h2 h3 h4
  -- Call coarse_source_good_only
  exact coarse_source_good_only
    (t_j := t_j)
    (hcfg := hcfg) (hB1 := hB1)
    (P := P) (hP_sub := hP_sub) (hP_nonempty' := hP_nonempty')
    (hnm := hnm) (hcoarse_P_eq := hcoarse_P_eq) (h_card_bound := h_card_bound)
    (hj0 := hj0)
    (h_good := h_good)
    (h_tj_ge_t := h_tj_ge_t)
    (hΔ0 := hΔ0) (hΔ1 := hΔ1) (hΔ_coarse_eq := hΔ_coarse_eq)
    (hCP_coarse_ge1 := hCP_coarse_ge1)
    (hCP_coarse_pos := hCP_coarse_pos)
    (hCP_coarse_weaken := hCP_coarse_weaken)
    (h_improved_incidence_coarse := h_improved_incidence_coarse)
    (h_exp_condition_v2 := h_exp_condition_v2)
    (hs := hs) (hs1 := hs1) (hst := hst)
    (hεG := hεG) (hη := hη) (hεN := hεN)
    (hε_inc := hε_inc)
    (hτ_pos := hτ_pos) (hCP := hCP) (hlam := hlam)
    (hK_ge1 := hK_ge1) (hK_pos := hK_pos)
    (hCΔ_pos := hCΔ_pos) (hCΔ_ge1 := hCΔ_ge1)
    (hCΔ_le := hCΔ_le')
    (hC_coarse_ge := hC_coarse_ge')
    (hC_coarse_pos := hC_coarse_pos')
    (hC'_coarse_ge1 := hC'_coarse_ge1)
    (hK_p5_pos := hK_p5_pos) (hK_p5_ge1 := hK_p5_ge1)
    (hK_p5_spec := hK_p5_spec')
    (hm_ge2 := hm_ge2)
    (hΔ_coarse_pos := hΔ_coarse_pos) (hΔ_coarse_lt_one := hΔ_coarse_lt_one)
    (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
    (hδ_le_delta := hδ_le_delta)
    (hLbar_ge1 := hLbar_ge1)
    (hMΔ_pos := hMΔ_pos)
    (h_slope_coarse := h_slope_coarse)
    (hδ_eq_dyadic := hδ_eq_dyadic)
    (PΔ := PΔ)
    (hPΔ_def := hPΔ_def)
    (h_good_absorb := h_good_absorb)

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
