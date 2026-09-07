module

/-
  Normal coarse bound helper for inductive_step_core_v2.

  Extracts the m≥2 normal first-scale case from core_v2 to avoid
  proof-context timeouts. Constructs the realized coarse S-set constant,
  weakens the fixed-degree polylog absorption hypothesis, and calls
  coarse_source_normal_only.

  Budget: C_coarse - K_p5 = C_P + 8 (degree-7 B1 factor + 1 margin).

  Whiteprint node: combining_theorem_rework / normal_coarse_bound
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseSourceData
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

/-- Coarse bound for m≥2 normal first-scale.

    Constructs the realized S-set constant `C_P_coarse_value`, bounds it
    by `Poly(k) * max(C_between 0, 1) * (2√2)^s`, weakens the caller's
    fixed-degree absorption hypothesis, and dispatches to
    `coarse_source_normal_only`. -/
lemma normal_coarse_bound
    {n k m M MΔ : ℕ}
    {s t τ ε_G η ε_N C_P lam δ Δ_coarse : ℝ}
    {K CΔ C'_coarse K_p5 C_coarse : ℝ}
    {config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M}
    {coarseConfig : CTNiceConfiguration m s CΔ MΔ}
    {scaleClass : Fin n → ScaleClass}
    {j0 : Fin n}
    {Δ : Fin (n + 1) → ℝ}
    {C_between : Fin n → ℝ}
    {N : Fin n → ℕ}
    (hcfg : CombiningConfig s t τ n ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    (hB1 : B1BridgeHypotheses k config)
    (P : Finset (DyadicSquare k))
    (hP_sub : P ⊆ config.P₀)
    (hP_nonempty' : P.Nonempty)
    (hnm : m ≤ k)
    (hcoarse_P_eq : coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hnm))
    (h_card_bound : (config.P₀.image (InductionConfigurations.containingSquare hnm)).card ≤ K * coarseConfig.P₀.card)
    (hj0 : j0.val = 0)
    (h_normal : scaleClass j0 = ScaleClass.normal)
    (hΔ0 : Δ 0 = 1)
    (hΔ1 : Δ 1 = Δ_coarse)
    (hΔ_coarse_eq : Δ_coarse = dyadicDelta m)
    -- Common parameters
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t)
    (hεG : 0 < ε_G) (hη : 0 < η) (hεN : 0 < ε_N)
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
    (hδ_eq : δ = dyadicDelta k)
    (hδ_le_delta : δ ≤ Δ_coarse)
    (hLbar_ge1 : 1 ≤ Real.log (1 / Δ_coarse))
    (hMΔ_pos : 0 < MΔ)
    (h_slope_coarse : ∀ T ∈ coarseConfig.T₀, |T.slope| ≤ 1)
    -- Fixed-degree absorption: log(1/Δ_m)^(C_P+8) ≥ K_p5 * C_P_coarse_upper * 13 * 2^s * Δ_m^ε_N
    (h_absorb_coarse : Real.rpow (Real.log (1 / dyadicDelta m)) (C_P + 8) ≥
        K_p5 * (81 * ((2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7) *
          max (C_between ⟨0, by omega⟩) 1 * (2 * Real.sqrt 2) ^ s) * 13 * (2 : ℝ) ^ s *
        Real.rpow (dyadicDelta m) ε_N) :
    (coarseConfig.T₀.card : ℝ) ≥
      Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
      Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
      Real.rpow Δ_coarse (-s + ε_N) := by
  classical
  -- Define realized coarse S-set constant
  let C_P_coarse_value : ℝ := 81 * K * max (C_between j0) 1 * (2 * Real.sqrt 2) ^ s
  have hCP_coarse_ge1 : 1 ≤ C_P_coarse_value := by
    have hK_ge1' : 1 ≤ K := hK_ge1
    have hmax_ge1 : 1 ≤ max (C_between j0) 1 := le_max_right _ _
    have hbase_ge1 : 1 ≤ 2 * Real.sqrt 2 := by
      have h : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 2]
    have hrpow_ge1 : 1 ≤ (2 * Real.sqrt 2) ^ s := Real.one_le_rpow hbase_ge1 (by linarith)
    have h_prod1 : 1 ≤ K * max (C_between j0) 1 := by
      calc (1 : ℝ)
        = 1 * 1 := by ring
      _ ≤ K * 1 := by gcongr
      _ ≤ K * max (C_between j0) 1 := by gcongr
    have h_prod2 : 1 ≤ K * max (C_between j0) 1 * (2 * Real.sqrt 2) ^ s := by
      calc (1 : ℝ)
        = 1 * 1 := by ring
      _ ≤ (K * max (C_between j0) 1) * 1 := by gcongr
      _ ≤ (K * max (C_between j0) 1) * (2 * Real.sqrt 2) ^ s := by gcongr
    have h_final : 1 ≤ 81 * (K * max (C_between j0) 1 * (2 * Real.sqrt 2) ^ s) := by
      have h81 : (1 : ℝ) ≤ 81 := by norm_num
      have h_pos : 0 ≤ K * max (C_between j0) 1 * (2 * Real.sqrt 2) ^ s := by positivity
      have h : (1 : ℝ) ≤ 81 * (K * max (C_between j0) 1 * (2 * Real.sqrt 2) ^ s) := by
        calc (1 : ℝ)
          ≤ K * max (C_between j0) 1 * (2 * Real.sqrt 2) ^ s := h_prod2
        _ ≤ 81 * (K * max (C_between j0) 1 * (2 * Real.sqrt 2) ^ s) := by
          have h81' : (1 : ℝ) ≤ 81 := by norm_num
          nlinarith
      exact h
    have h_eq : 81 * (K * max (C_between j0) 1 * (2 * Real.sqrt 2) ^ s) = C_P_coarse_value := by
      dsimp only [C_P_coarse_value]; ring
    rw [←h_eq]; exact h_final
  have hCP_coarse_pos : 0 < C_P_coarse_value := by
    exact lt_of_lt_of_le (by norm_num) hCP_coarse_ge1
  have hCP_coarse_weaken : C_P_coarse_value ≥ 81 * K * max (C_between j0) 1 * (2 * Real.sqrt 2) ^ s :=
    le_refl C_P_coarse_value
  have hj0_eq : j0 = (⟨0, by omega⟩ : Fin n) := by
    apply Fin.ext; simp [hj0]
  -- Upper bound on C_P_coarse_value using K ≤ Poly(k)
  let Poly_k : ℝ := (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7
  have hK_poly : K ≤ Poly_k := hK_bound
  have h_nonneg_max : 0 ≤ max (C_between j0) 1 := by
    have h : (0 : ℝ) ≤ 1 := by norm_num
    exact le_max_of_le_right h
  have h_nonneg_rpow : 0 ≤ (2 * Real.sqrt 2) ^ s := by positivity
  have h_j0_zero : j0 = (⟨0, by omega⟩ : Fin n) := hj0_eq
  have hCP_upper : C_P_coarse_value ≤
      81 * Poly_k * max (C_between (⟨0, by omega⟩ : Fin n)) 1 * (2 * Real.sqrt 2) ^ s := by
    have hK' : K ≤ Poly_k := hK_poly
    have hC : C_between j0 = C_between (⟨0, by omega⟩ : Fin n) := by
      exact congr_arg C_between h_j0_zero
    have h_main : 81 * K * max (C_between j0) 1 * (2 * Real.sqrt 2) ^ s ≤
        81 * Poly_k * max (C_between j0) 1 * (2 * Real.sqrt 2) ^ s := by
      gcongr
    have h_final : 81 * Poly_k * max (C_between j0) 1 * (2 * Real.sqrt 2) ^ s =
        81 * Poly_k * max (C_between (⟨0, by omega⟩ : Fin n)) 1 * (2 * Real.sqrt 2) ^ s := by
      rw [hC]
    exact h_final ▸ h_main
  -- Derive CΔ ≥ 1
  have hC1_pos : 0 < Real.rpow (dyadicDelta k) (-lam) := Real.rpow_pos_of_pos (dyadicDelta_pos k) _
  have hCΔ_ge1 : 1 ≤ CΔ :=
    coarse_CDelta_ge_one (by positivity) hC1_pos h_poly_K_le_δlam hCΔ_bounds2 hK_bound hK_pos
  have hCΔ_pos : 0 < CΔ := by linarith [hCΔ_ge1]
  have hCΔ_le' : CΔ ≤ K * Real.rpow δ (-lam) := by
    have h : CΔ ≤ K * Real.rpow (dyadicDelta k) (-lam) := hCΔ_bounds1
    rw [hδ_eq] at *
    exact h
  -- C_coarse budget
  have hC_coarse_ge' : C_coarse ≥ K_p5 + 1 := by
    rw [hC_coarse_val]; linarith [hCP, hK_p5_ge1]
  have hC_coarse_pos' : 0 < C_coarse := by linarith [hC_coarse_ge']
  have hC_diff : C_coarse - K_p5 = C_P + 8 := by
    rw [hC_coarse_val]; ring
  -- Weaken absorption from upper bound to realized value
  have h_absorb : Real.rpow (Real.log (1 / Δ_coarse)) (C_coarse - K_p5) ≥
      K_p5 * C_P_coarse_value * 13 * Real.rpow 2 s * Real.rpow Δ_coarse ε_N := by
    have hΔ_eq : Δ_coarse = dyadicDelta m := hΔ_coarse_eq
    rw [hC_diff, hΔ_eq] at *
    have h_rpow_nonneg : 0 ≤ Real.rpow (dyadicDelta m) ε_N := Real.rpow_nonneg (by linarith) _
    have h_upper : K_p5 * C_P_coarse_value * 13 * (2 : ℝ) ^ s * Real.rpow (dyadicDelta m) ε_N ≤
        K_p5 * (81 * Poly_k * max (C_between (⟨0, by omega⟩ : Fin n)) 1 * (2 * Real.sqrt 2) ^ s) * 13 * (2 : ℝ) ^ s *
          Real.rpow (dyadicDelta m) ε_N := by
      have h_pos1 : 0 ≤ K_p5 := by linarith
      have h_pos2 : 0 ≤ 13 * (2 : ℝ) ^ s := by positivity
      gcongr (K_p5 * ?_ * 13 * (2 : ℝ) ^ s * Real.rpow (dyadicDelta m) ε_N)
    exact le_trans h_upper h_absorb_coarse
  -- hK_p5_spec adapter: reorder so 2 ≤ m comes after 1 ≤ M
  have hK_p5_spec' : ∀ (t : ℝ), s ≤ t → t ≤ 1 →
      ∀ (C_P C_T M : ℝ), 0 < C_P → 1 ≤ C_P → 0 < C_T → 1 ≤ C_T → 1 ≤ M → 2 ≤ m →
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
                  (M * (DiscretisedFurstenbergEstimate.δ m) ^ s) ^ ((t - s) / (1 - s)) := by
    intro t ht1 ht2 C_P C_T M hCP_pos hCP_ge1 hCT_pos hCT_ge1 hM_ge1 hm P hP_nonempty hsset hdist hunit Tp h1 h2 h3 h4
    exact hK_p5_spec_orig t ht1 ht2 m hm C_P C_T M hCP_pos hCP_ge1 hCT_pos hCT_ge1 hM_ge1 P hP_nonempty hsset hdist hunit Tp h1 h2 h3 h4
  -- Geometric data
  have h_full_unit : ∀ (p : DSquare m), p ∈ finsetDyadicToDSquare coarseConfig.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet → 0 ≤ x.1 ∧ x.1 < 1 ∧ 0 ≤ x.2 ∧ x.2 < 1 :=
    coarse_full_unit_bound_from_B1 hnm hB1 hP_sub hcoarse_P_eq
  have h_unit_coarse : ∀ (p : DSquare m), p ∈ finsetDyadicToDSquare coarseConfig.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1 :=
    coarse_unit_coarse_from_full h_full_unit
  have h_diam_coarse : ∀ (p q : DSquare m),
      p ∈ finsetDyadicToDSquare coarseConfig.P₀ →
      q ∈ finsetDyadicToDSquare coarseConfig.P₀ → dist p q ≤ 3 :=
    coarse_diam_from_full_unit h_full_unit
  have hcoarse_P_nonempty : coarseConfig.P₀.Nonempty := by
    rw [hcoarse_P_eq]
    exact hP_nonempty'.image _
  -- Call coarse_source_normal_only
  exact coarse_source_normal_only
    (hcfg := hcfg) (hB1 := hB1)
    (P := P) (hP_sub := hP_sub) (hP_nonempty' := hP_nonempty')
    (hnm := hnm) (hcoarse_P_eq := hcoarse_P_eq) (h_card_bound := h_card_bound)
    (hj0 := hj0)
    (h_normal := h_normal)
    (hΔ0 := hΔ0) (hΔ1 := hΔ1) (hΔ_coarse_eq := hΔ_coarse_eq)
    (hCP_coarse_ge1 := hCP_coarse_ge1)
    (hCP_coarse_pos := hCP_coarse_pos)
    (hCP_coarse_weaken := hCP_coarse_weaken)
    (hs := hs) (hs1 := hs1) (hst := hst)
    (hεG := hεG) (hη := hη) (hεN := hεN)
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
    (h_absorb := h_absorb)

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
