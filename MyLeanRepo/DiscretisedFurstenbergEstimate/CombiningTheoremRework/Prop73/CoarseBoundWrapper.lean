module

/-
  CoarseBoundWrapper — Extracts δ/Δ setup, G0/B0/PΔ definitions,
  and coarse_bound_assembly call from InductiveStepCore_v2_Body.

  Reduces proof body size in the main lemma to avoid memory exhaustion.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseBoundAssembly
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.InductiveStepCore_v2_Helpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.BodyArithmetic
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.B1Integration
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformProp5
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DirecretisedFurstenbergEstimate.FormatConversion.M2
open DirecretisedFurstenbergEstimate.RegularIncidence

local instance {n : ℕ} : DecidableEq (DyadicSquare n) := Classical.decEq (DyadicSquare n)


/-- Coarse bound setup: δ/Δ definitions, G0/B0/PΔ, and coarse_bound_assembly call. -/
lemma coarse_bound_wrapper
    {n_fine k M m : ℕ}
    {s t τ ε_G η ε_N C_P lam ε_inc : ℝ}
    {K_p5 K CΔ : ℝ}
    {MΔ : ℕ}
    {config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M}
    {coarseConfig : CTNiceConfiguration m s CΔ MΔ}
    {P : Finset (DyadicSquare k)}
    (Δ : Fin (n_fine + 2) → ℝ)
    (scaleClass : Fin (n_fine + 1) → ScaleClass)
    (N : Fin (n_fine + 1) → ℕ)
    (C_between : Fin (n_fine + 1) → ℝ)
    (hm_eq2 : Δ 1 = dyadicDelta m)
    (hcfg : CombiningConfig s t τ (n_fine + 1) ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    (hB1 : B1BridgeHypotheses k config)
    (hextra : CombiningExtraHypotheses_v2 s t ε_G η ε_N C_P ε_inc (n_fine + 1) lam k M config Δ scaleClass)
    (hk_exp1 : dyadicDelta k ≤ Real.exp (-1))
    (hΔn_lt_Δ1 : Δ (Fin.last (n_fine + 1)) < Δ 1)
    (hnm : m ≤ k)
    -- B1 decomposition outputs
    (hK_ge1 : 1 ≤ K)
    (hK_pos : 0 < K)
    (hK_bound : K ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7)
    (hP_sub : P ⊆ config.P₀)
    (hP_nonempty' : P.Nonempty)
    (hcoarse_P_eq : coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hnm))
    (h_card_bound : (config.P₀.image (InductionConfigurations.containingSquare hnm)).card ≤ K * coarseConfig.P₀.card)
    (hCΔ_bounds1 : CΔ ≤ K * Real.rpow (dyadicDelta k) (-lam))
    (hCΔ_bounds2 : Real.rpow (dyadicDelta k) (-lam) ≤ K * CΔ)
    (hMΔ : 0 < MΔ)
    (h_slope_coarse : ∀ T ∈ coarseConfig.T₀, |T.slope| ≤ 1)
    -- Constants and hypotheses
    (hK_p5_ge1 : 1 ≤ K_p5)
    (hK_p5_pos : 0 < K_p5)
    (hK_p5_spec : ∀ (t : ℝ), s ≤ t → t ≤ 1 →
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
    (hs : 0 < s) (hst : s < t) (hs1 : s < 1)
    (hτ : 0 < τ) (hεG : 0 < ε_G) (hη : 0 < η) (hεN : 0 < ε_N)
    (hCP : 1 ≤ C_P) (hlam : 0 < lam)
    (h_poly_K_le_δlam : (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 ≤ Real.rpow (dyadicDelta k) (-lam))
    (h_k_large : (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 ≥ Real.rpow 2 (s + η - ε_N))
    (h_absorb_coarse : scaleClass ⟨0, by omega⟩ = ScaleClass.normal →
        Real.rpow (Real.log (1 / dyadicDelta m)) (C_P + 8) ≥
        K_p5 * (81 * ((2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7) *
          max (C_between ⟨0, by omega⟩) 1 * (2 * Real.sqrt 2) ^ s) * 13 * (2 : ℝ) ^ s *
        Real.rpow (dyadicDelta m) ε_N)
    (h_absorb_coarse_good : ∀ (t_j : ℝ), scaleClass ⟨0, by omega⟩ = ScaleClass.good t_j →
        Real.rpow (Real.log (1 / dyadicDelta m)) (C_P + 8) ≥
        K_p5 * (81 * ((2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7) *
          max (C_between ⟨0, by omega⟩) 1 * (2 * Real.sqrt 2)) * 13 * (2 : ℝ) ^ s *
        Real.rpow (dyadicDelta m) (2 * ε_G + ε_N))
    (h_good_improved_incidence : ∀ (t_j : ℝ),
        scaleClass ⟨0, by omega⟩ = ScaleClass.good t_j →
        ∀ (hnm : m ≤ k) (K' CΔ' : ℝ) (MΔ' : ℕ)
          (coarseConfig' : CTNiceConfiguration m s CΔ' MΔ')
          (P' : Finset (DyadicSquare k))
          (hP_sub' : P' ⊆ config.P₀)
          (hcoarse_P_eq' : coarseConfig'.P₀ = P'.image (InductionConfigurations.containingSquare hnm))
          (h_card_bound' : (config.P₀.image (InductionConfigurations.containingSquare hnm)).card ≤ K' * coarseConfig'.P₀.card)
          (hK_bound' : K' ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7)
          (hCΔ_bounds1' : CΔ' ≤ K' * Real.rpow (dyadicDelta k) (-lam))
          (hCΔ_bounds2' : Real.rpow (dyadicDelta k) (-lam) ≤ K' * CΔ')
          (h_slope_coarse' : ∀ T ∈ coarseConfig'.T₀, |T.slope| ≤ 1)
          (hP_nonempty' : P'.Nonempty),
        (coarseConfig'.T₀.card : ENNReal) ≥
          ENNReal.ofReal (Real.rpow (dyadicDelta m) (-(2 * s + ε_inc)))) :
    ∃ (Δ_coarse δbar δ : ℝ)
      (j0 : Fin (n_fine + 1))
      (G0 B0 : Finset (Fin (n_fine + 1)))
      (PΔ : ℝ),
      coarseConfig.P₀.Nonempty ∧
      Δ_coarse = Δ 1 ∧
      0 < Δ_coarse ∧ Δ_coarse < 1 ∧
      0 < δbar ∧ δbar < 1 ∧ δbar = dyadicDelta (k - m) ∧
      0 < δ ∧ δ < 1 ∧ δ = dyadicDelta k ∧
      (dyadicDelta k) = Δ_coarse * δbar ∧
      0 < PΔ ∧
      (PΔ = (∏ j ∈ G0, Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η) *
                 (∏ j ∈ B0, Δ (Fin.succ j) / Δ j.castSucc)) ∧
      (G0 = ({j0} : Finset (Fin (n_fine + 1))).filter (fun j => (scaleClass j).isGood)) ∧
      (B0 = ({j0} : Finset (Fin (n_fine + 1))).filter (fun j => (scaleClass j).isBad)) ∧
      (j0 = 0) ∧
      ((coarseConfig.T₀.card : ℝ) ≥
        Real.rpow (Real.log (1 / Δ_coarse)) (-(if m = 1 then 0 else K_p5 + C_P + 8)) * (MΔ : ℝ) *
        Real.rpow K (-1) * Real.rpow δ (1 * lam) *
        Real.rpow Δ_coarse (-s + ε_N) * PΔ) := by
  let C'_coarse : ℝ := 1
  let C_coarse : ℝ := if m = 1 then 0 else K_p5 + C_P + 8
  have hcoarse_P_nonempty : coarseConfig.P₀.Nonempty := by
    rw [hcoarse_P_eq]
    exact hP_nonempty'.image _
  let Δ_coarse : ℝ := Δ 1
  have hΔ_coarse_def : Δ_coarse = Δ 1 := by rfl
  let δbar : ℝ := (dyadicDelta k) / Δ_coarse
  have hδbar_def : δbar = (dyadicDelta k) / Δ_coarse := by rfl
  have hδ_pos : 0 < (dyadicDelta k) := dyadicDelta_pos k
  have hΔ_coarse_pos : 0 < Δ_coarse := hcfg.hΔ_pos 1
  have hΔ_lt_one : Δ_coarse < 1 := delta_coarse_lt_one hcfg
  have hδbar_pos : 0 < δbar := by positivity
  have h_gt : dyadicDelta k < Δ_coarse := by
    rw [hΔ_coarse_def, ←hcfg.hΔ_end]; exact hΔn_lt_Δ1
  have hδbar_lt_one : δbar < 1 := by
    rw [hδbar_def]
    have h : (dyadicDelta k) / Δ_coarse < 1 := by
      apply (div_lt_one (by positivity)).mpr; exact h_gt
    exact h
  have hδbar_eq : δbar = dyadicDelta (k - m) := deltabar_eq_spec hcfg m hnm hm_eq2 Δ_coarse δbar hΔ_coarse_def hδbar_def
  have hδ_eq : (dyadicDelta k) = Δ_coarse * δbar := by
    rw [hδbar_def] <;> field_simp [hΔ_coarse_pos.ne'] <;> ring
  let δ : ℝ := dyadicDelta k
  have hδ_def : δ = dyadicDelta k := by rfl
  have hδ_pos2 : 0 < δ := dyadicDelta_pos k
  have hδ_lt_one : δ < 1 := by
    have h : δ ≤ Real.exp (-1) := by
      have h' : δ = dyadicDelta k := by simp [hδ_def]
      rw [h']
      exact hk_exp1
    have h2 : Real.exp (-1) < 1 := by
      have h4 : Real.exp (-1) < Real.exp 0 := Real.exp_strictMono (by norm_num)
      have h5 : Real.exp 0 = 1 := by simp
      rw [h5] at h4; exact h4
    linarith
  let j0 : Fin (n_fine + 1) := 0
  let G0 : Finset (Fin (n_fine + 1)) := ({j0} : Finset (Fin (n_fine + 1))).filter (fun j => (scaleClass j).isGood)
  let B0 : Finset (Fin (n_fine + 1)) := ({j0} : Finset (Fin (n_fine + 1))).filter (fun j => (scaleClass j).isBad)
  let PΔ : ℝ :=
    (∏ j ∈ G0, Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η) *
    (∏ j ∈ B0, Δ (Fin.succ j) / Δ j.castSucc)
  have hPΔ_pos : 0 < PΔ := by
    dsimp only [PΔ]
    apply mul_pos <;> apply Finset.prod_pos <;> intro j _
    · have h1 : 0 < Δ j.castSucc := hcfg.hΔ_pos j.castSucc
      have h2 : 0 < Δ (Fin.succ j) := hcfg.hΔ_pos (Fin.succ j)
      exact Real.rpow_pos_of_pos (div_pos h1 h2) _
    · have h1 : 0 < Δ (Fin.succ j) := hcfg.hΔ_pos (Fin.succ j)
      have h2 : 0 < Δ j.castSucc := hcfg.hΔ_pos j.castSucc
      exact div_pos h1 h2
  have h_coarse_bound : (coarseConfig.T₀.card : ℝ) ≥
      Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
      Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
      Real.rpow Δ_coarse (-s + ε_N) * PΔ :=
    coarse_bound_assembly
      (hnm := hnm)
      (j0 := j0)
      (hj0 := by simp [j0])
      (hcfg := hcfg)
      (hB1 := hB1)
      (hP_sub := hP_sub)
      (hP_nonempty' := hP_nonempty')
      (hcoarse_P_eq := hcoarse_P_eq)
      (h_card_bound := h_card_bound)
      (hCΔ_bounds1 := hCΔ_bounds1)
      (hCΔ_bounds2 := hCΔ_bounds2)
      (h_slope_coarse := h_slope_coarse)
      (hm_eq2 := hm_eq2)
      (Δ_coarse := Δ_coarse)
      (hΔ_coarse_def := hΔ_coarse_def)
      (hΔ_coarse_pos := hΔ_coarse_pos)
      (hΔ_lt_one := hΔ_lt_one)
      (δ := δ)
      (hδ_def := hδ_def)
      (hδ_pos := hδ_pos2)
      (hδ_lt_one := hδ_lt_one)
      (hK_ge1 := hK_ge1)
      (hK_pos := hK_pos)
      (hK_bound := hK_bound)
      (h_poly_K_le_δlam := h_poly_K_le_δlam)
      (h_k_large := h_k_large)
      (hK_p5_pos := hK_p5_pos)
      (hK_p5_ge1 := hK_p5_ge1)
      (hK_p5_spec := hK_p5_spec)
      (hCP := hCP)
      (hs := hs)
      (hs1 := hs1)
      (hst := hst)
      (hεG := hεG)
      (hη := hη)
      (hεN := hεN)
      (hτ_pos := hτ)
      (hlam := hlam)
      (h_absorb_coarse := h_absorb_coarse)
      (h_absorb_coarse_good := h_absorb_coarse_good)
      (h_good_improved_incidence := h_good_improved_incidence)
      (h_tj_ge_t := hextra.h_tj_ge_t)
      (hε_inc_pos := hextra.hε_inc_pos)
      (h_exp_condition := hextra.h_exp_condition)
      (hcoarse_P_nonempty := hcoarse_P_nonempty)
      (hMΔ_pos := hMΔ)
      (hC_coarse_def := by rfl)
      (hC'_coarse_eq1 := by rfl)
      (hPΔ_def := by rfl)
  exact ⟨Δ_coarse, δbar, δ, j0, G0, B0, PΔ,
    hcoarse_P_nonempty, hΔ_coarse_def, hΔ_coarse_pos, hΔ_lt_one,
    hδbar_pos, hδbar_lt_one, hδbar_eq,
    hδ_pos2, hδ_lt_one, hδ_def, hδ_eq,
    hPΔ_pos, by rfl, by rfl, by rfl, by simp [j0], h_coarse_bound⟩

end DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure
