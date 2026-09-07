module

/-
  Non-All-Bad Branch — Extracted from InductiveStepCore_v2_Body.

  Contains the entire non-all-bad branch where at least one tail scale
  is normal or good. Constructs the fine CombiningConfig, applies the
  induction hypothesis, and combines coarse/fine bounds.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.TailSplit
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.FineConfigSublemma
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.InductiveStepCore_v2_Helpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.NonAllBadArithmetic
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.FineBranchHcfgFine
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.BodyArithmetic
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.B1Integration
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DirecretisedFurstenbergEstimate.FormatConversion.M2

attribute [local instance] Classical.propDecidable


/-- Non-all-bad branch: at least one tail scale is normal/good.
    Constructs fine config, applies IH, combines bounds. -/
lemma non_all_bad_branch
    {n_fine k m M MΔ : ℕ}
    {s t τ ε_G η ε_N C_P C_P_fine C_n : ℝ}
    {C_fine C'_fine C C' : ℝ}
    {lam lam_tail δ_tail : ℝ}
    {K Δ_coarse δ δbar PΔ Pb α A : ℝ}
    {CΔ : ℝ}
    {K_p5 : ℝ}
    {ε_inc : ℝ}
    {C_coarse C'_coarse : ℝ}
    (hnm : m ≤ k)
    (CQ : DyadicSquare m → ℝ)
    (config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M)
    (coarseConfig : CTNiceConfiguration m s CΔ MΔ)
    (P : Finset (DyadicSquare k))
    (Q : DyadicSquare m)
    (hQ : Q ∈ coarseConfig.P₀)
    (MQ : DyadicSquare m → ℕ)
    (hMQ : ∀ Q ∈ coarseConfig.P₀, 0 < MQ Q)
    (hMΔ_pos : 0 < MΔ)
    (fineConfig_Q : CTNiceConfiguration (k - m) s (CQ Q) (MQ Q))
    (fineConfig_B1_Q : B1BridgeHypotheses (k - m) fineConfig_Q)
    (Δ : Fin (n_fine + 2) → ℝ)
    (scaleClass : Fin (n_fine + 1) → ScaleClass)
    (N : Fin (n_fine + 1) → ℕ)
    (C_between : Fin (n_fine + 1) → ℝ)
    (Δ' : Fin (n_fine + 1) → ℝ)
    (scaleClass' : Fin n_fine → ScaleClass)
    (N' : Fin n_fine → ℕ)
    (C_between' : Fin n_fine → ℝ)
    (j0 : Fin (n_fine + 1))
    (shift : Fin n_fine → Fin (n_fine + 1))
    (hshift : ∀ j, shift j = Fin.succ j)
    (G' B' : Finset (Fin n_fine))
    (hG'_def : G' = Finset.univ.filter (fun j => (scaleClass' j).isGood))
    (hB'_def : B' = Finset.univ.filter (fun j => (scaleClass' j).isBad))
    (hPb_def : Pb = (∏ j ∈ G', Real.rpow (Δ' j.castSucc / Δ' (Fin.succ j)) η) *
        (∏ j ∈ B', Δ' (Fin.succ j) / Δ' j.castSucc))
    -- Hypotheses
    (hs : 0 < s) (hst : s < t) (hs1 : s < 1)
    (hτ : 0 < τ) (hτ1 : τ < 1)
    (hεG : 0 < ε_G) (hη : 0 < η) (hεN : 0 < ε_N)
    (hCP : 1 ≤ C_P) (hCP_fine : 1 ≤ C_P_fine)
    (hCn_ge1 : 1 ≤ C_n)
    (hCP_fine_eq : C_P_fine = C_P + 2 * C_n)
    (hC_fine_pos : 0 < C_fine) (hC'_fine_pos : 0 < C'_fine)
    (hlam : 0 < lam) (hlam_tail_pos : 0 < lam_tail)
    (hτ_lam_tail : τ * lam_tail = 2 * lam)
    (hδ_tail_pos : 0 < δ_tail)
    (hδτ_le_dtail : Real.rpow (dyadicDelta k) τ ≤ δ_tail)
    (h_poly_K_le_δlam : (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 ≤ Real.rpow (dyadicDelta k) (-lam))
    (h_k_large : (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 ≥ Real.rpow 2 (s + η - ε_N))
    (A : ℝ) (hA_pos : 0 < A) (hA_ge1 : 1 ≤ A)
    (hA_eq : A = 2700 * 3145728 * (8 / Real.log 2)^7)
    (hC_pos : 0 < C) (hC'_pos : 0 < C')
    (hC_ge : C ≥ (1 + (7 : ℝ)) * (1 + (1 : ℝ) + C'_fine) + K_p5 + C_P + 8 + C_fine)
    (hC'_ge : C' ≥ (1 : ℝ) + 2 * C'_fine / τ)
    (hk : dyadicDelta k ≤ Real.exp (-A))
    (hm_eq2 : Δ 1 = dyadicDelta m)
    (hcfg : CombiningConfig s t τ (n_fine + 1) ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    (hB1 : B1BridgeHypotheses k config)
    (hextra : CombiningExtraHypotheses_v2 s t ε_G η ε_N C_P ε_inc (n_fine + 1) lam k M config Δ scaleClass)
    (h_ih_bound : ∀ (k' : ℕ), dyadicDelta k' ≤ δ_tail →
      ∀ (M' : ℕ)
        (config' : CTNiceConfiguration k' s (Real.rpow (dyadicDelta k') (-lam_tail)) M')
        (Δ' : Fin (n_fine + 1) → ℝ)
        (scaleClass' : Fin n_fine → ScaleClass)
        (N' : Fin n_fine → ℕ)
        (C_between' : Fin n_fine → ℝ),
        CombiningConfig s t τ n_fine ε_G η lam_tail ε_N C_P_fine C_between' k' M' config' Δ' scaleClass' N' →
        B1BridgeHypotheses k' config' →
        CombiningExtraHypotheses_v2 s t ε_G η ε_N C_P_fine ε_inc n_fine lam_tail k' M' config' Δ' scaleClass' →
        (config'.T₀.card : ENNReal) ≥
          ENNReal.ofReal (combiningLowerBound (dyadicDelta k') (M' : ℝ) C_fine C'_fine lam_tail s ε_N η n_fine Δ' scaleClass'))
    (h_eq89 : Real.log (1 / dyadicDelta k) ≥ Real.rpow τ (-(C_P_fine : ℝ)))
    (hK_p5_ge1 : 1 ≤ K_p5)
    -- Local data
    (hK_ge1 : 1 ≤ K) (hK_bound : K ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7)
    (hP_sub : P ⊆ config.P₀)
    (hcoarse_P_eq : coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hnm))
    (h_card_density_all : ∀ (Q : DyadicSquare m), Q ∈ coarseConfig.P₀ →
        ((config.P₀.filter (fun p => InductionConfigurations.squareContained hnm p Q)).card : ℝ) ≤
        K * ((P.filter (fun p => InductionConfigurations.squareContained hnm p Q)).card : ℝ))
    (hCΔ_bounds1 : CΔ ≤ K * Real.rpow (dyadicDelta k) (-lam))
    (hCΔ_bounds2 : Real.rpow (dyadicDelta k) (-lam) ≤ K * CΔ)
    (hCQ_bounds : ∀ (Q : DyadicSquare m), Q ∈ coarseConfig.P₀ →
        CQ Q ≤ K * Real.rpow (dyadicDelta k) (-lam) ∧
        Real.rpow (dyadicDelta k) (-lam) ≤ K * CQ Q)
    (hfine_P_eq_Q : fineConfig_Q.P₀ =
        (P.filter (fun p => InductionConfigurations.squareContained hnm p Q)).image
          (InductionConfigurations.squareHomothety hnm Q))
    (h_card_ineq_Q : K * (config.T₀.card : ℝ) * (MΔ : ℝ) * (MQ Q : ℝ) ≥
        (coarseConfig.T₀.card : ℝ) * fineConfig_Q.T₀.card * (M : ℝ))
    (h_slope_coarse : ∀ T ∈ coarseConfig.T₀, |T.slope| ≤ 1)
    (hΔ_coarse_pos : 0 < Δ_coarse)
    (hΔ_lt_one : Δ_coarse < 1)
    (hδbar_pos : 0 < δbar)
    (hδbar_lt_one : δbar < 1)
    (hδbar_eq : δbar = dyadicDelta (k - m))
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hδ_def : δ = dyadicDelta k)
    (hδ_eq : δ = Δ_coarse * δbar)
    (hPΔ_pos : 0 < PΔ)
    (hPb_pos : 0 < Pb)
    (h_coarse_bound : (coarseConfig.T₀.card : ℝ) ≥
        Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
        Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
        Real.rpow Δ_coarse (-s + ε_N) * PΔ)
    (hC_coarse_nonneg : 0 ≤ C_coarse)
    (hC'_coarse_nonneg : 0 ≤ C'_coarse)
    (hC'_final_ge : C' * lam ≥ C'_coarse * lam + C'_fine * lam_tail)
    (hC_ge_final : C ≥ (1 + α) * (C'_coarse + 1) + C_coarse + C_fine)
    (hK_poly : K ≤ A * (Real.log (1 / δ)) ^ α)
    (hL_ge1 : 1 ≤ Real.log (1 / δ))
    (hL_ge_A : Real.log (1 / δ) ≥ A)
    (hα_pos : 0 < α)
    (h_product : combiningLowerBound (dyadicDelta k) (M : ℝ) C C' lam s ε_N η (n_fine + 1) Δ scaleClass =
        Real.rpow (Real.log (1 / dyadicDelta k)) (-C) * (M : ℝ) *
        Real.rpow (dyadicDelta k) (C' * lam) * Real.rpow (dyadicDelta k) (-s + ε_N) * (PΔ * Pb))
    (hΔ'_def : ∀ i, Δ' i = Δ (Fin.succ i) / Δ 1)
    (hscaleClass'_def : ∀ j, scaleClass' j = scaleClass (shift j))
    (hC_between'_def : ∀ j, C_between' j = C_between (shift j))
    (hj0 : j0 = 0)
    (h_not_all_bad : ¬(∀ j ∈ (Finset.univ.erase j0), (scaleClass j).isBad))
    -- Fine absorption hypotheses
    (h_absorb_fine_normal : ∀ (K : ℝ), 1 ≤ K →
      K ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7 →
      ∀ (j : Fin n_fine), scaleClass (shift j) = ScaleClass.normal →
        9 * (C_between (shift j)) * 2 * K *
          (24 * Real.log (1 / dyadicDelta (k - m)) / ((n_fine : ℕ) : ℝ)) ^ n_fine *
          (4 : ℝ) ^ n_fine ≤
        Real.log (1 / dyadicDelta (k - m)) ^ C_P_fine *
          (Δ' j.castSucc / Δ' (Fin.succ j)) ^ ε_N)
    (h_absorb_fine_good : ∀ (K : ℝ), 1 ≤ K →
      K ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7 →
      ∀ (j : Fin n_fine) (t_j : ℝ), scaleClass (shift j) = ScaleClass.good t_j →
        9 * (C_between (shift j)) * 2 * K *
          (24 * Real.log (1 / dyadicDelta (k - m)) / ((n_fine : ℕ) : ℝ)) ^ n_fine *
          (4 : ℝ) ^ n_fine ≤
        Real.log (1 / dyadicDelta (k - m)) ^ C_P_fine *
          (Δ' j.castSucc / Δ' (Fin.succ j)) ^ ε_G)
    (hΔn_lt_Δ1 : Δ (Fin.last (n_fine + 1)) < Δ 1)
    (hk_exp1 : dyadicDelta k ≤ Real.exp (-1))
    (hΔ_coarse_eq : Δ_coarse = Δ 1)
    (hn_fine : 1 ≤ n_fine) :
    (config.T₀.card : ENNReal) ≥
      ENNReal.ofReal (combiningLowerBound (dyadicDelta k) (M : ℝ) C C' lam s ε_N η (n_fine + 1) Δ scaleClass) := by
  let MQ_Q := MQ Q
  have hMQ_Q_pos : 0 < MQ_Q := hMQ Q hQ
  have h_exists0 : ∃ j, j ∈ (Finset.univ.erase (0 : Fin (n_fine + 1))) ∧ ¬(scaleClass j).isBad := by
    have h_eq : (Finset.univ.erase j0) = (Finset.univ.erase (0 : Fin (n_fine + 1))) := by
      rw [hj0] <;> rfl
    have h_not_all_bad' : ¬(∀ j ∈ (Finset.univ.erase (0 : Fin (n_fine + 1))), (scaleClass j).isBad) := by
      rw [←h_eq]
      exact h_not_all_bad
    have h : ∃ j ∈ (Finset.univ.erase (0 : Fin (n_fine + 1))), ¬(scaleClass j).isBad := by
      simpa [Finset.mem_erase] using h_not_all_bad'
    rcases h with ⟨j, hj1, hj2⟩
    exact ⟨j, hj1, hj2⟩
  have hδbar_le_δτ : δbar ≤ Real.rpow δ τ := by
    have hmk' : m ≤ k := hnm
    have hdiv : dyadicDelta k / dyadicDelta m = dyadicDelta (k - m) := dyadicDelta_div k m hmk'
    have hδbar_eq2 : δbar = Δ (Fin.last (n_fine + 1)) / Δ 1 := by
      have h9 : Δ (Fin.last (n_fine + 1)) / Δ 1 = dyadicDelta k / dyadicDelta m := by
        rw [hcfg.hΔ_end, hm_eq2]
      rw [h9, hdiv]
      exact hδbar_eq
    have h_n_ge2 : 2 ≤ n_fine + 1 := by omega
    have h_main : δbar ≤ Real.rpow (dyadicDelta k) τ :=
      tail_nonbad_deltabar_le_deltaτ h_n_ge2 hτ Δ scaleClass hcfg.hΔ_pos hcfg.hΔ_strict
        hcfg.h_scale_ratio δbar hδbar_eq2 h_exists0
    have h_goal : δbar ≤ Real.rpow δ τ := by
      rw [hδ_def]
      exact h_main
    exact h_goal
  have h_dyadic_anti : dyadicDelta k < dyadicDelta m := by
    rw [←hcfg.hΔ_end, ←hm_eq2]; exact hΔn_lt_Δ1
  have hK_le : K ≤ Real.rpow δ (-lam) := by
    have hK_le_poly : K ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7 := hK_bound
    have hpoly_le : 2700 * 3145728 * (4 * (k : ℝ) + 7)^7 ≤ Real.rpow δ (-lam) := by
      simpa [hδ_def] using h_poly_K_le_δlam
    exact le_trans hK_le_poly hpoly_le
  have h_rpow_bounds := fine_tail_rpow_bound hδ_pos hδbar_pos hK_le hδbar_le_δτ hτ_lam_tail hlam hlam_tail_pos
  have hKδ := h_rpow_bounds.1
  have hδbar_tail := h_rpow_bounds.2
  let C_fine_target : ℝ := Real.rpow (dyadicDelta (k - m)) (-lam_tail)
  have hC_fine_target_pos : 0 < C_fine_target := Real.rpow_pos_of_pos (dyadicDelta_pos (k - m)) _
  have hCQ_le : CQ Q ≤ C_fine_target := by
    have h1 : CQ Q ≤ K * Real.rpow δ (-lam) := by
      simpa [hδ_def] using (hCQ_bounds Q hQ).1
    have h3 : C_fine_target = Real.rpow δbar (-lam_tail) := by
      simp only [C_fine_target, hδbar_eq] <;> rfl
    rw [h3]; exact le_trans h1 (le_trans hKδ hδbar_tail)
  let fineConfig_Q' := weaken_NiceConfiguration_C fineConfig_Q hCQ_le hC_fine_target_pos
  let fineConfig_B1_Q' : B1BridgeHypotheses (k - m) fineConfig_Q' :=
    { h_squares_unit := fineConfig_B1_Q.h_squares_unit
    , h_tubes_strip := fineConfig_B1_Q.h_tubes_strip
    , h_tubes_bounded := fineConfig_B1_Q.h_tubes_bounded }
  have hΔ1_lt_one : Δ 1 < 1 := by
    rw [←hΔ_coarse_eq]; exact hΔ_lt_one
  have h_scale_pos := fine_scale_positivity hm_eq2 hΔ1_lt_one hk_exp1 h_dyadic_anti
  have hm_pos := h_scale_pos.1
  have hk_pos := h_scale_pos.2.1
  have hm_lt_k := h_scale_pos.2.2
  have h_scale_sep : dyadicDelta (k - m) ≤ (dyadicDelta k)^τ := by
    have h1 : δbar ≤ Real.rpow δ τ := hδbar_le_δτ
    have h2 : δbar = dyadicDelta (k - m) := hδbar_eq
    rw [h2] at h1; simpa [hδ_def] using h1
  have h_small : Real.log (1 / dyadicDelta (k - m)) ≥ Real.rpow τ (-(C_P + C_n)) := by
    have h_eq : Real.log (1 / dyadicDelta (k - m)) = Real.log (1 / δbar) := by rw [hδbar_eq]
    rw [h_eq]
    exact small_log_bound hδbar_pos hδ_pos hτ hτ1 hδbar_le_δτ
      (by simpa [hδ_def] using h_eq89) hCn_ge1 hCP_fine_eq
  have hK_pos : 0 < K := by linarith [hK_ge1]
  have h_card_density_Q := h_card_density_all Q hQ
  have hδbar_le_dtail : dyadicDelta (k - m) ≤ δ_tail := by
    have h1 : δbar ≤ Real.rpow δ τ := hδbar_le_δτ
    have h2 : Real.rpow δ τ ≤ δ_tail := by simpa [hδ_def] using hδτ_le_dtail
    have h3 : δbar ≤ δ_tail := le_trans h1 h2
    exact hδbar_eq.symm ▸ h3
  have hlog_nonneg : 0 ≤ Real.log (1 / dyadicDelta (k - m)) := by
    apply Real.log_nonneg
    exact one_le_one_div (dyadicDelta_pos (k - m)) (dyadicDelta_le_one (k - m))
  have hscaleClass'_def_succ : ∀ (j : Fin n_fine), scaleClass' j = scaleClass j.succ := by
    intro j
    have h : scaleClass' j = scaleClass (shift j) := hscaleClass'_def j
    rw [hshift j] at h
    exact h
  have hC_between'_def_succ : ∀ (j : Fin n_fine), C_between' j = C_between j.succ := by
    intro j
    have h : C_between' j = C_between (shift j) := hC_between'_def j
    rw [hshift j] at h
    exact h
  rcases fine_branch_hcfg_fine
      (hn_fine_pos := by omega)
      (hm_pos := hm_pos)
      (hmk := hnm)
      (hlam := hlam)
      (hlam_tail_pos := hlam_tail_pos)
      (hτ_pos := hτ)
      (hτ_lt_one := hτ1)
      (hs_nonneg := by linarith)
      (config := config)
      (Δ := Δ)
      (scaleClass := scaleClass)
      (N := N)
      (C_between := C_between)
      (hcfg := hcfg)
      (K := K)
      (hK_pos := hK_pos)
      (hK_ge1 := hK_ge1)
      (coarseConfig := coarseConfig)
      (Q := Q)
      (hQ := hQ)
      (P := P)
      (hP_sub := hP_sub)
      (MQ := MQ)
      (hMQ := hMQ_Q_pos)
      (fineConfig := fineConfig_Q')
      (fineConfig_B1 := fineConfig_B1_Q')
      (hfine_P_eq := by
        simpa [fineConfig_Q', weaken_NiceConfiguration_C] using hfine_P_eq_Q)
      (hcoarse_P_eq := hcoarse_P_eq)
      (h_card_density := h_card_density_Q)
      (hΔ1_eq := hm_eq2)
      (Δ' := Δ')
      (hΔ'_def := hΔ'_def)
      (scaleClass' := scaleClass')
      (hscaleClass'_def := hscaleClass'_def_succ)
      (C_between' := C_between')
      (hC_between'_def := hC_between'_def_succ)
      (δ_tail := δ_tail)
      (hδ_tail_pos := hδ_tail_pos)
      (hδbar_le_dtail := hδbar_le_dtail)
      (h_absorb_normal := fun j hj => by
        have h1 : scaleClass (shift j) = ScaleClass.normal := by
          have h_eq : scaleClass' j = scaleClass (shift j) := hscaleClass'_def j
          rw [←h_eq]; exact hj
        have h := h_absorb_fine_normal K hK_ge1 hK_bound j h1
        have hC : (C_between (shift j) : ℝ) = C_between' j := (hC_between'_def j).symm
        rw [hC] at h
        exact h)
      (h_absorb_good := fun j t_j hj => by
        have h1 : scaleClass (shift j) = ScaleClass.good t_j := by
          have h_eq : scaleClass' j = scaleClass (shift j) := hscaleClass'_def j
          rw [←h_eq]; exact hj
        have h := h_absorb_fine_good K hK_ge1 hK_bound j t_j h1
        have hC : (C_between (shift j) : ℝ) = C_between' j := (hC_between'_def j).symm
        rw [hC] at h
        exact h)
      (C_n := C_n)
      (hCn_ge1 := hCn_ge1)
      (h_small := h_small)
      (hCP := hCP)
      (hCP_fine_eq := hCP_fine_eq)
      (hεG_pos := hεG)
      (hεN_pos := hεN)
      (hk_pos := hk_pos)
      (hm_lt_k := hm_lt_k)
      (h_scale_sep := h_scale_sep)
    with ⟨config'', C_between'', N'', hcfg_fine, hB1_fine, hT0_eq⟩
  have h_slope_fine : ∀ T ∈ config''.T₀, |T.slope| ≤ 1 :=
    fun T hT => fine_slope_bound hB1_fine T hT
  have h_tj_ge_t_fine : ∀ (j : Fin n_fine) (t_j : ℝ),
      scaleClass' j = ScaleClass.good t_j → t ≤ t_j := by
    intro j t_j hj
    have h_coarse : scaleClass (shift j) = ScaleClass.good t_j := by
      have h_eq : scaleClass' j = scaleClass (shift j) := hscaleClass'_def j
      rw [←h_eq]; exact hj
    exact hextra.h_tj_ge_t (shift j) t_j h_coarse
  have h_tj_le_two_fine : ∀ (j : Fin n_fine) (t_j : ℝ),
      scaleClass' j = ScaleClass.good t_j → t_j ≤ 2 := by
    intro j t_j hj
    have h_coarse : scaleClass (shift j) = ScaleClass.good t_j := by
      have h_eq : scaleClass' j = scaleClass (shift j) := hscaleClass'_def j
      rw [←h_eq]; exact hj
    exact hextra.h_tj_le_two (shift j) t_j h_coarse
  let hextra_fine : CombiningExtraHypotheses_v2 s t ε_G η ε_N C_P_fine ε_inc
      n_fine lam_tail (k - m) MQ_Q config'' Δ' scaleClass' :=
    { h_slope := h_slope_fine
    , h_tj_ge_t := h_tj_ge_t_fine
    , h_tj_le_two := h_tj_le_two_fine
    , hε_inc_pos := hextra.hε_inc_pos
    , h_exp_condition := hextra.h_exp_condition }
  have h_fine_ih := h_ih_bound (k - m) hδbar_le_dtail MQ_Q config''
    Δ' scaleClass' N'' C_between'' hcfg_fine hB1_fine hextra_fine
  -- h_card_ineq_Q is already a parameter
  have h_fine_bound : (fineConfig_Q.T₀.card : ℝ) ≥
      Real.rpow (Real.log (1 / dyadicDelta (k - m))) (-C_fine) * (MQ_Q : ℝ) *
      Real.rpow (dyadicDelta (k - m)) (C'_fine * lam_tail) *
      Real.rpow (dyadicDelta (k - m)) (-s + ε_N) * Pb := by
    have h_ih' : (config''.T₀.card : ENNReal) ≥
        ENNReal.ofReal (combiningLowerBound (dyadicDelta (k - m)) (MQ_Q : ℝ) C_fine C'_fine lam_tail s ε_N η n_fine Δ' scaleClass') := h_fine_ih
    have h_eq1 : (config''.T₀.card : ENNReal) = (fineConfig_Q.T₀.card : ENNReal) := by
      rw [hT0_eq] <;> rfl
    rw [h_eq1] at h_ih'
    have h_real : (fineConfig_Q.T₀.card : ℝ) ≥
        combiningLowerBound (dyadicDelta (k - m)) (MQ_Q : ℝ) C_fine C'_fine lam_tail s ε_N η n_fine Δ' scaleClass' := by
      exact_mod_cast h_ih'
    have h_eq : combiningLowerBound (dyadicDelta (k - m)) (MQ_Q : ℝ) C_fine C'_fine lam_tail s ε_N η n_fine Δ' scaleClass' =
        Real.rpow (Real.log (1 / dyadicDelta (k - m))) (-C_fine) * (MQ_Q : ℝ) *
        Real.rpow (dyadicDelta (k - m)) (C'_fine * lam_tail) *
        Real.rpow (dyadicDelta (k - m)) (-s + ε_N) * Pb := by
      simp [combiningLowerBound, hG'_def, hB'_def, hPb_def] <;> ring
    rw [h_eq] at h_real
    exact h_real
  have h_fine_bound' : (fineConfig_Q.T₀.card : ℝ) ≥
      Real.rpow (Real.log (1 / δbar)) (-C_fine) * (MQ_Q : ℝ) *
      Real.rpow δbar (C'_fine * lam_tail) *
      Real.rpow δbar (-s + ε_N) * Pb := by
    simpa [hδbar_eq] using h_fine_bound
  have hδ_le_one : δ ≤ 1 := by
    rw [hδ_def]; exact dyadicDelta_le_one k
  have hα_pos' : 0 < α := hα_pos
  have hMQ_pos' : 0 < (MQ_Q : ℝ) := by exact_mod_cast hMQ_Q_pos
  have h_card_ineq_Q' : K * (config.T₀.card : ℝ) * (MΔ : ℝ) * (MQ_Q : ℝ) ≥
      (coarseConfig.T₀.card : ℝ) * (fineConfig_Q.T₀.card : ℝ) * (M : ℝ) :=
    h_card_ineq_Q
  have h_main_raw : (config.T₀.card : ℝ) ≥
      Real.rpow (Real.log (1 / δ)) (-C) * (M : ℝ) *
      Real.rpow δ (C' * lam) * Real.rpow δ (-s + ε_N) * (PΔ * Pb) :=
    combine_bounds_fixed_tail
      hδ_pos hδ_le_one hΔ_coarse_pos hΔ_lt_one hδbar_pos hδbar_lt_one hδ_eq
      hs hεN
      hC_coarse_nonneg hC_fine_pos hC'_coarse_nonneg hC'_fine_pos hC'_pos
      hK_ge1
      hA_pos hα_pos' hK_poly hL_ge1 hL_ge_A
      (by exact_mod_cast hcfg.hM_pos)
      (by exact_mod_cast hMΔ_pos)
      hMQ_pos'
      h_card_ineq_Q'
      hPΔ_pos hPb_pos
      lam hlam lam_tail hlam_tail_pos
      hC'_final_ge
      h_coarse_bound
      h_fine_bound'
      C hC_pos hC_ge_final
  have h_main : (config.T₀.card : ℝ) ≥
      Real.rpow (Real.log (1 / dyadicDelta k)) (-C) * (M : ℝ) *
      Real.rpow (dyadicDelta k) (C' * lam) * Real.rpow (dyadicDelta k) (-s + ε_N) * (PΔ * Pb) := by
    rw [hδ_def] at h_main_raw
    exact h_main_raw
  have h_final : (config.T₀.card : ℝ) ≥
      combiningLowerBound (dyadicDelta k) (M : ℝ) C C' lam s ε_N η (n_fine + 1) Δ scaleClass := by
    rw [h_product]
    exact h_main
  have h_ennreal : ENNReal.ofReal (combiningLowerBound (dyadicDelta k) (M : ℝ) C C' lam s ε_N η (n_fine + 1) Δ scaleClass) ≤
      (config.T₀.card : ENNReal) := by
    have h1 : ENNReal.ofReal (combiningLowerBound (dyadicDelta k) (M : ℝ) C C' lam s ε_N η (n_fine + 1) Δ scaleClass) ≤
        ENNReal.ofReal (config.T₀.card : ℝ) := ENNReal.ofReal_le_ofReal h_final
    have h2 : ENNReal.ofReal (config.T₀.card : ℝ) = (config.T₀.card : ENNReal) := by
      simp
    rw [h2] at h1
    exact h1
  simpa using h_ennreal

end DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure
