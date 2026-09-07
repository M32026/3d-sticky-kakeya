module

/-
  BranchDispatch — Extracts the by_cases and both branch calls from _Body.

  Contains the arithmetic setup and all-tail-bad / non-all-bad dispatch.
  Reduces _Body proof body size to avoid memory exhaustion.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.AllBadBranchComplete
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.NonAllBadBranch
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.InductiveStepCore_v2_Helpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.BodyArithmetic
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.ProductArithmeticBundle
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


/-- Branch dispatch: arithmetic setup + by_cases all-tail-bad / non-all-bad. -/
lemma branch_dispatch
    {n_fine k m M MΔ : ℕ}
    {s t τ ε_G η ε_N C_P C_P_fine C_n : ℝ}
    {C_fine C'_fine C C' : ℝ}
    {lam lam_tail δ_tail ε_inc : ℝ}
    {K A α Δ_coarse δ δbar PΔ : ℝ}
    {CΔ K_p5 : ℝ}
    {C_coarse C'_coarse : ℝ}
    {CQ : DyadicSquare m → ℝ}
    {config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M}
    {coarseConfig : CTNiceConfiguration m s CΔ MΔ}
    {P : Finset (DyadicSquare k)}
    {Q : DyadicSquare m}
    (hnm : m ≤ k)
    (hC'_coarse_eq1 : C'_coarse = 1)
    (hC_coarse_nonneg : 0 ≤ C_coarse)
    (Δ : Fin (n_fine + 2) → ℝ)
    (scaleClass : Fin (n_fine + 1) → ScaleClass)
    (N : Fin (n_fine + 1) → ℕ)
    (C_between : Fin (n_fine + 1) → ℝ)
    (j0 : Fin (n_fine + 1))
    (shift : Fin n_fine → Fin (n_fine + 1))
    (hshift : ∀ j, shift j = Fin.succ j)
    (MQ : DyadicSquare m → ℕ)
    (hQ : Q ∈ coarseConfig.P₀)
    (fineConfig_Q : CTNiceConfiguration (k - m) s (CQ Q) (MQ Q))
    (fineConfig_B1_Q : B1BridgeHypotheses (k - m) fineConfig_Q)
    -- Arithmetic inputs
    (hK_bound : K ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7)
    (hA_eq : A = 2700 * 3145728 * (8 / Real.log 2)^7)
    (hk_exp1 : dyadicDelta k ≤ Real.exp (-1))
    (hk : dyadicDelta k ≤ Real.exp (-A))
    (hK_p5_ge1 : 1 ≤ K_p5)
    (hCP : 1 ≤ C_P)
    (hC'_fine_pos : 0 < C'_fine)
    (hC'_ge : C' ≥ (1 : ℝ) + 2 * C'_fine / τ)
    (hτ : 0 < τ)
    (hlam : 0 < lam)
    (hτ_lam_tail : τ * lam_tail = 2 * lam)
    (hC_fine_pos : 0 < C_fine)
    (hC_ge : C ≥ (1 + (7 : ℝ)) * (1 + (1 : ℝ) + C'_fine) + K_p5 + C_P + 8 + C_fine)
    (hδ_def : δ = dyadicDelta k)
    (hδbar_eq : δbar = dyadicDelta (k - m))
    (hδ_eq : (dyadicDelta k) = Δ_coarse * δbar)
    (hj0 : j0 = 0)
    -- B1 outputs
    (hK_ge1 : 1 ≤ K)
    (hK_pos : 0 < K)
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
    -- Specialized Q-facts
    (hfine_P_eq' : fineConfig_Q.P₀ =
        (P.filter (fun p => InductionConfigurations.squareContained hnm p Q)).image
          (InductionConfigurations.squareHomothety hnm Q))
    (h_card_ineq' : K * (config.T₀.card : ℝ) * (MΔ : ℝ) * (MQ Q : ℝ) ≥
        (coarseConfig.T₀.card : ℝ) * fineConfig_Q.T₀.card * (M : ℝ))
    (h_slope_coarse : ∀ T ∈ coarseConfig.T₀, |T.slope| ≤ 1)
    (hMQ : ∀ Q ∈ coarseConfig.P₀, 0 < MQ Q)
    (hMΔ : 0 < MΔ)
    -- Coarse bound outputs
    (hcoarse_P_nonempty : coarseConfig.P₀.Nonempty)
    (hΔ_coarse_pos : 0 < Δ_coarse)
    (hΔ_coarse_eq : Δ_coarse = Δ 1)
    (hΔ_lt_one : Δ_coarse < 1)
    (hδbar_pos : 0 < δbar)
    (hδbar_lt_one : δbar < 1)
    (hδ_pos2 : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hPΔ_pos : 0 < PΔ)
    (h_coarse_bound : (coarseConfig.T₀.card : ℝ) ≥
        Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
        Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
        Real.rpow Δ_coarse (-s + ε_N) * PΔ)
    -- Product bundle inputs
    (G0 B0 : Finset (Fin (n_fine + 1)))
    (hG0_def : G0 = ({j0} : Finset (Fin (n_fine + 1))).filter (fun j => (scaleClass j).isGood))
    (hB0_def : B0 = ({j0} : Finset (Fin (n_fine + 1))).filter (fun j => (scaleClass j).isBad))
    (hPΔ_def : PΔ = (∏ j ∈ G0, Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η) *
                      (∏ j ∈ B0, Δ (Fin.succ j) / Δ j.castSucc))
    -- Exact identities
    (hα_eq : α = 7)
    (hC_coarse_def : C_coarse = if m = 1 then 0 else K_p5 + C_P + 8)
    -- Original hypotheses
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
    (hCP_fine : 1 ≤ C_P_fine)
    (hCn_ge1 : 1 ≤ C_n)
    (hCP_fine_eq : C_P_fine = C_P + 2 * C_n)
    (hlam_tail_pos : 0 < lam_tail)
    (hδ_tail_pos : 0 < δ_tail)
    (hδτ_le_dtail : Real.rpow (dyadicDelta k) τ ≤ δ_tail)
    (h_poly_K_le_δlam : (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 ≤ Real.rpow (dyadicDelta k) (-lam))
    (h_k_large : (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 ≥ Real.rpow 2 (s + η - ε_N))
    (hA_pos : 0 < A)
    (hA_ge1 : 1 ≤ A)
    (hα_pos : 0 < α)
    (hC_pos : 0 < C)
    (hC'_pos : 0 < C')
    (hm_eq2 : Δ 1 = dyadicDelta m)
    (hs : 0 < s) (hst : s < t) (hs1 : s < 1)
    (hτ1 : τ < 1) (hεG : 0 < ε_G) (hη : 0 < η) (hεN : 0 < ε_N)
    (h_absorb_fine_normal : ∀ (K : ℝ), 1 ≤ K →
      K ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7 →
      ∀ (j : Fin n_fine), scaleClass ⟨j.val + 1, by omega⟩ = ScaleClass.normal →
        9 * (C_between ⟨j.val + 1, by omega⟩) * 2 * K *
          (24 * Real.log (1 / dyadicDelta (k - m)) / ((n_fine : ℕ) : ℝ)) ^ n_fine *
          (4 : ℝ) ^ n_fine ≤
        Real.log (1 / dyadicDelta (k - m)) ^ C_P_fine *
          (Δ ⟨j.val + 1, by omega⟩ / Δ ⟨j.val + 2, by omega⟩) ^ ε_N)
    (h_absorb_fine_good : ∀ (K : ℝ), 1 ≤ K →
      K ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7 →
      ∀ (j : Fin n_fine) (t_j : ℝ), scaleClass ⟨j.val + 1, by omega⟩ = ScaleClass.good t_j →
        9 * (C_between ⟨j.val + 1, by omega⟩) * 2 * K *
          (24 * Real.log (1 / dyadicDelta (k - m)) / ((n_fine : ℕ) : ℝ)) ^ n_fine *
          (4 : ℝ) ^ n_fine ≤
        Real.log (1 / dyadicDelta (k - m)) ^ C_P_fine *
          (Δ ⟨j.val + 1, by omega⟩ / Δ ⟨j.val + 2, by omega⟩) ^ ε_G)
    (hΔn_lt_Δ1 : Δ (Fin.last (n_fine + 1)) < Δ 1)
    (h2 : 2 ≤ n_fine + 1) :
    (config.T₀.card : ENNReal) ≥
      ENNReal.ofReal (combiningLowerBound (dyadicDelta k) (M : ℝ) C C' lam s ε_N η (n_fine + 1) Δ scaleClass) := by
  -- Product arithmetic bundle (computed internally)
  rcases product_arithmetic_bundle
      Δ scaleClass N C_between config hcfg j0 (by simp [hj0]) G0 B0
      hG0_def hB0_def PΔ hPΔ_pos hPΔ_def
    with ⟨Δ', scaleClass', N', C_between', G', B', Pb,
      hΔ'_def, hscaleClass'_def, hN'_def, hC_between'_def, hG'_def, hB'_def,
      hPb_def, hPb_pos, _, _, h_product⟩
  -- Rewrite G'/B' definitions for all_bad_branch_complete (expects scaleClass (Fin.succ j))
  have hG'_def_allbad : G' = Finset.univ.filter (fun j : Fin n_fine => (scaleClass (Fin.succ j)).isGood) := by
    rw [hG'_def]
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hscaleClass'_def]
  have hB'_def_allbad : B' = Finset.univ.filter (fun j : Fin n_fine => (scaleClass (Fin.succ j)).isBad) := by
    rw [hB'_def]
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hscaleClass'_def]
  -- Convert Δ-based absorption hypotheses to Δ'-based for NonAllBadBranch
  have h_j1_eq : ∀ (j : Fin n_fine), (Fin.castAdd 1 j).succ = (⟨j.val + 1, by omega⟩ : Fin (n_fine + 2)) := by
    intro j; apply Fin.ext; simp
  have h_j2_eq : ∀ (j : Fin n_fine), (Fin.succ j).succ = (⟨j.val + 2, by omega⟩ : Fin (n_fine + 2)) := by
    intro j; apply Fin.ext; simp
  have h_ratio_eq : ∀ (j : Fin n_fine),
      Δ' j.castSucc / Δ' (Fin.succ j) = Δ ⟨j.val + 1, by omega⟩ / Δ ⟨j.val + 2, by omega⟩ := by
    intro j
    have h1 : Δ' j.castSucc = Δ (Fin.castAdd 1 j).succ / Δ 1 := hΔ'_def j.castSucc
    have h2 : Δ' (Fin.succ j) = Δ (Fin.succ (Fin.succ j)) / Δ 1 := hΔ'_def (Fin.succ j)
    have hΔ1_pos : 0 < Δ 1 := hcfg.hΔ_pos 1
    have h3 : (Δ (Fin.castAdd 1 j).succ / Δ 1) / (Δ (Fin.succ (Fin.succ j)) / Δ 1) =
        Δ (Fin.castAdd 1 j).succ / Δ (Fin.succ (Fin.succ j)) := by
      field_simp [hΔ1_pos.ne'] <;> ring
    rw [h1, h2, h3, h_j1_eq j, h_j2_eq j]
  have h_shift_j_eq : ∀ (j : Fin n_fine), shift j = (⟨j.val + 1, by omega⟩ : Fin (n_fine + 1)) := by
    intro j
    rw [hshift j] <;> apply Fin.ext <;> simp
  have h_absorb_fine_normal' : ∀ (K : ℝ), 1 ≤ K →
      K ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7 →
      ∀ (j : Fin n_fine), scaleClass (shift j) = ScaleClass.normal →
        9 * (C_between (shift j)) * 2 * K *
          (24 * Real.log (1 / dyadicDelta (k - m)) / ((n_fine : ℕ) : ℝ)) ^ n_fine *
          (4 : ℝ) ^ n_fine ≤
        Real.log (1 / dyadicDelta (k - m)) ^ C_P_fine *
          (Δ' j.castSucc / Δ' (Fin.succ j)) ^ ε_N := by
    intro K hK1 hK2 j hj
    have h_shift := h_shift_j_eq j
    have h_scale : scaleClass ⟨j.val + 1, by omega⟩ = ScaleClass.normal := by
      rw [←h_shift]; exact hj
    have h_main := h_absorb_fine_normal K hK1 hK2 j h_scale
    have h_cbet : C_between (shift j) = C_between ⟨j.val + 1, by omega⟩ := by rw [h_shift]
    rw [h_cbet, h_ratio_eq j]
    exact h_main
  have h_absorb_fine_good' : ∀ (K : ℝ), 1 ≤ K →
      K ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7 →
      ∀ (j : Fin n_fine) (t_j : ℝ), scaleClass (shift j) = ScaleClass.good t_j →
        9 * (C_between (shift j)) * 2 * K *
          (24 * Real.log (1 / dyadicDelta (k - m)) / ((n_fine : ℕ) : ℝ)) ^ n_fine *
          (4 : ℝ) ^ n_fine ≤
        Real.log (1 / dyadicDelta (k - m)) ^ C_P_fine *
          (Δ' j.castSucc / Δ' (Fin.succ j)) ^ ε_G := by
    intro K hK1 hK2 j t_j hj
    have h_shift := h_shift_j_eq j
    have h_scale : scaleClass ⟨j.val + 1, by omega⟩ = ScaleClass.good t_j := by
      rw [←h_shift]; exact hj
    have h_main := h_absorb_fine_good K hK1 hK2 j t_j h_scale
    have h_cbet : C_between (shift j) = C_between ⟨j.val + 1, by omega⟩ := by rw [h_shift]
    rw [h_cbet, h_ratio_eq j]
    exact h_main
  have hδ_eq2 : (dyadicDelta k) = Δ_coarse * dyadicDelta (k - m) := by
    have h1 : (dyadicDelta k) = Δ_coarse * δbar := hδ_eq
    rw [h1, hδbar_eq]
  have hK_poly : K ≤ A * (Real.log (1 / dyadicDelta k)) ^ α :=
    k_poly_bound_spec k K A α hA_eq hK_bound hk_exp1 hα_eq
  have hL_ge1 : 1 ≤ Real.log (1 / dyadicDelta k) :=
    log_one_over_dyadic_ge_one_bound k hk_exp1
  have hL_ge_A : Real.log (1 / dyadicDelta k) ≥ A :=
    log_one_over_dyadic_ge_A k A hk
  have hC'_coarse_nonneg : 0 ≤ (C'_coarse : ℝ) := by
    rw [hC'_coarse_eq1] <;> norm_num
  have hC'_coarse_ge1 : 1 ≤ C'_coarse := by
    rw [hC'_coarse_eq1] <;> norm_num
  have hC'_final_ge : C' * lam ≥ (C'_coarse : ℝ) * lam + C'_fine * lam_tail := by
    have h1 : C'_coarse = 1 := hC'_coarse_eq1
    rw [h1]
    exact C_prime_final_ge_helper C' C'_fine lam lam_tail τ hC'_ge hτ hlam hτ_lam_tail
  have hC_ge_final : C ≥ (1 + α) * ((C'_coarse : ℝ) + 1) + C_coarse + C_fine := by
    rw [hα_eq, hC'_coarse_eq1, hC_coarse_def]
    exact C_ge_final_helper C C'_fine C_fine K_p5 C_P m hC_ge hC'_fine_pos hK_p5_ge1 hCP
  let all_tail_bad : Prop := ∀ j ∈ (Finset.univ.erase j0), (scaleClass j).isBad
  have h_isBad_iff : ∀ (x : Fin (n_fine + 1)), (scaleClass x).isBad ↔ scaleClass x = .bad := by
    intro x
    constructor
    · intro h
      cases h2 : scaleClass x
      · simp [ScaleClass.isBad, h2] at h
      · simp [ScaleClass.isBad, h2] at h
      · rfl
    · intro h
      rw [h] <;> rfl
  have hδ_eq' : δ = Δ_coarse * δbar := by
    rw [hδ_def, hδbar_eq]
    exact hδ_eq2
  by_cases h_all_bad : all_tail_bad
  · -- ALL-TAIL-BAD BRANCH
    have hC_ge_simple : C ≥ C_coarse + (1 + α) * (C'_coarse + 1) := by
      calc
        C_coarse + (1 + α) * (C'_coarse + 1)
            = (1 + α) * (C'_coarse + 1) + C_coarse + 0 := by ring
        _ ≤ (1 + α) * (C'_coarse + 1) + C_coarse + C_fine := by
          exact add_le_add_right hC_fine_pos.le _
        _ ≤ C := hC_ge_final
    have hC'_lam_ge : C'_coarse * lam ≤ C' * lam := by
      calc
        C'_coarse * lam ≤ C'_coarse * lam + C'_fine * lam_tail := by
          exact le_add_of_nonneg_right (mul_nonneg hC'_fine_pos.le hlam_tail_pos.le)
        _ ≤ C' * lam := hC'_final_ge
    exact all_bad_branch_complete
      (config := config)
      (coarseConfig := coarseConfig)
      (fineConfig_Q := fineConfig_Q)
      (P := P)
      (Q := Q)
      (Δ := Δ)
      (scaleClass := scaleClass)
      (Δ' := Δ')
      (G' := G')
      (B' := B')
      (j0 := j0)
      (hnm := hnm)
      (hj0 := hj0)
      (h_all_bad := h_all_bad)
      (hΔ_pos := hcfg.hΔ_pos)
      (hΔ_end := hcfg.hΔ_end)
      (hm_eq2 := hm_eq2)
      (hΔ'_def := hΔ'_def)
      (hG'_def := hG'_def_allbad)
      (hB'_def := hB'_def_allbad)
      (hPb_def := hPb_def)
      (hδbar_eq := hδbar_eq)
      (hδbar_pos := hδbar_pos)
      (hδbar_lt_one := hδbar_lt_one)
      (hδ_pos := hδ_pos2)
      (hδ_lt_one := hδ_lt_one)
      (hδ_eq := hδ_eq')
      (hΔ_coarse_pos := hΔ_coarse_pos)
      (hΔ_lt_one := hΔ_lt_one)
      (hK_pos := hK_pos)
      (hK_ge1 := hK_ge1)
      (hM_pos := hcfg.hM_pos)
      (hMΔ_pos := hMΔ)
      (hMQ_pos := hMQ Q hQ)
      (hPΔ_pos := hPΔ_pos)
      (hP_sub := hP_sub)
      (hcoarse_P_eq := hcoarse_P_eq)
      (hQ := hQ)
      (hfine_P_eq := hfine_P_eq')
      (h_card_ineq := h_card_ineq')
      (h_coarse_bound := h_coarse_bound)
      (hL_ge1 := by simpa [hδ_def] using hL_ge1)
      (hL_ge_A := by simpa [hδ_def] using hL_ge_A)
      (hK_poly := by simpa [hδ_def] using hK_poly)
      (hC_coarse_nonneg := hC_coarse_nonneg)
      (hC'_coarse_ge1 := hC'_coarse_ge1)
      (hC_pos := hC_pos)
      (hC_ge_simple := hC_ge_simple)
      (hC'_lam_ge := hC'_lam_ge)
      (hs1 := hs1)
      (hεN := hεN)
      (hA_pos := hA_pos)
      (hα_pos := hα_pos)
      (h_product := h_product)
      (hδ_def := hδ_def)
  · -- NON-ALL-BAD BRANCH
    exact non_all_bad_branch
      (hnm := hnm)
      (CQ := CQ)
      (config := config)
      (coarseConfig := coarseConfig)
      (fineConfig_Q := fineConfig_Q)
      (fineConfig_B1_Q := fineConfig_B1_Q)
      (P := P)
      (Q := Q)
      (hQ := hQ)
      (Δ := Δ)
      (scaleClass := scaleClass)
      (N := N)
      (C_between := C_between)
      (Δ' := Δ')
      (scaleClass' := scaleClass')
      (N' := N')
      (C_between' := C_between')
      (j0 := j0)
      (shift := shift)
      (hshift := hshift)
      (MQ := MQ)
      (hMQ := hMQ)
      (hMΔ_pos := hMΔ)
      (G' := G')
      (B' := B')
      (hG'_def := hG'_def)
      (hB'_def := hB'_def)
      (hPb_def := hPb_def)
      (hs := hs) (hst := hst) (hs1 := hs1)
      (hτ := hτ) (hτ1 := hτ1)
      (hεG := hεG) (hη := hη) (hεN := hεN)
      (hCP := hCP) (hCP_fine := hCP_fine)
      (hCn_ge1 := hCn_ge1)
      (hCP_fine_eq := hCP_fine_eq)
      (hC_fine_pos := hC_fine_pos) (hC'_fine_pos := hC'_fine_pos)
      (hlam := hlam) (hlam_tail_pos := hlam_tail_pos)
      (hτ_lam_tail := hτ_lam_tail)
      (hδ_tail_pos := hδ_tail_pos)
      (hδτ_le_dtail := hδτ_le_dtail)
      (h_poly_K_le_δlam := h_poly_K_le_δlam)
      (h_k_large := h_k_large)
      (A := A) (hA_pos := hA_pos) (hA_ge1 := hA_ge1)
      (hA_eq := hA_eq)
      (hC_pos := hC_pos) (hC'_pos := hC'_pos)
      (hC_ge := hC_ge) (hC'_ge := hC'_ge)
      (hk := hk)
      (hm_eq2 := hm_eq2)
      (hcfg := hcfg)
      (hB1 := hB1)
      (hextra := hextra)
      (h_ih_bound := h_ih_bound)
      (ε_inc := ε_inc)
      (h_eq89 := h_eq89)
      (K_p5 := K_p5) (hK_p5_ge1 := hK_p5_ge1)
      (hK_ge1 := hK_ge1) (hK_bound := hK_bound)
      (hP_sub := hP_sub)
      (hcoarse_P_eq := hcoarse_P_eq)
      (h_card_density_all := h_card_density_all)
      (hCΔ_bounds1 := hCΔ_bounds1)
      (hCΔ_bounds2 := hCΔ_bounds2)
      (hCQ_bounds := hCQ_bounds)
      (hfine_P_eq_Q := hfine_P_eq')
      (h_card_ineq_Q := h_card_ineq')
      (h_slope_coarse := h_slope_coarse)
      (hΔ_coarse_pos := hΔ_coarse_pos)
      (hΔ_lt_one := hΔ_lt_one)
      (hδbar_pos := hδbar_pos)
      (hδbar_lt_one := hδbar_lt_one)
      (hδbar_eq := hδbar_eq)
      (hδ_pos := hδ_pos2)
      (hδ_lt_one := hδ_lt_one)
      (hδ_def := hδ_def)
      (hδ_eq := hδ_eq')
      (hPΔ_pos := hPΔ_pos)
      (hPb_pos := hPb_pos)
      (h_coarse_bound := h_coarse_bound)
      (C_coarse := C_coarse)
      (C'_coarse := C'_coarse)
      (hC_coarse_nonneg := hC_coarse_nonneg)
      (hC'_coarse_nonneg := hC'_coarse_nonneg)
      (hC'_final_ge := hC'_final_ge)
      (hC_ge_final := hC_ge_final)
      (hK_poly := by simpa [hδ_def] using hK_poly)
      (hL_ge1 := by simpa [hδ_def] using hL_ge1)
      (hL_ge_A := by simpa [hδ_def] using hL_ge_A)
      (hα_pos := hα_pos)
      (h_product := h_product)
      (hΔ'_def := hΔ'_def)
      (hscaleClass'_def := fun j => by rw [hscaleClass'_def j, hshift j])
      (hC_between'_def := fun j => by rw [hC_between'_def j, hshift j])
      (hj0 := hj0)
      (h_not_all_bad := h_all_bad)
      (h_absorb_fine_normal := h_absorb_fine_normal')
      (h_absorb_fine_good := h_absorb_fine_good')
      (hΔn_lt_Δ1 := hΔn_lt_Δ1)
      (hk_exp1 := hk_exp1)
      (hΔ_coarse_eq := hΔ_coarse_eq)
      (hn_fine := by omega)

end DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure
