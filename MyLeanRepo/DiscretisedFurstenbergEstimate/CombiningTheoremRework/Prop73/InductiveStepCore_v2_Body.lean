module

/-
  Inductive Step Core v2 Body — Proof body extracted as top-level lemma.

  This module contains the proof body of inductive_step_core_v2 as a standalone
  lemma to avoid proof term size issues in the main theorem declaration.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.InductiveStepCore_v2_Helpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.TailSplit
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.FineConfigSublemma
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseSourceData
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseGeometricData
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseSsetConversion
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.BetweenScalesToSset
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseBoundDispatcher
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.FineConfigThinning
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.NormalCoarseBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.GoodCoarseBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.GoodCaseImprovedIncidence
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.FineBranchHcfgFine
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.AllBadAbsorption
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.AllBadBranch
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.AllBadBranchComplete
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.NonAllBadBranch
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseBoundAssembly
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.ProductSplittingExtra
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.ProductArithmeticBundle
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.BranchDispatch
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseBoundWrapper
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.NonAllBadArithmetic
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

/-- Weaken the C constant of a NiceConfiguration. -/
lemma inductive_step_core_v2_body
    {s t τ ε_G η ε_N C_P C_P_fine : ℝ} {n k M : ℕ}
    {C_fine C'_fine C C' : ℝ}
    (m : ℕ)
    (hs : 0 < s) (hst : s < t) (hs1 : s < 1)
    (hτ : 0 < τ) (hτ1 : τ < 1)
    (hεG : 0 < ε_G) (hη : 0 < η)
    (hεN : 0 < ε_N) (hεN_le : ε_N ≤ ε_G)
    (hCP : 1 ≤ C_P) (hCP_fine : 1 ≤ C_P_fine)
    (C_n : ℝ) (hCn_ge1 : 1 ≤ C_n)
    (hCP_fine_eq : C_P_fine = C_P + 2 * C_n)
    (h2 : 2 ≤ n)
    (hC_fine_pos : 0 < C_fine) (hC'_fine_pos : 0 < C'_fine)
    (K_p5 : ℝ) (hK_p5_ge1 : 1 ≤ K_p5)
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
    (ε_inc : ℝ)
    (h_eq89 : Real.log (1 / dyadicDelta k) ≥ Real.rpow τ (-(C_P_fine : ℝ)))
    (lam : ℝ) (hlam : 0 < lam)
    -- Pre-applied IH at fixed lam_tail = 2λ/τ, at C_P_fine
    (lam_tail : ℝ) (hlam_tail_pos : 0 < lam_tail)
    (hτ_lam_tail : τ * lam_tail = 2 * lam)
    (δ_tail : ℝ) (hδ_tail_pos : 0 < δ_tail)
    (h_ih_bound : ∀ (k' : ℕ), dyadicDelta k' ≤ δ_tail →
      ∀ (M' : ℕ)
        (config' : CTNiceConfiguration k' s (Real.rpow (dyadicDelta k') (-lam_tail)) M')
        (Δ' : Fin ((n - 1) + 1) → ℝ)
        (scaleClass' : Fin (n - 1) → ScaleClass)
        (N' : Fin (n - 1) → ℕ)
        (C_between' : Fin (n - 1) → ℝ),
        CombiningConfig s t τ (n - 1) ε_G η lam_tail ε_N C_P_fine C_between' k' M' config' Δ' scaleClass' N' →
        B1BridgeHypotheses k' config' →
        CombiningExtraHypotheses_v2 s t ε_G η ε_N C_P_fine ε_inc (n - 1) lam_tail k' M' config' Δ' scaleClass' →
        (config'.T₀.card : ENNReal) ≥
          ENNReal.ofReal (combiningLowerBound (dyadicDelta k') (M' : ℝ) C_fine C'_fine lam_tail s ε_N η (n - 1) Δ' scaleClass'))
    (hδτ_le_dtail : Real.rpow (dyadicDelta k) τ ≤ δ_tail)
    (h_poly_K_le_δlam : (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 ≤ Real.rpow (dyadicDelta k) (-lam))
    (h_k_large : (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 ≥ Real.rpow 2 (s + η - ε_N))
    {A : ℝ} (hA_pos : 0 < A) (hA_ge1 : 1 ≤ A)
    (hA_eq : A = 2700 * 3145728 * (8 / Real.log 2)^7)
    (hC_pos : 0 < C) (hC'_pos : 0 < C')
    (hC_ge : C ≥ (1 + (7 : ℝ)) * (1 + (1 : ℝ) + C'_fine) + K_p5 + C_P + 8 + C_fine)
    (hC'_ge : C' ≥ (1 : ℝ) + 2 * C'_fine / τ)
    (hk : dyadicDelta k ≤ Real.exp (-A))
    (config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M)
    (Δ : Fin (n + 1) → ℝ)
    (hm_eq2 : Δ 1 = dyadicDelta m)
    (scaleClass : Fin n → ScaleClass)
    (N : Fin n → ℕ)
    (C_between : Fin n → ℝ)
    -- log(1/Δ_m)^(C_P+8) ≥ K_p5 * C_P_coarse_upper * 13 * 2^s * Δ_m^ε_N
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
    (h_absorb_fine_normal : ∀ (K : ℝ), 1 ≤ K →
      K ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7 →
      ∀ (j : Fin (n - 1)), scaleClass ⟨j.val + 1, by omega⟩ = ScaleClass.normal →
        9 * (C_between ⟨j.val + 1, by omega⟩) * 2 * K *
          (24 * Real.log (1 / dyadicDelta (k - m)) / ((n - 1 : ℕ) : ℝ)) ^ (n - 1) *
          (4 : ℝ) ^ (n - 1) ≤
        Real.log (1 / dyadicDelta (k - m)) ^ C_P_fine *
          (Δ ⟨j.val + 1, by omega⟩ / Δ ⟨j.val + 2, by omega⟩) ^ ε_N)
    (h_absorb_fine_good : ∀ (K : ℝ), 1 ≤ K →
      K ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7 →
      ∀ (j : Fin (n - 1)) (t_j : ℝ), scaleClass ⟨j.val + 1, by omega⟩ = ScaleClass.good t_j →
        9 * (C_between ⟨j.val + 1, by omega⟩) * 2 * K *
          (24 * Real.log (1 / dyadicDelta (k - m)) / ((n - 1 : ℕ) : ℝ)) ^ (n - 1) *
          (4 : ℝ) ^ (n - 1) ≤
        Real.log (1 / dyadicDelta (k - m)) ^ C_P_fine *
          (Δ ⟨j.val + 1, by omega⟩ / Δ ⟨j.val + 2, by omega⟩) ^ ε_G)
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
          ENNReal.ofReal (Real.rpow (dyadicDelta m) (-(2 * s + ε_inc))))
    (hcfg : CombiningConfig s t τ n ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    (hB1 : B1BridgeHypotheses k config)
    (h_uniform : UniformIncidenceData s t ε_inc)
    (hextra : CombiningExtraHypotheses_v2 s t ε_G η ε_N C_P ε_inc n lam k M config Δ scaleClass)
    (n_fine : ℕ)
    (h_n_eq : n = n_fine + 1) :
    (config.T₀.card : ENNReal) ≥
      ENNReal.ofReal (combiningLowerBound (dyadicDelta k) (M : ℝ) C C' lam s ε_N η n Δ scaleClass) := by
    subst h_n_eq
    let n : ℕ := n_fine + 1
    let C'_coarse : ℝ := 1
    let C_coarse : ℝ := if m = 1 then 0 else K_p5 + C_P + 8
    let α : ℝ := 7
    have hk_exp1 : dyadicDelta k ≤ Real.exp (-1) := by
      have hA_ge1' : 1 ≤ A := hA_ge1
      have h : Real.exp (-A) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      exact le_trans hk h
    have hΔn_lt_Δ1 : Δ (Fin.last n) < Δ 1 := delta_last_lt_delta_one hcfg (by omega)
    have hnm : m ≤ k := by
      have h_end : Δ (Fin.last n) = dyadicDelta k := hcfg.hΔ_end
      have h_gt : dyadicDelta m > dyadicDelta k := by
        rw [←hm_eq2, ←h_end]; exact hΔn_lt_Δ1
      have hmk : m < k := dyadicDelta_strict_anti h_gt
      exact le_of_lt hmk
    have h_squares_unit := hB1.h_squares_unit
    have h_tubes_strip := hB1.h_tubes_strip
    have h_tubes_bounded := hB1.h_tubes_bounded
    have hC1_ge1 : 1 ≤ Real.rpow (dyadicDelta k) (-lam) := c1_ge1_spec k lam hlam
    have hP0_nonempty : config.P₀.Nonempty := by
      have hps : config.pointSet.Nonempty := hcfg.h_uniform.1
      rcases hps with ⟨x, hx⟩
      have h_exists : ∃ (p : _), p ∈ config.P₀ ∧ x ∈ p.toSet := by
        simpa [NiceConfiguration.pointSet, Set.mem_iUnion] using hx
      rcases h_exists with ⟨p, hp, _⟩
      exact ⟨p, hp⟩
    classical
    let h_b1 := b1_bridge_decomposition hnm s (by linarith) (by linarith)
        (Real.rpow (dyadicDelta k) (-lam)) hC1_ge1 M hcfg.hM_pos config
        hP0_nonempty h_squares_unit h_tubes_strip h_tubes_bounded
    let K := Classical.choose h_b1
    have hK_spec := Classical.choose_spec h_b1
    have hK_ge1 := hK_spec.1
    have hK_bound := hK_spec.2.1
    have h_exists_P := hK_spec.2.2
    let P := Classical.choose h_exists_P
    have hP_spec := Classical.choose_spec h_exists_P
    have hP_sub : P ⊆ config.P₀ := Classical.choose hP_spec
    have h_after_P := Classical.choose_spec hP_spec
    let tubeFamily := Classical.choose h_after_P
    have h_after_tube := Classical.choose_spec h_after_P
    let CΔ := Classical.choose h_after_tube
    have h_after_CΔ := Classical.choose_spec h_after_tube
    let MΔ := Classical.choose h_after_CΔ
    have h_after_MΔ := Classical.choose_spec h_after_CΔ
    have hMΔ : 0 < MΔ := Classical.choose h_after_MΔ
    have h_after_hMΔ := Classical.choose_spec h_after_MΔ
    let coarseConfig := Classical.choose h_after_hMΔ
    have h_after_coarse := Classical.choose_spec h_after_hMΔ
    let CQ := Classical.choose h_after_coarse
    have h_after_CQ := Classical.choose_spec h_after_coarse
    let MQ := Classical.choose h_after_CQ
    have h_after_MQ := Classical.choose_spec h_after_CQ
    have hMQ : ∀ Q ∈ coarseConfig.P₀, 0 < MQ Q := Classical.choose h_after_MQ
    have h_after_hMQ := Classical.choose_spec h_after_MQ
    let fineConfig := Classical.choose h_after_hMQ
    have h_after_fine := Classical.choose_spec h_after_hMQ
    let fineConfig_B1 := Classical.choose h_after_fine
    have h_all_props := Classical.choose_spec h_after_fine
    have hP_nonempty' := h_all_props.1
    have hcoarse_P_eq := h_all_props.2.1
    have h_card_bound := h_all_props.2.2.1
    have h_card_density_all := h_all_props.2.2.2.1
    have h_tubeFamily_data := h_all_props.2.2.2.2.1
    have hCΔ_bounds1 := h_all_props.2.2.2.2.2.1
    have hCΔ_bounds2 := h_all_props.2.2.2.2.2.2.1
    have hCQ_bounds := h_all_props.2.2.2.2.2.2.2.1
    have h_intersection_data := h_all_props.2.2.2.2.2.2.2.2.1
    have h_covering_data := h_all_props.2.2.2.2.2.2.2.2.2.1
    have hfine_P_eq := h_all_props.2.2.2.2.2.2.2.2.2.2.1
    have h_tubeImage_data := h_all_props.2.2.2.2.2.2.2.2.2.2.2.1
    have h_card_ineq := h_all_props.2.2.2.2.2.2.2.2.2.2.2.2.1
    have h_slope_coarse := h_all_props.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hK_pos : 0 < K := by linarith [hK_ge1]

    rcases coarse_bound_wrapper
        Δ scaleClass N C_between hm_eq2 hcfg hB1 hextra hk_exp1 hΔn_lt_Δ1 hnm
        hK_ge1 hK_pos hK_bound hP_sub hP_nonempty' hcoarse_P_eq h_card_bound
        hCΔ_bounds1 hCΔ_bounds2 hMΔ h_slope_coarse
        hK_p5_ge1 hK_p5_pos hK_p5_spec hs hst hs1 hτ hεG hη hεN hCP hlam
        h_poly_K_le_δlam h_k_large h_absorb_coarse h_absorb_coarse_good h_good_improved_incidence
      with ⟨Δ_coarse, δbar, δ, j0, G0, B0, PΔ,
        hcoarse_P_nonempty, hΔ_coarse_def, hΔ_coarse_pos, hΔ_lt_one,
        hδbar_pos, hδbar_lt_one, hδbar_eq,
        hδ_pos2, hδ_lt_one, hδ_def, hδ_eq,
        hPΔ_pos, hPΔ_def, hG0_def, hB0_def, hj0, h_coarse_bound⟩

    -- Fine config construction and final bound combination
    rcases hcoarse_P_nonempty with ⟨Q, hQ⟩
    let shift : Fin n_fine → Fin (n_fine + 1) := Fin.succ
    let fineConfig_Q := fineConfig Q hQ
    let fineConfig_B1_Q := fineConfig_B1 Q hQ
    let MQ_Q := MQ Q
    have hC_coarse_nonneg : 0 ≤ C_coarse :=
      C_coarse_nonneg_helper m K_p5 C_P hK_p5_ge1 hCP
    have hα_pos : 0 < α := by norm_num [α]
    exact branch_dispatch
      (G0 := G0) (B0 := B0)
      (hC_coarse_nonneg := hC_coarse_nonneg)
      (Δ := Δ) (scaleClass := scaleClass) (N := N) (C_between := C_between)
      (j0 := j0) (shift := shift) (MQ := MQ) (hQ := hQ)
      (fineConfig_Q := fineConfig_Q) (fineConfig_B1_Q := fineConfig_B1_Q)
      (hK_bound := hK_bound) (hA_eq := hA_eq) (hk_exp1 := hk_exp1) (hk := hk)
      (hK_p5_ge1 := hK_p5_ge1) (hCP := hCP) (hC'_fine_pos := hC'_fine_pos)
      (hC'_ge := hC'_ge) (hτ := hτ) (hlam := hlam) (hτ_lam_tail := hτ_lam_tail)
      (hC_fine_pos := hC_fine_pos) (hC_ge := hC_ge) (hδ_def := hδ_def)
      (hδbar_eq := hδbar_eq) (hδ_eq := hδ_eq) (hj0 := hj0)
      (hK_ge1 := hK_ge1) (hK_pos := hK_pos) (hP_sub := hP_sub)
      (hcoarse_P_eq := hcoarse_P_eq) (h_card_density_all := h_card_density_all)
      (hCΔ_bounds1 := hCΔ_bounds1) (hCΔ_bounds2 := hCΔ_bounds2)
      (hCQ_bounds := hCQ_bounds) (hfine_P_eq' := hfine_P_eq Q hQ)
      (h_card_ineq' := h_card_ineq Q hQ) (h_slope_coarse := h_slope_coarse)
      (hMQ := hMQ) (hMΔ := hMΔ) (hnm := hnm)
      (hcoarse_P_nonempty := ⟨Q, hQ⟩)
      (hΔ_coarse_pos := hΔ_coarse_pos) (hΔ_lt_one := hΔ_lt_one)
      (hδbar_pos := hδbar_pos) (hδbar_lt_one := hδbar_lt_one)
      (hδ_pos2 := hδ_pos2) (hδ_lt_one := hδ_lt_one)
      (hPΔ_pos := hPΔ_pos) (hPΔ_def := hPΔ_def) (hG0_def := hG0_def) (hB0_def := hB0_def)
      (h_coarse_bound := h_coarse_bound)
      (hα_eq := by rfl) (hC_coarse_def := by rfl) (hC'_coarse_eq1 := by rfl)
      (hα_pos := hα_pos)
      (hshift := fun j => by rfl) (hΔ_coarse_eq := hΔ_coarse_def)
      (hcfg := hcfg) (hB1 := hB1) (hextra := hextra)
      (h_ih_bound := h_ih_bound) (h_eq89 := h_eq89)
      (hCP_fine := hCP_fine) (hCn_ge1 := hCn_ge1) (hCP_fine_eq := hCP_fine_eq)
      (hlam_tail_pos := hlam_tail_pos) (hδ_tail_pos := hδ_tail_pos)
      (hδτ_le_dtail := hδτ_le_dtail) (h_poly_K_le_δlam := h_poly_K_le_δlam)
      (h_k_large := h_k_large) (hA_pos := hA_pos) (hA_ge1 := hA_ge1)
      (hC_pos := hC_pos) (hC'_pos := hC'_pos) (hm_eq2 := hm_eq2)
      (hs := hs) (hst := hst) (hs1 := hs1) (hτ1 := hτ1)
      (hεG := hεG) (hη := hη) (hεN := hεN)
      (h_absorb_fine_normal := h_absorb_fine_normal)
      (h_absorb_fine_good := h_absorb_fine_good)
      (hΔn_lt_Δ1 := hΔn_lt_Δ1) (h2 := by omega)

end DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure
