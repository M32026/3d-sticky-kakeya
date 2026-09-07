module

/-
  Theorem 6.1 Main Assembly — Clean Skeleton

  Proves theorem6_1_main by assembling all components.
  Uses ember's complete_parameter_selection for all numeric parameters.
  δ thresholds carry real absorption statements (not set to 1).

  Whiteprint node: theorem6_1_main_assembly
  Status: 0 sorrys — assembly complete
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Contracts.AppendixA
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformProp5
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformProp5Wrapper
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.SSetExponentCap
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.CProp5Absorption
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductPropBoundedHelpers2
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.HeavyParentUniformClean
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.GlobalRetainedRegular
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.CoarseParentSSetRatio
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.CoarseBranchAssemblyClean
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.CoarseBranchAdapters
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.Gap1Helpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.B1InductionDataType
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.B1BridgeHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.HeavyConfigHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.ScaleConversion
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.FixedScaleAdapter
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.FixedScaleAdapterRadius
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.FixedPackingBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.ProvenanceRadiusAddition
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.FineBranchTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.FullParameterSelection
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.StandaloneParentGeometry
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicConversion
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Bridge_SSetTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.PolynomialMajorants
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.B1InductionDataConstructor
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.CleanFineCor25Chain
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.CleanB1Geometry
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.CRetCancellationClean
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.CoarseBranchFromB1Data
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.ExactMFrontend
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.IncidenceOffsetBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.RetainedRegularityClean
public import MyLeanRepo.DiscretisedFurstenbergEstimate.GeometricIntersection
public import MyLeanRepo.InductionOnScales.Pigeonhole
public import MyLeanRepo.OSWPrelude
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Theorem61MainAssemblyHelpers

@[expose] public section
open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 5000000

noncomputable section

namespace DirecretisedFurstenbergEstimate

open RegularIncidence
open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.CombiningTheoremRework
open DiscretisedFurstenbergEstimate.InductionConfigurations
open DiscretisedFurstenbergEstimate.CoveringUtils
open DyadicCardToNcover (toAffineLine)
open FixedPackingBound (C_pack)
open Section6 (FineCor25Data)

theorem theorem6_1_main_assembly (s t : ℝ) (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2) :
    ∃ ε_inc : ℝ, ε_inc < 1 ∧
      UniformRegularIncidenceEstimate (fun ℓ : AffineLine => ℓ.1) s t ε_inc ε_inc := by
  -- STEP 1: Fixed K from uniform_prop5
  have h_main : ∃ (K : ℝ), 0 < K ∧ _ := DiscretisedFurstenbergEstimate.uniform_prop5 s hs hs1
  let K : ℝ := Classical.choose h_main
  have hK_pos : 0 < K := (Classical.choose_spec h_main).1
  have hK_spec : UniformProp5Spec s K := (Classical.choose_spec h_main).2

  -- STEP 2: εA, δA from appendix_a_main
  rcases appendix_a_main s t hs hs1 hst ht2
    with ⟨εA, hεA_lt_one, hAppA⟩
  have hεA_pos : 0 < εA := hAppA.1
  rcases hAppA.2 with ⟨δA, hδA_pos, hδA_one, hAppABody⟩

  -- STEP 3: Parameter selection via ember's complete_parameter_selection
  -- C_parent_poly includes D² = 262144² as required.
  rcases complete_parameter_selection εA s t hεA_pos hs hs1 hst ht2
      ((10 : ℝ)^50) ((10 : ℝ)^20) ((10 : ℝ)^80)
      (by positivity) (by positivity) (by positivity)
      16 7 23
    with ⟨εInc, εReg, fixedLoss, pointLoss, tubeLoss, loss_B1, loss_parent,
      coarseGain, localLoss, netGain, lambda, rho_M, rho_mass, rho_sqrt, heavyMargin, heavySlack,
      coarsePointPolyLoss, coarseTubePolyLoss, coarseLogLoss,
      finePointPolyLoss, fineGlobalPolyLoss, fineMarginLoss, fineCQPolyLoss, fineLogLoss,
      pointRegularityLoss, a_C_ret, b_fine, localFineLoss,
      δ_front, δ_abs, δ_B1, δ_parent, δ_app_sqrt,
      hεInc_pos, hεInc_lt_εA, hεInc_lt_εReg, hεInc_lt_netGain,
      hεInc_le_εReg, hεInc_le_netGain, hnetGain_pos, hbudget,
      hεReg_pos, hεReg_lt_s, hfixedLoss_pos, hpointLoss_pos, htubeLoss_pos,
      hfrontend_budget, hrho_mass_pos, hrho_sqrt_pos, hheavyMargin_pos,
      hheavySlack_gt, hcoarseGain_le, hM_lower_exp_le,
      hδ_front_pos, hδ_abs_pos, hδ_B1_pos, hδ_parent_pos, hδ_app_sqrt_pos,
      h_abs_sqrt, h_abs_point, h_abs_tube, hheavy_absorb, h_abs_parent,
      hloss_B1_pos, hloss_parent_pos, hlambda_pos, hrho_M_pos, hlocalLoss_pos, hloss_parent_lt_εA,
      hcoarsePointPolyLoss_pos, hcoarseTubePolyLoss_pos, hcoarseLogLoss_pos,
      hcoarse_prop5_budget,
      hfinePointPolyLoss_pos, hfineGlobalPolyLoss_pos, hfineMarginLoss_pos,
      hfineCQPolyLoss_pos, hfineLogLoss_pos,
      hpointRegularityLoss_eq, ha_C_ret_eq, hb_fine_eq, hlocalFineLoss_eq,
      hrho_sqrt_eq, hrho_sqrt_le_rho_mass,
      hlocalFineLoss_lt⟩

  have hεInc_lt_one : εInc < 1 := by linarith [hεInc_lt_εA, hεA_lt_one]

  -- Fine-branch absorption thresholds (S5: C_pack, S6: 9-factor)
  let fine_loss : ℝ := (εA - εInc) / 3
  have hfine_loss_pos : 0 < fine_loss := by
    dsimp only [fine_loss]; linarith [hεInc_lt_εA]
  rcases absorb_constant_local (FixedPackingBound.C_pack : ℝ) fine_loss
      (by simp [FixedPackingBound.C_pack] <;> norm_num) hfine_loss_pos
    with ⟨δ_Cpack, hδ_Cpack_pos, h_abs_Cpack_raw⟩
  rcases absorb_constant_local ((9 : ℝ)^(2 * s + εA)) fine_loss
      (by positivity) hfine_loss_pos
    with ⟨δ_9factor, hδ_9factor_pos, h_abs_9factor_raw⟩

  -- STEP 4b: C_prop5 absorption threshold
  -- Combined polynomial majorant for denominator C_P_prop5 * 13 * CΔ_prop5 * 2^s
  -- C_coarse_point ≤ C_poly_point * n^23 * δ_n^{-(εReg+pointLoss)}
  -- data.CΔ ≤ C_poly_tube * n^7 * δ_n^{-(εReg+tubeLoss)}
  let C_poly_point : ℝ := 162 * (10:ℝ)^50 * 2 * 2700 * 3145728 * 8 * 11^7 + 1
  let C_poly_tube : ℝ := 2700 * 3145728 * 11^7 + 1
  let C_poly_prop5 : ℝ := C_poly_point * C_poly_tube * 13 * (2:ℝ)^s
  let degree_prop5 : ℕ := 30
  let a_prop5 : ℝ := 2 * εReg + pointLoss + tubeLoss
  let b_prop5 : ℝ := coarseLogLoss
  let loss_coarse : ℝ := loss_parent / 2
  have hC_poly_prop5_pos : 0 < C_poly_prop5 := by positivity
  have hb_prop5_pos : 0 < b_prop5 := hcoarseLogLoss_pos
  have h_prop5_budget : a_prop5 + b_prop5 < loss_coarse := hcoarse_prop5_budget
  rcases Section6.coarse_prop5_fixed_absorption K C_poly_prop5 degree_prop5
      hK_pos hC_poly_prop5_pos a_prop5 b_prop5 loss_coarse hb_prop5_pos h_prop5_budget
    with ⟨δ_prop5, hδ_prop5_pos, h_abs_prop5_spec⟩

  -- Fine-chain fixed thresholds (selected BEFORE deltaR, no runtime constants)
  let C_fine_point_poly : ℝ := (10:ℝ)^8
  let C_fine_global_poly : ℝ := 2 * (2700 * 3145728 * (11:ℝ)^7)^2
  let C_fine_CQ_poly : ℝ := 2700 * 3145728 * (11:ℝ)^7
  rcases uniform_polynomial_absorption C_fine_point_poly (by positivity) 1 finePointPolyLoss hfinePointPolyLoss_pos
    with ⟨δ_fine_point, hδ_fine_point_pos, h_abs_fine_point⟩
  rcases uniform_polynomial_absorption C_fine_global_poly (by positivity) 14 fineGlobalPolyLoss hfineGlobalPolyLoss_pos
    with ⟨δ_fine_global, hδ_fine_global_pos, h_abs_fine_global⟩
  rcases absorb_constant_local (81:ℝ) fineMarginLoss (by norm_num) hfineMarginLoss_pos
    with ⟨δ_fine_margin, hδ_fine_margin_pos, h_abs_fine_margin⟩
  rcases uniform_polynomial_absorption C_fine_CQ_poly (by positivity) 7 fineCQPolyLoss hfineCQPolyLoss_pos
    with ⟨δ_fine_CQ, hδ_fine_CQ_pos, h_abs_fine_CQ⟩
  -- Fine scale conversion threshold (for h_convert_chain)
  have ha_fine_nonneg : 0 ≤ a_C_ret := by
    have h1 : 0 < pointRegularityLoss := by linarith [hεReg_pos, hpointLoss_pos, hfinePointPolyLoss_pos]
    linarith [hrho_sqrt_pos, hfineGlobalPolyLoss_pos, hfineMarginLoss_pos]
  have hb_fine_nonneg : 0 ≤ b_fine := by linarith [hεReg_pos, htubeLoss_pos, hfineCQPolyLoss_pos]
  rcases Section6.fine_ratio_convert_for_chain ha_fine_nonneg hb_fine_nonneg hfineLogLoss_pos hK_pos
    with ⟨δ_fine_convert, hδ_fine_convert_pos, hδ_fine_convert_le_one, h_abs_fine_convert⟩

  have hSlack_pos : 0 < heavySlack := by
    have h : heavySlack > rho_mass + rho_sqrt + heavyMargin := hheavySlack_gt
    have h2 : 0 < rho_mass + rho_sqrt + heavyMargin := by positivity
    linarith
  let ε_inc : ℝ := εInc

  -- Combined fine threshold
  let δ_fine : ℝ := min (min (min δ_fine_point δ_fine_global) (min δ_fine_margin δ_fine_CQ)) δ_fine_convert
  have hδ_fine_pos : 0 < δ_fine := by
    dsimp only [δ_fine]
    exact lt_min (lt_min (lt_min (by positivity) (by positivity)) (by positivity)) (by positivity)

  -- STEP 4b: Additional thresholds for auxiliary existential fields
  -- B1 polylog threshold (strict: use half to get <)
  let δ_b1 := b1_polylog_threshold loss_B1 hloss_B1_pos
  have hδ_b1_pos : 0 < δ_b1 := (b1_polylog_threshold_spec loss_B1 hloss_B1_pos).1
  have hδ_b1_half_pos : 0 < δ_b1 / 2 := by positivity

  -- Packing bound threshold: C_pack * 4^{-(2*s+εInc)} * δ_n^{netGain-εInc} ≤ 1
  let C_pack_total := (FixedPackingBound.C_pack : ℝ) * (4 : ℝ)^(-(2 * s + εInc))
  have hC_pack_total_pos : 0 < C_pack_total := by
    dsimp only [C_pack_total]
    have h1 : (0 : ℝ) < (FixedPackingBound.C_pack : ℝ) := by
      have h_pos : 0 < FixedPackingBound.C_pack := by norm_num [FixedPackingBound.C_pack]
      exact_mod_cast h_pos
    have h2 : (0 : ℝ) < (4 : ℝ)^(-(2 * s + εInc)) := by positivity
    exact mul_pos h1 h2
  have h_netGain_minus_εInc_pos : 0 < netGain - εInc := by linarith [hεInc_lt_netGain]
  rcases absorb_constant_local C_pack_total (netGain - εInc) hC_pack_total_pos h_netGain_minus_εInc_pos
    with ⟨δ_packing, hδ_packing_pos, h_abs_packing⟩

  -- STEP 4c: Obtain frontend threshold from exact_m_frontend
  rcases DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.exact_m_frontend
      (hs_pos := hs)
      (hεReg_pos := hεReg_pos)
      (hεReg_lt_s := hεReg_lt_s)
      (hεA_pos := hεA_pos)
      (hfixedLoss_pos := hfixedLoss_pos)
      (hpointLoss_pos := hpointLoss_pos)
      (htubeLoss_pos := htubeLoss_pos)
      (h_budget := hfrontend_budget)
    with ⟨δ_exact, hδ_exact_pos, h_frontend⟩

  -- Combined extra threshold
  let δ_extra : ℝ := min (min (δ_b1 / 2) δ_packing) δ_exact
  have hδ_extra_pos : 0 < δ_extra := by
    dsimp only [δ_extra]
    exact lt_min (lt_min (by positivity) (by positivity)) (by positivity)

  -- STEP 4: δR threshold (nested min avoids slow Finset.min')
  let δR : ℝ := min (min (min (min (min (min (1 / 8) (δA / 9)) (min δ_front δ_abs))
                       (min (min δ_B1 δ_parent) δ_app_sqrt))
                  (min δ_Cpack δ_9factor))
              δ_fine)
          (min δ_prop5 δ_extra)
  have hδR_pos : 0 < δR := by
    dsimp only [δR]
    exact lt_min (lt_min (lt_min (lt_min (lt_min (lt_min (by norm_num) (by positivity)) (by positivity)) (by positivity)) (by positivity)) hδ_fine_pos) (lt_min hδ_prop5_pos hδ_extra_pos)
  have hδR_eighth : δR ≤ 1 / 8 := by
    dsimp only [δR]; exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))))
  have hδR_one : δR ≤ 1 := by linarith [hδR_eighth]
  have hδR_le_δA9 : δR ≤ δA / 9 := by
    dsimp only [δR]; exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))))
  have hδR_le_front : δR ≤ δ_front := by
    dsimp only [δR]; exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))))
  have hδR_le_abs : δR ≤ δ_abs := by
    dsimp only [δR]; exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))))
  have hδR_le_B1 : δR ≤ δ_B1 := by
    dsimp only [δR]; exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))))
  have hδR_le_parent : δR ≤ δ_parent := by
    dsimp only [δR]; exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))))
  have hδR_le_app_sqrt : δR ≤ δ_app_sqrt := by
    dsimp only [δR]
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  have hδR_le_Cpack : δR ≤ δ_Cpack := by
    dsimp only [δR]; exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδR_le_9factor : δR ≤ δ_9factor := by
    dsimp only [δR]; exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hδR_le_fine : δR ≤ δ_fine := by
    dsimp only [δR]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδR_le_fine_point : δR ≤ δ_fine_point := by
    dsimp only [δR, δ_fine]
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))))
  have hδR_le_fine_global : δR ≤ δ_fine_global := by
    dsimp only [δR, δ_fine]
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))))
  have hδR_le_fine_margin : δR ≤ δ_fine_margin := by
    dsimp only [δR, δ_fine]
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hδR_le_fine_CQ : δR ≤ δ_fine_CQ := by
    dsimp only [δR, δ_fine]
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  have hδR_le_fine_convert : δR ≤ δ_fine_convert := by
    dsimp only [δR, δ_fine]
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδR_le_prop5 : δR ≤ δ_prop5 := by
    dsimp only [δR]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδR_le_extra : δR ≤ δ_extra := by
    dsimp only [δR]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hδR_le_b1_half : δR ≤ δ_b1 / 2 := by
    dsimp only [δR, δ_extra]
    exact le_trans hδR_le_extra (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδR_le_packing : δR ≤ δ_packing := by
    dsimp only [δR, δ_extra]
    exact le_trans hδR_le_extra (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδR_le_exact : δR ≤ δ_exact := by
    dsimp only [δR, δ_extra]
    exact le_trans hδR_le_extra (min_le_right _ _)
  have h9δR_le_δA : 9 * δR ≤ δA := by
    calc 9 * δR ≤ 9 * (δA / 9) := by gcongr
      _ = δA := by ring
  have hδR_le_δA : δR ≤ δA := le_trans hδR_le_δA9 (by linarith [hδA_pos])

  -- STEP 5: UniformRegularIncidenceEstimate binders
  refine ⟨ε_inc, hεInc_lt_one, ?_⟩
  refine ⟨hεInc_pos, hεInc_pos, δR, hδR_pos, hδR_one, ?_⟩
  intro u hu_t hu2 δ hδ_pos hδ_le
  let u0 : ℝ := min u 1
  have hsu0_lt : s < u0 := by
    dsimp only [u0]
    have h1 : s < u := lt_of_lt_of_le hst hu_t
    have h2 : s < 1 := hs1
    exact lt_min h1 h2
  have hu0_one : u0 ≤ 1 := min_le_right _ _
  intro P hP_sub hP_regular
  intro tubeFamily hT_sset hT_close hT_chart

  -- Original family of affine lines (union of all tube families)
  let originalFamily : Set AffineLine := ⋃ p, ⋃ hp : p ∈ P, tubeFamily p hp

  -- STEP 6: Frontend discretization via exact_m_frontend

  -- Weaken input regularity from ε_inc to εReg (ε_inc ≤ εReg)
  have hδ_le_one : δ ≤ 1 := le_trans hδ_le hδR_one
  have hC_weak : Real.rpow δ (-ε_inc) ≤ Real.rpow δ (-εReg) :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one (by linarith [hεInc_le_εReg])
  have hP_regular' : IsSquareRootRegular δ u (Real.rpow δ (-εReg)) (Real.rpow δ (-εReg)) P :=
    hP_regular.weaken_constants hC_weak hC_weak
  have hT_sset' : ∀ p hp, IsDeltaSSet δ s (Real.rpow δ (-εReg)) (tubeFamily p hp) := by
    intro p hp
    exact IsDeltaSSet.weaken_C (hT_sset p hp) hC_weak

  -- Derive offset bound from incidence
  have hOffset : ∀ p hp, ∀ ℓ ∈ tubeFamily p hp, ‖ℓ.offset‖ ≤ 2 := by
    intro p hp ℓ hℓ
    have h_p_ball : p ∈ Metric.closedBall (0 : Plane) 1 := hP_sub hp
    have h_inc : p ∈ Metric.cthickening δ ℓ.1 := hT_close p hp ℓ hℓ
    have h := ImprovedIncidenceGeneral.offset_bound_from_incidence hδ_pos hδ_le_one h_p_ball h_inc
    simpa [Metric.mem_closedBall] using h

  -- Apply frontend with runtime u
  have h_s_lt_u : s < u := lt_of_lt_of_le hst hu_t
  have hδ_le_exact : δ ≤ δ_exact := le_trans hδ_le hδR_le_exact
  rcases h_frontend u h_s_lt_u hu2 δ hδ_pos hδ_le_exact hδ_le_one
      P hP_sub hP_regular' tubeFamily hT_sset' hT_close hT_chart hOffset
    with ⟨n, m, C₁_nat, M, C_P, K_P,
      h_even, h_scale1, h_scale2, hM_pos, hM_lower, hC1_bound, hC1_ge1,
      hCP_nonneg, hCP_bound, hKP_pos, hKP_bound,
      config, hP0_nonempty, h_squares_unit, h_tubes_strip, h_T0_card,
      h_intersection, h_mass_enn, h_regular_config, h_P0_ge_ncover,
      h_tube_provenance_family, h_point_provenance, h_pointSet_ball,
      h_slope_bound, h_tube_provenance_T0⟩

  -- Derive hnm : m ≤ n from n = 2 * m
  have hnm : m ≤ n := by omega

  -- Let C₁ : ℝ := (C₁_nat : ℝ)
  let C₁ : ℝ := (C₁_nat : ℝ)
  have hC₁ : (1 : ℝ) ≤ C₁ := by
    have h : (1 : ℕ) ≤ C₁_nat := hC1_ge1
    have h' : (1 : ℝ) ≤ (C₁_nat : ℝ) := by exact_mod_cast h
    simpa [C₁] using h'

  -- δd n ≤ δR : δ_n ≤ δ/4 ≤ δ ≤ δR
  have hδn_le_R : δd n ≤ δR := by
    calc δd n ≤ δ / 4 := h_scale1
         _ ≤ δ := by linarith
         _ ≤ δR := hδ_le

  -- K_P bound : K_P ≤ δ_n^{-(εReg+pointLoss)} = δ_n^{-rho_sqrt}
  have hK_P_bound' : K_P ≤ (δd n)^(-rho_sqrt) := by
    have h_eq : rho_sqrt = εReg + pointLoss := hrho_sqrt_eq
    rw [h_eq]
    exact hKP_bound

  -- C_P bound : C_P ≤ δ_n^{-(εReg+pointLoss)} ≤ 10^6 * δ_n^{-(εReg+pointLoss)}
  have hC_P_bound' : C_P ≤ (10 : ℝ)^6 * (δd n)^(-(εReg + pointLoss)) := by
    have h1 : C_P ≤ (δd n)^(-(εReg + pointLoss)) := hCP_bound
    have h2 : (δd n)^(-(εReg + pointLoss)) ≤ (10 : ℝ)^6 * (δd n)^(-(εReg + pointLoss)) := by
      have h3 : 0 < (δd n)^(-(εReg + pointLoss)) := Real.rpow_pos_of_pos (DiscretisedFurstenbergEstimate.dyadicDelta_pos n) _
      have h4 : (1 : ℝ) ≤ (10 : ℝ)^6 := by norm_num
      exact le_mul_of_one_le_left h3.le h4
    exact le_trans h1 h2

  -- Mass bound : ENNReal → ℝ using rho_sqrt ≤ rho_mass
  have hδn_pos : 0 < δd n := DiscretisedFurstenbergEstimate.dyadicDelta_pos n
  have hδn_lt_one : δd n < 1 := by
    have h : δd n ≤ 1 / 8 := le_trans hδn_le_R hδR_eighth
    linarith
  have h_mass_enn' : (config.P₀.card : ENNReal) ≥ ENNReal.ofReal ((δd n)^(-u + rho_sqrt)) := by
    have h_exp : -u + rho_sqrt = -u + εReg + pointLoss := by
      rw [hrho_sqrt_eq] <;> ring
    have h1 : (δd n)^(-u + rho_sqrt) = (δd n)^(-u + εReg + pointLoss) := by
      rw [h_exp]
    rw [h1]
    exact h_mass_enn
  have hP_mass_lower : (config.P₀.card : ℝ) ≥ (δd n)^(-u + rho_mass) :=
    frontend_mass_adapter hδn_pos hδn_lt_one hrho_sqrt_le_rho_mass h_mass_enn'

  -- Point square provenance : S0(p_orig) ∈ q.toSet and ‖S0 p_orig‖ ≤ 3/4
  have h_point_square_provenance : ∀ q ∈ config.P₀, ∃ (c : EuclideanPlane), c ∈ q.toSet ∧ ‖c‖ ≤ 3 / 4 := by
    intro q hq
    rcases h_point_provenance q hq with ⟨p_orig, hp_orig, hS0_mem⟩
    have h_p_norm : ‖p_orig‖ ≤ 1 := by
      have h := hP_sub hp_orig
      simpa [Metric.mem_closedBall] using h
    refine' ⟨S0 p_orig, hS0_mem, _⟩
    exact S0_norm_le_three_quarters h_p_norm

  -- Tube provenance : ℓ ∈ originalFamily and distance bound
  have h_tube_provenance : ∀ T ∈ config.T₀, ∃ (ℓ : AffineLine), ℓ ∈ originalFamily ∧
      dist (toAffineLine T) (RegularIncidence.S0_line ℓ) ≤ (15 / 2 : ℝ) * (δ / 4) := by
    intro T hT
    rcases h_tube_provenance_T0 T hT with ⟨p_orig, hp_orig, ℓ, hℓ, hdist⟩
    have hℓ_orig : ℓ ∈ originalFamily := by
      simp only [originalFamily, Set.mem_iUnion₂]
      exact ⟨p_orig, hp_orig, hℓ⟩
    exact ⟨ℓ, hℓ_orig, hdist⟩

  -- B1 threshold : δd n < b1_polylog_threshold
  have hδn_small : δd n < b1_polylog_threshold loss_B1 hloss_B1_pos := by
    have h1 : δd n ≤ δR := hδn_le_R
    have h2 : δR ≤ δ_b1 / 2 := hδR_le_b1_half
    have h3 : δd n ≤ δ_b1 / 2 := le_trans h1 h2
    have h4 : δ_b1 / 2 < δ_b1 := by
      have h5 : 0 < δ_b1 := hδ_b1_pos
      linarith
    exact lt_of_le_of_lt h3 h4

  -- Packing bound : C_pack_total * (δd n)^(netGain - εInc) ≤ 1
  have h_coarse_absorb : (FixedPackingBound.C_pack : ℝ) * (4 : ℝ)^(-(2 * s + εInc)) * (δd n)^(netGain - εInc) ≤ 1 := by
    have h1 : δd n ≤ δ_packing := le_trans hδn_le_R hδR_le_packing
    have h2 : C_pack_total ≤ (δd n)^(-(netGain - εInc)) := h_abs_packing (δd n) hδn_pos h1
    have h3 : (δd n)^(-(netGain - εInc)) = 1 / (δd n)^(netGain - εInc) := by
      rw [Real.rpow_neg hδn_pos.le] <;> ring
    rw [h3] at h2
    have h4 : 0 < (δd n)^(netGain - εInc) := Real.rpow_pos_of_pos hδn_pos _
    have h5 : C_pack_total * (δd n)^(netGain - εInc) ≤ 1 := by
      calc C_pack_total * (δd n)^(netGain - εInc)
        ≤ (1 / (δd n)^(netGain - εInc)) * (δd n)^(netGain - εInc) := by gcongr
      _ = 1 := by field_simp [h4.ne'] <;> ring
    simpa [C_pack_total] using h5

  -- n > 0 (if n=0, δd 0 = 1 > 1/8 ≥ δR, contradiction)
  have hn_pos : 0 < n := by
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0] at hδn_le_R
    have h1 : δd 0 = 1 := by
      rw [DiscretisedFurstenbergEstimate.dyadicDelta] <;> norm_num
    rw [h1] at hδn_le_R
    have h2 : (1 : ℝ) ≤ δR := hδn_le_R
    have h3 : δR ≤ 1 / 8 := hδR_eighth
    linarith

  -- Chain δd n ≤ δR ≤ δ_parent
  have hδn_le_parent : δd n ≤ δ_parent := by
    calc δd n ≤ δR := hδn_le_R
         _ ≤ δ_parent := hδR_le_parent

  -- Apply complete_parameter_selection parent absorption
  have h_abs_parent10 : (10 : ℝ)^80 * (n : ℝ)^23 ≤ (δd n)^(-loss_parent) :=
    h_abs_parent n hδn_le_parent

  -- Parent absorption via reciprocal adapter
  have h_absorb_geo_frontend : ((9 : ℝ)^(-(s + εA)) / (262144 : ℝ)^2) ≥ (δd n)^loss_parent :=
    parent_geometric_reciprocal_adapter
      (hn_pos := hn_pos)
      (hs_lt_one := hs1)
      (hεA_lt_one := hεA_lt_one)
      (hδn_pos := hδn_pos)
      (hδn_lt_one := hδn_lt_one)
      (h_abs_parent := h_abs_parent10)

  -- Aliases matching downstream variable names
  have h_scale : δd n ≤ δ / 4 := h_scale1
  have hK_P_pos : 0 < K_P := hKP_pos
  have hK_P_bound : K_P ≤ (δd n)^(-rho_sqrt) := hK_P_bound'
  have h_regular : IsSquareRootRegular (δd n) u C_P K_P config.pointSet := h_regular_config
  have hC₁_bound : C₁ ≤ (δd n)^(-(εReg + tubeLoss)) := hC1_bound
  have hC_P_bound : C_P ≤ (10 : ℝ)^6 * (δd n)^(-(εReg + pointLoss)) := hC_P_bound'
  have h_tubes_bounded : config.T₀.card ≤ 12 * 16^n := h_T0_card

  have hN_le : config.P₀.card ≤ 4^n := config_P0_card_le_4n config h_squares_unit
  have hM_lower_pkg : (M : ℝ) ≥ (δd n)^(-s + lambda + rho_M) := by
    have h_exp : -s + εReg + fixedLoss ≤ -s + lambda + rho_M := by linarith [hM_lower_exp_le]
    have hδn_pos : 0 < δd n := DiscretisedFurstenbergEstimate.dyadicDelta_pos n
    have h_pow : (δd n)^(-s + lambda + rho_M) ≤ (δd n)^(-s + εReg + fixedLoss) :=
      Real.rpow_le_rpow_of_exponent_ge hδn_pos hδn_lt_one.le h_exp
    exact le_trans h_pow hM_lower

  -- STEP 7: HeavyParentUniformClean
  have hP0_lower : (config.P₀.card : ℝ) >
      2 * C_geo_local * K_P * (δd n)^(-u + heavySlack) := by
    have hδn_pos : 0 < δd n := DiscretisedFurstenbergEstimate.dyadicDelta_pos n
    have hδn_lt_one : δd n < 1 := by
      have h : δd n ≤ 1 / 8 := le_trans hδn_le_R hδR_eighth
      linarith
    set loss : ℝ := heavySlack - rho_mass - rho_sqrt with hloss_def
    have hloss_gt_heavyMargin : loss > heavyMargin := by
      dsimp only [loss]; linarith [hheavySlack_gt]
    have hloss_pos : 0 < loss := by linarith [hheavyMargin_pos]
    have h1 : (δd n)^loss < (δd n)^heavyMargin :=
      Real.rpow_lt_rpow_of_exponent_gt hδn_pos hδn_lt_one hloss_gt_heavyMargin
    have h2 : (δd n)^heavyMargin ≤ δ_front^heavyMargin := by
      have h3 : δd n ≤ δ_front := le_trans hδn_le_R hδR_le_front
      have h4 : 0 ≤ heavyMargin := by linarith
      exact Real.rpow_le_rpow hδn_pos.le h3 h4
    have h5 : 2 * C_geo_local * (δd n)^loss < 1 := by
      calc 2 * C_geo_local * (δd n)^loss
        < 2 * C_geo_local * (δd n)^heavyMargin := by gcongr <;> linarith
      _ ≤ 2 * C_geo_local * δ_front^heavyMargin := by gcongr <;> linarith
      _ < 1 := hheavy_absorb
    have h_pos1 : 0 < (δd n)^(-u + rho_mass) := by positivity
    have h_factor : 2 * C_geo_local * (δd n)^loss < 1 := h5
    have h8 : 2 * C_geo_local * (δd n)^loss * (δd n)^(-u + rho_mass) <
        (δd n)^(-u + rho_mass) := by
      have h : (2 * C_geo_local * (δd n)^loss) * (δd n)^(-u + rho_mass) < 1 * (δd n)^(-u + rho_mass) :=
        mul_lt_mul_of_pos_right h_factor h_pos1
      simpa [mul_assoc] using h
    have h10 : (δd n)^loss * (δd n)^(-u + rho_mass) =
        (δd n)^(-u + heavySlack - rho_sqrt) := by
      rw [← Real.rpow_add hδn_pos]
      <;> simp [hloss_def] <;> ring_nf
    have h6 : (δd n)^(-u + rho_mass) > 2 * C_geo_local * (δd n)^(-u + heavySlack - rho_sqrt) := by
      have h9 : 2 * C_geo_local * (δd n)^loss * (δd n)^(-u + rho_mass) =
          2 * C_geo_local * ((δd n)^loss * (δd n)^(-u + rho_mass)) := by ring
      rw [h9, h10] at h8
      exact h8
    have h11 : 2 * C_geo_local * K_P * (δd n)^(-u + heavySlack) ≤
        2 * C_geo_local * (δd n)^(-u + heavySlack - rho_sqrt) := by
      have h12 : 0 < (δd n)^(-u + heavySlack) := by positivity
      have h13 : K_P * (δd n)^(-u + heavySlack) ≤
          (δd n)^(-rho_sqrt) * (δd n)^(-u + heavySlack) :=
        mul_le_mul_of_nonneg_right hK_P_bound h12.le
      have h14 : (δd n)^(-rho_sqrt) * (δd n)^(-u + heavySlack) =
          (δd n)^(-u + heavySlack - rho_sqrt) := by
        rw [← Real.rpow_add hδn_pos] <;> ring_nf
      calc 2 * C_geo_local * K_P * (δd n)^(-u + heavySlack)
        = 2 * C_geo_local * (K_P * (δd n)^(-u + heavySlack)) := by ring
      _ ≤ 2 * C_geo_local * ((δd n)^(-rho_sqrt) * (δd n)^(-u + heavySlack)) := by gcongr
      _ = 2 * C_geo_local * (δd n)^(-u + heavySlack - rho_sqrt) := by rw [h14]
    calc (config.P₀.card : ℝ)
      ≥ (δd n)^(-u + rho_mass) := hP_mass_lower
    _ > 2 * C_geo_local * (δd n)^(-u + heavySlack - rho_sqrt) := h6
    _ ≥ 2 * C_geo_local * K_P * (δd n)^(-u + heavySlack) := h11
  rcases heavy_parent_uniform_clean hnm h_even config h_regular heavySlack hSlack_pos hK_P_pos hP0_lower
    with ⟨P_heavy, M_fiber, Q_heavy, hP_heavy_sub, hP_heavy_retention, hQ_eq, h_fiber_bounds, h_retained_union_regular⟩

  -- STEP 8 & 9: Restricted heavy config + all sub-hypotheses
  rcases heavy_config_from_subset config P_heavy hP_heavy_sub hP_heavy_retention
      hP0_nonempty h_squares_unit h_tubes_strip h_tubes_bounded
    with ⟨config_heavy, hP0_eq, h_T0_sub, hP_heavy_nonempty, h_squares_unit', h_tubes_strip', h_tubes_bounded', h_T0_coverage⟩
  have hC₁' : 1 ≤ C₁ := hC₁
  rcases @b1_bridge_data_helper n m hnm s t C₁ M config_heavy hs.le hs1.le hC₁' hM_pos hP_heavy_nonempty
      h_squares_unit' h_tubes_strip' h_tubes_bounded'
    with ⟨data, hK_B1_bound, h_coarse_count, h_fineP_eq_all, h_raw_product⟩
  let K_B1 : ℝ := @Section6.B1InductionData.K n m hnm s t C₁ M config_heavy data

  -- STEP 10: Post-B1 retention
  let containSq : DiscretisedFurstenbergEstimate.DyadicSquare n → DiscretisedFurstenbergEstimate.DyadicSquare m :=
    DiscretisedFurstenbergEstimate.InductionConfigurations.containingSquare hnm
  let sqContain := DiscretisedFurstenbergEstimate.InductionConfigurations.squareContained hnm
  have hQ0_eq : config_heavy.P₀.image containSq = Q_heavy := by
    rw [hP0_eq]
    exact hQ_eq.symm
  have hP_heavy_nonempty' : P_heavy.Nonempty := by
    rw [← hP0_eq]; exact hP_heavy_nonempty
  have hQ_heavy_nonempty : Q_heavy.Nonempty := by
    rw [hQ_eq]
    exact hP_heavy_nonempty'.image containSq
  have hM_fiber_pos : 0 < (M_fiber : ℝ) :=
    M_fiber_pos_from_upper Q_heavy hQ_heavy_nonempty
      (fun Q => (P_heavy.filter (fun p => sqContain p Q)).card)
      (fun Q hQ => (h_fiber_bounds Q hQ).2.2)
  have hF0_lower : ∀ Q ∈ config_heavy.P₀.image containSq,
      (M_fiber : ℝ) ≤ ((config_heavy.P₀.filter (fun p => sqContain p Q)).card : ℝ) := by
    intro Q hQ
    have hQ' : Q ∈ Q_heavy := hQ0_eq ▸ hQ
    have h_filter : config_heavy.P₀.filter (fun p => sqContain p Q) = P_heavy.filter (fun p => sqContain p Q) := by
      ext x; simp [hP0_eq]
    rw [h_filter]
    exact (h_fiber_bounds Q hQ').1
  have hF0_upper : ∀ Q ∈ config_heavy.P₀.image containSq,
      ((config_heavy.P₀.filter (fun p => sqContain p Q)).card : ℝ) < 2 * (M_fiber : ℝ) := by
    intro Q hQ
    have hQ' : Q ∈ Q_heavy := hQ0_eq ▸ hQ
    have h_filter : config_heavy.P₀.filter (fun p => sqContain p Q) = P_heavy.filter (fun p => sqContain p Q) := by
      ext x; simp [hP0_eq]
    rw [h_filter]
    exact (h_fiber_bounds Q hQ').2.2
  rcases post_b1_retention_helper hnm hM_fiber_pos h_coarse_count hF0_lower hF0_upper
    with ⟨K_global, hK_global_pos, hK_global_bound, h_global_card, h_retention_fiber⟩

  -- STEP 11: Retained regularity via GlobalRetainedRegular
  let P_retained : Set EuclideanPlane :=
      ⋃ p ∈ (data.P : Set (DSq n)), (p.toSet : Set EuclideanPlane)
  let C_heavy : ℝ := C_P * 18 * (numDyadicLevels config.P₀.card : ℝ)
  let C_point : ℝ := C_heavy * 9 * K_global
  have h_pointSet_eq : config_heavy.pointSet = (⋃ p ∈ (P_heavy : Set (DSq n)), (p.toSet : Set EuclideanPlane)) := by
    simp [NiceConfiguration.pointSet, hP0_eq]
  have hReg_heavy : IsSquareRootRegular (δd n) u C_heavy K_P config_heavy.pointSet := by
    rw [h_pointSet_eq]
    exact h_retained_union_regular
  have h_retained_regular : IsSquareRootRegular (δd n) u C_point K_P P_retained :=
    global_retained_regular
      (hnm := hnm)
      (config := config_heavy)
      (hReg := hReg_heavy)
      (P := data.P)
      (hP_sub := data.hP_sub)
      K_global hK_global_pos h_global_card
      data.hP_nonempty

  -- STEP 12: Harbor S-set on data.coarseConfig.P₀
  let R_harbor : ℝ := 2 * K_B1
  let C_coarse_point : ℝ := 162 * C_point * R_harbor * (2 * Real.sqrt 2) ^ u
  have hC_point_pos : 0 < C_point := by
    have hCP_pos : 0 < C_P := h_regular.to_isDeltaSSet.2.2.1
    have h_num_pos : (0 : ℝ) < (numDyadicLevels config.P₀.card : ℝ) := by
      have h : 0 < numDyadicLevels config.P₀.card := by
        simp [numDyadicLevels] <;> omega
      exact_mod_cast h
    positivity
  have h_coarse_sset : DiscretisedFurstenbergEstimate.IsFinsetDeltaSSet (δd m) u C_coarse_point
      (DiscretisedFurstenbergEstimate.DyadicConversion.finsetDyadicToDSquare data.coarseConfig.P₀) :=
    b1_data_coarse_sset hnm h_even config_heavy data
      M_fiber hM_fiber_pos hF0_lower hF0_upper
      C_point hC_point_pos
      h_retained_regular.to_isDeltaSSet
      (by linarith [hs, hst, hu_t])

  -- STEP 13: Appendix A at 9*δ_n via FixedScaleAdapterRadius
  let getRetainedSquare (x : EuclideanPlane) (hx : x ∈ P_retained) : DSq n :=
    Classical.choose (show ∃ (p : DSq n), p ∈ data.P ∧ x ∈ p.toSet from by
      simpa [P_retained, Set.mem_iUnion] using hx)
  have getRetainedSquare_mem : ∀ (x : EuclideanPlane) (hx : x ∈ P_retained),
      getRetainedSquare x hx ∈ data.P := by
    intro x hx
    have h_spec : ∃ (p : DSq n), p ∈ data.P ∧ x ∈ p.toSet := by
      simpa [P_retained, Set.mem_iUnion] using hx
    exact (Classical.choose_spec h_spec).1
  have getRetainedSquare_in : ∀ (x : EuclideanPlane) (hx : x ∈ P_retained),
      x ∈ (getRetainedSquare x hx).toSet := by
    intro x hx
    have h_spec : ∃ (p : DSq n), p ∈ data.P ∧ x ∈ p.toSet := by
      simpa [P_retained, Set.mem_iUnion] using hx
    exact (Classical.choose_spec h_spec).2

  let retainedTubeFamily : (p : EuclideanPlane) → p ∈ P_retained → Finset (DTb n) :=
    fun x hx =>
      let q : DSq n := getRetainedSquare x hx
      let hq : q ∈ data.P := getRetainedSquare_mem x hx
      data.tubeFamily q hq

  have hP_retained_ball : P_retained ⊆ Metric.closedBall 0 1 := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨p, hp, xp⟩
    have hq_config : p ∈ config.P₀ := by
      have h1 : p ∈ data.P := hp
      have h2 : p ∈ config_heavy.P₀ := data.hP_sub h1
      rw [hP0_eq] at h2
      exact hP_heavy_sub h2
    rcases h_point_square_provenance p hq_config with ⟨c, hc_in, hc_norm⟩
    have hx0 : |x 0 - c 0| ≤ δd n := by
      have h1 : (p.i : ℝ) * δd n ≤ x 0 := xp.1
      have h2 : x 0 < ((p.i : ℝ) + 1) * δd n := xp.2.1
      have h3 : (p.i : ℝ) * δd n ≤ c 0 := hc_in.1
      have h4 : c 0 < ((p.i : ℝ) + 1) * δd n := hc_in.2.1
      rw [abs_sub_le_iff] <;> constructor <;> linarith
    have hx1 : |x 1 - c 1| ≤ δd n := by
      have h1 : (p.j : ℝ) * δd n ≤ x 1 := xp.2.2.1
      have h2 : x 1 < ((p.j : ℝ) + 1) * δd n := xp.2.2.2
      have h3 : (p.j : ℝ) * δd n ≤ c 1 := hc_in.2.2.1
      have h4 : c 1 < ((p.j : ℝ) + 1) * δd n := hc_in.2.2.2
      rw [abs_sub_le_iff] <;> constructor <;> linarith
    have h_dist : ‖x - c‖ ≤ |x 0 - c 0| + |x 1 - c 1| := by
      let v := x - c
      have h5 : ‖v‖ ^ 2 = (v 0)^2 + (v 1)^2 := by
        rw [EuclideanSpace.real_norm_sq_eq v, Fin.sum_univ_two] <;> rfl
      have h7 : (v 0)^2 + (v 1)^2 ≤ (|v 0| + |v 1|)^2 := by
        have h8 : (v 0)^2 = |v 0|^2 := by simp [sq_abs]
        have h9 : (v 1)^2 = |v 1|^2 := by simp [sq_abs]
        rw [h8, h9]
        have h10 : 0 ≤ 2 * |v 0| * |v 1| := by positivity
        linarith
      have h11 : ‖v‖ ^ 2 ≤ (|v 0| + |v 1|)^2 := by
        rw [h5] <;> exact h7
      have h12 : 0 ≤ ‖v‖ := by positivity
      have h13 : 0 ≤ |v 0| + |v 1| := by positivity
      have h14 : |‖v‖| ≤ |(|v 0| + |v 1|)| := sq_le_sq.mp h11
      have h15 : |‖v‖| = ‖v‖ := by rw [abs_of_nonneg h12]
      have h16 : |(|v 0| + |v 1|)| = |v 0| + |v 1| := by rw [abs_of_nonneg h13]
      rw [h15, h16] at h14
      exact h14
    have hδ_le : δd n ≤ 1 / 8 := le_trans hδn_le_R hδR_eighth
    have h_main : ‖x‖ ≤ 1 := by
      have h_tri : ‖c + (x - c)‖ ≤ ‖c‖ + ‖x - c‖ := norm_add_le c (x - c)
      have h_eq : c + (x - c) = x := by abel
      rw [h_eq] at h_tri
      calc ‖x‖ ≤ ‖c‖ + ‖x - c‖ := h_tri
           _ ≤ 3 / 4 + (|x 0 - c 0| + |x 1 - c 1|) := by gcongr
           _ ≤ 3 / 4 + (δd n + δd n) := by gcongr
           _ ≤ 3 / 4 + (1 / 8 + 1 / 8) := by gcongr
           _ = 1 := by norm_num
    simpa [Metric.mem_closedBall, dist_zero_right] using h_main

  have h_slope_bound : ∀ (p : EuclideanPlane) (hp : p ∈ P_retained)
      (T : DTb n), T ∈ retainedTubeFamily p hp → |T.slope| ≤ 1 := by
    intro p hp T hT
    let q : DSq n := getRetainedSquare p hp
    let hq : q ∈ data.P := getRetainedSquare_mem p hp
    have hT_in_config : T ∈ config_heavy.tubeFamily q (data.hP_sub hq) :=
      data.h_tube_sub q hq hT
    have hT_in_T0 : T ∈ config_heavy.T₀ :=
      config_heavy.h_subset q (data.hP_sub hq) hT_in_config
    have h_strip : -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ) := h_tubes_strip' T hT_in_T0
    exact full_T0_slope_bound (hn_pos := hn_pos) h_strip

  have h_intercept_bound : ∀ (p : EuclideanPlane) (hp : p ∈ P_retained)
      (T : DTb n), T ∈ retainedTubeFamily p hp → |T.intercept| ≤ 3 := by
    intro p hp T hT
    let q : DSq n := getRetainedSquare p hp
    let hq : q ∈ data.P := getRetainedSquare_mem p hp
    have h_inter : (T.toSet ∩ q.toSet).Nonempty :=
      data.h_tube_intersect q hq T hT
    have h_q_unit : 0 ≤ q.i ∧ q.i < (2 ^ n : ℤ) ∧ 0 ≤ q.j ∧ q.j < (2 ^ n : ℤ) :=
      h_squares_unit' q (data.hP_sub hq)
    have h_slope : |T.slope| ≤ 1 := h_slope_bound p hp T hT
    exact tube_intercept_bound_from_intersection (hn_pos := hn_pos) T q h_inter h_q_unit h_slope

  let C_T : ℝ := 5 * data.K * C₁
  have hCT_one' : 1 ≤ C_T := by
    dsimp only [C_T]
    have h1 : 1 ≤ data.K := data.hK_ge1
    have h2 : 1 ≤ C₁ := hC₁
    have h3 : 0 < data.K := by linarith
    have h4 : 0 < C₁ := by linarith
    have h5 : data.K * C₁ ≥ 1 := by
      have h51 : data.K * C₁ ≥ 1 * C₁ := by
        exact mul_le_mul_of_nonneg_right h1 (by linarith)
      have h52 : 1 * C₁ = C₁ := by ring
      rw [h52] at h51
      linarith
    have h6 : 5 * data.K * C₁ ≥ 5 := by
      have h61 : 5 * data.K * C₁ = 5 * (data.K * C₁) := by ring
      rw [h61]
      have h63 : (5 : ℝ) * 1 ≤ (5 : ℝ) * (data.K * C₁) :=
        mul_le_mul_of_nonneg_left h5 (by norm_num)
      have h64 : (5 : ℝ) * 1 = 5 := by ring
      rw [h64] at h63
      exact h63
    have h7 : (1 : ℝ) ≤ 5 := by norm_num
    linarith
  have hTubes_sset : ∀ (p : EuclideanPlane) (hp : p ∈ P_retained),
      IsDeltaSSet (δd n) s C_T (retainedTubeFamily p hp : Set (DTb n)) := by
    intro p hp
    let q : DSq n := getRetainedSquare p hp
    let hq : q ∈ data.P := getRetainedSquare_mem p hp
    have h_main : IsDeltaSSet (δd n) s (5 * data.K * C₁) (retainedTubeFamily p hp : Set (DTb n)) :=
      retained_sset_from_b1_data q hq hC₁ hs
    simpa [C_T] using h_main

  have hIncidence : ∀ (p : EuclideanPlane) (hp : p ∈ P_retained)
      (T : DTb n), T ∈ retainedTubeFamily p hp →
      ∃ (Q : DSq n), p ∈ (Q.toSet : Set EuclideanPlane) ∧ (T.toSet ∩ Q.toSet).Nonempty := by
    intro p hp T hT
    let q : DSq n := getRetainedSquare p hp
    let hq : q ∈ data.P := getRetainedSquare_mem p hp
    have h_p_in : p ∈ (q.toSet : Set EuclideanPlane) := getRetainedSquare_in p hp
    have h_inter : (T.toSet ∩ q.toSet).Nonempty :=
      data.h_tube_intersect q hq T hT
    exact ⟨q, h_p_in, h_inter⟩

  let C_retained : ℝ := C_point
  let K_retained : ℝ := K_P
  let δ_app : ℝ := 9 * δd n

  have h_majorant_point : C_point ≤ (δd n)^(-(εReg + pointLoss)) * (10 : ℝ)^50 * (n : ℝ)^16 :=
    point_majorant_general
      (δ_n := δd n)
      (N := config.P₀.card)
      (A_P := (10 : ℝ)^6)
      (K_B1 := K_B1)
      hn_pos
      (Finset.card_pos.mpr hP0_nonempty)
      hN_le
      (DiscretisedFurstenbergEstimate.dyadicDelta_pos n)
      hδn_lt_one
      hεReg_pos
      hpointLoss_pos
      (by norm_num)
      (by norm_num)
      (le_of_lt (lt_of_lt_of_le (by norm_num) data.hK_ge1))
      hK_B1_bound
      (le_of_lt hK_global_pos)
      hK_global_bound
      hC_P_bound
  have hδn_le_δ_abs : δd n ≤ δ_abs := le_trans hδn_le_R hδR_le_abs
  have h_absorb_point : C_retained * 361 ≤ Real.rpow δ_app (-εA) := by
    have h1 : C_point * 361 ≤
        (δd n)^(-(εReg + pointLoss)) * (10 : ℝ)^50 * (n : ℝ)^16 * 361 :=
      mul_le_mul_of_nonneg_right h_majorant_point (by norm_num)
    have h2 := h_abs_point n hδn_le_δ_abs
    simpa [δ_app] using le_trans h1 h2
  have h9_pow : (9 : ℝ)^(u / 2) ≤ 9 := nine_half_pow_le_nine u hu2
  have hK_P_nonneg : 0 ≤ K_P := hK_P_pos.le
  have h12 : K_retained * (9 : ℝ)^(u / 2) ≤ (δd n)^(-rho_sqrt) * 9 := by
    have h13 : K_retained = K_P := by rfl
    rw [h13]
    have h14 : K_P * (9 : ℝ)^(u / 2) ≤ K_P * 9 :=
      mul_le_mul_of_nonneg_left h9_pow hK_P_nonneg
    have h15 : K_P * 9 ≤ (δd n)^(-rho_sqrt) * 9 :=
      mul_le_mul_of_nonneg_right hK_P_bound (by norm_num)
    exact le_trans h14 h15
  have hδn_le_app_sqrt : δd n ≤ δ_app_sqrt := le_trans hδn_le_R hδR_le_app_sqrt
  have h_abs_sqrt_applied : (δd n)^(-rho_sqrt) * 9 ≤ (9 * δd n)^(-εA) :=
    h_abs_sqrt n hδn_le_app_sqrt
  have h_absorb_sqrt : K_retained * (9 : ℝ)^(u / 2) ≤ Real.rpow δ_app (-εA) := by
    simpa [δ_app] using le_trans h12 h_abs_sqrt_applied
  have h_majorant_tube : max 1 (10 * C_T) ≤
      (δd n)^(-(εReg + tubeLoss)) * (10 : ℝ)^20 * (n : ℝ)^7 :=
    tube_majorant
      hn_pos hεReg_pos htubeLoss_pos hC₁ data.hK_ge1 hC₁_bound hK_B1_bound
  have hδn_le_δ_B1 : δd n ≤ δ_B1 := le_trans hδn_le_R hδR_le_B1
  have h_absorb_tube : max 1 (10 * C_T) * 628849 * 44^s ≤ Real.rpow δ_app (-εA) := by
    have h_pos : 0 ≤ 628849 * (44 : ℝ)^s := by
      have h1 : 0 ≤ (44 : ℝ)^s := Real.rpow_nonneg (by norm_num) s
      exact mul_nonneg (by norm_num) h1
    have h1 : max 1 (10 * C_T) * 628849 * (44 : ℝ)^s ≤
        (δd n)^(-(εReg + tubeLoss)) * (10 : ℝ)^20 * (n : ℝ)^7 * 628849 * (44 : ℝ)^s := by
      have h_pos1 : (0 : ℝ) ≤ 628849 := by norm_num
      have h_pos2 : (0 : ℝ) ≤ (44 : ℝ)^s := Real.rpow_nonneg (by norm_num) s
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h_majorant_tube h_pos1) h_pos2
    have h2 := h_abs_tube n hδn_le_δ_B1
    simpa [δ_app] using le_trans h1 h2

  have h9δn_le_deltaA : 9 * δd n ≤ δA := by
    have h1 : 9 * δd n ≤ 9 * δR := by
      exact mul_le_mul_of_nonneg_left hδn_le_R (by norm_num)
    have h2 : 9 * δR ≤ δA := h9δR_le_δA
    exact le_trans h1 h2

  have h_appA_disj : _ :=
    apply_appendix_a_to_dyadic_at_radius
      (hnm := hnm) (h_even := h_even)
      (hs_pos := hs) (hs_lt_one := hs1) (hst := hst) (hu_t := hu_t) (hu_two := hu2)
      (C_P := C_retained) (K_P := K_retained) (C_T := C_T)
      (P := P_retained) (hP_bdd := hP_retained_ball) (hP_regular := h_retained_regular)
      (tubeFamily := retainedTubeFamily) (hTubes_sset := hTubes_sset)
      (h_slope_bound := h_slope_bound) (h_intercept_bound := h_intercept_bound)
      (hIncidence := hIncidence) (hCT_one := hCT_one')
      (εA := εA) (hεA_pos := hεA_pos)
      (deltaA := δA) (hδA_pos := hδA_pos) (hδA_one := hδA_one)
      (h_body := hAppABody)
      (h_absorb_point := h_absorb_point) (h_absorb_sqrt := h_absorb_sqrt)
      (h_absorb_tube := h_absorb_tube) (h9δn_le_deltaA := h9δn_le_deltaA)

  -- STEP 14: Branch on Appendix A outcome
  let allRetainedTubes : Finset (DTb n) :=
    data.P.attach.biUnion (fun q => data.tubeFamily q q.property)

  -- Slope bound for all retained tubes (direct proof via data.h_tube_sub)
  have hm_all : ∀ T ∈ allRetainedTubes, |T.slope| ≤ 1 := by
    intro T hT
    rcases Finset.mem_biUnion.mp hT with ⟨q, _, hTq⟩
    have hT_in_config : T ∈ config_heavy.tubeFamily q.val (data.hP_sub q.property) :=
      data.h_tube_sub q.val q.property hTq
    have hT_in_T0 : T ∈ config_heavy.T₀ :=
      config_heavy.h_subset q.val (data.hP_sub q.property) hT_in_config
    have h_strip : -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ) := h_tubes_strip' T hT_in_T0
    exact full_T0_slope_bound (hn_pos := hn_pos) h_strip

  -- Intercept bound for all retained tubes via tube_intercept_bound_from_intersection
  have hb_all : ∀ T ∈ allRetainedTubes, |T.intercept| ≤ 3 := by
    intro T hT
    rcases Finset.mem_biUnion.mp hT with ⟨q, _, hTq⟩
    let q' : DSq n := q.val
    have hq' : q' ∈ data.P := q.property
    have h_inter : (T.toSet ∩ q'.toSet).Nonempty :=
      data.h_tube_intersect q' hq' T hTq
    have h_q_unit : 0 ≤ q'.i ∧ q'.i < (2 ^ n : ℤ) ∧ 0 ≤ q'.j ∧ q'.j < (2 ^ n : ℤ) :=
      h_squares_unit' q' (data.hP_sub hq')
    have h_slope : |T.slope| ≤ 1 := hm_all T hT
    exact tube_intercept_bound_from_intersection (hn_pos := hn_pos) T q' h_inter h_q_unit h_slope

  let δ' : ℝ := δ / 4
  have hδ'_pos : 0 < δ' := by positivity
  have hδ'_eq : δ' = δ / 4 := by rfl
  -- Scale conditions from frontend even-scale selection
  have h_scale' : δd n ≤ δ' := by
    simpa [hδ'_eq] using h_scale
  have h_scale2' : δ' < 4 * δd n := by
    simpa [hδ'_eq] using h_scale2
  -- Provenance thickness from frontend tube construction
  have h_all_sub_T0 : ∀ (X : DTb n), X ∈ allRetainedTubes → X ∈ config.T₀ := by
    intro T hT
    rcases Finset.mem_biUnion.mp hT with ⟨q, _, hTq⟩
    have hT_in_heavy : T ∈ config_heavy.tubeFamily q.val (data.hP_sub q.property) :=
      data.h_tube_sub q.val q.property hTq
    have hT_in_T0 : T ∈ config_heavy.T₀ :=
      config_heavy.h_subset q.val (data.hP_sub q.property) hT_in_heavy
    exact h_T0_sub hT_in_T0
  have h_thick : ∀ (T : DTb n), T ∈ allRetainedTubes →
      ∃ (ℓ : AffineLine), ℓ ∈ originalFamily ∧
        dist (toAffineLine T) (RegularIncidence.S0_line ℓ) ≤ (15 / 2 : ℝ) * δ' := by
    intro T hT
    have hT_in_T0 : T ∈ config.T₀ := h_all_sub_T0 T hT
    exact h_tube_provenance T hT_in_T0
  -- Fine branch exponent parameters
  let ρ_T : ℝ := fine_loss
  let loss_fine : ℝ := fine_loss
  have h_pos_diff : 0 < εA - εInc := sub_pos.mpr hεInc_lt_εA
  have hx_nonneg : 0 ≤ fine_loss := div_nonneg h_pos_diff.le (by norm_num)
  have h_budget_raw : εInc ≤ εA - fine_loss - fine_loss := by
    have h_fl : fine_loss = (εA - εInc) / 3 := by
      rfl
    rw [h_fl]
    exact fine_budget_thirds (le_of_lt hεInc_lt_εA)
  have hρ_T_nonneg : 0 ≤ ρ_T := hx_nonneg
  have hloss_fine_nonneg : 0 ≤ loss_fine := hx_nonneg
  have h_budget : εInc ≤ εA - ρ_T - loss_fine := h_budget_raw
  -- Missing: absorption conditions (frontend must ensure δ_n small enough)
  have h_absorb_Cpack : (FixedPackingBound.C_pack : ℝ) ≤ (δd n)^(-ρ_T) := by
    have hδn_pos' : 0 < δd n :=
      DiscretisedFurstenbergEstimate.dyadicDelta_pos n
    simpa [ρ_T] using h_abs_Cpack_raw (δd n) hδn_pos' (le_trans hδn_le_R hδR_le_Cpack)
  have h_scale_small : (δd n)^(-loss_fine) ≥ (9 : ℝ)^(2 * s + εA) := by
    have hδn_pos'' : 0 < δd n :=
      DiscretisedFurstenbergEstimate.dyadicDelta_pos n
    simpa [loss_fine] using h_abs_9factor_raw (δd n) hδn_pos'' (le_trans hδn_le_R hδR_le_9factor)
  have hδn_leδ : δd n ≤ δ := by
    have h : δd n ≤ δ / 4 := h_scale
    linarith

  -- Forward inclusion: union over P_retained ⊆ image of allRetainedTubes
  have h_union_sub : (⋃ (p : EuclideanPlane), ⋃ (hp : p ∈ P_retained),
        toAffineLine '' (retainedTubeFamily p hp : Set (DTb n))) ⊆
      toAffineLine '' (allRetainedTubes : Set (DTb n)) := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨p, hp, T, hT, rfl⟩
    let q : DSq n := getRetainedSquare p hp
    let hq : q ∈ data.P := getRetainedSquare_mem p hp
    have hT_in_all : T ∈ allRetainedTubes := by
      rw [Finset.mem_biUnion]
      refine ⟨⟨q, hq⟩, ?_⟩
      simpa [retainedTubeFamily, getRetainedSquare] using hT
    exact Set.mem_image_of_mem toAffineLine hT_in_all

  -- Case split on Appendix A disjunction
  cases h_appA_disj with
  | inl h_fine =>
    -- Fine branch: transfer bound via Ncover monotonicity (union ⊆ image)
    have h_fine9 : ENNReal.ofReal ((9 * δd n)^(-(2 * s + εA))) ≤
        RegularIncidence.Ncover (9 * δd n) (toAffineLine '' (allRetainedTubes : Set (DTb n))) := by
      have h1 : RegularIncidence.Ncover (9 * δd n)
            (⋃ (p : EuclideanPlane), ⋃ (hp : p ∈ P_retained),
              toAffineLine '' (retainedTubeFamily p hp : Set (DTb n))) ≤
          RegularIncidence.Ncover (9 * δd n)
            (toAffineLine '' (allRetainedTubes : Set (DTb n))) :=
        by simpa [RegularIncidence.Ncover] using Metric.externalCoveringNumber_mono_set h_union_sub
      exact le_trans h_fine h1
    exact fine_branch_full
      (retainedTubes := allRetainedTubes)
      (originalFamily := originalFamily)
      (hδn_pos := DiscretisedFurstenbergEstimate.dyadicDelta_pos n)
      (hδn_eq := by rfl)
      (hδn_one := by linarith [hδn_le_R, hδR_eighth])
      (hδ'_pos := hδ'_pos)
      (hδ'_eq := hδ'_eq)
      (hδ_pos := hδ_pos)
      (h_scale := h_scale)
      (h_scale2 := h_scale2)
      (hδn_leδ := hδn_leδ)
      (hm := hm_all)
      (hb := hb_all)
      (hs_pos := hs)
      (hεA_pos := hεA_pos)
      (hεInc_pos := hεInc_pos)
      (hρ_T_nonneg := hρ_T_nonneg)
      (hloss_fine_nonneg := hloss_fine_nonneg)
      (h_budget := h_budget)
      (h_absorb_Cpack := h_absorb_Cpack)
      (h_scale_small := h_scale_small)
      (h_fine9 := h_fine9)
      (h_thick := h_thick)
  | inr h_coarse =>
    -- Coarse branch: juniper's coarse_branch_from_b1_data
    -- Select Q via retained-fiber density (for FineCor25 chain)
    rcases b1_induction_data_select_fiber hnm data K_global hK_global_pos h_global_card h_fineP_eq_all
      with ⟨Q, hQ, h_density, h_fineP_eq⟩
    -- Alpha parameters
    let u0 : ℝ := min u 1
    let α_base : ℝ := (min t 1 - s) / (1 - s)
    let α_actual : ℝ := (u0 - s) / (1 - s)
    let coarseGain_raw : ℝ := εA * α_base / 2
    -- Coarse polylog loss
    let loss_coarse : ℝ := loss_parent / 2
    -- Geometry constant from Appendix A coarse bound + root-aware parent geometry
    -- (Inlined to avoid let-binding timeout in large context)
    have hC_geo_pos : 0 < ((9 : ℝ)^(-(s + εA)) / (262144 : ℝ)^2) := by
      have h1 : 0 < (9 : ℝ)^(-(s + εA)) := Real.rpow_pos_of_pos (by norm_num) _
      have h2 : (0 : ℝ) < (262144 : ℝ)^2 := by positivity
      exact div_pos h1 h2
    have h_absorb_geo : ((9 : ℝ)^(-(s + εA)) / (262144 : ℝ)^2) ≥ (δd n)^loss_parent :=
      h_absorb_geo_frontend
    have h_coarse_bound_geo : (data.coarseConfig.T₀.card : ℝ) ≥
        ((9 : ℝ)^(-(s + εA)) / (262144 : ℝ)^2) * (δd n)^(-(s + εA)) := by
      -- Appendix A coarse: (9δn)^{-(s+εA)} ≤ Ncover(3δ_m, union)
      have h_sqrt_eq : Real.sqrt (9 * δd n) = 3 * δd m :=
        dyadic_delta_sqrt_eq n m h_even
      have h_coarse' : ENNReal.ofReal ((9 * δd n)^(-(s + εA))) ≤
          RegularIncidence.Ncover (3 * δd m)
            (toAffineLine '' (allRetainedTubes : Set (DTb n))) := by
        have h_mono1 : RegularIncidence.Ncover (3 * δd m)
              (⋃ (p : EuclideanPlane), ⋃ (hp : p ∈ P_retained),
                toAffineLine '' (retainedTubeFamily p hp : Set (DTb n))) ≤
            RegularIncidence.Ncover (3 * δd m)
              (toAffineLine '' (allRetainedTubes : Set (DTb n))) :=
          by simpa [RegularIncidence.Ncover] using Metric.externalCoveringNumber_mono_set h_union_sub
        have h_coarse3 : ENNReal.ofReal ((9 * δd n)^(-(s + εA))) ≤
            RegularIncidence.Ncover (3 * δd m)
              (⋃ (p : EuclideanPlane), ⋃ (hp : p ∈ P_retained),
                toAffineLine '' (retainedTubeFamily p hp : Set (DTb n))) :=
          by simpa [h_sqrt_eq, RegularIncidence.Ncover] using h_coarse
        exact le_trans h_coarse3 h_mono1
      -- Geometry: Ncover(3δ_m, image) ≤ 262144² * |coarseTubes|
      have h_parent_geom : ∀ (T : DTb n), T ∈ allRetainedTubes →
          ∃ (C : _root_.DyadicTube n) (U_stand : _root_.DyadicTube m),
            C.a = T.a ∧ |(C.b : ℝ) - (T.b : ℝ)| ≤ 1 ∧
            C.toSet ⊆ U_stand.toSet ∧
            |(DiscretisedFurstenbergEstimate.Bridge.tubeToMainShifted U_stand).slope| ≤ 1 ∧
            DiscretisedFurstenbergEstimate.Bridge.tubeToMainShifted U_stand ∈ data.coarseConfig.T₀ :=
        fun T hT => b1_data_to_parent data T hT
      have h_geom : RegularIncidence.Ncover (3 * δd m)
            (toAffineLine '' (allRetainedTubes : Set (DTb n))) ≤
          (262144 : ENNReal)^2 * (data.coarseConfig.T₀.card : ENNReal) :=
        coarse_ncover_3_le_coarseCard_via_root hnm allRetainedTubes data.coarseConfig.T₀
          hm_all hb_all h_parent_geom
      -- Combine: (9δn)^{-(s+εA)} ≤ 262144² * |coarseTubes|
      have h3 : ENNReal.ofReal ((9 * δd n)^(-(s + εA))) ≤
          (262144 : ENNReal)^2 * (data.coarseConfig.T₀.card : ENNReal) :=
        le_trans h_coarse' h_geom
      -- Convert to real and rearrange
      have h4 : ((9 * δd n)^(-(s + εA)) : ℝ) ≤
          (262144 : ℝ)^2 * (data.coarseConfig.T₀.card : ℝ) := by
        exact_mod_cast h3
      exact coarse_geo_bound_algebra s εA (δd n) (DiscretisedFurstenbergEstimate.dyadicDelta_pos n)
        data.coarseConfig.T₀.card h4
    -- Prop 5: apply uniform_prop5_wrapper_with_K to data.coarseConfig (outer K, t'=u0)
    -- Scale constants to ≥ 1
    let C_P_prop5 : ℝ := max C_coarse_point 1
    let CΔ_prop5 : ℝ := max data.CΔ 1
    have hC_P_prop5_pos : 0 < C_P_prop5 :=
      lt_of_lt_of_le zero_lt_one (le_max_right C_coarse_point 1)
    have hC_P_prop5_ge1 : 1 ≤ C_P_prop5 := le_max_right _ _
    have hCΔ_prop5_pos : 0 < CΔ_prop5 :=
      lt_of_lt_of_le zero_lt_one (le_max_right data.CΔ 1)
    have hCΔ_prop5_ge1 : 1 ≤ CΔ_prop5 := le_max_right _ _
    -- Modified coarse config with CΔ_prop5 ≥ 1
    let coarseConfig' : CTNiceConfiguration m s CΔ_prop5 data.MΔ :=
      { P₀ := data.coarseConfig.P₀,
        T₀ := data.coarseConfig.T₀,
        tubeFamily := data.coarseConfig.tubeFamily,
        h_subset := data.coarseConfig.h_subset,
        h_size := data.coarseConfig.h_size,
        h_delta_s_set := fun p hp => IsDeltaSSet.mono_const (data.coarseConfig.h_delta_s_set p hp) (le_max_left data.CΔ 1),
        h_intersect := data.coarseConfig.h_intersect,
        h_tube_parameters := data.coarseConfig.h_tube_parameters,
        h_bounded := data.coarseConfig.h_bounded }
    -- Cap S-set exponent u → u0 = min(u,1), after scaling constant to ≥1
    have h_coarse_sset_scaled : DiscretisedFurstenbergEstimate.IsFinsetDeltaSSet (δd m) u C_P_prop5
        (DiscretisedFurstenbergEstimate.DyadicConversion.finsetDyadicToDSquare data.coarseConfig.P₀) :=
      IsDeltaSSet.mono_const h_coarse_sset (le_max_left C_coarse_point 1)
    have h_coarse_sset_u0 : DiscretisedFurstenbergEstimate.IsFinsetDeltaSSet (δd m) u0 C_P_prop5
        (DiscretisedFurstenbergEstimate.DyadicConversion.finsetDyadicToDSquare data.coarseConfig.P₀) :=
      DiscretisedFurstenbergEstimate.sset_cap_exponent_at_one h_coarse_sset_scaled hC_P_prop5_ge1
    -- Coarse square index bounds: containingSquare preserves [0,2^m) range
    have h_coarse_index_bounds : ∀ (Q : DiscretisedFurstenbergEstimate.DyadicSquare m), Q ∈ data.coarseConfig.P₀ →
        0 ≤ Q.i ∧ Q.i < (2 ^ m : ℤ) ∧ 0 ≤ Q.j ∧ Q.j < (2 ^ m : ℤ) := by
      intro Q hQ
      have h1 : Q ∈ (data.P.image (DiscretisedFurstenbergEstimate.InductionConfigurations.containingSquare hnm)) := by
        rw [data.h_coarse_P_eq] at hQ; exact hQ
      rcases Finset.mem_image.mp h1 with ⟨p_dy, hp_dy, rfl⟩
      have h2 : p_dy ∈ config_heavy.P₀ := data.hP_sub hp_dy
      have h3 := h_squares_unit' p_dy h2
      have h4 : 0 ≤ p_dy.i := h3.1
      have h5 : p_dy.i < (2 ^ n : ℤ) := h3.2.1
      have h7 : 0 ≤ p_dy.j := h3.2.2.1
      have h8 : p_dy.j < (2 ^ n : ℤ) := h3.2.2.2
      have h_nmm : n = m + m := by omega
      have h2m_pos : 0 < (2 ^ m : ℤ) := by positivity
      have h2m_nonneg : 0 ≤ (2 ^ m : ℤ) := by positivity
      have h_rf : (DiscretisedFurstenbergEstimate.InductionConfigurations.refinementFactor n m : ℤ) = (2 ^ m : ℤ) := by
        have h1 : n - m = m := by omega
        simp [DiscretisedFurstenbergEstimate.InductionConfigurations.refinementFactor, h1] <;> omega
      have h_bound_i : p_dy.i < (2 ^ m : ℤ) * (2 ^ m : ℤ) := by
        have h9 : (2 ^ n : ℤ) = (2 ^ m : ℤ) * (2 ^ m : ℤ) := by
          rw [h_nmm, pow_add] <;> ring
        rw [h9] at h5; exact h5
      have h_bound_j : p_dy.j < (2 ^ m : ℤ) * (2 ^ m : ℤ) := by
        have h9 : (2 ^ n : ℤ) = (2 ^ m : ℤ) * (2 ^ m : ℤ) := by
          rw [h_nmm, pow_add] <;> ring
        rw [h9] at h8; exact h8
      have h_i_def : (DiscretisedFurstenbergEstimate.InductionConfigurations.containingSquare hnm p_dy).i = p_dy.i / (2 ^ m : ℤ) := by
        simp [DiscretisedFurstenbergEstimate.InductionConfigurations.containingSquare, h_rf] <;> rfl
      have h_j_def : (DiscretisedFurstenbergEstimate.InductionConfigurations.containingSquare hnm p_dy).j = p_dy.j / (2 ^ m : ℤ) := by
        simp [DiscretisedFurstenbergEstimate.InductionConfigurations.containingSquare, h_rf] <;> rfl
      have h_ii : 0 ≤ p_dy.i / (2 ^ m : ℤ) := Int.ediv_nonneg h4 h2m_nonneg
      have h_ij : p_dy.i / (2 ^ m : ℤ) < (2 ^ m : ℤ) := Int.ediv_lt_of_lt_mul h2m_pos h_bound_i
      have h_ji : 0 ≤ p_dy.j / (2 ^ m : ℤ) := Int.ediv_nonneg h7 h2m_nonneg
      have h_jj : p_dy.j / (2 ^ m : ℤ) < (2 ^ m : ℤ) := Int.ediv_lt_of_lt_mul h2m_pos h_bound_j
      constructor
      · rw [h_i_def]; exact h_ii
      · constructor
        · rw [h_i_def]; exact h_ij
        · constructor
          · rw [h_j_def]; exact h_ji
          · rw [h_j_def]; exact h_jj
    -- h_unit: |x.1| ≤ 1 for all points in all coarse DSquares
    have h_coarse_unit := b1_geometry_unit_of_bounds (config := data.coarseConfig) h_coarse_index_bounds
    -- h_diam: dist ≤ 3 for any two coarse DSquares
    have h_coarse_diam := b1_geometry_diam_of_bounds (config := data.coarseConfig) h_coarse_index_bounds
    -- m ≥ 2 (from δd n ≤ 1/8 and n = 2m)
    have hm_ge2 : 2 ≤ m := hm_ge2_from_delta n m h_even (le_trans hδn_le_R hδR_eighth)
    have h_coarse_sset_u0' : DiscretisedFurstenbergEstimate.IsFinsetDeltaSSet (δd m) u0 C_P_prop5
        (DiscretisedFurstenbergEstimate.DyadicConversion.finsetDyadicToDSquare coarseConfig'.P₀) := by
      have hP_eq : coarseConfig'.P₀ = data.coarseConfig.P₀ := by rfl
      rw [hP_eq]
      exact h_coarse_sset_u0
    have h_coarse_P_nonempty : coarseConfig'.P₀.Nonempty := by
      have hP_eq : coarseConfig'.P₀ = data.coarseConfig.P₀ := by rfl
      rw [hP_eq, data.h_coarse_P_eq]
      exact data.hP_nonempty.image _
    -- Apply production wrapper
    have h_prop5_raw := apply_prop5_wrapper
      m s u0 CΔ_prop5 C_P_prop5 K data.MΔ
      hK_pos hK_spec
      (le_of_lt hsu0_lt)
      (hu0_one)
      coarseConfig'
      (hn_ge_2 := hm_ge2)
      (hM_pos := data.hMΔ_pos)
      (hP_nonempty := h_coarse_P_nonempty)
      (hCP := hC_P_prop5_pos)
      (hCP_ge1 := hC_P_prop5_ge1)
      (hC₁ := hCΔ_prop5_pos)
      (hC1_ge1 := hCΔ_prop5_ge1)
      (hs_nonneg := le_of_lt hs)
      (hP_set := h_coarse_sset_u0')
      (h_slope := data.h_coarse_slope)
      (h_diam := h_coarse_diam)
      (h_unit := h_coarse_unit)
    -- Define C_prop5 with actual constants (coarse-scale formulation)
    let C_prop5 : ℝ := Section6.C_prop5_at_coarse_scale K C_P_prop5 CΔ_prop5 s (δd m)
    have hδm_lt_one : δd m < 1 :=
      dyadicDelta_lt_one m hm_ge2
    have hδm_pos : 0 < δd m := by
      rw [dyadicDelta_eq_inv_pow m]
      positivity
    have hC_prop5_pos : 0 < C_prop5 :=
      C_prop5_at_coarse_scale_pos K C_P_prop5 CΔ_prop5 s (δd m)
        hK_pos hC_P_prop5_pos hCΔ_prop5_pos (le_of_lt hs) hδm_pos hδm_lt_one
    -- Extract h_prop5: wrapper conclusion matches C_prop5 * MΔ * δm^{-s} * (MΔ*δm^s)^α_actual
    have h_prop5 : (data.coarseConfig.T₀.card : ℝ) ≥
        C_prop5 * (data.MΔ : ℝ) * (δd m)^(-s) *
        ((data.MΔ : ℝ) * (δd m)^s)^α_actual :=
      prop5_match_coarse_form
        (u0 := u0)
        (α := α_actual)
        (K := K)
        (C_P := C_P_prop5)
        (C₁ := CΔ_prop5)
        (s := s)
        (δ := δd m)
        (M := (data.MΔ : ℝ))
        (card := (data.coarseConfig.T₀.card : ℝ))
        (hα := by rfl)
        (h_raw := h_prop5_raw)
        (hK_pos := hK_pos)
        (hCP_pos := hC_P_prop5_pos)
        (hC1_pos := hCΔ_prop5_pos)
        (hδ_pos := hδm_pos)
        (hs_nonneg := le_of_lt hs)
    -- Polylog absorption: C_prop5 ≥ δn^loss_coarse (via top-level adapter)
    have hC_point_nonneg : 0 ≤ C_point :=
      C_point_nonneg_lemma C_P hCP_nonneg config.P₀.card K_global hK_global_pos
    have h_absorb_prop5 : C_prop5 ≥ (δd n)^loss_coarse :=
      coarse_absorption_adapter
        n m hn_pos h_even
        K s εReg pointLoss tubeLoss
        C_point K_B1 u C₁ data.CΔ
        (le_of_lt (lt_trans hs (lt_of_lt_of_le hst hu_t))) hu2
        loss_coarse δ_prop5
        h_majorant_point hK_B1_bound hC₁_bound
        hK_pos (le_of_lt hs)
        hC_point_nonneg
        data.hK_ge1 hC₁
        data.hCΔ_compare.1 data.hCΔ_compare.2
        hεReg_pos hpointLoss_pos htubeLoss_pos
        hδn_pos hδn_lt_one
        (le_trans hδn_le_R hδR_le_prop5)
        h_abs_prop5_spec
    have h_ledger : (0 ≤ loss_coarse) ∧
        (loss_coarse < (εA - loss_parent) * α_actual / 2) ∧
        (loss_coarse ≤ loss_parent / 2) ∧
        (netGain ≤ coarseGain_raw - localLoss - lambda - rho_M - loss_B1 - loss_parent) := by
      dsimp only [loss_coarse, α_actual, u0, coarseGain_raw, α_base]
      exact coarse_loss_ledger_adapter
        s t u hs1 hst hu_t
        εA loss_parent coarseGain netGain localLoss lambda rho_M loss_B1
        hεA_pos hloss_parent_pos hnetGain_pos hbudget hcoarseGain_le
        hlocalLoss_pos hlambda_pos hrho_M_pos hloss_B1_pos
    have hloss_coarse_nonneg := h_ledger.1
    have hloss_coarse_small := h_ledger.2.1
    have hloss_coarse_le_half := h_ledger.2.2.1
    have h_selector_budget := h_ledger.2.2.2
    -- Same-Q FineCor25Data via clean_fine_cor25_chain
    -- Use selector fields from FullParameterSelection (NO ad-hoc lets)
    let C_point_chain : ℝ := C_heavy
    have hE : IsDeltaSSet (δd n) u C_point_chain config_heavy.pointSet :=
      hReg_heavy.to_isDeltaSSet
    -- Cancellation using actual K_P (NOT K_P_chain)
    let configP0 : Finset (DiscretisedFurstenbergEstimate.DyadicSquare n) := config.P₀
    let coarseImage := configP0.image containSq
    have h_coarse_sub : data.coarseConfig.P₀ ⊆ coarseImage := by
      rw [data.h_coarse_P_eq]
      have h1 : config_heavy.P₀ ⊆ config.P₀ := by
        rw [hP0_eq]
        exact hP_heavy_sub
      have hP_sub' : data.P ⊆ config.P₀ := Finset.Subset.trans data.hP_sub h1
      exact Finset.image_mono containSq hP_sub'
    have h_cancellation_chain : (data.coarseConfig.P₀.card : ℝ) * (δd m)^u ≤ 9 * K_P :=
      coarse_card_delta_m_u_cancellation_clean
        (hnm := h_even) (config := config) (hReg := h_regular)
        (hK_P_pos := hK_P_pos) (h_coarse_sub := h_coarse_sub)
    -- hnm_ge2: n=2m and n≥3 implies n-m=m≥2
    have hnm_ge2 : 2 ≤ n - m :=
      hnm_ge2_adapter n m h_even (le_trans hδn_le_R hδR_eighth)
    -- h_small_chain: 81 ≤ δ_n^{-fineMarginLoss}
    have h_small_chain : (81 : ℝ) ≤ (δd n)^(-fineMarginLoss) :=
      h_abs_fine_margin (δd n) hδn_pos
        (le_trans hδn_le_R hδR_le_fine_margin)
    -- h_CP_chain: C_heavy ≤ δ_n^{-pointRegularityLoss}
    -- C_heavy = C_P * 18 * numDyadicLevels(card P₀)
    -- C_P ≤ 10^6 * δ_n^{-(εReg+pointLoss)}, numDyadicLevels ≤ 2n+2 ≤ 4n
    -- So C_heavy ≤ 10^8 * n * δ_n^{-(εReg+pointLoss)}
    -- And 10^8 * n ≤ δ_n^{-finePointPolyLoss} from threshold
    have h_CP_majorant : C_point_chain ≤
        (10 : ℝ)^8 * (n : ℝ) * (δd n)^(-(εReg + pointLoss)) := by
      dsimp only [C_point_chain, C_heavy]
      exact fine_chain_CP_majorant_adapter
        n hn_pos config.P₀.card hN_le C_P εReg pointLoss hC_P_bound hδn_pos
    have h_fine_point_abs : C_fine_point_poly * (n : ℝ)^1 ≤ (δd n)^(-finePointPolyLoss) := by
      simpa [pow_one] using h_abs_fine_point n (le_trans hδn_le_R hδR_le_fine_point)
    have h_CP_chain : C_point_chain ≤ (δd n)^(-pointRegularityLoss) :=
      fine_chain_CP_complete_adapter n C_point_chain C_fine_point_poly εReg pointLoss
        finePointPolyLoss pointRegularityLoss (δd n) hδn_pos
        h_CP_majorant h_fine_point_abs hpointRegularityLoss_eq (by rfl)
    -- h_Kglobal_chain: K_global ≤ δ_n^{-fineGlobalPolyLoss}
    have h_Kglobal_chain : K_global ≤ (δd n)^(-fineGlobalPolyLoss) :=
      fine_chain_Kglobal_complete_adapter n hn_pos K_global K_B1 C_fine_global_poly
        fineGlobalPolyLoss (δd n) hδn_pos data.hK_ge1 hK_global_bound hK_B1_bound
        (h_abs_fine_global n (le_trans hδn_le_R hδR_le_fine_global)) (by rfl)
    -- h_KP_chain is directly hK_P_bound using rho_sqrt (NOT εInc)
    have h_KP_chain : K_P ≤ (δd n)^(-rho_sqrt) := hK_P_bound
    -- C_Q_chain = max(data.CQ Q, 1) — interface correction
    let C_Q_chain : ℝ := max (data.CQ Q) 1
    -- hC_Q_bound_chain: max(CQ,1) ≤ δ_n^{-b_fine}
    -- CQ ≤ K_B1 * C₁ ≤ 2700*3145728*(4n+7)^7 * δ_n^{-(εReg+tubeLoss)}
    -- ≤ C_fine_CQ_poly * n^7 * δ_n^{-(εReg+tubeLoss)}
    -- ≤ δ_n^{-fineCQPolyLoss} * δ_n^{-(εReg+tubeLoss)} = δ_n^{-b_fine}
    -- And 1 ≤ δ_n^{-b_fine} since δ_n ≤ 1 and b_fine > 0
    have h_CQ_raw : data.CQ Q ≤ data.K * C₁ := (data.hCQ_compare Q hQ).1
    have h_K_eq : data.K = K_B1 := by rfl
    have h_CQ_majorant1 : data.CQ Q ≤
        C_fine_CQ_poly * (n : ℝ)^7 * (δd n)^(-(εReg + tubeLoss)) := by
      rw [h_K_eq] at h_CQ_raw
      have h4 : 4 * (n : ℝ) + 7 ≤ 11 * (n : ℝ) := by
        have h5 : 1 ≤ (n : ℝ) := by exact_mod_cast hn_pos
        linarith
      calc data.CQ Q
        ≤ K_B1 * C₁ := h_CQ_raw
        _ ≤ (2700 * 3145728 * (4 * (n : ℝ) + 7)^7) * C₁ := by gcongr
        _ ≤ (2700 * 3145728 * (4 * (n : ℝ) + 7)^7) * (δd n)^(-(εReg + tubeLoss)) := by gcongr <;> exact hC₁_bound
        _ ≤ (2700 * 3145728 * (11 * (n : ℝ))^7) * (δd n)^(-(εReg + tubeLoss)) := by
          gcongr
        _ = C_fine_CQ_poly * (n : ℝ)^7 * (δd n)^(-(εReg + tubeLoss)) := by ring
    have h_CQ_fine_abs : C_fine_CQ_poly * (n : ℝ)^7 ≤ (δd n)^(-fineCQPolyLoss) :=
      h_abs_fine_CQ n (le_trans hδn_le_R hδR_le_fine_CQ)
    have h_CQ_bound : data.CQ Q ≤ (δd n)^(-b_fine) := by
      have hbf : b_fine = εReg + tubeLoss + fineCQPolyLoss := hb_fine_eq
      rw [hbf]
      have hδ_pos : 0 < δd n := dyadicDelta_pos n
      calc data.CQ Q
        ≤ C_fine_CQ_poly * (n : ℝ)^7 * (δd n)^(-(εReg + tubeLoss)) := h_CQ_majorant1
        _ ≤ (δd n)^(-fineCQPolyLoss) * (δd n)^(-(εReg + tubeLoss)) := by gcongr
        _ = (δd n)^(-(εReg + tubeLoss + fineCQPolyLoss)) := by
          rw [← Real.rpow_add hδ_pos] <;> ring_nf
    have h1_le_bound : (1 : ℝ) ≤ (δd n)^(-b_fine) := by
      have hδ_le1 : δd n ≤ 1 := le_trans hδn_le_R hδR_one
      have hbf_pos : 0 < b_fine := by linarith [hεReg_pos, htubeLoss_pos, hfineCQPolyLoss_pos]
      have h : (δd n)^(-b_fine) ≥ 1 := by
        have h5 : -b_fine ≤ 0 := by linarith
        have h6 : (δd n)^(-b_fine) ≥ (1 : ℝ)^(-b_fine) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hδ_le1 h5
        simpa using h6
      exact h
    have hC_Q_bound_chain : C_Q_chain ≤ (δd n)^(-b_fine) := by
      dsimp only [C_Q_chain]
      exact max_le h_CQ_bound h1_le_bound
    -- C_ret for fine ratio conversion
    let C_ret_chain : ℝ := C_point_chain * 9 * K_global *
        (data.coarseConfig.P₀.card : ℝ) * (δd m)^u
    have hC_ret_chain_pos : 0 < C_ret_chain := by
      have h1 : 0 < C_point_chain := hE.2.2.1
      have h2 : 0 < (data.coarseConfig.P₀.card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr (⟨Q, hQ⟩)
      positivity
    -- h_C_ret_bound: C_ret ≤ δ_n^{-a_C_ret}
    -- C_ret = C_point * 9 * K_global * card * δ_m^u
    -- ≤ C_point * 9 * K_global * 9 * K_P  (by cancellation)
    -- = 81 * C_point * K_global * K_P
    -- ≤ 81 * δ^{-pointRegLoss} * δ^{-fineGlobalLoss} * δ^{-rho_sqrt}
    -- ≤ δ^{-fineMarginLoss} * δ^{-(pointRegLoss+fineGlobalLoss+rho_sqrt)}  (by h_small)
    -- = δ^{-a_C_ret}
    have h_C_ret_bound : C_ret_chain ≤ (δd n)^(-a_C_ret) := by
      have hδ_pos : 0 < δd n := dyadicDelta_pos n
      have h_acr : a_C_ret = pointRegularityLoss + fineGlobalPolyLoss + rho_sqrt + fineMarginLoss := ha_C_ret_eq
      rw [h_acr]
      calc C_ret_chain
        = C_point_chain * 9 * K_global * ((data.coarseConfig.P₀.card : ℝ) * (δd m)^u) := by ring
        _ ≤ C_point_chain * 9 * K_global * (9 * K_P) := by gcongr
        _ = 81 * C_point_chain * K_global * K_P := by ring
        _ ≤ 81 * (δd n)^(-pointRegularityLoss) * (δd n)^(-fineGlobalPolyLoss) * (δd n)^(-rho_sqrt) := by
          gcongr <;> assumption
        _ = 81 * (δd n)^(-(pointRegularityLoss + fineGlobalPolyLoss + rho_sqrt)) := by
          have h1 : (δd n)^(-pointRegularityLoss) * (δd n)^(-fineGlobalPolyLoss) =
              (δd n)^(-(pointRegularityLoss + fineGlobalPolyLoss)) := by
            rw [← Real.rpow_add hδ_pos] <;> ring_nf
          have h_main : (δd n)^(-pointRegularityLoss) * (δd n)^(-fineGlobalPolyLoss) * (δd n)^(-rho_sqrt) =
              (δd n)^(-(pointRegularityLoss + fineGlobalPolyLoss + rho_sqrt)) := by
            have h2 : (δd n)^(-pointRegularityLoss) * (δd n)^(-fineGlobalPolyLoss) * (δd n)^(-rho_sqrt) =
                ((δd n)^(-pointRegularityLoss) * (δd n)^(-fineGlobalPolyLoss)) * (δd n)^(-rho_sqrt) := by ring
            rw [h2, h1]
            rw [← Real.rpow_add hδ_pos] <;> ring_nf
          have h_target : 81 * (δd n)^(-pointRegularityLoss) * (δd n)^(-fineGlobalPolyLoss) * (δd n)^(-rho_sqrt) =
              81 * ((δd n)^(-pointRegularityLoss) * (δd n)^(-fineGlobalPolyLoss) * (δd n)^(-rho_sqrt)) := by ring
          rw [h_target, h_main] <;> ring
        _ ≤ (δd n)^(-fineMarginLoss) * (δd n)^(-(pointRegularityLoss + fineGlobalPolyLoss + rho_sqrt)) := by
          gcongr
        _ = (δd n)^(-(pointRegularityLoss + fineGlobalPolyLoss + rho_sqrt + fineMarginLoss)) := by
          rw [← Real.rpow_add hδ_pos] <;> ring_nf
    -- h_convert_chain via fine_ratio_convert_for_chain
    have hC_Q_chain_pos : 0 < C_Q_chain := by
      dsimp only [C_Q_chain]
      have h : 0 ≤ max (data.CQ Q) 1 := by positivity
      have h2 : (1 : ℝ) ≤ max (data.CQ Q) 1 := le_max_right _ _
      linarith
    have h_convert_chain : (1 / K) * Real.log (1 / δd (n - m)) ^ (-K) *
        (1 / ((81 * max C_ret_chain 1 * (2 * Real.sqrt 2) ^ s) *
          (13 * C_Q_chain * Real.rpow 2 s))) *
        (δd (n - m)) ^ (-s) ≥
      (δd n) ^ (-(s / 2 - (a_C_ret + b_fine + fineLogLoss))) :=
      h_abs_fine_convert n m hnm h_even C_ret_chain C_Q_chain
        hC_ret_chain_pos hC_Q_chain_pos h_C_ret_bound hC_Q_bound_chain
        (le_trans hδn_le_R hδR_le_fine_convert)
    -- ha proof: selector order is pointRegularityLoss + fineGlobalPolyLoss + rho_sqrt + fineMarginLoss
    -- but clean_fine_cor25_chain expects pointRegularityLoss + rho_sqrt + fineGlobalPolyLoss + fineMarginLoss
    have ha_chain : a_C_ret = pointRegularityLoss + rho_sqrt + fineGlobalPolyLoss + fineMarginLoss := by
      rw [ha_C_ret_eq] <;> ring
    let fineData : FineCor25Data (δd n) s :=
      clean_fine_cor25_chain
        (h_even := h_even) (hnm := hnm)
        (data := data)
        (K := K) (hK_pos := hK_pos)
        (hK_spec := fun C_P C_T M => hK_spec s (by linarith) (by linarith) (n := n - m) C_P C_T M)
        (C_point := C_point_chain) (hE := hE) (hu_pos := by linarith [hst, hu_t]) (hs_u := by linarith [hst, hu_t])
        (K_global := K_global) (hK_global_pos := hK_global_pos)
        (Q := Q) (hQ := hQ) (h_density := h_density) (h_fineP_eq := h_fineP_eq)
        (K_P := K_P) (h_KP_pos := hK_P_pos)
        (h_cancellation := h_cancellation_chain)
        (pointRegularityLoss := pointRegularityLoss) (rho_sqrt := rho_sqrt)
        (loss_global := fineGlobalPolyLoss) (margin := fineMarginLoss) (a_C_ret := a_C_ret)
        (h_CP := h_CP_chain) (h_Kglobal := h_Kglobal_chain)
        (h_KP := h_KP_chain) (h_small := h_small_chain)
        (ha := ha_chain)
        (hs_pos := hs) (hs_lt_one := hs1)
        (hnm_ge2 := hnm_ge2)
        (b := b_fine) (polylogLoss := fineLogLoss)
        (ha_nonneg := by linarith [hpointRegularityLoss_eq, ha_C_ret_eq])
        (hb_nonneg := by linarith [hb_fine_eq])
        (hpolylogLoss_pos := hfineLogLoss_pos)
        (hC_Q_bound := hC_Q_bound_chain)
        (h_convert := h_convert_chain)
    have hfine_count : fineData.localCount = ((data.fineConfig Q hQ).T₀.card : ℝ) := by
      rfl
    have hfine_mult : fineData.localMultiplicity = (data.MQ Q : ℝ) := by
      rfl
    have hfine_loss : fineData.localLoss ≤ localLoss := by
      have h1 : fineData.localLoss = a_C_ret + b_fine + fineLogLoss := by rfl
      rw [h1]
      have h2 : a_C_ret + b_fine + fineLogLoss = localFineLoss := hlocalFineLoss_eq.symm
      rw [h2]
      exact le_of_lt hlocalFineLoss_lt
    -- K_nat bound
    have hK_nat_bound : (Nat.ceil data.K : ℝ) ≤ 2 * 2700 * 3145728 * (4 * (n : ℝ) + 7)^7 := by
      have hK_nonneg : 0 ≤ data.K := by linarith [data.hK_ge1]
      have h1 : (Nat.ceil data.K : ℝ) ≤ data.K + 1 := by
        have h2 : (Nat.ceil data.K : ℝ) < data.K + 1 := Nat.ceil_lt_add_one hK_nonneg
        linarith
      have h2 : data.K + 1 ≤ 2 * data.K := by linarith [data.hK_ge1]
      have h3 : data.K ≤ 2700 * 3145728 * (4 * (n : ℝ) + 7)^7 := hK_B1_bound
      linarith
    -- hselector_budget_M
    have hselector_budget_M : εReg + fixedLoss ≤ lambda + rho_M := hM_lower_exp_le
    -- hδn_small provided by frontend spec
    -- Absorption
    have h_absorb_coarse : ENNReal.ofReal (δ ^ (-(2 * s + εInc))) ≤
        ENNReal.ofReal ((δd n) ^ (-(2 * s + netGain))) / (C_pack : ENNReal) := by
      set δn := δd n with hδn_def
      have hδn_pos : 0 < δn := dyadicDelta_pos n
      have hδn_lt_one : δn < 1 := by
        have h : δn ≤ 1 / 8 := le_trans hδn_le_R hδR_eighth
        linarith
      have h_exp_pos : 0 < 2 * s + εInc := by linarith [hs, hεInc_pos]
      have h_gap_pos : 0 < netGain - εInc := by linarith [hεInc_lt_netGain]
      have h4δn_leδ : 4 * δn ≤ δ := by linarith [h_scale]
      have h1 : δ ^ (-(2 * s + εInc)) ≤ (4 * δn) ^ (-(2 * s + εInc)) := by
        exact Real.rpow_le_rpow_of_nonpos (by positivity) h4δn_leδ (by linarith)
      have h2 : (4 * δn) ^ (-(2 * s + εInc)) =
          (4 : ℝ)^(-(2 * s + εInc)) * δn ^ (-(2 * s + εInc)) := by
        rw [Real.mul_rpow (by norm_num) hδn_pos.le] <;> ring
      have h3 : δn ^ (-(2 * s + εInc)) =
          δn ^ (-(2 * s + netGain)) * δn ^ (netGain - εInc) := by
        have h4 : -(2 * s + εInc) = -(2 * s + netGain) + (netGain - εInc) := by ring
        rw [h4]
        rw [← Real.rpow_add hδn_pos] <;> ring
      have h5 : (4 : ℝ)^(-(2 * s + εInc)) * δn ^ (netGain - εInc) ≤ 1 / (C_pack : ℝ) := by
        set x : ℝ := (4 : ℝ)^(-(2 * s + εInc)) * δn ^ (netGain - εInc) with hx_def
        have h6 : (C_pack : ℝ) * x ≤ 1 := by
          simpa [hx_def, mul_assoc] using h_coarse_absorb
        have hCpack_pos : (0 : ℝ) < (C_pack : ℝ) := by
          have h : C_pack = 31730689 := FixedPackingBound.C_pack_eq
          rw [h] <;> norm_num
        have hCpack_ne : (C_pack : ℝ) ≠ 0 := hCpack_pos.ne'
        have h_eq : (C_pack : ℝ) * x / (C_pack : ℝ) = x := by
          exact mul_div_cancel_left₀ x hCpack_ne
        have h9 : x ≤ 1 / (C_pack : ℝ) := by
          calc x
            = (C_pack : ℝ) * x / (C_pack : ℝ) := h_eq.symm
          _ ≤ (1 : ℝ) / (C_pack : ℝ) := by gcongr
        exact h9
      have h_main_real : δ ^ (-(2 * s + εInc)) ≤
          δn ^ (-(2 * s + netGain)) / (C_pack : ℝ) := by
        calc δ ^ (-(2 * s + εInc))
          ≤ (4 * δn) ^ (-(2 * s + εInc)) := h1
        _ = (4 : ℝ)^(-(2 * s + εInc)) * δn ^ (-(2 * s + εInc)) := h2
        _ = (4 : ℝ)^(-(2 * s + εInc)) * (δn ^ (-(2 * s + netGain)) * δn ^ (netGain - εInc)) := by rw [h3]
        _ = δn ^ (-(2 * s + netGain)) * ((4 : ℝ)^(-(2 * s + εInc)) * δn ^ (netGain - εInc)) := by ring
        _ ≤ δn ^ (-(2 * s + netGain)) * (1 / (C_pack : ℝ)) := by gcongr
        _ = δn ^ (-(2 * s + netGain)) / (C_pack : ℝ) := by ring
      have h_pos1 : 0 ≤ δ ^ (-(2 * s + εInc)) := by positivity
      have hCpack_pos' : (0 : ℝ) < (C_pack : ℝ) := by
        have h : C_pack = 31730689 := FixedPackingBound.C_pack_eq
        rw [h] <;> norm_num
      have h_pos2 : 0 ≤ δn ^ (-(2 * s + netGain)) / (C_pack : ℝ) := by positivity
      have h_div : ENNReal.ofReal (δn ^ (-(2 * s + netGain)) / (C_pack : ℝ)) =
          ENNReal.ofReal (δn ^ (-(2 * s + netGain))) / (C_pack : ENNReal) := by
        convert ENNReal.ofReal_div_of_pos (x := δn ^ (-(2 * s + netGain))) (y := (C_pack : ℝ)) hCpack_pos'
        <;> simp
      calc ENNReal.ofReal (δ ^ (-(2 * s + εInc)))
        ≤ ENNReal.ofReal (δn ^ (-(2 * s + netGain)) / (C_pack : ℝ)) :=
          ENNReal.ofReal_le_ofReal h_main_real
      _ = ENNReal.ofReal (δn ^ (-(2 * s + netGain))) / (C_pack : ENNReal) := h_div

    -- Full-T0 geometry bounds for coarse branch
    have hm_T0 : ∀ T ∈ config_heavy.T₀, |T.slope| ≤ 1 := by
      intro T hT
      have h_strip : -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ) := h_tubes_strip' T hT
      exact full_T0_slope_bound (hn_pos := hn_pos) h_strip

    have hb_T0 : ∀ T ∈ config_heavy.T₀, |T.intercept| ≤ 3 := by
      intro T hT
      rcases h_T0_coverage T hT with ⟨p, hp, hT_family⟩
      have h_inter : (T.toSet ∩ p.toSet).Nonempty :=
        config_heavy.h_intersect p hp T hT_family
      have h_q_unit : 0 ≤ p.i ∧ p.i < (2 ^ n : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ n : ℤ) :=
        h_squares_unit' p hp
      have h_slope : |T.slope| ≤ 1 := hm_T0 T hT
      exact tube_intercept_bound_from_intersection (hn_pos := hn_pos) T p h_inter h_q_unit h_slope

    have hthick_T0 : ∀ (T : DTb n), T ∈ config_heavy.T₀ →
        ∃ (ℓ : AffineLine), ℓ ∈ originalFamily ∧
          dist (toAffineLine T) (RegularIncidence.S0_line ℓ) ≤ (15 / 2 : ℝ) * (δ / 4) := by
      intro T hT
      exact h_tube_provenance T (h_T0_sub hT)

    exact coarse_branch_from_b1_data
      (hn_pos := hn_pos) (hm_pos := by omega) (hnm := hnm)
      (data := data)
      (hs_pos := hs) (hs_lt_one := hs1) (hst := hst) (htu := hu_t)
      (hεA_pos := hεA_pos) (hεInc_pos := hεInc_pos) (hM_pos := hM_pos)
      (hδ_pos := hδ_pos)
      (h_even := h_even) (h_scale := h_scale) (h_scale2 := h_scale2)
      (Q := Q) (hQ := hQ)
      (hK_nat_bound := hK_nat_bound)
      (lambda := lambda) (rho_M := rho_M) (loss_B1 := loss_B1)
      (hloss_B1_pos := hloss_B1_pos) (hlambda_nonneg := by linarith [hlambda_pos]) (hrho_M_nonneg := by linarith [hrho_M_pos])
      (εReg := εReg) (fixedLoss := fixedLoss)
      (hεReg_nonneg := by linarith) (hfixedLoss_nonneg := by linarith)
      (hM_lower_frontend := hM_lower) (hselector_budget_M := hselector_budget_M)
      (hδn_small := hδn_small)
      (C_geo := (9 : ℝ)^(-(s + εA)) / (262144 : ℝ)^2) (hC_geo_pos := by positivity)
      (loss_parent := loss_parent) (h_loss_parent_nonneg := by linarith)
      (h_loss_parent_lt_εA := hloss_parent_lt_εA) (h_absorb_geo := h_absorb_geo)
      (h_coarse_bound_geo := h_coarse_bound_geo)
      (u0 := u0) (hu0_def := by rfl)
      (α_base := α_base) (α_actual := α_actual)
      (hα_base_def := by rfl) (hα_actual_def := by rfl)
      (C_prop5 := C_prop5) (hC_prop5_pos := hC_prop5_pos)
      (h_prop5 := h_prop5)
      (loss_coarse := loss_coarse) (hloss_coarse_nonneg := hloss_coarse_nonneg)
      (h_absorb_prop5 := h_absorb_prop5)
      (hloss_coarse_small := hloss_coarse_small)
      (hloss_coarse_le_half := hloss_coarse_le_half)
      (coarseGain_raw := coarseGain_raw) (localLoss := localLoss) (netGain := netGain)
      (h_coarseGain_raw_def := by rfl)
      (h_selector_budget := h_selector_budget)
      (h_netGain_pos := hnetGain_pos)
      (fineData := fineData)
      (hfine_count := hfine_count) (hfine_mult := hfine_mult) (hfine_loss := hfine_loss)
      (N₀ := config_heavy.T₀.card)
      (fineTubes := config_heavy.T₀)
      (h_fineTubes_card := by rfl)
      (h_raw_product := h_raw_product)
      (hm := hm_T0)
      (hb := hb_T0)
      (h_thick := hthick_T0)
      (h_absorb := h_absorb_coarse)

end DirecretisedFurstenbergEstimate

end
