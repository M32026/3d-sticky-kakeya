module

/-
# Incidence-to-Ring Contradiction Interface (V4)

This module defines the endgame lemma `incidence_to_ring_contradiction` with
the V4-native quantifier order: the Ring theorem conclusion is already specialized
to the current `δ` and a fixed `K_work`, avoiding the circular threshold problem.

The proof body integrates the full 6-helper pipeline: Phase 0 composition,
Kaufman energy + three-direction selection, projective normalization,
dense graph construction, BSG extraction, and the Ring theorem contradiction.

Supporting lemmas are in `IncidenceToRingContradiction.SupportingLemmas`.

## Whiteprint node

`incidence_to_ring_contradiction`
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeSetBasics
public import MyLeanRepo.SetDiscretizationBridge
public import MyLeanRepo.Lemma51Corollary
public import MyLeanRepo.Energy.AverageProjectionEnergy
public import MyLeanRepo.Energy.RegularSetHasBoundedEnergy
public import MyLeanRepo.ProductLikeIncidence.ProductLikeProof
public import MyLeanRepo.ProductLikeIncidence.Phase0.Phase0CompositionV3
public import MyLeanRepo.ProductLikeIncidence.Phase0.ProjectionBoundComplete
public import MyLeanRepo.ProductLikeIncidence.Phase0ThresholdWiring
public import MyLeanRepo.ProductLikeIncidence.Phase0Absorption
public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV3
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV4
public import MyLeanRepo.ProductLikeIncidence.V4NumericFills
public import MyLeanRepo.ProductLikeIncidence.ExtractionNumericConditions
public import MyLeanRepo.ProductLikeIncidence.DensityApplicationV4
public import MyLeanRepo.ProductLikeIncidence.KaufmanAbsorptionV3
public import MyLeanRepo.ProductLikeIncidence.ExactEndgameGeneralizedV3
public import MyLeanRepo.ProductLikeIncidence.Obligation3ProjectiveTransform
public import MyLeanRepo.ProductLikeIncidence.EnergyScaling
public import MyLeanRepo.ProductLikeIncidence.NormalizeAndExtract
public import MyLeanRepo.ProductLikeIncidence.ProductDensityFromThreefold
public import MyLeanRepo.ProductLikeIncidence.Phase3_4Integration
public import MyLeanRepo.ProductLikeIncidence.Phase56Integration
public import MyLeanRepo.ProductLikeIncidence.GridSeparatedCard
public import MyLeanRepo.ProductLikeIncidence.Phase7Budgets
public import MyLeanRepo.ProductLikeIncidence.Phase7FullIntegrationV2
public import MyLeanRepo.ProductLikeIncidence.Phase7ScaledProjections
public import MyLeanRepo.ProductLikeIncidence.Phase7ChartBounds
public import MyLeanRepo.ProductLikeIncidence.TranslationBounds
public import MyLeanRepo.ProductLikeIncidence.SimpleNormalize
public import MyLeanRepo.ProductLikeIncidence.NormalizeWithPopularity
public import MyLeanRepo.ProductLikeIncidence.ThickeningCovering
public import MyLeanRepo.ProductLikeIncidence.BoundedOccupancy
public import MyLeanRepo.ProductLikeIncidence.CardinalityLowerBound
public import MyLeanRepo.ProductLikeIncidence.K_A_Wrapper
public import MyLeanRepo.ProductLikeIncidence.PopularityThresholds
public import MyLeanRepo.ProductLikeIncidence.NormalizedSetTransfer
public import MyLeanRepo.ProductLikeIncidence.NormalizedSizeUpperBounds
public import MyLeanRepo.ProductLikeIncidence.CategoryBExtraction
public import MyLeanRepo.ProductLikeIncidence.MeasureSupportHelpers
public import MyLeanRepo.ProductLikeIncidence.GlueH3ToH4
public import MyLeanRepo.ProductLikeIncidence.Helper3ProjectiveNormalization
public import MyLeanRepo.ProductLikeIncidence.ProjectiveFBound
public import MyLeanRepo.ProductLikeIncidence.Helper4ToHelper5Bridges
public import MyLeanRepo.ProductLikeIncidence.AbsoluteCoordinateWiring
public import MyLeanRepo.ProductLikeIncidence.PbarProductUpper
public import MyLeanRepo.ProductLikeIncidence.Helper5AbsorptionCalibration
public import MyLeanRepo.ProductLikeIncidence.Helper4DenseGraph
public import MyLeanRepo.ProductLikeIncidence.Helper5BSGExtraction
public import MyLeanRepo.ProductLikeIncidence.GlueH5ToH6
public import MyLeanRepo.ProductLikeIncidence.Helper5UnifiedExponent
public import MyLeanRepo.ProductLikeIncidence.PbarSmallBridge
public import MyLeanRepo.ProductLikeIncidence.FactorAbsorbSimple
public import MyLeanRepo.ProductLikeIncidence.Helper6BridgeConditions
public import MyLeanRepo.ProductLikeIncidence.MassBudgetBridge
public import MyLeanRepo.ProductLikeIncidence.SPreShiftBridge
public import MyLeanRepo.ProductLikeIncidence.Helper6AbsorptionBridges
public import MyLeanRepo.ProductLikeIncidence.Helper6BudgetBridges
public import MyLeanRepo.ProductLikeIncidence.AbsorptionBudgetHelpers
public import MyLeanRepo.ProductLikeIncidence.PbarSmallNormalizedBridge
public import MyLeanRepo.ProductLikeIncidence.RawProjBoundNormalizedBridge
public import MyLeanRepo.ProductLikeIncidence.GraphAbsorbProof
public import MyLeanRepo.ProductLikeIncidence.ChartFullLambdaBoundBridge
public import MyLeanRepo.ProductLikeIncidence.MultOrigBridge
public import MyLeanRepo.ProductLikeIncidence.BudgetNonNegativity
public import MyLeanRepo.ProductLikeIncidence.SymmetryBridge

public import MyLeanRepo.ProductLikeIncidence.IncidenceToRingContradiction.SupportingLemmas

public import MyLeanRepo.OSWPrelude

@[expose] public section

set_option maxHeartbeats 10000000

noncomputable section

open Set Bornology ENNReal MeasureTheory

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- **Incidence-to-Ring contradiction (V4 interface)**

Given all incidence data AND a Ring theorem conclusion already specialized to
the current `δ` (with fixed `K_work`), derive `False`.

This lemma packages the entire unproved endgame:
1. Kaufman energy averaging → projected measures ν₁, ν₂, ν₃
2. Energy-to-Frostman extraction → A_cells^(i) (unions of δ-cells) with
   νᵢ(A_cells^(i)) ≥ 3/4, and (δ, κ0, K_work·δ^(-εnc))-set structure
3. Dense graph from shared parameter cubes, restricted to A_cells membership
4. Three-direction projective normalization + BSG → subsets with controlled doubling
5. Frostman measure construction on extracted δ-sets
6. Ring theorem → additive/multiplicative expansion
7. Lemma 5.1 → contradiction with small P

The `h_ring_spec` parameter is the Ring theorem conclusion AFTER
instantiating `K_work` and `δ ≤ δ₀_ring`. This avoids the circular threshold
problem.

The V4 budget parameters and conditions come from `exists_budgetV4` and
outer δ₀ thresholds. -/

lemma incidence_to_ring_contradiction
    {δ s τ κ0 η η_work ε L_exp p_projective C C_work K_ring K_diff εnc εgain rho_sel rho_sep : ℝ}
    (hδ_pos : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales) (hδ_le_one : δ ≤ 1)
    (hs_pos : 0 < s) (hs_lt_one : s < 1) (hτ_pos : 0 < τ)
    (hkappa_pos : 0 < κ0) (hkappa_lt_s : κ0 < s) (h2kappa_lt_tau : 2 * κ0 < τ)
    (hη_pos : 0 < η)
    (hη_work_pos : 0 < η_work)
    (hη_lt_work : η < η_work)
    (hε_pos : 0 < ε)
    (h10ε_lt_η_work : 10 * ε < η_work)
    (h5η_work_lt : 5 * η_work < 2 * (s - κ0))
    (h4η_work_lt_tau : 4 * η_work < τ)
    (hη_work_eq_two : η_work = 2 * η)
    (hL_exp_pos : 0 < L_exp)
    (hL_exp_eq_seven : L_exp = 7)
    (hη_work_le_kappa0 : η_work ≤ κ0)
    (hp_ge_10 : 10 ≤ p_projective)
    (hC_ge1 : 1 ≤ C)
    (hC_le_target : C ≤ δ ^ (-η))
    (hC_work_eq : C_work = 35 * C)
    (hC_work_ge1 : 1 ≤ C_work)
    (hC_work_le : C_work ≤ δ ^ (-η_work))
    (hK_ring_ge1 : 1 ≤ K_ring)
    (hK_diff_pos : 0 < K_diff)
    (hK_diff_le : K_diff ≤ δ ^ (-qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep))
    (h_budget : εgain > qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep)
    (h_frostman_gap : 2 * η_work < τ * rho_sep)
    (hG_eta_work_le : gapCoefficientV4 L_exp κ0 p_projective τ * η_work ≤ εnc / 2)
    (h_qTotal_le_enc : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤ εnc)
    (h_proj_absorb : (126 : ℝ) * Real.sqrt 98 * (35 : ℝ)^2 ≤ δ ^ (-η))
    -- Exact endgame numeric conditions (from outer δ₀ thresholds):
    (c_sel : ℝ)
    (hc_sel_pos : 0 < c_sel)
    (hδ_rho_sel_le_c_sel2 : δ ^ rho_sel ≤ c_sel / 2)
    (hδ_rho_sel_le_c_sel8 : δ ^ rho_sel ≤ c_sel / 8)
    (h_small_neighborhood : 2 * (3 * C * 2 ^ τ) * (δ ^ rho_sep) ^ τ ≤ c_sel / 8)
    (h_dir_64 : δ ^ (εgain - qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep) ≤ 1 / 64)
    (hc_sel_eq : c_sel = cPhase0 δ η (35 * C) / 2)
    (h_pbar_98 : (98 : ℝ) ≤ δ ^ (-(2 * s - 2 * κ0 - 5 * η_work)))
    (h_extract_128 : (128 : ℝ) ≤ δ ^ (-κ0))
    (h_box_bound : (2 ^ 20 : ℝ) ≤ δ ^ (-(η_work / 100)))
    -- rho_sel default equality (needed for lossy coordinate lower budget)
    (hrho_sel_eq : rho_sel = rhoSelDefault η_work)
    -- rho_sep upper bound (comes from rhoSepDefault η_work κ0 = η_work / κ0)
    (hrho_sep_le : rho_sep ≤ η_work / κ0)
    -- Phase0 plan constant absorption threshold
    (h_plan_absorb : planConstant s κ0 ≤ δ ^ (-(qPlan η_work - 5 * η_work)))
    -- Phase0 Kaufman constant absorption threshold
    (h_Kauf_absorb : kaufmanConstant τ κ0 ≤ δ ^ (-(51 * η_work / 100)))
    -- V4 KBSG constant absorption threshold
    (h_KBSG_absorb : (81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80 ≤ δ ^ (-(qAbsorb η_work)))
    -- Phase0 box constant absorption threshold
    (hδ_box_small : δ ^ (-(qBox η_work τ)) ≥ 8 * (1 + (1 + 12 * δ) *
        ((6 * (35 * C) * 2 ^ τ) /
         (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2))) ^ (1 / τ) + 6 * δ))
    -- V4 terminal regularity budget
    (h_small_bsg : η_work ≤ εnc / (2 * bsgOverheadCoefficientV4 L_exp κ0 p_projective))
    -- V4 extraction gap budget
    (h_qTotalV4_le_enc4 : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤ εnc / 4)
    (h_qbox_lt_one : qBox η_work τ < 1)
    -- Sumset constant absorption (outer δ₀ threshold)
    (h_sumset_absorb : (3 : ℝ) * Real.sqrt 2 ≤
        δ ^ (-(qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep -
                 (L_exp * η + (qMassV4 η_work rho_sep + 3 * rho_sel) / 2))))
    -- Extraction log absorption (outer δ₀ threshold)
    (h_extract_log_absorb : extractLogAbsorbHyp δ εnc η_work τ κ0 (qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep))
    -- c_dense calibration: density exponent ≤ q_K (for hc_dense_ge)
    (h_c_dense_exp_le : 3 * rho_sel + 2 * rho_sep + qAbsorb η_work + L_exp * η_work ≤ qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep)
    {Y : Set ℝ} {X : ℝ → Set ℝ} {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hY_sub : Y ⊆ productLikeUnitGrid δ)
    (hY_delta : IsProductLikeRealDeltaSCSet δ τ C Y)
    (hXy_delta : ∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ ∧
      IsProductLikeRealDeltaSCSet δ s C (X y))
    (hP_bdd : Bornology.IsBounded P)
    (h_fiber : ∀ z ∈ productLikeIncidenceSet Y X,
      ∃ (Pz : Set (EuclideanSpace ℝ (Fin 2))),
        Pz ⊆ P ∧ IsDeltaSCSet δ s C Pz ∧
          ∀ p ∈ Pz, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ)
    (hP_small : ENat.toENNReal (dyadicCoveringNumber δ P) <
      ENNReal.ofReal (δ ^ (-(2 * s + η))))
    {Zf : Finset (EuclideanSpace ℝ (Fin 2))}
    {Pz : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2))}
    {P_cubes_fin : Finset (Set (EuclideanSpace ℝ (Fin 2)))}
    (hZf : (Zf : Set _) = productLikeIncidenceSet Y X)
    (hPz : ∀ z ∈ Zf, Pz z ⊆ P ∧ IsDeltaSCSet δ s C (Pz z) ∧
      ∀ p ∈ Pz z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ)
    (hP_cubes : (P_cubes_fin : Set _) = dyadicCubesMeeting δ P)
    (h_energy : ENNReal.ofReal (C⁻¹ ^ 6 * δ ^ (-(2 * τ + 2 * s - η))) ≤
      ∑ Q ∈ P_cubes_fin,
        ((Zf.filter (fun z => (Pz z ∩ Q).Nonempty)).card : ENNReal) ^ 2)
    -- Ring theorem conclusion ALREADY SPECIALIZED to current δ and K_ring:
    (h_ring_spec :
      ∀ (A : Set ℝ) (μ : Measure ℝ),
        A ⊆ Set.Icc 1 2 →
        IsProductLikeRealDeltaSCSet δ κ0 (K_ring * δ ^ (-εnc)) A →
        Nreal δ A ≤ ENNReal.ofReal (K_ring * δ ^ (-(s + εnc))) →
        IsDirectionFrostman δ κ0 (K_ring * δ ^ (-εnc)) μ →
        ∃ x ∈ μ.support,
          ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ A ≤
            Nreal δ (Set.image2 (fun a b => a + x * b) A A)) :
    False := by
  -- =====================================================================
  -- Step 1: Helper 1 — Phase 0 result extraction
  -- =====================================================================
  -- Calls phase0_composition_v3 to obtain Tbar, Pbar_param, T_y_points,
  -- bounding box R, and all Phase 0 regularity/size properties.

  have hδ_lt_one : δ < 1 := by
    exact hδ_le_one.lt_of_ne (fun h => by
      rw [h] at h_pbar_98
      norm_num at h_pbar_98 <;> linarith)

  have hY_fin : Y.Finite := by
    exact (productLikeUnitGrid_finite hδ_pos).subset hY_sub

  have hY_nonempty : Y.Nonempty := by
    have h_re_nonempty : (productLikeRealLineCopy Y).Nonempty := hY_delta.2.1
    rcases h_re_nonempty with ⟨x, hx⟩
    have h_x0_in_Y : x 0 ∈ Y := hx
    exact ⟨x 0, h_x0_in_Y⟩

  -- =====================================================================
  -- Step 2: Call H1_to_H2_full (composes Helper1 → glue → Helper2)
  -- Output: Pbar_param, R, k_R, ν, E, μE, θ1/θ2/θ3, E1/E2/E3, E3fin, μE3
  -- =====================================================================
  rcases H1_to_H2_full
    (hδ_pos := hδ_pos) (hδ_dyadic := hδ_dyadic) (hδ_le_one := hδ_le_one)
    (hs_pos := hs_pos) (hs_lt_one := hs_lt_one) (hτ_pos := hτ_pos)
    (hkappa_pos := hkappa_pos) (hkappa_lt_s := hkappa_lt_s) (h2kappa_lt_tau := h2kappa_lt_tau)
    (hη_pos := hη_pos) (hη_work_pos := hη_work_pos) (hη_work_eq_two := hη_work_eq_two)
    (hε_pos := hε_pos)
    (hL_exp_pos := hL_exp_pos) (hL_exp_eq_seven := hL_exp_eq_seven)
    (hη_work_le_kappa0 := hη_work_le_kappa0) (hp_ge_10 := hp_ge_10)
    (h5η_work_lt := h5η_work_lt) (h4η_work_lt_tau := h4η_work_lt_tau)
    (hC_ge1 := hC_ge1) (hC_le_target := hC_le_target)
    (hC_work_eq := hC_work_eq) (hC_work_ge1 := hC_work_ge1) (hC_work_le := hC_work_le)
    (hK_ring_ge1 := hK_ring_ge1)
    (hrho_sel_eq := hrho_sel_eq) (hrho_sep_le := hrho_sep_le)
    (h_frostman_gap := h_frostman_gap)
    (hG_eta_work_le := hG_eta_work_le) (h_qTotalV4_le_enc4 := h_qTotalV4_le_enc4)
    (c_sel := c_sel) (hc_sel_pos := hc_sel_pos) (hc_sel_eq := hc_sel_eq)
    (hδ_rho_sel_le_c_sel2 := hδ_rho_sel_le_c_sel2)
    (hδ_rho_sel_le_c_sel8 := hδ_rho_sel_le_c_sel8)
    (h_small_neighborhood := h_small_neighborhood)
    (h_plan_absorb := h_plan_absorb) (h_Kauf_absorb := h_Kauf_absorb)
    (h_box_bound := h_box_bound) (h_proj_absorb := h_proj_absorb)
    (h_pbar_98 := h_pbar_98) (hδ_box_small := hδ_box_small)
    (h_qbox_lt_one := h_qbox_lt_one) (h_extract_log_absorb := h_extract_log_absorb)
    (hY_sub := hY_sub) (hY_delta := hY_delta) (hXy_delta := hXy_delta)
    (hZf := hZf) (hPz := hPz) (hP_small := hP_small)
  with ⟨Pbar_param, C_Pbar2, q_bad2, R, k_R, ν, E, μE, θ1, θ2, θ3, E1, E2, E3, E3fin, μE3, T_y_points, c_mult,
    hT_y_points_sub, hPbar_lower_strong,
    h_dir_frostman, hν_support_eq, hν_support_sub, hν_point_mass,
    hE_nonempty, hμE_prob, hμE_support_sub, hμE_eq, hμE_energy,
    hE_card_eq, hE_unique_per_cube,
    hE3_sub_E2, hE2_sub_E1, hE1_sub_E, hE3_nonempty,
    hE1_size, hE2_size, hE3_size, hE3_size3,
    hμE3_prob, hμE3_support, hE3fin_eq, hμE3_eq,
    hE3_energy_ratio, hE3_energy_abs,
    h_sep12, h_sep13, h_sep23,
    hθ1_lt_θ3, hθ3_lt_θ2,
    hθ1_in_Icc, hθ2_in_Icc, hθ3_in_Icc,
    hE_energy_dirs, hE3_Nreal_dirs,
    h_coord_energy0, h_coord_energy1,
    hq_bad2_eq,
    hR_eq_pow2, hR_ge1, hPbar_Rbox, h4R_le_qbox, hE3_sub_Pbar,
    hPbar_small_coeff1, h_raw_proj_bound, hc_mult_eq2, h_multiplicity
  ⟩

  -- Clear Helper1-specific hypotheses no longer needed
  clear hZf hPz hP_small hXy_delta

  -- =====================================================================
  -- Step 3: Helper 3 — Projective normalization
  -- =====================================================================

  -- Reconstruct E3 ⊆ E from the chain
  have hE3_sub_E : E3 ⊆ E :=
    subset_trans hE3_sub_E2 (subset_trans hE2_sub_E1 hE1_sub_E)

  -- Directed separation from absolute separation + ordering
  have h_dir_sep13 : θ3 - θ1 ≥ δ ^ rho_sep := by
    have h : |θ1 - θ3| = θ3 - θ1 := by
      have h' : θ1 - θ3 < 0 := by linarith
      rw [abs_of_neg h'] <;> linarith
    rw [h] at h_sep13
    exact h_sep13
  have h_dir_sep32 : θ2 - θ3 ≥ δ ^ rho_sep := by
    have h : |θ2 - θ3| = θ2 - θ3 := by
      have h' : θ2 - θ3 > 0 := by linarith
      rw [abs_of_pos h']
    rw [h] at h_sep23
    exact h_sep23

  -- κ0 ≤ 1
  have hκ0_le_one : κ0 ≤ 1 := by linarith [hs_lt_one, hkappa_lt_s]

  -- δ^κ0 ≤ 1/128 from h_extract_128
  have hδ_kappa_small : δ ^ κ0 ≤ 1 / 128 := by
    have h1 : (128 : ℝ) ≤ δ ^ (-κ0) := h_extract_128
    have h2 : δ ^ (-κ0) = (δ ^ κ0)⁻¹ := by
      rw [Real.rpow_neg hδ_pos.le] <;> ring
    rw [h2] at h1
    have h3 : 0 < δ ^ κ0 := by positivity
    have h4 : δ ^ κ0 ≤ (128 : ℝ)⁻¹ := by
      have h5 : 128 * δ ^ κ0 ≤ 1 := by
        have h6 : 0 < δ ^ κ0 := h3
        have h7 : 128 * δ ^ κ0 ≤ (δ ^ κ0)⁻¹ * δ ^ κ0 := by
          exact mul_le_mul_of_nonneg_right h1 h6.le
        have h8 : (δ ^ κ0)⁻¹ * δ ^ κ0 = 1 := by
          field_simp [h6.ne'] <;> ring
        rw [h8] at h7
        exact h7
      have h9 : δ ^ κ0 ≤ 1 / 128 := by linarith
      simpa using h9
    simpa using h4

  -- Define energy exponents
  let q_norm_energy : ℝ := qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep
  let q_coord_energy : ℝ := q_norm_energy - qEnergy η_work τ κ0

  have h_eq_norm : q_norm_energy = q_coord_energy + qEnergy η_work τ κ0 := by
    dsimp only [q_norm_energy, q_coord_energy] <;> ring
  have h_qnorm_eq : q_norm_energy = qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by rfl

  -- Positivity derivations
  have hεnc_pos : 0 < εnc := by
    have h1 : 0 < gapCoefficientV4 L_exp κ0 p_projective τ := by
      dsimp only [gapCoefficientV4] <;> positivity
    have h2 : 0 < gapCoefficientV4 L_exp κ0 p_projective τ * η_work := mul_pos h1 hη_work_pos
    have h3 : gapCoefficientV4 L_exp κ0 p_projective τ * η_work ≤ εnc / 2 := hG_eta_work_le
    have h4 : 0 < εnc / 2 := lt_of_lt_of_le h2 h3
    linarith only [h4]
  have hrho_sel_pos : 0 < rho_sel := by
    rw [hrho_sel_eq]
    dsimp only [rhoSelDefault, qAbsorb] <;> positivity
  have hrho_sel_nonneg : 0 ≤ rho_sel := le_of_lt hrho_sel_pos
  have hrho_sep_pos : 0 < rho_sep := by
    have h1 : 0 < τ * rho_sep := by linarith [h_frostman_gap, hη_work_pos]
    exact (mul_pos_iff_of_pos_left hτ_pos).mp h1
  have hrho_sep_nonneg : 0 ≤ rho_sep := le_of_lt hrho_sep_pos
  have hq_box_pos : 0 < qBox η_work τ := by
    dsimp only [qBox, qAbsorb] <;> positivity
  have h_qcoord_pos : 0 < q_coord_energy := by
    have h_eq : q_coord_energy = qCoordEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by
      simp [q_coord_energy, q_norm_energy, qNormEnergyV3, qCoordEnergyV3] <;> ring
    rw [h_eq]
    dsimp only [qCoordEnergyV3, rhoExc, qKaufBase, qPlan, qKaufman, qAbsorb, qBox]
    <;> positivity
  have h_qnorm_pos : 0 < q_norm_energy := by
    have h_eq : q_norm_energy = qCoordEnergyV3 η_work ε τ κ0 rho_sel rho_sep + qEnergy η_work τ κ0 := by
      simp [q_norm_energy, qNormEnergyV3] <;> ring
    rw [h_eq]
    have h_eq2 : q_coord_energy = qCoordEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by
      simp [q_coord_energy, q_norm_energy, qNormEnergyV3, qCoordEnergyV3] <;> ring
    have h1 : 0 < qCoordEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by
      rw [←h_eq2]; exact h_qcoord_pos
    have h2 : 0 < qEnergy η_work τ κ0 := by
      dsimp only [qEnergy] <;> positivity
    linarith only [h1, h2]

  -- h_exp_le: q_bad2 + 6*rho_sel + 2*κ0*rho_sep ≤ q_coord_energy
  -- q_coord_energy = rhoExc + 6*rho_sel + 2*κ0*rho_sep, and q_bad2 = rhoExc by hq_bad2_eq.
  have h_exp_le : q_bad2 + 6 * rho_sel + 2 * κ0 * rho_sep ≤ q_coord_energy := by
    have h1 : q_coord_energy = qCoordEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by
      simp [q_coord_energy, q_norm_energy, qNormEnergyV3, qCoordEnergyV3] <;> ring
    rw [h1]
    have h2 : qCoordEnergyV3 η_work ε τ κ0 rho_sel rho_sep =
        rhoExc η_work ε τ κ0 rho_sel + 6 * rho_sel + 2 * κ0 * rho_sep := by
      rfl
    rw [h2, hq_bad2_eq] <;> linarith

  -- Bridge H2→H3
  rcases bridge_H2_to_H3_stub
    (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
    (hL_nonneg := by linarith [hL_exp_pos])
    (hη_work_pos := hη_work_pos) (hε_pos := hε_pos)
    (hεnc_pos := hεnc_pos) (hκ_pos := hkappa_pos) (hκ_le_one := hκ0_le_one)
    (hp_nonneg := by linarith [hp_ge_10]) (hτ_pos := hτ_pos)
    (hrho_sel_nonneg := hrho_sel_nonneg) (hrho_sep_nonneg := hrho_sep_nonneg)
    (hR_ge1 := hR_ge1)
    (h4R_le_qbox := h4R_le_qbox)
    (h_qTotalV4_le_enc4 := h_qTotalV4_le_enc4)
    (h_qbox_lt_one := h_qbox_lt_one)
    (hK_ring_ge1 := hK_ring_ge1)
    (h_eq_norm := h_eq_norm) (h_qnorm_eq := h_qnorm_eq)
    (h_norm_pos := h_qnorm_pos)
    (h_extract_log_absorb := h_extract_log_absorb)
  with ⟨hC_energy_pos, hC_extract_pos, h_energy_absorb, hC_extract_large⟩

  let C_energy : ℝ := (4 * R) ^ (2 * κ0)
  let C_extract : ℝ := K_ring * δ ^ (-εnc / 2)
  have hC_extract_def : C_extract = K_ring * δ ^ (-εnc / 2) := by rfl

  -- Dummy fiber sets
  let P_y : ℝ → Set (EuclideanSpace ℝ (Fin 2)) := fun _ => ∅
  have hP_y_bdd : ∀ y, Bornology.IsBounded (P_y y) := by
    intro y
    have h : P_y y = (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
      rfl
    rw [h]
    exact isBounded_empty

  -- hPbar_bounded: follows from hPbar_Rbox (rectangle [-R,R]^2 is bounded).
  have hPbar_bounded : Bornology.IsBounded Pbar_param := by
    have hR_nonneg : 0 ≤ R := by linarith only [hR_ge1]
    let S : Set (EuclideanSpace ℝ (Fin 2)) := {p | ∀ i : Fin 2, p i ∈ Set.Icc (-R) R}
    have h_rect_bdd : Bornology.IsBounded S := bounded_coordinate_rectangle hR_nonneg
    have h_sub : Pbar_param ⊆ S := hPbar_Rbox
    exact h_rect_bdd.subset h_sub

  -- hPbar_Rbox' in Helper3 format: ∀ p ∈ Pbar_param, |p 0| ≤ R ∧ |p 1| ≤ R
  have hPbar_Rbox' : ∀ p ∈ Pbar_param, |p 0| ≤ R ∧ |p 1| ≤ R := by
    intro p hp
    have h1 : p ∈ {p : EuclideanSpace ℝ (Fin 2) | ∀ i, p i ∈ Set.Icc (-R) R} := hPbar_Rbox hp
    have h2 : ∀ i : Fin 2, p i ∈ Set.Icc (-R) R := h1
    have h0 : p 0 ∈ Set.Icc (-R) R := h2 0
    have h1' : p 1 ∈ Set.Icc (-R) R := h2 1
    exact ⟨abs_le.mpr ⟨h0.1, h0.2⟩, abs_le.mpr ⟨h1'.1, h1'.2⟩⟩

  -- hE3_sub_Pbar: from H1_to_H2_full output (E3 lives under Pbar_param)
  -- (already destructured from h_step2_all above)

  -- Call Helper3 (production)
  rcases projective_normalization_helper
    (hδ_pos := hδ_pos) (hδ_dyadic := hδ_dyadic) (hδ_le_one := hδ_le_one) (hδ_lt_one := hδ_lt_one)
    (hκ0_pos := hkappa_pos) (hκ0_le_one := hκ0_le_one)
    (θ1 := θ1) (θ2 := θ2) (θ3 := θ3)
    (hθ1_lt_θ3 := hθ1_lt_θ3) (hθ3_lt_θ2 := hθ3_lt_θ2)
    (hθ1_in_Icc := hθ1_in_Icc) (hθ2_in_Icc := hθ2_in_Icc) (hθ3_in_Icc := hθ3_in_Icc)
    (h_dir_sep13 := h_dir_sep13) (h_dir_sep32 := h_dir_sep32)
    (E3 := E3) (μE3 := μE3)
    (hμE3_prob := hμE3_prob) (hE3_nonempty := hE3_nonempty) (hμE3_support := hμE3_support)
    (Pbar_param := Pbar_param)
    (hPbar_bounded := hPbar_bounded) (hE3_sub_Pbar := hE3_sub_Pbar)
    (R := R) (k_R := k_R)
    (hR_eq_pow2 := hR_eq_pow2) (hR_ge1 := hR_ge1)
    (hPbar_Rbox := hPbar_Rbox')
    (P_y := P_y) (hP_y_bdd := hP_y_bdd)
    (Y := Y) (hY_fin := hY_fin) (hY_nonempty := hY_nonempty)
    (q_bad := q_bad2) (q_coord_energy := q_coord_energy) (q_norm_energy := q_norm_energy) (rho_sel := rho_sel)
    (h_qcoord_pos := h_qcoord_pos) (h_qnorm_pos := h_qnorm_pos)
    (h_coord_energy0 := h_coord_energy0) (h_coord_energy1 := h_coord_energy1)
    (h_exp_le := h_exp_le)
    (C_energy := C_energy) (C_extract := C_extract)
    (hC_energy_pos := hC_energy_pos) (hC_energy_large := by rfl) (hC_extract_pos := hC_extract_pos)
    (hδ_kappa_small := hδ_kappa_small)
    (h_energy_absorb := h_energy_absorb) (hC_extract_large := hC_extract_large)
  with ⟨F, F_inv, x, E3', μE3', P_y', L_proj, C_inv, round_fun, S1, S2, E3'', h_step3_all⟩

  -- Decompose Helper3 output conjunction (31 components)
  rcases h_step3_all with ⟨
    hF_formula, hF_inv1, hF_inv2, hE3'_eq, hμE3'_eq, hμE3'_prob3,
    hμE3'_support, hE3'_nonempty3, hP_y'_eq, hx_eq, h_affine_proj,
    hL_proj_nonneg, hF_lip, hC_inv_nonneg, hC_inv_bound, hF_inv_lip,
    h_round_near, hround_grid,
    hS1_grid, hS2_grid, hS1_sep, hS2_sep,
    hS1_sub_round, hS2_sub_round,
    hS1_delta, hS2_delta,
    hS1_finite, hS2_finite, hS1_nonempty, hS2_nonempty,
    hE3''_sub, hE3''_mass, hE3''_round
  ⟩

  -- Clear Helper3-specific hypotheses no longer needed
  clear h_small_neighborhood h_plan_absorb h_Kauf_absorb h_pbar_98 hδ_box_small h_extract_log_absorb hC_extract_large h_energy_absorb

  -- =====================================================================
  -- Bridge H3→H4: occupancy, projection bounds, size bounds via glue_H3_to_H4
  -- =====================================================================

  -- c_dense and hδ_small_absorb needed by both glue_H3_to_H4 and Helper4
  let c_dense : ENNReal := ENNReal.ofReal (δ ^ (3 * rho_sel + 2 * rho_sep + qAbsorb η_work + L_exp * η_work))
  have hc_dense_eq : c_dense = ENNReal.ofReal (δ ^ (3 * rho_sel + 2 * rho_sep + qAbsorb η_work + L_exp * η_work)) := by rfl
  have hδ_small_absorb : δ ^ qAbsorb η_work ≤ 1 / (2 * 1024 * 6 * 6) := by
    have h1 : δ ^ (-(qAbsorb η_work)) = (δ ^ qAbsorb η_work)⁻¹ := by
      rw [Real.rpow_neg hδ_pos.le] <;> ring
    rw [h1] at h_KBSG_absorb
    have h_pos : 0 < δ ^ qAbsorb η_work := by positivity
    have h2 : δ ^ qAbsorb η_work ≤ 1 / ((81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80) := by
      have h3 : (81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80 ≤ (δ ^ qAbsorb η_work)⁻¹ := h_KBSG_absorb
      have h4 : (81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80 > 0 := by positivity
      calc
        δ ^ qAbsorb η_work
          = 1 / (δ ^ qAbsorb η_work)⁻¹ := by field_simp [h_pos.ne'] <;> ring
        _ ≤ 1 / ((81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80) := by
          gcongr
    have h5 : (81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80 ≥ 2 * 1024 * 6 * 6 := by norm_num
    have h6 : 1 / ((81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80) ≤ 1 / (2 * 1024 * 6 * 6) := by
      gcongr
    exact le_trans h2 h6

  -- E3 size bound: E3.encard ≥ δ^{3ρ_sel} * Nplane(Pbar_param)
  have hE3_size_glue : ENat.toENNReal E3.encard ≥
      ENNReal.ofReal (δ ^ (3 * rho_sel)) * Nplane δ Pbar_param := by
    rw [hE_card_eq] at hE3_size3
    exact hE3_size3

  -- Direction projection bounds for θ1, θ2, θ3
  have h_proj_θ1 : Nreal δ (affineProjection θ1 E3) ≤
      ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) :=
    hE3_Nreal_dirs θ1 (by simp)
  have h_proj_θ2 : Nreal δ (affineProjection θ2 E3) ≤
      ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) :=
    hE3_Nreal_dirs θ2 (by simp)
  have h_proj_θ3 : Nreal δ (affineProjection θ3 E3) ≤
      ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) :=
    hE3_Nreal_dirs θ3 (by simp)

  -- Occupancy: (E3 ∩ Q).encard ≤ 1 for every dyadic cube Q
  have hE3_occupancy : ∀ Q ∈ dyadicCubes 2 δ, (E3 ∩ Q).encard ≤ 1 := by
    intro Q hQ
    by_cases hQmeet : (Q ∩ Pbar_param).Nonempty
    · have hQ' : Q ∈ dyadicCubesMeeting δ Pbar_param := ⟨hQ, hQmeet⟩
      rcases hE_unique_per_cube Q hQ' with ⟨p, hp, huniq⟩
      have h_sub : E3 ∩ Q ⊆ {p} := by
        intro x hx
        have hx1 : x ∈ E3 := hx.1
        have hx2 : x ∈ Q := hx.2
        have hx3 : x ∈ E := hE3_sub_E hx1
        have hx4 : x ∈ Pbar_param := hE3_sub_Pbar hx1
        exact huniq x ⟨hx3, hx2, hx4⟩
      have h : (E3 ∩ Q).encard ≤ ({p} : Set _).encard := Set.encard_mono h_sub
      rw [Set.encard_singleton] at h
      exact h
    · have h2 : (Q ∩ Pbar_param) = ∅ := Set.not_nonempty_iff_eq_empty.mp hQmeet
      have h1 : E3 ∩ Q ⊆ Q ∩ Pbar_param := by
        intro x hx
        exact ⟨hx.2, hE3_sub_Pbar hx.1⟩
      have h3 : E3 ∩ Q ⊆ (∅ : Set _) := by
        rw [h2] at h1
        exact h1
      have h_empty : E3 ∩ Q = ∅ := by simpa using h3
      rw [h_empty]
      rw [Set.encard_empty]
      <;> norm_num

  -- Uniform measure on E3
  have hμE3_uniform : μE3 = ∑ p ∈ E3fin,
      (1 / ENat.toENNReal E3.encard) • Measure.dirac p := hμE3_eq

  -- Call production glue_H3_to_H4
  rcases glue_H3_to_H4
    (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one) (hδ_dyadic := hδ_dyadic)
    (hη_pos := hη_pos) (hη_work_pos := hη_work_pos) (hη_work_eq_two := hη_work_eq_two)
    (hL_exp_pos := hL_exp_pos)
    (hrho_sel_pos := hrho_sel_pos) (hrho_sep_pos := hrho_sep_pos)
    (c_dense := c_dense) (hc_dense_eq := hc_dense_eq)
    (hδ_small_absorb := hδ_small_absorb)
    (Pbar_param := Pbar_param) (hPbar_bounded := hPbar_bounded)
    (E3 := E3) (E3fin := E3fin) (hE3fin_eq := hE3fin_eq)
    (hE3_nonempty := hE3_nonempty) (hE3_sub_Pbar := hE3_sub_Pbar)
    (hE3_size := hE3_size_glue)
    (θ1 := θ1) (θ2 := θ2) (θ3 := θ3)
    (hθ1_lt_θ3 := hθ1_lt_θ3) (hθ3_lt_θ2 := hθ3_lt_θ2)
    (hθ1_in_Icc := hθ1_in_Icc) (hθ2_in_Icc := hθ2_in_Icc) (hθ3_in_Icc := hθ3_in_Icc)
    (h_proj_θ2 := h_proj_θ2) (h_proj_θ1 := h_proj_θ1) (h_proj_θ3 := h_proj_θ3)
    (hE3_occupancy := hE3_occupancy)
    (μE3 := μE3) (hμE3_prob := hμE3_prob) (hμE3_uniform := hμE3_uniform)
    (F := F) (F_inv := F_inv)
    (hF_formula := hF_formula) (hF_inv1 := hF_inv1)
    (E3' := E3') (hE3'_eq := hE3'_eq)
    (μE3' := μE3') (hμE3'_eq := hμE3'_eq)
    (hμE3'_prob := hμE3'_prob3)
    (hE3'_nonempty := hE3'_nonempty3)
    (L_proj := L_proj) (C_inv := C_inv)
    (hL_proj_nonneg := hL_proj_nonneg) (hF_lip := hF_lip)
    (hC_inv_nonneg := hC_inv_nonneg) (hC_inv_le := hC_inv_bound) (hF_inv_lip := hF_inv_lip)
    (round_fun := round_fun) (h_round_near := h_round_near) (hround_grid := hround_grid)
    (S1 := S1) (S2 := S2)
    (hS1_grid := hS1_grid) (hS2_grid := hS2_grid)
    (hS1_sep := hS1_sep) (hS2_sep := hS2_sep)
    (hS1_sub_img := hS1_sub_round) (hS2_sub_img := hS2_sub_round)
    (hS1_delta := hS1_delta) (hS2_delta := hS2_delta)
    (hS1_finite := hS1_finite) (hS2_finite := hS2_finite)
    (hS1_nonempty := hS1_nonempty) (hS2_nonempty := hS2_nonempty)
    (E3'' := E3'') (hE3''_sub := hE3''_sub)
    (hE3''_mass := hE3''_mass) (hE3''_round := hE3''_round)
  with ⟨Pbar4, M_G_real, hPbar_param_sub_Pbar4, hE3'_sub_Pbar4, hPbar4_bounded, hPbar4_fin,
    hE3'_finite, hE3'_size4, hE3''_sub4, hE3''_half_encard4,
    hM_G_real_pos, hM_G_real_bound, h_occupancy4,
    h_proj_x4, h_proj_y4, hS1_bound4, hS2_bound4, h_third_proj4, h_third_proj_param4⟩

  -- Bridge inputs (now from glue_H3_to_H4)
  have hE3'_finite : E3'.Finite := hE3'_finite
  have hE3'_sub_Pbar : E3' ⊆ Pbar4 := hE3'_sub_Pbar4
  have hE3'_size : ENat.toENNReal E3'.encard ≥
      ENNReal.ofReal (δ ^ (3 * rho_sel)) * ENat.toENNReal (dyadicCoveringNumber δ Pbar_param) :=
    hE3'_size4
  have hE3''_half_encard : ENat.toENNReal E3''.encard ≥ ENat.toENNReal E3'.encard / 2 :=
    hE3''_half_encard4
  have h_occupancy : ∀ Q, Q ∈ dyadicCubes 2 δ →
      ENat.toENNReal (E3' ∩ Q).encard ≤ ENNReal.ofReal (1024 * δ ^ (-2 * rho_sep)) := by
    intro Q hQ
    have h1 : ENat.toENNReal (E3' ∩ Q).encard ≤ ENNReal.ofReal M_G_real := h_occupancy4 Q hQ
    have h2 : M_G_real ≤ 1024 * δ ^ (-2 * rho_sep) := hM_G_real_bound
    exact h1.trans (ENNReal.ofReal_le_ofReal h2)
  have h_proj_x : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0) E3') ≤
      (2 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar_param)).toReal)) :=
    h_proj_x4
  have h_proj_y : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 1) E3') ≤
      (2 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar_param)).toReal)) :=
    h_proj_y4
  have hS1_bound : Nreal δ S1 ≤ (3 : ENNReal) * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0) E3') :=
    hS1_bound4
  have hS2_bound : Nreal δ S2 ≤ (3 : ENNReal) * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 1) E3') :=
    hS2_bound4
  have h_third_proj : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) E3') ≤
      ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar4).toReal)) :=
    h_third_proj4

  -- Provide IsProbabilityMeasure instance for production Helper4
  letI : IsProbabilityMeasure μE3' := hμE3'_prob3

  rcases dense_graph_helper
    (κ0 := κ0) (C_extract := C_extract)
    (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one) (hδ_dyadic := hδ_dyadic)
    (hη_pos := hη_pos) (hη_work_pos := hη_work_pos) (hη_work_eq_two := hη_work_eq_two)
    (hL_exp_pos := hL_exp_pos)
    (hrho_sel_pos := hrho_sel_pos) (hrho_sep_pos := hrho_sep_pos)
    (c_dense := c_dense) (hc_dense_eq := hc_dense_eq)
    (M_G_real := M_G_real) (hM_G_pos := hM_G_real_pos)
    (hM_G_bound1024 := hM_G_real_bound)
    (hδ_small_absorb := hδ_small_absorb)
    (Pbar_param := Pbar_param) (Pbar := Pbar4)
    (E3' := E3') (E3'' := E3'') (S1 := S1) (S2 := S2)
    (round := round_fun)
    (hround_grid := hround_grid) (h_round_near := h_round_near)
    (hS1_grid := hS1_grid) (hS2_grid := hS2_grid)
    (hS1_sep := hS1_sep) (hS2_sep := hS2_sep)
    (hS1_delta := hS1_delta) (hS2_delta := hS2_delta)
    (hS1_finite := hS1_finite) (hS2_finite := hS2_finite)
    (hS1_nonempty := hS1_nonempty) (hS2_nonempty := hS2_nonempty)
    (hE3'_finite := hE3'_finite) (hE3'_sub_Pbar := hE3'_sub_Pbar)
    (hPbar_bounded := hPbar4_bounded) (hPbar_param_sub_Pbar := hPbar_param_sub_Pbar4)
    (hE3'_size := hE3'_size)
    (hE3''_sub := hE3''_sub) (hE3''_half := hE3''_half_encard)
    (h_occupancy := h_occupancy4)
    (h_proj_x := h_proj_x) (h_proj_y := h_proj_y)
    (hS1_bound := hS1_bound) (hS2_bound := hS2_bound)
    (h_third_proj_E3' := h_third_proj)
    (hE3''_mass := hE3''_mass) (hE3''_round := hE3''_round)
  with ⟨Gamma, hGamma_sub_S, hGamma_grid, hGamma_finite, hGamma_nonempty,
        hGamma_sep, hGamma_dense, hGamma_from_E3'', hGamma_third1, hGamma_third2⟩

  -- =====================================================================
  -- Sumset direct route: hGamma_third1 + h_third_proj_param + product bound
  -- =====================================================================

  let qMassV4_val : ℝ := qMassV4 η_work rho_sep
  have hqMassV4_val_eq : qMassV4_val = 2 * rho_sep + qAbsorb η_work := by
    dsimp only [qMassV4_val, qMassV4] <;> ring
  have hqAbsorb_pos : 0 < qAbsorb η_work := by
    dsimp only [qAbsorb] <;> linarith [hη_work_pos]
  have hqMassV4_nonneg : 0 ≤ qMassV4_val := by
    rw [hqMassV4_val_eq]
    have h1 : 0 ≤ 2 * rho_sep := by linarith [hrho_sep_pos]
    have h2 : 0 ≤ qAbsorb η_work := hqAbsorb_pos.le
    exact add_nonneg h1 h2

  -- Derive E3'' size lower bound for product_bound_wiring_coord
  have hE3''_size_for_prod : ENat.toENNReal E3''.encard ≥
      (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel)) * Nplane δ Pbar_param := by
    let half : ENNReal := 1 / 2
    let b : ENNReal := ENNReal.ofReal (δ ^ (3 * rho_sel)) * Nplane δ Pbar_param
    have h1 : ENat.toENNReal E3''.encard ≥ ENat.toENNReal E3'.encard / 2 := hE3''_half_encard
    have h2 : ENat.toENNReal E3'.encard ≥ b := hE3'_size4
    have h3 : ENat.toENNReal E3'.encard / 2 ≥ b / 2 := by
      exact ENNReal.div_le_div h2 (by norm_num)
    have h4 : b / 2 = half * b := by
      have h5 : b / (2 : ENNReal) = b * (2 : ENNReal)⁻¹ := by rw [div_eq_mul_inv]
      have h6 : (2 : ENNReal)⁻¹ = half := by
        simp [half] <;> norm_num
      rw [h5, h6] <;> rw [mul_comm]
    have h_assoc : half * b = half * ENNReal.ofReal (δ ^ (3 * rho_sel)) * Nplane δ Pbar_param := by
      dsimp only [half, b]
      rw [←mul_assoc]
    calc
      ENat.toENNReal E3''.encard ≥ ENat.toENNReal E3'.encard / 2 := h1
      _ ≥ b / 2 := h3
      _ = half * b := h4
      _ = half * ENNReal.ofReal (δ ^ (3 * rho_sel)) * Nplane δ Pbar_param := h_assoc

  -- Occupancy bound for E3'' (follows from E3' since E3'' ⊆ E3')
  have h_occupancy_E3'' : ∀ Q ∈ dyadicCubes 2 δ,
      ENat.toENNReal (E3'' ∩ Q).encard ≤ ENNReal.ofReal M_G_real := by
    intro Q hQ
    have h_sub : E3'' ∩ Q ⊆ E3' ∩ Q := by
      intro x hx; exact ⟨hE3''_sub hx.1, hx.2⟩
    have h3 : ENat.toENNReal (E3'' ∩ Q).encard ≤ ENat.toENNReal (E3' ∩ Q).encard :=
      ENat.toENNReal_mono (Set.encard_mono h_sub)
    have h4 : ENat.toENNReal (E3' ∩ Q).encard ≤ ENNReal.ofReal M_G_real := h_occupancy4 Q hQ
    exact le_trans h3 h4

  -- Call product_bound_wiring_coord
  have h_prod_lower : (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4_val)) * Nplane δ Pbar_param ≤
      Nreal δ S1 * Nreal δ S2 :=
    product_bound_wiring_coord
      (qAbsorb := qAbsorb η_work)
      (qMassV4 := qMassV4_val)
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hrho_sel_pos := hrho_sel_pos) (hrho_sep_nonneg := hrho_sep_pos.le)
      (hqAbsorb_pos := hqAbsorb_pos)
      (hqMassV4_eq := hqMassV4_val_eq)
      (h_box_bound := h_box_bound)
      (hE3''_size := hE3''_size_for_prod)
      (hS1_finite := hS1_finite) (hS2_finite := hS2_finite)
      (hS1_grid := hS1_grid) (hS2_grid := hS2_grid)
      (hS1_sep := hS1_sep) (hS2_sep := hS2_sep)
      (hE3''_finite := (hE3'_finite.subset hE3''_sub))
      (h_occupancy := h_occupancy_E3'')
      (hM_G_bound := by
        have h1 : M_G_real ≤ 1024 * δ ^ (-2 * rho_sep) := hM_G_real_bound
        exact ENNReal.ofReal_le_ofReal h1)
      (round_fun := round_fun)
      (h_round_near := h_round_near)
      (h_round_image := hE3''_round)

  -- Pbar_param ne_top (follows from Pbar4 finiteness and subset)
  have hPbar_param_ne_top : Nplane δ Pbar_param ≠ ⊤ := by
    have h_sub : Pbar_param ⊆ Pbar4 := hPbar_param_sub_Pbar4
    have h1 : dyadicCubesMeeting δ Pbar_param ⊆ dyadicCubesMeeting δ Pbar4 := by
      intro Q hQ
      exact ⟨hQ.1, Set.Nonempty.mono (Set.inter_subset_inter_right Q h_sub) hQ.2⟩
    have h : Nplane δ Pbar_param ≤ Nplane δ Pbar4 := ENat.toENNReal_mono (Set.encard_mono h1)
    exact ne_top_of_le_ne_top hPbar4_fin h

  -- S1, S2 ne_top (follows from finiteness)
  have hNreal_S1_eq : Nreal δ S1 = ENat.toENNReal S1.encard := by
    have h1 : dyadicCoveringNumber δ (productLikeRealLineCopy S1) = S1.encard :=
      dyadicCoveringNumber_realLineCopy hδ_pos hS1_grid
    simpa [Nreal] using congr_arg ENat.toENNReal h1
  have hS1_ne_top : Nreal δ S1 ≠ ⊤ := by
    rw [hNreal_S1_eq]
    exact ENat.toENNReal_ne_top.mpr hS1_finite.encard_lt_top.ne
  have hNreal_S2_eq : Nreal δ S2 = ENat.toENNReal S2.encard := by
    have h1 : dyadicCoveringNumber δ (productLikeRealLineCopy S2) = S2.encard :=
      dyadicCoveringNumber_realLineCopy hδ_pos hS2_grid
    simpa [Nreal] using congr_arg ENat.toENNReal h1
  have hS2_ne_top : Nreal δ S2 ≠ ⊤ := by
    rw [hNreal_S2_eq]
    exact ENat.toENNReal_ne_top.mpr hS2_finite.encard_lt_top.ne

  -- Rearrange using production corollary: N(Pbar_param) ≤ 2 * δ^(-(3ρ+qMass)) * N(S1) * N(S2)
  let C_P2S : ℝ := 2 * δ ^ (-(3 * rho_sel + qMassV4_val))
  have hC_P2S_pos : 0 < C_P2S := by positivity
  have h_prod_upper : Nplane δ Pbar_param ≤
      (2 : ENNReal) * ENNReal.ofReal (δ ^ (-(3 * rho_sel + qMassV4_val))) *
        Nreal δ S1 * Nreal δ S2 :=
    product_upper_from_wiring
      (qMassV4 := qMassV4_val)
      (hδ_pos := hδ_pos)
      (hrho_sel_pos := hrho_sel_pos)
      (hqMassV4_nonneg := hqMassV4_nonneg)
      (hPbar_ne_top := hPbar_param_ne_top)
      (hS1_ne_top := hS1_ne_top)
      (hS2_ne_top := hS2_ne_top)
      (h_product_lower := h_prod_lower)
  have h_C_P2S_eq : ENNReal.ofReal C_P2S =
      (2 : ENNReal) * ENNReal.ofReal (δ ^ (-(3 * rho_sel + qMassV4_val))) := by
    have h_pos2 : 0 ≤ (2 : ℝ) := by norm_num
    have h1 : ENNReal.ofReal C_P2S =
        ENNReal.ofReal ((2 : ℝ) * δ ^ (-(3 * rho_sel + qMassV4_val))) := by rfl
    rw [h1]
    rw [ENNReal.ofReal_mul h_pos2]
    <;> simp
  have h_prod : Nplane δ Pbar_param ≤ ENNReal.ofReal C_P2S * Nreal δ S1 * Nreal δ S2 := by
    rw [h_C_P2S_eq]
    exact h_prod_upper

  -- Combine hGamma_third1 + h_third_proj_param4
  have h_third_Gamma : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) Gamma) ≤
      (3 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) := by
    calc
      Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) Gamma)
        ≤ (3 : ENNReal) * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) E3') := hGamma_third1
      _ ≤ (3 : ENNReal) * (ENNReal.ofReal (δ ^ (-(L_exp * η))) *
              ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal))) := by
          gcongr
          <;> exact h_third_proj_param4
      _ = (3 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
            ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) := by ring

  -- Apply sumset_bridge_algebra
  have h_sumset_helper5 : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) Gamma) ≤
      (3 : ENNReal) * ENNReal.ofReal (Real.sqrt C_P2S * δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((Nreal δ S1).toReal * (Nreal δ S2).toReal)) :=
    sumset_bridge_algebra
      (hδ_pos := hδ_pos)
      (hPbar_ne_top := hPbar_param_ne_top)
      (hS1_ne_top := hS1_ne_top)
      (hS2_ne_top := hS2_ne_top)
      (hC_P2S_pos := hC_P2S_pos)
      (h_third := h_third_Gamma)
      (h_prod := h_prod)

  -- Helper5 V4 budget exponent definitions (needed for C_sum in h_sumset_const)
  let q_K : ℝ := qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep
  let θ_num : ℝ := qAbsorb η_work
  let q_input : ℝ := qInputV4 L_exp η_work rho_sel rho_sep
  let qKA : ℝ := qKAV4 L_exp η_work rho_sel rho_sep
  let qDiffV3 : ℝ := 80 * q_K + 2 * qKA + qAbsorb η_work
  let qSizeLossV3 : ℝ := qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
  let C_sum : ℝ := 3 * Real.sqrt C_P2S * δ ^ (-(L_exp * η))
  let R_norm : ℝ := 2 * R

  -- h_sumset_const proves C_sum ≤ δ^(-q_K) (needed for bsg_extraction_helper)
  have h_sumset_const : C_sum ≤ δ ^ (-q_K) := by
    set e_proj : ℝ := L_exp * η with he_proj
    set e_mass : ℝ := (3 * rho_sel + qMassV4_val) / 2 with he_mass
    have h_sqrt : Real.sqrt C_P2S = Real.sqrt 2 * δ ^ (-e_mass) := by
      dsimp only [C_P2S]
      have h_pos1 : 0 ≤ (2 : ℝ) := by norm_num
      have h_pos2 : 0 ≤ δ ^ (-(3 * rho_sel + qMassV4_val)) := by positivity
      have h1 : Real.sqrt (2 * δ ^ (-(3 * rho_sel + qMassV4_val))) =
          Real.sqrt 2 * Real.sqrt (δ ^ (-(3 * rho_sel + qMassV4_val))) := by
        rw [Real.sqrt_mul] <;> positivity
      rw [h1]
      have h2 : Real.sqrt (δ ^ (-(3 * rho_sel + qMassV4_val))) = δ ^ (-e_mass) := by
        simp only [he_mass]
        have h_pos : 0 ≤ δ ^ (-(3 * rho_sel + qMassV4_val)) := by positivity
        rw [Real.sqrt_eq_rpow]
        rw [← Real.rpow_mul hδ_pos.le] <;> ring_nf
      rw [h2] <;> ring
    have h3 : δ ^ (-e_mass) * δ ^ (-e_proj) = δ ^ (-(e_proj + e_mass)) := by
      rw [← Real.rpow_add hδ_pos] <;> ring_nf
    have h_ep : δ ^ (-(L_exp * η)) = δ ^ (-e_proj) := by rw [he_proj]
    have h_C_sum_eq : C_sum = (3 : ℝ) * Real.sqrt 2 * δ ^ (-(e_proj + e_mass)) := by
      dsimp only [C_sum]
      rw [h_sqrt, h_ep]
      calc
        3 * (Real.sqrt 2 * δ ^ (-e_mass)) * δ ^ (-e_proj)
          = 3 * Real.sqrt 2 * (δ ^ (-e_mass) * δ ^ (-e_proj)) := by ring
        _ = 3 * Real.sqrt 2 * δ ^ (-(e_proj + e_mass)) := by rw [h3] <;> ring
    rw [h_C_sum_eq]
    have hqK : q_K = qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by rfl
    have hem : e_mass = (qMassV4 η_work rho_sep + 3 * rho_sel) / 2 := by
      simp only [he_mass, qMassV4_val] <;> ring
    have h5 : (3 : ℝ) * Real.sqrt 2 ≤
        δ ^ (-(q_K - (e_proj + e_mass))) := by
      rw [hqK, hem]
      exact h_sumset_absorb
    have h_posA : 0 < δ ^ (-(e_proj + e_mass)) := by positivity
    have h6 : (3 : ℝ) * Real.sqrt 2 * δ ^ (-(e_proj + e_mass)) ≤
        δ ^ (-(e_proj + e_mass)) * δ ^ (-(q_K - (e_proj + e_mass))) := by
      calc
        3 * Real.sqrt 2 * δ ^ (-(e_proj + e_mass))
          = δ ^ (-(e_proj + e_mass)) * (3 * Real.sqrt 2) := by ring
        _ ≤ δ ^ (-(e_proj + e_mass)) * δ ^ (-(q_K - (e_proj + e_mass))) := by
          gcongr
    have h7 : δ ^ (-(e_proj + e_mass)) * δ ^ (-(q_K - (e_proj + e_mass))) = δ ^ (-q_K) := by
      rw [← Real.rpow_add hδ_pos] <;> ring_nf
    rw [h7] at h6
    exact h6
  have h_coeff_eq : (3 : ENNReal) * ENNReal.ofReal (Real.sqrt C_P2S * δ ^ (-(L_exp * η))) =
      ENNReal.ofReal C_sum := by
    have h_pos3 : 0 ≤ (3 : ℝ) := by norm_num
    have h1 : (3 : ENNReal) * ENNReal.ofReal (Real.sqrt C_P2S * δ ^ (-(L_exp * η))) =
        ENNReal.ofReal ((3 : ℝ) * (Real.sqrt C_P2S * δ ^ (-(L_exp * η)))) := by
      have h3 : (3 : ENNReal) = ENNReal.ofReal (3 : ℝ) := by simp
      rw [h3]
      rw [← ENNReal.ofReal_mul h_pos3]
      <;> rfl
    rw [h1]
    have h2 : (3 : ℝ) * (Real.sqrt C_P2S * δ ^ (-(L_exp * η))) = C_sum := by
      dsimp only [C_sum] <;> ring
    rw [h2]
  have h_sumset : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) Gamma) ≤
      ENNReal.ofReal C_sum * ENNReal.ofReal (Real.sqrt ((Nreal δ S1).toReal * (Nreal δ S2).toReal)) := by
    rw [h_coeff_eq] at h_sumset_helper5
    exact h_sumset_helper5

  -- =====================================================================
  -- Step 5: Helper 5 — BSG extraction
  -- =====================================================================

  -- Positivity proofs for Helper5 exponents
  have hq_K_pos : 0 < q_K := by
    have h_eq : q_K = (L_exp + 2) * η_work + qProjective p_projective ε κ0 + qDensityV4 η_work rho_sel rho_sep := by
      simp only [q_K, qKV4, qK] <;> ring
    rw [h_eq]
    have h1 : 0 < (L_exp + 2) * η_work := by positivity
    have h2 : 0 < qProjective p_projective ε κ0 := by
      dsimp only [qProjective] <;> positivity
    have h3 : 0 < qDensityV4 η_work rho_sel rho_sep := by
      dsimp only [qDensityV4, qAbsorb]
      have h31 : 0 < 3 * rho_sel := by positivity
      have h32 : 0 < 2 * rho_sep := by positivity
      have h33 : 0 < η_work / 100 := by positivity
      linarith only [h31, h32, h33]
    linarith only [h1, h2, h3]
  have hθ_num_pos : 0 < θ_num := by
    dsimp only [θ_num, qAbsorb] <;> positivity
  have hqKA_nonneg : 0 ≤ qKA := by
    dsimp only [qKA, qKAV4, alphaProjectionV4, qMassV4] <;> positivity
  have hqAbsorb_nonneg : 0 ≤ qAbsorb η_work := by positivity
  have hq_input_nonneg : 0 ≤ q_input := by
    dsimp only [q_input, qInputV4, qFixedCoordinate] <;> positivity
  have hqSizeLossV3_pos : 0 < qSizeLossV3 :=
    qSizeLossV4_pos hL_exp_pos hη_work_pos hε_pos hkappa_pos
      (by linarith [hp_ge_10]) hτ_pos hrho_sel_nonneg hrho_sep_nonneg
  have hqDiffV3_eq : qDiffV3 = 80 * q_K + 2 * qKA + qAbsorb η_work := by rfl
  have hqSizeLossV3_ge : q_input + 10 * q_K ≤ qSizeLossV3 := by
    set gap : ℝ := qSizeLossV3 - q_input - 10 * q_K with hgap_def
    have h_gap_eq : gap = qAbsorb η_work + qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep :=
      v4_size_loss_gap_eq (L_exp := L_exp) (η_work := η_work) (ε := ε) (κ0 := κ0) (p_projective := p_projective) (τ := τ) (rho_sel := rho_sel) (rho_sep := rho_sep)
    have h_nonneg : 0 ≤ gap := by
      rw [h_gap_eq]
      have h1 : 0 ≤ qAbsorb η_work := hqAbsorb_nonneg
      have h2 : 0 ≤ qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep :=
        qNormChunkV4_nonneg hL_exp_pos hη_work_pos hε_pos hkappa_pos
          (by linarith [hp_ge_10]) hτ_pos hrho_sel_nonneg hrho_sep_nonneg
      linarith only [h1, h2]
    linarith only [hgap_def, h_nonneg]

  -- Constant proofs
  have hC_A_pos : 0 < C := by linarith [hC_ge1]
  have hC_sum_pos : 0 < C_sum := by
    dsimp only [C_sum] <;> positivity
  have hC_sum_le : C_sum ≤ δ ^ (-q_K) := h_sumset_const

  -- Density bridge H4→H5: derive c_dense_real from Helper4's (c_dense/4) bound
  let density_exp : ℝ := 3 * rho_sel + 2 * rho_sep + qAbsorb η_work + L_exp * η_work
  have h_absorb4 : δ ^ (q_K - density_exp) ≤ 1 / 4 := by
    have h_gap : q_K - density_exp = 2 * η_work + qProjective p_projective ε κ0 := by
      simp only [q_K, qKV4, qDensityV4, qK, qProjective] <;> ring
    rw [h_gap]
    have h_ge : qAbsorb η_work ≤ 2 * η_work + qProjective p_projective ε κ0 := by
      dsimp only [qAbsorb, qProjective]
      have h1 : 0 < η_work := hη_work_pos
      have h2 : 0 ≤ p_projective * ε / κ0 := by positivity
      linarith only [h1, h2]
    have h1 : δ ^ (2 * η_work + qProjective p_projective ε κ0) ≤ δ ^ (qAbsorb η_work) :=
      Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h_ge
    have h3 : δ ^ (qAbsorb η_work) ≤ 1 / 4 := by
      have h4 : (81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80 ≤ δ ^ (-(qAbsorb η_work)) := h_KBSG_absorb
      have h5 : 0 < δ ^ (qAbsorb η_work) := by positivity
      have h6 : δ ^ (-(qAbsorb η_work)) = (δ ^ (qAbsorb η_work))⁻¹ := by
        rw [Real.rpow_neg hδ_pos.le] <;> ring
      rw [h6] at h4
      field_simp [h5.ne'] at h4 ⊢ <;> linarith
    exact le_trans h1 h3
  have hGamma_dense_H4 : ENat.toENNReal (dyadicCoveringNumber δ Gamma) ≥
      (ENNReal.ofReal (δ ^ density_exp) / 4) * Nreal δ S1 * Nreal δ S2 := by
    have h_eq : (ENNReal.ofReal (δ ^ density_exp) / 4) = (c_dense / 4) := by
      rw [←hc_dense_eq] <;> rfl
    rw [h_eq]
    exact hGamma_dense
  rcases density_bridge_helper4_to_helper5 hδ_pos hδ_lt_one h_absorb4
    (S1 := S1) (S2 := S2) (Gamma := Gamma)
    (hGamma_density_H4 := hGamma_dense_H4)
  with ⟨c_dense_real, hc_dense_pos, hc_dense_ge, hGamma_dense_real⟩

  -- Absorption conditions
  have h_absorb_ret : δ ^ θ_num ≤ 1 / (3 ^ 10 : ℝ) := by
    dsimp only [θ_num]
    have h1 : (81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80 ≤ δ ^ (-(qAbsorb η_work)) := h_KBSG_absorb
    have h_inv : δ ^ (-(qAbsorb η_work)) = (δ ^ (qAbsorb η_work))⁻¹ := by
      rw [Real.rpow_neg hδ_pos.le] <;> ring
    rw [h_inv] at h1
    have h2 : δ ^ (qAbsorb η_work) ≤ 1 / ((81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80) := by
      have h_pos : 0 < δ ^ (qAbsorb η_work) := by positivity
      field_simp [h_pos.ne'] at h1 ⊢ <;> linarith
    have h3 : 1 / ((81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80) ≤ 1 / (3 ^ 10 : ℝ) := by
      gcongr <;> norm_num
    exact le_trans h2 h3
  have h_absorb_size : δ ^ (qSizeLossV3 - q_input - 10 * q_K) ≤ 1 / (3 ^ 10 : ℝ) := by
    set gap : ℝ := qSizeLossV3 - q_input - 10 * q_K with hgap_def
    have h_gap_eq : gap = qAbsorb η_work + qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep :=
      v4_size_loss_gap_eq (L_exp := L_exp) (η_work := η_work) (ε := ε) (κ0 := κ0) (p_projective := p_projective) (τ := τ) (rho_sel := rho_sel) (rho_sep := rho_sep)
    have h_nonneg : 0 ≤ qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep :=
      qNormChunkV4_nonneg hL_exp_pos hη_work_pos hε_pos hkappa_pos
        (by linarith [hp_ge_10]) hτ_pos hrho_sel_nonneg hrho_sep_nonneg
    have h_ge : qAbsorb η_work ≤ gap := by
      rw [h_gap_eq]; linarith [h_nonneg]
    have h1 : δ ^ gap ≤ δ ^ (qAbsorb η_work) :=
      Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h_ge
    exact le_trans h1 h_absorb_ret

  -- R_norm and boundedness
  have hR_norm_pos : 0 < R_norm := by
    dsimp only [R_norm] <;> linarith [hR_ge1]
  have hR_norm_int : ∃ (c : ℤ), R_norm = (c : ℝ) := by
    refine ⟨(2 : ℤ) * (2 : ℤ) ^ k_R, ?_⟩
    have h1 : R = (2 : ℝ) ^ k_R := hR_eq_pow2
    dsimp only [R_norm]
    rw [h1] <;> norm_cast <;> ring
  have hS1_bdd : ∀ x ∈ S1, |x| ≤ R_norm + 1 := by
    intro x hx
    have h1 : x ∈ Set.image (fun p : EuclideanSpace ℝ (Fin 2) => round_fun (p 0)) E3' := hS1_sub_round hx
    rcases h1 with ⟨p, hpE3', rfl⟩
    have h2 : p ∈ F '' E3 := by rw [hE3'_eq] at hpE3'; exact hpE3'
    rcases h2 with ⟨q, hqE3, rfl⟩
    have hqPbar : q ∈ Pbar_param := hE3_sub_Pbar hqE3
    have hq_bdd : |q 0| ≤ R ∧ |q 1| ≤ R := hPbar_Rbox' q hqPbar
    exact round_coordinate_bound (hδ_lt_one := hδ_lt_one) (hδ_pos := hδ_pos)
      (hθ1_in_Icc := hθ1_in_Icc) (hθ2_in_Icc := hθ2_in_Icc)
      (hθ1_lt_θ3 := hθ1_lt_θ3) (hθ3_lt_θ2 := hθ3_lt_θ2)
      (hq_bdd := hq_bdd) (hF_formula := hF_formula)
      (h_round_near := h_round_near) (hR_norm_eq := by rfl) 0
  have hS2_bdd : ∀ x ∈ S2, |x| ≤ R_norm + 1 := by
    intro x hx
    have h1 : x ∈ Set.image (fun p : EuclideanSpace ℝ (Fin 2) => round_fun (p 1)) E3' := hS2_sub_round hx
    rcases h1 with ⟨p, hpE3', rfl⟩
    have h2 : p ∈ F '' E3 := by rw [hE3'_eq] at hpE3'; exact hpE3'
    rcases h2 with ⟨q, hqE3, rfl⟩
    have hqPbar : q ∈ Pbar_param := hE3_sub_Pbar hqE3
    have hq_bdd : |q 0| ≤ R ∧ |q 1| ≤ R := hPbar_Rbox' q hqPbar
    exact round_coordinate_bound (hδ_lt_one := hδ_lt_one) (hδ_pos := hδ_pos)
      (hθ1_in_Icc := hθ1_in_Icc) (hθ2_in_Icc := hθ2_in_Icc)
      (hθ1_lt_θ3 := hθ1_lt_θ3) (hθ3_lt_θ2 := hθ3_lt_θ2)
      (hq_bdd := hq_bdd) (hF_formula := hF_formula)
      (h_round_near := h_round_near) (hR_norm_eq := by rfl) 1

  -- =====================================================================
  -- Step 5: Helper 5 — BSG extraction (PRODUCTION)
  -- =====================================================================

  -- C_sum absorption (already proved as h_sumset_const)
  have hC_sum_le : C_sum ≤ δ ^ (-q_K) := h_sumset_const
  have hC_A_pos : 0 < C := by linarith [hC_ge1]

  -- κ0 ≤ τ follows from 2*κ0 < τ
  have hκ0_le_tau : κ0 ≤ τ := by linarith [h2kappa_lt_tau]

  -- Define C_work' locally (equals C_work = 35*C)
  let C_work' : ℝ := C_work
  have hC_work'_eq : C_work' = 35 * C := hC_work_eq
  have hC_work'_pos : 0 < C_work' := by linarith [hC_work_ge1]
  have hC_work'_le : C_work' ≤ δ ^ (-η_work) := hC_work_le

  -- =====================================================================
  -- hPbar_lower_granite: derive from hPbar_lower_strong + hC_work_le
  -- =====================================================================
  rcases pbar_lower_granite_bridge
    (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
    (hη_work_pos := hη_work_pos)
    (h5η_work_lt := h5η_work_lt)
    (h_box_bound := h_box_bound)
    (hC_work_pos := hC_work'_pos) (hC_work_le := hC_work'_le)
    (hPbar_lower_strong := hPbar_lower_strong)
  with ⟨hPbar_lower_granite, hPbar_size⟩

  -- =====================================================================
  -- absolute_coordinate_wiring → K_A + size lower bounds
  -- =====================================================================
  let α : ℝ := alphaProjectionV4 L_exp η_work
  have hα_pos : 0 < α := by
    dsimp only [α, alphaProjectionV4] <;> positivity
  have h_exp_id : α + qMassV4_val + 3 * rho_sel + 9 * η_work / 4 = q_input - qAbsorb η_work / 2 := by
    dsimp only [α, qMassV4_val, q_input, qInputV4, qFixedCoordinate,
      alphaProjectionV4, qMassV4, rhoSelDefault, qAbsorb]
    rw [hrho_sel_eq]
    simp only [rhoSelDefault, qAbsorb] <;> ring
  have h_KA_id : 2 * α + qMassV4_val + 3 * rho_sel + 2 * qAbsorb η_work = qKA := by
    dsimp only [α, qMassV4_val, qKA, qKAV4, alphaProjectionV4, qMassV4] <;> ring
  have hPbar_pos : 0 < Nplane δ Pbar_param := by
    have h_pos : 0 < ENNReal.ofReal (δ ^ (-2 * s + η_work / 2) / (98 * C_work' ^ 4)) := by positivity
    exact lt_of_lt_of_le h_pos hPbar_lower_strong

  have hα_eq_Lexpη : α = L_exp * η := by
    dsimp only [α, alphaProjectionV4]
    rw [hη_work_eq_two] <;> ring
  have h_proj_x4' : Nreal δ ((fun p : EuclideanSpace ℝ (Fin 2) => p 0) '' E3') ≤
      2 * ENNReal.ofReal (δ ^ (-α)) * ENNReal.ofReal (Real.sqrt (Nplane δ Pbar_param).toReal) := by
    have h_eq : δ ^ (-(L_exp * η)) = δ ^ (-α) := by rw [← hα_eq_Lexpη]
    rw [h_eq] at h_proj_x4
    exact h_proj_x4
  have h_proj_y4' : Nreal δ ((fun p : EuclideanSpace ℝ (Fin 2) => p 1) '' E3') ≤
      2 * ENNReal.ofReal (δ ^ (-α)) * ENNReal.ofReal (Real.sqrt (Nplane δ Pbar_param).toReal) := by
    have h_eq : δ ^ (-(L_exp * η)) = δ ^ (-α) := by rw [← hα_eq_Lexpη]
    rw [h_eq] at h_proj_y4
    exact h_proj_y4
  rcases absolute_coordinate_wiring
    (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
    (hα_pos := hα_pos) (hrho_sel_pos := hrho_sel_pos)
    (hrho_sep_nonneg := hrho_sep_pos.le)
    (hqAbsorb_pos := hqAbsorb_pos) (hqMassV4_nonneg := hqMassV4_nonneg)
    (hq_input_nonneg := hq_input_nonneg) (hqKA_nonneg := hqKA_nonneg)
    (hqMassV4_eq := hqMassV4_val_eq) (h_exp_id := h_exp_id) (h_KA_id := h_KA_id)
    (h_box_bound := h_box_bound)
    (Pbar := Pbar_param)
    (hPbar_fin := hPbar_param_ne_top) (hPbar_pos := hPbar_pos)
    (hPbar_lower := hPbar_lower_granite)
    (S1 := S1) (S2 := S2)
    (hS1_grid := hS1_grid) (hS2_grid := hS2_grid)
    (hS1_finite := hS1_finite) (hS2_finite := hS2_finite)
    (hS1_sep := hS1_sep) (hS2_sep := hS2_sep)
    (E3' := E3') (E3'' := E3'')
    (hE3'_finite := hE3'_finite) (hE3''_finite := (hE3'_finite.subset hE3''_sub))
    (hE3''_sub := hE3''_sub)
    (hE3'_size := hE3'_size4)
    (hE3''_half := hE3''_half_encard)
    (M_G_real := M_G_real)
    (hM_G_pos := hM_G_real_pos) (hM_G_bound := hM_G_real_bound)
    (hE3'_occupancy := h_occupancy4)
    (round_fun := round_fun)
    (h_round_near := h_round_near)
    (hE3''_round := hE3''_round)
    (h_proj1 := h_proj_x4') (h_proj2 := h_proj_y4')
    (h_round1 := hS1_bound4) (h_round2 := hS2_bound4)
  with ⟨K_A, hS1_le_S2, hS2_le_S1, hK_A_ge_one, hK_A_ne_top, hK_A_le,
        hS1_lower, hS2_lower⟩

  -- =====================================================================
  -- Production Helper5 — BSG extraction (FULL CALL)
  -- =====================================================================
  rcases ProductLikeIncidence.IncidenceToRingContradiction.bsg_extraction_helper
    (hδ_pos := hδ_pos) (hδ_dyadic := hδ_dyadic) (hδ_lt_one := hδ_lt_one)
    (hs_pos := hs_pos) (hs_lt_one := hs_lt_one)
    (hκ0_pos := hkappa_pos) (hκ0_lt_s := hkappa_lt_s)
    (q_K := q_K) (θ_num := θ_num) (q_input := q_input)
    (qSizeLossV3 := qSizeLossV3) (qDiffV3 := qDiffV3) (qKA := qKA) (qAbsorb := qAbsorb η_work)
    (hq_K_pos := hq_K_pos) (hθ_num_pos := hθ_num_pos) (hqKA_nonneg := hqKA_nonneg)
    (hqAbsorb_nonneg := hqAbsorb_nonneg) (hq_input_nonneg := hq_input_nonneg)
    (hqSizeLossV3_pos := hqSizeLossV3_pos) (hqDiffV3_eq := hqDiffV3_eq)
    (hqSizeLossV3_ge := hqSizeLossV3_ge)
    (C_A := C_extract) (C_sum := C_sum) (c_dense := c_dense_real)
    (hC_A_pos := hC_extract_pos) (hC_sum_pos := hC_sum_pos) (hc_dense_pos := hc_dense_pos)
    (hC_sum_le := hC_sum_le) (hc_dense_ge := hc_dense_ge)
    (K_A := K_A) (hK_A_ge_one := hK_A_ge_one) (hK_A_ne_top := hK_A_ne_top)
    (hK_A_le := hK_A_le)
    (hS1_le_S2 := hS1_le_S2) (hS2_le_S1 := hS2_le_S1)
    (hS1_lower := hS1_lower) (hS2_lower := hS2_lower)
    (hS1_delta := hS1_delta) (hS2_delta := hS2_delta)
    (hS1_nonempty := hS1_nonempty) (hS2_nonempty := hS2_nonempty)
    (hS1_fin := hS1_finite) (hS2_fin := hS2_finite)
    (hS1_sep := hS1_sep) (hS2_sep := hS2_sep)
    (hS1_grid := hS1_grid) (hS2_grid := hS2_grid)
    (Gamma := Gamma)
    (hGamma_sub := hGamma_sub_S) (hGamma_fin := hGamma_finite)
    (hGamma_nonempty := hGamma_nonempty) (hGamma_grid := hGamma_grid)
    (hGamma_dense := hGamma_dense_real) (h_sumset := h_sumset)
    (h_absorb_ret := h_absorb_ret)
    (h_absorb_KBSG := h_KBSG_absorb)
    (h_absorb_size := h_absorb_size)
    (R_norm := R_norm) (hR_norm_pos := hR_norm_pos) (hR_norm_int := hR_norm_int)
    (hS1_bdd := hS1_bdd) (hS2_bdd := hS2_bdd)
  with ⟨
    B1, B2, G',
    C_BSG, K_BSG, K_BSG_B2, K_BSG_all,
    K_sector_B1, K_sector_B2,
    k, j,
    B1_norm, B2_norm,
    G_norm, G_orig,
    R_ret, M_ret,
    hB1_sub_S1, hB2_sub_S2, hG'_sub_Gamma, hG'_fibers, hG'_grid,
    hG'_nonempty,
    hB1_fin, hB2_fin,
    hB1_nonempty, hB2_nonempty,
    hB1_int_grid, hB2_int_grid,
    hB1_delta, hB2_delta,
    hB1_size_lower, hB2_size_lower,
    hG'_density,
    h_sec1_B1, h_sec2_B1, h_sec3_B1,
    h_sec1_B2, h_sec2_B2, h_sec3_B2,
    hK_BSG_pos, h_diff_self, h_diff_cross, h_sum_B1B2_B1,
    hK_BSG_B2_pos, h_diff_B2B2, h_diff_B2B1_B2, h_sum_B1B2_B2,
    hK_BSG_all_pos, hK_BSG_le_all, hK_BSG_B2_le_all,
    hK_BSG_all_B1, hK_BSG_all_B2, hK_BSG_all_le,
    hB1_norm_unit, hB2_norm_unit,
    hB1_norm_nonempty, hB2_norm_nonempty,
    hB1_norm_fin, hB2_norm_fin,
    hB1_norm_sep, hB2_norm_sep,
    hG_norm_fin, hG_norm_grid, hG_norm_sub,
    hG_orig_sub, hG'_witness,
    hG_norm_density_ncard,
    hR_ret_pos, hR_ret_eq, hM_ret_pos,
    hC_BSG_eq, hM_ret_eq,
    hB1_size_lower_norm, hB2_size_lower_norm,
    hB1_norm_size_upper, hB2_norm_size_upper,
    hB1_norm_delta, hB2_norm_delta,
    h_norm1, h_norm2, h_norm3,
    h_norm4, h_norm5, h_norm6
  ⟩

  -- =====================================================================
  -- Helper5 output aliases for glue_h5_to_h6
  -- =====================================================================
  have hC_BSG_pos : 0 < C_BSG := by
    rw [hC_BSG_eq]
    positivity
  let c_ret : ℝ := δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ)) / 4
  have hc_ret_nonneg : 0 ≤ c_ret := by positivity
  have h_density_ncard : c_ret * (B1_norm.ncard : ℝ) * (B2_norm.ncard : ℝ) ≤
      (G_norm.ncard : ℝ) := hG_norm_density_ncard
  have h_retention1 : c_ret * (S1.ncard : ℝ) / M_ret ≤ (B1_norm.ncard : ℝ) :=
    hB1_size_lower_norm
  have h_retention2 : c_ret * (S2.ncard : ℝ) / M_ret ≤ (B2_norm.ncard : ℝ) :=
    hB2_size_lower_norm

  -- =====================================================================
  -- K_BSG_unified via production helper5_unified_exponent_v4
  -- =====================================================================
  let R_v4 : ℝ := R_norm / 2
  let R1_v4 : ℝ := R_norm + 1
  have hR1_eq : 2 * R1_v4 + 1 = 4 * R_v4 + 3 := by
    dsimp only [R1_v4, R_v4] <;> ring
  have h4R_v4_le_qbox : 4 * R_v4 ≤ δ ^ (-(qBox η_work τ)) := by
    dsimp only [R_v4, R_norm] <;> linarith [h4R_le_qbox]

  have hqDiffV3_eq' : qDiffV3 = 80 * q_K + 2 * qKA + qAbsorb η_work := by rfl
  have hqKV4_ge : qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep ≥ q_K := by
    exact le_refl _
  have hqKAV4_ge : qKAV4 L_exp η_work rho_sel rho_sep ≥ qKA := by
    simpa [qKA] using le_refl _
  have hGraphV4_eq : qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep =
      22 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep + η_work / 2 + η_work / 20 := by rfl
  have hNormChunk_eq : qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep =
      qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep + qBox η_work τ + qAbsorb η_work := by rfl
  have hDiffV4_eq : qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep =
      80 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep +
      2 * qKAV4 L_exp η_work rho_sel rho_sep + qAbsorb η_work +
      qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by rfl

  have h_absorb_unified : δ ^ (qAbsorb η_work) ≤ 1 / (512 * (3 ^ 22 : ℝ)) := by
    have h1 : (81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80 ≤ δ ^ (-(qAbsorb η_work)) := h_KBSG_absorb
    have h_inv : δ ^ (-(qAbsorb η_work)) = (δ ^ (qAbsorb η_work))⁻¹ := by
      rw [Real.rpow_neg hδ_pos.le] <;> ring
    rw [h_inv] at h1
    have h_pos : 0 < δ ^ (qAbsorb η_work) := by positivity
    have h2 : δ ^ (qAbsorb η_work) ≤ 1 / ((81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80) := by
      field_simp [h_pos.ne'] at h1 ⊢ <;> linarith
    have h3 : (1 : ℝ) / ((81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80) ≤ 1 / (512 * (3 ^ 22 : ℝ)) := by
      gcongr <;> norm_num
    exact le_trans h2 h3

  rcases ProductLikeIncidence.IncidenceToRingContradiction.helper5_unified_exponent_v4
    (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
    (hqDiffV3_eq := hqDiffV3_eq')
    (hqKV4_ge := hqKV4_ge) (hqKAV4_ge := hqKAV4_ge)
    (hGraphV4_eq := hGraphV4_eq)
    (hη_work_pos := hη_work_pos)
    (hqBox_nonneg := by dsimp only [qBox] <;> positivity)
    (hNormChunk_eq := hNormChunk_eq)
    (hDiffV4_eq := hDiffV4_eq)
    (h4R_le_qbox := h4R_v4_le_qbox)
    (hR1_eq := hR1_eq)
    (hK_BSG_pos := hK_BSG_pos)
    (hK_BSG_B2_pos := hK_BSG_B2_pos)
    (hK_BSG_all_pos := hK_BSG_all_pos)
    (hK_BSG_le_all := hK_BSG_le_all)
    (hK_BSG_B2_le_all := hK_BSG_B2_le_all)
    (hK_BSG_all_le := hK_BSG_all_le)
    (hR_ret_pos := hR_ret_pos)
    (hR_ret_eq := hR_ret_eq)
    (h_absorb := h_absorb_unified)
    (hqAbsorb_pos := hqAbsorb_pos)
  with ⟨K_BSG_unified, h_unified_def, hK_BSG_unified_pos, hK_BSG_unified_le,
    _h_dom1, _h_dom2, _h_dom3, _h_dom4⟩

  let q_diff : ℝ := qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep

  -- Boundedness of B1_norm, B2_norm
  have hB1_bounded : IsBounded B1_norm := by
    have h : B1_norm ⊆ Set.Icc (0 : ℝ) 1 := by
      intro x hx
      exact (hB1_norm_unit hx).2
    exact IsBounded.subset (Metric.isBounded_Icc 0 1) h
  have hB2_bounded : IsBounded B2_norm := by
    have h : B2_norm ⊆ Set.Icc (0 : ℝ) 1 := by
      intro x hx
      exact (hB2_norm_unit hx).2
    exact IsBounded.subset (Metric.isBounded_Icc 0 1) h

  -- G_norm separated from grid + finite
  have hG_norm_separated : ∀ z ∈ G_norm, ∀ w ∈ G_norm, z ≠ w → dist z w ≥ δ := by
    intro z hz w hw hne
    have hz1 : ∃ k : ℤ, z 0 = δ * (k : ℝ) := hG_norm_grid z hz 0
    have hz2 : ∃ k : ℤ, z 1 = δ * (k : ℝ) := hG_norm_grid z hz 1
    have hw1 : ∃ k : ℤ, w 0 = δ * (k : ℝ) := hG_norm_grid w hw 0
    have hw2 : ∃ k : ℤ, w 1 = δ * (k : ℝ) := hG_norm_grid w hw 1
    rcases hz1 with ⟨kz0, hkz0⟩
    rcases hz2 with ⟨kz1, hkz1⟩
    rcases hw1 with ⟨kw0, hkw0⟩
    rcases hw2 with ⟨kw1, hkw1⟩
    have h_ne_coord : kz0 ≠ kw0 ∨ kz1 ≠ kw1 := by
      by_contra h
      push Not at h
      have h_eq : z = w := by
        ext i
        fin_cases i <;> simp [h.1, h.2, hkz0, hkz1, hkw0, hkw1]
      exact hne h_eq
    have h_coord_diff_ge1 : ∀ (a b : ℤ), a ≠ b → |(a : ℝ) - (b : ℝ)| ≥ 1 := by
      intro a b h
      have h1 : a - b ≠ 0 := by omega
      have h2 : |a - b| ≥ 1 := by
        by_cases h3 : a - b > 0
        · have h4 : a - b ≥ 1 := by omega
          rw [abs_of_pos h3] <;> omega
        · have h5 : a - b < 0 := by omega
          have h6 : a - b ≤ -1 := by omega
          rw [abs_of_neg h5] <;> omega
      exact_mod_cast h2
    have h_dist_ge : dist z w ≥ δ := by
      have h_dist_coord0 : dist z w ≥ |z 0 - w 0| := by
        have h : dist z w = ‖z - w‖ := by rfl
        rw [h]
        have h2 : ‖(z - w)‖ ≥ |(z - w) 0| := by
          have h3 : ‖(z - w)‖ ^ 2 = |(z - w) 0| ^ 2 + |(z - w) 1| ^ 2 := by
            rw [EuclideanSpace.norm_sq_eq (z - w), Fin.sum_univ_two] <;> rfl
          have h4 : 0 ≤ |(z - w) 1| ^ 2 := by positivity
          have h5 : ‖(z - w)‖ ^ 2 ≥ |(z - w) 0| ^ 2 := by
            rw [h3] <;> linarith only [h4]
          have h6 : 0 ≤ ‖(z - w)‖ := by positivity
          have h7 : 0 ≤ |(z - w) 0| := by positivity
          by_contra h8
          have h9 : ‖(z - w)‖ < |(z - w) 0| := by linarith
          have h10 : ‖(z - w)‖ ^ 2 < |(z - w) 0| ^ 2 := by
            gcongr
          linarith only [h5, h10]
        simpa [Pi.sub_apply] using h2
      have h_dist_coord1 : dist z w ≥ |z 1 - w 1| := by
        have h : dist z w = ‖z - w‖ := by rfl
        rw [h]
        have h2 : ‖(z - w)‖ ≥ |(z - w) 1| := by
          have h3 : ‖(z - w)‖ ^ 2 = |(z - w) 0| ^ 2 + |(z - w) 1| ^ 2 := by
            rw [EuclideanSpace.norm_sq_eq (z - w), Fin.sum_univ_two] <;> rfl
          have h4 : 0 ≤ |(z - w) 0| ^ 2 := by positivity
          have h5 : ‖(z - w)‖ ^ 2 ≥ |(z - w) 1| ^ 2 := by
            rw [h3] <;> linarith only [h4]
          have h6 : 0 ≤ ‖(z - w)‖ := by positivity
          have h7 : 0 ≤ |(z - w) 1| := by positivity
          by_contra h8
          have h9 : ‖(z - w)‖ < |(z - w) 1| := by linarith
          have h10 : ‖(z - w)‖ ^ 2 < |(z - w) 1| ^ 2 := by
            gcongr
          linarith only [h5, h10]
        simpa [Pi.sub_apply] using h2
      rcases h_ne_coord with (h | h)
      · -- kz0 ≠ kw0
        have h6 : |(kz0 : ℝ) - (kw0 : ℝ)| ≥ 1 := h_coord_diff_ge1 kz0 kw0 h
        have h7 : z 0 - w 0 = δ * ((kz0 : ℝ) - (kw0 : ℝ)) := by
          simp [hkz0, hkw0] <;> ring
        have h8 : |z 0 - w 0| ≥ δ := by
          rw [h7]
          have h_abs : |δ * ((kz0 : ℝ) - (kw0 : ℝ))| = |δ| * |(kz0 : ℝ) - (kw0 : ℝ)| := by rw [abs_mul]
          rw [h_abs]
          have h_absδ : |δ| = δ := abs_of_pos hδ_pos
          rw [h_absδ]
          have h91 : |(kz0 : ℝ) - (kw0 : ℝ)| ≥ 1 := h6
          have h9 : δ * |(kz0 : ℝ) - (kw0 : ℝ)| ≥ δ := by
            have h10 : δ * |(kz0 : ℝ) - (kw0 : ℝ)| ≥ δ * 1 := mul_le_mul_of_nonneg_left h91 hδ_pos.le
            simpa using h10
          exact h9
        exact le_trans h8 h_dist_coord0
      · -- kz1 ≠ kw1
        have h6 : |(kz1 : ℝ) - (kw1 : ℝ)| ≥ 1 := h_coord_diff_ge1 kz1 kw1 h
        have h7 : z 1 - w 1 = δ * ((kz1 : ℝ) - (kw1 : ℝ)) := by
          simp [hkz1, hkw1] <;> ring
        have h8 : |z 1 - w 1| ≥ δ := by
          rw [h7]
          have h_abs : |δ * ((kz1 : ℝ) - (kw1 : ℝ))| = |δ| * |(kz1 : ℝ) - (kw1 : ℝ)| := by rw [abs_mul]
          rw [h_abs]
          have h_absδ : |δ| = δ := abs_of_pos hδ_pos
          rw [h_absδ]
          have h91 : |(kz1 : ℝ) - (kw1 : ℝ)| ≥ 1 := h6
          have h9 : δ * |(kz1 : ℝ) - (kw1 : ℝ)| ≥ δ := by
            have h10 : δ * |(kz1 : ℝ) - (kw1 : ℝ)| ≥ δ * 1 := mul_le_mul_of_nonneg_left h91 hδ_pos.le
            simpa using h10
          exact h9
        exact le_trans h8 h_dist_coord1
    exact h_dist_ge

  -- =====================================================================
  -- Step 6: Helper6 — glue_h5_to_h6
  -- =====================================================================

  -- Convert h_multiplicity (uses rcases c_mult) to explicit formula before local let shadows c_mult
  have h_multiplicity_exp : ∀ p ∈ Pbar_param,
      ENat.toENNReal ({y ∈ Y | p ∈ T_y_points y}.encard) ≥
        ENNReal.ofReal (δ ^ (η_work / 2) / (14 * (35 * C) ^ 2)) * ENat.toENNReal Y.encard := by
    intro p hp
    have h := h_multiplicity p hp
    have h_eq : c_mult / 2 = δ ^ (η_work / 2) / (14 * (35 * C) ^ 2) := by
      rw [hc_mult_eq2] <;> ring
    rw [h_eq] at h
    exact h

  -- Redefine c_mult locally (from Phase0 definition)
  let c_mult : ℝ := δ ^ (η_work / 2) / (7 * C_work' ^ 2)
  have hc_mult_pos : 0 < c_mult := by positivity
  have hc_mult_eq : c_mult = δ ^ (η_work / 2) / (7 * C_work' ^ 2) := by rfl

  -- Operator correction: c_endgame = c_mult / 2
  let c_endgame : ℝ := c_mult / 2
  let ε_mass : ℝ := 3 * η_work / 2 + η_work / 100

  have hc_endgame_pos : 0 < c_endgame := by
    dsimp only [c_endgame] <;> linarith [hc_mult_pos]
  have hc_endgame_eq_exp : c_endgame = δ ^ (η_work / 2) / (14 * (35 * C) ^ 2) := by
    dsimp only [c_endgame, c_mult]
    rw [hC_work'_eq] <;> ring
  have hc_endgame_le_one : c_endgame ≤ 1 := by
    dsimp only [c_endgame]
    have h1 : c_mult ≤ 1 := by
      dsimp only [c_mult]
      have h2 : δ ^ (η_work / 2) < 1 := Real.rpow_lt_one hδ_pos.le hδ_lt_one (by linarith)
      have h4 : C_work' ≥ 1 := by
        rw [hC_work'_eq]
        have h5 : C ≥ 1 := hC_ge1
        have h6 : (35 : ℝ) * C ≥ 1 := by
          calc (35 : ℝ) * C ≥ (35 : ℝ) * 1 := by gcongr
            _ ≥ 1 := by norm_num
        exact h6
      have h5 : (7 : ℝ) * C_work' ^ 2 ≥ 1 := by
        have h6 : C_work' ^ 2 ≥ 1 := by
          have h7 : C_work' ^ 2 ≥ 1 ^ 2 := by gcongr
          simpa using h7
        calc (7 : ℝ) * C_work' ^ 2 ≥ (7 : ℝ) * 1 := by gcongr
          _ ≥ 1 := by norm_num
      have h_pos : 0 < (7 : ℝ) * C_work' ^ 2 := by positivity
      have h_div : δ ^ (η_work / 2) / (7 * C_work' ^ 2) < 1 / (7 * C_work' ^ 2) := by
        apply div_lt_div_of_pos_right h2 h_pos
      have h_final : 1 / (7 * C_work' ^ 2) ≤ 1 := by
        apply (div_le_one h_pos).mpr
        exact h5
      have h6 : δ ^ (η_work / 2) / (7 * C_work' ^ 2) < 1 := by
        calc δ ^ (η_work / 2) / (7 * C_work' ^ 2)
          < 1 / (7 * C_work' ^ 2) := h_div
        _ ≤ 1 := h_final
      exact h6.le
    linarith only [h1]
  have hε_mass_pos : 0 < ε_mass := by
    dsimp only [ε_mass] <;> positivity

  -- Budget parameters (CORRECTED: full sum for q_graph_total, proper ηProj)
  set q_graph_total : ℝ := qInitV3 η_work rho_sel + 2 * rho_sep +
      qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep +
      qAbsorb η_work + qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep
    with hq_graph_total
  let q_size : ℝ := qSizeLossV3
  let ζ_dir : ℝ := ζDir p_projective ε κ0
  let η_proj : ℝ := ηProj L_exp η ε κ0 p_projective

  have hp_nonneg : 0 ≤ p_projective := by
    have h10 : (10 : ℝ) ≤ p_projective := hp_ge_10
    exact le_of_lt (lt_of_lt_of_le (by norm_num) h10)
  have h_q_graph_total_nonneg : 0 ≤ q_graph_total :=
    q_graph_total_nonneg
      (hL_exp_pos := hL_exp_pos) (hη_work_pos := hη_work_pos)
      (hε_pos := hε_pos) (hκ0_pos := hkappa_pos)
      (hp_nonneg := hp_nonneg)
      (hτ_pos := hτ_pos)
      (hrho_sel_nonneg := hrho_sel_pos.le)
      (hrho_sep_nonneg := hrho_sep_pos.le)
  have h_q_diff_nonneg : 0 ≤ q_diff :=
    qDiffV4_nonneg (hL_exp_pos := hL_exp_pos) (hη_work_pos := hη_work_pos)
      (hε_pos := hε_pos) (hκ0_pos := hkappa_pos)
      (hp_nonneg := hp_nonneg) (hτ_pos := hτ_pos)
      (hrho_sel_nonneg := hrho_sel_pos.le) (hrho_sep_nonneg := hrho_sep_pos.le)
  have h_q_size_nonneg : 0 ≤ q_size :=
    qSizeLossV4_nonneg (hL_exp_pos := hL_exp_pos) (hη_work_pos := hη_work_pos)
      (hε_pos := hε_pos) (hκ0_pos := hkappa_pos)
      (hp_nonneg := hp_nonneg) (hτ_pos := hτ_pos)
      (hrho_sel_nonneg := hrho_sel_pos.le) (hrho_sep_nonneg := hrho_sep_pos.le)
  have hζ_dir_nonneg : 0 ≤ ζ_dir := by
    dsimp only [ζ_dir, ζDir, qProjective] <;> positivity
  have hη_proj_nonneg : 0 ≤ η_proj := by
    dsimp only [η_proj, ηProj, qProjective] <;> positivity

  -- Graph constants (CORRECTED: C_raw=4, C_Pbar=4 per operator)
  let C_raw : ℝ := 4
  let C_Pbar_h6 : ℝ := 4
  let c_proj : ℝ := δ ^ q_graph_total
  let K_work : ℝ := K_ring

  have hC_raw_pos : 0 < C_raw := by norm_num
  have hC_Pbar_pos : 0 < C_Pbar_h6 := by norm_num
  have hc_proj_pos : 0 < c_proj := by positivity
  have hεgain_pos : 0 < εgain := by
    have h10 : 0 ≤ qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep :=
      qTotalV4_nonneg hL_exp_pos hη_work_pos hε_pos hkappa_pos
        (by linarith [hp_ge_10]) hτ_pos hrho_sel_nonneg hrho_sep_nonneg
    have h12 : εgain > qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := h_budget
    linarith only [h10, h12]
  have hc_proj_ge : c_proj ≥ δ ^ q_graph_total := by rfl
  have hK_work_ge1 : 1 ≤ K_work := hK_ring_ge1

  -- Direction transport (CORRECTED: L_chart = δ^(-2*q_pole))
  let q_pole : ℝ := rho_sep
  let C_ν_h6 : ℝ := 3 * C * (2 : ℝ)^τ
  let L_chart : ℝ := δ ^ (-2 * q_pole)

  have hq_pole_pos : 0 < q_pole := hrho_sep_pos
  have hC_ν_pos : 0 < C_ν_h6 := by
    dsimp only [C_ν_h6] <;> positivity
  have hL_chart_pos : 0 < L_chart := by
    dsimp only [L_chart] <;> positivity
  have hL_chart_ge_one : 1 ≤ L_chart := by
    dsimp only [L_chart]
    have h1 : δ ^ (0 : ℝ) = (1 : ℝ) := by simp
    have h2 : δ ^ (0 : ℝ) ≤ δ ^ (-2 * q_pole) :=
      Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le (by linarith)
    rw [h1] at h2
    exact h2
  have hL_chart_ge : L_chart ≥ δ ^ (-2 * q_pole) := by
    have h_eq : L_chart = δ ^ (-2 * q_pole) := by exact rfl
    rw [h_eq]
  -- Budget component equalities for bridges
  have h_q_graph_total_eq : q_graph_total = qInitV3 η_work rho_sel + 2 * rho_sep +
      qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep +
      qAbsorb η_work + qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by rfl
  have h_q_diff_eq : q_diff = qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by rfl
  have h_q_size_eq : q_size = qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
    dsimp only [q_size, qSizeLossV3] <;> rfl
  have h_ζ_dir_eq : ζ_dir = ζDir p_projective ε κ0 := by rfl
  have h_η_proj_eq : η_proj = ηProj L_exp η ε κ0 p_projective := by rfl
  have h_delta_small : δ ^ (εgain - (q_graph_total + 2 * q_diff + q_size + η + ζ_dir + η_proj)) ≤ 1 / 64 :=
    delta_small_from_dir64_v4
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hη_work_pos := hη_work_pos) (hη_pos := hη_pos)
      (by linarith [hη_work_eq_two])
      (hL_exp_nonneg := by linarith)
      (hε_pos := hε_pos) (hκ0_pos := hkappa_pos)
      (hp_pos := by linarith) (hτ_pos := hτ_pos)
      (hrho_sel_nonneg := by linarith) (hrho_sep_nonneg := by linarith)
      (h_budget := h_budget) (h_dir_64 := h_dir_64)
      q_graph_total q_diff q_size ζ_dir η_proj
      h_q_graph_total_eq h_q_diff_eq h_q_size_eq h_ζ_dir_eq h_η_proj_eq
  have h_proj_budget : (L_exp - 1 / 2 : ℝ) * η < ζ_dir + η_proj :=
    proj_budget_v4 (hL_exp_nonneg := by linarith) (hη_pos := hη_pos)
      (hε_pos := hε_pos) (hκ0_pos := hkappa_pos) (hp_pos := by linarith)

  -- h_factor_absorb via factor_absorb_simple (C_raw=4, C_Pbar=4)
  have h_e_ge : ζ_dir + η_proj - (L_exp - 1 / 2 : ℝ) * η ≥ η_work / 100 := by
    have h2 : 0 < qProjective p_projective ε κ0 := by dsimp only [qProjective]; positivity
    have h3 : ζ_dir + η_proj - (L_exp - 1 / 2 : ℝ) * η = 2 * qProjective p_projective ε κ0 + η / 2 := by
      dsimp only [ζ_dir, η_proj, ζDir, ηProj, qProjective] <;> ring
    rw [h3]
    have h4 : η = η_work / 2 := by linarith [hη_work_eq_two]
    rw [h4]; linarith [h2]
  have h_factor_absorb : 6 * C_raw * Real.sqrt C_Pbar_h6 * δ ^ (ζ_dir + η_proj - (L_exp - 1 / 2 : ℝ) * η) < 1 :=
    factor_absorb_simple (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (he_ge := h_e_ge) (h_box_bound := h_box_bound)
  -- hY_mass: ν Y = 1 ≥ δ^ε_mass
  have hY_mass : ν Y ≥ ENNReal.ofReal (δ ^ ε_mass) := by
    have h1 : ν Y = 1 := by
      have h_supp : ν.support = Y := hν_support_eq
      have h2 : ν (ν.support) = ν Set.univ := by
        have h3 : ν ((ν.support)ᶜ) = 0 := MeasureTheory.Measure.measure_compl_support
        have h_ms : MeasurableSet (ν.support) := by
          have h_closed : IsClosed (ν.support) := MeasureTheory.Measure.isClosed_support
          exact h_closed.measurableSet
        have h4 : ν (ν.support ∪ (ν.support)ᶜ) = ν (ν.support) + ν ((ν.support)ᶜ) := by
          rw [measure_union' disjoint_compl_right h_ms]
        have h5 : ν.support ∪ (ν.support)ᶜ = (Set.univ : Set ℝ) := by simp
        rw [h5] at h4
        rw [h3] at h4
        simpa using h4.symm
      have h6 : ν Y = ν Set.univ := by
        rw [← h_supp]
        exact h2
      have h7 : ν Set.univ = 1 := h_dir_frostman.1
      rw [h6, h7]
    rw [h1]
    have h3 : δ ^ ε_mass < 1 := Real.rpow_lt_one hδ_pos.le hδ_lt_one hε_mass_pos
    have h4 : ENNReal.ofReal (δ ^ ε_mass) ≤ 1 := by
      rw [ENNReal.ofReal_le_one] <;> linarith
    exact h4
  -- hPbar_small: weaken from coeff-1 to C_Pbar_h6=4
  have hPbar_small : ENat.toENNReal (dyadicCoveringNumber δ Pbar_param) <
      ENNReal.ofReal (C_Pbar_h6 * δ ^ (-(2 * s + η))) := by
    have h1 : ENat.toENNReal (dyadicCoveringNumber δ Pbar_param) = Nplane δ Pbar_param := by rfl
    rw [h1]
    have h2 : Nplane δ Pbar_param < ENNReal.ofReal (δ ^ (-(2 * s + η))) := hPbar_small_coeff1
    have h3 : (1 : ℝ) ≤ C_Pbar_h6 := by norm_num
    have hpos : 0 ≤ δ ^ (-(2 * s + η)) := by positivity
    have h4 : ENNReal.ofReal (δ ^ (-(2 * s + η))) ≤
        ENNReal.ofReal (C_Pbar_h6 * δ ^ (-(2 * s + η))) := by
      apply ENNReal.ofReal_le_ofReal
      have h5 : 0 ≤ δ ^ (-(2 * s + η)) := by positivity
      have h6 : δ ^ (-(2 * s + η)) ≤ C_Pbar_h6 * δ ^ (-(2 * s + η)) := by
        calc
          δ ^ (-(2 * s + η)) = 1 * δ ^ (-(2 * s + η)) := by ring
          _ ≤ C_Pbar_h6 * δ ^ (-(2 * s + η)) := by gcongr <;> norm_num
      exact h6
    exact lt_of_lt_of_le h2 h4
  -- Save coefficient-1 version before shadowing
  have h_raw_proj_bound_coeff1 := h_raw_proj_bound
  have h_raw_proj_bound : ∀ y ∈ Y,
      Nreal δ (Set.image (fun q : EuclideanSpace ℝ (Fin 2) => q 0 * y + q 1) (T_y_points y)) ≤
      ENNReal.ofReal C_raw * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar_param)).toReal)) := by
    intro y hy
    have h := h_raw_proj_bound y hy
    have hNplane_eq : ENat.toENNReal (dyadicCoveringNumber δ Pbar_param) = Nplane δ Pbar_param := by rfl
    rw [hNplane_eq]
    have h5 : (1 : ENNReal) ≤ ENNReal.ofReal C_raw := by norm_num
    have h6 : ENNReal.ofReal (δ ^ (-(L_exp * η))) * ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) ≤
        ENNReal.ofReal C_raw * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) := by
      calc ENNReal.ofReal (δ ^ (-(L_exp * η))) * ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal))
        = (1 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
            ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) := by simp
      _ ≤ ENNReal.ofReal C_raw * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
            ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) := by gcongr
    exact le_trans h h6
  -- h_mass_budget via mass_budget_bridge
  have hC_work'_le2 : C_work' ≤ 35 * δ ^ (-η_work / 2) := by
    have h1 : C_work' = 35 * C := hC_work'_eq
    have h2 : C ≤ δ ^ (-η) := hC_le_target
    have h3 : η = η_work / 2 := by linarith [hη_work_eq_two]
    have h4 : C ≤ δ ^ (-η_work / 2) := by
      have h5 : (-η : ℝ) = -η_work / 2 := by
        have h6 : η = η_work / 2 := by linarith [hη_work_eq_two]
        linarith only [h6]
      have h2' : C ≤ δ ^ (-η) := hC_le_target
      rw [h5] at h2'
      exact h2'
    calc
      C_work' = 35 * C := h1
      _ ≤ 35 * δ ^ (-η_work / 2) := by gcongr
  have h_mass_budget : δ ^ ε_mass ≤ c_endgame / 2 := by
    have h := mass_budget_bridge
      (hδ_pos := hδ_pos)
      (_hδ_lt_one := hδ_lt_one)
      (_hη_work_pos := hη_work_pos)
      (hC_work'_pos := hC_work'_pos) (hC_work'_le := hC_work'_le2)
      (hc_mult_def := by dsimp only [c_mult] <;> rfl)
      (hε_mass_def := by dsimp only [ε_mass] <;> ring)
      (h_box_bound := h_box_bound)
    have h4 : c_endgame / 2 = c_mult / 4 := by
      dsimp only [c_endgame] <;> ring
    rw [h4]
    exact h
  have h_chartFullLambda_bound : ∀ (i : Fin 4) (y : ℝ), sectorPredicate i x y →
      |chartFullLambda i y θ1 θ3 θ2 x| ≤ 1 :=
    chart_full_lambda_bound_bridge
      (hδ_pos := hδ_pos)
      (hθ1_lt_θ3 := hθ1_lt_θ3)
      (hθ3_lt_θ2 := hθ3_lt_θ2)
      (hθ1_in_Icc := hθ1_in_Icc)
      (hθ2_in_Icc := hθ2_in_Icc)
      (hx_formula := hx_eq)
  have hν_uniform : ∀ y ∈ Y, ν {y} = ENNReal.ofReal (1 / (Y.ncard : ℝ)) := hν_point_mass

  -- Resolution A translation vector
  let v_resA : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 (fun i : Fin 2 =>
      if i = 0 then (k : ℝ) / (θ3 - θ1) - (j : ℝ) / (θ2 - θ3)
      else -(k : ℝ) * θ1 / (θ3 - θ1) + (j : ℝ) * θ2 / (θ2 - θ3))
  have hv0 : v_resA 0 = (k : ℝ) / (θ3 - θ1) - (j : ℝ) / (θ2 - θ3) := by
    simp [v_resA]
  have hv1 : v_resA 1 = -(k : ℝ) * θ1 / (θ3 - θ1) + (j : ℝ) * θ2 / (θ2 - θ3) := by
    simp [v_resA]

  -- Normalized (translated) point sets and Pbar
  let T_y_points' : ℝ → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun y => (fun q => q - v_resA) '' T_y_points y
  let Pbar_param' : Set (EuclideanSpace ℝ (Fin 2)) :=
    (fun q => q - v_resA) '' Pbar_param

  -- S_pre uses normalized point sets
  let S_pre : ℝ → Set ℝ := fun y =>
    if y = θ2 then Set.univ
    else intervalThicken (δ * (1 + |x y|) / 2)
      (phase7ScaledProjection y θ2 θ3 (T_y_points' y))

  -- S_pre_orig uses original point sets
  let S_pre_orig : ℝ → Set ℝ := fun y =>
    if y = θ2 then Set.univ
    else intervalThicken (δ * (1 + |x y|) / 2)
      (phase7ScaledProjection y θ2 θ3 (T_y_points y))

  have hT'_eq : ∀ y, T_y_points' y = (fun q => q - v_resA) '' T_y_points y := by
    intro y; rfl

  -- hS_pre_shift via Resolution A identity
  have hS_pre_shift : ∀ y, S_pre y = {z | z + (k : ℝ) * x y + (j : ℝ) ∈ S_pre_orig y} :=
    spre_shift_bridge
      (h_ord13 := hθ1_lt_θ3) (h_ord32 := hθ3_lt_θ2)
      (hv0 := hv0) (hv1 := hv1)
      (hx_formula := hx_eq)
      (T_y_points := T_y_points) (T_y_points' := T_y_points')
      (hT'_eq := hT'_eq)
      (r := fun y => δ * (1 + |x y|) / 2)

  have hG_orig_sub_Gamma : G_orig ⊆ Gamma := Set.Subset.trans hG_orig_sub hG'_sub_Gamma

  -- h_mult_orig via mult_orig_bridge (uses original T_y_points)
  -- Convert h_multiplicity_exp to use c_endgame
  have h_multiplicity' : ∀ p ∈ Pbar_param,
      ENat.toENNReal ({y ∈ Y | p ∈ T_y_points y}.encard) ≥
        ENNReal.ofReal c_endgame * ENat.toENNReal Y.encard := by
    intro p hp
    have h := h_multiplicity_exp p hp
    rw [hc_endgame_eq_exp]
    exact h

  -- Convert h_round_near to expected direction
  have h_round_near' : ∀ t : ℝ, |round_fun t - t| ≤ δ / 2 := by
    intro t
    have h := h_round_near t
    have h' : |round_fun t - t| = |t - round_fun t| := by rw [abs_sub_comm]
    rw [h']
    exact h

  have h_mult_orig : ∀ g ∈ Gamma,
      ({y ∈ hY_fin.toFinset | g 0 * x y + g 1 ∈ S_pre_orig y}.card : ℝ)
        ≥ c_endgame * hY_fin.toFinset.card :=
    mult_orig_bridge
      (_hδ_pos := hδ_pos)
      (hY_fin := hY_fin)
      (h_ord13 := hθ1_lt_θ3) (h_ord32 := hθ3_lt_θ2)
      (hx_formula := hx_eq)
      (hF_formula := hF_formula)
      (h_round_near := h_round_near')
      (c_mult_dir := c_endgame)
      (hc_mult_dir_pos := hc_endgame_pos)
      (hGamma_witness := hGamma_from_E3'')
      (hE3''_sub_F := by
      have h_sub : E3'' ⊆ E3' := hE3''_sub
      have h_eq : E3' = F '' E3 := hE3'_eq
      rw [h_eq] at h_sub
      exact h_sub)
      (hE3_sub_Pbar := hE3_sub_Pbar)
      (h_multiplicity_points := h_multiplicity')
      (S_pre_orig := S_pre_orig)
      (hS_pre_orig_def := fun y => by
        simp only [S_pre_orig]
        <;> rfl)

  have hc_proj_nonneg : 0 ≤ c_proj := by positivity

  -- h_budget: from outer h_budget (εgain > qTotalV4) and qTotalV4 ≥ RHS
  have h_budget : εgain > q_graph_total + 2 * q_diff + q_size + η + ζ_dir + η_proj :=
    budget_total_lemma
      (hL_exp_pos := hL_exp_pos)
      (hη_work_pos := hη_work_pos)
      (hη_pos := hη_pos)
      (hη_work_eq_two := hη_work_eq_two)
      (hε_pos := hε_pos)
      (hκ0_pos := hkappa_pos)
      (hp_ge_10 := hp_ge_10)
      (hτ_pos := hτ_pos)
      (hrho_sel_pos := hrho_sel_pos)
      (hrho_sep_pos := hrho_sep_pos)
      (hq_graph_total_eq := by rfl)
      (hq_diff_eq := by rfl)
      (hq_size_eq := by rfl)
      (hζ_dir_eq := by rfl)
      (hη_proj_eq := by rfl)
      (h_outer := h_budget)
  have h_proj_budget : (L_exp - 1 / 2 : ℝ) * η < ζ_dir + η_proj := by
    have hL_exp_nonneg : 0 ≤ L_exp := by linarith [hL_exp_pos]
    exact proj_budget_v4 hL_exp_nonneg hη_pos hε_pos hkappa_pos (show 0 < p_projective from by linarith [hp_ge_10])

  have hPbar_bdd : IsBounded Pbar_param := hPbar_bounded

  have hν_frost : IsDirectionFrostman δ τ C_ν_h6 ν := by
    have h1 : C_ν_h6 = 3 * C * (2 : ℝ)^τ := by dsimp only [C_ν_h6] <;> ring
    rw [h1]
    exact h_dir_frostman

  have hY_sub_unit : Y ⊆ Set.Icc 0 1 := by
    intro y hy
    have h : y ∈ productLikeUnitGrid δ := hY_sub hy
    exact h.2

  have hT_sub : ∀ y ∈ Y, T_y_points y ⊆ Pbar_param := hT_y_points_sub

  -- Translation bounds for normalized sets
  have hPbar_small' : ENat.toENNReal (dyadicCoveringNumber δ Pbar_param') <
      ENNReal.ofReal (4 * δ ^ (-(2 * s + η))) :=
    pbar_small_normalized_bridge
      (hδ_pos := hδ_pos)
      (v := -v_resA)
      (hPbar'_eq := by dsimp only [Pbar_param']; rfl)
      (hPbar_bdd := hPbar_bdd)
      (hPbar_small := hPbar_small_coeff1)
  have hPbar'_ne_top : ENat.toENNReal (dyadicCoveringNumber δ Pbar_param') ≠ ⊤ := by
    intro h
    rw [h] at hPbar_small'
    simpa using hPbar_small'
  have h_raw_proj_bound' : ∀ y ∈ Y,
      Nreal δ (Set.image (fun q : EuclideanSpace ℝ (Fin 2) => q 0 * y + q 1) (T_y_points' y)) ≤
      ENNReal.ofReal (4 : ℝ) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar_param')).toReal)) := by
    intro y hy
    have hT_bdd : IsBounded (T_y_points y) :=
      IsBounded.subset hPbar_bdd (hT_y_points_sub y hy)
    exact raw_proj_bound_normalized_bridge
      (hδ_pos := hδ_pos)
      (v := -v_resA)
      (hT'_eq := hT'_eq y)
      (hPbar'_eq := by dsimp only [Pbar_param']; rfl)
      (hT_bdd := hT_bdd)
      (hPbar_bdd := hPbar_bdd)
      (hPbar'_ne_top := hPbar'_ne_top)
      (h_raw_proj_bound := h_raw_proj_bound_coeff1 y hy)

  -- hB1_upper, hB2_upper via upstream projection + box absorption
  have h_enc_ge_B : εnc ≥ (L_exp + 1 / 2 : ℝ) * η + η_work / 100 :=
    enc_ge_B_lemma
      (hL_exp_eq_seven := hL_exp_eq_seven)
      (hη_work_pos := hη_work_pos)
      (hη_pos := hη_pos)
      (hη_work_eq_two := hη_work_eq_two)
      (h_qTotalV4_le_enc4 := by linarith [h_qTotalV4_le_enc4])
      (hε_pos := hε_pos)
      (hκ0_pos := hkappa_pos)
      (hp_nonneg := hp_nonneg)
      (hτ_pos := hτ_pos)
      (hrho_sel_nonneg := hrho_sel_nonneg)
      (hrho_sep_nonneg := hrho_sep_nonneg)
  have h_box_B : δ ^ (η_work / 100) ≤ 1 / (12 : ℝ) := by
    have h1 : δ ^ (η_work / 100) ≤ 1 / (2 ^ 20 : ℝ) := by
      have h2 : 0 < δ ^ (η_work / 100) := by positivity
      have h3 : (2 ^ 20 : ℝ) ≤ δ ^ (-(η_work / 100)) := h_box_bound
      have h4 : δ ^ (-(η_work / 100)) = 1 / δ ^ (η_work / 100) := by
        rw [Real.rpow_neg hδ_pos.le] <;> ring
      rw [h4] at h3
      have h5 : δ ^ (η_work / 100) ≤ 1 / (2 ^ 20 : ℝ) := by
        field_simp [h2.ne'] at h3 ⊢ <;> linarith
      exact h5
    have h6 : (1 : ℝ) / (2 ^ 20 : ℝ) ≤ 1 / (12 : ℝ) := by norm_num
    exact le_trans h1 h6
  have h_absorb_B : (12 : ℝ) * δ ^ (εnc - (L_exp + 1 / 2 : ℝ) * η) ≤ K_work := by
    have h1 : (12 : ℝ) * δ ^ (εnc - (L_exp + 1 / 2 : ℝ) * η) ≤ 1 :=
      box_bound_absorption (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
        (hC_pos := by norm_num) (hη_work_pos := hη_work_pos)
        (h_enc_ge := h_enc_ge_B) (h_box := h_box_B)
    have h2 : (1 : ℝ) ≤ K_work := hK_work_ge1
    linarith only [h1, h2]
  have hS1_bound1 : Nreal δ S1 ≤ (6 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
      ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) := by
    calc Nreal δ S1
      ≤ (3 : ENNReal) * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0) E3') := hS1_bound
    _ ≤ (3 : ENNReal) * ((2 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal))) := by gcongr
    _ = (6 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) := by simp [mul_assoc] <;> ring
  have hS1_upper_B : Nreal δ S1 ≤ ENNReal.ofReal ((12 : ℝ) * δ ^ (-(s + (L_exp + 1 / 2 : ℝ) * η))) :=
    s_upper_bound_lemma (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hS_bound := hS1_bound1) (hPbar_small := hPbar_small)
  have hB1_upper : Nreal δ B1_norm ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))) :=
    normalized_size_upper_bound
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hB_norm_transfer := hB1_norm_size_upper)
      (hS_upper := hS1_upper_B)
      (hd_def := by ring)
      (hd_nonneg := by linarith [h_enc_ge_B])
      (hC_pos := by norm_num)
      (hK_work_pos := by positivity)
      (h_absorb := h_absorb_B)
  have hS2_bound1 : Nreal δ S2 ≤ (6 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
      ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) := by
    calc Nreal δ S2
      ≤ (3 : ENNReal) * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 1) E3') := hS2_bound
    _ ≤ (3 : ENNReal) * ((2 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal))) := by gcongr
    _ = (6 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) := by simp [mul_assoc] <;> ring
  have hS2_upper_B : Nreal δ S2 ≤ ENNReal.ofReal ((12 : ℝ) * δ ^ (-(s + (L_exp + 1 / 2 : ℝ) * η))) :=
    s_upper_bound_lemma (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hS_bound := hS2_bound1) (hPbar_small := hPbar_small)
  have hB2_upper : Nreal δ B2_norm ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))) :=
    normalized_size_upper_bound
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hB_norm_transfer := hB2_norm_size_upper)
      (hS_upper := hS2_upper_B)
      (hd_def := by ring)
      (hd_nonneg := by linarith [h_enc_ge_B])
      (hC_pos := by norm_num)
      (hK_work_pos := by positivity)
      (h_absorb := h_absorb_B)

  -- Absorption bridges
  have hτ_le_one : τ ≤ 1 := by
    simp only [IsProductLikeRealDeltaSCSet, IsDeltaSCSet] at hY_delta
    exact_mod_cast hY_delta.2.2.2.2.2.2.1
  have hqBox_nonneg : 0 ≤ qBox η_work τ := by
    dsimp only [qBox, qAbsorb]; positivity
  have hR_norm_nonneg : 0 ≤ R_norm := le_of_lt hR_norm_pos
  have h2R_norm_le : 2 * R_norm ≤ δ ^ (-(qBox η_work τ)) := by
    have h : 2 * R_norm = 4 * R := by
      dsimp only [R_norm] <;> ring
    rw [h]
    exact h4R_le_qbox
  have hM_ret_eq' : M_ret = (2 * R_norm + 3) * (3 ^ 10 : ℝ) / δ ^ (10 * q_K) := by
    rw [hM_ret_eq] <;> ring
  have h_retention : c_ret / M_ret ≥
      δ ^ (32 * q_K + qBox η_work τ) / ((256 : ℝ) * (3 ^ 32 : ℝ)) :=
    retention_ratio_lower
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hq_K_pos := hq_K_pos)
      (hqBox_nonneg := hqBox_nonneg)
      (hR_norm_nonneg := hR_norm_nonneg)
      (hM_ret_eq := hM_ret_eq')
      (hc_ret_eq := by dsimp only [c_ret] <;> ring)
      (h2R_norm_le := h2R_norm_le)
  have h_qAbsorb_threshold : δ ^ (qAbsorb η_work) ≤ 1 / ((256 : ℝ) * (3 ^ 32 : ℝ)) :=
    qabsorb_threshold (hδ_pos := hδ_pos) (h_KBSG_absorb := h_KBSG_absorb)
  have h_size_absorb : c_ret / M_ret * δ ^ (-s + q_input) ≥ δ ^ (-s + q_size) :=
    bridge_size_absorb
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hC_pos := by norm_num)
      (hL_nonneg := by linarith [hL_exp_pos])
      (hη_work_pos := hη_work_pos)
      (hε_pos := hε_pos)
      (hκ0_pos := hkappa_pos)
      (hp_nonneg := by linarith [hp_ge_10])
      (hτ_pos := hτ_pos)
      (hrho_sel_nonneg := hrho_sel_nonneg)
      (hrho_sep_nonneg := hrho_sep_nonneg)
      (h_retention := h_retention)
      (h_qAbsorb_threshold := h_qAbsorb_threshold)

  have hR_ret_eq' : R_ret = (64 : ℝ) * (3 ^ 22 : ℝ) * (2 * R_norm + 3) * δ ^ (-22 * q_K) := by
    rw [hR_ret_eq]
    have h_pos : 0 < δ ^ (22 * q_K) := by positivity
    have h_pos2 : (0 : ℝ) < 16 * (3 ^ 22 : ℝ) := by positivity
    have h_eq : 4 * (2 * (R_norm + 1) + 1) = 4 * (2 * R_norm + 3) := by ring
    rw [h_eq]
    have h_div : (4 * (2 * R_norm + 3)) / (δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ))) =
        (64 : ℝ) * (3 ^ 22 : ℝ) * (2 * R_norm + 3) * δ ^ (-22 * q_K) := by
      have h1 : (4 * (2 * R_norm + 3)) / (δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ))) =
          (4 * (2 * R_norm + 3)) * (16 * (3 ^ 22 : ℝ)) / δ ^ (22 * q_K) := by
        field_simp [h_pos.ne', h_pos2.ne'] <;> ring
      rw [h1]
      have h3 : δ ^ (-22 * q_K) = (δ ^ (22 * q_K))⁻¹ := by
        have h4 : (-22 * q_K) = -(22 * q_K) := by ring
        rw [h4]
        exact Real.rpow_neg hδ_pos.le (22 * q_K)
      rw [h3]
      <;> field_simp [h_pos.ne'] <;> ring
    exact h_div
  have h_budget_ineq : εnc / 2 ≥ 32 * q_K + 2 * qAbsorb η_work + qBox η_work τ := by
    have h1 : εnc / 2 ≥ 2 * qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
      linarith [h_qTotalV4_le_enc4]
    have hqK_eq : q_K = qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by rfl
    have h2 : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≥
        32 * q_K + 2 * qAbsorb η_work + qBox η_work τ := by
      rw [hqK_eq]
      exact budget_ineq_v4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
        hL_exp_pos hη_work_pos hε_pos hkappa_pos (by linarith [hp_ge_10]) hτ_pos hrho_sel_pos hrho_sep_pos
    linarith [h1, h2]
  have h_threshold : δ ^ εnc ≤ K_work / (2 * C_BSG * R_ret) :=
    regularity_threshold
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hq_K_pos := hq_K_pos) (hεnc_pos := hεnc_pos)
      (hR_norm_nonneg := hR_norm_nonneg)
      (hK_ring_pos := by linarith only [hK_ring_ge1])
      (hC_A_eq := hC_extract_def)
      (hK_work_eq := by dsimp only [K_work] <;> rfl)
      (hC_BSG_eq := by simpa [θ_num] using hC_BSG_eq)
      (hR_ret_eq := hR_ret_eq')
      (h2R_norm_le := h2R_norm_le)
      (hqBox_nonneg := hqBox_nonneg)
      (h_KBSG_absorb := h_KBSG_absorb)
      (h_budget_ineq := h_budget_ineq)
  have h_reg_absorb : 2 * (C_BSG * R_ret) ≤ K_work * δ ^ (-εnc) :=
    bridge_reg_absorb
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hC_BSG_pos := hC_BSG_pos) (hR_ret_pos := hR_ret_pos)
      (hK_work_pos := by positivity)
      (hεnc_pos := hεnc_pos)
      (h_threshold := h_threshold)

  have hc_proj_le : c_proj ≤ (δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ))) * c_endgame / 8 :=
    graph_absorb_hc_proj_le
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hη_work_pos := hη_work_pos)
      (hκ0_pos := hkappa_pos)
      (hτ_pos := hτ_pos)
      (hrho_sel_nonneg := hrho_sel_nonneg)
      (hrho_sep_nonneg := hrho_sep_nonneg)
      (hq_K_eq := by rfl)
      (hq_graph_total_eq := h_q_graph_total_eq)
      (hc_endgame_eq := by
        dsimp only [c_endgame, c_mult] <;> ring)
      (hC_work'_pos := hC_work'_pos)
      (hC_work'_le := hC_work'_le)
      (hKBSG_absorb := h_KBSG_absorb)
  have h_graph_absorb : c_ret ≥ (2 / c_endgame) * c_proj :=
    bridge_graph_absorb_lower
      (hc_mult_dir_pos := hc_endgame_pos)
      (hD_pos := by positivity)
      (hc_ret_eq := by
        dsimp only [c_ret] <;> ring)
      (hc_proj_le := hc_proj_le)

  have h_sector_absorb : C_ν_h6 * δ ^ τ ≤ δ ^ ε_mass / 2 :=
    bridge_sector_absorb
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hη_work_pos := hη_work_pos)
      (hη_work_eq_two := hη_work_eq_two)
      (hτ_le_one := hτ_le_one)
      (h4η_work_lt_tau := h4η_work_lt_tau)
      (hε_mass_def := by dsimp only [ε_mass] <;> ring)
      (hC_Y_le := hC_le_target)
      (hC_ν_eq := by dsimp only [C_ν_h6] <;> ring)
      (h_box_bound := h_box_bound)

  have h_frostman_budget : C_ν_h6 * (8 : ℝ) * δ ^ (-ε_mass) * L_chart ^ τ ≤ K_work * δ ^ (-εnc) :=
    helper6_frostman_budget_bridge_v4
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hη_pos := hη_pos) (hη_work_pos := hη_work_pos)
      (hη_work_eq_two := hη_work_eq_two)
      (hτ_pos := hτ_pos) (hτ_le_one := hτ_le_one)
      (hε_pos := hε_pos) (hκ0_pos := hkappa_pos)
      (hp_nonneg := hp_nonneg)
      (hL_exp_eq_seven := hL_exp_eq_seven)
      (hrho_sel_nonneg := hrho_sel_pos.le)
      (hrho_sep_nonneg := hrho_sep_pos.le)
      (hε_mass_eq := by dsimp only [ε_mass] <;> ring)
      (hC_Y_le := hC_le_target)
      (hC_ν_pos := hC_ν_pos)
      (hC_ν_le := by
        have h_eq : C_ν_h6 = 3 * C * (2 : ℝ)^τ := by dsimp only [C_ν_h6] <;> ring
        exact le_of_eq h_eq)
      (hL_chart_eq := by dsimp only [L_chart, q_pole] <;> ring)
      (hK_work_ge1 := hK_work_ge1)
      (h_qTotalV4_le_enc4 := h_qTotalV4_le_enc4)
      (h_box_bound := h_box_bound)

  -- hS_pre_thick holds by equality (S_pre uses normalized T_y_points')
  have hS_pre_thick : ∀ y ∈ Y, y ≠ θ2 → S_pre y ⊆
      intervalThicken (δ * (1 + |x y|) / 2) (phase7ScaledProjection y θ2 θ3 (T_y_points' y)) := by
    intro y _ hy_ne
    have h : S_pre y = intervalThicken (δ * (1 + |x y|) / 2)
        (phase7ScaledProjection y θ2 θ3 (T_y_points' y)) := by
      simp only [S_pre, if_neg hy_ne]
    rw [h]
  have hx_formula : ∀ y, x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y)) := hx_eq

  -- Provide IsProbabilityMeasure instance for ν (needed by glue_h5_to_h6)
  haveI : IsProbabilityMeasure ν := ⟨h_dir_frostman.1⟩

  -- Rewrite rho_sel proof to match expected type
  have hrho_sel_pos' : 0 < rhoSelDefault η_work := by
    rw [← hrho_sel_eq]
    exact hrho_sel_pos

  -- Rewrite rho_sep proof to match expected type
  have hrho_sep_pos' : 0 < rhoSepDefault η_work κ0 := by
    dsimp only [rhoSepDefault]
    positivity

  -- Boundedness of translated Pbar
  have hPbar_bdd' : IsBounded Pbar_param' := by
    dsimp only [Pbar_param']
    have h_trans_lip : LipschitzWith 1 (fun q : EuclideanSpace ℝ (Fin 2) => q - v_resA) := by
      intro x y
      have h : dist (x - v_resA) (y - v_resA) = dist x y := by
        simp [dist_eq_norm] <;> abel
      have h' : edist (x - v_resA) (y - v_resA) = edist x y := by
        rw [edist_dist, edist_dist, h]
      rw [h']
      <;> simp [mul_one]
    exact h_trans_lip.isBounded_image hPbar_bounded

  -- Symmetry bridge: B2-B1 difference bound from B1-B2 bound
  have h_norm5_symm : Nreal δ (Set.image2 (· - ·) B2_norm B1_norm) ≤
      (2 : ENNReal) * ENNReal.ofReal (K_BSG_B2 * R_ret) * Nreal δ B2_norm :=
    symmetry_bridge_lemma
      (hδ_pos := hδ_pos)
      (hB1_norm_fin := hB1_norm_fin)
      (hB2_norm_fin := hB2_norm_fin)
      (hB1_norm_unit := hB1_norm_unit)
      (hB2_norm_unit := hB2_norm_unit)
      (K_BSG_B2 := K_BSG_B2)
      (R_ret := R_ret)
      (h_norm5 := h_norm5)

  -- Call glue_h5_to_h6 with all inputs
  exact glue_h5_to_h6
    (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one) (hδ_dyadic := hδ_dyadic)
    (hs_pos := hs_pos) (hs_lt_one := hs_lt_one) (hτ_pos := hτ_pos)
    (hkappa_pos := hkappa_pos) (hκ0_lt_s := hkappa_lt_s) (hκ0_le_tau := hκ0_le_tau)
    (hε_pos := hε_pos) (hε_mass_pos := hε_mass_pos) (hη_pos := hη_pos)
    (hη_work_pos := hη_work_pos) (hη_work_eq_two := hη_work_eq_two)
    (h10ε_lt_η_work := h10ε_lt_η_work)
    (h5η_work_lt := h5η_work_lt) (h4η_work_lt_tau := h4η_work_lt_tau)
    (hL_exp_pos := hL_exp_pos) (hL_exp_eq_seven := hL_exp_eq_seven)
    (hη_work_le_kappa0 := hη_work_le_kappa0) (hp_ge_10 := hp_ge_10)
    (q_graph_total := q_graph_total) (q_diff := q_diff) (q_size := q_size)
    (ζ_dir := ζ_dir) (η_proj := η_proj)
    (h_q_graph_total_nonneg := h_q_graph_total_nonneg)
    (h_q_diff_nonneg := h_q_diff_nonneg)
    (h_q_size_nonneg := h_q_size_nonneg)
    (hζ_dir_nonneg := hζ_dir_nonneg)
    (hη_proj_nonneg := hη_proj_nonneg)
    (h_budget := h_budget) (h_proj_budget := h_proj_budget)
    (hG_eta_work_le := hG_eta_work_le)
    (h_small_bsg := h_small_bsg)
    (hrho_sel_pos := hrho_sel_pos') (hrho_sep_pos := hrho_sep_pos')
    (C_raw := C_raw) (C_Pbar := C_Pbar_h6) (c_proj := c_proj) (K_work := K_work)
    (hC_raw_pos := hC_raw_pos) (hC_Pbar_pos := hC_Pbar_pos)
    (hc_proj_pos := hc_proj_pos) (hεgain_pos := hεgain_pos)
    (hc_proj_ge := hc_proj_ge)
    (h_delta_small := h_delta_small) (h_factor_absorb := h_factor_absorb)
    (q_pole := q_pole) (C_ν := C_ν_h6) (L_chart := L_chart)
    (hq_pole_pos := hq_pole_pos) (hC_ν_pos := hC_ν_pos)
    (hL_chart_pos := hL_chart_pos) (hL_chart_ge_one := hL_chart_ge_one)
    (hL_chart_ge := hL_chart_ge)
    (Y := Y) (ν := ν)
    (hν_frost := hν_frost)
    (hY_sub_unit := hY_sub_unit) (hY_fin := hY_fin)
    (hY_mass := hY_mass)
    (Pbar_param := Pbar_param') (hPbar_bdd := hPbar_bdd')
    (T_y_points := T_y_points') (hT_sub := by
      intro y hy
      have h : T_y_points' y ⊆ Pbar_param' := by
        intro q hq
        rcases hq with ⟨p, hp, rfl⟩
        exact ⟨p, hT_y_points_sub y hy hp, rfl⟩
      exact h)
    (θ1 := θ1) (θ2 := θ2) (θ3 := θ3)
    (hθ1_in_Icc := hθ1_in_Icc) (hθ2_in_Icc := hθ2_in_Icc) (hθ3_in_Icc := hθ3_in_Icc)
    (h_ord13 := hθ1_lt_θ3) (h_ord32 := hθ3_lt_θ2)
    (h_sep13 := h_sep13) (h_sep23 := h_sep23)
    (x := x) (hx_formula := hx_formula)
    (S_pre := S_pre) (hS_pre_thick := hS_pre_thick)
    (h_raw_proj_bound := h_raw_proj_bound')
    (c_mult_dir := c_endgame) (hc_mult_dir_pos := hc_endgame_pos) (hc_mult_dir_le_one := hc_endgame_le_one)
    (hν_uniform := hν_uniform)
    (h_mass_budget := h_mass_budget)
    (h_ring_spec := h_ring_spec)
    (hK_work_ge1 := hK_work_ge1)
    (hPbar_small := hPbar_small')
    (h_sector_absorb := h_sector_absorb)
    (h_frostman_budget := h_frostman_budget)
    (h_chartFullLambda_bound := h_chartFullLambda_bound)
    (B1_norm := B1_norm) (B2_norm := B2_norm)
    (G' := G') (G_norm := G_norm) (G_orig := G_orig)
    (C_BSG := C_BSG) (K_BSG := K_BSG) (K_BSG_B2 := K_BSG_B2)
    (R_ret := R_ret) (M_ret := M_ret)
    (k := k) (j := j)
    (hB1_grid := hB1_norm_unit) (hB2_grid := hB2_norm_unit)
    (hB1_nonempty := hB1_norm_nonempty) (hB2_nonempty := hB2_norm_nonempty)
    (hB1_finite := hB1_norm_fin) (hB2_finite := hB2_norm_fin)
    (hB1_sep := hB1_norm_sep) (hB2_sep := hB2_norm_sep)
    (hG_norm_finite := hG_norm_fin)
    (hG_norm_grid := hG_norm_grid)
    (hG_norm_sub := hG_norm_sub)
    (hG_orig_sub := hG_orig_sub)
    (h_norm_shift := hG'_witness)
    (hG_norm_separated := hG_norm_separated)
    (c_ret := c_ret) (hc_ret_nonneg := hc_ret_nonneg)
    (h_density_ncard := h_density_ncard)
    (hM_ret_pos := hM_ret_pos)
    (hC_BSG_pos := hC_BSG_pos) (hR_ret_pos := hR_ret_pos)
    (hB1_delta := hB1_norm_delta) (hB2_delta := hB2_norm_delta)
    (h_diff_B1B1_raw := h_norm1)
    (h_diff_B2B1_over_B1_raw := h_norm2)
    (h_sum_B1B2_over_B1_raw := h_norm3)
    (h_diff_B2B2_raw := h_norm4)
    (h_diff_B2B1_over_B2_raw := h_norm5_symm)
    (h_sum_B1B2_over_B2_raw := h_norm6)
    (q_input := q_input)
    (S1 := S1) (S2 := S2)
    (hS1_finite := hS1_finite) (hS2_finite := hS2_finite)
    (hS1_lower_encard := hS1_lower) (hS2_lower_encard := hS2_lower)
    (h_retention1 := h_retention1) (h_retention2 := h_retention2)
    (h_size_absorb := h_size_absorb)
    (hB1_upper := hB1_upper) (hB2_upper := hB2_upper)
    (h_reg_absorb := h_reg_absorb)
    (Gamma := Gamma)
    (S_pre_orig := S_pre_orig)
    (h_mult_orig := h_mult_orig)
    (hG_orig_sub_Gamma := hG_orig_sub_Gamma)
    (hS_pre_shift := hS_pre_shift)
    (hc_proj_nonneg := hc_proj_nonneg)
    (h_graph_absorb := h_graph_absorb)
    (hK_BSG_pos := hK_BSG_pos) (hK_BSG_B2_pos := hK_BSG_B2_pos)
    (K_BSG_unified := K_BSG_unified)
    (hK_BSG_unified_pos := hK_BSG_unified_pos)
    (hK_BSG_unified_le := hK_BSG_unified_le)
    (h_unified_def := h_unified_def)
    (h_diff_B1B2_over_B2_raw := h_norm5)


end ProductLikeIncidence.ProductReduction
