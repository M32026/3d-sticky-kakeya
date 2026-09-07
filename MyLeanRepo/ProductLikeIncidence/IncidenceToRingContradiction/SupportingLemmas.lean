module

/-
# Supporting Lemmas for Incidence-to-Ring Contradiction

Eight helper lemmas extracted from the monolithic proof to reduce
elaboration memory pressure.

## Lemmas

1. `phase0_result_helper` — Phase 0 composition
2. `bridge_proj_bound` — projection bound bridge
3. `bridge_endgame_numeric` — endgame numeric bridge
4. `glue_H1_to_H2` — glue Helper 1 to Helper 2
5. `endgame_directions_helper` — Kaufman energy + three-direction selection
6. `H1_to_H2_full` — full H1 to H2 composition
7. `bridge_H2_to_H3_stub` — H2 to H3 bridge stub
8. `bounded_coordinate_rectangle` — utility lemma
9. `budget_computation_lemma` — budget parameter computation and non-negativity
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

public import MyLeanRepo.OSWPrelude

@[expose] public section


noncomputable section

open Set Bornology ENNReal MeasureTheory

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- Helper 1: Phase 0 result extraction (lines 711-930 of monolithic proof).

Repaired contract: includes Pz_trim, defining equations, Nplane bound,
and T_y_points equation. -/
lemma phase0_result_helper
    {δ s τ κ0 η η_work ε L_exp p_projective C C_work εnc rho_sel rho_sep : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_dyadic : δ ∈ dyadicScales)
    (hδ_le_one : δ ≤ 1)
    (hs_pos : 0 < s)
    (hs_lt_one : s < 1)
    (hτ_pos : 0 < τ)
    (hkappa_pos : 0 < κ0)
    (h2kappa_lt_tau : 2 * κ0 < τ)
    (hη_work_pos : 0 < η_work)
    (hη_work_eq_two : η_work = 2 * η)
    (hε_pos : 0 < ε)
    (h5η_work_lt : 5 * η_work < 2 * (s - κ0))
    (h4η_work_lt_tau : 4 * η_work < τ)
    (hC_ge1 : 1 ≤ C)
    (hC_work_eq : C_work = 35 * C)
    (hC_work_le : C_work ≤ δ ^ (-η_work))
    (h_frostman_gap : 2 * η_work < τ * rho_sep)
    (hrho_sel_eq : rho_sel = rhoSelDefault η_work)
    (h_pbar_98 : (98 : ℝ) ≤ δ ^ (-(2 * s - 2 * κ0 - 5 * η_work)))
    (hδ_box_small : δ ^ (-(qBox η_work τ)) ≥ 8 * (1 + (1 + 12 * δ) *
        ((6 * (35 * C) * 2 ^ τ) /
         (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2))) ^ (1 / τ) + 6 * δ))
    (h_qTotalV4_le_enc4 : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤ εnc / 4)
    (h_qbox_lt_one : qBox η_work τ < 1)
    (h_extract_log_absorb : extractLogAbsorbHyp δ εnc η_work τ κ0 (qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep))
    {Y : Set ℝ}
    {X : ℝ → Set ℝ}
    {P : Set (EuclideanSpace ℝ (Fin 2))}
    {Zf : Finset (EuclideanSpace ℝ (Fin 2))}
    {Pz : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2))}
    (hY_sub : Y ⊆ productLikeUnitGrid δ)
    (hY_delta : IsProductLikeRealDeltaSCSet δ τ C Y)
    (hXy_delta : ∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ ∧
      IsProductLikeRealDeltaSCSet δ s C (X y))
    (hZf : (Zf : Set _) = productLikeIncidenceSet Y X)
    (hPz : ∀ z ∈ Zf, Pz z ⊆ P ∧ IsDeltaSCSet δ s C (Pz z) ∧
      ∀ p ∈ Pz z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ)
    (hP_small : ENat.toENNReal (dyadicCoveringNumber δ P) <
      ENNReal.ofReal (δ ^ (-(2 * s + η)))) :
    ∃ (Pz_trim : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2)))
      (U_y : ℝ → Set (Set (EuclideanSpace ℝ (Fin 2))))
      (T : Set (Set (EuclideanSpace ℝ (Fin 2))))
      (Tbar : Set (Set (EuclideanSpace ℝ (Fin 2))))
      (Pbar_param : Set (EuclideanSpace ℝ (Fin 2)))
      (T_y_points : ℝ → Set (EuclideanSpace ℝ (Fin 2)))
      (C_work' c_mult C_Pbar R : ℝ)
      (k_R : ℕ),
      (∀ y, U_y y = ⋃ x ∈ X y, dyadicCubesMeeting δ (Pz_trim (mkPoint2 x y))) ∧
      T = ⋃ y ∈ Y, U_y y ∧
      (∀ z ∈ productLikeIncidenceSet Y X, Pz_trim z ⊆ Pz z) ∧
      (∀ z ∈ productLikeIncidenceSet Y X, IsDeltaSCSet (d := 2) δ s C_work' (Pz_trim z)) ∧
      (∀ z ∈ productLikeIncidenceSet Y X,
        ∀ p ∈ Pz_trim z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ) ∧
      (∀ z ∈ productLikeIncidenceSet Y X, Bornology.IsBounded (Pz_trim z)) ∧
      C_work' = 35 * C ∧
      c_mult = δ ^ (η_work / 2) / (7 * C_work' ^ 2) ∧
      C_Pbar = 4 * (49 * C_work'^4) / c_mult^2 ∧
      R = (2 : ℝ) ^ k_R ∧
      Tbar ⊆ T ∧
      Tbar.Finite ∧
      Tbar ⊆ dyadicCubes 2 δ ∧
      Pbar_param = ⋃₀ Tbar ∧
      Nplane δ Pbar_param = ENat.toENNReal Tbar.encard ∧
      ENNReal.ofReal (δ ^ (-2 * κ0)) ≤ Nplane δ Pbar_param ∧
      IsDeltaSCSet (d := 2) δ (2 * s) C_Pbar Pbar_param ∧
      Pbar_param.Nonempty ∧
      (∀ y, T_y_points y = ⋃₀ (Tbar ∩ U_y y)) ∧
      (∀ y ∈ Y, T_y_points y ⊆ Pbar_param) ∧
      (∀ p ∈ Pbar_param,
        ENat.toENNReal ({y ∈ Y | p ∈ T_y_points y}.encard) ≥
          ENNReal.ofReal (c_mult / 2) * ENat.toENNReal Y.encard) ∧
      (∀ y ∈ Y, ∀ p ∈ T_y_points y,
        ∃ x ∈ X y, |p 0 * y + p 1 - x| ≤ 4 * δ) ∧
      (Pbar_param ⊆ {p : EuclideanSpace ℝ (Fin 2) | ∀ i, p i ∈ Set.Icc (-R) R}) ∧
      4 * R ≤ δ ^ (-(qBox η_work τ)) ∧
      0 < C_work' ∧
      0 < c_mult ∧
      1 ≤ R ∧
      0 < R ∧
      ENNReal.ofReal (δ ^ (-2 * s + η_work / 2) / (98 * C_work' ^ 4)) ≤
        ENat.toENNReal Tbar.encard := by
  have hC_pos : 0 < C := by linarith only [hC_ge1]
  have hδ_lt_one : δ < 1 := by
    by_contra h
    have hδ_eq_one : δ = 1 := by linarith only [h, hδ_le_one]
    have h1 : δ ^ (-η_work) = 1 := by rw [hδ_eq_one]; simp
    have h2 : C_work ≤ 1 := by rw [h1] at hC_work_le; exact hC_work_le
    have h3 : (35 : ℝ) ≤ C_work := by
      have h4 : C_work = 35 * C := hC_work_eq
      rw [h4]; have h5 : (1 : ℝ) ≤ C := hC_ge1; nlinarith only [h4, h5]
    linarith only [h2, h3]
  have hY_fin : Y.Finite := Set.Finite.subset (productLikeUnitGrid_finite hδ_pos) hY_sub
  have hY_nonempty : Y.Nonempty := by
    have h1 : (productLikeRealLineCopy Y).Nonempty := hY_delta.2.1
    rcases h1 with ⟨p, hp⟩
    have h2 : p 0 ∈ Y := by delta productLikeRealLineCopy at hp; exact hp
    exact ⟨p 0, h2⟩
  have hy_bounds : ∀ y ∈ Y, 0 ≤ y ∧ y ≤ 1 := by
    intro y hy; have h : y ∈ productLikeUnitGrid δ := hY_sub hy; exact ⟨h.2.1, h.2.2⟩
  let q_box : ℝ := qBox η_work τ
  have hrho_sep_pos : 0 < rho_sep := by
    have h1 : 0 < 2 * η_work := by positivity
    have h2 : 0 < τ * rho_sep := by linarith [h_frostman_gap, h1]
    exact (mul_pos_iff_of_pos_left hτ_pos).mp h2
  have hrho_sel_pos : 0 < rho_sel := by
    rw [hrho_sel_eq]; dsimp only [rhoSelDefault, qAbsorb]; positivity
  have hq_box_pos : 0 < q_box := by dsimp only [q_box, qBox, qAbsorb]; positivity
  have hC_absorb : 35 * C ≤ δ ^ (-η_work) := by
    have h1 : C_work = 35 * C := hC_work_eq; rw [← h1]; exact hC_work_le
  have hκ_v3 : (η_work / 2) + 4 * η_work < 2 * (s - κ0) := by
    have h1 : (η_work / 2) + 4 * η_work < 5 * η_work := by linarith only [hη_work_pos]
    exact lt_trans h1 h5η_work_lt
  have hδ_pbar_v3 : δ ^ (-(2 * s - 2 * κ0 - (η_work / 2) - 4 * η_work)) ≥ 98 := by
    set expA : ℝ := -(2 * s - 2 * κ0 - (η_work / 2) - 4 * η_work) with hexpA
    set expB : ℝ := -(2 * s - 2 * κ0 - 5 * η_work) with hexpB
    have h_exp_lt : expA < expB := by simp only [hexpA, hexpB]; linarith only [hη_work_pos]
    have h_mono : δ ^ expB < δ ^ expA := Real.rpow_lt_rpow_of_exponent_gt hδ_pos hδ_lt_one h_exp_lt
    have h98 : (98 : ℝ) ≤ δ ^ expB := h_pbar_98
    linarith only [h_mono, h98]
  have hδ_box_small_v3 : δ ^ (-q_box) ≥ 8 * (1 + (1 + 12 * δ) *
      ((6 * (35 * C) * 2 ^ τ) / (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2))) ^ (1 / τ) + 6 * δ) :=
    hδ_box_small
  have hP_small_v3 : ENat.toENNReal (dyadicCoveringNumber δ
        (⋃ z ∈ productLikeIncidenceSet Y X, Pz z)) <
      ENNReal.ofReal (δ ^ (-(2 * s + η_work / 2))) := by
    have h_union_sub_P : (⋃ z ∈ productLikeIncidenceSet Y X, Pz z) ⊆ P := by
      intro p hp
      rcases Set.mem_iUnion₂.mp hp with ⟨z, hz, hpz⟩
      have hz' : z ∈ Zf := by
        have hz_set : z ∈ (Zf : Set _) := hZf.symm ▸ hz; exact_mod_cast hz_set
      exact (hPz z hz').1 hpz
    have h_mono : dyadicCoveringNumber δ (⋃ z ∈ productLikeIncidenceSet Y X, Pz z) ≤
        dyadicCoveringNumber δ P := by apply dyadicCoveringNumber_mono; exact h_union_sub_P
    have h_eta_eq : η_work / 2 = η := by linarith only [hη_work_eq_two]
    have h_bound : ENat.toENNReal (dyadicCoveringNumber δ P) <
        ENNReal.ofReal (δ ^ (-(2 * s + η_work / 2))) := by rw [h_eta_eq] at *; exact hP_small
    exact lt_of_le_of_lt (ENat.toENNReal_mono h_mono) h_bound
  have h_cY_large_v3 : 2 < (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2)) * (Y.ncard : ℝ) :=
    cY_large_v3 (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one) (hη_work_pos := hη_work_pos)
      (hτ_pos := hτ_pos) (hC_pos := hC_pos) (h4η_work_lt_tau := h4η_work_lt_tau)
      (hC_work_eq := hC_work_eq) (hC_work_le := hC_work_le)
      (hY_sub := hY_sub) (hY_delta := hY_delta) (hY_fin := hY_fin)
  have hPz_delta' : ∀ z ∈ productLikeIncidenceSet Y X, IsDeltaSCSet (d := 2) δ s C (Pz z) := by
    intro z hz
    have hz_set : z ∈ (Zf : Set (EuclideanSpace ℝ (Fin 2))) := hZf.symm ▸ hz
    have hz' : z ∈ Zf := by exact_mod_cast hz_set
    exact (hPz z hz').2.1
  have hPz_approx' : ∀ z ∈ productLikeIncidenceSet Y X,
      ∀ p ∈ Pz z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ := by
    intro z hz
    have hz_set : z ∈ (Zf : Set (EuclideanSpace ℝ (Fin 2))) := hZf.symm ▸ hz
    have hz' : z ∈ Zf := by exact_mod_cast hz_set
    exact (hPz z hz').2.2
  have hPz_bounded' : ∀ z ∈ productLikeIncidenceSet Y X, Bornology.IsBounded (Pz z) := by
    intro z hz
    have hz_set : z ∈ (Zf : Set (EuclideanSpace ℝ (Fin 2))) := hZf.symm ▸ hz
    have hz' : z ∈ Zf := by exact_mod_cast hz_set
    exact (hPz z hz').2.1.1
  rcases phase0_composition_v3
      (hδ_pos := hδ_pos) (hδ_dyadic := hδ_dyadic)
      (hs_pos := hs_pos) (hs_lt_one := hs_lt_one) (hτ_pos := hτ_pos)
      (hη_work_pos := hη_work_pos) (hC_ge1 := hC_ge1) (hC_absorb := hC_absorb)
      (hκ := hκ_v3) (hqBox_pos := hq_box_pos)
      (hδ_pbar := hδ_pbar_v3) (hδ_box_small := hδ_box_small_v3)
      (hY_fin := hY_fin) (hY_nonempty := hY_nonempty)
      (hY_sub := hY_sub) (hY_delta := hY_delta) (hXy_delta := hXy_delta)
      (hy_bounds := hy_bounds)
      (hPz_delta := hPz_delta')
      (hPz_approx := hPz_approx')
      (hPz_bounded := hPz_bounded')
      (hP_small := hP_small_v3) (h_cY_large := h_cY_large_v3)
    with ⟨η_target, C_work', Pz_trim, h_phase0_all⟩
  have hC_work'_eq := h_phase0_all.2.2.1
  have hPz_trim_sub := h_phase0_all.2.2.2.1
  have hPz_trim_delta_work := h_phase0_all.2.2.2.2.1
  have hPz_trim_approx := h_phase0_all.2.2.2.2.2.1
  have hPz_trim_bounded := h_phase0_all.2.2.2.2.2.2.1
  have h_phase0_main := h_phase0_all.2.2.2.2.2.2.2
  let U_y : ℝ → Set (Set (EuclideanSpace ℝ (Fin 2))) := fun y =>
    ⋃ x ∈ X y, dyadicCubesMeeting δ (Pz_trim (mkPoint2 x y))
  let T : Set (Set (EuclideanSpace ℝ (Fin 2))) := ⋃ y ∈ Y, U_y y
  let c_mult : ℝ := δ ^ (η_work / 2) / (7 * C_work' ^ 2)
  rcases h_phase0_main with ⟨Tbar, hTbar_all⟩
  have hTbar_sub := hTbar_all.1
  have hTbar_regular := hTbar_all.2.1
  have hTbar_lower := hTbar_all.2.2.2.2.2.2.1
  have h_point_mult := hTbar_all.2.2.2.2.1
  have h_approx_v2 := hTbar_all.2.2.2.2.2.1
  have h_pbar_size := hTbar_all.2.2.2.2.2.2.2.1
  have h_box := hTbar_all.2.2.2.2.2.2.2.2
  let Pbar_param : Set (EuclideanSpace ℝ (Fin 2)) := ⋃₀ Tbar
  let T_y_points : ℝ → Set (EuclideanSpace ℝ (Fin 2)) := fun y => ⋃₀ (Tbar ∩ U_y y)
  let C_Pbar : ℝ := 4 * (49 * C_work'^4) / (c_mult)^2
  rcases h_box with ⟨R, hR_data⟩
  rcases hR_data with ⟨⟨k_R, hR_eq_pow2⟩, hPbar_Rbox, h4R_le_qbox⟩
  have hC_work'_pos : 0 < C_work' := by rw [hC_work'_eq]; positivity
  have hc_mult_pos : 0 < c_mult := by
    dsimp only [c_mult]
    have h1 : 0 < δ ^ (η_work / 2) := by positivity
    have h2 : 0 < (7 * C_work' ^ 2) := by positivity
    exact div_pos h1 h2
  have hR_ge1 : 1 ≤ R := by
    have h_eq : R = (2 : ℝ) ^ k_R := hR_eq_pow2
    rw [h_eq]
    have h2 : ∀ n : ℕ, (1 : ℝ) ≤ (2 : ℝ) ^ n := by
      intro n; induction n with | zero => norm_num | succ n ih => simp [pow_succ] at *; linarith
    exact h2 k_R
  have hR_pos : 0 < R := by rw [hR_eq_pow2]; positivity
  have hPbar_delta : IsDeltaSCSet (d := 2) δ (2 * s) C_Pbar Pbar_param := hTbar_regular
  have hPbar_nonempty : Pbar_param.Nonempty := hTbar_regular.2.1
  have hP_param_in_Rbox : Pbar_param ⊆
      {p : EuclideanSpace ℝ (Fin 2) | ∀ i, p i ∈ Set.Icc (-R) R} := by
    intro p hp; have h : |p 0| ≤ R ∧ |p 1| ≤ R := hPbar_Rbox p hp
    intro i; fin_cases i
    · have h'' : -R ≤ p 0 ∧ p 0 ≤ R := abs_le.mp h.1; exact ⟨h''.1, h''.2⟩
    · have h'' : -R ≤ p 1 ∧ p 1 ≤ R := abs_le.mp h.2; exact ⟨h''.1, h''.2⟩
  have hT_y_points_sub : ∀ y ∈ Y, T_y_points y ⊆ Pbar_param := by
    intro y _; dsimp only [T_y_points]; apply Set.sUnion_subset
    intro x hx; have h : x ∈ Tbar := hx.1; exact Set.subset_sUnion_of_mem h
  have hTbar_sub_cubes : Tbar ⊆ dyadicCubes 2 δ := by
    intro Q hQ
    have hQ_in_T : Q ∈ T := hTbar_sub hQ
    simp only [T, U_y, Set.mem_iUnion] at hQ_in_T
    rcases hQ_in_T with ⟨y, _hy, x, _hx, hQ_meeting⟩
    exact hQ_meeting.1
  have hT_finite : T.Finite := by
    apply Set.Finite.biUnion hY_fin
    intro y hy
    have hXy_fin : (X y).Finite := Set.Finite.subset (productLikeUnitGrid_finite hδ_pos) (hXy_delta y hy).1
    apply Set.Finite.biUnion hXy_fin
    intro x hx
    have hz_in : mkPoint2 x y ∈ productLikeIncidenceSet Y X := by
      simp only [productLikeIncidenceSet, Set.mem_iUnion]
      exact ⟨y, hy, by simp [mkPoint2, hx]⟩
    exact dyadicCubesMeeting_finite hδ_pos (hPz_trim_bounded (mkPoint2 x y) hz_in)
  have hTbar_finite : Tbar.Finite := Set.Finite.subset hT_finite hTbar_sub
  have hNplane_eq : Nplane δ Pbar_param = ENat.toENNReal Tbar.encard := by
    have h1 : dyadicCoveringNumber δ Pbar_param = Tbar.encard :=
      cubeFamilyCoveringEqCard hδ_pos hTbar_sub_cubes
    simp [Nplane, h1]
  have hPbar_size : ENNReal.ofReal (δ ^ (-2 * κ0)) ≤ Nplane δ Pbar_param := by
    rw [hNplane_eq]; exact h_pbar_size
  refine' ⟨Pz_trim, U_y, T, Tbar, Pbar_param, T_y_points, C_work', c_mult, C_Pbar, R, k_R, _⟩
  constructor
  · intro y; rfl
  constructor
  · rfl
  constructor
  · exact hPz_trim_sub
  constructor
  · exact hPz_trim_delta_work
  constructor
  · exact hPz_trim_approx
  constructor
  · exact hPz_trim_bounded
  constructor
  · exact hC_work'_eq
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact hR_eq_pow2
  constructor
  · exact hTbar_sub
  constructor
  · exact hTbar_finite
  constructor
  · exact hTbar_sub_cubes
  constructor
  · rfl
  constructor
  · exact hNplane_eq
  constructor
  · exact hPbar_size
  constructor
  · exact hPbar_delta
  constructor
  · exact hPbar_nonempty
  constructor
  · intro y; rfl
  constructor
  · exact hT_y_points_sub
  constructor
  · exact h_point_mult
  constructor
  · exact h_approx_v2
  constructor
  · exact hP_param_in_Rbox
  constructor
  · exact h4R_le_qbox
  constructor
  · exact hC_work'_pos
  constructor
  · exact hc_mult_pos
  constructor
  · exact hR_ge1
  constructor
  · exact hR_pos
  · exact hTbar_lower

lemma bridge_proj_bound
    {δ s η η_work L_exp C C_work R : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hδ_dyadic : δ ∈ dyadicScales)
    (hs_pos : 0 < s)
    (hη_pos : 0 < η)
    (hη_work_pos : 0 < η_work)
    (hη_work_eq_two : η_work = 2 * η)
    (hL_exp_pos : 0 < L_exp)
    (hL_exp_eq_seven : L_exp = 7)
    (hC_pos : 0 < C)
    (hC_ge1 : 1 ≤ C)
    (hC_work_eq : C_work = 35 * C)
    (hC_work_pos : 0 < C_work)
    (hC_le_target : C ≤ δ ^ (-η))
    {Y : Set ℝ} {X : ℝ → Set ℝ}
    {P : Set (EuclideanSpace ℝ (Fin 2))}
    {Pz Pz_trim : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2))}
    {Tbar : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    {Pbar_param : Set (EuclideanSpace ℝ (Fin 2))}
    (hY_sub : Y ⊆ productLikeUnitGrid δ)
    (hY_fin : Y.Finite)
    (hXy_delta : ∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ ∧
      IsProductLikeRealDeltaSCSet δ s C (X y))
    -- Original Pz properties
    (hPz_delta : ∀ z ∈ productLikeIncidenceSet Y X,
      IsDeltaSCSet (d := 2) δ s C (Pz z))
    (hPz_approx : ∀ z ∈ productLikeIncidenceSet Y X,
      ∀ p ∈ Pz z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ)
    (hPz_bounded : ∀ z ∈ productLikeIncidenceSet Y X,
      Bornology.IsBounded (Pz z))
    -- Pz_trim properties (from Helper1)
    (_hPz_trim_sub : ∀ z ∈ productLikeIncidenceSet Y X, Pz_trim z ⊆ Pz z)
    (hPz_trim_approx : ∀ z ∈ productLikeIncidenceSet Y X,
      ∀ p ∈ Pz_trim z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ)
    (hPz_trim_bounded : ∀ z ∈ productLikeIncidenceSet Y X,
      Bornology.IsBounded (Pz_trim z))
    -- Outer smallness
    (hP_small : ENat.toENNReal (dyadicCoveringNumber δ P) <
      ENNReal.ofReal (δ ^ (-(2 * s + η))))
    (hP_union_sub_P : (⋃ z ∈ productLikeIncidenceSet Y X, Pz z) ⊆ P)
    -- Helper1 outputs
    (hTbar_finite : Tbar.Finite)
    (hTbar_lower : ENNReal.ofReal (δ ^ (-2 * s + η) / (98 * C_work ^ 4)) ≤
      ENat.toENNReal Tbar.encard)
    (hTbar_sub_cubes : Tbar ⊆ dyadicCubes 2 δ)
    (hPbar_eq : Pbar_param = ⋃₀ Tbar)
    (hPbar_Rbox : Pbar_param ⊆ {p : EuclideanSpace ℝ (Fin 2) | ∀ i, p i ∈ Set.Icc (-R) R})
    (hR_pos : 0 < R)
    -- Absorption
    (h_absorb : (126 : ℝ) * Real.sqrt 98 * (35 : ℝ)^2 ≤ δ ^ (-η)) :
    (∀ y ∈ Y,
      Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1)
        (⋃₀ (Tbar ∩ (⋃ x ∈ X y, dyadicCubesMeeting δ (Pz_trim (mkPoint2 x y)))))) ≤
      ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal))) ∧
    ENat.toENNReal (⋃ y ∈ Y, ⋃ x ∈ X y, dyadicCubesMeeting δ (Pz (mkPoint2 x y))).encard <
      ENNReal.ofReal (δ ^ (-(2 * s + η))) := by
  let T_orig : Set (Set (EuclideanSpace ℝ (Fin 2))) :=
    ⋃ y ∈ Y, ⋃ x ∈ X y, dyadicCubesMeeting δ (Pz (mkPoint2 x y))

  -- T_orig ⊆ dyadicCubesMeeting δ P
  have hT_orig_sub : T_orig ⊆ dyadicCubesMeeting δ P := by
    intro Q hQ
    rcases Set.mem_iUnion₂.mp hQ with ⟨y, hy, hQ'⟩
    rcases Set.mem_iUnion₂.mp hQ' with ⟨x, hx, hQ_meeting⟩
    have hQ_cube : Q ∈ dyadicCubes 2 δ := hQ_meeting.1
    have hQ_meets : (Q ∩ Pz (mkPoint2 x y)).Nonempty := hQ_meeting.2
    have hz_in : mkPoint2 x y ∈ productLikeIncidenceSet Y X := by
      simp only [productLikeIncidenceSet, Set.mem_iUnion]
      exact ⟨y, hy, by simp [mkPoint2, hx]⟩
    have h_sub1 : Pz (mkPoint2 x y) ⊆ (⋃ z ∈ productLikeIncidenceSet Y X, Pz z) := by
      intro p hp
      exact Set.mem_iUnion₂.mpr ⟨mkPoint2 x y, hz_in, hp⟩
    have h_sub : Pz (mkPoint2 x y) ⊆ P := Set.Subset.trans h_sub1 hP_union_sub_P
    have hQ_meets_P : (Q ∩ P).Nonempty := by
      rcases hQ_meets with ⟨p, hpQ, hpPz⟩
      exact ⟨p, hpQ, h_sub hpPz⟩
    exact ⟨hQ_cube, hQ_meets_P⟩

  -- T_orig.Finite
  have hT_orig_finite : T_orig.Finite := by
    apply Set.Finite.biUnion hY_fin
    intro y hy
    have hXy_fin : (X y).Finite :=
      Set.Finite.subset (productLikeUnitGrid_finite hδ_pos) (hXy_delta y hy).1
    apply Set.Finite.biUnion hXy_fin
    intro x hx
    have hz_in : mkPoint2 x y ∈ productLikeIncidenceSet Y X := by
      simp only [productLikeIncidenceSet, Set.mem_iUnion]
      exact ⟨y, hy, by simp [mkPoint2, hx]⟩
    exact dyadicCubesMeeting_finite hδ_pos (hPz_bounded (mkPoint2 x y) hz_in)

  -- hT_upper for T_orig
  have hT_upper : ENat.toENNReal T_orig.encard < ENNReal.ofReal (δ ^ (-(2 * s + η))) := by
    have h1 : T_orig.encard ≤ (dyadicCubesMeeting δ P).encard :=
      Set.encard_mono hT_orig_sub
    have h2 : ENat.toENNReal T_orig.encard ≤ ENat.toENNReal (dyadicCubesMeeting δ P).encard :=
      ENat.toENNReal_mono h1
    have h3 : (dyadicCubesMeeting δ P).encard = dyadicCoveringNumber δ P := by rfl
    rw [h3] at h2
    exact lt_of_le_of_lt h2 hP_small

  have h_norm_bound : ∀ p ∈ Pbar_param, ‖p‖ ≤ 2 * R := by
    intro p hp
    have h2 : ∀ i, p i ∈ Set.Icc (-R) R := hPbar_Rbox hp
    have h3 : (p 0)^2 ≤ R^2 := by
      have h31 : -R ≤ p 0 := (h2 0).1
      have h32 : p 0 ≤ R := (h2 0).2
      nlinarith
    have h4 : (p 1)^2 ≤ R^2 := by
      have h41 : -R ≤ p 1 := (h2 1).1
      have h42 : p 1 ≤ R := (h2 1).2
      nlinarith
    have h5 : ‖p‖ ^ 2 = (p 0)^2 + (p 1)^2 := by
      rw [EuclideanSpace.real_norm_sq_eq p, Fin.sum_univ_two]
    have h6 : ‖p‖ ^ 2 ≤ (2 * R)^2 := by
      have h7 : ‖p‖ ^ 2 ≤ 2 * R^2 := by linarith
      have h8 : 2 * R^2 ≤ (2 * R)^2 := by nlinarith [hR_pos]
      linarith
    have h9 : 0 ≤ ‖p‖ := by positivity
    nlinarith
  have hPbar_bounded : Bornology.IsBounded Pbar_param := by
    have h : ∃ (C : ℝ), ∀ (x : EuclideanSpace ℝ (Fin 2)), x ∈ Pbar_param →
        ∀ (y : EuclideanSpace ℝ (Fin 2)), y ∈ Pbar_param → dist x y ≤ C := by
      use 4 * R
      intro x hx y hy
      have hx_norm : ‖x‖ ≤ 2 * R := h_norm_bound x hx
      have hy_norm : ‖y‖ ≤ 2 * R := h_norm_bound y hy
      have h_dist : dist x y ≤ ‖x‖ + ‖y‖ := dist_le_norm_add_norm x y
      linarith
    exact Metric.isBounded_iff.mpr h

  -- hU_y_sub_T_orig
  have hU_y_sub_T_orig : ∀ y ∈ Y,
      (⋃ x ∈ X y, dyadicCubesMeeting δ (Pz (mkPoint2 x y))) ⊆ T_orig := by
    intro y hy Q hQ
    exact Set.mem_iUnion₂.mpr ⟨y, hy, hQ⟩

  -- Call projection_bound_full
  have h_proj_bound : ∀ y ∈ Y,
      Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1)
        (⋃₀ (Tbar ∩ (⋃ x ∈ X y, dyadicCubesMeeting δ (Pz_trim (mkPoint2 x y)))))) ≤
      ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) :=
    projection_bound_full
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one) (hδ_dyadic := hδ_dyadic)
      (hs_pos := hs_pos) (hη_pos := hη_pos) (hη_work_pos := hη_work_pos)
      (hη_work_eq_two := hη_work_eq_two)
      (hL_exp_pos := hL_exp_pos) (hL_exp_eq_seven := hL_exp_eq_seven)
      (hC_pos := hC_pos) (hC_ge1 := hC_ge1)
      (hC_work_eq := hC_work_eq) (hC_work_pos := hC_work_pos)
      (hC_le_target := hC_le_target)
      (hY_sub := hY_sub) (hXy_delta := hXy_delta)
      (hPz_delta := hPz_delta) (hPz_approx := hPz_approx) (hPz_bounded := hPz_bounded)
      (hPz_trim_approx := hPz_trim_approx) (hPz_trim_bounded := hPz_trim_bounded)
      (hT_finite := hT_orig_finite) (hT_upper := hT_upper)
      (hTbar_finite := hTbar_finite) (hTbar_lower := hTbar_lower)
      (hU_y_sub_T := hU_y_sub_T_orig)
      (hTbar_sub_cubes := hTbar_sub_cubes)
      (hPbar_eq := hPbar_eq) (hPbar_bounded := hPbar_bounded)
      (h_absorb := h_absorb)

  constructor
  · exact h_proj_bound
  · exact hT_upper


lemma bridge_endgame_numeric
    {δ η η_work τ κ0 s C C_work' c_mult C_Pbar R rho_sel c_sel : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hη_work_pos : 0 < η_work)
    (hτ_pos : 0 < τ)
    (hkappa_pos : 0 < κ0)
    (h2kappa_lt_tau : 2 * κ0 < τ)
    (hC_ge1 : 1 ≤ C)
    (hs_lt_one : s < 1)
    (hkappa_lt_s : κ0 < s)
    (hη_work_eq_two : η_work = 2 * η)
    (hR_pos : 0 < R)
    (hrho_sel_pos : 0 < rho_sel)
    (hc_mult_pos : 0 < c_mult)
    -- Helper1 equations
    (hC_work'_eq : C_work' = 35 * C)
    (hc_mult_eq : c_mult = δ ^ (η_work / 2) / (7 * C_work' ^ 2))
    (hC_Pbar_eq : C_Pbar = 4 * (49 * C_work'^4) / c_mult^2)
    -- Outer thresholds
    (hC_le_target : C ≤ δ ^ (-η))
    (h_plan_absorb : planConstant s κ0 ≤ δ ^ (-(qPlan η_work - 5 * η_work)))
    (h_Kauf_absorb : kaufmanConstant τ κ0 ≤ δ ^ (-(51 * η_work / 100)))
    (h4R_le_qbox : 4 * R ≤ δ ^ (-(qBox η_work τ)))
    (hδ_rho_sel_le_c_sel8 : δ ^ rho_sel ≤ c_sel / 8)
    (hc_sel_eq : c_sel = cPhase0 δ η (35 * C) / 2) :
    let C_ν : ℝ := 3 * C * (2 : ℝ)^τ
    let C_Kaufman : ℝ := 1 + (C_ν + 1) * (2 * R * Real.sqrt 2)^(2 * κ0) * (1 + 2 * κ0 / (τ - 2 * κ0))
    let C_plan : ℝ := robust_projection.energyBoundConstant C_Pbar s κ0
    let q_bad : ℝ := qKaufBase η_work τ κ0 + rho_sel
    (C_Kaufman * C_plan ≤ δ ^ (-(qKaufBase η_work τ κ0))) ∧
    (C_Kaufman * C_plan ≤ δ ^ (-q_bad) * ((c_mult / 2) / 8)) := by
  let C_ν : ℝ := 3 * C * (2 : ℝ)^τ
  let C_Kaufman : ℝ := 1 + (C_ν + 1) * (2 * R * Real.sqrt 2)^(2 * κ0) * (1 + 2 * κ0 / (τ - 2 * κ0))
  let C_plan : ℝ := robust_projection.energyBoundConstant C_Pbar s κ0
  let q_box : ℝ := qBox η_work τ

  -- Step 1: Derive C_Pbar bound for plan_bound_from_threshold
  -- C_Pbar = 4 * 49^2 * 35^8 * C^8 * δ^(-η_work)
  -- C ≤ δ^(-η) = δ^(-η_work/2) → C^8 ≤ δ^(-4η_work)
  -- So C_Pbar ≤ 4 * 49^2 * 35^8 * δ^(-5η_work)
  have hC_le_halfwork : C ≤ δ ^ (-η_work / 2) := by
    have h1 : η = η_work / 2 := by linarith [hη_work_eq_two]
    have h2 : C ≤ δ ^ (-η) := hC_le_target
    have h3 : (-η) = -η_work / 2 := by linarith [hη_work_eq_two]
    rw [h3] at h2; exact h2

  have hC_Pbar_bound : C_Pbar ≤ (4 * (49 : ℝ)^2 * (35 : ℝ)^8) * δ ^ (-5 * η_work) := by
    rw [hC_Pbar_eq, hc_mult_eq, hC_work'_eq]
    have hC8 : C ^ 8 ≤ δ ^ (-4 * η_work) := by
      have h1 : C ≤ δ ^ (-η_work / 2) := hC_le_halfwork
      have h2 : C ^ 8 ≤ (δ ^ (-η_work / 2)) ^ 8 := by gcongr
      have h3 : (δ ^ (-η_work / 2)) ^ 8 = δ ^ (-4 * η_work) := by
        have h4 : (δ ^ (-η_work / 2)) ^ 8 = δ ^ ((-η_work / 2) * (8 : ℝ)) := by
          rw [← Real.rpow_natCast]
          rw [Real.rpow_mul hδ_pos.le] <;> ring_nf
        rw [h4] <;> ring_nf
      rw [h3] at h2; exact h2
    have hpos : 0 < δ ^ (η_work / 2) := by positivity
    have hpos2 : 0 < (7 : ℝ) := by norm_num
    have h_main : 4 * (49 * (35 * C) ^ 4) / (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2)) ^ 2 ≤
        (4 * (49 : ℝ)^2 * (35 : ℝ)^8) * δ ^ (-5 * η_work) := by
      have hden : (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2)) ^ 2 =
          δ ^ η_work / ((7 * (35 * C) ^ 2) ^ 2) := by
        have h1 : (δ ^ (η_work / 2)) ^ 2 = δ ^ η_work := by
          have h21 : (δ ^ (η_work / 2)) ^ 2 = (δ ^ (η_work / 2)) * (δ ^ (η_work / 2)) := by
            rw [pow_two]
          rw [h21]
          have h22 : (δ ^ (η_work / 2)) * (δ ^ (η_work / 2)) = δ ^ (η_work / 2 + η_work / 2) := by
            rw [← Real.rpow_add hδ_pos]
          rw [h22] <;> ring_nf
        rw [div_pow, h1]
      rw [hden]
      have hpos2 : 0 < (7 * (35 * C) ^ 2) := by positivity
      have h_eq : 4 * (49 * (35 * C) ^ 4) / (δ ^ η_work / ((7 * (35 * C) ^ 2) ^ 2)) =
          (4 * (49 : ℝ)^2 * (35 : ℝ)^8) * C ^ 8 / (δ ^ η_work) := by
        have hdiv : 4 * (49 * (35 * C) ^ 4) / (δ ^ η_work / ((7 * (35 * C) ^ 2) ^ 2)) =
            4 * (49 * (35 * C) ^ 4) * ((7 * (35 * C) ^ 2) ^ 2) / (δ ^ η_work) := by
          rw [div_div_eq_mul_div]
        rw [hdiv]
        have h_expand : 4 * (49 * (35 * C) ^ 4) * ((7 * (35 * C) ^ 2) ^ 2) =
            (4 * (49 : ℝ)^2 * (35 : ℝ)^8) * C ^ 8 := by ring
        rw [h_expand]
      rw [h_eq]
      let K : ℝ := 4 * (49 : ℝ)^2 * (35 : ℝ)^8
      have h10 : 0 < δ ^ η_work := by positivity
      have h11 : K * C ^ 8 / (δ ^ η_work) ≤ K * δ ^ (-4 * η_work) / (δ ^ η_work) := by
        gcongr
      have h14 : δ ^ (-η_work) = (δ ^ η_work)⁻¹ := by
        have h : ∀ (y : ℝ), δ ^ (-y) = (δ ^ y)⁻¹ := Real.rpow_neg hδ_pos.le
        exact h η_work
      have h12 : K * δ ^ (-4 * η_work) / (δ ^ η_work) = K * δ ^ (-5 * η_work) := by
        have h15 : K * δ ^ (-4 * η_work) / (δ ^ η_work) =
            K * (δ ^ (-4 * η_work) * δ ^ (-η_work)) := by
          rw [h14] <;> field_simp
        rw [h15]
        have h16 : δ ^ (-4 * η_work) * δ ^ (-η_work) = δ ^ (-5 * η_work) := by
          rw [← Real.rpow_add hδ_pos]
          have h17 : -4 * η_work + -η_work = -5 * η_work := by ring
          rw [h17]
        rw [h16]
      calc
        K * C ^ 8 / (δ ^ η_work) ≤ K * δ ^ (-4 * η_work) / (δ ^ η_work) := h11
        _ = K * δ ^ (-5 * η_work) := h12
    exact h_main

  -- Step 2: plan_bound_from_threshold → C_plan ≤ δ^(-qPlan η_work)
  have hC_plan_bound : C_plan ≤ δ ^ (-(qPlan η_work)) :=
    plan_bound_from_threshold
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one) (hη_work_pos := hη_work_pos)
      (hs_lt_one := hs_lt_one) (hkappa_lt_s := hkappa_lt_s) (hkappa_pos := hkappa_pos)
      (hC_Pbar_bound := hC_Pbar_bound) (h_plan_absorb := h_plan_absorb)
      (hC_plan_def := by rfl)

  -- Step 3: kauf_bound_from_threshold → C_Kaufman ≤ δ^(-(η_work + qKaufman + qAbsorb))
  have hC_le_halfwork2 : C ≤ δ ^ (-η_work / 2) := by
    have h1 : η = η_work / 2 := by linarith [hη_work_eq_two]
    have h2 : C ≤ δ ^ (-η) := hC_le_target
    have h3 : (-η) = -η_work / 2 := by linarith [hη_work_eq_two]
    rw [h3] at h2; exact h2

  have hq_box_pos : 0 < q_box := by
    dsimp only [q_box, qBox, qAbsorb]; positivity

  have hC_Kauf_bound : C_Kaufman ≤ δ ^ (-(η_work + qKaufman η_work τ κ0 + qAbsorb η_work)) :=
    kauf_bound_from_threshold
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hη_work_pos := hη_work_pos) (hτ_pos := hτ_pos)
      (hkappa_pos := hkappa_pos) (h2kappa_lt_tau := h2kappa_lt_tau)
      (hC_ge1 := hC_ge1)
      (hq_box_pos := hq_box_pos) (hq_box_eq := by rfl)
      (hC_le_target := hC_le_halfwork2)
      (hR_pos := hR_pos) (h4R_le_qbox := h4R_le_qbox)
      (h_Kauf_absorb := h_Kauf_absorb)
      (hC_ν_def := by rfl) (hC_Kauf_def := by rfl)

  -- Step 4: Nonnegativity
  have hC_plan_nonneg : 0 ≤ C_plan := by
    dsimp only [C_plan]
    have hC_Pbar_pos : 0 < C_Pbar := by
      rw [hC_Pbar_eq, hc_mult_eq, hC_work'_eq] <;> positivity
    have h_main_pos : 0 < robust_projection.energyBoundConstant C_Pbar s κ0 :=
      robust_projection.energyBoundConstant_pos hC_Pbar_pos hkappa_pos hkappa_lt_s
    exact le_of_lt h_main_pos

  have hC_Kauf_nonneg : 0 ≤ C_Kaufman := by
    dsimp only [C_Kaufman, C_ν]
    have h1 : 0 ≤ C := by linarith [hC_ge1]
    have h2 : 0 < τ - 2 * κ0 := by linarith [h2kappa_lt_tau]
    positivity

  -- Step 5: kaufman_product_bound_qKaufBase → h_product_bound
  have h_product_bound : C_Kaufman * C_plan ≤ δ ^ (-(qKaufBase η_work τ κ0)) :=
    kaufman_product_bound_qKaufBase
      (hδ_pos := hδ_pos)
      (hC_plan_bound := hC_plan_bound)
      (hC_Kaufman_bound := hC_Kauf_bound)
      (hC_plan_nonneg := hC_plan_nonneg)
      (hC_Kaufman_nonneg := hC_Kauf_nonneg)

  -- Step 6: c_endgame = c_mult / 2 = c_sel
  -- c_sel = cPhase0 δ η (35*C) / 2
  -- c_mult = δ^(η_work/2) / (7 * C_work'^2) = δ^η / (7 * (35*C)^2) = cPhase0 δ η (35*C)
  -- So c_sel = c_mult / 2
  have hc_sel_eq_cmult_half : c_sel = c_mult / 2 := by
    have h1 : cPhase0 δ η (35 * C) = δ ^ η / (7 * (35 * C) ^ 2) := by
      rfl
    have h2 : c_mult = δ ^ (η_work / 2) / (7 * C_work' ^ 2) := hc_mult_eq
    have h3 : η_work / 2 = η := by linarith [hη_work_eq_two]
    have h4 : C_work' = 35 * C := hC_work'_eq
    rw [hc_sel_eq, h1, h2, h3, h4]

  have hc_endgame_pos : 0 < c_mult / 2 := by positivity

  -- Step 7: kaufman_absorption_with_rho_sel → h_ed_kaufman_absorb
  have hδ_rho_sel_le_endgame8 : δ ^ rho_sel ≤ (c_mult / 2) / 8 := by
    rw [← hc_sel_eq_cmult_half]
    exact hδ_rho_sel_le_c_sel8

  let q_bad : ℝ := qKaufBase η_work τ κ0 + rho_sel

  have h_ed_kaufman_absorb : C_Kaufman * C_plan ≤ δ ^ (-q_bad) * ((c_mult / 2) / 8) :=
    kaufman_absorption_with_rho_sel
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hc_pos := hc_endgame_pos)
      (hC_product_nonneg := mul_nonneg hC_Kauf_nonneg hC_plan_nonneg)
      (h_product_bound := h_product_bound)
      (h_rho_sel_pos := hrho_sel_pos)
      (hδ_rho_sel_small := hδ_rho_sel_le_endgame8)

  exact ⟨h_product_bound, h_ed_kaufman_absorb⟩


/-- Glue theorem: Helper1 → Helper2.

Takes outer V4 hypotheses + Helper1 outputs, calls both bridges, and produces
ALL derived gap facts needed by `endgame_directions_helper` (Helper2).

Facts that are direct outer hypotheses or direct Helper1 outputs are NOT
re-output — the caller already has them. -/
lemma glue_H1_to_H2
    {δ s τ κ0 η η_work ε L_exp C C_work rho_sel rho_sep : ℝ}
    -- Outer V4 hypotheses
    (hδ_pos : 0 < δ)
    (hδ_dyadic : δ ∈ dyadicScales)
    (hδ_le_one : δ ≤ 1)
    (hs_pos : 0 < s)
    (hs_lt_one : s < 1)
    (hτ_pos : 0 < τ)
    (hkappa_pos : 0 < κ0)
    (hkappa_lt_s : κ0 < s)
    (h2kappa_lt_tau : 2 * κ0 < τ)
    (hη_pos : 0 < η)
    (hη_work_pos : 0 < η_work)
    (hη_work_eq_two : η_work = 2 * η)
    (hC_ge1 : 1 ≤ C)
    (hC_work_eq : C_work = 35 * C)
    (hC_work_le : C_work ≤ δ ^ (-η_work))
    (hC_le_target : C ≤ δ ^ (-η))
    (h_frostman_gap : 2 * η_work < τ * rho_sep)
    (hrho_sel_eq : rho_sel = rhoSelDefault η_work)
    (hrho_sep_le : rho_sep ≤ η_work / κ0)
    (hη_work_le_kappa0 : η_work ≤ κ0)
    (hL_exp_pos : 0 < L_exp)
    (hL_exp_eq_seven : L_exp = 7)
    (h_proj_absorb : (126 : ℝ) * Real.sqrt 98 * (35 : ℝ)^2 ≤ δ ^ (-η))
    (h_plan_absorb : planConstant s κ0 ≤ δ ^ (-(qPlan η_work - 5 * η_work)))
    (h_Kauf_absorb : kaufmanConstant τ κ0 ≤ δ ^ (-(51 * η_work / 100)))
    (c_sel : ℝ)
    (hδ_rho_sel_le_c_sel8 : δ ^ rho_sel ≤ c_sel / 8)
    (hc_sel_eq : c_sel = cPhase0 δ η (35 * C) / 2)
    -- Y / X / P / Pz data
    {Y : Set ℝ} {X : ℝ → Set ℝ}
    {P : Set (EuclideanSpace ℝ (Fin 2))}
    {Zf : Finset (EuclideanSpace ℝ (Fin 2))}
    {Pz : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2))}
    (hY_sub : Y ⊆ productLikeUnitGrid δ)
    (hY_delta : IsProductLikeRealDeltaSCSet δ τ C Y)
    (hXy_delta : ∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ ∧
      IsProductLikeRealDeltaSCSet δ s C (X y))
    (hZf : (Zf : Set _) = productLikeIncidenceSet Y X)
    (hPz : ∀ z ∈ Zf, Pz z ⊆ P ∧ IsDeltaSCSet δ s C (Pz z) ∧
      ∀ p ∈ Pz z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ)
    (hP_small : ENat.toENNReal (dyadicCoveringNumber δ P) <
      ENNReal.ofReal (δ ^ (-(2 * s + η))))
    -- Helper1 outputs (only those used in the glue proof)
    {Pz_trim : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2))}
    {Tbar : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    {Pbar_param : Set (EuclideanSpace ℝ (Fin 2))}
    {T_y_points : ℝ → Set (EuclideanSpace ℝ (Fin 2))}
    {C_work' c_mult C_Pbar R : ℝ}
    (hPz_trim_sub : ∀ z ∈ productLikeIncidenceSet Y X, Pz_trim z ⊆ Pz z)
    (hPz_trim_approx : ∀ z ∈ productLikeIncidenceSet Y X,
      ∀ p ∈ Pz_trim z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ)
    (hPz_trim_bounded : ∀ z ∈ productLikeIncidenceSet Y X,
      Bornology.IsBounded (Pz_trim z))
    (hC_work'_eq : C_work' = 35 * C)
    (hc_mult_eq : c_mult = δ ^ (η_work / 2) / (7 * C_work' ^ 2))
    (hC_Pbar_eq : C_Pbar = 4 * (49 * C_work'^4) / c_mult^2)
    (hTbar_finite : Tbar.Finite)
    (hTbar_grid : Tbar ⊆ dyadicCubes 2 δ)
    (hPbar_eq_sUnion : Pbar_param = ⋃₀ Tbar)
    (hT_y_points_eq : ∀ y ∈ Y, T_y_points y =
      ⋃₀ (Tbar ∩ (⋃ x ∈ X y, dyadicCubesMeeting δ (Pz_trim (mkPoint2 x y)))))
    (hPbar_Rbox_set : Pbar_param ⊆ {p : EuclideanSpace ℝ (Fin 2) | ∀ i, p i ∈ Set.Icc (-R) R})
    (h4R_le_qbox : 4 * R ≤ δ ^ (-(qBox η_work τ)))
    (hC_work'_pos : 0 < C_work')
    (hc_mult_pos : 0 < c_mult)
    (hR_ge1 : 1 ≤ R)
    (hTbar_lower : ENNReal.ofReal (δ ^ (-2 * s + η_work / 2) / (98 * C_work' ^ 4)) ≤
      ENat.toENNReal Tbar.encard) :
    -- Output: all gap facts Helper2 needs (not direct outer or Helper1 outputs)
    (δ < 1) ∧
    Y.Finite ∧
    Y.Nonempty ∧
    (0 < rho_sel) ∧
    (0 < rho_sep) ∧
    (rho_sep ≤ 1) ∧
    (∀ p ∈ Pbar_param, |p 0| ≤ R ∧ |p 1| ≤ R) ∧
    (0 < rhoExc η_work ε τ κ0 rho_sel) ∧
    (rhoExc η_work ε τ κ0 rho_sel = qKaufBase η_work τ κ0 + rho_sel) ∧
    ((1 + ((3 * C * 2 ^ τ) + 1) * (2 * R * Real.sqrt 2) ^ (2 * κ0) *
        (1 + (2 * κ0) / (τ - 2 * κ0))) *
      robust_projection.energyBoundConstant C_Pbar s κ0 ≤
      δ ^ (-(qKaufBase η_work τ κ0))) ∧
    (∀ y ∈ Y,
      Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) (T_y_points y)) ≤
      ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal))) ∧
    ((1 + ((3 * C * 2 ^ τ) + 1) * (2 * R * Real.sqrt 2) ^ (2 * κ0) *
        (1 + (2 * κ0) / (τ - 2 * κ0))) *
      robust_projection.energyBoundConstant C_Pbar s κ0 ≤
      δ ^ (-(rhoExc η_work ε τ κ0 rho_sel)) * ((c_mult / 2) / 8)) := by
  -- Step 1: Derive hP_union_sub_P
  have hP_union_sub_P : (⋃ z ∈ productLikeIncidenceSet Y X, Pz z) ⊆ P := by
    intro p hp
    rcases Set.mem_iUnion₂.mp hp with ⟨z, hz, hpz⟩
    have hz' : z ∈ Zf := by
      have hz_set : z ∈ (Zf : Set _) := hZf.symm ▸ hz
      exact_mod_cast hz_set
    exact (hPz z hz').1 hpz

  -- Step 2: Derive original Pz properties
  have hPz_delta_orig : ∀ z ∈ productLikeIncidenceSet Y X,
      IsDeltaSCSet (d := 2) δ s C (Pz z) := by
    intro z hz
    have hz' : z ∈ Zf := by
      have hz_set : z ∈ (Zf : Set _) := hZf.symm ▸ hz
      exact_mod_cast hz_set
    exact (hPz z hz').2.1
  have hPz_approx_orig : ∀ z ∈ productLikeIncidenceSet Y X,
      ∀ p ∈ Pz z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ := by
    intro z hz
    have hz' : z ∈ Zf := by
      have hz_set : z ∈ (Zf : Set _) := hZf.symm ▸ hz
      exact_mod_cast hz_set
    exact (hPz z hz').2.2
  have hPz_bounded_orig : ∀ z ∈ productLikeIncidenceSet Y X,
      Bornology.IsBounded (Pz z) := by
    intro z hz
    have hz' : z ∈ Zf := by
      have hz_set : z ∈ (Zf : Set _) := hZf.symm ▸ hz
      exact_mod_cast hz_set
    exact (hPz z hz').2.1.1

  -- Step 3: hδ_lt_one
  have hδ_lt_one : δ < 1 := by
    by_contra h
    have hδ_eq_one : δ = 1 := by linarith only [h, hδ_le_one]
    have h1 : δ ^ (-η_work) = 1 := by rw [hδ_eq_one]; simp
    have h2 : C_work ≤ 1 := by rw [h1] at hC_work_le; exact hC_work_le
    have h3 : (35 : ℝ) ≤ C_work := by
      have h4 : C_work = 35 * C := hC_work_eq
      rw [h4]; have h5 : (1 : ℝ) ≤ C := hC_ge1; nlinarith only [h4, h5]
    linarith only [h2, h3]

  -- Step 4: hR_pos
  have hR_pos : 0 < R := by linarith [hR_ge1]

  -- Step 5: hC_Pbar_pos
  have hC_Pbar_pos : 0 < C_Pbar := by
    rw [hC_Pbar_eq]
    have h1 : 0 < C_work' := hC_work'_pos
    have h2 : 0 < c_mult := hc_mult_pos
    positivity

  -- Step 5: hPbar_Rbox pointwise
  have hPbar_Rbox : ∀ p ∈ Pbar_param, |p 0| ≤ R ∧ |p 1| ≤ R := by
    intro p hp
    have h : ∀ i : Fin 2, p i ∈ Set.Icc (-R) R := hPbar_Rbox_set hp
    have h0 : -R ≤ p 0 ∧ p 0 ≤ R := h 0
    have h1 : -R ≤ p 1 ∧ p 1 ≤ R := h 1
    constructor <;> rw [abs_le] <;> constructor <;> linarith

  -- Step 6: hrho_sel_pos
  have hrho_sel_pos : 0 < rho_sel := by
    rw [hrho_sel_eq]; dsimp only [rhoSelDefault, qAbsorb]; positivity

  -- Step 7: hY_fin
  have hY_fin : Y.Finite := Set.Finite.subset (productLikeUnitGrid_finite hδ_pos) hY_sub

  -- Step 8: Call Bridge_ProjBound
  have h_bridges : (∀ y ∈ Y,
      Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1)
        (⋃₀ (Tbar ∩ (⋃ x ∈ X y, dyadicCubesMeeting δ (Pz_trim (mkPoint2 x y)))))) ≤
      ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal))) ∧
    ENat.toENNReal (⋃ y ∈ Y, ⋃ x ∈ X y, dyadicCubesMeeting δ (Pz (mkPoint2 x y))).encard <
      ENNReal.ofReal (δ ^ (-(2 * s + η))) :=
    bridge_proj_bound
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one) (hδ_dyadic := hδ_dyadic)
      (hs_pos := hs_pos) (hη_pos := hη_pos) (hη_work_pos := hη_work_pos)
      (hη_work_eq_two := hη_work_eq_two)
      (hL_exp_pos := hL_exp_pos) (hL_exp_eq_seven := hL_exp_eq_seven)
      (hC_pos := by linarith only [hC_ge1]) (hC_ge1 := hC_ge1)
      (hC_work_eq := hC_work'_eq) (hC_work_pos := hC_work'_pos)
      (hC_le_target := hC_le_target)
      (hY_sub := hY_sub) (hY_fin := hY_fin)
      (hXy_delta := hXy_delta)
      (hPz_delta := hPz_delta_orig) (hPz_approx := hPz_approx_orig)
      (hPz_bounded := hPz_bounded_orig)
      (_hPz_trim_sub := hPz_trim_sub)
      (hPz_trim_approx := hPz_trim_approx)
      (hPz_trim_bounded := hPz_trim_bounded)
      (hP_small := hP_small) (hP_union_sub_P := hP_union_sub_P)
      (hTbar_finite := hTbar_finite)
      (hTbar_lower := by
        have h_eq : δ ^ (-2 * s + η_work / 2) = δ ^ (-2 * s + η) := by
          have h : η_work / 2 = η := by linarith [hη_work_eq_two]
          rw [h]
        rw [h_eq] at hTbar_lower
        exact hTbar_lower)
      (hTbar_sub_cubes := hTbar_grid)
      (hPbar_eq := hPbar_eq_sUnion) (hPbar_Rbox := hPbar_Rbox_set)
      (hR_pos := hR_pos) (h_absorb := h_proj_absorb)
  rcases h_bridges with ⟨h_proj_bound, _hT_upper⟩

  -- Step 9: Call Bridge_EndgameNumeric
  have h_endgame :
      let C_ν : ℝ := 3 * C * (2 : ℝ)^τ
      let C_Kaufman : ℝ := 1 + (C_ν + 1) * (2 * R * Real.sqrt 2)^(2 * κ0) * (1 + 2 * κ0 / (τ - 2 * κ0))
      let C_plan : ℝ := robust_projection.energyBoundConstant C_Pbar s κ0
      let q_bad : ℝ := qKaufBase η_work τ κ0 + rho_sel
      (C_Kaufman * C_plan ≤ δ ^ (-(qKaufBase η_work τ κ0))) ∧
      (C_Kaufman * C_plan ≤ δ ^ (-q_bad) * ((c_mult / 2) / 8)) :=
    bridge_endgame_numeric
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one) (hη_work_pos := hη_work_pos)
      (hτ_pos := hτ_pos) (hkappa_pos := hkappa_pos) (h2kappa_lt_tau := h2kappa_lt_tau)
      (hC_ge1 := hC_ge1) (hs_lt_one := hs_lt_one)
      (hkappa_lt_s := hkappa_lt_s)
      (hη_work_eq_two := hη_work_eq_two) (hR_pos := hR_pos)
      (hrho_sel_pos := hrho_sel_pos) (hc_mult_pos := hc_mult_pos)
      (hC_work'_eq := hC_work'_eq) (hc_mult_eq := hc_mult_eq)
      (hC_Pbar_eq := hC_Pbar_eq)
      (hC_le_target := hC_le_target) (h_plan_absorb := h_plan_absorb)
      (h_Kauf_absorb := h_Kauf_absorb) (h4R_le_qbox := h4R_le_qbox)
      (hδ_rho_sel_le_c_sel8 := hδ_rho_sel_le_c_sel8)
      (hc_sel_eq := hc_sel_eq)
  rcases h_endgame with ⟨h_product_bound, h_ed_kaufman_absorb⟩

  -- Step 10: Derive hrho_sep_pos
  have hrho_sep_pos : 0 < rho_sep := by
    have h : 0 < τ * rho_sep := by linarith [h_frostman_gap, hη_work_pos]
    exact (mul_pos_iff_of_pos_left hτ_pos).mp h

  -- Step 11: Derive hrho_sep_le_one
  have hrho_sep_le_one : rho_sep ≤ 1 := by
    calc rho_sep ≤ η_work / κ0 := hrho_sep_le
      _ ≤ κ0 / κ0 := by gcongr <;> linarith
      _ = 1 := by
        have h : 0 < κ0 := hkappa_pos
        field_simp [h.ne']

  -- Step 12: Derive hY_nonempty
  have hY_nonempty : Y.Nonempty := by
    have h : (productLikeRealLineCopy Y).Nonempty := hY_delta.2.1
    rcases h with ⟨x, hx⟩
    exact ⟨x 0, hx⟩

  -- Step 13: Rewrite projection bound to T_y_points format
  have h_proj_bound' : ∀ y ∈ Y,
      Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) (T_y_points y)) ≤
      ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) := by
    intro y hy
    have h_eq : T_y_points y =
        ⋃₀ (Tbar ∩ (⋃ x ∈ X y, dyadicCubesMeeting δ (Pz_trim (mkPoint2 x y)))) :=
      hT_y_points_eq y hy
    rw [h_eq]
    exact h_proj_bound y hy

  -- Step 14: q_bad properties
  have h_qbad_eq : rhoExc η_work ε τ κ0 rho_sel = qKaufBase η_work τ κ0 + rho_sel := by
    rw [rhoExc]

  have hq_bad_pos : 0 < rhoExc η_work ε τ κ0 rho_sel := by
    rw [h_qbad_eq]
    have h1 : 0 < qKaufBase η_work τ κ0 := by
      dsimp only [qKaufBase, qPlan, qKaufman, qAbsorb, qBox]
      have h11 : 0 < 10 * η_work + η_work / 100 := by linarith [hη_work_pos]
      have h12 : 0 < 2 * κ0 * (4 * η_work / τ + η_work / 100) := by positivity
      have h13 : 0 < η_work := hη_work_pos
      have h14 : 0 < η_work / 100 := by positivity
      linarith
    have h2 : 0 < rho_sel := hrho_sel_pos
    linarith

  -- Step 15: Rewrite h_ed_kaufman_absorb to use rhoExc
  have h_ed_kaufman_absorb' :
      (1 + ((3 * C * 2 ^ τ) + 1) * (2 * R * Real.sqrt 2) ^ (2 * κ0) *
        (1 + (2 * κ0) / (τ - 2 * κ0))) *
      robust_projection.energyBoundConstant C_Pbar s κ0 ≤
      δ ^ (-(rhoExc η_work ε τ κ0 rho_sel)) * ((c_mult / 2) / 8) := by
    have h3 : -(rhoExc η_work ε τ κ0 rho_sel) = -(qKaufBase η_work τ κ0 + rho_sel) := by
      rw [h_qbad_eq]
    rw [h3]
    exact h_ed_kaufman_absorb

  -- Step 16: Assemble all 12 gap facts
  exact ⟨hδ_lt_one, hY_fin, hY_nonempty, hrho_sel_pos, hrho_sep_pos, hrho_sep_le_one,
    hPbar_Rbox, hq_bad_pos, h_qbad_eq, h_product_bound, h_proj_bound', h_ed_kaufman_absorb'⟩


/--
Helper 2: Endgame Directions.

Given Phase 0 outputs and all numeric conditions, construct Frostman measure ν,
uniform point set E, three separated directions θ1 < θ3 < θ2, nested subsets
E1 ⊇ E2 ⊇ E3, and energy/projection bounds.
-/
lemma endgame_directions_helper
    {δ s τ κ0 η η_work L_exp C C_work K_ring εnc ε p_projective : ℝ}
    {rho_sel rho_sep q_bad : ℝ}
    (hδ_pos : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales) (hδ_le_one : δ ≤ 1)
    (hδ_lt_one : δ < 1)
    (hs_pos : 0 < s) (hs_lt_one : s < 1) (hτ_pos : 0 < τ)
    (hkappa_pos : 0 < κ0) (hkappa_lt_s : κ0 < s) (h2kappa_lt_tau : 2 * κ0 < τ)
    (hη_pos : 0 < η) (hη_work_pos : 0 < η_work) (hη_work_eq_two : η_work = 2 * η)
    (hL_exp_pos : 0 < L_exp) (hL_exp_eq_seven : L_exp = 7)
    (hη_work_le_kappa0 : η_work ≤ κ0) (hp_ge_10 : 10 ≤ p_projective)
    (hC_ge1 : 1 ≤ C) (hC_le_target : C ≤ δ ^ (-η))
    (hC_work_eq : C_work = 35 * C) (hC_work_ge1 : 1 ≤ C_work) (hC_work_le : C_work ≤ δ ^ (-η_work))
    (hK_ring_ge1 : 1 ≤ K_ring)
    (hrho_sel_pos : 0 < rho_sel) (hrho_sep_pos : 0 < rho_sep) (hrho_sep_le_one : rho_sep ≤ 1)
    (hrho_sel_eq : rho_sel = rhoSelDefault η_work) (hrho_sep_le : rho_sep ≤ η_work / κ0)
    (h_frostman_gap : 2 * η_work < τ * rho_sep)
    (hG_eta_work_le : gapCoefficientV4 L_exp κ0 p_projective τ * η_work ≤ εnc / 2)
    (h_qTotalV4_le_enc4 : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤ εnc / 4)
    (c_sel : ℝ) (hc_sel_pos : 0 < c_sel) (hc_sel_eq : c_sel = cPhase0 δ η (35 * C) / 2)
    (hδ_rho_sel_le_c_sel2 : δ ^ rho_sel ≤ c_sel / 2)
    (hδ_rho_sel_le_c_sel8 : δ ^ rho_sel ≤ c_sel / 8)
    (h_small_neighborhood : 2 * (3 * C * 2 ^ τ) * (δ ^ rho_sep) ^ τ ≤ c_sel / 8)
    (h_plan_absorb : planConstant s κ0 ≤ δ ^ (-(qPlan η_work - 5 * η_work)))
    (h_Kauf_absorb : kaufmanConstant τ κ0 ≤ δ ^ (-(51 * η_work / 100)))
    (h_box_bound : (2 ^ 20 : ℝ) ≤ δ ^ (-(η_work / 100)))
    (h_proj_absorb : (126 : ℝ) * Real.sqrt 98 * (35 : ℝ)^2 ≤ δ ^ (-η))
    (R : ℝ) (k_R : ℕ) (hR_eq_pow2 : R = (2 : ℝ) ^ k_R) (hR_ge1 : 1 ≤ R)
    (h4R_le_qbox : 4 * R ≤ δ ^ (-(qBox η_work τ)))
    {Y : Set ℝ} (hY_sub : Y ⊆ productLikeUnitGrid δ)
    (hY_delta : IsProductLikeRealDeltaSCSet δ τ C Y)
    (hY_fin : Y.Finite) (hY_nonempty : Y.Nonempty)
    (C_work' c_mult : ℝ) (hC_work'_eq : C_work' = 35 * C)
    (hc_mult_eq : c_mult = δ ^ (η_work / 2) / (7 * C_work' ^ 2))
    (hC_work'_pos : 0 < C_work') (hc_mult_pos : 0 < c_mult)
    (C_Pbar : ℝ) (hC_Pbar_eq : C_Pbar = 4 * (49 * C_work'^4) / c_mult^2)
    {Tbar : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    {Pbar_param : Set (EuclideanSpace ℝ (Fin 2))}
    {T_y_points : ℝ → Set (EuclideanSpace ℝ (Fin 2))}
    (hPbar_delta : IsDeltaSCSet (d := 2) δ (2 * s) C_Pbar Pbar_param)
    (hPbar_nonempty : Pbar_param.Nonempty)
    (hPbar_size : ENNReal.ofReal (δ ^ (-2 * κ0)) ≤ Nplane δ Pbar_param)
    (hPbar_Rbox : ∀ p ∈ Pbar_param, |p 0| ≤ R ∧ |p 1| ≤ R)
    (hT_y_points_sub : ∀ y ∈ Y, T_y_points y ⊆ Pbar_param)
    (hTbar_finite : Tbar.Finite)
    (hPbar_eq_sUnion : Pbar_param = ⋃₀ Tbar)
    (hNplane_eq : Nplane δ Pbar_param = ENat.toENNReal Tbar.encard)
    (hTbar_lower_strong : ENNReal.ofReal (δ ^ (-2 * s + η_work / 2) / (98 * C_work' ^ 4)) ≤
      ENat.toENNReal Tbar.encard)
    {Pz_trim : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2))}
    {X : ℝ → Set ℝ} {P : Set (EuclideanSpace ℝ (Fin 2))}
    {Zf : Finset (EuclideanSpace ℝ (Fin 2))}
    {Pz : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2))}
    (hZf : (Zf : Set _) = productLikeIncidenceSet Y X)
    (hPz : ∀ z ∈ productLikeIncidenceSet Y X,
      (Pz z ⊆ P) ∧ (IsDeltaSCSet (d := 2) δ s C (Pz z)) ∧
        (∀ p ∈ Pz z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ))
    (hPz_trim_sub : ∀ z ∈ productLikeIncidenceSet Y X, Pz_trim z ⊆ Pz z)
    (hPz_trim_delta : ∀ z ∈ productLikeIncidenceSet Y X,
      IsDeltaSCSet (d := 2) δ s C_work' (Pz_trim z))
    (hPz_trim_approx : ∀ z ∈ productLikeIncidenceSet Y X,
      ∀ p ∈ Pz_trim z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ)
    (hPz_trim_bounded : ∀ z ∈ productLikeIncidenceSet Y X, Bornology.IsBounded (Pz_trim z))
    (hP_small : ENat.toENNReal (dyadicCoveringNumber δ P) <
      ENNReal.ofReal (δ ^ (-(2 * s + η))))
    (hXy_delta : ∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ ∧
      IsProductLikeRealDeltaSCSet δ s C (X y))
    (hq_bad_pos : 0 < q_bad)
    (h_qbad_eq : q_bad = rhoExc η_work ε τ κ0 rho_sel)
    (h_product_bound : (1 + ((3 * C * 2 ^ τ) + 1) * (2 * R * Real.sqrt 2) ^ (2 * κ0) *
        (1 + (2 * κ0) / (τ - 2 * κ0))) *
      robust_projection.energyBoundConstant C_Pbar s κ0 ≤
      δ ^ (-(qKaufBase η_work τ κ0)))
    (h_multiplicity_points : ∀ p ∈ Pbar_param,
      ENat.toENNReal {y ∈ Y | p ∈ T_y_points y}.encard ≥
        ENNReal.ofReal (c_mult / 2) * ENat.toENNReal Y.encard)
    (h_proj_bound : ∀ y ∈ Y,
      Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) (T_y_points y)) ≤
      ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar_param)).toReal)))
    (h_ed_kaufman_absorb :
      (1 + ((3 * C * 2 ^ τ) + 1) * (2 * R * Real.sqrt 2) ^ (2 * κ0) *
        (1 + (2 * κ0) / (τ - 2 * κ0))) *
      robust_projection.energyBoundConstant C_Pbar s κ0 ≤
      δ ^ (-q_bad) * ((c_mult / 2) / 8)) :
    ∃ (ν : Measure ℝ)
      (E : Finset (EuclideanSpace ℝ (Fin 2)))
      (μE : Measure (EuclideanSpace ℝ (Fin 2)))
      (θ1 θ2 θ3 : ℝ)
      (E1 E2 E3 : Set (EuclideanSpace ℝ (Fin 2)))
      (E3fin : Finset (EuclideanSpace ℝ (Fin 2)))
      (μE3 : Measure (EuclideanSpace ℝ (Fin 2))),
      IsDirectionFrostman δ τ (3 * C * 2 ^ τ) ν ∧
      ν.support = Y ∧ ν.support ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ y ∈ Y, ν {y} = ENNReal.ofReal (1 / (Y.ncard : ℝ))) ∧
      E.Nonempty ∧ IsProbabilityMeasure μE ∧ μE.support ⊆ Pbar_param ∧
      (μE = ∑ p ∈ E, (1 / (E.card : ENNReal)) • Measure.dirac p) ∧
      robust_projection_main.rieszEnergy (2 * κ0) hδ_pos μE ≤
        ENNReal.ofReal (robust_projection.energyBoundConstant C_Pbar s κ0) ∧
      (E.card : ENNReal) = Nplane δ Pbar_param ∧
      (∀ Q ∈ dyadicCubesMeeting δ Pbar_param,
        ∃! (p : EuclideanSpace ℝ (Fin 2)), p ∈ E ∧ p ∈ Q ∩ Pbar_param) ∧
      E3 ⊆ E2 ∧ E2 ⊆ E1 ∧ E1 ⊆ (E : Set _) ∧ E3.Nonempty ∧
      ENat.toENNReal E1.encard ≥ ENNReal.ofReal (δ ^ rho_sel) * (E.card : ENNReal) ∧
      ENat.toENNReal E2.encard ≥ ENNReal.ofReal (δ ^ rho_sel) * ENat.toENNReal E1.encard ∧
      ENat.toENNReal E3.encard ≥ ENNReal.ofReal (δ ^ rho_sel) * ENat.toENNReal E2.encard ∧
      ENat.toENNReal E3.encard ≥ ENNReal.ofReal (δ ^ (3 * rho_sel)) * (E.card : ENNReal) ∧
      IsProbabilityMeasure μE3 ∧ μE3.support = E3 ∧ (E3fin : Set _) = E3 ∧
      (μE3 = ∑ p ∈ E3fin, (1 / ENat.toENNReal E3.encard) • Measure.dirac p) ∧
      (∀ θ ∈ ({θ1, θ2, θ3} : Set ℝ),
        robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ + p 1) μE3) ≤
        ENNReal.ofReal (δ ^ (-6 * rho_sel)) *
          robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
            (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ + p 1) μE)) ∧
      (∀ θ ∈ ({θ1, θ2, θ3} : Set ℝ),
        robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ + p 1) μE3) ≤
        ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel)))) ∧
      |θ1 - θ2| ≥ δ ^ rho_sep ∧ |θ1 - θ3| ≥ δ ^ rho_sep ∧ |θ2 - θ3| ≥ δ ^ rho_sep ∧
      θ1 < θ3 ∧ θ3 < θ2 ∧
      θ1 ∈ Set.Icc (0 : ℝ) 1 ∧ θ2 ∈ Set.Icc (0 : ℝ) 1 ∧ θ3 ∈ Set.Icc (0 : ℝ) 1 ∧
      (∀ y ∈ ({θ1, θ2, θ3} : Set ℝ),
        robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) μE) ≤
        ENNReal.ofReal (δ ^ (-q_bad))) ∧
      (∀ y ∈ ({θ1, θ2, θ3} : Set ℝ),
        Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) E3) ≤
        ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar_param)).toReal))) ∧
      robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) =>
          ((θ3 - θ1) / (θ2 - θ1)) * (p 0 * θ2 + p 1)) μE3) ≤
        ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep))) ∧
      robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) =>
          ((θ2 - θ3) / (θ2 - θ1)) * (p 0 * θ1 + p 1)) μE3) ≤
        ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep))) := by
  let c_endgame : ℝ := c_mult / 2
  let C_Y : ℝ := C
  let C_ν : ℝ := 3 * C_Y * 2 ^ τ
  let C_plan : ℝ := robust_projection.energyBoundConstant C_Pbar s κ0
  let C_Kaufman : ℝ := 1 + (C_ν + 1) * (2 * R * Real.sqrt 2) ^ (2 * κ0) *
      (1 + (2 * κ0) / (τ - 2 * κ0))
  have hc_endgame_pos : 0 < c_endgame := by
    dsimp only [c_endgame]
    positivity
  have hC_Y_pos : 0 < C_Y := by
    dsimp only [C_Y]
    linarith [hC_ge1]
  have hR_pos : 0 < R := by linarith [hR_ge1]
  have hC_Pbar_pos : 0 < C_Pbar := by
    rw [hC_Pbar_eq]
    positivity
  have hC_Kauf_nonneg : 0 ≤ C_Kaufman := by
    dsimp only [C_Kaufman, C_ν]
    have h2 : 0 < τ - 2 * κ0 := by linarith [h2kappa_lt_tau]
    positivity
  have hC_plan_nonneg : 0 ≤ C_plan := by
    dsimp only [C_plan]
    have h_main_pos : 0 < robust_projection.energyBoundConstant C_Pbar s κ0 :=
      robust_projection.energyBoundConstant_pos hC_Pbar_pos hkappa_pos hkappa_lt_s
    exact le_of_lt h_main_pos
  have hrho_sep_le_one' : rho_sep ≤ 1 := by
    have h1 : rho_sep ≤ η_work / κ0 := hrho_sep_le
    have h2 : η_work / κ0 ≤ 1 := by
      have h3 : η_work ≤ κ0 := hη_work_le_kappa0
      have h4 : 0 < κ0 := hkappa_pos
      exact (div_le_one h4).mpr h3
    linarith
  have h_cendgame_eq_csel : c_endgame = c_sel := by
    dsimp only [c_endgame]
    have h1 : c_mult = cPhase0 δ η (35 * C) := by
      rw [hc_mult_eq, hC_work'_eq]
      have h2 : η_work / 2 = η := by linarith [hη_work_eq_two]
      rw [h2] <;> rfl
    rw [h1, hc_sel_eq] <;> ring
  have hδ_rho_sel_le_c2 : δ ^ rho_sel ≤ c_endgame / 2 := by
    rw [h_cendgame_eq_csel]
    exact hδ_rho_sel_le_c_sel2
  have hδ_rho_sel_le_c8 : δ ^ rho_sel ≤ c_endgame / 8 := by
    rw [h_cendgame_eq_csel]
    exact hδ_rho_sel_le_c_sel8
  have h_small_neighborhood' : 2 * (3 * C_Y * 2 ^ τ) * (δ ^ rho_sep) ^ τ ≤ c_endgame / 8 := by
    have h1 : C_Y = C := by rfl
    rw [h1, h_cendgame_eq_csel]
    exact h_small_neighborhood
  have hC_Kaufman_eq : C_Kaufman = (1 + ((3 * C_Y * 2 ^ τ) + 1) * (2 * R * Real.sqrt 2) ^ (2 * κ0) * (1 + (2 * κ0) / (τ - 2 * κ0))) := by
    dsimp only [C_Kaufman, C_ν, C_Y] <;> ring
  have hC_plan_eq : C_plan = robust_projection.energyBoundConstant C_Pbar s κ0 := by rfl
  have h_kaufman_absorb : C_Kaufman * C_plan ≤ δ ^ (-q_bad) * (c_endgame / 8) := by
    rw [hC_Kaufman_eq, hC_plan_eq]
    exact h_ed_kaufman_absorb
  have hP_param_in_Rbox : Pbar_param ⊆ {p : EuclideanSpace ℝ (Fin 2) | ∀ i, p i ∈ Set.Icc (-R) R} := by
    intro p hp; have h : |p 0| ≤ R ∧ |p 1| ≤ R := hPbar_Rbox p hp; intro i; fin_cases i
    · have h1 : -R ≤ p 0 ∧ p 0 ≤ R := abs_le.mp h.1; exact ⟨h1.1, h1.2⟩
    · have h2 : -R ≤ p 1 ∧ p 1 ≤ R := abs_le.mp h.2; exact ⟨h2.1, h2.2⟩
  exact exact_endgame_steps_1_4_generalized_v3
    (C_trim := C_work') rho_sel rho_sep
    (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one) (hδ_dyadic := hδ_dyadic) (hδ_le_one := hδ_le_one)
    (hs_pos := hs_pos) (hτ_pos := hτ_pos) (hκ0_pos := hkappa_pos) (hκ0_lt_s := hkappa_lt_s)
    (hτ_gt_2κ0 := h2kappa_lt_tau) (hrho_sel_pos := hrho_sel_pos) (hrho_sep_pos := hrho_sep_pos)
    (hrho_sep_le_one := hrho_sep_le_one') (hL_pos := hL_exp_pos) (hη_pos := hη_pos)
    (hc_pos := hc_endgame_pos) (hC_Y_pos := hC_Y_pos) (hC_Pbar_pos := hC_Pbar_pos) (hR_pos := hR_pos)
    (q_bad := q_bad) (hq_bad_pos := hq_bad_pos) (hR_ge1 := hR_ge1)
    (hδ_rho_sel_le_c2 := hδ_rho_sel_le_c2) (h_small_neighborhood := h_small_neighborhood')
    (h_kaufman_absorb := h_kaufman_absorb)
    (hY_grid := hY_sub) (hY_delta := hY_delta) (hY_fin := hY_fin) (hY_nonempty := hY_nonempty)
    (hPbar_delta := hPbar_delta) (hPbar_nonempty := hPbar_nonempty) (hPbar_size := hPbar_size)
    (hP_param_in_Rbox := hP_param_in_Rbox) (hT_y_points_sub := hT_y_points_sub)
    (h_multiplicity_points := h_multiplicity_points) (h_proj_bound := h_proj_bound)

/-- Combined boundary theorem: outer hypotheses → Helper2 outputs.

Calls phase0_result_helper (Helper1), then glue_H1_to_H2, then
endgame_directions_helper (Helper2). Returns ALL Helper2 outputs.
This definitively closes the H1→H2 boundary. -/
lemma H1_to_H2_full
    {δ s τ κ0 η η_work ε L_exp p_projective C C_work K_ring εnc rho_sel rho_sep : ℝ}
    -- Core positivity/order
    (hδ_pos : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales) (hδ_le_one : δ ≤ 1)
    (hs_pos : 0 < s) (hs_lt_one : s < 1) (hτ_pos : 0 < τ)
    (hkappa_pos : 0 < κ0) (hkappa_lt_s : κ0 < s) (h2kappa_lt_tau : 2 * κ0 < τ)
    (hη_pos : 0 < η) (hη_work_pos : 0 < η_work) (hη_work_eq_two : η_work = 2 * η)
    (hε_pos : 0 < ε)
    (hL_exp_pos : 0 < L_exp) (hL_exp_eq_seven : L_exp = 7)
    (hη_work_le_kappa0 : η_work ≤ κ0)
    (hp_ge_10 : 10 ≤ p_projective)
    (h5η_work_lt : 5 * η_work < 2 * (s - κ0))
    (h4η_work_lt_tau : 4 * η_work < τ)
    (hC_ge1 : 1 ≤ C) (hC_le_target : C ≤ δ ^ (-η))
    (hC_work_eq : C_work = 35 * C) (hC_work_ge1 : 1 ≤ C_work) (hC_work_le : C_work ≤ δ ^ (-η_work))
    (hK_ring_ge1 : 1 ≤ K_ring)
    -- rho parameters
    (hrho_sel_eq : rho_sel = rhoSelDefault η_work)
    (hrho_sep_le : rho_sep ≤ η_work / κ0)
    (h_frostman_gap : 2 * η_work < τ * rho_sep)
    -- budgets
    (hG_eta_work_le : gapCoefficientV4 L_exp κ0 p_projective τ * η_work ≤ εnc / 2)
    (h_qTotalV4_le_enc4 : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤ εnc / 4)
    -- numeric thresholds
    (c_sel : ℝ) (hc_sel_pos : 0 < c_sel) (hc_sel_eq : c_sel = cPhase0 δ η (35 * C) / 2)
    (hδ_rho_sel_le_c_sel2 : δ ^ rho_sel ≤ c_sel / 2)
    (hδ_rho_sel_le_c_sel8 : δ ^ rho_sel ≤ c_sel / 8)
    (h_small_neighborhood : 2 * (3 * C * 2 ^ τ) * (δ ^ rho_sep) ^ τ ≤ c_sel / 8)
    (h_plan_absorb : planConstant s κ0 ≤ δ ^ (-(qPlan η_work - 5 * η_work)))
    (h_Kauf_absorb : kaufmanConstant τ κ0 ≤ δ ^ (-(51 * η_work / 100)))
    (h_box_bound : (2 ^ 20 : ℝ) ≤ δ ^ (-(η_work / 100)))
    (h_proj_absorb : (126 : ℝ) * Real.sqrt 98 * (35 : ℝ)^2 ≤ δ ^ (-η))
    -- Phase0 thresholds
    (h_pbar_98 : (98 : ℝ) ≤ δ ^ (-(2 * s - 2 * κ0 - 5 * η_work)))
    (hδ_box_small : δ ^ (-(qBox η_work τ)) ≥ 8 * (1 + (1 + 12 * δ) *
        ((6 * (35 * C) * 2 ^ τ) /
         (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2))) ^ (1 / τ) + 6 * δ))
    (h_qbox_lt_one : qBox η_work τ < 1)
    (h_extract_log_absorb : extractLogAbsorbHyp δ εnc η_work τ κ0 (qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep))
    -- Data
    {Y : Set ℝ} {X : ℝ → Set ℝ} {P : Set (EuclideanSpace ℝ (Fin 2))}
    {Zf : Finset (EuclideanSpace ℝ (Fin 2))}
    {Pz : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2))}
    (hY_sub : Y ⊆ productLikeUnitGrid δ)
    (hY_delta : IsProductLikeRealDeltaSCSet δ τ C Y)
    (hXy_delta : ∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ ∧ IsProductLikeRealDeltaSCSet δ s C (X y))
    (hZf : (Zf : Set _) = productLikeIncidenceSet Y X)
    (hPz : ∀ z ∈ Zf, Pz z ⊆ P ∧ IsDeltaSCSet δ s C (Pz z) ∧ ∀ p ∈ Pz z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ)
    (hP_small : ENat.toENNReal (dyadicCoveringNumber δ P) < ENNReal.ofReal (δ ^ (-(2 * s + η)))) :
    ∃ (Pbar_param : Set (EuclideanSpace ℝ (Fin 2)))
      (C_Pbar q_bad R : ℝ)
      (k_R : ℕ)
      (ν : Measure ℝ)
      (E : Finset (EuclideanSpace ℝ (Fin 2)))
      (μE : Measure (EuclideanSpace ℝ (Fin 2)))
      (θ1 θ2 θ3 : ℝ)
      (E1 E2 E3 : Set (EuclideanSpace ℝ (Fin 2)))
      (E3fin : Finset (EuclideanSpace ℝ (Fin 2)))
      (μE3 : Measure (EuclideanSpace ℝ (Fin 2)))
      (T_y_points : ℝ → Set (EuclideanSpace ℝ (Fin 2)))
      (c_mult : ℝ),
      (∀ y ∈ Y, T_y_points y ⊆ Pbar_param) ∧
      ENNReal.ofReal (δ ^ (-2 * s + η_work / 2) / (98 * C_work ^ 4)) ≤ Nplane δ Pbar_param ∧
      IsDirectionFrostman δ τ (3 * C * 2 ^ τ) ν ∧
      ν.support = Y ∧
      ν.support ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ y ∈ Y, ν {y} = ENNReal.ofReal (1 / (Y.ncard : ℝ))) ∧
      E.Nonempty ∧
      IsProbabilityMeasure μE ∧
      μE.support ⊆ Pbar_param ∧
      (μE = ∑ p ∈ E, (1 / (E.card : ENNReal)) • Measure.dirac p) ∧
      robust_projection_main.rieszEnergy (2 * κ0) hδ_pos μE ≤
        ENNReal.ofReal (robust_projection.energyBoundConstant C_Pbar s κ0) ∧
      (E.card : ENNReal) = Nplane δ Pbar_param ∧
      (∀ Q ∈ dyadicCubesMeeting δ Pbar_param,
        ∃! (p : EuclideanSpace ℝ (Fin 2)), p ∈ E ∧ p ∈ Q ∩ Pbar_param) ∧
      E3 ⊆ E2 ∧ E2 ⊆ E1 ∧ E1 ⊆ (E : Set _) ∧
      E3.Nonempty ∧
      ENat.toENNReal E1.encard ≥ ENNReal.ofReal (δ ^ rho_sel) * (E.card : ENNReal) ∧
      ENat.toENNReal E2.encard ≥ ENNReal.ofReal (δ ^ rho_sel) * ENat.toENNReal E1.encard ∧
      ENat.toENNReal E3.encard ≥ ENNReal.ofReal (δ ^ rho_sel) * ENat.toENNReal E2.encard ∧
      ENat.toENNReal E3.encard ≥ ENNReal.ofReal (δ ^ (3 * rho_sel)) * (E.card : ENNReal) ∧
      IsProbabilityMeasure μE3 ∧
      μE3.support = E3 ∧
      (E3fin : Set _) = E3 ∧
      (μE3 = ∑ p ∈ E3fin, (1 / ENat.toENNReal E3.encard) • Measure.dirac p) ∧
      (∀ θ ∈ ({θ1, θ2, θ3} : Set ℝ),
        robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ + p 1) μE3) ≤
        ENNReal.ofReal (δ ^ (-6 * rho_sel)) *
          robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
            (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ + p 1) μE)) ∧
      (∀ θ ∈ ({θ1, θ2, θ3} : Set ℝ),
        robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ + p 1) μE3) ≤
        ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel)))) ∧
      |θ1 - θ2| ≥ δ ^ rho_sep ∧
      |θ1 - θ3| ≥ δ ^ rho_sep ∧
      |θ2 - θ3| ≥ δ ^ rho_sep ∧
      θ1 < θ3 ∧ θ3 < θ2 ∧
      θ1 ∈ Set.Icc (0 : ℝ) 1 ∧
      θ2 ∈ Set.Icc (0 : ℝ) 1 ∧
      θ3 ∈ Set.Icc (0 : ℝ) 1 ∧
      (∀ y ∈ ({θ1, θ2, θ3} : Set ℝ),
        robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) μE) ≤
        ENNReal.ofReal (δ ^ (-q_bad))) ∧
      (∀ y ∈ ({θ1, θ2, θ3} : Set ℝ),
        Nreal δ (Set.image (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * y + p 1) E3) ≤
        ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar_param)).toReal))) ∧
      robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) =>
          ((θ3 - θ1) / (θ2 - θ1)) * (p 0 * θ2 + p 1)) μE3) ≤
        ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep))) ∧
      robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) =>
          ((θ2 - θ3) / (θ2 - θ1)) * (p 0 * θ1 + p 1)) μE3) ≤
        ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep))) ∧
      q_bad = rhoExc η_work ε τ κ0 rho_sel ∧
      R = (2 : ℝ) ^ k_R ∧
      1 ≤ R ∧
      Pbar_param ⊆ {p : EuclideanSpace ℝ (Fin 2) | ∀ i, p i ∈ Set.Icc (-R) R} ∧
      4 * R ≤ δ ^ (-(qBox η_work τ)) ∧
      E3 ⊆ Pbar_param ∧
      (Nplane δ Pbar_param < ENNReal.ofReal (δ ^ (-(2 * s + η)))) ∧
      (∀ y ∈ Y,
        Nreal δ (Set.image (fun (q : EuclideanSpace ℝ (Fin 2)) => q 0 * y + q 1) (T_y_points y)) ≤
        ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal))) ∧
      c_mult = δ ^ (η_work / 2) / (7 * (35 * C) ^ 2) ∧
      (∀ p ∈ Pbar_param,
        ENat.toENNReal ({y ∈ Y | p ∈ T_y_points y}.encard) ≥
          ENNReal.ofReal (c_mult / 2) * ENat.toENNReal Y.encard) := by
  -- Derive hδ_lt_one
  have hδ_lt_one : δ < 1 := by
    by_contra h
    have hδ_eq_one : δ = 1 := by linarith only [h, hδ_le_one]
    have h1 : δ ^ (-η_work) = 1 := by rw [hδ_eq_one]; simp
    have h2 : C_work ≤ 1 := by rw [h1] at hC_work_le; exact hC_work_le
    have h3 : (35 : ℝ) ≤ C_work := by
      have h4 : C_work = 35 * C := hC_work_eq
      rw [h4]; have h5 : (1 : ℝ) ≤ C := hC_ge1; nlinarith only [h4, h5]
    linarith only [h2, h3]
  -- Derive hY_fin, hY_nonempty
  have hY_fin : Y.Finite := Set.Finite.subset (productLikeUnitGrid_finite hδ_pos) hY_sub
  have hY_nonempty : Y.Nonempty := by
    have h1 : (productLikeRealLineCopy Y).Nonempty := hY_delta.2.1
    rcases h1 with ⟨p, hp⟩
    have h2 : p 0 ∈ Y := by delta productLikeRealLineCopy at hp; exact hp
    exact ⟨p 0, h2⟩

  -- Step 1: Call Helper1 (phase0_result_helper)
  rcases phase0_result_helper
      (hδ_pos := hδ_pos) (hδ_dyadic := hδ_dyadic) (hδ_le_one := hδ_le_one)
      (hs_pos := hs_pos) (hs_lt_one := hs_lt_one) (hτ_pos := hτ_pos)
      (hkappa_pos := hkappa_pos) (h2kappa_lt_tau := h2kappa_lt_tau)
      (hη_work_pos := hη_work_pos) (hη_work_eq_two := hη_work_eq_two)
      (hε_pos := hε_pos)
      (h5η_work_lt := h5η_work_lt)
      (h4η_work_lt_tau := h4η_work_lt_tau)
      (hC_ge1 := hC_ge1) (hC_work_eq := hC_work_eq) (hC_work_le := hC_work_le)
      (h_frostman_gap := h_frostman_gap) (hrho_sel_eq := hrho_sel_eq)
      (h_pbar_98 := h_pbar_98) (hδ_box_small := hδ_box_small)
      (h_qTotalV4_le_enc4 := h_qTotalV4_le_enc4) (h_qbox_lt_one := h_qbox_lt_one)
      (h_extract_log_absorb := h_extract_log_absorb)
      (hY_sub := hY_sub) (hY_delta := hY_delta) (hXy_delta := hXy_delta)
      (hZf := hZf) (hPz := hPz) (hP_small := hP_small)
    with ⟨Pz_trim, U_y, T, Tbar, Pbar_param, T_y_points, C_work', c_mult, C_Pbar, R, k_R,
      hU_y_eq, hT_eq,
      hPz_trim_sub, hPz_trim_delta, hPz_trim_approx, hPz_trim_bounded,
      hC_work'_eq, hc_mult_eq, hC_Pbar_eq, hR_eq_pow2,
      hTbar_sub_T, hTbar_finite, hTbar_grid, hPbar_eq_sUnion, hNplane_eq, hPbar_size,
      hPbar_delta, hPbar_nonempty,
      hT_y_points_eq, hT_y_points_sub,
      h_multiplicity, h_approx_fiber,
      hPbar_Rbox_set, h4R_le_qbox,
      hC_work'_pos, hc_mult_pos, hR_ge1, hR_pos, hTbar_lower⟩

  -- Convert hT_y_points_eq to glue's expected format (∀ y ∈ Y, ...)
  have hT_y_points_eq' : ∀ y ∈ Y, T_y_points y =
      ⋃₀ (Tbar ∩ (⋃ x ∈ X y, dyadicCubesMeeting δ (Pz_trim (mkPoint2 x y)))) := by
    intro y _
    rw [hT_y_points_eq y, hU_y_eq y]

  -- Step 2: Call glue_H1_to_H2 to derive all gap facts
  rcases glue_H1_to_H2 (ε := ε)
      (hδ_pos := hδ_pos) (hδ_dyadic := hδ_dyadic) (hδ_le_one := hδ_le_one)
      (hs_pos := hs_pos) (hs_lt_one := hs_lt_one) (hτ_pos := hτ_pos)
      (hkappa_pos := hkappa_pos) (hkappa_lt_s := hkappa_lt_s) (h2kappa_lt_tau := h2kappa_lt_tau)
      (hη_pos := hη_pos) (hη_work_pos := hη_work_pos) (hη_work_eq_two := hη_work_eq_two)
      (hC_ge1 := hC_ge1) (hC_work_eq := hC_work_eq) (hC_work_le := hC_work_le)
      (hC_le_target := hC_le_target)
      (h_frostman_gap := h_frostman_gap) (hrho_sel_eq := hrho_sel_eq)
      (hrho_sep_le := hrho_sep_le) (hη_work_le_kappa0 := hη_work_le_kappa0)
      (hL_exp_pos := hL_exp_pos) (hL_exp_eq_seven := hL_exp_eq_seven)
      (h_proj_absorb := h_proj_absorb) (h_plan_absorb := h_plan_absorb)
      (h_Kauf_absorb := h_Kauf_absorb)
      (c_sel := c_sel) (hδ_rho_sel_le_c_sel8 := hδ_rho_sel_le_c_sel8)
      (hc_sel_eq := hc_sel_eq)
      (hY_sub := hY_sub) (hY_delta := hY_delta) (hXy_delta := hXy_delta)
      (hZf := hZf) (hPz := hPz) (hP_small := hP_small)
      (hPz_trim_sub := hPz_trim_sub) (hPz_trim_approx := hPz_trim_approx)
      (hPz_trim_bounded := hPz_trim_bounded)
      (hC_work'_eq := hC_work'_eq) (hc_mult_eq := hc_mult_eq) (hC_Pbar_eq := hC_Pbar_eq)
      (hTbar_finite := hTbar_finite) (hTbar_grid := hTbar_grid)
      (hPbar_eq_sUnion := hPbar_eq_sUnion) (hT_y_points_eq := hT_y_points_eq')
      (hPbar_Rbox_set := hPbar_Rbox_set) (h4R_le_qbox := h4R_le_qbox)
      (hC_work'_pos := hC_work'_pos) (hc_mult_pos := hc_mult_pos)
      (hR_ge1 := hR_ge1) (hTbar_lower := hTbar_lower)
    with ⟨hδ_lt_one', hY_fin', hY_nonempty', hrho_sel_pos, hrho_sep_pos, hrho_sep_le_one,
      hPbar_Rbox, hq_bad_pos, h_qbad_eq, h_product_bound, h_proj_bound, h_ed_kaufman_absorb⟩

  -- Prove Pz z ⊆ P for all incidence points
  have hPz_sub_P : ∀ z ∈ productLikeIncidenceSet Y X, Pz z ⊆ P := by
    intro z hz
    have hz' : z ∈ Zf := by
      have hz_set : z ∈ (Zf : Set _) := hZf.symm ▸ hz
      exact_mod_cast hz_set
    exact (hPz z hz').1

  -- Prove Tbar ⊆ dyadicCubesMeeting δ P
  have hTbar_sub_meeting : Tbar ⊆ dyadicCubesMeeting δ P := by
    intro Q hQ
    have hQ_in_T : Q ∈ T := hTbar_sub_T hQ
    rw [hT_eq] at hQ_in_T
    simp only [Set.mem_iUnion] at hQ_in_T
    rcases hQ_in_T with ⟨y, hy, hQ_in_Uy⟩
    rw [hU_y_eq y] at hQ_in_Uy
    simp only [Set.mem_iUnion] at hQ_in_Uy
    rcases hQ_in_Uy with ⟨x, hx, hQ_meeting⟩
    have h1 : Q ∈ dyadicCubesMeeting δ (Pz_trim (mkPoint2 x y)) := hQ_meeting
    have hz_in : mkPoint2 x y ∈ productLikeIncidenceSet Y X := by
      simp only [productLikeIncidenceSet, Set.mem_iUnion]
      exact ⟨y, hy, by simp [mkPoint2, hx]⟩
    have h2 : Pz_trim (mkPoint2 x y) ⊆ P :=
      subset_trans (hPz_trim_sub (mkPoint2 x y) hz_in) (hPz_sub_P (mkPoint2 x y) hz_in)
    have h2' : Q ∩ Pz_trim (mkPoint2 x y) ⊆ Q ∩ P := Set.inter_subset_inter_right _ h2
    exact ⟨h1.1, Set.Nonempty.mono h2' h1.2⟩

  -- hPbar_small_coeff1 via pbar_small_bridge
  have hPbar_small_coeff1 : Nplane δ Pbar_param < ENNReal.ofReal (δ ^ (-(2 * s + η))) :=
    pbar_small_bridge
      (hδ_pos := hδ_pos)
      (hPbar_eq_sUnion := hPbar_eq_sUnion)
      (hTbar_sub_cubes := hTbar_grid)
      (hTbar_finite := hTbar_finite)
      (hTbar_sub_meeting := hTbar_sub_meeting)
      (hP_small := hP_small)

  -- h_raw_proj_bound (no C factor — strongest version)
  have h_raw_proj_bound : ∀ y ∈ Y,
      Nreal δ (Set.image (fun (q : EuclideanSpace ℝ (Fin 2)) => q 0 * y + q 1) (T_y_points y)) ≤
      ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) :=
    h_proj_bound

  -- Define q_bad
  let q_bad : ℝ := rhoExc η_work ε τ κ0 rho_sel

  -- Convert hPz from domain Zf to domain productLikeIncidenceSet Y X
  have hPz' : ∀ z ∈ productLikeIncidenceSet Y X,
      (Pz z ⊆ P) ∧ (IsDeltaSCSet (d := 2) δ s C (Pz z)) ∧
        (∀ p ∈ Pz z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ) := by
    intro z hz
    have hz' : z ∈ Zf := by
      have hz_set : z ∈ (Zf : Set _) := hZf.symm ▸ hz
      exact_mod_cast hz_set
    exact hPz z hz'

  -- Step 3: Call Helper2 (endgame_directions_helper)
  rcases endgame_directions_helper (q_bad := q_bad) (ε := ε)
    (hδ_pos := hδ_pos) (hδ_dyadic := hδ_dyadic) (hδ_le_one := hδ_le_one)
    (hδ_lt_one := hδ_lt_one)
    (hs_pos := hs_pos) (hs_lt_one := hs_lt_one) (hτ_pos := hτ_pos)
    (hkappa_pos := hkappa_pos) (hkappa_lt_s := hkappa_lt_s) (h2kappa_lt_tau := h2kappa_lt_tau)
    (hη_pos := hη_pos) (hη_work_pos := hη_work_pos) (hη_work_eq_two := hη_work_eq_two)
    (hL_exp_pos := hL_exp_pos) (hL_exp_eq_seven := hL_exp_eq_seven)
    (hη_work_le_kappa0 := hη_work_le_kappa0) (hp_ge_10 := hp_ge_10)
    (hC_ge1 := hC_ge1) (hC_le_target := hC_le_target)
    (hC_work_eq := hC_work_eq) (hC_work_ge1 := hC_work_ge1) (hC_work_le := hC_work_le)
    (hK_ring_ge1 := hK_ring_ge1)
    (hrho_sel_pos := hrho_sel_pos) (hrho_sep_pos := hrho_sep_pos)
    (hrho_sep_le_one := hrho_sep_le_one) (hrho_sel_eq := hrho_sel_eq)
    (hrho_sep_le := hrho_sep_le) (h_frostman_gap := h_frostman_gap)
    (hG_eta_work_le := hG_eta_work_le) (h_qTotalV4_le_enc4 := h_qTotalV4_le_enc4)
    (c_sel := c_sel) (hc_sel_pos := hc_sel_pos) (hc_sel_eq := hc_sel_eq)
    (hδ_rho_sel_le_c_sel2 := hδ_rho_sel_le_c_sel2)
    (hδ_rho_sel_le_c_sel8 := hδ_rho_sel_le_c_sel8)
    (h_small_neighborhood := h_small_neighborhood)
    (h_plan_absorb := h_plan_absorb) (h_Kauf_absorb := h_Kauf_absorb)
    (h_box_bound := h_box_bound) (h_proj_absorb := h_proj_absorb)
    (R := R) (k_R := k_R) (hR_eq_pow2 := hR_eq_pow2) (hR_ge1 := hR_ge1)
    (h4R_le_qbox := h4R_le_qbox)
    (hY_sub := hY_sub) (hY_delta := hY_delta) (hY_fin := hY_fin) (hY_nonempty := hY_nonempty)
    (C_work' := C_work') (c_mult := c_mult) (hC_work'_eq := hC_work'_eq)
    (hc_mult_eq := hc_mult_eq) (hC_work'_pos := hC_work'_pos) (hc_mult_pos := hc_mult_pos)
    (C_Pbar := C_Pbar) (hC_Pbar_eq := hC_Pbar_eq)
    (hPbar_delta := hPbar_delta) (hPbar_nonempty := hPbar_nonempty)
    (hPbar_size := hPbar_size) (hPbar_Rbox := hPbar_Rbox)
    (hT_y_points_sub := hT_y_points_sub) (hTbar_finite := hTbar_finite)
    (hPbar_eq_sUnion := hPbar_eq_sUnion) (hNplane_eq := hNplane_eq)
    (hTbar_lower_strong := hTbar_lower)
    (Zf := Zf) (Pz := Pz) (hZf := hZf) (hPz := hPz')
    (hPz_trim_sub := hPz_trim_sub) (hPz_trim_delta := hPz_trim_delta)
    (hPz_trim_approx := hPz_trim_approx) (hPz_trim_bounded := hPz_trim_bounded)
    (hP_small := hP_small) (hXy_delta := hXy_delta)
    (hq_bad_pos := hq_bad_pos) (h_qbad_eq := h_qbad_eq)
    (h_product_bound := h_product_bound)
    (h_multiplicity_points := h_multiplicity)
    (h_proj_bound := h_proj_bound)
    (h_ed_kaufman_absorb := h_ed_kaufman_absorb)
    with ⟨ν, E, μE, θ1, θ2, θ3, E1, E2, E3, E3fin, μE3, h_all⟩

  have hq_bad_eq : q_bad = rhoExc η_work ε τ κ0 rho_sel := by
    dsimp only [q_bad] <;> rfl

  -- Destructure h_all to extract facts needed for hE3_sub_Pbar
  have h_all' := h_all
  rcases h_all' with ⟨h_frost, hν_supp, hν_Icc, hν_card, hE_ne, hμE_prob, hμE_supp, hμE_form, hE_energy, hE_card, hE_unique, hE3_sub_E2, hE2_sub_E1, hE1_sub_E, hE3_ne, hE1_card, hE2_card, hE3_card1, hE3_card2, hμE3_prob, hμE3_supp, hE3fin_coe, hμE3_form, h_energy_norm, h_energy_abs, h_sep12, h_sep13, h_sep23, h_ord13, h_ord32, hθ1_Icc, hθ2_Icc, hθ3_Icc, h_energy_dirs, h_proj_E3, h_coord0, h_coord1⟩

  -- Prove E3 ⊆ Pbar_param using support_uniform_finset
  have hE_supp_eq : (E : Set _) = μE.support := by
    rw [hμE_form]
    exact (support_uniform_finset hE_ne).symm
  have hE_sub_Pbar : (E : Set _) ⊆ Pbar_param := by
    rw [hE_supp_eq]
    exact hμE_supp
  have hE3_sub_E : E3 ⊆ (E : Set _) :=
    subset_trans hE3_sub_E2 (subset_trans hE2_sub_E1 hE1_sub_E)
  have hE3_sub_Pbar : E3 ⊆ Pbar_param :=
    subset_trans hE3_sub_E hE_sub_Pbar

  -- Assemble 44-way conjunction from destructured h_all (37) + 7 extra facts
  exact ⟨Pbar_param, C_Pbar, q_bad, R, k_R, ν, E, μE, θ1, θ2, θ3, E1, E2, E3, E3fin, μE3, T_y_points, c_mult,
    hT_y_points_sub,
    (by
      have h_eq : C_work' = C_work := by
        calc C_work' = 35 * C := hC_work'_eq
          _ = C_work := hC_work_eq.symm
      have h' := hTbar_lower
      rw [h_eq] at h'
      rw [hNplane_eq]
      exact h'),
    h_frost, hν_supp, hν_Icc, hν_card, hE_ne, hμE_prob, hμE_supp, hμE_form, hE_energy, hE_card, hE_unique,
    hE3_sub_E2, hE2_sub_E1, hE1_sub_E, hE3_ne, hE1_card, hE2_card, hE3_card1, hE3_card2,
    hμE3_prob, hμE3_supp, hE3fin_coe, hμE3_form,
    h_energy_norm, h_energy_abs, h_sep12, h_sep13, h_sep23, h_ord13, h_ord32,
    hθ1_Icc, hθ2_Icc, hθ3_Icc, h_energy_dirs, h_proj_E3, h_coord0, h_coord1,
    hq_bad_eq, hR_eq_pow2, hR_ge1, hPbar_Rbox_set, h4R_le_qbox, hE3_sub_Pbar,
    hPbar_small_coeff1, h_raw_proj_bound,
    (by rw [hc_mult_eq, hC_work'_eq] <;> ring),
    h_multiplicity⟩

/--
Stub for Bridge_H2_to_H3 (proved in .scratch/fjord/Bridge_H2_to_H3.lean).
Produces C_energy, C_extract, and absorption facts for Helper3.
-/
lemma bridge_H2_to_H3_stub
    {δ L_exp η_work ε κ0 p_projective τ rho_sel rho_sep εnc K_ring R : ℝ}
    {q_coord_energy q_norm_energy : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hL_nonneg : 0 ≤ L_exp) (hη_work_pos : 0 < η_work) (hε_pos : 0 < ε)
    (hεnc_pos : 0 < εnc) (hκ_pos : 0 < κ0) (hκ_le_one : κ0 ≤ 1)
    (hp_nonneg : 0 ≤ p_projective) (hτ_pos : 0 < τ)
    (hrho_sel_nonneg : 0 ≤ rho_sel) (hrho_sep_nonneg : 0 ≤ rho_sep)
    (hR_ge1 : 1 ≤ R)
    (h4R_le_qbox : 4 * R ≤ δ ^ (-(qBox η_work τ)))
    (h_qTotalV4_le_enc4 : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤ εnc / 4)
    (h_qbox_lt_one : qBox η_work τ < 1)
    (hK_ring_ge1 : 1 ≤ K_ring)
    (h_eq_norm : q_norm_energy = q_coord_energy + qEnergy η_work τ κ0)
    (h_qnorm_eq : q_norm_energy = qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep)
    (h_norm_pos : 0 < q_norm_energy)
    (h_extract_log_absorb : extractLogAbsorbHyp δ εnc η_work τ κ0 q_norm_energy) :
    let C_energy := (4 * R) ^ (2 * κ0)
    let C_extract := K_ring * δ ^ (-εnc / 2)
    (0 < C_energy) ∧ (0 < C_extract) ∧
    (C_energy * (δ / (4 * R)) ^ (-q_coord_energy) ≤ (δ / (4 * R)) ^ (-q_norm_energy)) ∧
    (robust_projection_main.energyToLargeMassDeltaSetC (δ / (4 * R)) κ0
      ((3 : ℝ) ^ (2 * κ0) * (δ / (4 * R)) ^ (-q_norm_energy)) ≤ C_extract) := by
  dsimp only
  set L_norm : ℝ := 4 * R with hL_norm_def
  set C_energy : ℝ := L_norm ^ (2 * κ0) with hC_energy_def
  set C_extract : ℝ := K_ring * δ ^ (-εnc / 2) with hC_extract_def
  set q_energy : ℝ := qEnergy η_work τ κ0 with hq_energy_def
  set q_box : ℝ := qBox η_work τ with hq_box_def
  have hL_norm_ge1 : 1 ≤ L_norm := by dsimp only [L_norm] <;> linarith
  have hL_norm_pos : 0 < L_norm := by linarith
  have h_x_pos : 0 < δ / L_norm := by positivity
  have h_x_lt_one : δ / L_norm < 1 := by
    have h2 : 1 ≤ L_norm := hL_norm_ge1
    have h3 : δ / L_norm ≤ δ := by
      calc δ / L_norm ≤ δ / 1 := by gcongr
           _ = δ := by ring
    have h4 : δ < 1 := hδ_lt_one
    linarith
  have hC_energy_pos : 0 < C_energy := by dsimp only [C_energy] <;> positivity
  have hC_extract_pos : 0 < C_extract := by dsimp only [C_extract] <;> positivity
  have hq_energy_pos : 0 < q_energy := by dsimp only [q_energy, qEnergy, qBox, qAbsorb] <;> positivity
  have hqBox_nonneg : 0 ≤ q_box := by dsimp only [q_box, qBox, qAbsorb] <;> positivity
  have hεnc_half_pos : 0 < εnc / 2 := by linarith [hεnc_pos]
  have hK_ring_pos : 0 < K_ring := by linarith [hK_ring_ge1]
  have h_small : (δ / L_norm) ^ q_energy ≤ 1 / C_energy := by
    have h_es : (δ / (4 * R)) ^ q_energy ≤ 1 / (4 * R) ^ (2 * κ0) :=
      energy_small_from_qbox hδ_pos hδ_lt_one hη_work_pos hτ_pos hκ_pos hR_ge1 h4R_le_qbox
    have h_eq1 : δ / L_norm = δ / (4 * R) := by dsimp only [L_norm] <;> rfl
    have h_eq2 : C_energy = (4 * R) ^ (2 * κ0) := by dsimp only [C_energy, L_norm] <;> rfl
    rw [h_eq1, h_eq2]; exact h_es
  have h1 : C_energy ≤ (δ / L_norm) ^ (-q_energy) :=
    weaken_const_by_delta h_x_pos h_x_lt_one hC_energy_pos hq_energy_pos h_small
  have h2 : (δ / L_norm) ^ (-q_norm_energy) =
      (δ / L_norm) ^ (-q_coord_energy) * (δ / L_norm) ^ (-q_energy) := by
    rw [h_eq_norm, ← Real.rpow_add h_x_pos] <;> ring_nf
  have h3 : (δ / L_norm) ^ (-q_coord_energy) ≥ 0 := by positivity
  have h_energy_absorb : C_energy * (δ / L_norm) ^ (-q_coord_energy) ≤ (δ / L_norm) ^ (-q_norm_energy) := by
    rw [h2]
    have h4 : C_energy * (δ / L_norm) ^ (-q_coord_energy) ≤
        (δ / L_norm) ^ (-q_energy) * (δ / L_norm) ^ (-q_coord_energy) := by
      exact mul_le_mul_of_nonneg_right h1 h3
    have h5 : (δ / L_norm) ^ (-q_energy) * (δ / L_norm) ^ (-q_coord_energy) =
        (δ / L_norm) ^ (-q_coord_energy) * (δ / L_norm) ^ (-q_energy) := by ring
    rw [h5] at h4; exact h4
  have hL_norm_le_qbox : L_norm ≤ δ ^ (-q_box) := by dsimp only [L_norm, q_box]; exact h4R_le_qbox
  have hδ'_le_quarter : δ / L_norm ≤ 1 / 4 := by
    dsimp only [L_norm]
    have hR_ge4 : (4 : ℝ) ≤ 4 * R := by have h : 1 ≤ R := hR_ge1; linarith
    have h : δ / (4 * R) ≤ δ / 4 := by gcongr
    have h' : δ < 1 := hδ_lt_one; linarith
  have h_norm_pos' : 0 < qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by
    rw [←h_qnorm_eq] <;> exact h_norm_pos
  have h_gap_half_raw : (1 + qBox η_work τ) * qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep < εnc / 2 :=
    extraction_gap_bridge_enc2 hL_nonneg hη_work_pos hε_pos hκ_pos hp_nonneg
      hτ_pos hrho_sel_nonneg hrho_sep_nonneg h_qTotalV4_le_enc4 h_qbox_lt_one h_norm_pos'
  have h_gap_half : (1 + q_box) * q_norm_energy < εnc / 2 := by
    have h1 : (1 + q_box) = (1 + qBox η_work τ) := by dsimp only [q_box] <;> ring
    have h2 : q_norm_energy = qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep := h_qnorm_eq
    rw [h1, h2]; exact h_gap_half_raw
  have h_extract_small : extractLogConstant κ0 * (Real.log (1 / (δ / L_norm))) ^ 2 ≤
      (δ / L_norm) ^ (-((εnc / 2) / (1 + q_box) - q_norm_energy)) := by
    have hL_norm_eq : L_norm = 4 * R := by rfl
    have h_goal : extractLogConstant κ0 * (Real.log (1 / (δ / (4 * R)))) ^ 2 ≤
        (δ / (4 * R)) ^ (-((εnc / 2) / (1 + q_box) - q_norm_energy)) :=
      extract_small_from_log_absorb hδ_pos hδ_lt_one hκ_pos hR_ge1 h4R_le_qbox
        hqBox_nonneg h_gap_half h_extract_log_absorb
    have h_eq1 : δ / L_norm = δ / (4 * R) := by dsimp only [L_norm] <;> rfl
    rw [h_eq1]; exact h_goal
  have hC_extract_large_raw : robust_projection_main.energyToLargeMassDeltaSetC (δ / L_norm) κ0
      ((3 : ℝ) ^ (2 * κ0) * (δ / L_norm) ^ (-q_norm_energy)) ≤
      K_ring * δ ^ (-(εnc / 2)) :=
    extraction_constant_bound
      (εnc := εnc / 2)
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hL_ge1 := hL_norm_ge1) (hL_le_qbox := hL_norm_le_qbox)
      (hκ_pos := hκ_pos) (hκ_le_one := hκ_le_one)
      (hεnc_pos := hεnc_half_pos) (hK_ring_pos := hK_ring_pos)
      (hK_ring_ge_one := hK_ring_ge1) (hq_norm_pos := h_norm_pos)
      (hqBox_nonneg := hqBox_nonneg) (h_gap := h_gap_half)
      (hδ'_le_quarter := hδ'_le_quarter)
      (hδ_small := h_extract_small)
  have h_exp_eq : δ ^ (-εnc / 2) = δ ^ (-(εnc / 2)) := by ring_nf
  have h_final : robust_projection_main.energyToLargeMassDeltaSetC (δ / L_norm) κ0
      ((3 : ℝ) ^ (2 * κ0) * (δ / L_norm) ^ (-q_norm_energy)) ≤ C_extract := by
    dsimp only [C_extract]; rw [h_exp_eq]; exact hC_extract_large_raw
  exact ⟨hC_energy_pos, hC_extract_pos, h_energy_absorb, h_final⟩


/-- Boundedness of the coordinate rectangle `[-R,R]^2` in Euclidean 2-space. -/
lemma bounded_coordinate_rectangle {R : ℝ} (hR : 0 ≤ R) :
    Bornology.IsBounded {p : EuclideanSpace ℝ (Fin 2) | ∀ i : Fin 2, p i ∈ Set.Icc (-R) R} := by
  let S : Set (EuclideanSpace ℝ (Fin 2)) := {p | ∀ i, p i ∈ Set.Icc (-R) R}
  have h_sub : S ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (2 * R) := by
    intro p hp
    have h01 : -R ≤ p 0 := (hp 0).1
    have h02 : p 0 ≤ R := (hp 0).2
    have h11 : -R ≤ p 1 := (hp 1).1
    have h12 : p 1 ≤ R := (hp 1).2
    have hsq0 : (p 0)^2 ≤ R^2 := by nlinarith
    have hsq1 : (p 1)^2 ≤ R^2 := by nlinarith
    have h2 : ‖p‖ ^ 2 = (p 0)^2 + (p 1)^2 := by
      rw [EuclideanSpace.real_norm_sq_eq p, Fin.sum_univ_two]
    have h3 : ‖p‖ ^ 2 ≤ (2 * R)^2 := by
      rw [h2]
      have h4 : R^2 + R^2 ≤ (2 * R)^2 := by nlinarith
      linarith
    have h5 : 0 ≤ ‖p‖ := by positivity
    have h6 : ‖p‖ ≤ 2 * R := by nlinarith
    simpa [Metric.mem_closedBall] using h6
  have h_bdd : Bornology.IsBounded (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (2 * R)) :=
    Metric.isBounded_closedBall
  exact h_bdd.subset h_sub


/-- V4 budget inequality: `qTotalV4 ≥ 32 * qKV4 + 2 * qAbsorb + qBox`.

Extracted from the inline `h_budget_ineq` proof to reduce elaborator memory.
Uses only the V4 budget function definitions and positivity. -/
lemma budget_ineq_v4
    (L_exp η_work ε κ0 p_projective τ rho_sel rho_sep : ℝ)
    (hL_exp_pos : 0 < L_exp) (hη_work_pos : 0 < η_work)
    (hε_pos : 0 < ε) (hκ0_pos : 0 < κ0)
    (hp_nonneg : 0 ≤ p_projective) (hτ_pos : 0 < τ)
    (hrho_sel_pos : 0 < rho_sel) (hrho_sep_pos : 0 < rho_sep) :
    qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≥
      32 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep +
      2 * qAbsorb η_work + qBox η_work τ := by
  have hqAbsorb_nonneg : 0 ≤ qAbsorb η_work := by
    have h : qAbsorb η_work = η_work / 100 := by rfl
    rw [h]; positivity
  have hqBox_nonneg : 0 ≤ qBox η_work τ := by
    have h : qBox η_work τ = 4 * η_work / τ + qAbsorb η_work := by rfl
    rw [h]; positivity
  have hqProjective_nonneg : 0 ≤ qProjective p_projective ε κ0 := by
    have h : qProjective p_projective ε κ0 = p_projective * ε / κ0 := by rfl
    rw [h]; positivity
  have hqK_nonneg : 0 ≤ qK L_exp η_work ε κ0 p_projective := by
    have h : qK L_exp η_work ε κ0 p_projective = (L_exp + 2) * η_work + qProjective p_projective ε κ0 := by rfl
    rw [h]; positivity
  have hqDensity_nonneg : 0 ≤ qDensityV4 η_work rho_sel rho_sep := by
    have h : qDensityV4 η_work rho_sel rho_sep = 3 * rho_sel + 2 * rho_sep + qAbsorb η_work := by rfl
    rw [h]; positivity
  have hqKV4_nonneg : 0 ≤ qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by
    have h : qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep =
        qK L_exp η_work ε κ0 p_projective + qDensityV4 η_work rho_sel rho_sep := by rfl
    rw [h]; positivity
  have hqGraphV4_nonneg : 0 ≤ qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by
    have h : qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep =
        22 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep + η_work / 2 + η_work / 20 := by rfl
    rw [h]; positivity
  have hqNormChunk_nonneg : 0 ≤ qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
    have h : qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep =
        qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep + qBox η_work τ + qAbsorb η_work := by rfl
    rw [h]; positivity
  have hqKAV4_nonneg : 0 ≤ qKAV4 L_exp η_work rho_sel rho_sep := by
    have h : qKAV4 L_exp η_work rho_sel rho_sep =
        2 * alphaProjectionV4 L_exp η_work + qMassV4 η_work rho_sep + 3 * rho_sel + 2 * qAbsorb η_work := by rfl
    rw [h]; have h2 : 0 ≤ alphaProjectionV4 L_exp η_work := by
      have h3 : alphaProjectionV4 L_exp η_work = (L_exp / 2) * η_work := by rfl
      rw [h3]; positivity
    have h4 : 0 ≤ qMassV4 η_work rho_sep := by
      have h5 : qMassV4 η_work rho_sep = 2 * rho_sep + qAbsorb η_work := by rfl
      rw [h5]; positivity
    positivity
  have hqDiffV4_nonneg : 0 ≤ qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
    have h : qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep =
        80 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep +
        2 * qKAV4 L_exp η_work rho_sel rho_sep + qAbsorb η_work +
        qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by rfl
    rw [h]; positivity
  have hqEffV4_nonneg : 0 ≤ qEffV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by
    have h : qEffV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep =
        10 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by rfl
    rw [h]; positivity
  have hqInputV4_nonneg : 0 ≤ qInputV4 L_exp η_work rho_sel rho_sep := by
    have h : qInputV4 L_exp η_work rho_sel rho_sep =
        (L_exp / 2 + 21 / 4) * η_work + 2 * rho_sep + qFixedCoordinate η_work + (3 * rho_sel) / 2 := by rfl
    rw [h]; have h2 : 0 ≤ qFixedCoordinate η_work := by
      have h3 : qFixedCoordinate η_work = 3 * qAbsorb η_work := by rfl
      rw [h3]; positivity
    positivity
  have hqSizeLossV4_nonneg : 0 ≤ qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
    have h : qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep =
        qEffV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep +
        qInputV4 L_exp η_work rho_sel rho_sep + qAbsorb η_work +
        qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by rfl
    rw [h]; positivity
  have hζDir_nonneg : 0 ≤ ζDir p_projective ε κ0 := by
    have h : ζDir p_projective ε κ0 = qProjective p_projective ε κ0 := by rfl
    rw [h]; exact hqProjective_nonneg
  have hηProj_nonneg : 0 ≤ ηProj L_exp η_work ε κ0 p_projective := by
    have h : ηProj L_exp η_work ε κ0 p_projective = L_exp * η_work + qProjective p_projective ε κ0 := by rfl
    rw [h]; positivity
  have hqNormEnergyV3_nonneg : 0 ≤ qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by
    have h1 : 0 ≤ qPlan η_work := by
      have h : qPlan η_work = 10 * η_work + qAbsorb η_work := by rfl
      rw [h]; positivity
    have h2 : 0 ≤ qKaufman η_work τ κ0 := by
      have h : qKaufman η_work τ κ0 = 2 * κ0 * qBox η_work τ := by rfl
      rw [h]; positivity
    have h3 : 0 ≤ qKaufBase η_work τ κ0 := by
      have h : qKaufBase η_work τ κ0 = qPlan η_work + η_work + qKaufman η_work τ κ0 + qAbsorb η_work := by rfl
      rw [h]; positivity
    have h4 : 0 ≤ rhoExc η_work ε τ κ0 rho_sel := by
      have h : rhoExc η_work ε τ κ0 rho_sel = qKaufBase η_work τ κ0 + rho_sel := by rfl
      rw [h]; positivity
    have h5 : 0 ≤ qCoordEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by
      have h : qCoordEnergyV3 η_work ε τ κ0 rho_sel rho_sep =
          rhoExc η_work ε τ κ0 rho_sel + 6 * rho_sel + 2 * κ0 * rho_sep := by rfl
      rw [h]; positivity
    have h6 : 0 ≤ qEnergy η_work τ κ0 := by
      have h : qEnergy η_work τ κ0 = 2 * κ0 * qBox η_work τ := by rfl
      rw [h]; positivity
    have h7 : qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep =
        qCoordEnergyV3 η_work ε τ κ0 rho_sel rho_sep + qEnergy η_work τ κ0 := by rfl
    rw [h7]; positivity
  have hqInitV3_nonneg : 0 ≤ qInitV3 η_work rho_sel := by
    have h : qInitV3 η_work rho_sel = 3 * rho_sel + 2 * η_work := by rfl
    rw [h]; positivity
  have h_diff_ge : qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≥
      80 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by
    have h4 : qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep =
        80 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep +
        2 * qKAV4 L_exp η_work rho_sel rho_sep + qAbsorb η_work +
        qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by rfl
    rw [h4]
    linarith only [hqKAV4_nonneg, hqAbsorb_nonneg, hqNormChunk_nonneg]
  have h_normchunk_ge : qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≥
      qBox η_work τ + qAbsorb η_work := by
    have h2 : qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep =
        qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep + qBox η_work τ + qAbsorb η_work := by rfl
    rw [h2]
    linarith only [hqGraphV4_nonneg]
  have h_sizeloss_ge : qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≥
      qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
    have h4 : qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep =
        qEffV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep +
        qInputV4 L_exp η_work rho_sel rho_sep + qAbsorb η_work +
        qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by rfl
    rw [h4]
    linarith only [hqEffV4_nonneg, hqInputV4_nonneg, hqAbsorb_nonneg]
  have h_total_ge : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≥
      2 * qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep +
      qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep +
      qAbsorb η_work := by
    have h8 : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep =
        qInitV3 η_work rho_sel + 2 * rho_sep +
        qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep + qAbsorb η_work +
        2 * qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep +
        qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep +
        η_work + ζDir p_projective ε κ0 +
        ηProj L_exp η_work ε κ0 p_projective +
        qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by rfl
    rw [h8]
    have hη_work_nonneg : 0 ≤ η_work := by linarith [hη_work_pos]
    have h2rho_sep : 0 ≤ 2 * rho_sep := by linarith [hrho_sep_pos]
    linarith only [hqInitV3_nonneg, h2rho_sep, hqGraphV4_nonneg, hqAbsorb_nonneg,
      hη_work_nonneg, hζDir_nonneg, hηProj_nonneg, hqNormEnergyV3_nonneg]
  have h_main : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≥
      160 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep +
      qBox η_work τ + 2 * qAbsorb η_work := by
    calc qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
      ≥ 2 * qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep +
          qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep + qAbsorb η_work := h_total_ge
    _ ≥ 2 * (80 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep) +
          (qBox η_work τ + qAbsorb η_work) + qAbsorb η_work := by
      have h1 : 2 * qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≥
          2 * (80 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep) := by gcongr
      have h2 : qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≥
          qBox η_work τ + qAbsorb η_work := by
        calc qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
          ≥ qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := h_sizeloss_ge
        _ ≥ qBox η_work τ + qAbsorb η_work := h_normchunk_ge
      linarith
    _ = 160 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep +
        qBox η_work τ + 2 * qAbsorb η_work := by ring
  linarith [h_main, hqKV4_nonneg]


/-- Pbar lower bound bridge: from `hPbar_lower_strong` and `C_work ≤ δ^{-η_work}`,
derive both the granite lower bound and `δ^{-2κ0} ≤ Nplane(Pbar_param)`.

Extracted from inline proofs to reduce elaborator memory. -/
lemma pbar_lower_granite_bridge
    {δ s κ0 η_work C_work : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hη_work_pos : 0 < η_work)
    (h5η_work_lt : 5 * η_work < 2 * (s - κ0))
    (h_box_bound : (2 ^ 20 : ℝ) ≤ δ ^ (-(η_work / 100)))
    (hC_work_pos : 0 < C_work) (hC_work_le : C_work ≤ δ ^ (-η_work))
    {Pbar_param : Set (EuclideanSpace ℝ (Fin 2))}
    (hPbar_lower_strong : ENNReal.ofReal (δ ^ (-2 * s + η_work / 2) / (98 * C_work ^ 4)) ≤ Nplane δ Pbar_param) :
    (Nplane δ Pbar_param ≥ (1 / 98 : ENNReal) * ENNReal.ofReal (δ ^ (-2 * s + 9 * η_work / 2))) ∧
    (ENNReal.ofReal (δ ^ (-2 * κ0)) ≤ Nplane δ Pbar_param) := by
  let A := δ ^ (-2 * s + η_work / 2)
  let B := δ ^ (4 * η_work)
  let D := C_work ^ 4
  have hA_pos : 0 < A := by positivity
  have hB_pos : 0 < B := by positivity
  have hD_pos : 0 < D := by positivity
  have hC_nonneg : 0 ≤ C_work := by linarith
  have h1 : D ≤ 1 / B := by
    have h1a : C_work ^ 4 ≤ (δ ^ (-η_work)) ^ 4 := by
      have h : C_work ≤ δ ^ (-η_work) := hC_work_le
      gcongr
    have h1b : (δ ^ (-η_work)) ^ 4 = 1 / B := by
      dsimp only [B]
      have h_pow : (δ ^ (-η_work)) ^ 4 = δ ^ (-4 * η_work) := by
        have h_nat : (δ ^ (-η_work)) ^ 4 = (δ ^ (-η_work)) ^ (4 : ℝ) := by
          simp [Real.rpow_natCast]
        rw [h_nat]
        have h_real : (δ ^ (-η_work)) ^ (4 : ℝ) = δ ^ ((-η_work) * (4 : ℝ)) := by
          rw [← Real.rpow_mul (by linarith)] <;> ring
        rw [h_real] <;> ring_nf
      rw [h_pow]
      have h_inv : δ ^ (-4 * η_work) = 1 / δ ^ (4 * η_work) := by
        have h_neg : δ ^ (-4 * η_work) = (δ ^ (4 * η_work))⁻¹ := by
          rw [show -4 * η_work = -(4 * η_work) by ring]
          rw [Real.rpow_neg (by linarith)] <;> ring
        rw [h_neg] <;> field_simp
      exact h_inv
    rw [h1b] at h1a
    exact h1a
  have h2 : B ≤ 1 / D := by
    have h21 : D * B ≤ 1 := by
      calc D * B ≤ (1 / B) * B := by gcongr
        _ = 1 := by field_simp [hB_pos.ne'] <;> ring
    calc B
      = (1 / D) * (D * B) := by field_simp [hD_pos.ne'] <;> ring
    _ ≤ (1 / D) * 1 := by gcongr
    _ = 1 / D := by ring
  have h3 : (1 / 98 : ℝ) * δ ^ (-2 * s + 9 * η_work / 2) ≤ A / (98 * D) := by
    have h3a : δ ^ (-2 * s + 9 * η_work / 2) = A * B := by
      dsimp only [A, B]
      rw [← Real.rpow_add hδ_pos] <;> ring_nf
    have h3b : 0 ≤ (1 / 98 : ℝ) * A := by positivity
    have h3c : (1 / 98 : ℝ) * A * B ≤ (1 / 98 : ℝ) * A * (1 / D) := by
      exact mul_le_mul_of_nonneg_left h2 h3b
    have h3d : (1 / 98 : ℝ) * A * (1 / D) = A / (98 * D) := by
      field_simp [hD_pos.ne'] <;> ring
    have h_eq : (1 / 98 : ℝ) * δ ^ (-2 * s + 9 * η_work / 2) = (1 / 98 : ℝ) * A * B := by
      rw [h3a] <;> ring
    rw [h_eq]
    calc (1 / 98 : ℝ) * A * B
      ≤ (1 / 98 : ℝ) * A * (1 / D) := h3c
    _ = A / (98 * D) := h3d
  have h4 : ENNReal.ofReal ((1 / 98 : ℝ) * δ ^ (-2 * s + 9 * η_work / 2)) ≤
      ENNReal.ofReal (A / (98 * D)) := by gcongr
  have h_pos2 : 0 ≤ δ ^ (-2 * s + 9 * η_work / 2) := by positivity
  have h_main : ENNReal.ofReal ((1 / 98 : ℝ) * δ ^ (-2 * s + 9 * η_work / 2)) ≤ Nplane δ Pbar_param :=
    le_trans h4 hPbar_lower_strong
  have h_eq : (1 / 98 : ENNReal) * ENNReal.ofReal (δ ^ (-2 * s + 9 * η_work / 2)) =
      ENNReal.ofReal ((1 / 98 : ℝ) * δ ^ (-2 * s + 9 * η_work / 2)) := by
    simp [ENNReal.ofReal_mul]
  have hPbar_lower_granite : Nplane δ Pbar_param ≥
      (1 / 98 : ENNReal) * ENNReal.ofReal (δ ^ (-2 * s + 9 * η_work / 2)) := by
    rw [h_eq]
    exact h_main
  let d : ℝ := 2 * (s - κ0) - 9 * η_work / 2
  have hd_gt : d > η_work / 100 := by
    dsimp only [d]
    have h1 : 5 * η_work < 2 * (s - κ0) := h5η_work_lt
    linarith only [h1, hη_work_pos]
  have hd_ge : d ≥ η_work / 100 := by linarith only [hd_gt]
  have h1' : δ ^ (-d) ≥ δ ^ (-(η_work / 100)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le (by linarith)
  have h2' : δ ^ (-d) ≥ (2 ^ 20 : ℝ) := by
    calc δ ^ (-d) ≥ δ ^ (-(η_work / 100)) := h1'
         _ ≥ (2 ^ 20 : ℝ) := h_box_bound
  have h3' : δ ^ (-d) ≥ 98 := by linarith
  have h4' : δ ^ (-2 * s + 9 * η_work / 2) = δ ^ (-d) * δ ^ (-2 * κ0) := by
    have h5 : -d + (-2 * κ0) = -2 * s + 9 * η_work / 2 := by
      dsimp only [d] <;> ring
    rw [← Real.rpow_add hδ_pos, h5]
  have h5' : (1 / 98 : ℝ) * δ ^ (-2 * s + 9 * η_work / 2) ≥ δ ^ (-2 * κ0) := by
    rw [h4']
    have h6 : (1 / 98 : ℝ) * δ ^ (-d) ≥ 1 := by
      have h7 : δ ^ (-d) ≥ 98 := h3'
      linarith only [h7]
    have h8 : 0 ≤ δ ^ (-2 * κ0) := by positivity
    have h9 : (1 / 98 : ℝ) * (δ ^ (-d) * δ ^ (-2 * κ0)) ≥ δ ^ (-2 * κ0) := by
      calc (1 / 98 : ℝ) * (δ ^ (-d) * δ ^ (-2 * κ0))
        = ((1 / 98 : ℝ) * δ ^ (-d)) * δ ^ (-2 * κ0) := by ring
      _ ≥ 1 * δ ^ (-2 * κ0) := by gcongr
      _ = δ ^ (-2 * κ0) := by ring
    exact h9
  have h10 : ENNReal.ofReal (δ ^ (-2 * κ0)) ≤
      ENNReal.ofReal ((1 / 98 : ℝ) * δ ^ (-2 * s + 9 * η_work / 2)) := by
    gcongr
  have h11 : ENNReal.ofReal ((1 / 98 : ℝ) * δ ^ (-2 * s + 9 * η_work / 2)) =
      (1 / 98 : ENNReal) * ENNReal.ofReal (δ ^ (-2 * s + 9 * η_work / 2)) := by
    simp [ENNReal.ofReal_mul]
  rw [h11] at h10
  exact ⟨hPbar_lower_granite, le_trans h10 hPbar_lower_granite⟩


/-- Boundedness of a rounded projected coordinate: `|round_fun ((F q) i)| ≤ R_norm + 1`.

Extracted from the repetitive `hS1_bdd`/`hS2_bdd` proofs. -/
lemma round_coordinate_bound
    {δ R R_norm : ℝ} {θ1 θ2 θ3 : ℝ}
    {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {q : EuclideanSpace ℝ (Fin 2)} {round_fun : ℝ → ℝ}
    (hδ_lt_one : δ < 1) (hδ_pos : 0 < δ)
    (hθ1_in_Icc : θ1 ∈ Set.Icc 0 1) (hθ2_in_Icc : θ2 ∈ Set.Icc 0 1)
    (hθ1_lt_θ3 : θ1 < θ3) (hθ3_lt_θ2 : θ3 < θ2)
    (hq_bdd : |q 0| ≤ R ∧ |q 1| ≤ R)
    (hF_formula : ∀ p, (F p) 0 = ((θ3 - θ1) / (θ2 - θ1)) * (p 0 * θ2 + p 1) ∧
                        (F p) 1 = ((θ2 - θ3) / (θ2 - θ1)) * (p 0 * θ1 + p 1))
    (h_round_near : ∀ t : ℝ, |t - round_fun t| ≤ δ / 2)
    (hR_norm_eq : R_norm = 2 * R) (i : Fin 2) :
    |round_fun ((F q) i)| ≤ R_norm + 1 := by
  have hθ1_abs : |θ1| ≤ 1 := by
    have h1 : 0 ≤ θ1 := hθ1_in_Icc.1
    have h2 : θ1 ≤ 1 := hθ1_in_Icc.2
    rw [abs_of_nonneg h1]; exact h2
  have hθ2_abs : |θ2| ≤ 1 := by
    have h1 : 0 ≤ θ2 := hθ2_in_Icc.1
    have h2 : θ2 ≤ 1 := hθ2_in_Icc.2
    rw [abs_of_nonneg h1]; exact h2
  have hF_bdd := projective_F_bound F q θ1 θ2 θ3 R
    hθ1_lt_θ3 hθ3_lt_θ2 hθ1_abs hθ2_abs
    hq_bdd.1 hq_bdd.2 (hF_formula q).1 (hF_formula q).2
  have h3 : |(F q) i| ≤ 2 * R := by
    fin_cases i <;> tauto
  have h4 : |round_fun ((F q) i)| ≤ |(F q) i| + |round_fun ((F q) i) - (F q) i| := by
    have h_abs : |(F q) i + (round_fun ((F q) i) - (F q) i)| ≤ |(F q) i| + |round_fun ((F q) i) - (F q) i| :=
      abs_add_le _ _
    have h_eq : (F q) i + (round_fun ((F q) i) - (F q) i) = round_fun ((F q) i) := by
      exact add_sub_cancel ((F q) i) (round_fun ((F q) i))
    rw [h_eq] at h_abs
    exact h_abs
  have h5 : |round_fun ((F q) i) - (F q) i| ≤ δ / 2 := by
    have h51 : |(F q) i - round_fun ((F q) i)| ≤ δ / 2 := h_round_near ((F q) i)
    have h52 : |round_fun ((F q) i) - (F q) i| = |(F q) i - round_fun ((F q) i)| := by
      rw [show round_fun ((F q) i) - (F q) i = -((F q) i - round_fun ((F q) i)) by ring, abs_neg]
    rw [h52]; exact h51
  have h6 : δ / 2 ≤ 1 := by
    have h9 : δ < 1 := hδ_lt_one
    have h10 : (0 : ℝ) < 2 := by norm_num
    have h11 : δ / 2 < 1 / 2 := div_lt_div_of_pos_right h9 h10
    have h12 : (1 / 2 : ℝ) ≤ 1 := by norm_num
    exact h11.le.trans h12
  have h7 : |round_fun ((F q) i)| ≤ 2 * R + 1 := by
    have h9 : |(F q) i| ≤ 2 * R := h3
    have h10 : |round_fun ((F q) i) - (F q) i| ≤ δ / 2 := h5
    have h11 : |round_fun ((F q) i)| ≤ |(F q) i| + |round_fun ((F q) i) - (F q) i| := h4
    have h12 : |(F q) i| + |round_fun ((F q) i) - (F q) i| ≤ 2 * R + δ / 2 := by
      exact add_le_add h9 h10
    have h13 : 2 * R + δ / 2 ≤ 2 * R + 1 := by
      exact add_le_add_right h6 (2 * R)
    exact h11.trans (h12.trans h13)
  rw [hR_norm_eq]
  exact h7

/-- Shared upper bound for `hS1_upper_B`/`hS2_upper_B`: given a pre-bound on `S`
in terms of `Nplane δ Pbar_param`, and the smallness of `Pbar_param`, derives
`Nreal δ S ≤ 12 · δ^{-(s + (L_exp+1/2)·η)}`. -/
lemma s_upper_bound_lemma
    {δ s L_exp η : ℝ}
    {S : Set ℝ}
    {Pbar_param : Set (EuclideanSpace ℝ (Fin 2))}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hS_bound : Nreal δ S ≤ (6 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)))
    (hPbar_small : Nplane δ Pbar_param < ENNReal.ofReal ((4 : ℝ) * δ ^ (-(2 * s + η)))) :
    Nreal δ S ≤ ENNReal.ofReal ((12 : ℝ) * δ ^ (-(s + (L_exp + 1 / 2 : ℝ) * η))) := by
  have h_lt_top : Nplane δ Pbar_param < ⊤ := by
    apply lt_trans hPbar_small
    exact ENNReal.ofReal_lt_top
  have h_ne_top : Nplane δ Pbar_param ≠ ⊤ := ne_of_lt h_lt_top
  have h2 : (Nplane δ Pbar_param).toReal ≤ (4 : ℝ) * δ ^ (-(2 * s + η)) := by
    have h3 : (Nplane δ Pbar_param).toReal ≤ (ENNReal.ofReal ((4 : ℝ) * δ ^ (-(2 * s + η)))).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hPbar_small.le
    have h4 : (ENNReal.ofReal ((4 : ℝ) * δ ^ (-(2 * s + η)))).toReal = (4 : ℝ) * δ ^ (-(2 * s + η)) := by
      rw [ENNReal.toReal_ofReal] <;> positivity
    rw [h4] at h3; exact h3
  have h5 : Real.sqrt ((Nplane δ Pbar_param).toReal) ≤ (2 : ℝ) * δ ^ (-(s + η / 2)) := by
    calc Real.sqrt ((Nplane δ Pbar_param).toReal)
      ≤ Real.sqrt ((4 : ℝ) * δ ^ (-(2 * s + η))) := Real.sqrt_le_sqrt h2
    _ = (2 : ℝ) * δ ^ (-(s + η / 2)) := by
      have h6 : Real.sqrt ((4 : ℝ) * δ ^ (-(2 * s + η))) = (2 : ℝ) * δ ^ (-(s + η / 2)) := by
        have h7 : 0 ≤ (4 : ℝ) := by norm_num
        have h8 : 0 ≤ δ ^ (-(2 * s + η)) := by positivity
        rw [Real.sqrt_mul h7]
        have h9 : Real.sqrt (4 : ℝ) = 2 := by norm_num
        have h10 : Real.sqrt (δ ^ (-(2 * s + η))) = δ ^ (-(s + η / 2)) := by
          rw [Real.sqrt_eq_rpow] <;> rw [← Real.rpow_mul hδ_pos.le] <;> ring_nf <;> norm_num
        rw [h9, h10] <;> ring
      exact h6
  have h_rpow : δ ^ (-(L_exp * η)) * ((2 : ℝ) * δ ^ (-(s + η / 2))) =
      (2 : ℝ) * δ ^ (-(s + (L_exp + 1 / 2 : ℝ) * η)) := by
    have h1 : δ ^ (-(L_exp * η)) * ((2 : ℝ) * δ ^ (-(s + η / 2))) =
        (2 : ℝ) * (δ ^ (-(L_exp * η)) * δ ^ (-(s + η / 2))) := by ring
    rw [h1]
    have h2 : δ ^ (-(L_exp * η)) * δ ^ (-(s + η / 2)) = δ ^ (-(L_exp * η) + (-(s + η / 2))) := by
      rw [← Real.rpow_add hδ_pos]
    rw [h2] <;> ring_nf
  calc Nreal δ S
    ≤ (6 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar_param).toReal)) := hS_bound
  _ ≤ (6 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal ((2 : ℝ) * δ ^ (-(s + η / 2))) := by gcongr
  _ = ENNReal.ofReal ((12 : ℝ) * δ ^ (-(s + (L_exp + 1 / 2 : ℝ) * η))) := by
    have h_pos3 : (0 : ℝ) ≤ 6 := by norm_num
    have h6 : (6 : ENNReal) = ENNReal.ofReal (6 : ℝ) := by simp
    rw [h6]
    have h_step1 : ENNReal.ofReal (6 : ℝ) * ENNReal.ofReal (δ ^ (-(L_exp * η))) =
        ENNReal.ofReal ((6 : ℝ) * δ ^ (-(L_exp * η))) := by
      rw [← ENNReal.ofReal_mul h_pos3]
    rw [h_step1]
    have h_pos4 : 0 ≤ (6 : ℝ) * δ ^ (-(L_exp * η)) := by positivity
    have h_step2 : ENNReal.ofReal ((6 : ℝ) * δ ^ (-(L_exp * η))) * ENNReal.ofReal ((2 : ℝ) * δ ^ (-(s + η / 2))) =
        ENNReal.ofReal (((6 : ℝ) * δ ^ (-(L_exp * η))) * ((2 : ℝ) * δ ^ (-(s + η / 2)))) := by
      rw [← ENNReal.ofReal_mul h_pos4]
    have h_all : ((6 : ℝ) * δ ^ (-(L_exp * η))) * ((2 : ℝ) * δ ^ (-(s + η / 2))) =
        (12 : ℝ) * δ ^ (-(s + (L_exp + 1 / 2 : ℝ) * η)) := by
      have h1 : ((6 : ℝ) * δ ^ (-(L_exp * η))) * ((2 : ℝ) * δ ^ (-(s + η / 2))) =
          (6 : ℝ) * (δ ^ (-(L_exp * η)) * ((2 : ℝ) * δ ^ (-(s + η / 2)))) := by ring
      rw [h1, h_rpow] <;> ring
    rw [h_step2, h_all]

/-- Energy lower bound for the B-series upper bounds: `εnc ≥ (L_exp + 1/2) · η + η_work/100`. -/
lemma enc_ge_B_lemma
    {L_exp η_work ε κ0 p_projective τ rho_sel rho_sep εnc η : ℝ}
    (hL_exp_eq_seven : L_exp = 7)
    (hη_work_pos : 0 < η_work)
    (hη_pos : 0 < η)
    (hη_work_eq_two : η_work = 2 * η)
    (h_qTotalV4_le_enc4 : εnc ≥ 4 * qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep)
    (hε_pos : 0 < ε) (hκ0_pos : 0 < κ0)
    (hp_nonneg : 0 ≤ p_projective)
    (hτ_pos : 0 < τ)
    (hrho_sel_nonneg : 0 ≤ rho_sel)
    (hrho_sep_nonneg : 0 ≤ rho_sep) :
    εnc ≥ (L_exp + 1 / 2 : ℝ) * η + η_work / 100 := by
  have h1 : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≥ η_work := by
    rw [qTotalV4_expansion L_exp η_work ε κ0 p_projective τ rho_sel rho_sep]
    have h_coeff : (527 / 2 : ℝ) * L_exp + 26873 / 50 ≥ 1 := by
      rw [hL_exp_eq_seven] <;> norm_num
    have h_first : ((527 / 2 : ℝ) * L_exp + 26873 / 50) * η_work ≥ η_work := by
      have h_pos : 0 < η_work := hη_work_pos
      have h9 : ((527 / 2 : ℝ) * L_exp + 26873 / 50) ≥ 1 := h_coeff
      calc
        ((527 / 2 : ℝ) * L_exp + 26873 / 50) * η_work ≥ 1 * η_work := by gcongr
        _ = η_work := by ring
    have h2 : 0 ≤ 260 * qProjective p_projective ε κ0 := by
      dsimp only [qProjective]; positivity
    have h3 : 0 ≤ (1595 / 2 : ℝ) * rho_sel := by positivity
    have h4 : 0 ≤ (528 + 2 * κ0) * rho_sep := by positivity
    have h5 : 0 ≤ (284 + 4 * κ0) * qAbsorb η_work := by
      dsimp only [qAbsorb]; positivity
    have h6 : 0 ≤ ((16 * κ0 + 12) / τ) * η_work := by positivity
    have h_sum : ((527 / 2 : ℝ) * L_exp + 26873 / 50) * η_work +
        260 * qProjective p_projective ε κ0 +
        (1595 / 2 : ℝ) * rho_sel +
        (528 + 2 * κ0) * rho_sep +
        (284 + 4 * κ0) * qAbsorb η_work +
        ((16 * κ0 + 12) / τ) * η_work ≥ η_work := by
      have h7 : 0 ≤ 260 * qProjective p_projective ε κ0 := h2
      have h8 : 0 ≤ (1595 / 2 : ℝ) * rho_sel := h3
      have h9 : 0 ≤ (528 + 2 * κ0) * rho_sep := h4
      have h10 : 0 ≤ (284 + 4 * κ0) * qAbsorb η_work := h5
      have h11 : 0 ≤ ((16 * κ0 + 12) / τ) * η_work := h6
      have h_nonneg : 0 ≤ 260 * qProjective p_projective ε κ0 + (1595 / 2 : ℝ) * rho_sel + (528 + 2 * κ0) * rho_sep + (284 + 4 * κ0) * qAbsorb η_work + ((16 * κ0 + 12) / τ) * η_work := by linarith
      linarith [h_first, h_nonneg]
    exact h_sum
  have h2 : εnc ≥ 4 * qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
    linarith [h_qTotalV4_le_enc4]
  have h3 : (L_exp + 1 / 2 : ℝ) * η + η_work / 100 ≤ 4 * η_work := by
    rw [hη_work_eq_two, hL_exp_eq_seven]
    have hη_nonneg : 0 ≤ η := by linarith [hη_pos]
    linarith only [hη_nonneg, hη_work_eq_two, hL_exp_eq_seven]
  linarith only [h1, h2, h3]

/-- Budget inequality: from `εgain > qTotalV4(η_work)` derive `εgain > q_graph_total + 2·q_diff + q_size + η + ζ_dir + η_proj`. -/
lemma budget_total_lemma
    {L_exp η_work ε κ0 p_projective τ rho_sel rho_sep η εgain : ℝ}
    {q_graph_total q_diff q_size ζ_dir η_proj : ℝ}
    (hL_exp_pos : 0 < L_exp)
    (hη_work_pos : 0 < η_work)
    (hη_pos : 0 < η)
    (hη_work_eq_two : η_work = 2 * η)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_ge_10 : 10 ≤ p_projective)
    (hτ_pos : 0 < τ)
    (hrho_sel_pos : 0 < rho_sel)
    (hrho_sep_pos : 0 < rho_sep)
    (hq_graph_total_eq : q_graph_total = qInitV3 η_work rho_sel + 2 * rho_sep +
        qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep + qAbsorb η_work +
        qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep)
    (hq_diff_eq : q_diff = qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep)
    (hq_size_eq : q_size = qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep)
    (hζ_dir_eq : ζ_dir = ζDir p_projective ε κ0)
    (hη_proj_eq : η_proj = ηProj L_exp η ε κ0 p_projective)
    (h_outer : εgain > qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep) :
    εgain > q_graph_total + 2 * q_diff + q_size + η + ζ_dir + η_proj := by
  have h_def : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep =
      qInitV3 η_work rho_sel + 2 * rho_sep +
      qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep +
      qAbsorb η_work + 2 * qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep +
      qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep +
      η_work + ζDir p_projective ε κ0 +
      ηProj L_exp η_work ε κ0 p_projective +
      qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by rfl
  have h1 : q_graph_total + 2 * q_diff + q_size + η + ζ_dir + η_proj ≤
      qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
    rw [hq_graph_total_eq, hq_diff_eq, hq_size_eq, hζ_dir_eq, hη_proj_eq, h_def]
    have h2 : η ≤ η_work := by linarith [hη_work_eq_two]
    have h3 : ηProj L_exp η ε κ0 p_projective ≤ ηProj L_exp η_work ε κ0 p_projective := by
      dsimp only [ηProj, qProjective]
      have h4 : 0 ≤ L_exp * (η_work - η) := by positivity
      linarith only [h4]
    have h5 : 0 ≤ qInitV3 η_work rho_sel := by dsimp only [qInitV3]; positivity
    have h6 : 0 ≤ 2 * rho_sep := by linarith [hrho_sep_pos]
    have hqAbsorb_nonneg : 0 ≤ qAbsorb η_work := by
      have h : qAbsorb η_work = η_work / 100 := by rfl
      rw [h]; positivity
    have h8 : 0 ≤ qAbsorb η_work := hqAbsorb_nonneg
    have hqProjective_nonneg : 0 ≤ qProjective p_projective ε κ0 := by
      have hp_pos : 0 < p_projective := by linarith [hp_ge_10]
      have h : qProjective p_projective ε κ0 = p_projective * ε / κ0 := by rfl
      rw [h]
      exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have hqK_nonneg : 0 ≤ qK L_exp η_work ε κ0 p_projective := by
      have h : qK L_exp η_work ε κ0 p_projective = (L_exp + 2) * η_work + qProjective p_projective ε κ0 := by rfl
      rw [h]; positivity
    have hqDensity_nonneg : 0 ≤ qDensityV4 η_work rho_sel rho_sep := by
      have h : qDensityV4 η_work rho_sel rho_sep = 3 * rho_sel + 2 * rho_sep + qAbsorb η_work := by rfl
      rw [h]; positivity
    have hqKV4_nonneg : 0 ≤ qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by
      have h : qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep =
          qK L_exp η_work ε κ0 p_projective + qDensityV4 η_work rho_sel rho_sep := by rfl
      rw [h]; positivity
    have h7 : 0 ≤ qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by
      have h : qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep =
          22 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep + η_work / 2 + η_work / 20 := by rfl
      rw [h]; positivity
    have hqBox_nonneg : 0 ≤ qBox η_work τ := by
      have h : qBox η_work τ = 4 * η_work / τ + qAbsorb η_work := by rfl
      rw [h]; positivity
    have hqNormChunkV4_nonneg : 0 ≤ qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
      have h : qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep =
          qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep + qBox η_work τ + qAbsorb η_work := by rfl
      rw [h]; positivity
    have hqAlpha_nonneg : 0 ≤ alphaProjectionV4 L_exp η_work := by
      have h : alphaProjectionV4 L_exp η_work = (L_exp / 2) * η_work := by rfl
      rw [h]; positivity
    have hqMass_nonneg : 0 ≤ qMassV4 η_work rho_sep := by
      have h : qMassV4 η_work rho_sep = 2 * rho_sep + qAbsorb η_work := by rfl
      rw [h]; positivity
    have hqKAV4_nonneg : 0 ≤ qKAV4 L_exp η_work rho_sel rho_sep := by
      have h : qKAV4 L_exp η_work rho_sel rho_sep =
          2 * alphaProjectionV4 L_exp η_work + qMassV4 η_work rho_sep + 3 * rho_sel + 2 * qAbsorb η_work := by rfl
      rw [h]; positivity
    have h9 : 0 ≤ 2 * qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
      have h : qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep =
          80 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep +
          2 * qKAV4 L_exp η_work rho_sel rho_sep + qAbsorb η_work +
          qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by rfl
      rw [h]; positivity
    have hqEffV4_nonneg : 0 ≤ qEffV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by
      have h : qEffV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep =
          10 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by rfl
      rw [h]; positivity
    have hqFixedCoord_nonneg : 0 ≤ qFixedCoordinate η_work := by
      have h : qFixedCoordinate η_work = 3 * qAbsorb η_work := by rfl
      rw [h]; positivity
    have hqInputV4_nonneg : 0 ≤ qInputV4 L_exp η_work rho_sel rho_sep := by
      have h : qInputV4 L_exp η_work rho_sel rho_sep =
          (L_exp / 2 + 21 / 4) * η_work + 2 * rho_sep + qFixedCoordinate η_work + (3 * rho_sel) / 2 := by rfl
      rw [h]; positivity
    have h10 : 0 ≤ qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
      have h : qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep =
          qEffV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep +
          qInputV4 L_exp η_work rho_sel rho_sep + qAbsorb η_work +
          qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by rfl
      rw [h]; positivity
    have h11 : 0 ≤ ζDir p_projective ε κ0 := by
      have h : ζDir p_projective ε κ0 = qProjective p_projective ε κ0 := by rfl
      rw [h]; exact hqProjective_nonneg
    have h12 : 0 ≤ qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by
      have h12a : 0 ≤ qPlan η_work := by
        have h : qPlan η_work = 10 * η_work + qAbsorb η_work := by rfl
        rw [h]; positivity
      have h12b : 0 ≤ qKaufman η_work τ κ0 := by
        have h : qKaufman η_work τ κ0 = 2 * κ0 * qBox η_work τ := by rfl
        have hqBox : 0 < qBox η_work τ := by
          dsimp only [qBox, qAbsorb]
          have hdiv : 0 < 4 * η_work / τ := by positivity
          have hqa : 0 < qAbsorb η_work := by dsimp only [qAbsorb]; positivity
          linarith
        rw [h]
        have hκ : 0 ≤ κ0 := by linarith [hκ0_pos]
        exact mul_nonneg (mul_nonneg (by norm_num) hκ) (by linarith)
      have h12c : 0 ≤ qKaufBase η_work τ κ0 := by
        have h : qKaufBase η_work τ κ0 = qPlan η_work + η_work + qKaufman η_work τ κ0 + qAbsorb η_work := by rfl
        rw [h]; positivity
      have h12d : 0 ≤ rhoExc η_work ε τ κ0 rho_sel := by
        have h : rhoExc η_work ε τ κ0 rho_sel = qKaufBase η_work τ κ0 + rho_sel := by rfl
        rw [h]; positivity
      have h12e : 0 ≤ qCoordEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by
        have h : qCoordEnergyV3 η_work ε τ κ0 rho_sel rho_sep =
            rhoExc η_work ε τ κ0 rho_sel + 6 * rho_sel + 2 * κ0 * rho_sep := by rfl
        rw [h]; positivity
      have h12f : 0 ≤ qEnergy η_work τ κ0 := by
        have h : qEnergy η_work τ κ0 = 2 * κ0 * qBox η_work τ := by rfl
        rw [h]; positivity
      have h12g : qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep =
          qCoordEnergyV3 η_work ε τ κ0 rho_sel rho_sep + qEnergy η_work τ κ0 := by rfl
      rw [h12g]; positivity
    linarith only [h2, h3, h5, h6, h7, h8, h9, h10, h11, h12]
  exact lt_of_le_of_lt h1 h_outer

/-- **Symmetry bridge**: B2-B1 difference bound from B1-B2 bound.

Given a bound on `Nreal δ (B1 - B2)`, derive the same bound on
`Nreal δ (B2 - B1)` using negation invariance of `Nreal` on finite
grid-separated sets. -/
lemma symmetry_bridge_lemma
    {δ : ℝ} {B1_norm B2_norm : Set ℝ}
    (hδ_pos : 0 < δ)
    (hB1_norm_fin : B1_norm.Finite)
    (hB2_norm_fin : B2_norm.Finite)
    (hB1_norm_unit : B1_norm ⊆ productLikeUnitGrid δ)
    (hB2_norm_unit : B2_norm ⊆ productLikeUnitGrid δ)
    (K_BSG_B2 R_ret : ℝ)
    (h_norm5 : Nreal δ (Set.image2 (· - ·) B1_norm B2_norm) ≤
        (2 : ENNReal) * ENNReal.ofReal (K_BSG_B2 * R_ret) * Nreal δ B2_norm) :
    Nreal δ (Set.image2 (· - ·) B2_norm B1_norm) ≤
      (2 : ENNReal) * ENNReal.ofReal (K_BSG_B2 * R_ret) * Nreal δ B2_norm := by
  let D12 := Set.image2 (· - ·) B1_norm B2_norm
  let D21 := Set.image2 (· - ·) B2_norm B1_norm
  have hB1_norm_grid : ∀ x ∈ B1_norm, x ∈ productLikeIntegerGrid δ :=
    fun x hx => (hB1_norm_unit hx).1
  have hB2_norm_grid : ∀ x ∈ B2_norm, x ∈ productLikeIntegerGrid δ :=
    fun x hx => (hB2_norm_unit hx).1
  have hD12_finite : D12.Finite := Set.Finite.image2 (· - ·) hB1_norm_fin hB2_norm_fin
  have hD12_grid : ∀ z ∈ D12, z ∈ productLikeIntegerGrid δ :=
    diff_set_grid hB1_norm_grid hB2_norm_grid
  have hD12_sep : ∀ z ∈ D12, ∀ w ∈ D12, z ≠ w → |z - w| ≥ δ :=
    diff_set_separated hδ_pos hB1_norm_grid hB2_norm_grid
  have h_eq : D21 = Set.image (fun x : ℝ => -x) D12 := by
    ext z
    simp only [Set.mem_image, Set.mem_image2]
    constructor
    · rintro ⟨b2, hb2, b1, hb1, rfl⟩
      refine ⟨b1 - b2, ⟨b1, hb1, b2, hb2, rfl⟩, by ring⟩
    · rintro ⟨w, ⟨b1, hb1, b2, hb2, rfl⟩, rfl⟩
      exact ⟨b2, hb2, b1, hb1, by ring⟩
  have hNreal_eq : Nreal δ D21 = Nreal δ D12 := by
    rw [h_eq]
    exact nreal_neg_invariant hδ_pos hD12_finite hD12_grid hD12_sep
  rw [hNreal_eq]
  exact h_norm5

/-- ## Budget computation lemma

Extracts the budget parameter computation and associated non-negativity
proofs from the main proof to reduce elaboration memory pressure.

Given the raw V4 parameters, computes `q_graph_total`, `q_diff`, `q_size`,
`ζ_dir`, `η_proj`, and returns their definitions, non-negativity proofs,
the delta-small bound, projection budget, and factor absorption result. -/
lemma budget_computation_lemma
    {δ L_exp η_work η ε κ0 p_projective τ rho_sel rho_sep εgain : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hL_exp_pos : 0 < L_exp)
    (hη_pos : 0 < η)
    (hη_work_pos : 0 < η_work)
    (hη_work_eq_two : η_work = 2 * η)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_ge_10 : 10 ≤ p_projective)
    (hτ_pos : 0 < τ)
    (hrho_sel_pos : 0 < rho_sel)
    (hrho_sep_pos : 0 < rho_sep)
    (h_budget : εgain > qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep)
    (h_dir_64 : δ ^ (εgain - qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep) ≤ 1 / 64)
    (h_box_bound : (2 : ℝ) ^ 20 ≤ δ ^ (-(η_work / 100))) :
    let q_graph_total : ℝ := qInitV3 η_work rho_sel + 2 * rho_sep +
        qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep +
        qAbsorb η_work + qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep
    let q_diff : ℝ := qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
    let q_size : ℝ := qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
    let ζ_dir : ℝ := ζDir p_projective ε κ0
    let η_proj : ℝ := ηProj L_exp η ε κ0 p_projective
    (0 ≤ q_graph_total) ∧ (0 ≤ q_diff) ∧ (0 ≤ q_size) ∧ (0 ≤ ζ_dir) ∧ (0 ≤ η_proj) ∧
    (q_graph_total = qInitV3 η_work rho_sel + 2 * rho_sep +
        qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep +
        qAbsorb η_work + qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep) ∧
    (q_diff = qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep) ∧
    (q_size = qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep) ∧
    (ζ_dir = ζDir p_projective ε κ0) ∧
    (η_proj = ηProj L_exp η ε κ0 p_projective) ∧
    δ ^ (εgain - (q_graph_total + 2 * q_diff + q_size + η + ζ_dir + η_proj)) ≤ 1 / 64 ∧
    (L_exp - 1 / 2 : ℝ) * η < ζ_dir + η_proj ∧
    6 * (4 : ℝ) * Real.sqrt 4 * δ ^ (ζ_dir + η_proj - (L_exp - 1 / 2 : ℝ) * η) < 1 := by
  dsimp only
  set q_graph_total : ℝ := qInitV3 η_work rho_sel + 2 * rho_sep +
      qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep +
      qAbsorb η_work + qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep
    with hq_graph_total
  set q_diff : ℝ := qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
    with hq_diff
  set q_size : ℝ := qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
    with hq_size
  set ζ_dir : ℝ := ζDir p_projective ε κ0 with hζ_dir
  set η_proj : ℝ := ηProj L_exp η ε κ0 p_projective with hη_proj
  have hp_nonneg : 0 ≤ p_projective := by linarith
  have hrho_sel_nonneg : 0 ≤ rho_sel := by linarith
  have hrho_sep_nonneg : 0 ≤ rho_sep := by linarith
  have hη_lt_work : η < η_work := by linarith [hη_work_eq_two]
  have hL_exp_nonneg : 0 ≤ L_exp := by linarith
  have hp_pos : 0 < p_projective := by linarith
  have h_q_graph_total_nonneg : 0 ≤ q_graph_total :=
    q_graph_total_nonneg hL_exp_pos hη_work_pos hε_pos hκ0_pos hp_nonneg hτ_pos hrho_sel_nonneg hrho_sep_nonneg
  have h_q_diff_nonneg : 0 ≤ q_diff :=
    qDiffV4_nonneg hL_exp_pos hη_work_pos hε_pos hκ0_pos hp_nonneg hτ_pos hrho_sel_nonneg hrho_sep_nonneg
  have h_q_size_nonneg : 0 ≤ q_size :=
    qSizeLossV4_nonneg hL_exp_pos hη_work_pos hε_pos hκ0_pos hp_nonneg hτ_pos hrho_sel_nonneg hrho_sep_nonneg
  have hζ_dir_nonneg : 0 ≤ ζ_dir := by
    dsimp only [ζ_dir, ζDir, qProjective] <;> positivity
  have hη_proj_nonneg : 0 ≤ η_proj := by
    dsimp only [η_proj, ηProj, qProjective] <;> positivity
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
      (hη_work_pos := hη_work_pos) (hη_pos := hη_pos) (hη_lt_work := hη_lt_work)
      (hL_exp_nonneg := hL_exp_nonneg)
      (hε_pos := hε_pos) (hκ0_pos := hκ0_pos)
      (hp_pos := hp_pos) (hτ_pos := hτ_pos)
      (hrho_sel_nonneg := hrho_sel_nonneg) (hrho_sep_nonneg := hrho_sep_nonneg)
      (h_budget := h_budget) (h_dir_64 := h_dir_64)
      q_graph_total q_diff q_size ζ_dir η_proj
      h_q_graph_total_eq h_q_diff_eq h_q_size_eq h_ζ_dir_eq h_η_proj_eq
  have h_proj_budget : (L_exp - 1 / 2 : ℝ) * η < ζ_dir + η_proj :=
    proj_budget_v4 (hL_exp_nonneg := hL_exp_nonneg) (hη_pos := hη_pos)
      (hε_pos := hε_pos) (hκ0_pos := hκ0_pos) (hp_pos := hp_pos)
  have h_e_ge : ζ_dir + η_proj - (L_exp - 1 / 2 : ℝ) * η ≥ η_work / 100 := by
    have h2 : 0 < qProjective p_projective ε κ0 := by dsimp only [qProjective]; positivity
    have h3 : ζ_dir + η_proj - (L_exp - 1 / 2 : ℝ) * η = 2 * qProjective p_projective ε κ0 + η / 2 := by
      dsimp only [ζ_dir, η_proj, ζDir, ηProj, qProjective] <;> ring
    rw [h3]
    have h4 : η = η_work / 2 := by linarith [hη_work_eq_two]
    rw [h4]; linarith [h2]
  have h_factor_absorb : 6 * (4 : ℝ) * Real.sqrt 4 * δ ^ (ζ_dir + η_proj - (L_exp - 1 / 2 : ℝ) * η) < 1 :=
    factor_absorb_simple (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (he_ge := h_e_ge) (h_box_bound := h_box_bound)
  exact ⟨h_q_graph_total_nonneg, h_q_diff_nonneg, h_q_size_nonneg, hζ_dir_nonneg, hη_proj_nonneg,
    h_q_graph_total_eq, h_q_diff_eq, h_q_size_eq, h_ζ_dir_eq, h_η_proj_eq,
    h_delta_small, h_proj_budget, h_factor_absorb⟩

/-! ## Absorption bridge wrappers -/

/-- **Size absorption wrapper**: wraps `bridge_size_absorb`. -/
lemma size_absorb_lemma
    {δ s C c_ret M_ret : ℝ}
    {L_exp η_work ε κ0 p_projective τ rho_sel rho_sep : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hC_pos : 0 < C)
    (hL_nonneg : 0 ≤ L_exp)
    (hη_work_pos : 0 < η_work)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_nonneg : 0 ≤ p_projective)
    (hτ_pos : 0 < τ)
    (hrho_sel_nonneg : 0 ≤ rho_sel)
    (hrho_sep_nonneg : 0 ≤ rho_sep)
    (h_retention : c_ret / M_ret ≥
        δ^(32 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep + qBox η_work τ) / C)
    (h_qAbsorb_threshold : δ^(qAbsorb η_work) ≤ 1 / C) :
    c_ret / M_ret * δ^(-s + qInputV4 L_exp η_work rho_sel rho_sep) ≥
      δ^(-s + qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep) :=
  bridge_size_absorb
    (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
    (hC_pos := hC_pos) (hL_nonneg := hL_nonneg)
    (hη_work_pos := hη_work_pos) (hε_pos := hε_pos)
    (hκ0_pos := hκ0_pos) (hp_nonneg := hp_nonneg)
    (hτ_pos := hτ_pos)
    (hrho_sel_nonneg := hrho_sel_nonneg) (hrho_sep_nonneg := hrho_sep_nonneg)
    (h_retention := h_retention)
    (h_qAbsorb_threshold := h_qAbsorb_threshold)

/-- **Regularity absorption wrapper**: bundles `regularity_threshold` and
`bridge_reg_absorb` into a single lemma. -/
lemma reg_absorb_lemma
    {δ εnc q_K qAbsorb qBox R_norm C_A K_ring K_work C_BSG R_ret : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hq_K_pos : 0 < q_K) (hεnc_pos : 0 < εnc)
    (hR_norm_nonneg : 0 ≤ R_norm)
    (hK_ring_pos : 0 < K_ring)
    (hC_A_eq : C_A = K_ring * δ ^ (-εnc / 2))
    (hK_work_eq : K_work = K_ring)
    (hC_BSG_eq : C_BSG = C_A * δ ^ (-(10 * q_K + qAbsorb)))
    (hR_ret_eq : R_ret = (64 : ℝ) * (3 ^ 22 : ℝ) * (2 * R_norm + 3) * δ ^ (-22 * q_K))
    (h2R_norm_le : 2 * R_norm ≤ δ ^ (-qBox))
    (hqBox_nonneg : 0 ≤ qBox)
    (h_KBSG_absorb : (81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80 ≤ δ ^ (-qAbsorb))
    (h_budget_ineq : εnc / 2 ≥ 32 * q_K + 2 * qAbsorb + qBox)
    (hC_BSG_pos : 0 < C_BSG)
    (hR_ret_pos : 0 < R_ret)
    (hK_work_pos : 0 < K_work) :
    2 * (C_BSG * R_ret) ≤ K_work * δ ^ (-εnc) :=
  have h_threshold : δ ^ εnc ≤ K_work / (2 * C_BSG * R_ret) :=
    regularity_threshold
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hq_K_pos := hq_K_pos) (hεnc_pos := hεnc_pos)
      (hR_norm_nonneg := hR_norm_nonneg)
      (hK_ring_pos := hK_ring_pos)
      (hC_A_eq := hC_A_eq) (hK_work_eq := hK_work_eq)
      (hC_BSG_eq := hC_BSG_eq) (hR_ret_eq := hR_ret_eq)
      (h2R_norm_le := h2R_norm_le) (hqBox_nonneg := hqBox_nonneg)
      (h_KBSG_absorb := h_KBSG_absorb)
      (h_budget_ineq := h_budget_ineq)
  bridge_reg_absorb
    (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
    (hC_BSG_pos := hC_BSG_pos) (hR_ret_pos := hR_ret_pos)
    (hK_work_pos := hK_work_pos) (hεnc_pos := hεnc_pos)
    (h_threshold := h_threshold)

/-- **Graph absorption wrapper**: bundles `graph_absorb_hc_proj_le` and
`bridge_graph_absorb_lower`. -/
lemma graph_absorb_lemma
    {δ η_work ε τ κ0 L_exp p_projective rho_sel rho_sep : ℝ}
    {q_K q_graph_total C_work' c_endgame c_ret c_proj D : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hη_work_pos : 0 < η_work)
    (hκ0_pos : 0 < κ0) (hτ_pos : 0 < τ)
    (hrho_sel_nonneg : 0 ≤ rho_sel) (hrho_sep_nonneg : 0 ≤ rho_sep)
    (hq_K_eq : q_K = qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep)
    (hq_graph_total_eq : q_graph_total =
        qInitV3 η_work rho_sel + 2 * rho_sep +
        qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep +
        qAbsorb η_work + qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep)
    (hc_endgame_eq : c_endgame = δ ^ (η_work / 2) / (14 * C_work' ^ 2))
    (hC_work'_pos : 0 < C_work')
    (hC_work'_le : C_work' ≤ δ ^ (-η_work))
    (hKBSG_absorb : (81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80 ≤ δ ^ (-(qAbsorb η_work)))
    (hc_mult_dir_pos : 0 < c_endgame)
    (hD_pos : 0 < D)
    (hc_ret_eq : c_ret = D / 4)
    (hc_proj_eq : c_proj = δ ^ q_graph_total)
    (hD_eq : D = δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ))) :
    c_ret ≥ (2 / c_endgame) * c_proj :=
  have h1 : δ ^ q_graph_total ≤ (δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ))) * c_endgame / 8 :=
    graph_absorb_hc_proj_le
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hη_work_pos := hη_work_pos) (hκ0_pos := hκ0_pos)
      (hτ_pos := hτ_pos)
      (hrho_sel_nonneg := hrho_sel_nonneg) (hrho_sep_nonneg := hrho_sep_nonneg)
      (hq_K_eq := hq_K_eq) (hq_graph_total_eq := hq_graph_total_eq)
      (hc_endgame_eq := hc_endgame_eq)
      (hC_work'_pos := hC_work'_pos) (hC_work'_le := hC_work'_le)
      (hKBSG_absorb := hKBSG_absorb)
  have hc_proj_le : c_proj ≤ D * c_endgame / 8 := by
    rw [hc_proj_eq, hD_eq]
    exact h1
  bridge_graph_absorb_lower
    (hc_mult_dir_pos := hc_mult_dir_pos)
    (hD_pos := hD_pos)
    (hc_ret_eq := hc_ret_eq)
    (hc_proj_le := hc_proj_le)

/-- **Sector absorption wrapper**: wraps `bridge_sector_absorb`. -/
lemma sector_absorb_lemma
    {δ τ η η_work ε_mass C_Y C_ν : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hη_work_pos : 0 < η_work)
    (hη_work_eq_two : η_work = 2 * η)
    (hτ_le_one : τ ≤ 1)
    (h4η_work_lt_tau : 4 * η_work < τ)
    (hε_mass_def : ε_mass = 3 * η_work / 2 + η_work / 100)
    (hC_Y_le : C_Y ≤ δ ^ (-η))
    (hC_ν_eq : C_ν = 3 * C_Y * (2 : ℝ) ^ τ)
    (h_box_bound : (2 ^ 20 : ℝ) ≤ δ ^ (-(η_work / 100))) :
    C_ν * δ ^ τ ≤ δ ^ ε_mass / 2 :=
  bridge_sector_absorb
    (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
    (hη_work_pos := hη_work_pos) (hη_work_eq_two := hη_work_eq_two)
    (hτ_le_one := hτ_le_one) (h4η_work_lt_tau := h4η_work_lt_tau)
    (hε_mass_def := hε_mass_def) (hC_Y_le := hC_Y_le)
    (hC_ν_eq := hC_ν_eq) (h_box_bound := h_box_bound)

/-- **Frostman budget wrapper**: wraps `helper6_frostman_budget_bridge_v4`. -/
lemma frostman_budget_lemma
    {δ τ η η_work ε εnc ε_mass C_Y C_ν L_chart K_work : ℝ}
    {L_exp p_projective κ0 rho_sel rho_sep : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hη_pos : 0 < η) (hη_work_pos : 0 < η_work)
    (hη_work_eq_two : η_work = 2 * η)
    (hτ_pos : 0 < τ) (hτ_le_one : τ ≤ 1)
    (hε_pos : 0 < ε) (hκ0_pos : 0 < κ0)
    (hp_nonneg : 0 ≤ p_projective)
    (hL_exp_eq_seven : L_exp = 7)
    (hrho_sel_nonneg : 0 ≤ rho_sel) (hrho_sep_nonneg : 0 ≤ rho_sep)
    (hε_mass_eq : ε_mass = 3 * η_work / 2 + η_work / 100)
    (hC_Y_le : C_Y ≤ δ ^ (-η))
    (hC_ν_pos : 0 < C_ν)
    (hC_ν_le : C_ν ≤ 3 * C_Y * (2 : ℝ) ^ τ)
    (hL_chart_eq : L_chart = δ ^ (-2 * rho_sep))
    (hK_work_ge1 : 1 ≤ K_work)
    (h_qTotalV4_le_enc4 : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤ εnc / 4)
    (h_box_bound : (2 : ℝ) ^ 20 ≤ δ ^ (-(η_work / 100))) :
    C_ν * (8 : ℝ) * δ ^ (-ε_mass) * L_chart ^ τ ≤ K_work * δ ^ (-εnc) :=
  helper6_frostman_budget_bridge_v4
    (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
    (hη_pos := hη_pos) (hη_work_pos := hη_work_pos)
    (hη_work_eq_two := hη_work_eq_two)
    (hτ_pos := hτ_pos) (hτ_le_one := hτ_le_one)
    (hε_pos := hε_pos) (hκ0_pos := hκ0_pos)
    (hp_nonneg := hp_nonneg) (hL_exp_eq_seven := hL_exp_eq_seven)
    (hrho_sel_nonneg := hrho_sel_nonneg) (hrho_sep_nonneg := hrho_sep_nonneg)
    (hε_mass_eq := hε_mass_eq) (hC_Y_le := hC_Y_le)
    (hC_ν_pos := hC_ν_pos) (hC_ν_le := hC_ν_le)
    (hL_chart_eq := hL_chart_eq) (hK_work_ge1 := hK_work_ge1)
    (h_qTotalV4_le_enc4 := h_qTotalV4_le_enc4)
    (h_box_bound := h_box_bound)

end ProductLikeIncidence.ProductReduction
