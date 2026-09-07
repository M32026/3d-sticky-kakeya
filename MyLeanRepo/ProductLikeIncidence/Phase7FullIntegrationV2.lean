module

/-
# Phase 7 Full Integration (Two-Family Version)

Restructured version of phase7_full_integration that separates pre-sector
incidence (S_pre) from post-sector smallness (hPostProjectionSmall).

## Key changes from original

1. **Removed**: `h_proj_bound` (global projection bound impossible due to λ pole)
2. **Added**: `S_pre`, `hS_pre_def`, `h_raw_proj_bound`, `h_chartFullLambda_bound`
3. **four_sector_pigeonhole** called explicitly after double counting
4. **hPostProjectionSmall** proved using scalar_covering_upper:
   - Post-sector projection ⊆ sectorProjectionSet (|chartFullLambda| ≤ 1)
   - N(sectorProjectionSet) ≤ 2 * N(raw fiber) via scalar_covering_upper
   - Factor 2 absorbed in budget

## Pipeline
1. Double counting → Θ_bad
2. four_sector_pigeonhole → sector i, Θ_sec
3. hG_density_pre from double counting (restricted to Θ_sec)
4. hPostProjectionSmall using |chartFullLambda| + scalar_covering_upper (factor 2)
5. Call direction_failure_composition_v6_with_sector
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.Compat
public import MyLeanRepo.ProductLikeIncidence.DirectionTransportProjectiveLine
public import MyLeanRepo.ProductLikeIncidence.SectorRingLemma51Wrapper
public import MyLeanRepo.ProductLikeIncidence.Phase8SectorTranslation
public import MyLeanRepo.ProductLikeIncidence.FourSectorChart
public import MyLeanRepo.ProductLikeIncidence.SectorChartGridHelpers
public import MyLeanRepo.ProductLikeIncidence.DirectionFailureCompositionV8
public import MyLeanRepo.ProductLikeIncidence.DirectionFailureCompositionV6WithSector
public import MyLeanRepo.ProductLikeIncidence.Phase7ScaledProjections
public import MyLeanRepo.ProductLikeIncidence.ChartFullLambda
public import MyLeanRepo.ProductLikeIncidence.Phase7Budgets
public import MyLeanRepo.ProductLikeIncidence.Phase7ChartBounds
public import MyLeanRepo.ProductLikeIncidence.Phase7PostProjectionSmall
public import MyLeanRepo.ProductLikeIncidence.Phase7DoubleCountingHelper
public import MyLeanRepo.ProductLikeIncidence.Phase7SectorSetupHelper
public import MyLeanRepo.FourSectorSelection
public import MyLeanRepo.OSWPrelude

@[expose] public section

open Set ENNReal Bornology MeasureTheory Classical


noncomputable section

namespace ProductLikeIncidence.ProductReduction

/-- Helper to convert `h_point_mult` into the format expected by
`double_counting_good_directions`, avoiding let-binding instance issues. -/
private lemma phase7_point_mult_converter_v2
    {Yfin : Finset ℝ} {A : Finset (EuclideanSpace ℝ (Fin 2))}
    {T : ℝ → Finset (EuclideanSpace ℝ (Fin 2))} {S_pre : ℝ → Set ℝ}
    {c_mult_dir : ℝ} {F_graph : Set (EuclideanSpace ℝ (Fin 2))}
    {x : ℝ → ℝ}
    (hA_eq : (A : Set _) = F_graph)
    (h_point_mult : ∀ p ∈ F_graph,
      ({y ∈ Yfin | p 0 * x y + p 1 ∈ S_pre y}.card : ℝ) ≥ c_mult_dir * Yfin.card)
    (h_T_def : ∀ y, (T y : Set _) = (A : Set _) ∩ {p : EuclideanSpace ℝ (Fin 2) | p 0 * x y + p 1 ∈ S_pre y}) :
    ∀ p ∈ A, ({y ∈ Yfin | p ∈ T y}.card : ℝ) ≥ c_mult_dir * Yfin.card := by
  intro p hp
  have h_p_in_F : p ∈ F_graph := by
    rw [← hA_eq]
    exact hp
  have h_main : ({y ∈ Yfin | p 0 * x y + p 1 ∈ S_pre y}.card : ℝ) ≥ c_mult_dir * Yfin.card :=
    h_point_mult p h_p_in_F
  have h_filter_eq : {y ∈ Yfin | p ∈ T y} = {y ∈ Yfin | p 0 * x y + p 1 ∈ S_pre y} := by
    ext y
    simp only [Finset.mem_filter]
    have h1 : p ∈ T y ↔ p 0 * x y + p 1 ∈ S_pre y := by
      have h2 : p ∈ (T y : Set _) ↔ p ∈ (A : Set _) ∧ p 0 * x y + p 1 ∈ S_pre y := by
        rw [h_T_def y]
        <;> simp [Set.mem_inter_iff]
        <;> tauto
      have h3 : (p ∈ (A : Set _) ∧ p 0 * x y + p 1 ∈ S_pre y) ↔ p 0 * x y + p 1 ∈ S_pre y := by
        exact ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩
      exact h2.trans h3
    exact ⟨fun ⟨hY, hT⟩ => ⟨hY, h1.mp hT⟩, fun ⟨hY, hS⟩ => ⟨hY, h1.mpr hS⟩⟩
  have h_goal : ({y ∈ Yfin | p ∈ T y}.card : ℝ) =
      ({y ∈ Yfin | p 0 * x y + p 1 ∈ S_pre y}.card : ℝ) :=
    congr_arg (fun s : Finset ℝ => (s.card : ℝ)) h_filter_eq
  rw [h_goal]
  exact h_main

lemma phase7_full_integration_v2
    {δ s τ κ0 ε ε_mass η εgain εnc : ℝ}
    {L_exp p_projective : ℝ}
    -- Basic
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hδ_dyadic : δ ∈ dyadicScales)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hτ_pos : 0 < τ)
    (hkappa_pos : 0 < κ0)
    (hκ0_lt_s : κ0 < s)
    (hκ0_le_tau : κ0 ≤ τ)
    (hε_pos : 0 < ε) (hε_mass_pos : 0 < ε_mass) (hη_pos : 0 < η)
    -- Budget parameters
    (q_graph_total q_diff q_size ζ_dir η_proj : ℝ)
    (h_q_graph_total_nonneg : 0 ≤ q_graph_total)
    (h_q_diff_nonneg : 0 ≤ q_diff)
    (h_q_size_nonneg : 0 ≤ q_size)
    (hζ_dir_nonneg : 0 ≤ ζ_dir)
    (hη_proj_nonneg : 0 ≤ η_proj)
    (h_budget : εgain > q_graph_total + 2 * q_diff + q_size + η + ζ_dir + η_proj)
    -- Projection exponent budget
    (h_proj_budget : (L_exp - 1 / 2 : ℝ) * η < ζ_dir + η_proj)
    -- Graph params
    (C_raw C_Pbar c_proj K_BSG K_work : ℝ)
    (hC_raw_pos : 0 < C_raw)
    (hC_Pbar_pos : 0 < C_Pbar)
    (hc_proj_pos : 0 < c_proj)
    (hK_BSG_pos : 0 < K_BSG)
    (hεgain_pos : 0 < εgain)
    (hK_BSG_le : K_BSG ≤ δ ^ (-q_diff))
    (hc_proj_ge : c_proj ≥ δ ^ q_graph_total)
    (h_delta_small : δ ^ (εgain - (q_graph_total + 2 * q_diff + q_size + η + ζ_dir + η_proj)) ≤ 1 / 64)
    -- Factor absorption: 6*C_raw*sqrt(C_Pbar)*δ^(ζ_dir+η_proj-(L_exp-1/2)*η) < 1
    (h_factor_absorb : 6 * C_raw * Real.sqrt C_Pbar * δ ^ (ζ_dir + η_proj - (L_exp - 1 / 2 : ℝ) * η) < 1)
    -- Direction transport params
    (q_pole C_ν L_chart : ℝ)
    (hq_pole_pos : 0 < q_pole)
    (hC_ν_pos : 0 < C_ν)
    (hL_chart_pos : 0 < L_chart)
    (hL_chart_ge_one : 1 ≤ L_chart)
    (hL_chart_ge : L_chart ≥ δ ^ (-2 * q_pole))
    -- Phase0 outputs
    {Y : Set ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν_frost : IsDirectionFrostman δ τ C_ν ν)
    (hY_sub_unit : Y ⊆ Set.Icc 0 1)
    (hY_fin : Y.Finite)
    (hY_mass : ν Y ≥ ENNReal.ofReal (δ ^ ε_mass))
    {Pbar_param : Set (EuclideanSpace ℝ (Fin 2))}
    (hPbar_bdd : IsBounded Pbar_param)
    (T_y_points : ℝ → Set (EuclideanSpace ℝ (Fin 2)))
    (hT_sub : ∀ y ∈ Y, T_y_points y ⊆ Pbar_param)
    -- Phase3 outputs: three directions
    (θ1 θ2 θ3 : ℝ)
    (hθ1_in_Icc : θ1 ∈ Set.Icc 0 1)
    (hθ2_in_Icc : θ2 ∈ Set.Icc 0 1)
    (hθ3_in_Icc : θ3 ∈ Set.Icc 0 1)
    (h_ord13 : θ1 < θ3)
    (h_ord32 : θ3 < θ2)
    (h_sep13 : |θ1 - θ3| ≥ δ ^ q_pole)
    (h_sep23 : |θ2 - θ3| ≥ δ ^ q_pole)
    -- Phase4 outputs: projective transform
    (x : ℝ → ℝ)
    (hx_formula : ∀ y, x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y)))
    -- Pre-sector projection family
    (S_pre : ℝ → Set ℝ)
    (hS_pre_thick : ∀ y ∈ Y, y ≠ θ2 → S_pre y ⊆
      intervalThicken (δ * (1 + |x y|) / 2) (phase7ScaledProjection y θ2 θ3 (T_y_points y)))
    -- Raw projection bound (for A_y = π_y(T_y_points))
    (h_raw_proj_bound : ∀ y ∈ Y,
      Nreal δ (Set.image (fun q : EuclideanSpace ℝ (Fin 2) => q 0 * y + q 1) (T_y_points y)) ≤
      ENNReal.ofReal C_raw *
      ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar_param)).toReal)))
    -- Phase5 outputs: incidence graph
    {F_graph : Set (EuclideanSpace ℝ (Fin 2))}
    (hF_graph_finite : F_graph.Finite)
    (hF_graph_grid : ∀ p ∈ F_graph, ∀ i : Fin 2, ∃ k : ℤ, p i = δ * (k : ℝ))
    {B1 B2 : Set ℝ}
    (hF_graph_sub : F_graph ⊆ {p | p 0 ∈ B1 ∧ p 1 ∈ B2})
    (hB1_grid_set : B1 ⊆ productLikeUnitGrid δ)
    (hB2_grid_set : B2 ⊆ productLikeUnitGrid δ)
    (hB1_bounded : IsBounded B1)
    (hB2_bounded : IsBounded B2)
    (hB1_nonempty : B1.Nonempty)
    (hB2_nonempty : B2.Nonempty)
    (hB1_lower : Nreal δ B1 ≥ ENNReal.ofReal (δ ^ (-s + q_size)))
    (hB2_lower : Nreal δ B2 ≥ ENNReal.ofReal (δ ^ (-s + q_size)))
    -- Sector data
    {C_B1 C_B2 : ℝ}
    (hB1_delta_kappa : IsProductLikeRealDeltaSCSet δ κ0 C_B1 B1)
    (hB2_delta_kappa : IsProductLikeRealDeltaSCSet δ κ0 C_B2 B2)
    (hC1_absorb : 2 * C_B1 ≤ K_work * δ ^ (-εnc))
    (hC2_absorb : 2 * C_B2 ≤ K_work * δ ^ (-εnc))
    (hB1_upper : Nreal δ B1 ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))))
    (hB2_upper : Nreal δ B2 ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))))
    (h_diff_B1B1 : Nreal δ (Set.image2 (· - ·) B1 B1) ≤ ENNReal.ofReal K_BSG * Nreal δ B1)
    (h_diff_B2B2 : Nreal δ (Set.image2 (· - ·) B2 B2) ≤ ENNReal.ofReal K_BSG * Nreal δ B2)
    (h_diff_B2B1 : Nreal δ (Set.image2 (· - ·) B2 B1) ≤ ENNReal.ofReal K_BSG * Nreal δ B1)
    (h_diff_B1B2 : Nreal δ (Set.image2 (· - ·) B1 B2) ≤ ENNReal.ofReal K_BSG * Nreal δ B2)
    (h_sum_B1B2_over_B1 : Nreal δ (Set.image2 (· + ·) B1 B2) ≤ ENNReal.ofReal K_BSG * Nreal δ B1)
    (h_sum_B1B2_over_B2 : Nreal δ (Set.image2 (· + ·) B1 B2) ≤ ENNReal.ofReal K_BSG * Nreal δ B2)
    -- Double counting
    (c_mult_dir : ℝ)
    (hc_mult_dir_pos : 0 < c_mult_dir)
    (hc_mult_dir_le_one : c_mult_dir ≤ 1)
    (h_point_mult : ∀ p ∈ F_graph,
      ({y ∈ hY_fin.toFinset | p 0 * x y + p 1 ∈ S_pre y}.card : ℝ)
        ≥ c_mult_dir * hY_fin.toFinset.card)
    (hF_graph_covering : ENat.toENNReal (dyadicCoveringNumber δ F_graph) ≥
      ENNReal.ofReal (2 / c_mult_dir) * ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2)
    -- Uniform measure
    (hν_uniform : ∀ y ∈ Y, ν {y} = ENNReal.ofReal (1 / (Y.ncard : ℝ)))
    -- Mass budget: bad direction mass fraction c_mult_dir/2 times νY ≥ δ^ε_mass
    (h_mass_budget : δ ^ ε_mass ≤ c_mult_dir / 2)
    -- Ring spec
    (h_ring_spec :
      ∀ (A : Set ℝ) (μ : Measure ℝ),
        A ⊆ Set.Icc 1 2 →
        IsProductLikeRealDeltaSCSet δ κ0 (K_work * δ ^ (-εnc)) A →
        Nreal δ A ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))) →
        IsDirectionFrostman δ κ0 (K_work * δ ^ (-εnc)) μ →
        ∃ x_dir ∈ μ.support,
          ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ A ≤
            Nreal δ (Set.image2 (fun a b => a + x_dir * b) A A))
    (hK_work_ge1 : 1 ≤ K_work)
    -- Pbar small
    (hPbar_small : ENat.toENNReal (dyadicCoveringNumber δ Pbar_param) <
        ENNReal.ofReal (C_Pbar * δ ^ (-(2 * s + η))))
    -- Sector absorption (uses ε_mass)
    (h_sector_absorb : C_ν * δ ^ τ ≤ δ ^ ε_mass / 2)
    (h_frostman_budget : C_ν * (8 : ℝ) * δ ^ (-ε_mass) * L_chart ^ τ ≤ K_work * δ ^ (-εnc))
    -- chartFullLambda absolute value bound for selected sector
    (h_chartFullLambda_bound : ∀ (i : Fin 4) (y : ℝ), sectorPredicate i x y →
      |chartFullLambda i y θ1 θ3 θ2 x| ≤ 1)
    :
    False := by
  -- ========================================================================
  -- Step 1: Double counting — extract Θ_bad (via helper)
  -- ========================================================================
  rcases phase7_double_counting_helper
    (hδ_pos := hδ_pos)
    (hε_mass_pos := hε_mass_pos)
    (hY_sub_unit := hY_sub_unit)
    (Yfin := hY_fin.toFinset)
    (hYfin_eq := hY_fin.coe_toFinset)
    (hY_mass := hY_mass)
    (hF_graph_finite := hF_graph_finite)
    (hF_graph_grid := hF_graph_grid)
    (x := x)
    (c_mult_dir := c_mult_dir)
    (hc_mult_dir_pos := hc_mult_dir_pos)
    (hc_mult_dir_le_one := hc_mult_dir_le_one)
    (h_point_mult := h_point_mult)
    (hν_uniform := hν_uniform)
    (h_mass_budget := h_mass_budget)
    (c_proj := c_proj)
    (hc_proj_pos := hc_proj_pos)
    (hF_graph_covering := hF_graph_covering)
    with ⟨Θ_bad, hΘ_bad_sub_Y, h_Θbad_mass, hG_density⟩

  -- ========================================================================
  -- Steps 2-5: Sector setup (via helper)
  -- ========================================================================
  have hK_work_pos : 0 < K_work := by linarith [hK_work_ge1]
  rcases phase7_sector_setup_helper
    (hδ_pos := hδ_pos)
    (hδ_lt_one := hδ_lt_one)
    (hδ_dyadic := hδ_dyadic)
    (hτ_pos := hτ_pos)
    (hε_mass_pos := hε_mass_pos)
    (C_ν := C_ν)
    (hC_ν_pos := hC_ν_pos)
    (hν_frost := hν_frost)
    (hY_sub_unit := hY_sub_unit)
    (hY_fin := hY_fin)
    (h_sector_absorb := h_sector_absorb)
    (h_Θbad_mass := h_Θbad_mass)
    (hΘ_bad_sub_Y := hΘ_bad_sub_Y)
    (θ1 := θ1) (θ2 := θ2) (θ3 := θ3)
    (q_pole := q_pole)
    (hθ1_in_Icc := hθ1_in_Icc)
    (hθ2_in_Icc := hθ2_in_Icc)
    (h_ord13 := h_ord13)
    (h_ord32 := h_ord32)
    (h_sep13 := h_sep13)
    (h_sep23 := h_sep23)
    (hq_pole_pos := hq_pole_pos)
    (L_chart := L_chart)
    (hL_chart_ge := hL_chart_ge)
    (x := x)
    (hx_formula := hx_formula)
    (c_proj := c_proj)
    (hB1_grid_set := hB1_grid_set)
    (hB2_grid_set := hB2_grid_set)
    (hB1_bounded := hB1_bounded)
    (hB2_bounded := hB2_bounded)
    (hB1_delta_kappa := hB1_delta_kappa)
    (hB2_delta_kappa := hB2_delta_kappa)
    (hK_work_pos := hK_work_pos)
    (hC1_absorb := hC1_absorb)
    (hC2_absorb := hC2_absorb)
    (hB1_upper := hB1_upper)
    (hB2_upper := hB2_upper)
    (h_diff_B1B1 := h_diff_B1B1)
    (h_diff_B2B2 := h_diff_B2B2)
    (h_diff_B2B1 := h_diff_B2B1)
    (h_diff_B1B2 := h_diff_B1B2)
    (h_sum_B1B2_over_B1 := h_sum_B1B2_over_B1)
    (h_sum_B1B2_over_B2 := h_sum_B1B2_over_B2)
    (hG_density := hG_density)
    with ⟨r, i, Θ_sec, hr_pos, hδ_le_r, h_r_pow, hΘ_sec_sub,
      hΘ_sec_finite, hΘ_sec_closed, hΘ_sec_mass, h_sector, h_sector_range,
      h_sector_proj_id, hΘ_sec_sub_Y2, hG_density_pre, h_chart_colip_sec,
      h_diff1_sector, h_diff2_sector, h_size_upper_sector, hB1_delta_kappa_sector⟩

  have hΘ_sec_sub_Y : Θ_sec ⊆ Y := hΘ_sec_sub_Y2

  -- ========================================================================
  -- Step 6: hPostProjectionSmall via extracted lemma (Route B, factor 6)
  -- ========================================================================
  have hPostProjectionSmall : ∀ y ∈ Θ_sec,
      ENat.toENNReal (dyadicCoveringNumber δ
        (projectionSet1D (sectorTMap i (x y))
          (FourSectorChart.chartSectorCoordPoint i ''
            (F_graph ∩ {p | p 0 * x y + p 1 ∈ S_pre y})))) <
      (1 / 2 : ENNReal) * ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
        ENNReal.ofReal (δ ^ (-εgain)) *
        Nreal δ (sectorCoordSet i B2 B1) := by
    intro y hy
    have hy_ne_theta2 : y ≠ θ2 := by
      have h_notin_ball : y ∉ Metric.ball θ2 r := (hΘ_sec_sub hy).2
      have h_dist : dist y θ2 ≥ r := by simpa [Metric.mem_ball] using h_notin_ball
      have h_pos : 0 < dist y θ2 := lt_of_lt_of_le hr_pos h_dist
      exact dist_pos.mp h_pos
    exact phase7_post_projection_small_routeB
      (C_raw := C_raw)
      (C_Pbar := C_Pbar)
      (c_proj := c_proj)
      (K_BSG := K_BSG)
      (hδ_pos := hδ_pos)
      (hδ_lt_one := hδ_lt_one)
      (h_budget := h_budget)
      (h_proj_budget := h_proj_budget)
      (h_factor_absorb := h_factor_absorb)
      (hC_raw_pos := hC_raw_pos)
      (hC_Pbar_pos := hC_Pbar_pos)
      (hc_proj_pos := hc_proj_pos)
      (hK_BSG_pos := hK_BSG_pos)
      (hεgain_pos := hεgain_pos)
      (hK_BSG_le := hK_BSG_le)
      (hc_proj_ge := hc_proj_ge)
      (h_delta_small := h_delta_small)
      (i := i)
      (y := y)
      (Θ_sec := Θ_sec)
      (hy := hy)
      (hy_ne_theta2 := hy_ne_theta2)
      (hΘ_sec_sub_Y := hΘ_sec_sub_Y)
      (h_sector := h_sector y hy)
      (hx_formula := hx_formula)
      (hT_sub := hT_sub)
      (hS_pre_thick := hS_pre_thick)
      (hPbar_bdd := hPbar_bdd)
      (hPbar_small := hPbar_small)
      (h_raw_proj_bound := h_raw_proj_bound)
      (h_chartFullLambda_bound := h_chartFullLambda_bound)
      (hB1_lower := hB1_lower)
      (hB2_lower := hB2_lower)

  -- ========================================================================
  -- Step 7: Finite instance and call v6_with_sector
  -- ========================================================================
  have hΘ_bad_finite : Set.Finite Θ_bad := hY_fin.subset hΘ_bad_sub_Y
  letI : Finite Θ_bad := hΘ_bad_finite

  exact direction_failure_composition_v6_with_sector
    (ε := ε_mass)
    (hδ_pos := hδ_pos)
    (hδ_lt_one := hδ_lt_one)
    (hδ_dyadic := hδ_dyadic)
    (hs_pos := hs_pos) (hs_lt_one := hs_lt_one)
    (hτ_pos := hτ_pos)
    (hkappa_pos := hkappa_pos)
    (hκ0_lt_s := hκ0_lt_s)
    (hκ0_le_tau := hκ0_le_tau)
    (hε_pos := hε_mass_pos) (hη_pos := hη_pos)
    (h_q_graph_total_nonneg := h_q_graph_total_nonneg)
    (h_q_diff_nonneg := h_q_diff_nonneg)
    (h_q_size_nonneg := h_q_size_nonneg)
    (hζ_dir_nonneg := hζ_dir_nonneg)
    (hη_proj_nonneg := hη_proj_nonneg)
    (h_budget := h_budget)
    (hc_proj_pos := hc_proj_pos)
    (hK_BSG_pos := hK_BSG_pos)
    (hεgain_pos := hεgain_pos)
    (hK_BSG_le := hK_BSG_le)
    (hc_proj_ge := hc_proj_ge)
    (h_delta_small := h_delta_small)
    (hC_ν_pos := hC_ν_pos)
    (hL_chart_pos := hL_chart_pos)
    (hL_chart_ge_one := hL_chart_ge_one)
    (hF_graph_finite := hF_graph_finite)
    (hF_graph_grid := hF_graph_grid)
    (hF_graph_sub := hF_graph_sub)
    (hB1_grid_set := hB1_grid_set)
    (hB2_grid_set := hB2_grid_set)
    (hB1_bounded := hB1_bounded)
    (hB2_bounded := hB2_bounded)
    (hB1_nonempty := hB1_nonempty)
    (hB2_nonempty := hB2_nonempty)
    (hB1_lower := hB1_lower)
    (hB2_lower := hB2_lower)
    (hν_frost := hν_frost)
    (y1 := θ2)
    (h_Θbad_mass := h_Θbad_mass)
    (x := x)
    (S_pre := S_pre)
    (h_ring_spec := h_ring_spec)
    (hK_work_ge1 := hK_work_ge1)
    (h_diff1_sector := h_diff1_sector)
    (h_diff2_sector := h_diff2_sector)
    (h_size_upper_sector := h_size_upper_sector)
    (hB1_delta_kappa_sector := hB1_delta_kappa_sector)
    (h_frostman_budget := h_frostman_budget)
    (r := r)
    (hr_pos := hr_pos)
    (i := i)
    (Θ_sec := Θ_sec)
    (hΘ_sec_sub := hΘ_sec_sub)
    (hΘ_sec_finite := hΘ_sec_finite)
    (hΘ_sec_mass := hΘ_sec_mass)
    (h_sector := h_sector)
    (h_sector_range := h_sector_range)
    (hG_density_pre := hG_density_pre)
    (hPostProjectionSmall := hPostProjectionSmall)
    (h_chart_colip_sec := h_chart_colip_sec)

end ProductLikeIncidence.ProductReduction
