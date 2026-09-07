module

/-
# Direction Failure Composition v6 (with pre-selected sector, pre/post separation)

Variant of `direction_failure_composition_v6` that:
1. Accepts four_sector_pigeonhole outputs as explicit arguments
2. Separates pre-sector incidence (S_pre) from post-sector smallness (hPostProjectionSmall)

## Why pre/post separation?

The projective scaling `λ(y) = (θ2-θ3)/(θ2-y)` can be large in reciprocal sectors.
The useful bound is `|chartFullLambda_i(y)| = |chartSectorScalar_i(x(y)) * λ(y)| ≤ 1`,
which is a post-sector coefficient.

The old interface used one family `S(y)` for both incidence and smallness, forcing
`N(S_pre(y))` to be small — impossible when λ(y) is large.

## New interface

- `S_pre(y)`: pre-sector projection `λ(y) * π_y(T_y)`, used ONLY for incidence
- `hG_density_pre`: graph density with pre-sector incidence
- `hPostProjectionSmall`: DIRECT bound on post-sector graph projection
  (replaces both `hS_small_sec` AND the generic four-sector projection-preservation step)

The caller proves `hPostProjectionSmall` using `|chartFullLambda_i(y)| ≤ 1` plus
scaling/translation/thickening factors, without factoring through `N(S_pre(y))`.
-/

public import MyLeanRepo.ProductLikeIncidence.DirectionFailureCompositionV8
public import MyLeanRepo.FourSectorSelection
public import MyLeanRepo.OSWPrelude

@[expose] public section

open Set ENNReal Bornology MeasureTheory Classical

noncomputable section

namespace ProductLikeIncidence.ProductReduction

lemma direction_failure_composition_v6_with_sector
    {δ s τ κ0 ε η εgain εnc : ℝ}
    {q_graph_total q_diff q_size ζ_dir η_proj : ℝ}
    {c_proj K_BSG K_work : ℝ}
    {C_ν L_chart : ℝ}
    {B1_original B2_original : Set ℝ}
    {F_graph : Set (EuclideanSpace ℝ (Fin 2))}
    -- Basic
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hδ_dyadic : δ ∈ dyadicScales)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hτ_pos : 0 < τ)
    (hkappa_pos : 0 < κ0)
    (hκ0_lt_s : κ0 < s)
    (hκ0_le_tau : κ0 ≤ τ)
    (hε_pos : 0 < ε) (hη_pos : 0 < η)
    -- Budget
    (h_q_graph_total_nonneg : 0 ≤ q_graph_total)
    (h_q_diff_nonneg : 0 ≤ q_diff)
    (h_q_size_nonneg : 0 ≤ q_size)
    (hζ_dir_nonneg : 0 ≤ ζ_dir)
    (hη_proj_nonneg : 0 ≤ η_proj)
    (h_budget : εgain > q_graph_total + 2 * q_diff + q_size + η + ζ_dir + η_proj)
    -- Graph params
    (hc_proj_pos : 0 < c_proj)
    (hK_BSG_pos : 0 < K_BSG)
    (hεgain_pos : 0 < εgain)
    (hK_BSG_le : K_BSG ≤ δ ^ (-q_diff))
    (hc_proj_ge : c_proj ≥ δ ^ q_graph_total)
    (h_delta_small : δ ^ (εgain - (q_graph_total + 2 * q_diff + q_size + η + ζ_dir + η_proj)) ≤ 1 / 64)
    -- Direction transport params
    (hC_ν_pos : 0 < C_ν)
    (hL_chart_pos : 0 < L_chart)
    (hL_chart_ge_one : 1 ≤ L_chart)
    -- F_graph
    (hF_graph_finite : F_graph.Finite)
    (hF_graph_grid : ∀ p ∈ F_graph, ∀ i : Fin 2, ∃ k : ℤ, p i = δ * (k : ℝ))
    (hF_graph_sub : F_graph ⊆ {p | p 0 ∈ B1_original ∧ p 1 ∈ B2_original})
    -- B1, B2 grid-aligned subsets of [0,1]
    (hB1_grid_set : B1_original ⊆ productLikeUnitGrid δ)
    (hB2_grid_set : B2_original ⊆ productLikeUnitGrid δ)
    (hB1_bounded : IsBounded B1_original)
    (hB2_bounded : IsBounded B2_original)
    (hB1_nonempty : B1_original.Nonempty)
    (hB2_nonempty : B2_original.Nonempty)
    (hB1_lower : Nreal δ B1_original ≥ ENNReal.ofReal (δ ^ (-s + q_size)))
    (hB2_lower : Nreal δ B2_original ≥ ENNReal.ofReal (δ ^ (-s + q_size)))
    -- Bad directions
    {Θ_bad : Set ℝ}
    [Finite Θ_bad]
    {ν : Measure ℝ}
    [hν_prob : IsProbabilityMeasure ν]
    (hν_frost : IsDirectionFrostman δ τ C_ν ν)
    {y1 : ℝ}
    (h_Θbad_mass : ν Θ_bad ≥ ENNReal.ofReal (δ ^ ε))
    -- Cross-ratio
    (x : ℝ → ℝ)
    -- Pre-sector projection family (for incidence ONLY)
    (S_pre : ℝ → Set ℝ)
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
    -- Sector data from Phase8SectorTranslation
    (h_diff1_sector : ∀ i : Fin 4,
      Nreal δ (Set.image2 (· - ·) (sectorRingBaseSet i B1_original B2_original)
        (sectorRingBaseSet i B1_original B2_original)) ≤
      ENNReal.ofReal K_BSG * Nreal δ (sectorRingBaseSet i B1_original B2_original))
    (h_diff2_sector : ∀ i : Fin 4,
      Nreal δ (Set.image2 (· - ·) (sectorCoordSet i B1_original B2_original)
        (sectorRingBaseSet i B1_original B2_original)) ≤
      ENNReal.ofReal K_BSG * Nreal δ (sectorRingBaseSet i B1_original B2_original))
    (h_size_upper_sector : ∀ i : Fin 4,
      Nreal δ (sectorRingBaseSet i B1_original B2_original) ≤
      ENNReal.ofReal (K_work * δ ^ (-(s + εnc))))
    (hB1_delta_kappa_sector : ∀ i : Fin 4,
      IsProductLikeRealDeltaSCSet δ κ0 (K_work * δ ^ (-εnc))
        (sectorRingBaseSet i B1_original B2_original))
    -- Frostman constant budget
    (h_frostman_budget : C_ν * (8 : ℝ) * δ ^ (-ε) * L_chart ^ τ ≤ K_work * δ ^ (-εnc))
    -- =====================================================================
    -- SECTOR SELECTION INPUTS (from four_sector_pigeonhole)
    -- =====================================================================
    (r : ℝ)
    (hr_pos : 0 < r)
    (i : Fin 4)
    (Θ_sec : Set ℝ)
    (hΘ_sec_sub : Θ_sec ⊆ Θ_bad \ Metric.ball y1 r)
    (hΘ_sec_finite : Set.Finite Θ_sec)
    (hΘ_sec_mass : ν Θ_sec ≥ (1 / 8 : ENNReal) * ν Θ_bad)
    (h_sector : ∀ y ∈ Θ_sec, sectorPredicate i x y)
    (h_sector_range : ∀ y ∈ Θ_sec, sectorTMap i (x y) ∈ Set.Icc 0 1)
    -- =====================================================================
    -- PRE-SECTOR DENSITY (using S_pre for incidence)
    -- =====================================================================
    (hG_density_pre : ∀ y ∈ Θ_sec,
      ENat.toENNReal (dyadicCoveringNumber δ
        (F_graph ∩ {p | p 0 * x y + p 1 ∈ S_pre y})) ≥
      ENNReal.ofReal c_proj * Nreal δ B1_original * Nreal δ B2_original)
    -- =====================================================================
    -- POST-SECTOR PROJECTION SMALLNESS (DIRECT — no factoring through S_pre)
    --
    -- The caller proves this using |chartFullLambda_i(y)| ≤ 1 plus
    -- scaling/translation/thickening factors.
    -- =====================================================================
    (hPostProjectionSmall : ∀ y ∈ Θ_sec,
      ENat.toENNReal (dyadicCoveringNumber δ
        (projectionSet1D (sectorTMap i (x y))
          (FourSectorChart.chartSectorCoordPoint i ''
            (F_graph ∩ {p | p 0 * x y + p 1 ∈ S_pre y})))) <
      (1 / 2 : ENNReal) * ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
        ENNReal.ofReal (δ ^ (-εgain)) *
        Nreal δ (sectorCoordSet i B2_original B1_original))
    -- =====================================================================
    -- CHART CO-LIPSCHITZ (on selected sector)
    -- =====================================================================
    (h_chart_colip_sec : ∀ y ∈ Θ_sec, ∀ z ∈ Θ_sec, y ≠ y1 → z ≠ y1 →
      |y - z| ≤ L_chart * |sectorTMap i (x y) - sectorTMap i (x z)|)
    :
    False := by
  -- ========================================================================
  -- Step 2: Sector chart
  -- ========================================================================
  let sector_chart : ℝ → ℝ := fun y => sectorTMap i (x y)

  have h_chart_range : ∀ y ∈ Θ_sec, sector_chart y ∈ Set.Icc 0 1 := by
    intro y hy; exact h_sector_range y hy

  let sector_chart_meas : ℝ → ℝ := fun y => if y ∈ Θ_sec then sector_chart y else 0

  have h_chart_meas : Measurable sector_chart_meas := by
    have hms : MeasurableSet Θ_sec := hΘ_sec_finite.measurableSet
    have h_main : ∀ (s : Set ℝ), MeasurableSet s → MeasurableSet (sector_chart_meas ⁻¹' s) := by
      intro s hs
      by_cases h0 : (0 : ℝ) ∈ s
      · have h_eq : sector_chart_meas ⁻¹' s = Θ_secᶜ ∪ {y ∈ Θ_sec | sector_chart y ∈ s} := by
          ext y
          simp only [Set.mem_preimage, Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq]
          by_cases hy : y ∈ Θ_sec <;> simp [sector_chart_meas, hy, h0] <;> tauto
        rw [h_eq]
        have hsub : Set.Finite {y ∈ Θ_sec | sector_chart y ∈ s} := hΘ_sec_finite.subset fun _ => And.left
        exact hms.compl.union hsub.measurableSet
      · have h_eq : sector_chart_meas ⁻¹' s = {y ∈ Θ_sec | sector_chart y ∈ s} := by
          ext y
          simp only [Set.mem_preimage, Set.mem_setOf_eq]
          by_cases hy : y ∈ Θ_sec <;> simp [sector_chart_meas, hy, h0] <;> tauto
        rw [h_eq]
        have hsub : Set.Finite {y ∈ Θ_sec | sector_chart y ∈ s} := hΘ_sec_finite.subset fun _ => And.left
        exact hsub.measurableSet
    exact Measurable.le (fun s a => a) h_main

  have h_agree_on_sec : ∀ y ∈ Θ_sec, sector_chart_meas y = sector_chart y := by
    intro y hy
    simp [sector_chart_meas, hy]

  have h_chart_colip : ∀ y ∈ Θ_sec, ∀ z ∈ Θ_sec, y ≠ y1 → z ≠ y1 →
      |y - z| ≤ L_chart * |sector_chart_meas y - sector_chart_meas z| := by
    intro y hy z hz hy1 hz1
    have h_eq_y : sector_chart_meas y = sector_chart y := h_agree_on_sec y hy
    have h_eq_z : sector_chart_meas z = sector_chart z := h_agree_on_sec z hz
    rw [h_eq_y, h_eq_z]
    exact h_chart_colip_sec y hy z hz hy1 hz1

  have h_chart_range_meas : ∀ y ∈ Θ_sec, sector_chart_meas y ∈ Set.Icc 0 1 := by
    intro y hy
    rw [h_agree_on_sec y hy]
    exact h_chart_range y hy

  -- ========================================================================
  -- Step 3: Construct ν_dir
  -- ========================================================================
  have hΘ_bad_pos : 0 < ν Θ_bad := by
    have h4 : 0 < ENNReal.ofReal (δ ^ ε) := ENNReal.ofReal_pos.mpr (by positivity)
    exact h4.trans_le h_Θbad_mass
  have hΘ_sec_pos : 0 < ν Θ_sec := by
    have h1 : ν Θ_sec ≥ (1 / 8 : ENNReal) * ν Θ_bad := hΘ_sec_mass
    have h2 : 0 < (1 / 8 : ENNReal) * ν Θ_bad := by
      have hpos : (0 : ENNReal) < (1 / 8 : ENNReal) := by norm_num
      have hmul_pos : ∀ (a b : ENNReal), 0 < a → 0 < b → 0 < a * b := by
        intro a b ha hb
        simpa [pos_iff_ne_zero] using mul_ne_zero ha.ne' hb.ne'
      exact hmul_pos (1 / 8) (ν Θ_bad) hpos hΘ_bad_pos
    exact h2.trans_le h1

  let ν_dir : Measure ℝ :=
    (ν Θ_sec)⁻¹ • Measure.map sector_chart_meas (ν.restrict Θ_sec)

  have hν_dir_prob : IsProbabilityMeasure ν_dir := by
    have h_map_univ : (Measure.map sector_chart_meas (ν.restrict Θ_sec)) Set.univ = ν Θ_sec := by
      rw [Measure.map_apply h_chart_meas (MeasurableSet.univ)] <;> simp
    refine' ⟨_⟩
    have h : ν_dir Set.univ = (ν Θ_sec)⁻¹ * (Measure.map sector_chart_meas (ν.restrict Θ_sec)) Set.univ := by
      simp [ν_dir] <;> rfl
    rw [h, h_map_univ]
    have hΘ_ne_top : ν Θ_sec ≠ ⊤ := by
      have h : ν Θ_sec ≤ ν Set.univ := measure_mono (Set.subset_univ _)
      rw [hν_prob.1] at h
      exact ne_top_of_le_ne_top (by simp) h
    exact ENNReal.inv_mul_cancel hΘ_sec_pos.ne' hΘ_ne_top

  have hν_dir_frost : IsDirectionFrostman δ κ0 (K_work * δ ^ (-εnc)) ν_dir := by
    have hΘ_ne_top : ν Θ_sec ≠ ⊤ := by
      have h : ν Θ_sec ≤ ν Set.univ := measure_mono (Set.subset_univ _)
      rw [hν_prob.1] at h
      exact ne_top_of_le_ne_top (by simp) h
    have h_pole_avoid : ∀ y ∈ Θ_sec, y ≠ y1 := by
      intro y hy
      have h1 : Θ_sec ⊆ Θ_bad \ Metric.ball y1 r := hΘ_sec_sub
      have h2 : y ∉ Metric.ball y1 r := (h1 hy).2
      intro h_eq
      rw [h_eq] at h2
      exact h2 (by simp [Metric.mem_ball, hr_pos])
    have h_frost_result := direct_frostman_transport
      (hν_frost := hν_frost)
      (hΘ_sec_finite := hΘ_sec_finite)
      (hΘ_sec_pos := hΘ_sec_pos)
      (hΘ_sec_ne_top := hΘ_ne_top)
      (hΘ_sec_mass_ge := by
        have h1 : ν Θ_sec ≥ (1 / 8 : ENNReal) * ν Θ_bad := hΘ_sec_mass
        have h2 : ν Θ_bad ≥ ENNReal.ofReal (δ ^ ε) := h_Θbad_mass
        calc ν Θ_sec ≥ (1 / 8 : ENNReal) * ν Θ_bad := h1
             _ ≥ (1 / 8 : ENNReal) * ENNReal.ofReal (δ ^ ε) := by gcongr
             _ = ENNReal.ofReal ((1 / 8 : ℝ) * δ ^ ε) := by
               simp [ENNReal.ofReal_mul] <;> ring_nf)
      (h_pole_avoid := h_pole_avoid)
      (h_f_dir_meas := h_chart_meas)
      (h_f_dir_colip := h_chart_colip)
      (h_f_dir_range := h_chart_range_meas)
      (hδ_pos := hδ_pos)
      (hδ_lt_one := hδ_lt_one)
      (hτ_pos := hτ_pos)
      (hkappa_pos := hkappa_pos)
      (hκ0_le_tau := hκ0_le_tau)
      (hε_pos := hε_pos)
      (hC_ν_pos := hC_ν_pos)
      (hL_chart_pos := hL_chart_pos)
      (hL_chart_ge_one := hL_chart_ge_one)
      (hK_work_ge1 := hK_work_ge1)
      (h_frostman_budget := h_frostman_budget)
    exact h_frost_result.2

  -- ========================================================================
  -- Step 4: Reverse support correspondence
  -- ========================================================================
  have h_reverse_support : ∀ t ∈ ν_dir.support, ∃ y ∈ Θ_sec, sector_chart y = t := by
    have hΘ_sec_finite' : Set.Finite Θ_sec := hΘ_sec_finite
    let Image := sector_chart '' Θ_sec
    have h_image_finite : Set.Finite Image := hΘ_sec_finite'.image _
    have h_image_closed : IsClosed Image := h_image_finite.isClosed
    have h_map_null : (Measure.map sector_chart_meas (ν.restrict Θ_sec)) Imageᶜ = 0 := by
      rw [Measure.map_apply h_chart_meas h_image_closed.isOpen_compl.measurableSet]
      have h7 : sector_chart_meas ⁻¹' Imageᶜ ∩ Θ_sec = ∅ := by
        ext z
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        intro ⟨hz2, hz1⟩
        have hz3 : sector_chart_meas z = sector_chart z := by
          simp [sector_chart_meas, hz1]
        rw [hz3] at hz2
        have hz4 : sector_chart z ∈ Image := ⟨z, hz1, rfl⟩
        exact hz2 hz4
      rw [Measure.restrict_apply (h_image_closed.isOpen_compl.measurableSet.preimage h_chart_meas), h7]
      <;> simp
    have h_dir_null : ν_dir Imageᶜ = 0 := by
      simp [ν_dir, h_map_null] <;> simp
    intro t ht
    by_cases h : t ∈ Image
    · rcases h with ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · have h5 : t ∈ Imageᶜ := h
      have h6 : IsOpen Imageᶜ := h_image_closed.isOpen_compl
      have h7 : 0 < ν_dir Imageᶜ := by
        rw [Measure.mem_support_iff_forall] at ht
        exact ht Imageᶜ (h6.mem_nhds h5)
      rw [h_dir_null] at h7
      exact False.elim (lt_irrefl 0 h7)

  -- ========================================================================
  -- Step 5: Sector point map and graph witness
  --
  -- PRE/POST SEPARATION:
  -- - Density uses S_pre (pre-sector incidence)
  -- - Projection bound uses hPostProjectionSmall DIRECTLY
  --   (no factoring through N(S_pre), no generic projection-preservation factor)
  -- ========================================================================
  let B1 := sectorRingBaseSet i B2_original B1_original
  let B2 := sectorCoordSet i B2_original B1_original
  let sec_map := FourSectorChart.chartSectorCoordPoint i

  let G_family (y : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
    sec_map '' (F_graph ∩ {p | p 0 * x y + p 1 ∈ S_pre y})

  have hG_family : ∀ y ∈ Θ_sec,
      IsBounded (G_family y) ∧
      (∀ p ∈ G_family y, p 0 ∈ B1 ∧ p 1 ∈ B2) ∧
      (∀ p ∈ G_family y, ∀ j : Fin 2, ∃ k : ℤ, p j = δ * (k : ℝ)) ∧
      ENat.toENNReal (dyadicCoveringNumber δ (G_family y)) ≥
        ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2 ∧
      ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D (sector_chart y) (G_family y))) <
        (1 / 2 : ENNReal) * ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
          ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ B2 := by
    intro y hy
    let G_y := F_graph ∩ {p | p 0 * x y + p 1 ∈ S_pre y}
    have hG_y_sub_F : G_y ⊆ F_graph := fun x hx => hx.1
    have hG_y_finite : Set.Finite G_y := hF_graph_finite.subset hG_y_sub_F
    have hG_y_bdd : IsBounded G_y := hG_y_finite.isBounded
    have hG_y_grid : ∀ p ∈ G_y, ∀ j : Fin 2, ∃ k : ℤ, p j = δ * (k : ℝ) :=
      fun p hp => hF_graph_grid p (hp.1)
    have hG_y_sub2 : ∀ p ∈ G_y, p 0 ∈ B1_original ∧ p 1 ∈ B2_original :=
      fun p hp => hF_graph_sub (hp.1)

    -- 1. Boundedness
    have h1 : IsBounded (G_family y) := (hG_y_finite.image sec_map).isBounded

    -- 2. Subset B1 × B2
    have h2 : ∀ p ∈ G_family y, p 0 ∈ B1 ∧ p 1 ∈ B2 := by
      intro p hp
      rcases hp with ⟨q, hq, rfl⟩
      have hq0 : q 0 ∈ B1_original := (hG_y_sub2 q hq).1
      have hq1 : q 1 ∈ B2_original := (hG_y_sub2 q hq).2
      exact phase8_to_chart_sector i hq0 hq1

    -- 3. Grid
    have h3 : ∀ p ∈ G_family y, ∀ j : Fin 2, ∃ k : ℤ, p j = δ * (k : ℝ) := by
      intro p hp j
      rcases hp with ⟨q, hq, rfl⟩
      have hq0 : ∃ k : ℤ, q 0 = δ * (k : ℝ) := hG_y_grid q hq 0
      have hq1 : ∃ k : ℤ, q 1 = δ * (k : ℝ) := hG_y_grid q hq 1
      fin_cases i <;> fin_cases j <;> simp [sec_map, FourSectorChart.chartSectorCoordPoint,
        FourSectorChart.chartSectorCoord] <;>
        (try { exact hq0 }) <;> (try { exact hq1 }) <;>
        (try { rcases hq0 with ⟨k, hk⟩; refine ⟨-k, ?_⟩; simp [hk] <;> ring }) <;>
        (try { rcases hq1 with ⟨k, hk⟩; refine ⟨-k, ?_⟩; simp [hk] <;> ring })

    -- 4. Density (from pre-sector incidence)
    have h4_cover : dyadicCoveringNumber δ (G_family y) = dyadicCoveringNumber δ G_y :=
      chartSector_grid_covering_preservation hδ_pos hG_y_grid
    have hB1_intgrid : B1_original ⊆ productLikeIntegerGrid δ := fun x hx => (hB1_grid_set hx).1
    have hB2_intgrid : B2_original ⊆ productLikeIntegerGrid δ := fun x hx => (hB2_grid_set hx).1
    have h_neg_eq1 : -B1_original = Set.image (fun x : ℝ => -x) B1_original := by
      ext y; simp only [Set.mem_neg, Set.mem_image]; constructor
      · intro h; exact ⟨-y, h, by ring⟩
      · rintro ⟨x, hx, rfl⟩; simpa using hx
    have h_neg_eq2 : -B2_original = Set.image (fun x : ℝ => -x) B2_original := by
      ext y; simp only [Set.mem_neg, Set.mem_image]; constructor
      · intro h; exact ⟨-y, h, by ring⟩
      · rintro ⟨x, hx, rfl⟩; simpa using hx
    have hN_product : Nreal δ B1 * Nreal δ B2 = Nreal δ B1_original * Nreal δ B2_original := by
      have h_refl1 : Nreal δ (-B1_original) = Nreal δ B1_original := by
        rw [h_neg_eq1]; exact nreal_reflection_eq hδ_pos hB1_intgrid hB1_bounded
      have h_refl2 : Nreal δ (-B2_original) = Nreal δ B2_original := by
        rw [h_neg_eq2]; exact nreal_reflection_eq hδ_pos hB2_intgrid hB2_bounded
      fin_cases i
      · simp [B1, B2, sectorRingBaseSet, sectorCoordSet]
      · simp [B1, B2, sectorRingBaseSet, sectorCoordSet, mul_comm]
      · simp [B1, B2, sectorRingBaseSet, sectorCoordSet, h_refl1]
      · simp [B1, B2, sectorRingBaseSet, sectorCoordSet, h_refl2, mul_comm]
    have h4 : ENat.toENNReal (dyadicCoveringNumber δ (G_family y)) ≥
        ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2 := by
      rw [h4_cover]
      have h_rhs : ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2 =
          ENNReal.ofReal c_proj * Nreal δ B1_original * Nreal δ B2_original := by
        calc ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2
          = ENNReal.ofReal c_proj * (Nreal δ B1 * Nreal δ B2) := by rw [mul_assoc]
        _ = ENNReal.ofReal c_proj * (Nreal δ B1_original * Nreal δ B2_original) := by rw [hN_product]
        _ = ENNReal.ofReal c_proj * Nreal δ B1_original * Nreal δ B2_original := by rw [mul_assoc]
      rw [h_rhs]
      exact hG_density_pre y hy

    -- 5. Projection bound (DIRECT from hPostProjectionSmall — no S_pre factoring!)
    have h_sec_eq : FourSectorChart.chartSectorT i (x y) = sector_chart y := by
      simp [sector_chart, sectorTMap, FourSectorChart.chartSectorT] <;> fin_cases i <;> rfl
    have h5 : ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D (sector_chart y) (G_family y))) <
        (1 / 2 : ENNReal) * ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
          ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ B2 := by
      rw [←h_sec_eq]
      exact hPostProjectionSmall y hy

    exact ⟨h1, h2, h3, h4, h5⟩

  -- ========================================================================
  -- Step 6: fixed_sector_graph_witness
  -- ========================================================================
  have h_graph_witness := fixed_sector_graph_witness
    (G_family := G_family)
    (hG_family := hG_family)
    (h_reverse_support := h_reverse_support)

  -- ========================================================================
  -- Step 7: sector_ring_lemma51_wrapper
  -- ========================================================================
  have hB1_bdd : IsBounded B1 := by
    fin_cases i <;> simp (config := {decide := true}) [B1, sectorRingBaseSet] <;>
      (try { exact hB2_bounded }) <;> (try { exact hB1_bounded }) <;>
      (try { exact IsBounded.neg hB1_bounded }) <;> (try { exact IsBounded.neg hB2_bounded })
  have hB2_bdd : IsBounded B2 := by
    fin_cases i <;> simp (config := {decide := true}) [B2, sectorCoordSet] <;>
      (try { exact hB1_bounded }) <;> (try { exact hB2_bounded })
  have hB1_nonempty' : B1.Nonempty := by
    fin_cases i <;> simp (config := {decide := true}) [B1, sectorRingBaseSet] <;>
      (try { exact hB2_nonempty }) <;> (try { exact hB1_nonempty }) <;>
      (try { exact hB2_nonempty.image _ }) <;> (try { exact hB1_nonempty.image _ })
  have hB2_nonempty' : B2.Nonempty := by
    fin_cases i <;> simp (config := {decide := true}) [B2, sectorCoordSet] <;>
      (try { exact hB1_nonempty }) <;> (try { exact hB2_nonempty })
  let j : Fin 4 := match i with
    | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2
  have hB1_eq_j : B1 = sectorRingBaseSet j B1_original B2_original := by
    fin_cases i <;> simp [B1, sectorRingBaseSet] <;> rfl
  have hB2_eq_j : B2 = sectorCoordSet j B1_original B2_original := by
    fin_cases i <;> simp [B2, sectorCoordSet] <;> rfl

  have hB1_grid : ∀ b ∈ B1, ∃ k : ℤ, b = δ * (k : ℝ) := by
    intro b hb
    fin_cases i
    · simp only [B1, sectorRingBaseSet] at hb; exact (hB1_grid_set hb).1
    · simp only [B1, sectorRingBaseSet] at hb; exact (hB2_grid_set hb).1
    · simp only [B1, sectorRingBaseSet, Set.mem_image] at hb
      rcases hb with ⟨x, hx, rfl⟩
      rcases (hB1_grid_set hx).1 with ⟨k, hk⟩
      refine ⟨-k, ?_⟩; simp [hk]
    · simp only [B1, sectorRingBaseSet, Set.mem_image] at hb
      rcases hb with ⟨x, hx, rfl⟩
      rcases (hB2_grid_set hx).1 with ⟨k, hk⟩
      refine ⟨-k, ?_⟩; simp [hk]
  have hB2_grid : ∀ b ∈ B2, ∃ k : ℤ, b = δ * (k : ℝ) := by
    intro b hb
    fin_cases i
    · simp only [B2, sectorCoordSet] at hb; exact (hB2_grid_set hb).1
    · simp only [B2, sectorCoordSet] at hb; exact (hB1_grid_set hb).1
    · simp only [B2, sectorCoordSet] at hb; exact (hB2_grid_set hb).1
    · simp only [B2, sectorCoordSet] at hb; exact (hB1_grid_set hb).1

  exact sector_ring_lemma51_wrapper
    (q_A := q_size + η)
    (hδ_pos := hδ_pos)
    (hδ_dyadic := hδ_dyadic)
    (hδ_le_one := by linarith)
    (hs_pos := hs_pos) (hs_lt_one := hs_lt_one)
    (hτ_pos := hτ_pos)
    (hκ0_pos := hkappa_pos) (hκ0_lt_s := hκ0_lt_s)
    (hκ0_le_tau := hκ0_le_tau)
    (hη_pos := hη_pos)
    (q_graph := q_graph_total)
    (h_q_graph_nonneg := h_q_graph_total_nonneg)
    (h_q_diff_nonneg := h_q_diff_nonneg)
    (h_q_A_nonneg := by linarith [h_q_size_nonneg, hη_pos])
    (hζ_dir_nonneg := hζ_dir_nonneg)
    (hη_proj_nonneg := hη_proj_nonneg)
    (h_budget := by simpa [add_assoc] using h_budget)
    (hK_work_ge1 := hK_work_ge1)
    (h_ring_spec := h_ring_spec)
    (hB1_bdd := hB1_bdd)
    (hB2_bdd := hB2_bdd)
    (hB1_nonempty := hB1_nonempty')
    (hB2_nonempty := hB2_nonempty')
    (c := sectorShift i)
    (hA_range := by
      have hB1_def : B1 = sectorRingBaseSet i B2_original B1_original := by rfl
      rw [hB1_def]
      exact sector_translate_subset hB2_grid_set hB1_grid_set i)
    (hB1_grid := hB1_grid)
    (hB2_grid := hB2_grid)
    (hc_proj_pos := hc_proj_pos)
    (hK_BSG_pos := hK_BSG_pos)
    (h_diff1 := by rw [hB1_eq_j]; exact h_diff1_sector j)
    (h_diff2 := by rw [hB2_eq_j, hB1_eq_j]; exact h_diff2_sector j)
    (h_size_upper := by rw [hB1_eq_j]; exact h_size_upper_sector j)
    (hB1_delta_kappa := by rw [hB1_eq_j]; exact hB1_delta_kappa_sector j)
    (hν_frost := hν_dir_frost)
    (h_graph_witness := h_graph_witness)

end ProductLikeIncidence.ProductReduction
