module

/-
# Sector Setup Helper for Phase7FullIntegrationV2

Extracts Steps 2-5 (four-sector pigeonhole through sector data) from V2
to reduce per-elaboration memory.

Returns the exact outputs of four_sector_pigeonhole plus chart co-Lipschitz
and sector ring/coordinate properties.
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeIncidence.Phase8SectorTranslation
public import MyLeanRepo.ProductLikeIncidence.SectorChartGridHelpers
public import MyLeanRepo.ProductLikeIncidence.FourSectorChart
public import MyLeanRepo.ProductLikeIncidence.Phase7ChartBounds
public import MyLeanRepo.FourSectorSelection
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set ENNReal Bornology MeasureTheory Classical


namespace ProductLikeIncidence.ProductReduction

/-- Sector setup: four-sector pigeonhole + chart co-Lipschitz + sector data.

Given Θ_bad from double counting and all B1/B2 properties, produces:
- Selected sector i, Θ_sec, pole-removal radius r
- Sector predicate and chart properties
- Dense fiber density on Θ_sec
- Chart co-Lipschitz bound
- Sector ring/coordinate difference, size, and delta-set properties -/
lemma phase7_sector_setup_helper
    {δ s τ κ0 ε_mass εnc : ℝ}
    {Y Θ_bad : Set ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hδ_dyadic : δ ∈ dyadicScales)
    (hτ_pos : 0 < τ)
    (hε_mass_pos : 0 < ε_mass)
    (C_ν : ℝ)
    (hC_ν_pos : 0 < C_ν)
    (hν_frost : IsDirectionFrostman δ τ C_ν ν)
    (hY_sub_unit : Y ⊆ Set.Icc 0 1)
    (hY_fin : Y.Finite)
    (h_sector_absorb : C_ν * δ ^ τ ≤ δ ^ ε_mass / 2)
    (h_Θbad_mass : ν Θ_bad ≥ ENNReal.ofReal (δ ^ ε_mass))
    (hΘ_bad_sub_Y : Θ_bad ⊆ Y)
    (θ1 θ2 θ3 : ℝ)
    (q_pole : ℝ)
    (hθ1_in_Icc : θ1 ∈ Set.Icc 0 1)
    (hθ2_in_Icc : θ2 ∈ Set.Icc 0 1)
    (h_ord13 : θ1 < θ3)
    (h_ord32 : θ3 < θ2)
    (h_sep13 : |θ1 - θ3| ≥ δ ^ q_pole)
    (h_sep23 : |θ2 - θ3| ≥ δ ^ q_pole)
    (hq_pole_pos : 0 < q_pole)
    (L_chart : ℝ)
    (hL_chart_ge : L_chart ≥ δ ^ (-2 * q_pole))
    (x : ℝ → ℝ)
    (hx_formula : ∀ y, x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y)))
    {F_graph : Set (EuclideanSpace ℝ (Fin 2))}
    {S_pre : ℝ → Set ℝ}
    (c_proj : ℝ)
    {B1 B2 : Set ℝ}
    (hB1_grid_set : B1 ⊆ productLikeUnitGrid δ)
    (hB2_grid_set : B2 ⊆ productLikeUnitGrid δ)
    (hB1_bounded : IsBounded B1)
    (hB2_bounded : IsBounded B2)
    {C_B1 C_B2 : ℝ}
    (hB1_delta_kappa : IsProductLikeRealDeltaSCSet δ κ0 C_B1 B1)
    (hB2_delta_kappa : IsProductLikeRealDeltaSCSet δ κ0 C_B2 B2)
    {K_BSG K_work : ℝ}
    (hK_work_pos : 0 < K_work)
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
    (hG_density : ∀ y ∈ Θ_bad,
      ENat.toENNReal (dyadicCoveringNumber δ
        (F_graph ∩ {p | p 0 * x y + p 1 ∈ S_pre y})) ≥
      ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2) :
    ∃ (r : ℝ) (i : Fin 4) (Θ_sec : Set ℝ),
      0 < r ∧ δ ≤ r ∧ r ^ τ = δ ^ ε_mass / (2 * C_ν) ∧
      Θ_sec ⊆ Θ_bad \ Metric.ball θ2 r ∧
      Set.Finite Θ_sec ∧
      IsClosed Θ_sec ∧
      (ν Θ_sec ≥ (1 / 8 : ENNReal) * ν Θ_bad) ∧
      (∀ y ∈ Θ_sec, sectorPredicate i x y) ∧
      (∀ y ∈ Θ_sec, sectorTMap i (x y) ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ y ∈ Θ_sec, ∀ (U V : ℝ),
        sectorTMap i (x y) * (sectorCoordMap i U V).1 + (sectorCoordMap i U V).2 =
        if i = 0 ∨ i = 2 then U + x y * V else (1 / (x y)) * (U + x y * V)) ∧
      (Θ_sec ⊆ Y) ∧
      (∀ y ∈ Θ_sec,
        ENat.toENNReal (dyadicCoveringNumber δ
          (F_graph ∩ {p | p 0 * x y + p 1 ∈ S_pre y})) ≥
        ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2) ∧
      (∀ y ∈ Θ_sec, ∀ z ∈ Θ_sec, y ≠ θ2 → z ≠ θ2 →
        |y - z| ≤ L_chart * |sectorTMap i (x y) - sectorTMap i (x z)|) ∧
      (∀ i : Fin 4, Nreal δ (Set.image2 (· - ·) (sectorRingBaseSet i B1 B2) (sectorRingBaseSet i B1 B2)) ≤
        ENNReal.ofReal K_BSG * Nreal δ (sectorRingBaseSet i B1 B2)) ∧
      (∀ i : Fin 4, Nreal δ (Set.image2 (· - ·) (sectorCoordSet i B1 B2) (sectorRingBaseSet i B1 B2)) ≤
        ENNReal.ofReal K_BSG * Nreal δ (sectorRingBaseSet i B1 B2)) ∧
      (∀ i : Fin 4, Nreal δ (sectorRingBaseSet i B1 B2) ≤
        ENNReal.ofReal (K_work * δ ^ (-(s + εnc)))) ∧
      (∀ i : Fin 4, IsProductLikeRealDeltaSCSet δ κ0 (K_work * δ ^ (-εnc)) (sectorRingBaseSet i B1 B2)) := by
  have hΘ_bad_sub : Θ_bad ⊆ Set.Icc 0 1 := subset_trans hΘ_bad_sub_Y hY_sub_unit
  have hΘ_bad_finite : Set.Finite Θ_bad := hY_fin.subset hΘ_bad_sub_Y
  haveI : Finite Θ_bad := hΘ_bad_finite

  -- Step 2: Four-sector pigeonhole
  have h_four_sector := four_sector_pigeonhole
    (hνY_frost := hν_frost)
    (hTheta_mass := h_Θbad_mass)
    (theta2 := θ2)
    (hδ_pos := hδ_pos)
    (hδ_lt_one := hδ_lt_one)
    (hκ0_pos := hτ_pos)
    (hC_Y_pos := hC_ν_pos)
    (hq_pos := hε_mass_pos)
    (h_absorb := h_sector_absorb)
    (x := x)
  rcases h_four_sector with ⟨r, hr_pos, hδ_le_r, h_r_pow, i, Θ_sec, hΘ_sec_sub,
    hΘ_sec_finite, hΘ_sec_closed, hΘ_sec_mass, h_sector, h_sector_range,
    h_sector_proj_id⟩

  have hΘ_sec_sub_bad : Θ_sec ⊆ Θ_bad := fun y hy => (hΘ_sec_sub hy).1
  have hΘ_sec_sub_Y : Θ_sec ⊆ Y := subset_trans hΘ_sec_sub_bad hΘ_bad_sub_Y

  -- Step 3: hG_density_pre (restrict to Θ_sec)
  have hG_density_pre : ∀ y ∈ Θ_sec,
      ENat.toENNReal (dyadicCoveringNumber δ
        (F_graph ∩ {p | p 0 * x y + p 1 ∈ S_pre y})) ≥
      ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2 := by
    intro y hy
    exact hG_density y (hΘ_sec_sub_bad hy)

  -- Step 4: Chart co-Lipschitz on Θ_sec
  have h_chart_colip_sec : ∀ y ∈ Θ_sec, ∀ z ∈ Θ_sec, y ≠ θ2 → z ≠ θ2 →
      |y - z| ≤ L_chart * |sectorTMap i (x y) - sectorTMap i (x z)| := by
    intro y hy z hz hyne hzne
    have h_y0 : 0 ≤ y := (hΘ_bad_sub (hΘ_sec_sub_bad hy)).1
    have h_y1 : y ≤ 1 := (hΘ_bad_sub (hΘ_sec_sub_bad hy)).2
    have h_z0 : 0 ≤ z := (hΘ_bad_sub (hΘ_sec_sub_bad hz)).1
    have h_z1 : z ≤ 1 := (hΘ_bad_sub (hΘ_sec_sub_bad hz)).2
    have h_sep13' : θ3 - θ1 ≥ δ ^ q_pole := by
      have h_neg : θ1 - θ3 < 0 := by linarith
      have h_abs : |θ1 - θ3| = θ3 - θ1 := by
        rw [abs_of_neg h_neg] <;> ring
      exact h_abs ▸ h_sep13
    have h_sep32' : θ2 - θ3 ≥ δ ^ q_pole := by
      have h_pos : 0 < θ2 - θ3 := by linarith
      have h_abs : |θ2 - θ3| = θ2 - θ3 := by
        rw [abs_of_pos h_pos]
      exact h_abs ▸ h_sep23
    have h_x_eq : x = crossRatioMap θ1 θ2 θ3 := by
      funext y0; exact hx_formula y0
    rw [h_x_eq] at h_sector ⊢
    have h_bound := sector_colipschitz
      (hδ_pos := hδ_pos) (hδ_le_one := hδ_lt_one.le)
      (h13 := h_ord13) (h23 := h_ord32)
      (hθ1_nonneg := hθ1_in_Icc.1) (hθ2_le_one := hθ2_in_Icc.2)
      (h_sep13 := h_sep13') (h_sep32 := h_sep32')
      (hrho_nonneg := by linarith)
      (hy_ne := hyne) (hz_ne := hzne)
      (hy0 := h_y0) (hy1 := h_y1) (hz0 := h_z0) (hz1 := h_z1)
      (h_sector_y := h_sector y hy) (h_sector_z := h_sector z hz)
    calc |y - z|
      ≤ δ^(-2*q_pole) * |sectorTMap i (crossRatioMap θ1 θ2 θ3 y) - sectorTMap i (crossRatioMap θ1 θ2 θ3 z)| := h_bound
    _ ≤ L_chart * |sectorTMap i (crossRatioMap θ1 θ2 θ3 y) - sectorTMap i (crossRatioMap θ1 θ2 θ3 z)| := by
      gcongr <;> linarith

  -- Step 5: Sector data
  have hB1_intgrid : B1 ⊆ productLikeIntegerGrid δ :=
    fun x hx => (hB1_grid_set hx).1
  have hB2_intgrid : B2 ⊆ productLikeIntegerGrid δ :=
    fun x hx => (hB2_grid_set hx).1

  have h_sum_comm : Set.image2 (· + ·) B2 B1 = Set.image2 (· + ·) B1 B2 := by
    ext z; simp [Set.mem_image2, add_comm] <;> constructor <;>
      rintro ⟨a, ha, b, hb, rfl⟩ <;> exact ⟨b, hb, a, ha, by ring⟩

  have h_diff1_sector : ∀ i : Fin 4,
      Nreal δ (Set.image2 (· - ·) (sectorRingBaseSet i B1 B2)
        (sectorRingBaseSet i B1 B2)) ≤
      ENNReal.ofReal K_BSG * Nreal δ (sectorRingBaseSet i B1 B2) := by
    intro i
    fin_cases i
    · dsimp only [sectorRingBaseSet]; exact h_diff_B2B2
    · dsimp only [sectorRingBaseSet]; exact h_diff_B1B1
    · dsimp only [sectorRingBaseSet]
      rw [neg_diff_eq hδ_pos hB2_intgrid hB2_bounded,
          nreal_reflection_eq hδ_pos hB2_intgrid hB2_bounded]
      exact h_diff_B2B2
    · dsimp only [sectorRingBaseSet]
      rw [neg_diff_eq hδ_pos hB1_intgrid hB1_bounded,
          nreal_reflection_eq hδ_pos hB1_intgrid hB1_bounded]
      exact h_diff_B1B1

  have h_diff2_sector : ∀ i : Fin 4,
      Nreal δ (Set.image2 (· - ·) (sectorCoordSet i B1 B2)
        (sectorRingBaseSet i B1 B2)) ≤
      ENNReal.ofReal K_BSG * Nreal δ (sectorRingBaseSet i B1 B2) := by
    intro i
    fin_cases i
    · dsimp only [sectorCoordSet, sectorRingBaseSet]; exact h_diff_B1B2
    · dsimp only [sectorCoordSet, sectorRingBaseSet]; exact h_diff_B2B1
    · dsimp only [sectorCoordSet, sectorRingBaseSet]
      rw [diff_neg_eq_add (S := B2) (T := B1),
          nreal_reflection_eq hδ_pos hB2_intgrid hB2_bounded]
      exact h_sum_B1B2_over_B2
    · dsimp only [sectorCoordSet, sectorRingBaseSet]
      rw [diff_neg_eq_add (S := B1) (T := B2), h_sum_comm,
          nreal_reflection_eq hδ_pos hB1_intgrid hB1_bounded]
      exact h_sum_B1B2_over_B1

  have h_size_upper_sector : ∀ i : Fin 4,
      Nreal δ (sectorRingBaseSet i B1 B2) ≤
      ENNReal.ofReal (K_work * δ ^ (-(s + εnc))) := by
    intro i
    fin_cases i
    · dsimp only [sectorRingBaseSet]; exact hB2_upper
    · dsimp only [sectorRingBaseSet]; exact hB1_upper
    · dsimp only [sectorRingBaseSet]
      rw [nreal_reflection_eq hδ_pos hB2_intgrid hB2_bounded]
      exact hB2_upper
    · dsimp only [sectorRingBaseSet]
      rw [nreal_reflection_eq hδ_pos hB1_intgrid hB1_bounded]
      exact hB1_upper

  have hB1_delta_kappa_sector : ∀ i : Fin 4,
      IsProductLikeRealDeltaSCSet δ κ0 (K_work * δ ^ (-εnc))
        (sectorRingBaseSet i B1 B2) := by
    intro i
    fin_cases i
    · simp only [sectorRingBaseSet]
      have hC2_pos' : 0 < C_B2 := hB2_delta_kappa.2.2.2.2.2.2.2.1
      have h_C_le : C_B2 ≤ K_work * δ ^ (-εnc) := by
        have h_pos : 0 < K_work * δ ^ (-εnc) := by positivity
        have h : C_B2 ≤ 2 * C_B2 := by linarith
        linarith [hC2_absorb]
      exact IsDeltaSCSet.mono hB2_delta_kappa h_C_le
    · simp only [sectorRingBaseSet]
      have hC1_pos' : 0 < C_B1 := hB1_delta_kappa.2.2.2.2.2.2.2.1
      have h_C_le : C_B1 ≤ K_work * δ ^ (-εnc) := by
        have h_pos : 0 < K_work * δ ^ (-εnc) := by positivity
        have h : C_B1 ≤ 2 * C_B1 := by linarith
        linarith [hC1_absorb]
      exact IsDeltaSCSet.mono hB1_delta_kappa h_C_le
    · simp only [sectorRingBaseSet]
      have h_r : IsProductLikeRealDeltaSCSet δ κ0 (2 * C_B2) ((fun x : ℝ => -x) '' B2) :=
        isProductLikeRealDeltaSCSet_reflect hδ_dyadic hδ_pos hB2_grid_set hB2_delta_kappa
      exact IsDeltaSCSet.mono h_r hC2_absorb
    · simp only [sectorRingBaseSet]
      have h_r : IsProductLikeRealDeltaSCSet δ κ0 (2 * C_B1) ((fun x : ℝ => -x) '' B1) :=
        isProductLikeRealDeltaSCSet_reflect hδ_dyadic hδ_pos hB1_grid_set hB1_delta_kappa
      exact IsDeltaSCSet.mono h_r hC1_absorb

  exact ⟨r, i, Θ_sec, hr_pos, hδ_le_r, h_r_pow, hΘ_sec_sub,
    hΘ_sec_finite, hΘ_sec_closed, hΘ_sec_mass,
    h_sector, h_sector_range, h_sector_proj_id,
    hΘ_sec_sub_Y, hG_density_pre, h_chart_colip_sec,
    h_diff1_sector, h_diff2_sector, h_size_upper_sector, hB1_delta_kappa_sector⟩

end ProductLikeIncidence.ProductReduction
