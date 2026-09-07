module

/-
# Direction Failure Composition v6 (four-sector-first)

Correct pipeline:
1. four_sector_pigeonhole on Θ_bad → sector i, Θ_sec (mass ≥ δ^ε/8)
2. sector_chart(y) = sectorTMap i (x(y))
3. ν_dir = normalize(map sector_chart (ν.restrict Θ_sec))
4. Graph witness via sector point transform
5. sector_ring_lemma51_wrapper → False

## Whiteprint node: DirectionFailureComposition
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.Compat
public import MyLeanRepo.ProductLikeIncidence.DirectionTransportProjectiveLine
public import MyLeanRepo.ProductLikeIncidence.SectorRingLemma51Wrapper
public import MyLeanRepo.ProductLikeIncidence.Phase8SectorTranslation
public import MyLeanRepo.ProductLikeIncidence.FourSectorChart
public import MyLeanRepo.ProductLikeIncidence.SectorChartGridHelpers
public import MyLeanRepo.FourSectorSelection
public import MyLeanRepo.OSWPrelude

@[expose] public section

open Set ENNReal Bornology MeasureTheory Classical

noncomputable section

namespace ProductLikeIncidence.ProductReduction

/-- The sector-dependent projection factor for the graph witness bound. -/
def sectorFactorENNReal (i : Fin 4) : ENNReal :=
  match i with
  | 0 => 1 / 2
  | 1 => 1 / 4
  | 2 => 1 / 2
  | 3 => 1 / 4

/-- Direct Frostman transport: normalize a pushforward measure without pole removal.
    Given ν Frostman with exponent τ, Θ_sec with mass ≥ δ^ε/8, and f_dir
    Lipschitz/co-Lipschitz, the normalized pushforward is Frostman with
    exponent κ0 and constant K_work * δ^{-εnc}. -/
lemma direct_frostman_transport
    {δ τ κ0 ε εnc C_ν L_chart K_work : ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν_frost : IsDirectionFrostman δ τ C_ν ν)
    {Θ_sec : Set ℝ} (hΘ_sec_finite : Set.Finite Θ_sec)
    (hΘ_sec_pos : 0 < ν Θ_sec) (hΘ_sec_ne_top : ν Θ_sec ≠ ⊤)
    (hΘ_sec_mass_ge : ν Θ_sec ≥ ENNReal.ofReal ((1 / 8 : ℝ) * δ ^ ε))
    {y1 : ℝ} (h_pole_avoid : ∀ y ∈ Θ_sec, y ≠ y1)
    {f_dir : ℝ → ℝ}
    (h_f_dir_meas : Measurable f_dir)
    (h_f_dir_colip : ∀ y ∈ Θ_sec, ∀ z ∈ Θ_sec, y ≠ y1 → z ≠ y1 →
      |y - z| ≤ L_chart * |f_dir y - f_dir z|)
    (h_f_dir_range : ∀ y ∈ Θ_sec, f_dir y ∈ Set.Icc (0 : ℝ) 1)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hτ_pos : 0 < τ) (hkappa_pos : 0 < κ0) (hκ0_le_tau : κ0 ≤ τ)
    (hε_pos : 0 < ε) (hC_ν_pos : 0 < C_ν)
    (hL_chart_pos : 0 < L_chart) (hL_chart_ge_one : 1 ≤ L_chart)
    (hK_work_ge1 : 1 ≤ K_work)
    (h_frostman_budget : C_ν * (8 : ℝ) * δ ^ (-ε) * L_chart ^ τ ≤ K_work * δ ^ (-εnc)) :
    IsProbabilityMeasure ((ν Θ_sec)⁻¹ • Measure.map f_dir (ν.restrict Θ_sec)) ∧
    IsDirectionFrostman δ κ0 (K_work * δ ^ (-εnc))
      ((ν Θ_sec)⁻¹ • Measure.map f_dir (ν.restrict Θ_sec)) := by
  let ν_dir := (ν Θ_sec)⁻¹ • Measure.map f_dir (ν.restrict Θ_sec)
  -- Probability
  have h_prob : IsProbabilityMeasure ν_dir := by
    have h_map_univ : (Measure.map f_dir (ν.restrict Θ_sec)) Set.univ = ν Θ_sec := by
      rw [Measure.map_apply h_f_dir_meas MeasurableSet.univ] <;> simp
    refine' ⟨_⟩
    have h : ν_dir Set.univ = (ν Θ_sec)⁻¹ * (Measure.map f_dir (ν.restrict Θ_sec)) Set.univ := by
      simp [ν_dir] <;> rfl
    rw [h, h_map_univ]
    exact ENNReal.inv_mul_cancel hΘ_sec_pos.ne' hΘ_sec_ne_top
  -- Extract Frostman
  have hν_univ : ν Set.univ = 1 := hν_frost.1
  have hν_supp : ν.support ⊆ Set.Icc (0 : ℝ) 1 := hν_frost.2.1
  have hν_reg : ∀ (a r : ℝ), δ ≤ r → r ≤ 1 →
      ν (Set.Icc (a - r) (a + r)) ≤ ENNReal.ofReal (C_ν * r ^ τ) := hν_frost.2.2
  have hC_ν_ge1 : 1 ≤ C_ν := by
    have h4 : ν (Set.Icc ((1 / 2 : ℝ) - 1) ((1 / 2 : ℝ) + 1)) ≤
        ENNReal.ofReal (C_ν * (1 : ℝ) ^ τ) := hν_reg (1 / 2) 1 (by linarith) (by norm_num)
    have h5 : Set.Icc (0 : ℝ) 1 ⊆ Set.Icc ((1 / 2 : ℝ) - 1) ((1 / 2 : ℝ) + 1) := by
      intro x hx; have hxl : 0 ≤ x := hx.1; have hxr : x ≤ 1 := hx.2
      constructor <;> norm_num <;> linarith
    have h_supp_compl_null : ν (ν.supportᶜ) = 0 := MeasureTheory.Measure.measure_compl_support (μ := ν)
    have h_Icc_compl_null : ν ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 :=
      measure_mono_null (compl_subset_compl.mpr hν_supp) h_supp_compl_null
    have h_Icc_eq_univ : ν (Set.Icc (0 : ℝ) 1) = ν Set.univ := by
      have h1 : ν ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 := h_Icc_compl_null
      have h2 : ν ((Set.Icc (0 : ℝ) 1)ᶜ) = ν Set.univ - ν (Set.Icc (0 : ℝ) 1) :=
        MeasureTheory.measure_compl isClosed_Icc.measurableSet (by simp)
      have h3 : ν Set.univ - ν (Set.Icc (0 : ℝ) 1) = 0 := by rw [← h2, h1]
      have h4 : ν Set.univ ≤ ν (Set.Icc (0 : ℝ) 1) := tsub_eq_zero_iff_le.mp h3
      have h5 : ν (Set.Icc (0 : ℝ) 1) ≤ ν Set.univ := measure_mono (Set.subset_univ _)
      exact le_antisymm h5 h4
    have h6 : ν (Set.Icc (0 : ℝ) 1) = 1 := by rw [h_Icc_eq_univ, hν_univ]
    have h9 : ν (Set.Icc ((1 / 2 : ℝ) - 1) ((1 / 2 : ℝ) + 1)) ≥ 1 := by
      calc _ ≥ ν (Set.Icc (0 : ℝ) 1) := measure_mono h5
           _ = 1 := h6
    have h10 : (1 : ENNReal) ≤ ENNReal.ofReal (C_ν * (1 : ℝ) ^ τ) := le_trans h9 h4
    simpa using h10
  -- Normalization factor ≤ 8·δ^{-ε}
  have h_norm_factor : (ν Θ_sec)⁻¹ ≤ ENNReal.ofReal ((8 : ℝ) * δ ^ (-ε)) := by
    have h3 : ν Θ_sec ≥ ENNReal.ofReal ((1 / 8 : ℝ) * δ ^ ε) := hΘ_sec_mass_ge
    have h4 : (ν Θ_sec)⁻¹ ≤ (ENNReal.ofReal ((1 / 8 : ℝ) * δ ^ ε))⁻¹ := by gcongr
    have h5 : ((1 / 8 : ℝ) * δ ^ ε)⁻¹ = (8 : ℝ) * δ ^ (-ε) := by
      have h_pos : 0 < (1 / 8 : ℝ) * δ ^ ε := by positivity
      field_simp [h_pos.ne']
      have h_eq : δ ^ ε * δ ^ (-ε) = 1 := by
        rw [← Real.rpow_add hδ_pos] <;> ring_nf <;> norm_num
      linarith
    have h6 : (ENNReal.ofReal ((1 / 8 : ℝ) * δ ^ ε))⁻¹ =
        ENNReal.ofReal (((1 / 8 : ℝ) * δ ^ ε)⁻¹) := by
      exact (ENNReal.ofReal_inv_of_pos (x := (1 / 8 : ℝ) * δ ^ ε) (by positivity)).symm
    rw [h6, h5] at h4
    exact h4
  set C_frost : ℝ := C_ν * ((8 : ℝ) * δ ^ (-ε) * L_chart ^ τ) with hC_frost_def
  -- Frostman with midpoint trick
  have h_frost : ∀ (x : ℝ) (r : ℝ), δ ≤ r → r ≤ 1 →
      ν_dir (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (C_frost * r ^ τ) := by
    intro x r hrδ hr1
    let I := Set.Icc (x - r) (x + r)
    let S := Θ_sec ∩ f_dir ⁻¹' I
    have hr_pos : 0 < r := by linarith
    have h_measI : MeasurableSet I := measurableSet_Icc
    have h_eq : ν_dir I = (ν Θ_sec)⁻¹ * ν S := by
      have h1 : (Measure.map f_dir (ν.restrict Θ_sec)) I = (ν.restrict Θ_sec) (f_dir ⁻¹' I) := by
        rw [Measure.map_apply h_f_dir_meas h_measI]
      have h2 : (ν.restrict Θ_sec) (f_dir ⁻¹' I) = ν S := by
        have h_set : f_dir ⁻¹' I ∩ Θ_sec = S := by ext z; simp [S, and_comm]
        rw [Measure.restrict_apply (h_measI.preimage h_f_dir_meas), h_set]
      have h3 : ν_dir I = (ν Θ_sec)⁻¹ * (Measure.map f_dir (ν.restrict Θ_sec)) I := by
        simp [ν_dir] <;> rfl
      rw [h3, h1, h2]
    rw [h_eq]
    by_cases hS : S = ∅
    · rw [hS]; simp
    · rcases Set.nonempty_iff_ne_empty.mpr hS with ⟨y0, hy0⟩
      have h_y0_in : y0 ∈ Θ_sec := hy0.1
      have h_y0_ne : y0 ≠ y1 := h_pole_avoid y0 h_y0_in
      have h_diam : ∀ y ∈ S, ∀ z ∈ S, |y - z| ≤ 2 * L_chart * r := by
        intro y hy z hz
        have h_y_in : y ∈ Θ_sec := hy.1
        have h_z_in : z ∈ Θ_sec := hz.1
        have h_y_ne : y ≠ y1 := h_pole_avoid y h_y_in
        have h_z_ne : z ≠ y1 := h_pole_avoid z h_z_in
        have h1 : f_dir y ∈ I := hy.2
        have h2 : f_dir z ∈ I := hz.2
        have h3 : |f_dir y - f_dir z| ≤ 2 * r := by
          rw [abs_le] <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
        have h4 := h_f_dir_colip y h_y_in z h_z_in h_y_ne h_z_ne
        calc |y - z| ≤ L_chart * |f_dir y - f_dir z| := h4
          _ ≤ L_chart * (2 * r) := by gcongr
          _ = 2 * L_chart * r := by ring
      have h_bounded : BddAbove S ∧ BddBelow S := by
        have h1 : ∀ y ∈ S, |y - y0| ≤ 2 * L_chart * r := fun y hy => h_diam y hy y0 hy0
        constructor
        · use y0 + 2 * L_chart * r; intro y hy; have h2 := h1 y hy; linarith [abs_le.mp h2]
        · use y0 - 2 * L_chart * r; intro y hy; have h2 := h1 y hy; linarith [abs_le.mp h2]
      have hS' : Set.Nonempty S := Set.nonempty_iff_ne_empty.mpr hS
      let a : ℝ := sInf S
      let b : ℝ := sSup S
      have ha_le : ∀ y ∈ S, a ≤ y := fun y hy => csInf_le h_bounded.2 hy
      have h_le_b : ∀ y ∈ S, y ≤ b := fun y hy => le_csSup h_bounded.1 hy
      have h_span : b - a ≤ 2 * L_chart * r := by
        have h1 : ∀ z ∈ S, b ≤ z + 2 * L_chart * r := by
          intro z hz
          have h2 : ∀ y ∈ S, y ≤ z + 2 * L_chart * r := by
            intro y hy
            have h3 : |y - z| ≤ 2 * L_chart * r := h_diam y hy z hz
            have h4 : y - z ≤ 2 * L_chart * r := by linarith [abs_le.mp h3]
            linarith
          exact csSup_le hS' h2
        have h3 : ∀ z ∈ S, b - 2 * L_chart * r ≤ z := by intro z hz; linarith [h1 z hz]
        have h4 : b - 2 * L_chart * r ≤ a := le_csInf hS' h3
        linarith
      let c : ℝ := (a + b) / 2
      let R : ℝ := L_chart * r
      have h_S_sub : S ⊆ Set.Icc (c - R) (c + R) := by
        intro y hy
        have h6 : a ≤ y := ha_le y hy
        have h7 : y ≤ b := h_le_b y hy
        have h8 : y - c ≤ (b - a) / 2 := by dsimp only [c]; linarith
        have h9 : c - y ≤ (b - a) / 2 := by dsimp only [c]; linarith
        have h10 : (b - a) / 2 ≤ R := by dsimp only [R]; linarith [h_span]
        constructor <;> linarith
      have hR_pos : 0 < R := by positivity
      have hR_ge_delta : δ ≤ R := by
        have h1 : δ ≤ r := hrδ
        have h2 : 1 ≤ L_chart := hL_chart_ge_one
        nlinarith
      by_cases h_large : R > 1
      · have h5 : ν S ≤ 1 := by
          have h6 : ν S ≤ ν Set.univ := measure_mono (Set.subset_univ _)
          rw [hν_univ] at h6; exact h6
        have h6 : 1 ≤ C_ν * R ^ τ := by
          have h7 : 1 < R := h_large
          have h8 : 1 < R ^ τ := Real.one_lt_rpow h7 hτ_pos
          have h9 : 1 ≤ C_ν := hC_ν_ge1
          nlinarith
        have h12 : R ^ τ = L_chart ^ τ * r ^ τ := by
          have h13 : R = L_chart * r := rfl
          rw [h13]; exact Real.mul_rpow (by linarith) (by linarith)
        have h14 : 1 ≤ C_ν * L_chart ^ τ * r ^ τ := by
          have h15 : C_ν * R ^ τ = C_ν * L_chart ^ τ * r ^ τ := by
            rw [h12] <;> ring
          rw [h15] at h6
          exact h6
        calc (ν Θ_sec)⁻¹ * ν S
        ≤ ENNReal.ofReal ((8 : ℝ) * δ ^ (-ε)) * 1 := by gcongr
        _ = ENNReal.ofReal ((8 : ℝ) * δ ^ (-ε)) := by simp
        _ ≤ ENNReal.ofReal (C_frost * r ^ τ) := by
          have h11 : C_frost * r ^ τ = (8 : ℝ) * δ ^ (-ε) * (C_ν * L_chart ^ τ * r ^ τ) := by
            rw [hC_frost_def] <;> ring
          rw [h11]
          have h16 : 0 ≤ (8 : ℝ) * δ ^ (-ε) := by positivity
          have h17 : (8 : ℝ) * δ ^ (-ε) ≤ (8 : ℝ) * δ ^ (-ε) * (C_ν * L_chart ^ τ * r ^ τ) :=
            le_mul_of_one_le_right h16 h14
          exact ENNReal.ofReal_le_ofReal h17
      · have h_small : R ≤ 1 := by linarith
        have h_frost_S : ν S ≤ ENNReal.ofReal (C_ν * R ^ τ) :=
          calc ν S ≤ ν (Set.Icc (c - R) (c + R)) := measure_mono h_S_sub
               _ ≤ ENNReal.ofReal (C_ν * R ^ τ) := hν_reg c R hR_ge_delta h_small
        have h_R_pow : R ^ τ = L_chart ^ τ * r ^ τ := by
          have h1 : R = L_chart * r := rfl
          rw [h1]; exact Real.mul_rpow (by linarith) (by linarith)
        have h_final : (8 : ℝ) * δ ^ (-ε) * (C_ν * R ^ τ) ≤ C_frost * r ^ τ := by
          have h_eq : (8 : ℝ) * δ ^ (-ε) * (C_ν * R ^ τ) = C_frost * r ^ τ := by
            have h2 : R ^ τ = L_chart ^ τ * r ^ τ := h_R_pow
            simp only [hC_frost_def, h2] <;> ring
          exact le_of_eq h_eq
        calc (ν Θ_sec)⁻¹ * ν S
        ≤ ENNReal.ofReal ((8 : ℝ) * δ ^ (-ε)) * ENNReal.ofReal (C_ν * R ^ τ) := by gcongr
        _ = ENNReal.ofReal ((8 : ℝ) * δ ^ (-ε) * (C_ν * R ^ τ)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal (C_frost * r ^ τ) := by exact ENNReal.ofReal_le_ofReal h_final
  -- Weaken exponent τ → κ0
  have h_frost_kappa : ∀ (x : ℝ) (r : ℝ), δ ≤ r → r ≤ 1 →
      ν_dir (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal ((K_work * δ ^ (-εnc)) * r ^ κ0) := by
    intro x r hrδ hr1
    have h1 : ν_dir (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (C_frost * r ^ τ) :=
      h_frost x r hrδ hr1
    have h2 : r ^ τ ≤ r ^ κ0 := by
      have h3 : 0 < r := by linarith
      have h4 : r ≤ 1 := hr1
      have h5 : κ0 ≤ τ := hκ0_le_tau
      have h6 : Real.log r ≤ 0 := by
        have h61 : 0 < r := h3
        have h62 : r ≤ 1 := h4
        have h : Real.log r ≤ Real.log 1 := Real.log_le_log (by linarith) (by linarith)
        simpa using h
      have h7 : τ * Real.log r ≤ κ0 * Real.log r := by nlinarith
      have h8 : Real.log (r ^ τ) ≤ Real.log (r ^ κ0) := by
        rw [Real.log_rpow h3, Real.log_rpow h3] <;> linarith
      exact Real.log_le_log_iff (by positivity) (by positivity) |>.mp h8
    have h_Cfrost_le : C_frost ≤ K_work * δ ^ (-εnc) := by
      have h51 : C_frost = C_ν * (8 : ℝ) * δ ^ (-ε) * L_chart ^ τ := by
        simp [hC_frost_def] <;> ring
      rw [h51]
      exact h_frostman_budget
    have h_pos1 : 0 ≤ C_frost := by positivity
    have h_pos2 : 0 ≤ r ^ κ0 := Real.rpow_nonneg (by linarith) κ0
    have h6 : C_frost * r ^ τ ≤ (K_work * δ ^ (-εnc)) * r ^ κ0 := by
      calc C_frost * r ^ τ ≤ C_frost * r ^ κ0 := mul_le_mul_of_nonneg_left h2 h_pos1
           _ ≤ (K_work * δ ^ (-εnc)) * r ^ κ0 := mul_le_mul_of_nonneg_right h_Cfrost_le h_pos2
    exact le_trans h1 (ENNReal.ofReal_le_ofReal h6)
  -- Support ⊆ [0,1]
  let Image := f_dir '' Θ_sec
  have h_image_finite : Set.Finite Image := hΘ_sec_finite.image _
  have h_image_closed : IsClosed Image := h_image_finite.isClosed
  have h_image_sub : Image ⊆ Set.Icc (0 : ℝ) 1 := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    exact h_f_dir_range y hy
  have h_dir_null : ν_dir Imageᶜ = 0 := by
    have h1 : (Measure.map f_dir (ν.restrict Θ_sec)) Imageᶜ = 0 := by
      rw [Measure.map_apply h_f_dir_meas h_image_closed.isOpen_compl.measurableSet]
      have h7 : f_dir ⁻¹' Imageᶜ ∩ Θ_sec = ∅ := by
        ext z; simp [Image]; tauto
      rw [Measure.restrict_apply (h_image_closed.isOpen_compl.measurableSet.preimage h_f_dir_meas), h7] <;> simp
    simp [ν_dir, h1] <;> simp
  have h_supp_dir : ν_dir.support ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    by_contra h
    have h5 : x ∈ Imageᶜ := by
      intro h52
      exact h (h_image_sub h52)
    have h6 : IsOpen Imageᶜ := h_image_closed.isOpen_compl
    have h7 : 0 < ν_dir Imageᶜ := by
      rw [Measure.mem_support_iff_forall] at hx
      exact hx Imageᶜ (h6.mem_nhds h5)
    rw [h_dir_null] at h7
    exact False.elim (lt_irrefl 0 h7)
  exact ⟨h_prob, ⟨h_prob.1, h_supp_dir, h_frost_kappa⟩⟩

/-- Budget absorption lemma for direction failure projection bound.

Given `δ^D ≤ 1/64` where `D = εgain - (q_graph_total + 2*q_diff + q_A + q_size + ζ_dir + η_proj)`,
and `factor ≥ 1/4`, proves:
`factor * (c_proj / (16 * K_BSG^2)) * δ^{-εgain} * δ^{-s+q_size} ≥ δ^{-(s+η+ζ_dir+η_proj)}`. -/
lemma direction_budget_absorption
    {δ s η ζ_dir η_proj εgain q_graph_total q_diff q_size : ℝ}
    {c_proj K_BSG factor : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (h_factor_ge : factor ≥ 1 / 4)
    (hc_proj_ge : c_proj ≥ δ ^ q_graph_total)
    (hK_BSG_pos : 0 < K_BSG)
    (hK_BSG_le : K_BSG ≤ δ ^ (-q_diff))
    (hD_pos : 0 < εgain - (q_graph_total + 2 * q_diff + q_size + η + ζ_dir + η_proj))
    (h_delta_small : δ ^ (εgain - (q_graph_total + 2 * q_diff + q_size + η + ζ_dir + η_proj)) ≤ 1 / 64) :
    factor * (c_proj / (16 * K_BSG ^ 2)) * δ ^ (-εgain) * δ ^ (-s + q_size) ≥
    δ ^ (-(s + η + ζ_dir + η_proj)) := by
  set D : ℝ := εgain - (q_graph_total + 2 * q_diff + q_size + η + ζ_dir + η_proj) with hD_def
  have hD_pos' : 0 < D := hD_pos
  have hδ_nonneg : 0 ≤ δ := by linarith

  have hδ_negD_ge : δ ^ (-D) ≥ 64 := by
    have h1 : δ ^ (-D) = (δ ^ D)⁻¹ := Real.rpow_neg hδ_nonneg D
    rw [h1]
    have h_pos : 0 < δ ^ D := by positivity
    have h2 : (δ ^ D)⁻¹ ≥ (1 / 64 : ℝ)⁻¹ := by gcongr
    have h3 : (1 / 64 : ℝ)⁻¹ = 64 := by norm_num
    rw [h3] at h2; exact h2

  have hK2_le : K_BSG ^ 2 ≤ δ ^ (-2 * q_diff) := by
    have h1 : K_BSG ≤ δ ^ (-q_diff) := hK_BSG_le
    have h2 : 0 ≤ K_BSG := by linarith
    have h3 : K_BSG ^ 2 ≤ (δ ^ (-q_diff)) ^ 2 := by gcongr
    have h4 : (δ ^ (-q_diff)) ^ 2 = δ ^ (-2 * q_diff) := by
      have h5 : (δ ^ (-q_diff)) ^ 2 = (δ ^ (-q_diff)) * (δ ^ (-q_diff)) := by ring
      rw [h5]
      have h6 : (δ ^ (-q_diff)) * (δ ^ (-q_diff)) = δ ^ ((-q_diff) + (-q_diff)) := by
        rw [← Real.rpow_add hδ_pos]
      rw [h6]
      have h7 : (-q_diff) + (-q_diff) = -2 * q_diff := by ring
      rw [h7]
    rw [h4] at h3
    exact h3

  have h_invK2_ge : (K_BSG ^ 2)⁻¹ ≥ δ ^ (2 * q_diff) := by
    have h5 : (K_BSG ^ 2)⁻¹ ≥ (δ ^ (-2 * q_diff))⁻¹ := by gcongr
    have h_pos2 : 0 < δ ^ (2 * q_diff) := by positivity
    have h6 : (δ ^ (-2 * q_diff))⁻¹ = δ ^ (2 * q_diff) := by
      have h7 : δ ^ (-(2 * q_diff)) = (δ ^ (2 * q_diff))⁻¹ := Real.rpow_neg hδ_nonneg (2 * q_diff)
      have h7' : δ ^ (-2 * q_diff) = δ ^ (-(2 * q_diff)) := by
        rw [show (-2 * q_diff) = (-(2 * q_diff)) by ring]
      rw [h7', h7]
      field_simp [h_pos2.ne']
    rw [h6] at h5; exact h5

  have h_cdiv_ge : c_proj / (16 * K_BSG ^ 2) ≥
      (1 / 16 : ℝ) * δ ^ q_graph_total * δ ^ (2 * q_diff) := by
    have h1 : c_proj / (16 * K_BSG ^ 2) =
        c_proj * (1 / 16 : ℝ) * (K_BSG ^ 2)⁻¹ := by
      field_simp [hK_BSG_pos.ne'] <;> ring
    rw [h1]
    have hc_proj_nonneg : 0 ≤ c_proj := by
      have h : 0 ≤ δ ^ q_graph_total := by positivity
      linarith [hc_proj_ge]
    have h2 : c_proj * (K_BSG ^ 2)⁻¹ ≥ (δ ^ q_graph_total) * (δ ^ (2 * q_diff)) := by
      exact mul_le_mul hc_proj_ge h_invK2_ge (by positivity) hc_proj_nonneg
    calc c_proj * (1 / 16 : ℝ) * (K_BSG ^ 2)⁻¹
      = (1 / 16 : ℝ) * (c_proj * (K_BSG ^ 2)⁻¹) := by ring
    _ ≥ (1 / 16 : ℝ) * ((δ ^ q_graph_total) * (δ ^ (2 * q_diff))) := by gcongr
    _ = (1 / 16 : ℝ) * δ ^ q_graph_total * δ ^ (2 * q_diff) := by ring

  set E : ℝ := q_graph_total + 2 * q_diff + q_size - εgain - s with hE_def
  have hE_eq : E = -(D + η + ζ_dir + η_proj + s) := by
    simp only [E, D, hD_def]; ring

  have h_rpow_sum : δ ^ q_graph_total * δ ^ (2 * q_diff) * δ ^ (-εgain) * δ ^ (-s + q_size) = δ ^ E := by
    have h1 : δ ^ q_graph_total * δ ^ (2 * q_diff) = δ ^ (q_graph_total + 2 * q_diff) := by
      rw [← Real.rpow_add hδ_pos]
    have h2 : δ ^ (q_graph_total + 2 * q_diff) * δ ^ (-εgain) = δ ^ (q_graph_total + 2 * q_diff - εgain) := by
      have h21 : δ ^ (q_graph_total + 2 * q_diff) * δ ^ (-εgain) = δ ^ ((q_graph_total + 2 * q_diff) + (-εgain)) := by
        rw [← Real.rpow_add hδ_pos]
      rw [h21]
      have h22 : (q_graph_total + 2 * q_diff) + (-εgain) = q_graph_total + 2 * q_diff - εgain := by ring
      rw [h22]
    have h3 : δ ^ (q_graph_total + 2 * q_diff - εgain) * δ ^ (-s + q_size) = δ ^ E := by
      have h31 : δ ^ (q_graph_total + 2 * q_diff - εgain) * δ ^ (-s + q_size) = δ ^ ((q_graph_total + 2 * q_diff - εgain) + (-s + q_size)) := by
        rw [← Real.rpow_add hδ_pos]
      rw [h31]
      have h32 : (q_graph_total + 2 * q_diff - εgain) + (-s + q_size) = E := by
        simp only [E, hE_def] <;> ring
      rw [h32]
    rw [h1, h2, h3]

  have h1 : factor * (c_proj / (16 * K_BSG ^ 2)) * δ ^ (-εgain) * δ ^ (-s + q_size) ≥
      factor / 16 * δ ^ E := by
    calc factor * (c_proj / (16 * K_BSG ^ 2)) * δ ^ (-εgain) * δ ^ (-s + q_size)
      ≥ factor * ((1 / 16 : ℝ) * δ ^ q_graph_total * δ ^ (2 * q_diff)) * δ ^ (-εgain) * δ ^ (-s + q_size) := by gcongr
    _ = factor / 16 * (δ ^ q_graph_total * δ ^ (2 * q_diff) * δ ^ (-εgain) * δ ^ (-s + q_size)) := by ring
    _ = factor / 16 * δ ^ E := by rw [h_rpow_sum]

  have h9 : factor / 16 * δ ^ (-D) ≥ 1 := by
    have h10 : factor / 16 ≥ 1 / 64 := by linarith [h_factor_ge]
    calc factor / 16 * δ ^ (-D)
      ≥ (1 / 64 : ℝ) * δ ^ (-D) := by gcongr
    _ ≥ (1 / 64 : ℝ) * 64 := by gcongr
    _ = 1 := by norm_num

  have h_rpow4 : δ ^ (-(D + η + ζ_dir + η_proj + s)) =
      δ ^ (-D) * δ ^ (-(η + ζ_dir + η_proj + s)) := by
    rw [← Real.rpow_add hδ_pos] <;> ring_nf

  have h7 : factor / 16 * δ ^ (-(D + η + ζ_dir + η_proj + s)) ≥
      δ ^ (-(s + η + ζ_dir + η_proj)) := by
    rw [h_rpow4]
    have h_eq : -(η + ζ_dir + η_proj + s) = -(s + η + ζ_dir + η_proj) := by ring
    calc factor / 16 * (δ ^ (-D) * δ ^ (-(η + ζ_dir + η_proj + s)))
      = (factor / 16 * δ ^ (-D)) * δ ^ (-(η + ζ_dir + η_proj + s)) := by ring
    _ ≥ 1 * δ ^ (-(η + ζ_dir + η_proj + s)) := by gcongr
    _ = δ ^ (-(η + ζ_dir + η_proj + s)) := by ring
    _ = δ ^ (-(s + η + ζ_dir + η_proj)) := by rw [h_eq]

  have h_final : factor / 16 * δ ^ E ≥ δ ^ (-(s + η + ζ_dir + η_proj)) := by
    rw [hE_eq]
    exact h7

  exact le_trans h_final h1

/-- Direction failure composition v7: four-sector-first, sector chart,
    direct ν_dir construction, signed transform, terminal wrapper. -/
lemma direction_failure_composition_v6
    {δ s τ κ0 ε η εgain εnc : ℝ}
    {q_graph_total q_diff q_size ζ_dir η_proj : ℝ}
    {c_proj K_BSG K_work : ℝ}
    {q_pole C_ν L_chart : ℝ}
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
    (hq_pole_pos : 0 < q_pole)
    (hC_ν_pos : 0 < C_ν)
    (hL_chart_pos : 0 < L_chart)
    (hL_chart_ge_one : 1 ≤ L_chart)
    -- F_graph
    (hF_graph_finite : F_graph.Finite)
    (hF_graph_grid : ∀ p ∈ F_graph, ∀ i : Fin 2, ∃ k : ℤ, p i = δ * (k : ℝ))
    (hF_graph_sub : F_graph ⊆ {p | p 0 ∈ B1_original ∧ p 1 ∈ B2_original})
    -- B1, B2 grid-aligned subsets of [0,1] (NEW per operator correction)
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
    (hy1_in_unit : y1 ∈ Set.Icc 0 1)
    (hΘ_bad_sub : Θ_bad ⊆ Set.Icc 0 1)
    (h_Θbad_mass : ν Θ_bad ≥ ENNReal.ofReal (δ ^ ε))
    -- Cross-ratio
    (x : ℝ → ℝ)
    -- Chart co-Lipschitz on Θ_bad (from cross-ratio properties)
    (h_chart_colip_all : ∀ (i : Fin 4), ∀ y ∈ Θ_bad, ∀ z ∈ Θ_bad, y ≠ y1 → z ≠ y1 →
      sectorPredicate i x y → sectorPredicate i x z →
      |y - z| ≤ L_chart * |sectorTMap i (x y) - sectorTMap i (x z)|)
    (h_sector_absorb : C_ν * δ ^ τ ≤ δ ^ ε / 2)
    -- Per-y small projected sets
    (S : ℝ → Set ℝ)
    (hS_small : ∀ y ∈ Θ_bad, Nreal δ (S y) < ENNReal.ofReal (δ ^ (-(s + η + ζ_dir + η_proj))))
    -- Density at original cross-ratio projection
    (hG_density : ∀ y ∈ Θ_bad,
      ENat.toENNReal (dyadicCoveringNumber δ
        (F_graph ∩ {p | p 0 * x y + p 1 ∈ S y})) ≥
      ENNReal.ofReal c_proj * Nreal δ B1_original * Nreal δ B2_original)
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
    :
    False := by
  -- ========================================================================
  -- Step 1: Four-sector pigeonhole on Θ_bad (mass δ^ε)
  -- ========================================================================
  have h_four_sector := four_sector_pigeonhole
    (hνY_frost := hν_frost)
    (hTheta_mass := h_Θbad_mass)
    (theta2 := y1)
    (hδ_pos := hδ_pos)
    (hδ_lt_one := hδ_lt_one)
    (hκ0_pos := hτ_pos)
    (hC_Y_pos := hC_ν_pos)
    (hq_pos := hε_pos)
    (h_absorb := h_sector_absorb)
    (x := x)
  rcases h_four_sector with ⟨r, hr_pos, hδ_le_r, h_r_pow, i, Θ_sec, hΘ_sec_sub,
    hΘ_sec_finite, hΘ_sec_closed, hΘ_sec_mass, h_sector, h_sector_range,
    h_sector_proj_id⟩

  have hΘ_sec_sub_bad : Θ_sec ⊆ Θ_bad := fun y hy => (hΘ_sec_sub hy).1

  -- ========================================================================
  -- Step 2: Sector chart
  -- ========================================================================
  let sector_chart : ℝ → ℝ := fun y => sectorTMap i (x y)

  have h_chart_range : ∀ y ∈ Θ_sec, sector_chart y ∈ Set.Icc 0 1 := by
    intro y hy; exact h_sector_range y hy

  -- Measurable extension of sector_chart: agree on Θ_sec, constant 0 elsewhere.
  -- Since Θ_sec is finite, this function is measurable.
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
    have h_y_bad : y ∈ Θ_bad := hΘ_sec_sub_bad hy
    have h_z_bad : z ∈ Θ_bad := hΘ_sec_sub_bad hz
    have h_eq_y : sector_chart_meas y = sector_chart y := h_agree_on_sec y hy
    have h_eq_z : sector_chart_meas z = sector_chart z := h_agree_on_sec z hz
    rw [h_eq_y, h_eq_z]
    exact h_chart_colip_all i y h_y_bad z h_z_bad hy1 hz1 (h_sector y hy) (h_sector z hz)

  have h_chart_range_meas : ∀ y ∈ Θ_sec, sector_chart_meas y ∈ Set.Icc 0 1 := by
    intro y hy
    rw [h_agree_on_sec y hy]
    exact h_chart_range y hy

  -- ========================================================================
  -- Step 3: Construct ν_dir = normalize(map sector_chart (ν.restrict Θ_sec))
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
  -- ν_dir is pushforward through sector_chart, Θ_sec is finite ⇒ image is closed
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
  -- CONVENTION FIX: Use production chartSectorCoordPoint i (same sector index).
  -- B-sets use SWAPPED arguments (B2_original, B1_original) so that
  -- sectorRingBaseSet i B2 B1 matches the chart output coordinates.
  -- Sector data hypotheses are accessed at permuted index phase8ToChartSector i.
  -- ========================================================================
  let B1 := sectorRingBaseSet i B2_original B1_original
  let B2 := sectorCoordSet i B2_original B1_original

  -- Production sector point map (correct affineProjection convention)
  let sec_map := FourSectorChart.chartSectorCoordPoint i

  let G_family (y : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
    sec_map '' (F_graph ∩ {p | p 0 * x y + p 1 ∈ S y})

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
    let G_y := F_graph ∩ {p | p 0 * x y + p 1 ∈ S y}
    have hG_y_sub_F : G_y ⊆ F_graph := fun x hx => hx.1
    have hG_y_finite : Set.Finite G_y := hF_graph_finite.subset hG_y_sub_F
    have hG_y_bdd : IsBounded G_y := hG_y_finite.isBounded
    have hG_y_grid : ∀ p ∈ G_y, ∀ j : Fin 2, ∃ k : ℤ, p j = δ * (k : ℝ) :=
      fun p hp => hF_graph_grid p (hp.1)
    have hG_y_sub2 : ∀ p ∈ G_y, p 0 ∈ B1_original ∧ p 1 ∈ B2_original :=
      fun p hp => hF_graph_sub (hp.1)
    have hG_y_density : ENat.toENNReal (dyadicCoveringNumber δ G_y) ≥
        ENNReal.ofReal c_proj * Nreal δ B1_original * Nreal δ B2_original :=
      hG_density y (hΘ_sec_sub_bad hy)

    -- 1. Boundedness
    have h1 : IsBounded (G_family y) := (hG_y_finite.image sec_map).isBounded

    -- 2. Subset B1 × B2 via phase8_to_chart_sector
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

    -- 4. Density
    have h4_cover : dyadicCoveringNumber δ (G_family y) = dyadicCoveringNumber δ G_y :=
      chartSector_grid_covering_preservation hδ_pos hG_y_grid
    have hB1_intgrid : B1_original ⊆ productLikeIntegerGrid δ := fun x hx => (hB1_grid_set hx).1
    have hB2_intgrid : B2_original ⊆ productLikeIntegerGrid δ := fun x hx => (hB2_grid_set hx).1
    have h_neg_eq1 : -B1_original = Set.image (fun x : ℝ => -x) B1_original := by
      ext y
      simp only [Set.mem_neg, Set.mem_image]
      constructor
      · intro h; exact ⟨-y, h, by ring⟩
      · rintro ⟨x, hx, rfl⟩; simpa using hx
    have h_neg_eq2 : -B2_original = Set.image (fun x : ℝ => -x) B2_original := by
      ext y
      simp only [Set.mem_neg, Set.mem_image]
      constructor
      · intro h; exact ⟨-y, h, by ring⟩
      · rintro ⟨x, hx, rfl⟩; simpa using hx
    have hN_product : Nreal δ B1 * Nreal δ B2 = Nreal δ B1_original * Nreal δ B2_original := by
      have h_refl1 : Nreal δ (-B1_original) = Nreal δ B1_original := by
        rw [h_neg_eq1]
        exact nreal_reflection_eq hδ_pos hB1_intgrid hB1_bounded
      have h_refl2 : Nreal δ (-B2_original) = Nreal δ B2_original := by
        rw [h_neg_eq2]
        exact nreal_reflection_eq hδ_pos hB2_intgrid hB2_bounded
      fin_cases i
      · have hB1_eq : B1 = B1_original := by
          simp [B1, sectorRingBaseSet]
        have hB2_eq : B2 = B2_original := by
          simp [B2, sectorCoordSet]
        rw [hB1_eq, hB2_eq]
      · have hB1_eq : B1 = B2_original := by
          simp [B1, sectorRingBaseSet]
        have hB2_eq : B2 = B1_original := by
          simp [B2, sectorCoordSet]
        rw [hB1_eq, hB2_eq, mul_comm]
      · have hB1_eq : B1 = -B1_original := by
          simp [B1, sectorRingBaseSet]
        have hB2_eq : B2 = B2_original := by
          simp [B2, sectorCoordSet]
        rw [hB1_eq, hB2_eq, h_refl1]
      · have hB1_eq : B1 = -B2_original := by
          simp [B1, sectorRingBaseSet]
        have hB2_eq : B2 = B1_original := by
          simp [B2, sectorCoordSet]
        rw [hB1_eq, hB2_eq, h_refl2, mul_comm]
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
      exact hG_y_density

    -- 5. Projection bound
    let base : ENNReal := ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
      ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ B2
    let factor_real : ℝ := match i with
      | 0 => 1 / 2 | 1 => 1 / 4 | 2 => 1 / 2 | 3 => 1 / 4
    let factor_ennreal : ENNReal := sectorFactorENNReal i

    have h_factor_ge : factor_real ≥ 1 / 4 := by
      dsimp only [factor_real]; fin_cases i <;> norm_num

    have h_chart_pred : FourSectorChart.chartSectorPred i (x y) := by
      have h_sp : sectorPredicate i x y := h_sector y hy
      fin_cases i <;> simp [sectorPredicate, FourSectorChart.chartSectorPred,
        Set.mem_Icc, Set.mem_Ioi, Set.mem_Ico, Set.mem_Iio] at h_sp ⊢ <;> tauto

    have h_proj_sub : affineProjection (x y) G_y ⊆ S y := by
      intro z hz
      rcases hz with ⟨p, hp, rfl⟩
      exact hp.2

    have h_line_copy_sub : realLineCopy (affineProjection (x y) G_y) ⊆ realLineCopy (S y) := by
      intro w hw
      simpa [realLineCopy] using h_proj_sub (by simpa [realLineCopy] using hw)

    have h_proj_bound : Nreal δ (affineProjection (x y) G_y) ≤ Nreal δ (S y) := by
      dsimp only [Nreal]
      exact ENat.toENNReal_mono (dyadicCoveringNumber_mono h_line_copy_sub)

    have hS_small' : Nreal δ (S y) < ENNReal.ofReal (δ ^ (-(s + η + ζ_dir + η_proj))) :=
      hS_small y (hΘ_sec_sub_bad hy)

    have h_lt : Nreal δ (affineProjection (x y) G_y) <
        ENNReal.ofReal (δ ^ (-(s + η + ζ_dir + η_proj))) :=
      lt_of_le_of_lt h_proj_bound hS_small'

    -- Lower bound Nreal δ B2 ≥ δ^{-s+q_size}
    have hB2_lower' : Nreal δ B2 ≥ ENNReal.ofReal (δ ^ (-s + q_size)) := by
      fin_cases i <;> simp [B2, sectorCoordSet] <;>
        (try { exact hB2_lower }) <;> (try { exact hB1_lower })

    -- Budget absorption in real numbers
    have h_real_ineq : factor_real * (c_proj / (16 * K_BSG ^ 2)) * δ ^ (-εgain) * δ ^ (-s + q_size) ≥
        δ ^ (-(s + η + ζ_dir + η_proj)) :=
      direction_budget_absorption
        (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
        (h_factor_ge := h_factor_ge)
        (hc_proj_ge := hc_proj_ge)
        (hK_BSG_pos := hK_BSG_pos) (hK_BSG_le := hK_BSG_le)
        (hD_pos := by linarith [h_budget]) (h_delta_small := h_delta_small)

    -- Lift to ENNReal
    let X : ℝ := (c_proj / (16 * K_BSG ^ 2)) * δ ^ (-εgain) * δ ^ (-s + q_size)
    have hX_pos : 0 < X := by positivity
    have h_fr_pos : 0 < factor_real := by
      dsimp only [factor_real]; fin_cases i <;> norm_num

    have h_base_lower : base ≥ ENNReal.ofReal X := by
      have h2 : Nreal δ B2 ≥ ENNReal.ofReal (δ ^ (-s + q_size)) := hB2_lower'
      simp only [base, X]
      have h3 : ENNReal.ofReal (c_proj / (16 * K_BSG ^ 2)) * ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ B2 ≥
          ENNReal.ofReal (c_proj / (16 * K_BSG ^ 2)) * ENNReal.ofReal (δ ^ (-εgain)) * ENNReal.ofReal (δ ^ (-s + q_size)) := by
        gcongr
      have h4 : ENNReal.ofReal (c_proj / (16 * K_BSG ^ 2)) * ENNReal.ofReal (δ ^ (-εgain)) * ENNReal.ofReal (δ ^ (-s + q_size)) =
          ENNReal.ofReal X := by
        simp only [X]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        <;> ring
      rw [h4] at h3
      exact h3

    have h_factor_eq : sectorFactorENNReal i = ENNReal.ofReal factor_real := by
      fin_cases i <;> simp [sectorFactorENNReal, factor_real] <;> norm_num

    have h_mul_eq : sectorFactorENNReal i * ENNReal.ofReal X = ENNReal.ofReal (factor_real * X) := by
      rw [h_factor_eq, ← ENNReal.ofReal_mul (show 0 ≤ factor_real from by linarith)]
      <;> rfl

    let factor_ennreal : ENNReal := sectorFactorENNReal i

    have h_absorb : factor_ennreal * base ≥ ENNReal.ofReal (δ ^ (-(s + η + ζ_dir + η_proj))) := by
      have h_X_eq : factor_real * X = factor_real * (c_proj / (16 * K_BSG ^ 2)) * δ ^ (-εgain) * δ ^ (-s + q_size) := by
        simp [X] <;> ring
      have h_ineq : δ ^ (-(s + η + ζ_dir + η_proj)) ≤ factor_real * X := by
        rw [h_X_eq]
        exact h_real_ineq
      have h_fe : factor_ennreal = sectorFactorENNReal i := by rfl
      calc factor_ennreal * base
        ≥ factor_ennreal * ENNReal.ofReal X := by gcongr
      _ = sectorFactorENNReal i * ENNReal.ofReal X := by rw [h_fe]
      _ = ENNReal.ofReal (factor_real * X) := h_mul_eq
      _ ≥ ENNReal.ofReal (δ ^ (-(s + η + ζ_dir + η_proj))) := by
        exact ENNReal.ofReal_le_ofReal h_ineq

    have h_conv : ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D (x y) G_y)) =
        Nreal δ (affineProjection (x y) G_y) := by rfl

    have h5 : ENat.toENNReal (dyadicCoveringNumber δ
          (projectionSet1D (FourSectorChart.chartSectorT i (x y))
            (FourSectorChart.chartSectorCoordPoint i '' G_y))) <
          (1 / 2 : ENNReal) * base := by
      have h_cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by fin_cases i <;> tauto
      rcases h_cases with (rfl | rfl | rfl | rfl)
      · -- Sector 0: exact projection, input factor 1/2
        have h_fac : factor_ennreal = (1 / 2 : ENNReal) := by
          simp [factor_ennreal, sectorFactorENNReal]
        have h_abs0 : (1 / 2 : ENNReal) * base ≥ ENNReal.ofReal (δ ^ (-(s + η + ζ_dir + η_proj))) := by
          rw [←h_fac]; exact h_absorb
        have h_in : Nreal δ (affineProjection (x y) G_y) < (1 / 2 : ENNReal) * base := by
          exact lt_of_lt_of_le h_lt h_abs0
        have h_proj_eq : affineProjection (FourSectorChart.chartSectorT 0 (x y))
              (FourSectorChart.chartSectorCoordPoint 0 '' G_y) = affineProjection (x y) G_y := by
          have h_s : FourSectorChart.chartSectorScalar 0 (x y) = 1 := by
            simp [FourSectorChart.chartSectorScalar] <;> norm_num
          rw [FourSectorChart.chart_sector_projection_set 0 (x y) h_chart_pred G_y, h_s]
          ext z; simp [scaleSet]
        have h_goal : ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D (FourSectorChart.chartSectorT 0 (x y)) (FourSectorChart.chartSectorCoordPoint 0 '' G_y))) =
            Nreal δ (affineProjection (x y) G_y) := by
          have h1 : ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D (FourSectorChart.chartSectorT 0 (x y)) (FourSectorChart.chartSectorCoordPoint 0 '' G_y))) =
              Nreal δ (affineProjection (FourSectorChart.chartSectorT 0 (x y)) (FourSectorChart.chartSectorCoordPoint 0 '' G_y)) := by rfl
          rw [h1, h_proj_eq]
        rw [h_goal]
        exact h_in
      · -- Sector 1: factor-2 preservation, input factor 1/4
        have h_fac : factor_ennreal = (1 / 4 : ENNReal) := by
          simp [factor_ennreal, sectorFactorENNReal]
        have h_abs1 : (1 / 4 : ENNReal) * base ≥ ENNReal.ofReal (δ ^ (-(s + η + ζ_dir + η_proj))) := by
          rw [←h_fac]; exact h_absorb
        have h_in : Nreal δ (affineProjection (x y) G_y) < (1 / 4 : ENNReal) * base := by
          exact lt_of_lt_of_le h_lt h_abs1
        have h_bound : Nreal δ (affineProjection (FourSectorChart.chartSectorT 1 (x y))
              (FourSectorChart.chartSectorCoordPoint 1 '' G_y)) ≤
            (2 : ENNReal) * Nreal δ (affineProjection (x y) G_y) :=
          FourSectorChart.four_sector_projection_preservation hδ_pos h_chart_pred hG_y_bdd
        have h_lt2 : (2 : ENNReal) * Nreal δ (affineProjection (x y) G_y) <
            (2 : ENNReal) * ((1 / 4 : ENNReal) * base) :=
          ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) h_in
        have h_arith : (2 : ENNReal) * ((1 / 4 : ENNReal) * base) = (1 / 2 : ENNReal) * base := by
          have h1 : (2 : ENNReal) * (1 / 4 : ENNReal) = (1 / 2 : ENNReal) := by
            have h2 : (2 : ENNReal) = ENNReal.ofReal 2 := by simp
            have h4 : (1 / 4 : ENNReal) = ENNReal.ofReal (1 / 4) := by simp
            have hhalf : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2) := by simp
            have h_mul : ENNReal.ofReal 2 * ENNReal.ofReal (1 / 4) = ENNReal.ofReal (2 * (1 / 4 : ℝ)) := by
              rw [ENNReal.ofReal_mul (by norm_num)]
            have h_eq : 2 * (1 / 4 : ℝ) = (1 / 2 : ℝ) := by norm_num
            calc (2 : ENNReal) * (1 / 4 : ENNReal)
              = ENNReal.ofReal 2 * ENNReal.ofReal (1 / 4) := by rw [h2, h4]
            _ = ENNReal.ofReal (2 * (1 / 4 : ℝ)) := h_mul
            _ = ENNReal.ofReal (1 / 2) := by rw [h_eq]
            _ = (1 / 2 : ENNReal) := hhalf.symm
          rw [← mul_assoc, h1] <;> rfl
        have h_goal : ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D (FourSectorChart.chartSectorT 1 (x y)) (FourSectorChart.chartSectorCoordPoint 1 '' G_y))) =
            Nreal δ (affineProjection (FourSectorChart.chartSectorT 1 (x y)) (FourSectorChart.chartSectorCoordPoint 1 '' G_y)) := by rfl
        rw [h_goal]
        calc Nreal δ (affineProjection (FourSectorChart.chartSectorT 1 (x y)) (FourSectorChart.chartSectorCoordPoint 1 '' G_y))
          ≤ (2 : ENNReal) * Nreal δ (affineProjection (x y) G_y) := h_bound
        _ < (2 : ENNReal) * ((1 / 4 : ENNReal) * base) := h_lt2
        _ = (1 / 2 : ENNReal) * base := h_arith
      · -- Sector 2: exact projection, input factor 1/2
        have h_fac : factor_ennreal = (1 / 2 : ENNReal) := by
          simp [factor_ennreal, sectorFactorENNReal]
        have h_abs2 : (1 / 2 : ENNReal) * base ≥ ENNReal.ofReal (δ ^ (-(s + η + ζ_dir + η_proj))) := by
          rw [←h_fac]; exact h_absorb
        have h_in : Nreal δ (affineProjection (x y) G_y) < (1 / 2 : ENNReal) * base := by
          exact lt_of_lt_of_le h_lt h_abs2
        have h_proj_eq : affineProjection (FourSectorChart.chartSectorT 2 (x y))
              (FourSectorChart.chartSectorCoordPoint 2 '' G_y) = affineProjection (x y) G_y := by
          have h_s : FourSectorChart.chartSectorScalar 2 (x y) = 1 := by
            simp [FourSectorChart.chartSectorScalar] <;> norm_num
          rw [FourSectorChart.chart_sector_projection_set 2 (x y) h_chart_pred G_y, h_s]
          ext z; simp [scaleSet]
        have h_goal : ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D (FourSectorChart.chartSectorT 2 (x y)) (FourSectorChart.chartSectorCoordPoint 2 '' G_y))) =
            Nreal δ (affineProjection (x y) G_y) := by
          have h1 : ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D (FourSectorChart.chartSectorT 2 (x y)) (FourSectorChart.chartSectorCoordPoint 2 '' G_y))) =
              Nreal δ (affineProjection (FourSectorChart.chartSectorT 2 (x y)) (FourSectorChart.chartSectorCoordPoint 2 '' G_y)) := by rfl
          rw [h1, h_proj_eq]
        rw [h_goal]
        exact h_in
      · -- Sector 3: factor-2 preservation, input factor 1/4
        have h_fac : factor_ennreal = (1 / 4 : ENNReal) := by
          simp [factor_ennreal, sectorFactorENNReal]
        have h_abs3 : (1 / 4 : ENNReal) * base ≥ ENNReal.ofReal (δ ^ (-(s + η + ζ_dir + η_proj))) := by
          rw [←h_fac]; exact h_absorb
        have h_in : Nreal δ (affineProjection (x y) G_y) < (1 / 4 : ENNReal) * base := by
          exact lt_of_lt_of_le h_lt h_abs3
        have h_bound : Nreal δ (affineProjection (FourSectorChart.chartSectorT 3 (x y))
              (FourSectorChart.chartSectorCoordPoint 3 '' G_y)) ≤
            (2 : ENNReal) * Nreal δ (affineProjection (x y) G_y) :=
          FourSectorChart.four_sector_projection_preservation hδ_pos h_chart_pred hG_y_bdd
        have h_lt2 : (2 : ENNReal) * Nreal δ (affineProjection (x y) G_y) <
            (2 : ENNReal) * ((1 / 4 : ENNReal) * base) :=
          ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) h_in
        have h_arith : (2 : ENNReal) * ((1 / 4 : ENNReal) * base) = (1 / 2 : ENNReal) * base := by
          have h1 : (2 : ENNReal) * (1 / 4 : ENNReal) = (1 / 2 : ENNReal) := by
            have h2 : (2 : ENNReal) = ENNReal.ofReal 2 := by simp
            have h4 : (1 / 4 : ENNReal) = ENNReal.ofReal (1 / 4) := by simp
            have hhalf : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2) := by simp
            have h_mul : ENNReal.ofReal 2 * ENNReal.ofReal (1 / 4) = ENNReal.ofReal (2 * (1 / 4 : ℝ)) := by
              rw [ENNReal.ofReal_mul (by norm_num)]
            have h_eq : 2 * (1 / 4 : ℝ) = (1 / 2 : ℝ) := by norm_num
            calc (2 : ENNReal) * (1 / 4 : ENNReal)
              = ENNReal.ofReal 2 * ENNReal.ofReal (1 / 4) := by rw [h2, h4]
            _ = ENNReal.ofReal (2 * (1 / 4 : ℝ)) := h_mul
            _ = ENNReal.ofReal (1 / 2) := by rw [h_eq]
            _ = (1 / 2 : ENNReal) := hhalf.symm
          rw [← mul_assoc, h1] <;> rfl
        have h_goal : ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D (FourSectorChart.chartSectorT 3 (x y)) (FourSectorChart.chartSectorCoordPoint 3 '' G_y))) =
            Nreal δ (affineProjection (FourSectorChart.chartSectorT 3 (x y)) (FourSectorChart.chartSectorCoordPoint 3 '' G_y)) := by rfl
        rw [h_goal]
        calc Nreal δ (affineProjection (FourSectorChart.chartSectorT 3 (x y)) (FourSectorChart.chartSectorCoordPoint 3 '' G_y))
          ≤ (2 : ENNReal) * Nreal δ (affineProjection (x y) G_y) := h_bound
        _ < (2 : ENNReal) * ((1 / 4 : ENNReal) * base) := h_lt2
        _ = (1 / 2 : ENNReal) * base := h_arith

    have h_sec_eq : FourSectorChart.chartSectorT i (x y) = sector_chart y := by
      simp [sector_chart, sectorTMap, FourSectorChart.chartSectorT] <;> fin_cases i <;> rfl
    have h_G_eq : FourSectorChart.chartSectorCoordPoint i '' G_y = G_family y := by
      simp [G_family, sec_map] <;> rfl
    have h5_final : ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D (sector_chart y) (G_family y))) <
        (1 / 2 : ENNReal) * ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
          ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ B2 := by
      rw [←h_sec_eq, ←h_G_eq]
      have h_base_eq : (1 / 2 : ENNReal) * base =
          (1 / 2 : ENNReal) * ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
            ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ B2 := by
        simp [base] <;> ring
      rw [h_base_eq] at h5
      exact h5

    exact ⟨h1, h2, h3, h4, h5_final⟩

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
      (try { exact hB2_bounded }) <;>
      (try { exact hB1_bounded }) <;>
      (try { exact IsBounded.neg hB1_bounded }) <;>
      (try { exact IsBounded.neg hB2_bounded })
  have hB2_bdd : IsBounded B2 := by
    fin_cases i <;> simp (config := {decide := true}) [B2, sectorCoordSet] <;>
      (try { exact hB1_bounded }) <;>
      (try { exact hB2_bounded })
  have hB1_nonempty' : B1.Nonempty := by
    fin_cases i <;> simp (config := {decide := true}) [B1, sectorRingBaseSet] <;>
      (try { exact hB2_nonempty }) <;>
      (try { exact hB1_nonempty }) <;>
      (try { exact hB2_nonempty.image _ }) <;>
      (try { exact hB1_nonempty.image _ })
  have hB2_nonempty' : B2.Nonempty := by
    fin_cases i <;> simp (config := {decide := true}) [B2, sectorCoordSet] <;>
      (try { exact hB1_nonempty }) <;>
      (try { exact hB2_nonempty })
  -- Permuted sector index for sector data hypotheses.
  -- sectorRingBaseSet i B2_original B1_original = sectorRingBaseSet j B1_original B2_original
  let j : Fin 4 := match i with
    | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2
  have hB1_eq_j : B1 = sectorRingBaseSet j B1_original B2_original := by
    fin_cases i <;> simp [B1, sectorRingBaseSet] <;> rfl
  have hB2_eq_j : B2 = sectorCoordSet j B1_original B2_original := by
    fin_cases i <;> simp [B2, sectorCoordSet] <;> rfl

  have hB1_grid : ∀ b ∈ B1, ∃ k : ℤ, b = δ * (k : ℝ) := by
    intro b hb
    fin_cases i
    · -- Sector 0: B1 = B1_original
      simp only [B1, sectorRingBaseSet] at hb
      exact (hB1_grid_set hb).1
    · -- Sector 1: B1 = B2_original
      simp only [B1, sectorRingBaseSet] at hb
      exact (hB2_grid_set hb).1
    · -- Sector 2: B1 = -B1_original
      simp only [B1, sectorRingBaseSet, Set.mem_image] at hb
      rcases hb with ⟨x, hx, rfl⟩
      rcases (hB1_grid_set hx).1 with ⟨k, hk⟩
      refine ⟨-k, ?_⟩
      simp [hk]
    · -- Sector 3: B1 = -B2_original
      simp only [B1, sectorRingBaseSet, Set.mem_image] at hb
      rcases hb with ⟨x, hx, rfl⟩
      rcases (hB2_grid_set hx).1 with ⟨k, hk⟩
      refine ⟨-k, ?_⟩
      simp [hk]
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
