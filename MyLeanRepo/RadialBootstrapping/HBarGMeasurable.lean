module

/-
  HBarGMeasurable.lean

  Prove that HBarG_r (with G-intersection bad tubes) is measurable.
  Uses countable dense directions + lower semicontinuity of section measure.
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.HBarMeasurable
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal


noncomputable section

namespace RadialBootstrapping

/-- For fixed x, the map n ↦ ν₂({y | |dot(y-x,n)| < r} ∩ G_x) is lower semicontinuous.

    Proof using inner regularity: approximate the measurable set from within by a compact set K,
    then use uniform continuity to show K stays inside the tube for nearby normals. -/
lemma tubeG_measure_lsc (x : Point) (G : Set (Point × Point))
    (hG_meas : MeasurableSet G) (ν₂ : Measure Point) [IsProbabilityMeasure ν₂]
    (r : ℝ) (hr : 0 < r) :
    LowerSemicontinuous (fun m : UnitSphere' =>
      ν₂ {b₂ | |dot (b₂ - x) (m : Point)| < r ∧ (x, b₂) ∈ G}) := by
  intro n
  dsimp only
  intro a ha
  let U : Set Point := {b₂ | |dot (b₂ - x) (n : Point)| < r ∧ (x, b₂) ∈ G}
  have hU_meas : MeasurableSet U := by
    have h1 : MeasurableSet {b₂ : Point | |dot (b₂ - x) (n : Point)| < r} := by
      have h_cont : Continuous (fun b₂ : Point => |dot (b₂ - x) (n : Point)|) := by fun_prop
      exact (h_cont.isOpen_preimage _ isOpen_Iio).measurableSet
    have h2 : MeasurableSet {b₂ : Point | (x, b₂) ∈ G} :=
      hG_meas.preimage (by fun_prop)
    exact h1.inter h2
  have h_gt : a < ν₂ U := ha
  have hU_ne_top : ν₂ U ≠ ⊤ := by
    have h : ν₂ U ≤ ν₂ Set.univ := measure_mono (subset_univ _)
    have h2 : ν₂ Set.univ = 1 := measure_univ
    rw [h2] at h
    exact ne_top_of_le_ne_top (by simp) h
  have ha_ne_top : a ≠ ⊤ := ne_top_of_lt h_gt

  -- Choose eps_enn such that a + eps_enn < ν₂ U
  have h1_real : a.toReal < (ν₂ U).toReal :=
    (ENNReal.toReal_lt_toReal ha_ne_top hU_ne_top).mpr h_gt
  let eps_real : ℝ := ((ν₂ U).toReal - a.toReal) / 2
  have heps_real_pos : 0 < eps_real := by
    dsimp only [eps_real]
    linarith
  let eps_enn : ENNReal := ENNReal.ofReal eps_real
  have heps_enn_ne_zero : eps_enn ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr heps_real_pos)
  have h_a_eps_lt : a + eps_enn < ν₂ U := by
    have ha_eq : a = ENNReal.ofReal a.toReal := by simp [ha_ne_top]
    have hU_eq : ν₂ U = ENNReal.ofReal (ν₂ U).toReal := by simp [hU_ne_top]
    rw [ha_eq, hU_eq]
    have h_add : ENNReal.ofReal a.toReal + eps_enn = ENNReal.ofReal (a.toReal + eps_real) := by
      rw [← ENNReal.ofReal_add (by positivity) heps_real_pos.le] <;> ring
    rw [h_add]
    have h_ineq : a.toReal + eps_real < (ν₂ U).toReal := by
      dsimp only [eps_real]
      linarith [h1_real]
    have h_nonneg1 : 0 ≤ a.toReal + eps_real := by positivity
    have h_nonneg2 : 0 ≤ (ν₂ U).toReal := by positivity
    have h_ne_top1 : ENNReal.ofReal (a.toReal + eps_real) ≠ ⊤ := by simp
    have h_ne_top2 : ENNReal.ofReal (ν₂ U).toReal ≠ ⊤ := by simp
    have h_toReal1 : (ENNReal.ofReal (a.toReal + eps_real)).toReal = a.toReal + eps_real := by
      rw [ENNReal.toReal_ofReal h_nonneg1]
    have h_toReal2 : (ENNReal.ofReal (ν₂ U).toReal).toReal = (ν₂ U).toReal := by
      rw [ENNReal.toReal_ofReal h_nonneg2]
    have h_toReal_lt : (ENNReal.ofReal (a.toReal + eps_real)).toReal < (ENNReal.ofReal (ν₂ U).toReal).toReal := by
      rw [h_toReal1, h_toReal2] <;> exact h_ineq
    exact (ENNReal.toReal_lt_toReal h_ne_top1 h_ne_top2).mp h_toReal_lt

  -- Inner regularity: find compact K ⊆ U with ν₂ (U \\ K) < eps_enn
  have h_compact_exists : ∃ (K : Set Point), K ⊆ U ∧ IsCompact K ∧ ν₂ (U.diff K) < eps_enn :=
    hU_meas.exists_isCompact_sdiff_lt hU_ne_top heps_enn_ne_zero
  rcases h_compact_exists with ⟨K, hK_sub, hK_compact, hK_diff_lt⟩

  have hK_meas : MeasurableSet K := hK_compact.measurableSet
  have h_diff_ne_top : ν₂ (U.diff K) ≠ ⊤ := ne_top_of_lt hK_diff_lt
  have h_eq : ν₂ U = ν₂ K + ν₂ (U.diff K) := by
    have h_disj : Disjoint K (U.diff K) := by
      rw [Set.disjoint_left]
      intro z hz1 hz2
      exact hz2.2 hz1
    have hU2_meas : MeasurableSet (U.diff K) := hU_meas.diff hK_meas
    have h : ν₂ (K ∪ (U.diff K)) = ν₂ K + ν₂ (U.diff K) :=
      measure_union h_disj hU2_meas
    have h_union : K ∪ (U.diff K) = U := by
      ext z
      simp only [Set.mem_union, Set.mem_diff]
      constructor
      · rintro (h | h)
        · exact hK_sub h
        · exact h.1
      · intro hz
        by_cases hK : z ∈ K
        · exact Or.inl hK
        · exact Or.inr ⟨hz, hK⟩
    rw [h_union] at h
    exact h
  have hK_gt : a < ν₂ K := by
    have h1 : a + ν₂ (U.diff K) < a + eps_enn :=
      ENNReal.add_lt_add_left ha_ne_top hK_diff_lt
    have h2 : a + ν₂ (U.diff K) < ν₂ K + ν₂ (U.diff K) := by
      rw [h_eq] at h_a_eps_lt
      exact lt_trans h1 h_a_eps_lt
    exact (ENNReal.add_lt_add_iff_right h_diff_ne_top).mp h2

  have hK_nonempty : K.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h] at hK_gt
    simp at hK_gt

  -- Max of f(y) := |dot(y-x,n)| on K
  let f : Point → ℝ := fun y => |dot (y - x) (n : Point)|
  have h_cont_f : Continuous f := by fun_prop
  have h_image_compact : IsCompact (f '' K) := hK_compact.image h_cont_f
  have h_image_nonempty : (f '' K).Nonempty := hK_nonempty.image f
  rcases h_image_compact.exists_isGreatest h_image_nonempty with ⟨d, hd⟩
  have hd_in : d ∈ f '' K := hd.1
  have hd_max : ∀ w ∈ f '' K, w ≤ d := hd.2
  rcases hd_in with ⟨y0, hy0, rfl⟩
  have h_y0_lt : f y0 < r := (hK_sub hy0).1
  have hd_le : ∀ y ∈ K, f y ≤ f y0 := by
    intro y hy
    have h5 : f y ∈ f '' K := ⟨y, hy, rfl⟩
    exact hd_max (f y) h5
  let epsilon : ℝ := r - f y0
  have hepsilon_pos : 0 < epsilon := by linarith

  -- Bound ‖y-x‖ on K
  have hK_bounded : ∃ (M : ℝ), 0 ≤ M ∧ ∀ y ∈ K, ‖y - x‖ ≤ M := by
    have h : Bornology.IsBounded K := hK_compact.isBounded
    rcases Metric.isBounded_iff.mp h with ⟨C, hC⟩
    rcases hK_nonempty with ⟨x0, hx0⟩
    have hC_nonneg : 0 ≤ C := by
      have h : dist x0 x0 ≤ C := hC hx0 hx0
      simpa using h
    let M := C + dist x0 x
    have hM_nonneg : 0 ≤ M := by
      apply add_nonneg
      · exact hC_nonneg
      · exact dist_nonneg
    have hM_le : ∀ y ∈ K, dist y x ≤ M := by
      intro y hy
      have h1 : dist y x ≤ dist y x0 + dist x0 x := dist_triangle y x0 x
      have h2 : dist y x0 ≤ C := hC hy hx0
      linarith
    exact ⟨M, hM_nonneg, fun y hy => by simpa [dist_eq_norm] using hM_le y hy⟩
  rcases hK_bounded with ⟨M, hM_nonneg, hM_le⟩

  by_cases hM : M = 0
  · -- M = 0: K ⊆ {x}, tube condition trivial for any normal
    filter_upwards with m'
    have hK_sub2 : K ⊆ {b₂ | |dot (b₂ - x) (m' : Point)| < r ∧ (x, b₂) ∈ G} := by
      intro y hy
      have h_y_eq_x : y = x := by
        have h1 : ‖y - x‖ ≤ M := hM_le y hy
        rw [hM] at h1
        have h3 : ‖y - x‖ = 0 := by linarith [norm_nonneg (y - x)]
        have h4 : y - x = 0 := by simpa using h3
        exact eq_of_sub_eq_zero h4
      have h_yG : (x, y) ∈ G := (hK_sub hy).2
      rw [h_y_eq_x] at h_yG
      rw [h_y_eq_x]
      exact ⟨by simpa using hr, h_yG⟩
    calc a < ν₂ K := hK_gt
      _ ≤ ν₂ _ := measure_mono hK_sub2
  · -- M > 0
    have hM_pos : 0 < M := lt_of_le_of_ne hM_nonneg (Ne.symm hM)
    let δ : ℝ := epsilon / M
    have hδ_pos : 0 < δ := by positivity
    have h_nhds : ∀ᶠ (m' : UnitSphere') in nhds n, ‖(m' : Point) - (n : Point)‖ < δ :=
      Metric.ball_mem_nhds n hδ_pos
    filter_upwards [h_nhds] with m' hdist
    have hK_sub2 : K ⊆ {b₂ | |dot (b₂ - x) (m' : Point)| < r ∧ (x, b₂) ∈ G} := by
      intro y hy
      have h_y_G : (x, y) ∈ G := (hK_sub hy).2
      have h_dot_eq : dot (y - x) (m' : Point) =
          dot (y - x) (n : Point) + dot (y - x) ((m' : Point) - (n : Point)) := by
        have h3 : (m' : Point) = (n : Point) + ((m' : Point) - (n : Point)) := by abel
        have h4 : dot (y - x) ((n : Point) + ((m' : Point) - (n : Point))) =
            dot (y - x) (n : Point) + dot (y - x) ((m' : Point) - (n : Point)) := by
          unfold dot
          rw [inner_add_right]
          <;> rfl
        have h5 : dot (y - x) (m' : Point) = dot (y - x) ((n : Point) + ((m' : Point) - (n : Point))) := by
          apply congr_arg (fun z : Point => dot (y - x) z)
          exact h3
        rw [h5]
        exact h4
      have h_abs : |dot (y - x) (m' : Point)| ≤
          |dot (y - x) (n : Point)| + |dot (y - x) ((m' : Point) - (n : Point))| := by
        rw [h_dot_eq]
        have h3 : ‖dot (y - x) (n : Point) + dot (y - x) ((m' : Point) - (n : Point))‖ ≤
            ‖dot (y - x) (n : Point)‖ + ‖dot (y - x) ((m' : Point) - (n : Point))‖ :=
          norm_add_le _ _
        simpa using h3
      have h_cauchy : |dot (y - x) ((m' : Point) - (n : Point))| ≤
          ‖y - x‖ * ‖(m' : Point) - (n : Point)‖ := by
        have h : |inner ℝ (y - x) ((m' : Point) - (n : Point))| ≤
            ‖y - x‖ * ‖(m' : Point) - (n : Point)‖ :=
          abs_real_inner_le_norm (y - x) ((m' : Point) - (n : Point))
        simpa [dot] using h
      have h2 : |dot (y - x) (n : Point)| ≤ f y0 := hd_le y hy
      have h3 : ‖y - x‖ * ‖(m' : Point) - (n : Point)‖ < epsilon := by
        have h_norm_nonneg : 0 ≤ ‖(m' : Point) - (n : Point)‖ := norm_nonneg _
        calc ‖y - x‖ * ‖(m' : Point) - (n : Point)‖
          ≤ M * ‖(m' : Point) - (n : Point)‖ :=
            mul_le_mul_of_nonneg_right (hM_le y hy) h_norm_nonneg
        _ < M * δ := by
          exact mul_lt_mul_of_pos_left hdist hM_pos
        _ = epsilon := by
          simp [δ, hM_pos.ne'] <;> field_simp [hM_pos.ne'] <;> ring
      have h4 : |dot (y - x) (m' : Point)| < r := by
        linarith [h_abs, h2, h3]
      exact ⟨h4, h_y_G⟩
    calc a < ν₂ K := hK_gt
      _ ≤ ν₂ _ := measure_mono hK_sub2

/-- Bad tubes through x (strict form): G-intersection mass > K'·r^(σ+τ). -/
def BadTubesG_strict (ν₂ : Measure Point) (G : Set (Point × Point))
    (K' σ τ r : ℝ) (x : Point) : Set (AffineSubspace ℝ Point) :=
  {ℓ | x ∈ (ℓ : Set Point) ∧ Module.finrank ℝ ℓ.direction = 1 ∧
    ν₂ {b₂ | b₂ ∈ Metric.thickening r (ℓ : Set Point) ∧ (x, b₂) ∈ G} >
      ENNReal.ofReal (K' * Real.rpow r (σ + τ))}

/-- HBarG_r (strict form): pairs (x,y) where y lies in some G-bad r-tube through x. -/
def HBarG_r_strict (ν₂ : Measure Point) (G : Set (Point × Point))
    (K' σ τ r : ℝ) : Set (Point × Point) :=
  {p | ∃ ℓ ∈ BadTubesG_strict ν₂ G K' σ τ r p.1, p.2 ∈ Metric.thickening r (ℓ : Set Point)}

/-- HBarG_r (strict form) is measurable. -/
lemma HBarG_r_strict_measurable (ν₂ : Measure Point) [IsProbabilityMeasure ν₂]
    (G : Set (Point × Point)) (hG_meas : MeasurableSet G)
    (K' σ τ r : ℝ) (hr : 0 < r) (hK'_nonneg : 0 ≤ K') (hστ_nonneg : 0 ≤ σ + τ) :
    MeasurableSet (HBarG_r_strict ν₂ G K' σ τ r) := by
  let threshold : ℝ := K' * Real.rpow r (σ + τ)
  have hthreshold_nonneg : 0 ≤ threshold := by
    have h1 : 0 ≤ Real.rpow r (σ + τ) := Real.rpow_nonneg (by linarith) (σ + τ)
    exact mul_nonneg hK'_nonneg h1

  rcases TopologicalSpace.exists_countable_dense UnitSphere' with ⟨D, hD_count, hD_dense⟩

  let S : UnitSphere' → Set (Point × Point) := fun q =>
    {p | ν₂ {b₂ | |dot (b₂ - p.1) (q : Point)| < r ∧ (p.1, b₂) ∈ G} > ENNReal.ofReal threshold ∧
      |dot (p.2 - p.1) (q : Point)| < r}

  have hS_meas : ∀ (q : UnitSphere'), MeasurableSet (S q) := by
    intro q
    let C : Set ((Point × Point) × Point) :=
      {z | |dot (z.2 - z.1.1) (q : Point)| < r ∧ (z.1.1, z.2) ∈ G}
    have hC_meas : MeasurableSet C := by
      have h1 : MeasurableSet {z : (Point × Point) × Point | |dot (z.2 - z.1.1) (q : Point)| < r} := by
        have h_cont : Continuous (fun z : (Point × Point) × Point => |dot (z.2 - z.1.1) (q : Point)|) := by fun_prop
        exact (h_cont.isOpen_preimage _ isOpen_Iio).measurableSet
      have h2 : MeasurableSet {z : (Point × Point) × Point | (z.1.1, z.2) ∈ G} :=
        hG_meas.preimage (by fun_prop)
      exact h1.inter h2
    have h_meas_f : Measurable (fun p : Point × Point => ν₂ (Prod.mk p ⁻¹' C)) :=
      measurable_measure_prodMk_left hC_meas
    have h_ioi_meas : MeasurableSet (Set.Ioi (ENNReal.ofReal threshold)) :=
      isOpen_Ioi.measurableSet
    have h_set1 : MeasurableSet {p : Point × Point | ν₂ (Prod.mk p ⁻¹' C) > ENNReal.ofReal threshold} :=
      h_meas_f h_ioi_meas
    have h_cont2 : Continuous (fun p : Point × Point => |dot (p.2 - p.1) (q : Point)|) := by fun_prop
    have h_set2 : MeasurableSet {p : Point × Point | |dot (p.2 - p.1) (q : Point)| < r} :=
      (h_cont2.isOpen_preimage _ isOpen_Iio).measurableSet
    have h_goal : MeasurableSet (S q) := by
      simp only [S, Set.mem_setOf_eq]
      exact h_set1.inter h_set2
    exact h_goal

  have h_eq : HBarG_r_strict ν₂ G K' σ τ r = ⋃ q ∈ D, S q := by
    ext p
    constructor
    · rintro ⟨ℓ, hℓ_bad, hytube⟩
      have hxℓ : p.1 ∈ (ℓ : Set Point) := hℓ_bad.1
      have hfin : Module.finrank ℝ ℓ.direction = 1 := hℓ_bad.2.1
      have hmass : ν₂ {b₂ | b₂ ∈ Metric.thickening r (ℓ : Set Point) ∧ (p.1, b₂) ∈ G} >
          ENNReal.ofReal threshold := hℓ_bad.2.2
      rcases exists_normal_of_affineSubspace p.1 ℓ hxℓ hfin with ⟨n, hn_eq⟩
      have h_tube_eq : Metric.thickening r (ℓ : Set Point) = tubeOfNormal r p.1 n := by
        rw [hn_eq]
        exact (tubeOfNormal_eq_thickening r hr p.1 n).symm
      have h1 : ν₂ {b₂ | |dot (b₂ - p.1) (n : Point)| < r ∧ (p.1, b₂) ∈ G} >
          ENNReal.ofReal threshold := by
        have h_set_eq : {b₂ | |dot (b₂ - p.1) (n : Point)| < r ∧ (p.1, b₂) ∈ G} =
            {b₂ | b₂ ∈ Metric.thickening r (ℓ : Set Point) ∧ (p.1, b₂) ∈ G} := by
          ext y
          simp [h_tube_eq, tubeOfNormal, mem_lineOfNormal_iff] <;> tauto
        rw [h_set_eq]; exact hmass
      have h2 : |dot (p.2 - p.1) (n : Point)| < r := by
        have h : p.2 ∈ Metric.thickening r (ℓ : Set Point) := hytube
        rw [h_tube_eq] at h
        simpa [tubeOfNormal, mem_lineOfNormal_iff] using h
      let B_x : Set UnitSphere' := {m | ν₂ {b₂ | |dot (b₂ - p.1) (m : Point)| < r ∧ (p.1, b₂) ∈ G} >
          ENNReal.ofReal threshold}
      have hB_open : IsOpen B_x := by
        have h_lsc := tubeG_measure_lsc p.1 G hG_meas ν₂ r hr
        have h : IsOpen {m : UnitSphere' | ENNReal.ofReal threshold < (fun m : UnitSphere' =>
            ν₂ {b₂ | |dot (b₂ - p.1) (m : Point)| < r ∧ (p.1, b₂) ∈ G}) m} :=
          Semicontinuous.isOpen h_lsc (ENNReal.ofReal threshold)
        simpa [B_x] using h
      have hn_in_B : n ∈ B_x := h1
      let Arc : Set UnitSphere' := {m | |dot (p.2 - p.1) (m : Point)| < r}
      have hArc_open : IsOpen Arc := by
        have h_cont : Continuous (fun m : UnitSphere' => |dot (p.2 - p.1) (m : Point)|) := by fun_prop
        exact (h_cont.isOpen_preimage _ isOpen_Iio)
      have hn_in_Arc : n ∈ Arc := h2
      have h_inter_nonempty : (B_x ∩ Arc).Nonempty := ⟨n, hn_in_B, hn_in_Arc⟩
      have h_inter_open : IsOpen (B_x ∩ Arc) := hB_open.inter hArc_open
      rcases hD_dense.inter_open_nonempty (B_x ∩ Arc) h_inter_open h_inter_nonempty with ⟨q, hq_inter, hqD⟩
      have hqB : q ∈ B_x := hq_inter.1
      have hqArc : q ∈ Arc := hq_inter.2
      have hqS : p ∈ S q := ⟨hqB, hqArc⟩
      exact Set.mem_iUnion₂.mpr ⟨q, hqD, hqS⟩
    · intro h
      rcases Set.mem_iUnion₂.mp h with ⟨q, hqD, hqS⟩
      let ℓ : AffineSubspace ℝ Point := lineOfNormal p.1 q
      have hxℓ : p.1 ∈ (ℓ : Set Point) := by
        simpa [ℓ, lineOfNormal] using AffineSubspace.left_vadd_mem_mk' p.1 (normalFunctional q).ker
      have hfin : Module.finrank ℝ ℓ.direction = 1 := lineOfNormal_finrank p.1 q
      have h_set_eq : {b₂ | |dot (b₂ - p.1) (q : Point)| < r ∧ (p.1, b₂) ∈ G} =
          {b₂ | b₂ ∈ Metric.thickening r (ℓ : Set Point) ∧ (p.1, b₂) ∈ G} := by
        ext y
        simp only [Set.mem_setOf_eq]
        have h_tube : y ∈ tubeOfNormal r p.1 q ↔ |dot (y - p.1) (q : Point)| < r := by
          simp [tubeOfNormal, mem_lineOfNormal_iff]
        have h_eq2 : tubeOfNormal r p.1 q = Metric.thickening r (ℓ : Set Point) :=
          tubeOfNormal_eq_thickening r hr p.1 q
        constructor
        · intro h
          exact ⟨by rw [←h_eq2]; exact h_tube.mpr h.1, h.2⟩
        · intro h
          exact ⟨h_tube.mp (by rw [h_eq2]; exact h.1), h.2⟩
      have h_bad : ℓ ∈ BadTubesG_strict ν₂ G K' σ τ r p.1 := by
        exact ⟨hxℓ, hfin, by rw [←h_set_eq]; exact hqS.1⟩
      have hytube : p.2 ∈ Metric.thickening r (ℓ : Set Point) := by
        have h : |dot (p.2 - p.1) (q : Point)| < r := hqS.2
        have h' : p.2 ∈ tubeOfNormal r p.1 q := by
          simpa [tubeOfNormal, mem_lineOfNormal_iff] using h
        have h_eq : tubeOfNormal r p.1 q = Metric.thickening r (ℓ : Set Point) := by
          exact tubeOfNormal_eq_thickening r hr p.1 q
        rw [h_eq] at h'
        exact h'
      exact ⟨ℓ, h_bad, hytube⟩

  rw [h_eq]
  exact MeasurableSet.biUnion hD_count (fun q _ => hS_meas q)

end RadialBootstrapping

end
