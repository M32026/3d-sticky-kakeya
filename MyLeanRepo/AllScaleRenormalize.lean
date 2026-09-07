module

/-
# All-Scale Renormalization Lemma
-/

public import MyLeanRepo.AllScaleFrostman
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory ENNReal Set Classical

namespace WeakTwoEndsSumProduct

/-- Small-scale bound case B1: r ≥ δ/r₀. -/
lemma all_scale_renormalize_bound_b1
    {δ κ C r₀ r L : ℝ}
    (hδ : 0 < δ) (hκ_pos : 0 < κ) (hC_pos : 0 < C)
    (hr₀_pos : 0 < r₀) (hr_pos : 0 < r)
    (hL_nonneg : 0 ≤ L) (hL_lt : L < δ / r₀)
    (h_r_ge : δ / r₀ ≤ r)
    (h_small : C * δ ^ (κ / 2) ≤ 1) :
    C * (2 : ℝ) ^ (-κ) * r₀ ^ (κ / 2) * L ^ κ ≤ (2 ^ (κ / 2)) * r ^ (κ / 2) := by
  have h_dr_nonneg : 0 ≤ δ / r₀ := by positivity
  have h1 : L ^ κ ≤ (δ / r₀) ^ κ :=
    Real.rpow_le_rpow hL_nonneg hL_lt.le hκ_pos.le
  have h_split : (δ / r₀) ^ κ = (δ / r₀) ^ (κ / 2) * (δ / r₀) ^ (κ / 2) := by
    rw [← Real.rpow_add (by positivity)] <;> ring_nf
  have h_mul : r₀ ^ (κ / 2) * (δ / r₀) ^ (κ / 2) = δ ^ (κ / 2) := by
    have h : r₀ ^ (κ / 2) * (δ / r₀) ^ (κ / 2) = (r₀ * (δ / r₀)) ^ (κ / 2) := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
    rw [h]
    have h2 : r₀ * (δ / r₀) = δ := by field_simp [hr₀_pos.ne'] <;> ring
    rw [h2]
  have h_alg : r₀ ^ (κ / 2) * (δ / r₀) ^ κ = δ ^ (κ / 2) * (δ / r₀) ^ (κ / 2) := by
    rw [h_split]
    have h3 : r₀ ^ (κ / 2) * ((δ / r₀) ^ (κ / 2) * (δ / r₀) ^ (κ / 2)) =
        (r₀ ^ (κ / 2) * (δ / r₀) ^ (κ / 2)) * (δ / r₀) ^ (κ / 2) := by ring
    rw [h3, h_mul] <;> ring
  have h4 : (δ / r₀) ^ (κ / 2) ≤ r ^ (κ / 2) :=
    Real.rpow_le_rpow (by positivity) h_r_ge (by linarith)
  have h5 : C * δ ^ (κ / 2) ≤ 1 := h_small
  have h6 : (2 : ℝ) ^ (-κ) ≤ (2 : ℝ) ^ (κ / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h_pos2 : 0 ≤ C * (2 : ℝ) ^ (-κ) := by positivity
  have h_pos3 : 0 ≤ r₀ ^ (κ / 2) := by positivity
  have h71 : r₀ ^ (κ / 2) * L ^ κ ≤ r₀ ^ (κ / 2) * (δ / r₀) ^ κ :=
    mul_le_mul_of_nonneg_left h1 h_pos3
  have h7 : C * (2 : ℝ) ^ (-κ) * r₀ ^ (κ / 2) * L ^ κ ≤
      C * (2 : ℝ) ^ (-κ) * (r₀ ^ (κ / 2) * (δ / r₀) ^ κ) := by
    have h_eq : C * (2 : ℝ) ^ (-κ) * r₀ ^ (κ / 2) * L ^ κ =
        C * (2 : ℝ) ^ (-κ) * (r₀ ^ (κ / 2) * L ^ κ) := by ring
    rw [h_eq]
    exact mul_le_mul_of_nonneg_left h71 h_pos2
  rw [h_alg] at h7
  have h8 : C * (2 : ℝ) ^ (-κ) * (δ ^ (κ / 2) * (δ / r₀) ^ (κ / 2)) ≤
      (2 ^ (κ / 2)) * r ^ (κ / 2) := by
    have h9 : C * (2 : ℝ) ^ (-κ) * (δ ^ (κ / 2) * (δ / r₀) ^ (κ / 2)) =
        (C * δ ^ (κ / 2)) * ((2 : ℝ) ^ (-κ) * (δ / r₀) ^ (κ / 2)) := by ring
    rw [h9]
    have h10 : 0 ≤ (2 : ℝ) ^ (-κ) := by positivity
    have h11 : 0 ≤ (δ / r₀) ^ (κ / 2) := by positivity
    have h_factor2 : (2 : ℝ) ^ (-κ) * (δ / r₀) ^ (κ / 2) ≤
        (2 : ℝ) ^ (κ / 2) * (δ / r₀) ^ (κ / 2) :=
      mul_le_mul_of_nonneg_right h6 h11
    have h12 : (C * δ ^ (κ / 2)) * ((2 : ℝ) ^ (-κ) * (δ / r₀) ^ (κ / 2)) ≤
        1 * ((2 : ℝ) ^ (κ / 2) * (δ / r₀) ^ (κ / 2)) :=
      mul_le_mul h5 h_factor2 (by positivity) (by positivity)
    rw [one_mul] at h12
    exact h12.trans (mul_le_mul_of_nonneg_left h4 (by positivity))
  exact h7.trans h8

/-- Small-scale bound case B2: r < δ/r₀. -/
lemma all_scale_renormalize_bound_b2
    {δ κ C r₀ r L : ℝ}
    (hδ : 0 < δ) (hκ_pos : 0 < κ) (hC_pos : 0 < C)
    (hr₀_pos : 0 < r₀) (hr₀_le_one : r₀ ≤ 1)
    (hr_pos : 0 < r) (hL_nonneg : 0 ≤ L) (hL_le_2r : L ≤ 2 * r)
    (h_r_lt : r < δ / r₀)
    (h_small : C * δ ^ (κ / 2) ≤ 1) :
    C * (2 : ℝ) ^ (-κ) * r₀ ^ (κ / 2) * L ^ κ ≤ (2 ^ (κ / 2)) * r ^ (κ / 2) := by
  have h_2r_nonneg : 0 ≤ 2 * r := by positivity
  have h1 : L ^ κ ≤ (2 * r) ^ κ :=
    Real.rpow_le_rpow hL_nonneg hL_le_2r hκ_pos.le
  have h2 : (2 * r) ^ κ = (2 : ℝ) ^ κ * r ^ κ :=
    Real.mul_rpow (by positivity) (by positivity)
  have h1' : L ^ κ ≤ (2 : ℝ) ^ κ * r ^ κ := by
    rw [h2] at h1; exact h1
  have h_pos1 : 0 ≤ C * (2 : ℝ) ^ (-κ) * r₀ ^ (κ / 2) := by positivity
  have h3 : C * (2 : ℝ) ^ (-κ) * r₀ ^ (κ / 2) * L ^ κ ≤
      C * (2 : ℝ) ^ (-κ) * r₀ ^ (κ / 2) * ((2 : ℝ) ^ κ * r ^ κ) :=
    mul_le_mul_of_nonneg_left h1' h_pos1
  have h41 : (-κ) + κ = 0 := by ring
  have h4 : (2 : ℝ) ^ (-κ) * (2 : ℝ) ^ κ = 1 := by
    have h42 : (2 : ℝ) ^ (-κ) * (2 : ℝ) ^ κ = (2 : ℝ) ^ ((-κ) + κ) := by
      rw [← Real.rpow_add (by norm_num)]
    rw [h42, h41]
    exact Real.rpow_zero 2
  have h5 : C * (2 : ℝ) ^ (-κ) * r₀ ^ (κ / 2) * ((2 : ℝ) ^ κ * r ^ κ) =
      C * r₀ ^ (κ / 2) * r ^ κ := by
    have h6 : C * (2 : ℝ) ^ (-κ) * r₀ ^ (κ / 2) * ((2 : ℝ) ^ κ * r ^ κ) =
        C * (r₀ ^ (κ / 2)) * (((2 : ℝ) ^ (-κ) * (2 : ℝ) ^ κ) * r ^ κ) := by ring
    rw [h6, h4] <;> ring
  have h6 : C * (2 : ℝ) ^ (-κ) * r₀ ^ (κ / 2) * L ^ κ ≤ C * r₀ ^ (κ / 2) * r ^ κ :=
    h3.trans (le_of_eq h5)
  have h7 : r ^ (κ / 2) < (δ / r₀) ^ (κ / 2) :=
    Real.rpow_lt_rpow (by positivity) h_r_lt (by linarith)
  have h8 : (δ / r₀) ^ (κ / 2) = δ ^ (κ / 2) / r₀ ^ (κ / 2) :=
    Real.div_rpow (by positivity) (by positivity) (κ / 2)
  have h9 : C * r₀ ^ (κ / 2) * r ^ (κ / 2) ≤ 1 := by
    have h10 : C * r₀ ^ (κ / 2) * r ^ (κ / 2) < C * r₀ ^ (κ / 2) * (δ / r₀) ^ (κ / 2) :=
      mul_lt_mul_of_pos_left h7 (by positivity)
    have h11 : C * r₀ ^ (κ / 2) * (δ / r₀) ^ (κ / 2) = C * δ ^ (κ / 2) := by
      rw [h8]; field_simp [hr₀_pos.ne'] <;> ring
    rw [h11] at h10
    exact h10.le.trans h_small
  have h10 : r ^ κ = r ^ (κ / 2) * r ^ (κ / 2) := by
    rw [← Real.rpow_add (by linarith)] <;> ring_nf
  have h11 : C * r₀ ^ (κ / 2) * r ^ κ ≤ (2 ^ (κ / 2)) * r ^ (κ / 2) := by
    rw [h10]
    have h12 : C * r₀ ^ (κ / 2) * r ^ (κ / 2) ≤ 1 := h9
    have h13 : 0 ≤ r ^ (κ / 2) := by positivity
    have h14 : (1 : ℝ) ≤ (2 ^ (κ / 2)) := by
      have h15 : 0 ≤ κ / 2 := by linarith
      exact Real.one_le_rpow (by norm_num) h15
    nlinarith
  exact h6.trans h11

/-- All-scale Frostman implies the measure has no atoms. -/
lemma all_scale_frostman_no_atoms
    {κ C : ℝ} {μ : Measure ℝ} (hκ_pos : 0 < κ) (hC_pos : 0 < C)
    (h_frost : ∀ (x r : ℝ), 0 < r → μ (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (C * r ^ κ))
    (x : ℝ) : μ {x} = 0 := by
  have h1 : ∀ (ε : ℝ), 0 < ε → μ {x} ≤ ENNReal.ofReal (C * ε ^ κ) := by
    intro ε hε
    have h2 : {x} ⊆ Set.Icc (x - ε) (x + ε) := by
      intro y hy; simp only [Set.mem_singleton_iff] at hy; rw [hy]; simp [hε.le] <;> linarith
    have h3 : μ {x} ≤ μ (Set.Icc (x - ε) (x + ε)) := measure_mono h2
    have h4 := h_frost x ε hε
    exact h3.trans h4
  have h_top : μ {x} ≠ ⊤ := by
    have h51 : (1 : ℝ)^κ = 1 := by simp
    have h5 : μ {x} ≤ ENNReal.ofReal C := by
      have h := h1 1 (by norm_num)
      have h52 : C * (1 : ℝ)^κ = C := by simp
      rw [h52] at h
      exact h
    have h6 : ENNReal.ofReal C ≠ ⊤ := ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top h6 h5
  by_contra h_pos
  have h_pos' : 0 < μ {x} := by
    exact Ne.bot_lt h_pos
  have h_lt_top : μ {x} < ⊤ := lt_top_iff_ne_top.mpr h_top
  have h_toReal_pos : 0 < (μ {x}).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨h_pos', h_lt_top⟩
  set y : ℝ := (μ {x}).toReal with hy_def
  have hy_pos : 0 < y := h_toReal_pos
  set ε : ℝ := (y / (2 * C)) ^ (1 / κ) with hε_def
  have hε_pos : 0 < ε := by positivity
  have hε_pow : ε ^ κ = y / (2 * C) := by
    rw [hε_def]
    have h7 : (1 / κ) * κ = 1 := by field_simp [hκ_pos.ne'] <;> ring
    have h_pos_base : 0 ≤ y / (2 * C) := by positivity
    have h6 : ((y / (2 * C)) ^ (1 / κ)) ^ κ = (y / (2 * C)) := by
      rw [← Real.rpow_mul h_pos_base, h7, Real.rpow_one]
    exact h6
  have h7 : C * ε ^ κ < y := by
    rw [hε_pow]
    have h8 : 0 < 2 * C := by positivity
    have h9 : C * (y / (2 * C)) < y := by
      have h10 : C * y < (2 * C) * y := by nlinarith
      calc C * (y / (2 * C)) = (C * y) / (2 * C) := by field_simp [h8.ne'] <;> ring
        _ < ((2 * C) * y) / (2 * C) := by gcongr
        _ = y := by field_simp [h8.ne'] <;> ring
    exact h9
  have h10 : ENNReal.ofReal (C * ε ^ κ) < μ {x} := by
    have h14 : C * ε ^ κ < (μ {x}).toReal := by
      simpa [hy_def] using h7
    have h15 : 0 ≤ C * ε ^ κ := by positivity
    exact (ENNReal.ofReal_lt_iff_lt_toReal h15 h_top).mpr h14
  have h13 : μ {x} ≤ ENNReal.ofReal (C * ε ^ κ) := h1 ε hε_pos
  exact not_le.mpr h10 h13

/-- Bound on μ(J) for the renormalized interval, used in all_scale_renormalize. -/
lemma all_scale_renormalize_interval_bound
    {δ κ C r₀ r : ℝ}
    (hδ : 0 < δ) (hκ_pos : 0 < κ) (hC_pos : 0 < C)
    (hr₀_pos : 0 < r₀) (hr₀_le_one : r₀ ≤ 1) (hr_pos : 0 < r)
    {μ : Measure ℝ} {I₀ : Set ℝ} {x₀ : ℝ}
    (hμI₀_ne_zero : μ I₀ ≠ 0) (hμI₀_ne_top : μ I₀ ≠ ⊤)
    (h_frost_ball : ∀ (x r : ℝ), 0 < r → μ (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (C * r ^ κ))
    (h_density : ENNReal.ofReal (r₀ ^ (κ / 2)) ≤ μ I₀)
    (h_self_sim : ∀ (a b : ℝ), Set.Icc a b ⊆ I₀ → δ ≤ b - a →
      μ (Set.Icc a b) ≤ μ I₀ * ENNReal.ofReal (((b - a) / r₀) ^ (κ / 2)))
    (h_small : C * δ ^ (κ / 2) ≤ 1)
    {L R : ℝ} (hLR : L ≤ R) (hL_nonneg : 0 ≤ L) (hR_le_one : R ≤ 1) (h_len : R - L ≤ 2 * r)
    (h_sub : Set.Icc (x₀ + r₀ * L) (x₀ + r₀ * R) ⊆ I₀) :
    μ (Set.Icc (x₀ + r₀ * L) (x₀ + r₀ * R)) ≤
    μ I₀ * ENNReal.ofReal ((2 * r) ^ (κ / 2)) := by
  let J := Set.Icc (x₀ + r₀ * L) (x₀ + r₀ * R)
  set ℓ : ℝ := R - L with hℓ_def
  have hℓ_nonneg : 0 ≤ ℓ := by linarith
  have hℓ_le_2r : ℓ ≤ 2 * r := h_len
  have h_len_J : (x₀ + r₀ * R) - (x₀ + r₀ * L) = r₀ * ℓ := by ring
  by_cases h_long : δ ≤ r₀ * ℓ
  · -- Long case: self-similarity
    have h6 : μ J ≤ μ I₀ * ENNReal.ofReal (ℓ ^ (κ / 2)) := by
      have h7 := h_self_sim (x₀ + r₀ * L) (x₀ + r₀ * R) h_sub (by linarith)
      have h8 : ((x₀ + r₀ * R) - (x₀ + r₀ * L)) / r₀ = ℓ := by
        rw [h_len_J]; field_simp [hr₀_pos.ne'] <;> ring
      rw [h8] at h7; exact h7
    have h9 : ℓ ^ (κ / 2) ≤ (2 * r) ^ (κ / 2) := by
      gcongr <;> linarith
    have h10 : μ J ≤ μ I₀ * ENNReal.ofReal ((2 * r) ^ (κ / 2)) := by
      calc μ J ≤ μ I₀ * ENNReal.ofReal (ℓ ^ (κ / 2)) := h6
           _ ≤ μ I₀ * ENNReal.ofReal ((2 * r) ^ (κ / 2)) := by
             gcongr <;> exact ENNReal.ofReal_le_ofReal h9
    simpa [J] using h10
  · -- Short case
    have h_short : r₀ * ℓ < δ := by linarith
    by_cases hℓ0 : ℓ = 0
    · -- ℓ = 0, J is a singleton
      have h_eq : x₀ + r₀ * R = x₀ + r₀ * L := by
        have h : R = L := by linarith
        rw [h]
      have hJ_point : J = {x₀ + r₀ * L} := by
        ext z
        simp only [J, Set.mem_Icc, Set.mem_singleton_iff]
        constructor
        · rintro ⟨h1, h2⟩; linarith
        · intro h; rw [h, h_eq]; exact ⟨by linarith, by linarith⟩
      have h_atom : μ J = 0 := by
        rw [hJ_point]
        exact all_scale_frostman_no_atoms hκ_pos hC_pos h_frost_ball (x₀ + r₀ * L)
      have h_goal : μ J ≤ μ I₀ * ENNReal.ofReal ((2 * r) ^ (κ / 2)) := by
        rw [h_atom]; simp
      simpa [J] using h_goal
    · -- ℓ > 0, all-scale Frostman at half-length
      have hℓ_pos : 0 < ℓ := by
        have h_ne : (0 : ℝ) ≠ ℓ := Ne.symm hℓ0
        exact lt_of_le_of_ne hℓ_nonneg h_ne
      set m : ℝ := x₀ + r₀ * (L + R) / 2 with hm_def
      have h_rad_pos : 0 < r₀ * ℓ / 2 := by positivity
      have hJ_sub : J ⊆ Set.Icc (m - r₀ * ℓ / 2) (m + r₀ * ℓ / 2) := by
        intro z hz
        have hzl : x₀ + r₀ * L ≤ z := hz.1
        have hzr : z ≤ x₀ + r₀ * R := hz.2
        dsimp only [m]
        constructor <;> nlinarith
      have h_frost : μ (Set.Icc (m - r₀ * ℓ / 2) (m + r₀ * ℓ / 2)) ≤
          ENNReal.ofReal (C * (r₀ * ℓ / 2) ^ κ) := h_frost_ball m (r₀ * ℓ / 2) h_rad_pos
      have hμJ : μ J ≤ ENNReal.ofReal (C * (r₀ * ℓ / 2) ^ κ) :=
        calc μ J ≤ μ (Set.Icc (m - r₀ * ℓ / 2) (m + r₀ * ℓ / 2)) := measure_mono hJ_sub
             _ ≤ ENNReal.ofReal (C * (r₀ * ℓ / 2) ^ κ) := h_frost
      have h_rad_pow : (r₀ * ℓ / 2) ^ κ = (2 : ℝ)^(-κ) * r₀ ^ κ * ℓ ^ κ := by
        have h1 : (r₀ * ℓ / 2) ^ κ = (r₀ * ℓ) ^ κ / (2 : ℝ) ^ κ := by
          rw [Real.div_rpow (by positivity) (by positivity)]
        rw [h1]
        have h2 : (r₀ * ℓ) ^ κ = r₀ ^ κ * ℓ ^ κ := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
        rw [h2]
        have h4 : (2 : ℝ) ^ κ ≠ 0 := by positivity
        have h5 : (2 : ℝ)^(-κ) = 1 / (2 : ℝ)^κ := by
          rw [Real.rpow_neg (by positivity)] <;> field_simp
        rw [h5]
        field_simp [h4] <;> ring
      have h_eq2 : C * (r₀ * ℓ / 2) ^ κ = C * (2 : ℝ)^(-κ) * r₀ ^ κ * ℓ ^ κ := by
        rw [h_rad_pow] <;> ring
      have hμJ2 : μ J ≤ ENNReal.ofReal (C * (2 : ℝ)^(-κ) * r₀ ^ κ * ℓ ^ κ) := by
        rw [h_eq2] at hμJ; exact hμJ
      have hℓ_lt_dr : ℓ < δ / r₀ := by
        have h : r₀ * ℓ < δ := h_short
        calc ℓ = (r₀ * ℓ) / r₀ := by field_simp [hr₀_pos.ne'] <;> ring
          _ < δ / r₀ := by gcongr
      have h_real : C * (2 : ℝ)^(-κ) * r₀ ^ (κ / 2) * ℓ ^ κ ≤ (2 * r) ^ (κ / 2) := by
        have h_rpow_eq : (2 ^ (κ / 2)) * r ^ (κ / 2) = (2 * r) ^ (κ / 2) := by
          have hr_nonneg : 0 ≤ r := by linarith
          rw [← Real.mul_rpow (by positivity) hr_nonneg] <;> ring
        by_cases h31 : δ / r₀ ≤ r
        · have h_bound := all_scale_renormalize_bound_b1 hδ hκ_pos hC_pos hr₀_pos hr_pos hℓ_nonneg hℓ_lt_dr h31 h_small
          rw [h_rpow_eq] at h_bound; exact h_bound
        · have h32 : r < δ / r₀ := by linarith
          have h_bound := all_scale_renormalize_bound_b2 hδ hκ_pos hC_pos hr₀_pos hr₀_le_one hr_pos hℓ_nonneg hℓ_le_2r h32 h_small
          rw [h_rpow_eq] at h_bound; exact h_bound
      have h_inv : (μ I₀)⁻¹ ≤ ENNReal.ofReal (r₀ ^ (-(κ / 2))) := by
        have h17 : ENNReal.ofReal (r₀ ^ (κ / 2)) ≤ μ I₀ := h_density
        have h18 : (μ I₀)⁻¹ ≤ (ENNReal.ofReal (r₀ ^ (κ / 2)))⁻¹ := ENNReal.inv_le_inv' h17
        have h19 : (ENNReal.ofReal (r₀ ^ (κ / 2)))⁻¹ = ENNReal.ofReal ((r₀ ^ (κ / 2))⁻¹) := by
          rw [ENNReal.ofReal_inv_of_pos (by positivity)]
        rw [h19] at h18
        have h20 : (r₀ ^ (κ / 2))⁻¹ = r₀ ^ (-(κ / 2)) := by
          rw [← Real.rpow_neg (by positivity)]
        rw [h20] at h18; exact h18
      have h23 : ENNReal.ofReal (r₀ ^ (-(κ / 2))) * ENNReal.ofReal (C * (2 : ℝ)^(-κ) * r₀ ^ κ * ℓ ^ κ) =
          ENNReal.ofReal (C * (2 : ℝ)^(-κ) * r₀ ^ (κ / 2) * ℓ ^ κ) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        have h25 : r₀ ^ (-(κ / 2)) * r₀ ^ κ = r₀ ^ (κ / 2) := by
          rw [← Real.rpow_add (by positivity)] <;> ring_nf
        have h24 : r₀ ^ (-(κ / 2)) * (C * (2 : ℝ)^(-κ) * r₀ ^ κ * ℓ ^ κ) =
            C * (2 : ℝ)^(-κ) * r₀ ^ (κ / 2) * ℓ ^ κ := by
          calc
            r₀ ^ (-(κ / 2)) * (C * (2 : ℝ)^(-κ) * r₀ ^ κ * ℓ ^ κ)
              = C * (2 : ℝ)^(-κ) * (r₀ ^ (-(κ / 2)) * r₀ ^ κ) * ℓ ^ κ := by ring
            _ = C * (2 : ℝ)^(-κ) * r₀ ^ (κ / 2) * ℓ ^ κ := by rw [h25] <;> ring
        rw [h24]
      have h_main_ineq : (μ I₀)⁻¹ * μ J ≤ ENNReal.ofReal ((2 * r) ^ (κ / 2)) := by
        have h22 : (μ I₀)⁻¹ * ENNReal.ofReal (C * (2 : ℝ)^(-κ) * r₀ ^ κ * ℓ ^ κ) ≤
            ENNReal.ofReal (r₀ ^ (-(κ / 2))) * ENNReal.ofReal (C * (2 : ℝ)^(-κ) * r₀ ^ κ * ℓ ^ κ) :=
          mul_le_mul_of_nonneg_right h_inv (by positivity)
        calc (μ I₀)⁻¹ * μ J
          ≤ (μ I₀)⁻¹ * ENNReal.ofReal (C * (2 : ℝ)^(-κ) * r₀ ^ κ * ℓ ^ κ) := by gcongr
        _ ≤ ENNReal.ofReal (r₀ ^ (-(κ / 2))) * ENNReal.ofReal (C * (2 : ℝ)^(-κ) * r₀ ^ κ * ℓ ^ κ) := h22
        _ = ENNReal.ofReal (C * (2 : ℝ)^(-κ) * r₀ ^ (κ / 2) * ℓ ^ κ) := h23
        _ ≤ ENNReal.ofReal ((2 * r) ^ (κ / 2)) := ENNReal.ofReal_le_ofReal h_real
      have h29 : μ I₀ * ((μ I₀)⁻¹ * μ J) = μ J := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hμI₀_ne_zero hμI₀_ne_top, one_mul]
      have h30 : μ I₀ * ((μ I₀)⁻¹ * μ J) ≤ μ I₀ * ENNReal.ofReal ((2 * r) ^ (κ / 2)) :=
        mul_le_mul_of_nonneg_left h_main_ineq (by positivity)
      have h_final : μ J ≤ μ I₀ * ENNReal.ofReal ((2 * r) ^ (κ / 2)) := by
        rw [h29] at h30; exact h30
      simpa [J] using h_final

lemma all_scale_renormalize
    {δ κ C : ℝ} (hδ : 0 < δ) (hκ_pos : 0 < κ)
    {μ : Measure ℝ} {x₀ r₀ : ℝ}
    (hr₀_pos : 0 < r₀) (hr₀_le_one : r₀ ≤ 1)
    (hμI₀_pos : 0 < μ (Set.Icc x₀ (x₀ + r₀)))
    (hμI₀_ne_top : μ (Set.Icc x₀ (x₀ + r₀)) ≠ ⊤)
    (hμ_allscale : IsAllScaleFrostman κ C μ)
    (hμ_supp : μ.support ⊆ Set.Icc 0 1)
    (h_density : ENNReal.ofReal (r₀ ^ (κ / 2)) ≤ μ (Set.Icc x₀ (x₀ + r₀)))
    (h_self_sim : ∀ (a b : ℝ), Set.Icc a b ⊆ Set.Icc x₀ (x₀ + r₀) → δ ≤ b - a →
      μ (Set.Icc a b) ≤
        μ (Set.Icc x₀ (x₀ + r₀)) * ENNReal.ofReal (((b - a) / r₀) ^ (κ / 2)))
    (h_small : C * δ ^ (κ / 2) ≤ 1) :
    ∃ (ν : Measure ℝ),
      ν Set.univ = 1 ∧
      ν.support ⊆ Set.Icc 0 1 ∧
      IsAllScaleFrostman (κ / 2) (2 ^ (κ / 2)) ν ∧
      ∀ (z : ℝ), z ∈ ν.support → x₀ + r₀ * z ∈ μ.support := by
  let I₀ := Set.Icc x₀ (x₀ + r₀)
  let h : ℝ → ℝ := fun y => (y - x₀) / r₀
  let μ_map : Measure ℝ := Measure.map h (μ.restrict I₀)
  let ν : Measure ℝ := (μ I₀)⁻¹ • μ_map
  have hμI₀_ne_zero : μ I₀ ≠ 0 := hμI₀_pos.ne'
  have h_meas : Measurable h := by fun_prop
  have h_inj : Function.Injective h := by
    intro y1 y2 h_eq
    simp only [h] at h_eq
    field_simp [hr₀_pos.ne'] at h_eq <;> linarith
  have h_image : h '' I₀ = Set.Icc (0 : ℝ) 1 := by
    ext z
    simp only [h, Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      have h1 : 0 ≤ (y - x₀) / r₀ := by apply div_nonneg <;> linarith
      have h2 : (y - x₀) / r₀ ≤ 1 := by
        rw [div_le_one hr₀_pos] <;> linarith
      exact ⟨h1, h2⟩
    · rintro ⟨hz1, hz2⟩
      have h_left : x₀ ≤ x₀ + r₀ * z := by
        have h : 0 ≤ r₀ * z := by positivity
        linarith
      have h_right : x₀ + r₀ * z ≤ x₀ + r₀ := by
        have h : r₀ * z ≤ r₀ := by
          calc r₀ * z ≤ r₀ * 1 := by gcongr
            _ = r₀ := by ring
        linarith
      refine ⟨x₀ + r₀ * z, ⟨h_left, h_right⟩, ?_⟩
      have h_eq : (x₀ + r₀ * z - x₀) / r₀ = z := by
        have h : (x₀ + r₀ * z - x₀) = r₀ * z := by ring
        rw [h]; field_simp [hr₀_pos.ne'] <;> ring
      exact h_eq
  have h_preimage_all : h ⁻¹' (Set.Icc (0 : ℝ) 1) = I₀ := by
    have h1 : h ⁻¹' (h '' I₀) = I₀ := Set.preimage_image_eq I₀ h_inj
    rw [h_image] at h1
    exact h1
  have hν_univ : ν Set.univ = 1 := by
    have h1 : μ_map Set.univ = μ I₀ := by
      rw [Measure.map_apply h_meas MeasurableSet.univ]
      <;> simp [I₀, Measure.restrict_apply] <;> rfl
    have h2 : (μ I₀)⁻¹ * μ I₀ = 1 := ENNReal.inv_mul_cancel hμI₀_ne_zero hμI₀_ne_top
    have h3 : ν Set.univ = (μ I₀)⁻¹ * μ_map Set.univ := by
      simp [ν, Measure.smul_apply] <;> rfl
    rw [h3, h1, h2]
  have h_restrict_support : (μ.restrict I₀).support ⊆ I₀ := by
    have h1 : (μ.restrict I₀).support ⊆ closure I₀ ∩ μ.support :=
      Measure.support_restrict_subset
    have h2 : closure I₀ ∩ μ.support ⊆ closure I₀ := by
      intro x hx; exact hx.1
    have h3 : (μ.restrict I₀).support ⊆ closure I₀ := h1.trans h2
    have h4 : closure I₀ = I₀ := IsClosed.closure_eq isClosed_Icc
    rw [h4] at h3; exact h3
  have hμmap_support : μ_map.support ⊆ Set.Icc (0 : ℝ) 1 := by
    have h5 : μ_map (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
      rw [Measure.map_apply h_meas (measurableSet_Icc.compl)]
      have h6 : h ⁻¹' ((Set.Icc (0 : ℝ) 1)ᶜ) = (h ⁻¹' (Set.Icc (0 : ℝ) 1))ᶜ := by
        rw [preimage_compl]
      rw [h6, h_preimage_all]
      have h7 : (μ.restrict I₀) (I₀ᶜ) = 0 := by
        have h8 : (μ.restrict I₀) (I₀ᶜ) = μ (I₀ᶜ ∩ I₀) := by
          rw [Measure.restrict_apply (measurableSet_Icc.compl)] <;> rfl
        rw [h8]
        have h9 : I₀ᶜ ∩ I₀ = ∅ := by ext x; simp [I₀] <;> tauto
        rw [h9] <;> simp
      exact h7
    have h7 : Set.Icc (0 : ℝ) 1 ∈ {t : Set ℝ | IsClosed t ∧ μ_map tᶜ = 0} :=
      ⟨isClosed_Icc, h5⟩
    rw [Measure.support_eq_sInter]
    exact Set.sInter_subset_of_mem h7
  have hc_ne_zero : (μ I₀)⁻¹ ≠ 0 := by
    intro h
    have h' : μ I₀ = ⊤ := ENNReal.inv_eq_zero.mp h
    exact hμI₀_ne_top h'
  have hν_support_eq : ν.support = μ_map.support := by
    ext x
    constructor
    · intro hx
      by_contra h9
      let U := μ_map.supportᶜ
      have hU_open : IsOpen U := Measure.isOpen_compl_support
      have hxU : x ∈ U := h9
      have hμU : μ_map U = 0 := Measure.measure_compl_support
      have hνU : ν U = 0 := by
        simp [ν, hμU, Measure.smul_apply] <;> rfl
      have h10 : U ⊆ ν.supportᶜ := by
        rw [Measure.compl_support_eq_sUnion]
        intro y hy
        exact ⟨U, ⟨hU_open, hνU⟩, hy⟩
      exact h10 hxU hx
    · intro hx
      by_contra h9
      let U := ν.supportᶜ
      have hU_open : IsOpen U := Measure.isOpen_compl_support
      have hxU : x ∈ U := h9
      have hνU : ν U = 0 := Measure.measure_compl_support
      have h11 : (μ I₀)⁻¹ * μ_map U = 0 := by simpa [ν, Measure.smul_apply] using hνU
      have h12 : μ_map U = 0 := (mul_eq_zero.mp h11).resolve_left hc_ne_zero
      have h13 : U ⊆ μ_map.supportᶜ := by
        rw [Measure.compl_support_eq_sUnion]
        intro y hy
        exact ⟨U, ⟨hU_open, h12⟩, hy⟩
      exact h13 hxU hx
  have hν_supp : ν.support ⊆ Set.Icc 0 1 := by
    rw [hν_support_eq]
    exact hμmap_support
  have hκ2_pos : 0 < κ / 2 := by linarith
  have hC2_pos : 0 < (2 : ℝ) ^ (κ / 2) := by positivity
  have hC_pos : 0 < C := hμ_allscale.2.2.1
  have h_frost_ball := hμ_allscale.2.2.2

  have hν_formula : ∀ (S : Set ℝ), MeasurableSet S → S ⊆ Set.Icc (0 : ℝ) 1 →
      ν S = (μ I₀)⁻¹ * μ (h ⁻¹' S) := by
    intro S hS_meas hS_sub
    have h_preimage_sub : h ⁻¹' S ⊆ I₀ := by
      intro x hx
      have h1 : h x ∈ S := hx
      have h2 : h x ∈ Set.Icc (0 : ℝ) 1 := hS_sub h1
      have h3 : x ∈ h ⁻¹' (Set.Icc (0 : ℝ) 1) := h2
      have h4 : h ⁻¹' (Set.Icc (0 : ℝ) 1) = I₀ := by
        have h5 : h ⁻¹' (h '' I₀) = I₀ := Set.preimage_image_eq I₀ h_inj
        rw [h_image] at h5; exact h5
      rw [h4] at h3; exact h3
    have h1 : μ_map S = (μ.restrict I₀) (h ⁻¹' S) := by
      rw [Measure.map_apply h_meas hS_meas]
    have h3 : h ⁻¹' S ∩ I₀ = h ⁻¹' S := by
      ext z; simp [h_preimage_sub] <;> tauto
    have h2 : (μ.restrict I₀) (h ⁻¹' S) = μ (h ⁻¹' S) := by
      have h4 : (μ.restrict I₀) (h ⁻¹' S) = μ (h ⁻¹' S ∩ I₀) :=
        Measure.restrict_apply (h_meas hS_meas)
      rw [h4, h3]
    have h3 : μ_map S = μ (h ⁻¹' S) := by
      rw [h1, h2]
    have h4 : ν S = (μ I₀)⁻¹ * μ_map S := by
      simp [ν, Measure.smul_apply] <;> rfl
    rw [h4, h3]

  have h_main : ∀ (y r : ℝ), 0 < r →
      ν (Set.Icc (y - r) (y + r)) ≤ ENNReal.ofReal ((2 ^ (κ / 2)) * r ^ (κ / 2)) := by
    intro y r hr
    let L := max (y - r) 0
    let R := min (y + r) 1
    have hL_nonneg : 0 ≤ L := by simp [L] <;> linarith
    have hR_le_one : R ≤ 1 := by simp [R] <;> linarith
    have h_clipped : Set.Icc (y - r) (y + r) ∩ Set.Icc (0 : ℝ) 1 = Set.Icc L R := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Icc, L, R]
      constructor
      · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
        have h5 : max (y - r) 0 ≤ x := by rw [max_le_iff] <;> exact ⟨h1, h3⟩
        have h6 : x ≤ min (y + r) 1 := by rw [le_min_iff] <;> exact ⟨h2, h4⟩
        exact ⟨h5, h6⟩
      · rintro ⟨h1, h2⟩
        have h3 : y - r ≤ x := le_trans (le_max_left (y - r) 0) h1
        have h4 : x ≤ y + r := le_trans h2 (min_le_left (y + r) 1)
        have h5 : 0 ≤ x := le_trans (le_max_right (y - r) 0) h1
        have h6 : x ≤ 1 := le_trans h2 (min_le_right (y + r) 1)
        exact ⟨⟨h3, h4⟩, ⟨h5, h6⟩⟩
    by_cases hLR : L ≤ R
    · have h_len : R - L ≤ 2 * r := by
        have hL1 : y - r ≤ L := by simp [L] <;> linarith
        have hR1 : R ≤ y + r := by simp [R] <;> linarith
        linarith
      have h_preimage_LR : h ⁻¹' (Set.Icc L R) = Set.Icc (x₀ + r₀ * L) (x₀ + r₀ * R) := by
        ext z; simp only [h, Set.mem_preimage, Set.mem_Icc]
        constructor
        · rintro ⟨h1, h2⟩
          have h3 : x₀ + r₀ * L ≤ z := by
            have h4 : r₀ * L ≤ z - x₀ := by
              have h5 : L ≤ (z - x₀) / r₀ := h1
              have h6 : r₀ * L ≤ r₀ * ((z - x₀) / r₀) := by gcongr
              have h7 : r₀ * ((z - x₀) / r₀) = z - x₀ := by field_simp [hr₀_pos.ne'] <;> ring
              rw [h7] at h6; exact h6
            linarith
          have h6 : z ≤ x₀ + r₀ * R := by
            have h7 : (z - x₀) / r₀ ≤ R := h2
            have h8 : z - x₀ ≤ r₀ * R := by
              have h9 : z - x₀ = r₀ * ((z - x₀) / r₀) := by field_simp [hr₀_pos.ne'] <;> ring
              rw [h9]; gcongr
            linarith
          exact ⟨h3, h6⟩
        · rintro ⟨h1, h2⟩
          have h3 : L ≤ (z - x₀) / r₀ := by
            have h4 : r₀ * L ≤ z - x₀ := by linarith
            have h5 : L = (r₀ * L) / r₀ := by field_simp [hr₀_pos.ne'] <;> ring
            rw [h5]; gcongr
          have h6 : (z - x₀) / r₀ ≤ R := by
            have h7 : z - x₀ ≤ r₀ * R := by linarith
            have h8 : (r₀ * R) / r₀ = R := by field_simp [hr₀_pos.ne'] <;> ring
            have h9 : (z - x₀) / r₀ ≤ (r₀ * R) / r₀ := by gcongr
            rw [h8] at h9; exact h9
          exact ⟨h3, h6⟩
      have h_sub : Set.Icc (x₀ + r₀ * L) (x₀ + r₀ * R) ⊆ I₀ := by
        intro z hy
        rcases hy with ⟨hyl, hyr⟩
        have h11 : 0 ≤ r₀ * L := by positivity
        have h1 : x₀ ≤ z := by linarith
        have h22 : R ≤ 1 := hR_le_one
        have h21 : r₀ * R ≤ r₀ := by
          calc r₀ * R ≤ r₀ * 1 := mul_le_mul_of_nonneg_left h22 hr₀_pos.le
               _ = r₀ := by ring
        have h2 : z ≤ x₀ + r₀ := by linarith
        exact ⟨h1, h2⟩
      let J := Set.Icc (x₀ + r₀ * L) (x₀ + r₀ * R)
      have h_bound : μ J ≤ μ I₀ * ENNReal.ofReal ((2 * r) ^ (κ / 2)) :=
        all_scale_renormalize_interval_bound hδ hκ_pos hC_pos hr₀_pos hr₀_le_one hr
          hμI₀_ne_zero hμI₀_ne_top h_frost_ball h_density h_self_sim h_small
          hLR hL_nonneg hR_le_one h_len h_sub
      have hLR_sub : Set.Icc L R ⊆ Set.Icc (y - r) (y + r) := by
        intro z hz
        have h1 : y - r ≤ z := le_trans (le_max_left (y - r) 0) hz.1
        have h2 : z ≤ y + r := le_trans hz.2 (min_le_left (y + r) 1)
        exact ⟨h1, h2⟩
      have h11 : ν (Set.Icc (y - r) (y + r)) = (μ I₀)⁻¹ * μ J := by
        have h_disj : (Set.Icc (y - r) (y + r)) \ (Set.Icc L R) ⊆ (ν.support)ᶜ := by
          intro z hz
          have h2 : z ∉ Set.Icc (0 : ℝ) 1 := by
            intro h3
            have h4 : z ∈ Set.Icc (y - r) (y + r) ∩ Set.Icc (0 : ℝ) 1 := ⟨hz.1, h3⟩
            rw [h_clipped] at h4
            exact hz.2 h4
          exact fun h5 => h2 (hν_supp h5)
        have h3 : ν ((Set.Icc (y - r) (y + r)) \ (Set.Icc L R)) = 0 :=
          measure_mono_null h_disj Measure.measure_compl_support
        have h4 : Set.Icc (y - r) (y + r) = (Set.Icc L R) ∪ ((Set.Icc (y - r) (y + r)) \ (Set.Icc L R)) := by
          ext z
          simp only [Set.mem_union, Set.mem_diff]
          constructor
          · intro hz
            by_cases h : z ∈ Set.Icc L R
            · exact Or.inl h
            · exact Or.inr ⟨hz, h⟩
          · rintro (h | h)
            · exact hLR_sub h
            · exact h.1
        have h5 : Disjoint (Set.Icc L R) ((Set.Icc (y - r) (y + r)) \ (Set.Icc L R)) := by
          rw [Set.disjoint_left]
          intro z hz1 hz2
          exact hz2.2 hz1
        have h_meas2 : MeasurableSet ((Set.Icc (y - r) (y + r)) \ (Set.Icc L R)) :=
          measurableSet_Icc.diff measurableSet_Icc
        have h12 : ν (Set.Icc (y - r) (y + r)) = ν (Set.Icc L R) := by
          rw [h4, measure_union h5 h_meas2, h3, add_zero]
        rw [h12]
        have hLR_in01 : Set.Icc L R ⊆ Set.Icc (0 : ℝ) 1 := by
          intro z hz
          have h1 : 0 ≤ z := by linarith [hL_nonneg, hz.1]
          have h2 : z ≤ 1 := by linarith [hR_le_one, hz.2]
          exact ⟨h1, h2⟩
        have h13 := hν_formula (Set.Icc L R) measurableSet_Icc hLR_in01
        rw [h13, h_preimage_LR]
      rw [h11]
      have h12 : (μ I₀)⁻¹ * μ J ≤ (μ I₀)⁻¹ * (μ I₀ * ENNReal.ofReal ((2 * r) ^ (κ / 2))) := by gcongr
      have h_cancel : (μ I₀)⁻¹ * (μ I₀ * ENNReal.ofReal ((2 * r) ^ (κ / 2))) = ENNReal.ofReal ((2 * r) ^ (κ / 2)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hμI₀_ne_zero hμI₀_ne_top, one_mul]
      rw [h_cancel] at h12
      have h13 : (2 * r) ^ (κ / 2) = (2 ^ (κ / 2)) * r ^ (κ / 2) := by
        have hr_nonneg : 0 ≤ r := by linarith
        rw [← Real.mul_rpow (by positivity) hr_nonneg] <;> ring
      rw [h13] at h12
      exact h12
    · have h_empty : Set.Icc (y - r) (y + r) ∩ Set.Icc (0 : ℝ) 1 = ∅ := by
        rw [h_clipped]; rw [Set.Icc_eq_empty_of_lt] <;> linarith
      have h_disj : Disjoint (Set.Icc (y - r) (y + r)) (Set.Icc (0 : ℝ) 1) := by
        rw [disjoint_iff_inter_eq_empty]; exact h_empty
      have h14 : Set.Icc (y - r) (y + r) ⊆ (ν.support)ᶜ := by
        intro x hx; intro hxs; have h16 : x ∈ Set.Icc (0 : ℝ) 1 := hν_supp hxs; exact h_disj.le_bot ⟨hx, h16⟩
      have h17 : ν (Set.Icc (y - r) (y + r)) ≤ ν (ν.supportᶜ) := measure_mono h14
      have h18 : ν (ν.supportᶜ) = 0 := Measure.measure_compl_support
      have h19 : ν (Set.Icc (y - r) (y + r)) = 0 := by rw [h18] at h17; simpa using h17
      rw [h19] <;> positivity

  -- Support provenance: z ∈ ν.support → x₀ + r₀*z ∈ μ.support
  have hν_prov : ∀ (z : ℝ), z ∈ ν.support → x₀ + r₀ * z ∈ μ.support := by
    let h_homeo : Homeomorph ℝ ℝ :=
      { toFun := h
        invFun := fun z => x₀ + r₀ * z
        left_inv := by intro y; simp [h]; field_simp [hr₀_pos.ne'] <;> ring
        right_inv := by intro z; simp [h]; field_simp [hr₀_pos.ne'] <;> ring
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    intro z hz
    have hz' : z ∈ μ_map.support := by
      rw [hν_support_eq] at hz; exact hz
    by_contra h_y_not_supp
    have h1 : ∃ (V : Set ℝ), IsOpen V ∧ (x₀ + r₀ * z) ∈ V ∧ μ V = 0 := by
      have h_not_in : (x₀ + r₀ * z) ∈ μ.supportᶜ := h_y_not_supp
      rw [Measure.compl_support_eq_sUnion] at h_not_in
      rcases h_not_in with ⟨V, ⟨hV_open, hV_null⟩, hV_mem⟩
      exact ⟨V, hV_open, hV_mem, hV_null⟩
    rcases h1 with ⟨V, hV_open, hV_mem, hV_null⟩
    let U := h '' V
    have hU_open : IsOpen U := h_homeo.isOpenMap V hV_open
    have hz_U : z ∈ U := by
      have h2 : h (x₀ + r₀ * z) = z := by
        simp [h] <;> field_simp [hr₀_pos.ne'] <;> ring
      exact ⟨x₀ + r₀ * z, hV_mem, h2⟩
    have h3 : μ_map U = 0 := by
      rw [Measure.map_apply h_meas hU_open.measurableSet]
      have h4 : h ⁻¹' U = V := Set.preimage_image_eq V h_inj
      rw [h4]
      have h5 : (μ.restrict I₀) V = 0 := by
        rw [Measure.restrict_apply hV_open.measurableSet]
        have h7 : V ∩ I₀ ⊆ V := by
          intro x hx
          exact hx.1
        exact MeasureTheory.measure_mono_null h7 hV_null
      exact h5
    have h4 : U ⊆ μ_map.supportᶜ := by
      rw [Measure.compl_support_eq_sUnion]
      intro y hy
      exact ⟨U, ⟨hU_open, h3⟩, hy⟩
    exact h4 hz_U hz'

  exact ⟨ν, hν_univ, hν_supp, ⟨hν_univ, hκ2_pos, hC2_pos, h_main⟩, hν_prov⟩

end WeakTwoEndsSumProduct
