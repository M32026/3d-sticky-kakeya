module

/-
# Generalized Average Projection Energy Bound

Generalizes `average_projection_energy_bound` from the fixed box `[-3,3]^2`
(diameter `6√2`) to an arbitrary box `[-R,R]^2` (diameter `2R√2`) for `R ≥ 1`.

## Main results
- `average_projection_energy_bound_gen`: R-generalized averaging bound

## Whiteprint node
`exact_endgame_composition`
-/

public import MyLeanRepo.Energy.AverageProjectionEnergy
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Classical

namespace robust_projection_main

/-! ## Generalized helper inequalities -/

/-- Generalized: `(√5)^s * (1 + C_μ * s/(τ-s)) ≤ C_Frost(D)`. -/
lemma sqrt5_C_Frost_bound_gen (s τ C_μ D : ℝ) (hs_pos : 0 < s) (hst : s < τ)
    (hCμ_pos : 0 < C_μ) (h_sqrt5_le : Real.sqrt 5 ≤ D) (hD_pos : 0 < D)
    (C_Frost : ℝ) (hC_Frost_def : C_Frost = (C_μ + 1) * D ^ s * (1 + s / (τ - s))) :
    (Real.sqrt 5) ^ s * (1 + C_μ * s / (τ - s)) ≤ C_Frost := by
  rw [hC_Frost_def]
  have h16 : (Real.sqrt 5) ^ s ≤ D ^ s :=
    Real.rpow_le_rpow (by positivity) h_sqrt5_le hs_pos.le
  have h19 : 0 ≤ C_μ * s / (τ - s) := by positivity
  have h20 : 1 ≤ C_μ + 1 := by linarith
  have h21 : 0 ≤ s / (τ - s) := by positivity
  have h22 : 1 + C_μ * s / (τ - s) ≤ (C_μ + 1) * (1 + s / (τ - s)) := by
    have h23 : 0 ≤ C_μ := by linarith
    have h24 : 0 ≤ s / (τ - s) := by positivity
    have h : (C_μ + 1) * (1 + s / (τ - s)) - (1 + C_μ * s / (τ - s)) = C_μ + s / (τ - s) := by ring
    have h5 : 0 ≤ C_μ + s / (τ - s) := by linarith
    linarith [h, h5]
  have h24 : (Real.sqrt 5) ^ s * (1 + C_μ * s / (τ - s)) ≤
      D ^ s * (1 + C_μ * s / (τ - s)) := by gcongr
  have h25 : D ^ s * (1 + C_μ * s / (τ - s)) ≤
      D ^ s * ((C_μ + 1) * (1 + s / (τ - s))) := by gcongr
  have h26 : D ^ s * ((C_μ + 1) * (1 + s / (τ - s))) =
      (C_μ + 1) * D ^ s * (1 + s / (τ - s)) := by ring
  rw [h26] at h25
  exact le_trans h24 h25

/-- Generalized: `1 + C_μ * s/(τ-s) ≤ C_Frost(D) * v^(-s)` when `0 < v ≤ D`. -/
lemma C_Frost_large_v0_bound_gen (s τ C_μ v D : ℝ) (hs_pos : 0 < s) (hst : s < τ)
    (hCμ_pos : 0 < C_μ) (hv_pos : 0 < v) (hv_bound : v ≤ D) (hD_pos : 0 < D)
    (C_Frost : ℝ) (hC_Frost_def : C_Frost = (C_μ + 1) * D ^ s * (1 + s / (τ - s))) :
    1 + C_μ * s / (τ - s) ≤ C_Frost * v ^ (-s) := by
  have h_v_nonneg : 0 ≤ v := hv_pos.le
  have h14 : v ^ (-s) ≥ D ^ (-s) := by
    have h141 : v ^ s ≤ D ^ s := Real.rpow_le_rpow h_v_nonneg hv_bound hs_pos.le
    have h142 : 0 < v ^ s := by positivity
    have h143 : 0 < D ^ s := by positivity
    have h144 : (D ^ s)⁻¹ ≤ (v ^ s)⁻¹ := by gcongr
    have h145 : v ^ (-s) = (v ^ s)⁻¹ := by rw [Real.rpow_neg] <;> linarith
    have h146 : D ^ (-s) = (D ^ s)⁻¹ := by rw [Real.rpow_neg] <;> linarith
    rw [h145, h146]; exact h144
  have hC_Frost_pos : 0 < C_Frost := by rw [hC_Frost_def] <;> positivity
  have h17 : C_Frost * v ^ (-s) ≥ C_Frost * D ^ (-s) :=
    mul_le_mul_of_nonneg_left h14 hC_Frost_pos.le
  have h18 : C_Frost * D ^ (-s) = (C_μ + 1) * (1 + s / (τ - s)) := by
    have h19 : 0 < D := hD_pos
    have h20 : D ^ s * D ^ (-s) = 1 := by
      have h_pos : 0 < D ^ s := by positivity
      have h_neg : D ^ (-s) = (D ^ s)⁻¹ := by rw [Real.rpow_neg] <;> linarith
      rw [h_neg]; field_simp [h_pos.ne']
    calc
      C_Frost * D ^ (-s)
        = ((C_μ + 1) * D ^ s * (1 + s / (τ - s))) * D ^ (-s) := by rw [hC_Frost_def]
      _ = (C_μ + 1) * (D ^ s * D ^ (-s)) * (1 + s / (τ - s)) := by ring
      _ = (C_μ + 1) * (1 + s / (τ - s)) := by rw [h20] <;> ring
  have h20 : 0 ≤ s / (τ - s) := by positivity
  have h22 : 1 + C_μ * s / (τ - s) ≤ (C_μ + 1) * (1 + s / (τ - s)) := by
    have h23 : 0 ≤ C_μ := by linarith
    have h24 : 0 ≤ s / (τ - s) := by positivity
    have h : (C_μ + 1) * (1 + s / (τ - s)) - (1 + C_μ * s / (τ - s)) = C_μ + s / (τ - s) := by ring
    have h5 : 0 ≤ C_μ + s / (τ - s) := by linarith
    linarith [h, h5]
  calc 1 + C_μ * s / (τ - s)
      ≤ (C_μ + 1) * (1 + s / (τ - s)) := h22
    _ = C_Frost * D ^ (-s) := h18.symm
    _ ≤ C_Frost * v ^ (-s) := h17

/-- Simple bound: `(√5)^s ≤ C_Frost(D)`. -/
lemma sqrt5_le_C_Frost_gen (s τ C_μ D : ℝ) (hs_pos : 0 < s) (hst : s < τ)
    (hCμ_pos : 0 < C_μ) (h_sqrt5_le : Real.sqrt 5 ≤ D) (hD_pos : 0 < D)
    (C_Frost : ℝ) (hC_Frost_def : C_Frost = (C_μ + 1) * D ^ s * (1 + s / (τ - s))) :
    (Real.sqrt 5) ^ s ≤ C_Frost := by
  rw [hC_Frost_def]
  have h1 : (Real.sqrt 5) ^ s ≤ D ^ s :=
    Real.rpow_le_rpow (by positivity) h_sqrt5_le hs_pos.le
  have h2 : 0 ≤ D ^ s := by positivity
  have h3 : 1 ≤ C_μ + 1 := by linarith
  have h4 : 0 ≤ s / (τ - s) := by positivity
  have h5 : 1 ≤ 1 + s / (τ - s) := by linarith
  have h6 : D ^ s ≤ (C_μ + 1) * D ^ s := by
    have h_pos : 0 ≤ D ^ s := by positivity
    nlinarith
  have h7 : 0 ≤ (C_μ + 1) * D ^ s := by positivity
  have h8 : (C_μ + 1) * D ^ s ≤ (C_μ + 1) * D ^ s * (1 + s / (τ - s)) :=
    le_mul_of_one_le_right h7 h5
  exact le_trans h1 (le_trans h6 h8)

/-! ## Generalized directional energy integral -/

/-- Generalized `directional_energy_integral` with diameter bound `D` instead of `6√2`.
Requires `D ≥ 1` and `√5 ≤ D`. -/
lemma directional_energy_integral_gen
    {δ τ κ C_μ D : ℝ} {μ : Measure ℝ}
    (hτ_pos : 0 < τ) (hκ_pos : 0 < κ) (hτ_gt_2κ : τ > 2 * κ)
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1) (hCμ_pos : 0 < C_μ)
    (hμ_frost : IsDirectionFrostman δ τ C_μ μ)
    (hμ_support_bdd : μ.support ⊆ Set.Icc 0 1)
    (hD_ge_one : 1 ≤ D) (h_sqrt5_le : Real.sqrt 5 ≤ D)
    {v0 v1 : ℝ} (hv_ne_zero : (v0, v1) ≠ (0, 0))
    (hv_bound : Real.sqrt (v0^2 + v1^2) ≤ D) :
    ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-2 * κ)) ∂μ ≤
      ENNReal.ofReal ((C_μ + 1) * D ^ (2 * κ) * (1 + (2 * κ) / (τ - 2 * κ))) *
      ENNReal.ofReal ((max (Real.sqrt (v0^2 + v1^2)) δ) ^ (-2 * κ)) := by
  set s : ℝ := 2 * κ with hs_def
  have hs_pos : 0 < s := by positivity
  have hst : s < τ := by linarith
  set v : ℝ := Real.sqrt (v0^2 + v1^2) with hv_def
  have h_v_nonneg : 0 ≤ v := Real.sqrt_nonneg _
  have h_v2 : v^2 = v0^2 + v1^2 := by rw [hv_def, Real.sq_sqrt (by positivity)]
  have hτ_sub_pos : 0 < τ - s := by linarith
  have hD_pos : 0 < D := by linarith
  let C_Frost : ℝ := (C_μ + 1) * D ^ s * (1 + s / (τ - s))
  have hC_Frost_pos : 0 < C_Frost := by positivity
  have hC_Frost_ge_one : 1 ≤ C_Frost := by
    dsimp only [C_Frost]
    have h1 : 1 ≤ C_μ + 1 := by linarith
    have h2 : 1 ≤ D ^ s := Real.one_le_rpow hD_ge_one hs_pos.le
    have h3 : 0 ≤ s / (τ - s) := by positivity
    have h4 : 1 ≤ 1 + s / (τ - s) := by linarith
    have h5 : 0 ≤ (C_μ + 1) * D ^ s := by positivity
    have h6 : 1 ≤ (C_μ + 1) * D ^ s := by
      have h_pos2 : 0 ≤ D ^ s := by positivity
      have h61 : 1 * 1 ≤ (C_μ + 1) * D ^ s := mul_le_mul h1 h2 (by norm_num) (by linarith)
      simpa using h61
    have h7 : (C_μ + 1) * D ^ s ≤ (C_μ + 1) * D ^ s * (1 + s / (τ - s)) :=
      le_mul_of_one_le_right h5 h4
    exact le_trans h6 h7
  have h_goal : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ ≤
      ENNReal.ofReal C_Frost * ENNReal.ofReal ((max v δ) ^ (-s)) := by
    by_cases h_v_leδ : v ≤ δ
    · have h_max : max v δ = δ := by rw [max_eq_right] <;> linarith
      have h_bound : ∀ y, (max (|v0 * y + v1|) δ) ^ (-s) ≤ δ ^ (-s) := by
        intro y
        have h5 : δ ≤ max (|v0 * y + v1|) δ := le_max_right _ _
        have h6 : 0 < δ := hδ_pos
        have h7 : 0 ≤ max (|v0 * y + v1|) δ := by positivity
        have h8 : δ ^ s ≤ (max (|v0 * y + v1|) δ) ^ s :=
          Real.rpow_le_rpow h6.le h5 (by linarith)
        have h9 : 0 < δ ^ s := by positivity
        have h10 : ((max (|v0 * y + v1|) δ) ^ s)⁻¹ ≤ (δ ^ s)⁻¹ := by gcongr
        have h11 : (max (|v0 * y + v1|) δ) ^ (-s) = ((max (|v0 * y + v1|) δ) ^ s)⁻¹ := by
          rw [Real.rpow_neg] <;> linarith
        have h12 : δ ^ (-s) = (δ ^ s)⁻¹ := by rw [Real.rpow_neg] <;> linarith
        rw [h11, h12]; exact h10
      have h7 : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ ≤
          ENNReal.ofReal (δ ^ (-s)) := by
        have h8 : ∀ y, ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ≤
            ENNReal.ofReal (δ ^ (-s)) := by
          intro y; exact ENNReal.ofReal_le_ofReal (h_bound y)
        have h9 : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ ≤
            ∫⁻ (y : ℝ), ENNReal.ofReal (δ ^ (-s)) ∂μ := lintegral_mono h8
        have h10 : ∫⁻ (y : ℝ), ENNReal.ofReal (δ ^ (-s)) ∂μ = ENNReal.ofReal (δ ^ (-s)) := by
          rw [lintegral_const, hμ_frost.1] <;> simp
        rw [h10] at h9; exact h9
      rw [h_max]
      have h9 : ENNReal.ofReal (δ ^ (-s)) ≤
          ENNReal.ofReal C_Frost * ENNReal.ofReal (δ ^ (-s)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by
          have h10 : 0 < δ ^ (-s) := by positivity
          nlinarith [hC_Frost_ge_one])
      exact le_trans h7 h9
    have h_v_gtδ : δ < v := by linarith
    have h_v_pos : 0 < v := by linarith
    have h_max : max v δ = v := by rw [max_eq_left] <;> linarith
    rw [h_max]
    by_cases h_v0 : v0 = 0
    · have h_v1_ne_zero : v1 ≠ 0 := by
        intro h; simp [h_v0, h] at hv_ne_zero <;> tauto
      have h_v_eq : v = |v1| := by
        rw [hv_def, h_v0]; simp [Real.sqrt_sq_eq_abs] <;> ring
      have h_abs : ∀ y, |v0 * y + v1| = |v1| := by
        intro y; rw [h_v0]; ring_nf
      have h_gtδ : |v1| > δ := by linarith [h_v_eq]
      have h_max2 : ∀ y, max (|v0 * y + v1|) δ = |v1| := by
        intro y; rw [h_abs y, max_eq_left] <;> linarith
      have h10 : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ =
          ENNReal.ofReal (|v1| ^ (-s)) := by
        simp_rw [h_max2]
        rw [lintegral_const, hμ_frost.1] <;> simp
      rw [h10]
      have h11 : |v1| = v := by linarith [h_v_eq]
      rw [h11]
      have h12 : ENNReal.ofReal (v ^ (-s)) ≤
          ENNReal.ofReal C_Frost * ENNReal.ofReal (v ^ (-s)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by
          have h13 : 0 < v ^ (-s) := by positivity
          nlinarith [hC_Frost_ge_one])
      exact h12
    · have h_v0_ne_zero : v0 ≠ 0 := h_v0
      set y0 : ℝ := -v1 / v0 with hy0_def
      have h_abs2 : ∀ y : ℝ, |v0 * y + v1| = |v0| * dist y y0 := by
        intro y
        have h6 : v0 * y + v1 = v0 * (y - y0) := by
          dsimp only [y0]; field_simp [h_v0_ne_zero] <;> ring
        rw [h6, abs_mul] <;> rfl
      by_cases h_small_v0 : |v0| < v / Real.sqrt 5
      · have h_sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
        have h1 : v1^2 > 4 * v^2 / 5 := by
          have h2 : v0^2 < v^2 / 5 := by
            have h3 : |v0| < v / Real.sqrt 5 := h_small_v0
            have h4 : |v0| ^ 2 < (v / Real.sqrt 5) ^ 2 := by gcongr
            have h5 : |v0| ^ 2 = v0^2 := by simp
            have h6 : (v / Real.sqrt 5) ^ 2 = v^2 / 5 := by
              calc (v / Real.sqrt 5) ^ 2
                  = v^2 / (Real.sqrt 5)^2 := by ring
                _ = v^2 / 5 := by rw [h_sqrt5_sq]
            rw [h5, h6] at h4; exact h4
          nlinarith [h_v2]
        have h_v1_gt : |v1| > 2 * v / Real.sqrt 5 := by
          have h_pos : 0 < 2 * v / Real.sqrt 5 := by positivity
          have h9 : |v1| ^ 2 > (2 * v / Real.sqrt 5) ^ 2 := by
            have h10 : |v1| ^ 2 = v1^2 := by simp
            have h11 : (2 * v / Real.sqrt 5) ^ 2 = 4 * v^2 / 5 := by
              calc (2 * v / Real.sqrt 5) ^ 2
                  = 4 * v^2 / (Real.sqrt 5)^2 := by ring
                _ = 4 * v^2 / 5 := by rw [h_sqrt5_sq]
            rw [h10, h11]; exact h1
          nlinarith [abs_nonneg v1]
        have h_ge : ∀ y ∈ Set.Icc (0 : ℝ) 1, |v0 * y + v1| ≥ v / Real.sqrt 5 := by
          intro y hy
          have h_y1 : 0 ≤ y := hy.1
          have h_y2 : y ≤ 1 := hy.2
          have h_tri : |v1| ≤ |v0 * y + v1| + |v0 * y| := by
            calc |v1| = |(v0 * y + v1) - v0 * y| := by ring_nf
                 _ ≤ |v0 * y + v1| + |v0 * y| := by exact abs_sub _ _
          have h_absy : |v0 * y| = |v0| * y := by
            rw [abs_mul, abs_of_nonneg h_y1] <;> ring
          have h_main : |v0 * y + v1| ≥ |v1| - |v0| * y := by linarith
          have h13 : |v0| * y ≤ |v0| := by
            calc |v0| * y ≤ |v0| * 1 := by gcongr
                 _ = |v0| := by ring
          have h14 : |v1| - |v0| * y ≥ |v1| - |v0| := by linarith
          set q : ℝ := v / Real.sqrt 5 with hq
          have h15 : |v1| > 2 * q := by
            have h151 : |v1| > 2 * v / Real.sqrt 5 := h_v1_gt
            have h152 : 2 * v / Real.sqrt 5 = 2 * q := by simp [hq] <;> ring
            rw [h152] at h151; exact h151
          have h16 : |v0| < q := h_small_v0
          have h17 : |v1| - |v0| > q := by linarith
          have h18 : |v1| - |v0| * y ≥ q := by linarith
          linarith
        have h_support_ae : ∀ᵐ y ∂μ, y ∈ μ.support := by
          have h : μ (μ.supportᶜ) = 0 := MeasureTheory.Measure.measure_compl_support
          have h' : μ {y | y ∉ μ.support} = 0 := by
            have h_eq : {y | y ∉ μ.support} = μ.supportᶜ := by ext y; simp
            rw [h_eq]; exact h
          rw [ae_iff]; exact h'
        have h_support : ∀ᵐ y ∂μ, y ∈ Set.Icc (0 : ℝ) 1 := by
          filter_upwards [h_support_ae] with y hy
          exact hμ_frost.2.1 hy
        have h_bound3 : ∀ᵐ y ∂μ,
            ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ≤
            ENNReal.ofReal ((Real.sqrt 5 / v) ^ s) := by
          filter_upwards [h_support] with y hy
          have h4 : |v0 * y + v1| ≥ v / Real.sqrt 5 := h_ge y hy
          have h6 : max (|v0 * y + v1|) δ ≥ v / Real.sqrt 5 := by
            have h7 : max (|v0 * y + v1|) δ ≥ |v0 * y + v1| := le_max_left _ _
            linarith
          have h_v_sqrt5_pos : 0 < v / Real.sqrt 5 := by positivity
          have h_max_nonneg : 0 ≤ max (|v0 * y + v1|) δ := by positivity
          have h9 : (v / Real.sqrt 5) ^ s ≤ (max (|v0 * y + v1|) δ) ^ s :=
            Real.rpow_le_rpow h_v_sqrt5_pos.le h6 (by linarith)
          have h10 : 0 < (v / Real.sqrt 5) ^ s := by positivity
          have h11 : ((max (|v0 * y + v1|) δ) ^ s)⁻¹ ≤ ((v / Real.sqrt 5) ^ s)⁻¹ := by gcongr
          have h12 : (max (|v0 * y + v1|) δ) ^ (-s) = ((max (|v0 * y + v1|) δ) ^ s)⁻¹ := by
            rw [Real.rpow_neg] <;> linarith
          have h13 : (v / Real.sqrt 5) ^ (-s) = ((v / Real.sqrt 5) ^ s)⁻¹ := by
            rw [Real.rpow_neg] <;> linarith
          have h14 : (max (|v0 * y + v1|) δ) ^ (-s) ≤ (v / Real.sqrt 5) ^ (-s) := by
            rw [h12, h13]; exact h11
          have h15 : (v / Real.sqrt 5) ^ (-s) = (Real.sqrt 5 / v) ^ s := by
            have h16 : v / Real.sqrt 5 = (Real.sqrt 5 / v)⁻¹ := by
              field_simp [h_v_pos.ne'] <;> ring
            rw [h16]
            have h17 : 0 < Real.sqrt 5 / v := by positivity
            have h18 : (Real.sqrt 5 / v)⁻¹ ^ (-s) = ((Real.sqrt 5 / v) ^ (-s))⁻¹ := by
              rw [Real.inv_rpow] <;> linarith
            rw [h18]
            have h19 : (Real.sqrt 5 / v) ^ (-s) = ((Real.sqrt 5 / v) ^ s)⁻¹ := by
              rw [Real.rpow_neg] <;> linarith
            rw [h19] <;> field_simp
          rw [h15] at h14
          exact ENNReal.ofReal_le_ofReal h14
        have h9_int : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ ≤
            ∫⁻ (y : ℝ), ENNReal.ofReal ((Real.sqrt 5 / v) ^ s) ∂μ :=
          lintegral_mono_ae h_bound3
        have h9_const : ∫⁻ (y : ℝ), ENNReal.ofReal ((Real.sqrt 5 / v) ^ s) ∂μ =
            ENNReal.ofReal ((Real.sqrt 5 / v) ^ s) := by
          rw [lintegral_const, hμ_frost.1] <;> simp
        have h9 : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ ≤
            ENNReal.ofReal ((Real.sqrt 5 / v) ^ s) := by
          rw [h9_const] at h9_int; exact h9_int
        have h10 : (Real.sqrt 5 / v) ^ s = (Real.sqrt 5) ^ s * v ^ (-s) := by
          have h_sqrt5_pos : 0 < Real.sqrt 5 := by positivity
          have h1 : (Real.sqrt 5 / v) ^ s = (Real.sqrt 5 * v⁻¹) ^ s := by
            have h_eq : Real.sqrt 5 / v = Real.sqrt 5 * v⁻¹ := by rw [div_eq_mul_inv]
            rw [h_eq]
          rw [h1]
          have h2 : (Real.sqrt 5 * v⁻¹) ^ s = (Real.sqrt 5) ^ s * v⁻¹ ^ s := by
            have h_v_inv_nonneg : 0 ≤ v⁻¹ := by positivity
            rw [Real.mul_rpow (by positivity) h_v_inv_nonneg]
          rw [h2]
          have h3 : v⁻¹ ^ s = v ^ (-s) := by
            have h31 : v⁻¹ ^ s = (v ^ s)⁻¹ := by rw [Real.inv_rpow] <;> linarith
            have h32 : v ^ (-s) = (v ^ s)⁻¹ := by rw [Real.rpow_neg] <;> linarith
            rw [h31, ←h32]
          rw [h3]
        rw [h10] at h9
        have h11 : (Real.sqrt 5) ^ s ≤ C_Frost :=
          sqrt5_le_C_Frost_gen s τ C_μ D hs_pos hst hCμ_pos h_sqrt5_le hD_pos C_Frost rfl
        have h14 : ENNReal.ofReal ((Real.sqrt 5) ^ s * v ^ (-s)) ≤
            ENNReal.ofReal C_Frost * ENNReal.ofReal (v ^ (-s)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          have h15 : 0 ≤ v ^ (-s) := by positivity
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h11 h15)
        exact le_trans h9 h14
      · have h_large_v0 : |v0| ≥ v / Real.sqrt 5 := by linarith
        by_cases h_v0_le1 : |v0| ≤ 1
        · set ε : ℝ := δ / |v0| with hε_def
          have hε_pos : 0 < ε := by positivity
          have hδ_le_ε : δ ≤ ε := by
            dsimp only [ε]
            have h4 : 0 < |v0| := abs_pos.mpr h_v0_ne_zero
            have h5 : |v0| ≤ 1 := h_v0_le1
            have h6 : δ / |v0| ≥ δ / 1 := by gcongr
            simpa using h6
          have h_factor : ∀ y, max (|v0 * y + v1|) δ = |v0| * max (dist y y0) ε := by
            intro y
            rw [h_abs2 y]
            have h4 : 0 < |v0| := abs_pos.mpr h_v0_ne_zero
            by_cases h7 : dist y y0 ≤ δ / |v0|
            · have h8 : |v0| * dist y y0 ≤ δ := by
                calc |v0| * dist y y0 ≤ |v0| * (δ / |v0|) := by gcongr
                     _ = δ := by field_simp [h4.ne'] <;> ring
              have h9 : max (|v0| * dist y y0) δ = δ := by rw [max_eq_right h8]
              have h10 : max (dist y y0) (δ / |v0|) = δ / |v0| := by rw [max_eq_right h7]
              rw [h9, h10] <;> field_simp [h4.ne'] <;> ring
            · have h7' : dist y y0 > δ / |v0| := by exact lt_of_not_ge h7
              have h8 : |v0| * dist y y0 > δ := by
                calc |v0| * dist y y0 > |v0| * (δ / |v0|) := by gcongr
                     _ = δ := by field_simp [h4.ne'] <;> ring
              have h9 : max (|v0| * dist y y0) δ = |v0| * dist y y0 := by
                rw [max_eq_left (by linarith)]
              have h10 : max (dist y y0) (δ / |v0|) = dist y y0 := by
                rw [max_eq_left (by linarith)]
              rw [h9, h10] <;> ring
          have h5 : ∀ y, ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) =
              ENNReal.ofReal (|v0| ^ (-s)) * ENNReal.ofReal ((max (dist y y0) ε) ^ (-s)) := by
            intro y
            rw [h_factor y]
            have h6 : 0 < |v0| := abs_pos.mpr h_v0_ne_zero
            have h7 : 0 ≤ max (dist y y0) ε := by positivity
            have h8 : (|v0| * max (dist y y0) ε) ^ (-s) =
                |v0| ^ (-s) * (max (dist y y0) ε) ^ (-s) := by
              rw [Real.mul_rpow h6.le h7]
            rw [h8, ← ENNReal.ofReal_mul (by positivity)] <;> rfl
          have h10 : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ =
              ENNReal.ofReal (|v0| ^ (-s)) *
              ∫⁻ (y : ℝ), ENNReal.ofReal ((max (dist y y0) ε) ^ (-s)) ∂μ := by
            simp_rw [h5]
            rw [lintegral_const_mul] <;> fun_prop
          rw [h10]
          have h_frost := frostman_negative_power_integral hδ_pos hδ_le_one hτ_pos hs_pos hst hμ_frost y0 ε hε_pos hδ_le_ε
          have h11 : |v0| ^ (-s) ≤ (Real.sqrt 5) ^ s * v ^ (-s) := by
            have h12 : 0 < v / Real.sqrt 5 := by positivity
            have h13 : v / Real.sqrt 5 ≤ |v0| := h_large_v0
            have h14 : (v / Real.sqrt 5) ^ s ≤ |v0| ^ s :=
              Real.rpow_le_rpow h12.le h13 (by linarith)
            have h15 : 0 < (v / Real.sqrt 5) ^ s := by positivity
            have h16 : 0 < |v0| ^ s := by positivity
            have h17 : (|v0| ^ s)⁻¹ ≤ ((v / Real.sqrt 5) ^ s)⁻¹ := by gcongr
            have h18 : |v0| ^ (-s) = (|v0| ^ s)⁻¹ := by rw [Real.rpow_neg] <;> linarith
            have h19 : (v / Real.sqrt 5) ^ (-s) = ((v / Real.sqrt 5) ^ s)⁻¹ := by
              rw [Real.rpow_neg] <;> linarith
            have h20 : |v0| ^ (-s) ≤ (v / Real.sqrt 5) ^ (-s) := by
              rw [h18, h19]; exact h17
            have h21 : (v / Real.sqrt 5) ^ (-s) = (Real.sqrt 5) ^ s * v ^ (-s) :=
              rpow_div_sqrt5_identity v s (by linarith) hs_pos
            rw [h21] at h20; exact h20
          have h15 : (Real.sqrt 5) ^ s * (1 + C_μ * s / (τ - s)) ≤ C_Frost :=
            sqrt5_C_Frost_bound_gen s τ C_μ D hs_pos hst hCμ_pos h_sqrt5_le hD_pos C_Frost rfl
          have h_final_ineq : |v0| ^ (-s) * (1 + C_μ * s / (τ - s)) ≤ C_Frost * v ^ (-s) := by
            have h24 : |v0| ^ (-s) * (1 + C_μ * s / (τ - s)) ≤
                (Real.sqrt 5) ^ s * v ^ (-s) * (1 + C_μ * s / (τ - s)) := by
              gcongr <;> exact h11
            have h25 : (Real.sqrt 5) ^ s * v ^ (-s) * (1 + C_μ * s / (τ - s)) =
                v ^ (-s) * ((Real.sqrt 5) ^ s * (1 + C_μ * s / (τ - s))) := by ring
            rw [h25] at h24
            have h26 : v ^ (-s) * ((Real.sqrt 5) ^ s * (1 + C_μ * s / (τ - s))) ≤
                v ^ (-s) * C_Frost := by gcongr <;> exact h15
            have h27 : v ^ (-s) * C_Frost = C_Frost * v ^ (-s) := by ring
            rw [h27] at h26
            exact le_trans h24 h26
          calc
            ENNReal.ofReal (|v0| ^ (-s)) * ∫⁻ (y : ℝ), ENNReal.ofReal ((max (dist y y0) ε) ^ (-s)) ∂μ
              ≤ ENNReal.ofReal (|v0| ^ (-s)) * ENNReal.ofReal (1 + C_μ * s / (τ - s)) := by gcongr <;> exact h_frost
            _ = ENNReal.ofReal (|v0| ^ (-s) * (1 + C_μ * s / (τ - s))) := by
                rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
            _ ≤ ENNReal.ofReal C_Frost * ENNReal.ofReal (v ^ (-s)) := by
                rw [← ENNReal.ofReal_mul (by positivity)]
                exact ENNReal.ofReal_le_ofReal h_final_ineq
        · have h_v0_gt1 : 1 < |v0| := by linarith
          have h_ge : ∀ y, max (|v0 * y + v1|) δ ≥ max (dist y y0) δ := by
            intro y
            rw [h_abs2 y]
            have h4 : |v0| * dist y y0 ≥ dist y y0 := by
              have h5 : 1 ≤ |v0| := by linarith
              have h6 : 0 ≤ dist y y0 := dist_nonneg
              nlinarith
            have h6 : max (|v0| * dist y y0) δ ≥ max (dist y y0) δ := by
              exact max_le_max h4 (by linarith)
            exact h6
          have h10 : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ ≤
              ∫⁻ (y : ℝ), ENNReal.ofReal ((max (dist y y0) δ) ^ (-s)) ∂μ := by
            have h11 : ∀ y, (max (|v0 * y + v1|) δ) ^ (-s) ≤ (max (dist y y0) δ) ^ (-s) := by
              intro y
              have h12 : 0 ≤ max (dist y y0) δ := by positivity
              have h13 : max (dist y y0) δ ≤ max (|v0 * y + v1|) δ := h_ge y
              have h14 : (max (dist y y0) δ) ^ s ≤ (max (|v0 * y + v1|) δ) ^ s :=
                Real.rpow_le_rpow h12 h13 hs_pos.le
              have h15 : 0 < (max (dist y y0) δ) ^ s := by positivity
              have h16 : 0 < (max (|v0 * y + v1|) δ) ^ s := by positivity
              have h17 : ((max (|v0 * y + v1|) δ) ^ s)⁻¹ ≤ ((max (dist y y0) δ) ^ s)⁻¹ := by gcongr
              have h18 : (max (|v0 * y + v1|) δ) ^ (-s) = ((max (|v0 * y + v1|) δ) ^ s)⁻¹ := by
                rw [Real.rpow_neg] <;> linarith
              have h19 : (max (dist y y0) δ) ^ (-s) = ((max (dist y y0) δ) ^ s)⁻¹ := by
                rw [Real.rpow_neg] <;> linarith
              rw [h18, h19]; exact h17
            have h11' : ∀ y, ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ≤
                ENNReal.ofReal ((max (dist y y0) δ) ^ (-s)) := by
              intro y; exact ENNReal.ofReal_le_ofReal (h11 y)
            exact lintegral_mono h11'
          have h_frost := frostman_negative_power_integral hδ_pos hδ_le_one hτ_pos hs_pos hst hμ_frost y0 δ hδ_pos (by linarith)
          have h13 : 1 + C_μ * s / (τ - s) ≤ C_Frost * v ^ (-s) :=
            C_Frost_large_v0_bound_gen s τ C_μ v D hs_pos hst hCμ_pos (by linarith) hv_bound hD_pos C_Frost rfl
          calc
            ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ
              ≤ ∫⁻ (y : ℝ), ENNReal.ofReal ((max (dist y y0) δ) ^ (-s)) ∂μ := h10
            _ ≤ ENNReal.ofReal (1 + C_μ * s / (τ - s)) := h_frost
            _ ≤ ENNReal.ofReal (C_Frost * v ^ (-s)) := by exact ENNReal.ofReal_le_ofReal h13
            _ = ENNReal.ofReal C_Frost * ENNReal.ofReal (v ^ (-s)) := by
                rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
  simpa [hs_def] using h_goal

/-! ## Generalized main theorem -/

/-- Generalized average projection energy bound for box `[-R,R]^2` with `R ≥ 1`. -/
theorem average_projection_energy_bound_gen
    {δ τ κ C_μ R : ℝ} {μ : Measure ℝ}
    {ν : Measure (EuclideanSpace ℝ (Fin 2))}
    [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    (hτ_pos : 0 < τ) (hκ_pos : 0 < κ) (hτ_gt_2κ : τ > 2 * κ)
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1) (hCμ_pos : 0 < C_μ)
    (hμ_frost : IsDirectionFrostman δ τ C_μ μ)
    (hμ_support_bdd : μ.support ⊆ Set.Icc 0 1)
    (hR_ge1 : 1 ≤ R)
    (hν_support_bdd : ν.support ⊆ {p | ∀ i, p i ∈ Set.Icc (-R) R}) :
    ∫⁻ (y : ℝ), rieszEnergy (2 * κ) (hδ := hδ_pos)
        (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 0 * y + p 1) ν) ∂μ ≤
      ENNReal.ofReal (1 + (C_μ + 1) * (2 * R * Real.sqrt 2) ^ (2 * κ) *
        (1 + (2 * κ) / (τ - 2 * κ))) *
      rieszEnergy (2 * κ) (hδ := hδ_pos) ν := by
  let s : ℝ := 2 * κ
  let D : ℝ := 2 * R * Real.sqrt 2
  have hD_pos : 0 < D := by positivity
  have hD_ge_one : 1 ≤ D := by
    have h1 : 1 ≤ Real.sqrt 2 := by apply Real.le_sqrt_of_sq_le; norm_num
    have h2 : 0 < R := by linarith
    nlinarith
  have h_sqrt5_le : Real.sqrt 5 ≤ D := by
    have h4 : Real.sqrt 5 ≤ Real.sqrt 8 := Real.sqrt_le_sqrt (by norm_num)
    have h5 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
      rw [show (8 : ℝ) = 4 * 2 by norm_num]
      rw [Real.sqrt_mul (by norm_num)] <;> norm_num
    have h6 : Real.sqrt 5 ≤ 2 * Real.sqrt 2 := h4.trans_eq h5
    have h7 : 2 * Real.sqrt 2 ≤ D := by
      dsimp only [D]
      have h8 : 1 ≤ R := hR_ge1
      have h9 : 0 < Real.sqrt 2 := by positivity
      nlinarith
    linarith
  let C_dir : ℝ := (C_μ + 1) * D ^ s * (1 + s / (τ - s))
  let C_total : ℝ := 1 + C_dir
  have hτ_sub_pos : 0 < τ - s := by linarith
  have hC_dir_pos : 0 < C_dir := by positivity
  have hC_total_pos : 0 < C_total := by linarith
  have hC_total_ge_one : 1 ≤ C_total := by linarith
  let E2 := EuclideanSpace ℝ (Fin 2)
  let proj : ℝ → E2 → ℝ := fun y p => p 0 * y + p 1
  let F : ℝ → E2 → E2 → ENNReal := fun y x z =>
    ENNReal.ofReal ((max (|proj y x - proj y z|) δ) ^ (-s))
  let S : Set E2 := {p | ∀ i, p i ∈ Set.Icc (-R) R}
  have hF_eq : ∀ y x z, F y x z = energyIntegrand δ κ y x z := by
    intro y x z
    have h : proj y x - proj y z = (x 0 - z 0) * y + (x 1 - z 1) := by
      dsimp only [proj] <;> ring
    simp only [F, energyIntegrand, h] <;> rfl
  have h1 : ∀ᵐ (x : E2) ∂ν, x ∈ S := by
    have h_support : ∀ᵐ (x : E2) ∂ν, x ∈ ν.support := by
      have h : ν (ν.supportᶜ) = 0 := MeasureTheory.Measure.measure_compl_support
      have h' : ν {x | x ∉ ν.support} = 0 := by
        have h_eq : {x | x ∉ ν.support} = ν.supportᶜ := by ext x; simp
        rw [h_eq]; exact h
      rw [ae_iff]; exact h'
    filter_upwards [h_support] with x hx
    exact hν_support_bdd hx
  have h_pointwise_ae : ∀ᵐ (x : E2) ∂ν, ∀ᵐ (z : E2) ∂ν,
      ∫⁻ (y : ℝ), F y x z ∂μ ≤
        ENNReal.ofReal C_total * ENNReal.ofReal ((max (dist x z) δ) ^ (-s)) := by
    filter_upwards [h1] with x hx
    have h2 : ∀ᵐ (z : E2) ∂ν, z ∈ S := by
      have h_support : ∀ᵐ (z : E2) ∂ν, z ∈ ν.support := by
        have h : ν (ν.supportᶜ) = 0 := MeasureTheory.Measure.measure_compl_support
        have h' : ν {z | z ∉ ν.support} = 0 := by
          have h_eq : {z | z ∉ ν.support} = ν.supportᶜ := by ext z; simp
          rw [h_eq]; exact h
        rw [ae_iff]; exact h'
      filter_upwards [h_support] with z hz
      exact hν_support_bdd hz
    filter_upwards [h2] with z hz
    let v0 := x 0 - z 0
    let v1 := x 1 - z 1
    have hv_bound : Real.sqrt (v0^2 + v1^2) ≤ D := by
      dsimp only [D]
      have hx0 : -R ≤ x 0 := (hx 0).1
      have hx0' : x 0 ≤ R := (hx 0).2
      have hx1 : -R ≤ x 1 := (hx 1).1
      have hx1' : x 1 ≤ R := (hx 1).2
      have hz0 : -R ≤ z 0 := (hz 0).1
      have hz0' : z 0 ≤ R := (hz 0).2
      have hz1 : -R ≤ z 1 := (hz 1).1
      have hz1' : z 1 ≤ R := (hz 1).2
      have h_v02 : v0^2 ≤ (2 * R)^2 := by dsimp only [v0]; nlinarith
      have h_v12 : v1^2 ≤ (2 * R)^2 := by dsimp only [v1]; nlinarith
      have h : v0^2 + v1^2 ≤ (2 * R)^2 + (2 * R)^2 := by linarith
      have h' : Real.sqrt (v0^2 + v1^2) ≤ Real.sqrt ((2 * R)^2 + (2 * R)^2) := Real.sqrt_le_sqrt h
      have hR_nonneg : 0 ≤ R := by linarith
      have h'' : Real.sqrt ((2 * R)^2 + (2 * R)^2) = 2 * R * Real.sqrt 2 := by
        have h1 : (2 * R)^2 + (2 * R)^2 = 2 * (2 * R)^2 := by ring
        rw [h1]
        have h2 : Real.sqrt (2 * (2 * R)^2) = Real.sqrt 2 * Real.sqrt ((2 * R)^2) := by
          rw [Real.sqrt_mul] <;> norm_num <;> linarith
        rw [h2]
        have h3 : Real.sqrt ((2 * R)^2) = 2 * R := by
          rw [Real.sqrt_sq] <;> linarith
        rw [h3] <;> ring
      rw [h''] at h'; exact h'
    have h_abs : ∀ y, |proj y x - proj y z| = |v0 * y + v1| := by
      intro y; dsimp only [v0, v1, proj]; ring_nf
    have h_dist : dist x z = Real.sqrt (v0^2 + v1^2) := by
      have h1 : dist x z = ‖x - z‖ := by exact dist_eq_norm x z
      rw [h1]
      have h_norm_sq : ∀ (v : E2), ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
        intro v
        have h3 : ‖v‖ ^ 2 = ∑ i : Fin 2, (v i)^2 := by exact EuclideanSpace.real_norm_sq_eq v
        rw [h3, Fin.sum_univ_two] <;> ring
      have h4 : ‖x - z‖ ^ 2 = (x - z) 0 ^ 2 + (x - z) 1 ^ 2 := h_norm_sq (x - z)
      have h5 : (x - z) 0 = x 0 - z 0 := by exact PiLp.sub_apply (fun x => ℝ) x z 0
      have h6 : (x - z) 1 = x 1 - z 1 := by exact PiLp.sub_apply (fun x => ℝ) x z 1
      have h7 : 0 ≤ ‖x - z‖ := by positivity
      rw [← Real.sqrt_sq h7, h4, h5, h6]
    by_cases h_v : (v0, v1) = (0, 0)
    · have h_v0 : v0 = 0 := by simp [Prod.ext_iff] at h_v <;> tauto
      have h_v1 : v1 = 0 := by simp [Prod.ext_iff] at h_v <;> tauto
      have hF_eq2 : ∀ y, F y x z = ENNReal.ofReal (δ ^ (-s)) := by
        intro y
        have h4 : |proj y x - proj y z| = 0 := by
          rw [h_abs y, h_v0, h_v1] <;> simp
        have h5 : max (|proj y x - proj y z|) δ = δ := by
          rw [h4]
          have h6 : max (0 : ℝ) δ = δ := by
            rw [max_eq_right] <;> linarith [hδ_pos]
          exact h6
        simp only [F, h5] <;> rfl
      have h_int : ∫⁻ (y : ℝ), F y x z ∂μ = ENNReal.ofReal (δ ^ (-s)) := by
        simp_rw [hF_eq2]
        rw [lintegral_const, measure_univ] <;> simp
      have h_dist_zero : dist x z = 0 := by
        rw [h_dist, h_v0, h_v1] <;> ring
      rw [h_int, h_dist_zero]
      have h_max0 : max (0 : ℝ) δ = δ := by
        rw [max_eq_right] <;> linarith [hδ_pos]
      simp only [h_max0]
      have h6 : ENNReal.ofReal (δ ^ (-s)) ≤
          ENNReal.ofReal C_total * ENNReal.ofReal (δ ^ (-s)) := by
        rw [← ENNReal.ofReal_mul (by linarith)]
        exact ENNReal.ofReal_le_ofReal (by
          have h7 : 0 < δ ^ (-s) := by positivity
          nlinarith [hC_total_ge_one])
      exact h6
    · have h4 : ∫⁻ (y : ℝ), F y x z ∂μ =
          ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ := by
        congr with y; simp [F, h_abs y]
      rw [h4]
      have h5_raw := directional_energy_integral_gen
        hτ_pos hκ_pos hτ_gt_2κ hδ_pos hδ_le_one hCμ_pos hμ_frost hμ_support_bdd
        hD_ge_one h_sqrt5_le h_v hv_bound
      have h_s_eq : s = 2 * κ := by rfl
      have h5 : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ ≤
          ENNReal.ofReal C_dir * ENNReal.ofReal ((max (Real.sqrt (v0^2 + v1^2)) δ) ^ (-s)) := by
        have h5' : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-2 * κ)) ∂μ ≤
            ENNReal.ofReal ((C_μ + 1) * D ^ (2 * κ) * (1 + (2 * κ) / (τ - 2 * κ))) *
            ENNReal.ofReal ((max (Real.sqrt (v0^2 + v1^2)) δ) ^ (-2 * κ)) := h5_raw
        have h_neg_eq : (-s : ℝ) = -2 * κ := by dsimp only [s]; ring
        have h_Cdir_eq2 : C_dir = (C_μ + 1) * D ^ (2 * κ) * (1 + (2 * κ) / (τ - 2 * κ)) := by
          dsimp only [C_dir, s] <;> rfl
        simpa [h_neg_eq, h_Cdir_eq2] using h5'
      have h6 : ENNReal.ofReal C_dir * ENNReal.ofReal ((max (Real.sqrt (v0^2 + v1^2)) δ) ^ (-s)) ≤
          ENNReal.ofReal C_total * ENNReal.ofReal ((max (Real.sqrt (v0^2 + v1^2)) δ) ^ (-s)) := by
        have h7 : C_dir ≤ C_total := by linarith
        exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal h7) (by positivity)
      have h7 : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ ≤
          ENNReal.ofReal C_total * ENNReal.ofReal ((max (Real.sqrt (v0^2 + v1^2)) δ) ^ (-s)) :=
        le_trans h5 h6
      rw [h_dist] at *
      exact h7
  have h_expand : ∀ (y : ℝ),
      rieszEnergy s (hδ := hδ_pos) (Measure.map (proj y) ν) =
      ∫⁻ (x : E2), ∫⁻ (z : E2), F y x z ∂ν ∂ν := by
    intro y
    simp only [rieszEnergy]
    have h := @projection_energy_to_double_integral δ κ hδ_pos hκ_pos ν _ y
    simpa [hF_eq] using h
  have h_fubini :
      ∫⁻ (y : ℝ), ∫⁻ (x : E2), ∫⁻ (z : E2), F y x z ∂ν ∂ν ∂μ =
      ∫⁻ (x : E2), ∫⁻ (z : E2), ∫⁻ (y : ℝ), F y x z ∂μ ∂ν ∂ν := by
    have h_meas : Measurable (fun p : ℝ × E2 × E2 => F p.1 p.2.1 p.2.2) := by
      simpa [hF_eq] using energyIntegrand_measurable hδ_pos hκ_pos
    exact general_fubini3_swap h_meas
  have hC_total_eq : C_total = 1 + (C_μ + 1) * (2 * R * Real.sqrt 2) ^ (2 * κ) *
      (1 + (2 * κ) / (τ - 2 * κ)) := by
    dsimp only [C_total, C_dir, s, D] <;> rfl
  have h_inner_ae : ∀ᵐ (x : E2) ∂ν,
      ∫⁻ (z : E2), ∫⁻ (y : ℝ), F y x z ∂μ ∂ν ≤
      ∫⁻ (z : E2), ENNReal.ofReal C_total * ENNReal.ofReal ((max (dist x z) δ) ^ (-s)) ∂ν := by
    filter_upwards [h_pointwise_ae] with x hx
    exact lintegral_mono_ae hx
  have h_main_ineq : ∫⁻ (x : E2), ∫⁻ (z : E2), ∫⁻ (y : ℝ), F y x z ∂μ ∂ν ∂ν ≤
      ∫⁻ (x : E2), ∫⁻ (z : E2), ENNReal.ofReal C_total * ENNReal.ofReal ((max (dist x z) δ) ^ (-s)) ∂ν ∂ν :=
    lintegral_mono_ae h_inner_ae
  calc
    ∫⁻ (y : ℝ), rieszEnergy s (hδ := hδ_pos) (Measure.map (proj y) ν) ∂μ
      = ∫⁻ (y : ℝ), ∫⁻ (x : E2), ∫⁻ (z : E2), F y x z ∂ν ∂ν ∂μ := by
        congr with y; exact h_expand y
    _ = ∫⁻ (x : E2), ∫⁻ (z : E2), ∫⁻ (y : ℝ), F y x z ∂μ ∂ν ∂ν := h_fubini
    _ ≤ ∫⁻ (x : E2), ∫⁻ (z : E2),
          ENNReal.ofReal C_total * ENNReal.ofReal ((max (dist x z) δ) ^ (-s)) ∂ν ∂ν := h_main_ineq
    _ = ENNReal.ofReal C_total * rieszEnergy s (hδ := hδ_pos) ν := by
        have h_inner : ∀ (x : E2),
            ∫⁻ (z : E2), ENNReal.ofReal C_total * ENNReal.ofReal ((max (dist x z) δ) ^ (-s)) ∂ν =
            ENNReal.ofReal C_total * ∫⁻ (z : E2), ENNReal.ofReal ((max (dist x z) δ) ^ (-s)) ∂ν := by
          intro x
          have h_meas_z : Measurable (fun z : E2 => ENNReal.ofReal ((max (dist x z) δ) ^ (-s))) := by fun_prop
          rw [lintegral_const_mul (ENNReal.ofReal C_total) h_meas_z]
        have h_step1 : ∫⁻ (x : E2), ∫⁻ (z : E2),
              ENNReal.ofReal C_total * ENNReal.ofReal ((max (dist x z) δ) ^ (-s)) ∂ν ∂ν =
            ∫⁻ (x : E2), ENNReal.ofReal C_total *
              ∫⁻ (z : E2), ENNReal.ofReal ((max (dist x z) δ) ^ (-s)) ∂ν ∂ν := by
          congr with x; exact h_inner x
        rw [h_step1]
        have h_meas_x : Measurable (fun x : E2 => ∫⁻ (z : E2), ENNReal.ofReal ((max (dist x z) δ) ^ (-s)) ∂ν) := by fun_prop
        rw [lintegral_const_mul (ENNReal.ofReal C_total) h_meas_x]
        have h_riesz : rieszEnergy s (hδ := hδ_pos) ν =
            ∫⁻ (x : E2), ∫⁻ (z : E2), ENNReal.ofReal ((max (dist x z) δ) ^ (-s)) ∂ν ∂ν := by
          simp [rieszEnergy] <;> rfl
        exact congr_arg (fun x => ENNReal.ofReal C_total * x) h_riesz.symm
    _ = ENNReal.ofReal (1 + (C_μ + 1) * (2 * R * Real.sqrt 2) ^ (2 * κ) *
          (1 + (2 * κ) / (τ - 2 * κ))) *
        rieszEnergy s (hδ := hδ_pos) ν := by
      rw [hC_total_eq] <;> rfl

end robust_projection_main
