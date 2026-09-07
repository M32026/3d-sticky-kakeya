module

/-
  ConcentratedBridge.lean

  Bridge from concentrated_case_contradiction_G hypotheses (WITH direction
  separation on T_conc) to concentrated_two_ends_contradiction.

  Main result: concentrated_case_contradiction_G_with_sep

  Uses unit-ball support hypotheses for localization (R=1, tails=0).
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.TubeLine
public import MyLeanRepo.RadialBootstrapping.ConcentratedHPrime
public import MyLeanRepo.RadialBootstrapping.ConcentratedHPrimeS
public import MyLeanRepo.RadialBootstrapping.TwoEndsConcentrated
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set Finset Classical
open scoped ENNReal NNReal


noncomputable section

namespace RadialBootstrapping
namespace B1

/-! ============================================================================
   Helper lemmas
   ============================================================================ -/

/-- Derive h_annulus_large: r^(σ+4τ) > 4Cr from κ<1 and h_r_final. -/
lemma annulus_large_from_bridge
    (r σ τ C κ : ℝ)
    (hr : 0 < r) (hr_small : r < 1)
    (hσ : 0 ≤ σ) (hσ_lt_one : σ < 1) (hτ : 0 < τ)
    (hκ : κ = 14 * τ / (1 - σ)) (hκ_lt_one : κ < 1)
    (hC : 1 ≤ C)
    (h_r_final : 20 * C * Real.rpow r τ < 1) :
    Real.rpow r (σ + 4 * τ) > 4 * C * r := by
  have h1mσ : 0 < 1 - σ := by linarith
  have hτ_lt : τ < (1 - σ) / 14 := by
    have h2 : 14 * τ / (1 - σ) < 1 := by linarith [hκ_lt_one]
    have h3 : 14 * τ < 1 - σ := by
      calc 14 * τ = (14 * τ / (1 - σ)) * (1 - σ) := by field_simp [h1mσ.ne'] <;> ring
        _ < 1 * (1 - σ) := by gcongr
        _ = 1 - σ := by ring
    linarith
  set α : ℝ := 1 - σ - 4 * τ with hα_def
  have hα_pos : 0 < α := by linarith
  have hα_gt_τ : α > τ := by linarith
  have hrτ_lt : Real.rpow r τ < 1 / (20 * C) := by
    have hpos : 0 < 20 * C := by positivity
    calc Real.rpow r τ
      = (20 * C * Real.rpow r τ) / (20 * C) := by field_simp [hpos.ne'] <;> ring
    _ < 1 / (20 * C) := by gcongr
  have hrα_lt : Real.rpow r α < Real.rpow r τ :=
    Real.rpow_lt_rpow_of_exponent_gt hr hr_small hα_gt_τ
  have h4 : Real.rpow r α < 1 / (4 * C) := by
    calc Real.rpow r α < Real.rpow r τ := hrα_lt
      _ < 1 / (20 * C) := hrτ_lt
      _ ≤ 1 / (4 * C) := by
        have h5 : 0 < C := by linarith
        gcongr <;> norm_num
  have h5 : Real.rpow r (σ + 4 * τ) = r / Real.rpow r α := by
    have h6 : (σ + 4 * τ) + α = 1 := by simp [hα_def] <;> ring
    have h7 : Real.rpow r ((σ + 4 * τ) + α) = Real.rpow r (σ + 4 * τ) * Real.rpow r α :=
      Real.rpow_add hr (σ + 4 * τ) α
    have h8 : Real.rpow r ((σ + 4 * τ) + α) = r := by
      rw [h6]
      simp
    have h9 : Real.rpow r (σ + 4 * τ) * Real.rpow r α = r := by
      rw [←h7, h8]
    have h10 : 0 < Real.rpow r α := Real.rpow_pos_of_pos hr α
    field_simp [h10.ne'] at h9 ⊢
    <;> linarith
  rw [h5]
  have h11 : 0 < Real.rpow r α := Real.rpow_pos_of_pos hr α
  have h12 : r / Real.rpow r α > r / (1 / (4 * C)) := by gcongr
  have h13 : r / (1 / (4 * C)) = 4 * C * r := by
    have h14 : 0 < C := by linarith
    field_simp [h14.ne'] <;> ring
  rw [h13] at h12
  exact h12

/-- Choose threshold = 1/4 * r^(σ+3τ). Valid between required bounds. -/
lemma threshold_choice_valid_bridge
    (r σ τ : ℝ) (hr : 0 < r) (hσ : 0 ≤ σ) (hτ : 0 < τ) :
    let threshold := (1 / 4 : ℝ) * Real.rpow r (σ + 3 * τ)
    (0 < threshold) ∧
    ((1 / 6 + 1 / 1584 : ℝ) * Real.rpow r (σ + 3 * τ) < threshold) ∧
    (threshold < (1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) := by
  let threshold := (1 / 4 : ℝ) * Real.rpow r (σ + 3 * τ)
  have hpos : 0 < Real.rpow r (σ + 3 * τ) := Real.rpow_pos_of_pos hr (σ + 3 * τ)
  have h1 : (1 / 6 + 1 / 1584 : ℝ) < (1 / 4 : ℝ) := by norm_num
  have h2 : (1 / 4 : ℝ) < (1 / 3 : ℝ) := by norm_num
  exact ⟨by positivity, mul_lt_mul_of_pos_right h1 hpos, mul_lt_mul_of_pos_right h2 hpos⟩

/-- Derive h_r2τ_small for R=1 from h_count_small and R_high ≥ 1/2. -/
lemma r2τ_small_from_count_bridge
    (r σ τ K C R_high : ℝ)
    (hr : 0 < r) (hr_small : r < 1)
    (hσ : 0 ≤ σ) (hσ_lt_one : σ < 1) (hτ : 0 < τ)
    (hK : 1 ≤ K) (hC : 1 ≤ C)
    (hR_high_ge_half : 1 / 2 ≤ R_high)
    (h_count_small : Real.rpow r (-2 * τ) >
        (10^7 : ℝ) * K * C * Real.rpow ((R_high + r) / 4) σ) :
    Real.rpow r (2 * τ) <
        1 / (390 * K * C * Real.rpow (1 + (2 * (1 : ℝ) + 1) / 8) σ) := by
  have h1 : (R_high + r) / 4 ≥ 1 / 8 := by linarith
  have h4 : Real.rpow ((R_high + r) / 4) σ ≥ Real.rpow (1 / 8) σ :=
    Real.rpow_le_rpow (by linarith) h1 hσ
  have h5 : (10^7 : ℝ) * K * C * Real.rpow ((R_high + r) / 4) σ ≥
      (10^7 : ℝ) * K * C * Real.rpow (1 / 8) σ := by gcongr
  have h6 : Real.rpow r (-2 * τ) > (10^7 : ℝ) * K * C * Real.rpow (1 / 8) σ :=
    lt_of_le_of_lt h5 h_count_small
  have h7 : Real.rpow (1 / 8) σ ≥ 1 / 8 := by
    have h8 : σ ≤ 1 := by linarith
    have h9 : Real.rpow (1 / 8) σ ≥ Real.rpow (1 / 8) 1 :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by linarith) h8
    simpa using h9
  have h10 : (10^7 : ℝ) * K * C * Real.rpow (1 / 8) σ ≥
      (10^7 : ℝ) * K * C * (1 / 8) := by gcongr
  have h11 : Real.rpow r (-2 * τ) > (10^7 : ℝ) * K * C * (1 / 8) :=
    lt_of_le_of_lt h10 h6
  have h12 : (10^7 : ℝ) * (1 / 8) > 390 * Real.rpow (11 / 8) σ := by
    have h13 : Real.rpow (11 / 8) σ ≤ 11 / 8 := by
      have h14 : σ ≤ 1 := by linarith
      have h15 : Real.rpow (11 / 8) σ ≤ Real.rpow (11 / 8) 1 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h14
      simpa using h15
    nlinarith
  have h14 : Real.rpow r (-2 * τ) > 390 * K * C * Real.rpow (11 / 8) σ := by
    calc Real.rpow r (-2 * τ)
      > (10^7 : ℝ) * K * C * (1 / 8) := h11
      _ = K * C * ((10^7 : ℝ) * (1 / 8)) := by ring
      _ > K * C * (390 * Real.rpow (11 / 8) σ) := by gcongr
      _ = 390 * K * C * Real.rpow (11 / 8) σ := by ring
  have h15 : Real.rpow (1 + (2 * (1 : ℝ) + 1) / 8) σ = Real.rpow (11 / 8) σ := by
    have h16 : 1 + (2 * (1 : ℝ) + 1) / 8 = 11 / 8 := by norm_num
    rw [h16]
  rw [h15]
  have h_pos : 0 < Real.rpow r (2 * τ) := Real.rpow_pos_of_pos hr (2 * τ)
  have h_inv : Real.rpow r (-2 * τ) = (Real.rpow r (2 * τ))⁻¹ := by
    have h17 : Real.rpow r ((-2 * τ) + (2 * τ)) = Real.rpow r (-2 * τ) * Real.rpow r (2 * τ) :=
      Real.rpow_add hr (-2 * τ) (2 * τ)
    have h18 : (-2 * τ) + (2 * τ) = 0 := by ring
    have h19 : Real.rpow r ((-2 * τ) + (2 * τ)) = 1 := by rw [h18]; simp
    exact eq_inv_of_mul_eq_one_left (h17 ▸ h19)
  rw [h_inv] at h14
  set a := Real.rpow r (2 * τ) with ha
  set b := 390 * K * C * Real.rpow (11 / 8) σ with hb
  have ha_pos : 0 < a := h_pos
  have hb_pos : 0 < b := by
    have h21 : 0 < K := by linarith
    have h22 : 0 < C := by linarith
    have h23 : 0 < Real.rpow (11 / 8) σ := Real.rpow_pos_of_pos (by norm_num) σ
    positivity
  have h_gt : a⁻¹ > b := h14
  have h_mul : a * b < 1 := by
    have h4 : a⁻¹ = 1 / a := by simp
    rw [h4] at h_gt
    have h5 : a * (1 / a) = 1 := by
      field_simp [ha_pos.ne'] <;> ring
    have h6 : a * b < a * (1 / a) := by gcongr
    rw [h5] at h6
    exact h6
  have h25 : a < 1 / b := by
    have h7 : a * b < 1 := h_mul
    have h8 : a * b / b < 1 / b := by gcongr
    have h9 : a * b / b = a := by
      field_simp [hb_pos.ne'] <;> ring
    rw [h9] at h8
    exact h8
  exact h25

/-- Tail bound from unit ball support: ν(closedBall 0 1)ᶜ = 0. -/
lemma tail_bound_from_unit_ball_bridge
    {ν : Measure Point} [IsProbabilityMeasure ν]
    (h_supp : ν.support ⊆ Metric.closedBall (0 : Point) 1) :
    ν (Metric.closedBall (0 : Point) 1)ᶜ = 0 := by
  have h2 : (Metric.closedBall (0 : Point) 1)ᶜ ⊆ (ν.support)ᶜ := by
    exact Set.compl_subset_compl.mpr h_supp
  have h3 : ν (ν.support)ᶜ = 0 := Measure.measure_compl_support
  exact measure_mono_null h2 h3

/-- Prove R_high ≥ 1/2 from support distance and nonempty Y_x. -/
lemma R_high_ge_half_from_support
    (ν₁ ν₂ : Measure Point)
    (G : Set (Point × Point))
    (x : Point) (R_high : ℝ)
    (Y_x : Set Point)
    (hG_subset : G ⊆ ν₁.support ×ˢ ν₂.support)
    (h_support_dist : 1 / 2 ≤ sInf {d : ℝ | ∃ x' ∈ ν₁.support, ∃ y' ∈ ν₂.support, dist x' y' = d})
    (hY_sub_G : Y_x ⊆ {b₂ | (x, b₂) ∈ G})
    (hY_mass_pos : 0 < ν₂ Y_x)
    (h_dist_upper : ∀ y ∈ Y_x, dist x y ≤ R_high) :
    1 / 2 ≤ R_high := by
  have hY_nonempty : Y_x.Nonempty := by
    by_contra h
    have h' : Y_x = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [h'] at hY_mass_pos
    simp at hY_mass_pos
  rcases hY_nonempty with ⟨y, hy⟩
  have hxy_G : (x, y) ∈ G := hY_sub_G hy
  have hx_supp : x ∈ ν₁.support := (hG_subset hxy_G).1
  have hy_supp : y ∈ ν₂.support := (hG_subset hxy_G).2
  let S : Set ℝ := {d | ∃ x' ∈ ν₁.support, ∃ y' ∈ ν₂.support, dist x' y' = d}
  have h_dist_set : dist x y ∈ S := ⟨x, hx_supp, y, hy_supp, rfl⟩
  have h_bdd : BddBelow S := by
    refine' ⟨0, _⟩
    intro d hd
    have h1 : ∃ (x' y' : Point), x' ∈ ν₁.support ∧ y' ∈ ν₂.support ∧ dist x' y' = d := by
      simpa [S] using hd
    rcases h1 with ⟨x', y', hx', hy', h_eq⟩
    have h2 : 0 ≤ d := by
      have h3 : 0 ≤ dist x' y' := dist_nonneg
      linarith [h_eq]
    exact h2
  have h_sInf_le : sInf S ≤ dist x y := csInf_le h_bdd h_dist_set
  have h_ge : 1 / 2 ≤ dist x y := by
    calc 1 / 2 ≤ sInf S := h_support_dist
      _ ≤ dist x y := h_sInf_le
  have h_le : dist x y ≤ R_high := h_dist_upper y hy
  linarith

/-! ============================================================================
   Main bridge theorem
   ============================================================================ -/

/-- Concentrated case contradiction WITH direction separation on T_conc
    and unit-ball support hypotheses.

    For each x ∈ X_conc, applies `concentrated_H'_fiber_lower_mass` to get
    H' fiber mass ≥ r^(2τ)/396 ≥ r^(6τ)/396, then calls
    `concentrated_two_ends_contradiction`. -/
theorem concentrated_case_contradiction_G_with_sep
    (ν₁ ν₂ : ProbabilityMeasure Point)
    (G : Set (Point × Point))
    (K K' C σ τ r c κ : ℝ)
    (hσ : 0 ≤ σ) (hσ_lt_one : σ < 1) (hτ : 0 < τ) (hr : 0 < r) (hr_small : r < 1)
    (hκ : κ = 14 * τ / (1 - σ)) (hκ_lt_one : κ < 1)
    (hC : 1 ≤ C) (hK : 1 ≤ K) (hc_pos : 0 < c)
    (hν₂_growth : ∀ (x : Point) (ρ : ℝ), 0 < ρ →
      ν₂ (Metric.ball x ρ) ≤ Real.toNNReal (C * ρ))
    (hν₁_growth : ∀ (x : Point) (ρ : ℝ), 0 < ρ →
      ν₁ (Metric.ball x ρ) ≤ Real.toNNReal (C * ρ))
    (hG_forward : ∀ x ∈ (ν₁ : Measure Point).support,
      ∀ ℓ : AffineSubspace ℝ Point, x ∈ (ℓ : Set Point) →
        Module.finrank ℝ ℓ.direction = 1 → ∀ r' : ℝ, 0 < r' →
          ν₂ {b₂ | b₂ ∈ tubeLine r' ℓ ∧ (x, b₂) ∈ G} ≤
            ENNReal.ofReal (K * Real.rpow r' σ))
    (hG_reverse : ∀ y ∈ (ν₂ : Measure Point).support,
      ∀ ℓ : AffineSubspace ℝ Point, y ∈ (ℓ : Set Point) →
        Module.finrank ℝ ℓ.direction = 1 → ∀ r' : ℝ, 0 < r' →
          ν₁ {b₁ | b₁ ∈ tubeLine r' ℓ ∧ (b₁, y) ∈ G} ≤
            ENNReal.ofReal (K * Real.rpow r' σ))
    (hG_meas : MeasurableSet G)
    (hG_subset : G ⊆ (ν₁ : Measure Point).support ×ˢ (ν₂ : Measure Point).support)
    (h_support_dist : 1 / 2 ≤ sInf {d : ℝ |
      ∃ x ∈ (ν₁ : Measure Point).support,
        ∃ y ∈ (ν₂ : Measure Point).support, dist x y = d})
    (h_supp1 : (ν₁ : Measure Point).support ⊆ Metric.closedBall (0 : Point) 1)
    (h_supp2 : (ν₂ : Measure Point).support ⊆ Metric.closedBall (0 : Point) 1)
    (R_low R_high : ℝ)
    (hR_low_pos : 0 < R_low) (hR_high_pos : 0 < R_high)
    (hR_le : R_low ≤ R_high)
    (hr_tube_small : r ≤ R_low / 4)
    (h_rκ_le_R : Real.rpow r κ ≤ R_high)
    (N : ℕ)
    (hN_pos : 0 < N)
    (hR : 2 * R_high + r ≤ r * (2 : ℝ)^N)
    (h_log_absorb : Real.rpow r (σ + 3 * τ) ≥ C * r + 792 * (N : ℝ) * Real.rpow r (σ + 4 * τ))
    (h_param_strengthened : Real.rpow r τ * ((Nat.floor (16 * Real.pi * R_high / R_low) + 1 : ℝ)) * K * (2 : ℝ)^σ ≤ 66)
    (h_card_strong : (Nat.ceil ((1 - κ) * Real.log (1 / r) / Real.log 2) + 1 : ℝ) ≤
        (1 / 1584 : ℝ) * Real.rpow r (-τ))
    (h_count_small : Real.rpow r (-2 * τ) >
        (10^7 : ℝ) * K * C * Real.rpow ((R_high + r) / 4) σ)
    (hσ3τ_gt_κ : σ + 3 * τ > κ)
    (h_r_log_small : Real.rpow r τ * Real.log (1 / r) ≤ 1 / 100)
    (h_r_final : 20 * C * Real.rpow r τ < 1)
    (h_inner_cond : 18 * C * r ≤ Real.rpow r (σ + 3 * τ))
    (X_conc : Set Point)
    (hX_conc_subset : X_conc ⊆ (ν₁ : Measure Point).support)
    (hX_conc_meas : (ν₁ : Measure Point) X_conc ≥ ENNReal.ofReal (Real.rpow r τ / 2))
    (hX_conc_prop : ∀ x ∈ X_conc,
      ∃ (T_x S T_conc : Finset (AffineSubspace ℝ Point)) (Y_x : Set Point),
        MeasurableSet Y_x ∧
        (∀ ℓ ∈ T_x, x ∈ (ℓ : Set Point) ∧ Module.finrank ℝ ℓ.direction = 1) ∧
        Y_x ⊆ {b₂ | (x, b₂) ∈ G} ∧
        Y_x ⊆ ⋃ ℓ ∈ T_x, tubeLine r ℓ ∧
        (∀ y ∈ Y_x, R_low ≤ dist x y ∧ dist x y ≤ R_high) ∧
        ν₂ Y_x ≥ ENNReal.ofReal (Real.rpow r (2 * τ)) ∧
        (∀ ℓ ∈ T_x,
          ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) ≤ ν₂ (tubeLine r ℓ ∩ Y_x) ∧
          ν₂ (tubeLine r ℓ ∩ Y_x) ≤ ENNReal.ofReal (Real.rpow r (σ - τ))) ∧
        S ⊆ T_x ∧
        (∀ ℓ1 ∈ S, ∀ ℓ2 ∈ S, ℓ1 ≠ ℓ2 →
          submoduleDirDist ℓ1.direction ℓ2.direction ≥ r / (4 * R_high)) ∧
        T_conc ⊆ S ∧
        (∀ ℓ ∈ T_conc, IsConcentrated (ν₂ : Measure Point) Y_x (tubeLine r ℓ) r κ) ∧
        2 * T_conc.card ≥ S.card ∧
        (S.card : ℝ) ≥ Real.rpow r (2 * τ - σ) / (K * (2 : ℝ)^σ)) :
    False := by
  classical
  let ν₁m : Measure Point := ν₁
  let ν₂m : Measure Point := ν₂

  -- Step 0: Prove R_high ≥ 1/2
  have hX_nonempty : X_conc.Nonempty := by
    by_contra h
    have h' : X_conc = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [h'] at hX_conc_meas
    have hpos : 0 < Real.rpow r τ := Real.rpow_pos_of_pos hr τ
    have hpos2 : 0 < ENNReal.ofReal (Real.rpow r τ / 2) := by
      apply ENNReal.ofReal_pos.mpr; positivity
    have h9 : (0 : ENNReal) ≥ ENNReal.ofReal (Real.rpow r τ / 2) := by
      simpa using hX_conc_meas
    have h10 : ENNReal.ofReal (Real.rpow r τ / 2) = 0 := by
      have h11 : ENNReal.ofReal (Real.rpow r τ / 2) ≤ 0 := h9
      have h12 : ENNReal.ofReal (Real.rpow r τ / 2) = 0 := by
        exact le_zero_iff.mp h9
      exact h12
    exact hpos2.ne' h10
  rcases hX_nonempty with ⟨x0, hx0⟩
  rcases hX_conc_prop x0 hx0 with ⟨T_x0, S0, T_conc0, Y_x0, hY_meas0, h_lines0, hY_sub_G0, hY_cover0, h_dist0, hY_mass0, h_mass_Tx0, hS_sub0, h_sep0, hTconc_sub0, h_conc0, h_card_half0, hS_card_lower0⟩
  have hY_mass_pos0 : 0 < ν₂m Y_x0 := by
    have h_eq : ν₂m Y_x0 = (ν₂ Y_x0 : ENNReal) :=
      (ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν₂ Y_x0).symm
    rw [h_eq]
    have h : (ν₂ Y_x0 : ENNReal) ≥ ENNReal.ofReal (Real.rpow r (2 * τ)) := hY_mass0
    have hpos : 0 < Real.rpow r (2 * τ) := Real.rpow_pos_of_pos hr (2 * τ)
    have hpos2 : 0 < ENNReal.ofReal (Real.rpow r (2 * τ)) := by
      apply ENNReal.ofReal_pos.mpr; exact hpos
    exact lt_of_lt_of_le hpos2 h
  have hR_high_ge_half : 1 / 2 ≤ R_high :=
    R_high_ge_half_from_support ν₁m ν₂m G x0 R_high Y_x0 hG_subset h_support_dist hY_sub_G0 hY_mass_pos0
      (fun y hy => (h_dist0 y hy).2)

  -- Step 1: Choose threshold
  let threshold : ℝ := (1 / 4 : ℝ) * Real.rpow r (σ + 3 * τ)
  have hth := threshold_choice_valid_bridge r σ τ hr hσ hτ
  have hthreshold_pos : 0 < threshold := hth.1
  have hthreshold_large : threshold > (1 / 6 + 1 / 1584 : ℝ) * Real.rpow r (σ + 3 * τ) := hth.2.1
  have hthreshold_lt : threshold < (1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ) := hth.2.2
  have hthreshold_nonneg : 0 ≤ threshold := by linarith

  have hκ_pos : 0 < κ := by
    rw [hκ]
    have h1 : 0 < 1 - σ := by linarith
    have h2 : 0 < 14 * τ := by positivity
    exact div_pos h2 h1
  have hrκ_pos : 0 < Real.rpow r κ := Real.rpow_pos_of_pos hr κ

  -- Step 2: Per-x H' fiber mass (using S-based lemma)
  let F : ℕ := Nat.floor (16 * Real.pi * R_high / R_low) + 1
  have hF_def : F = Nat.floor (16 * Real.pi * R_high / R_low) + 1 := by rfl
  have hK_pos : 0 < K := by linarith
  have h_per_x_mass : ∀ x ∈ X_conc,
      ν₂m {y | (x, y) ∈ ConcentratedH' ν₂m G r κ threshold ∧ (x, y) ∈ G}
        ≥ ENNReal.ofReal ((1 / 396 : ℝ) * Real.rpow r (6 * τ)) := by
    intro x hx
    rcases hX_conc_prop x hx with ⟨T_x, S, T_conc, Y_x, hY_meas, h_lines_Tx, hY_sub_G, hY_cover, h_dist, hY_mass, h_mass_Tx, hS_sub_Tx, h_sep, hTconc_sub, h_conc, h_card_half, hS_card_lower⟩
    have h_lines_S : ∀ ℓ ∈ S, x ∈ (ℓ : Set Point) ∧ Module.finrank ℝ ℓ.direction = 1 := by
      intro ℓ hℓ
      exact h_lines_Tx ℓ (hS_sub_Tx hℓ)
    have h_mass_lower_S : ∀ ℓ ∈ S,
        ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) ≤ ν₂m (Metric.thickening r (ℓ : Set Point) ∩ Y_x) := by
      intro ℓ hℓ
      have h_eq : ν₂m (Metric.thickening r (ℓ : Set Point) ∩ Y_x) =
          (ν₂ (tubeLine r ℓ ∩ Y_x) : ENNReal) := by
        rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν₂ _] <;> rfl
      rw [h_eq]
      exact (h_mass_Tx ℓ (hS_sub_Tx hℓ)).1
    have h_y_dist : ∀ (z : Point), z ∈ Y_x → dist x z ≥ R_low := by
      intro z hz
      exact (h_dist z hz).1
    have h_conc' : ∀ ℓ ∈ T_conc, IsConcentrated ν₂m Y_x (Metric.thickening r (ℓ : Set Point)) r κ := by
      intro ℓ hℓ
      simpa [tubeLine] using h_conc ℓ hℓ
    -- Derive hT_conc_sum_lower from cardinality-half + hS_card_lower + per-tube mass
    let tube_mass (ℓ : AffineSubspace ℝ Point) : ENNReal := ν₂m (Metric.thickening r (ℓ : Set Point) ∩ Y_x)
    have h_per_tube_lower : ∀ ℓ ∈ T_conc, tube_mass ℓ ≥ ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) := by
      intro ℓ hℓ
      exact h_mass_lower_S ℓ (hTconc_sub hℓ)
    have h_sum_card : ∑ ℓ ∈ T_conc, tube_mass ℓ ≥
        (T_conc.card : ENNReal) * ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) := by
      have h1 : ∑ ℓ ∈ T_conc, tube_mass ℓ ≥ ∑ ℓ ∈ T_conc, ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) :=
        Finset.sum_le_sum fun ℓ hℓ => h_per_tube_lower ℓ hℓ
      have h2 : ∑ ℓ ∈ T_conc, ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) =
          (T_conc.card : ENNReal) * ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) := by
        simp [Finset.sum_const, mul_comm]
        <;> rfl
      rw [h2] at h1
      exact h1
    have h_card_lower_real : (T_conc.card : ℝ) ≥
        Real.rpow r (2 * τ - σ) / (2 * K * (2 : ℝ)^σ) := by
      have h1 : 2 * (T_conc.card : ℝ) ≥ (S.card : ℝ) := by exact_mod_cast h_card_half
      have h2 : (T_conc.card : ℝ) ≥ (S.card : ℝ) / 2 := by linarith
      have hS' : Real.rpow r (2 * τ - σ) / (K * (2 : ℝ)^σ) ≤ (S.card : ℝ) := hS_card_lower
      have h3 : Real.rpow r (2 * τ - σ) / (2 * K * (2 : ℝ)^σ) ≤ (S.card : ℝ) / 2 := by
        calc
          Real.rpow r (2 * τ - σ) / (2 * K * (2 : ℝ)^σ)
            = (Real.rpow r (2 * τ - σ) / (K * (2 : ℝ)^σ)) / 2 := by ring
          _ ≤ (S.card : ℝ) / 2 := by gcongr
      calc
        (T_conc.card : ℝ) ≥ (S.card : ℝ) / 2 := h2
        _ ≥ Real.rpow r (2 * τ - σ) / (2 * K * (2 : ℝ)^σ) := h3
    have h_card_lower_ennreal : (T_conc.card : ENNReal) ≥
        ENNReal.ofReal (Real.rpow r (2 * τ - σ) / (2 * K * (2 : ℝ)^σ)) := by
      exact_mod_cast h_card_lower_real
    have h_pos_a : 0 ≤ Real.rpow r (2 * τ - σ) / (2 * K * (2 : ℝ)^σ) := by
      apply div_nonneg
      · exact Real.rpow_nonneg hr.le (2 * τ - σ)
      · positivity
    have h_pos_b : 0 ≤ Real.rpow r (σ + 3 * τ) := Real.rpow_nonneg hr.le (σ + 3 * τ)
    have h_rpow_mul : Real.rpow r (2 * τ - σ) * Real.rpow r (σ + 3 * τ) = Real.rpow r (5 * τ) := by
      have h5 : Real.rpow r ((2 * τ - σ) + (σ + 3 * τ)) =
          Real.rpow r (2 * τ - σ) * Real.rpow r (σ + 3 * τ) :=
        Real.rpow_add hr (2 * τ - σ) (σ + 3 * τ)
      have h6 : (2 * τ - σ) + (σ + 3 * τ) = 5 * τ := by ring
      rw [h6] at h5
      exact h5.symm
    have hT_conc_sum_lower : ∑ ℓ ∈ T_conc, tube_mass ℓ ≥
        ENNReal.ofReal (Real.rpow r (5 * τ) / (2 * K * (2 : ℝ)^σ)) := by
      calc
        ∑ ℓ ∈ T_conc, tube_mass ℓ
          ≥ (T_conc.card : ENNReal) * ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) := h_sum_card
        _ ≥ ENNReal.ofReal (Real.rpow r (2 * τ - σ) / (2 * K * (2 : ℝ)^σ)) *
              ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) := by gcongr
        _ = ENNReal.ofReal ((Real.rpow r (2 * τ - σ) / (2 * K * (2 : ℝ)^σ)) * Real.rpow r (σ + 3 * τ)) := by
          rw [← ENNReal.ofReal_mul h_pos_a]
        _ = ENNReal.ofReal (Real.rpow r (5 * τ) / (2 * K * (2 : ℝ)^σ)) := by
          have h_eq : (Real.rpow r (2 * τ - σ) / (2 * K * (2 : ℝ)^σ)) * Real.rpow r (σ + 3 * τ) =
              Real.rpow r (5 * τ) / (2 * K * (2 : ℝ)^σ) := by
            have h7 : (Real.rpow r (2 * τ - σ) / (2 * K * (2 : ℝ)^σ)) * Real.rpow r (σ + 3 * τ) =
                (Real.rpow r (2 * τ - σ) * Real.rpow r (σ + 3 * τ)) / (2 * K * (2 : ℝ)^σ) := by ring
            rw [h7, h_rpow_mul] <;> ring
          rw [h_eq]
    have h_set_eq : {y : Point | (x, y) ∈ ConcentratedH' ν₂m G r κ threshold ∧ (x, y) ∈ G} =
        ({y : Point | (x, y) ∈ ConcentratedH' ν₂m G r κ threshold} ∩ {b₂ | (x, b₂) ∈ G}) := by
      ext y; simp [Set.mem_inter_iff] <;> tauto
    rw [h_set_eq]
    exact concentrated_H'_fiber_lower_mass_S
      ν₂m G hG_meas r R_low R_high κ σ τ threshold K
      hr hR_low_pos hR_high_pos hr_tube_small
      hrκ_pos hthreshold_nonneg hthreshold_lt x S T_conc Y_x hY_meas
      h_lines_S hY_sub_G h_mass_lower_S h_sep hTconc_sub h_conc' hT_conc_sum_lower
      h_y_dist F hF_def hK_pos hσ hτ (by simpa [hF_def] using h_param_strengthened)

  -- Step 3: Derive remaining hypotheses for two-ends lemma
  have h_inner_small : C * r ≤ (1 / 6 : ℝ) * Real.rpow r (σ + 3 * τ) := by
    have h : 18 * C * r ≤ Real.rpow r (σ + 3 * τ) := h_inner_cond
    have h2 : C * r ≤ Real.rpow r (σ + 3 * τ) / 18 := by linarith
    have h3 : Real.rpow r (σ + 3 * τ) / 18 ≤ (1 / 6 : ℝ) * Real.rpow r (σ + 3 * τ) := by
      have h4 : 0 ≤ Real.rpow r (σ + 3 * τ) := Real.rpow_nonneg hr.le _
      linarith
    linarith

  have h_annulus_large : Real.rpow r (σ + 4 * τ) > 4 * C * r :=
    annulus_large_from_bridge r σ τ C κ hr hr_small hσ hσ_lt_one hτ hκ hκ_lt_one hC h_r_final

  have h_r2τ_small : Real.rpow r (2 * τ) <
      1 / (390 * K * C * Real.rpow (1 + (2 * (1 : ℝ) + 1) / 8) σ) :=
    r2τ_small_from_count_bridge r σ τ K C R_high hr hr_small hσ hσ_lt_one hτ hK hC
      hR_high_ge_half h_count_small

  let ε : ℝ := Real.rpow r (7 * τ) / 6336
  have hε_pos : 0 < ε := by
    dsimp only [ε]
    have h1 : 0 < Real.rpow r (7 * τ) := Real.rpow_pos_of_pos hr (7 * τ)
    positivity

  have h_tail1 : ν₁m (Metric.closedBall (0 : Point) 1)ᶜ < ENNReal.ofReal ε := by
    have h : ν₁m (Metric.closedBall (0 : Point) 1)ᶜ = 0 :=
      tail_bound_from_unit_ball_bridge h_supp1
    rw [h]
    positivity

  have h_tail2 : ν₂m (Metric.closedBall (0 : Point) 1)ᶜ < ENNReal.ofReal ε := by
    have h : ν₂m (Metric.closedBall (0 : Point) 1)ᶜ = 0 :=
      tail_bound_from_unit_ball_bridge h_supp2
    rw [h]
    positivity

  -- Step 4: Call two-ends contradiction
  exact concentrated_two_ends_contradiction
    ν₁ ν₂ G K C σ τ r c κ (1 : ℝ)
    hσ hσ_lt_one hτ hr hr_small hκ hκ_lt_one hC hK hG_meas hG_subset hν₂_growth hG_reverse
    threshold hthreshold_pos hthreshold_large
    X_conc hX_conc_meas hX_conc_subset
    h_per_x_mass
    h_inner_small h_r_log_small h_r_final h_card_strong
    (by norm_num) h_tail1 h_tail2 h_r2τ_small h_annulus_large

end B1
end RadialBootstrapping
