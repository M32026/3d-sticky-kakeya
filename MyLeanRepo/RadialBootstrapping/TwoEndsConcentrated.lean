module

/-
  TwoEndsConcentrated.lean

  Per-tube two-ends mass bound for the concentrated case.

  Given a concentrated tube ℓ with center z_ℓ, y in the concentrating ball,
  mass lower bound on the tube, and Frostman bound, find an annulus around y
  with mass ≥ r^(σ+4τ).

  Uses dyadic_annulus_pigeonhole from PigeonholeHelpers.
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.PigeonholeHelpers
public import MyLeanRepo.RadialBootstrapping.HBarMeasurable
public import MyLeanRepo.RadialBootstrapping.ConcentratedHPrime
public import MyLeanRepo.RadialBootstrapping.DirectionExtraction
public import MyLeanRepo.RadialBootstrapping.ConcentratedCase
public import MyLeanRepo.RadialBootstrapping.CountBoundGeneral
public import MyLeanRepo.RadialBootstrapping.WxiBound
public import MyLeanRepo.RadialBootstrapping.ConcentratedCaseFull
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set Finset Classical
open scoped ENNReal NNReal

set_option maxHeartbeats 500000

noncomputable section

namespace RadialBootstrapping

/-- Strong version of per_tube_two_ends_mass using a weaker concentration bound
    and the strong dyadic card bound.

    Given mass ≥ threshold in the r^κ-ball, and threshold > (1/6 + 1/1584)*r^(σ+3τ),
    obtains an annulus with mass > r^(σ+4τ). -/
lemma per_tube_two_ends_mass_strong
    {ν₂ : Measure Point} [IsProbabilityMeasure ν₂]
    (ℓ : AffineSubspace ℝ Point)
    (x y z : Point)
    (r κ σ τ C : ℝ)
    (threshold : ℝ)
    (hr : 0 < r) (hr_small : r < 1)
    (hσ : 0 ≤ σ) (hτ : 0 < τ)
    (hκ_pos : 0 < κ) (hκ_lt_one : κ < 1)
    (hC : 1 ≤ C)
    (h_finrank : Module.finrank ℝ ℓ.direction = 1)
    (x_in_ℓ : x ∈ (ℓ : Set Point))
    (z_in_ball : dist z y < Real.rpow r κ)
    (S : Set Point)
    (hS_sub_tube : S ⊆ Metric.thickening r (ℓ : Set Point))
    (hS_meas : MeasurableSet S)
    (h_conc : ν₂ (S ∩ Metric.ball z (Real.rpow r κ)) ≥
        ENNReal.ofReal threshold)
    (hFrostman : ∀ (p : Point) (ρ : ℝ), 0 < ρ →
        ν₂ (Metric.ball p ρ) ≤ ENNReal.ofReal (C * ρ))
    (h_inner_small : C * r ≤ (1 / 6 : ℝ) * Real.rpow r (σ + 3 * τ))
    (h_r_log_small : Real.rpow r τ * Real.log (1 / r) ≤ 1 / 100)
    (h_r_final : 20 * C * Real.rpow r τ < 1)
    (h_threshold_pos : 0 < threshold)
    (h_threshold_gt_inner : (1 / 6 : ℝ) * Real.rpow r (σ + 3 * τ) < threshold)
    (h_card_strong : (Nat.ceil ((1 - κ) * Real.log (1 / r) / Real.log 2) + 1 : ℝ) ≤
        (1 / 1584 : ℝ) * Real.rpow r (-τ))
    (h_threshold_large : threshold > (1 / 6 + 1 / 1584 : ℝ) * Real.rpow r (σ + 3 * τ)) :
    ∃ (ξ : ℝ), ξ ∈ dyadicAnnulusScales r κ (Nat.ceil ((1 - κ) * Real.log (1 / r) / Real.log 2)) ∧
      r ≤ ξ ∧ ξ ≤ Real.rpow r κ ∧
      ν₂ (S ∩ {z' | ξ ≤ dist z' y ∧ dist z' y < 2 * ξ}) >
        ENNReal.ofReal (Real.rpow r (σ + 4 * τ)) := by
  set r_kappa : ℝ := Real.rpow r κ with hr_kappa_def
  have hr_kappa_pos : 0 < r_kappa := Real.rpow_pos_of_pos hr κ
  have h1 : Metric.ball z r_kappa ⊆ Metric.ball y (2 * r_kappa) := by
    intro w hw
    have h_dist1 : dist w z < r_kappa := by simpa [Metric.mem_ball] using hw
    have h_dist2 : dist w y ≤ dist w z + dist z y := dist_triangle w z y
    have h_dist3 : dist w y < 2 * r_kappa := by
      calc dist w y ≤ dist w z + dist z y := h_dist2
        _ < r_kappa + r_kappa := by linarith
        _ = 2 * r_kappa := by ring
    simpa [Metric.mem_ball] using h_dist3
  have h_sigma3tau_nonneg : 0 ≤ σ + 3 * τ := by linarith
  set inner : ℝ := (1 / 6 : ℝ) * Real.rpow r (σ + 3 * τ) with hinner_def
  set card_bound_val : ℝ := (1 / 1584 : ℝ) * Real.rpow r (-τ) with hcard_def
  have h_inner_nonneg : 0 ≤ inner := by
    have h : 0 ≤ Real.rpow r (σ + 3 * τ) := Real.rpow_nonneg (by linarith) _
    positivity
  have h_card_bound_pos : 0 < card_bound_val := by
    have h : 0 < Real.rpow r (-τ) := Real.rpow_pos_of_pos hr (-τ)
    positivity
  have h_card_bound_real : ((dyadicAnnulusScales r κ (Nat.ceil ((1 - κ) * Real.log (1 / r) / Real.log 2))).card : ℝ) ≤ card_bound_val := by
    have h1 : (dyadicAnnulusScales r κ (Nat.ceil ((1 - κ) * Real.log (1 / r) / Real.log 2))).card ≤
        Nat.ceil ((1 - κ) * Real.log (1 / r) / Real.log 2) + 1 := by
      let N := Nat.ceil ((1 - κ) * Real.log (1 / r) / Real.log 2)
      have h : (dyadicAnnulusScales r κ N).card ≤ N + 1 := by
        have h_def : dyadicAnnulusScales r κ N =
            (Finset.image (fun k : ℕ => r * (2 : ℝ)^k) (Finset.range N)) ∪ {Real.rpow r κ} := by
          simp [dyadicAnnulusScales] <;> rfl
        rw [h_def]
        have h1 : ((Finset.image (fun k : ℕ => r * (2 : ℝ)^k) (Finset.range N)) ∪ {Real.rpow r κ}).card ≤
            (Finset.image (fun k : ℕ => r * (2 : ℝ)^k) (Finset.range N)).card + 1 := by
          calc _ ≤ (Finset.image (fun k : ℕ => r * (2 : ℝ)^k) (Finset.range N)).card + ({Real.rpow r κ} : Finset ℝ).card := Finset.card_union_le _ _
            _ = (Finset.image (fun k : ℕ => r * (2 : ℝ)^k) (Finset.range N)).card + 1 := by simp
        have h2 : (Finset.image (fun k : ℕ => r * (2 : ℝ)^k) (Finset.range N)).card ≤ N := by
          have h21 : (Finset.image (fun k : ℕ => r * (2 : ℝ)^k) (Finset.range N)).card ≤ (Finset.range N).card :=
            Finset.card_image_le
          have h22 : (Finset.range N).card = N := by simp
          rw [h22] at h21
          exact h21
        linarith
      exact h
    have h2 : ((dyadicAnnulusScales r κ (Nat.ceil ((1 - κ) * Real.log (1 / r) / Real.log 2))).card : ℝ) ≤
        (Nat.ceil ((1 - κ) * Real.log (1 / r) / Real.log 2) + 1 : ℝ) := by exact_mod_cast h1
    exact le_trans h2 h_card_strong
  have h_outer : ν₂ (S ∩ Metric.ball y (2 * r_kappa)) ≥ ENNReal.ofReal threshold := by
    have h_sub : S ∩ Metric.ball z r_kappa ⊆ S ∩ Metric.ball y (2 * r_kappa) := by
      intro w hw; exact ⟨hw.1, h1 hw.2⟩
    exact le_trans h_conc (measure_mono h_sub)
  have h_inner : ν₂ (S ∩ Metric.ball y r) ≤ ENNReal.ofReal inner := by
    have h_sub : S ∩ Metric.ball y r ⊆ Metric.ball y r := by intro w hw; exact hw.2
    have h2 : ν₂ (S ∩ Metric.ball y r) ≤ ν₂ (Metric.ball y r) := measure_mono h_sub
    have h3 : ν₂ (Metric.ball y r) ≤ ENNReal.ofReal (C * r) := hFrostman y r hr
    have h4 : ENNReal.ofReal (C * r) ≤ ENNReal.ofReal inner := by
      rw [hinner_def]; exact ENNReal.ofReal_le_ofReal h_inner_small
    exact le_trans (le_trans h2 h3) h4
  rcases dyadic_annulus_pigeonhole_strong ν₂ y r κ σ τ C threshold inner card_bound_val
      hr hr_small hσ hτ hC hκ_pos hκ_lt_one S h_outer h_inner h_inner_nonneg h_threshold_pos
      h_threshold_gt_inner h_card_bound_pos h_card_bound_real
    with ⟨ξ, hξ_in, hξ_ge, hξ_le, h_mass⟩
  have h_ann_mass_large : ν₂ (S ∩ {z' | ξ ≤ dist z' y ∧ dist z' y < 2 * ξ}) >
      ENNReal.ofReal (Real.rpow r (σ + 4 * τ)) := by
    have h5 : ν₂ (S ∩ {z' | ξ ≤ dist z' y ∧ dist z' y < 2 * ξ}) ≥
        ENNReal.ofReal ((threshold - inner) / card_bound_val) := h_mass
    have h6 : (threshold - inner) / card_bound_val > Real.rpow r (σ + 4 * τ) := by
      rw [hinner_def, hcard_def]
      have h7 : Real.rpow r (σ + 3 * τ) / Real.rpow r (-τ) = Real.rpow r (σ + 4 * τ) := by
        have h_sub := (Real.rpow_sub hr (σ + 3 * τ) (-τ)).symm
        have h8 : (σ + 3 * τ) - (-τ) = σ + 4 * τ := by ring
        rw [h8] at h_sub; exact h_sub
      have h9 : (threshold - (1 / 6 : ℝ) * Real.rpow r (σ + 3 * τ)) /
          ((1 / 1584 : ℝ) * Real.rpow r (-τ)) =
          (threshold - (1 / 6 : ℝ) * Real.rpow r (σ + 3 * τ)) / Real.rpow r (-τ) * (1584 : ℝ) := by
        field_simp
        <;> ring
      rw [h9]
      have h10 : threshold - (1 / 6 : ℝ) * Real.rpow r (σ + 3 * τ) >
          (1 / 1584 : ℝ) * Real.rpow r (σ + 3 * τ) := by
        have h11 : threshold > (1 / 6 + 1 / 1584 : ℝ) * Real.rpow r (σ + 3 * τ) := h_threshold_large
        have h12 : (1 / 6 + 1 / 1584 : ℝ) * Real.rpow r (σ + 3 * τ) =
            (1 / 6 : ℝ) * Real.rpow r (σ + 3 * τ) + (1 / 1584 : ℝ) * Real.rpow r (σ + 3 * τ) := by ring
        rw [h12] at h11
        linarith
      have h13 : (threshold - (1 / 6 : ℝ) * Real.rpow r (σ + 3 * τ)) / Real.rpow r (-τ) >
          (1 / 1584 : ℝ) * Real.rpow r (σ + 3 * τ) / Real.rpow r (-τ) := by
        gcongr
        <;> exact Real.rpow_pos_of_pos hr (-τ)
      have h14 : (1 / 1584 : ℝ) * Real.rpow r (σ + 3 * τ) / Real.rpow r (-τ) =
          (1 / 1584 : ℝ) * Real.rpow r (σ + 4 * τ) := by
        have h141 : (1 / 1584 : ℝ) * Real.rpow r (σ + 3 * τ) / Real.rpow r (-τ) =
            (1 / 1584 : ℝ) * (Real.rpow r (σ + 3 * τ) / Real.rpow r (-τ)) := by ring
        rw [h141, h7] <;> ring
      rw [h14] at h13
      have h15 : (threshold - (1 / 6 : ℝ) * Real.rpow r (σ + 3 * τ)) / Real.rpow r (-τ) * (1584 : ℝ) >
          (1 / 1584 : ℝ) * Real.rpow r (σ + 4 * τ) * (1584 : ℝ) := by gcongr
      have h16 : (1 / 1584 : ℝ) * Real.rpow r (σ + 4 * τ) * (1584 : ℝ) = Real.rpow r (σ + 4 * τ) := by
        field_simp <;> ring
      rw [h16] at h15
      exact h15
    have h7 : ENNReal.ofReal ((threshold - inner) / card_bound_val) >
        ENNReal.ofReal (Real.rpow r (σ + 4 * τ)) := by
      exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr h6
    exact lt_of_lt_of_le h7 h5
  exact ⟨ξ, hξ_in, hξ_ge, hξ_le, h_ann_mass_large⟩

/-- Exponent inequality: κ = 14τ/(1-σ) and κ < 1 implies σ + 4τ < 1. -/
lemma exponent_sigma_4tau_lt_one {σ τ κ : ℝ} (hσ : 0 ≤ σ) (hσ_lt_one : σ < 1)
    (hτ : 0 < τ) (hκ : κ = 14 * τ / (1 - σ)) (hκ_lt_one : κ < 1) :
    σ + 4 * τ < 1 := by
  have h1 : 14 * τ < 1 - σ := by
    rw [hκ] at hκ_lt_one
    have h2 : 0 < 1 - σ := by linarith
    have h3 : 14 * τ / (1 - σ) < 1 := hκ_lt_one
    have h4 : 14 * τ < 1 - σ := by
      calc 14 * τ = (14 * τ / (1 - σ)) * (1 - σ) := by field_simp [h2.ne'] <;> ring
      _ < 1 * (1 - σ) := by gcongr <;> linarith
      _ = 1 - σ := by ring
    exact h4
  linarith

/-- Full concentrated-case contradiction via the two-ends argument. -/
lemma concentrated_two_ends_contradiction
    (ν₁ ν₂ : ProbabilityMeasure Point)
    (G : Set (Point × Point))
    (K C σ τ r c κ R : ℝ)
    (hσ : 0 ≤ σ) (hσ_lt_one : σ < 1) (hτ : 0 < τ)
    (hr : 0 < r) (hr_small : r < 1)
    (hκ : κ = 14 * τ / (1 - σ)) (hκ_lt_one : κ < 1)
    (hC : 1 ≤ C) (hK : 1 ≤ K)
    (hG_meas : MeasurableSet G)
    (hG_sub_supp : G ⊆ (ν₁ : Measure Point).support ×ˢ (ν₂ : Measure Point).support)
    (hν₂_growth : ∀ (x : Point) (ρ : ℝ), 0 < ρ →
      ν₂ (Metric.ball x ρ) ≤ Real.toNNReal (C * ρ))
    (hG_reverse : ∀ y ∈ (ν₂ : Measure Point).support,
      ∀ ℓ : AffineSubspace ℝ Point, y ∈ (ℓ : Set Point) →
        Module.finrank ℝ ℓ.direction = 1 → ∀ r' : ℝ, 0 < r' →
          ν₁ {b₁ | b₁ ∈ Metric.thickening r' (ℓ : Set Point) ∧ (b₁, y) ∈ G} ≤
            ENNReal.ofReal (K * Real.rpow r' σ))
    (threshold : ℝ)
    (hthreshold_pos : 0 < threshold)
    (hthreshold_large : threshold > (1 / 6 + 1 / 1584 : ℝ) * Real.rpow r (σ + 3 * τ))
    (X_conc : Set Point)
    (hX_conc_mass : (ν₁ : Measure Point) X_conc ≥ ENNReal.ofReal (Real.rpow r τ / 2))
    (hX_conc_supp : X_conc ⊆ (ν₁ : Measure Point).support)
    -- Per-x mass for H' fiber (CH' ∩ G)
    (h_per_x_mass : ∀ x ∈ X_conc,
      (ν₂ : Measure Point) {y | (x, y) ∈ ConcentratedH' ν₂ G r κ threshold ∧ (x, y) ∈ G}
        ≥ ENNReal.ofReal ((1 / 396 : ℝ) * Real.rpow r (6 * τ)))
    (h_inner_small : C * r ≤ (1 / 6 : ℝ) * Real.rpow r (σ + 3 * τ))
    (h_r_log_small : Real.rpow r τ * Real.log (1 / r) ≤ 1 / 100)
    (h_r_final : 20 * C * Real.rpow r τ < 1)
    -- Strong card bound: scales.card ≤ (1/1584) * r^(-τ)
    (h_card_strong : (Nat.ceil ((1 - κ) * Real.log (1 / r) / Real.log 2) + 1 : ℝ) ≤
      (1 / 1584 : ℝ) * Real.rpow r (-τ))
    -- Localization
    (hR_pos : 0 < R)
    (h_tail1 : (ν₁ : Measure Point) ((Metric.closedBall (0 : Point) R)ᶜ) <
        ENNReal.ofReal (Real.rpow r (7 * τ) / 6336))
    (h_tail2 : (ν₂ : Measure Point) ((Metric.closedBall (0 : Point) R)ᶜ) <
        ENNReal.ofReal (Real.rpow r (7 * τ) / 6336))
    -- Small-r condition for count bound
    (h_r2τ_small : Real.rpow r (2 * τ) <
        1 / (390 * K * C * Real.rpow (1 + (2 * R + 1) / 8) σ))
    -- Direct contradiction when ξ < 2r: r^(σ+4τ) > 4Cr
    (h_annulus_large : Real.rpow r (σ + 4 * τ) > 4 * C * r) :
    False := by
  classical
  let ν₁m : Measure Point := ν₁
  let ν₂m : Measure Point := ν₂
  have hν₂_growth' : ∀ (p : Point) (ρ : ℝ), 0 < ρ →
      ν₂m (Metric.ball p ρ) ≤ ENNReal.ofReal (C * ρ) := by
    intro p ρ hρ
    have h : ν₂ (Metric.ball p ρ) ≤ Real.toNNReal (C * ρ) := hν₂_growth p ρ hρ
    have h_pos : 0 ≤ C * ρ := by positivity
    have h_eq : (Real.toNNReal (C * ρ) : ENNReal) = ENNReal.ofReal (C * ρ) := by
      have h5 : (Real.toNNReal (C * ρ) : ℝ) = C * ρ := by
        simp [Real.coe_toNNReal, h_pos]
      rw [← ENNReal.ofReal_coe_nnreal, h5]
    have h_coe : ν₂m (Metric.ball p ρ) = (ν₂ (Metric.ball p ρ) : ENNReal) :=
      (ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν₂ _).symm
    have h_cast : (ν₂ (Metric.ball p ρ) : ENNReal) ≤ (Real.toNNReal (C * ρ) : ENNReal) := by
      exact_mod_cast h
    rw [h_coe]
    exact le_trans h_cast (le_of_eq h_eq)
  have hthreshold_nonneg' : 0 ≤ threshold := le_of_lt hthreshold_pos
  have hκ_pos : 0 < κ := by
    rw [hκ]
    have h1 : 0 < 1 - σ := by linarith
    have h2 : 0 < 14 * τ := by positivity
    exact div_pos h2 h1
  have hrκ_pos : 0 < Real.rpow r κ := Real.rpow_pos_of_pos hr κ
  have h_sigma4tau_lt_one : σ + 4 * τ < 1 :=
    exponent_sigma_4tau_lt_one hσ hσ_lt_one hτ hκ hκ_lt_one

  -- Step 1: Define H' = CH' ∩ (X_conc × univ) ∩ G
  let CH' : Set (Point × Point) := ConcentratedH' ν₂ G r κ threshold
  have hCH'_meas : MeasurableSet CH' :=
    ConcentratedH'_measurable ν₂ G hG_meas r κ threshold hr hrκ_pos hthreshold_nonneg'
  let H' : Set (Point × Point) := CH' ∩ G
  have hH'_meas : MeasurableSet H' :=
    hCH'_meas.inter hG_meas

  have hH'_x_mass : ∀ x ∈ X_conc,
      ν₂m {y | (x, y) ∈ H'} ≥ ENNReal.ofReal ((1 / 396 : ℝ) * Real.rpow r (6 * τ)) := by
    intro x hx
    have h1 : {y | (x, y) ∈ H'} =
        {y | (x, y) ∈ CH' ∧ (x, y) ∈ G} := by
      ext y
      simp [H', Set.mem_inter_iff]
      <;> rfl
    rw [h1]
    exact h_per_x_mass x hx

  have hH'_prod : (ν₁m.prod ν₂m) H' ≥
      ENNReal.ofReal ((1 / 792 : ℝ) * Real.rpow r (7 * τ)) := by
    have h_fubini : (ν₁m.prod ν₂m) H' = ∫⁻ x, ν₂m {y | (x, y) ∈ H'} ∂ν₁m := by exact Measure.prod_apply hH'_meas
    let c_H' : ENNReal := ENNReal.ofReal ((1 / 396 : ℝ) * Real.rpow r (6 * τ))
    let f : Point → ENNReal := fun x => ν₂m {y | (x, y) ∈ H'}
    have hf_meas : Measurable f := by
      exact measurable_measure_prodMk_left_finite hH'_meas
    let S : Set Point := {x | f x ≥ c_H'}
    have hS_meas : MeasurableSet S := hf_meas measurableSet_Ici
    have hX_sub_S : X_conc ⊆ S := by
      intro x hx
      have h : f x ≥ c_H' := hH'_x_mass x hx
      exact h
    have h2 : ∫⁻ x, f x ∂ν₁m ≥ ∫⁻ x, (S.indicator (fun _ => c_H')) x ∂ν₁m := by
      apply lintegral_mono; intro x
      by_cases hx : x ∈ S
      · have h_ge : f x ≥ c_H' := hx
        simpa [hx, Set.indicator_apply] using h_ge
      · simp [hx, Set.indicator_apply] <;> positivity
    have h3 : ∫⁻ x, (S.indicator (fun _ => c_H')) x ∂ν₁m = c_H' * ν₁m S := by
      rw [lintegral_indicator hS_meas]
      <;> simp [mul_comm] <;> ring
    have h4 : ν₁m S ≥ ν₁m X_conc := measure_mono hX_sub_S
    have h5 : ν₁m X_conc ≥ ENNReal.ofReal (Real.rpow r τ / 2) := hX_conc_mass
    have h6 : c_H' * ν₁m S ≥ c_H' * ν₁m X_conc := by gcongr
    have h7 : c_H' * ν₁m X_conc ≥
        c_H' * ENNReal.ofReal (Real.rpow r τ / 2) := by gcongr
    have hpos1 : 0 ≤ (1 / 396 : ℝ) * Real.rpow r (6 * τ) := by
      have h : 0 ≤ Real.rpow r (6 * τ) := Real.rpow_nonneg hr.le _
      exact mul_nonneg (by norm_num) h
    have hpos2 : 0 ≤ Real.rpow r τ / 2 := by
      have h : 0 ≤ Real.rpow r τ := Real.rpow_nonneg hr.le _
      exact div_nonneg h (by norm_num)
    calc (ν₁m.prod ν₂m) H'
      = ∫⁻ x, f x ∂ν₁m := h_fubini
    _ ≥ ∫⁻ x, (S.indicator (fun _ => c_H')) x ∂ν₁m := h2
    _ = c_H' * ν₁m S := h3
    _ ≥ c_H' * ν₁m X_conc := h6
    _ ≥ c_H' * ENNReal.ofReal (Real.rpow r τ / 2) := h7
    _ = ENNReal.ofReal (((1 / 396 : ℝ) * Real.rpow r (6 * τ)) * (Real.rpow r τ / 2)) := by
      rw [← ENNReal.ofReal_mul hpos1] <;> rfl
    _ = ENNReal.ofReal ((1 / 792 : ℝ) * Real.rpow r (7 * τ)) := by
      congr 1
      have h8 : Real.rpow r (6 * τ) * Real.rpow r τ = Real.rpow r (7 * τ) := by
        have h9 := Real.rpow_add hr (6 * τ) τ
        have h10 : (6 * τ) + τ = 7 * τ := by ring
        rw [h10] at h9; exact h9.symm
      ring_nf at * <;> linarith

  -- Step 2: Localize
  let ε : ℝ := Real.rpow r (7 * τ) / 6336
  have hε_pos : 0 < ε := by
    dsimp only [ε]; have h1 : 0 < Real.rpow r (7 * τ) := Real.rpow_pos_of_pos hr (7 * τ)
    positivity
  let B : Set Point := Metric.closedBall (0 : Point) R
  have hB_meas : MeasurableSet B := measurableSet_closedBall
  let H'_R : Set (Point × Point) := H' ∩ (B ×ˢ B)
  have hH'R_meas : MeasurableSet H'_R := hH'_meas.inter (hB_meas.prod hB_meas)

  have h_tail_bound : (ν₁m.prod ν₂m) (H' \ H'_R) < ENNReal.ofReal (2 * ε) := by
    have h_sub : H' \ H'_R ⊆ (Bᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ Bᶜ) := by
      rintro ⟨x, y⟩ ⟨h_in_H', h_not_in_R⟩
      have h_not_both : x ∉ B ∨ y ∉ B := by
        by_contra h; push Not at h
        have h_in : (x, y) ∈ B ×ˢ B := ⟨h.1, h.2⟩
        have h_in_H'R : (x, y) ∈ H'_R := ⟨h_in_H', h_in⟩
        exact h_not_in_R h_in_H'R
      rcases h_not_both with (h | h)
      · exact Or.inl ⟨h, trivial⟩
      · exact Or.inr ⟨trivial, h⟩
    have h1 : (ν₁m.prod ν₂m) ((Bᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ Bᶜ)) ≤
        (ν₁m.prod ν₂m) (Bᶜ ×ˢ Set.univ) + (ν₁m.prod ν₂m) (Set.univ ×ˢ Bᶜ) :=
      measure_union_le _ _
    have h2 : (ν₁m.prod ν₂m) (Bᶜ ×ˢ Set.univ) = ν₁m Bᶜ := by
      simpa [Measure.prod_prod] using rfl
    have h3 : (ν₁m.prod ν₂m) (Set.univ ×ˢ Bᶜ) = ν₂m Bᶜ := by
      simpa [Measure.prod_prod] using rfl
    have h4 : (ν₁m.prod ν₂m) (H' \ H'_R) ≤ ν₁m Bᶜ + ν₂m Bᶜ := by
      calc (ν₁m.prod ν₂m) (H' \ H'_R)
        ≤ (ν₁m.prod ν₂m) ((Bᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ Bᶜ)) := measure_mono h_sub
      _ ≤ (ν₁m.prod ν₂m) (Bᶜ ×ˢ Set.univ) + (ν₁m.prod ν₂m) (Set.univ ×ˢ Bᶜ) := h1
      _ = ν₁m Bᶜ + ν₂m Bᶜ := by rw [h2, h3]
    have h5 : ν₁m Bᶜ + ν₂m Bᶜ < ENNReal.ofReal ε + ENNReal.ofReal ε :=
      ENNReal.add_lt_add h_tail1 h_tail2
    have h6 : ENNReal.ofReal ε + ENNReal.ofReal ε = ENNReal.ofReal (2 * ε) := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)] <;> ring_nf
    rw [h6] at h5
    exact lt_of_le_of_lt h4 h5

  have hH'R_prod : (ν₁m.prod ν₂m) H'_R ≥
      ENNReal.ofReal (3 * Real.rpow r (7 * τ) / 3168) := by
    have h_union : H' = H'_R ∪ (H' \ H'_R) := by
      ext p; simp [H'_R] <;> tauto
    have h_disj : Disjoint H'_R (H' \ H'_R) := by exact Disjoint.symm disjoint_sdiff_left
    have h_diff_meas : MeasurableSet (H' \ H'_R) := hH'_meas.diff hH'R_meas
    have h_eq : (ν₁m.prod ν₂m) H' = (ν₁m.prod ν₂m) H'_R + (ν₁m.prod ν₂m) (H' \ H'_R) := by
      rw [h_union]
      have h_add : (ν₁m.prod ν₂m) (H'_R ∪ (H' \ H'_R)) + (ν₁m.prod ν₂m) (H'_R ∩ (H' \ H'_R)) =
          (ν₁m.prod ν₂m) H'_R + (ν₁m.prod ν₂m) (H' \ H'_R) :=
        measure_union_add_inter' hH'R_meas (H' \ H'_R)
      have h_empty : H'_R ∩ (H' \ H'_R) = ∅ := by
        ext z; simp [Set.disjoint_left.mp h_disj] <;> tauto
      rw [h_empty] at h_add; simpa using h_add
    have h_top : (ν₁m.prod ν₂m) (H' \ H'_R) ≠ ⊤ :=
      ne_of_lt (lt_of_lt_of_le h_tail_bound (by simp))
    have h_sub : (ν₁m.prod ν₂m) H'_R ≥ (ν₁m.prod ν₂m) H' - (ν₁m.prod ν₂m) (H' \ H'_R) := by
      rw [h_eq]; simp [h_top] <;> exact le_refl _
    have h7 : (ν₁m.prod ν₂m) H' - (ν₁m.prod ν₂m) (H' \ H'_R) ≥
        ENNReal.ofReal ((1 / 792 : ℝ) * Real.rpow r (7 * τ)) - ENNReal.ofReal (2 * ε) := by
      gcongr <;> exact le_of_lt h_tail_bound
    have h8 : ENNReal.ofReal ((1 / 792 : ℝ) * Real.rpow r (7 * τ)) - ENNReal.ofReal (2 * ε) =
        ENNReal.ofReal (((1 / 792 : ℝ) * Real.rpow r (7 * τ)) - 2 * ε) := by
      have h9 : 0 ≤ (2 * ε) := by linarith
      have h10 : (2 * ε) ≤ (1 / 792 : ℝ) * Real.rpow r (7 * τ) := by
        dsimp only [ε]
        have h11 : 0 ≤ Real.rpow r (7 * τ) := Real.rpow_nonneg hr.le _
        nlinarith
      exact Eq.symm (ENNReal.ofReal_sub (1 / 792 * r.rpow (7 * τ)) h9)
    rw [h8] at h7
    have h9 : ((1 / 792 : ℝ) * Real.rpow r (7 * τ)) - 2 * ε =
        3 * Real.rpow r (7 * τ) / 3168 := by
      dsimp only [ε]; ring
    rw [h9] at h7
    exact le_trans h7 h_sub

  have h_dist_bound : ∀ p ∈ H'_R, dist p.1 p.2 ≤ 2 * R := by
    rintro ⟨x, y⟩ ⟨_, hx, hy⟩
    have h1 : dist x (0 : Point) ≤ R := by simpa [B, Metric.mem_closedBall] using hx
    have h2 : dist y (0 : Point) ≤ R := by simpa [B, Metric.mem_closedBall] using hy
    have h3 : dist x y ≤ dist x (0 : Point) + dist (0 : Point) y := dist_triangle _ _ _
    have h4 : dist (0 : Point) y = dist y (0 : Point) := dist_comm _ _
    rw [h4] at h3; linarith

  -- Step 3: Scales (same as dyadic_annulus_pigeonhole internal scales)
  let N : ℕ := Nat.ceil ((1 - κ) * Real.log (1 / r) / Real.log 2)
  let x_val : ℝ := (1 - κ) * Real.log (1 / r) / Real.log 2
  let scales : Finset ℝ :=
    Finset.image (fun k : ℕ => r * (2 : ℝ)^k) (Finset.range N) ∪ {Real.rpow r κ}

  have hx_val_pos : 0 < x_val := by
    dsimp only [x_val]
    have h1 : 0 < 1 - κ := by linarith
    have h2 : 1 < 1 / r := by apply one_lt_one_div <;> linarith
    have h3 : 0 < Real.log (1 / r) := Real.log_pos h2
    have h4 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hN_pos : 0 < N := Nat.ceil_pos.mpr hx_val_pos
  have h_pow_id : (2 : ℝ)^x_val = Real.rpow r (κ - 1) :=
    dyadic_pow_identity r κ hr hr_small hκ_pos hκ_lt_one

  have h_scales_bounds : ∀ ξ ∈ scales, r ≤ ξ ∧ ξ ≤ Real.rpow r κ := by
    intro ξ hξ
    rw [Finset.mem_union] at hξ
    rcases hξ with (hξ | hξ)
    · rcases Finset.mem_image.mp hξ with ⟨k, hk, rfl⟩
      have hk_lt : k < N := Finset.mem_range.mp hk
      have h_lower : r ≤ r * (2 : ℝ)^k := by
        have h2 : (1 : ℝ) ≤ (2 : ℝ)^k := by
          have h3 : ∀ n : ℕ, (1 : ℝ) ≤ (2 : ℝ)^n := by
            intro n; induction n with
            | zero => norm_num
            | succ n ih => simp [pow_succ] at * <;> nlinarith
          exact h3 k
        nlinarith
      have h_k_le : k ≤ N - 1 := by omega
      have h_pow_le : (2 : ℝ)^k ≤ (2 : ℝ)^(N - 1) := by
        have h_mono : ∀ m n : ℕ, m ≤ n → (2 : ℝ)^m ≤ (2 : ℝ)^n := by
          intro m n hmn; induction' hmn with n hmn ih
          · simp
          · calc (2 : ℝ)^m ≤ (2 : ℝ)^n := ih
            _ ≤ (2 : ℝ)^(n + 1) := by simp [pow_succ] <;> norm_num <;> linarith
        exact h_mono k (N - 1) h_k_le
      have h7 : ((N - 1 : ℕ) : ℝ) < x_val := by
        have h_nonneg : 0 ≤ x_val := by linarith
        have h8 : (N : ℝ) < x_val + 1 := Nat.ceil_lt_add_one h_nonneg
        have hN_pos' : 0 < N := hN_pos
        have h9 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
          have h1 : 1 ≤ N := by omega
          rw [Nat.cast_sub h1] <;> norm_num
        rw [h9]
        linarith
      have h8 : (2 : ℝ)^(N - 1) < (2 : ℝ)^x_val := by
        have h_cast : (2 : ℝ)^(N - 1) = (2 : ℝ)^((N - 1 : ℕ) : ℝ) := by norm_cast
        rw [h_cast]
        have h_base : 1 < (2 : ℝ) := by norm_num
        exact Real.rpow_lt_rpow_of_exponent_lt h_base h7
      have h_upper : r * (2 : ℝ)^k < Real.rpow r κ := by
        calc r * (2 : ℝ)^k
          ≤ r * (2 : ℝ)^(N - 1) := by gcongr
        _ < r * (2 : ℝ)^x_val := by gcongr
        _ = r * Real.rpow r (κ - 1) := by rw [h_pow_id]
        _ = Real.rpow r κ := by
          have h10 : Real.rpow r (1 + (κ - 1)) = Real.rpow r 1 * Real.rpow r (κ - 1) :=
            Real.rpow_add hr 1 (κ - 1)
          have h11 : 1 + (κ - 1) = κ := by ring
          have h12 : Real.rpow r 1 = r := by simp
          rw [h11, h12] at h10
          exact h10.symm
      exact ⟨h_lower, le_of_lt h_upper⟩
    · rw [Finset.mem_singleton] at hξ
      rw [hξ]
      have h_r_le_rκ : r ≤ Real.rpow r κ := by
        have h : Real.rpow r 1 < Real.rpow r κ :=
          Real.rpow_lt_rpow_of_exponent_gt hr hr_small hκ_lt_one
        have h2 : Real.rpow r 1 = r := by simp
        rw [h2] at h
        exact le_of_lt h
      exact ⟨h_r_le_rκ, le_refl _⟩

  have h_scales_card_strong : (scales.card : ℝ) ≤ (1 / 1584 : ℝ) * Real.rpow r (-τ) := by
    have h1 : scales.card ≤ N + 1 := by
      have h2 : (Finset.image (fun k : ℕ => r * (2 : ℝ)^k) (Finset.range N)).card ≤ N :=
        by exact Finset.card_image_le.trans (by simp [N])
      have h3 : scales.card ≤ (Finset.image (fun k : ℕ => r * (2 : ℝ)^k) (Finset.range N)).card + 1 := by
        exact Finset.card_union_le _ _
      linarith
    have h5 : (scales.card : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    have h6 : ((N + 1 : ℕ) : ℝ) ≤ (1 / 1584 : ℝ) * Real.rpow r (-τ) := by
      simpa [N] using h_card_strong
    exact le_trans h5 h6

  -- Step 4: Countable dense subset and S_nc definitions
  rcases TopologicalSpace.exists_countable_dense (UnitSphere' × Point) with ⟨D, hD_count, hD_dense⟩
  let S_nc (nc : UnitSphere' × Point) : Set (Point × Point) :=
    ConcentratedH'_S ν₂ G r κ threshold nc
  have hCH'_eq : CH' = ⋃ nc ∈ D, S_nc nc :=
    ConcentratedH'_eq_union ν₂ G hG_meas r κ threshold hr hrκ_pos hthreshold_nonneg' hD_count hD_dense

  let S_nc_ξ (nc : UnitSphere' × Point) (ξ : ℝ) : Set (Point × Point) :=
    {p ∈ S_nc nc |
      ν₂m (tubeOfNormal r p.1 nc.1 ∩
        {z | ξ ≤ dist z p.2 ∧ dist z p.2 < 2 * ξ} ∩
        {b₂ | (p.1, b₂) ∈ G}) ≥ ENNReal.ofReal (Real.rpow r (σ + 4 * τ))}

  have hS_nc_ξ_meas : ∀ (nc : UnitSphere' × Point) (ξ : ℝ),
      MeasurableSet (S_nc_ξ nc ξ) := by
    intro nc ξ
    have h1 : MeasurableSet (S_nc nc) :=
      ConcentratedH'_S_meas ν₂ G hG_meas r κ threshold hr hrκ_pos hthreshold_nonneg' nc
    let A : Set ((Point × Point) × Point) :=
      {p | |dot (p.2 - p.1.1) (nc.1 : Point)| < r ∧
        ξ ≤ dist p.2 p.1.2 ∧ dist p.2 p.1.2 < 2 * ξ ∧ (p.1.1, p.2) ∈ G}
    have h_cont1 : Continuous (fun p : (Point × Point) × Point =>
        |dot (p.2 - p.1.1) (nc.1 : Point)|) := by fun_prop
    have h_cont2 : Continuous (fun p : (Point × Point) × Point => dist p.2 p.1.2) := by fun_prop
    have hA1 : MeasurableSet {p : (Point × Point) × Point | |dot (p.2 - p.1.1) (nc.1 : Point)| < r} :=
      (isOpen_lt h_cont1 continuous_const).measurableSet
    have hA2 : MeasurableSet {p : (Point × Point) × Point | ξ ≤ dist p.2 p.1.2} :=
      (isClosed_le continuous_const h_cont2).measurableSet
    have hA3 : MeasurableSet {p : (Point × Point) × Point | dist p.2 p.1.2 < 2 * ξ} :=
      (isOpen_lt h_cont2 continuous_const).measurableSet
    have h_proj1 : Measurable (fun p : (Point × Point) × Point => p.1.1) :=
      measurable_fst.comp measurable_fst
    have h_proj2 : Measurable (fun p : (Point × Point) × Point => p.2) := measurable_snd
    have h_proj : Measurable (fun p : (Point × Point) × Point => (p.1.1, p.2)) := by
      exact Measurable.prodMk h_proj1 h_proj2 <;> aesop
    have hA4 : MeasurableSet {p : (Point × Point) × Point | (p.1.1, p.2) ∈ G} :=
      hG_meas.preimage h_proj
    have hA_meas : MeasurableSet A := by
      convert hA1.inter (hA2.inter hA3) |>.inter hA4 using 1
      <;> ext p <;> simp [A] <;> tauto
    have h_f_meas : Measurable (fun p : Point × Point => ν₂m {z | (p, z) ∈ A}) :=
      measurable_measure_prodMk_left_finite hA_meas
    let h4_set : Set (Point × Point) := {p |
        ENNReal.ofReal (Real.rpow r (σ + 4 * τ)) ≤ ν₂m {z | (p, z) ∈ A}}
    have h4 : MeasurableSet h4_set := measurableSet_le measurable_const h_f_meas
    have h5 : S_nc_ξ nc ξ = (S_nc nc) ∩ h4_set := by
      ext p
      dsimp only [S_nc_ξ, h4_set]
      simp only [Set.mem_sep_iff, Set.mem_inter_iff, Set.mem_setOf_eq]
      have hA_eq : {z : Point | (p, z) ∈ A} =
          tubeOfNormal r p.1 nc.1 ∩
          {z | ξ ≤ dist z p.2 ∧ dist z p.2 < 2 * ξ} ∩
          {b₂ | (p.1, b₂) ∈ G} := by
        ext z
        simp [A, tubeOfNormal, Set.mem_inter_iff]
        <;> constructor <;> intro h <;> aesop
      rw [hA_eq]
      <;> rfl
    rw [h5]; exact h1.inter h4

  let H''_ξ (ξ : ℝ) : Set (Point × Point) :=
    H'_R ∩ ⋃ nc ∈ D, S_nc_ξ nc ξ

  have hH''_ξ_meas : ∀ ξ ∈ scales, MeasurableSet (H''_ξ ξ) := by
    intro ξ _
    have h_union_meas : MeasurableSet (⋃ nc ∈ D, S_nc_ξ nc ξ) :=
      MeasurableSet.biUnion hD_count (fun nc _ => hS_nc_ξ_meas nc ξ)
    exact hH'R_meas.inter h_union_meas

  -- Step 5: Cover H'_R ⊆ ⋃ ξ ∈ scales, H''_ξ ξ
  have h_cover : H'_R ⊆ ⋃ ξ ∈ scales, H''_ξ ξ := by
    intro p hp
    have h_p_in_H' : p ∈ H' := hp.1
    have h_p_in_CH' : p ∈ CH' := h_p_in_H'.1
    have h_p_in_G : p ∈ G := h_p_in_H'.2
    rcases (Set.mem_iUnion₂.mp (hCH'_eq ▸ h_p_in_CH')) with ⟨nc, hnc_D, hpn⟩
    let x := p.1
    let y := p.2
    let n : UnitSphere' := nc.1
    let c : Point := nc.2
    have h_mass : ν₂m (tubeOfNormal r x n ∩ Metric.ball c (Real.rpow r κ) ∩
        {b₂ | (x, b₂) ∈ G}) > ENNReal.ofReal threshold := hpn.1
    have h_y_in : y ∈ tubeOfNormal r x n ∩ Metric.ball c (Real.rpow r κ) := hpn.2
    have h_conc_mass : ν₂m (tubeOfNormal r x n ∩ Metric.ball c (Real.rpow r κ) ∩
        {b₂ | (x, b₂) ∈ G}) ≥ ENNReal.ofReal threshold :=
      le_of_lt h_mass
    let ℓ : AffineSubspace ℝ Point := lineOfNormal x n
    have h_finrank : Module.finrank ℝ ℓ.direction = 1 := lineOfNormal_finrank x n
    have h_x_in_ℓ : x ∈ (ℓ : Set Point) := by
      rw [mem_lineOfNormal_iff x n x] <;> simp
    have h_tube_eq : tubeOfNormal r x n = Metric.thickening r (ℓ : Set Point) :=
      tubeOfNormal_eq_thickening r hr x n
    let S_set : Set Point := tubeOfNormal r x n ∩ {b₂ | (x, b₂) ∈ G}
    have hS_meas : MeasurableSet S_set := by
      have h1 : MeasurableSet (tubeOfNormal r x n) :=
        (tubeOfNormal_open r hr x n).measurableSet
      have h2 : MeasurableSet {b₂ | (x, b₂) ∈ G} := by
        have hfg : Measurable (fun (b₂ : Point) => (x, b₂)) := by exact measurable_prodMk_left <;> aesop
        exact hG_meas.preimage hfg
      exact h1.inter h2
    have h_conc_mass2 : ν₂m (S_set ∩ Metric.ball c (Real.rpow r κ)) ≥
        ENNReal.ofReal threshold := by
      have h2 : S_set ∩ Metric.ball c (Real.rpow r κ) =
          tubeOfNormal r x n ∩ Metric.ball c (Real.rpow r κ) ∩ {b₂ | (x, b₂) ∈ G} := by
        ext z; simp [S_set, Set.mem_inter_iff] <;> tauto
      rw [h2]
      exact h_conc_mass
    have h_z_in_ball : dist c y < Real.rpow r κ := by
      have h : dist y c < Real.rpow r κ := by simpa [Metric.mem_ball] using h_y_in.2
      rw [dist_comm] at h
      exact h
    have hFrostman' : ∀ (p : Point) (ρ : ℝ), 0 < ρ →
        ν₂m (Metric.ball p ρ) ≤ ENNReal.ofReal (C * ρ) := hν₂_growth'
    have h_threshold_gt_inner : (1 / 6 : ℝ) * Real.rpow r (σ + 3 * τ) < threshold := by
      have h : (1 / 6 + 1 / 1584 : ℝ) * Real.rpow r (σ + 3 * τ) >
          (1 / 6 : ℝ) * Real.rpow r (σ + 3 * τ) := by
        have hpos : 0 < Real.rpow r (σ + 3 * τ) := Real.rpow_pos_of_pos hr _
        nlinarith
      exact lt_trans h hthreshold_large
    rcases per_tube_two_ends_mass_strong ℓ x y c r κ σ τ C threshold
        hr hr_small hσ hτ hκ_pos hκ_lt_one hC h_finrank h_x_in_ℓ h_z_in_ball
        S_set (by intro z hz; simpa [h_tube_eq] using hz.1) hS_meas
        h_conc_mass2 hFrostman' h_inner_small h_r_log_small h_r_final
        hthreshold_pos h_threshold_gt_inner h_card_strong hthreshold_large
      with ⟨ξ, hξ_scales, hξ_ge, hξ_le, h_ann_mass⟩
    have hξ_in_scales : ξ ∈ scales := by
      have h_eq : scales = dyadicAnnulusScales r κ N := by
        simp [scales, dyadicAnnulusScales] <;> rfl
      rw [h_eq]
      exact hξ_scales
    have h_p_in_Sncξ : p ∈ S_nc_ξ nc ξ := by
      have h_set_eq : tubeOfNormal r x n ∩
          {z | ξ ≤ dist z y ∧ dist z y < 2 * ξ} ∩ {b₂ | (x, b₂) ∈ G} =
          tubeOfNormal r x n ∩ {b₂ | (x, b₂) ∈ G} ∩
          {z' | ξ ≤ dist z' y ∧ dist z' y < 2 * ξ} := by
        ext z; simp [Set.mem_inter_iff] <;> tauto
      have h5 : ν₂m (tubeOfNormal r x n ∩
          {z | ξ ≤ dist z y ∧ dist z y < 2 * ξ} ∩ {b₂ | (x, b₂) ∈ G}) ≥
          ENNReal.ofReal (Real.rpow r (σ + 4 * τ)) := by
        rw [h_set_eq]
        exact le_of_lt h_ann_mass
      exact ⟨hpn, h5⟩
    have h6 : p ∈ H''_ξ ξ := by
      exact ⟨hp, Set.mem_iUnion₂.mpr ⟨nc, hnc_D, h_p_in_Sncξ⟩⟩
    exact Set.mem_iUnion₂.mpr ⟨ξ, hξ_in_scales, h6⟩

  -- Step 6: Pigeonhole
  have h_scales_nonempty : scales.Nonempty := by
    have h : Real.rpow r κ ∈ scales := by simp [scales]
    exact ⟨Real.rpow r κ, h⟩
  have h_sum : ∑ ξ ∈ scales, (ν₁m.prod ν₂m) (H''_ξ ξ) ≥
      (ν₁m.prod ν₂m) H'_R := by
    have h1 : H'_R ⊆ ⋃ ξ ∈ scales, H''_ξ ξ := h_cover
    have h2 : (ν₁m.prod ν₂m) H'_R ≤ (ν₁m.prod ν₂m) (⋃ ξ ∈ scales, H''_ξ ξ) :=
      measure_mono h1
    have h3 : (ν₁m.prod ν₂m) (⋃ ξ ∈ scales, H''_ξ ξ) ≤
        ∑ ξ ∈ scales, (ν₁m.prod ν₂m) (H''_ξ ξ) :=
      measure_biUnion_finset_le _ _
    exact le_trans h2 h3
  have h_sum' : ∑ ξ ∈ scales, (ν₁m.prod ν₂m) (H''_ξ ξ) ≥
      ENNReal.ofReal (3 * Real.rpow r (7 * τ) / 3168) :=
    le_trans hH'R_prod h_sum
  have h_pigeon := finset_pigeonhole_ennreal
    (fun ξ => (ν₁m.prod ν₂m) (H''_ξ ξ))
    ENNReal.ofReal_ne_top h_scales_nonempty h_sum'
  rcases h_pigeon with ⟨ξ₀, hξ₀_in, hξ₀_mass⟩
  have hξ₀_bounds : r ≤ ξ₀ ∧ ξ₀ ≤ Real.rpow r κ := h_scales_bounds ξ₀ hξ₀_in
  have hξ₀_pos : 0 < ξ₀ := by linarith [hξ₀_bounds.1]

  have hξ₀_lower : (ν₁m.prod ν₂m) (H''_ξ ξ₀) ≥
      ENNReal.ofReal (Real.rpow r (8 * τ)) := by
    have h2 : (scales.card : ENNReal) ≤
        ENNReal.ofReal ((1 / 1584 : ℝ) * Real.rpow r (-τ)) := by
      simpa using ENNReal.ofReal_le_ofReal h_scales_card_strong
    have h3 : (ν₁m.prod ν₂m) (H''_ξ ξ₀) ≥
        ENNReal.ofReal (3 * Real.rpow r (7 * τ) / 3168) / (scales.card : ENNReal) := hξ₀_mass
    have h4 : ENNReal.ofReal (3 * Real.rpow r (7 * τ) / 3168) / (scales.card : ENNReal) ≥
        ENNReal.ofReal (3 * Real.rpow r (7 * τ) / 3168) /
        ENNReal.ofReal ((1 / 1584 : ℝ) * Real.rpow r (-τ)) := by
      gcongr
    have h_pos1 : 0 < (1 / 1584 : ℝ) * Real.rpow r (-τ) := by
      have h : 0 < Real.rpow r (-τ) := Real.rpow_pos_of_pos hr (-τ)
      positivity
    have h5 : ENNReal.ofReal (3 * Real.rpow r (7 * τ) / 3168) /
        ENNReal.ofReal ((1 / 1584 : ℝ) * Real.rpow r (-τ)) =
        ENNReal.ofReal ((3 * Real.rpow r (7 * τ) / 3168) /
          ((1 / 1584 : ℝ) * Real.rpow r (-τ))) := by
      exact (ENNReal.ofReal_div_of_pos h_pos1).symm
    have h6 : (3 * Real.rpow r (7 * τ) / 3168) /
        ((1 / 1584 : ℝ) * Real.rpow r (-τ)) =
        (3 / 2 : ℝ) * Real.rpow r (8 * τ) := by
      have h7 : Real.rpow r (7 * τ) / Real.rpow r (-τ) = Real.rpow r (8 * τ) := by
        have h_sub := (Real.rpow_sub hr (7 * τ) (-τ)).symm
        have h8 : (7 * τ) - (-τ) = 8 * τ := by ring
        rw [h8] at h_sub; exact h_sub
      have h11 : ((1 / 1584 : ℝ) * Real.rpow r (-τ)) ≠ 0 := by positivity
      have h10 : (3 * Real.rpow r (7 * τ) / 3168) / ((1 / 1584 : ℝ) * Real.rpow r (-τ)) =
          (3 * 1584 / 3168 : ℝ) * (Real.rpow r (7 * τ) / Real.rpow r (-τ)) := by
        field_simp [h11] <;> ring
      rw [h10]
      have h12 : (3 * 1584 / 3168 : ℝ) = (3 / 2 : ℝ) := by norm_num
      rw [h12, h7] <;> ring
    calc (ν₁m.prod ν₂m) (H''_ξ ξ₀)
      ≥ ENNReal.ofReal (3 * Real.rpow r (7 * τ) / 3168) / (scales.card : ENNReal) := h3
    _ ≥ ENNReal.ofReal (3 * Real.rpow r (7 * τ) / 3168) /
          ENNReal.ofReal ((1 / 1584 : ℝ) * Real.rpow r (-τ)) := h4
    _ = ENNReal.ofReal ((3 * Real.rpow r (7 * τ) / 3168) /
          ((1 / 1584 : ℝ) * Real.rpow r (-τ))) := h5
    _ = ENNReal.ofReal ((3 / 2 : ℝ) * Real.rpow r (8 * τ)) := by rw [h6]
    _ ≥ ENNReal.ofReal (Real.rpow r (8 * τ)) := by
      have h7 : 0 ≤ Real.rpow r (8 * τ) := Real.rpow_nonneg hr.le _
      exact ENNReal.ofReal_le_ofReal (by linarith)

  -- Case split on ξ₀ < 2r
  by_cases hξ_lt_two_r : ξ₀ < 2 * r
  · -- Direct contradiction: annulus mass > Frostman bound on ball(y,4r)
    have h_pos_mass : 0 < (ν₁m.prod ν₂m) (H''_ξ ξ₀) := by
      have h : 0 < Real.rpow r (8 * τ) := Real.rpow_pos_of_pos hr (8 * τ)
      exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr h) hξ₀_lower
    have h_nonempty : (H''_ξ ξ₀).Nonempty := by
      by_contra h
      have h_empty : H''_ξ ξ₀ = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      rw [h_empty] at h_pos_mass
      simpa using h_pos_mass
    rcases h_nonempty with ⟨p, hp⟩
    rcases Set.mem_iUnion₂.mp hp.2 with ⟨nc, hnc_D, hpn⟩
    let y := p.2
    have h_ann_mass : ν₂m (tubeOfNormal r p.1 nc.1 ∩
        {z | ξ₀ ≤ dist z y ∧ dist z y < 2 * ξ₀} ∩ {b₂ | (p.1, b₂) ∈ G}) ≥
        ENNReal.ofReal (Real.rpow r (σ + 4 * τ)) := hpn.2
    have h_sub : tubeOfNormal r p.1 nc.1 ∩
        {z | ξ₀ ≤ dist z y ∧ dist z y < 2 * ξ₀} ∩ {b₂ | (p.1, b₂) ∈ G} ⊆
        Metric.ball y (4 * r) := by
      intro z hz
      have h9 : dist z y < 2 * ξ₀ := hz.1.2.2
      have h10 : 2 * ξ₀ < 4 * r := by linarith
      have h11 : dist z y < 4 * r := by linarith
      simpa [Metric.mem_ball] using h11
    have h12 : ν₂m (Metric.ball y (4 * r)) ≥
        ENNReal.ofReal (Real.rpow r (σ + 4 * τ)) :=
      le_trans h_ann_mass (measure_mono h_sub)
    have h13 : ν₂m (Metric.ball y (4 * r)) ≤ ENNReal.ofReal (C * (4 * r)) :=
      hν₂_growth' y (4 * r) (by positivity)
    have h14 : ENNReal.ofReal (Real.rpow r (σ + 4 * τ)) ≤
        ENNReal.ofReal (C * (4 * r)) := le_trans h12 h13
    have h15 : Real.rpow r (σ + 4 * τ) ≤ C * (4 * r) := by
      have h_pos2 : 0 ≤ C * (4 * r) := by positivity
      exact (ENNReal.ofReal_le_ofReal_iff h_pos2).mp h14
    linarith [h_annulus_large]

  · -- ξ₀ ≥ 2r case: proceed with direction extraction
    have hξ₀_ge_two_r : 2 * r ≤ ξ₀ := by linarith
    rcases fix_y (H''_ξ ξ₀) (hH''_ξ_meas ξ₀ hξ₀_in)
      (ENNReal.ofReal (Real.rpow r (8 * τ)))
      ENNReal.ofReal_ne_top hξ₀_lower with ⟨y, hy_mass⟩
    let X_y : Set Point := {x | (x, y) ∈ H''_ξ ξ₀}
    have hX_y_mass : ν₁m X_y ≥ ENNReal.ofReal (Real.rpow r (8 * τ)) := hy_mass

    have hXy_nonempty : X_y.Nonempty := by
      by_contra h
      have h_empty : X_y = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      rw [h_empty] at hX_y_mass
      have h_pos : 0 < Real.rpow r (8 * τ) := Real.rpow_pos_of_pos hr (8 * τ)
      have h_cont : (0 : ENNReal) ≥ ENNReal.ofReal (Real.rpow r (8 * τ)) := by simpa using hX_y_mass
      exact not_le.mpr (ENNReal.ofReal_pos.mpr h_pos) h_cont

    have h_y_supp : y ∈ (ν₂m).support := by
      rcases hXy_nonempty with ⟨x, hx⟩
      have h_in_H'R : (x, y) ∈ H'_R := hx.1
      have h_in_H' : (x, y) ∈ H' := h_in_H'R.1
      have h_in_G : (x, y) ∈ G := h_in_H'.2
      exact (hG_sub_supp h_in_G).2

    have h_choose : ∀ x ∈ X_y, ∃ (ℓ : AffineSubspace ℝ Point),
        x ∈ (ℓ : Set Point) ∧ Module.finrank ℝ ℓ.direction = 1 ∧
        y ∈ Metric.thickening r (ℓ : Set Point) ∧ (x, y) ∈ G ∧
        ν₂m (Metric.thickening r (ℓ : Set Point) ∩
          {z | ξ₀ ≤ dist z y ∧ dist z y < 2 * ξ₀} ∩
          {b₂ | (x, b₂) ∈ G}) ≥ ENNReal.ofReal (Real.rpow r (σ + 4 * τ)) := by
      intro x hx
      have h_p_in_H'' : (x, y) ∈ H''_ξ ξ₀ := hx
      have h_p_in_H'R : (x, y) ∈ H'_R := h_p_in_H''.1
      have h_p_in_H' : (x, y) ∈ H' := h_p_in_H'R.1
      have h_p_in_G : (x, y) ∈ G := h_p_in_H'.2
      rcases Set.mem_iUnion₂.mp h_p_in_H''.2 with ⟨nc, hnc_D, hpn⟩
      let n := nc.1
      let c := nc.2
      let ℓ : AffineSubspace ℝ Point := lineOfNormal x n
      have h_finrank : Module.finrank ℝ ℓ.direction = 1 := lineOfNormal_finrank x n
      have h_x_in : x ∈ (ℓ : Set Point) := by
        rw [mem_lineOfNormal_iff x n x] <;> simp
      have h_tube_eq : tubeOfNormal r x n = Metric.thickening r (ℓ : Set Point) :=
        tubeOfNormal_eq_thickening r hr x n
      have h_y_in_tube : y ∈ Metric.thickening r (ℓ : Set Point) := by
        rw [←h_tube_eq]; exact hpn.1.2.1
      have h_ann_mass : ν₂m (Metric.thickening r (ℓ : Set Point) ∩
          {z | ξ₀ ≤ dist z y ∧ dist z y < 2 * ξ₀} ∩ {b₂ | (x, b₂) ∈ G}) ≥
          ENNReal.ofReal (Real.rpow r (σ + 4 * τ)) := by
        have h := hpn.2
        rw [h_tube_eq] at h
        exact h
      exact ⟨ℓ, h_x_in, h_finrank, h_y_in_tube, h_p_in_G, h_ann_mass⟩
    choose ℓ hℓ_x hℓ_fin hℓ_y hℓ_G hℓ_ann using h_choose
    -- Convert ℓ from dependent function to total function
    rcases hXy_nonempty with ⟨x₀, hx₀⟩
    let ℓ' (x : Point) : AffineSubspace ℝ Point :=
      if hx : x ∈ X_y then ℓ x hx else ℓ x₀ hx₀
    have hℓ_x' : ∀ x ∈ X_y, x ∈ (ℓ' x : Set Point) := by
      intro x hx
      have h_eq : ℓ' x = ℓ x hx := by simp [ℓ', hx]
      rw [h_eq]
      exact hℓ_x x hx
    have hℓ_fin' : ∀ x ∈ X_y, Module.finrank ℝ (ℓ' x).direction = 1 := by
      intro x hx
      have h_eq : ℓ' x = ℓ x hx := by simp [ℓ', hx]
      rw [h_eq]
      exact hℓ_fin x hx
    have hℓ_y' : ∀ x ∈ X_y, y ∈ Metric.thickening r ((ℓ' x) : Set Point) := by
      intro x hx
      have h_eq : ℓ' x = ℓ x hx := by simp [ℓ', hx]
      rw [h_eq]
      exact hℓ_y x hx
    have hℓ_G' : ∀ x ∈ X_y, (x, y) ∈ G := by
      intro x hx
      exact hℓ_G x hx
    have hℓ_ann' : ∀ x ∈ X_y, ν₂m (Metric.thickening r ((ℓ' x) : Set Point) ∩
          {z | ξ₀ ≤ dist z y ∧ dist z y < 2 * ξ₀} ∩ {b₂ | (x, b₂) ∈ G}) ≥
          ENNReal.ofReal (Real.rpow r (σ + 4 * τ)) := by
      intro x hx
      have h_eq : ℓ' x = ℓ x hx := by simp [ℓ', hx]
      rw [h_eq]
      exact hℓ_ann x hx

    let D : ℝ := 2 * R
    have hD : 0 ≤ D := by positivity
    have h_bounded : ∀ x ∈ X_y, dist x y ≤ D := by
      intro x hx
      have h1 : (x, y) ∈ H'_R := hx.1
      exact h_dist_bound (x, y) h1

    have hG_reverse' : ∀ (ℓ' : AffineSubspace ℝ Point), y ∈ (ℓ' : Set Point) →
        Module.finrank ℝ ℓ'.direction = 1 → ∀ r' : ℝ, 0 < r' →
          ν₁m {b₁ | b₁ ∈ Metric.thickening r' (ℓ' : Set Point) ∧ (b₁, y) ∈ G} ≤
            ENNReal.ofReal (K * Real.rpow r' σ) := by
      intro ℓ' hyℓ hfin r' hr'
      have h := hG_reverse y h_y_supp ℓ' hyℓ hfin r' hr'
      have h_eq : ν₁m {b₁ | b₁ ∈ Metric.thickening r' (ℓ' : Set Point) ∧ (b₁, y) ∈ G} =
          (ν₁ {b₁ | b₁ ∈ Metric.thickening r' (ℓ' : Set Point) ∧ (b₁, y) ∈ G} : ENNReal) := by
        exact (ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν₁ _).symm
      rw [h_eq]; exact h

    let δ : ℝ := r / ξ₀
    have hδ_pos : 0 < δ := by positivity
    have hδ_le_half : δ ≤ 1 / 2 := by
      have h1 : ξ₀ ≥ 2 * r := hξ₀_ge_two_r
      have h2 : 0 < ξ₀ := hξ₀_pos
      have h3 : r / ξ₀ ≤ r / (2 * r) := by gcongr
      have h4 : r / (2 * r) = 1 / 2 := by
        have h5 : 0 < r := hr
        field_simp [h5.ne'] <;> ring
      linarith

    rcases direction_separated_extraction G K σ r ξ₀ D δ
        (Real.rpow r (8 * τ))
        hσ (le_of_lt hσ_lt_one) hr hξ₀_pos hD hK (Real.rpow_nonneg hr.le _)
        (by rfl) hδ_pos y X_y hX_y_mass ℓ' hℓ_x' hℓ_fin' hℓ_y' hℓ_G'
        h_bounded hG_reverse'
      with ⟨S, hS_from_fiber, hS_y_in_tube, hS_sep, hS_card, hS_cover⟩

    let m : ℝ := Real.rpow r (σ + 4 * τ)
    have hm_pos : 0 < m := Real.rpow_pos_of_pos hr (σ + 4 * τ)

    have hS_finrank : ∀ L ∈ S, Module.finrank ℝ L.direction = 1 := by
      intro L hL
      rcases hS_from_fiber L hL with ⟨x, hx, rfl⟩
      exact hℓ_fin' x hx

    have h_mass_per_tube : ∀ L ∈ S,
        ν₂m (Metric.ball y (2 * ξ₀) \ Metric.ball y ξ₀ ∩ Metric.thickening r (L : Set Point)) ≥
          ENNReal.ofReal m := by
      intro L hL
      rcases hS_from_fiber L hL with ⟨x, hx, rfl⟩
      have h1 : {z | ξ₀ ≤ dist z y ∧ dist z y < 2 * ξ₀} =
          Metric.ball y (2 * ξ₀) \ Metric.ball y ξ₀ := by
        ext z; simp [Metric.mem_ball, dist_comm z y] <;> constructor <;> intro h <;> exact ⟨by linarith, by linarith⟩
      have h2 := hℓ_ann' x hx
      have h3 : ν₂m (Metric.ball y (2 * ξ₀) \ Metric.ball y ξ₀ ∩ Metric.thickening r ((ℓ' x) : Set Point)) ≥
          ν₂m (Metric.thickening r ((ℓ' x) : Set Point) ∩
            {z | ξ₀ ≤ dist z y ∧ dist z y < 2 * ξ₀} ∩ {b₂ | (x, b₂) ∈ G}) := by
        rw [h1]
        apply measure_mono
        intro z hz
        exact ⟨hz.1.2, hz.1.1⟩
      exact le_trans h2 h3

    have h_small : 2 * r / ξ₀ ≤ 1 := by
      have h1 : ξ₀ ≥ 2 * r := hξ₀_ge_two_r
      have h2 : 0 < ξ₀ := hξ₀_pos
      calc 2 * r / ξ₀ ≤ 2 * r / (2 * r) := by gcongr
        _ = 1 := by
          have h3 : 0 < 2 * r := by positivity
          field_simp [h3.ne'] <;> ring

    have hFrostman : ν₂m (Metric.ball y (2 * ξ₀)) ≤
        ENNReal.ofReal (C * (2 * ξ₀)) :=
      hν₂_growth' y (2 * ξ₀) (by positivity)

    let W : ℝ := r + (D + r) * (δ / 8)
    have hW_pos : 0 < W := by positivity
    let C₁ : ℝ := 1 + (D + 1) / 8
    have hC₁_pos : 0 < C₁ := by positivity
    have hξ₀_le_one : ξ₀ ≤ 1 := by
      have h1 : ξ₀ ≤ Real.rpow r κ := hξ₀_bounds.2
      have h2 : Real.rpow r κ < 1 := Real.rpow_lt_one hr.le hr_small hκ_pos
      linarith
    have hW_eq : W = r + (D + r) * δ / 8 := by
      dsimp only [W] <;> ring
    have hWξ_bound : W * ξ₀ ≤ C₁ * r :=
      width_times_xi_bound r ξ₀ D hr hr_small hξ₀_pos hξ₀_le_one hD δ rfl W hW_eq C₁ rfl
    have h_card_lower : (S.card : ℝ) ≥
        Real.rpow r (8 * τ) / (15 * K * Real.rpow W σ) := hS_card
    have h_count : (S.card : ℝ) * m > 26 * C * ξ₀ :=
      concentrated_count_bound_general
        (r := r) (τ := τ) (σ := σ) (ξ₀ := ξ₀) (κ := κ) (K := K) (C := C)
        (W := W) (m := m) (D := D) (C₁ := C₁)
        hr hr_small hτ hσ hσ_lt_one hξ₀_pos hξ₀_bounds.2
        hκ hκ_pos hK hC hW_pos hm_pos (by rfl) hWξ_bound hC₁_pos
        h_card_lower h_r2τ_small

    exact concentrated_contradiction_of_affine r τ σ ξ₀ C m hr hτ hσ
      hξ₀_pos (by linarith) (by positivity) y S
      hS_finrank
      hS_y_in_tube
      (fun L1 hL1 L2 hL2 hne => hS_sep L1 hL1 L2 hL2 hne)
      h_small h_mass_per_tube hFrostman h_count

end RadialBootstrapping
