module

/-
  B1 Fine Card Lower Bound.

  Packages the Ncover lower bound chain for `h_fine_card_lower`:
    Δ^{-2u+ε/4} ≤ |config_n.P₀|

  Chain:
  1. `deltasSet_extraction_dyadic_main`: Ncover(δ_n, Pbar) ≥ (1/10000)·C⁻¹·δ_n^{-u}
  2. `source_to_nice_configuration`: Ncover(δ_n, pointSet) ≥ δ_n^{ρ_mass}·Ncover(δ_n, Pbar)
  3. `fine_card_lower_ncover`: |P₀| ≥ Ncover(δ_n, pointSet)
  4. Absorb constants and ρ_mass into Δ^{ε/4}

  Whiteprint node: improved_incidence_general / b1_fine_card_lower
  Dependencies: RegularB1Bounds
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.RegularB1Bounds
public import MyLeanRepo.OSWPrelude

@[expose] public section


open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate

/-! ### Fine card lower bound: full chain -/

/-- Full Ncover-to-card lower bound chain for B1 bridge. -/
lemma b1_fine_card_lower_general
    {n : ℕ} {Δ δ_n δ u ε εA ρ_mass C : ℝ}
    (fine_gain : ℝ) (hfine_gain_pos : 0 < fine_gain)
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hδ_n_pos : 0 < δ_n)
    (hδ_n_eq : δ_n = DiscretisedFurstenbergEstimate.dyadicDelta n)
    (hδ_n_eq2 : δ_n = Δ ^ 2)
    (hδ_ge : δ_n / 4 ≤ δ)
    (hε_pos : 0 < ε) (hεA_pos : 0 < εA) (hρ_mass_nonneg : 0 ≤ ρ_mass)
    (hu_nonneg : 0 ≤ u)
    {Pbar : Finset EuclideanPlane}
    {P₀ : Finset (DiscretisedFurstenbergEstimate.DyadicSquare n)}
    {pointSet : Set EuclideanPlane}
    (hpointSet_sub : pointSet ⊆
      ⋃ p ∈ (P₀ : Set (DiscretisedFurstenbergEstimate.DyadicSquare n)),
        (p.toSet : Set EuclideanPlane))
    (hPbar_ncover_lower : Metric.externalCoveringNumber δ_n.toNNReal (Pbar : Set EuclideanPlane) ≥
        ENNReal.ofReal ((1 / 10000 : ℝ) * C⁻¹ * Real.rpow δ_n (-u)))
    (hNcover_pointSet_lower : Metric.externalCoveringNumber δ_n.toNNReal pointSet ≥
        ENNReal.ofReal (Real.rpow δ_n ρ_mass) *
          Metric.externalCoveringNumber δ_n.toNNReal (Pbar : Set EuclideanPlane))
    (hC_eq : C = 81 * Real.rpow δ (-εA))
    (h_exponent : 2 * εA + 2 * ρ_mass < fine_gain)
    (hΔ_small : (1 / 810000 : ℝ) * Real.rpow 4 (-εA) ≥
        Real.rpow Δ (fine_gain - 2 * εA - 2 * ρ_mass)) :
    Real.rpow Δ (-2 * u + fine_gain) ≤ (P₀.card : ℝ) := by
  have hδ_pos : 0 < δ := by linarith
  have hδ_n4_pos : 0 < δ_n / 4 := by positivity

  -- C > 0
  have hC_pos : 0 < C := by
    rw [hC_eq]
    have h1 : 0 < Real.rpow δ (-εA) := Real.rpow_pos_of_pos hδ_pos _
    positivity

  -- δ^{εA} ≥ (δ_n/4)^{εA} = 4^{-εA} * δ_n^{εA}
  have h_rpow_div : Real.rpow (δ_n / 4) εA = Real.rpow δ_n εA / Real.rpow 4 εA := by
    simpa using Real.div_rpow (show (0 : ℝ) ≤ δ_n by linarith) (show (0 : ℝ) ≤ 4 by norm_num) εA
  have h_rpow4_neg : Real.rpow 4 (-εA) = (Real.rpow 4 εA)⁻¹ := by
    simpa using Real.rpow_neg (show (0 : ℝ) ≤ 4 by norm_num) εA
  have h6 : Real.rpow (δ_n / 4) εA = Real.rpow 4 (-εA) * Real.rpow δ_n εA := by
    rw [h_rpow_div, h_rpow4_neg]
    <;> field_simp <;> ring
  have h5 : Real.rpow (δ_n / 4) εA ≤ Real.rpow δ εA :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
  have h10 : Real.rpow 4 (-εA) * Real.rpow δ_n εA ≤ Real.rpow δ εA := by
    calc Real.rpow 4 (-εA) * Real.rpow δ_n εA
      = Real.rpow (δ_n / 4) εA := h6.symm
    _ ≤ Real.rpow δ εA := h5

  -- δ_n^{εA-u} = δ_n^{εA} * δ_n^{-u}
  have h11 : Real.rpow δ_n (εA - u) = Real.rpow δ_n εA * Real.rpow δ_n (-u) := by
    have h : Real.rpow δ_n (εA + -u) = Real.rpow δ_n εA * Real.rpow δ_n (-u) := Real.rpow_add hδ_n_pos εA (-u)
    have h_eq : εA + -u = εA - u := by ring
    rw [h_eq] at h
    exact h

  -- (1/10000) * C⁻¹ * δ_n^{-u} ≥ (1/810000) * 4^{-εA} * δ_n^{εA-u}
  have h_inv_C : (81 * Real.rpow δ (-εA))⁻¹ = (1 / 81 : ℝ) * Real.rpow δ εA := by
    have h_ne : Real.rpow δ (-εA) ≠ 0 := (Real.rpow_pos_of_pos hδ_pos _).ne'
    have h_mul : Real.rpow δ (-εA) * Real.rpow δ εA = 1 := by
      have h : Real.rpow δ ((-εA) + εA) = Real.rpow δ (-εA) * Real.rpow δ εA := Real.rpow_add hδ_pos (-εA) εA
      have h_sum : (-εA) + εA = 0 := by ring
      rw [h_sum] at h
      have h1 : Real.rpow δ 0 = 1 := by simp
      rw [h1] at h
      exact h.symm
    field_simp [h_ne] <;> nlinarith
  have h2 : (1 / 10000 : ℝ) * C⁻¹ * Real.rpow δ_n (-u) ≥
      (1 / 810000 : ℝ) * Real.rpow 4 (-εA) * Real.rpow δ_n (εA - u) := by
    rw [hC_eq, h_inv_C]
    calc (1 / 10000 : ℝ) * ((1 / 81 : ℝ) * Real.rpow δ εA) * Real.rpow δ_n (-u)
      = (1 / 810000 : ℝ) * Real.rpow δ εA * Real.rpow δ_n (-u) := by ring
    _ ≥ (1 / 810000 : ℝ) * (Real.rpow 4 (-εA) * Real.rpow δ_n εA) * Real.rpow δ_n (-u) := by
      have h_nonneg : 0 ≤ Real.rpow δ_n (-u) := Real.rpow_nonneg hδ_n_pos.le _
      gcongr <;> exact h_nonneg
    _ = (1 / 810000 : ℝ) * Real.rpow 4 (-εA) * Real.rpow δ_n (εA - u) := by
        rw [h11] <;> ring

  -- K = const * δ_n^{-u+εA+ρ_mass}
  set K : ℝ := (1 / 810000 : ℝ) * Real.rpow 4 (-εA) * Real.rpow δ_n (-u + εA + ρ_mass) with hK_def
  have hK_nonneg : 0 ≤ K := by
    dsimp only [K]
    have h1 : 0 ≤ Real.rpow 4 (-εA) := Real.rpow_nonneg (by norm_num) _
    have h2 : 0 ≤ Real.rpow δ_n (-u + εA + ρ_mass) := Real.rpow_nonneg hδ_n_pos.le _
    positivity

  -- δ_n^{-u+εA+ρ_mass} = δ_n^{ρ_mass} * δ_n^{εA-u}
  have h12 : Real.rpow δ_n (-u + εA + ρ_mass) =
      Real.rpow δ_n ρ_mass * Real.rpow δ_n (εA - u) := by
    have h := Real.rpow_add hδ_n_pos ρ_mass (εA - u)
    have h_sum : ρ_mass + (εA - u) = -u + εA + ρ_mass := by ring
    rw [h_sum] at h
    simpa using h

  -- Combined lower bound
  have h_combined_lower : Real.rpow δ_n ρ_mass * (1 / 10000 : ℝ) * C⁻¹ * Real.rpow δ_n (-u) ≥ K := by
    dsimp only [K]
    calc Real.rpow δ_n ρ_mass * (1 / 10000 : ℝ) * C⁻¹ * Real.rpow δ_n (-u)
      = Real.rpow δ_n ρ_mass * ((1 / 10000 : ℝ) * C⁻¹ * Real.rpow δ_n (-u)) := by ring
    _ ≥ Real.rpow δ_n ρ_mass * ((1 / 810000 : ℝ) * Real.rpow 4 (-εA) * Real.rpow δ_n (εA - u)) := by
        gcongr
        <;> exact Real.rpow_nonneg hδ_n_pos.le _
    _ = (1 / 810000 : ℝ) * Real.rpow 4 (-εA) * Real.rpow δ_n (-u + εA + ρ_mass) := by
        rw [h12] <;> ring

  -- Product positivity for ENNReal
  have h_prod_pos : 0 ≤ Real.rpow δ_n ρ_mass * (1 / 10000 : ℝ) * C⁻¹ * Real.rpow δ_n (-u) := by
    have h1 : 0 ≤ Real.rpow δ_n ρ_mass := Real.rpow_nonneg hδ_n_pos.le _
    have h2 : 0 ≤ C⁻¹ := by positivity
    have h3 : 0 ≤ Real.rpow δ_n (-u) := Real.rpow_nonneg hδ_n_pos.le _
    positivity

  -- Ncover(pointSet) ≥ ENNReal.ofReal(K)
  have h1 : Metric.externalCoveringNumber δ_n.toNNReal pointSet ≥ ENNReal.ofReal K := by
    set a : ℝ := Real.rpow δ_n ρ_mass with ha_def
    set b : ℝ := (1 / 10000 : ℝ) * C⁻¹ * Real.rpow δ_n (-u) with hb_def
    have ha_nonneg : 0 ≤ a := Real.rpow_nonneg hδ_n_pos.le _
    have hb_nonneg : 0 ≤ b := by
      dsimp only [b]
      have h1 : 0 ≤ C⁻¹ := by positivity
      have h2 : 0 ≤ Real.rpow δ_n (-u) := Real.rpow_nonneg hδ_n_pos.le _
      positivity
    have h_ofreal_mul : ENNReal.ofReal a * ENNReal.ofReal b = ENNReal.ofReal (a * b) := by
      have h : ENNReal.ofReal (a * b) = ENNReal.ofReal a * ENNReal.ofReal b := by
        simpa using ENNReal.ofReal_mul ha_nonneg
      exact h.symm
    have h_assoc : a * b = Real.rpow δ_n ρ_mass * (1 / 10000 : ℝ) * C⁻¹ * Real.rpow δ_n (-u) := by
      simp [ha_def, hb_def] <;> ring
    calc Metric.externalCoveringNumber δ_n.toNNReal pointSet
      ≥ ENNReal.ofReal (Real.rpow δ_n ρ_mass) *
          Metric.externalCoveringNumber δ_n.toNNReal (Pbar : Set EuclideanPlane) :=
        hNcover_pointSet_lower
    _ ≥ ENNReal.ofReal (Real.rpow δ_n ρ_mass) *
          ENNReal.ofReal ((1 / 10000 : ℝ) * C⁻¹ * Real.rpow δ_n (-u)) := by gcongr
    _ = ENNReal.ofReal (Real.rpow δ_n ρ_mass * ((1 / 10000 : ℝ) * C⁻¹ * Real.rpow δ_n (-u))) := h_ofreal_mul
    _ = ENNReal.ofReal (Real.rpow δ_n ρ_mass * (1 / 10000 : ℝ) * C⁻¹ * Real.rpow δ_n (-u)) := by
      rw [h_assoc]
    _ ≥ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal h_combined_lower

  -- |P₀| ≥ Ncover(pointSet)
  have h9 : Metric.externalCoveringNumber (DiscretisedFurstenbergEstimate.dyadicDelta n).toNNReal pointSet ≤
      (P₀.card : ℕ∞) := fine_card_lower_ncover hpointSet_sub
  have h10 : Metric.externalCoveringNumber δ_n.toNNReal pointSet ≤ (P₀.card : ENNReal) := by
    have h_eq : δ_n.toNNReal = (DiscretisedFurstenbergEstimate.dyadicDelta n).toNNReal := by
      rw [hδ_n_eq]
    rw [h_eq]
    exact_mod_cast h9

  have h11 : ENNReal.ofReal K ≤ (P₀.card : ENNReal) := le_trans h1 h10
  have h_card_nonneg : 0 ≤ (P₀.card : ℝ) := by positivity
  have h12 : K ≤ (P₀.card : ℝ) := by
    have h_card_real : (P₀.card : ENNReal) = ENNReal.ofReal (↑(P₀.card : ℝ)) := by simp
    rw [h_card_real] at h11
    exact (ENNReal.ofReal_le_ofReal_iff h_card_nonneg).mp h11

  -- K = const * Δ^{-2u+2εA+2ρ_mass}
  have h13 : K = (1 / 810000 : ℝ) * Real.rpow 4 (-εA) *
      Real.rpow Δ (-2 * u + 2 * εA + 2 * ρ_mass) := by
    dsimp only [K]
    have h14 : Real.rpow δ_n (-u + εA + ρ_mass) =
        Real.rpow Δ (-2 * u + 2 * εA + 2 * ρ_mass) := by
      rw [hδ_n_eq2]
      have h15 : (Δ ^ 2 : ℝ) = Real.rpow Δ 2 := by simp [Real.rpow_two] <;> ring
      rw [h15]
      have h16 := Real.rpow_mul hΔ_pos.le (2 : ℝ) (-u + εA + ρ_mass)
      have h17 : 2 * (-u + εA + ρ_mass) = -2 * u + 2 * εA + 2 * ρ_mass := by ring
      simpa [h17] using h16.symm
    rw [h14]

  rw [h13] at h12

  -- Final: Δ^{-2u+ε/4} ≤ const * Δ^{-2u+2εA+2ρ_mass}
  -- From hΔ_small: const ≥ Δ^{ε/4 - 2εA - 2ρ_mass}
  -- Multiply by Δ^{-2u}: const * Δ^{-2u} ≥ Δ^{ε/4 - 2εA - 2ρ_mass} * Δ^{-2u} = Δ^{-2u + ε/4 - 2εA - 2ρ_mass}
  -- Wait, that's not right. We need:
  -- Δ^{-2u+ε/4} = Δ^{-2u} * Δ^{ε/4}
  -- ≤ Δ^{-2u} * const * Δ^{2εA+2ρ_mass}  (from hΔ_small rearranged)
  -- = const * Δ^{-2u+2εA+2ρ_mass}
  have h_exp_pos : 0 < fine_gain - 2 * εA - 2 * ρ_mass := by linarith
  have h_rpow2_nonneg : 0 ≤ Real.rpow Δ (2 * εA + 2 * ρ_mass) := Real.rpow_nonneg hΔ_pos.le _
  have h_rpow_minus2u_nonneg : 0 ≤ Real.rpow Δ (-2 * u) := Real.rpow_nonneg hΔ_pos.le _

  -- Δ^{ε/4} ≤ const * Δ^{2εA+2ρ_mass}
  have h18 : Real.rpow Δ fine_gain ≤
      (1 / 810000 : ℝ) * Real.rpow 4 (-εA) * Real.rpow Δ (2 * εA + 2 * ρ_mass) := by
    have h19 : Real.rpow Δ (fine_gain - 2 * εA - 2 * ρ_mass) ≤
        (1 / 810000 : ℝ) * Real.rpow 4 (-εA) := hΔ_small
    have h20 : Real.rpow Δ fine_gain =
        Real.rpow Δ (fine_gain - 2 * εA - 2 * ρ_mass) * Real.rpow Δ (2 * εA + 2 * ρ_mass) := by
      have h21 : Real.rpow Δ ((fine_gain - 2 * εA - 2 * ρ_mass) + (2 * εA + 2 * ρ_mass)) =
          Real.rpow Δ (fine_gain - 2 * εA - 2 * ρ_mass) * Real.rpow Δ (2 * εA + 2 * ρ_mass) :=
        Real.rpow_add hΔ_pos (fine_gain - 2 * εA - 2 * ρ_mass) (2 * εA + 2 * ρ_mass)
      have h_sum : (fine_gain - 2 * εA - 2 * ρ_mass) + (2 * εA + 2 * ρ_mass) = fine_gain := by ring
      have h22 : Real.rpow Δ fine_gain = Real.rpow Δ ((fine_gain - 2 * εA - 2 * ρ_mass) + (2 * εA + 2 * ρ_mass)) := by rw [h_sum]
      rw [h22]
      exact h21
    rw [h20]
    have h22 : 0 ≤ Real.rpow Δ (2 * εA + 2 * ρ_mass) := h_rpow2_nonneg
    nlinarith

  -- Δ^{-2u+ε/4} = Δ^{-2u} * Δ^{ε/4}
  have h23 : Real.rpow Δ (-2 * u + fine_gain) =
      Real.rpow Δ (-2 * u) * Real.rpow Δ fine_gain := by
    have h := Real.rpow_add hΔ_pos (-2 * u) fine_gain
    have h_sum : (-2 * u) + fine_gain = -2 * u + fine_gain := by ring
    rw [h_sum] at h
    simpa using h

  -- const * Δ^{-2u+2εA+2ρ_mass} = const * Δ^{-2u} * Δ^{2εA+2ρ_mass}
  have h24 : (1 / 810000 : ℝ) * Real.rpow 4 (-εA) * Real.rpow Δ (-2 * u + 2 * εA + 2 * ρ_mass) =
      (1 / 810000 : ℝ) * Real.rpow 4 (-εA) * Real.rpow Δ (-2 * u) * Real.rpow Δ (2 * εA + 2 * ρ_mass) := by
    have h : Real.rpow Δ ((-2 * u) + (2 * εA + 2 * ρ_mass)) =
        Real.rpow Δ (-2 * u) * Real.rpow Δ (2 * εA + 2 * ρ_mass) :=
      Real.rpow_add hΔ_pos (-2 * u) (2 * εA + 2 * ρ_mass)
    have h_sum : (-2 * u) + (2 * εA + 2 * ρ_mass) = -2 * u + 2 * εA + 2 * ρ_mass := by ring
    have h25 : Real.rpow Δ (-2 * u + 2 * εA + 2 * ρ_mass) =
        Real.rpow Δ (-2 * u) * Real.rpow Δ (2 * εA + 2 * ρ_mass) := by
      rw [← h_sum]
      exact h
    rw [h25] <;> ring

  calc Real.rpow Δ (-2 * u + fine_gain)
    = Real.rpow Δ (-2 * u) * Real.rpow Δ fine_gain := h23
  _ ≤ Real.rpow Δ (-2 * u) *
        ((1 / 810000 : ℝ) * Real.rpow 4 (-εA) * Real.rpow Δ (2 * εA + 2 * ρ_mass)) := by
      gcongr
      <;> exact h_rpow_minus2u_nonneg
  _ = (1 / 810000 : ℝ) * Real.rpow 4 (-εA) * Real.rpow Δ (-2 * u + 2 * εA + 2 * ρ_mass) := by
      rw [h24] <;> ring
  _ ≤ (P₀.card : ℝ) := h12

/-- Specialization of `b1_fine_card_lower_general` with `fine_gain = ε/4`. -/
lemma b1_fine_card_lower
    {n : ℕ} {Δ δ_n δ u ε εA ρ_mass C : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hδ_n_pos : 0 < δ_n)
    (hδ_n_eq : δ_n = DiscretisedFurstenbergEstimate.dyadicDelta n)
    (hδ_n_eq2 : δ_n = Δ ^ 2)
    (hδ_ge : δ_n / 4 ≤ δ)
    (hε_pos : 0 < ε) (hεA_pos : 0 < εA) (hρ_mass_nonneg : 0 ≤ ρ_mass)
    (hu_nonneg : 0 ≤ u)
    {Pbar : Finset EuclideanPlane}
    {P₀ : Finset (DiscretisedFurstenbergEstimate.DyadicSquare n)}
    {pointSet : Set EuclideanPlane}
    (hpointSet_sub : pointSet ⊆
      ⋃ p ∈ (P₀ : Set (DiscretisedFurstenbergEstimate.DyadicSquare n)),
        (p.toSet : Set EuclideanPlane))
    (hPbar_ncover_lower : Metric.externalCoveringNumber δ_n.toNNReal (Pbar : Set EuclideanPlane) ≥
        ENNReal.ofReal ((1 / 10000 : ℝ) * C⁻¹ * Real.rpow δ_n (-u)))
    (hNcover_pointSet_lower : Metric.externalCoveringNumber δ_n.toNNReal pointSet ≥
        ENNReal.ofReal (Real.rpow δ_n ρ_mass) *
          Metric.externalCoveringNumber δ_n.toNNReal (Pbar : Set EuclideanPlane))
    (hC_eq : C = 81 * Real.rpow δ (-εA))
    (h_exponent : 2 * εA + 2 * ρ_mass < ε / 4)
    (hΔ_small : (1 / 810000 : ℝ) * Real.rpow 4 (-εA) ≥
        Real.rpow Δ (ε / 4 - 2 * εA - 2 * ρ_mass)) :
    Real.rpow Δ (-2 * u + ε / 4) ≤ (P₀.card : ℝ) := by
  have hfg_pos : 0 < ε / 4 := by positivity
  exact @b1_fine_card_lower_general n Δ δ_n δ u ε εA ρ_mass C (ε / 4) hfg_pos
    hΔ_pos hΔ_lt_one hδ_n_pos hδ_n_eq hδ_n_eq2 hδ_ge hε_pos hεA_pos hρ_mass_nonneg hu_nonneg
    Pbar P₀ pointSet hpointSet_sub hPbar_ncover_lower hNcover_pointSet_lower hC_eq h_exponent hΔ_small

end DirecretisedFurstenbergEstimate.FrontEndLemmas

end
