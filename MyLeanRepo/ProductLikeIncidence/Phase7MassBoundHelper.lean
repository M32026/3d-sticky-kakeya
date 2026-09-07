module

/-
# Mass Bound Helper for Phase7DoubleCountingHelper

Standalone extraction of the ν Θ_bad mass bound to reduce elaboration overhead.
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeIncidence.Phase7Budgets
public import MyLeanRepo.ProductLikeSetBasics
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set ENNReal Bornology MeasureTheory Classical


namespace ProductLikeIncidence.ProductReduction

/-- Given Θ_bad_fin from double counting, prove ν Θ_bad ≥ δ^ε_mass. -/
lemma phase7_mass_bound
    {δ ε_mass : ℝ}
    {Y : Set ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hε_mass_pos : 0 < ε_mass)
    (Yfin : Finset ℝ)
    (hYfin_eq : (Yfin : Set ℝ) = Y)
    (hY_nonempty : Y.Nonempty)
    (c_mult_dir : ℝ)
    (hc_mult_dir_pos : 0 < c_mult_dir)
    (Θ_bad_fin : Finset ℝ)
    (hΘ_sub : Θ_bad_fin ⊆ Yfin)
    (hΘ_card : (Θ_bad_fin.card : ℝ) ≥ (c_mult_dir / 2) * Yfin.card)
    (hν_uniform : ∀ y ∈ Y, ν {y} = ENNReal.ofReal (1 / (Y.ncard : ℝ)))
    (h_mass_budget : δ ^ ε_mass ≤ c_mult_dir / 2) :
    ν (Θ_bad_fin : Set ℝ) ≥ ENNReal.ofReal (δ ^ ε_mass) := by
  let Θ_bad : Set ℝ := (Θ_bad_fin : Set ℝ)
  have hΘ_bad_sub_Y : Θ_bad ⊆ Y := by
    intro y hy
    have h1 : y ∈ Θ_bad_fin := by exact_mod_cast hy
    have h2 : y ∈ Yfin := hΘ_sub h1
    have h3 : y ∈ (Yfin : Set ℝ) := h2
    have h4 : y ∈ Y := by simpa [hYfin_eq] using h3
    exact h4
  have hYfin_pos : 0 < Yfin.card := by
    rcases hY_nonempty with ⟨y, hy⟩
    have h_y_in : y ∈ Yfin := by
      have h : y ∈ (Yfin : Set ℝ) := by rw [hYfin_eq] <;> exact hy
      exact h
    exact Finset.card_pos.mpr ⟨y, h_y_in⟩
  have hY_ncard_eq : (Y.ncard : ℝ) = (Yfin.card : ℝ) := by
    have h2 : Y = (Yfin : Set ℝ) := hYfin_eq.symm
    have h3 : Y.ncard = (Yfin : Set ℝ).ncard := by rw [h2]
    rw [h3, Set.ncard_coe_finset] <;> rfl
  have hν_Θ_bad : ν Θ_bad = ENNReal.ofReal ((Θ_bad_fin.card : ℝ) / (Yfin.card : ℝ)) := by
    have h1 : ν Θ_bad = ∑ y ∈ Θ_bad_fin, ν {y} := by
      rw [← MeasureTheory.sum_measure_singleton (s := Θ_bad_fin)]
    rw [h1]
    have h2 : ∑ y ∈ Θ_bad_fin, ν {y} =
        ∑ y ∈ Θ_bad_fin, ENNReal.ofReal (1 / (Y.ncard : ℝ)) := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hν_uniform y (hΘ_bad_sub_Y (by exact_mod_cast hy))
    rw [h2]
    have h3 : ∑ y ∈ Θ_bad_fin, ENNReal.ofReal (1 / (Y.ncard : ℝ)) =
        (↑Θ_bad_fin.card : ENNReal) * ENNReal.ofReal (1 / (Y.ncard : ℝ)) := by
      rw [Finset.sum_const] <;> simp [mul_comm]
    rw [h3]
    have h4 : (↑Θ_bad_fin.card : ENNReal) * ENNReal.ofReal (1 / (Y.ncard : ℝ)) =
        ENNReal.ofReal ((Θ_bad_fin.card : ℝ) / (Yfin.card : ℝ)) := by
      rw [hY_ncard_eq]
      have h5 : (↑Θ_bad_fin.card : ENNReal) = ENNReal.ofReal (↑Θ_bad_fin.card : ℝ) := by simp
      rw [h5]
      rw [← ENNReal.ofReal_mul (by positivity)] <;> ring_nf
    exact h4
  rw [hν_Θ_bad]
  have h1 : (Θ_bad_fin.card : ℝ) / (Yfin.card : ℝ) ≥ c_mult_dir / 2 := by
    have h_card : (Θ_bad_fin.card : ℝ) ≥ (c_mult_dir / 2) * (Yfin.card : ℝ) := hΘ_card
    have hYpos : (0 : ℝ) < (Yfin.card : ℝ) := by exact_mod_cast hYfin_pos
    calc (Θ_bad_fin.card : ℝ) / (Yfin.card : ℝ)
      ≥ ((c_mult_dir / 2) * (Yfin.card : ℝ)) / (Yfin.card : ℝ) := by gcongr
    _ = c_mult_dir / 2 := by field_simp [hYpos.ne'] <;> ring
  have h2 : δ ^ ε_mass ≤ c_mult_dir / 2 := h_mass_budget
  have h3 : (δ ^ ε_mass) ≤ (Θ_bad_fin.card : ℝ) / (Yfin.card : ℝ) := le_trans h2 h1
  exact ENNReal.ofReal_le_ofReal h3

end ProductLikeIncidence.ProductReduction
