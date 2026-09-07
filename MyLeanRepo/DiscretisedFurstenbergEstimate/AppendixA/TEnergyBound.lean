module

/-
  t-energy bound for CoarseSquare sets.

  Given ball-growth and diameter bounds, proves the total discrete t-energy
  ∑_{Q,R} dist(Q,R)^{-t} ≤ K_energy * C * |Qset|^2,
  where K_energy ~ log(R_max) is logarithmic in the diameter.

  Whiteprint node: appendix_a_alternative / t_energy_bound_coarse
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal


noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA3

open DirecretisedFurstenbergEstimate

abbrev CoarseSquare (Δ : ℝ) := ℤ × ℤ

/-- External covering number at scale Δ for a finite CoarseSquare set equals its cardinality,
    since distinct points are distance ≥ 1 > 2Δ. -/
lemma a3_covering_eq {Δ : ℝ} (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (S : Finset (CoarseSquare Δ)) :
    Metric.externalCoveringNumber Δ.toNNReal (S : Set (CoarseSquare Δ)) = ↑S.card := by
  let S' : Set (CoarseSquare Δ) := S
  have h_upper : Metric.externalCoveringNumber Δ.toNNReal S' ≤ S'.encard :=
    Metric.externalCoveringNumber_le_encard_self (ε := Δ.toNNReal) S'
  have h_int_dist : ∀ (a b : ℤ), a ≠ b → (1 : ℝ) ≤ dist a b := by
    intro a b hne
    have hdiff : a - b ≠ 0 := by simpa [sub_ne_zero] using hne
    have h2 : 1 ≤ |a - b| := Int.one_le_abs hdiff
    have h3 : (dist a b : ℝ) = ↑(|a - b|) := by
      simp [Int.dist_eq] <;> rfl
    rw [h3]
    exact_mod_cast h2
  have h_dist : ∀ (x y : CoarseSquare Δ), x ≠ y → (1 : ℝ) ≤ dist x y := by
    intro x y hxy
    rw [Prod.dist_eq]
    by_cases h : x.1 ≠ y.1
    · exact le_max_of_le_left (h_int_dist x.1 y.1 h)
    · have h3 : x.2 ≠ y.2 := by intro h4; apply hxy; ext <;> tauto
      exact le_max_of_le_right (h_int_dist x.2 y.2 h3)
  have h_sep : Metric.IsSeparated (2 * Δ.toNNReal) S' := by
    intro x _ y _ hxy
    have h5 : (2 * Δ.toNNReal : ENNReal) < 1 := by
      have h51 : (Δ.toNNReal : ℝ) = Δ := by
        rw [Real.toNNReal_of_nonneg (by linarith)] <;> rfl
      have h52 : (Δ.toNNReal : ℝ) < 1 / 2 := by rw [h51]; exact hΔ_lt_half
      have h53 : (2 * Δ.toNNReal : ℝ) < 1 := by linarith
      exact_mod_cast h53
    have h6 : (1 : ENNReal) ≤ edist x y := by
      have h61 : (1 : ℝ) ≤ dist x y := h_dist x y hxy
      have h62 : edist x y = ENNReal.ofReal (dist x y) := by exact edist_dist x y
      rw [h62]
      have h63 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
      rw [h63]
      exact ENNReal.ofReal_le_ofReal h61
    exact h5.trans_le h6
  have h_packing : S'.encard ≤ Metric.packingNumber (2 * Δ.toNNReal) S' := by exact Metric.IsSeparated.encard_le_packingNumber (fun ⦃a⦄ a_1 => a_1) h_sep
  have h_lower : S'.encard ≤ Metric.externalCoveringNumber Δ.toNNReal S' :=
    h_packing.trans (Metric.packingNumber_two_mul_le_externalCoveringNumber Δ.toNNReal S')
  have h_encard : S'.encard = ↑S.card := by simp [S']
  have h_upper' : Metric.externalCoveringNumber Δ.toNNReal (↑S : Set (CoarseSquare Δ)) ≤ ↑S.card := by
    simpa [S', h_encard] using h_upper
  have h_lower' : ↑S.card ≤ Metric.externalCoveringNumber Δ.toNNReal (↑S : Set (CoarseSquare Δ)) := by
    simpa [S', h_encard] using h_lower
  exact le_antisymm h_upper' h_lower'

end DirecretisedFurstenbergEstimate.AppendixA3
