import MyLeanRepo.Kakeya.Assouad.WZ1.Statements

/-!
# Two-ends reduction to strip non-concentration

Given the output of `two_ends_reduction`, prove that the subset
E' = E ∩ S has strip non-concentration for all r ≥ δ with constant K = w^{-ζ}.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- Convert two-ends reduction output to strip non-concentration for E' = E ∩ S. -/
lemma two_ends_to_strip_nonconcentration
    {E : DiscreteSet 2} {δ ζ : ℝ}
    (hδ : 0 < δ) (hζ : 0 < ζ)
    (normal : Point2) (t w : ℝ)
    (hnormal : ‖normal‖ = 1)
    (hwδ : δ ≤ w) (hw1 : w ≤ 1)
    (h_nonconc : ∀ (normal' : Point2) (t' : ℝ) (r : ℝ),
        ‖normal'‖ = 1 → δ ≤ r → r ≤ w →
        (E.filter fun p =>
          |inner ℝ p normal - t| ≤ w ∧
          |inner ℝ p normal' - t'| ≤ r).card ≤
        Real.rpow (r / w) ζ *
        (E.filter fun p => |inner ℝ p normal - t| ≤ w).card)
    (E' : DiscreteSet 2)
    (hE'_def : E' = E.filter fun p => |inner ℝ p normal - t| ≤ w) :
    ∀ (n : Point2), ‖n‖ = 1 → ∀ (t' r : ℝ), δ ≤ r →
      ((E'.filter fun y => |inner ℝ y n - t'| ≤ r).card : ENNReal) ≤
      ENNReal.ofReal ((w ^ ζ)⁻¹ * r ^ ζ) * (E'.card : ENNReal) := by
  have hw_pos : 0 < w := by linarith
  have h_pow_eq : ∀ (r : ℝ), 0 < r → Real.rpow (r / w) ζ = (w ^ ζ)⁻¹ * r ^ ζ := by
    intro r hr
    have h_div : (r / w) ^ ζ = r ^ ζ / w ^ ζ :=
      Real.div_rpow (by linarith) hw_pos.le ζ
    have h_goal : Real.rpow (r / w) ζ = (w ^ ζ)⁻¹ * r ^ ζ := by
      calc Real.rpow (r / w) ζ
        = (r / w) ^ ζ := by rfl
      _ = r ^ ζ / w ^ ζ := h_div
      _ = (w ^ ζ)⁻¹ * r ^ ζ := by field_simp
    exact h_goal
  intro n hn t' r hr
  have hr_pos : 0 < r := by linarith
  have h_filter_eq : (E.filter fun p =>
        |inner ℝ p normal - t| ≤ w ∧ |inner ℝ p n - t'| ≤ r) =
      E'.filter fun y => |inner ℝ y n - t'| ≤ r := by
    let P : Point2 → Prop := fun p => |inner ℝ p normal - t| ≤ w
    let Q : Point2 → Prop := fun y => |inner ℝ y n - t'| ≤ r
    have h5 : (E.filter P).filter Q = E.filter (fun p => P p ∧ Q p) := by
      ext x; simp [and_comm] <;> tauto
    have h6 : E'.filter Q = (E.filter P).filter Q := by
      rw [hE'_def] <;> rfl
    rw [h6]
    exact h5.symm
  by_cases h_case : r ≤ w
  · -- Case r ≤ w: use two-ends bound
    have h1 : ((E.filter fun p =>
          |inner ℝ p normal - t| ≤ w ∧ |inner ℝ p n - t'| ≤ r).card : ℝ) ≤
        Real.rpow (r / w) ζ * (E'.card : ℝ) := by
      rw [hE'_def]
      exact h_nonconc n t' r hn hr h_case
    rw [h_filter_eq] at h1
    have h2 : Real.rpow (r / w) ζ = (w ^ ζ)⁻¹ * r ^ ζ := h_pow_eq r hr_pos
    rw [h2] at h1
    have h_pos : 0 ≤ (w ^ ζ)⁻¹ * r ^ ζ := by positivity
    have h_enn : ENNReal.ofReal (((E'.filter fun y => |inner ℝ y n - t'| ≤ r).card : ℝ)) ≤
        ENNReal.ofReal ((w ^ ζ)⁻¹ * r ^ ζ * (E'.card : ℝ)) :=
      ENNReal.ofReal_le_ofReal h1
    have h_mul : ENNReal.ofReal ((w ^ ζ)⁻¹ * r ^ ζ * (E'.card : ℝ)) =
        ENNReal.ofReal ((w ^ ζ)⁻¹ * r ^ ζ) * ENNReal.ofReal ((E'.card : ℝ)) := by
      rw [ENNReal.ofReal_mul h_pos]
    have h_card1 : ENNReal.ofReal ((E'.card : ℝ)) = (E'.card : ENNReal) := by
      simp <;> norm_cast
    have h_card2 : ENNReal.ofReal (((E'.filter fun y => |inner ℝ y n - t'| ≤ r).card : ℝ)) =
        ((E'.filter fun y => |inner ℝ y n - t'| ≤ r).card : ENNReal) := by
      simp <;> norm_cast
    rw [h_card2, h_mul, h_card1] at h_enn
    exact h_enn
  · -- Case r > w: trivial bound
    have h_gt : w < r := by linarith
    have h_sub : (E'.filter fun y => |inner ℝ y n - t'| ≤ r) ⊆ E' :=
      Finset.filter_subset _ _
    have h4 : ((E'.filter fun y => |inner ℝ y n - t'| ≤ r).card : ENNReal) ≤
        (E'.card : ENNReal) := by
      exact_mod_cast Finset.card_le_card h_sub
    have h5 : 1 < r / w := by
      have h : w / w < r / w := by gcongr
      have hww : w / w = 1 := by field_simp [hw_pos.ne']
      rw [hww] at h; exact h
    have h6 : 1 < (r / w) ^ ζ := Real.one_lt_rpow h5 hζ
    have h7 : 1 < (w ^ ζ)⁻¹ * r ^ ζ := by
      have h8 : Real.rpow (r / w) ζ = (w ^ ζ)⁻¹ * r ^ ζ := h_pow_eq r hr_pos
      have h9 : (r / w) ^ ζ = Real.rpow (r / w) ζ := by rfl
      rw [h9, h8] at h6
      exact h6
    have h9 : (1 : ℝ) ≤ (w ^ ζ)⁻¹ * r ^ ζ := by linarith
    have h10 : (1 : ENNReal) ≤ ENNReal.ofReal ((w ^ ζ)⁻¹ * r ^ ζ) := by
      have h11 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal ((w ^ ζ)⁻¹ * r ^ ζ) := by
        gcongr <;> linarith
      simpa using h11
    have h11 : (E'.card : ENNReal) ≤
        ENNReal.ofReal ((w ^ ζ)⁻¹ * r ^ ζ) * (E'.card : ENNReal) := by
      have h12 : (1 : ENNReal) * (E'.card : ENNReal) ≤
          ENNReal.ofReal ((w ^ ζ)⁻¹ * r ^ ζ) * (E'.card : ENNReal) := by
        gcongr
        <;> exact h10
      simpa using h12
    exact le_trans h4 h11

end Kakeya.Assouad
