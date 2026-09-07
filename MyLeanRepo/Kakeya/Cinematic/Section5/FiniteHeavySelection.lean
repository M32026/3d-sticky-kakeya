import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Finite heavy-element selection

These elementary weighted estimates support the two heavy refinements after
the incidence-degree pigeonhole in PYZ Section 5.
-/

namespace Kakeya.Cinematic

lemma sum_le_heavy_card_mul_add_light_card_mul
    {α : Type*} [DecidableEq α]
    (elements : Finset α) (weight : α → ℝ)
    (threshold upper : ℝ)
    (hupper : ∀ element ∈ elements, weight element ≤ upper) :
    ∑ element ∈ elements, weight element ≤
      ((elements.filter fun element =>
          threshold ≤ weight element).card : ℝ) * upper +
        ((elements.filter fun element =>
          ¬ threshold ≤ weight element).card : ℝ) * threshold := by
  let heavy := elements.filter fun element =>
    threshold ≤ weight element
  let light := elements.filter fun element =>
    ¬ threshold ≤ weight element
  have hpartition :
      (∑ element ∈ elements, weight element) =
        (∑ element ∈ heavy, weight element) +
          ∑ element ∈ light, weight element := by
    simpa [heavy, light] using
      (Finset.sum_filter_add_sum_filter_not
        (s := elements) (p := fun element =>
          threshold ≤ weight element) weight).symm
  have hheavy :
      (∑ element ∈ heavy, weight element) ≤
        (heavy.card : ℝ) * upper := by
    calc
      (∑ element ∈ heavy, weight element) ≤
          ∑ _element ∈ heavy, upper := by
        apply Finset.sum_le_sum
        intro element helement
        exact hupper element (Finset.filter_subset _ _ helement)
      _ = (heavy.card : ℝ) * upper := by
        simp [Finset.sum_const]
  have hlight :
      (∑ element ∈ light, weight element) ≤
        (light.card : ℝ) * threshold := by
    calc
      (∑ element ∈ light, weight element) ≤
          ∑ _element ∈ light, threshold := by
        apply Finset.sum_le_sum
        intro element helement
        have hnot :
            ¬ threshold ≤ weight element :=
          (Finset.mem_filter.mp helement).2
        exact le_of_lt (lt_of_not_ge hnot)
      _ = (light.card : ℝ) * threshold := by
        simp [Finset.sum_const]
  rw [hpartition]
  exact add_le_add hheavy hlight

lemma sum_le_heavy_card_mul_add_card_mul
    {α : Type*} [DecidableEq α]
    (elements : Finset α) (weight : α → ℝ)
    (threshold upper : ℝ)
    (hthreshold : 0 ≤ threshold)
    (hupper : ∀ element ∈ elements, weight element ≤ upper) :
    ∑ element ∈ elements, weight element ≤
      ((elements.filter fun element =>
          threshold ≤ weight element).card : ℝ) * upper +
        (elements.card : ℝ) * threshold := by
  have hmain :=
    sum_le_heavy_card_mul_add_light_card_mul
      elements weight threshold upper hupper
  calc
    (∑ element ∈ elements, weight element) ≤
        ((elements.filter fun element =>
            threshold ≤ weight element).card : ℝ) * upper +
          ((elements.filter fun element =>
            ¬ threshold ≤ weight element).card : ℝ) * threshold :=
      hmain
    _ ≤
        ((elements.filter fun element =>
            threshold ≤ weight element).card : ℝ) * upper +
          (elements.card : ℝ) * threshold := by
      have hcard :
          (((elements.filter fun element =>
              ¬ threshold ≤ weight element).card : ℕ) : ℝ) ≤
            (elements.card : ℝ) := by
        exact_mod_cast
          Finset.card_filter_le
            elements (fun element => ¬ threshold ≤ weight element)
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hcard hthreshold)

lemma heavy_card_lower
    {α : Type*} [DecidableEq α]
    (elements : Finset α) (weight : α → ℝ)
    (threshold upper lower : ℝ)
    (hthreshold : 0 ≤ threshold)
    (hupper_pos : 0 < upper)
    (hupper : ∀ element ∈ elements, weight element ≤ upper)
    (hlower : lower ≤ ∑ element ∈ elements, weight element) :
    (lower - (elements.card : ℝ) * threshold) / upper ≤
      ((elements.filter fun element =>
        threshold ≤ weight element).card : ℝ) := by
  have hsum :=
    sum_le_heavy_card_mul_add_card_mul
      elements weight threshold upper hthreshold hupper
  apply (div_le_iff₀ hupper_pos).2
  linarith

lemma heavy_nonempty
    {α : Type*} [DecidableEq α]
    (elements : Finset α) (weight : α → ℝ)
    (threshold upper lower : ℝ)
    (hthreshold : 0 ≤ threshold)
    (hupper_pos : 0 < upper)
    (hupper : ∀ element ∈ elements, weight element ≤ upper)
    (hlower : lower ≤ ∑ element ∈ elements, weight element)
    (hstrict : (elements.card : ℝ) * threshold < lower) :
    (elements.filter fun element =>
      threshold ≤ weight element).Nonempty := by
  have hcard :=
    heavy_card_lower elements weight threshold upper lower
      hthreshold hupper_pos hupper hlower
  have hquotient_pos :
      0 < (lower - (elements.card : ℝ) * threshold) / upper := by
    positivity
  have hcard_pos :
      0 <
        ((elements.filter fun element =>
          threshold ≤ weight element).card : ℝ) :=
    hquotient_pos.trans_le hcard
  exact Finset.card_pos.mp <| by
    exact_mod_cast hcard_pos

end Kakeya.Cinematic
