import Mathlib.Algebra.Order.Field.GeomSum
import MyLeanRepo.Kakeya.CV.Statements

/-!
# Cardinality of dyadic bad-set atoms

Sums the finite colour and dyadic atom counts once the atomwise cardinality
bound has been established.
-/

namespace Kakeya.CV

open NNReal

/-- Finite geometric series bound in `ℝ≥0`. -/
lemma geometric_series_bound_nnreal (n : ℕ) :
    ∑ r ∈ Finset.range n, ((1 : ℝ≥0) / 8) ^ r ≤ (8 : ℝ≥0) / 7 := by
  have h_le : (1 : ℝ≥0) / 8 ≤ 1 := by
    have h : ((1 : ℝ≥0) / 8 : ℝ) ≤ (1 : ℝ) := by norm_num
    exact NNReal.coe_le_coe.mp h
  have h : ∑ i ∈ Finset.range n, ((1 : ℝ≥0) / 8) ^ i <
      (1 - ((1 : ℝ≥0) / 8))⁻¹ :=
    geom_sum_lt (by norm_num) (by norm_num) n
  have h_sub : (1 : ℝ≥0) - (1 : ℝ≥0) / 8 = (7 : ℝ≥0) / 8 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub h_le]
    norm_num
  have h_inv : ((7 : ℝ≥0) / 8)⁻¹ = (8 : ℝ≥0) / 7 := inv_div 7 8
  rw [h_sub, h_inv] at h
  exact h.le

theorem badSet_atom_cardinality_bound :
    BadSetAtomCardinalityStatement := by
  dsimp only [BadSetAtomCardinalityStatement]
  refine' fun Cube Colour _ _ levels Atom _ M D h_atom h_sum => _
  let one_eighth : ℝ≥0 := 1 / 8
  let eight_sevenths : ℝ≥0 := 8 / 7
  have h1 : (Fintype.card (Σ q, Σ r, Σ c, Atom q r c) : ℝ≥0) =
      ∑ q, ∑ r : Fin (levels q), ∑ c : Colour,
        (Fintype.card (Atom q r c) : ℝ≥0) := by
    simp [Fintype.card_sigma]
  have h2 : ∑ q, ∑ r : Fin (levels q), ∑ c : Colour,
      (Fintype.card (Atom q r c) : ℝ≥0) ≤
      ∑ q, ∑ r : Fin (levels q), ∑ c : Colour,
        (one_eighth ^ (r : ℕ) * M q ^ 3) := by
    apply Finset.sum_le_sum
    intro q _
    apply Finset.sum_le_sum
    intro r _
    apply Finset.sum_le_sum
    intro c _
    exact h_atom q r c
  have h_card_colour : (Finset.univ : Finset Colour).card = Fintype.card Colour :=
    Finset.card_univ
  have h3 : ∑ q, ∑ r : Fin (levels q), ∑ c : Colour,
      (one_eighth ^ (r : ℕ) * M q ^ 3) =
      (Fintype.card Colour : ℝ≥0) *
        ∑ q, (∑ r : Fin (levels q), one_eighth ^ (r : ℕ)) * M q ^ 3 := by
    have h4 : ∀ q, (∑ r : Fin (levels q),
        ∑ c : Colour, (one_eighth ^ (r : ℕ) * M q ^ 3)) =
        (Fintype.card Colour : ℝ≥0) *
          (∑ r : Fin (levels q), one_eighth ^ (r : ℕ)) * M q ^ 3 := by
      intro q
      have h5 : ∀ r : Fin (levels q),
          ∑ c : Colour, (one_eighth ^ (r : ℕ) * M q ^ 3) =
            (Fintype.card Colour : ℝ≥0) *
              (one_eighth ^ (r : ℕ) * M q ^ 3) := by
        intro r
        rw [Finset.sum_const, h_card_colour]
        ring
      have h_sum_r : ∑ r : Fin (levels q),
          ∑ c : Colour, (one_eighth ^ (r : ℕ) * M q ^ 3) =
          ∑ r : Fin (levels q), (Fintype.card Colour : ℝ≥0) *
            (one_eighth ^ (r : ℕ) * M q ^ 3) := by
        apply Finset.sum_congr rfl
        intro r _
        exact h5 r
      rw [h_sum_r]
      have h6 : ∑ r : Fin (levels q), (Fintype.card Colour : ℝ≥0) *
          (one_eighth ^ (r : ℕ) * M q ^ 3) =
          (Fintype.card Colour : ℝ≥0) *
            (∑ r : Fin (levels q), one_eighth ^ (r : ℕ)) * M q ^ 3 := by
        have h7 : ∑ r : Fin (levels q), (Fintype.card Colour : ℝ≥0) *
            (one_eighth ^ (r : ℕ) * M q ^ 3) =
            (Fintype.card Colour : ℝ≥0) *
              ∑ r : Fin (levels q), (one_eighth ^ (r : ℕ) * M q ^ 3) := by
          rw [Finset.mul_sum]
        rw [h7]
        have h8 : ∑ r : Fin (levels q), (one_eighth ^ (r : ℕ) * M q ^ 3) =
            (∑ r : Fin (levels q), one_eighth ^ (r : ℕ)) * M q ^ 3 := by
          rw [Finset.sum_mul]
        rw [h8]
        ring
      exact h6
    have h9 : ∑ q, ∑ r : Fin (levels q),
        ∑ c : Colour, (one_eighth ^ (r : ℕ) * M q ^ 3) =
        ∑ q, ((Fintype.card Colour : ℝ≥0) *
          (∑ r : Fin (levels q), one_eighth ^ (r : ℕ)) * M q ^ 3) := by
      apply Finset.sum_congr rfl
      intro q _
      exact h4 q
    rw [h9]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  have h6 : ∑ q, (∑ r : Fin (levels q), one_eighth ^ (r : ℕ)) * M q ^ 3 ≤
      eight_sevenths * ∑ q, M q ^ 3 := by
    have h7 : ∀ q,
        (∑ r : Fin (levels q), one_eighth ^ (r : ℕ)) ≤ eight_sevenths := by
      intro q
      have h8 : ∑ r : Fin (levels q), one_eighth ^ (r : ℕ) =
          ∑ r ∈ Finset.range (levels q), one_eighth ^ r := by
        apply Finset.sum_bij' (fun (x : Fin (levels q)) _ => (x : ℕ))
          (fun x hx => ⟨x, Finset.mem_range.mp hx⟩)
        <;> simp
      rw [h8]
      exact geometric_series_bound_nnreal (levels q)
    have h9 : ∑ q, (∑ r : Fin (levels q), one_eighth ^ (r : ℕ)) * M q ^ 3 ≤
        ∑ q, eight_sevenths * M q ^ 3 := by
      apply Finset.sum_le_sum
      intro q _
      exact mul_le_mul_of_nonneg_right (h7 q) (by positivity)
    have h10 : ∑ q, eight_sevenths * M q ^ 3 =
        eight_sevenths * ∑ q, M q ^ 3 := by
      rw [Finset.mul_sum]
    exact le_trans h9 h10.le
  have h_final : ∑ q, ∑ r : Fin (levels q), ∑ c : Colour,
      (Fintype.card (Atom q r c) : ℝ≥0) ≤
      (Fintype.card Colour : ℝ≥0) * eight_sevenths * D := by
    calc
      ∑ q, ∑ r : Fin (levels q), ∑ c : Colour,
          (Fintype.card (Atom q r c) : ℝ≥0)
        ≤ ∑ q, ∑ r : Fin (levels q), ∑ c : Colour,
          (one_eighth ^ (r : ℕ) * M q ^ 3) := h2
      _ = (Fintype.card Colour : ℝ≥0) *
          ∑ q, (∑ r : Fin (levels q), one_eighth ^ (r : ℕ)) * M q ^ 3 := h3
      _ ≤ (Fintype.card Colour : ℝ≥0) *
          (eight_sevenths * ∑ q, M q ^ 3) := by
            exact mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = (Fintype.card Colour : ℝ≥0) * eight_sevenths *
          (∑ q, M q ^ 3) := by ring
      _ ≤ (Fintype.card Colour : ℝ≥0) * eight_sevenths * D := by
            gcongr
  rw [h1]
  exact h_final

end Kakeya.CV
