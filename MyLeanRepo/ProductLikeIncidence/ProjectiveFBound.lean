module

/-
# Projective F Bound

Bounds the coordinates of the projectively normalized point `F q` given
bounds on `q` and the direction parameters `θ1, θ2`.

Given `|q 0|, |q 1| ≤ R`, `|θ1|, |θ2| ≤ 1`, and the projective formulas
for `F`, proves `|(F q) 0| ≤ 2R` and `|(F q) 1| ≤ 2R`.

This is used to derive `hS1_bdd`/`hS2_bdd` for Helper5: the rounded
coordinate sets `S1, S2` are bounded by `R_norm + 1 = 2R + 1`.

## Key insight

The coefficients `(θ3-θ1)/(θ2-θ1)` and `(θ2-θ3)/(θ2-θ1)` both lie in `[0,1]`
when `θ1 < θ3 < θ2`. Combined with `|θi| ≤ 1`, each coordinate of `F q`
is bounded by `|q 0| + |q 1| ≤ 2R`.
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set

namespace ProductLikeIncidence.ProductReduction

/-- Bound on projective normalization: if `|q 0|, |q 1| ≤ R` and `|θ1|, |θ2| ≤ 1`,
then both coordinates of `F q` are bounded by `2R`. -/
lemma projective_F_bound
    (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (q : EuclideanSpace ℝ (Fin 2))
    (θ1 θ2 θ3 R : ℝ)
    (h_ord13 : θ1 < θ3) (h_ord32 : θ3 < θ2)
    (hθ1_abs : |θ1| ≤ 1) (hθ2_abs : |θ2| ≤ 1)
    (hq0_le_R : |q 0| ≤ R) (hq1_le_R : |q 1| ≤ R)
    (hF0_eq : (F q) 0 = ((θ3 - θ1) / (θ2 - θ1)) * (q 0 * θ2 + q 1))
    (hF1_eq : (F q) 1 = ((θ2 - θ3) / (θ2 - θ1)) * (q 0 * θ1 + q 1)) :
    |(F q) 0| ≤ 2 * R ∧ |(F q) 1| ≤ 2 * R := by
  have hb3 : |(θ3 - θ1) / (θ2 - θ1)| ≤ 1 := by
    have h_pos : 0 < θ2 - θ1 := by linarith
    have h : (θ3 - θ1) / (θ2 - θ1) ≤ 1 := by
      apply (div_le_one h_pos).mpr <;> linarith
    have h' : 0 ≤ (θ3 - θ1) / (θ2 - θ1) := by positivity
    rw [abs_of_nonneg h'] <;> exact h
  have ha3 : |(θ2 - θ3) / (θ2 - θ1)| ≤ 1 := by
    have h_pos : 0 < θ2 - θ1 := by linarith
    have h : (θ2 - θ3) / (θ2 - θ1) ≤ 1 := by
      apply (div_le_one h_pos).mpr <;> linarith
    have h' : 0 ≤ (θ2 - θ3) / (θ2 - θ1) := by positivity
    rw [abs_of_nonneg h'] <;> exact h
  have h_tri1 : |q 0 * θ2 + q 1| ≤ |q 0| * |θ2| + |q 1| := by
    calc
      |q 0 * θ2 + q 1| ≤ |q 0 * θ2| + |q 1| := abs_add_le _ _
      _ = |q 0| * |θ2| + |q 1| := by rw [abs_mul]
  have h_tri2 : |q 0 * θ1 + q 1| ≤ |q 0| * |θ1| + |q 1| := by
    calc
      |q 0 * θ1 + q 1| ≤ |q 0 * θ1| + |q 1| := abs_add_le _ _
      _ = |q 0| * |θ1| + |q 1| := by rw [abs_mul]
  have hR_nonneg : 0 ≤ R := le_trans (abs_nonneg (q 0)) hq0_le_R
  have h0 : |(F q) 0| ≤ 2 * R := by
    rw [hF0_eq, abs_mul]
    have h_mul : |(θ3 - θ1) / (θ2 - θ1)| * |q 0 * θ2 + q 1| ≤ |q 0 * θ2 + q 1| :=
      mul_le_of_le_one_left (abs_nonneg _) hb3
    have h_mul1 : |q 0| * |θ2| ≤ R := by
      calc |q 0| * |θ2| ≤ R * 1 := mul_le_mul hq0_le_R hθ2_abs (abs_nonneg _) hR_nonneg
           _ = R := by ring
    have h_final : |q 0 * θ2 + q 1| ≤ 2 * R := by
      calc |q 0 * θ2 + q 1| ≤ |q 0| * |θ2| + |q 1| := h_tri1
           _ ≤ R + R := add_le_add h_mul1 hq1_le_R
           _ = 2 * R := by ring
    exact le_trans h_mul h_final
  have h1 : |(F q) 1| ≤ 2 * R := by
    rw [hF1_eq, abs_mul]
    have h_mul : |(θ2 - θ3) / (θ2 - θ1)| * |q 0 * θ1 + q 1| ≤ |q 0 * θ1 + q 1| :=
      mul_le_of_le_one_left (abs_nonneg _) ha3
    have h_mul1 : |q 0| * |θ1| ≤ R := by
      calc |q 0| * |θ1| ≤ R * 1 := mul_le_mul hq0_le_R hθ1_abs (abs_nonneg _) hR_nonneg
           _ = R := by ring
    have h_final : |q 0 * θ1 + q 1| ≤ 2 * R := by
      calc |q 0 * θ1 + q 1| ≤ |q 0| * |θ1| + |q 1| := h_tri2
           _ ≤ R + R := add_le_add h_mul1 hq1_le_R
           _ = 2 * R := by ring
    exact le_trans h_mul h_final
  exact ⟨h0, h1⟩

end ProductLikeIncidence.ProductReduction
