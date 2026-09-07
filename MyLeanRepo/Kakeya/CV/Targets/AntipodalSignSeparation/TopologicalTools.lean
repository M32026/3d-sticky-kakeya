import MyLeanRepo.Kakeya.CV.PolynomialMollification
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.OrderClosed

/-!
# Topological tools for antipodal sign separation

This file provides three auxiliary results used in the direct contradiction
proof of `antipodal_sign_separation`:

1. **Antipodal correspondence:** the polynomial at `-x` is the negation of the
   polynomial at `x`, so the positive and negative sign volumes swap.
2. **Sequence from closure:** in a first-countable space, every point in the
   closure of a set is the limit of a sequence from that set.
3. **Limit of strict inequalities:** if `a m > b m` for all `m` and both
   sequences converge in `ENNReal`, then the limit of `a` is at least the
   limit of `b`.
-/

noncomputable section

open MeasureTheory Filter

namespace Kakeya.CV

/-! ### Antipodal correspondence -/

/-- The parameter polynomial is odd in the coefficient vector because the
linear equivalence `P.equiv` preserves negation. -/
lemma parameterPolynomial_neg {k : ℕ} (P : PolynomialParameterization k)
    (x : CoefficientSpace P.dim) :
    parameterPolynomial P (-x) = -parameterPolynomial P x := by
  have h1 : P.equiv (-x) = -P.equiv x := by
    exact map_neg P.equiv x
  have h_main : parameterPolynomial P (-x) = -parameterPolynomial P x := by
    dsimp only [parameterPolynomial]
    exact congr_arg (fun p : degreeLESubmodule k => (p : MvPolynomial (Fin 3) ℝ)) h1
  exact h_main

/-- Evaluating the negation of a polynomial gives the negation of the value. -/
lemma polynomialValue_neg (p : MvPolynomial (Fin 3) ℝ) (y : Point 3) :
    polynomialValue (-p) y = -polynomialValue p y := by
  simp [polynomialValue]

/-- Parameters where the negative sign volume strictly exceeds the positive
sign volume.  This is the antipodal counterpart of `positiveSignClass`. -/
def negativeSignClass {k : ℕ} (P : PolynomialParameterization k)
    (selectedRegion : CoefficientSpace P.dim → Set (Point 3))
    (D : Set (CoefficientSpace P.dim)) : Set (CoefficientSpace P.dim) :=
  {x | x ∈ D ∧
    volume (selectedRegion x ∩ {y | polynomialValue (parameterPolynomial P x) y < 0}) >
      volume (selectedRegion x ∩ {y | 0 < polynomialValue (parameterPolynomial P x) y})}

/-- A parameter lies in the positive sign class exactly when its antipode lies
in the negative sign class, assuming the selected region is antipodally
invariant and `D` is antipodal. -/
lemma positiveSignClass_neg_iff {k : ℕ}
    (P : PolynomialParameterization k)
    (selectedRegion : CoefficientSpace P.dim → Set (Point 3))
    (D : Set (CoefficientSpace P.dim))
    (hD_antipodal : ∀ x, x ∈ D → -x ∈ D)
    (hRegion_antipodal : ∀ x, x ∈ D → selectedRegion (-x) = selectedRegion x) :
    ∀ (x : CoefficientSpace P.dim), x ∈ D →
      (x ∈ positiveSignClass P selectedRegion D ↔
        -x ∈ negativeSignClass P selectedRegion D) := by
  intro x hx
  have hx' : -x ∈ D := hD_antipodal x hx
  have h_reg : selectedRegion (-x) = selectedRegion x := hRegion_antipodal x hx
  have h_poly : parameterPolynomial P (-x) = -parameterPolynomial P x :=
    parameterPolynomial_neg P x
  simp only [positiveSignClass, negativeSignClass, Set.mem_setOf_eq]
  have h1 : {y : Point 3 | 0 < polynomialValue (parameterPolynomial P (-x)) y} =
      {y : Point 3 | polynomialValue (parameterPolynomial P x) y < 0} := by
    ext y
    rw [h_poly]
    simp [polynomialValue_neg]
  have h2 : {y : Point 3 | polynomialValue (parameterPolynomial P (-x)) y < 0} =
      {y : Point 3 | 0 < polynomialValue (parameterPolynomial P x) y} := by
    ext y
    rw [h_poly]
    simp [polynomialValue_neg]
  constructor
  · rintro ⟨hD, h_ineq⟩
    refine ⟨hx', ?_⟩
    rw [h_reg, h1, h2]
    exact h_ineq
  · rintro ⟨hD, h_ineq⟩
    refine ⟨hx, ?_⟩
    rw [h_reg, h1, h2] at h_ineq
    exact h_ineq

/-- The negative sign class is the antipodal image of the positive sign class. -/
lemma negativeSignClass_eq_image {k : ℕ}
    (P : PolynomialParameterization k)
    (selectedRegion : CoefficientSpace P.dim → Set (Point 3))
    (D : Set (CoefficientSpace P.dim))
    (hD_antipodal : ∀ x, x ∈ D → -x ∈ D)
    (hRegion_antipodal : ∀ x, x ∈ D → selectedRegion (-x) = selectedRegion x) :
    negativeSignClass P selectedRegion D =
      (fun x : CoefficientSpace P.dim => -x) '' positiveSignClass P selectedRegion D := by
  ext y
  simp only [negativeSignClass, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · intro hy
    have h_yD : y ∈ D := hy.1
    have h_neg_yD : -y ∈ D := hD_antipodal y h_yD
    have h_iff_raw : (-y ∈ positiveSignClass P selectedRegion D ↔
        -(-y) ∈ negativeSignClass P selectedRegion D) :=
      positiveSignClass_neg_iff P selectedRegion D hD_antipodal hRegion_antipodal
        (-y) h_neg_yD
    have h_neg_neg : -(-y) = y := by simp
    have h_iff : (-y ∈ positiveSignClass P selectedRegion D ↔
        y ∈ negativeSignClass P selectedRegion D) := by
      rw [h_neg_neg] at h_iff_raw
      exact h_iff_raw
    have h3 : -y ∈ positiveSignClass P selectedRegion D :=
      h_iff.mpr hy
    exact ⟨-y, h3, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    have h_xD : x ∈ D := hx.1
    have h_iff : x ∈ positiveSignClass P selectedRegion D ↔
        -x ∈ negativeSignClass P selectedRegion D :=
      positiveSignClass_neg_iff P selectedRegion D hD_antipodal hRegion_antipodal
        x h_xD
    exact h_iff.mp hx

/-! ### Sequence from closure -/

/-- In a first-countable topological space, every point in the closure of a set
is the limit of a sequence taking values in that set.

This is a direct application of `mem_closure_iff_seq_limit`, which holds in
any `FrechetUrysohnSpace` (and every first-countable space is one). -/
lemma exists_seq_in_closure_tendsto {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] {S : Set X} {z : X}
    (h : z ∈ closure S) :
    ∃ (zseq : ℕ → X), (∀ m, zseq m ∈ S) ∧ Tendsto zseq atTop (nhds z) := by
  have h_main : z ∈ closure S ↔ ∃ (x : ℕ → X),
      (∀ n, x n ∈ S) ∧ Tendsto x atTop (nhds z) :=
    mem_closure_iff_seq_limit
  exact h_main.mp h

/-! ### Limit of strict inequalities in `ENNReal` -/

/-- If `a m > b m` for all `m` and both sequences converge in `ENNReal`, then
the limit of `a` is at least the limit of `b`.

This follows from `le_of_tendsto_of_tendsto`, since `a m > b m` implies
`b m ≤ a m` everywhere, and `ENNReal` has an order-closed topology. -/
lemma le_limit_of_strict_ineq {a b : ℕ → ENNReal} {a_lim b_lim : ENNReal}
    (ha : Tendsto a atTop (nhds a_lim))
    (hb : Tendsto b atTop (nhds b_lim))
    (h_strict : ∀ m, b m < a m) :
    b_lim ≤ a_lim := by
  have h_le : ∀ m, b m ≤ a m := fun m => (h_strict m).le
  have h_eventually : b ≤ᶠ[atTop] a := by
    filter_upwards with m
    exact h_le m
  exact le_of_tendsto_of_tendsto hb ha h_eventually

end Kakeya.CV
