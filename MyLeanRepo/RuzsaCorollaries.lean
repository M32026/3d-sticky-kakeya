module

/-
# Ruzsa and Plünnecke-Ruzsa Corollaries

Derived corollaries of the discretized Ruzsa triangle and Plünnecke-Ruzsa
inequalities, needed for the Weak Two-Ends Sum-Product Theorem (Ring Theorem).

## Main results

- `ruzsa_cor_sum_to_diff`: `N(X-Y) · N(X) · N(Y) ≤ 81 · N(X+Y)³`

## Proof route

1. Ruzsa triangle with `Z = X`: `N(X-Y) · N(X) ≤ 9 · N(X+X) · N(X+Y)`
2. PR sum: `N(X+X) · N(Y) ≤ 9 · N(X+Y)²`
3. Multiply and substitute to get the cubic bound.

## References

- Corso-Shmerkin-Wang, arXiv:2511.21656, Section 2.1 (Corollary 2.4)
-/

public import MyLeanRepo.RuzsaTriangle
public import MyLeanRepo.DiscretizedPluennecke
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped BigOperators Pointwise

namespace ProductLikeIncidence

/-! ## Corollary 2.4: Sum-to-difference bound -/

/-- If `X, Y` are bounded nonempty subsets of `ℝ`, then
    `N(X-Y) · N(X) · N(Y) ≤ 81 · N(X+Y)³`.

    This follows from the Ruzsa triangle inequality (with `Z = X`) combined
    with the Plünnecke-Ruzsa sum inequality. -/
lemma ruzsa_cor_sum_to_diff {δ : ℝ} (hδ : 0 < δ)
    {X Y : Set ℝ} (hX : Bornology.IsBounded X)
    (hY : Bornology.IsBounded Y)
    (hX_nonempty : X.Nonempty) (hY_nonempty : Y.Nonempty) :
    ENat.toENNReal (dyadicCoveringNumber δ
      (productLikeRealLineCopy (Set.image2 (· - ·) X Y))) *
    ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy X)) *
    ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy Y)) ≤
    81 * ENat.toENNReal (dyadicCoveringNumber δ
      (productLikeRealLineCopy (Set.image2 (· + ·) X Y))) ^ 3 := by
  let NXY := ENat.toENNReal (dyadicCoveringNumber δ
    (productLikeRealLineCopy (Set.image2 (· - ·) X Y)))
  let NX := ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy X))
  let NY := ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy Y))
  let NXX := ENat.toENNReal (dyadicCoveringNumber δ
    (productLikeRealLineCopy (Set.image2 (· + ·) X X)))
  let NXplusY := ENat.toENNReal (dyadicCoveringNumber δ
    (productLikeRealLineCopy (Set.image2 (· + ·) X Y)))
  -- Step 1: Ruzsa triangle with Z = X
  have h1 : NXY * NX ≤ 9 * NXX * NXplusY :=
    discretized_ruzsa_triangle hδ hX hY hX hX_nonempty
  -- Step 2: Plünnecke-Ruzsa sum
  have h2 : NXX * NY ≤ 9 * NXplusY * NXplusY :=
    discretized_pluennecke_ruzsa_sum hδ hX hY hY_nonempty
  -- Step 3: Multiply h1 by NY on the right
  have h3 : NXY * NX * NY ≤ (9 * NXX * NXplusY) * NY := by
    calc
      NXY * NX * NY
        = (NXY * NX) * NY := by rw [mul_assoc]
      _ ≤ (9 * NXX * NXplusY) * NY := by gcongr <;> exact h1
  -- Step 4: Use h2 to bound NXX * NY
  have h4 : (9 * NXX * NXplusY) * NY ≤ 81 * NXplusY ^ 3 := by
    calc
      (9 * NXX * NXplusY) * NY
        = 9 * (NXX * NY) * NXplusY := by ring
      _ ≤ 9 * (9 * NXplusY * NXplusY) * NXplusY := by gcongr <;> exact h2
      _ = 81 * NXplusY ^ 3 := by
        simp [pow_two, pow_three] <;> ring
  exact le_trans h3 h4

end ProductLikeIncidence
