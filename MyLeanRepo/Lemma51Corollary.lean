module

/-
# Discretized Lemma 5.1 — Projection Product-Case Inequality

A direct corollary of `discretized_bourgain_averaging16`, specializing
`B1 = A` and `B2 = B` to obtain the paper's Lemma `lem.proj-product-case`
in discretized covering-number form.

## Statement

For bounded `A, B ⊂ ℝ`, `G ⊂ A × B`, and `|x| ≤ 1`:
```
Nδ(A + x·A) · Nδ(G) ≤ 16 · Nδ(A - A) · Nδ(B - A) · Nδ(π_x(G))
```

Equivalently:
```
Nδ(π_x(G)) ≥ Nδ(A + x·A) · Nδ(G) / (16 · Nδ(A - A) · Nδ(B - A))
```

This is the discretized version of Lemma `lem.proj-product-case` in
Corso-Shmerkin-Wang (arXiv 2511.21656).

## Dependencies

- `MyLeanRepo.DiscretizedBourgainAveraging` — `discretized_bourgain_averaging16`
- `MyLeanRepo.Compat` — `projectionSet1D`
-/

public import MyLeanRepo.DiscretizedBourgainAveraging
public import MyLeanRepo.Compat
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory ENNReal Set Bornology ProductLikeIncidence

namespace WeakTwoEndsSumProduct

/-- **Discretized Lemma 5.1** (projection product-case inequality).

For `π_x(a,b) = a + x·b`, bounded `A, B ⊂ ℝ`, and `G ⊂ A × B`:
```
Nδ(A + x·A) * Nδ(G) ≤ 16 * Nδ(A - A) * Nδ(B - A) * Nδ(π_x(G))
```

This is a direct specialization of `discretized_bourgain_averaging16`
with `B1 := A` and `B2 := B`. -/
lemma discretized_lemma51 {δ x : ℝ} (hδ : 0 < δ) (hx : |x| ≤ 1)
    {A B : Set ℝ} (hA : IsBounded A) (hB : IsBounded B)
    {G : Set (EuclideanSpace ℝ (Fin 2))} (hG : IsBounded G)
    (hG_sub : ∀ p ∈ G, p 0 ∈ A ∧ p 1 ∈ B) :
    ENat.toENNReal (dyadicCoveringNumber δ
      (_root_.productLikeRealLineCopy (Set.image2 (fun a1 a2 => a1 + x * a2) A A))) *
    ENat.toENNReal (dyadicCoveringNumber δ G) ≤
    16 * ENat.toENNReal (dyadicCoveringNumber δ
      (_root_.productLikeRealLineCopy (Set.image2 (· - ·) A A))) *
    ENat.toENNReal (dyadicCoveringNumber δ
      (_root_.productLikeRealLineCopy (Set.image2 (· - ·) B A))) *
    ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D x G)) := by
  exact bourgain_projection_theorem.discretized_bourgain_averaging16 hδ
    (hA := hA) (hB1 := hA) (hB2 := hB) (hB := hG)
    (hB_sub := hG_sub) (hA_sub := Set.Subset.refl A) (hx := hx)

end WeakTwoEndsSumProduct
