module

/-
# Product-Like Incidence Sum Product Theorem

This module contains the main theorem `product_like_incidence_sum_product`
(Proposition A.7 from the reference paper).

## Theorem Statement

Given `0 < s < 1` and `τ > 0`, there exists an exponent `η = η(s, τ) > 0` such
that, for all sufficiently small dyadic positive scales `δ`, the following
product-like incidence lower bound holds.

If `Y ⊆ δℤ ∩ [0,1]` is a `(δ, τ, δ^{-η})`-set, each fiber `X y ⊆ δℤ ∩ [0,1]`
is a `(δ, s, δ^{-η})`-set, and every point in the product-like incidence set is
assigned a `(δ, s, δ^{-η})`-set of Appendix dyadic `δ`-tubes through it, then
the union of all assigned tubes has cardinality at least `δ^{-2s-η}`.

## Dependencies

- `MyLeanRepo.CoreDefinitions` — all shared definitions
- `MyLeanRepo.ProductLikeBasic` — basic infrastructure lemmas
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProductReduction
public import MyLeanRepo.WeakTwoEndsSumProduct
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

/--
[prop.product_like_incidence_sum_product.3031] Proposition A.7.  Given
`0 < s < 1` and `τ > 0`, there is an exponent `η = η(s, τ) > 0` such that, for
all sufficiently small dyadic positive scales `δ`, the following product-like
incidence lower bound holds.  If `Y ⊆ δℤ ∩ [0,1]` is a `(δ, τ, δ^{-η})`-set,
each fiber `X y ⊆ δℤ ∩ [0,1]` is a `(δ, s, δ^{-η})`-set, and every point
`z ∈ ⋃ y ∈ Y, X_y × {y}` is assigned a `(δ, s, δ^{-η})`-set of Appendix dyadic
`δ`-tubes through `z`, then the union of all assigned tubes has cardinality at
least `δ^{-2s-η}`.

The dyadic-scale restriction on `δ` is explicit.  The tube-set hypothesis uses
the Appendix parameter-realization convention: the union of chosen dyadic
parameter cubes for the tube family is an `IsDeltaSCSet`, with the tube exponent
restricted by `s ≤ 1`.  Cardinalities of tube families are recorded by
`Set.encard`, coerced to `ℝ≥0∞`, so the conclusion also covers the infinite case.
-/
theorem product_like_incidence_sum_product (s τ : ℝ) (hs_pos : 0 < s)
    (hs_lt_one : s < 1) (hτ_pos : 0 < τ) :
    ∃ η : ℝ, 0 < η ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧
        ∀ {δ : ℝ}, δ ∈ dyadicScales → 0 < δ → δ ≤ δ₀ →
          ∀ (Y : Set ℝ) (X : ℝ → Set ℝ)
            (𝒯z : EuclideanSpace ℝ (Fin 2) → Set (Set (EuclideanSpace ℝ (Fin 2)))),
            Y ⊆ productLikeUnitGrid δ →
              IsProductLikeRealDeltaSCSet δ τ (δ ^ (-η)) Y →
                (∀ y ∈ Y,
                  X y ⊆ productLikeUnitGrid δ ∧
                    IsProductLikeRealDeltaSCSet δ s (δ ^ (-η)) (X y)) →
                  (∀ z ∈ productLikeIncidenceSet Y X,
                    IsProductLikeAppendixDeltaSCSetOfDyadicTubes δ s (δ ^ (-η)) (𝒯z z) ∧
                      ∀ T ∈ 𝒯z z, z ∈ T) →
                    let 𝒯 : Set (Set (EuclideanSpace ℝ (Fin 2))) :=
                      ⋃ z ∈ productLikeIncidenceSet Y X, 𝒯z z
                    ENNReal.ofReal (δ ^ (-(2 * s + η))) ≤ ENat.toENNReal 𝒯.encard := by
  let κ0 : ℝ := min s τ / 4
  have hkappa_pos : 0 < κ0 := by
    dsimp only [κ0]
    have h1 : 0 < min s τ := by positivity
    linarith
  have hkappa_lt_s : κ0 < s := by
    dsimp only [κ0]
    have h1 : min s τ ≤ s := min_le_left s τ
    linarith
  have h2kappa_lt_tau : 2 * κ0 < τ := by
    dsimp only [κ0]
    have h1 : min s τ ≤ τ := min_le_right s τ
    linarith
  have hkappa_le_s : κ0 ≤ s := le_of_lt hkappa_lt_s
  let η_nc : ℝ := 1
  have hη_nc_pos : 0 < η_nc := by norm_num
  have h_ring : WeakTwoEndsSumProduct s κ0 :=
    WeakTwoEndsSumProduct.weak_two_ends_sum_product s κ0 hs_pos hs_lt_one hkappa_pos hkappa_le_s
  exact ProductLikeIncidence.ProductReduction.product_like_incidence_sum_product_of_key_lemma
    s τ κ0 η_nc hs_pos hs_lt_one hτ_pos
    hkappa_pos hkappa_lt_s h2kappa_lt_tau hη_nc_pos h_ring
