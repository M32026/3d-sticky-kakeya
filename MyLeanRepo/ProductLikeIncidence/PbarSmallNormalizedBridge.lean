module

/-
# Pbar Small Normalized Bridge

Derives the smallness bound for the normalized (translated) Pbar_param'
from the original Pbar_param smallness bound, using the 2D translation
covering bound (factor 4).

## Proof

1. `dyadic_cover_translate2d_le_four` gives `Nplane δ Pbar' ≤ 4 * Nplane δ Pbar`
2. Original `hPbar_small` gives `Nplane δ Pbar < δ^(-(2*s+η))`
3. Therefore `Nplane δ Pbar' < 4 * δ^(-(2*s+η))`

## Whiteprint node
`pbar_small_normalized_bridge`
-/

public import MyLeanRepo.ProductLikeIncidence.TranslationBounds
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set ENNReal Bornology

namespace ProductLikeIncidence.ProductReduction

/-- **Pbar small normalized bridge**: Given the original Pbar small bound and
a translation vector, conclude the normalized Pbar' is small with factor 4. -/
lemma pbar_small_normalized_bridge
    {δ s η : ℝ}
    (hδ_pos : 0 < δ)
    {Pbar Pbar' : Set (EuclideanSpace ℝ (Fin 2))}
    (v : EuclideanSpace ℝ (Fin 2))
    (hPbar'_eq : Pbar' = (fun p : EuclideanSpace ℝ (Fin 2) => p + v) '' Pbar)
    (hPbar_bdd : IsBounded Pbar)
    (hPbar_small : ENat.toENNReal (dyadicCoveringNumber δ Pbar) <
        ENNReal.ofReal (δ ^ (-(2 * s + η)))) :
    ENat.toENNReal (dyadicCoveringNumber δ Pbar') <
      ENNReal.ofReal (4 * δ ^ (-(2 * s + η))) := by
  have h_trans_nat : dyadicCoveringNumber δ Pbar' ≤ 4 * dyadicCoveringNumber δ Pbar := by
    rw [hPbar'_eq]
    exact dyadic_cover_translate2d_le_four hδ_pos v hPbar_bdd
  have h_trans : ENat.toENNReal (dyadicCoveringNumber δ Pbar') ≤
      (4 : ENNReal) * ENat.toENNReal (dyadicCoveringNumber δ Pbar) := by
    have h1 : ENat.toENNReal (dyadicCoveringNumber δ Pbar') ≤
        ENat.toENNReal (4 * dyadicCoveringNumber δ Pbar) :=
      ENat.toENNReal_mono h_trans_nat
    have h2 : ENat.toENNReal (4 * dyadicCoveringNumber δ Pbar) =
        (4 : ENNReal) * ENat.toENNReal (dyadicCoveringNumber δ Pbar) := by
      simp
    rw [h2] at h1
    exact h1
  have h_pos : 0 ≤ δ ^ (-(2 * s + η)) := by positivity
  have h_strict : (4 : ENNReal) * ENat.toENNReal (dyadicCoveringNumber δ Pbar) <
      (4 : ENNReal) * ENNReal.ofReal (δ ^ (-(2 * s + η))) := by
    have h4_ne_zero : (4 : ENNReal) ≠ 0 := by norm_num
    have h4_ne_top : (4 : ENNReal) ≠ ⊤ := by norm_num
    have h : ENat.toENNReal (dyadicCoveringNumber δ Pbar) * (4 : ENNReal) <
        ENNReal.ofReal (δ ^ (-(2 * s + η))) * (4 : ENNReal) :=
      ENNReal.mul_lt_mul_left h4_ne_zero h4_ne_top hPbar_small
    simpa [mul_comm] using h
  have h4 : (4 : ENNReal) * ENNReal.ofReal (δ ^ (-(2 * s + η))) =
      ENNReal.ofReal (4 * δ ^ (-(2 * s + η))) := by
    have h5 : (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) := by simp
    rw [h5]
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4)]
  calc ENat.toENNReal (dyadicCoveringNumber δ Pbar')
    ≤ (4 : ENNReal) * ENat.toENNReal (dyadicCoveringNumber δ Pbar) := h_trans
  _ < (4 : ENNReal) * ENNReal.ofReal (δ ^ (-(2 * s + η))) := h_strict
  _ = ENNReal.ofReal (4 * δ ^ (-(2 * s + η))) := h4

end ProductLikeIncidence.ProductReduction
