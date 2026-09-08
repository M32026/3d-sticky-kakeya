/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShape
public import Kakeya.DimensionThree.MainLemma2.ShadedDividingScales

/-!
# `SRC-A`: the lower fullness, recovered on `(𝕊'', Z'')` — the family FULLDROP dispersed it off

 §SRC-A: source l.4482–4484 requires the count floor, the **lower fullness** and the
two-level density statements to hold for the **same** family `(𝕊'', Z'')`.  the estimate `FULLDROP` removed
the fullness clause from `Kakeya.ML2Core.RefinedFloorHypothesis`, on the recorded ground that the
rate "lives in the trial's hereditary rows" — naming
`Kakeya.ML2Core.fullness_refinement_of_denseShading`, which concludes fullness of `S'` **with
respect to `Z`**, the *ambient* shading.  The deleted clause was with respect to **`W`**, the
*refined* one, and `Kakeya.ShadedBody.fullness_mono_shade` bounds
`fullness S' W ≤ fullness S' Z` — the **wrong side**.  (The tree states the principle against itself
at `Plank/EDWeightedExtraction.lean:16`: *"fullness is not monotone under restriction"*.)

**The repair is available, and it does not touch `FULLDROP`.**  Clause 5 of
`Kakeya.ML2Core.IsShadedRefinementOf` is the source's own mass retention (l.4100–4101),
`∑_{𝕊'}|Z| ≤ Λ ∑_{𝕊''}|Z''|`, and it *does* bound the refined fullness from below, at the cost of
one `Λ`:

> `Kakeya.ML2Core.IsShadedRefinementOf.fullness'_le` —
> `fullness' S Z ≤ Λ * fullness' S' W`.

The proof is three moves and no side conditions: the refinement's tubes are the ambient ones, so the
denominators satisfy `∑_{S'} |W_i| = ∑_{S'} |Z_i| ≤ ∑_S |Z_i|`; shrinking a denominator raises the
quotient; and clause 5 raises the numerator.

## The family/shading column, stated for every row of this file

| row | family | shading |
|---|---|---|
| `IsShadedRefinementOf` clause 5 (source l.4100–4101) | `S` numerator, `S'` denominator | `Z` on `S`, `W` on `S'` |
| `fullness' S Z` | `S` = `𝕊'` | `Z` — the **ambient** shading |
| `fullness' S' W` | `S'` = `𝕊''` | `W` = `Z''` — the **refined** shading |
| `fullness_refinement_of_denseShading` (the FULLDROP ground) | `S'` = `𝕊''` | **`Z`**, not `W` — this is the defect |
| `IsShadedRefinementOf.le_mul_fullness'_of_trial` (below) | `S'` = `𝕊''` | **`W`** = `Z''` — the deleted clause, on the right family *and* the right shading |

`Kakeya.ML2Core.IsShadedRefinementOf.le_mul_fullness'_of_trial` delivers
`δ^{ηin}/2 ≤ Λ · fullness' S' W` from the trial's own hereditary rows
(`ML2Shaded.HasDenseShading lam S Z` and `δ^{ηin}/2 ≤ lam`) — i.e. `FULLDROP`'s recorded ground is
**correct after all**, but only through this lemma and only up to the factor `Λ`, and neither was
on record.  What was missing is not the rate but the transport of the rate **across the shading**.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section Fullness

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}

/-- **`SRC-A`'s repair.**  The refined family's fullness, **with respect to the refined shading
`W`**, is at least `Λ⁻¹` times the ambient family's fullness with respect to `Z`.

Only clause 3 (same tubes) and clause 5 (the source's mass retention, l.4100–4101) of
`Kakeya.ML2Core.IsShadedRefinementOf` are used.  There are no side conditions: `ENNReal` division is
antitone in the denominator unconditionally. -/
theorem IsShadedRefinementOf.fullness'_le {Λ : ℝ≥0∞} {S S' : Finset ι}
    {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (href : IsShadedRefinementOf 𝒰 Λ S Z S' W) :
    ShadedBody.fullness' S (fun i => (Z i).toShadedBody)
      ≤ Λ * ShadedBody.fullness' S' (fun i => (W i).toShadedBody) := by
  have hcar : ∀ i, (W i).carrier = (Z i).carrier :=
    fun i => congrArg (fun t : Tube δ (EuclideanSpace ℝ (Fin 3)) => t.carrier) (href.2.2.1 i)
  have hden : ∑ i ∈ S', volume ((W i).toShadedBody).carrier
      ≤ ∑ i ∈ S, volume ((Z i).toShadedBody).carrier := by
    have h1 : ∑ i ∈ S', volume ((W i).toShadedBody).carrier
        = ∑ i ∈ S', volume ((Z i).toShadedBody).carrier :=
      Finset.sum_congr rfl fun i _ => by rw [hcar i]
    rw [h1]
    exact Finset.sum_le_sum_of_subset href.subset
  calc ShadedBody.fullness' S (fun i => (Z i).toShadedBody)
      = (∑ i ∈ S, volume (Z i).shade) / (∑ i ∈ S, volume ((Z i).toShadedBody).carrier) := rfl
    _ ≤ (∑ i ∈ S, volume (Z i).shade)
          / (∑ i ∈ S', volume ((W i).toShadedBody).carrier) :=
        ENNReal.div_le_div_left hden _
    _ ≤ (Λ * ∑ i ∈ S', volume (W i).shade)
          / (∑ i ∈ S', volume ((W i).toShadedBody).carrier) :=
        ENNReal.div_le_div_right href.retention _
    _ = Λ * ShadedBody.fullness' S' (fun i => (W i).toShadedBody) := mul_div_assoc _ _ _

/-- The dense-shading rate, transported across the refinement **onto the refined shading**. -/
theorem IsShadedRefinementOf.le_mul_fullness'_of_denseShading {Λ : ℝ≥0∞} {S S' : Finset ι}
    {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (href : IsShadedRefinementOf 𝒰 Λ S Z S' W) (hδ : 0 < δ) (hne : S.Nonempty) {lam : NNReal}
    (hdense : ML2Shaded.HasDenseShading lam S (fun i => (Z i).toShadedBody)) :
    (lam : ℝ≥0∞) ≤ Λ * ShadedBody.fullness' S' (fun i => (W i).toShadedBody) :=
  (hdense.le_fullness_tube hδ hne).trans href.fullness'_le

/-- **The clause `FULLDROP` deleted, recovered on `(𝕊'', Z'')`.**  From the trial's own hereditary
rows — `ML2Shaded.HasDenseShading lam S Z` and `δ^{ηin}/2 ≤ lam` — the refined family's fullness
**with respect to the refined shading `W`** is at least `Λ⁻¹ δ^{ηin}/2`.

This is what `the estimate FULLDROP`'s recorded ground needed and did not have: the rate does live in the
trial's hereditary rows, but transporting it from `Z` to `W` is this lemma and costs one `Λ`.  The
`Λ` is the honest price and must be carried by whoever re-delivers the clause to `hfac`. -/
theorem IsShadedRefinementOf.le_mul_fullness'_of_trial {Λ : ℝ≥0∞} {S S' : Finset ι}
    {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (href : IsShadedRefinementOf 𝒰 Λ S Z S' W) (hδ : 0 < δ) (hne : S.Nonempty) {lam : NNReal}
    (hdense : ML2Shaded.HasDenseShading lam S (fun i => (Z i).toShadedBody))
    {ηin : ℝ} (hlam : (δ : NNReal) ^ ηin / 2 ≤ lam) :
    (((δ : NNReal) ^ ηin / 2 : NNReal) : ℝ≥0∞)
      ≤ Λ * ShadedBody.fullness' S' (fun i => (W i).toShadedBody) :=
  le_trans (by exact_mod_cast hlam) (href.le_mul_fullness'_of_denseShading hδ hne hdense)

end Fullness

end Kakeya.ML2Core

end
