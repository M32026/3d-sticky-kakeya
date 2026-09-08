/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.RhoTubesRich
public import Kakeya.Factoring.RhoTubesUndilated

@[expose] public section

open MeasureTheory Convexity Kakeya
open scoped NNReal ENNReal

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*}

open Classical in
/-- **GWZ Lemma 5.11.** The two-scale tube factoring estimate for an *undilated* outer family of
`ρ`-tubes: the `c = 1` case of `ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate`.

The outer fullness clause is the fullness-to-fullness one,
`C⁻¹ · λ(𝕋, Y) ≤ λ(𝕋_ρ', Y_{𝕋_ρ}')`. It is not stated with the inner density parameter `lam` on
the left: `ShadedBody.fullness_le_one` is unconditional, so that form would entail `C⁻¹ · lam ≤ 1`
for every admissible configuration, which no hypothesis here supplies. See
`ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam` for the density-parameter form
and the extra hypotheses it costs.

Neither essential distinctness of the outer bodies nor a per-tube density hypothesis on the inner
shading is assumed; both were inert for every conclusion below. -/
theorem shadingMultiplicityEstimateForRhoTubesUndilatedRich
    {δ ρ : ℝ≥0} (hδ : 0 < δ) (hρ : ρ ∈ Set.Icc δ 1)
    (F : FactorFamily E ι κ)
    (T : ι → ShadedTube δ E) (Tρ : κ → Tube ρ E)
    (hinner : ∀ i ∈ F.innerSet, F.innerBody i = (T i).toShadedBody)
    (houter : ∀ j ∈ F.outerSet, F.outerBody j = (Tρ j).toConvexSpaceBody)
    (hball : ∀ i ∈ F.innerSet, (F.innerBody i).carrier ⊆ Metric.closedBall 0 1) :
    ∃ G : ShadedFactorFamily E ι κ,
      G.outerSet ⊆ F.outerSet ∧
      G.innerSet = {i ∈ F.innerSet | F.parent i ∈ G.outerSet} ∧
      G.parent = F.parent ∧
      (∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody = F.outerBody j) ∧
      (∀ i ∈ F.innerSet,
        (G.innerBody i).toConvexSpaceBody = (F.innerBody i).toConvexSpaceBody) ∧
      (∀ j ∈ G.outerSet, (G.fiber j).Nonempty) ∧
      (0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade → G.outerSet.Nonempty) ∧
      (shadingMultiplicityEstimateForRhoTubesDilate.C
            (Module.finrank ℝ E) F.innerSet.card δ 1)⁻¹ *
          fullness F.innerSet F.innerBody
        ≤ fullness G.outerSet G.outerBody ∧
      IsCRefinement G.innerSet G.innerBody F.innerSet F.innerBody
        (shadingMultiplicityEstimateForRhoTubesDilate.C
          (Module.finrank ℝ E) F.innerSet.card δ 1)⁻¹ ∧
      (∀ j ∈ G.outerSet,
        multiplicity F.innerSet F.innerBody
          ≤ (shadingMultiplicityEstimateForRhoTubesDilate.C
                (Module.finrank ℝ E) F.innerSet.card δ 1 : ENNReal)
            * multiplicity G.outerSet G.outerBody
            * multiplicity (G.fiber j) G.innerBody) ∧
      (∀ i ∈ G.innerSet,
        (G.innerBody i).shade ⊆ (G.outerBody (F.parent i)).shade) ∧
      (∃ u : Finset ι,
        u ⊆ G.innerSet ∧
        IsCRefinement u G.innerBody F.innerSet F.innerBody
          (shadingMultiplicityEstimateForRhoTubesDilate.C
            (Module.finrank ℝ E) F.innerSet.card δ 1)⁻¹ ∧
        (∀ j ∈ G.outerSet, ({i ∈ u | G.parent i = j} : Finset ι).Nonempty) ∧
        (∀ j ∈ G.outerSet, ∀ j' ∈ G.outerSet,
          (({i ∈ u | G.parent i = j} : Finset ι).card : ENNReal) ≤
            2 * (({i ∈ u | G.parent i = j'} : Finset ι).card : ENNReal)) ∧
        (∀ j ∈ G.outerSet,
          multiplicity (G.fiber j) G.innerBody =
            multiplicity {i ∈ u | G.parent i = j} G.innerBody)) ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (shadingMultiplicityEstimateForRhoTubesDilate.C
              (Module.finrank ℝ E) F.innerSet.card δ 1 : ENNReal)⁻¹
          * volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade)
          * (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ Metric.ball x (ρ : ℝ))
              / volume (Metric.ball x (ρ : ℝ)))
          ≤ volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  exact shadingMultiplicityEstimateForRhoTubesDilateRich (c := 1) hδ hρ le_rfl F T Tρ hinner
    (fun j hj => by
      rw [houter j hj]
      simp [Kakeya.Tube.dilate_one])
    hball

end ShadedBody
