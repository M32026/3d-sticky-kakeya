/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.RhoTubes

/-! # Two-scale factoring for undilated `ρ`-tubes (GWZ Lemma 5.11)

`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate` in `Kakeya/Factoring/RhoTubes.lean`
proves GWZ Lemma 5.11 for an outer family consisting of the `c`-*dilates* of a family of
`ρ`-tubes. This file specialises it to `c = 1`, where the dilate is the tube itself, and records
the density-parameter form obtained from the fullness form.

The specialisation cannot live in `Kakeya/Multiplicity.lean`, where the undilated statement was
originally placed: that file is strictly upstream of `Kakeya/Factoring/RhoTubes.lean` through
`Kakeya.Factoring.Pipeline` and `Kakeya.Factoring.Step2`, so citing the dilate theorem there is an
import cycle.

## Main statements

* `Kakeya.Tube.dilate_one`: the `1`-dilate of a tube is the tube;
* `ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated`: GWZ Lemma 5.11 for an undilated
  outer family, in fullness-to-fullness form, at the loss constant
  `ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C _ _ δ 1`;
* `ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam`: the same estimate with the
  outer fullness bounded below by the inner density parameter `lam`, at the additional cost of
  the two-sided density comparison constant `Cd` and the nondegeneracy hypothesis
  `∑ i ∈ F.innerSet, volume (F.innerBody i).carrier ≠ 0`.

## The `lam` form needs the nondegeneracy hypothesis

Without it the statement is false for every constant: with `F.innerSet = F.outerSet = ∅` the
containment `G.outerSet ⊆ F.outerSet` forces `fullness G.outerSet G.outerBody = 0`, while the
density hypotheses are vacuous and leave `lam` free.
-/

@[expose] public section

open MeasureTheory Convexity Kakeya
open scoped NNReal ENNReal

namespace Kakeya.Tube

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The `1`-dilate of a tube is the tube.** The affine homothety of ratio `1` centred anywhere
is the identity. -/
lemma dilate_one {δ : ℝ≥0} (T : Tube δ E) :
    Kakeya.Tube.dilate T (1 : ℝ) = T.toConvexSpaceBody := by
  apply ConvexSpaceBody.ext
  change (Kakeya.Tube.dilate T (1 : ℝ)).carrier = T.carrier
  rw [Kakeya.Tube.dilate_carrier]
  simp

end Kakeya.Tube

namespace ShadedBody

section RhoTubesUndilated

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
theorem shadingMultiplicityEstimateForRhoTubesUndilated
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
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (shadingMultiplicityEstimateForRhoTubesDilate.C
              (Module.finrank ℝ E) F.innerSet.card δ 1 : ENNReal)⁻¹
          * volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade)
          * (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ Metric.ball x (ρ : ℝ))
              / volume (Metric.ball x (ρ : ℝ)))
          ≤ volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade))
      -- GWZ Definition 5.7, exposed: the outer shading contains the `2ρ`-neighbourhood, inside the
      -- outer carrier, of every selected inner shade of its fibre
      ∧ (∀ j ∈ G.outerSet, ∀ i ∈ G.innerSet, G.parent i = j →
          (G.outerBody j).carrier ∩ Metric.cthickening (2 * (ρ : ℝ)) (G.innerBody i).shade
            ⊆ (G.outerBody j).shade) := by
  exact shadingMultiplicityEstimateForRhoTubesDilate (c := 1) hδ hρ le_rfl F T Tρ hinner
    (fun j hj => by
      rw [houter j hj]
      simp [Kakeya.Tube.dilate_one])
    hball

open Classical in
/-- **GWZ Lemma 5.11, density-parameter form.** As
`ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated`, but with the outer fullness bounded
below by the density parameter `lam` of the inner shading.

The conversion is `ShadedBody.le_fullness_of_le_fullness_of_forall_density`, and it is priced: the
loss constant acquires the factor `Cd` from the density hypothesis, and the nondegeneracy
condition `hs0` is carried explicitly. Neither is removable — on the empty family the density
hypotheses are vacuous while the outer fullness is `0`, refuting the clause for every constant.
Only the lower density bound is used. -/
theorem shadingMultiplicityEstimateForRhoTubesUndilated_lam
    {δ ρ Cd lam : ℝ≥0} (hδ : 0 < δ) (hρ : ρ ∈ Set.Icc δ 1) (hCd : Cd ≠ 0)
    (F : FactorFamily E ι κ)
    (T : ι → ShadedTube δ E) (Tρ : κ → Tube ρ E)
    (hinner : ∀ i ∈ F.innerSet, F.innerBody i = (T i).toShadedBody)
    (houter : ∀ j ∈ F.outerSet, F.outerBody j = (Tρ j).toConvexSpaceBody)
    (hball : ∀ i ∈ F.innerSet, (F.innerBody i).carrier ⊆ Metric.closedBall 0 1)
    (hs0 : ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier ≠ 0)
    (hlam_lb : ∀ i ∈ F.innerSet,
      (Cd : ENNReal)⁻¹ * ((lam : ENNReal) * volume (F.innerBody i).carrier)
        ≤ volume (F.innerBody i).shade) :
    ∃ G : ShadedFactorFamily E ι κ,
      G.outerSet ⊆ F.outerSet ∧
      G.innerSet = {i ∈ F.innerSet | F.parent i ∈ G.outerSet} ∧
      G.parent = F.parent ∧
      (∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody = F.outerBody j) ∧
      (∀ i ∈ F.innerSet,
        (G.innerBody i).toConvexSpaceBody = (F.innerBody i).toConvexSpaceBody) ∧
      (0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade → G.outerSet.Nonempty) ∧
      (Cd * shadingMultiplicityEstimateForRhoTubesDilate.C
            (Module.finrank ℝ E) F.innerSet.card δ 1)⁻¹ * lam
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
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (shadingMultiplicityEstimateForRhoTubesDilate.C
              (Module.finrank ℝ E) F.innerSet.card δ 1 : ENNReal)⁻¹
          * volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade)
          * (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ Metric.ball x (ρ : ℝ))
              / volume (Metric.ball x (ρ : ℝ)))
          ≤ volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade))
      -- GWZ Definition 5.7, exposed: the outer shading contains the `2ρ`-neighbourhood, inside the
      -- outer carrier, of every selected inner shade of its fibre
      ∧ (∀ j ∈ G.outerSet, ∀ i ∈ G.innerSet, G.parent i = j →
          (G.outerBody j).carrier ∩ Metric.cthickening (2 * (ρ : ℝ)) (G.innerBody i).shade
            ⊆ (G.outerBody j).shade) := by
  obtain ⟨G, h1, h2, h3, h4, h5, h6, hfull, h8, h9, h10, h11, h12⟩ :=
    shadingMultiplicityEstimateForRhoTubesUndilated hδ hρ F T Tρ hinner houter hball
  exact ⟨G, h1, h2, h3, h4, h5, h6,
    le_fullness_of_le_fullness_of_forall_density hCd hs0 hlam_lb hfull,
    h8, h9, h10, h11, h12⟩

end RhoTubesUndilated

end ShadedBody
