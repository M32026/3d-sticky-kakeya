/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.SelectScale

/-!
# Proposition 5.1 interfaces for Section 6

This file fixes the boundary between the corrected Proposition 5.1 and the geometric work in
Section 6.  Both adapters keep the fine family as the inner family.  The local adapter uses the
ordinary fibrewise Frostman hypothesis.  The global adapter implements GWZ Remark 5.3 and uses
Frostman control only after thickening the fine bodies at the shortest outer scale.

The Section 6 geometry is responsible for constructing the factor family and the explicit scale,
discretisation, volume-ratio, and Frostman witnesses below.  In particular, these adapters do not
infer a three-dimensional shortest-scale bound from a two-dimensional flat disc.
-/

@[expose] public section

open Kakeya
open scoped ENNReal NNReal

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [DecidableEq κ]

/-- The geometric and scale data that Section 6 must supply before applying Proposition 5.1. -/
structure Section6FactoringAtScaleInput
    (F : FactorFamily E ι κ) (δ w₁ : NNReal) where
  /-- The inner discretisation scale is positive. -/
  hδ : 0 < δ
  /-- The fine inner bodies are discretised at scale `δ`. -/
  hdisc : F.InnerIsDiscretizedAtScale δ
  /-- An explicit dyadic bound for every outer/inner volume ratio. -/
  volumeRatio : OuterInnerVolumeRatio F
  /-- The selected common shortest outer scale is positive. -/
  hw₁ : 0 < w₁
  /-- The actual outer bodies, rather than representatives, have shortest scale comparable to
  `w₁`. -/
  hscale : F.OuterIsAtScale 2 w₁
  /-- Section 6 works in three dimensions. -/
  hdim : Module.finrank ℝ E = 3
  /-- Fine inner bodies have uniformly comparable shape. -/
  hshape : F.InnerHasSimilarShape 2

/-- The data needed when Section 6 supplies only an upper bound for the outer shortest scales.
The wrapper selects a common scale by the original fine-shading mass before applying the fixed
scale core. -/
structure Section6FactoringSelectScaleInput
    (F : FactorFamily E ι κ) (δ B : NNReal) where
  /-- The inner discretisation scale is positive. -/
  hδ : 0 < δ
  /-- The fine inner bodies are discretised at scale `δ`. -/
  hdisc : F.InnerIsDiscretizedAtScale δ
  /-- An explicit dyadic bound for every outer/inner volume ratio. -/
  volumeRatio : OuterInnerVolumeRatio F
  /-- The lower endpoint does not exceed the supplied upper scale. -/
  hδB : δ ≤ B
  /-- Every used actual outer body has shortest scale at most `B`. -/
  hupper : ∀ j ∈ F.innerSet.image F.parent, (F.outerBody j).scale ≤ B
  /-- The original fine shading has positive total mass. -/
  hmass : 0 < ∑ i ∈ F.innerSet, MeasureTheory.volume (F.innerBody i).shade
  /-- Section 6 works in three dimensions. -/
  hdim : Module.finrank ℝ E = 3
  /-- Fine inner bodies have uniformly comparable shape. -/
  hshape : F.InnerHasSimilarShape 2

/-- The Section 6 local adapter.  It is exactly the ordinary-Frostman canonical core. -/
theorem section6LocalFactorisation
    (F : FactorFamily E ι κ) {C : ENNReal} {δ w₁ : NNReal}
    (input : Section6FactoringAtScaleInput F δ w₁)
    (hFrostman : F.HasFrostmanFibers C) :
    FactoringAndMultPropCoreAtScale (C := C) F input.hδ input.hdisc
      input.volumeRatio w₁ input.hw₁ :=
  factoringAndMultPropCoreAtScale F input.hδ input.hdisc input.volumeRatio w₁ input.hw₁
    input.hscale input.hdim input.hshape hFrostman

/-- The Section 6 global adapter.  Its inner indices are still the fine indices; coarse tubes may
be used by the caller only to prove GWZ Remark 5.3's thickened-Frostman input. -/
theorem section6GlobalFactorisation
    (F : FactorFamily E ι κ) {C : ENNReal} {δ w₁ : NNReal}
    (input : Section6FactoringAtScaleInput F δ w₁)
    (hFrostman : F.HasThickenedFrostmanFibers C) :
    FactoringAndMultPropCoreAtScale (C := C) F input.hδ input.hdisc
      input.volumeRatio w₁ input.hw₁ :=
  factoringAndMultPropCoreAtScale_of_thickenedFrostman F input.hδ input.hdisc
    input.volumeRatio w₁ input.hw₁ input.hscale input.hdim input.hshape hFrostman

/-- The scale-selecting Section 6 local adapter. -/
theorem section6LocalFactorisationSelectScale
    (F : FactorFamily E ι κ) {C : ENNReal} {δ B : NNReal}
    (input : Section6FactoringSelectScaleInput F δ B)
    (hFrostman : F.HasFrostmanFibers C) :
    FactoringAndMultPropCoreSelectScaleResult (C := C) F input.hδ input.hdisc
      input.volumeRatio input.hδB input.hupper input.hmass :=
  factoringAndMultPropCoreSelectScale F input.hδ input.hdisc input.volumeRatio input.hδB
    input.hupper input.hmass input.hdim input.hshape hFrostman

/-- The scale-selecting Section 6 global adapter.  The returned core still has fine inner
indices; a coarse family may occur only in the proof of `hFrostman`. -/
theorem section6GlobalFactorisationSelectScale
    (F : FactorFamily E ι κ) {C : ENNReal} {δ B : NNReal}
    (input : Section6FactoringSelectScaleInput F δ B)
    (hFrostman : F.HasThickenedFrostmanFibers C) :
    FactoringAndMultPropCoreSelectScaleResult (C := C) F input.hδ input.hdisc
      input.volumeRatio input.hδB input.hupper input.hmass :=
  factoringAndMultPropCoreSelectScale_of_thickenedFrostman F input.hδ input.hdisc
    input.volumeRatio input.hδB input.hupper input.hmass input.hdim input.hshape hFrostman

end ShadedBody

end
