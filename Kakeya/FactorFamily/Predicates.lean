/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FactorFamily.Basic
public import Kakeya.Frostman
public import Kakeya.Thickness.Lemmas

/-! # Predicates on factor families

This file records geometric hypotheses on a factor family with shaded inner bodies. These
predicates package the repeated hypotheses of the factoring-and-multiplicity argument while
keeping all comparison constants explicit.
-/

@[expose] public section

open MeasureTheory Convexity Kakeya

namespace ShadedBody.FactorFamily

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*}

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- The inner family of a shaded factor family is discretized at scale `δ` in the sense of
`ConvexSpaceBody.IsDiscretizedAtScale`. No constraint is placed on the outer family.

Positivity of `δ` is deliberately a separate hypothesis: it is a property of the scale parameter,
not part of the geometric predicate. -/
structure InnerIsDiscretizedAtScale (F : ShadedBody.FactorFamily E ι κ) (δ : NNReal) : Prop
    extends ConvexSpaceBody.IsDiscretizedAtScale F.innerSet
      (fun i ↦ (F.innerBody i).toConvexSpaceBody) δ

namespace InnerIsDiscretizedAtScale

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- Every inner body of an inner-discretized factor family lies in the closed unit ball. -/
theorem inner_subset_unitBall {F : FactorFamily E ι κ} {δ : NNReal}
    (h : F.InnerIsDiscretizedAtScale δ) {i : ι} (hi : i ∈ F.innerSet) :
    (F.innerBody i).carrier ⊆ Metric.closedBall 0 1 :=
  h.subset_unitBall i hi

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- The parent of every inner body in an inner-discretized family has scale at least `δ`. -/
theorem le_outer_scale_parent {F : FactorFamily E ι κ} {δ : NNReal}
    (h : F.InnerIsDiscretizedAtScale δ) {i : ι} (hi : i ∈ F.innerSet) :
    (δ : ENNReal) ≤ Metric.ethickness.scale ℝ (F.outerBody (F.parent i)).carrier := by
  rw [Metric.ethickness.le_scale_iff]
  intro k
  exact (h.le_scale i hi).trans <|
    (Metric.ethickness.scale_le _ k.isLt).trans <|
      Metric.ethickness_monotone (F.inner_le_parent i hi) k

open Classical in
omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- Every outer body used as a parent in an inner-discretized family has scale at least `δ`. -/
theorem le_outer_scale_of_mem_image {F : FactorFamily E ι κ} {δ : NNReal}
    (h : F.InnerIsDiscretizedAtScale δ) {j : κ} (hj : j ∈ F.innerSet.image F.parent) :
    (δ : ENNReal) ≤ Metric.ethickness.scale ℝ (F.outerBody j).carrier := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  exact h.le_outer_scale_parent hi

omit [Nontrivial E] in
/-- Every inner body of an inner-discretized family has volume in
`[c(n) * δ ^ n, 2 ^ n]`, where `n = finrank ℝ E`. -/
theorem volume_innerBody_mem_Icc {F : FactorFamily E ι κ} {δ : NNReal}
    (h : F.InnerIsDiscretizedAtScale δ) {i : ι} (hi : i ∈ F.innerSet) :
    volume (F.innerBody i).carrier ∈ Set.Icc
      ((Metric.lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal) *
        (δ : ENNReal) ^ Module.finrank ℝ E)
      (2 ^ Module.finrank ℝ E) :=
  volume_mem_Icc_of_le_scale h.subset_unitBall h.le_scale hi

end InnerIsDiscretizedAtScale

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- A shaded factor family is discretized at scale `δ` if its inner family is discretized in the
sense of `ConvexSpaceBody.IsDiscretizedAtScale` and every outer body lies in the closed unit ball.

Positivity of `δ` is deliberately a separate hypothesis: it is a property of the scale parameter,
not part of the geometric predicate. -/
structure IsDiscretizedAtScale (F : ShadedBody.FactorFamily E ι κ) (δ : NNReal) : Prop
    extends ConvexSpaceBody.IsDiscretizedAtScale F.innerSet
      (fun i ↦ (F.innerBody i).toConvexSpaceBody) δ where
  /-- Every outer body of the family lies in the closed unit ball. -/
  outer_subset_unitBall :
    ∀ j ∈ F.outerSet, (F.outerBody j).carrier ⊆ Metric.closedBall 0 1

namespace IsDiscretizedAtScale

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- Every inner body of a discretized factor family lies in the closed unit ball. -/
theorem inner_subset_unitBall {F : FactorFamily E ι κ} {δ : NNReal}
    (h : F.IsDiscretizedAtScale δ) {i : ι} (hi : i ∈ F.innerSet) :
    (F.innerBody i).carrier ⊆ Metric.closedBall 0 1 :=
  h.subset_unitBall i hi

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- The parent of every inner body in a discretized factor family has scale at least `δ`. -/
theorem le_outer_scale_parent {F : FactorFamily E ι κ} {δ : NNReal}
    (h : F.IsDiscretizedAtScale δ) {i : ι} (hi : i ∈ F.innerSet) :
    (δ : ENNReal) ≤ Metric.ethickness.scale ℝ (F.outerBody (F.parent i)).carrier := by
  rw [Metric.ethickness.le_scale_iff]
  intro k
  exact (h.le_scale i hi).trans <|
    (Metric.ethickness.scale_le _ k.isLt).trans <|
      Metric.ethickness_monotone (F.inner_le_parent i hi) k

open Classical in
omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- Every outer body used as a parent in a discretized factor family has scale at least `δ`.

The restriction to `F.innerSet.image F.parent` is necessary because `FactorFamily` permits unused
indices in `outerSet`. -/
theorem le_outer_scale_of_mem_image {F : FactorFamily E ι κ} {δ : NNReal}
    (h : F.IsDiscretizedAtScale δ) {j : κ} (hj : j ∈ F.innerSet.image F.parent) :
    (δ : ENNReal) ≤ Metric.ethickness.scale ℝ (F.outerBody j).carrier := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  exact h.le_outer_scale_parent hi

omit [Nontrivial E] in
/-- Every inner body of a discretized factor family has volume in
`[c(n) * δ ^ n, 2 ^ n]`, where `n = finrank ℝ E` and `c(n) = 1 / n!`. -/
theorem volume_innerBody_mem_Icc {F : FactorFamily E ι κ} {δ : NNReal}
    (h : F.IsDiscretizedAtScale δ) {i : ι} (hi : i ∈ F.innerSet) :
    volume (F.innerBody i).carrier ∈ Set.Icc
      ((Metric.lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal) *
        (δ : ENNReal) ^ Module.finrank ℝ E)
      (2 ^ Module.finrank ℝ E) :=
  volume_mem_Icc_of_le_scale h.subset_unitBall h.le_scale hi

omit [Nontrivial E] in
/-- Every outer body of a discretized factor family has volume at most `2 ^ n`, where
`n = finrank ℝ E`. -/
theorem volume_outerBody_le_two_pow_finrank {F : FactorFamily E ι κ} {δ : NNReal}
    (h : F.IsDiscretizedAtScale δ) {j : κ} (hj : j ∈ F.outerSet) :
    volume (F.outerBody j).carrier ≤ 2 ^ Module.finrank ℝ E :=
  volume_le_of_subset_closedBall h.outer_subset_unitBall hj

open Classical in
omit [Nontrivial E] in
/-- Every outer body used as a parent in a discretized factor family has volume in
`[c(n) * δ ^ n, 2 ^ n]`, where `n = finrank ℝ E` and `c(n) = 1 / n!`.

The restriction to `F.innerSet.image F.parent` is necessary because `FactorFamily` permits unused
indices in `outerSet`. -/
theorem volume_outerBody_mem_Icc_of_mem_image {F : FactorFamily E ι κ} {δ : NNReal}
    (h : F.IsDiscretizedAtScale δ) {j : κ} (hj : j ∈ F.innerSet.image F.parent) :
    volume (F.outerBody j).carrier ∈ Set.Icc
      ((Metric.lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal) *
        (δ : ENNReal) ^ Module.finrank ℝ E)
      (2 ^ Module.finrank ℝ E) := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  exact ⟨(h.volume_innerBody_mem_Icc hi).1.trans (measure_mono (F.inner_le_parent i hi)),
    h.volume_outerBody_le_two_pow_finrank (F.parent_mem i hi)⟩

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- Forget the outer localization of a discretized factor family. -/
theorem toInner {F : FactorFamily E ι κ} {δ : NNReal} (h : F.IsDiscretizedAtScale δ) :
    F.InnerIsDiscretizedAtScale δ where
  subset_unitBall := h.subset_unitBall
  le_scale := h.le_scale

end IsDiscretizedAtScale

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
instance {F : FactorFamily E ι κ} {δ : NNReal} :
    Coe (F.IsDiscretizedAtScale δ) (F.InnerIsDiscretizedAtScale δ) :=
  ⟨IsDiscretizedAtScale.toInner⟩

/-- The inner bodies of `F` have pairwise comparable thickness sequences, with multiplicative
comparison constant `K`. -/
def InnerHasSimilarShape (F : ShadedBody.FactorFamily E ι κ) (K : NNReal) : Prop :=
  ∀ i ∈ F.innerSet, ∀ i' ∈ F.innerSet,
    Metric.thickness ℝ (F.innerBody i).carrier ≤
      (K : ℝ) • Metric.thickness ℝ (F.innerBody i').carrier

/-- Every fiber of `F` is `C`-Frostman in its chosen outer body. -/
noncomputable def HasFrostmanFibers (F : ShadedBody.FactorFamily E ι κ) (C : ENNReal) : Prop :=
  ∀ j ∈ F.outerSet,
    ConvexSpaceBody.IsFrostmanIn (F.fiber j)
      (fun i ↦ (F.innerBody i).toConvexSpaceBody) (F.outerBody j) C

/-- GWZ Remark 5.3's weakened fibrewise Frostman hypothesis, in division-free form.

For an outer body `W`, the Córdoba argument uses the inner carriers thickened by twice the
shortest scale of `W`.  These thickened carriers need not remain contained in `W`, so the usual
`IsFrostmanIn` predicate would filter some of them out when computing the density in `W`.  The
division-free inequality below is the non-vacuous condition of “the thickened family is
`C`-Frostman in `W`”: its maximal density is normalized by the total thickened mass and `|W|`.
-/
noncomputable def HasThickenedFrostmanFibers
    (F : ShadedBody.FactorFamily E ι κ) (C : ENNReal) : Prop :=
  ∀ j ∈ F.outerSet,
    Kakeya.maxDensity (F.fiber j) (fun i ↦
        (F.innerBody i).toConvexSpaceBody.cthickening (2 * (F.outerBody j).scale)) *
        volume (F.outerBody j).carrier ≤
      C * ∑ i ∈ F.fiber j,
        volume ((F.innerBody i).toConvexSpaceBody.cthickening
          (2 * (F.outerBody j).scale)).carrier

/-- The shortest thickness of every outer body of `F` is comparable to `w₁`, with
multiplicative comparison constant `K`. -/
def OuterIsAtScale (F : ShadedBody.FactorFamily E ι κ) (K w₁ : NNReal) : Prop :=
  ∀ j ∈ F.outerSet,
    Metric.thickness ℝ (F.outerBody j).carrier (Module.finrank ℝ E - 1) ≤ (K : ℝ) * w₁ ∧
    (w₁ : ℝ) ≤
      (K : ℝ) * Metric.thickness ℝ (F.outerBody j).carrier (Module.finrank ℝ E - 1)

end ShadedBody.FactorFamily
