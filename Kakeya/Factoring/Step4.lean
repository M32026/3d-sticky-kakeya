/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.Step3

/-! # Step 4 of the factoring construction

This file formalizes Step 4 of the construction in GWZ Proposition 5.1. Step 4 is purely
definitional: it shades the outer bodies of the Step 3 family
`G₃ = step3FactorFamily F hu t' Ω hΩ k` by the shading `inducedShading` induced blockwise by the
Step 3 inner bodies, and thereby upgrades `G₃` from a `ShadedBody.FactorFamily` to a
`ShadedBody.ShadedFactorFamily`.

Writing `W j = F.outerBody j`, `r j = (W j).scale` and `N_r` for the closed `r`-thickening, the
outer shaded body over `j` has carrier the enlargement `N_{r j} (W j)` and shade
`N_{2 * r j} (U (𝒱'_j, Y₀')) ∩ N_{r j} (W j)`, where `𝒱'_j` is the Step 3 fiber over `j`. The
enlarged carrier — rather than `W j` itself — is forced: the `shade_subset` field of a `ShadedBody`
fails for the carrier `W j`, and the enlargement is what `Kakeya/Shading.lean` and the density
lower bound for induced shadings use.

Step 4 neither discards an inner body nor shrinks an inner shade, so it retains the Step 3 shading
mass verbatim and introduces no new constant.

## Main definitions and statements

* `ShadedBody.step4OuterBody`: the induced outer shading of Step 4;
* `ShadedBody.shade_step4OuterBody_eq`: over a surviving block, its shade is the enlargement
  intersected with the `2 * r j`-thickening of the union of the Step 3 shades over the fiber of `F`;
* `ShadedBody.iUnionShade_fiber_subset_shade_step4OuterBody`: the blockwise shading containment
  `U (𝒱'_j, Y₀') ⊆ Y_{𝒲',0} j`;
* `ShadedBody.iUnionShade_subset_iUnionShade_step4Outer`: its family-level counterpart
  `U (𝒱', Y₀') ⊆ U (𝒲', Y_{𝒲',0})`;
* `ShadedBody.step4ShadedFactorFamily`: the shaded factor family produced by Step 4.
-/

@[expose] public section

open MeasureTheory Convexity Kakeya

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [DecidableEq κ]

/-! ### The induced outer shading of Step 4 -/

/-- The induced outer shading of Step 4: the shading induced on the enlargement of the outer body
`F.outerBody j` by the Step 3 inner bodies lying over `j`.

Its carrier is `N_{r j} (F.outerBody j)` with `r j = (F.outerBody j).scale`, and its shade is
`N_{2 * r j} (U (𝒱'_j, Y₀')) ∩ N_{r j} (F.outerBody j)`, the union running over the Step 3 fiber
`{i ∈ u | F.parent i ∈ t' ∧ F.parent i = j}` and over the Step 3 shades `Y₀'`.

No membership hypothesis on `j` is needed: for `j ∉ t'` the Step 3 fiber is empty, so the shade is
empty, while the carrier is still the genuine convex body `N_{r j} (F.outerBody j)`. -/
noncomputable def step4OuterBody (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω)
    (k : ℕ) (j : κ) : ShadedBody E :=
  inducedShading ((step3FactorFamily F hu t' Ω hΩ k).fiber j)
    (step3FactorFamily F hu t' Ω hΩ k).innerBody
    ((step3FactorFamily F hu t' Ω hΩ k).outerBody j)

/-- The carrier of the Step 4 outer shaded body is the enlargement `N_{r j} (F.outerBody j)`. -/
theorem toConvexSpaceBody_step4OuterBody (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω)
    (k : ℕ) (j : κ) :
    (step4OuterBody F hu t' Ω hΩ k j).toConvexSpaceBody =
      (F.outerBody j).cthickening (F.outerBody j).scale := rfl

/-- The shade of the Step 4 outer shaded body. -/
theorem shade_step4OuterBody (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω)
    (k : ℕ) (j : κ) :
    (step4OuterBody F hu t' Ω hΩ k j).shade =
      Metric.cthickening (2 * (F.outerBody j).scale)
          (iUnionShade ((step3FactorFamily F hu t' Ω hΩ k).fiber j)
            (step3FactorFamily F hu t' Ω hΩ k).innerBody) ∩
        Metric.cthickening (F.outerBody j).scale (F.outerBody j).carrier := rfl

/-- **Compatibility of the Step 4 shading with the inner shading** (corrected form of GWZ
Remark 5.4). Over a surviving block `j ∈ t'`, the Step 4 shade is the enlargement
`N_{r j} (F.outerBody j)` intersected with the `2 * r j`-thickening of the union of the Step 3
shades over the fiber of `F` inside `u`.

The hypothesis `j ∈ t'` is not decorative: for `j ∉ t'` the Step 3 fiber over `j` is empty while
`{i ∈ u | F.parent i = j}` need not be. -/
theorem shade_step4OuterBody_eq (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω)
    (k : ℕ) {j : κ} (hj : j ∈ t') :
    (step4OuterBody F hu t' Ω hΩ k j).shade =
      Metric.cthickening (F.outerBody j).scale (F.outerBody j).carrier ∩
        Metric.cthickening (2 * (F.outerBody j).scale)
          (iUnionShade {i ∈ u | F.parent i = j} (step3InnerBody F u t' Ω hΩ k)) := by
  rw [shade_step4OuterBody, step3FactorFamily_fiber F hu t' Ω hΩ k hj, step3FactorFamily_innerBody]
  exact Set.inter_comm _ _

/-- **Shading containment for the Step 4 family**: the union of the Step 3 shades over the fiber
of `j` is contained in the Step 4 outer shade over `j`.

No hypothesis on `j` is required: for `j ∉ t'` the Step 3 fiber is empty and the statement holds
vacuously. -/
theorem iUnionShade_fiber_subset_shade_step4OuterBody (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω)
    (k : ℕ) (j : κ) :
    iUnionShade ((step3FactorFamily F hu t' Ω hΩ k).fiber j)
        (step3FactorFamily F hu t' Ω hΩ k).innerBody ⊆
      (step4OuterBody F hu t' Ω hΩ k j).shade := by
  let G := step3FactorFamily F hu t' Ω hΩ k
  have hVW : ∀ i ∈ G.fiber j, (G.innerBody i).toConvexSpaceBody ≤ G.outerBody j := by
    intro i hi
    have hi' : i ∈ {i ∈ {i ∈ u | F.parent i ∈ t'} | F.parent i = j} := by
      simpa [FactorFamily.fiber, G, step3FactorFamily] using hi
    have hiu : i ∈ u := (Finset.mem_filter.mp (Finset.mem_filter.mp hi').1).1
    have hparent : F.parent i = j := (Finset.mem_filter.mp hi').2
    have hiF : i ∈ F.innerSet := hu hiu
    calc
      (G.innerBody i).toConvexSpaceBody = (F.innerBody i).toConvexSpaceBody := by
        simp [G, step3FactorFamily]
      _ ≤ F.outerBody (F.parent i) := F.inner_le_parent i hiF
      _ = F.outerBody j := by rw [hparent]
      _ = G.outerBody j := by simp [G, step3FactorFamily]
  calc
    iUnionShade (G.fiber j) G.innerBody ⊆
        Metric.cthickening (G.outerBody j).scale (iUnionShade (G.fiber j) G.innerBody) :=
      Metric.self_subset_cthickening _
    _ ⊆ (inducedShading (G.fiber j) G.innerBody (G.outerBody j)).shade := by
      exact cthickening_scale_iUnionShade_subset_shade_inducedShading
        (s := G.fiber j) (V := G.innerBody) (W := G.outerBody j) hVW
    _ = (step4OuterBody F hu t' Ω hΩ k j).shade := by
      simp [G, step4OuterBody]

/-- **The Step 4 shaded union dominates the Step 3 one**: `U (𝒱', Y₀') ⊆ U (𝒲', Y_{𝒲',0})`.

This is what transfers a pointwise multiplicity bound on `U (𝒱', Y₀')` to `U (𝒲', Y_{𝒲',0})`. -/
theorem iUnionShade_subset_iUnionShade_step4Outer (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) :
    iUnionShade (step3FactorFamily F hu t' Ω hΩ k).innerSet
        (step3FactorFamily F hu t' Ω hΩ k).innerBody ⊆
      iUnionShade t' (step4OuterBody F hu t' Ω hΩ k) := by
  unfold iUnionShade
  apply Set.iUnion₂_subset
  intro i hi
  have hmem : i ∈ u ∧ F.parent i ∈ t' := Finset.mem_filter.mp hi
  refine Set.subset_iUnion₂_of_subset (F.parent i) hmem.2 ?_
  have hfib := iUnionShade_fiber_subset_shade_step4OuterBody F hu t' Ω hΩ k (F.parent i)
  refine Set.Subset.trans ?_ hfib
  refine Set.subset_iUnion₂_of_subset i ?_ (Set.Subset.refl _)
  simp [FactorFamily.fiber, hmem]

/-! ### The shaded factor family of Step 4 -/

/-- The shaded factor family produced by Step 4: the Step 3 family with its outer bodies shaded by
the induced shading `ShadedBody.step4OuterBody`. Its inner set, inner bodies, outer set and parent
map are those of `ShadedBody.step3FactorFamily`. -/
noncomputable def step4ShadedFactorFamily (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω)
    (k : ℕ) : ShadedFactorFamily E ι κ where
  innerSet := (step3FactorFamily F hu t' Ω hΩ k).innerSet
  innerBody := (step3FactorFamily F hu t' Ω hΩ k).innerBody
  outerSet := t'
  outerBody := step4OuterBody F hu t' Ω hΩ k
  parent := F.parent
  parent_mem := fun i hi ↦ (Finset.mem_filter.mp hi).2
  inner_le_parent := fun i hi ↦
    le_trans ((step3FactorFamily F hu t' Ω hΩ k).inner_le_parent i hi)
      (ConvexSpaceBody.self_le_cthickening (F.outerBody (F.parent i))
        (F.outerBody (F.parent i)).scale)
  shade_subset_parent := fun i hi ↦ by
    classical
    have hiFiber : i ∈ (step3FactorFamily F hu t' Ω hΩ k).fiber (F.parent i) := by
      simpa [FactorFamily.fiber, step3FactorFamily] using hi
    calc
      ((step3FactorFamily F hu t' Ω hΩ k).innerBody i).shade ⊆
          ⋃ j ∈ (step3FactorFamily F hu t' Ω hΩ k).fiber (F.parent i),
            ((step3FactorFamily F hu t' Ω hΩ k).innerBody j).shade := by
        exact Set.subset_iUnion₂
          (s := fun j (x : j ∈ (step3FactorFamily F hu t' Ω hΩ k).fiber (F.parent i)) ↦
            ((step3FactorFamily F hu t' Ω hΩ k).innerBody j).shade) i hiFiber
      _ ⊆ ((step4OuterBody F hu t' Ω hΩ k) (F.parent i)).shade :=
        iUnionShade_fiber_subset_shade_step4OuterBody F hu t' Ω hΩ k (F.parent i)

@[simp]
theorem step4ShadedFactorFamily_innerSet (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) :
    (step4ShadedFactorFamily F hu t' Ω hΩ k).innerSet =
      {i ∈ u | F.parent i ∈ t'} := rfl

@[simp]
theorem step4ShadedFactorFamily_innerBody (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) :
    (step4ShadedFactorFamily F hu t' Ω hΩ k).innerBody = step3InnerBody F u t' Ω hΩ k := rfl

@[simp]
theorem step4ShadedFactorFamily_outerSet (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) :
    (step4ShadedFactorFamily F hu t' Ω hΩ k).outerSet = t' := rfl

@[simp]
theorem step4ShadedFactorFamily_outerBody (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) :
    (step4ShadedFactorFamily F hu t' Ω hΩ k).outerBody =
      step4OuterBody F hu t' Ω hΩ k := rfl

@[simp]
theorem step4ShadedFactorFamily_parent (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) :
    (step4ShadedFactorFamily F hu t' Ω hΩ k).parent = F.parent := rfl

end ShadedBody
