/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.Pigeonhole
public import Kakeya.FactorFamily.Basic

/-! # Step 0 of the factoring construction

This file formalizes the blueprint subsubsection "Step 0: discarding the bodies of low relative
shading" of `subsec:step1`: the first step of the outer factoring family of GWZ Proposition 5.1
(`ShadedBody.outerFactoringFamily`) throws away the inner bodies whose shading is much thinner
than average.

The operation is already available on bare index sets, at an arbitrary level `c`, as
`ShadedBody.discardLowShading`, with its properties in `Kakeya/Factoring/Pigeonhole.lean`. What is
added here is the same operation performed on a factor family, at the single level `2⁻¹` used by
the construction, so that Step 1 and every later step can consume a factor family rather than an
unfolded filter expression. The outer family and the parent map are untouched; the only field that
changes is the inner indexing set.

Nothing here is new mathematics: each of the two lemmas is the corresponding lemma of
`Kakeya/Factoring/Pigeonhole.lean` at `c = 2⁻¹`, read through the definition below.

## Main statements

* `ShadedBody.FactorFamily.step0` (blueprint `def:factoringStep0`): the Step 0 family `F.step0`,
  together with the five `rfl` projections `ShadedBody.FactorFamily.innerSet_step0`,
  `innerBody_step0`, `outerSet_step0`, `outerBody_step0` and `parent_step0`;
* `ShadedBody.FactorFamily.le_volume_shade_of_mem_innerSet_step0` (blueprint
  `lem:factoringStep0Mem`): every surviving body has relative shading at least half the fullness of
  the *original* family `F`;
* `ShadedBody.FactorFamily.innerSet_step0_subset` and
  `ShadedBody.FactorFamily.isCRefinement_step0` (blueprint `lem:factoringStep0Refinement`): the
  surviving inner family is a `2⁻¹` refinement of the inner family of `F`.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal ENNReal

namespace ShadedBody

namespace FactorFamily

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*}

/-- **Step 0 of the construction in blueprint `def:outerFactoringFamily`** (blueprint
`def:factoringStep0`): the factor family obtained from `F` by discarding the inner bodies whose
relative shading is less than half the fullness of `F`.

Its inner indexing set is `ShadedBody.discardLowShading F.innerSet F.innerBody 2⁻¹`, the set of
`i ∈ F.innerSet` with `|Y (V i)| ≥ (λ(𝒱, Y) / 2) * |V i|`; the threshold uses the fullness
`λ(𝒱, Y) = fullness F.innerSet F.innerBody` of the *original* family `F`, fixed once and for all
before any index is discarded and never recomputed. The inner bodies with their shadings, the
outer family and the parent map are those of `F`, so the five fields are available by `rfl`. -/
noncomputable def step0 (F : FactorFamily E ι κ) : FactorFamily E ι κ :=
  F.ofSubset (_root_.ShadedBody.discardLowShading_subset F.innerSet F.innerBody 2⁻¹)

/-! ### The five fields of the Step 0 family

Each of the five fields of `F.step0` is the corresponding field of `F`, except for the inner
indexing set which is `ShadedBody.discardLowShading F.innerSet F.innerBody 2⁻¹`; all five
identities hold by definition. `innerSet_step0` is the bridge between the factor-family form of
Step 0 used from here on and the bare filter expression of
`Kakeya/Factoring/Pigeonhole.lean`. -/

/-- The inner indexing set of the Step 0 family is the surviving index set. -/
@[simp]
theorem innerSet_step0 (F : FactorFamily E ι κ) :
    F.step0.innerSet
      = _root_.ShadedBody.discardLowShading F.innerSet F.innerBody 2⁻¹ := by
  rfl

/-- Step 0 keeps the inner bodies, with their shadings, of `F`. -/
@[simp]
theorem innerBody_step0 (F : FactorFamily E ι κ) : F.step0.innerBody = F.innerBody := by
  rfl

/-- Step 0 keeps the outer indexing set of `F`. -/
@[simp]
theorem outerSet_step0 (F : FactorFamily E ι κ) : F.step0.outerSet = F.outerSet := by
  rfl

/-- Step 0 keeps the outer bodies of `F`. -/
@[simp]
theorem outerBody_step0 (F : FactorFamily E ι κ) : F.step0.outerBody = F.outerBody := by
  rfl

/-- Step 0 keeps the parent map of `F`. -/
@[simp]
theorem parent_step0 (F : FactorFamily E ι κ) : F.step0.parent = F.parent := by
  rfl

/-- **Bodies kept by Step 0** (blueprint `lem:factoringStep0Mem`): every index of the inner set of
`F.step0` satisfies `|Y (V i)| ≥ (λ(𝒱, Y) / 2) * |V i|`, the fullness being that of `F`. The same
then holds for every index in any subset of that inner set. -/
theorem le_volume_shade_of_mem_innerSet_step0 {F : FactorFamily E ι κ}
    {i : ι} (hi : i ∈ F.step0.innerSet) :
    ((2⁻¹ : ℝ≥0) : ℝ≥0∞) * (fullness F.innerSet F.innerBody : ℝ≥0∞)
        * volume (F.innerBody i).carrier
      ≤ volume (F.innerBody i).shade := by
  rw [innerSet_step0] at hi
  exact _root_.ShadedBody.le_volume_shade_of_mem_discardLowShading hi

/-- **Step 0 shrinks the inner indexing set** (blueprint `lem:factoringStep0Refinement`): the
containment that makes `F.step0` a factor family at all, and the first half of the refinement
`ShadedBody.FactorFamily.isCRefinement_step0`. -/
theorem innerSet_step0_subset (F : FactorFamily E ι κ) : F.step0.innerSet ⊆ F.innerSet := by
  simpa using _root_.ShadedBody.discardLowShading_subset F.innerSet F.innerBody (2⁻¹ : ℝ≥0)

/-- **Step 0 is a `2⁻¹` refinement** (blueprint `lem:factoringStep0Refinement`): the inner family
of `F.step0`, carrying its shading, is a `2⁻¹` refinement of the inner family of `F` carrying the
same shading, since `1 - 2⁻¹ = 2⁻¹`.

This is the mass lost by Step 0, and the source of the factor `2` carried by
`Kakeya.factoringStep1PigeonholeConstant`. -/
theorem isCRefinement_step0 (F : FactorFamily E ι κ) :
    IsCRefinement F.step0.innerSet F.step0.innerBody F.innerSet F.innerBody 2⁻¹ := by
  have hc1 : (2⁻¹ : ℝ≥0) < 1 := by norm_num
  have heq : (1 - 2⁻¹ : ℝ≥0) = 2⁻¹ := by
    apply NNReal.eq
    norm_num
  simpa only [innerSet_step0, innerBody_step0, heq] using
    _root_.ShadedBody.isCRefinement_discardLowShading F.innerSet F.innerBody hc1

end FactorFamily

end ShadedBody
