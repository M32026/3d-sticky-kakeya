/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.Step2

/-! # Step 3 of the factoring construction

This file formalizes Step 3 of the construction in GWZ Proposition 5.1. Given a factor family,
the blocks and level set selected by Steps 1 and 2, and the inner dyadic scale `2 ^ k`, it restricts
each surviving inner shade to the points in the level set where its fiber multiplicity lies in the
dyadic interval `[2 ^ k, 2 ^ (k + 1))`.

The level set is accepted with an explicit measurability proof. Step 2 deliberately works with
lower integrals and therefore does not need to establish measurability of its level sets, whereas a
`ShadedBody` must have a measurable shade. Keeping this hypothesis explicit prevents Step 3 from
hiding a regularity assumption.

The construction itself uses no linear or metric structure on `E`, so the first half of the file is
stated for a measurable convex space; only the mass statements, which mention `volume` and the
fixed Step 2 selection, need the strong ambient assumptions.

## Main definitions and statements

* `ShadedBody.step3DyadicSet`: the points where one fiber has the selected multiplicity scale;
* `ShadedBody.step3InnerBody`: one inner body equipped with the intermediate shade `Y₀'`;
* `ShadedBody.step3FactorFamily`: the surviving family, bundled as a `FactorFamily`;
* `ShadedBody.FactorFamily.step3'`: the same family with the Step 2 level set and inner scale
  substituted;
* `ShadedBody.step3FactorFamily_fiber_multiplicity`: every surviving fiber has pointwise
  multiplicity in `[2 ^ k, 2 ^ (k + 1))` on its shaded union;
* `ShadedBody.inv_mul_lintegral_le_sum_volume_step3FactorFamily`: the multiplicity mass retained
  by the construction.
-/

@[expose] public section

open MeasureTheory Convexity Kakeya
open scoped ENNReal

namespace Kakeya

/-- **Constant in Step 3 of the factoring construction**: Step 3 loses at most the pointwise
comparison constant from Step 2. -/
def factoringStep3Constant (N : ℕ) : ℕ := factoringStep2PointwiseConstant N

/-- The combined loss constant of Steps 2 and 3. -/
def factoringStep2Step3Constant (N : ℕ) : ℕ :=
  factoringStep2PigeonholeConstant N * factoringStep3Constant N

/-- Closed form of the combined loss constant of Steps 2 and 3. -/
theorem factoringStep2Step3Constant_eq (N : ℕ) :
    factoringStep2Step3Constant N = 4 * (Nat.log 2 N + 1) ^ 4 := by
  rw [factoringStep2Step3Constant, factoringStep3Constant,
    factoringStep2PigeonholeConstant_eq]
  simp only [factoringStep2PointwiseConstant, MultiplicityFamily.scaleTripleConstant,
    dyadicPigeonholeNatConstant]
  ring

end Kakeya

namespace ShadedBody

section Construction

variable
  {E : Type*} [TopologicalSpace E] [ConvexSpace ℝ E] [MeasurableSpace E]
  {ι κ : Type*} [DecidableEq κ]

/-! ### The Step 3 family -/

/-- The set of points where the multiplicity of the surviving fiber over `j` lies in the dyadic
interval `[2 ^ k, 2 ^ (k + 1))`. -/
def step3DyadicSet (F : FactorFamily E ι κ) (u : Finset ι) (t' : Finset κ)
    (k : ℕ) (j : κ) : Set E :=
  {x | 2 ^ k ≤ fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} j x ∧
    fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} j x < 2 ^ (k + 1)}

/-- The fiber-multiplicity dyadic set used in Step 3 is measurable. -/
theorem measurableSet_step3DyadicSet (F : FactorFamily E ι κ) (u : Finset ι)
    (t' : Finset κ) (k : ℕ) (j : κ) : MeasurableSet (step3DyadicSet F u t' k j) := by
  have hm : Measurable (fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} j) := by
    unfold fiberMultiplicity
    exact measurable_pointwiseMultiplicity _ _
  exact (measurableSet_le measurable_const hm).inter (measurableSet_lt hm measurable_const)

/-- The intermediate shaded inner body of Step 3:
`Y₀'(Vᵢ) = Y(Vᵢ) ∩ Ω ∩ {x | μ(𝒱'_{p(i)}, Y)(x) ∼ 2 ^ k}`. -/
noncomputable def step3InnerBody (F : FactorFamily E ι κ) (u : Finset ι)
    (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) (i : ι) : ShadedBody E where
  toConvexSpaceBody := (F.innerBody i).toConvexSpaceBody
  shade := (F.innerBody i).shade ∩ Ω ∩ step3DyadicSet F u t' k (F.parent i)
  measurableSet_shade := ((F.innerBody i).measurableSet_shade.inter hΩ).inter
    (measurableSet_step3DyadicSet F u t' k (F.parent i))
  shade_subset := fun _ hx ↦ (F.innerBody i).shade_subset hx.1.1

@[simp]
theorem toConvexSpaceBody_step3InnerBody (F : FactorFamily E ι κ) (u : Finset ι)
    (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) (i : ι) :
    (step3InnerBody F u t' Ω hΩ k i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody := rfl

@[simp]
theorem shade_step3InnerBody (F : FactorFamily E ι κ) (u : Finset ι)
    (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) (i : ι) :
    (step3InnerBody F u t' Ω hΩ k i).shade =
      (F.innerBody i).shade ∩ Ω ∩ step3DyadicSet F u t' k (F.parent i) := rfl

/-- The factor family produced in Step 3. Its outer set is `t'`, its inner set is the family
surviving Step 1, and its inner shades are the intermediate shadings `Y₀'`. -/
noncomputable def step3FactorFamily (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω)
    (k : ℕ) : FactorFamily E ι κ where
  innerSet := {i ∈ u | F.parent i ∈ t'}
  innerBody := step3InnerBody F u t' Ω hΩ k
  outerSet := t'
  outerBody := F.outerBody
  parent := F.parent
  parent_mem := fun _ hi ↦ (Finset.mem_filter.mp hi).2
  inner_le_parent := fun i hi ↦ F.inner_le_parent i (hu (Finset.mem_filter.mp hi).1)

@[simp]
theorem step3FactorFamily_innerSet (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) :
    (step3FactorFamily F hu t' Ω hΩ k).innerSet =
      {i ∈ u | F.parent i ∈ t'} := rfl

@[simp]
theorem step3FactorFamily_outerSet (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) :
    (step3FactorFamily F hu t' Ω hΩ k).outerSet = t' := rfl

@[simp]
theorem step3FactorFamily_parent (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) :
    (step3FactorFamily F hu t' Ω hΩ k).parent = F.parent := rfl

@[simp]
theorem step3FactorFamily_innerBody (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) :
    (step3FactorFamily F hu t' Ω hΩ k).innerBody = step3InnerBody F u t' Ω hΩ k := rfl

/-- Over a surviving block `j ∈ t'`, the fiber of the Step 3 family is the fiber of `F` inside `u`.

The hypothesis `j ∈ t'` is needed: for `j ∉ t'` the left-hand side is empty while
`{i ∈ u | F.parent i = j}` need not be. Note that `ShadedBody.FactorFamily.fiber` is defined with
`open Classical`, so this is not `rfl`; it is an equality of two filters of the same predicate
with different `Decidable` instances. -/
theorem step3FactorFamily_fiber (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω)
    (k : ℕ) {j : κ} (hj : j ∈ t') :
    (step3FactorFamily F hu t' Ω hΩ k).fiber j = {i ∈ u | F.parent i = j} := by
  classical
  rw [FactorFamily.fiber, step3FactorFamily_innerSet, step3FactorFamily_parent]
  ext i
  simp only [Finset.mem_filter]
  constructor
  · intro h
    exact ⟨h.1.1, h.2⟩
  · intro h
    exact ⟨⟨h.1, by simpa [h.2] using hj⟩, h.2⟩

/-! ### Pointwise properties -/

open Classical in
/-- In a surviving block, Step 3 retains exactly the original fiber multiplicity when the point is
in `Ω` and in the selected dyadic class, and retains no indices otherwise. -/
theorem pointwiseMultiplicity_step3FactorFamily_fiber (F : FactorFamily E ι κ)
    {u : Finset ι} (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E)
    (hΩ : MeasurableSet Ω) (k : ℕ) (j : κ) (x : E) :
    pointwiseMultiplicity ((step3FactorFamily F hu t' Ω hΩ k).fiber j)
        (step3FactorFamily F hu t' Ω hΩ k).innerBody x =
      if x ∈ Ω ∧ x ∈ step3DyadicSet F u t' k j then
        fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} j x
      else 0 := by
  classical
  simp only [FactorFamily.fiber, step3FactorFamily, fiberMultiplicity, pointwiseMultiplicity]
  by_cases hcond : x ∈ Ω ∧ x ∈ step3DyadicSet F u t' k j
  · rw [if_pos hcond]
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, step3InnerBody, Set.mem_inter_iff]
    constructor
    · exact fun hi ↦ ⟨hi.1, hi.2.1.1⟩
    · intro hi
      have hparent : F.parent i = j := hi.1.2
      exact ⟨hi.1, ⟨⟨hi.2, hcond.1⟩, by simpa [hparent] using hcond.2⟩⟩
  · rw [if_neg hcond]
    apply Finset.card_eq_zero.mpr
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨i, hi⟩
    simp only [Finset.mem_filter, step3InnerBody, Set.mem_inter_iff] at hi
    apply hcond
    have hparent : F.parent i = j := hi.1.2
    exact ⟨hi.2.1.2, by simpa [hparent] using hi.2.2⟩

open Classical in
/-- The total pointwise multiplicity after Step 3 is the sum of the multiplicities in the selected
dyadic blocks at points of `Ω`, and is zero off `Ω`. -/
theorem pointwiseMultiplicity_step3FactorFamily (F : FactorFamily E ι κ)
    {u : Finset ι} (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E)
    (hΩ : MeasurableSet Ω) (k : ℕ) (x : E) :
    pointwiseMultiplicity (step3FactorFamily F hu t' Ω hΩ k).innerSet
        (step3FactorFamily F hu t' Ω hΩ k).innerBody x =
      if x ∈ Ω then
        ∑ j ∈ MultiplicityFamily.dyadicLevel t'
            (fiberMultiplicity F {i ∈ u | F.parent i ∈ t'}) k x,
          fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} j x
      else 0 := by
  classical
  by_cases hx : x ∈ Ω
  · rw [if_pos hx]
    calc
      pointwiseMultiplicity (step3FactorFamily F hu t' Ω hΩ k).innerSet
          (step3FactorFamily F hu t' Ω hΩ k).innerBody x =
          ∑ j ∈ t', pointwiseMultiplicity ((step3FactorFamily F hu t' Ω hΩ k).fiber j)
            (step3FactorFamily F hu t' Ω hΩ k).innerBody x := by
        have hsum := pointwiseMultiplicity_eq_sum_fiberwise
            (step3FactorFamily F hu t' Ω hΩ k).innerSet t'
            (step3FactorFamily F hu t' Ω hΩ k).parent
            (step3FactorFamily F hu t' Ω hΩ k).innerBody x
            (step3FactorFamily F hu t' Ω hΩ k).parent_mem
        exact hsum.trans (by
          apply Finset.sum_congr rfl
          intro j _
          congr 2)
      _ = ∑ j ∈ t', if x ∈ step3DyadicSet F u t' k j then
            fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} j x else 0 := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rw [pointwiseMultiplicity_step3FactorFamily_fiber F hu t' Ω hΩ k j x]
        simp [hx]
      _ = ∑ j ∈ MultiplicityFamily.dyadicLevel t'
            (fiberMultiplicity F {i ∈ u | F.parent i ∈ t'}) k x,
          fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} j x := by
        unfold MultiplicityFamily.dyadicLevel
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        simp only [step3DyadicSet, Set.mem_setOf_eq]
        by_cases hj : 2 ^ k ≤ fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} j x ∧
          fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} j x < 2 ^ (k + 1)
        · simp [hj]
        · simp [hj]
  · rw [if_neg hx]
    simp [pointwiseMultiplicity, step3FactorFamily, step3InnerBody, hx]

/-- On the shaded union of each surviving fiber, its Step 3 pointwise multiplicity lies in the
selected dyadic interval `[2 ^ k, 2 ^ (k + 1))`.

No hypothesis on `j` is required, and in particular none is recorded: for `j ∉ t'` the Step 3 fiber
`{i ∈ u' | p i = j}` is empty, so the shaded union is empty and `hx` is vacuous. -/
theorem step3FactorFamily_fiber_multiplicity (F : FactorFamily E ι κ)
    {u : Finset ι} (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E)
    (hΩ : MeasurableSet Ω) (k : ℕ) {j : κ} {x : E}
    (hx : x ∈ ⋃ i ∈ (step3FactorFamily F hu t' Ω hΩ k).fiber j,
      ((step3FactorFamily F hu t' Ω hΩ k).innerBody i).shade) :
    2 ^ k ≤ pointwiseMultiplicity ((step3FactorFamily F hu t' Ω hΩ k).fiber j)
        (step3FactorFamily F hu t' Ω hΩ k).innerBody x ∧
      pointwiseMultiplicity ((step3FactorFamily F hu t' Ω hΩ k).fiber j)
          (step3FactorFamily F hu t' Ω hΩ k).innerBody x < 2 ^ (k + 1) := by
  classical
  rcases Set.mem_iUnion₂.mp hx with ⟨i, hi, hxi⟩
  have hi' : i ∈ {i ∈ {i ∈ u | F.parent i ∈ t'} | F.parent i = j} := by
    simpa [FactorFamily.fiber, step3FactorFamily] using hi
  have hparent : F.parent i = j := (Finset.mem_filter.mp hi').2
  have hxi' : x ∈ (F.innerBody i).shade ∩ Ω ∩
      step3DyadicSet F u t' k (F.parent i) := by
    simpa [step3FactorFamily, step3InnerBody] using hxi
  have hxdyadic : x ∈ step3DyadicSet F u t' k j := by
    simpa [hparent] using hxi'.2
  rw [pointwiseMultiplicity_step3FactorFamily_fiber F hu t' Ω hΩ k j x,
    if_pos ⟨hxi'.1.2, hxdyadic⟩]
  exact hxdyadic

/-- The selected dyadic blocks give a lower bound for the total Step 3 pointwise multiplicity. -/
theorem mul_card_dyadicLevel_le_pointwiseMultiplicity_step3FactorFamily
    (F : FactorFamily E ι κ) {u : Finset ι} (hu : u ⊆ F.innerSet)
    (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) {x : E}
    (hx : x ∈ Ω) :
    2 ^ k * (MultiplicityFamily.dyadicLevel t'
        (fiberMultiplicity F {i ∈ u | F.parent i ∈ t'}) k x).card ≤
      pointwiseMultiplicity (step3FactorFamily F hu t' Ω hΩ k).innerSet
        (step3FactorFamily F hu t' Ω hΩ k).innerBody x := by
  rw [pointwiseMultiplicity_step3FactorFamily F hu t' Ω hΩ k x, if_pos hx]
  apply (Nat.dyadic_class_card_sandwich _ _ k ?_).1
  intro j hj
  exact (Finset.mem_filter.mp hj).2

end Construction

section Fixed

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [DecidableEq κ]

namespace FactorFamily

/-- **Step 3 of the factoring construction at the fixed Step 2 selection**: the Step 3 family built
from the level set `F.step2Set' hu t' hw₁` and the inner scale `(F.step2' hu t' hw₁).1` chosen by
Step 2.

This mirrors `ShadedBody.FactorFamily.step2'`: `ShadedBody.step3FactorFamily` is stated for a
general measurable `Ω` and a general inner scale, and this substitutes the Step 2 selection once, so
that later statements need not repeat it. -/
noncomputable def step3' (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) {w₁ : ℝ} (hw₁ : 0 ≤ w₁)
    (hΩ : MeasurableSet (F.step2Set' hu t' hw₁)) : FactorFamily E ι κ :=
  step3FactorFamily F hu t' (F.step2Set' hu t' hw₁) hΩ (F.step2' hu t' hw₁).1

end FactorFamily

/-- On the fixed Step 2 level set, the original surviving multiplicity is at most the Step 2
pointwise constant times the Step 3 multiplicity. -/
theorem pointwiseMultiplicity_le_mul_pointwiseMultiplicity_step3FactorFamily
    (F : FactorFamily E ι κ) {u : Finset ι} (hu : u ⊆ F.innerSet)
    (t' : Finset κ) {w₁ : ℝ} (hw₁ : 0 ≤ w₁)
    (hΩ : MeasurableSet (F.step2Set' hu t' hw₁)) {x : E}
    (hx : x ∈ F.step2Set' hu t' hw₁) :
    pointwiseMultiplicity {i ∈ u | F.parent i ∈ t'} F.innerBody x ≤
      Kakeya.factoringStep3Constant F.innerSet.card *
        pointwiseMultiplicity (F.step3' hu t' hw₁ hΩ).innerSet
          (F.step3' hu t' hw₁ hΩ).innerBody x := by
  unfold FactorFamily.step3'
  have hbounds := F.bounds_of_mem_step2Set' hu t' hw₁ hx
  have hlower : 2 ^ (F.step2' hu t' hw₁).1 * 2 ^ (F.step2' hu t' hw₁).2.1 ≤
      pointwiseMultiplicity
        (step3FactorFamily F hu t' (F.step2Set' hu t' hw₁) hΩ
          (F.step2' hu t' hw₁).1).innerSet
        (step3FactorFamily F hu t' (F.step2Set' hu t' hw₁) hΩ
          (F.step2' hu t' hw₁).1).innerBody x := by
    calc
      2 ^ (F.step2' hu t' hw₁).1 * 2 ^ (F.step2' hu t' hw₁).2.1
          ≤ 2 ^ (F.step2' hu t' hw₁).1 * (MultiplicityFamily.dyadicLevel t'
              (fiberMultiplicity F {i ∈ u | F.parent i ∈ t'})
                (F.step2' hu t' hw₁).1 x).card :=
        Nat.mul_le_mul_left _ hbounds.2.2.1
      _ ≤ pointwiseMultiplicity
          (step3FactorFamily F hu t' (F.step2Set' hu t' hw₁) hΩ
            (F.step2' hu t' hw₁).1).innerSet
          (step3FactorFamily F hu t' (F.step2Set' hu t' hw₁) hΩ
            (F.step2' hu t' hw₁).1).innerBody x :=
        mul_card_dyadicLevel_le_pointwiseMultiplicity_step3FactorFamily F hu t'
          (F.step2Set' hu t' hw₁) hΩ (F.step2' hu t' hw₁).1 hx
  calc
    pointwiseMultiplicity {i ∈ u | F.parent i ∈ t'} F.innerBody x
        ≤ Kakeya.factoringStep2PointwiseConstant F.innerSet.card
            * (2 ^ (F.step2' hu t' hw₁).1 * 2 ^ (F.step2' hu t' hw₁).2.1) :=
      hbounds.2.1
    _ ≤ Kakeya.factoringStep2PointwiseConstant F.innerSet.card *
        pointwiseMultiplicity
          (step3FactorFamily F hu t' (F.step2Set' hu t' hw₁) hΩ
            (F.step2' hu t' hw₁).1).innerSet
          (step3FactorFamily F hu t' (F.step2Set' hu t' hw₁) hΩ
            (F.step2' hu t' hw₁).1).innerBody x :=
      Nat.mul_le_mul_left _ hlower
    _ = Kakeya.factoringStep3Constant F.innerSet.card *
        pointwiseMultiplicity
          (step3FactorFamily F hu t' (F.step2Set' hu t' hw₁) hΩ
            (F.step2' hu t' hw₁).1).innerSet
          (step3FactorFamily F hu t' (F.step2Set' hu t' hw₁) hΩ
            (F.step2' hu t' hw₁).1).innerBody x := rfl

/-! ### Mass retention -/

/-- Step 3 retains at least the inverse of
`Kakeya.factoringStep3Constant F.innerSet.card` times the multiplicity mass on the fixed Step 2
level set. -/
theorem inv_mul_lintegral_le_sum_volume_step3FactorFamily
    (F : FactorFamily E ι κ) {u : Finset ι} (hu : u ⊆ F.innerSet)
    (t' : Finset κ) {w₁ : ℝ} (hw₁ : 0 ≤ w₁)
    (hΩ : MeasurableSet (F.step2Set' hu t' hw₁)) :
    ((Kakeya.factoringStep3Constant F.innerSet.card : ℝ≥0∞))⁻¹ *
        ∫⁻ x in F.step2Set' hu t' hw₁,
          (pointwiseMultiplicity
            {i ∈ u | F.parent i ∈ t'} F.innerBody x : ℝ≥0∞) ≤
      ∑ i ∈ (F.step3' hu t' hw₁ hΩ).innerSet,
        volume ((F.step3' hu t' hw₁ hΩ).innerBody i).shade := by
  let Ω := F.step2Set' hu t' hw₁
  let k := (F.step2' hu t' hw₁).1
  let G := F.step3' hu t' hw₁ hΩ
  let C := Kakeya.factoringStep3Constant F.innerSet.card
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by
    have hpos : 4 ≤ C := (Kakeya.factoringStep2Constant_pos F.innerSet.card).2
    exact_mod_cast (by omega : C ≠ 0)
  have hCtop : (C : ℝ≥0∞) ≠ ⊤ := by simp
  have hCinvtop : ((C : ℝ≥0∞))⁻¹ ≠ ⊤ := by simp [hC0]
  have hpoint : ∀ x ∈ Ω,
      (pointwiseMultiplicity {i ∈ u | F.parent i ∈ t'} F.innerBody x : ℝ≥0∞) ≤
        (C : ℝ≥0∞) * (pointwiseMultiplicity G.innerSet G.innerBody x : ℝ≥0∞) := by
    intro x hx
    exact_mod_cast pointwiseMultiplicity_le_mul_pointwiseMultiplicity_step3FactorFamily
      F hu t' hw₁ hΩ hx
  have hintegral :
      ∫⁻ x in Ω, (C : ℝ≥0∞)⁻¹ *
          (pointwiseMultiplicity
            {i ∈ u | F.parent i ∈ t'} F.innerBody x : ℝ≥0∞) ≤
        ∫⁻ x in Ω, (pointwiseMultiplicity G.innerSet G.innerBody x : ℝ≥0∞) := by
    refine lintegral_mono_ae ((ae_restrict_iff' hΩ).2 ?_)
    exact Filter.Eventually.of_forall fun x hx ↦
      (ENNReal.inv_mul_le_iff hC0 hCtop).mpr (hpoint x hx)
  have hsupp : Function.support
      (fun x ↦ (pointwiseMultiplicity G.innerSet G.innerBody x : ℝ≥0∞)) ⊆ Ω := by
    intro x hx
    have hxnat : pointwiseMultiplicity G.innerSet G.innerBody x ≠ 0 := Nat.cast_ne_zero.mp hx
    have hxpos : 0 < pointwiseMultiplicity G.innerSet G.innerBody x :=
      Nat.pos_iff_ne_zero.mpr hxnat
    obtain ⟨i, hi, hxi⟩ := (pointwiseMultiplicity_pos_iff G.innerSet G.innerBody x).mp hxpos
    change x ∈ (F.innerBody i).shade ∩ Ω ∩ step3DyadicSet F u t' k (F.parent i) at hxi
    exact hxi.1.2
  calc
    ((Kakeya.factoringStep3Constant F.innerSet.card : ℝ≥0∞))⁻¹ *
          ∫⁻ x in F.step2Set' hu t' hw₁,
            (pointwiseMultiplicity
              {i ∈ u | F.parent i ∈ t'} F.innerBody x : ℝ≥0∞) =
        ∫⁻ x in Ω, (C : ℝ≥0∞)⁻¹ *
          (pointwiseMultiplicity
            {i ∈ u | F.parent i ∈ t'} F.innerBody x : ℝ≥0∞) := by
      symm
      exact lintegral_const_mul' (μ := volume.restrict Ω) (C : ℝ≥0∞)⁻¹ _ hCinvtop
    _ ≤ ∫⁻ x in Ω, (pointwiseMultiplicity G.innerSet G.innerBody x : ℝ≥0∞) := hintegral
    _ = ∫⁻ x, (pointwiseMultiplicity G.innerSet G.innerBody x : ℝ≥0∞) :=
      setLIntegral_eq_of_support_subset hsupp
    _ = ∑ i ∈ G.innerSet, volume (G.innerBody i).shade :=
      (sum_volume_shade_eq_lintegral_pointwiseMultiplicity G.innerSet G.innerBody).symm

/-- Steps 2 and 3 together retain at least the inverse of
`Kakeya.factoringStep2Step3Constant F.innerSet.card` times the shading mass selected before the
fixed Step 2 construction. -/
theorem inv_mul_sum_volume_shade_le_sum_volume_step3FactorFamily
    (F : FactorFamily E ι κ) {u : Finset ι} (hu : u ⊆ F.innerSet)
    {t' : Finset κ} (ht' : t' ⊆ u.image F.parent) {w₁ : ℝ} (hw₁ : 0 ≤ w₁)
    (hΩ : MeasurableSet (F.step2Set' hu t' hw₁)) :
    ((Kakeya.factoringStep2Step3Constant F.innerSet.card : ℝ≥0∞))⁻¹ *
        ∑ i ∈ {i ∈ u | F.parent i ∈ t'}, volume (F.innerBody i).shade ≤
      ∑ i ∈ (F.step3' hu t' hw₁ hΩ).innerSet,
        volume ((F.step3' hu t' hw₁ hΩ).innerBody i).shade := by
  have hstep2 := F.inv_mul_sum_volume_shade_le_lintegral_step2Set' hu ht' hw₁
  have hstep3 := inv_mul_lintegral_le_sum_volume_step3FactorFamily F hu t' hw₁ hΩ
  have hC₂0 :
      (Kakeya.factoringStep2PigeonholeConstant F.innerSet.card : ℝ≥0∞) ≠ 0 := by
    have hpos := (Kakeya.factoringStep2Constant_pos F.innerSet.card).1
    exact_mod_cast (by omega : Kakeya.factoringStep2PigeonholeConstant F.innerSet.card ≠ 0)
  have hC₂top :
      (Kakeya.factoringStep2PigeonholeConstant F.innerSet.card : ℝ≥0∞) ≠ ⊤ := by simp
  calc
    ((Kakeya.factoringStep2Step3Constant F.innerSet.card : ℝ≥0∞))⁻¹ *
          ∑ i ∈ {i ∈ u | F.parent i ∈ t'}, volume (F.innerBody i).shade =
        ((Kakeya.factoringStep3Constant F.innerSet.card : ℝ≥0∞))⁻¹ *
          (((Kakeya.factoringStep2PigeonholeConstant F.innerSet.card : ℝ≥0∞))⁻¹ *
            ∑ i ∈ {i ∈ u | F.parent i ∈ t'}, volume (F.innerBody i).shade) := by
      simp only [Kakeya.factoringStep2Step3Constant, Nat.cast_mul]
      rw [ENNReal.mul_inv (Or.inl hC₂0) (Or.inl hC₂top)]
      ac_rfl
    _ ≤ ((Kakeya.factoringStep3Constant F.innerSet.card : ℝ≥0∞))⁻¹ *
        ∫⁻ x in F.step2Set' hu t' hw₁,
          (pointwiseMultiplicity
            {i ∈ u | F.parent i ∈ t'} F.innerBody x : ℝ≥0∞) :=
      mul_le_mul_right hstep2 _
    _ ≤ ∑ i ∈ (F.step3' hu t' hw₁ hΩ).innerSet,
        volume ((F.step3' hu t' hw₁ hΩ).innerBody i).shade := hstep3

end Fixed

end ShadedBody
