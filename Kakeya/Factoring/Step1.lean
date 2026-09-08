/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.Pigeonhole
public import Kakeya.Factoring.Step0
public import Kakeya.FactorFamily.Predicates
public import Kakeya.LEApprox
public import Kakeya.Mathlib.Finset
public import Kakeya.Pigeonhole
public import Kakeya.Thickness.Lemmas

/-! # Step 1 of the factoring construction

This file contains the complete formalization of Step 1 in GWZ Proposition 5.1. The first part
develops the fiber-volume pigeonholing and discard machinery used internally by the construction.
The second part specializes those helpers to a family whose bodies have scale at least `δ` and
constructs the fixed surviving factor family.

The helper definitions are deliberately opaque at the module boundary. Downstream code should use
`ShadedBody.FactorFamily.step1` and its named property theorems rather than unfold or choose
an arbitrary generic Step 1 selection.

## Main statements

* `Kakeya.factoringStep1AtScaleConstant` and `Kakeya.coe_factoringStep1AtScaleConstant`: the
  explicit logarithmic loss at scale `δ`;
* `ShadedBody.FactorFamily.step1`: the fixed Step 1 factor family;
* `ShadedBody.FactorFamily.isCRefinement_step1`,
  `ShadedBody.FactorFamily.fiberVolume_step1_le_two_mul`, and the accompanying projection,
  decomposition, containment, and nonemptiness theorems: the properties consumed downstream.

The generic fiber pigeonholing also supplies `Kakeya.factoringStep1FiberPigeonholeConstant`, reused
by Step 5 for the same one-dimensional dyadic pigeonhole loss.
-/

public section

open MeasureTheory Convexity Kakeya
open scoped NNReal ENNReal

namespace Kakeya

/-- **Constant in `ShadedBody.exists_isCRefinement_fiberVolume_comparable`** (blueprint
`def:factoringStep1FiberPigeonholeConstant`): the loss factor
`C(a, b) = (1 + log₂ (b / a))₊` of the fiber pigeonholing, i.e. the loss produced by
`ENNReal.dyadic_pigeonhole₁''`, an upper bound for the number of dyadic classes needed to cover
`[a, b]`.

No relation between `a` and `b` is assumed; when `a ≤ b` the positive part is inactive and
`C(a, b) = 1 + log₂ (b / a) ≥ 1`. The constant depends only on the ratio `b / a`; in particular it
does *not* depend on the ambient dimension. -/
@[expose] noncomputable def factoringStep1FiberPigeonholeConstant (a b : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal (1 + Real.logb 2 ((b : ℝ) / (a : ℝ)))

private theorem coe_factoringStep1FiberPigeonholeConstant_private (a b : ℝ≥0) :
    (factoringStep1FiberPigeonholeConstant a b : ℝ≥0∞)
      = ENNReal.ofReal (1 + Real.logb 2 ((b : ℝ) / (a : ℝ))) := rfl

/-- The coercion of `Kakeya.factoringStep1FiberPigeonholeConstant` to `ℝ≥0∞` is literally the loss
factor appearing in `ENNReal.dyadic_pigeonhole₁''`, so no conversion is needed when that lemma is
applied. -/
theorem coe_factoringStep1FiberPigeonholeConstant (a b : ℝ≥0) :
    (factoringStep1FiberPigeonholeConstant a b : ℝ≥0∞)
      = ENNReal.ofReal (1 + Real.logb 2 ((b : ℝ) / (a : ℝ))) :=
  coe_factoringStep1FiberPigeonholeConstant_private a b

/-- **Constant in `ShadedBody.FactorFamily.isCRefinement_step1'`** (blueprint
`def:factoringStep1PigeonholeConstant`): `2 C(a, b)`, where the factor `2` is the loss incurred by
the discard step and `C(a, b) = factoringStep1FiberPigeonholeConstant a b` is the logarithmic loss
of the fiber pigeonholing.

Here `a` and `b` are lower and upper bounds for the surviving fiber volumes
`ShadedBody.fiberVolume`. The constant lives in `ℝ≥0` so that its inverse is again in `ℝ≥0` and can
serve directly as the parameter `c` of `ShadedBody.IsCRefinement`. It depends only on the ratio
`b / a`; in particular it does *not* depend on the ambient dimension. -/
@[expose] noncomputable def factoringStep1PigeonholeConstant (a b : ℝ≥0) : ℝ≥0 :=
  2 * factoringStep1FiberPigeonholeConstant a b

/-- **The Step 1 pigeonhole constant is twice the fiber pigeonhole constant**, the unfolding
lemma for `Kakeya.factoringStep1PigeonholeConstant`. It is stated because the body of that
definition is not exposed across the module boundary. -/
theorem factoringStep1PigeonholeConstant_eq (a b : ℝ≥0) :
    factoringStep1PigeonholeConstant a b = 2 * factoringStep1FiberPigeonholeConstant a b := rfl

/-- **The two loss factors combine** (blueprint `lem:factoringStep1ConstantInv`): the discard loss
`2⁻¹` times the fiber pigeonholing loss is the inverse of
`Kakeya.factoringStep1PigeonholeConstant`. -/
theorem factoringStep1PigeonholeConstant_inv (a b : ℝ≥0) :
    2⁻¹ * (factoringStep1FiberPigeonholeConstant a b)⁻¹
      = (factoringStep1PigeonholeConstant a b)⁻¹ := by
  calc
    2⁻¹ * (factoringStep1FiberPigeonholeConstant a b)⁻¹
        = (2 * factoringStep1FiberPigeonholeConstant a b)⁻¹ := by
      rw [← mul_inv, mul_comm]
    _ = (factoringStep1PigeonholeConstant a b)⁻¹ := rfl

/-- **The explicit constant is at least `2`** (blueprint `lem:factoringStep1ConstantLowerBd`),
first half: `C(a, b) = (1 + log₂ (b / a))₊ ≥ 1` as soon as `a ≤ b`.

This is a genuine pointwise inequality: `a` and `b` are plain elements of `ℝ≥0`, and there is no
`ρ`, no `ε` and no implicit constant. Positivity of `a` is not needed: when `a = 0` the `ℝ≥0`
convention `b / 0 = 0` gives `log₂ (b / a) = 0` and the constant is exactly `1`. -/
theorem one_le_factoringStep1FiberPigeonholeConstant {a b : ℝ≥0} (hab : a ≤ b) :
    1 ≤ factoringStep1FiberPigeonholeConstant a b := by
  rw [factoringStep1FiberPigeonholeConstant, Real.one_le_toNNReal, le_add_iff_nonneg_right]
  rcases eq_or_lt_of_le a.coe_nonneg with ha | ha
  · simp [← ha]
  · exact Real.logb_nonneg one_lt_two ((one_le_div ha).mpr (by exact_mod_cast hab))

/-- **The explicit constant is at least `2`** (blueprint `lem:factoringStep1ConstantLowerBd`),
second half: `2 C(a, b) ≥ 2`. This is what keeps the reciprocal
`(factoringStep1PigeonholeConstant a b)⁻¹` away from `0`. -/
theorem two_le_factoringStep1PigeonholeConstant {a b : ℝ≥0} (hab : a ≤ b) :
    2 ≤ factoringStep1PigeonholeConstant a b :=
  le_mul_of_one_le_right zero_le (one_le_factoringStep1FiberPigeonholeConstant hab)

/-- **The explicit constant is `⪅ 1`** (blueprint `lem:factoringStep1ConstantLeApproxOne`).

The hypotheses are those of `Kakeya.toNNReal_logb_div_leApprox_one`; in particular `a ≤ b` is
*not* assumed, so `factoringStep1PigeonholeConstant (a ρ) (b ρ) = 2 (1 + log₂ (b ρ / a ρ))₊` is
only bounded by, rather than equal to, `2 (1 + (log₂ (b ρ / a ρ))₊)`; that pointwise inequality is
subadditivity of the positive part, `Real.toNNReal_add_le`. The two upgrades along the way are
`Kakeya.LEApprox.const_add_one` with `c = 1` and `Kakeya.LEApprox.const_mul_one` with `k = 2`. -/
theorem factoringStep1PigeonholeConstant_leApprox_one {a b : ℝ≥0 → ℝ≥0}
    (hratio : (fun ρ => b ρ / a ρ) ≲ fun ρ : ℝ≥0 => ρ⁻¹) :
    (fun ρ => factoringStep1PigeonholeConstant (a ρ) (b ρ)) ⪅
      fun _ : ℝ≥0 => (1 : ℝ≥0) := by
  refine LEApprox.mono_left
    (X' := fun ρ : ℝ≥0 => 2 * (1 + Real.toNNReal (Real.logb 2 ((b ρ : ℝ) / (a ρ : ℝ)))))
    (((toNNReal_logb_div_leApprox_one hratio).const_add_one 1).const_mul_one 2)
    fun ρ _ _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  simpa [factoringStep1FiberPigeonholeConstant] using
    Real.toNNReal_add_le (r := (1 : ℝ)) (p := Real.logb 2 ((b ρ : ℝ) / (a ρ : ℝ)))

/-- **The explicit constant is `⪆ 1`** (blueprint `lem:factoringStep1ConstantApprox`): this is the
`⪆ 1` used by the construction, obtained from `⪅ 1` for the constant itself
(`Kakeya.factoringStep1PigeonholeConstant_leApprox_one`) together with the pointwise lower bound
`Kakeya.two_le_factoringStep1PigeonholeConstant`.

The hypothesis `hab`, unused in `Kakeya.toNNReal_logb_div_leApprox_one` and
`Kakeya.factoringStep1PigeonholeConstant_leApprox_one`, is essential here: it is what keeps the
constant `≥ 2`, hence its reciprocal away from `0`. It is `Kakeya.one_leApprox_inv`, applied with
`c = 2`, that converts the two facts into the stated `⪆ 1`. -/
theorem one_leApprox_factoringStep1PigeonholeConstant_inv {a b : ℝ≥0 → ℝ≥0}
    (hab : ∀ ρ : ℝ≥0, 0 < ρ → ρ ≤ 1 → a ρ ≤ b ρ)
    (hratio : (fun ρ => b ρ / a ρ) ≲ fun ρ : ℝ≥0 => ρ⁻¹) :
    (fun ρ => (factoringStep1PigeonholeConstant (a ρ) (b ρ))⁻¹) ⪆
      fun _ : ℝ≥0 => (1 : ℝ≥0) :=
  one_leApprox_inv (X := fun ρ => factoringStep1PigeonholeConstant (a ρ) (b ρ)) (c := 2)
    (factoringStep1PigeonholeConstant_leApprox_one hratio) (by norm_num)
    fun ρ hρ hρ1 => two_le_factoringStep1PigeonholeConstant (hab ρ hρ hρ1)

end Kakeya

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [DecidableEq κ]

/-- The total volume `A j = ∑_{i ∈ u, F.parent i = j} |F.innerBody i|` of a factor-family fiber
over the block `j`, taken inside `u`.

The blocks that still meet `u` -- the set `t₀` of the blueprint statements
`lem:factoringStep1FiberPigeonhole` and `lem:factoringStep1Pigeonhole` -- are the members of the
image `u.image F.parent`. -/
noncomputable def fiberVolume (F : FactorFamily E ι κ) (u : Finset ι) (j : κ) : ℝ≥0∞ :=
  ∑ i ∈ {i ∈ u | F.parent i = j}, volume (F.innerBody i).carrier

/-- The defining finite-sum formula for a fiber carrier volume. -/
theorem fiberVolume_eq_sum (F : FactorFamily E ι κ) (u : Finset ι) (j : κ) :
    fiberVolume F u j =
      ∑ i ∈ {i ∈ u | F.parent i = j}, volume (F.innerBody i).carrier := by
  rw [fiberVolume]

/-- **Fiber pigeonholing: comparable fiber volumes at a logarithmic cost** (blueprint
`lem:factoringStep1FiberPigeonhole`).

Let `F` be a factor family. If all the nonempty fiber volumes `fiberVolume F u j`, for
`j ∈ u.image F.parent`, lie in `[a, b]` with `0 < a`, then a subset `t'` of the blocks can be
selected so that the part of `u` lying over `t'` is a `C(a, b)⁻¹` refinement of `F.innerBody`
on `u` and the surviving fiber volumes are comparable up to a factor `2`. If that family has
positive shading mass, then `t'` is nonempty.
No relation between `a` and `b` is assumed.

The blocks are taken to be the image `u.image F.parent` rather than `F.outerSet`; this is what
makes the refinement inequality available without a hypothesis relating the two. -/
theorem exists_isCRefinement_fiberVolume_comparable
    (F : FactorFamily E ι κ) {u : Finset ι} {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ u.image F.parent, fiberVolume F u j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    ∃ t' ⊆ u.image F.parent,
      IsCRefinement {i ∈ u | F.parent i ∈ t'} F.innerBody u F.innerBody
          (factoringStep1FiberPigeonholeConstant a b)⁻¹ ∧
        (∀ j ∈ t', ∀ j' ∈ t',
          fiberVolume F {i ∈ u | F.parent i ∈ t'} j
            ≤ 2 * fiberVolume F {i ∈ u | F.parent i ∈ t'} j') ∧
        (0 < ∑ i ∈ u, volume (F.innerBody i).shade → t'.Nonempty) := by
  -- Weight: total shading volume of each fiber block
  let w : κ → ℝ≥0∞ := fun j ↦
    ∑ i ∈ {i ∈ u | F.parent i = j}, volume (F.innerBody i).shade
  -- Every index in `u` maps into `u.image F.parent`.
  have hp_mem_image : ∀ i ∈ u, F.parent i ∈ u.image F.parent := fun i hi ↦
    Finset.mem_image_of_mem F.parent hi
  -- Apply the dyadic pigeonhole lemma `ENNReal.dyadic_pigeonhole₁''` over the index set
  -- `u.image F.parent` with weight `w`, classified quantity `fiberVolume F u`, and bounds `a, b`.
  obtain ⟨t', ht'sub, htotal, hcomp⟩ :=
    ENNReal.dyadic_pigeonhole₁'' (s := u.image F.parent) (w := w) (f := fiberVolume F u) ha hA
  -- `htotal` bounds `(u.image F.parent).sum w` by
  -- `ENNReal.ofReal (1 + Real.logb (2 : ℝ) ((b : ℝ) / a)) * t'.sum w`.
  -- Rewrite the right-hand side using `coe_factoringStep1FiberPigeonholeConstant`.
  have hweight_total :
      (u.image F.parent).sum w
        ≤ (factoringStep1FiberPigeonholeConstant a b : ℝ≥0∞) * t'.sum w := by
    simpa [coe_factoringStep1FiberPigeonholeConstant] using htotal
  -- Use `isCRefinement_filter_mem` with `t₀ := u.image F.parent` and the pigeonhole constant.
  have h_refinement : IsCRefinement {i ∈ u | F.parent i ∈ t'} F.innerBody u F.innerBody
      (factoringStep1FiberPigeonholeConstant a b)⁻¹ := by
    refine isCRefinement_filter_mem (hp := hp_mem_image)
      (K := factoringStep1FiberPigeonholeConstant a b) ?_
    simpa [w] using hweight_total
  have h_selected_nonempty : 0 < ∑ i ∈ u, volume (F.innerBody i).shade → t'.Nonempty := by
    intro hu_pos
    by_contra ht'_nonempty
    have ht'_eq_empty : t' = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht'_nonempty
    have hsum_blocks : (u.image F.parent).sum w =
        ∑ i ∈ u, volume (F.innerBody i).shade := by
      simpa [w] using
        Finset.sum_fiberwise_of_maps_to hp_mem_image
          (fun i ↦ volume (F.innerBody i).shade)
    have hle_zero : ∑ i ∈ u, volume (F.innerBody i).shade ≤ 0 := by
      rw [← hsum_blocks]
      simpa [ht'_eq_empty] using hweight_total
    exact (not_le_of_gt hu_pos) hle_zero
  -- (ii) For `j, j' ∈ t'`, the restricted fiber volumes are equal to the original ones
  -- (`Finset.filter_mem_filter_eq`), so `hcomp` gives the comparability.
  have h_fiber_comp : ∀ j ∈ t', ∀ j' ∈ t',
      fiberVolume F {i ∈ u | F.parent i ∈ t'} j
        ≤ 2 * fiberVolume F {i ∈ u | F.parent i ∈ t'} j' := by
    intro j hj j' hj'
    have h_eq_j : fiberVolume F {i ∈ u | F.parent i ∈ t'} j
        = fiberVolume F u j := by
      unfold fiberVolume
      rw [Finset.filter_mem_filter_eq hj]
    have h_eq_j' : fiberVolume F {i ∈ u | F.parent i ∈ t'} j'
        = fiberVolume F u j' := by
      unfold fiberVolume
      rw [Finset.filter_mem_filter_eq hj']
    rw [h_eq_j, h_eq_j']
    exact hcomp j hj j' hj'
  exact ⟨t', ht'sub, h_refinement, h_fiber_comp, h_selected_nonempty⟩

/-- **The fiberwise decomposition of the total volume** (blueprint `lem:fiberVolumeLeTotal`): the
blocks with a nonempty fiber already exhaust `u`, so their fiber volumes sum to the total volume
of `u`. -/
theorem sum_fiberVolume_eq (F : FactorFamily E ι κ) (u : Finset ι) :
    ∑ j ∈ u.image F.parent, fiberVolume F u j =
      ∑ i ∈ u, volume (F.innerBody i).carrier := by
  calc
    ∑ j ∈ u.image F.parent, fiberVolume F u j
        = ∑ j ∈ u.image F.parent,
            ∑ i ∈ {i ∈ u | F.parent i = j}, volume (F.innerBody i).carrier := by
      simp [fiberVolume]
    _ = ∑ i ∈ u, volume (F.innerBody i).carrier :=
      Finset.sum_fiberwise_of_maps_to
        (fun i hi ↦ Finset.mem_image_of_mem F.parent hi) _

/-- **A fiber volume is at most the total volume** (blueprint `lem:fiberVolumeLeTotal`).

Since `u.image F.parent` is finite, this also bounds its largest fiber volume whenever that set is
nonempty. The total volume on the right is finite, each body being compact. -/
theorem fiberVolume_le_sum (F : FactorFamily E ι κ)
    {u : Finset ι} (hu : u ⊆ F.innerSet) (j : κ) :
    fiberVolume F u j ≤ ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier := by
  have hsub : {i ∈ u | F.parent i = j} ⊆ F.innerSet :=
    Finset.Subset.trans (Finset.filter_subset (fun i ↦ F.parent i = j) u) hu
  calc
    fiberVolume F u j =
        ∑ i ∈ {i ∈ u | F.parent i = j}, volume (F.innerBody i).carrier := rfl
    _ ≤ ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier :=
      Finset.sum_le_sum_of_subset hsub

namespace FactorFamily

/-- The fixed set of outer blocks selected by Step 1 from fiber-volume bounds `a` and `b`.

The choice is noncomputable because the pigeonhole lemma is existential. Once made, it is fixed:
all later Step 1 declarations state properties of this set rather than quantifying over arbitrary
valid selections. -/
noncomputable def step1OuterSet (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      fiberVolume F F.step0.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) : Finset κ :=
  (exists_isCRefinement_fiberVolume_comparable F ha hA).choose

private theorem step1OuterSet_spec (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      fiberVolume F F.step0.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    F.step1OuterSet ha hA ⊆ F.step0.innerSet.image F.parent ∧
      IsCRefinement {i ∈ F.step0.innerSet | F.parent i ∈ F.step1OuterSet ha hA}
        F.innerBody F.step0.innerSet F.innerBody
        (factoringStep1FiberPigeonholeConstant a b)⁻¹ ∧
      (∀ j ∈ F.step1OuterSet ha hA, ∀ j' ∈ F.step1OuterSet ha hA,
        fiberVolume F {i ∈ F.step0.innerSet | F.parent i ∈ F.step1OuterSet ha hA} j
          ≤ 2 * fiberVolume F
            {i ∈ F.step0.innerSet | F.parent i ∈ F.step1OuterSet ha hA} j') ∧
      (0 < ∑ i ∈ F.step0.innerSet, volume (F.innerBody i).shade →
        (F.step1OuterSet ha hA).Nonempty) :=
  (exists_isCRefinement_fiberVolume_comparable F ha hA).choose_spec

/-- **Step 1 of the factoring construction** (blueprint `lem:factoringStep1Pigeonhole`): the
factor family obtained by retaining the fixed outer set `F.step1OuterSet ha hA` and precisely the
Step 0 inner bodies whose parents belong to it.

The inner and outer bodies and the parent map are inherited from `F`; only their finite indexing
sets are restricted. -/
noncomputable def step1' (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      fiberVolume F F.step0.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    FactorFamily E ι κ where
  innerSet := {i ∈ F.step0.innerSet | F.parent i ∈ F.step1OuterSet ha hA}
  innerBody := F.innerBody
  outerSet := F.step1OuterSet ha hA
  outerBody := F.outerBody
  parent := F.parent
  parent_mem := fun _ hi ↦ (Finset.mem_filter.mp hi).2
  inner_le_parent := fun i hi ↦
    F.inner_le_parent i (F.innerSet_step0_subset (Finset.mem_filter.mp hi).1)

/-! ### The fields and properties of the Step 1 family -/

private theorem innerSet_step1'_private (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      fiberVolume F F.step0.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    (F.step1' ha hA).innerSet =
      {i ∈ F.step0.innerSet | F.parent i ∈ F.step1OuterSet ha hA} := rfl

/-- The inner set of `F.step1' ha hA` consists of the Step 0 survivors over its selected blocks. -/
@[simp]
theorem innerSet_step1' (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      fiberVolume F F.step0.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    (F.step1' ha hA).innerSet =
      {i ∈ F.step0.innerSet | F.parent i ∈ F.step1OuterSet ha hA} :=
  innerSet_step1'_private F ha hA

private theorem innerBody_step1'_private (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      fiberVolume F F.step0.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    (F.step1' ha hA).innerBody = F.innerBody := rfl

/-- Step 1 keeps the inner bodies and their shadings unchanged. -/
@[simp]
theorem innerBody_step1' (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      fiberVolume F F.step0.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    (F.step1' ha hA).innerBody = F.innerBody :=
  innerBody_step1'_private F ha hA

private theorem outerSet_step1'_private (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      fiberVolume F F.step0.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    (F.step1' ha hA).outerSet = F.step1OuterSet ha hA := rfl

/-- The outer set of the Step 1 family is the fixed pigeonholed set. -/
@[simp]
theorem outerSet_step1' (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      fiberVolume F F.step0.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    (F.step1' ha hA).outerSet = F.step1OuterSet ha hA :=
  outerSet_step1'_private F ha hA

private theorem outerBody_step1'_private (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      fiberVolume F F.step0.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    (F.step1' ha hA).outerBody = F.outerBody := rfl

/-- Step 1 keeps the outer bodies unchanged. -/
@[simp]
theorem outerBody_step1' (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      fiberVolume F F.step0.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    (F.step1' ha hA).outerBody = F.outerBody :=
  outerBody_step1'_private F ha hA

private theorem parent_step1'_private (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      fiberVolume F F.step0.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    (F.step1' ha hA).parent = F.parent := rfl

/-- Step 1 keeps the parent map unchanged. -/
@[simp]
theorem parent_step1' (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      fiberVolume F F.step0.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    (F.step1' ha hA).parent = F.parent :=
  parent_step1'_private F ha hA

/-- The outer blocks selected by Step 1 all meet the Step 0 inner family. -/
theorem outerSet_step1'_subset_image (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      fiberVolume F F.step0.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    (F.step1' ha hA).outerSet ⊆ F.step0.innerSet.image F.parent :=
  (step1OuterSet_spec F ha hA).1

/-- Every inner body retained by Step 1 has relative shading at least half the fullness of `F`. -/
theorem le_volume_shade_of_mem_innerSet_step1' (F : FactorFamily E ι κ) {a b : ℝ≥0}
    (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      fiberVolume F F.step0.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞))
    {i : ι} (hi : i ∈ (F.step1' ha hA).innerSet) :
    ((2⁻¹ : ℝ≥0) : ℝ≥0∞) * (fullness F.innerSet F.innerBody : ℝ≥0∞)
        * volume (F.innerBody i).carrier
      ≤ volume (F.innerBody i).shade :=
  F.le_volume_shade_of_mem_innerSet_step0 (Finset.mem_filter.mp hi).1

/-- The Step 1 inner set is the disjoint union of its fibers over the selected outer set. -/
theorem disjiUnion_fiber_step1'_eq (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      fiberVolume F F.step0.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    (F.step1' ha hA).outerSet.disjiUnion
        (fun j ↦ {i ∈ F.step0.innerSet | F.parent i = j})
        (Set.pairwiseDisjoint_filter F.parent ((F.step1' ha hA).outerSet : Set κ)
          F.step0.innerSet)
      = (F.step1' ha hA).innerSet := by
  ext i
  simp [Finset.mem_filter]

/-- **Mass retention in Step 1.** The fixed Step 1 family is a
`factoringStep1PigeonholeConstant a b`⁻¹ refinement of the original family. -/
theorem isCRefinement_step1' (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      fiberVolume F F.step0.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    IsCRefinement (F.step1' ha hA).innerSet (F.step1' ha hA).innerBody
      F.innerSet F.innerBody (factoringStep1PigeonholeConstant a b)⁻¹ := by
  have h_fiber := (step1OuterSet_spec F ha hA).2.1
  have h_comp := h_fiber.trans F.isCRefinement_step0
  simpa [factoringStep1PigeonholeConstant_inv] using h_comp

/-- Any two fibers of the fixed Step 1 family have comparable total volume. -/
theorem fiberVolume_step1'_le_two_mul (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      fiberVolume F F.step0.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞))
    {j j' : κ} (hj : j ∈ (F.step1' ha hA).outerSet)
    (hj' : j' ∈ (F.step1' ha hA).outerSet) :
    fiberVolume F (F.step1' ha hA).innerSet j
      ≤ 2 * fiberVolume F (F.step1' ha hA).innerSet j' :=
  (step1OuterSet_spec F ha hA).2.2.1 j hj j' hj'

/-- If the original family has positive shading mass, the fixed Step 1 outer set is nonempty. -/
theorem outerSet_step1'_nonempty (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      fiberVolume F F.step0.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞))
    (hs : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) :
    (F.step1' ha hA).outerSet.Nonempty := by
  apply (step1OuterSet_spec F ha hA).2.2.2
  have hfactor_pos : (0 : ℝ≥0∞) < ((2⁻¹ : ℝ≥0) : ℝ≥0∞) := by positivity
  exact (ENNReal.mul_pos hfactor_pos.ne' hs.ne').trans_le F.isCRefinement_step0.2

end FactorFamily

/-- **A fiber volume dominates one of its members** (blueprint `lem:fiberVolumeLowerBd`).

A block `j` in the image `u.image F.parent` has a nonempty fiber, and
`volume (F.innerBody i).carrier` for `i` in that fiber is one of the nonnegative summands of
`fiberVolume F u j`. Consequently any pointwise lower bound for the volumes of the bodies indexed
by `u` is a lower bound for every fiber volume over `u.image F.parent`. -/
theorem exists_volume_le_fiberVolume (F : FactorFamily E ι κ) (u : Finset ι)
    {j : κ} (hj : j ∈ u.image F.parent) :
    ∃ i ∈ {i ∈ u | F.parent i = j},
      volume (F.innerBody i).carrier ≤ fiberVolume F u j := by
  rcases Finset.mem_image.mp hj with ⟨i, hi, hp_eq⟩
  refine ⟨i, Finset.mem_filter.mpr ⟨hi, hp_eq⟩, ?_⟩
  unfold fiberVolume
  have h_nonneg : ∀ i' ∈ {i' ∈ u | F.parent i' = j},
      0 ≤ volume (F.innerBody i').carrier := by
    intro i' hi'
    positivity
  simpa using Finset.single_le_sum h_nonneg (Finset.mem_filter.mpr ⟨hi, hp_eq⟩)

/-- **The extremal fiber volumes are comparable up to the cardinality** (blueprint
`lem:fiberVolumeRatioBound`).

If the bodies of `𝒱` have volumes comparable to a common positive value `m`, in the explicit form
`m ≤ |V i| ≤ C * m` for `i ∈ s`, then the extremal surviving fiber volumes `a` and `b`
satisfy
`b / a ≤ (∑_{i ∈ s} |V i|) / m ≤ C * |𝒱|`. The blueprint's `≲` is rendered by the explicit
constant `C`.

The conclusion is stated in `ℝ≥0` rather than in `ℝ≥0∞` so that it feeds directly into the
hypothesis `hratio` of `Kakeya.one_leApprox_factoringStep1PigeonholeConstant_inv`, which reads
`b / a ≲ fun ρ => ρ⁻¹` under the convention `ρ = |𝒱|⁻¹`. -/
theorem fiberVolume_ratio_le (F : FactorFamily E ι κ)
    {u : Finset ι} (hu : u ⊆ F.innerSet)
    (ht₀ : (u.image F.parent).Nonempty)
    {m : ℝ≥0∞} (hm : 0 < m)
    (hmin : ∀ i ∈ F.innerSet, m ≤ volume (F.innerBody i).carrier)
    {C : ℝ≥0}
    (hmax : ∀ i ∈ F.innerSet, volume (F.innerBody i).carrier ≤ (C : ℝ≥0∞) * m)
    {a b : ℝ≥0}
    (ha : (a : ℝ≥0∞) = (u.image F.parent).inf' ht₀ (fiberVolume F u))
    (hb : (b : ℝ≥0∞) = (u.image F.parent).sup' ht₀ (fiberVolume F u)) :
    b / a ≤ C * F.innerSet.card := by
  -- m ≤ (a : ℝ≥0∞) because each fiber volume is ≥ m and a is the minimum
  have hm_le_a : m ≤ (a : ℝ≥0∞) := by
    rw [ha]
    apply Finset.le_inf'
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    have hi_s : i ∈ F.innerSet := hu hi
    have hmem : i ∈ {i' ∈ u | F.parent i' = F.parent i} :=
      Finset.mem_filter.mpr ⟨hi, rfl⟩
    have hvol : m ≤ volume (F.innerBody i).carrier := hmin i hi_s
    have hle : volume (F.innerBody i).carrier ≤ fiberVolume F u (F.parent i) := by
      unfold fiberVolume
      have h_nonneg : ∀ x ∈ {i' ∈ u | F.parent i' = F.parent i},
          0 ≤ volume (F.innerBody x).carrier := by
        intro x hx; positivity
      simpa using Finset.single_le_sum h_nonneg hmem
    exact le_trans hvol hle
  -- (a : ℝ≥0∞) is nonzero and finite
  have ha0 : (a : ℝ≥0∞) ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le hm hm_le_a)
  have ha_top : (a : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  -- (b : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (F.innerSet.card : ℝ≥0∞) * m
  have hb_le : (b : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (F.innerSet.card : ℝ≥0∞) * m := by
    rw [hb]
    apply Finset.sup'_le
    intro j hj
    have h1 : fiberVolume F u j ≤ ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier :=
      fiberVolume_le_sum F hu j
    have h2 : ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier
        ≤ (C : ℝ≥0∞) * (F.innerSet.card : ℝ≥0∞) * m := by
      calc
        ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier
            ≤ ∑ i ∈ F.innerSet, (C : ℝ≥0∞) * m :=
          Finset.sum_le_sum fun i hi => hmax i hi
        _ = (F.innerSet.card : ℕ) * ((C : ℝ≥0∞) * m) := by
          simp
        _ = (C : ℝ≥0∞) * (F.innerSet.card : ℝ≥0∞) * m := by
          ring
    exact le_trans h1 h2
  -- (b : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (s.card : ℝ≥0∞) * (a : ℝ≥0∞)
  have hb_le' : (b : ℝ≥0∞)
      ≤ (C : ℝ≥0∞) * (F.innerSet.card : ℝ≥0∞) * (a : ℝ≥0∞) := by
    calc
      (b : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (F.innerSet.card : ℝ≥0∞) * m := hb_le
      _ ≤ (C : ℝ≥0∞) * (F.innerSet.card : ℝ≥0∞) * (a : ℝ≥0∞) :=
        mul_le_mul_of_nonneg_left hm_le_a (by positivity)
  -- apply ENNReal.div_le_iff' to get the division inequality
  have hdiv : (b : ℝ≥0∞) / (a : ℝ≥0∞)
      ≤ (C : ℝ≥0∞) * (F.innerSet.card : ℝ≥0∞) := by
    rw [ENNReal.div_le_iff' ha0 ha_top]
    calc
      (b : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (F.innerSet.card : ℝ≥0∞) * (a : ℝ≥0∞) :=
        hb_le'
      _ = (a : ℝ≥0∞) * ((C : ℝ≥0∞) * (F.innerSet.card : ℝ≥0∞)) := by ring
  -- (a : ℝ≥0) ≠ 0, needed for ENNReal.coe_div
  have ha0' : a ≠ 0 := by
    intro hzero
    apply ha0
    simp [hzero]
  -- transfer to ℝ≥0
  apply ENNReal.coe_le_coe.mp
  rw [ENNReal.coe_div ha0']
  calc
    (b : ℝ≥0∞) / (a : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (F.innerSet.card : ℝ≥0∞) := hdiv
    _ = (C * F.innerSet.card : ℝ≥0∞) := by simp

end ShadedBody

/-! ## Step 1 for a family discretized at a scale `δ` -/


open MeasureTheory Convexity Kakeya
open scoped NNReal ENNReal

namespace Kakeya

/-! ### The explicit bounds at a scale `δ` -/

/-- **The explicit lower bound at scale `δ`** (blueprint `def:step1BoundsAtScale`):
`a(n, δ) = c(n) δ ^ n = δ ^ n / n !`, with `c(n) = Metric.lt_volume_convexHull.c n`.

It is the lower bound of `Convex.le_volume_of_le_scale` for the volume of a single body of the
discretized family, and depends only on the ambient dimension `n` and on the scale `δ`. -/
noncomputable def step1LowerBdAtScale (n : ℕ) (δ : ℝ≥0) : ℝ≥0 :=
  Metric.lt_volume_convexHull.c n * δ ^ n

/-- **The explicit upper bound at scale `δ`** (blueprint `def:step1BoundsAtScale`):
`b(n, N) = 2 ^ n N`.

It is the bound of `ShadedBody.sum_volume_le_card_mul_two_pow_finrank` for the total volume of a
discretized family of cardinality `N`, and depends only on the ambient dimension `n` and on `N`. -/
def step1UpperBdAtScale (n N : ℕ) : ℝ≥0 := 2 ^ n * N

/-- **The explicit lower bound read in `ℝ≥0∞`** (blueprint `lem:step1BoundsAtScaleCoe`), the form
in which it is matched by the volume bound `Convex.le_volume_of_le_scale`. -/
theorem coe_step1LowerBdAtScale (n : ℕ) (δ : ℝ≥0) :
    (step1LowerBdAtScale n δ : ℝ≥0∞)
      = (Metric.lt_volume_convexHull.c n : ℝ≥0∞) * (δ : ℝ≥0∞) ^ n := by
  simp [step1LowerBdAtScale]

/-- **The explicit upper bound read in `ℝ≥0∞`** (blueprint `lem:step1BoundsAtScaleCoe`), the form
in which it is matched by `ShadedBody.sum_volume_le_card_mul_two_pow_finrank`. -/
theorem coe_step1UpperBdAtScale (n N : ℕ) :
    (step1UpperBdAtScale n N : ℝ≥0∞) = 2 ^ n * N := by
  simp [step1UpperBdAtScale]

/-- **The explicit lower bound is positive** (blueprint `lem:step1BoundsAtScalePos`): this is the
hypothesis `0 < a` of `ShadedBody.exists_isCRefinement_fiberVolume_comparable` and
`ShadedBody.FactorFamily.step1'`, asserted in `ℝ≥0` where those ask for it. It depends on the
scale `δ` alone. -/
theorem step1LowerBdAtScale_pos (n : ℕ) {δ : ℝ≥0} (hδ : 0 < δ) : 0 < step1LowerBdAtScale n δ := by
  unfold step1LowerBdAtScale
  exact mul_pos (Metric.lt_volume_convexHull.c_pos n) (pow_pos hδ n)

/-- **The explicit bounds are ordered** (blueprint `lem:step1BoundsAtScaleLe`).

The hypothesis `1 ≤ N` cannot be dropped: at `N = 0` one has `step1UpperBdAtScale n 0 = 0`, which
is smaller than `step1LowerBdAtScale n δ` as soon as `0 < δ`. For a family discretized at scale `δ`
with `s` nonempty both hypotheses are available, `δ ≤ 1` by
`Metric.ethickness.le_of_le_scale_of_subset`. -/
theorem step1LowerBdAtScale_le_step1UpperBdAtScale (n : ℕ) {δ : ℝ≥0} {N : ℕ}
    (hδ : δ ≤ 1) (hN : 1 ≤ N) :
    step1LowerBdAtScale n δ ≤ step1UpperBdAtScale n N :=
  calc
    step1LowerBdAtScale n δ
        = Metric.lt_volume_convexHull.c n * δ ^ n := rfl
    _ ≤ Metric.lt_volume_convexHull.c n * 1 := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity : 0 ≤ Metric.lt_volume_convexHull.c n)
      simpa using pow_le_pow_left' hδ n
    _ ≤ 1 * 1 := by
      have hc : Metric.lt_volume_convexHull.c n ≤ 1 := by
        dsimp [Metric.lt_volume_convexHull.c]
        have hfact : (1 : ℝ≥0) ≤ (n.factorial : ℝ≥0) := by
          exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
        exact inv_le_one_of_one_le₀ hfact
      refine mul_le_mul_of_nonneg_right hc ?_
      positivity
    _ = 1 := by simp
    _ ≤ (2 : ℝ≥0) ^ n := by
      have h2 : (1 : ℝ≥0) ≤ (2 : ℝ≥0) := by norm_num
      simpa [one_pow] using pow_le_pow_left' h2 n
    _ ≤ (2 : ℝ≥0) ^ n * (N : ℝ≥0) := by
      have htemp : (2 : ℝ≥0) ^ n * (1 : ℝ≥0) ≤ (2 : ℝ≥0) ^ n * (N : ℝ≥0) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hN) (by positivity)
      simpa [mul_one] using htemp
    _ = step1UpperBdAtScale n N := rfl

/-! ### The ratio of the explicit bounds and its logarithm -/

/-- **The ratio of the explicit bounds** (blueprint `lem:step1BoundsAtScaleRatio`):
`b / a = 2 ^ n n ! N (δ ^ n)⁻¹` in `ℝ≥0`.

The last factor is deliberately written as the inverse of the natural power `δ ^ n` rather than as
an integer power of `δ`: only that form is matched by the coercion and logarithm lemmas
`Kakeya.coe_step1UpperBdAtScale_div_step1LowerBdAtScale` and
`Kakeya.logb_two_pow_mul_factorial_mul_natCast_mul_inv_pow`.

The hypothesis `0 < δ` is not needed for the identity itself, but is kept so that the signature
matches the lemmas below. -/
theorem step1UpperBdAtScale_div_step1LowerBdAtScale (n N : ℕ) {δ : ℝ≥0} (_hδ : 0 < δ) :
    step1UpperBdAtScale n N / step1LowerBdAtScale n δ
      = 2 ^ n * (n.factorial : ℝ≥0) * N * (δ ^ n)⁻¹ := by
  unfold step1UpperBdAtScale step1LowerBdAtScale
  simp [Metric.lt_volume_convexHull.c, div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm,
    mul_assoc]

/-- **The ratio of the explicit bounds as a real number** (blueprint
`lem:step1BoundsAtScaleRatioCoe`): `Kakeya.step1UpperBdAtScale_div_step1LowerBdAtScale` moved
across the coercion `ℝ≥0 → ℝ`, so that the logarithm can afterwards be taken in `ℝ`. -/
theorem coe_step1UpperBdAtScale_div_step1LowerBdAtScale (n N : ℕ) {δ : ℝ≥0} (hδ : 0 < δ) :
    ((step1UpperBdAtScale n N / step1LowerBdAtScale n δ : ℝ≥0) : ℝ)
      = 2 ^ n * (n.factorial : ℝ) * N * ((δ : ℝ) ^ n)⁻¹ := by
  have h := step1UpperBdAtScale_div_step1LowerBdAtScale n N hδ
  simpa [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_natCast] using
    congrArg (fun (x : ℝ≥0) => (x : ℝ)) h

/-- **The logarithm of a product of four explicit factors** (blueprint
`lem:logbTwoPowFactorialCardScale`):
`log₂ (2 ^ n n ! N (δ ^ n)⁻¹) = n + log₂ (n !) + log₂ N + n log₂ (1 / δ)`.

A statement about real numbers alone: no upper bound on `δ` is used, so it holds also for `1 < δ`,
when the last summand is negative. The hypothesis `1 ≤ N` cannot be dropped: at `N = 0` the
left-hand side is `log₂ 0 = 0` by convention while the right-hand side is not. -/
theorem logb_two_pow_mul_factorial_mul_natCast_mul_inv_pow (n : ℕ) {N : ℕ} (hN : 1 ≤ N)
    {δ : ℝ} (hδ : 0 < δ) :
    Real.logb 2 (2 ^ n * (n.factorial : ℝ) * N * (δ ^ n)⁻¹)
      = n + Real.logb 2 (n.factorial : ℝ) + Real.logb 2 N + n * Real.logb 2 (1 / δ) := by
  have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hfact : (n.factorial : ℝ) ≠ 0 := by
    have : 0 < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
    exact this.ne'
  have hNpos : (N : ℝ) ≠ 0 := by
    have hN0 : N ≠ 0 := Nat.one_le_iff_ne_zero.mp hN
    exact Nat.cast_ne_zero.mpr hN0
  have hprod1 : (2 : ℝ) ^ n * (n.factorial : ℝ) ≠ 0 := mul_ne_zero h2n hfact
  have hprod2 : (2 : ℝ) ^ n * (n.factorial : ℝ) * (N : ℝ) ≠ 0 := mul_ne_zero hprod1 hNpos
  have hdelN : (δ ^ n)⁻¹ ≠ 0 := by
    refine (inv_pos.mpr (pow_pos hδ n)).ne'
  have h_two : (1 : ℝ) < 2 := by norm_num
  calc
    Real.logb 2 ((2 : ℝ) ^ n * (n.factorial : ℝ) * (N : ℝ) * (δ ^ n)⁻¹)
        = Real.logb 2 (((2 : ℝ) ^ n * (n.factorial : ℝ) * (N : ℝ))) + Real.logb 2 ((δ ^ n)⁻¹) := by
      rw [Real.logb_mul hprod2 hdelN]
    _ = (Real.logb 2 ((2 : ℝ) ^ n * (n.factorial : ℝ)) + Real.logb 2 (N : ℝ))
        + Real.logb 2 ((δ ^ n)⁻¹) := by
      rw [Real.logb_mul hprod1 hNpos]
    _ = ((Real.logb 2 ((2 : ℝ) ^ n) + Real.logb 2 ((n.factorial : ℝ))) + Real.logb 2 (N : ℝ))
        + Real.logb 2 ((δ ^ n)⁻¹) := by
      rw [Real.logb_mul h2n hfact]
    _ = ((n * Real.logb 2 (2 : ℝ) + Real.logb 2 ((n.factorial : ℝ))) + Real.logb 2 (N : ℝ))
        + Real.logb 2 ((δ ^ n)⁻¹) := by
      rw [Real.logb_pow (2 : ℝ) (2 : ℝ) n]
    _ = ((n * 1 + Real.logb 2 ((n.factorial : ℝ))) + Real.logb 2 (N : ℝ))
        + Real.logb 2 ((δ ^ n)⁻¹) := by
      rw [Real.logb_self_eq_one h_two]
    _ = ((n + Real.logb 2 ((n.factorial : ℝ))) + Real.logb 2 (N : ℝ))
        + Real.logb 2 ((δ ^ n)⁻¹) := by ring
    _ = (n + Real.logb 2 ((n.factorial : ℝ)) + Real.logb 2 (N : ℝ))
        + Real.logb 2 ((δ ^ n)⁻¹) := by ring
    _ = n + Real.logb 2 ((n.factorial : ℝ)) + Real.logb 2 (N : ℝ)
        + Real.logb 2 ((δ ^ n)⁻¹) := by ring
    _ = n + Real.logb 2 ((n.factorial : ℝ)) + Real.logb 2 (N : ℝ) + (-Real.logb 2 (δ ^ n)) := by
      rw [Real.logb_inv]
    _ = n + Real.logb 2 ((n.factorial : ℝ)) + Real.logb 2 (N : ℝ) + (-(n * Real.logb 2 δ)) := by
      rw [Real.logb_pow (2 : ℝ) δ n]
    _ = n + Real.logb 2 ((n.factorial : ℝ)) + Real.logb 2 (N : ℝ) + n * (-Real.logb 2 δ) := by ring
    _ = n + Real.logb 2 ((n.factorial : ℝ)) + Real.logb 2 (N : ℝ) + n * Real.logb 2 (δ⁻¹) := by
      rw [Real.logb_inv]
    _ = n + Real.logb 2 ((n.factorial : ℝ)) + Real.logb 2 (N : ℝ) + n * Real.logb 2 (1 / δ) := by
      simp

/-- **The logarithm of the ratio of the explicit bounds** (blueprint
`lem:step1BoundsAtScaleLogRatioEq`), the argument of the logarithm being the quotient formed in
`ℝ≥0` and read as a real number. -/
theorem logb_step1UpperBdAtScale_div_step1LowerBdAtScale (n : ℕ) {N : ℕ} (hN : 1 ≤ N)
    {δ : ℝ≥0} (hδ : 0 < δ) :
    Real.logb 2 ((step1UpperBdAtScale n N / step1LowerBdAtScale n δ : ℝ≥0) : ℝ)
      = n + Real.logb 2 (n.factorial : ℝ) + Real.logb 2 N + n * Real.logb 2 (1 / (δ : ℝ)) := by
  rw [coe_step1UpperBdAtScale_div_step1LowerBdAtScale n N hδ]
  apply logb_two_pow_mul_factorial_mul_natCast_mul_inv_pow n hN (δ := (δ : ℝ))
  exact_mod_cast hδ

/-- **The logarithm of the ratio of the explicit bounds is nonnegative** (blueprint
`lem:step1BoundsAtScaleLogRatioNonneg`), by monotonicity of `log₂` at `1` from
`Kakeya.step1LowerBdAtScale_le_step1UpperBdAtScale`. -/
theorem logb_step1UpperBdAtScale_div_step1LowerBdAtScale_nonneg (n : ℕ) {N : ℕ} (hN : 1 ≤ N)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 ≤ Real.logb 2 ((step1UpperBdAtScale n N / step1LowerBdAtScale n δ : ℝ≥0) : ℝ) := by
  have hpos : 0 < step1LowerBdAtScale n δ := step1LowerBdAtScale_pos n hδ
  have hle : step1LowerBdAtScale n δ ≤ step1UpperBdAtScale n N :=
    step1LowerBdAtScale_le_step1UpperBdAtScale n hδ1 hN
  have h_onele : (1 : ℝ≥0) ≤ step1UpperBdAtScale n N / step1LowerBdAtScale n δ := by
    calc
      (1 : ℝ≥0) = (step1LowerBdAtScale n δ) * ((step1LowerBdAtScale n δ)⁻¹ : ℝ≥0) := by
        field_simp [hpos.ne']
      _ ≤ (step1UpperBdAtScale n N) * ((step1LowerBdAtScale n δ)⁻¹ : ℝ≥0) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
      _ = step1UpperBdAtScale n N / step1LowerBdAtScale n δ := rfl
  have h_onele' : (1 : ℝ) ≤ ((step1UpperBdAtScale n N / step1LowerBdAtScale n δ : ℝ≥0) : ℝ) := by
    exact_mod_cast h_onele
  have h_two : (1 : ℝ) < (2 : ℝ) := by norm_num
  exact Real.logb_nonneg h_two h_onele'

/-! ### The loss constant at a scale `δ` -/

/-- **Constant in `ShadedBody.FactorFamily.isCRefinement_step1`** (blueprint
`def:factoringStep1AtScaleConstant`): the loss constant
`Kakeya.factoringStep1PigeonholeConstant` evaluated at the explicit bounds
`Kakeya.step1LowerBdAtScale` and `Kakeya.step1UpperBdAtScale`.

It depends on the ambient dimension `n`, on the cardinality `N` and on the scale `δ`, and on
nothing else; `Kakeya.factoringStep1AtScaleConstant_eq` evaluates it in closed form. The existing
constant `ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C` of `Kakeya/Frostman.lean` has the same
value, but not definitionally: the argument of its logarithm is written with the cardinality cast
to a real and multiplied on the left. -/
@[expose] noncomputable def factoringStep1AtScaleConstant (n N : ℕ) (δ : ℝ≥0) : ℝ≥0 :=
  factoringStep1PigeonholeConstant (step1LowerBdAtScale n δ) (step1UpperBdAtScale n N)

/-- **The Step 1 constant at scale `δ` is the pigeonhole constant of the explicit bounds**, the
unfolding lemma for `Kakeya.factoringStep1AtScaleConstant`. It is stated because the body of
that definition is not exposed across the module boundary. -/
theorem factoringStep1AtScaleConstant_def (n N : ℕ) (δ : ℝ≥0) :
    factoringStep1AtScaleConstant n N δ =
      factoringStep1PigeonholeConstant (step1LowerBdAtScale n δ)
        (step1UpperBdAtScale n N) := rfl

/-- **Closed form of the constant at scale `δ`** (blueprint `lem:step1ConstantAtScaleEq`):
`C(n, N, δ) = 2 (1 + n + log₂ (n !) + log₂ N + n log₂ (1 / δ))₊` in `ℝ≥0`.

The positive part is what makes the right-hand side an element of `ℝ≥0`, and it is also what makes
the identity hold with no upper bound on `δ`: for `1 < δ` both sides may be truncated to `0`. That
under the further hypothesis `δ ≤ 1` it does not truncate is the content of
`Kakeya.coe_factoringStep1AtScaleConstant`. -/
theorem factoringStep1AtScaleConstant_eq (n : ℕ) {N : ℕ} (hN : 1 ≤ N) {δ : ℝ≥0}
    (hδ : 0 < δ) :
    factoringStep1AtScaleConstant n N δ
      = 2 * Real.toNNReal (1 + n + Real.logb 2 (n.factorial : ℝ) + Real.logb 2 N
          + n * Real.logb 2 (1 / (δ : ℝ))) := by
  unfold factoringStep1AtScaleConstant factoringStep1PigeonholeConstant
    factoringStep1FiberPigeonholeConstant
  have h_logb : Real.logb 2 ((step1UpperBdAtScale n N : ℝ) / (step1LowerBdAtScale n δ : ℝ))
      = n + Real.logb 2 (n.factorial : ℝ) + Real.logb 2 N + n * Real.logb 2 (1 / (δ : ℝ)) := by
    have h_div_coe : ((step1UpperBdAtScale n N / step1LowerBdAtScale n δ : ℝ≥0) : ℝ)
        = (step1UpperBdAtScale n N : ℝ) / (step1LowerBdAtScale n δ : ℝ) := by
      simp
    calc
      Real.logb 2 ((step1UpperBdAtScale n N : ℝ) / (step1LowerBdAtScale n δ : ℝ))
          = Real.logb 2 (((step1UpperBdAtScale n N / step1LowerBdAtScale n δ : ℝ≥0) : ℝ)) := by
        rw [h_div_coe]
      _ = n + Real.logb 2 (n.factorial : ℝ) + Real.logb 2 N + n * Real.logb 2 (1 / (δ : ℝ)) :=
        logb_step1UpperBdAtScale_div_step1LowerBdAtScale n hN hδ
  calc
    factoringStep1PigeonholeConstant (step1LowerBdAtScale n δ) (step1UpperBdAtScale n N)
        = 2 * Real.toNNReal (1 + Real.logb 2 ((step1UpperBdAtScale n N : ℝ)
          / (step1LowerBdAtScale n δ : ℝ))) :=
      rfl
    _ = 2 * Real.toNNReal (1 + (n + Real.logb 2 (n.factorial : ℝ) + Real.logb 2 N
          + n * Real.logb 2 (1 / (δ : ℝ)))) := by rw [h_logb]
    _ = 2 * Real.toNNReal (1 + n + Real.logb 2 (n.factorial : ℝ) + Real.logb 2 N
          + n * Real.logb 2 (1 / (δ : ℝ))) := by
      congr 1
      ring_nf

/-- **The constant at scale `δ` as a real number** (blueprint `lem:step1ConstantAtScaleCoe`):
`↑(C (n, N, δ)) = 2 (1 + n + log₂ (n !) + log₂ N + n log₂ (1 / δ))`.

It is the coercion `ℝ≥0 → ℝ` which licenses writing the right-hand side without the positive part
carried by the `ℝ≥0`-valued `Kakeya.factoringStep1AtScaleConstant_eq`, legitimate because the
bracket is at least `1` under the hypotheses `0 < δ ≤ 1` and `1 ≤ N`. -/
theorem coe_factoringStep1AtScaleConstant (n : ℕ) {N : ℕ} (hN : 1 ≤ N) {δ : ℝ≥0}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (factoringStep1AtScaleConstant n N δ : ℝ)
      = 2 * (1 + n + Real.logb 2 (n.factorial : ℝ) + Real.logb 2 N
          + n * Real.logb 2 (1 / (δ : ℝ))) := by
  have h_nonneg : 0 ≤ 1 + n + Real.logb 2 (n.factorial : ℝ) + Real.logb 2 N
      + n * Real.logb 2 (1 / (δ : ℝ)) := by
    have hlog_nonneg :
        0 ≤ Real.logb 2 ((step1UpperBdAtScale n N / step1LowerBdAtScale n δ : ℝ≥0) : ℝ) :=
      logb_step1UpperBdAtScale_div_step1LowerBdAtScale_nonneg n hN hδ hδ1
    have hlog : Real.logb 2 ((step1UpperBdAtScale n N / step1LowerBdAtScale n δ : ℝ≥0) : ℝ)
        = n + Real.logb 2 (n.factorial : ℝ) + Real.logb 2 N + n * Real.logb 2 (1 / (δ : ℝ)) :=
      logb_step1UpperBdAtScale_div_step1LowerBdAtScale n hN hδ
    rw [hlog] at hlog_nonneg
    nlinarith
  calc
    (factoringStep1AtScaleConstant n N δ : ℝ)
        = (2 * Real.toNNReal (1 + n + Real.logb 2 (n.factorial : ℝ) + Real.logb 2 N
            + n * Real.logb 2 (1 / (δ : ℝ))) : ℝ) := by
      exact_mod_cast factoringStep1AtScaleConstant_eq n hN hδ
    _ = (2 : ℝ) * (Real.toNNReal (1 + n + Real.logb 2 (n.factorial : ℝ) + Real.logb 2 N
        + n * Real.logb 2 (1 / (δ : ℝ))) : ℝ) := by simp
    _ = (2 : ℝ) * (1 + n + Real.logb 2 (n.factorial : ℝ) + Real.logb 2 N
        + n * Real.logb 2 (1 / (δ : ℝ))) := by rw [Real.coe_toNNReal _ h_nonneg]
    _ = 2 * (1 + n + Real.logb 2 (n.factorial : ℝ) + Real.logb 2 N
        + n * Real.logb 2 (1 / (δ : ℝ))) := by norm_num

end Kakeya

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [DecidableEq κ]

/-! ### Step 1 for a family discretized at a scale `δ`

The predicate `F.InnerIsDiscretizedAtScale δ` bundles "`𝒱` is discretized at scale `δ`" (blueprint
`def:scaleDeltaFamily`) together with localization of the outer bodies, with `N = s.card`. This
section uses its inherited inner-family fields. Under them the fiber volumes are trapped between
the closed-form bounds `Kakeya.step1LowerBdAtScale` and `Kakeya.step1UpperBdAtScale`, so
`ShadedBody.FactorFamily.step1` needs no bounds from its caller. Positivity of `δ` remains a
separate hypothesis. -/

omit [DecidableEq κ] in
/-- **Total volume at scale `δ`** (blueprint `lem:sumVolumeLeCardAtScale`): bounding each carrier
by the volume of the unit closed ball over the `N = s.card` indices of `s` bounds the total volume
of a discretized family by `N 2 ^ n`; in particular it is finite. -/
theorem sum_volume_le_card_mul_two_pow_finrank (F : FactorFamily E ι κ)
    (h₁ : ∀ i ∈ F.innerSet, (F.innerBody i).carrier ⊆ Metric.closedBall 0 1) :
    ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier
      ≤ F.innerSet.card * 2 ^ Module.finrank ℝ E :=
  calc
    ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier
        ≤ ∑ i ∈ F.innerSet, (2 ^ Module.finrank ℝ E : ℝ≥0∞) :=
      Finset.sum_le_sum fun i hi => by
        exact (measure_mono (h₁ i hi)).trans volume_closedBall_le_two_pow_finrank
    _ = F.innerSet.card * (2 ^ Module.finrank ℝ E : ℝ≥0∞) := by simp

open Classical in
/-- **The fiber volumes at scale `δ` are trapped between the explicit bounds** (blueprint
`lem:step1FiberVolumeBoundsAtScale`): this is the hypothesis `hA` of
`ShadedBody.exists_isCRefinement_fiberVolume_comparable` and
`ShadedBody.FactorFamily.step1'`, with the closed-form bounds
`Kakeya.step1LowerBdAtScale` and `Kakeya.step1UpperBdAtScale`.

The lower bound comes from `ShadedBody.exists_volume_le_fiberVolume` together with
`Convex.le_volume_of_le_scale`, the upper one from `ShadedBody.fiberVolume_le_sum` together with
`ShadedBody.sum_volume_le_card_mul_two_pow_finrank`. The remaining hypothesis `0 < a` of those
lemmas is `Kakeya.step1LowerBdAtScale_pos`, which needs nothing beyond `0 < δ`. -/
theorem fiberVolume_mem_Icc_step1BdAtScale [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0}
    (hdisc : F.InnerIsDiscretizedAtScale δ)
    {u : Finset ι} (hu : u ⊆ F.innerSet) {j : κ}
    (hj : j ∈ u.image F.parent) :
    fiberVolume F u j ∈ Set.Icc
      ((step1LowerBdAtScale (Module.finrank ℝ E) δ : ℝ≥0) : ℝ≥0∞)
      ((step1UpperBdAtScale (Module.finrank ℝ E) F.innerSet.card : ℝ≥0) : ℝ≥0∞) := by
  rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
  have hi_s : i ∈ F.innerSet := hu hi
  have hconvex : Convex ℝ ((F.innerBody i).carrier) := (F.innerBody i).convex
  have h_vol_le :
      volume (F.innerBody i).carrier ≤ fiberVolume F u (F.parent i) := by
    have hmem : i ∈ {i' ∈ u | F.parent i' = F.parent i} :=
      Finset.mem_filter.mpr ⟨hi, rfl⟩
    unfold fiberVolume
    have h_nonneg :
        ∀ x ∈ {i' ∈ u | F.parent i' = F.parent i},
          0 ≤ volume (F.innerBody x).carrier := by
      intro x _hx
      positivity
    simpa using Finset.single_le_sum h_nonneg hmem
  have h_scale : (δ : ℝ≥0∞) ≤ Metric.ethickness.scale ℝ ((F.innerBody i).carrier) :=
    hdisc.le_scale i hi_s
  have h_vol_lower :
      (step1LowerBdAtScale (Module.finrank ℝ E) δ : ℝ≥0∞)
        ≤ volume (F.innerBody i).carrier := by
    calc
      (step1LowerBdAtScale (Module.finrank ℝ E) δ : ℝ≥0∞)
          = (Metric.lt_volume_convexHull.c (Module.finrank ℝ E) : ℝ≥0∞)
            * (δ : ℝ≥0∞) ^ Module.finrank ℝ E := by
        rw [coe_step1LowerBdAtScale]
      _ ≤ volume (F.innerBody i).carrier :=
        hconvex.le_volume_of_le_scale h_scale
  have h_lower : (step1LowerBdAtScale (Module.finrank ℝ E) δ : ℝ≥0∞)
      ≤ fiberVolume F u (F.parent i) :=
    le_trans h_vol_lower h_vol_le
  have h_volume_total : ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier
      ≤ F.innerSet.card * (2 ^ Module.finrank ℝ E : ℝ≥0∞) := by
    calc
      ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier
          ≤ F.innerSet.card * 2 ^ Module.finrank ℝ E :=
        sum_volume_le_card_mul_two_pow_finrank F hdisc.subset_unitBall
      _ = F.innerSet.card * (2 ^ Module.finrank ℝ E : ℝ≥0∞) := by simp
  have h_fiber_upper :
      fiberVolume F u (F.parent i)
        ≤ (step1UpperBdAtScale (Module.finrank ℝ E) F.innerSet.card : ℝ≥0∞) := by
    calc
      fiberVolume F u (F.parent i)
          ≤ ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier :=
        fiberVolume_le_sum F hu (F.parent i)
      _ ≤ F.innerSet.card * (2 ^ Module.finrank ℝ E : ℝ≥0∞) := h_volume_total
      _ = (step1UpperBdAtScale (Module.finrank ℝ E) F.innerSet.card : ℝ≥0∞) := by
        rw [coe_step1UpperBdAtScale, mul_comm]
  exact Set.mem_Icc.mpr ⟨h_lower, h_fiber_upper⟩

namespace FactorFamily

/-- The Step 0 fiber volumes satisfy the closed-form bounds used to construct Step 1 at scale
`δ`. -/
theorem step1AtScale_fiberVolume_mem_Icc [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0}
    (hdisc : F.InnerIsDiscretizedAtScale δ) :
    ∀ j ∈ F.step0.innerSet.image F.parent,
      fiberVolume F F.step0.innerSet j ∈
        Set.Icc ((step1LowerBdAtScale (Module.finrank ℝ E) δ : ℝ≥0) : ℝ≥0∞)
          ((step1UpperBdAtScale (Module.finrank ℝ E) F.innerSet.card : ℝ≥0) : ℝ≥0∞) :=
  fun _j hj ↦
    fiberVolume_mem_Icc_step1BdAtScale F hdisc F.innerSet_step0_subset hj

/-- **Step 1 at scale `δ`** (blueprint `cor:factoringStep1AtScale`): the fixed Step 1
subfamily obtained using the closed-form bounds
`step1LowerBdAtScale (finrank ℝ E) δ` and
`step1UpperBdAtScale (finrank ℝ E) F.innerSet.card`.

The lower ethickness hypothesis is part of every downstream application of GWZ Proposition 5.1.
It makes the lower fiber-volume bound positive and makes the Step 1 loss a polylogarithmic
function of `δ⁻¹`, which is an allowed implicit dependence in those applications. -/
noncomputable def step1 [Nontrivial E] (F : FactorFamily E ι κ) {δ : ℝ≥0}
    (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) :
    FactorFamily E ι κ :=
  F.step1' (step1LowerBdAtScale_pos (Module.finrank ℝ E) hδ)
    (step1AtScale_fiberVolume_mem_Icc F hdisc)

private theorem innerSet_step1_private [Nontrivial E] (F : FactorFamily E ι κ)
    {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) :
    (F.step1 hδ hdisc).innerSet =
      {i ∈ F.step0.innerSet | F.parent i ∈ (F.step1 hδ hdisc).outerSet} := rfl

/-- The inner set of the at-scale Step 1 family consists of the Step 0 survivors over its fixed
outer set. -/
@[simp]
theorem innerSet_step1 [Nontrivial E] (F : FactorFamily E ι κ) {δ : ℝ≥0}
    (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) :
    (F.step1 hδ hdisc).innerSet =
      {i ∈ F.step0.innerSet | F.parent i ∈ (F.step1 hδ hdisc).outerSet} :=
  innerSet_step1_private F hδ hdisc

private theorem innerBody_step1_private [Nontrivial E] (F : FactorFamily E ι κ)
    {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) :
    (F.step1 hδ hdisc).innerBody = F.innerBody := rfl

/-- At-scale Step 1 keeps the inner bodies and their shadings unchanged. -/
@[simp]
theorem innerBody_step1 [Nontrivial E] (F : FactorFamily E ι κ) {δ : ℝ≥0}
    (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) :
    (F.step1 hδ hdisc).innerBody = F.innerBody :=
  innerBody_step1_private F hδ hdisc

private theorem outerBody_step1_private [Nontrivial E] (F : FactorFamily E ι κ)
    {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) :
    (F.step1 hδ hdisc).outerBody = F.outerBody := rfl

/-- At-scale Step 1 keeps the outer bodies unchanged. -/
@[simp]
theorem outerBody_step1 [Nontrivial E] (F : FactorFamily E ι κ) {δ : ℝ≥0}
    (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) :
    (F.step1 hδ hdisc).outerBody = F.outerBody :=
  outerBody_step1_private F hδ hdisc

private theorem parent_step1_private [Nontrivial E] (F : FactorFamily E ι κ)
    {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) :
    (F.step1 hδ hdisc).parent = F.parent := rfl

/-- At-scale Step 1 keeps the parent map unchanged. -/
@[simp]
theorem parent_step1 [Nontrivial E] (F : FactorFamily E ι κ) {δ : ℝ≥0}
    (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) :
    (F.step1 hδ hdisc).parent = F.parent :=
  parent_step1_private F hδ hdisc

/-- Every outer block selected by at-scale Step 1 meets the Step 0 inner family. -/
theorem outerSet_step1_subset_image [Nontrivial E] (F : FactorFamily E ι κ)
    {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) :
    (F.step1 hδ hdisc).outerSet ⊆ F.step0.innerSet.image F.parent :=
  F.outerSet_step1'_subset_image _ _

/-- Every inner body retained by at-scale Step 1 has relative shading at least half the fullness
of the original family. -/
theorem le_volume_shade_of_mem_innerSet_step1 [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ)
    {i : ι} (hi : i ∈ (F.step1 hδ hdisc).innerSet) :
    ((2⁻¹ : ℝ≥0) : ℝ≥0∞) * (fullness F.innerSet F.innerBody : ℝ≥0∞)
        * volume (F.innerBody i).carrier
      ≤ volume (F.innerBody i).shade :=
  F.le_volume_shade_of_mem_innerSet_step1' _ _ hi

/-- The at-scale Step 1 inner set is the disjoint union of its selected fibers. -/
theorem disjiUnion_fiber_step1_eq [Nontrivial E] (F : FactorFamily E ι κ)
    {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) :
    (F.step1 hδ hdisc).outerSet.disjiUnion
        (fun j ↦ {i ∈ F.step0.innerSet | F.parent i = j})
        (Set.pairwiseDisjoint_filter F.parent
          ((F.step1 hδ hdisc).outerSet : Set κ) F.step0.innerSet)
      = (F.step1 hδ hdisc).innerSet :=
  F.disjiUnion_fiber_step1'_eq _ _

/-- **Mass retention at scale `δ`.** The fixed at-scale Step 1 family is a
`factoringStep1AtScaleConstant (finrank ℝ E) F.innerSet.card δ`⁻¹ refinement of `F`. -/
theorem isCRefinement_step1 [Nontrivial E] (F : FactorFamily E ι κ)
    {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) :
    IsCRefinement (F.step1 hδ hdisc).innerSet
      (F.step1 hδ hdisc).innerBody F.innerSet F.innerBody
      (factoringStep1AtScaleConstant (Module.finrank ℝ E) F.innerSet.card δ)⁻¹ :=
  F.isCRefinement_step1' _ _

/-- Any two fibers of the fixed at-scale Step 1 family have comparable total volume. -/
theorem fiberVolume_step1_le_two_mul [Nontrivial E] (F : FactorFamily E ι κ)
    {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ)
    {j j' : κ} (hj : j ∈ (F.step1 hδ hdisc).outerSet)
    (hj' : j' ∈ (F.step1 hδ hdisc).outerSet) :
    fiberVolume F (F.step1 hδ hdisc).innerSet j
      ≤ 2 * fiberVolume F (F.step1 hδ hdisc).innerSet j' :=
  F.fiberVolume_step1'_le_two_mul _ _ hj hj'

/-- If the original family has positive shading mass, the fixed at-scale Step 1 outer set is
nonempty. -/
theorem outerSet_step1_nonempty [Nontrivial E] (F : FactorFamily E ι κ)
    {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ)
    (hs : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) :
    (F.step1 hδ hdisc).outerSet.Nonempty :=
  F.outerSet_step1'_nonempty _ _ hs

end FactorFamily

end ShadedBody
