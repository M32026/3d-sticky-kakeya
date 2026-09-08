/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.CThickening
public import Kakeya.Factoring.Productive
public import Kakeya.Factoring.Step1

/-! # The carrier-weighted first factoring step

This file supplies the version of Step 1 used by the corrected condition of GWZ Proposition
5.1.  A block is classified by the quotient of its total inner carrier volume by the volume of
the enlarged outer carrier.  Thus the selected blocks have comparable *normalized* fiber volume;
no comparison between the volumes of different outer bodies is assumed.
-/

public section

open MeasureTheory Convexity Kakeya
open scoped NNReal ENNReal

namespace Kakeya

/-- Lower endpoint used by carrier-weighted Step 1. -/
@[expose] public noncomputable def weightedStep1LowerBd (n N : ℕ) : ℝ≥0 :=
  (Metric.volume_comparison.C n * 2 ^ N)⁻¹

/-- Upper endpoint used by carrier-weighted Step 1. -/
@[expose] public noncomputable def weightedStep1UpperBd (M : ℕ) : ℝ≥0 := M

/-- The lower endpoint for carrier-weighted Step 1 is positive. -/
theorem weightedStep1LowerBd_pos (n N : ℕ) : 0 < weightedStep1LowerBd n N := by
  simp only [weightedStep1LowerBd]
  positivity

end Kakeya

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [DecidableEq κ]

/-- The volume of the outer carrier enlarged by its own shortest thickness. -/
@[expose] public noncomputable def enlargedOuterVolume
    (F : FactorFamily E ι κ) (j : κ) : ℝ≥0∞ :=
  volume ((F.outerBody j).cthickening (F.outerBody j).scale).carrier

omit [DecidableEq κ] in
/-- The defining formula for the enlarged outer carrier volume. -/
theorem enlargedOuterVolume_eq (F : FactorFamily E ι κ) (j : κ) :
    enlargedOuterVolume F j =
      volume ((F.outerBody j).cthickening (F.outerBody j).scale).carrier := rfl

/-- The fiber carrier volume normalized by the corresponding enlarged outer carrier. -/
public noncomputable def normalizedFiberVolume
    (F : FactorFamily E ι κ) (u : Finset ι) (j : κ) : ℝ≥0∞ :=
  fiberVolume F u j / enlargedOuterVolume F j

omit [DecidableEq κ] in
/-- The enlarged outer carrier has finite volume. -/
theorem enlargedOuterVolume_ne_top (F : FactorFamily E ι κ) (j : κ) :
    enlargedOuterVolume F j ≠ ⊤ := by
  exact ((F.outerBody j).cthickening (F.outerBody j).scale).isCompact.measure_ne_top

/-- Every used outer block has positive enlarged-carrier volume. -/
theorem enlargedOuterVolume_pos [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) {u : Finset ι} (hu : u ⊆ F.innerSet)
    {j : κ} (hj : j ∈ u.image F.parent) :
    0 < enlargedOuterVolume F j := by
  obtain ⟨i, hiu, rfl⟩ := Finset.mem_image.mp hj
  have hi : i ∈ F.innerSet := hu hiu
  have hVi : 0 < volume (F.innerBody i).carrier := by
    refine lt_of_lt_of_le ?_ (hdisc.volume_innerBody_mem_Icc hi).1
    positivity
  apply hVi.trans_le
  apply measure_mono
  exact (F.inner_le_parent i hi).trans
    (ConvexSpaceBody.self_le_cthickening (F.outerBody (F.parent i))
      (F.outerBody (F.parent i)).scale)

/-- The enlarged outer volume is controlled by one complete fiber when the outer/inner volume
ratio exponent is supplied explicitly. -/
theorem enlargedOuterVolume_le_mul_fiberVolume [Nontrivial E]
    (F : FactorFamily E ι κ) {u : Finset ι} (hu : u ⊆ F.innerSet) {N : ℕ}
    (hN : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
      volume (F.outerBody j).carrier ≤ 2 ^ N * volume (F.innerBody i).carrier)
    {j : κ} (hj : j ∈ u.image F.parent) :
    enlargedOuterVolume F j ≤
      (Metric.volume_comparison.C (Module.finrank ℝ E) : ℝ≥0∞) * 2 ^ N *
        fiberVolume F u j := by
  obtain ⟨i, hiu, hp⟩ := Finset.mem_image.mp hj
  have hi : i ∈ F.innerSet := hu hiu
  have hjF : j ∈ F.outerSet := by simpa [hp] using F.parent_mem i hi
  have hifiber : i ∈ F.fiber j := by
    exact (mem_factorFamily_fiber_iff F j i).2 ⟨hi, hp⟩
  have hViA : volume (F.innerBody i).carrier ≤ fiberVolume F u j := by
    rw [fiberVolume_eq_sum]
    have himem : i ∈ {i ∈ u | F.parent i = j} := by
      simp only [Finset.mem_filter]
      exact ⟨hiu, hp⟩
    exact Finset.single_le_sum
      (fun q _ ↦ (zero_le : (0 : ℝ≥0∞) ≤ volume (F.innerBody q).carrier)) himem
  calc
    enlargedOuterVolume F j
        ≤ (Metric.volume_comparison.C (Module.finrank ℝ E) : ℝ≥0∞) *
            volume (F.outerBody j).carrier := by
      let r : ℝ≥0 := Real.toNNReal (F.outerBody j).scale
      have hr : (r : ℝ) = (F.outerBody j).scale := by
        apply Real.coe_toNNReal
        dsimp only [ConvexSpaceBody.scale]
        exact Metric.thickness_nonneg _ _
      rw [enlargedOuterVolume, ← hr]
      exact ConvexSpaceBody.volume_cthickening_le (F.outerBody j) r hr.le
    _ ≤ (Metric.volume_comparison.C (Module.finrank ℝ E) : ℝ≥0∞) *
          (2 ^ N * volume (F.innerBody i).carrier) := by
      gcongr
      exact hN j hjF i hifiber
    _ ≤ (Metric.volume_comparison.C (Module.finrank ℝ E) : ℝ≥0∞) * 2 ^ N *
          fiberVolume F u j := by
      rw [mul_assoc]
      gcongr

/-- A complete fiber contains at most one enlarged-outer-volume contribution per inner index. -/
theorem fiberVolume_le_card_mul_enlargedOuterVolume
    (F : FactorFamily E ι κ) {u : Finset ι} (hu : u ⊆ F.innerSet) (j : κ) :
    fiberVolume F u j ≤ (u.card : ℝ≥0∞) * enlargedOuterVolume F j := by
  rw [fiberVolume_eq_sum]
  calc
    ∑ i ∈ {i ∈ u | F.parent i = j}, volume (F.innerBody i).carrier
        ≤ ∑ _i ∈ {i ∈ u | F.parent i = j}, enlargedOuterVolume F j := by
      apply Finset.sum_le_sum
      intro i hi
      have hiu := (Finset.mem_filter.mp hi).1
      have hp := (Finset.mem_filter.mp hi).2
      have hiF : i ∈ F.innerSet := hu hiu
      apply measure_mono
      exact (F.inner_le_parent i hiF).trans (by simpa [hp] using
        (ConvexSpaceBody.self_le_cthickening (F.outerBody j) (F.outerBody j).scale)
        )
    _ = ({i ∈ u | F.parent i = j}.card : ℝ≥0∞) * enlargedOuterVolume F j := by
      simp
    _ ≤ (u.card : ℝ≥0∞) * enlargedOuterVolume F j := by
      gcongr
      exact Finset.filter_subset _ _

/-- Explicit bounds for every nonempty normalized fiber. -/
theorem normalizedFiberVolume_mem_Icc [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) {u : Finset ι} (hu : u ⊆ F.innerSet) {N : ℕ}
    (hN : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
      volume (F.outerBody j).carrier ≤ 2 ^ N * volume (F.innerBody i).carrier)
    {j : κ} (hj : j ∈ u.image F.parent) :
    normalizedFiberVolume F u j ∈
      Set.Icc
        ((weightedStep1LowerBd (Module.finrank ℝ E) N : ℝ≥0) : ℝ≥0∞)
        ((weightedStep1UpperBd u.card : ℝ≥0) : ℝ≥0∞) := by
  have hB0 := (enlargedOuterVolume_pos F hδ hdisc hu hj).ne'
  have hBtop := enlargedOuterVolume_ne_top F j
  constructor
  · rw [normalizedFiberVolume]
    apply (ENNReal.le_div_iff_mul_le (Or.inl hB0) (Or.inl hBtop)).2
    have hcross := enlargedOuterVolume_le_mul_fiberVolume F hu hN hj
    rw [weightedStep1LowerBd]
    norm_cast
    let D : ℝ≥0 := Metric.volume_comparison.C (Module.finrank ℝ E) * (2 ^ N : ℕ)
    have hD0 : D ≠ 0 := by
      apply mul_ne_zero
      · exact (Metric.volume_comparison.C_pos _).ne'
      · positivity
    change ((D⁻¹ : ℝ≥0) : ℝ≥0∞) * enlargedOuterVolume F j ≤ fiberVolume F u j
    rw [ENNReal.coe_inv hD0]
    rw [ENNReal.inv_mul_le_iff (ENNReal.coe_ne_zero.mpr hD0) ENNReal.coe_ne_top]
    have hDcoe : (D : ℝ≥0∞) =
        (Metric.volume_comparison.C (Module.finrank ℝ E) : ℝ≥0∞) * 2 ^ N := by
      dsimp only [D]
      norm_cast
    rw [hDcoe]
    simpa only [mul_assoc] using hcross
  · rw [normalizedFiberVolume]
    apply (ENNReal.div_le_iff hB0 hBtop).2
    simpa [weightedStep1UpperBd] using
      fiberVolume_le_card_mul_enlargedOuterVolume F hu j

/-- Pairwise comparison of normalized fiber volumes, written without division. -/
theorem fiberVolume_mul_enlargedOuterVolume_le_of_normalizedFiberVolume_le [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) {u : Finset ι} (hu : u ⊆ F.innerSet)
    {i j : κ} (hi : i ∈ u.image F.parent) (hj : j ∈ u.image F.parent) (R : ENNReal)
    (hcomp : normalizedFiberVolume F u i ≤ R * normalizedFiberVolume F u j) :
    fiberVolume F u i * enlargedOuterVolume F j ≤
      R * enlargedOuterVolume F i * fiberVolume F u j := by
  have hBi0 := (enlargedOuterVolume_pos F hδ hdisc hu hi).ne'
  have hBj0 := (enlargedOuterVolume_pos F hδ hdisc hu hj).ne'
  have hBitop := enlargedOuterVolume_ne_top F i
  have hBjtop := enlargedOuterVolume_ne_top F j
  simp only [normalizedFiberVolume] at hcomp
  have hright : (fiberVolume F u i / enlargedOuterVolume F i) *
      enlargedOuterVolume F j ≤ R * fiberVolume F u j := by
    calc
      (fiberVolume F u i / enlargedOuterVolume F i) * enlargedOuterVolume F j ≤
          (R * (fiberVolume F u j / enlargedOuterVolume F j)) *
            enlargedOuterVolume F j := by gcongr
      _ = R * fiberVolume F u j := by
        rw [mul_assoc, ENNReal.div_mul_cancel hBj0 hBjtop]
  calc
    fiberVolume F u i * enlargedOuterVolume F j =
        enlargedOuterVolume F i *
          ((fiberVolume F u i / enlargedOuterVolume F i) *
            enlargedOuterVolume F j) := by
      rw [← mul_assoc, mul_comm (enlargedOuterVolume F i),
        ENNReal.div_mul_cancel hBi0 hBitop]
    _ ≤ enlargedOuterVolume F i * (R * fiberVolume F u j) := by gcongr
    _ = R * enlargedOuterVolume F i * fiberVolume F u j := by ring

/-- Weighted Step 1: normalized fiber volumes are made comparable at logarithmic cost.

The pigeonhole weight is the shading mass of a block.  Consequently the selected inner family
is a substantial refinement even though the classified quantity is normalized using an outer
carrier volume. -/
theorem exists_isCRefinement_normalizedFiberVolume_comparable
    (F : FactorFamily E ι κ) {carrierSet shadeSet : Finset ι} {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ shadeSet.image F.parent,
      normalizedFiberVolume F carrierSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    ∃ t' ⊆ shadeSet.image F.parent,
      IsCRefinement {i ∈ shadeSet | F.parent i ∈ t'} F.innerBody shadeSet F.innerBody
          (factoringStep1FiberPigeonholeConstant a b)⁻¹ ∧
        (∀ j ∈ t', ∀ j' ∈ t',
          normalizedFiberVolume F carrierSet j ≤
            2 * normalizedFiberVolume F carrierSet j') ∧
        (0 < ∑ i ∈ shadeSet, volume (F.innerBody i).shade → t'.Nonempty) := by
  let w : κ → ℝ≥0∞ := fun j ↦
    ∑ i ∈ {i ∈ shadeSet | F.parent i = j}, volume (F.innerBody i).shade
  have hp : ∀ i ∈ shadeSet, F.parent i ∈ shadeSet.image F.parent := fun i hi ↦
    Finset.mem_image_of_mem F.parent hi
  obtain ⟨t', ht', htotal, hcomp⟩ :=
    ENNReal.dyadic_pigeonhole₁'' (s := shadeSet.image F.parent) (w := w)
      (f := normalizedFiberVolume F carrierSet) ha hA
  have hweight : (shadeSet.image F.parent).sum w ≤
      (factoringStep1FiberPigeonholeConstant a b : ℝ≥0∞) * t'.sum w := by
    simpa [coe_factoringStep1FiberPigeonholeConstant] using htotal
  have href : IsCRefinement {i ∈ shadeSet | F.parent i ∈ t'} F.innerBody shadeSet F.innerBody
      (factoringStep1FiberPigeonholeConstant a b)⁻¹ := by
    refine isCRefinement_filter_mem (hp := hp)
      (K := factoringStep1FiberPigeonholeConstant a b) ?_
    simpa [w] using hweight
  have hne : 0 < ∑ i ∈ shadeSet, volume (F.innerBody i).shade → t'.Nonempty := by
    intro hu
    by_contra htne
    have htempty : t' = ∅ := Finset.not_nonempty_iff_eq_empty.mp htne
    have hsum : (shadeSet.image F.parent).sum w =
        ∑ i ∈ shadeSet, volume (F.innerBody i).shade := by
      simpa [w] using Finset.sum_fiberwise_of_maps_to hp
        (fun i ↦ volume (F.innerBody i).shade)
    have hz : ∑ i ∈ shadeSet, volume (F.innerBody i).shade ≤ 0 := by
      rw [← hsum]
      simpa [htempty] using hweight
    exact (not_le_of_gt hu) hz
  have hnormalized : ∀ j ∈ t', ∀ j' ∈ t',
      normalizedFiberVolume F carrierSet j ≤
        2 * normalizedFiberVolume F carrierSet j' := by
    exact hcomp
  exact ⟨t', ht', href, hnormalized, hne⟩

namespace FactorFamily

/-- The fixed outer set chosen by carrier-weighted Step 1. -/
public noncomputable def weightedStep1OuterSet
    (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      normalizedFiberVolume F F.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) : Finset κ :=
  (exists_isCRefinement_normalizedFiberVolume_comparable
    F (carrierSet := F.innerSet) (shadeSet := F.step0.innerSet) ha hA).choose

private theorem weightedStep1OuterSet_spec (F : FactorFamily E ι κ) {a b : ℝ≥0}
    (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      normalizedFiberVolume F F.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    F.weightedStep1OuterSet ha hA ⊆ F.step0.innerSet.image F.parent ∧
      IsCRefinement
        {i ∈ F.step0.innerSet | F.parent i ∈ F.weightedStep1OuterSet ha hA}
        F.innerBody F.step0.innerSet F.innerBody
        (factoringStep1FiberPigeonholeConstant a b)⁻¹ ∧
      (∀ j ∈ F.weightedStep1OuterSet ha hA,
        ∀ j' ∈ F.weightedStep1OuterSet ha hA,
          normalizedFiberVolume F F.innerSet j ≤
            2 * normalizedFiberVolume F F.innerSet j') ∧
      (0 < ∑ i ∈ F.step0.innerSet, volume (F.innerBody i).shade →
        (F.weightedStep1OuterSet ha hA).Nonempty) :=
  (exists_isCRefinement_normalizedFiberVolume_comparable
    F (carrierSet := F.innerSet) (shadeSet := F.step0.innerSet) ha hA).choose_spec

/-- The factor family selected by carrier-weighted Step 1. -/
public noncomputable def weightedStep1
    (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      normalizedFiberVolume F F.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    FactorFamily E ι κ where
  innerSet := {i ∈ F.step0.innerSet | F.parent i ∈ F.weightedStep1OuterSet ha hA}
  innerBody := F.innerBody
  outerSet := F.weightedStep1OuterSet ha hA
  outerBody := F.outerBody
  parent := F.parent
  parent_mem := fun _ hi ↦ (Finset.mem_filter.mp hi).2
  inner_le_parent := fun i hi ↦
    F.inner_le_parent i (F.innerSet_step0_subset (Finset.mem_filter.mp hi).1)

private theorem innerSet_weightedStep1_private
    (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      normalizedFiberVolume F F.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    (F.weightedStep1 ha hA).innerSet =
      {i ∈ F.step0.innerSet | F.parent i ∈ F.weightedStep1OuterSet ha hA} := rfl

@[simp]
theorem innerSet_weightedStep1 (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      normalizedFiberVolume F F.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    (F.weightedStep1 ha hA).innerSet =
      {i ∈ F.step0.innerSet | F.parent i ∈ F.weightedStep1OuterSet ha hA} :=
  innerSet_weightedStep1_private F ha hA

private theorem innerBody_weightedStep1_private
    (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      normalizedFiberVolume F F.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    (F.weightedStep1 ha hA).innerBody = F.innerBody := rfl

@[simp]
theorem innerBody_weightedStep1 (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      normalizedFiberVolume F F.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    (F.weightedStep1 ha hA).innerBody = F.innerBody :=
  innerBody_weightedStep1_private F ha hA

private theorem outerBody_weightedStep1_private
    (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      normalizedFiberVolume F F.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    (F.weightedStep1 ha hA).outerBody = F.outerBody := rfl

@[simp]
theorem outerBody_weightedStep1 (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      normalizedFiberVolume F F.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    (F.weightedStep1 ha hA).outerBody = F.outerBody :=
  outerBody_weightedStep1_private F ha hA

private theorem parent_weightedStep1_private
    (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      normalizedFiberVolume F F.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    (F.weightedStep1 ha hA).parent = F.parent := rfl

@[simp]
theorem parent_weightedStep1 (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      normalizedFiberVolume F F.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    (F.weightedStep1 ha hA).parent = F.parent :=
  parent_weightedStep1_private F ha hA

/-- Every block selected by weighted Step 1 meets the Step 0 inner family. -/
theorem outerSet_weightedStep1_subset_image (F : FactorFamily E ι κ) {a b : ℝ≥0}
    (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      normalizedFiberVolume F F.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    (F.weightedStep1 ha hA).outerSet ⊆ F.step0.innerSet.image F.parent :=
  (weightedStep1OuterSet_spec F ha hA).1

/-- Weighted Step 1 retains a named fraction of the original shading mass. -/
theorem isCRefinement_weightedStep1 (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      normalizedFiberVolume F F.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    IsCRefinement (F.weightedStep1 ha hA).innerSet (F.weightedStep1 ha hA).innerBody
      F.innerSet F.innerBody (factoringStep1PigeonholeConstant a b)⁻¹ := by
  have h := (weightedStep1OuterSet_spec F ha hA).2.1
  simpa [factoringStep1PigeonholeConstant_inv] using h.trans F.isCRefinement_step0

/-- The normalized fiber volumes selected by weighted Step 1 are pairwise comparable. -/
theorem normalizedFiberVolume_weightedStep1_le_two_mul
    (F : FactorFamily E ι κ) {a b : ℝ≥0} (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      normalizedFiberVolume F F.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞))
    {j j' : κ} (hj : j ∈ (F.weightedStep1 ha hA).outerSet)
    (hj' : j' ∈ (F.weightedStep1 ha hA).outerSet) :
    normalizedFiberVolume F F.innerSet j ≤
      2 * normalizedFiberVolume F F.innerSet j' :=
  (weightedStep1OuterSet_spec F ha hA).2.2.1 j hj j' hj'

/-- Positive input shading mass forces the weighted Step 1 outer set to be nonempty. -/
theorem outerSet_weightedStep1_nonempty (F : FactorFamily E ι κ) {a b : ℝ≥0}
    (ha : 0 < a)
    (hA : ∀ j ∈ F.step0.innerSet.image F.parent,
      normalizedFiberVolume F F.innerSet j ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞))
    (hs : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) :
    (F.weightedStep1 ha hA).outerSet.Nonempty := by
  apply (weightedStep1OuterSet_spec F ha hA).2.2.2
  have hhalf : (0 : ℝ≥0∞) < ((2⁻¹ : ℝ≥0) : ℝ≥0∞) := by positivity
  exact (ENNReal.mul_pos hhalf.ne' hs.ne').trans_le F.isCRefinement_step0.2

/-- The named loss constant for carrier-weighted Step 1 with an explicit eccentricity exponent. -/
@[expose] public noncomputable def weightedStep1AtScaleConstant (n M N : ℕ) : ℝ≥0 :=
  factoringStep1PigeonholeConstant (weightedStep1LowerBd n N) (weightedStep1UpperBd M)

/-- The carrier-weighted Step 1 loss is positive whenever its named lower endpoint does not
exceed its upper endpoint. -/
theorem weightedStep1AtScaleConstant_pos {n M N : ℕ}
    (h : weightedStep1LowerBd n N ≤ weightedStep1UpperBd M) :
    0 < weightedStep1AtScaleConstant n M N := by
  rw [weightedStep1AtScaleConstant]
  exact lt_of_lt_of_le (by norm_num) (two_le_factoringStep1PigeonholeConstant h)

/-- The complete-fiber normalized volumes satisfy the bounds used by at-scale weighted Step 1. -/
theorem normalizedFiberVolume_mem_Icc_step0Image [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (N : ℕ)
    (hN : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
      volume (F.outerBody j).carrier ≤ 2 ^ N * volume (F.innerBody i).carrier)
    {j : κ} (hj : j ∈ F.step0.innerSet.image F.parent) :
    normalizedFiberVolume F F.innerSet j ∈
      Set.Icc
        ((weightedStep1LowerBd (Module.finrank ℝ E) N : ℝ≥0) : ℝ≥0∞)
        ((weightedStep1UpperBd F.innerSet.card : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  apply normalizedFiberVolume_mem_Icc F hδ hdisc (by rfl) hN
  exact Finset.mem_image_of_mem F.parent (F.innerSet_step0_subset hi)

/-- Carrier-weighted Step 1 instantiated using the explicit outer/inner volume-ratio exponent. -/
public noncomputable def weightedStep1AtScale [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (N : ℕ)
    (hN : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
      volume (F.outerBody j).carrier ≤ 2 ^ N * volume (F.innerBody i).carrier) :
    FactorFamily E ι κ :=
  F.weightedStep1 (weightedStep1LowerBd_pos (Module.finrank ℝ E) N)
    (fun _j hj ↦ normalizedFiberVolume_mem_Icc_step0Image F hδ hdisc N hN hj)

private theorem innerSet_weightedStep1AtScale_private [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (N : ℕ)
    (hN : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
      volume (F.outerBody j).carrier ≤ 2 ^ N * volume (F.innerBody i).carrier) :
    (F.weightedStep1AtScale hδ hdisc N hN).innerSet =
      {i ∈ F.step0.innerSet | F.parent i ∈ (F.weightedStep1AtScale hδ hdisc N hN).outerSet} :=
  rfl

/-- The inner indices selected by carrier-weighted Step 1. -/
@[simp]
theorem innerSet_weightedStep1AtScale [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (N : ℕ)
    (hN : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
      volume (F.outerBody j).carrier ≤ 2 ^ N * volume (F.innerBody i).carrier) :
    (F.weightedStep1AtScale hδ hdisc N hN).innerSet =
      {i ∈ F.step0.innerSet | F.parent i ∈ (F.weightedStep1AtScale hδ hdisc N hN).outerSet} :=
  innerSet_weightedStep1AtScale_private F hδ hdisc N hN

/-- Carrier-weighted Step 1 keeps the inner bodies unchanged. -/
theorem innerBody_weightedStep1AtScale [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (N : ℕ)
    (hN : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
      volume (F.outerBody j).carrier ≤ 2 ^ N * volume (F.innerBody i).carrier) :
    (F.weightedStep1AtScale hδ hdisc N hN).innerBody = F.innerBody := by
  apply innerBody_weightedStep1

/-- Carrier-weighted Step 1 keeps the parent map unchanged. -/
theorem parent_weightedStep1AtScale [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (N : ℕ)
    (hN : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
      volume (F.outerBody j).carrier ≤ 2 ^ N * volume (F.innerBody i).carrier) :
    (F.weightedStep1AtScale hδ hdisc N hN).parent = F.parent := by
  apply parent_weightedStep1

/-- Every block selected by at-scale carrier-weighted Step 1 meets the Step 0 family. -/
theorem outerSet_weightedStep1AtScale_subset_image [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (N : ℕ)
    (hN : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
      volume (F.outerBody j).carrier ≤ 2 ^ N * volume (F.innerBody i).carrier) :
    (F.weightedStep1AtScale hδ hdisc N hN).outerSet ⊆
      F.step0.innerSet.image F.parent := by
  apply outerSet_weightedStep1_subset_image

/-- Positive input shading mass forces the at-scale carrier-weighted Step 1 outer set to be
nonempty. -/
theorem outerSet_weightedStep1AtScale_nonempty [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (N : ℕ)
    (hN : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
      volume (F.outerBody j).carrier ≤ 2 ^ N * volume (F.innerBody i).carrier)
    (hs : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) :
    (F.weightedStep1AtScale hδ hdisc N hN).outerSet.Nonempty := by
  apply outerSet_weightedStep1_nonempty
  exact hs

/-- Carrier-weighted Step 1 retains the named fraction of the original shading mass. -/
theorem isCRefinement_weightedStep1AtScale [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (N : ℕ)
    (hN : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
      volume (F.outerBody j).carrier ≤ 2 ^ N * volume (F.innerBody i).carrier) :
    IsCRefinement (F.weightedStep1AtScale hδ hdisc N hN).innerSet
      (F.weightedStep1AtScale hδ hdisc N hN).innerBody F.innerSet F.innerBody
      (weightedStep1AtScaleConstant (Module.finrank ℝ E) F.innerSet.card N)⁻¹ := by
  apply isCRefinement_weightedStep1

/-- The normalized fiber volumes in carrier-weighted Step 1 are pairwise two-comparable. -/
theorem normalizedFiberVolume_weightedStep1AtScale_le_two_mul [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (N : ℕ)
    (hN : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
      volume (F.outerBody j).carrier ≤ 2 ^ N * volume (F.innerBody i).carrier)
    {j j' : κ} (hj : j ∈ (F.weightedStep1AtScale hδ hdisc N hN).outerSet)
    (hj' : j' ∈ (F.weightedStep1AtScale hδ hdisc N hN).outerSet) :
    normalizedFiberVolume F F.innerSet j ≤
      2 * normalizedFiberVolume F F.innerSet j' := by
  apply normalizedFiberVolume_weightedStep1_le_two_mul F _ _ hj hj'

end FactorFamily

end ShadedBody
