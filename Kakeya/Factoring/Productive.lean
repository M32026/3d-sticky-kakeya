/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FactorFamily.Basic
public import Kakeya.Multiplicity

/-! # Removing null fibers from a shaded factor family

The final spatial restriction in the factoring pipeline can leave a fiber with indices but with
null shaded union.  Such a fiber cannot occur in a statement asserted for every retained block.
This file provides the null-stable restriction used by Proposition 5.1: retain precisely the
productive outer blocks and extend the surviving shading by zero to the original fibers.
-/

@[expose] public section

open MeasureTheory Convexity

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*}

omit [FiniteDimensional ℝ E] [BorelSpace E] in
open Classical in
/-- Membership in a shaded factor-family fiber. -/
@[simp]
theorem mem_shadedFactorFamily_fiber_iff (G : ShadedFactorFamily E ι κ)
    (j : κ) (i : ι) :
    i ∈ G.fiber j ↔ i ∈ G.innerSet ∧ G.parent i = j := by
  simp [ShadedFactorFamily.fiber]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
open Classical in
/-- Membership in an unshaded factor-family fiber. -/
@[simp]
theorem mem_factorFamily_fiber_iff (F : FactorFamily E ι κ) (j : κ) (i : ι) :
    i ∈ F.fiber j ↔ i ∈ F.innerSet ∧ F.parent i = j := by
  simp [FactorFamily.fiber]

open Classical in
/-- The outer blocks whose shaded fiber union has positive measure. -/
noncomputable def productiveOuterSet (G : ShadedFactorFamily E ι κ) : Finset κ :=
  G.outerSet.filter fun j ↦ volume (iUnionShade (G.fiber j) G.innerBody) ≠ 0

open Classical in
/-- All original indices whose parent is a productive output block. -/
noncomputable def productiveFinalInnerSet (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) : Finset ι :=
  F.innerSet.filter fun i ↦ F.parent i ∈ productiveOuterSet G

open Classical in
/-- Membership in the final inner set over productive blocks. -/
@[simp]
theorem mem_productiveFinalInnerSet_iff (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) (i : ι) :
    i ∈ productiveFinalInnerSet F G ↔
      i ∈ F.innerSet ∧ F.parent i ∈ productiveOuterSet G := by
  simp [productiveFinalInnerSet]

open Classical in
/-- The original input indices over one productive output block. -/
noncomputable def productiveFiber (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) (j : κ) : Finset ι :=
  {i ∈ F.innerSet | F.parent i ∈ productiveOuterSet G ∧ F.parent i = j}

open Classical in
/-- Membership in an original fiber over a productive output block. -/
@[simp]
theorem mem_productiveFiber_iff (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) (j : κ) (i : ι) :
    i ∈ productiveFiber F G j ↔
      i ∈ F.innerSet ∧ F.parent i ∈ productiveOuterSet G ∧ F.parent i = j := by
  simp [productiveFiber]

open Classical in
/-- Over a productive block the productive fiber is exactly the original input fiber. -/
theorem productiveFiber_eq_fiber (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) {j : κ} (hj : j ∈ productiveOuterSet G) :
    productiveFiber F G j = F.fiber j := by
  ext i
  simp only [mem_productiveFiber_iff, FactorFamily.fiber, Finset.mem_filter]
  constructor
  · rintro ⟨hi, _, hp⟩
    exact ⟨hi, hp⟩
  · rintro ⟨hi, hp⟩
    exact ⟨hi, hp ▸ hj, hp⟩

open Classical in
/-- Extend the output shading to the input family by assigning the empty shade to discarded
indices.  In applications the two bodies have the same carriers on `G.innerSet`. -/
noncomputable def zeroExtendedInnerBody (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) (i : ι) : ShadedBody E :=
  if i ∈ G.innerSet then G.innerBody i
  else (F.innerBody i).restrictShade ∅ MeasurableSet.empty

omit [FiniteDimensional ℝ E] [BorelSpace E] in
open Classical in
@[simp]
theorem zeroExtendedInnerBody_of_mem (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) {i : ι} (hi : i ∈ G.innerSet) :
    zeroExtendedInnerBody F G i = G.innerBody i := by
  simp [zeroExtendedInnerBody, hi]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
open Classical in
@[simp]
theorem zeroExtendedInnerBody_of_not_mem (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) {i : ι} (hi : i ∉ G.innerSet) :
    zeroExtendedInnerBody F G i =
      (F.innerBody i).restrictShade ∅ MeasurableSet.empty := by
  simp [zeroExtendedInnerBody, hi]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
open Classical in
/-- Zero extension preserves the input carrier when the selected output bodies do. -/
theorem zeroExtendedInnerBody_toConvexSpaceBody (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ)
    (hbody : ∀ i, (G.innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody) (i : ι) :
    (zeroExtendedInnerBody F G i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody := by
  by_cases hi : i ∈ G.innerSet
  · simp [zeroExtendedInnerBody, hi, hbody]
  · simp [zeroExtendedInnerBody, hi]

open Classical in
/-- The un-enlarged factor family on productive blocks, with the final shading extended by zero
to every original input body over those blocks.  This is the family to which the aggregate form
of Lemma 5.9 is applied. -/
noncomputable def productiveInputFamily (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) (hbody : ∀ i, (G.innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody) : FactorFamily E ι κ where
  innerSet := productiveFinalInnerSet F G
  innerBody := zeroExtendedInnerBody F G
  outerSet := productiveOuterSet G
  outerBody := F.outerBody
  parent := F.parent
  parent_mem := fun i hi ↦ (mem_productiveFinalInnerSet_iff F G i).mp hi |>.2
  inner_le_parent := by
    intro i hi
    rw [zeroExtendedInnerBody_toConvexSpaceBody F G hbody]
    exact F.inner_le_parent i ((mem_productiveFinalInnerSet_iff F G i).mp hi).1

open Classical in
/-- A productive input fiber is the original fiber over that productive block. -/
theorem productiveInputFamily_fiber_eq (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) (hbody : ∀ i, (G.innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody) {j : κ} (hj : j ∈ productiveOuterSet G) :
    (productiveInputFamily F G hbody).fiber j = F.fiber j := by
  ext i
  simp only [FactorFamily.fiber, productiveInputFamily, mem_productiveFinalInnerSet_iff,
    Finset.mem_filter]
  constructor
  · rintro ⟨⟨hi, _⟩, hp⟩
    exact ⟨hi, hp⟩
  · rintro ⟨hi, hp⟩
    exact ⟨⟨hi, hp ▸ hj⟩, hp⟩

@[simp]
theorem productiveInputFamily_outerSet (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) (hbody : ∀ i, (G.innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody) :
    (productiveInputFamily F G hbody).outerSet = productiveOuterSet G := rfl

@[simp]
theorem productiveInputFamily_outerBody (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) (hbody : ∀ i, (G.innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody) :
    (productiveInputFamily F G hbody).outerBody = F.outerBody := rfl

@[simp]
theorem productiveInputFamily_innerBody (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) (hbody : ∀ i, (G.innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody) :
    (productiveInputFamily F G hbody).innerBody = zeroExtendedInnerBody F G := rfl

open Classical in
/-- Membership in the zero-extended productive input family. -/
@[simp]
theorem mem_productiveInputFamily_innerSet_iff (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ)
    (hbody : ∀ i, (G.innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody) (i : ι) :
    i ∈ (productiveInputFamily F G hbody).innerSet ↔
      i ∈ F.innerSet ∧ F.parent i ∈ productiveOuterSet G := by
  simp [productiveInputFamily]

open Classical in
/-- On a productive block, zero extension to the original fiber has exactly the selected shaded
union. -/
theorem iUnionShade_zeroExtended_fiber (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) (hsub : G.innerSet ⊆ F.innerSet)
    (hparent : G.parent = F.parent) {j : κ} (hj : j ∈ productiveOuterSet G) :
    iUnionShade (productiveFiber F G j) (zeroExtendedInnerBody F G) =
      iUnionShade (G.fiber j) G.innerBody := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    have hp := (Finset.mem_filter.mp hi).2.2
    by_cases hiG : i ∈ G.innerSet
    · refine Set.mem_iUnion₂.mpr ⟨i, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨hiG, by simpa [hparent] using hp⟩
      · simpa [zeroExtendedInnerBody, hiG] using hxi
    · simp [zeroExtendedInnerBody, hiG] at hxi
  · intro hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    have hi' := Finset.mem_filter.mp hi
    have hpF : F.parent i = j := by simpa [← hparent] using hi'.2
    refine Set.mem_iUnion₂.mpr ⟨i, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hsub hi'.1, hpF ▸ hj, hpF⟩
    · simpa [zeroExtendedInnerBody, hi'.1] using hxi

open Classical in
/-- The final zero-extended inner union is pointwise contained in the preliminary output union. -/
theorem iUnionShade_productiveFinalInnerSet_subset (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) :
    iUnionShade (productiveFinalInnerSet F G) (zeroExtendedInnerBody F G) ⊆
      iUnionShade G.innerSet G.innerBody := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  by_cases hiG : i ∈ G.innerSet
  · exact Set.mem_iUnion₂.mpr ⟨i, hiG, by
      simpa [zeroExtendedInnerBody, hiG] using hxi⟩
  · simp [zeroExtendedInnerBody, hiG] at hxi

open Classical in
/-- Productive restriction can only decrease global pointwise multiplicity. -/
theorem pointwiseMultiplicity_productiveFinalInnerSet_le (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) (x : E) :
    pointwiseMultiplicity (productiveFinalInnerSet F G) (zeroExtendedInnerBody F G) x ≤
      pointwiseMultiplicity G.innerSet G.innerBody x := by
  apply Finset.card_le_card
  intro i hi
  have hi' := Finset.mem_filter.mp hi
  by_cases hiG : i ∈ G.innerSet
  · exact Finset.mem_filter.mpr ⟨hiG, by
      simpa [zeroExtendedInnerBody, hiG] using hi'.2⟩
  · simp [zeroExtendedInnerBody, hiG] at hi'

open Classical in
/-- A productive fiber remains non-null after zero extension to its original input fiber. -/
theorem volume_iUnionShade_zeroExtended_fiber_ne_zero (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) (hsub : G.innerSet ⊆ F.innerSet)
    (hparent : G.parent = F.parent) {j : κ} (hj : j ∈ productiveOuterSet G) :
    volume (iUnionShade (productiveFiber F G j) (zeroExtendedInnerBody F G)) ≠ 0 := by
  rw [iUnionShade_zeroExtended_fiber F G hsub hparent hj]
  exact (Finset.mem_filter.mp hj).2

open Classical in
/-- Pointwise multiplicity on a productive fiber is unchanged by zero extension. -/
theorem pointwiseMultiplicity_zeroExtended_fiber (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) (hsub : G.innerSet ⊆ F.innerSet)
    (hparent : G.parent = F.parent) {j : κ} (hj : j ∈ productiveOuterSet G) (x : E) :
    pointwiseMultiplicity (productiveFiber F G j) (zeroExtendedInnerBody F G) x =
      pointwiseMultiplicity (G.fiber j) G.innerBody x := by
  apply congrArg Finset.card
  ext i
  by_cases hiG : i ∈ G.innerSet
  · have hiF : i ∈ F.innerSet := hsub hiG
    have hz : zeroExtendedInnerBody F G i = G.innerBody i :=
      zeroExtendedInnerBody_of_mem F G hiG
    simp only [productiveFiber, Finset.mem_filter, ShadedFactorFamily.fiber]
    rw [hz]
    constructor
    · rintro ⟨⟨_, _, hp⟩, hxi⟩
      exact ⟨⟨hiG, by simpa [hparent] using hp⟩, hxi⟩
    · rintro ⟨⟨_, hp⟩, hxi⟩
      have hpF : F.parent i = j := by simpa [← hparent] using hp
      exact ⟨⟨hiF, hpF ▸ hj, hpF⟩, hxi⟩
  · have hz : (zeroExtendedInnerBody F G i).shade = ∅ := by
      simp [zeroExtendedInnerBody, hiG]
    simp only [productiveFiber, Finset.mem_filter, ShadedFactorFamily.fiber]
    rw [hz]
    simp [hiG]

open Classical in
/-- Zero extension also preserves the total shading mass of a productive fiber. -/
theorem sum_volume_zeroExtended_fiber (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) (hsub : G.innerSet ⊆ F.innerSet)
    (hparent : G.parent = F.parent) {j : κ} (hj : j ∈ productiveOuterSet G) :
    ∑ i ∈ productiveFiber F G j, volume (zeroExtendedInnerBody F G i).shade =
      ∑ i ∈ G.fiber j, volume (G.innerBody i).shade := by
  let s := productiveFiber F G j
  have hsubfiber : G.fiber j ⊆ s := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    have hp : F.parent i = j := by simpa [← hparent] using hi'.2
    exact Finset.mem_filter.mpr ⟨hsub hi'.1, hp ▸ hj, hp⟩
  calc
    ∑ i ∈ s, volume (zeroExtendedInnerBody F G i).shade =
        ∑ i ∈ G.fiber j, volume (zeroExtendedInnerBody F G i).shade := by
      symm
      apply Finset.sum_subset hsubfiber
      intro i his hif
      have hiG : i ∉ G.innerSet := by
        intro hiG
        apply hif
        exact Finset.mem_filter.mpr ⟨hiG, by
          have hp := (Finset.mem_filter.mp his).2.2
          simpa [hparent] using hp⟩
      simp [zeroExtendedInnerBody, hiG]
    _ = ∑ i ∈ G.fiber j, volume (G.innerBody i).shade := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [zeroExtendedInnerBody, (Finset.mem_filter.mp hi).1]

open Classical in
/-- The zero-extended active union is the union of the productive output fibers. -/
theorem iUnionShade_zeroExtended_eq_productive (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) (hsub : G.innerSet ⊆ F.innerSet)
    (hparent : G.parent = F.parent) :
    iUnionShade (productiveFinalInnerSet F G)
        (zeroExtendedInnerBody F G) =
      ⋃ j ∈ productiveOuterSet G, iUnionShade (G.fiber j) G.innerBody := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    have hp := (Finset.mem_filter.mp hi).2
    refine Set.mem_iUnion₂.mpr ⟨F.parent i, hp, ?_⟩
    rw [← iUnionShade_zeroExtended_fiber F G hsub hparent hp]
    exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hi).1, hp, rfl⟩, hxi⟩
  · intro hx
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
    rw [← iUnionShade_zeroExtended_fiber F G hsub hparent hj] at hxj
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxj
    exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2.1⟩, hxi⟩

omit [FiniteDimensional ℝ E] [BorelSpace E] in
open Classical in
/-- A shaded factor family is the union of its fibers. -/
theorem iUnionShade_eq_biUnion_fiber (G : ShadedFactorFamily E ι κ) :
    iUnionShade G.innerSet G.innerBody =
      ⋃ j ∈ G.outerSet, iUnionShade (G.fiber j) G.innerBody := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨G.parent i, G.parent_mem i hi,
      Set.mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩, hxi⟩⟩
  · intro hx
    obtain ⟨j, _, hxj⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxj
    exact Set.mem_iUnion₂.mpr ⟨i, (Finset.mem_filter.mp hi).1, hxi⟩

open Classical in
/-- Deleting null fibers changes the shaded union only on a null set. -/
theorem iUnionShade_zeroExtended_ae_eq (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) (hsub : G.innerSet ⊆ F.innerSet)
    (hparent : G.parent = F.parent) :
    iUnionShade (productiveFinalInnerSet F G)
        (zeroExtendedInnerBody F G) =ᵐ[volume] iUnionShade G.innerSet G.innerBody := by
  rw [iUnionShade_zeroExtended_eq_productive F G hsub hparent,
    iUnionShade_eq_biUnion_fiber G]
  let inactive := G.outerSet.filter fun j ↦ j ∉ productiveOuterSet G
  let Z := ⋃ j ∈ inactive, iUnionShade (G.fiber j) G.innerBody
  have hZ : volume Z = 0 := by
    change volume (⋃ j ∈ (inactive : Set κ), iUnionShade (G.fiber j) G.innerBody) = 0
    apply (measure_biUnion_null_iff (Set.to_countable (inactive : Set κ))).2
    intro j hj
    change j ∈ inactive at hj
    obtain ⟨hjG, hja⟩ := Finset.mem_filter.mp hj
    by_contra hz
    exact hja (Finset.mem_filter.mpr ⟨hjG, hz⟩)
  have hAE : ∀ᵐ x, x ∉ Z := by
    rw [ae_iff]
    have hset : {x : E | ¬x ∉ Z} = Z := by ext x; simp
    rw [hset]
    exact hZ
  filter_upwards [hAE] with x hxZ
  apply propext
  constructor
  · intro hx
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨j, (Finset.mem_filter.mp hj).1, hxj⟩
  · intro hx
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
    by_cases hja : j ∈ productiveOuterSet G
    · exact Set.mem_iUnion₂.mpr ⟨j, hja, hxj⟩
    · exact (hxZ (Set.mem_iUnion₂.mpr ⟨j,
        Finset.mem_filter.mpr ⟨hj, hja⟩, hxj⟩)).elim

open Classical in
/-- The global shaded-union volume is unchanged by productive restriction and zero extension. -/
theorem volume_iUnionShade_zeroExtended_eq (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) (hsub : G.innerSet ⊆ F.innerSet)
    (hparent : G.parent = F.parent) :
    volume (iUnionShade (productiveFinalInnerSet F G)
        (zeroExtendedInnerBody F G)) = volume (iUnionShade G.innerSet G.innerBody) :=
  measure_congr (iUnionShade_zeroExtended_ae_eq F G hsub hparent)

open Classical in
/-- The same null-pruning identity after intersection with an arbitrary set. -/
theorem volume_iUnionShade_zeroExtended_inter_eq (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) (hsub : G.innerSet ⊆ F.innerSet)
    (hparent : G.parent = F.parent) (A : Set E) :
    volume (iUnionShade (productiveFinalInnerSet F G)
        (zeroExtendedInnerBody F G) ∩ A) =
      volume (iUnionShade G.innerSet G.innerBody ∩ A) := by
  apply measure_congr
  exact (iUnionShade_zeroExtended_ae_eq F G hsub hparent).inter
    (Filter.EventuallyEq.rfl : A =ᵐ[volume] A)

open Classical in
/-- Productive restriction and zero extension preserve the total shading mass. -/
theorem sum_volume_zeroExtendedInnerBody (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) (hsub : G.innerSet ⊆ F.innerSet)
    (hparent : G.parent = F.parent) :
    ∑ i ∈ productiveFinalInnerSet F G,
        volume (zeroExtendedInnerBody F G i).shade =
      ∑ i ∈ G.innerSet, volume (G.innerBody i).shade := by
  let sG := {i ∈ G.innerSet | G.parent i ∈ productiveOuterSet G}
  let s := productiveFinalInnerSet F G
  have hsGs : sG ⊆ s := by
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hiG, hp⟩
    exact Finset.mem_filter.mpr ⟨hsub hiG, by simpa [hparent] using hp⟩
  calc
    ∑ i ∈ s, volume (zeroExtendedInnerBody F G i).shade =
        ∑ i ∈ sG, volume (zeroExtendedInnerBody F G i).shade := by
      symm
      apply Finset.sum_subset hsGs
      intro i his hiGs
      have hiGn : i ∉ G.innerSet := by
        intro hiG
        apply hiGs
        exact Finset.mem_filter.mpr ⟨hiG, by
          have := (Finset.mem_filter.mp his).2
          simpa [hparent] using this⟩
      simp [zeroExtendedInnerBody, hiGn]
    _ = ∑ i ∈ sG, volume (G.innerBody i).shade := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [zeroExtendedInnerBody, (Finset.mem_filter.mp hi).1]
    _ = ∑ i ∈ G.innerSet, volume (G.innerBody i).shade := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi hiA
      have hparentmem := G.parent_mem i hi
      have hnotproductive : G.parent i ∉ productiveOuterSet G := by
        intro ha
        exact hiA (Finset.mem_filter.mpr ⟨hi, ha⟩)
      have hzero : volume (iUnionShade (G.fiber (G.parent i)) G.innerBody) = 0 := by
        by_contra hz
        exact hnotproductive (Finset.mem_filter.mpr ⟨hparentmem, hz⟩)
      apply le_antisymm
      · calc
          volume (G.innerBody i).shade ≤
              volume (iUnionShade (G.fiber (G.parent i)) G.innerBody) := by
            apply measure_mono
            exact Set.subset_iUnion₂_of_subset i
              (Finset.mem_filter.mpr ⟨hi, rfl⟩) (Set.Subset.refl _)
          _ = 0 := hzero
      · exact bot_le

end ShadedBody
