/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.Combined

/-! # Selecting the outer scale before applying Proposition 5.1

The canonical corrected proposition is stated at one fixed outer scale.  This file supplies the
mass-weighted dyadic selection wrapper.  The upper bound on the outer scale is explicit: the
project's `FactorFamily.InnerIsDiscretizedAtScale` predicate intentionally controls only inner
bodies, so such a bound cannot be inferred from discretization alone.
-/

@[expose] public section

open MeasureTheory Convexity Kakeya
open scoped ENNReal NNReal

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [DecidableEq κ]

/-- The logarithmic scale-selection loss between the positive scales `δ` and `B`. -/
noncomputable def outerScaleSelectionConstant (δ B : NNReal) : NNReal :=
  Real.toNNReal (1 + Real.logb 2 ((B : ℝ) / δ))

/-- Coercion formula for the scale-selection constant on an admissible interval. -/
theorem coe_outerScaleSelectionConstant (δ B : NNReal) :
    (outerScaleSelectionConstant δ B : ENNReal) =
      ENNReal.ofReal (1 + Real.logb 2 ((B : ℝ) / δ)) := by
  exact ENNReal.ofNNReal_toNNReal _

/-- A family restricted to selected outer blocks and to their complete input fibers. -/
def FactorFamily.restrictOuter (F : FactorFamily E ι κ) (t : Finset κ) :
    FactorFamily E ι κ where
  innerSet := {i ∈ F.innerSet | F.parent i ∈ t}
  innerBody := F.innerBody
  outerSet := t
  outerBody := F.outerBody
  parent := F.parent
  parent_mem i hi := by
    exact (Finset.mem_filter.mp hi).2
  inner_le_parent i hi := by
    exact F.inner_le_parent i (Finset.mem_filter.mp hi).1

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- Every parent used by the inner family belongs to the outer index set. -/
theorem FactorFamily.innerSet_image_parent_subset_outerSet (F : FactorFamily E ι κ) :
    F.innerSet.image F.parent ⊆ F.outerSet := by
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  exact F.parent_mem i hi

omit [FiniteDimensional ℝ E] [Nontrivial E]
    [BorelSpace E] in
@[simp]
theorem FactorFamily.restrictOuter_innerSet (F : FactorFamily E ι κ) (t : Finset κ)
    : (F.restrictOuter t).innerSet = {i ∈ F.innerSet | F.parent i ∈ t} := rfl

omit [FiniteDimensional ℝ E] [Nontrivial E]
    [BorelSpace E] in
@[simp]
theorem FactorFamily.restrictOuter_outerSet (F : FactorFamily E ι κ) (t : Finset κ)
    : (F.restrictOuter t).outerSet = t := rfl

omit [FiniteDimensional ℝ E] [Nontrivial E]
    [BorelSpace E] in
@[simp]
theorem FactorFamily.restrictOuter_parent (F : FactorFamily E ι κ) (t : Finset κ)
    : (F.restrictOuter t).parent = F.parent := rfl

omit [FiniteDimensional ℝ E] [Nontrivial E]
    [BorelSpace E] in
@[simp]
theorem FactorFamily.restrictOuter_outerBody (F : FactorFamily E ι κ) (t : Finset κ)
    : (F.restrictOuter t).outerBody = F.outerBody := rfl

open Classical in
omit [FiniteDimensional ℝ E] [Nontrivial E]
    [BorelSpace E] in
/-- A selected block retains its complete input fiber. -/
theorem FactorFamily.restrictOuter_fiber_of_mem (F : FactorFamily E ι κ) (t : Finset κ)
    {j : κ} (hj : j ∈ t) :
    (F.restrictOuter t).fiber j = F.fiber j := by
  ext i
  simp only [FactorFamily.fiber, restrictOuter_innerSet, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hi, _⟩, hp⟩
    exact ⟨hi, hp⟩
  · rintro ⟨hi, hp⟩
    exact ⟨⟨hi, hp ▸ hj⟩, hp⟩

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- Discretization passes to an outer restriction. -/
theorem FactorFamily.InnerIsDiscretizedAtScale.restrictOuter
    {F : FactorFamily E ι κ} {δ : NNReal} (hdisc : F.InnerIsDiscretizedAtScale δ)
    (t : Finset κ) : (F.restrictOuter t).InnerIsDiscretizedAtScale δ where
  subset_unitBall i hi := hdisc.subset_unitBall i (Finset.mem_filter.mp hi).1
  le_scale i hi := hdisc.le_scale i (Finset.mem_filter.mp hi).1

omit [FiniteDimensional ℝ E] [Nontrivial E] [BorelSpace E] in
/-- Similar inner shape passes to an outer restriction. -/
theorem FactorFamily.InnerHasSimilarShape.restrictOuter
    {F : FactorFamily E ι κ} {K : NNReal} (hshape : F.InnerHasSimilarShape K)
    (t : Finset κ) : (F.restrictOuter t).InnerHasSimilarShape K := by
  intro i hi i' hi'
  exact hshape i (Finset.mem_filter.mp hi).1 i' (Finset.mem_filter.mp hi').1

open Classical in
omit [Nontrivial E] in
/-- Fiberwise Frostman control passes without loss because selected blocks keep complete fibers. -/
theorem FactorFamily.HasFrostmanFibers.restrictOuter
    {F : FactorFamily E ι κ} {C : ENNReal} (hFrostman : F.HasFrostmanFibers C)
    (t : Finset κ) (ht : t ⊆ F.outerSet) :
    (F.restrictOuter t).HasFrostmanFibers C := by
  intro j hj
  change ConvexSpaceBody.IsFrostmanIn ((F.restrictOuter t).fiber j)
    (fun i ↦ (F.innerBody i).toConvexSpaceBody) (F.outerBody j) C
  rw [FactorFamily.restrictOuter_fiber_of_mem F t hj]
  exact hFrostman j (ht hj)

open Classical in
omit [Nontrivial E] in
/-- GWZ Remark 5.3's thickened fibrewise Frostman control passes without loss because an outer
restriction retains every selected block's complete input fibre. -/
theorem FactorFamily.HasThickenedFrostmanFibers.restrictOuter
    {F : FactorFamily E ι κ} {C : ENNReal}
    (hFrostman : F.HasThickenedFrostmanFibers C)
    (t : Finset κ) (ht : t ⊆ F.outerSet) :
    (F.restrictOuter t).HasThickenedFrostmanFibers C := by
  intro j hj
  change Kakeya.maxDensity ((F.restrictOuter t).fiber j) (fun i ↦
        (F.innerBody i).toConvexSpaceBody.cthickening (2 * (F.outerBody j).scale)) *
        volume (F.outerBody j).carrier ≤
      C * ∑ i ∈ (F.restrictOuter t).fiber j,
        volume ((F.innerBody i).toConvexSpaceBody.cthickening
          (2 * (F.outerBody j).scale)).carrier
  rw [FactorFamily.restrictOuter_fiber_of_mem F t hj]
  exact hFrostman j (ht hj)

open Classical in
/-- Explicit outer/inner volume-ratio data passes to a complete-fiber outer restriction. -/
def OuterInnerVolumeRatio.restrictOuter {F : FactorFamily E ι κ}
    (D : OuterInnerVolumeRatio F) (t : Finset κ) (ht : t ⊆ F.outerSet) :
    OuterInnerVolumeRatio (F.restrictOuter t) where
  exponent := D.exponent
  volume_outer_le j hj i hi := by
    change volume (F.outerBody j).carrier ≤
      2 ^ D.exponent * volume (F.innerBody i).carrier
    rw [FactorFamily.restrictOuter_fiber_of_mem F t hj] at hi
    exact D.volume_outer_le j (ht hj) i hi

open Classical in
/-- The dyadic outer/inner volume-ratio exponent gives a uniform lower bound for the
density of every nonempty input fibre in its outer body. -/
theorem OuterInnerVolumeRatio.inv_two_pow_le_densityIn
    {F : FactorFamily E ι κ} (D : OuterInnerVolumeRatio F)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (hδ : 0 < δ)
    {j : κ} (hj : j ∈ F.innerSet.image F.parent) :
    ((2 : ENNReal) ^ D.exponent)⁻¹ ≤
      Kakeya.densityIn (F.fiber j) (fun i ↦ (F.innerBody i).toConvexSpaceBody)
        (F.outerBody j) := by
  obtain ⟨i, hi, hparent⟩ := Finset.mem_image.mp hj
  have hjout : j ∈ F.outerSet := by
    rw [← hparent]
    exact F.parent_mem i hi
  have hifib : i ∈ F.fiber j := by
    simp only [FactorFamily.fiber, Finset.mem_filter]
    exact ⟨hi, hparent⟩
  have hinnerpos : 0 < volume (F.innerBody i).carrier := by
    apply (F.innerBody i).toConvexSpaceBody.convex.volume_pos_of_scale_ne_zero
    exact ne_bot_of_le_ne_bot (ENNReal.coe_ne_zero.mpr hδ.ne') (hdisc.le_scale i hi)
  have houterpos : 0 < volume (F.outerBody j).carrier :=
    hinnerpos.trans_le (measure_mono (SetLike.coe_subset_coe.mpr
      (by simpa [hparent] using F.inner_le_parent i hi)))
  have hpow0 : (2 : ENNReal) ^ D.exponent ≠ 0 := by positivity
  have hpowtop : (2 : ENNReal) ^ D.exponent ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have hscaled : ((2 : ENNReal) ^ D.exponent)⁻¹ * volume (F.outerBody j).carrier ≤
      volume (F.innerBody i).carrier := by
    calc
      ((2 : ENNReal) ^ D.exponent)⁻¹ * volume (F.outerBody j).carrier ≤
          ((2 : ENNReal) ^ D.exponent)⁻¹ *
            ((2 : ENNReal) ^ D.exponent * volume (F.innerBody i).carrier) := by
        gcongr
        exact D.volume_outer_le j hjout i hifib
      _ = volume (F.innerBody i).carrier := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hpow0 hpowtop, one_mul]
  calc
    ((2 : ENNReal) ^ D.exponent)⁻¹ ≤
        volume (F.innerBody i).carrier / volume (F.outerBody j).carrier := by
      exact (ENNReal.le_div_iff_mul_le (Or.inl houterpos.ne')
        (Or.inl (F.outerBody j).isCompact.measure_ne_top)).2 hscaled
    _ ≤ Kakeya.densityIn (F.fiber j)
        (fun i ↦ (F.innerBody i).toConvexSpaceBody) (F.outerBody j) :=
      Kakeya.le_densityIn _ _ _ hifib (by simpa [hparent] using F.inner_le_parent i hi)

/-- The logarithmic loss for pigeonholing the carrier density of the outer fibres. -/
noncomputable def outerDensitySelectionConstant (card N : ℕ) : NNReal :=
  Real.toNNReal (1 + Real.logb 2
    ((card : ℝ) / ((((2 : NNReal) ^ N)⁻¹ : NNReal) : ℝ)))

/-- Data selected by shading-mass-weighted pigeonholing of the carrier density of the outer
fibres.  Complete fibres are retained, so all factorization hypotheses continue to hold. -/
structure OuterDensitySelection (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ)
    (D : OuterInnerVolumeRatio F)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) where
  /-- Selected nonempty outer blocks. -/
  selected : Finset κ
  /-- Only blocks used by the original inner family are selected. -/
  selected_subset : selected ⊆ F.innerSet.image F.parent
  /-- At least one block is retained. -/
  selected_nonempty : selected.Nonempty
  /-- The selection retains the total shading mass up to the explicit logarithmic loss. -/
  mass_refinement :
    ∑ i ∈ F.innerSet, volume (F.innerBody i).shade ≤
      (outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
        ∑ j ∈ selected, ∑ i ∈ F.innerSet with F.parent i = j,
          volume (F.innerBody i).shade
  /-- The carrier densities of the selected complete fibres are pairwise comparable. -/
  density_comparable : ∀ j ∈ selected, ∀ j' ∈ selected,
    Kakeya.densityIn (F.fiber j) (fun i ↦ (F.innerBody i).toConvexSpaceBody)
        (F.outerBody j) ≤
      2 * Kakeya.densityIn (F.fiber j') (fun i ↦ (F.innerBody i).toConvexSpaceBody)
        (F.outerBody j')

/-- Shading-mass-weighted dyadic pigeonholing produces a nonempty class of outer fibres with
pairwise comparable carrier density. -/
theorem nonempty_outerDensitySelection
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ)
    (D : OuterInnerVolumeRatio F)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) :
    Nonempty (OuterDensitySelection F hδ hdisc D hmass) := by
  let s := F.innerSet.image F.parent
  let w : κ → ENNReal := fun j ↦
    ∑ i ∈ F.innerSet with F.parent i = j, volume (F.innerBody i).shade
  let f : κ → ENNReal := fun j ↦
    Kakeya.densityIn (F.fiber j) (fun i ↦ (F.innerBody i).toConvexSpaceBody)
      (F.outerBody j)
  let a : NNReal := ((2 : NNReal) ^ D.exponent)⁻¹
  let b : NNReal := F.innerSet.card
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hf : ∀ j ∈ s, f j ∈ Set.Icc (a : ENNReal) (b : ENNReal) := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    constructor
    · simpa only [f, a, ENNReal.coe_inv (by positivity : (2 : NNReal) ^ D.exponent ≠ 0),
          ENNReal.coe_pow, ENNReal.coe_ofNat] using
        D.inv_two_pow_le_densityIn hdisc hδ (Finset.mem_image_of_mem F.parent hi)
    · calc
        f (F.parent i) ≤ ((F.fiber (F.parent i)).card : ENNReal) :=
          Kakeya.densityIn_le_card _ _ _
        _ ≤ (F.innerSet.card : ENNReal) := by
          classical
          rw [← F.finpartition_part_eq_fiber hi]
          exact_mod_cast Finset.card_le_card
            (F.finpartition.subset (F.finpartition.part_mem.mpr hi))
        _ = (b : ENNReal) := rfl
  obtain ⟨selected, hselected, hsum, hcomp⟩ :=
    ENNReal.dyadic_pigeonhole₁'' (s := s) w f ha hf
  have htotal : ∑ j ∈ s, w j =
      ∑ i ∈ F.innerSet, volume (F.innerBody i).shade := by
    dsimp [s, w]
    rw [Finset.sum_fiberwise_of_maps_to]
    intro i hi
    exact Finset.mem_image_of_mem F.parent hi
  have hselected_ne : selected.Nonempty := by
    by_contra hne
    have hempty : selected = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have : ∑ i ∈ F.innerSet, volume (F.innerBody i).shade ≤ 0 := by
      rw [← htotal]
      simpa [hempty] using hsum
    exact (not_lt_of_ge this) hmass
  refine ⟨{
    selected := selected
    selected_subset := hselected
    selected_nonempty := hselected_ne
    mass_refinement := ?_
    density_comparable := by simpa only [f] using hcomp }⟩
  rw [← htotal]
  have hcoe :
      (outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) =
        ENNReal.ofReal (1 + Real.logb 2 ((b : ℝ) / a)) := by
    unfold outerDensitySelectionConstant
    rw [ENNReal.ofNNReal_toNNReal]
    rfl
  rw [hcoe]
  exact hsum

/-- The canonical shading-mass-weighted outer-density selection. -/
noncomputable def outerDensitySelection
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ)
    (D : OuterInnerVolumeRatio F)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) :
    OuterDensitySelection F hδ hdisc D hmass :=
  Classical.choice (nonempty_outerDensitySelection F hδ hdisc D hmass)

/-- The factor family obtained by retaining the complete fibres selected by carrier density. -/
noncomputable def selectedOuterDensityFamily
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ)
    (D : OuterInnerVolumeRatio F)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) :
    FactorFamily E ι κ :=
  F.restrictOuter (outerDensitySelection F hδ hdisc D hmass).selected

omit [Nontrivial E] in
/-- The carrier-density selection is a substantial refinement of the original shaded inner
family, with exactly the named logarithmic loss. -/
theorem OuterDensitySelection.selection_refinement
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ)
    (D : OuterInnerVolumeRatio F)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade)
    (Q : OuterDensitySelection F hδ hdisc D hmass) :
    IsCRefinement (F.restrictOuter Q.selected).innerSet
      (F.restrictOuter Q.selected).innerBody F.innerSet F.innerBody
      (outerDensitySelectionConstant F.innerSet.card D.exponent)⁻¹ := by
  apply isCRefinement_of_sum_le
  · intro i hi
    exact (Finset.mem_filter.mp hi).1
  · have hpos : 0 < (outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
        ∑ j ∈ Q.selected, ∑ i ∈ F.innerSet with F.parent i = j,
          volume (F.innerBody i).shade := hmass.trans_le Q.mass_refinement
    exact ENNReal.coe_ne_zero.mp (pos_of_mul_pos_left hpos (by positivity)).ne'
  · rw [show (F.restrictOuter Q.selected).innerSet =
        {i ∈ F.innerSet | F.parent i ∈ Q.selected} by rfl]
    rw [show (F.restrictOuter Q.selected).innerBody = F.innerBody by rfl]
    calc
      ∑ i ∈ F.innerSet, volume (F.innerBody i).shade ≤
          (outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
            ∑ j ∈ Q.selected, ∑ i ∈ F.innerSet with F.parent i = j,
              volume (F.innerBody i).shade := Q.mass_refinement
      _ = (outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
          ∑ i ∈ {i ∈ F.innerSet | F.parent i ∈ Q.selected},
            volume (F.innerBody i).shade := by
        congr 1
        exact Finset.sum_fiberwise_eq_sum_filter F.innerSet Q.selected F.parent
          (fun i ↦ volume (F.innerBody i).shade)

omit [Nontrivial E] in
/-- The inner shading mass of the carrier-density-selected family is positive. -/
theorem OuterDensitySelection.selected_mass_pos
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ)
    (D : OuterInnerVolumeRatio F)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade)
    (Q : OuterDensitySelection F hδ hdisc D hmass) :
    0 < ∑ i ∈ (F.restrictOuter Q.selected).innerSet,
      volume ((F.restrictOuter Q.selected).innerBody i).shade := by
  have hprod : 0 < (outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
      ∑ j ∈ Q.selected, ∑ i ∈ F.innerSet with F.parent i = j,
        volume (F.innerBody i).shade := hmass.trans_le Q.mass_refinement
  have hsel : 0 < ∑ j ∈ Q.selected, ∑ i ∈ F.innerSet with F.parent i = j,
      volume (F.innerBody i).shade := pos_of_mul_pos_right hprod (by positivity)
  rw [show (F.restrictOuter Q.selected).innerSet =
      {i ∈ F.innerSet | F.parent i ∈ Q.selected} by rfl]
  rw [show (F.restrictOuter Q.selected).innerBody = F.innerBody by rfl]
  rw [← Finset.sum_fiberwise_eq_sum_filter F.innerSet Q.selected F.parent
    (fun i ↦ volume (F.innerBody i).shade)]
  exact hsel

omit [Nontrivial E] in
/-- Restricting to the carrier-density class costs its shading-mass pigeonhole constant divided
by the input fullness at the level of carrier mass.  This is the exact loss required before
applying `ConvexSpaceBody.IsFrostmanIn.of_subset`; in particular Frostman control does not pass
to this restriction for free. -/
theorem OuterDensitySelection.carrier_mass_le_selected
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ)
    (D : OuterInnerVolumeRatio F)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade)
    (Q : OuterDensitySelection F hδ hdisc D hmass) :
    ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier ≤
      (outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
        ((fullness F.innerSet F.innerBody : NNReal) : ENNReal)⁻¹ *
          ∑ i ∈ (F.restrictOuter Q.selected).innerSet,
            volume ((F.restrictOuter Q.selected).innerBody i).carrier := by
  let C : ENNReal := outerDensitySelectionConstant F.innerSet.card D.exponent
  let lam : ENNReal := fullness F.innerSet F.innerBody
  let selectedMass : ENNReal :=
    ∑ i ∈ (F.restrictOuter Q.selected).innerSet,
      volume ((F.restrictOuter Q.selected).innerBody i).carrier
  have hshadeEq : ∑ i ∈ F.innerSet, volume (F.innerBody i).shade =
      lam * ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier := by
    simpa only [lam] using
      ShadedBody.sum_volumeReal_shade_eq_fullness_mul F.innerSet F.innerBody
  have hlam0 : lam ≠ 0 := by
    intro hlam
    have : ∑ i ∈ F.innerSet, volume (F.innerBody i).shade = 0 := by
      rw [hshadeEq, hlam, zero_mul]
    exact hmass.ne' this
  have hlamtop : lam ≠ ⊤ := by
    exact ENNReal.coe_ne_top
  have hselectedShade :
      ∑ j ∈ Q.selected, ∑ i ∈ F.innerSet with F.parent i = j,
          volume (F.innerBody i).shade ≤ selectedMass := by
    dsimp only [selectedMass]
    rw [show (F.restrictOuter Q.selected).innerSet =
        {i ∈ F.innerSet | F.parent i ∈ Q.selected} by rfl]
    rw [show (F.restrictOuter Q.selected).innerBody = F.innerBody by rfl]
    calc
      ∑ j ∈ Q.selected, ∑ i ∈ F.innerSet with F.parent i = j,
          volume (F.innerBody i).shade =
          ∑ i ∈ {i ∈ F.innerSet | F.parent i ∈ Q.selected},
            volume (F.innerBody i).shade :=
        Finset.sum_fiberwise_eq_sum_filter F.innerSet Q.selected F.parent
          (fun i ↦ volume (F.innerBody i).shade)
      _ ≤ ∑ i ∈ {i ∈ F.innerSet | F.parent i ∈ Q.selected},
          volume (F.innerBody i).carrier :=
        Finset.sum_le_sum fun i _ ↦ measure_mono (F.innerBody i).shade_subset
  have hmain : lam * ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier ≤
      C * selectedMass := by
    rw [← hshadeEq]
    exact Q.mass_refinement.trans (mul_le_mul_left' hselectedShade C)
  calc
    ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier =
        lam⁻¹ * (lam * ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hlam0 hlamtop, one_mul]
    _ ≤ lam⁻¹ * (C * selectedMass) := mul_le_mul_left' hmain _
    _ = C * lam⁻¹ * selectedMass := by ring

/-- Global fine Frostman control restricts to the carrier-density-selected complete fibres with
the same explicit `C_select / fullness` carrier-mass loss. -/
theorem OuterDensitySelection.selected_inner_isFrostmanIn
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ)
    (D : OuterInnerVolumeRatio F)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade)
    (Q : OuterDensitySelection F hδ hdisc D hmass)
    {K : ConvexSpaceBody E} {CFr : ENNReal}
    (hFr : ConvexSpaceBody.IsFrostmanIn F.innerSet
      (fun i ↦ (F.innerBody i).toConvexSpaceBody) K CFr)
    (hFK : ∀ i ∈ F.innerSet, (F.innerBody i).toConvexSpaceBody ≤ K) :
    ConvexSpaceBody.IsFrostmanIn (F.restrictOuter Q.selected).innerSet
      (fun i ↦ ((F.restrictOuter Q.selected).innerBody i).toConvexSpaceBody) K
      (CFr * ((outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
        ((fullness F.innerSet F.innerBody : NNReal) : ENNReal)⁻¹)) := by
  let G := F.restrictOuter Q.selected
  have hsub : G.innerSet ⊆ F.innerSet := by
    intro i hi
    exact (Finset.mem_filter.mp hi).1
  have hvol : ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier ≤
      ((outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
        ((fullness F.innerSet F.innerBody : NNReal) : ENNReal)⁻¹) *
          ∑ i ∈ G.innerSet, volume (F.innerBody i).carrier := by
    have hraw := Q.carrier_mass_le_selected F hδ hdisc D hmass
    change ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier ≤
      ((outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
        ((fullness F.innerSet F.innerBody : NNReal) : ENNReal)⁻¹) *
          ∑ i ∈ G.innerSet, volume (G.innerBody i).carrier at hraw
    simpa only [show G.innerBody = F.innerBody from rfl] using hraw
  change ConvexSpaceBody.IsFrostmanIn G.innerSet
    (fun i ↦ (F.innerBody i).toConvexSpaceBody) K _
  exact hFr.of_le_of_subset hFK hsub hvol

omit [Nontrivial E] in
/-- Global Frostman control passes to the carrier-density-selected outer bodies with the exact
restriction loss `C_select / fullness` and the dyadic fibre-comparability loss `2`. -/
theorem OuterDensitySelection.outer_isFrostmanIn
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ)
    (D : OuterInnerVolumeRatio F)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade)
    (Q : OuterDensitySelection F hδ hdisc D hmass)
    {K : ConvexSpaceBody E} {C : ENNReal}
    (hFr : ConvexSpaceBody.IsFrostmanIn F.innerSet
      (fun i ↦ (F.innerBody i).toConvexSpaceBody) K C)
    (hVpos : ∀ i ∈ F.innerSet, 0 < volume (F.innerBody i).carrier)
    (hVK : ∀ i ∈ F.innerSet, (F.innerBody i).toConvexSpaceBody ≤ K)
    (hWK : ∀ j ∈ Q.selected, F.outerBody j ≤ K) :
    ConvexSpaceBody.IsFrostmanIn Q.selected F.outerBody K
      (2 * (C * (outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
        ((fullness F.innerSet F.innerBody : NNReal) : ENNReal)⁻¹)) := by
  classical
  let G := F.restrictOuter Q.selected
  let Cselect : ENNReal := outerDensitySelectionConstant F.innerSet.card D.exponent
  let lam : ENNReal := fullness F.innerSet F.innerBody
  have hsub : G.innerSet ⊆ F.innerSet := by
    intro i hi
    exact (Finset.mem_filter.mp hi).1
  have hvol : ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier ≤
      (Cselect * lam⁻¹) * ∑ i ∈ G.innerSet, volume (F.innerBody i).carrier := by
    simpa only [G, Cselect, lam, FactorFamily.restrictOuter_innerSet,
      show G.innerBody = F.innerBody from rfl] using
        Q.carrier_mass_le_selected F hδ hdisc D hmass
  have hFrG : ConvexSpaceBody.IsFrostmanIn G.innerSet
      (fun i ↦ (F.innerBody i).toConvexSpaceBody) K (C * (Cselect * lam⁻¹)) :=
    hFr.of_le_of_subset hVK hsub hvol
  have hpar : ∀ i ∈ G.innerSet, F.parent i ∈ Q.selected := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hne : ∀ j ∈ Q.selected, (G.fiber j).Nonempty := by
    intro j hj
    obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp (Q.selected_subset hj)
    refine ⟨i, ?_⟩
    simp only [G, FactorFamily.fiber, FactorFamily.restrictOuter_innerSet,
      Finset.mem_filter]
    exact ⟨⟨hi, hij ▸ hj⟩, hij⟩
  have hunif : ∀ j ∈ Q.selected, ∀ j' ∈ Q.selected,
      Kakeya.densityIn (G.fiber j)
          (fun i ↦ (F.innerBody i).toConvexSpaceBody) (F.outerBody j) ≤
        2 * Kakeya.densityIn (G.fiber j')
          (fun i ↦ (F.innerBody i).toConvexSpaceBody) (F.outerBody j') := by
    intro j hj j' hj'
    rw [FactorFamily.restrictOuter_fiber_of_mem F Q.selected hj,
      FactorFamily.restrictOuter_fiber_of_mem F Q.selected hj']
    exact Q.density_comparable j hj j' hj'
  simpa only [G, Cselect, lam, mul_assoc] using
    ConvexSpaceBody.isFrostmanIn_parents_of_uniform_fibres
      (q := G.innerSet) (out := Q.selected)
      (V := fun i ↦ (F.innerBody i).toConvexSpaceBody) (W := F.outerBody)
      (par := F.parent) (fib := G.fiber) (K := K)
      (C := C * (Cselect * lam⁻¹)) (Cmass := 2)
      hFrG (fun i hi ↦ hVpos i (hsub hi)) hpar
      (fun i hi ↦ F.inner_le_parent i (hsub hi)) hWK
      (fun j ↦ by ext i; simp only [G, FactorFamily.fiber,
        FactorFamily.restrictOuter_parent]) hne hunif

omit [Nontrivial E] in
/-- Move the logarithmic carrier-density selection loss to the right of the multiplicity
inequality.  This is the first of the two refinement bridges used in Proposition 6.6(A); the
second is the shortest-scale selection below. -/
theorem OuterDensitySelection.multiplicity_le_selected
    (F : FactorFamily E ι κ) {δ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ)
    (D : OuterInnerVolumeRatio F)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade)
    (Q : OuterDensitySelection F hδ hdisc D hmass) :
    multiplicity F.innerSet F.innerBody ≤
      (outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
        multiplicity (F.restrictOuter Q.selected).innerSet
          (F.restrictOuter Q.selected).innerBody := by
  let C : NNReal := outerDensitySelectionConstant F.innerSet.card D.exponent
  have hprod : 0 < (C : ENNReal) *
      ∑ i ∈ (F.restrictOuter Q.selected).innerSet,
        volume ((F.restrictOuter Q.selected).innerBody i).shade := by
    exact hmass.trans_le (by
      simpa only [C] using Q.mass_refinement.trans_eq (by
        congr 1
        rw [show (F.restrictOuter Q.selected).innerSet =
          {i ∈ F.innerSet | F.parent i ∈ Q.selected} by rfl]
        rw [show (F.restrictOuter Q.selected).innerBody = F.innerBody by rfl]
        exact Finset.sum_fiberwise_eq_sum_filter F.innerSet Q.selected F.parent
          (fun i ↦ volume (F.innerBody i).shade)))
  have hC0 : (C : ENNReal) ≠ 0 := (pos_of_mul_pos_left hprod (by positivity)).ne'
  have hC0nn : C ≠ 0 := ENNReal.coe_ne_zero.mp hC0
  have hcancel : (C : ENNReal) * ((C⁻¹ : NNReal) : ENNReal) = 1 := by
    rw [ENNReal.coe_inv hC0nn]
    exact ENNReal.mul_inv_cancel hC0 ENNReal.coe_ne_top
  calc
    multiplicity F.innerSet F.innerBody =
        (C : ENNReal) * (((C⁻¹ : NNReal) : ENNReal) *
          multiplicity F.innerSet F.innerBody) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ (C : ENNReal) * multiplicity (F.restrictOuter Q.selected).innerSet
          (F.restrictOuter Q.selected).innerBody := by
      exact mul_le_mul_right (by
        simpa only [C] using
          (Q.selection_refinement F hδ hdisc D hmass).mul_multiplicity_le) _

/-- Data selected by mass-weighted dyadic pigeonholing of the outer shortest scale. -/
structure OuterScaleSelection (F : FactorFamily E ι κ) {δ B : NNReal}
    (hδ : 0 < δ) (hδB : δ ≤ B)
    (hupper : ∀ j ∈ F.innerSet.image F.parent, (F.outerBody j).scale ≤ B)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) where
  /-- Selected outer blocks. -/
  selected : Finset κ
  selected_subset : selected ⊆ F.innerSet.image F.parent
  selected_nonempty : selected.Nonempty
  mass_refinement :
    ∑ i ∈ F.innerSet, volume (F.innerBody i).shade ≤
      (outerScaleSelectionConstant δ B : ENNReal) *
        ∑ j ∈ selected, ∑ i ∈ F.innerSet with F.parent i = j,
          volume (F.innerBody i).shade
  scale_comparable : ∀ i ∈ selected, ∀ j ∈ selected,
    (F.outerBody i).scale ≤ 2 * (F.outerBody j).scale

open Classical in
/-- Mass-weighted dyadic pigeonholing produces a nonempty comparable outer-scale class. -/
theorem nonempty_outerScaleSelection
    (F : FactorFamily E ι κ) {δ B : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hδB : δ ≤ B)
    (hupper : ∀ j ∈ F.innerSet.image F.parent, (F.outerBody j).scale ≤ B)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) :
    Nonempty (OuterScaleSelection F hδ hδB hupper hmass) := by
  let s := F.innerSet.image F.parent
  let w : κ → ENNReal := fun j ↦
    ∑ i ∈ F.innerSet with F.parent i = j, volume (F.innerBody i).shade
  let f : κ → ℝ := fun j ↦ (F.outerBody j).scale
  have hf : ∀ j ∈ s, f j ∈ Set.Icc (δ : ℝ) (B : ℝ) := by
    intro j hj
    have hj' : j ∈ F.innerSet.image F.parent := by simpa only [s] using hj
    constructor
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj'
      have hlo := hdisc.le_outer_scale_parent hi
      rw [ConvexSpaceBody.ethickness_scale_eq_ofReal_scale] at hlo
      have hscale0 : 0 ≤ (F.outerBody (F.parent i)).scale := by
        exact Metric.thickness_nonneg _ _
      rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff hscale0] at hlo
      exact hlo
    · exact hupper j hj'
  obtain ⟨t, hts, hmass', hcomp⟩ :=
    ENNReal.dyadic_pigeonhole' (s := s) (w := w) (f := fun j _ ↦ f j)
      (n := 1) (by exact_mod_cast hδ) (by exact_mod_cast hδB) (by
        intro j hj
        exact ⟨fun _ ↦ (hf j hj).1, fun _ ↦ (hf j hj).2⟩)
  have hmass'' :
      ∑ i ∈ F.innerSet, volume (F.innerBody i).shade ≤
        (outerScaleSelectionConstant δ B : ENNReal) * ∑ j ∈ t, w j := by
    calc
      ∑ i ∈ F.innerSet, volume (F.innerBody i).shade =
          ∑ j ∈ s, w j := by
        symm
        exact Finset.sum_fiberwise_of_maps_to
          (fun i hi ↦ Finset.mem_image_of_mem F.parent hi)
          (fun i ↦ volume (F.innerBody i).shade)
      _ ≤ (outerScaleSelectionConstant δ B : ENNReal) * ∑ j ∈ t, w j := by
        change s.sum w ≤
          ENNReal.ofReal (1 + Real.logb 2 ((B : ℝ) / δ)) * t.sum w
        rw [pow_one] at hmass'
        exact hmass'
  have htne : t.Nonempty := by
    by_contra ht
    have htempty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    have : ∑ i ∈ F.innerSet, volume (F.innerBody i).shade ≤ 0 := by
      simpa only [htempty, Finset.sum_empty, mul_zero] using hmass''
    exact (not_le_of_gt hmass) this
  refine ⟨{
    selected := t
    selected_subset := hts
    selected_nonempty := htne
    mass_refinement := by simpa only [w] using hmass''
    scale_comparable := ?_ }⟩
  intro i hi j hj
  simpa only [f, Pi.smul_apply, smul_eq_mul] using hcomp i hi j hj 0

/-- The canonical outer-scale selection, with proof data kept explicit in its arguments. -/
noncomputable def outerScaleSelection
    (F : FactorFamily E ι κ) {δ B : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hδB : δ ≤ B)
    (hupper : ∀ j ∈ F.innerSet.image F.parent, (F.outerBody j).scale ≤ B)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) :
    OuterScaleSelection F hδ hδB hupper hmass :=
  Classical.choice (nonempty_outerScaleSelection F hδ hdisc hδB hupper hmass)

/-- The selected representative scale. -/
noncomputable def selectedOuterScale
    (F : FactorFamily E ι κ) {δ B : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hδB : δ ≤ B)
    (hupper : ∀ j ∈ F.innerSet.image F.parent, (F.outerBody j).scale ≤ B)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) : NNReal :=
  Real.toNNReal (F.outerBody
    (outerScaleSelection F hδ hdisc hδB hupper hmass).selected_nonempty.choose).scale

/-- The representative selected outer scale is positive. -/
theorem selectedOuterScale_pos
    (F : FactorFamily E ι κ) {δ B : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hδB : δ ≤ B)
    (hupper : ∀ j ∈ F.innerSet.image F.parent, (F.outerBody j).scale ≤ B)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) :
    0 < selectedOuterScale F hδ hdisc hδB hupper hmass := by
  let Q := outerScaleSelection F hδ hdisc hδB hupper hmass
  let j := Q.selected_nonempty.choose
  have hj : j ∈ F.innerSet.image F.parent := Q.selected_subset Q.selected_nonempty.choose_spec
  obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hj
  have hlo := hdisc.le_outer_scale_parent hi
  rw [hij] at hlo
  rw [ConvexSpaceBody.ethickness_scale_eq_ofReal_scale] at hlo
  have hδcoe : (0 : ENNReal) < (δ : ENNReal) := ENNReal.coe_pos.mpr hδ
  have hscale : 0 < (F.outerBody j).scale := by
    rw [← ENNReal.ofReal_pos]
    exact hδcoe.trans_le hlo
  exact Real.toNNReal_pos.mpr hscale

/-- The representative scale selected from a discretized factor family is no smaller than the
inner discretization scale. -/
theorem le_selectedOuterScale
    (F : FactorFamily E ι κ) {δ B : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hδB : δ ≤ B)
    (hupper : ∀ j ∈ F.innerSet.image F.parent, (F.outerBody j).scale ≤ B)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) :
    δ ≤ selectedOuterScale F hδ hdisc hδB hupper hmass := by
  let Q := outerScaleSelection F hδ hdisc hδB hupper hmass
  let j := Q.selected_nonempty.choose
  have hj : j ∈ F.innerSet.image F.parent := Q.selected_subset Q.selected_nonempty.choose_spec
  obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hj
  have hlo := hdisc.le_outer_scale_parent hi
  rw [hij, ConvexSpaceBody.ethickness_scale_eq_ofReal_scale] at hlo
  rw [← ENNReal.coe_le_coe]
  change (δ : ENNReal) ≤ (Real.toNNReal (F.outerBody j).scale : ENNReal)
  rw [← show ENNReal.ofReal (F.outerBody j).scale =
    (Real.toNNReal (F.outerBody j).scale : ENNReal) from rfl]
  exact hlo

/-- The factor family selected by outer scale. -/
noncomputable def selectedOuterScaleFamily
    (F : FactorFamily E ι κ) {δ B : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hδB : δ ≤ B)
    (hupper : ∀ j ∈ F.innerSet.image F.parent, (F.outerBody j).scale ≤ B)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) :
    FactorFamily E ι κ :=
  F.restrictOuter (outerScaleSelection F hδ hdisc hδB hupper hmass).selected

/-- The scale-selected family is an ordinary refinement of the original family: it only removes
complete outer fibres and leaves every retained shaded inner body unchanged. -/
theorem selectedOuterScaleFamily_isRefinement
    (F : FactorFamily E ι κ) {δ B : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hδB : δ ≤ B)
    (hupper : ∀ j ∈ F.innerSet.image F.parent, (F.outerBody j).scale ≤ B)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) :
    IsRefinement
      (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerSet
      (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerBody
      F.innerSet F.innerBody := by
  constructor
  · intro i hi
    exact (Finset.mem_filter.mp hi).1
  · intro i _
    exact ⟨rfl, Set.Subset.rfl⟩

/-- The selected family is at the representative scale with comparison constant `2`. -/
theorem selectedOuterScaleFamily_outerIsAtScale
    (F : FactorFamily E ι κ) {δ B : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hδB : δ ≤ B)
    (hupper : ∀ j ∈ F.innerSet.image F.parent, (F.outerBody j).scale ≤ B)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) :
    (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).OuterIsAtScale 2
      (selectedOuterScale F hδ hdisc hδB hupper hmass) := by
  let Q := outerScaleSelection F hδ hdisc hδB hupper hmass
  let j₀ := Q.selected_nonempty.choose
  have hj₀ : j₀ ∈ Q.selected := Q.selected_nonempty.choose_spec
  have hj₀used : j₀ ∈ F.innerSet.image F.parent := Q.selected_subset hj₀
  obtain ⟨i₀, hi₀, hi₀j₀⟩ := Finset.mem_image.mp hj₀used
  have hj₀lower := hdisc.le_outer_scale_parent hi₀
  rw [hi₀j₀] at hj₀lower
  rw [ConvexSpaceBody.ethickness_scale_eq_ofReal_scale] at hj₀lower
  have hj₀pos : 0 < (F.outerBody j₀).scale := by
    rw [← ENNReal.ofReal_pos]
    exact (ENNReal.coe_pos.mpr hδ).trans_le hj₀lower
  have hwcoe :
      ((selectedOuterScale F hδ hdisc hδB hupper hmass : NNReal) : ℝ) =
        (F.outerBody j₀).scale := by
    exact Real.coe_toNNReal _ hj₀pos.le
  intro j hj
  have hjQ : j ∈ Q.selected := by
    simpa only [selectedOuterScaleFamily, FactorFamily.restrictOuter_outerSet] using hj
  change (F.outerBody j).scale ≤ (2 : ℝ) *
      (selectedOuterScale F hδ hdisc hδB hupper hmass : ℝ) ∧
    (selectedOuterScale F hδ hdisc hδB hupper hmass : ℝ) ≤
      (2 : ℝ) * (F.outerBody j).scale
  rw [hwcoe]
  exact ⟨Q.scale_comparable j hjQ j₀ hj₀, Q.scale_comparable j₀ hj₀ j hjQ⟩

/-- Result package for the optional scale-selecting wrapper around the canonical core. -/
structure FactoringAndMultPropCoreSelectScaleResult
    (F : FactorFamily E ι κ) {C : ENNReal} {δ B : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (hδB : δ ≤ B)
    (hupper : ∀ j ∈ F.innerSet.image F.parent, (F.outerBody j).scale ≤ B)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) : Prop where
  /-- Positivity of the selected scale. -/
  scale_pos : 0 < selectedOuterScale F hδ hdisc hδB hupper hmass
  /-- The selected complete fibers retain a logarithmic fraction of input shading mass. -/
  selection_mass :
    ∑ i ∈ F.innerSet, volume (F.innerBody i).shade ≤
      (outerScaleSelectionConstant δ B : ENNReal) *
        ∑ i ∈ (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerSet,
          volume ((selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerBody i).shade
  /-- The canonical fixed-scale core applied to the selected subfamily. -/
  core : FactoringAndMultPropCoreAtScale (C := C)
    (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass)
    hδ
    (hdisc.restrictOuter _)
    (D.restrictOuter _
      ((outerScaleSelection F hδ hdisc hδB hupper hmass).selected_subset.trans
        F.innerSet_image_parent_subset_outerSet))
    (selectedOuterScale F hδ hdisc hδB hupper hmass) scale_pos

/-- The logarithmic mass selection is an explicit refinement of the original fine family.

This is the bridge needed by Section 6.6(A): the fixed-scale core runs on the selected complete
fibres, whereas the multiplicity split has to start from the original fine family. -/
theorem FactoringAndMultPropCoreSelectScaleResult.selection_refinement
    (F : FactorFamily E ι κ) {C : ENNReal} {δ B : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (hδB : δ ≤ B)
    (hupper : ∀ j ∈ F.innerSet.image F.parent, (F.outerBody j).scale ≤ B)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade)
    (Q : FactoringAndMultPropCoreSelectScaleResult (C := C) F hδ hdisc D hδB hupper
      hmass) :
    IsCRefinement
      (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerSet
      (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerBody
      F.innerSet F.innerBody (outerScaleSelectionConstant δ B)⁻¹ :=
  isCRefinement_of_isRefinement_of_sum_le
    (s' := (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerSet)
    (V' := (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerBody)
    (s := F.innerSet) (V := F.innerBody)
    (selectedOuterScaleFamily_isRefinement F hδ hdisc hδB hupper hmass) Q.selection_mass

/-- The selected complete fibres retain the original fullness up to the same logarithmic loss. -/
theorem FactoringAndMultPropCoreSelectScaleResult.selection_fullness
    (F : FactorFamily E ι κ) {C : ENNReal} {δ B : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (hδB : δ ≤ B)
    (hupper : ∀ j ∈ F.innerSet.image F.parent, (F.outerBody j).scale ≤ B)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade)
    (Q : FactoringAndMultPropCoreSelectScaleResult (C := C) F hδ hdisc D hδB hupper
      hmass) :
    (((outerScaleSelectionConstant δ B)⁻¹ : NNReal) : ENNReal) *
        (fullness F.innerSet F.innerBody : ENNReal) ≤
      (fullness (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerSet
        (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerBody : ENNReal) :=
  Q.selection_refinement F hδ hdisc D hδB hupper hmass |>.coe_mul_fullness_le

/-- Selecting one outer scale by shading mass also retains the fine carrier mass, at the
logarithmic selection cost divided by the input fullness.  This is the carrier-mass form needed
to restrict a global Frostman hypothesis after the optional scale-selection wrapper; it is not a
loss-free passage to a subfamily. -/
theorem FactoringAndMultPropCoreSelectScaleResult.carrier_mass_le_selected
    (F : FactorFamily E ι κ) {C : ENNReal} {δ B : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (hδB : δ ≤ B)
    (hupper : ∀ j ∈ F.innerSet.image F.parent, (F.outerBody j).scale ≤ B)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade)
    (Q : FactoringAndMultPropCoreSelectScaleResult (C := C) F hδ hdisc D hδB hupper
      hmass) :
    ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier ≤
      (outerScaleSelectionConstant δ B : ENNReal) *
        ((fullness F.innerSet F.innerBody : NNReal) : ENNReal)⁻¹ *
          ∑ i ∈ (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerSet,
            volume ((selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerBody i).carrier := by
  let Csel : ENNReal := outerScaleSelectionConstant δ B
  let lam : ENNReal := fullness F.innerSet F.innerBody
  let selectedMass : ENNReal :=
    ∑ i ∈ (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerSet,
      volume ((selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerBody i).carrier
  have hshadeEq : ∑ i ∈ F.innerSet, volume (F.innerBody i).shade =
      lam * ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier := by
    simpa only [lam] using
      ShadedBody.sum_volumeReal_shade_eq_fullness_mul F.innerSet F.innerBody
  have hlam0 : lam ≠ 0 := by
    intro hlam
    have : ∑ i ∈ F.innerSet, volume (F.innerBody i).shade = 0 := by
      rw [hshadeEq, hlam, zero_mul]
    exact hmass.ne' this
  have hlamtop : lam ≠ ⊤ := ENNReal.coe_ne_top
  have hselectedShade :
      ∑ i ∈ (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerSet,
          volume ((selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerBody i).shade ≤
        selectedMass := by
    dsimp only [selectedMass]
    exact Finset.sum_le_sum fun i _ ↦
      measure_mono ((selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerBody i).shade_subset
  have hmain : lam * ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier ≤
      Csel * selectedMass := by
    rw [← hshadeEq]
    exact Q.selection_mass.trans (mul_le_mul_left' hselectedShade Csel)
  calc
    ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier =
        lam⁻¹ * (lam * ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hlam0 hlamtop, one_mul]
    _ ≤ lam⁻¹ * (Csel * selectedMass) := mul_le_mul_left' hmain _
    _ = Csel * lam⁻¹ * selectedMass := by ring

/-- A global Frostman hypothesis restricts to the complete fibres retained by the optional
outer-scale selection, with precisely the carrier-mass loss recorded above. -/
theorem FactoringAndMultPropCoreSelectScaleResult.selected_inner_isFrostmanIn
    (F : FactorFamily E ι κ) {C CFr : ENNReal} {δ B : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (hδB : δ ≤ B)
    (hupper : ∀ j ∈ F.innerSet.image F.parent, (F.outerBody j).scale ≤ B)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade)
    (Q : FactoringAndMultPropCoreSelectScaleResult (C := C) F hδ hdisc D hδB hupper
      hmass)
    {K : ConvexSpaceBody E}
    (hFr : ConvexSpaceBody.IsFrostmanIn F.innerSet
      (fun i ↦ (F.innerBody i).toConvexSpaceBody) K CFr)
    (hFK : ∀ i ∈ F.innerSet, (F.innerBody i).toConvexSpaceBody ≤ K) :
    ConvexSpaceBody.IsFrostmanIn
      (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerSet
      (fun i ↦ ((selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerBody i).toConvexSpaceBody)
      K
      (CFr * ((outerScaleSelectionConstant δ B : ENNReal) *
        ((fullness F.innerSet F.innerBody : NNReal) : ENNReal)⁻¹)) := by
  let G := selectedOuterScaleFamily F hδ hdisc hδB hupper hmass
  have hsub : G.innerSet ⊆ F.innerSet := by
    intro i hi
    exact (Finset.mem_filter.mp hi).1
  have hvol : ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier ≤
      ((outerScaleSelectionConstant δ B : ENNReal) *
        ((fullness F.innerSet F.innerBody : NNReal) : ENNReal)⁻¹) *
          ∑ i ∈ G.innerSet, volume (F.innerBody i).carrier := by
    have hraw := Q.carrier_mass_le_selected F hδ hdisc D hδB hupper hmass
    change ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier ≤
      ((outerScaleSelectionConstant δ B : ENNReal) *
        ((fullness F.innerSet F.innerBody : NNReal) : ENNReal)⁻¹) *
          ∑ i ∈ G.innerSet, volume (G.innerBody i).carrier at hraw
    simpa only [show G.innerBody = F.innerBody from rfl] using hraw
  change ConvexSpaceBody.IsFrostmanIn G.innerSet
    (fun i ↦ (F.innerBody i).toConvexSpaceBody) K
      (CFr * ((outerScaleSelectionConstant δ B : ENNReal) *
        ((fullness F.innerSet F.innerBody : NNReal) : ENNReal)⁻¹))
  exact hFr.of_le_of_subset hFK hsub hvol

/-- Under a uniform fibre-density bracket, the optional outer-scale selection transfers global
fine Frostman control to the selected actual parent bodies.  The constant displays both genuine
losses: `Cmass` from parent aggregation and `C_select / fullness` from restricting to the
mass-selected scale. -/
theorem FactoringAndMultPropCoreSelectScaleResult.selected_outer_isFrostmanIn
    (F : FactorFamily E ι κ) {C CFr Cmass : ENNReal} {δ B : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (hδB : δ ≤ B)
    (hupper : ∀ j ∈ F.innerSet.image F.parent, (F.outerBody j).scale ≤ B)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade)
    (Q : FactoringAndMultPropCoreSelectScaleResult (C := C) F hδ hdisc D hδB hupper
      hmass)
    {K : ConvexSpaceBody E}
    (hFr : ConvexSpaceBody.IsFrostmanIn F.innerSet
      (fun i ↦ (F.innerBody i).toConvexSpaceBody) K CFr)
    (hVpos : ∀ i ∈ F.innerSet, 0 < volume (F.innerBody i).carrier)
    (hFK : ∀ i ∈ F.innerSet, (F.innerBody i).toConvexSpaceBody ≤ K)
    (hWK : ∀ j ∈ (outerScaleSelection F hδ hdisc hδB hupper hmass).selected,
      F.outerBody j ≤ K)
    (hunif : ∀ j ∈ (outerScaleSelection F hδ hdisc hδB hupper hmass).selected,
      ∀ j' ∈ (outerScaleSelection F hδ hdisc hδB hupper hmass).selected,
        Kakeya.densityIn (F.fiber j)
            (fun i ↦ (F.innerBody i).toConvexSpaceBody) (F.outerBody j) ≤
          Cmass *
            Kakeya.densityIn (F.fiber j')
              (fun i ↦ (F.innerBody i).toConvexSpaceBody) (F.outerBody j')) :
    ConvexSpaceBody.IsFrostmanIn
      (outerScaleSelection F hδ hdisc hδB hupper hmass).selected F.outerBody K
      (Cmass * (CFr * ((outerScaleSelectionConstant δ B : ENNReal) *
        ((fullness F.innerSet F.innerBody : NNReal) : ENNReal)⁻¹))) := by
  classical
  let S := outerScaleSelection F hδ hdisc hδB hupper hmass
  let G := selectedOuterScaleFamily F hδ hdisc hδB hupper hmass
  have hFrG : ConvexSpaceBody.IsFrostmanIn G.innerSet
      (fun i ↦ (G.innerBody i).toConvexSpaceBody) K
      (CFr * ((outerScaleSelectionConstant δ B : ENNReal) *
        ((fullness F.innerSet F.innerBody : NNReal) : ENNReal)⁻¹)) :=
    Q.selected_inner_isFrostmanIn F hδ hdisc D hδB hupper hmass hFr hFK
  have hpar : ∀ i ∈ G.innerSet, G.parent i ∈ S.selected := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hne : ∀ j ∈ S.selected, (G.fiber j).Nonempty := by
    intro j hj
    obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp (S.selected_subset hj)
    refine ⟨i, ?_⟩
    simp only [G, selectedOuterScaleFamily, FactorFamily.fiber,
      FactorFamily.restrictOuter_innerSet, Finset.mem_filter]
    exact ⟨⟨hi, hij ▸ hj⟩, hij⟩
  change ConvexSpaceBody.IsFrostmanIn S.selected G.outerBody K _
  exact ConvexSpaceBody.isFrostmanIn_parents_of_uniform_fibres
    (q := G.innerSet) (out := S.selected)
    (V := fun i ↦ (G.innerBody i).toConvexSpaceBody) (W := G.outerBody)
    (par := G.parent) (fib := G.fiber) hFrG
    (fun i hi ↦ by
      simpa only [show G.innerBody = F.innerBody from rfl] using
        hVpos i (Finset.mem_filter.mp hi).1)
    hpar
    (fun i hi ↦ G.inner_le_parent i hi)
    (by simpa only [show G.outerBody = F.outerBody from rfl, S] using hWK)
    (fun j ↦ by
      ext i
      constructor
      · intro hi
        have hi' : i ∈ G.innerSet ∧ G.parent i = j := by
          simpa only [ShadedBody.FactorFamily.fiber, Finset.mem_filter] using hi
        simpa only [Finset.mem_filter] using hi'
      · intro hi
        have hi' : i ∈ G.innerSet ∧ G.parent i = j := by
          simpa only [Finset.mem_filter] using hi
        simpa only [ShadedBody.FactorFamily.fiber, Finset.mem_filter] using hi') hne
    (by
      intro j hj j' hj'
      dsimp only [G, selectedOuterScaleFamily]
      rw [FactorFamily.restrictOuter_fiber_of_mem F S.selected hj,
        FactorFamily.restrictOuter_fiber_of_mem F S.selected hj']
      exact hunif j hj j' hj')

/-- The fixed-scale multiplicity product, pulled back to the original family selected by the
optional outer-scale wrapper.  The inverse selection constant is kept on the left so this theorem
does not hide the logarithmic loss incurred before the fixed-scale core is applied. -/
theorem FactoringAndMultPropCoreSelectScaleResult.selection_multiplicity_product
    (F : FactorFamily E ι κ) {C : ENNReal} {δ B : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (hδB : δ ≤ B)
    (hupper : ∀ j ∈ F.innerSet.image F.parent, (F.outerBody j).scale ≤ B)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade)
    (Q : FactoringAndMultPropCoreSelectScaleResult (C := C) F hδ hdisc D hδB hupper
      hmass)
    {j : κ}
    (hj : j ∈ (outerThickFamilyAtScale
      (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass) hδ
      (hdisc.restrictOuter (outerScaleSelection F hδ hdisc hδB hupper hmass).selected)
      (D.restrictOuter (outerScaleSelection F hδ hdisc hδB hupper hmass).selected
        ((outerScaleSelection F hδ hdisc hδB hupper hmass).selected_subset.trans
          F.innerSet_image_parent_subset_outerSet))
      (selectedOuterScale F hδ hdisc hδB hupper hmass) Q.scale_pos).outerSet) :
    (((outerScaleSelectionConstant δ B)⁻¹ : NNReal) : ENNReal) *
        multiplicity F.innerSet F.innerBody ≤
      (factoringCoreAtScaleUniformProductConstant (Module.finrank ℝ E)
        (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerSet.card
        (D.restrictOuter (outerScaleSelection F hδ hdisc hδB hupper hmass).selected
          ((outerScaleSelection F hδ hdisc hδB hupper hmass).selected_subset.trans
            F.innerSet_image_parent_subset_outerSet)).exponent
        (selectedOuterScale F hδ hdisc hδB hupper hmass) : ENNReal) *
        multiplicity (outerThickFamilyAtScale
          (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass) hδ
          (hdisc.restrictOuter (outerScaleSelection F hδ hdisc hδB hupper hmass).selected)
          (D.restrictOuter (outerScaleSelection F hδ hdisc hδB hupper hmass).selected
            ((outerScaleSelection F hδ hdisc hδB hupper hmass).selected_subset.trans
              F.innerSet_image_parent_subset_outerSet))
          (selectedOuterScale F hδ hdisc hδB hupper hmass) Q.scale_pos).outerSet
          (outerThickFamilyAtScale
            (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass) hδ
            (hdisc.restrictOuter (outerScaleSelection F hδ hdisc hδB hupper hmass).selected)
            (D.restrictOuter (outerScaleSelection F hδ hdisc hδB hupper hmass).selected
              ((outerScaleSelection F hδ hdisc hδB hupper hmass).selected_subset.trans
                F.innerSet_image_parent_subset_outerSet))
            (selectedOuterScale F hδ hdisc hδB hupper hmass) Q.scale_pos).outerBody *
        multiplicity ((outerThickFamilyAtScale
          (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass) hδ
          (hdisc.restrictOuter (outerScaleSelection F hδ hdisc hδB hupper hmass).selected)
          (D.restrictOuter (outerScaleSelection F hδ hdisc hδB hupper hmass).selected
            ((outerScaleSelection F hδ hdisc hδB hupper hmass).selected_subset.trans
              F.innerSet_image_parent_subset_outerSet))
          (selectedOuterScale F hδ hdisc hδB hupper hmass) Q.scale_pos).fiber j)
          (outerThickFamilyAtScale
            (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass) hδ
            (hdisc.restrictOuter (outerScaleSelection F hδ hdisc hδB hupper hmass).selected)
            (D.restrictOuter (outerScaleSelection F hδ hdisc hδB hupper hmass).selected
              ((outerScaleSelection F hδ hdisc hδB hupper hmass).selected_subset.trans
                F.innerSet_image_parent_subset_outerSet))
            (selectedOuterScale F hδ hdisc hδB hupper hmass) Q.scale_pos).innerBody := by
  calc
    (((outerScaleSelectionConstant δ B)⁻¹ : NNReal) : ENNReal) *
          multiplicity F.innerSet F.innerBody ≤
        multiplicity (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerSet
          (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerBody :=
      (Q.selection_refinement F hδ hdisc D hδB hupper hmass).mul_multiplicity_le
    _ ≤ _ := Q.core.multiplicity_product j hj

/-- The preceding estimate with the scale-selection loss moved to the right.  This is the
convenient form for consumers, while the proof makes the single logarithmic loss explicit. -/
theorem FactoringAndMultPropCoreSelectScaleResult.multiplicity_product_original
    (F : FactorFamily E ι κ) {C : ENNReal} {δ B : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (hδB : δ ≤ B)
    (hupper : ∀ j ∈ F.innerSet.image F.parent, (F.outerBody j).scale ≤ B)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade)
    (Q : FactoringAndMultPropCoreSelectScaleResult (C := C) F hδ hdisc D hδB hupper
      hmass) :
    let S := outerScaleSelection F hδ hdisc hδB hupper hmass
    let G := selectedOuterScaleFamily F hδ hdisc hδB hupper hmass
    let D' := D.restrictOuter S.selected
      (S.selected_subset.trans F.innerSet_image_parent_subset_outerSet)
    let w₁ := selectedOuterScale F hδ hdisc hδB hupper hmass
    let W := outerThickFamilyAtScale G hδ (hdisc.restrictOuter S.selected) D' w₁ Q.scale_pos
    ∀ j ∈ W.outerSet,
      multiplicity F.innerSet F.innerBody ≤
        (outerScaleSelectionConstant δ B : ENNReal) *
          (factoringCoreAtScaleUniformProductConstant (Module.finrank ℝ E)
            G.innerSet.card D'.exponent w₁ : ENNReal) *
          multiplicity W.outerSet W.outerBody * multiplicity (W.fiber j) W.innerBody := by
  dsimp only
  intro j hj
  have hprod : 0 < (outerScaleSelectionConstant δ B : ENNReal) *
      ∑ i ∈ (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerSet,
        volume ((selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerBody i).shade :=
    hmass.trans_le Q.selection_mass
  have hsel0 : (outerScaleSelectionConstant δ B : ENNReal) ≠ 0 :=
    (pos_of_mul_pos_left hprod (by positivity)).ne'
  have hsel0nn : outerScaleSelectionConstant δ B ≠ 0 := ENNReal.coe_ne_zero.mp hsel0
  have hseltop : (outerScaleSelectionConstant δ B : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hcancel : (outerScaleSelectionConstant δ B : ENNReal) *
      (((outerScaleSelectionConstant δ B)⁻¹ : NNReal) : ENNReal) = 1 := by
    rw [ENNReal.coe_inv hsel0nn]
    exact ENNReal.mul_inv_cancel hsel0 hseltop
  calc
    multiplicity F.innerSet F.innerBody =
        (outerScaleSelectionConstant δ B : ENNReal) *
          (((outerScaleSelectionConstant δ B)⁻¹ : NNReal) : ENNReal) *
          multiplicity F.innerSet F.innerBody := by rw [hcancel, one_mul]
    _ = (outerScaleSelectionConstant δ B : ENNReal) *
          ((((outerScaleSelectionConstant δ B)⁻¹ : NNReal) : ENNReal) *
            multiplicity F.innerSet F.innerBody) := by ring
    _ ≤ (outerScaleSelectionConstant δ B : ENNReal) *
          ((factoringCoreAtScaleUniformProductConstant (Module.finrank ℝ E)
              (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerSet.card
              (D.restrictOuter
                (outerScaleSelection F hδ hdisc hδB hupper hmass).selected
                ((outerScaleSelection F hδ hdisc hδB hupper hmass).selected_subset.trans
                  F.innerSet_image_parent_subset_outerSet)).exponent
              (selectedOuterScale F hδ hdisc hδB hupper hmass) : ENNReal) *
            multiplicity (outerThickFamilyAtScale
              (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass) hδ
              (hdisc.restrictOuter
                (outerScaleSelection F hδ hdisc hδB hupper hmass).selected)
              (D.restrictOuter
                (outerScaleSelection F hδ hdisc hδB hupper hmass).selected
                ((outerScaleSelection F hδ hdisc hδB hupper hmass).selected_subset.trans
                  F.innerSet_image_parent_subset_outerSet))
              (selectedOuterScale F hδ hdisc hδB hupper hmass) Q.scale_pos).outerSet
              (outerThickFamilyAtScale
                (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass) hδ
                (hdisc.restrictOuter
                  (outerScaleSelection F hδ hdisc hδB hupper hmass).selected)
                (D.restrictOuter
                  (outerScaleSelection F hδ hdisc hδB hupper hmass).selected
                  ((outerScaleSelection F hδ hdisc hδB hupper hmass).selected_subset.trans
                    F.innerSet_image_parent_subset_outerSet))
                (selectedOuterScale F hδ hdisc hδB hupper hmass) Q.scale_pos).outerBody *
            multiplicity ((outerThickFamilyAtScale
              (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass) hδ
              (hdisc.restrictOuter
                (outerScaleSelection F hδ hdisc hδB hupper hmass).selected)
              (D.restrictOuter
                (outerScaleSelection F hδ hdisc hδB hupper hmass).selected
                ((outerScaleSelection F hδ hdisc hδB hupper hmass).selected_subset.trans
                  F.innerSet_image_parent_subset_outerSet))
              (selectedOuterScale F hδ hdisc hδB hupper hmass) Q.scale_pos).fiber j)
              (outerThickFamilyAtScale
                (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass) hδ
                (hdisc.restrictOuter
                  (outerScaleSelection F hδ hdisc hδB hupper hmass).selected)
                (D.restrictOuter
                  (outerScaleSelection F hδ hdisc hδB hupper hmass).selected
                  ((outerScaleSelection F hδ hdisc hδB hupper hmass).selected_subset.trans
                    F.innerSet_image_parent_subset_outerSet))
                (selectedOuterScale F hδ hdisc hδB hupper hmass) Q.scale_pos).innerBody) := by
      exact mul_le_mul_right
        (Q.selection_multiplicity_product F hδ hdisc D hδB hupper hmass hj) _
    _ = _ := by ring

/-- The optional wrapper selects one outer scale by shading mass, then invokes the canonical
core. -/
theorem factoringAndMultPropCoreSelectScale
    (F : FactorFamily E ι κ) {C : ENNReal} {δ B : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (hδB : δ ≤ B)
    (hupper : ∀ j ∈ F.innerSet.image F.parent, (F.outerBody j).scale ≤ B)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade)
    (hdim : Module.finrank ℝ E = 3) (hshape : F.InnerHasSimilarShape 2)
    (hFrostman : F.HasFrostmanFibers C) :
    FactoringAndMultPropCoreSelectScaleResult (C := C) F hδ hdisc D hδB hupper hmass := by
  let Q := outerScaleSelection F hδ hdisc hδB hupper hmass
  let ht : Q.selected ⊆ F.outerSet := Q.selected_subset.trans
    F.innerSet_image_parent_subset_outerSet
  let G := selectedOuterScaleFamily F hδ hdisc hδB hupper hmass
  let w₁ := selectedOuterScale F hδ hdisc hδB hupper hmass
  let hw₁ := selectedOuterScale_pos F hδ hdisc hδB hupper hmass
  have hmassG :
      ∑ i ∈ F.innerSet, volume (F.innerBody i).shade ≤
        (outerScaleSelectionConstant δ B : ENNReal) *
          ∑ i ∈ G.innerSet, volume (G.innerBody i).shade := by
    rw [show G.innerSet = {i ∈ F.innerSet | F.parent i ∈ Q.selected} by
      rfl]
    rw [show G.innerBody = F.innerBody by rfl]
    calc
      ∑ i ∈ F.innerSet, volume (F.innerBody i).shade ≤
          (outerScaleSelectionConstant δ B : ENNReal) *
            ∑ j ∈ Q.selected, ∑ i ∈ F.innerSet with F.parent i = j,
              volume (F.innerBody i).shade := Q.mass_refinement
      _ = (outerScaleSelectionConstant δ B : ENNReal) *
          ∑ i ∈ {i ∈ F.innerSet | F.parent i ∈ Q.selected},
            volume (F.innerBody i).shade := by
        congr 1
        exact Finset.sum_fiberwise_eq_sum_filter F.innerSet Q.selected F.parent
          (fun i ↦ volume (F.innerBody i).shade)
  refine {
    scale_pos := hw₁
    selection_mass := by simpa only [G] using hmassG
    core := factoringAndMultPropCoreAtScale G hδ
      (hdisc.restrictOuter Q.selected) (D.restrictOuter Q.selected ht) w₁ hw₁
      (selectedOuterScaleFamily_outerIsAtScale F hδ hdisc hδB hupper hmass)
      hdim (hshape.restrictOuter Q.selected) (hFrostman.restrictOuter Q.selected ht) }

/-- The scale-selecting wrapper under GWZ Remark 5.3's thickened-Frostman hypothesis.  The
selected subfamily keeps complete fine fibres, so coarse tubes used to establish the hypothesis
never replace the fine inner indices. -/
theorem factoringAndMultPropCoreSelectScale_of_thickenedFrostman
    (F : FactorFamily E ι κ) {C : ENNReal} {δ B : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (hδB : δ ≤ B)
    (hupper : ∀ j ∈ F.innerSet.image F.parent, (F.outerBody j).scale ≤ B)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade)
    (hdim : Module.finrank ℝ E = 3) (hshape : F.InnerHasSimilarShape 2)
    (hFrostman : F.HasThickenedFrostmanFibers C) :
    FactoringAndMultPropCoreSelectScaleResult (C := C) F hδ hdisc D hδB hupper hmass := by
  let Q := outerScaleSelection F hδ hdisc hδB hupper hmass
  let ht : Q.selected ⊆ F.outerSet := Q.selected_subset.trans
    F.innerSet_image_parent_subset_outerSet
  let G := selectedOuterScaleFamily F hδ hdisc hδB hupper hmass
  let w₁ := selectedOuterScale F hδ hdisc hδB hupper hmass
  let hw₁ := selectedOuterScale_pos F hδ hdisc hδB hupper hmass
  have hmassG :
      ∑ i ∈ F.innerSet, volume (F.innerBody i).shade ≤
        (outerScaleSelectionConstant δ B : ENNReal) *
          ∑ i ∈ G.innerSet, volume (G.innerBody i).shade := by
    rw [show G.innerSet = {i ∈ F.innerSet | F.parent i ∈ Q.selected} by
      rfl]
    rw [show G.innerBody = F.innerBody by rfl]
    calc
      ∑ i ∈ F.innerSet, volume (F.innerBody i).shade ≤
          (outerScaleSelectionConstant δ B : ENNReal) *
            ∑ j ∈ Q.selected, ∑ i ∈ F.innerSet with F.parent i = j,
              volume (F.innerBody i).shade := Q.mass_refinement
      _ = (outerScaleSelectionConstant δ B : ENNReal) *
          ∑ i ∈ {i ∈ F.innerSet | F.parent i ∈ Q.selected},
            volume (F.innerBody i).shade := by
        congr 1
        exact Finset.sum_fiberwise_eq_sum_filter F.innerSet Q.selected F.parent
          (fun i ↦ volume (F.innerBody i).shade)
  refine {
    scale_pos := hw₁
    selection_mass := by simpa only [G] using hmassG
    core := factoringAndMultPropCoreAtScale_of_thickenedFrostman G hδ
      (hdisc.restrictOuter Q.selected) (D.restrictOuter Q.selected ht) w₁ hw₁
      (selectedOuterScaleFamily_outerIsAtScale F hδ hdisc hδB hupper hmass)
      hdim (hshape.restrictOuter Q.selected)
      (hFrostman.restrictOuter Q.selected ht) }

end ShadedBody
