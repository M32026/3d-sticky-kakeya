/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.HybridParentPacking
public import Kakeya.Tube.Rescale

/-!
# Counting essentially distinct assigned parents through a leaf

This file supplies the cross-parent packing input used by the corrected proof of GWZ
Proposition 6.6(A).  The assignment of a fine tube to a coarse parent need not be geometrically
unique.  Instead, the actual coarse parent family is assumed pairwise essentially distinct.

If a fine tube assigned to `R k` lies both in a fixed dilation of `R k` and in a test tube whose
radius is a fixed multiple of the parent radius, then `R k` lies in a fixed dilation of the test
tube's core.  Consequently only boundedly many pairwise essentially distinct parents can
contribute to one test tube.  This is the precise replacement for the unsupported same-parent
identity in the printed proof of Proposition 6.6(A).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Kakeya

namespace edParentCount

/-- The intermediate dilation used to compare a parent and a test tube through a common leaf.

It depends only on the fixed parent-dilation ratio `D` and test-radius ratio `Ctest`.  The generous
quadratic expression keeps all three elementary longitudinal and transverse budgets transparent.
-/
def comparisonDilate (D Ctest : NNReal) : ℝ :=
  8 * ((D : ℝ) + (Ctest : ℝ) + 1) ^ 2

/-- The final dilation after reversing the comparison from the common leaf to the test tube. -/
def finalDilate (D Ctest : NNReal) : ℝ :=
  6 * (comparisonDilate D Ctest) ^ 2 + 2 * comparisonDilate D Ctest

/-- Constant in the essentially-distinct assigned-parent count. -/
def C (n : ℕ) (D Ctest : NNReal) : NNReal :=
  Tube.essDistinctTubesInSelfDilate.C n (finalDilate D Ctest)

/-- The comparison dilation when the common leaf is contained only in an `L`-dilate of the
test tube.  The first term is the direct-test comparison above; the other two are exactly the
longitudinal and transverse budgets of `Tube.subset_dilate_rescale_of_subset_dilate`. -/
def comparisonDilateOfTestDilate (D Ctest L : NNReal) : ℝ :=
  max (comparisonDilate D Ctest) (max (2 * (L : ℝ)) (6 * (L : ℝ) ^ 2 * (Ctest : ℝ)))

/-- Final parent/test comparison dilation when the leaf lies in an `L`-dilate of the test tube. -/
def finalDilateOfTestDilate (D Ctest L : NNReal) : ℝ :=
  6 * (comparisonDilateOfTestDilate D Ctest L) ^ 2 +
    2 * comparisonDilateOfTestDilate D Ctest L

/-- Constant in the assigned-parent count with a dilated test tube. -/
def COfTestDilate (n : ℕ) (D Ctest L : NNReal) : NNReal :=
  Tube.essDistinctTubesInSelfDilate.C n (finalDilateOfTestDilate D Ctest L)

theorem one_le_comparisonDilate {D Ctest : NNReal} (hD : 1 ≤ D) (hCtest : 1 ≤ Ctest) :
    1 ≤ comparisonDilate D Ctest := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hC' : (1 : ℝ) ≤ Ctest := by exact_mod_cast hCtest
  unfold comparisonDilate
  nlinarith [sq_nonneg ((D : ℝ) + (Ctest : ℝ) + 1)]

theorem one_le_finalDilate {D Ctest : NNReal} (hD : 1 ≤ D) (hCtest : 1 ≤ Ctest) :
    1 ≤ finalDilate D Ctest := by
  have hc := one_le_comparisonDilate hD hCtest
  unfold finalDilate
  nlinarith [sq_nonneg (comparisonDilate D Ctest)]

theorem comparisonDilate_le_comparisonDilateOfTestDilate (D Ctest L : NNReal) :
    comparisonDilate D Ctest ≤ comparisonDilateOfTestDilate D Ctest L :=
  le_max_left _ _

theorem two_mul_L_le_comparisonDilateOfTestDilate (D Ctest L : NNReal) :
    2 * (L : ℝ) ≤ comparisonDilateOfTestDilate D Ctest L :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem six_mul_L_sq_mul_Ctest_le_comparisonDilateOfTestDilate (D Ctest L : NNReal) :
    6 * (L : ℝ) ^ 2 * (Ctest : ℝ) ≤ comparisonDilateOfTestDilate D Ctest L :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem one_le_comparisonDilateOfTestDilate {D Ctest L : NNReal}
    (hD : 1 ≤ D) (hCtest : 1 ≤ Ctest) :
    1 ≤ comparisonDilateOfTestDilate D Ctest L :=
  (one_le_comparisonDilate hD hCtest).trans
    (comparisonDilate_le_comparisonDilateOfTestDilate D Ctest L)

theorem one_le_finalDilateOfTestDilate {D Ctest L : NNReal}
    (hD : 1 ≤ D) (hCtest : 1 ≤ Ctest) :
    1 ≤ finalDilateOfTestDilate D Ctest L := by
  have hc := one_le_comparisonDilateOfTestDilate (L := L) hD hCtest
  unfold finalDilateOfTestDilate
  nlinarith [sq_nonneg (comparisonDilateOfTestDilate D Ctest L)]

theorem two_mul_D_le_comparisonDilate {D Ctest : NNReal} (hD : 1 ≤ D) :
    2 * (D : ℝ) ≤ comparisonDilate D Ctest := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hC0 : (0 : ℝ) ≤ Ctest := NNReal.coe_nonneg Ctest
  unfold comparisonDilate
  nlinarith [sq_nonneg ((D : ℝ) + (Ctest : ℝ) + 1 - 1)]

theorem six_mul_D_sq_le_comparisonDilate {D Ctest : NNReal} (hD : 1 ≤ D) :
    6 * (D : ℝ) ^ 2 ≤ comparisonDilate D Ctest := by
  have hD0 : (0 : ℝ) ≤ D := NNReal.coe_nonneg D
  have hC0 : (0 : ℝ) ≤ Ctest := NNReal.coe_nonneg Ctest
  unfold comparisonDilate
  nlinarith [sq_nonneg ((D : ℝ) + (Ctest : ℝ) + 1),
    sq_nonneg ((Ctest : ℝ) + 1), mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ D)
      (by linarith : (D : ℝ) ≤ D + Ctest + 1)]

theorem four_mul_Ctest_le_comparisonDilate {D Ctest : NNReal} (hCtest : 1 ≤ Ctest) :
    4 * (Ctest : ℝ) ≤ comparisonDilate D Ctest := by
  have hC' : (1 : ℝ) ≤ Ctest := by exact_mod_cast hCtest
  have hD0 : (0 : ℝ) ≤ D := NNReal.coe_nonneg D
  unfold comparisonDilate
  nlinarith [sq_nonneg ((D : ℝ) + (Ctest : ℝ) + 1 - 1)]

/-- A parent and a test tube are uniformly comparable through one common assigned leaf.

The fine tube `U` is allowed to lie in a fixed dilation `D · R` rather than in `R` itself.  The
test tube has radius `Ctest * ρ`, while the parent has radius `ρ`.  The conclusion is at the
parent scale: the parent lies in a fixed dilation of the `ρ`-rescale of the test tube.
-/
theorem parent_subset_testDilate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    {σ ρ D Ctest : NNReal} (hρ0 : 0 < ρ) (hD : 1 ≤ D) (hCtest : 1 ≤ Ctest)
    (R : Tube ρ E) (U : Tube σ E) (V : Tube (Ctest * ρ) E)
    (hUR : U.toConvexSpaceBody ≤ Tube.dilate R (D : ℝ))
    (hUV : U.toConvexSpaceBody ≤ V.toConvexSpaceBody) :
    R.carrier ⊆
      (Tube.dilate (V.rescale ρ) (finalDilate D Ctest)).carrier := by
  let c : ℝ := comparisonDilate D Ctest
  have hc1 : 1 ≤ c := one_le_comparisonDilate hD hCtest
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hD0 : 0 < (D : ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hD)
  have hρr : 0 < (ρ : ℝ) := by exact_mod_cast hρ0
  have hparentK : (Tube.dilate R (D : ℝ)).carrier ⊆
      (Tube.dilate (U.rescale ρ) c).carrier := by
    apply Tube.subset_dilate_rescale_of_subset_dilate
        (T := R) (T₀ := U) (c := (D : ℝ)) (Λ := c)
        (ρ := ρ) (K := (Tube.dilate R (D : ℝ)).carrier)
    · exact_mod_cast hD
    · exact two_mul_D_le_comparisonDilate hD
    · have hbudget := six_mul_D_sq_le_comparisonDilate (D := D) (Ctest := Ctest) hD
      nlinarith
    · exact hUR
    · exact Set.Subset.rfl
  have hRmid : R.carrier ⊆ (Tube.dilate (U.rescale ρ) c).carrier :=
    (Tube.subset_dilate R (by exact_mod_cast hD)).trans hparentK
  have hVleU : V.toConvexSpaceBody ≤ (U.rescale (4 * (Ctest * ρ))).toConvexSpaceBody :=
    Tube.rescale_le_of_le U V hUV
  have hfatU : (U.rescale (4 * (Ctest * ρ))).toConvexSpaceBody ≤
      Tube.dilate (U.rescale ρ) c := by
    apply Tube.rescale_le_dilate_of_le_mul (T := U.rescale ρ) hc1
    have h4 := four_mul_Ctest_le_comparisonDilate (D := D) hCtest
    push_cast
    nlinarith
  have hρtest : ρ ≤ Ctest * ρ := by
    calc
      ρ = ρ * 1 := by rw [mul_one]
      _ ≤ ρ * Ctest := mul_le_mul_of_nonneg_left hCtest (by positivity)
      _ = Ctest * ρ := mul_comm ρ Ctest
  have hVsmall : (V.rescale ρ).toConvexSpaceBody ≤ V.toConvexSpaceBody := by
    calc
      (V.rescale ρ).toConvexSpaceBody
          ≤ (V.rescale (Ctest * ρ)).toConvexSpaceBody :=
        Tube.rescale_le_rescale_of_radius_le V hρtest
      _ = V.toConvexSpaceBody := Tube.toConvexSpaceBody_rescale_self V
  have hVmid : (V.rescale ρ).carrier ⊆ (Tube.dilate (U.rescale ρ) c).carrier := by
    exact le_trans hVsmall (le_trans hVleU hfatU)
  have hreverse : (Tube.dilate (U.rescale ρ) c).carrier ⊆
      (Tube.dilate (V.rescale ρ) (finalDilate D Ctest)).carrier := by
    apply Tube.subset_dilate_rescale_of_subset_dilate
        (T := U.rescale ρ) (T₀ := V.rescale ρ) (c := c)
        (Λ := finalDilate D Ctest) (ρ := ρ)
        (K := (Tube.dilate (U.rescale ρ) c).carrier)
    · exact hc1
    · unfold finalDilate
      nlinarith [sq_nonneg c]
    · unfold finalDilate
      nlinarith [sq_nonneg c]
    · exact hVmid
    · exact Set.Subset.rfl
  exact hRmid.trans hreverse

/-- A parent and a test tube are uniformly comparable when their common assigned leaf lies only
in a fixed dilation of the test tube.  This is the form used after a plank-shaped test body is
enclosed in a tube: the enclosure costs `L`, but the number of parents remains absolute. -/
theorem parent_subset_testDilate_of_subset_dilate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    {σ ρ D Ctest L : NNReal} (hρ0 : 0 < ρ) (hD : 1 ≤ D) (hCtest : 1 ≤ Ctest)
    (hL : 1 ≤ L) (R : Tube ρ E) (U : Tube σ E) (V : Tube (Ctest * ρ) E)
    (hUR : U.toConvexSpaceBody ≤ Tube.dilate R (D : ℝ))
    (hUV : U.toConvexSpaceBody ≤ Tube.dilate V (L : ℝ)) :
    R.carrier ⊆
      (Tube.dilate (V.rescale ρ) (finalDilateOfTestDilate D Ctest L)).carrier := by
  let c : ℝ := comparisonDilateOfTestDilate D Ctest L
  have hc1 : 1 ≤ c := one_le_comparisonDilateOfTestDilate hD hCtest
  have hD0 : 0 < (D : ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hD)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hρr : 0 < (ρ : ℝ) := by exact_mod_cast hρ0
  have hparentK : (Tube.dilate R (D : ℝ)).carrier ⊆
      (Tube.dilate (U.rescale ρ) c).carrier := by
    apply Tube.subset_dilate_rescale_of_subset_dilate
        (T := R) (T₀ := U) (c := (D : ℝ)) (Λ := c)
        (ρ := ρ) (K := (Tube.dilate R (D : ℝ)).carrier)
    · exact_mod_cast hD
    · exact (two_mul_D_le_comparisonDilate hD).trans
        (comparisonDilate_le_comparisonDilateOfTestDilate D Ctest L)
    · have hbudget := (six_mul_D_sq_le_comparisonDilate (D := D) (Ctest := Ctest) hD).trans
        (comparisonDilate_le_comparisonDilateOfTestDilate D Ctest L)
      nlinarith
    · exact hUR
    · exact Set.Subset.rfl
  have hRmid : R.carrier ⊆ (Tube.dilate (U.rescale ρ) c).carrier :=
    (Tube.subset_dilate R (by exact_mod_cast hD)).trans hparentK
  have htestK : (Tube.dilate V (L : ℝ)).carrier ⊆
      (Tube.dilate (U.rescale ρ) c).carrier := by
    apply Tube.subset_dilate_rescale_of_subset_dilate
        (T := V) (T₀ := U) (c := (L : ℝ)) (Λ := c)
        (ρ := ρ) (K := (Tube.dilate V (L : ℝ)).carrier)
    · exact hL1
    · exact two_mul_L_le_comparisonDilateOfTestDilate D Ctest L
    · have hbudget :=
          six_mul_L_sq_mul_Ctest_le_comparisonDilateOfTestDilate D Ctest L
      have hbudgetρ := mul_le_mul_of_nonneg_right hbudget (NNReal.coe_nonneg ρ)
      dsimp only [c]
      push_cast
      nlinarith
    · exact hUV
    · exact Set.Subset.rfl
  have hρtest : ρ ≤ Ctest * ρ := by
    calc
      ρ = ρ * 1 := by rw [mul_one]
      _ ≤ ρ * Ctest := mul_le_mul_of_nonneg_left hCtest (by positivity)
      _ = Ctest * ρ := mul_comm ρ Ctest
  have hVsmall : (V.rescale ρ).toConvexSpaceBody ≤ V.toConvexSpaceBody := by
    calc
      (V.rescale ρ).toConvexSpaceBody ≤
          (V.rescale (Ctest * ρ)).toConvexSpaceBody :=
        Tube.rescale_le_rescale_of_radius_le V hρtest
      _ = V.toConvexSpaceBody := Tube.toConvexSpaceBody_rescale_self V
  have hVmid : (V.rescale ρ).carrier ⊆ (Tube.dilate (U.rescale ρ) c).carrier :=
    le_trans hVsmall <| (Tube.subset_dilate V hL1).trans htestK
  have hreverse : (Tube.dilate (U.rescale ρ) c).carrier ⊆
      (Tube.dilate (V.rescale ρ) (finalDilateOfTestDilate D Ctest L)).carrier := by
    apply Tube.subset_dilate_rescale_of_subset_dilate
        (T := U.rescale ρ) (T₀ := V.rescale ρ) (c := c)
        (Λ := finalDilateOfTestDilate D Ctest L) (ρ := ρ)
        (K := (Tube.dilate (U.rescale ρ) c).carrier)
    · exact hc1
    · unfold finalDilateOfTestDilate
      nlinarith [sq_nonneg c]
    · unfold finalDilateOfTestDilate
      nlinarith [sq_nonneg c]
    · exact hVmid
    · exact Set.Subset.rfl
  exact hRmid.trans hreverse

/-- Pairwise essentially distinct assigned parents have bounded overlap through fine leaves.

No uniqueness of the geometric parent is asserted or used.  The filter counts only the label
actually assigned to the witnessing leaf, matching the parent-map fibres used by Proposition 5.1.
-/
theorem card_assignedParents_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    {ι κ : Type*} [DecidableEq κ]
    {σ ρ D Ctest : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hD : 1 ≤ D) (hCtest : 1 ≤ Ctest)
    (q : Finset ι) (T : ι → Tube σ E) (r : Finset κ) (R : κ → Tube ρ E)
    (assign : ι → κ)
    (hED : (↑r : Set κ).Pairwise fun k l =>
      IsEssentiallyDistinct (R k).carrier (R l).carrier)
    (hassign : ∀ i ∈ q, assign i ∈ r ∧
      (T i).toConvexSpaceBody ≤ Tube.dilate (R (assign i)) (D : ℝ))
    (V : Tube (Ctest * ρ) E) :
    ((r.filter fun k => ∃ i ∈ q, assign i = k ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody).card : ENNReal)
      ≤ (C (Module.finrank ℝ E) D Ctest : ENNReal) := by
  classical
  let a : Finset κ := r.filter fun k => ∃ i ∈ q, assign i = k ∧
    (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody
  have hEDa : (↑a : Set κ).Pairwise fun k l =>
      IsEssentiallyDistinct (R k).carrier (R l).carrier := by
    intro k hk l hl hkl
    exact hED (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hl).1 hkl
  have hsub : ∀ k ∈ a, (R k).carrier ⊆
      (Tube.dilate (V.rescale ρ) (finalDilate D Ctest)).carrier := by
    intro k hk
    rcases (Finset.mem_filter.mp hk).2 with ⟨i, hiq, hik, hiV⟩
    subst k
    exact parent_subset_testDilate hρ0 hD hCtest (R (assign i)) (T i) V
      (hassign i hiq).2 hiV
  have hpack := Tube.essDistinctTubesInSelfDilate
    (E := E) (δ := ρ) (c := finalDilate D Ctest)
    (one_le_finalDilate hD hCtest) hρ0 hρ1 (V.rescale ρ) a R hEDa hsub
  simpa only [a, C] using hpack

/-- Pairwise essentially distinct assigned parents have bounded overlap through leaves contained
in a fixed dilation of a test tube. -/
theorem card_assignedParents_le_of_subset_dilate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    {ι κ : Type*} [DecidableEq κ]
    {σ ρ D Ctest L : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hD : 1 ≤ D) (hCtest : 1 ≤ Ctest) (hL : 1 ≤ L)
    (q : Finset ι) (T : ι → Tube σ E) (r : Finset κ) (R : κ → Tube ρ E)
    (assign : ι → κ)
    (hED : (↑r : Set κ).Pairwise fun k l ↦
      IsEssentiallyDistinct (R k).carrier (R l).carrier)
    (hassign : ∀ i ∈ q, assign i ∈ r ∧
      (T i).toConvexSpaceBody ≤ Tube.dilate (R (assign i)) (D : ℝ))
    (V : Tube (Ctest * ρ) E) :
    ((r.filter fun k ↦ ∃ i ∈ q, assign i = k ∧
        (T i).toConvexSpaceBody ≤ Tube.dilate V (L : ℝ)).card : ENNReal)
      ≤ (COfTestDilate (Module.finrank ℝ E) D Ctest L : ENNReal) := by
  classical
  let a : Finset κ := r.filter fun k ↦ ∃ i ∈ q, assign i = k ∧
    (T i).toConvexSpaceBody ≤ Tube.dilate V (L : ℝ)
  have hEDa : (↑a : Set κ).Pairwise fun k l ↦
      IsEssentiallyDistinct (R k).carrier (R l).carrier := by
    intro k hk l hl hkl
    exact hED (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hl).1 hkl
  have hsub : ∀ k ∈ a, (R k).carrier ⊆
      (Tube.dilate (V.rescale ρ) (finalDilateOfTestDilate D Ctest L)).carrier := by
    intro k hk
    rcases (Finset.mem_filter.mp hk).2 with ⟨i, hiq, hik, hiV⟩
    subst k
    exact parent_subset_testDilate_of_subset_dilate hρ0 hD hCtest hL
      (R (assign i)) (T i) V (hassign i hiq).2 hiV
  have hpack := Tube.essDistinctTubesInSelfDilate
    (E := E) (δ := ρ) (c := finalDilateOfTestDilate D Ctest L)
    (one_le_finalDilateOfTestDilate hD hCtest) hρ0 hρ1 (V.rescale ρ) a R hEDa hsub
  simpa only [a, COfTestDilate] using hpack

end edParentCount

end Kakeya

end

end
