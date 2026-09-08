/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Asymptotics
public import Kakeya.ConvexBody
public import Kakeya.DimensionThree.BushCount.Regimes
public import Kakeya.Multiplicity
public import Kakeya.Tube.Basic
public import Kakeya.Tube.CardEssentiallyDistinct
public import Kakeya.Tube.BushSeparation

/-!
# The bush bound in `ℝ ^ 3`

Only `O(δ ^ (-2))` pairwise essentially distinct `δ`-tubes in `ℝ ^ 3` can pass through a
single point. This file combines the two regimes of
`Kakeya/DimensionThree/BushCount/Regimes.lean`, where the geometry lives, and states the
bound in the three forms its consumers use: the universe-free existential
`Kakeya.bushCount_exists`, the pointwise `Kakeya.bushCount`, and the multiplicity bound
`Kakeya.multiplicity_le_bushCount` for an arbitrary shading.

The bound is a statement about tubes alone, so it is stated here for its own sake. Its
consequences for `Kakeya.FrostmanEstimate` are drawn elsewhere: the base case `K_F(1)` in
`Kakeya/DimensionThree/FrostmanOne.lean`, and the sharp upper bound for `P = |s| * δ ^ 2` in
`Kakeya/DimensionThree/MainLemma1/SizeUpper.lean`.
-/

@[expose] public section

namespace Kakeya

/-! ### The bush bound -/

/-- [Bush bound, existential form]
There is an absolute constant `C ≥ 1` such that for `δ ≤ bushSeparation.δ` at most
`C * δ ^ (-2)` pairwise essentially distinct `δ`-tubes of `ℝ ^ 3` pass through a common
point. The statement is phrased for families indexed by `Fin n` so that the constant `C`
carries no universe parameter; `Kakeya.bushCount` transports it to an arbitrary index type.

The two regimes `δ ≤ δ₀` and `δ₀ < δ` are `Kakeya.bushCount.exists_bound_small` and
`Kakeya.bushCount.exists_bound_large`, and `δ = 0` is trivial because the right-hand side
is then `⊤`. -/
theorem bushCount_exists : ∃ C : NNReal, 1 ≤ C ∧
    ∀ (δ : NNReal), δ ≤ bushSeparation.δ → ∀ (n : ℕ)
      (T : Fin n → Tube δ (EuclideanSpace ℝ (Fin 3))),
      Pairwise (fun i j ↦ IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      ∀ x : EuclideanSpace ℝ (Fin 3), (∀ i, x ∈ (T i).carrier) →
        (n : ENNReal) ≤ C * (δ : ENNReal) ^ (-2 : ℝ) := by
  obtain ⟨δ₀, K₁, hδ₀_pos, hδ₀_le1, hsmall⟩ := bushCount.exists_bound_small
  obtain ⟨K₂, hlarge⟩ := bushCount.exists_bound_large hδ₀_pos
  set C : NNReal := max 1 (max (K₁ : NNReal) (K₂ : NNReal)) with hCdef
  have hC_one : 1 ≤ C := le_max_left _ _
  have hC_K₁ : (K₁ : NNReal) ≤ C :=
    calc
      (K₁ : NNReal) ≤ max (K₁ : NNReal) (K₂ : NNReal) := le_max_left _ _
      _ ≤ C := le_max_right _ _
  have hC_K₂ : (K₂ : NNReal) ≤ C :=
    calc
      (K₂ : NNReal) ≤ max (K₁ : NNReal) (K₂ : NNReal) := le_max_right _ _
      _ ≤ C := le_max_right _ _
  have hC_K₁_real : (K₁ : ℝ) ≤ (C : ℝ) := NNReal.coe_le_coe.mpr hC_K₁
  have hC_K₂_real : (K₂ : ℝ) ≤ (C : ℝ) := NNReal.coe_le_coe.mpr hC_K₂
  refine ⟨C, hC_one, ?_⟩
  intro δ hδ_le n T hPairwise x hx_all
  by_cases hδ0 : δ = 0
  · subst hδ0
    have hzero_rpow : (0 : ENNReal) ^ (-2 : ℝ) = ⊤ := by
      refine ENNReal.zero_rpow_of_neg ?_
      norm_num
    have hC_ne_zero : (C : ENNReal) ≠ 0 := by
      have hC_pos : 0 < (C : ℝ) := by
        calc
          (0 : ℝ) < 1 := by norm_num
          _ ≤ (C : ℝ) := by exact_mod_cast hC_one
      exact ENNReal.coe_ne_zero.mpr (ne_of_gt hC_pos)
    calc
      (n : ENNReal) ≤ ⊤ := le_top
      _ = (C : ENNReal) * (0 : ENNReal) ^ (-2 : ℝ) := by
        rw [hzero_rpow, ENNReal.mul_top hC_ne_zero]
  · have hδ_pos : 0 < δ := pos_iff_ne_zero.mpr hδ0
    have hδ_real_pos : 0 < (δ : ℝ) := by exact_mod_cast hδ_pos
    have hδ_real_le_one : (δ : ℝ) ≤ 1 := by
      have hδ_sep_le_one : bushSeparation.δ ≤ 1 := bushSeparation.δ_le_one
      have : (δ : ℝ) ≤ (bushSeparation.δ : ℝ) := by exact_mod_cast hδ_le
      exact this.trans (by exact_mod_cast hδ_sep_le_one)
    have hcard_s : ((Finset.univ : Finset (Fin n)).card : ℝ) = (n : ℝ) := by simp
    by_cases hδ_small : (δ : ℝ) ≤ δ₀
    · -- small regime δ ≤ δ₀
      have hbound := hsmall hδ_real_pos hδ_small (Finset.univ : Finset (Fin n)) T
        (by
          intro i hi j hj hij
          exact hPairwise hij)
        x (by
          intro i hi
          exact hx_all i)
      rw [hcard_s] at hbound
      have hbound' : (n : ℝ) * (δ : ℝ) ^ (2 : ℕ) ≤ (C : ℝ) := by
        calc
          (n : ℝ) * (δ : ℝ) ^ (2 : ℕ) ≤ (K₁ : ℝ) := hbound
          _ ≤ (C : ℝ) := hC_K₁_real
      exact ENNReal.natCast_le_coe_mul_rpow_neg_two hδ_pos hbound'
    · -- large regime δ₀ < δ
      have hδ_large : δ₀ < (δ : ℝ) := by
        by_contra! hnot
        exact hδ_small hnot
      have hbound := hlarge hδ_real_pos hδ_real_le_one hδ_large (Finset.univ : Finset (Fin n)) T
        (by
          intro i hi j hj hij
          exact hPairwise hij)
        x (by
          intro i hi
          exact hx_all i)
      rw [hcard_s] at hbound
      have hbound' : (n : ℝ) * (δ : ℝ) ^ (2 : ℕ) ≤ (C : ℝ) := by
        calc
          (n : ℝ) * (δ : ℝ) ^ (2 : ℕ) ≤ (K₂ : ℝ) := hbound
          _ ≤ (C : ℝ) := hC_K₂_real
      exact ENNReal.natCast_le_coe_mul_rpow_neg_two hδ_pos hbound'

/-- The constant in the bush bound `Kakeya.bushCount`, an absolute constant (the ambient
dimension is `3` throughout). It is the constant produced by `Kakeya.bushCount_exists`, and
is therefore not given by a closed formula: the direction classes are counted by
`Metric.exists_finset_sphere_net` (contributing `192 * δ ^ (-2)` classes in dimension `3`),
while the number of tubes per class comes from the packing bound
`Kakeya.packing_card_le_of_features`, whose constant is obtained from the finite labelings of
`Kakeya.finite_label_of_bounded` and is not computed explicitly. Only `1 ≤ bushCount.C` is
used downstream. -/
noncomputable def bushCount.C : NNReal := bushCount_exists.choose

lemma bushCount.one_le_C : 1 ≤ bushCount.C := bushCount_exists.choose_spec.1

lemma bushCount.C_pos : 0 < bushCount.C := lt_of_lt_of_le zero_lt_one bushCount.one_le_C

/-- [Bush bound: essentially distinct `δ`-tubes through a point]
For `δ ≤ bushSeparation.δ`, a finite family of pairwise essentially distinct
`δ`-tubes in `ℝ ^ 3` has at most `bushCount.C * δ ^ (-2)` members through any given point.
(No positivity assumption on `δ` is needed: for `δ = 0` the right-hand side is `⊤`.)

This is `Kakeya.bushCount_exists` transported from `Fin n` to an arbitrary index type along
`Finset.equivFin` applied to the subfamily of tubes through `x`. -/
theorem bushCount {δ : NNReal} (hδ_le : δ ≤ bushSeparation.δ)
    {ι : Type*} (s : Finset ι) (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3)))
    (hED : (s : Set ι).Pairwise
      fun i j ↦ IsEssentiallyDistinct (T i).carrier (T j).carrier)
    (x : EuclideanSpace ℝ (Fin 3)) :
    (Finset.multiplicityAt s (fun i ↦ (T i).toConvexSpaceBody) x : ENNReal) ≤
      bushCount.C * (δ : ENNReal) ^ (-2 : ℝ) := by
  classical
  let s' := s.filter fun i => x ∈ (T i).toConvexSpaceBody
  have hcard : (Finset.multiplicityAt s (fun i ↦ (T i).toConvexSpaceBody) x : ENNReal) =
      (s'.card : ENNReal) := by
    simp [Finset.multiplicityAt, s']
  rw [hcard]
  by_cases hne : s'.Nonempty
  · let e := s'.equivFin
    let T' : Fin s'.card → Tube δ (EuclideanSpace ℝ (Fin 3)) := fun k => T (e.symm k).val
    have hx' : ∀ k, x ∈ (T' k).carrier := by
      intro k
      have hmem_s' : (e.symm k).val ∈ s' := (e.symm k).property
      rcases Finset.mem_filter.mp hmem_s' with ⟨_, hx_s'⟩
      -- hx_s' : x ∈ (T (e.symm k).val).toConvexSpaceBody
      -- Tube extends ConvexSpaceBody, so `(T i).carrier` is `(T i).toConvexSpaceBody.carrier`
      -- and `SetLike` uses `carrier` as the `coe`, so `x ∈ (T i).toConvexSpaceBody` is
      -- syntactically `x ∈ (T i).toConvexSpaceBody.carrier` which is `x ∈ (T i).carrier`
      have hx_carrier : x ∈ (T (e.symm k).val).carrier := hx_s'
      simpa [T'] using hx_carrier
    have hpair' : Pairwise (fun i j : Fin s'.card =>
        IsEssentiallyDistinct (T' i).carrier (T' j).carrier) := by
      intro i j hne_ij
      have hne_val : (e.symm i).val ≠ (e.symm j).val := by
        intro h
        apply hne_ij
        exact e.symm.injective (Subtype.ext h)
      have hi_mem_s : (e.symm i).val ∈ s := by
        have hi_s' : (e.symm i).val ∈ s' := (e.symm i).property
        exact Finset.mem_of_mem_filter (e.symm i).val hi_s'
      have hj_mem_s : (e.symm j).val ∈ s := by
        have hj_s' : (e.symm j).val ∈ s' := (e.symm j).property
        exact Finset.mem_of_mem_filter (e.symm j).val hj_s'
      exact hED hi_mem_s hj_mem_s hne_val
    have hbound := bushCount_exists.choose_spec.2 δ hδ_le s'.card T' hpair' x hx'
    simpa [bushCount.C] using hbound
  · have hcard0 : s'.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
    simp [hcard0]

/-- [Trivial multiplicity bound for essentially distinct `δ`-tubes]
The global multiplicity of an arbitrary shading of a finite family of pairwise essentially
distinct `δ`-tubes in `ℝ ^ 3` is at most `bushCount.C * δ ^ (-2)`.

Since each shade is contained in its tube, the pointwise multiplicity is bounded by the
bush bound at every point, and `ShadedBody.multiplicity_le_of_pointwiseMultiplicity_le`
passes from the pointwise to the global multiplicity. -/
theorem multiplicity_le_bushCount {δ : NNReal} (hδ_le : δ ≤ bushSeparation.δ)
    {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (hED : (s : Set ι).Pairwise
      fun i j ↦ IsEssentiallyDistinct (T i).carrier (T j).carrier) :
    ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody) ≤
      bushCount.C * (δ : ENNReal) ^ (-2 : ℝ) := by
  apply ShadedBody.multiplicity_le_of_pointwiseMultiplicity_le s (fun i ↦ (T i).toShadedBody)
  intro x hx
  haveI : DecidablePred (fun i : ι => x ∈ ((T i).toShadedBody).shade) := Classical.decPred _
  have h_card_le : (ShadedBody.pointwiseMultiplicity s (fun i ↦ (T i).toShadedBody) x : ℕ) ≤
      Finset.multiplicityAt s (fun i ↦ (T i).toTube.toConvexSpaceBody) x := by
    have h_subset : (Finset.filter (fun i ↦ x ∈ ((T i).toShadedBody).shade) s) ⊆
        (Finset.filter (fun i ↦ x ∈ (T i).toTube.toConvexSpaceBody) s) := by
      intro i hi
      rw [Finset.mem_filter] at hi
      rcases hi with ⟨hi_s, hi_x⟩
      refine Finset.mem_filter.mpr ⟨hi_s, (T i).shade_subset hi_x⟩
    have h_card_subset : (Finset.filter (fun i ↦ x ∈ ((T i).toShadedBody).shade) s).card ≤
        (Finset.filter (fun i ↦ x ∈ (T i).toTube.toConvexSpaceBody) s).card :=
      Finset.card_le_card h_subset
    simpa [ShadedBody.pointwiseMultiplicity, Finset.multiplicityAt]
  have h_cast : (ShadedBody.pointwiseMultiplicity s (fun i ↦ (T i).toShadedBody) x : ENNReal) ≤
      (Finset.multiplicityAt s (fun i ↦ (T i).toTube.toConvexSpaceBody) x : ENNReal) :=
    Nat.cast_le.mpr h_card_le
  calc
    (ShadedBody.pointwiseMultiplicity s (fun i ↦ (T i).toShadedBody) x : ENNReal) ≤
        (Finset.multiplicityAt s (fun i ↦ (T i).toTube.toConvexSpaceBody) x : ENNReal) := h_cast
    _ ≤ bushCount.C * (δ : ENNReal) ^ (-2 : ℝ) :=
      bushCount hδ_le s (fun i ↦ (T i).toTube) hED x

end Kakeya
