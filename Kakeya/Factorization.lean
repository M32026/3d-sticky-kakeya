/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Density
public import Kakeya.BiasedDensity
public import Kakeya.GreedyPartition
public import Kakeya.Thickness.Basic
public import Kakeya.Thickness.Lemmas
public import Kakeya.Thickness.Volume
public import Kakeya.KatzTao
public import Kakeya.Frostman
public import Kakeya.FactorFamily.Basic
public import Mathlib.Order.Partition.Finpartition
public import Kakeya.Pigeonhole
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Real
public import Kakeya.Mathlib.ENNReal
public import Kakeya.Mathlib.Finpartition

/-!
We formalise [GWZ, Section 4]
-/
public section

open MeasureTheory Metric Kakeya

namespace ConvexSpaceBody

/-- The `ENNReal` cancellation underlying the biased Katz--Tao estimate: from
`c⁻¹ ^ ϖ * r ^ ϖ * Δ * S ≤ 2 * Δ * k` one may cancel `Δ` and invert the factor `c⁻¹ ^ ϖ * r ^ ϖ`.
Stated with abstract `ENNReal` atoms so that it elaborates independently of the (large)
measure-theoretic terms it is applied to.
-/
private lemma le_rpow_mul_of_mul_le {ϖ : ℝ} (hϖ : 0 ≤ ϖ) {c r Δ S k : ENNReal}
    (hc : c ≠ 0) (hc' : c ≠ ⊤) (hr : r ^ ϖ ≠ 0) (hr' : r ^ ϖ ≠ ⊤) (hΔ : Δ ≠ 0) (hΔ' : Δ ≠ ⊤)
    (h : c⁻¹ ^ ϖ * r ^ ϖ * Δ * S ≤ 2 * Δ * k) : S ≤ 2 * c ^ ϖ * r ^ (-ϖ) * k := by
  have hcancel : c⁻¹ ^ ϖ * r ^ ϖ * S ≤ 2 * k :=
    (ENNReal.mul_le_mul_iff_left hΔ hΔ').mp <| by
      calc c⁻¹ ^ ϖ * r ^ ϖ * S * Δ = c⁻¹ ^ ϖ * r ^ ϖ * Δ * S := by ring
        _ ≤ 2 * Δ * k := h
        _ = 2 * k * Δ := by ring
  have hone : c ^ ϖ * r ^ (-ϖ) * (c⁻¹ ^ ϖ * r ^ ϖ) = 1 := by
    calc c ^ ϖ * r ^ (-ϖ) * (c⁻¹ ^ ϖ * r ^ ϖ) = c ^ ϖ * c⁻¹ ^ ϖ * (r ^ (-ϖ) * r ^ ϖ) := by ring
      _ = (1 : ENNReal) ^ ϖ * ((r ^ ϖ)⁻¹ * r ^ ϖ) := by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hϖ, ENNReal.mul_inv_cancel hc hc', ENNReal.rpow_neg]
      _ = 1 := by rw [ENNReal.one_rpow, one_mul, ENNReal.inv_mul_cancel hr hr']
  calc S = c ^ ϖ * r ^ (-ϖ) * (c⁻¹ ^ ϖ * r ^ ϖ * S) := by rw [← mul_assoc, hone, one_mul]
    _ ≤ c ^ ϖ * r ^ (-ϖ) * (2 * k) := mul_le_mul_right hcancel _
    _ = 2 * c ^ ϖ * r ^ (-ϖ) * k := by ring

/-- The endpoint ratio of the biased score range, rewritten as a single `rpow`:
`(N * x ^ (-ϖ)) / 2 ^ (-n ϖ) = N * (2 ^ n / x) ^ ϖ` for `x > 0`.
-/
private lemma mul_rpow_neg_div_rpow {N x ϖ : ℝ} {n : ℕ} (hx : 0 < x) :
    N * x ^ (-ϖ) / (2 : ℝ) ^ (-(n : ℝ) * ϖ) = N * ((2 : ℝ) ^ n / x) ^ ϖ := by
  rw [neg_mul, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast,
    Real.rpow_neg hx.le, Real.div_rpow (by positivity) hx.le]
  simp only [div_eq_mul_inv, inv_inv]
  ring

/-- The `ENNReal` cancellation underlying the biased maximal-density comparison.  Stated with
abstract `ENNReal` atoms so that it elaborates independently of the (large) measure-theoretic
terms it is applied to.
-/
private lemma half_div_rpow_mul_le {ϖ : ℝ} (hϖ : 0 ≤ ϖ) {b w d c : ENNReal}
    (hw : w ^ ϖ ≠ 0) (hw' : w ^ ϖ ≠ ⊤) (h : b ^ (-ϖ) * d ≤ 2 * (w ^ (-ϖ) * c)) :
    2⁻¹ * (w / b) ^ ϖ * d ≤ c := by
  calc 2⁻¹ * (w / b) ^ ϖ * d = 2⁻¹ * w ^ ϖ * (b ^ (-ϖ) * d) := by
        rw [ENNReal.div_rpow_of_nonneg _ _ hϖ, ENNReal.rpow_neg, div_eq_mul_inv]; ring
    _ ≤ 2⁻¹ * w ^ ϖ * (2 * (w ^ (-ϖ) * c)) := mul_le_mul_right h _
    _ = ((2 : ENNReal)⁻¹ * 2) * (w ^ ϖ * (w ^ ϖ)⁻¹) * c := by rw [ENNReal.rpow_neg]; ring
    _ = c := by
      rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), ENNReal.mul_inv_cancel hw hw',
        one_mul, one_mul]

noncomputable section --# Factorization
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [DecidableEq ι]
  (s : Finset ι)
  (V : ι → ConvexSpaceBody E)

/-- Definition 4.2 of [GWZ]. The family `(fun t ↦ t.convexHull_biUnion V)` on `parts` corresponds
  to 𝕎 in Definition 4.2 of [GWZ] -/
structure Factorization (C : NNReal) extends Finpartition s where
  /-- 𝕎 is KatzTao. -/
  isKatzTao : IsKatzTao parts (fun t ↦ t.convexHull_biUnion V) C
  /-- Density of 𝕍 in each W ∈ 𝕎 is close to its maxDensity. -/
  maxDensity_le_mul : ∀ t ∈ parts, maxDensity s V ≤ C * densityIn t V (t.convexHull_biUnion V)
  /-- Convex sets in 𝕎 are of similar dimensions. -/
  simDims :  ∀ t ∈ parts, ∀ t' ∈ parts,
    ethickness ℝ (t.convexHull_biUnion V).carrier ≤ C •
      ethickness ℝ (t'.convexHull_biUnion V).carrier

/-- The factor family underlying a factorization. Its outer indices are the parts of the
partition, and its outer bodies are their convex hulls. -/
noncomputable abbrev Factorization.toFactorFamily {κ : Type*} [DecidableEq κ] {s : Finset κ}
    {V : κ → ConvexSpaceBody E} {C : NNReal} (f : Factorization s V C) :
    FactorFamily E κ (Finset κ) :=
  FactorFamily.ofFinpartition V f.toFinpartition

/-- A partition part is its fiber in the factor family underlying a factorization. -/
theorem Factorization.toFactorFamily_fiber {κ : Type*} [DecidableEq κ] {s : Finset κ}
    {V : κ → ConvexSpaceBody E} {C : NNReal} (f : Factorization s V C) {t : Finset κ}
    (ht : t ∈ f.parts) : f.toFactorFamily.fiber t = t := by
  exact FactorFamily.ofFinpartition_fiber V f.toFinpartition ht

/-- The outer family of a factorization is Katz--Tao. -/
theorem Factorization.toFactorFamily_isKatzTao {κ : Type*} [DecidableEq κ] {s : Finset κ}
    {V : κ → ConvexSpaceBody E} {C : NNReal} (f : Factorization s V C) :
    IsKatzTao f.toFactorFamily.outerSet f.toFactorFamily.outerBody C :=
  f.isKatzTao

/-- The maximal-density estimate of a factorization, stated for its underlying factor family. -/
theorem Factorization.toFactorFamily_maxDensity_le_mul {κ : Type*} [DecidableEq κ]
    {s : Finset κ}
    {V : κ → ConvexSpaceBody E} {C : NNReal} (f : Factorization s V C) :
    ∀ t ∈ f.toFactorFamily.outerSet,
      maxDensity f.toFactorFamily.innerSet f.toFactorFamily.innerBody ≤
        C * densityIn (f.toFactorFamily.fiber t) f.toFactorFamily.innerBody
          (f.toFactorFamily.outerBody t) := by
  intro t ht
  rw [f.toFactorFamily_fiber ht]
  exact f.maxDensity_le_mul t ht

/-- The outer bodies of a factorization have comparable dimensions. -/
theorem Factorization.toFactorFamily_simDims {κ : Type*} [DecidableEq κ] {s : Finset κ}
    {V : κ → ConvexSpaceBody E} {C : NNReal} (f : Factorization s V C) :
    ∀ t ∈ f.toFactorFamily.outerSet, ∀ t' ∈ f.toFactorFamily.outerSet,
      ethickness ℝ (f.toFactorFamily.outerBody t).carrier ≤
        C • ethickness ℝ (f.toFactorFamily.outerBody t').carrier :=
  f.simDims

-- Mathlib.Order.Partition.Finpartition contains all we need for Finpartition

/-- the `maxDensity_le_mul` property implies being Frostman, Definition 4.2(ii) of [GWZ] -/
theorem Factorization.isFrostman {s : Finset ι} {V : ι → ConvexSpaceBody E} {C}
    (f : Factorization s V C) : ∀ t ∈ f.parts, IsFrostmanIn t V (t.convexHull_biUnion V) C := by
  intro t ht K hK
  trans maxDensity s V
  · trans
    · apply le_maxDensity
    · apply maxDensity_mono
      rw [f.sup_parts.symm]
      apply Finset.le_sup ht
  · exact f.maxDensity_le_mul t ht

/-- Each fiber of the factor family underlying a factorization is Frostman in its outer body. -/
theorem Factorization.toFactorFamily_isFrostman {κ : Type*} [DecidableEq κ] {s : Finset κ}
    {V : κ → ConvexSpaceBody E} {C : NNReal} (f : Factorization s V C) :
    ∀ t ∈ f.toFactorFamily.outerSet,
      IsFrostmanIn (f.toFactorFamily.fiber t) f.toFactorFamily.innerBody
        (f.toFactorFamily.outerBody t) C := by
  intro t ht
  rw [f.toFactorFamily_fiber ht]
  exact f.isFrostman t ht

/-- **Restricting a factorization to a sub-collection of its parts.**

A `ConvexSpaceBody.Factorization` of `s` restricts to one of the union `s'` of an arbitrary
sub-collection `P` of its parts, at the *same* constant `C` and with `parts` literally `P`.

All four fields are inherited, and it is worth recording why field by field, because this is
what makes the *part* the atom that a selection may keep or drop while the factorization
survives:

* the `Finpartition` is `Finpartition.ofSubset`, whose `parts` is `P` by construction;
* `isKatzTao` is `maxDensity P (fun t => t.convexHull_biUnion V) ≤ C`, which
  `ConvexSpaceBody.maxDensity_mono` gives from `P ⊆ f.parts`;
* `maxDensity_le_mul` compares `maxDensity s' V` with a density inside the part `t`.  The left
  side is monotone in the index set and `s' ⊆ s`; the right side is attached to `t` itself,
  whose hull `t.convexHull_biUnion V` is unchanged when *other* parts are dropped.  This is the
  field for which keeping whole parts is essential;
* `simDims` is a pairwise condition on parts, so it restricts.

Dropping a part is therefore free.  Dropping members *inside* a part is not: that shrinks the
part's hull, and both `maxDensity_le_mul` and the plank dimensions attached to the hull
(`Kakeya.IsPlankOfDimensions`) are two-sided. -/
noncomputable def Factorization.ofSubsetParts {s : Finset ι} {V : ι → ConvexSpaceBody E}
    {C : NNReal} (f : Factorization s V C) {P : Finset (Finset ι)} (hP : P ⊆ f.parts)
    {s' : Finset ι} (hs' : P.sup id = s') : Factorization s' V C where
  toFinpartition := f.toFinpartition.ofSubset hP hs'
  isKatzTao := by
    simp only [Finpartition.ofSubset_parts]
    exact f.isKatzTao.subset hP
  maxDensity_le_mul := by
    intro t ht
    have htP : t ∈ P := by
      simpa only [Finpartition.ofSubset_parts] using ht
    have hs'le : s' ⊆ s := by
      rw [← hs']
      rw [← f.sup_parts]
      exact Finset.sup_mono (f := id) hP
    exact (maxDensity_mono V hs'le).trans (f.maxDensity_le_mul t (hP htP))
  simDims := by
    intro t ht t' ht'
    exact f.simDims t (hP (by simpa only [Finpartition.ofSubset_parts] using ht))
      t' (hP (by simpa only [Finpartition.ofSubset_parts] using ht'))

/-- The parts of `ConvexSpaceBody.Factorization.ofSubsetParts` are the retained ones. -/
@[simp] theorem Factorization.ofSubsetParts_parts {s : Finset ι} {V : ι → ConvexSpaceBody E}
    {C : NNReal} (f : Factorization s V C) {P : Finset (Finset ι)} (hP : P ⊆ f.parts)
    {s' : Finset ι} (hs' : P.sup id = s') :
    (f.ofSubsetParts hP hs').parts = P := by
  rfl

/-- **The empty index set carries a factorization, at any constant.**

Its `parts` are empty, so every clause quantified over parts — `maxDensity_le_mul`, `simDims`
and any plank-dimension requirement on the hulls — holds vacuously, and `isKatzTao` holds
because the empty family has zero maximal density.

This is what makes *discarding a whole fibre* free for a selection that has to return a
factorization of every fibre: the discarded fibres are empty and are witnessed here. -/
theorem exists_factorization_of_eq_empty {V : ι → ConvexSpaceBody E} {s : Finset ι}
    (hs : s = ∅) (C : NNReal) :
    ∃ F : Factorization s V C, F.parts = ∅ := by
  subst hs
  let F : Factorization (∅ : Finset ι) V C := {
    toFinpartition := Finpartition.empty (Finset ι)
    isKatzTao := by
      change maxDensity (∅ : Finset (Finset ι))
        (fun t : Finset ι => t.convexHull_biUnion V) ≤ C
      rw [maxDensity_empty]
      exact zero_le
    maxDensity_le_mul := by
      simp
    simDims := by
      simp
  }
  exact ⟨F, by simp⟩

/-- The recursively defined partition obtained by repeatedly extracting a subfamily of maximal
density. -/
@[nolint defsWithUnderscore]
def greedy_partition : Finpartition s := by
  induction s using Finset.strongInductionOn
  case a s H =>
    let t := density_maximizer s V
    have hts : t ⊆ s := density_maximizer_subset s V
    by_cases ht : t.Nonempty
    · apply (H (s \ t) (Finset.sdiff_ssubset hts ht)).extend
      · exact ht.ne_empty
      · exact Finset.sdiff_disjoint
      · exact sdiff_sup_cancel hts
    · exact ⊤

private lemma parts_greedy_partition_of_nonempty (h : (density_maximizer s V).Nonempty) :
    (greedy_partition s V).parts =
      {density_maximizer s V} ∪ (greedy_partition (s \ density_maximizer s V) V).parts := by
  unfold greedy_partition
  rw [Finset.strongInductionOn_eq, dif_pos]
  · simp
  · assumption

private lemma maxDensity_eq_of_subset_greedy_partition {A} (hAne : A.Nonempty)
    (hA : A ⊆ (greedy_partition s V).parts) :
      ∃ r ∈ A, maxDensity (A.sup id) V = densityIn r V (r.convexHull_biUnion V) := by
  induction s using Finset.strongInductionOn
  case a s H =>
    have hle {r} (hr : r ∈ A) :
        densityIn r V (r.convexHull_biUnion V) ≤ maxDensity (A.sup id) V := by
      trans maxDensity r V
      · apply le_maxDensity
      · apply maxDensity_mono
        exact Finset.le_sup (f := id) hr
    have hAs : A.sup id ≤ s := by
      rw [← (greedy_partition s V).sup_parts]
      apply Finset.sup_mono (f := id) hA
    by_cases ht : (density_maximizer s V).Nonempty
    · have hA' := parts_greedy_partition_of_nonempty s V ht ▸ hA
      set t := density_maximizer s V
      have hts : t ⊆ s := density_maximizer_subset s V
      by_cases h : t ∈ A
      · use t
        constructor
        · assumption
        · apply le_antisymm
          · convert maxDensity_mono V (?_ : _ ≤ s)
            · apply densityIn_maximizer_eq
            · exact hAs
          · exact hle h
      · suffices A ⊆ (greedy_partition (s \ t) V).parts from
          H (s \ t) (Finset.sdiff_ssubset hts ht) this
        intro t' ht'
        rcases Finset.mem_union.mp (hA' ht') with h1|h2
        · simp only [Finset.mem_singleton] at h1
          rw [h1] at ht'
          contradiction
        · assumption
    · rw [Finset.not_nonempty_iff_eq_empty] at ht
      obtain ⟨r, hr⟩ := hAne
      use r
      constructor
      · exact hr
      · apply le_antisymm
        · trans maxDensity s V
          · apply maxDensity_mono
            exact hAs
          · rw [maxDensity_eq_zero_of_maximizer_eq_empty ht]
            simp
        · exact hle hr

private lemma maxDensity_eq_of_mem_part_greedy_partition r (hr : r ∈ (greedy_partition s V).parts) :
  maxDensity r V = densityIn r V (r.convexHull_biUnion V) := by
  let A : Finset (Finset ι) := {r}
  have hAne : A.Nonempty := Finset.singleton_nonempty r
  have hA : A ⊆ (greedy_partition s V).parts := Finset.singleton_subset_iff.mpr hr
  obtain ⟨r', hr', h⟩ := maxDensity_eq_of_subset_greedy_partition s V hAne hA
  have : r = r' := (Finset.mem_singleton.mp hr').symm
  convert h
  simp [A]

/-- The constant in `nonempty_factorization`. -/
@[nolint defsWithUnderscore]
abbrev nonempty_factorization.C (dim : ℕ) (card : ℕ) (δ : NNReal) : ENNReal :=
  ENNReal.ofReal (1 + Real.logb 2 (card / 1)) * ENNReal.ofReal (1 + Real.logb 2 (1 / δ)) ^ dim

section nonempty_factorization
variable
  {δ : NNReal}
  {s : Finset ι}
  {V : ι → ConvexSpaceBody E}

private theorem nonempty_factorization.constructA [Nontrivial E] (hδ : 0 < δ) (hs : s.Nonempty)
    (h2 : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier) : ∃ s' ⊆ (greedy_partition s V).parts,
    ∑ t ∈ (greedy_partition s V).parts, ∑ i ∈ t, volume (V i).carrier ≤
        ENNReal.ofReal (1 + Real.logb 2 (↑s.card / 1)) * ∑ t ∈ s', ∑ i ∈ t, volume (V i).carrier ∧
      ∀ i ∈ s', ∀ j ∈ s', maxDensity i V ≤ 2 * maxDensity j V :=
   let P := greedy_partition s V
   let w := fun t ↦ ∑ i ∈ t, volume (V i).carrier
   let hPw : ∀ t ∈ P.parts, 0 < w t := by
    intro t ht
    apply ENNReal.sum_pos_of_nonempty
    · exact P.nonempty_of_mem_parts ht
    · intro i hi
      apply (V i).convex.volume_pos_of_scale_ne_zero
      exact (lt_of_lt_of_le (ENNReal.coe_pos.mpr hδ) (h2 i (P.subset ht hi))).ne.symm
   ENNReal.dyadic_pigeonhole₁ P.parts w (fun t ↦ maxDensity t V)
      zero_lt_one (by simpa : 1 ≤ (s.card : ℝ)) (fun t ht ↦
      ⟨ by
        norm_cast
        apply one_le_maxDensity
        simpa [← Finset.sum_pos_iff_of_nonneg] using hPw t ht,
        by
        trans (t.card : ENNReal)
        · apply maxDensity_le_card
        · norm_cast
          grw [P.subset ht]⟩)

-- A second pigeonholing to have `maxDensity_le_mul`
set_option linter.defProp false in
private def nonempty_factorization.constructB [Nontrivial E] (hδ : 0 < δ) (hs : s.Nonempty)
    (h1 : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (h2 : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier) :=
  let hδ₁ := ethickness.le_of_le_scale_of_subset h1 h2 hs
  let P := greedy_partition s V
  let w := fun t ↦ ∑ i ∈ t, volume (V i).carrier
  let conA := constructA hδ hs h2
  ENNReal.dyadic_pigeonhole conA.choose w
      (fun t (k : Fin (Module.finrank ℝ E)) ↦ ethickness ℝ (t.convexHull_biUnion V).carrier k)
        hδ hδ₁ (by
    intro t ht
    simp only [Set.mem_Icc]
    have htne := P.nonempty_of_mem_parts (conA.choose_spec.1 ht)
    have htsub : t ⊆ s := P.subset (conA.choose_spec.1 ht)
    constructor
    · rintro ⟨k, hk⟩
      simpa using le_ethickness_convexHullBiUnion h2 htne htsub hk
    · rintro ⟨k, hk⟩
      simpa using ethickness_convexHullBiUnion_le h1 htne htsub k)

/-- The subfamily for which we construct a factorization -/
@[nolint defsWithUnderscore]
def nonempty_factorization.subfamily [Nontrivial E] (hδ : 0 < δ) (hs : s.Nonempty)
    (h1 : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (h2 : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier) : Finset ι :=
  (constructB hδ hs h1 h2).choose.sup id

/-- The subfamily is heavy. -/
theorem nonempty_factorization.subfamily_subset [Nontrivial E] (hδ : 0 < δ) (hs : s.Nonempty)
    (h1 : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (h2 : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier) : subfamily hδ hs h1 h2 ⊆ s := by
  let P := greedy_partition s V
  nth_rw 2 [P.sup_parts.symm]
  exact Finset.sup_mono (f := id)
    ((constructB hδ hs h1 h2).choose_spec.1.trans (constructA hδ hs h2).choose_spec.1)

private lemma nonempty_factorization.subfamily_sum [Nontrivial E] (hδ : 0 < δ) (hs : s.Nonempty)
    (h1 : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (h2 : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier)
    (f : ι → ENNReal) :
    ∑ i ∈ subfamily hδ hs h1 h2, f i = (constructB hδ hs h1 h2).choose.sum (fun t ↦ t.sum f) := by
  let P := greedy_partition s V
  let consA := constructA hδ hs h2
  let consB := constructB hδ hs h1 h2
  rw [subfamily, Finset.sup_eq_biUnion]
  apply Finset.sum_biUnion
  apply P.disjoint.subset
  exact consB.choose_spec.1.trans consA.choose_spec.1

/-- The subfamily is heavy. -/
theorem nonempty_factorization.weight_subfamily [Nontrivial E] (hδ : 0 < δ) (hs : s.Nonempty)
    (h1 : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (h2 : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier) :
    ∑ i ∈ s, volume (V i).carrier ≤
      (nonempty_factorization.C (Module.finrank ℝ E) s.card δ) *
        ∑ i ∈ (subfamily hδ hs h1 h2), volume (V i).carrier := by
  let P := greedy_partition s V
  let w := fun t ↦ ∑ i ∈ t, volume (V i).carrier
  let consA := constructA hδ hs h2
  let consB := constructB hδ hs h1 h2
  calc
    _ = P.parts.sum w := P.sum_eq_sum_parts_sum _
    _ ≤ _ := consA.choose_spec.2.1
    _ ≤ ENNReal.ofReal (1 + Real.logb 2 (↑s.card / 1)) *
          (ENNReal.ofReal (1 + Real.logb 2 (1 / δ)) ^ (Module.finrank ℝ E)
            * consB.choose.sum w) := by
      gcongr 1
      exact consB.choose_spec.2.1
    _ = _ := by
      rw [← mul_assoc]
      congr 1
      symm
      apply subfamily_sum

private lemma nonempty_factorization.maxDensity_le_mul [Nontrivial E] (hδ : 0 < δ) (hs : s.Nonempty)
    (h1 : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (h2 : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier) :
    let B := (constructB hδ hs h1 h2).choose
    ∀ t ∈ B, maxDensity (B.sup id) V ≤ 2 * densityIn t V (t.convexHull_biUnion V) := by
  have propA := (constructA hδ hs h2).choose_spec
  have hA := propA.1
  have hB := (constructB hδ hs h1 h2).choose_spec.1
  intro B t ht
  obtain ⟨r, hr, hr'⟩ :=
    maxDensity_eq_of_subset_greedy_partition s V ⟨t, ht⟩ (hB.trans hA)
  apply hB at ht
  apply hB at hr
  have := propA.2.2 r hr t ht
  replace ht := maxDensity_eq_of_mem_part_greedy_partition s V t (hA ht)
  replace hr := maxDensity_eq_of_mem_part_greedy_partition s V r (hA hr)
  rw [hr', ← hr, ← ht]
  convert this

-- TODO: golf this proof
private lemma nonempty_factorization.isKatzTao [Nontrivial E] (hδ : 0 < δ) (hs : s.Nonempty)
    (h1 : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (h2 : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier) :
    IsKatzTao (constructB hδ hs h1 h2).choose (fun t ↦ (t.convexHull_biUnion V)) 2 := by
  rw [isKatzTao_iff]
  intro K
  set consB := constructB hδ hs h1 h2
  set B := consB.choose
  by_cases hBe : B = ∅
  · simp [hBe]
  have hA := (constructA hδ hs h2).choose_spec.1
  have hB := (constructB hδ hs h1 h2).choose_spec.1
  set P := greedy_partition s V
  let w := fun t ↦ ∑ i ∈ t, volume (V i).carrier
  let Q : Finpartition (B.sup id) := P.ofSubset (hB.trans hA) rfl
  have hBne : B.Nonempty := Finset.nonempty_of_ne_empty hBe
  have hvol (i : ι) (hi : i ∈ s) : 0 < volume (V i).carrier := by
    apply (V i).convex.volume_pos_of_scale_ne_zero
    exact (lt_of_lt_of_le (ENNReal.coe_pos.mpr hδ) (h2 i hi)).ne.symm
  have hmax_pos : 0 < maxDensity (B.sup id) V := by
    apply lt_of_lt_of_le zero_lt_one
    apply one_le_maxDensity
    obtain ⟨t, ht⟩ := hBne
    obtain ⟨i, hi⟩ := P.nonempty_of_mem_parts (hA (hB ht))
    exact ⟨i, Finset.mem_sup.mpr ⟨_, ht, hi⟩, hvol i (P.subset (hA (hB ht)) hi)⟩
  rw [← ENNReal.mul_le_mul_iff_left hmax_pos.ne.symm (maxDensity_ne_top _ _), Finset.sum_mul]
  trans 2 * ∑ t ∈ B with (fun t ↦ t.convexHull_biUnion V) t ≤ K, w t
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    simp only [Finset.mem_filter] at ht
    calc
      _ ≤ volume (t.convexHull_biUnion V).carrier *
        (2 * densityIn t V (t.convexHull_biUnion V)) := by
          apply mul_le_mul_right
          apply maxDensity_le_mul hδ hs h1 h2
          exact ht.1
      _ = _ := by
        simp [w, sum_volume_eq_densityIn_mul_volume' (t.le_convexHull_biUnion V)]
        ring
  · norm_cast
    rw [mul_assoc]
    apply mul_le_mul_right
    trans ∑ i ∈ B.sup id with V i ≤ K, volume (V i).carrier
    · rw [← Finset.sum_biUnion]
      · apply Finset.sum_le_sum_of_subset
        · simp only [Finset.biUnion_subset_iff_forall_subset, Finset.mem_filter, and_imp]
          intro t ht htK i hi
          simp only [Finset.mem_filter, Finset.mem_sup]
          constructor
          · exact ⟨t, ht, hi⟩
          · rw [(Q.nonempty_of_mem_parts ht).convexHull_biUnion_le_iff] at htK
            exact htK i hi
      · apply Set.PairwiseDisjoint.subset
        · exact Q.disjoint
        · norm_cast
          apply Finset.filter_subset
    · rw [mul_comm]
      apply sum_volume_le_maxDensity_mul_volume (B.sup id)

private lemma nonempty_factorization.simdims [Nontrivial E] (hδ : 0 < δ) (hs : s.Nonempty)
    (h1 : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (h2 : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier) :
    let B := (constructB hδ hs h1 h2).choose
    ∀ t ∈ B, ∀ t' ∈ B, ethickness ℝ (t.convexHull_biUnion V).carrier ≤
      (2 : NNReal) • ethickness ℝ (t'.convexHull_biUnion V).carrier := by
  intro B i hi j hj k
  by_cases hk : k < Module.finrank ℝ E
  · exact (constructB hδ hs h1 h2).choose_spec.2.2 i hi j hj ⟨k, hk⟩
  · push Not at hk
    simp [ethickness_eq_zero_of_finrank_le hk]

/-- The factorization of the subfamily selected by `nonempty_factorization.subfamily`. -/
@[nolint defsWithUnderscore]
def nonempty_factorization.factorization [Nontrivial E] (hδ : 0 < δ) (hs : s.Nonempty)
    (h1 : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (h2 : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier) :
    Factorization (subfamily hδ hs h1 h2) V 2 where
  __ :=
    let P := greedy_partition s V
    let consA := constructA hδ hs h2
    let consB := constructB hδ hs h1 h2
    P.ofSubset (consB.choose_spec.1.trans consA.choose_spec.1) rfl
  isKatzTao := isKatzTao hδ hs h1 h2
  maxDensity_le_mul := maxDensity_le_mul hδ hs h1 h2
  simDims := simdims hδ hs h1 h2

/-- The first dyadic pigeonholing of `nonempty_factorization.constructA`, run against an
arbitrary block weight `fun t ↦ ∑ i ∈ t, w i` instead of the block volumes.  The score whose range
is pigeonholed is the density `maxDensity t V`, exactly as in the volume-weighted proof, so the
range hypothesis is discharged by the same volume-positivity argument. -/
private theorem nonempty_factorization.constructA_weighted [Nontrivial E] (hδ : 0 < δ)
    (hs : s.Nonempty) (h2 : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier) (w : ι → ENNReal) :
    ∃ A ⊆ (greedy_partition s V).parts,
      ∑ t ∈ (greedy_partition s V).parts, ∑ i ∈ t, w i ≤
          ENNReal.ofReal (1 + Real.logb 2 (↑s.card / 1)) * ∑ t ∈ A, ∑ i ∈ t, w i ∧
        ∀ t ∈ A, ∀ t' ∈ A, maxDensity t V ≤ 2 * maxDensity t' V :=
  let P := greedy_partition s V
  let wv := fun t ↦ ∑ i ∈ t, volume (V i).carrier
  let hPw : ∀ t ∈ P.parts, 0 < wv t := by
    intro t ht
    apply ENNReal.sum_pos_of_nonempty
    · exact P.nonempty_of_mem_parts ht
    · intro i hi
      apply (V i).convex.volume_pos_of_scale_ne_zero
      exact (lt_of_lt_of_le (ENNReal.coe_pos.mpr hδ) (h2 i (P.subset ht hi))).ne.symm
  ENNReal.dyadic_pigeonhole₁ P.parts (fun t ↦ ∑ i ∈ t, w i) (fun t ↦ maxDensity t V)
      zero_lt_one (by simpa : 1 ≤ (s.card : ℝ)) (fun t ht ↦
      ⟨ by
        norm_cast
        apply one_le_maxDensity
        simpa [← Finset.sum_pos_iff_of_nonneg] using hPw t ht,
        by
        trans (t.card : ENNReal)
        · apply maxDensity_le_card
        · norm_cast
          grw [P.subset ht]⟩)

/-- The second, `dim`-fold dyadic pigeonholing of `nonempty_factorization.constructB`, run against
an arbitrary block weight `fun t ↦ ∑ i ∈ t, w i` and stated for an arbitrary subfamily `A` of the
blocks of the greedy partition.  The comparability conclusion is stated for the whole `ethickness`
function rather than for the coordinates below `Module.finrank ℝ E`, the extension to the vanishing
coordinates being `Metric.ethickness_eq_zero_of_finrank_le`. -/
private theorem nonempty_factorization.constructB_weighted [Nontrivial E] (hδ : 0 < δ)
    (hs : s.Nonempty) (h1 : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (h2 : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier) (w : ι → ENNReal)
    {A : Finset (Finset ι)} (hA : A ⊆ (greedy_partition s V).parts) :
    ∃ B ⊆ A,
      ∑ t ∈ A, ∑ i ∈ t, w i ≤
          ENNReal.ofReal (1 + Real.logb 2 (1 / (δ : ℝ))) ^ Module.finrank ℝ E *
            ∑ t ∈ B, ∑ i ∈ t, w i ∧
        ∀ t ∈ B, ∀ t' ∈ B, ethickness ℝ (t.convexHull_biUnion V).carrier ≤
          (2 : NNReal) • ethickness ℝ (t'.convexHull_biUnion V).carrier := by
  let hδ₁ := ethickness.le_of_le_scale_of_subset h1 h2 hs
  let w' : Finset ι → ENNReal := fun t ↦ ∑ i ∈ t, w i
  let consB :=
    ENNReal.dyadic_pigeonhole A w'
      (fun t (k : Fin (Module.finrank ℝ E)) ↦ ethickness ℝ (t.convexHull_biUnion V).carrier k)
        hδ hδ₁ (by
    intro t ht
    simp only [Set.mem_Icc]
    have htne : t.Nonempty := (greedy_partition s V).nonempty_of_mem_parts (hA ht)
    have htsub : t ⊆ s := (greedy_partition s V).subset (hA ht)
    constructor
    · rintro ⟨k, hk⟩
      simpa using le_ethickness_convexHullBiUnion h2 htne htsub hk
    · rintro ⟨k, hk⟩
      simpa using ethickness_convexHullBiUnion_le h1 htne htsub k)
  refine ⟨consB.choose, consB.choose_spec.1, ?_, ?_⟩
  · exact consB.choose_spec.2.1
  · intro t ht t' ht' k
    by_cases hk : k < Module.finrank ℝ E
    · exact (consB.choose_spec.2.2 t ht t' ht' ⟨k, hk⟩)
    · push Not at hk
      simp [ethickness_eq_zero_of_finrank_le hk]

/-- The density comparison of `nonempty_factorization.maxDensity_le_mul`, stated for an arbitrary
subfamily `A` of the blocks of the greedy partition with pairwise comparable densities instead of
for the class retained by the first pigeonholing. -/
private lemma nonempty_factorization.maxDensity_le_mul_of_parts [Nontrivial E]
    {A : Finset (Finset ι)} (hA : A ⊆ (greedy_partition s V).parts)
    (hcomp : ∀ t ∈ A, ∀ t' ∈ A, maxDensity t V ≤ 2 * maxDensity t' V) :
    ∀ t ∈ A, maxDensity (A.sup id) V ≤ 2 * densityIn t V (t.convexHull_biUnion V) := by
  intro t ht
  obtain ⟨r, hr, hr'⟩ :=
    maxDensity_eq_of_subset_greedy_partition s V ⟨t, ht⟩ hA
  have hmax := hcomp r hr t ht
  replace ht := maxDensity_eq_of_mem_part_greedy_partition s V t (hA ht)
  replace hr := maxDensity_eq_of_mem_part_greedy_partition s V r (hA hr)
  rw [hr', ← hr, ← ht]
  exact hmax

/-- The Katz--Tao property of `nonempty_factorization.isKatzTao`, stated for an arbitrary subfamily
`A` of the blocks of the greedy partition with pairwise comparable densities instead of for the
class retained by the first pigeonholing. -/
private lemma nonempty_factorization.isKatzTao_of_parts [Nontrivial E] (hδ : 0 < δ)
    (h2 : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier) {A : Finset (Finset ι)}
    (hA : A ⊆ (greedy_partition s V).parts)
    (hcomp : ∀ t ∈ A, ∀ t' ∈ A, maxDensity t V ≤ 2 * maxDensity t' V) :
    IsKatzTao A (fun t ↦ (t.convexHull_biUnion V)) 2 := by
  rw [isKatzTao_iff]
  intro K
  by_cases hAe : A = ∅
  · simp [hAe]
  set P := greedy_partition s V
  let w := fun t ↦ ∑ i ∈ t, volume (V i).carrier
  let Q : Finpartition (A.sup id) := P.ofSubset hA rfl
  have hAne : A.Nonempty := Finset.nonempty_of_ne_empty hAe
  have hvol (i : ι) (hi : i ∈ s) : 0 < volume (V i).carrier := by
    apply (V i).convex.volume_pos_of_scale_ne_zero
    exact (lt_of_lt_of_le (ENNReal.coe_pos.mpr hδ) (h2 i hi)).ne.symm
  have hmax_pos : 0 < maxDensity (A.sup id) V := by
    apply lt_of_lt_of_le zero_lt_one
    apply one_le_maxDensity
    obtain ⟨t, ht⟩ := hAne
    obtain ⟨i, hi⟩ := P.nonempty_of_mem_parts (hA ht)
    exact ⟨i, Finset.mem_sup.mpr ⟨_, ht, hi⟩, hvol i (P.subset (hA ht) hi)⟩
  rw [← ENNReal.mul_le_mul_iff_left hmax_pos.ne.symm (maxDensity_ne_top _ _), Finset.sum_mul]
  trans 2 * ∑ t ∈ A with (fun t ↦ t.convexHull_biUnion V) t ≤ K, w t
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    simp only [Finset.mem_filter] at ht
    calc
      _ ≤ volume (t.convexHull_biUnion V).carrier *
         (2 * densityIn t V (t.convexHull_biUnion V)) := by
          apply mul_le_mul_right
          apply maxDensity_le_mul_of_parts hA hcomp
          exact ht.1
      _ = _ := by
        simp [w, sum_volume_eq_densityIn_mul_volume' (t.le_convexHull_biUnion V)]
        ring
  · norm_cast
    rw [mul_assoc]
    apply mul_le_mul_right
    trans ∑ i ∈ A.sup id with V i ≤ K, volume (V i).carrier
    · rw [← Finset.sum_biUnion]
      · apply Finset.sum_le_sum_of_subset
        · simp only [Finset.biUnion_subset_iff_forall_subset, Finset.mem_filter, and_imp]
          intro t ht htK i hi
          simp only [Finset.mem_filter, Finset.mem_sup]
          constructor
          · exact ⟨t, ht, hi⟩
          · rw [(Q.nonempty_of_mem_parts ht).convexHull_biUnion_le_iff] at htK
            exact htK i hi
      · apply Set.PairwiseDisjoint.subset
        · exact Q.disjoint
        · norm_cast
          apply Finset.filter_subset
    · rw [mul_comm]
      apply sum_volume_le_maxDensity_mul_volume (A.sup id)

/-- Any subfamily `A` of the blocks of the greedy partition whose densities are pairwise comparable
and whose outer bodies have pairwise comparable ethicknesses carries a factorization of its union,
with `A` as its set of parts.  This is the weight-free content of
`nonempty_factorization.isKatzTao`, `nonempty_factorization.maxDensity_le_mul` and
`nonempty_factorization.simdims`, separated from the particular subfamily those three are stated
for so that it applies both to the class retained by the two weighted pigeonholes and to a single
block. -/
private theorem nonempty_factorization.exists_factorization_of_parts [Nontrivial E] (hδ : 0 < δ)
    (h2 : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier) {A : Finset (Finset ι)}
    (hA : A ⊆ (greedy_partition s V).parts)
    (hcomp : ∀ t ∈ A, ∀ t' ∈ A, maxDensity t V ≤ 2 * maxDensity t' V)
    (hsim : ∀ t ∈ A, ∀ t' ∈ A, ethickness ℝ (t.convexHull_biUnion V).carrier ≤
      (2 : NNReal) • ethickness ℝ (t'.convexHull_biUnion V).carrier) :
    ∃ F : Factorization (A.sup id) V 2, F.parts = A := by
  exact ⟨{
    toFinpartition := (greedy_partition s V).ofSubset hA rfl
    isKatzTao := isKatzTao_of_parts hδ h2 hA hcomp
    maxDensity_le_mul := maxDensity_le_mul_of_parts hA hcomp
    simDims := hsim }, rfl⟩

/-- Chaining the two weighted pigeonholing losses into the single loss
`nonempty_factorization.C`, and passing from a sum over the retained blocks to a sum over their
union.  This is the weighted counterpart of the computation inside
`nonempty_factorization.weight_subfamily`, with the two pigeonholing conclusions taken as
hypotheses so that it is independent of how the two classes were selected. -/
private lemma nonempty_factorization.sum_le_C_mul_of_parts (w : ι → ENNReal)
    {A B : Finset (Finset ι)} (hA : A ⊆ (greedy_partition s V).parts) (hB : B ⊆ A)
    (hAsum : ∑ t ∈ (greedy_partition s V).parts, ∑ i ∈ t, w i ≤
      ENNReal.ofReal (1 + Real.logb 2 (↑s.card / 1)) * ∑ t ∈ A, ∑ i ∈ t, w i)
    (hBsum : ∑ t ∈ A, ∑ i ∈ t, w i ≤
      ENNReal.ofReal (1 + Real.logb 2 (1 / (δ : ℝ))) ^ Module.finrank ℝ E *
        ∑ t ∈ B, ∑ i ∈ t, w i) :
    ∑ i ∈ s, w i ≤
      nonempty_factorization.C (Module.finrank ℝ E) s.card δ * ∑ i ∈ B.sup id, w i := by
  calc
    ∑ i ∈ s, w i = (greedy_partition s V).parts.sum (fun t ↦ ∑ i ∈ t, w i) :=
      (greedy_partition s V).sum_eq_sum_parts_sum w
    _ ≤ _ := hAsum
    _ ≤ ENNReal.ofReal (1 + Real.logb 2 (↑s.card / 1)) *
          (ENNReal.ofReal (1 + Real.logb 2 (1 / (δ : ℝ))) ^ Module.finrank ℝ E *
            ∑ t ∈ B, ∑ i ∈ t, w i) := by
      gcongr 1
    _ = _ := by
      conv_lhs =>
        rw [Finset.sum_sum_eq_sum_sup_id
          ((greedy_partition s V).disjoint.subset (hB.trans hA)) w]
      rw [← mul_assoc]

/-- A single block of the greedy partition of a nonempty family carries a factorization whose only
part is that block.  This supplies the conclusion of
`nonempty_factorization.factorization_weighted` in the degenerate case where the two weighted
pigeonholes retain no block at all, which happens when the weight vanishes identically. -/
private lemma nonempty_factorization.exists_singleton_factorization [Nontrivial E] (hδ : 0 < δ)
    (hs : s.Nonempty) (h2 : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier) :
    ∃ s' ⊆ s, s'.Nonempty ∧ ∃ F : Factorization s' V 2, F.parts.Nonempty := by
  let P := greedy_partition s V
  rcases hs with ⟨i, hi⟩
  obtain ⟨r, hr, hir⟩ := P.exists_mem hi
  let A' : Finset (Finset ι) := {r}
  have hA' : A' ⊆ P.parts := by
    simp [A', hr]
  have hcomp' : ∀ t ∈ A', ∀ t' ∈ A', maxDensity t V ≤ 2 * maxDensity t' V := by
    intro t ht t' ht'
    simp only [A', Finset.mem_singleton] at ht ht'
    subst t
    subst t'
    simpa [one_mul] using
      (mul_le_mul_of_nonneg_right (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal)) (by positivity))
  have hsim' : ∀ t ∈ A', ∀ t' ∈ A', ethickness ℝ (t.convexHull_biUnion V).carrier ≤
      (2 : NNReal) • ethickness ℝ (t'.convexHull_biUnion V).carrier := by
    intro t ht t' ht' k
    simp only [A', Finset.mem_singleton] at ht ht'
    subst t
    subst t'
    rw [Pi.smul_apply, ENNReal.smul_def, smul_eq_mul]
    simpa [one_mul] using
      (mul_le_mul_of_nonneg_right (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal)) (by positivity))
  obtain ⟨F, hFparts⟩ := exists_factorization_of_parts hδ h2 hA' hcomp' hsim'
  have hFne : F.parts.Nonempty := by
    rw [hFparts]
    simp [A']
  have hs' : A'.sup id ⊆ s := by
    rw [← P.sup_parts]
    exact Finset.sup_mono (f := id) hA'
  have hs'ne : (A'.sup id).Nonempty := by
    refine ⟨i, Finset.mem_sup.mpr ⟨r, ?_, hir⟩⟩
    simp [A']
  exact ⟨A'.sup id, hs', hs'ne, F, hFne⟩

/-- **(GWZ Lemma 4.1, weighted form) Maximal density factoring against an arbitrary weight**
(blueprint `lem:factmaxWeighted`).

The maximal-density factorization, with the heavy-subfamily bound taken in an arbitrary weight
`w : ι → ℝ≥0∞` fixed before the construction, instead of in the body volumes.
`ConvexSpaceBody.nonempty_factorization.weight_subfamily` is the case
`w = fun i => volume (V i).carrier`.

*Why the volume-weighted form does not suffice.*  Every application in this development needs the
retained subfamily to be heavy for some weight other than the volume — typically a shading mass
`|Y i|`, which for a family of tubes of a common thickness is not comparable to `|V i|` at all.
For such a family the body volumes are all equal, so the volume-weighted bound degenerates to a
statement about cardinality and says nothing about where the shading sits.  The first consumer is
`Kakeya.ml1Boot.exists_perParentFactorization`.

*Why it is a separate statement and what it costs.*  The greedy partition is built from the
density score alone and never looks at a weight, and both dyadic pigeonholes
(`ENNReal.dyadic_pigeonhole₁`, `ENNReal.dyadic_pigeonhole`) already accept a free weight with no
positivity, finiteness or non-vanishing hypothesis on it — their range hypothesis constrains only
the *other* function.  So the construction is the existing one with the block weights
`∑ i ∈ t, w i` in place of `∑ i ∈ t, volume (V i).carrier`, and the three conclusions of the
factorization, which never mention the weight, are untouched.

One point is not mechanical.  For a general `w` the retained class may be **empty**, since `w` may
vanish identically; the volume-weighted proof got nonemptiness from strict positivity of the volume
weight, which is unavailable here, and no positivity hypothesis on `w` may be added because the
consumers do not have one.  The repair is the blueprint's: the greedy partition of `s` is nonempty
because `s` is, and if the pigeonholes retain nothing then the displayed bound forces
`∑ i ∈ s, w i = 0`, so any single block of the partition serves equally well.

The intended Lean end state, recorded in the blueprint note following `lem:factmaxWeighted`, is a
single weight-parametrised greedy construction with the volume-weighted results recovered as the
instance at `w = fun i => volume (V i).carrier`, rather than two copies of it. -/
theorem nonempty_factorization.factorization_weighted [Nontrivial E] (hδ : 0 < δ)
    (hs : s.Nonempty) (h1 : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (h2 : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier) (w : ι → ENNReal) :
    ∃ s' ⊆ s, s'.Nonempty ∧
      ∑ i ∈ s, w i ≤ nonempty_factorization.C (Module.finrank ℝ E) s.card δ * ∑ i ∈ s', w i ∧
      ∃ F : Factorization s' V 2, F.parts.Nonempty := by
  obtain ⟨A, hA, hAsum, hAcomp⟩ := nonempty_factorization.constructA_weighted hδ hs h2 w
  obtain ⟨B, hB, hBsum, hBsim⟩ := nonempty_factorization.constructB_weighted hδ hs h1 h2 w hA
  have hsum : ∑ i ∈ s, w i ≤
      nonempty_factorization.C (Module.finrank ℝ E) s.card δ * ∑ i ∈ B.sup id, w i :=
    nonempty_factorization.sum_le_C_mul_of_parts w hA hB hAsum hBsum
  rcases B.eq_empty_or_nonempty with hBe | hBn
  · rw [hBe] at hsum
    have hzero : ∑ i ∈ s, w i = 0 := by
      apply le_antisymm
      · simpa [Finset.sup_empty, Finset.sum_empty, mul_zero] using hsum
      · exact zero_le
    obtain ⟨s', hs'sub, hs'ne, F, hFne⟩ :=
      nonempty_factorization.exists_singleton_factorization hδ hs h2
    refine ⟨s', hs'sub, hs'ne, ?weight, F, hFne⟩
    rw [hzero]
    exact zero_le
  · rcases hBn with ⟨t, ht⟩
    obtain ⟨i, hi⟩ := (greedy_partition s V).nonempty_of_mem_parts (hA (hB ht))
    obtain ⟨F, hFparts⟩ := nonempty_factorization.exists_factorization_of_parts hδ h2
      (hB.trans hA) (fun t ht t' ht' => hAcomp t (hB ht) t' (hB ht')) hBsim
    refine ⟨B.sup id, ?_, ?_, ?_, F, ?_⟩
    · rw [← (greedy_partition s V).sup_parts]
      exact Finset.sup_mono (f := id) (hB.trans hA)
    · exact ⟨i, Finset.mem_sup.mpr ⟨t, ht, hi⟩⟩
    · exact hsum
    · rw [hFparts]
      exact ⟨t, ht⟩

end nonempty_factorization

section Shared

variable {J : Type*}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Blueprint `lem:ethicknessPigeonhole`: the `n`-fold dyadic pigeonholing of the ethicknesses of
a finite family of convex bodies whose ethicknesses all lie in `[δ, 1]`.  This is the
score-independent step consumed by
`ConvexSpaceBody.nonempty_biasedFactorization.ethickness_pigeonhole`;
`ConvexSpaceBody.nonempty_factorization.constructB` performs the same step inline by calling
`ENNReal.dyadic_pigeonhole` directly, and is a candidate for a later refactor. -/
theorem exists_subset_ethickness_pigeonhole [Nontrivial E] (j : Finset J)
    (W : J → ConvexSpaceBody E) (m : J → ENNReal) {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hrange : ∀ t ∈ j, ∀ k : Fin (Module.finrank ℝ E),
      ethickness ℝ (W t).carrier k ∈ Set.Icc (δ : ENNReal) 1) :
    ∃ j' ⊆ j,
      ∑ t ∈ j, m t ≤
          ENNReal.ofReal (1 + Real.logb 2 (1 / δ)) ^ Module.finrank ℝ E * ∑ t ∈ j', m t ∧
        ∀ t ∈ j', ∀ t' ∈ j', ∀ k : Fin (Module.finrank ℝ E),
          ethickness ℝ (W t).carrier k ≤ 2 * ethickness ℝ (W t').carrier k := by
  have ha : (0 : ℝ) < (δ : ℝ) := mod_cast hδ
  have hb : (δ : ℝ) ≤ (1 : ℝ) := mod_cast hδ1
  have hrange' : ∀ t ∈ j, (fun (k : Fin (Module.finrank ℝ E)) => ethickness ℝ (W t).carrier k) ∈
      Set.Icc (Function.const _ (ENNReal.ofReal (δ : ℝ)))
        (Function.const _ (ENNReal.ofReal (1 : ℝ))) := by
    intro t ht
    simp_rw [Set.mem_Icc, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_one]
    exact ⟨fun k => (hrange t ht k).1, fun k => (hrange t ht k).2⟩
  obtain ⟨j', hj', hsum, hle⟩ :=
    ENNReal.dyadic_pigeonhole j m
      (fun (t : J) (k : Fin (Module.finrank ℝ E)) => ethickness ℝ (W t).carrier k) ha hb hrange'
  refine ⟨j', hj', ?_, ?_⟩
  · simpa using hsum
  · intro t ht t' ht' k
    have hle' := hle t ht t' ht' k
    simpa using hle'

/-- Blueprint `lem:sumBlockWeightsLeMaxDensity`: for a family `P` of pairwise disjoint blocks with
union `s'`, the total weight of the blocks whose outer body `W_t` lies in `K` is at most
`Δ_max(𝕍') |K|`. -/
theorem sum_weight_parts_le_maxDensity_mul {P : Finset (Finset ι)}
    (hP : (P : Set (Finset ι)).PairwiseDisjoint id) (V : ι → ConvexSpaceBody E)
    (K : ConvexSpaceBody E) :
    ∑ t ∈ P with t.convexHull_biUnion V ≤ K, ∑ i ∈ t, volume (V i).carrier
      ≤ maxDensity (P.sup id) V * volume K.carrier := by
  have hsub : {t ∈ P | t.convexHull_biUnion V ≤ K} ⊆ P := Finset.filter_subset _ _
  rw [Finset.sum_sum_eq_sum_sup_id (hP.subset (mod_cast hsub)) (fun i ↦ volume (V i).carrier)]
  refine (Finset.sum_le_sum_of_subset fun i hi => ?_).trans
    (sum_volume_le_maxDensity_mul_volume (P.sup id) V K)
  obtain ⟨t, ht, hi'⟩ := Finset.mem_sup.1 hi
  exact Finset.mem_filter.mpr ⟨Finset.sup_mono (f := id) hsub hi,
    (t.le_convexHull_biUnion V hi').trans (Finset.mem_filter.mp ht).2⟩

end Shared

/-- [GWZ, Definition (Maximal density factoring with bias `ϖ`)], blueprint
`def:biasedFactoring`. A biased maximal density factoring of `V` (contained in a
convex reference set `U`) is a partition `𝕍 = ⊔_{W ∈ 𝕎} 𝕍_W` (with `𝕎` the family
`fun t ↦ t.convexHull_biUnion V` indexed by `parts`) obtained by maximizing the
*biased* density `|W|^{-ϖ} Δ(V, W)`. It satisfies, up to the slow-growing constant
`C`, the biased factoring estimates of [GWZ, Lemma 9.2]. -/
structure BiasedFactorization (U : ConvexSpaceBody E) (ϖ : ℝ) (C : NNReal)
    extends Finpartition s where
  /-- Each body of `𝕍` is contained in the reference set `U`. -/
  contained : ∀ i ∈ s, V i ≤ U
  /-- [GWZ, (factmaxmod1)] For *every* convex body `K` --- with no containment hypothesis
  relating `K` and `W ∈ 𝕎` --- `Δ(𝕍_W, K) ⪅ (|K|/|W|)^ϖ Δ(𝕍_W, W)`.  Taking `K ⊆ W` gives the
  Frostman reading; the unrestricted form is what the thick case of [GWZ, Section 9] consumes. -/
  densityIn_le_biased : ∀ t ∈ parts, ∀ K : ConvexSpaceBody E,
    densityIn t V K ≤
      (C : ENNReal) *
        (volume K.carrier / volume (t.convexHull_biUnion V).carrier) ^ ϖ *
        densityIn t V (t.convexHull_biUnion V)
  /-- For each `W ∈ 𝕎`, `Δ(𝕍_W, W) ≳ (|W|/|U|)^ϖ Δ_max(𝕍)`. -/
  maxDensity_le_densityIn_biased : ∀ t ∈ parts,
    (C : ENNReal)⁻¹ *
        (volume (t.convexHull_biUnion V).carrier / volume U.carrier) ^ ϖ * maxDensity s V ≤
      densityIn t V (t.convexHull_biUnion V)
  /-- [GWZ, (factmaxmod2)] `𝕎` is Katz--Tao with constant `C (|W|/|U|)^{-ϖ}`. -/
  isKatzTao : ∀ t ∈ parts,
    IsKatzTao parts (fun t' ↦ t'.convexHull_biUnion V)
      ((C : ENNReal) * (volume (t.convexHull_biUnion V).carrier / volume U.carrier) ^ (-ϖ))
  /-- Convex sets in `𝕎` are of similar dimensions. -/
  simDims : ∀ t ∈ parts, ∀ t' ∈ parts,
    ethickness ℝ (t.convexHull_biUnion V).carrier ≤ C •
      ethickness ℝ (t'.convexHull_biUnion V).carrier

/-- The `densityIn_le_biased` property implies being Frostman: blueprint item (i) of
`lemmafactmaxbias`, the biased counterpart of `ConvexSpaceBody.Factorization.isFrostman`.

Indeed for `K ≤ W_t` the volume ratio `|K| / |W_t|` is at most `1`, so its `ϖ`-th power is at
most `1` since `ϖ ≥ 0`. -/
theorem BiasedFactorization.isFrostman {s : Finset ι} {V : ι → ConvexSpaceBody E}
    {U : ConvexSpaceBody E} {ϖ : ℝ} {C : NNReal} (hϖ : 0 ≤ ϖ)
    (f : BiasedFactorization s V U ϖ C) :
    ∀ t ∈ f.parts, IsFrostmanIn t V (t.convexHull_biUnion V) C := by
  intro t ht K' hK'
  have h_div : volume K'.carrier / volume (t.convexHull_biUnion V).carrier ≤ (1 : ENNReal) :=
    (ENNReal.div_le_div (measure_mono (SetLike.coe_subset_coe.mpr hK')) le_rfl).trans
      ENNReal.div_self_le_one
  have h_rpow : (volume K'.carrier / volume (t.convexHull_biUnion V).carrier) ^ ϖ ≤ 1 :=
    (ENNReal.rpow_le_rpow h_div hϖ).trans_eq (ENNReal.one_rpow ϖ)
  refine (f.densityIn_le_biased t ht K').trans ?_
  calc (C : ENNReal) * (volume K'.carrier / volume (t.convexHull_biUnion V).carrier) ^ ϖ *
        densityIn t V (t.convexHull_biUnion V)
      ≤ (C : ENNReal) * 1 * densityIn t V (t.convexHull_biUnion V) :=
        mul_le_mul_left (mul_le_mul_right h_rpow _) _
    _ = _ := by rw [mul_one]

/-- The pigeonholing loss factor in `nonempty_biasedFactorization`, blueprint
`L_{\ref{lemmafactmaxbias}}`. It is the product of the two dyadic pigeonholing losses: the
first over the range `[2 ^ (-dim * ϖ), card * (c * δ ^ dim) ^ (-ϖ)]` of the biased scores,
the second over the `dim` ethicknesses of the outer bodies, each lying in `[δ, 1]`. It is
slow-growing in `δ` for fixed `dim` and `ϖ`. -/
@[nolint defsWithUnderscore]
noncomputable abbrev nonempty_biasedFactorization.L
    (dim : ℕ) (card : ℕ) (δ : NNReal) (ϖ : ℝ) : ENNReal :=
  ENNReal.ofReal (1 + Real.logb 2 ((card : ℝ) *
      ((2 : ℝ) ^ dim / ((Metric.lt_volume_convexHull.c dim : ℝ) * (δ : ℝ) ^ dim)) ^ ϖ)) *
    ENNReal.ofReal (1 + Real.logb 2 (1 / δ)) ^ dim

/-- The factoring constant in `nonempty_biasedFactorization`, blueprint
`C_{\ref{lemmafactmaxbias}}`. The factor `2` comes from the dyadic pigeonholing of the
biased scores and the factor `volume_comparison.C dim ^ ϖ = (4 ^ dim / c) ^ ϖ` from the
volume comparison of outer bodies with comparable ethicknesses. It depends only on the
ambient dimension and on the bias exponent `ϖ`, not on `δ`. -/
@[nolint defsWithUnderscore]
noncomputable abbrev nonempty_biasedFactorization.C (dim : ℕ) (ϖ : ℝ) : NNReal :=
  2 * Metric.volume_comparison.C dim ^ ϖ

namespace nonempty_biasedFactorization

section Constants

variable {δ : NNReal} {ϖ : ℝ}

/-- Blueprint `lem:biasedScoreRangeRatio`: the ratio `b / a` of the endpoints
`a = 2 ^ (-dim * ϖ)`, `b = card * (c * δ ^ dim) ^ (-ϖ)` of the biased score range is at least
`1` (and, being a real number, finite).  This is the admissibility hypothesis of the dyadic
pigeonholing `ENNReal.dyadic_pigeonhole₁`. -/
theorem one_le_range_ratio {dim card : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hϖ : 0 < ϖ)
    (hcard : 1 ≤ card) :
    1 ≤ (card : ℝ) *
      ((2 : ℝ) ^ dim / ((Metric.lt_volume_convexHull.c dim : ℝ) * (δ : ℝ) ^ dim)) ^ ϖ := by
  have hδpos : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hδ1' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hδsqdim : (δ : ℝ) ^ dim ≤ 1 := pow_le_one₀ (by positivity) hδ1'
  have hcpos : 0 < (Metric.lt_volume_convexHull.c dim : ℝ) := by
    exact_mod_cast Metric.lt_volume_convexHull.c_pos dim
  have hcleone : (Metric.lt_volume_convexHull.c dim : ℝ) ≤ 1 := by
    calc
      (Metric.lt_volume_convexHull.c dim : ℝ) = ((Nat.factorial dim : ℝ)⁻¹) := by
        simp [Metric.lt_volume_convexHull.c]
      _ ≤ 1 := Nat.cast_inv_le_one (Nat.factorial dim)
  have hden_pos : 0 < (Metric.lt_volume_convexHull.c dim : ℝ) * (δ : ℝ) ^ dim := by
    positivity
  have hden_le_one : (Metric.lt_volume_convexHull.c dim : ℝ) * (δ : ℝ) ^ dim ≤ 1 := by
    nlinarith
  have htwo_pow_ge_one : 1 ≤ (2 : ℝ) ^ dim :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) (n := dim)
  have hineq : (Metric.lt_volume_convexHull.c dim : ℝ) * (δ : ℝ) ^ dim ≤ (2 : ℝ) ^ dim := by
    nlinarith
  have hbase_ge_one :
      1 ≤ (2 : ℝ) ^ dim / ((Metric.lt_volume_convexHull.c dim : ℝ) * (δ : ℝ) ^ dim) := by
    field_simp [hden_pos.ne.symm]
    exact hineq
  have hpow_ge_one :
      1 ≤ ((2 : ℝ) ^ dim / ((Metric.lt_volume_convexHull.c dim : ℝ) * (δ : ℝ) ^ dim)) ^ ϖ :=
    Real.one_le_rpow hbase_ge_one (by linarith)
  have hcard_ge_one : (1 : ℝ) ≤ (card : ℝ) := by exact_mod_cast hcard
  exact one_le_mul_of_one_le_of_one_le hcard_ge_one hpow_ge_one

/-- Blueprint `lem:factmaxbiasLossBounds` (lower bound): the pigeonholing loss `L` is at least
`1`. -/
theorem one_le_L {dim card : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hϖ : 0 < ϖ) (hcard : 1 ≤ card) :
    1 ≤ L dim card δ ϖ := by
  have hb2 : (1 : ℝ) < (2 : ℝ) := by norm_num
  have hδpos : (0 : ℝ) < δ := mod_cast hδ
  have hlogbX : 0 ≤ Real.logb 2 ((card : ℝ) *
      ((2 : ℝ) ^ dim / ((Metric.lt_volume_convexHull.c dim : ℝ) * (δ : ℝ) ^ dim)) ^ ϖ) :=
    Real.logb_nonneg hb2 (one_le_range_ratio hδ hδ1 hϖ hcard)
  have hlogb1d : 0 ≤ Real.logb 2 ((1 : ℝ) / (δ : ℝ)) :=
    Real.logb_nonneg hb2 ((one_le_div hδpos).mpr (mod_cast hδ1 : (δ : ℝ) ≤ 1))
  have hA : 1 ≤ ENNReal.ofReal (1 + Real.logb 2 ((card : ℝ) *
      ((2 : ℝ) ^ dim / ((Metric.lt_volume_convexHull.c dim : ℝ) * (δ : ℝ) ^ dim)) ^ ϖ)) := by
    rw [ENNReal.one_le_ofReal]; linarith
  have hB : 1 ≤ ENNReal.ofReal (1 + Real.logb 2 ((1 : ℝ) / (δ : ℝ))) := by
    rw [ENNReal.one_le_ofReal]; linarith
  calc (1 : ENNReal) = 1 * 1 := (mul_one 1).symm
    _ ≤ _ := mul_le_mul' hA (one_le_pow_of_one_le' hB dim)

/-- Blueprint `lem:factmaxbiasLossBounds` (upper bound): the pigeonholing loss `L` is finite.
Being a product of `ENNReal.ofReal`s, this needs no hypotheses. -/
theorem L_lt_top {dim card : ℕ} : L dim card δ ϖ < ⊤ := by
  unfold L
  have hA : ENNReal.ofReal (1 + Real.logb 2 ((card : ℝ) *
      ((2 : ℝ) ^ dim / ((Metric.lt_volume_convexHull.c dim : ℝ) * (δ : ℝ) ^ dim)) ^ ϖ)) < ⊤ :=
    ENNReal.ofReal_lt_top
  have hB : ENNReal.ofReal (1 + Real.logb 2 (1 / δ)) < ⊤ := ENNReal.ofReal_lt_top
  have hBpow : ENNReal.ofReal (1 + Real.logb 2 (1 / δ)) ^ dim < ⊤ :=
    ENNReal.pow_lt_top hB
  exact ENNReal.mul_lt_top hA hBpow

/-- The factoring constant, pushed through the `NNReal → ENNReal` coercion.
-/
private theorem coe_C_eq {dim : ℕ} :
    (nonempty_biasedFactorization.C dim ϖ : ENNReal) =
      2 * (Metric.volume_comparison.C dim : ENNReal) ^ ϖ := by
  rw [show nonempty_biasedFactorization.C dim ϖ = 2 * Metric.volume_comparison.C dim ^ ϖ from rfl,
    ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero (Metric.volume_comparison.C_pos dim).ne',
    ENNReal.coe_ofNat]

/-- The factoring constant `C = 2 * volume_comparison.C dim ^ ϖ` is at least `2`, since the
volume comparison constant `4 ^ dim * dim !` is at least `1`.
-/
private theorem two_le_C {dim : ℕ} (hϖ : 0 ≤ ϖ) :
    (2 : ENNReal) ≤ (nonempty_biasedFactorization.C dim ϖ : ENNReal) := by
  have h_one_le_Cv : (1 : ENNReal) ≤ (Metric.volume_comparison.C dim : ENNReal) := by
    refine ENNReal.coe_le_coe.mpr ?_
    have hCval : Metric.volume_comparison.C dim =
        ((4 : ℝ) ^ dim * (Nat.factorial dim : ℝ) : ℝ) := by
      dsimp [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
      push_cast
      field_simp
    have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ dim := one_le_pow₀ (by norm_num)
    have hfac : (1 : ℝ) ≤ (Nat.factorial dim : ℝ) :=
      mod_cast Nat.succ_le_of_lt (Nat.factorial_pos dim)
    have : (1 : ℝ) ≤ Metric.volume_comparison.C dim := by rw [hCval]; nlinarith
    exact mod_cast this
  calc (2 : ENNReal) = 2 * (1 : ENNReal) ^ ϖ := by simp
    _ ≤ 2 * (Metric.volume_comparison.C dim : ENNReal) ^ ϖ := by gcongr
    _ = (nonempty_biasedFactorization.C dim ϖ : ENNReal) := coe_C_eq.symm

end Constants

section StandingHypotheses

variable
  [Nontrivial E]
  {δ : NNReal} {ϖ : ℝ}
  {s : Finset ι}
  {V : ι → ConvexSpaceBody E}
  (hδ : 0 < δ) (hϖ : 0 < ϖ) (hs : s.Nonempty)
  (h1 : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
  (h2 : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier)

omit [Nontrivial E] in
/-- The union of a subfamily of the blocks of the greedy partition is contained in `s`.
-/
private lemma sup_subset_of_subset_parts {P : Finset (Finset ι)}
    (hP : P ⊆ (Kakeya.greedyPartitionScore (Kakeya.biasedScore V ϖ) s).parts) : P.sup id ⊆ s :=
  (Finset.sup_mono hP).trans
    (Kakeya.greedyPartitionScore_isPartition (Kakeya.biasedScore V ϖ) s).2.le

omit [Nontrivial E] [DecidableEq ι] in
/-- The biased score of a nonempty block is its biased density inside its own outer body.
-/
private lemma biasedScore_eq_biasedDensityIn {t : Finset ι} (htne : t.Nonempty) :
    Kakeya.biasedScore V ϖ t = Kakeya.biasedDensityIn t V ϖ (t.convexHull_biUnion V) := by
  dsimp [Kakeya.biasedScore, Kakeya.biasedDensityIn]
  rw [Finset.filter_true_of_mem fun i hi => Finset.le_convexHull_biUnion V hi,
    htne.convexHull_biUnion_carrier V]

omit [DecidableEq ι] [Nontrivial E] in
include hδ h1 h2 in
/-- The outer body of a nonempty block of the family has positive volume: it dominates
`c_n δ ^ n > 0`.
-/
private lemma volume_convexHullBiUnion_pos {t : Finset ι} (htne : t.Nonempty) (hts : t ⊆ s) :
    0 < volume (t.convexHull_biUnion V).carrier :=
  lt_of_lt_of_le
    (ENNReal.mul_pos
      (ENNReal.coe_pos.mpr (Metric.lt_volume_convexHull.c_pos (Module.finrank ℝ E))).ne'
      (pow_ne_zero _ (ENNReal.coe_pos.mpr hδ).ne'))
    (Kakeya.volume_convexHullBiUnion_mem_Icc h1 h2 htne hts).1

include hδ h2 in
/-- Some body indexed by a nonempty block of the family has positive volume.
-/
private lemma exists_volume_pos {P : Finset (Finset ι)} {t : Finset ι} (ht : t ∈ P)
    (htne : t.Nonempty) (hts : t ⊆ s) : ∃ i ∈ P.sup id, 0 < volume (V i).carrier := by
  obtain ⟨i, hi⟩ := htne
  exact ⟨i, Finset.mem_sup.mpr ⟨t, ht, hi⟩, (V i).convex.volume_pos_of_scale_ne_zero
    (lt_of_lt_of_le (ENNReal.coe_pos.mpr hδ) (h2 i (hts hi))).ne'⟩

include hδ hs h1 h2 in
/-- Blueprint `lem:blockEthicknessPigeonhole`: the ethickness pigeonholing applied to the outer
bodies `W_t` of a subfamily `P₁` of the blocks of the greedy partition for the biased score. -/
theorem ethickness_pigeonhole {P₁ : Finset (Finset ι)}
    (hP₁ : P₁ ⊆ (Kakeya.greedyPartitionScore (Kakeya.biasedScore V ϖ) s).parts) :
    ∃ P ⊆ P₁,
      ∑ t ∈ P₁, ∑ i ∈ t, volume (V i).carrier ≤
          ENNReal.ofReal (1 + Real.logb 2 (1 / δ)) ^ Module.finrank ℝ E *
            ∑ t ∈ P, ∑ i ∈ t, volume (V i).carrier ∧
        ∀ t ∈ P, ∀ t' ∈ P, ∀ k : Fin (Module.finrank ℝ E),
          ethickness ℝ (t.convexHull_biUnion V).carrier k
            ≤ 2 * ethickness ℝ (t'.convexHull_biUnion V).carrier k := by
  set P0 := Kakeya.greedyPartitionScore (Kakeya.biasedScore V ϖ) s
  have hδ1 : δ ≤ 1 := ethickness.le_of_le_scale_of_subset h1 h2 hs
  have hrange : ∀ t ∈ P₁, ∀ k : Fin (Module.finrank ℝ E),
      ethickness ℝ ((fun (t' : Finset ι) => t'.convexHull_biUnion V) t).carrier k ∈
        Set.Icc (δ : ENNReal) 1 := by
    intro t ht k
    have htne : t.Nonempty := P0.nonempty_of_mem_parts (hP₁ ht)
    have htsub : t ⊆ s := P0.subset (hP₁ ht)
    have hk : (k : ℕ) < Module.finrank ℝ E := k.2
    have hmem := ethickness_convexHullBiUnion_mem_Icc h1 h2 htne htsub hk
    simpa using hmem
  exact exists_subset_ethickness_pigeonhole P₁ (fun t => t.convexHull_biUnion V)
    (fun t => ∑ i ∈ t, volume (V i).carrier) hδ hδ1 hrange

include hδ hϖ hs h1 h2 in
/-- Blueprint `lem:biasedScoreDyadicPigeonhole`: the one-dimensional dyadic pigeonholing of the
biased scores of the blocks of the greedy partition, over their range
`[2 ^ (-n ϖ), N (c δ ^ n) ^ (-ϖ)]`. -/
theorem constructA :
    ∃ P₁ ⊆ (Kakeya.greedyPartitionScore (Kakeya.biasedScore V ϖ) s).parts,
      ∑ t ∈ (Kakeya.greedyPartitionScore (Kakeya.biasedScore V ϖ) s).parts,
            ∑ i ∈ t, volume (V i).carrier ≤
          ENNReal.ofReal (1 + Real.logb 2 ((s.card : ℝ) *
              ((2 : ℝ) ^ Module.finrank ℝ E /
                ((Metric.lt_volume_convexHull.c (Module.finrank ℝ E) : ℝ) *
                  (δ : ℝ) ^ Module.finrank ℝ E)) ^ ϖ)) *
            ∑ t ∈ P₁, ∑ i ∈ t, volume (V i).carrier ∧
        ∀ t ∈ P₁, ∀ t' ∈ P₁, Kakeya.biasedScore V ϖ t ≤ 2 * Kakeya.biasedScore V ϖ t' := by
  let P0 := Kakeya.greedyPartitionScore (Kakeya.biasedScore V ϖ) s
  let w := fun t : Finset ι => ∑ i ∈ t, volume (V i).carrier
  have hσ0 : Kakeya.biasedScore V ϖ (∅ : Finset ι) = 0 := by
    simp only [Kakeya.biasedScore, Finset.sum_empty, ENNReal.zero_div]
  have hδ1 : δ ≤ 1 := ethickness.le_of_le_scale_of_subset h1 h2 hs
  set n := Module.finrank ℝ E
  set c := Metric.lt_volume_convexHull.c n
  -- The real bounds for the dyadic pigeonholing
  set a := (2 : ℝ) ^ (-(n : ℝ) * ϖ) with ha_def
  set b := (s.card : ℝ) * ((c : ℝ) * (δ : ℝ) ^ n) ^ (-ϖ) with hb_def
  have ha_pos : 0 < a := by rw [ha_def]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hpos_cδ : 0 < (c : ℝ) * (δ : ℝ) ^ n :=
    mul_pos (mod_cast Metric.lt_volume_convexHull.c_pos n) (pow_pos (mod_cast hδ) n)
  have hratio : 1 ≤ (s.card : ℝ) * ((2 : ℝ) ^ n / ((c : ℝ) * (δ : ℝ) ^ n)) ^ ϖ :=
    one_le_range_ratio hδ hδ1 hϖ (Finset.one_le_card.mpr hs)
  have hcalc : b / a = (s.card : ℝ) * ((2 : ℝ) ^ n / ((c : ℝ) * (δ : ℝ) ^ n)) ^ ϖ :=
    mul_rpow_neg_div_rpow hpos_cδ
  have hab : a ≤ b := (one_le_div ha_pos).mp (by rw [hcalc]; exact hratio)
  have hmem_Icc : ∀ t ∈ P0.parts,
      Kakeya.biasedScore V ϖ t ∈ Set.Icc (ENNReal.ofReal a) (ENNReal.ofReal b) := by
    intro t ht
    have htne : t.Nonempty := P0.nonempty_of_mem_parts ht
    have htsub : t ⊆ s := P0.subset ht
    have hmax : ∀ t' ⊆ t, Kakeya.biasedScore V ϖ t' ≤ Kakeya.biasedScore V ϖ t := fun _ ht' =>
      (Kakeya.le_maxScore (Kakeya.biasedScore V ϖ) ht').trans_eq
        (Kakeya.score_eq_maxScore_of_mem_greedyPartition hσ0 ht).symm
    refine ⟨?_, ?_⟩
    · have h := biasedScore_lower_bound hδ hϖ h1 h2 htne htsub hmax
      rwa [ha_def, ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)),
        show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    · have h := biasedScore_upper_bound hδ hϖ h2 htne htsub
      rw [hb_def, ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_rpow_of_pos hpos_cδ,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
      simpa using h
  obtain ⟨P₁, hP₁sub, hsum, hscore⟩ :=
    ENNReal.dyadic_pigeonhole₁ P0.parts w (fun t => Kakeya.biasedScore V ϖ t) ha_pos hab hmem_Icc
  exact ⟨P₁, hP₁sub, by rwa [hcalc] at hsum, hscore⟩

include hδ hs h2 in
/-- Blueprint `lem:blockWeightSum`: a weight bound between families of blocks transfers to the
corresponding index sets, and forces the surviving family of blocks to be nonempty. -/
theorem weight_subfamily {P : Finset (Finset ι)}
    (hP : P ⊆ (Kakeya.greedyPartitionScore (Kakeya.biasedScore V ϖ) s).parts) {loss : ENNReal}
    (hloss : ∑ t ∈ (Kakeya.greedyPartitionScore (Kakeya.biasedScore V ϖ) s).parts,
        ∑ i ∈ t, volume (V i).carrier ≤ loss * ∑ t ∈ P, ∑ i ∈ t, volume (V i).carrier) :
    ∑ i ∈ s, volume (V i).carrier ≤ loss * ∑ i ∈ P.sup id, volume (V i).carrier ∧ P.Nonempty := by
  let P0 := Kakeya.greedyPartitionScore (Kakeya.biasedScore V ϖ) s
  have hle : ∑ i ∈ s, volume (V i).carrier ≤ loss * ∑ i ∈ P.sup id, volume (V i).carrier := by
    calc
      ∑ i ∈ s, volume (V i).carrier = P0.parts.sum (fun t ↦ ∑ i ∈ t, volume (V i).carrier) := by
        exact P0.sum_eq_sum_parts_sum (fun i ↦ volume (V i).carrier)
      _ ≤ loss * P.sum (fun t ↦ ∑ i ∈ t, volume (V i).carrier) := by
        simpa [P0] using hloss
      _ = loss * ∑ i ∈ P.sup id, volume (V i).carrier := by
        rw [Finset.sum_sum_eq_sum_sup_id (P0.disjoint.subset hP) (fun i ↦ volume (V i).carrier)]
  refine ⟨hle, ?_⟩
  by_contra hPne
  have hPempty : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hPne
  have hsum_pos : 0 < ∑ i ∈ s, volume (V i).carrier := by
    refine ENNReal.sum_pos_of_nonempty hs ?_
    intro i hi
    apply (V i).convex.volume_pos_of_scale_ne_zero
    exact (lt_of_lt_of_le (ENNReal.coe_pos.mpr hδ) (h2 i hi)).ne.symm
  have hle0 : ∑ i ∈ s, volume (V i).carrier ≤ 0 := by
    calc
      _ ≤ loss * ∑ i ∈ P.sup id, volume (V i).carrier := hle
      _ = 0 := by simp [hPempty]
  exact (not_lt_of_ge hle0) hsum_pos

include hδ hϖ hs h1 h2 in
/-- Blueprint `lem:biasedTwoPigeonholings`: performing the two pigeonholings in succession
produces a nonempty subfamily `P` of the blocks of the greedy partition on which both the biased
scores and the ethicknesses of the outer bodies are pairwise comparable up to a factor `2`, at a
total cost of the loss `L`. -/
theorem constructB :
    ∃ P ⊆ (Kakeya.greedyPartitionScore (Kakeya.biasedScore V ϖ) s).parts, P.Nonempty ∧
      (∀ t ∈ P, ∀ t' ∈ P, Kakeya.biasedScore V ϖ t ≤ 2 * Kakeya.biasedScore V ϖ t') ∧
      (∀ t ∈ P, ∀ t' ∈ P, ∀ k : Fin (Module.finrank ℝ E),
        ethickness ℝ (t.convexHull_biUnion V).carrier k
          ≤ 2 * ethickness ℝ (t'.convexHull_biUnion V).carrier k) ∧
      (∑ t ∈ (Kakeya.greedyPartitionScore (Kakeya.biasedScore V ϖ) s).parts,
          ∑ i ∈ t, volume (V i).carrier ≤
        L (Module.finrank ℝ E) s.card δ ϖ * ∑ t ∈ P, ∑ i ∈ t, volume (V i).carrier) ∧
      ∑ i ∈ s, volume (V i).carrier ≤
        L (Module.finrank ℝ E) s.card δ ϖ * ∑ i ∈ P.sup id, volume (V i).carrier := by
  -- Step 1: Apply constructA to get P₁ with score comparability
  obtain ⟨P₁, hP₁_parts, hP₁_loss, hP₁_score⟩ :=
    constructA (hδ := hδ) (hϖ := hϖ) (hs := hs) (h1 := h1) (h2 := h2)
  -- Step 2: Apply ethickness_pigeonhole to P₁ to get P with ethickness comparability
  obtain ⟨P, hP_sub, hP_eth_loss, hP_eth⟩ :=
    ethickness_pigeonhole (hδ := hδ) (hs := hs) (h1 := h1) (h2 := h2) hP₁_parts
  -- P is still a subfamily of the blocks (transitivity)
  have hP_parts := hP_sub.trans hP₁_parts
  -- Chain the loss factors: `sum_all_parts ≤ L * sum_P`, using `L = firstFactor * secondFactor`
  have hP_loss : ∑ t ∈ (Kakeya.greedyPartitionScore (Kakeya.biasedScore V ϖ) s).parts,
      ∑ i ∈ t, volume (V i).carrier ≤
    L (Module.finrank ℝ E) s.card δ ϖ * ∑ t ∈ P, ∑ i ∈ t, volume (V i).carrier :=
    hP₁_loss.trans <| (mul_assoc _ _ _).ge.trans' (mul_le_mul_right hP_eth_loss _)
  -- Apply weight_subfamily to get nonemptiness and the index-weight bound
  obtain ⟨hP_index_weight, hP_nonempty⟩ :=
    weight_subfamily (hδ := hδ) (hs := hs) (h2 := h2) hP_parts hP_loss
  exact ⟨P, hP_parts, hP_nonempty,
    fun t ht t' ht' => hP₁_score t (hP_sub ht) t' (hP_sub ht'),
    hP_eth, hP_loss, hP_index_weight⟩

section Pigeonholed

variable
  {P : Finset (Finset ι)}
  (hP : P ⊆ (Kakeya.greedyPartitionScore (Kakeya.biasedScore V ϖ) s).parts)
  (hPne : P.Nonempty)
  (hPscore : ∀ t ∈ P, ∀ t' ∈ P, Kakeya.biasedScore V ϖ t ≤ 2 * Kakeya.biasedScore V ϖ t')
  (hPeth : ∀ t ∈ P, ∀ t' ∈ P, ∀ k : Fin (Module.finrank ℝ E),
    ethickness ℝ (t.convexHull_biUnion V).carrier k
      ≤ 2 * ethickness ℝ (t'.convexHull_biUnion V).carrier k)

omit [Nontrivial E] in
include h1 hP in
/-- Every body indexed by the union of the surviving blocks lies in the closed unit ball.
-/
private lemma le_closedUnitBall_of_mem_sup : ∀ i ∈ P.sup id, V i ≤ closedUnitBall := fun i hi =>
  SetLike.coe_subset_coe.mpr (h1 i (sup_subset_of_subset_parts hP hi))

omit [Nontrivial E] in
include hP hPscore in
/-- Blueprint `lem:biasedMaxLeTwoScore`: under the pigeonholed hypotheses `(⋆⋆)`, the maximal
biased density of the surviving family `𝕍'` is at most twice the biased score of any surviving
block. -/
theorem maxBiasedDensity_le_two_mul {t : Finset ι} (ht : t ∈ P) :
    Kakeya.maxBiasedDensity (P.sup id) V ϖ ≤ 2 * Kakeya.biasedScore V ϖ t := by
  have hσ : (Kakeya.biasedScore V ϖ) (∅ : Finset ι) = 0 := by simp [Kakeya.biasedScore]
  have hAne : P.Nonempty := ⟨t, ht⟩
  obtain ⟨r, hr, h⟩ := Kakeya.maxScore_eq_of_subset_greedyPartition hσ hAne hP
  have hmax : Kakeya.maxBiasedDensity (P.sup id) V ϖ = Kakeya.biasedScore V ϖ r := by
    calc
      Kakeya.maxBiasedDensity (P.sup id) V ϖ
          = Kakeya.maxScore (Kakeya.biasedScore V ϖ) (P.sup id) := rfl
      _ = Kakeya.biasedScore V ϖ r := h
  rw [hmax]
  exact hPscore r hr t ht

omit [Nontrivial E] in
include hδ hϖ h1 h2 hP hPscore in
/-- Blueprint `lem:biasedFrostman`: the biased Frostman estimate for the inner families, valid
for *every* convex body `K` with no containment hypothesis relating `K` and `W_t`. -/
theorem densityIn_le_biased {t : Finset ι} (ht : t ∈ P) (K : ConvexSpaceBody E) :
    densityIn t V K ≤
      2 * (volume K.carrier / volume (t.convexHull_biUnion V).carrier) ^ ϖ *
        densityIn t V (t.convexHull_biUnion V) := by
  have htne : t.Nonempty :=
    (Kakeya.greedyPartitionScore_isPartition (Kakeya.biasedScore V ϖ) s).1 t (hP ht)
  have hts : t ⊆ s := (Kakeya.greedyPartitionScore (Kakeya.biasedScore V ϖ) s).subset (hP ht)
  have hWtpos : volume (t.convexHull_biUnion V).carrier ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by positivity)
      (Kakeya.volume_convexHullBiUnion_mem_Icc h1 h2 htne hts).1)
  calc
    densityIn t V K ≤ densityIn (P.sup id) V K :=
      Kakeya.densityIn_mono' V K t _ (Finset.le_sup (f := id) ht)
    _ = volume K.carrier ^ ϖ * Kakeya.biasedDensityIn (P.sup id) V ϖ K :=
      Kakeya.densityIn_eq_rpow_mul_biasedDensityIn _ V hϖ K
    _ ≤ volume K.carrier ^ ϖ * (2 * Kakeya.biasedScore V ϖ t) :=
      mul_le_mul_right ((Kakeya.le_maxBiasedDensity _ V hϖ K).trans
        (maxBiasedDensity_le_two_mul hP hPscore ht)) _
    _ = 2 * (volume K.carrier ^ ϖ *
        Kakeya.biasedDensityIn t V ϖ (t.convexHull_biUnion V)) := by
      rw [biasedScore_eq_biasedDensityIn htne]; ring
    _ = 2 * ((volume K.carrier / volume (t.convexHull_biUnion V).carrier) ^ ϖ *
             densityIn t V (t.convexHull_biUnion V)) := by
      rw [Kakeya.rpow_mul_biasedDensityIn_eq_div_rpow_mul_densityIn t V hϖ K
        (t.convexHull_biUnion V) hWtpos]
    _ = _ := by ring

include hδ hϖ h1 h2 hP hPscore in
/-- Blueprint `lem:biasedMaxDensityLeMul`: the biased comparison of the maximal density of the
surviving family with the density inside a surviving block. -/
theorem maxDensity_le_mul_biased {t : Finset ι} (ht : t ∈ P) :
    2⁻¹ * (volume (t.convexHull_biUnion V).carrier /
          volume (closedUnitBall (E := E)).carrier) ^ ϖ * maxDensity (P.sup id) V
      ≤ densityIn t V (t.convexHull_biUnion V) := by
  set W := volume (t.convexHull_biUnion V).carrier
  set C := densityIn t V (t.convexHull_biUnion V) with hCdef
  have ht_nonempty : t.Nonempty :=
    (Kakeya.greedyPartitionScore_isPartition (Kakeya.biasedScore V ϖ) s).1 t (hP ht)
  have ht_sub_s : t ⊆ s :=
    (Kakeya.greedyPartitionScore (Kakeya.biasedScore V ϖ) s).subset (hP ht)
  -- `W` is positive and finite, hence so is `W ^ ϖ`
  have hvolW_ne_top : W ≠ ⊤ := (t.convexHull_biUnion V).isCompact.measure_ne_top
  have hWrpow_ne_zero : W ^ ϖ ≠ 0 :=
    (ENNReal.rpow_pos (volume_convexHullBiUnion_pos hδ h1 h2 ht_nonempty ht_sub_s)
      hvolW_ne_top).ne'
  -- bridge lemma: `biasedScore V ϖ t = W ^ (-ϖ) * C`
  have h_score_rpow : Kakeya.biasedScore V ϖ t = W ^ (-ϖ) * C := by
    have h_aux : C = W ^ ϖ * Kakeya.biasedScore V ϖ t := by
      rw [hCdef, biasedScore_eq_biasedDensityIn ht_nonempty]
      exact densityIn_eq_rpow_mul_biasedDensityIn t V hϖ (t.convexHull_biUnion V)
    rw [ENNReal.rpow_neg, h_aux, ← mul_assoc, ENNReal.inv_mul_cancel hWrpow_ne_zero
      (ENNReal.rpow_ne_top_of_nonneg hϖ.le hvolW_ne_top), one_mul]
  -- combine the maximal-density and the pigeonholed score estimates
  refine half_div_rpow_mul_le hϖ.le hWrpow_ne_zero
    (ENNReal.rpow_ne_top_of_nonneg hϖ.le hvolW_ne_top) ?_
  rw [← h_score_rpow]
  exact (rpow_mul_maxDensity_le_maxBiasedDensity hϖ
      (exists_volume_pos hδ h2 ht ht_nonempty ht_sub_s)
      (le_closedUnitBall_of_mem_sup h1 hP)).trans
    (maxBiasedDensity_le_two_mul hP hPscore ht)

omit [DecidableEq ι] in
include hϖ hPeth in
/-- Blueprint `lem:biasedBlockVolumeComparison`: comparable ethicknesses give comparable volumes,
hence comparable volume factors.  Note `(c / 4 ^ n) = (Metric.volume_comparison.C n)⁻¹`. -/
theorem rpow_volume_parts_le {t t' : Finset ι} (ht : t ∈ P) (ht' : t' ∈ P) :
    volume (t.convexHull_biUnion V).carrier ≤
        (Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal) *
          volume (t'.convexHull_biUnion V).carrier ∧
      ((Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal)⁻¹) ^ ϖ *
          (volume (t.convexHull_biUnion V).carrier /
            volume (closedUnitBall (E := E)).carrier) ^ ϖ
        ≤ (volume (t'.convexHull_biUnion V).carrier /
            volume (closedUnitBall (E := E)).carrier) ^ ϖ := by
  set n := Module.finrank ℝ E
  set C := (Metric.volume_comparison.C n : ENNReal)
  set Wt := (t.convexHull_biUnion V).carrier
  set Wt' := (t'.convexHull_biUnion V).carrier
  set B := (closedUnitBall (E := E)).carrier
  -- Part (a): volume comparison via comparable ethicknesses
  have hVolLe : volume Wt ≤ C * volume Wt' := by
    refine ConvexSpaceBody.volume_le_of_ethickness_le (fun k => ?_)
    by_cases hk : k < n
    · simpa only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] using hPeth t ht t' ht' ⟨k, hk⟩
    · simp only [Pi.smul_apply, ethickness_eq_zero_of_finrank_le (not_lt.mp hk), smul_zero, le_refl]
  -- Part (b): rpow inequality
  refine ⟨hVolLe, ?_⟩
  rw [← ENNReal.mul_rpow_of_nonneg _ _ hϖ.le, ← mul_div_assoc]
  refine ENNReal.rpow_le_rpow (ENNReal.div_le_div_right ?_ _) hϖ.le
  calc C⁻¹ * volume Wt ≤ C⁻¹ * (C * volume Wt') := mul_le_mul_right hVolLe _
    _ = volume Wt' := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel
        (ENNReal.coe_ne_zero.mpr (Metric.volume_comparison.C_pos n).ne') ENNReal.coe_ne_top,
        one_mul]

include hδ hϖ h1 h2 hP hPscore hPeth in
/-- Blueprint `lem:biasedBlockVolumeLowerBound`: the per-block form of the biased comparison. -/
theorem rpow_volume_mul_le {t t' : Finset ι} (ht : t ∈ P) (ht' : t' ∈ P) :
    ((Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal)⁻¹) ^ ϖ *
          (volume (t.convexHull_biUnion V).carrier /
            volume (closedUnitBall (E := E)).carrier) ^ ϖ *
          volume (t'.convexHull_biUnion V).carrier * maxDensity (P.sup id) V
      ≤ 2 * ∑ i ∈ t', volume (V i).carrier := by
  set C := (Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal)
  set Wt := t.convexHull_biUnion V
  set Wt' := t'.convexHull_biUnion V
  set B := closedUnitBall (E := E)
  have h_rpow_parts := (rpow_volume_parts_le hϖ hPeth ht ht').2
  have h_max_le : 2⁻¹ * (volume Wt'.carrier / volume B.carrier) ^ ϖ * maxDensity (P.sup id) V ≤
      densityIn t' V Wt' :=
    maxDensity_le_mul_biased hδ hϖ h1 h2 hP hPscore ht'
  -- clear the factor `2⁻¹` from `h_max_le`
  have key : (volume Wt'.carrier / volume B.carrier) ^ ϖ * maxDensity (P.sup id) V
      ≤ 2 * densityIn t' V Wt' := by
    calc (volume Wt'.carrier / volume B.carrier) ^ ϖ * maxDensity (P.sup id) V
        = 2 * (2⁻¹ * (volume Wt'.carrier / volume B.carrier) ^ ϖ * maxDensity (P.sup id) V) := by
          rw [← mul_assoc, ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero (by norm_num), one_mul]
      _ ≤ 2 * densityIn t' V Wt' := mul_le_mul_right h_max_le 2
  calc
    (C⁻¹) ^ ϖ * (volume Wt.carrier / volume B.carrier) ^ ϖ * volume Wt'.carrier *
          maxDensity (P.sup id) V
        ≤ (volume Wt'.carrier / volume B.carrier) ^ ϖ * volume Wt'.carrier *
          maxDensity (P.sup id) V :=
      mul_le_mul_left (mul_le_mul_left h_rpow_parts _) _
    _ = ((volume Wt'.carrier / volume B.carrier) ^ ϖ * maxDensity (P.sup id) V) *
          volume Wt'.carrier := by ring
    _ ≤ (2 * densityIn t' V Wt') * volume Wt'.carrier := mul_le_mul_left key _
    _ = 2 * ∑ i ∈ t', volume (V i).carrier := by
      rw [sum_volume_eq_densityIn_mul_volume' (t'.le_convexHull_biUnion V), mul_assoc]

include hδ hϖ h1 h2 hP hPscore hPeth in
/-- Blueprint `lem:biasedSumBlockVolumes`: summing the per-block estimate over the outer bodies
contained in a convex body `K`. -/
theorem sum_volume_parts_le {t : Finset ι} (ht : t ∈ P) (K : ConvexSpaceBody E) :
    ((Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal)⁻¹) ^ ϖ *
          (volume (t.convexHull_biUnion V).carrier /
            volume (closedUnitBall (E := E)).carrier) ^ ϖ *
          maxDensity (P.sup id) V *
          ∑ t' ∈ P with t'.convexHull_biUnion V ≤ K,
            volume (t'.convexHull_biUnion V).carrier
      ≤ 2 * maxDensity (P.sup id) V * volume K.carrier := by
  set A := ((Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal)⁻¹) ^ ϖ *
    (volume (t.convexHull_biUnion V).carrier / volume (closedUnitBall (E := E)).carrier) ^ ϖ
  set Δmax := maxDensity (P.sup id) V
  have hPdisjoint : (P : Set (Finset ι)).PairwiseDisjoint id :=
    ((Kakeya.greedyPartitionScore (Kakeya.biasedScore V ϖ) s).disjoint).subset (by
      simpa using hP)
  rw [mul_assoc (2 : ENNReal), Finset.mul_sum]
  calc
    ∑ t' ∈ P with t'.convexHull_biUnion V ≤ K,
          A * Δmax * volume (t'.convexHull_biUnion V).carrier
        ≤ ∑ t' ∈ P with t'.convexHull_biUnion V ≤ K, 2 * ∑ i ∈ t', volume (V i).carrier := by
      refine Finset.sum_le_sum fun t' ht' => ?_
      rw [mul_right_comm]
      exact rpow_volume_mul_le hδ hϖ h1 h2 hP hPscore hPeth ht (Finset.mem_filter.mp ht').1
    _ = 2 * ∑ t' ∈ P with t'.convexHull_biUnion V ≤ K, ∑ i ∈ t', volume (V i).carrier :=
      (Finset.mul_sum ..).symm
    _ ≤ 2 * (Δmax * volume K.carrier) :=
      mul_le_mul_right (sum_weight_parts_le_maxDensity_mul hPdisjoint V K) 2

include hδ hϖ h1 h2 hP hPscore hPeth in
/-- Blueprint `lem:biasedIsKatzTao`: the biased Katz--Tao estimate for the outer family `𝕎`. -/
theorem maxDensity_parts_le_biased {t : Finset ι} (ht : t ∈ P) :
    IsKatzTao P (fun t' ↦ t'.convexHull_biUnion V)
      ((nonempty_biasedFactorization.C (Module.finrank ℝ E) ϖ : ENNReal) *
        (volume (t.convexHull_biUnion V).carrier /
          volume (closedUnitBall (E := E)).carrier) ^ (-ϖ)) := by
  have htne : t.Nonempty :=
    (Kakeya.greedyPartitionScore_isPartition (Kakeya.biasedScore V ϖ) s).1 t (hP ht)
  have hts : t ⊆ s := (Kakeya.greedyPartitionScore (Kakeya.biasedScore V ϖ) s).subset (hP ht)
  have hBfin : volume (closedUnitBall (E := E)).carrier ≠ ⊤ :=
    ConvexSpaceBody.closedUnitBall.isCompact.measure_ne_top
  have hRfin : volume (t.convexHull_biUnion V).carrier /
      volume (closedUnitBall (E := E)).carrier ≠ ⊤ :=
    ENNReal.div_ne_top (t.convexHull_biUnion V).isCompact.measure_ne_top
      (ConvexSpaceBody.closedUnitBall_volume_pos (E := E)).ne'
  have hRpos : 0 < volume (t.convexHull_biUnion V).carrier /
      volume (closedUnitBall (E := E)).carrier :=
    pos_iff_ne_zero.mpr (ENNReal.div_ne_zero.mpr
      ⟨(volume_convexHullBiUnion_pos hδ h1 h2 htne hts).ne', hBfin⟩)
  rw [isKatzTao_iff, coe_C_eq]
  exact fun K => le_rpow_mul_of_mul_le hϖ.le
    (ENNReal.coe_ne_zero.mpr (Metric.volume_comparison.C_pos _).ne') ENNReal.coe_ne_top
    (ENNReal.rpow_pos hRpos hRfin).ne' (ENNReal.rpow_ne_top_of_nonneg hϖ.le hRfin)
    (lt_of_lt_of_le zero_lt_one
      (one_le_maxDensity (exists_volume_pos hδ h2 ht htne hts))).ne' (maxDensity_ne_top _ _)
    (sum_volume_parts_le hδ hϖ h1 h2 hP hPscore hPeth ht K)

end Pigeonholed

end StandingHypotheses

end nonempty_biasedFactorization

/-- The factor family underlying a biased factorization. -/
noncomputable abbrev BiasedFactorization.toFactorFamily {κ : Type*} [DecidableEq κ]
    {s : Finset κ} {V : κ → ConvexSpaceBody E} {U : ConvexSpaceBody E} {ϖ : ℝ} {C : NNReal}
    (f : BiasedFactorization s V U ϖ C) : FactorFamily E κ (Finset κ) :=
  FactorFamily.ofFinpartition V f.toFinpartition

/-- A partition part is its fiber in the factor family underlying a biased factorization. -/
theorem BiasedFactorization.toFactorFamily_fiber {κ : Type*} [DecidableEq κ]
    {s : Finset κ} {V : κ → ConvexSpaceBody E} {U : ConvexSpaceBody E} {ϖ : ℝ} {C : NNReal}
    (f : BiasedFactorization s V U ϖ C) {t : Finset κ} (ht : t ∈ f.parts) :
    f.toFactorFamily.fiber t = t := by
  exact FactorFamily.ofFinpartition_fiber V f.toFinpartition ht

/-- The inner bodies of a biased factorization lie in its reference body. -/
theorem BiasedFactorization.toFactorFamily_contained {κ : Type*} [DecidableEq κ]
    {s : Finset κ} {V : κ → ConvexSpaceBody E} {U : ConvexSpaceBody E} {ϖ : ℝ} {C : NNReal}
    (f : BiasedFactorization s V U ϖ C) :
    ∀ i ∈ f.toFactorFamily.innerSet, f.toFactorFamily.innerBody i ≤ U :=
  f.contained

/-- The first biased-density estimate, stated for the underlying factor family. -/
theorem BiasedFactorization.toFactorFamily_densityIn_le_biased
    {κ : Type*} [DecidableEq κ] {s : Finset κ} {V : κ → ConvexSpaceBody E}
    {U : ConvexSpaceBody E} {ϖ : ℝ} {C : NNReal} (f : BiasedFactorization s V U ϖ C) :
    ∀ t ∈ f.toFactorFamily.outerSet, ∀ K : ConvexSpaceBody E,
      densityIn (f.toFactorFamily.fiber t) f.toFactorFamily.innerBody K ≤
        (C : ENNReal) *
          (volume K.carrier / volume (f.toFactorFamily.outerBody t).carrier) ^ ϖ *
          densityIn (f.toFactorFamily.fiber t) f.toFactorFamily.innerBody
            (f.toFactorFamily.outerBody t) := by
  intro t ht K
  rw [f.toFactorFamily_fiber ht]
  exact f.densityIn_le_biased t ht K

/-- The lower biased-density estimate, stated for the underlying factor family. -/
theorem BiasedFactorization.toFactorFamily_maxDensity_le_densityIn_biased
    {κ : Type*} [DecidableEq κ] {s : Finset κ} {V : κ → ConvexSpaceBody E}
    {U : ConvexSpaceBody E} {ϖ : ℝ} {C : NNReal} (f : BiasedFactorization s V U ϖ C) :
    ∀ t ∈ f.toFactorFamily.outerSet,
      (C : ENNReal)⁻¹ *
          (volume (f.toFactorFamily.outerBody t).carrier / volume U.carrier) ^ ϖ *
          maxDensity f.toFactorFamily.innerSet f.toFactorFamily.innerBody ≤
        densityIn (f.toFactorFamily.fiber t) f.toFactorFamily.innerBody
          (f.toFactorFamily.outerBody t) := by
  intro t ht
  rw [f.toFactorFamily_fiber ht]
  exact f.maxDensity_le_densityIn_biased t ht

/-- The outer maximal-density estimate, stated for the underlying factor family. -/
theorem BiasedFactorization.toFactorFamily_maxDensity_outer_le_biased
    {κ : Type*} [DecidableEq κ] {s : Finset κ} {V : κ → ConvexSpaceBody E}
    {U : ConvexSpaceBody E} {ϖ : ℝ} {C : NNReal} (f : BiasedFactorization s V U ϖ C) :
    ∀ t ∈ f.toFactorFamily.outerSet,
      maxDensity f.toFactorFamily.outerSet f.toFactorFamily.outerBody ≤
        (C : ENNReal) *
          (volume (f.toFactorFamily.outerBody t).carrier / volume U.carrier) ^ (-ϖ) :=
  by
    intro t ht
    exact f.isKatzTao t ht

/-- The outer bodies of a biased factorization have comparable dimensions. -/
theorem BiasedFactorization.toFactorFamily_simDims
    {κ : Type*} [DecidableEq κ] {s : Finset κ} {V : κ → ConvexSpaceBody E}
    {U : ConvexSpaceBody E} {ϖ : ℝ} {C : NNReal} (f : BiasedFactorization s V U ϖ C) :
    ∀ t ∈ f.toFactorFamily.outerSet, ∀ t' ∈ f.toFactorFamily.outerSet,
      ethickness ℝ (f.toFactorFamily.outerBody t).carrier ≤
        C • ethickness ℝ (f.toFactorFamily.outerBody t').carrier :=
  f.simDims

/-- [GWZ, Lemma 9.2] Biased maximal density factoring lemma (blueprint
`lemmafactmaxbias`). Given a finite family `V` of convex bodies in `B₁` and a bias
exponent `ϖ > 0`, there is a subfamily `s' ⊆ s` capturing all but a slow-growing
fraction of the total volume and a biased maximal density factoring of `s'`. -/
theorem nonempty_biasedFactorization [Nontrivial E] {δ : NNReal} {ϖ : ℝ} (hϖ : 0 < ϖ)
    (hδ : 0 < δ) (hs : s.Nonempty)
    (h1 : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (h2 : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier) :
    ∃ s' ⊆ s,
      (∑ i ∈ s, volume (V i).carrier ≤
        (nonempty_biasedFactorization.L (Module.finrank ℝ E) s.card δ ϖ) *
          ∑ i ∈ s', volume (V i).carrier) ∧
      Nonempty (BiasedFactorization s' V ConvexSpaceBody.closedUnitBall ϖ
        (nonempty_biasedFactorization.C (Module.finrank ℝ E) ϖ)) := by
  -- Step 1: Apply the two pigeonholings (constructB) to get a subfamily P of blocks
  obtain ⟨P, hP_parts, hP_ne, hP_score, hP_eth, hP_loss, hP_index_weight⟩ :=
    nonempty_biasedFactorization.constructB (hδ := hδ) (hϖ := hϖ) (hs := hs) (h1 := h1) (h2 := h2)
  have h_two_le_C : (2 : ENNReal) ≤
      (nonempty_biasedFactorization.C (Module.finrank ℝ E) ϖ : ENNReal) :=
    nonempty_biasedFactorization.two_le_C hϖ.le
  -- Step 2: build the `BiasedFactorization` on `s' = P.sup id`
  refine ⟨P.sup id, nonempty_biasedFactorization.sup_subset_of_subset_parts hP_parts,
    hP_index_weight, ⟨{
    toFinpartition := (Kakeya.greedyPartitionScore (Kakeya.biasedScore V ϖ) s).ofSubset hP_parts rfl
    contained := nonempty_biasedFactorization.le_closedUnitBall_of_mem_sup h1 hP_parts
    densityIn_le_biased := fun t ht K =>
      (nonempty_biasedFactorization.densityIn_le_biased hδ hϖ h1 h2 hP_parts hP_score
        (ht : t ∈ P) K).trans (by gcongr)
    maxDensity_le_densityIn_biased := fun t ht =>
      le_trans (by gcongr) (nonempty_biasedFactorization.maxDensity_le_mul_biased hδ hϖ h1 h2
        hP_parts hP_score (ht : t ∈ P))
    isKatzTao := fun t ht => nonempty_biasedFactorization.maxDensity_parts_le_biased hδ hϖ h1 h2
      hP_parts hP_score hP_eth (ht : t ∈ P)
    simDims := fun t ht t' ht' k => by
      by_cases hk : k < Module.finrank ℝ E
      · exact (hP_eth t ht t' ht' ⟨k, hk⟩).trans (mul_le_mul_left h_two_le_C _)
      · push Not at hk
        simp [ethickness_eq_zero_of_finrank_le hk] }⟩⟩

end
end ConvexSpaceBody
