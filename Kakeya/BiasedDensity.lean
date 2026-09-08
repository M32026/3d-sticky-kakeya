/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Density
public import Kakeya.GreedyPartition
public import Kakeya.Mathlib.ENNReal
public import Kakeya.Thickness.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Biased density

We formalise the *biased* density `Δ_ϖ(𝕍, K) = |K|^{-ϖ} Δ(𝕍, K)` and the associated maximal
biased density `Δ^ϖ_max(𝕍)` of [GWZ, Section 9.2] (blueprint `def:biasedDelta`,
`def:biasedDeltamax`).

The biased density is implemented as the *single* division
`(∑ i ∈ 𝕍[K], |V i|) / |K| ^ (1 + ϖ)` in `[0, ∞]`, rather than as the product of the two extended
reals `|K|^{-ϖ}` and `Δ(𝕍, K)`, so that no indeterminate `0 * ∞` can arise.  When `|K| = 0` the
value is `0`, because the numerator vanishes (every `V i` with `i ∈ 𝕍[K]` is contained in `K`).
This follows the convention already used for `Kakeya.densityIn`.

As for `Kakeya.maxDensity`, the Lean definition of `Kakeya.maxBiasedDensity` is the maximum of the
biased *score* over subfamilies; that this agrees with the supremum over all convex bodies is
`Kakeya.iSup_biasedDensityIn_eq_maxBiasedDensity`.
-/

@[expose] public section

open MeasureTheory Metric Module
open Topology Convexity
open scoped ENNReal NNReal

namespace Kakeya

noncomputable section

variable
  {E : Type*} [TopologicalSpace E] [ConvexSpace ℝ E]
  [MeasureSpace E]
  {ι : Type*}

/-- `Δ_ϖ(𝕍, K)`, the *biased density* of the family `(V i)_{i ∈ s}` inside the convex body `K`
(blueprint `def:biasedDelta`).  Taking `ϖ = 0` recovers `Kakeya.densityIn`. -/
abbrev biasedDensityIn (s : Finset ι) (W : ι → ConvexSpaceBody E) (ϖ : ℝ)
    (K : ConvexSpaceBody E) : ENNReal :=
  (∑ i ∈ s with W i ≤ K, volume (W i).carrier) / volume K.carrier ^ (1 + ϖ)

/-- `σ_ϖ(t)`, the *biased score* of a subfamily `t`: the biased density of `(V i)_{i ∈ t}` inside
the convex hull `W_t = conv (⋃ i ∈ t, V i)` of the subfamily.

The raw convex hull is used rather than `Finset.convexHull_biUnion` so that the empty subfamily
gets score `0` (both numerator and denominator vanish, and `0 / 0 = 0` in `[0, ∞]`), as required
by the greedy partition construction. -/
abbrev biasedScore (W : ι → ConvexSpaceBody E) (ϖ : ℝ) (t : Finset ι) : ENNReal :=
  (∑ i ∈ t, volume (W i).carrier)
    / volume (Convexity.convexHull ℝ (⋃ i ∈ t, (W i).carrier)) ^ (1 + ϖ)

/-- `Δ^ϖ_max(𝕍)`, the *maximal biased density* (blueprint `def:biasedDeltamax`).

Following `Kakeya.maxDensity`, this is *defined* as the maximum of the biased score over
subfamilies (`Kakeya.maxScore`); that it agrees with the supremum of `biasedDensityIn` over all
convex bodies is `Kakeya.iSup_biasedDensityIn_eq_maxBiasedDensity`. -/
def maxBiasedDensity (s : Finset ι) (W : ι → ConvexSpaceBody E) (ϖ : ℝ) : ENNReal :=
  maxScore (biasedScore W ϖ) s

end

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-- Blueprint `lem:densityInEqRpowMulBiased`: the density is the biased density times the volume
factor `|K| ^ ϖ`. -/
theorem densityIn_eq_rpow_mul_biasedDensityIn (s : Finset ι) (W : ι → ConvexSpaceBody E)
    {ϖ : ℝ} (hϖ : 0 < ϖ) (K : ConvexSpaceBody E) :
    densityIn s W K = volume K.carrier ^ ϖ * biasedDensityIn s W ϖ K := by
  set V := volume K.carrier
  have hVne_top : V ≠ ∞ := K.isCompact.measure_ne_top
  by_cases hV0 : V = 0
  · rw [hV0, ENNReal.zero_rpow_of_pos hϖ, zero_mul]
    exact densityIn_eq_zero_of_volume_eq_zero hV0
  · have hp0 : V ^ ϖ ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hV0) hVne_top).ne'
    change (∑ i ∈ s with W i ≤ K, volume (W i).carrier) / V
        = V ^ ϖ * ((∑ i ∈ s with W i ≤ K, volume (W i).carrier) / V ^ (1 + ϖ : ℝ))
    rw [← mul_div_assoc, ENNReal.rpow_add _ _ hV0 hVne_top, ENNReal.rpow_one,
      mul_comm V (V ^ ϖ), ENNReal.mul_div_mul_left _ _ hp0
        (ENNReal.rpow_ne_top_of_nonneg hϖ.le hVne_top)]

/-- Blueprint `lem:rpowVolumeRatioBiased`: rewriting a biased density as a power of a volume
ratio times the (unbiased) density. -/
theorem rpow_mul_biasedDensityIn_eq_div_rpow_mul_densityIn (s : Finset ι)
    (W : ι → ConvexSpaceBody E) {ϖ : ℝ} (hϖ : 0 < ϖ) (K W' : ConvexSpaceBody E)
    (hW' : volume W'.carrier ≠ 0) :
    volume K.carrier ^ ϖ * biasedDensityIn s W ϖ W'
      = (volume K.carrier / volume W'.carrier) ^ ϖ * densityIn s W W' := by
  have hy_top : volume W'.carrier ≠ ⊤ := W'.isCompact.measure_ne_top
  rw [densityIn_eq_rpow_mul_biasedDensityIn s W hϖ W', ENNReal.div_rpow_of_nonneg _ _ hϖ.le,
    ← mul_assoc, ENNReal.div_mul_cancel
      (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hW') hy_top).ne'
      (ENNReal.rpow_ne_top_of_nonneg hϖ.le hy_top)]

/-- Blueprint `lem:maxBiasedDensityAttainedAtHull`: the biased density inside `K` is at most the
biased score of the subfamily `𝕍_u[K]` of members contained in `K`.

This is the biased analogue of `Kakeya.densityIn_maximizer_eq`; the point is that replacing `K` by
the hull of `𝕍_u[K]` keeps the numerator and does not increase the denominator. -/
theorem biasedDensityIn_le_biasedScore_familyIn (u : Finset ι) (W : ι → ConvexSpaceBody E)
    {ϖ : ℝ} (hϖ : 0 < ϖ) (K : ConvexSpaceBody E) :
    biasedDensityIn u W ϖ K ≤ biasedScore W ϖ (familyIn u W K) := by
  dsimp [biasedDensityIn, biasedScore, familyIn]
  gcongr
  exact Convexity.convexHull_min
    (Set.iUnion₂_subset fun _ hi => SetLike.coe_subset_coe.mpr (Finset.mem_filter.mp hi).2)
    K.isConvexSet

/-- Blueprint `lem:biasedScoreLeMaxBiasedDensity`: every biased density is at most the maximal
biased density.  The biased analogue of `Kakeya.le_maxDensity`. -/
theorem le_maxBiasedDensity (u : Finset ι) (W : ι → ConvexSpaceBody E) {ϖ : ℝ} (hϖ : 0 < ϖ)
    (K : ConvexSpaceBody E) :
    biasedDensityIn u W ϖ K ≤ maxBiasedDensity u W ϖ := by
  calc
    biasedDensityIn u W ϖ K ≤ biasedScore W ϖ (familyIn u W K) :=
      biasedDensityIn_le_biasedScore_familyIn u W hϖ K
    _ ≤ maxScore (biasedScore W ϖ) u :=
      le_maxScore (biasedScore W ϖ) (Finset.filter_subset (fun i ↦ W i ≤ K) u)
    _ = maxBiasedDensity u W ϖ := rfl

/-- The consequence of `Kakeya.le_maxBiasedDensity` recorded in blueprint
`lem:biasedScoreLeMaxBiasedDensity`: every biased score of a subfamily of `u` is at most the
maximal biased density of `u`.

Since `Kakeya.maxBiasedDensity` is *defined* as `Kakeya.maxScore` of the biased score, this holds
for every `ϖ`, with no positivity hypothesis. -/
theorem biasedScore_le_maxBiasedDensity {u t : Finset ι} (htu : t ⊆ u)
    (W : ι → ConvexSpaceBody E) (ϖ : ℝ) :
    biasedScore W ϖ t ≤ maxBiasedDensity u W ϖ :=
  le_maxScore _ htu

/-- Blueprint `lem:maxBiasedDensityEqMaxScore`: the supremum of the biased density over all convex
bodies agrees with `Kakeya.maxBiasedDensity`, i.e. with the maximal biased score over
subfamilies.  The biased analogue of `Kakeya.maxDensity_le_iff`. -/
theorem iSup_biasedDensityIn_eq_maxBiasedDensity (u : Finset ι) (W : ι → ConvexSpaceBody E)
    {ϖ : ℝ} (hϖ : 0 < ϖ) :
    ⨆ K : ConvexSpaceBody E, biasedDensityIn u W ϖ K = maxBiasedDensity u W ϖ := by
  refine le_antisymm (iSup_le fun K => le_maxBiasedDensity u W hϖ K) ?_
  set t := scoreMaximizer (biasedScore W ϖ) u
  change biasedScore W ϖ t ≤ _
  rcases t.eq_empty_or_nonempty with ht | ht
  · simp [ht, biasedScore]
  have hsub : t ⊆ {i ∈ u | W i ≤ t.convexHull_biUnion W} := fun i hi =>
    Finset.mem_filter.2 ⟨scoreMaximizer_subset _ _ hi, Finset.le_convexHull_biUnion W hi⟩
  calc
    biasedScore W ϖ t = (∑ i ∈ t, volume (W i).carrier)
        / volume (t.convexHull_biUnion W).carrier ^ (1 + ϖ) := by
      rw [ht.convexHull_biUnion_carrier W]
    _ ≤ biasedDensityIn u W ϖ (t.convexHull_biUnion W) :=
      ENNReal.div_le_div_right (Finset.sum_le_sum_of_subset hsub) _
    _ ≤ _ := le_iSup _ _

/-- Blueprint `lem:biasedScoreSingleton`: the biased score of a singleton subfamily is
`|V i| ^ (-ϖ)`, because `W_{i} = V i`. -/
theorem biasedScore_singleton (W : ι → ConvexSpaceBody E) (ϖ : ℝ) {i : ι}
    (hpos : 0 < volume (W i).carrier) :
    biasedScore W ϖ {i} = volume (W i).carrier ^ (-ϖ) := by
  have hconv : Convexity.convexHull ℝ ((W i).carrier) = (W i).carrier :=
    (W i).isConvexSet.convexHull_eq_self
  rw [show (-ϖ : ℝ) = 1 - (1 + ϖ) by ring,
    ENNReal.rpow_sub _ _ hpos.ne' (W i).isCompact.measure_ne_top]
  simp only [biasedScore, Finset.sum_singleton, Finset.set_biUnion_singleton, hconv,
    ENNReal.rpow_one]

/-- Raising to the negative power `-ϖ` is antitone on `[0, ∞]` for `0 ≤ ϖ`. -/
private lemma rpow_neg_le_rpow_neg {x y : ENNReal} {ϖ : ℝ} (hxy : x ≤ y) (hϖ : 0 ≤ ϖ) :
    y ^ (-ϖ) ≤ x ^ (-ϖ) := by
  rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
  exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow hxy hϖ)

section StandingHypotheses

variable
  [Nontrivial E]
  {δ : NNReal} {ϖ : ℝ}
  {s : Finset ι}
  {V : ι → ConvexSpaceBody E}

omit [Nontrivial E] in
/-- Blueprint `lem:biasedScoreLowerBound`: a lower bound `2 ^ (-n ϖ)` for the biased score of a
block of the greedy partition.

The hypothesis `hmax` is what membership in the greedy partition supplies (blueprint
`lem:scoreBlockEqMaxScore`): the score of a block is the maximum of the score over its
subfamilies.  Stating the lemma this way keeps it independent of the greedy construction. -/
theorem biasedScore_lower_bound (hδ : 0 < δ) (hϖ : 0 < ϖ)
    (h1 : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (h2 : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier)
    {t : Finset ι} (ht : t.Nonempty) (hts : t ⊆ s)
    (hmax : ∀ t' ⊆ t, biasedScore V ϖ t' ≤ biasedScore V ϖ t) :
    (2 : ENNReal) ^ (-(finrank ℝ E : ℝ) * ϖ) ≤ biasedScore V ϖ t := by
  -- It suffices to bound the score of a singleton subfamily `{i} ⊆ t`.
  obtain ⟨i, hi⟩ := ht
  have hi_s : i ∈ s := hts hi
  have hvol_pos : 0 < volume (V i).carrier :=
    (ENNReal.mul_pos (ENNReal.coe_pos.mpr (lt_volume_convexHull.c_pos _)).ne'
      (pow_ne_zero _ (ENNReal.coe_pos.mpr hδ).ne')).trans_le (le_volume_of_le_scale h2 hi_s)
  have hvol_le : volume (V i).carrier ≤ (2 : ENNReal) ^ (finrank ℝ E : ℝ) := by
    rw [ENNReal.rpow_natCast]
    exact (measure_mono (h1 i hi_s)).trans volume_closedBall_le_two_pow_finrank
  calc
    (2 : ENNReal) ^ (-(finrank ℝ E : ℝ) * ϖ)
        = ((2 : ENNReal) ^ (finrank ℝ E : ℝ)) ^ (-ϖ) := by
      rw [← ENNReal.rpow_mul, neg_mul, mul_neg]
    _ ≤ volume (V i).carrier ^ (-ϖ) := rpow_neg_le_rpow_neg hvol_le hϖ.le
    _ = biasedScore V ϖ {i} := (biasedScore_singleton V ϖ hvol_pos).symm
    _ ≤ biasedScore V ϖ t := hmax {i} (Finset.singleton_subset_iff.mpr hi)

omit [Nontrivial E] in
/-- Blueprint `lem:biasedScoreUpperBound`: the biased score of any nonempty subfamily is at most
`N * (c * δ ^ n) ^ (-ϖ)`, where `c = Metric.lt_volume_convexHull.c n` and `N = #s`. -/
theorem biasedScore_upper_bound (hδ : 0 < δ) (hϖ : 0 < ϖ)
    (h2 : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier)
    {t : Finset ι} (ht : t.Nonempty) (hts : t ⊆ s) :
    biasedScore V ϖ t ≤ (s.card : ENNReal) *
      ((lt_volume_convexHull.c (finrank ℝ E) : ENNReal) * (δ : ENNReal) ^ finrank ℝ E) ^ (-ϖ) := by
  set W := t.convexHull_biUnion V with hW_def
  set B := (lt_volume_convexHull.c (finrank ℝ E) : ENNReal) * (δ : ENNReal) ^ finrank ℝ E
  have hWtop : volume W.carrier ≠ ∞ := W.isCompact.measure_ne_top
  have hW_lower : B ≤ volume W.carrier := le_volume_convexHullBiUnion h2 ht hts
  have h0 : volume W.carrier ^ ϖ ≠ 0 :=
    (ENNReal.rpow_pos ((ENNReal.mul_pos (ENNReal.coe_pos.mpr (lt_volume_convexHull.c_pos _)).ne'
      (pow_ne_zero _ (ENNReal.coe_pos.mpr hδ).ne')).trans_le hW_lower) hWtop).ne'
  -- The score of `t` is the density in `W_t` corrected by the volume factor `|W_t| ^ (-ϖ)`.
  have hscore_eq : biasedDensityIn t V ϖ W = biasedScore V ϖ t := by
    dsimp only [biasedScore, biasedDensityIn]
    rw [Finset.filter_true_of_mem fun i hi => Finset.le_convexHull_biUnion V hi, hW_def,
      ht.convexHull_biUnion_carrier V]
  calc
    biasedScore V ϖ t = volume W.carrier ^ (-ϖ) * densityIn t V W := by
      rw [densityIn_eq_rpow_mul_biasedDensityIn t V hϖ W, hscore_eq, ENNReal.rpow_neg,
        ← mul_assoc, ENNReal.inv_mul_cancel h0 (ENNReal.rpow_ne_top_of_nonneg hϖ.le hWtop),
        one_mul]
    _ ≤ B ^ (-ϖ) * (s.card : ENNReal) :=
      mul_le_mul' (rpow_neg_le_rpow_neg hW_lower hϖ.le)
        ((densityIn_le_card t V W).trans (Nat.cast_le.2 (Finset.card_le_card hts)))
    _ = _ := mul_comm _ _

end StandingHypotheses

/-- Blueprint `lem:maxDensityLeMaxBiasedDensity`: the maximal density is dominated by the maximal
biased density, at the cost of the volume factor `|U| ^ (-ϖ)` of the ambient body `U`. -/
theorem rpow_mul_maxDensity_le_maxBiasedDensity {s' : Finset ι} {V : ι → ConvexSpaceBody E}
    {ϖ : ℝ} (hϖ : 0 < ϖ) (hpos : ∃ i ∈ s', 0 < volume (V i).carrier)
    {U : ConvexSpaceBody E} (hVU : ∀ i ∈ s', V i ≤ U) :
    volume U.carrier ^ (-ϖ) * maxDensity s' V ≤ maxBiasedDensity s' V ϖ := by
  obtain ⟨i, hi, hvi⟩ := hpos
  have hUtop : volume U.carrier ≠ ∞ := U.isCompact.measure_ne_top
  have hUp0 : volume U.carrier ^ ϖ ≠ 0 :=
    (ENNReal.rpow_pos (hvi.trans_le (measure_mono (SetLike.coe_subset_coe.mpr (hVU i hi))))
      hUtop).ne'
  rcases (density_maximizer s' V).eq_empty_or_nonempty with ht | ht
  · rw [maxDensity_eq_zero_of_maximizer_eq_empty ht, mul_zero]
    exact zero_le
  rw [← densityIn_self_maximizer_eq s' V]
  set K := (density_maximizer s' V).convexHull_biUnion V
  have hKU : volume K.carrier ^ ϖ ≤ volume U.carrier ^ ϖ :=
    ENNReal.rpow_le_rpow (measure_mono (SetLike.coe_subset_coe.mpr
      ((ht.convexHull_biUnion_le_iff V U).mpr fun j hj =>
        hVU j (density_maximizer_subset s' V hj)))) hϖ.le
  calc
    volume U.carrier ^ (-ϖ) * densityIn s' V K
        = volume U.carrier ^ (-ϖ) * volume K.carrier ^ ϖ * biasedDensityIn s' V ϖ K := by
      rw [densityIn_eq_rpow_mul_biasedDensityIn s' V hϖ K, ← mul_assoc]
    _ ≤ 1 * biasedDensityIn s' V ϖ K := by
      refine mul_le_mul_left ?_ _
      rw [ENNReal.rpow_neg,
        ← ENNReal.inv_mul_cancel hUp0 (ENNReal.rpow_ne_top_of_nonneg hϖ.le hUtop)]
      exact mul_le_mul_right hKU _
    _ ≤ maxBiasedDensity s' V ϖ := (one_mul _).trans_le (le_maxBiasedDensity s' V hϖ K)

end

end Kakeya
