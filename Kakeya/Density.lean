/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ConvexHull
public import Kakeya.ConvexBody
public import Kakeya.Tube.Basic
public import Kakeya.Tube.CardEssentiallyDistinct
public import Kakeya.Mathlib.MeasureTheory.Action
public import Kakeya.Mathlib.Algebra.Div

/-!
We formalise the notation $Δ(𝕎, K)$ and $Δ_max(𝕎)$ in [GWZ].
-/

@[expose] public section

open MeasureTheory
open Topology Convexity

-- (H.W.) Not sure which is appropriate : `ConvexSpaceBody.maxDensity` or `Finset.maxDenstity`
-- (H.W.) Before we decide on this, just use `Kakeya.maxDensity`
namespace Kakeya

noncomputable section
variable
  {E : Type*} [TopologicalSpace E] [ConvexSpace ℝ E]
  [MeasureSpace E]
  {ι : Type*}
  (s : Finset ι)
  (W : ι → ConvexSpaceBody E)

instance : DecidablePred fun i ↦ W i ≤ K := Classical.decPred _

/-- $𝕎[K]$ defined in [GWZ, Eq (1)]: the subfamily of `s` consisting of those indices `i`
  whose body `W i` is contained in `K`. -/
def familyIn (K : ConvexSpaceBody E) : Finset ι := {i ∈ s | W i ≤ K}

/-- $Δ(𝕎, K)$ defined in [GWZ, Eq (2)]
  We implement it with type `ENNReal`. It equals 0 if K has zero volume. -/
abbrev densityIn (K : ConvexSpaceBody E) : ENNReal :=
    (∑ i ∈ s with W i ≤ K, volume (W i).carrier) / volume K.carrier

/-  (H.W.) is it necessary to write this? given that `densityIn` is exposed?
See the proof of `IsFrostman.empty_parts`. -/
@[simp]
theorem densityIn_empty {W : ι → ConvexSpaceBody E} {K : ConvexSpaceBody E} :
    densityIn ∅ W K = 0 := by simp

lemma densityIn_mono' (K : ConvexSpaceBody E) (s t : Finset ι) (h : s ⊆ t) :
    densityIn s W K ≤ densityIn t W K := by
  simp only [densityIn]; gcongr

/-- `densityIn s W K` is monotone in `s` -/
theorem densityIn_mono (K : ConvexSpaceBody E) :
  Monotone fun s ↦ densityIn s W K := densityIn_mono' _ K

/-- If `K` has zero volume, then `densityIn s W K` is zero. -/
theorem densityIn_eq_zero_of_volume_eq_zero {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} (h : volume K.carrier = 0) : densityIn s W K = 0 := by
  simp only [ENNReal.div_eq_zero_iff, Finset.sum_eq_zero_iff, Finset.mem_filter, and_imp]
  exact Or.inl fun i _ hi ↦ measure_mono_null hi h

/-- Blueprint `lem:sumVolumeFamilyInEqZero`: a null test body carries no weight, because every
member of the family contained in it is null. -/
theorem sum_volume_familyIn_eq_zero_of_volume_eq_zero {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} (h : volume K.carrier = 0) :
    ∑ i ∈ s with W i ≤ K, volume (W i).carrier = 0 := by
  refine Finset.sum_eq_zero ?_
  intro i hi
  have hiW : W i ≤ K := (Finset.mem_filter.mp hi).2
  exact measure_mono_null hiW h

/-- If every member of the family is contained in `K` then `densityIn s W K` takes a simpler form -/
theorem densityIn_of_all_le {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} (h : ∀ i ∈ s, W i ≤ K) :
    densityIn s W K = (∑ i ∈ s, volume (W i).carrier) / volume K.carrier := by
  nth_rw 2 [← Finset.filter_eq_self.mpr h]

/-- Filtering the index set by the body-containment condition `W i ≤ K`
does not change `densityIn s W K`: the sum already only counts those `i`.
Useful for the Phase 3 filter-strengthen step in `density_to_isKatzTao`. -/
lemma densityIn_eq_densityIn_filter (s : Finset ι)
    (W : ι → ConvexSpaceBody E) (K : ConvexSpaceBody E) :
    densityIn s W K = densityIn {i ∈ s | W i ≤ K} W K := by
  classical
  unfold densityIn
  congr 1
  rw [Finset.filter_filter]
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext i
  simp [and_self]

/-- `densityIn` depends on the family only through its values on the index set. -/
theorem densityIn_congr {s : Finset ι} {W W' : ι → ConvexSpaceBody E} {K : ConvexSpaceBody E}
    (h : ∀ i ∈ s, W i = W' i) : densityIn s W K = densityIn s W' K := by
  unfold densityIn
  have hfilter : s.filter (fun i => W i ≤ K) = s.filter (fun i => W' i ≤ K) :=
    Finset.filter_congr (fun i hi => by rw [h i hi])
  rw [hfilter]
  refine congrArg (fun t => t / volume K.carrier) ?_
  apply Finset.sum_congr rfl (fun i hi => ?_)
  rw [h i ((Finset.mem_filter.mp hi).1)]


/-- This is `density s W K` specialized to `K` being a convex hull of a subfamily of sets in W. -/
abbrev densityInConvexHulliUnion (t : Finset ι) : ENNReal := (∑ i ∈ t, volume (W i).carrier)
    / (volume <| convexHull ℝ <| ⋃ i ∈ t, (W i).carrier)

/-- Given a family of convex body, encoded in `s W`,
  the function `densityIn s W : ConvexSpaceBody E -> ℝ` achieves its maximum
  at a convex body which is the convex hull of a union of some members of the given family.
  See `densityIn_self_maximizer_eq`. -/
@[nolint defsWithUnderscore]
def density_maximizer : Finset ι := (Finset.exists_max_image s.powerset
    (densityInConvexHulliUnion W) s.powerset_nonempty).choose

private lemma density_maximizer_spec : density_maximizer s W ∈ s.powerset ∧
    ∀ t ∈ s.powerset,
      densityInConvexHulliUnion W t ≤ densityInConvexHulliUnion W (density_maximizer s W) :=
  (Finset.exists_max_image _ _ s.powerset_nonempty).choose_spec

theorem density_maximizer_subset : density_maximizer s W ⊆ s := by
  simpa using (density_maximizer_spec s W).1

/-- We give an equivalent definition of $Δ_max(𝕎)$ defined in [GWZ, Eq (3)], using which it is
  easier to prove $Δ_max(𝕎)$ is attained by some convex body.
  Avoid using this definition directly. -/
def maxDensity : ENNReal := densityInConvexHulliUnion W (density_maximizer s W)

@[simp]
theorem maxDensity_empty : maxDensity ∅ W = 0 := by
  simp [maxDensity, show density_maximizer ∅ W = ∅ from
    Finset.subset_empty.1 (density_maximizer_subset _ _)]

theorem maxDensity_eq_zero_of_maximizer_eq_empty {s : Finset ι} {W : ι → ConvexSpaceBody E}
  (h : density_maximizer s W = ∅) : maxDensity s W = 0 := by
  unfold maxDensity
  simp [h]

private lemma densityIn_le_densityInConvexHulliUnion (K : ConvexSpaceBody E) :
    ∃ t ⊆ s, densityIn s W K ≤ densityInConvexHulliUnion W t := by
  use {i ∈ s | W i ≤ K}, by simp
  simp only [densityIn, densityInConvexHulliUnion, Finset.mem_filter]
  gcongr
  apply Convexity.convexHull_min
  · simp only [Set.iUnion_subset_iff, and_imp]
    exact fun (i : ι) (_ : i ∈ s) ↦ id
  · exact K.isConvexSet

/-- `maxDensity s W` is an upper bound for `densityIn s W : ConvexSpaceBody E → ENNReal`.
  It is actually the supremum. See `Kakeya.maxDensity_le_iff`. -/
theorem le_maxDensity (K : ConvexSpaceBody E) : densityIn s W K ≤ maxDensity s W := by
  obtain ⟨t, ht, htK⟩ := densityIn_le_densityInConvexHulliUnion s W K
  apply htK.trans
  apply (density_maximizer_spec s W).2
  simpa

/-- `densityInConvexHulliUnion` only sees the family on the subfamily it is applied to. -/
theorem densityInConvexHulliUnion_congr {W W' : ι → ConvexSpaceBody E} {t : Finset ι}
    (h : ∀ i ∈ t, W i = W' i) :
    densityInConvexHulliUnion W t = densityInConvexHulliUnion W' t := by
  unfold densityInConvexHulliUnion
  congr 1
  · apply Finset.sum_congr rfl (fun i hi => by rw [h i hi])
  · have h_union : (⋃ i ∈ t, (W i).carrier) = (⋃ i ∈ t, (W' i).carrier) := by
      refine Set.iUnion₂_congr (fun i hi => ?_)
      simpa using congrArg (·.carrier) (h i hi)
    rw [h_union]

/-- `maxDensity` depends on the family only through its values on the index set. -/
theorem maxDensity_congr {s : Finset ι} {W W' : ι → ConvexSpaceBody E}
    (h : ∀ i ∈ s, W i = W' i) : maxDensity s W = maxDensity s W' := by
  apply le_antisymm
  · have hm' := density_maximizer_spec s W'
    have hsub : density_maximizer s W ⊆ s := density_maximizer_subset s W
    calc
      maxDensity s W = densityInConvexHulliUnion W (density_maximizer s W) := rfl
      _ = densityInConvexHulliUnion W' (density_maximizer s W) :=
        densityInConvexHulliUnion_congr (fun i hi => h i (hsub hi))
      _ ≤ densityInConvexHulliUnion W' (density_maximizer s W') :=
        hm'.2 _ (by simpa using hsub)
      _ = maxDensity s W' := rfl
  · have hm' := density_maximizer_spec s W
    have hsub : density_maximizer s W' ⊆ s := density_maximizer_subset s W'
    calc
      maxDensity s W' = densityInConvexHulliUnion W' (density_maximizer s W') := rfl
      _ = densityInConvexHulliUnion W (density_maximizer s W') :=
        densityInConvexHulliUnion_congr (fun i hi => (h i (hsub hi)).symm)
      _ ≤ densityInConvexHulliUnion W (density_maximizer s W) :=
        hm'.2 _ (by simpa using hsub)
      _ = maxDensity s W := rfl

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}
  {s : Finset ι}
  {W : ι → ConvexSpaceBody E}

/-- `maxDensity` is at least `1`, if the family contains at least one element with positive vol. -/
theorem one_le_maxDensity (h : ∃ i ∈ s, 0 < volume (W i).carrier) :
    1 ≤ maxDensity s W := by
  obtain ⟨i, hi, hv⟩ := h
  refine le_trans ?_ (le_maxDensity s W (W i))
  rw [ENNReal.le_div_iff_mul_le (.inl hv.ne') (.inl (W i).3.measure_ne_top), one_mul]
  exact Finset.single_le_sum_of_canonicallyOrdered (f := fun j ↦ volume (W j).carrier)
    (Finset.mem_filter.mpr ⟨hi, le_rfl⟩)

/-- This can be taken as an equivalent definiton for `densityIn`,
  where no division is involved, only multiplication. -/
theorem sum_volume_eq_densityIn_mul_volume (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (K : ConvexSpaceBody E) :
    ∑ i ∈ s with W i ≤ K, volume (W i).carrier = densityIn s W K * volume K.carrier := by
  by_cases hK : volume K.carrier = 0
  · rw [sum_volume_familyIn_eq_zero_of_volume_eq_zero hK, hK, mul_zero]
  · rw [ENNReal.div_mul_cancel hK K.isCompact.measure_ne_top]

/-- Alternative definition of `densityIn s W K` when the entire family is contained in `K`. -/
theorem sum_volume_eq_densityIn_mul_volume' {K : ConvexSpaceBody E} (h : ∀ i ∈ s, W i ≤ K) :
    ∑ i ∈ s, volume (W i).carrier = densityIn s W K * volume K.carrier := by
  convert sum_volume_eq_densityIn_mul_volume s W K
  symm
  rwa [Finset.filter_eq_self]

theorem densityIn_le_iff (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (K : ConvexSpaceBody E) (C : ENNReal) :
    densityIn s W K ≤ C ↔
      ∑ i ∈ s with W i ≤ K, volume (W i).carrier ≤ C * volume K.carrier := by
  rw [sum_volume_eq_densityIn_mul_volume]
  by_cases hK : volume K.carrier = 0
  · simp [hK, densityIn_eq_zero_of_volume_eq_zero hK]
  · rw [ENNReal.mul_le_mul_iff_left hK K.3.measure_ne_top]

/-- An upper bound of `densityIn` in terms of `densityIn` of a subfamily. -/
theorem densityIn_le_of_sum_le {K : ConvexSpaceBody E} {t : Finset ι} {C : ENNReal}
    (h : ∑ i ∈ s with W i ≤ K, volume (W i).carrier ≤
      C * ∑ i ∈ t with W i ≤ K, volume (W i).carrier) :
    densityIn s W K ≤ C * densityIn t W K := by
  refine densityIn_le_iff _ _ _ _|>.2 <| h.trans ?_
  grw [mul_assoc, sum_volume_eq_densityIn_mul_volume]

theorem densityIn_le_card (s : Finset ι) (W : ι → ConvexSpaceBody E) (K : ConvexSpaceBody E) :
    densityIn s W K ≤ s.card := by
  rw [densityIn_le_iff, ← nsmul_eq_mul]
  calc ∑ i ∈ s with W i ≤ K, volume (W i).carrier
      ≤ {i ∈ s | W i ≤ K}.card • volume K.carrier :=
        Finset.sum_le_card_nsmul _ _ _ fun i hi ↦ measure_mono (Finset.mem_filter.mp hi).2
    _ ≤ s.card • volume K.carrier := nsmul_le_nsmul_left (by positivity) (Finset.card_filter_le s _)

/-- Count-and-minimum-volume lower bound for `densityIn`. -/
theorem densityIn_ge_of_count_volume {K : ConvexSpaceBody E} {t : Finset ι} {vmin : ENNReal}
    (htss : t ⊆ s) (htK : ∀ i ∈ t, W i ≤ K)
    (hvmin : ∀ i ∈ t, vmin ≤ volume (W i).carrier) :
    (t.card : ENNReal) * vmin / volume K.carrier ≤ densityIn s W K := by
  refine ENNReal.div_le_div_right ?_ _
  rw [← nsmul_eq_mul]
  exact (Finset.card_nsmul_le_sum t _ vmin hvmin).trans (Finset.sum_le_sum_of_subset
    fun i hi ↦ Finset.mem_filter.mpr ⟨htss hi, htK i hi⟩)

theorem densityIn_ne_top (s : Finset ι) (W : ι → ConvexSpaceBody E) (K : ConvexSpaceBody E) :
    densityIn s W K ≠ ⊤ := by
  refine ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (densityIn_le_card s _ _)

/-- The numerator of `densityIn` is monotone in the body argument. -/
theorem sum_volume_filter_le_of_le {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {K K' : ConvexSpaceBody E} (h : K' ≤ K) :
    ∑ i ∈ s with W i ≤ K', volume (W i).carrier ≤
      ∑ i ∈ s with W i ≤ K, volume (W i).carrier := by
  have hsub : (s.filter fun i => W i ≤ K') ⊆ (s.filter fun i => W i ≤ K) :=
    Finset.monotone_filter_right s (fun i hi hi' => hi'.trans h)
  exact Finset.sum_le_sum_of_subset hsub

/-- If the density in `K` vanishes, then it also vanishes in every sub-body of `K`. -/
theorem densityIn_eq_zero_of_le_of_eq_zero {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {K K' : ConvexSpaceBody E} (h : K' ≤ K) (h0 : densityIn s W K = 0) :
    densityIn s W K' = 0 := by
  have hvolKneTop : volume K.carrier ≠ ⊤ := K.isCompact.measure_ne_top
  unfold densityIn at h0 ⊢
  rw [ENNReal.div_eq_zero_iff] at h0
  have hnum : ∑ i ∈ s with W i ≤ K, volume (W i).carrier = 0 := by
    rcases h0 with (hsum0 | htop)
    · exact hsum0
    · exact absurd htop hvolKneTop
  have hnum' : ∑ i ∈ s with W i ≤ K', volume (W i).carrier = 0 := by
    have hsum' : ∑ i ∈ s with W i ≤ K', volume (W i).carrier ≤
        ∑ i ∈ s with W i ≤ K, volume (W i).carrier :=
      sum_volume_filter_le_of_le h
    rw [hnum] at hsum'
    exact le_antisymm hsum' zero_le
  rw [hnum', ENNReal.zero_div]

theorem densityIn_pos_iff (s : Finset ι) (W : ι → ConvexSpaceBody E) (K : ConvexSpaceBody E) :
    0 < densityIn s W K ↔ (∃ i ∈ s, 0 < volume (W i).carrier ∧  W i ≤ K) := by
  simp only [ENNReal.div_pos_iff, and_iff_left K.3.measure_ne_top, ← pos_iff_ne_zero,
    Finset.sum_pos_iff, Finset.mem_filter]
  exact ⟨fun ⟨i, ⟨his, hiK⟩, hv⟩ ↦ ⟨i, his, hv, hiK⟩, fun ⟨i, his, hv, hiK⟩ ↦ ⟨i, ⟨his, hiK⟩, hv⟩⟩

/-- A single member of the family contained in `K` gives a lower bound on `densityIn s W K`. -/
theorem le_densityIn (s : Finset ι) (W : ι → ConvexSpaceBody E) (K : ConvexSpaceBody E)
    {i : ι} (hi : i ∈ s) (hWK : W i ≤ K) :
    volume (W i).carrier / volume K.carrier ≤ densityIn s W K := by
  unfold densityIn
  gcongr
  exact Finset.single_le_sum_of_canonicallyOrdered (f := fun j ↦ volume (W j).carrier)
    (Finset.mem_filter.mpr ⟨hi, hWK⟩)

/- This is an immediate consequence of `densityIn_pos_iff`.
theorem densityIn_pos_of_all_le
    {s : Finset ι} {V : ι → ConvexSpaceBody E} {K : ConvexSpaceBody E}
    (hs : s.Nonempty)
    (hV_pos : ∀ i ∈ s, 0 < volume.real (V i).carrier)
    (hViK : ∀ i ∈ s, V i ≤ K)
    (hK_pos : 0 < volume.real K.carrier) :
    0 < densityIn s V K := by
  have h_eq : ∑ i ∈ s, volume.real (V i).carrier =
      densityIn s V K * volume.real K.carrier := by
    rw [← sum_volume_eq_densityIn_mul_volume,
      Finset.filter_true_of_mem (fun i hi => hViK i hi)]
  exact ((mul_pos_iff.mp (h_eq ▸ Finset.sum_pos
    (fun i hi => hV_pos i hi) hs)).resolve_right
    (fun h => absurd h.2 (not_lt.mpr (le_of_lt hK_pos)))).1
-/

/-- A handy property of `density_maximizer`. -/
theorem densityIn_maximizer_eq (s : Finset ι) (W : ι → ConvexSpaceBody E) :
    densityIn (density_maximizer s W) W ((density_maximizer s W).convexHull_biUnion W) =
      maxDensity s W := by
  refine le_antisymm ((densityIn_mono W _ (density_maximizer_subset s W)).trans
    (le_maxDensity s W _)) ?_
  by_cases he : density_maximizer s W = ∅
  · rw [maxDensity_eq_zero_of_maximizer_eq_empty he]; exact zero_le
  · unfold maxDensity densityInConvexHulliUnion densityIn
    replace he : (density_maximizer s W).Nonempty := Finset.nonempty_iff_ne_empty.mpr he
    simp only [Finset.convexHull_biUnion_of_nonempty he, Finset.convexHull_biUnion'_carrier]
    gcongr
    intro i
    simpa +contextual [Finset.mem_filter] using fun hi ↦
      (Finset.le_convexHull_biUnion W hi).trans_eq
      (Finset.convexHull_biUnion_of_nonempty he W)

/-- This property characterizes `density_maximizer`. See also `densityIn_maximizer_eq`. -/
theorem densityIn_self_maximizer_eq (s : Finset ι) (W : ι → ConvexSpaceBody E) :
    densityIn s W ((density_maximizer s W).convexHull_biUnion W) = maxDensity s W := by
  have h := density_maximizer_spec s W
  apply le_antisymm
  · apply le_maxDensity
  · rw [← densityIn_maximizer_eq]
    apply densityIn_mono
    apply density_maximizer_subset

/-- Together with `le_maxDensity`, we know `maxDensity` is indeed the supremum. -/
theorem maxDensity_le_iff (s : Finset ι) (W : ι → ConvexSpaceBody E) (r : ENNReal) :
    maxDensity s W ≤ r ↔ ∀ K, densityIn s W K ≤ r := by
  constructor <;> intro h
  · intro K
    trans maxDensity s W
    · apply le_maxDensity
    · exact h
  · rw [← densityIn_self_maximizer_eq]
    apply h

theorem maxDensity_mono (W : ι → ConvexSpaceBody E) : Monotone fun s ↦ maxDensity s W := by
  /- maxDensity monotone since powerset is monotone -/
  intro s t hst
  rw [maxDensity_le_iff]
  intro K
  trans densityIn t W K
  · exact densityIn_mono _ _ hst
  · apply le_maxDensity

theorem maxDensity_le_card (s : Finset ι)
    (W : ι → ConvexSpaceBody E) : maxDensity s W ≤ s.card := by
  rw [← densityIn_self_maximizer_eq]
  apply densityIn_le_card

theorem maxDensity_ne_top (s : Finset ι) (W : ι → ConvexSpaceBody E) : maxDensity s W ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (maxDensity_le_card s _)

/-- Blueprint `lem:maxDensityAttainedAtHullBody`: the maximal density is attained at the convex
hull `W_u` of a *nonempty* subfamily `u ⊆ s`, and that hull is contained in any convex body
containing all the members of the family. -/
theorem exists_convexHullBiUnion_densityIn_eq_maxDensity {s : Finset ι} {W : ι → ConvexSpaceBody E}
    (hpos : ∃ i ∈ s, 0 < volume (W i).carrier) :
    ∃ u ⊆ s, u.Nonempty ∧
      densityIn s W (u.convexHull_biUnion W) = maxDensity s W ∧
      ∀ U : ConvexSpaceBody E, (∀ i ∈ s, W i ≤ U) → u.convexHull_biUnion W ≤ U := by
  have hu_sub : density_maximizer s W ⊆ s := density_maximizer_subset s W
  have hu_nonempty : (density_maximizer s W).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr fun he ↦ one_ne_zero (α := ENNReal) <| le_zero_iff.mp <|
      maxDensity_eq_zero_of_maximizer_eq_empty he ▸ one_le_maxDensity hpos
  exact ⟨_, hu_sub, hu_nonempty, densityIn_self_maximizer_eq s W, fun U hU ↦
    (hu_nonempty.convexHull_biUnion_le_iff W U).2 fun i hi ↦ hU i (hu_sub hi)⟩

/-- Blueprint `lem:maxDensityLeOfForallSumLe`: a uniform bound `∑_{𝕎[K]}|W_t| ≤ c|K|` over all
convex bodies `K` gives `Δ_max(𝕎) ≤ c`. -/
theorem maxDensity_le_of_forall_sum_le {s : Finset ι} {W : ι → ConvexSpaceBody E} {c : ENNReal}
    (h : ∀ K : ConvexSpaceBody E,
      ∑ i ∈ s with W i ≤ K, volume (W i).carrier ≤ c * volume K.carrier) :
    maxDensity s W ≤ c :=
  (maxDensity_le_iff s W c).2 fun K ↦ (densityIn_le_iff s W K c).2 (h K)

/-- An upper bound in terms of `maxDensity` for the sum of volumes of subsets in the family `s`,
  contained in `K`. `maxDensity` is very often used in this way. -/
theorem sum_volume_le_maxDensity_mul_volume (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (K : ConvexSpaceBody E) :
    ∑ i ∈ s with W i ≤ K, volume (W i).carrier ≤ maxDensity s W * volume K.carrier := by
  rw [sum_volume_eq_densityIn_mul_volume]
  gcongr
  exact le_maxDensity s W K

/-- A variant of `sum_volume_le_maxDensity_mul_volume`. -/
theorem sum_volume_le_maxDensity_mul_volume' {W : ι → ConvexSpaceBody E} (h : ∀ i ∈ s, W i ≤ K) :
    ∑ i ∈ s, volume (W i).carrier ≤ maxDensity s W * volume K.carrier := by
  convert sum_volume_le_maxDensity_mul_volume s W K
  symm
  rwa [Finset.filter_eq_self]

/-- The multiplicative constant in `IsKatzTao.tube_card_le` depending only on the dimension.
It is the volume `√π ^ dim / Γ(dim / 2 + 1)` of the closed unit ball, divided by the constant
`Tube.le_volume.c dim` of the tube volume lower bound.  Since
`Tube.le_volume.c dim = (√π ^ dim / Γ(dim / 2 + 1)) / 3`, this constant is in fact equal to `3`
for every `dim`; see the note below. -/
-- NOTE: the numerator re-spells the unit-ball volume that `Tube.le_volume.c` already encodes,
-- so this whole constant collapses to the numeral `3`.  Simplifying it to `3` (or to
-- `3 * Tube.le_volume.c dim / Tube.le_volume.c dim`) is a genuine improvement but requires
-- repairing the `hV₁` step of `Tube.card_le_of_densityIn_le` below, which is out of scope for a
-- statement-only pass.  Left as a follow-up.
@[nolint defsWithUnderscore]
noncomputable abbrev Tube.card_le_of_densityIn_le.C (dim : ℕ) : NNReal :=
  ⟨√Real.pi ^ dim / Real.Gamma (dim / 2 + 1), by positivity⟩ / Tube.le_volume.c dim

/-- If a family of δ-tubes in the unit ball is C-convex Katz-Tao, then
    the number of tubes is at most C * δ^(-(n-1)) up to a multiplicative constant. -/
theorem Tube.card_le_of_densityIn_le [Nontrivial E] {δ : NNReal} (hδ : δ ≠ 0) {T : ι → Tube δ E}
    (hT : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) {C : ENNReal}
    (h : densityIn s (fun i ↦ (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall ≤ C) :
    s.card ≤ card_le_of_densityIn_le.C (Module.finrank ℝ E) *
      C * δ ^ (-(Module.finrank ℝ E - 1 : ℤ)) := by
  set n := Module.finrank ℝ E
  have hn : 0 < n := Module.finrank_pos
  have hc : (Tube.le_volume.c n : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos n).ne'
  have hV₁ : volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier
      = card_le_of_densityIn_le.C n * Tube.le_volume.c n := by
    simp only [ConvexSpaceBody.closedUnitBall_carrier, InnerProductSpace.volume_closedBall,
      ENNReal.ofReal_one, one_pow, one_mul]
    rw [ENNReal.ofReal_eq_coe_nnreal (by positivity), ← ENNReal.coe_mul]
    norm_cast
    exact (div_mul_cancel₀ _ (Tube.le_volume.c_pos _).ne').symm
  have h1 : (s.card : ENNReal) * Tube.le_volume.c n * δ ^ (n - 1)
      ≤ C * volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier :=
    calc ((s.card : ENNReal) * Tube.le_volume.c n * δ ^ (n - 1))
        = ∑ _i ∈ s, (Tube.le_volume.c n * δ ^ (n - 1) : ENNReal) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ _ := Finset.sum_le_sum fun _ _ ↦ Tube.le_volume _
      _ = _ := sum_volume_eq_densityIn_mul_volume' (K := ConvexSpaceBody.closedUnitBall) hT
      _ ≤ _ := mul_le_mul_left h _
  calc _
      ≤ C * volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier
          / (Tube.le_volume.c n * δ ^ (n - 1)) := by
        rw [ENNReal.le_div_iff_mul_le
          (.inl (mul_ne_zero hc (pow_ne_zero _ (ENNReal.coe_ne_zero.mpr hδ))))
          (.inl (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)))]
        rwa [← mul_assoc]
    _ = _ := by
        rw [hV₁, mul_comm (Tube.le_volume.c n : ENNReal) ((δ : ENNReal) ^ (n - 1)), ← mul_assoc,
          ENNReal.mul_div_mul_right _ _ hc ENNReal.coe_ne_top,
          show ((n : ℤ) - 1) = ((n - 1 : ℕ) : ℤ) from by omega,
          ENNReal.zpow_neg, zpow_natCast, div_eq_mul_inv,
          mul_comm C (card_le_of_densityIn_le.C n : ENNReal)]

theorem densityIn_mul_le_of_volume_band {ι' : Type*} (t : Finset ι') (W : ι' → ConvexSpaceBody E)
    (K : ConvexSpaceBody E) {vhi vlo : ENNReal}
    (hW : ∀ i ∈ t, volume (W i).carrier ≤ vhi) (hK : vlo ≤ volume K.carrier) :
    Kakeya.densityIn t W K * vlo ≤ ((Kakeya.familyIn t W K).card : ENNReal) * vhi := by
  calc
    Kakeya.densityIn t W K * vlo
        ≤ Kakeya.densityIn t W K * volume K.carrier := mul_le_mul' le_rfl hK
    _ = ∑ i ∈ t with W i ≤ K, volume (W i).carrier := by
      rw [← Kakeya.sum_volume_eq_densityIn_mul_volume t W K]
    _ = ∑ i ∈ Kakeya.familyIn t W K, volume (W i).carrier := rfl
    _ ≤ ∑ i ∈ Kakeya.familyIn t W K, vhi := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' : i ∈ t := (Finset.mem_filter.mp hi).1
      exact hW i hi'
    _ = ((Kakeya.familyIn t W K).card : ENNReal) * vhi := by
      simp [Finset.sum_const, nsmul_eq_mul]

theorem le_densityIn_mul_of_volume_band {ι' : Type*} (t : Finset ι') (W : ι' → ConvexSpaceBody E)
    (K : ConvexSpaceBody E) {vhi vlo : ENNReal}
    (hW : ∀ i ∈ t, vlo ≤ volume (W i).carrier) (hK : volume K.carrier ≤ vhi) :
    ((Kakeya.familyIn t W K).card : ENNReal) * vlo ≤ Kakeya.densityIn t W K * vhi := by
  have hcard_sum : ((Kakeya.familyIn t W K).card : ENNReal) * vlo ≤
      ∑ i ∈ Kakeya.familyIn t W K, volume (W i).carrier := by
    calc
      ((Kakeya.familyIn t W K).card : ENNReal) * vlo
          = (Kakeya.familyIn t W K).card • vlo := by rw [nsmul_eq_mul]
      _ ≤ ∑ i ∈ Kakeya.familyIn t W K, volume (W i).carrier :=
        Finset.card_nsmul_le_sum (Kakeya.familyIn t W K) (fun i => volume (W i).carrier) vlo ?_
    intro i hi
    apply hW i
    simpa [Kakeya.familyIn] using Finset.mem_filter.mp hi |>.left
  calc
    ((Kakeya.familyIn t W K).card : ENNReal) * vlo
        ≤ ∑ i ∈ Kakeya.familyIn t W K, volume (W i).carrier := hcard_sum
    _ = Kakeya.densityIn t W K * volume K.carrier := by
      simpa [Kakeya.familyIn] using Kakeya.sum_volume_eq_densityIn_mul_volume t W K
    _ ≤ Kakeya.densityIn t W K * vhi := by
      gcongr

/-- `Kakeya.maxDensity` is subadditive along a covering of the index set: monotone in the index set
and additive-dominated on a union, both read off `Kakeya.maxDensity_le_iff`. -/
theorem maxDensity_le_sum_of_subset_biUnion {ι' : Type*} [DecidableEq ι] {u : Finset ι}
    {A : Finset ι'} {f : ι' → Finset ι} (W : ι → ConvexSpaceBody E) (hu : u ⊆ A.biUnion f) :
    Kakeya.maxDensity u W ≤ ∑ a ∈ A, Kakeya.maxDensity (f a) W := by
  classical
  rw [Kakeya.maxDensity_le_iff]
  intro K
  have hsub : u.filter (fun i => W i ≤ K) ⊆
      A.biUnion (fun a => (f a).filter (fun i => W i ≤ K)) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨a, haA, hia⟩ := Finset.mem_biUnion.mp (hu hi.1)
    exact Finset.mem_biUnion.mpr ⟨a, haA, Finset.mem_filter.mpr ⟨hia, hi.2⟩⟩
  have hbi : ∀ (B : Finset ι') (g : ι → ENNReal),
      (∑ i ∈ B.biUnion (fun a => (f a).filter (fun i => W i ≤ K)), g i)
        ≤ ∑ a ∈ B, ∑ i ∈ (f a).filter (fun i => W i ≤ K), g i := by
    intro B g
    induction B using Finset.cons_induction with
    | empty => simp
    | cons a B ha ih =>
      rw [Finset.cons_eq_insert, Finset.biUnion_insert, Finset.sum_insert ha]
      set X : Finset ι := (f a).filter (fun i => W i ≤ K) with hX
      set Y : Finset ι := B.biUnion (fun c => (f c).filter (fun i => W i ≤ K)) with hY
      have hdisj : Disjoint X (Y \ X) := Finset.disjoint_sdiff
      have hunion : X ∪ Y = X ∪ (Y \ X) := by
        rw [Finset.union_sdiff_self_eq_union]
      calc (∑ i ∈ X ∪ Y, g i)
          = ∑ i ∈ X ∪ (Y \ X), g i := by rw [hunion]
        _ = (∑ i ∈ X, g i) + ∑ i ∈ Y \ X, g i := Finset.sum_union hdisj
        _ ≤ (∑ i ∈ X, g i) + ∑ i ∈ Y, g i := by
            have hle : (∑ i ∈ Y \ X, g i) ≤ ∑ i ∈ Y, g i :=
              Finset.sum_le_sum_of_subset (Finset.sdiff_subset (s := Y) (t := X))
            gcongr
        _ ≤ (∑ i ∈ X, g i) + ∑ c ∈ B, ∑ i ∈ (f c).filter (fun i => W i ≤ K), g i := by
            gcongr
  have hnum : (∑ i ∈ u.filter (fun i => W i ≤ K), volume (W i).carrier)
      ≤ ∑ a ∈ A, ∑ i ∈ (f a).filter (fun i => W i ≤ K), volume (W i).carrier :=
    le_trans (Finset.sum_le_sum_of_subset hsub) (hbi A _)
  calc Kakeya.densityIn u W K
      ≤ (∑ a ∈ A, ∑ i ∈ (f a).filter (fun i => W i ≤ K), volume (W i).carrier)
          / volume K.carrier := ENNReal.div_le_div_right hnum _
    _ = ∑ a ∈ A, Kakeya.densityIn (f a) W K := by
        simp only [Kakeya.densityIn, div_eq_mul_inv, Finset.sum_mul]
    _ ≤ ∑ a ∈ A, Kakeya.maxDensity (f a) W :=
        Finset.sum_le_sum fun a _ => Kakeya.le_maxDensity (f a) W K

section TranslationInvariance

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-- Volume of a translated convex body equals the volume of the original. -/
lemma volumeReal_translate (K : ConvexSpaceBody E) (v : E) :
    volume.real (ConvexSpaceBody.translate K v).carrier = volume.real K.carrier := by
  change volume.real ((v + ·) '' K.carrier) = volume.real K.carrier
  exact measureReal_image_add volume v K.carrier

/-- ENNReal volume of a translated convex body equals the volume of the original. -/
lemma volume_translate (K : ConvexSpaceBody E) (v : E) :
    volume (ConvexSpaceBody.translate K v).carrier = volume K.carrier := by
  change volume ((v + ·) '' K.carrier) = volume K.carrier
  exact MeasureTheory.measure_image_add _ _ _

/-- `densityIn` is invariant under translating the test body and all bodies
    by the same constant vector. -/
lemma densityIn_translate (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (K : ConvexSpaceBody E) (v : E) : densityIn s (fun i => ConvexSpaceBody.translate (W i) v)
    (ConvexSpaceBody.translate K v) = densityIn s W K := div_eq_div_of_eq_eq (by congr <;> simp) <|
  MeasureTheory.measure_image_add _ _ _

/-- `maxDensity` is invariant under translating every body in the family by
    the same constant vector. The supremum is taken over all test convex
    bodies, and translation by `v` is a bijection on `ConvexBody E`. -/
lemma maxDensity_translate (s : Finset ι) (W : ι → ConvexSpaceBody E) (v : E) :
    maxDensity s (fun i => ConvexSpaceBody.translate (W i) v) = maxDensity s W := by
  apply le_antisymm
  · rw [maxDensity_le_iff]
    intro K
    have hK : K = ConvexSpaceBody.translate (ConvexSpaceBody.translate K (-v)) v :=
      (ConvexSpaceBody.translate_neg_cancel (K := K) (v := v)).symm
    rw [hK, densityIn_translate]
    exact le_maxDensity s W _
  · rw [maxDensity_le_iff]
    intro K
    rw [← densityIn_translate s W K v]
    exact le_maxDensity s (fun i => ConvexSpaceBody.translate (W i) v) _

end TranslationInvariance


end

end Kakeya

/-!
# Indexed-family conversion helpers
-/

open MeasureTheory


namespace Kakeya

variable
  (E : Type*)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `densityIn` only depends on the bodies indexed by `s`. -/
lemma densityIn_eq_of_eqOn
    {ι : Type*} (s : Finset ι) {W W' : ι → ConvexSpaceBody E}
    (h : ∀ i ∈ s, W i = W' i) (K : ConvexSpaceBody E) :
    densityIn s W K = densityIn s W' K := by
  classical
  unfold densityIn
  have h_filter_eq :
      {i ∈ s | W i ≤ K} = {i ∈ s | W' i ≤ K} :=
    Finset.filter_congr fun i hi => by rw [h i hi]
  rw [h_filter_eq]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i (Finset.mem_filter.mp hi).1]

end Kakeya
