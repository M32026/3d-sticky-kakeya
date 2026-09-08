/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineOuterTubes
public import Kakeya.Tube.CoverCountComparable
public import Kakeya.Tube.EssentiallyDistinctReduction

/-!
# Step 10's count clause: from *one* canonical cover to *every* cover

Blueprint: `blueprint/src/GWZAdapted/section9.tex`, the non-eccentric case, the invocation of
GWZ Lemma 9.1 at `ζ = η_j/2`.

## The gap this file closes, and the one it does not

`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer` carries the count clause of Lemma 9.1 as
the binder `hcnt`, which is `Lemma91At`'s clause verbatim at the
*outer* `σ`-tube family: at every scale of Lemma 9.1's window, *one* essentially distinct all-used
`ρ`-tube family over the outer tubes, of cardinality at least `ρ^{-2-ζ}`.  GWZ's `|𝕋_ρ|` is the
*canonical* parent cover, and the spine produces it on the **rescaled bodies**
`spineFamily (spineRescaleUnit …) 𝕋 i`, not on the outer tubes.  A `ρ`-tube containing a rescaled
body (a short chord, of length `≍ 1/(4R)`) need not contain the unit-length outer tube, so "used"
does not transport for free; what does transport, at a constant, is the *count*:

> **step 10's count clause is discharged by the existence, at each scale of Lemma 9.1's window, of
> *one* essentially distinct all-used `ρ`-tube family over the rescaled bodies whose cardinality is
> at least `Λ ρ^{-2-ζ}`, with `Λ = Kakeya.ML2Reduction.spineOuterCountLoss R` a constant.**

That is GWZ's reading, and
`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_canonicalCover` is step 10 with the
count clause replaced by that datum.  The transport is
`Kakeya.ML2Reduction.outerCanonicalCover_of_canonicalCover`: replace each member `W j` of the
canonical family by the `ρ`-tube `Tube.rescale (outerFamily … i_j) ρ` on the core of the outer tube
of the body `W j` uses (`Tube.rescale_le_rescale_of_radius_le`), pass to a maximal essentially
distinct subfamily (`Kakeya.Tube.exists_maximal_essDistinct`), and bound the fibres: `W j` shares
the chord of its body with `Tube.rescale (outerFamily … i_j) ρ`
(`Tube.subset_dilate_of_common_chord_at`), which overlaps a retained tube heavily
(`Kakeya.Tube.tubeOverlapCoreClose`), so every `W j` of a fibre lies in one fixed dilate of the
retained tube (`Kakeya.Tube.subset_dilate_rescale_of_subset_dilate`) and
`Tube.essDistinctTubesInSelfDilate` counts it.  The loss is
`spineOuterCountLoss R = 1 + C(3, 6·max(32K, C₃)²)` with `K = max 1 (8R/5)` — larger than
`Kakeya.ML2Reduction.spineCoverCountLoss R`, the constant of the earlier same-scale comparison of
covers, because the fibres are counted in a larger dilate; both are constants, and the `ζ`-slack
pays for either.

What this file does **not** do is *build* the canonical cover on the rescaled bodies.  Both of its
clauses are reduced here to things the tree already has:

* **used** — `Kakeya.ML2Reduction.outerTube_used_of_used`: pushing an upstairs `ρup`-tube family
  down through `Kakeya.ML2Reduction.outerTube` keeps every member used, and keeps the index
  `Finset` literally unchanged, so the cardinality is preserved on the nose.
* **essentially distinct** — `Kakeya.ML2Reduction.canonicalCoverAt_of_used_of_maxDensity`:
  essential distinctness does *not* transport (`outerTube` fattens `Ψ(W)` by `≍ 4R` in every
  direction, so upstairs essentially distinct tubes can push down onto outer tubes that coincide),
  but it does not have to — `Kakeya.Tube.refineToEssDistinctLeaves` extracts an essentially
  distinct subfamily from *any* family of `ρ`-tubes, at the cardinality loss
  `Kakeya.Tube.refineToEssDistinctLeaves.C n · Δ_max`, and a subfamily inherits "used" for free.

What is left is therefore (i) the upstairs canonical family itself — GWZ's
`TTSigmaBigCardinalityV1`, i.e. `Kakeya.ML2Spine.spine_tube_card_lower`, at the scale
`ρup = ρ θ` — and (ii) the arithmetic that the two losses
`spineOuterCountLoss R · refineToEssDistinctLeaves.C 3 · Δ_max` fit inside the count budget.
Neither is a comparison of covers, which is what this file removes.  See.

## Why the chord length is `1/(4R)` and not `2/5`

`Tube.CoverCountComparableChord` fixes the chord threshold at `2/5`, which is free for a family of
*tubes* (`Tube.exists_chord_of_shadedTube`: a tube's core has length `1`).  The bodies of the
canonical-cover datum are not tubes — they are the affine images
`spineFamily (spineRescaleUnit …) 𝕋 i` — and the chord the
rescaling supplies is the image of the core, whose length is pinned between `1/(4R)` and `1/4`
(`Kakeya.ML2Reduction.rescaledCore_dist_ge`, `Kakeya.ML2Reduction.rescaledCore_dist_le`).  Since
`Tube.IsRescalingSituation` forces `R ≥ Tube.normalization.C 3 = 64`, that chord is **never** as
long as `2/5`: the `2/5`-threshold form is available in the tree and inapplicable here.  The
comparison therefore has to be run at a general chord length `d`, at the loss
`Tube.coverCountLossAt 3 (max 1 (2/(5d)))` — still a constant, depending only on the dimension and
on `R`.

## Main declarations

* `Kakeya.ML2Reduction.rescaledCore_dist_ge` / `rescaledCore_dist_le` — the image of a tube's core
  under `Ψ = Tube.rescaleMap T₀ R` has length in `[1/(4R), 1/4]`.
* `Kakeya.ML2Reduction.exists_chord_spineFamily` — the chord hypothesis of
  `Kakeya.ML2Reduction.coverCountComparable`, discharged at the step-10 bodies at `d = 1/(4R)`.
* `Kakeya.ML2Reduction.spineCoverCountLoss` — the constant of the same-scale comparison of covers.
* `Kakeya.ML2Reduction.rescaled_count_of_canonicalCover` — the earlier `∀`-over-covers form of the
  count clause, from the canonical-cover datum (kept as a record; no longer on the spine's path).
* `Kakeya.ML2Reduction.dilate_carrier_subset_dilate_of_le`,
  `Kakeya.ML2Reduction.outerTransportRatio`,
  `Kakeya.ML2Reduction.exists_edUsed_rescale_of_edUsed_body` — the body→outer-tube transport of an
  essentially distinct all-used family, at a constant loss.
* `Kakeya.ML2Reduction.spineOuterCountLoss` — the constant `Λ` of that transport at the step-10
  bodies.
* `Kakeya.ML2Reduction.outerCanonicalCover_of_canonicalCover` — `Lemma91At`'s count clause on the
  outer family, from the canonical-cover datum on the rescaled bodies.
* `Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_canonicalCover` — step 10 with `hcnt`
  replaced by that datum.
* `Kakeya.ML2Reduction.nonempty_of_canonicalCover` — the datum is **not** satisfied by the empty
  family, so it is not the `∅`-witness triviality.
* `Kakeya.ML2Reduction.outerTube_used_of_used` — the "used" half of the push-down.
* `Kakeya.ML2Reduction.canonicalCoverAt_of_used_of_maxDensity` — the essential-distinctness half.
* `Kakeya.ML2Reduction.spineCoverCountLoss_eq` — the constant is
  `Tube.count_of_canonicalCover_of_diam`'s at `d = 1/(4R)`.
-/

@[expose] public section

open MeasureTheory Metric Set ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Reduction

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι κ : Type*} {θ τ : NNReal}

/-! ## The chord the rescaling supplies -/

/-- **`Ψ` shortens the core of an inner tube by exactly the homothety factor**: the image of the
core of a `τ`-tube `T ⊆ T₀` has length at least `1/(4R)`.

This is the chord hypothesis of `Kakeya.ML2Reduction.coverCountComparable` at the step-10 bodies.
`Tube.dist_rescaleMap` supplies the homothety half and `Tube.normalization_core_length` the fact
that `Φ` never shortens.  (MainLemma1 carries the same fact as
`Tube.dist_rescaleMap_ge_of_subset`; it is re-proved here in two lines rather than importing a
MainLemma1 module into the MainLemma2 reduction, which Section 8 owns.) -/
theorem rescaledCore_dist_ge (hθ : 0 < θ) (hθ1 : θ ≤ 1) {R : ℝ} (hR : 0 < R)
    (T₀ : Tube θ E) (T : Tube τ E) (hsub : T.carrier ⊆ T₀.carrier) :
    1 / (4 * R) ≤ dist (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y) := by
  rw [Tube.dist_rescaleMap T₀ hR T.x T.y]
  exact div_le_div_of_nonneg_right
    (Tube.normalization_core_length hθ hθ1 T₀ T hsub).1
    (by positivity : (0 : ℝ) < 4 * R).le

/-- **The same chord is at most `1/4` long**, because `Φ` distorts the core by at most
`Tube.normalization.C` and the rescaling situation puts `R` past that same constant.

`1/4 < 2/5`, so the chord threshold of `Tube.CoverCountComparableChord` is **not** met by the
witness the rescaling produces: the `2/5` form of the comparison is inapplicable at step 10's call
site, and the chord length has to be carried as a parameter. -/
theorem rescaledCore_dist_le (hθ : 0 < θ) (hθ1 : θ ≤ 1) {R : ℝ}
    (hR : (Tube.normalization.C (Module.finrank ℝ E) : ℝ) ≤ R)
    (T₀ : Tube θ E) (T : Tube τ E) (hsub : T.carrier ⊆ T₀.carrier) :
    dist (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y) ≤ 1 / 4 := by
  have hC1 : (1 : ℝ) ≤ (Tube.normalization.C (Module.finrank ℝ E) : ℝ) := by
    exact_mod_cast Tube.normalization.one_le_C (Module.finrank ℝ E)
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one (hC1.trans hR)
  rw [Tube.dist_rescaleMap T₀ hR0 T.x T.y]
  rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
  have h := (Tube.normalization_core_length hθ hθ1 T₀ T hsub).2
  nlinarith

/-- `1/4 < 2/5`: the numerical half of `Kakeya.ML2Reduction.rescaledCore_dist_le`'s point. -/
theorem rescaledCore_lt_chordThreshold : (1 : ℝ) / 4 < 2 / 5 := by norm_num

/-- **The nondegeneracy hypothesis of `Kakeya.ML2Reduction.coverCountComparable`, discharged at the
bodies of step 10's count clause**, at chord length `d = 1/(4R)`. -/
theorem exists_chord_spineFamily {R : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hR : 0 < R)
    (T₀ : Tube θ E) (𝕋 : ι → ShadedTube τ E) {s : Finset ι}
    (hsub : ∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier) :
    ∀ i ∈ s, ∃ p ∈ ((spineFamily (spineRescaleUnit hθ T₀ hR) 𝕋 i).toConvexSpaceBody).carrier,
      ∃ q ∈ ((spineFamily (spineRescaleUnit hθ T₀ hR) 𝕋 i).toConvexSpaceBody).carrier,
        1 / (4 * R) ≤ dist p q := by
  intro i hi
  refine ⟨spineRescaleUnit hθ T₀ hR (𝕋 i).x, ⟨(𝕋 i).x, (𝕋 i).toTube.x_mem_carrier, rfl⟩,
          spineRescaleUnit hθ T₀ hR (𝕋 i).y, ⟨(𝕋 i).y, (𝕋 i).toTube.y_mem_carrier, rfl⟩, ?_⟩
  rw [spineRescaleUnit_apply, spineRescaleUnit_apply]
  exact rescaledCore_dist_ge hθ hθ1 hR T₀ (𝕋 i).toTube (hsub i hi)

/-! ## The constant -/

/-- **The comparability loss of step 10's count clause**: `Tube.coverCountLossAt` at the chord
length `1/(4R)` the rescaling delivers, i.e. at `K = max 1 (8R/5)`.  It depends only on the ambient
dimension and on the normalization radius `R` — not on the scale `ρ`, not on the tubes, not on the
family.  At the standing value `R = Tube.normalization.C 3 = 64` it is a closed numeral. -/
noncomputable abbrev spineCoverCountLoss (R : ℝ) : NNReal :=
  Tube.coverCountLossAt 3 (max 1 (8 * R / 5))

theorem one_le_spineCoverCountLoss (R : ℝ) : (1 : ℝ) ≤ (spineCoverCountLoss R : ℝ) :=
  Tube.one_le_coverCountLossAt_real _ _

/-- `2/(5K) ≤ 1/(4R)` at `K = max 1 (8R/5)`: the chord the rescaling gives clears the threshold the
comparison at `K` demands. -/
theorem chordThreshold_le_rescaledChord {R : ℝ} (hR : 0 < R) :
    2 / (5 * max 1 (8 * R / 5)) ≤ 1 / (4 * R) := by
  rcases le_total (8 * R / 5) 1 with h | h
  · rw [max_eq_left h, div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  · rw [max_eq_right h, div_le_div_iff₀ (by positivity) (by positivity)]
    ring_nf
    nlinarith

/-! ## The count clause -/

/-- **Step 10's count clause, verbatim, from one canonical cover.**

`hcanon` is GWZ's `|𝕋̃_ρ[T_b]|`: at each scale of Lemma 9.1's window, *one* essentially distinct
`ρ`-tube family, every member of which contains one of the rescaled bodies, of cardinality at least
`Λ ρ^{-2-ζ}`.  The conclusion is the `hcnt` binder of
`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer` character for character, i.e. the bound for
*every* essentially distinct cover.

The competitor cover's own essential distinctness is **not used** — that hypothesis is inert in
Lemma 9.1's count clause, and is kept only because the clause states it. -/
theorem rescaled_count_of_canonicalCover
    {σ : NNReal} {R ϖ ζ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hR : 0 < R)
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hϖ : 0 ≤ ϖ)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3))) {α : Type u} {s : Finset α}
    (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hsub : ∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier)
    (hcanon : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀) (W : κ₀ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ j ∈ t, ∃ i ∈ s,
          (spineFamily (spineRescaleUnit hθ T₀ hR) 𝕋 i).toConvexSpaceBody
            ≤ (W j).toConvexSpaceBody) ∧
        (spineCoverCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ) ≤ (t.card : ℝ)) :
    ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∀ {κ : Type u} (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, ∃ j ∈ tρ,
          (spineFamily (spineRescaleUnit hθ T₀ hR) 𝕋 i).toConvexSpaceBody
            ≤ (Tρ j).toConvexSpaceBody) →
        (tρ : Set κ).Pairwise
          (fun j k ↦ _root_.IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) →
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ) := by
  intro ρ hρ κ tρ Tρ hcov _hED
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hρ0 : 0 < ρ := lt_of_lt_of_le (NNReal.rpow_pos hσ0) hρ.1
  have hρ1 : ρ ≤ 1 := hρ.2.trans (NNReal.rpow_le_one hσ1 hϖ)
  obtain ⟨κ₀, t, W, hEDW, hused, hlow⟩ := hcanon ρ hρ
  refine Tube.count_of_canonicalCover (E := EuclideanSpace ℝ (Fin 3)) hρ0 hρ1
    (K := max 1 (8 * R / 5)) (le_max_left _ _)
    (fun i => (spineFamily (spineRescaleUnit hθ T₀ hR) 𝕋 i).toConvexSpaceBody) s
    ?_ t W hEDW hused ?_ tρ Tρ hcov
  · intro i hi
    obtain ⟨p, hp, q, hq, hpq⟩ := exists_chord_spineFamily hθ hθ1 hR T₀ 𝕋 hsub i hi
    exact ⟨p, hp, q, hq, (chordThreshold_le_rescaledChord hR).trans hpq⟩
  · rwa [hfr]

/-- **The canonical-cover datum is not the `∅`-witness triviality.**

Every scale of a nonempty window forces the family itself to be nonempty: the datum's cardinality
clause makes the cover nonempty (`Λ ρ^{-2-ζ} > 0`), and its "used" clause then produces a member of
`s`.  So the datum cannot be satisfied by the empty family, which is the check the three
`SpineInheritance` adapters of `STATUS-S9` failed. -/
theorem nonempty_of_canonicalCover
    {σ : NNReal} {R ϖ ζ : ℝ} (hθ : 0 < θ) {hR : 0 < R} (hσ0 : 0 < σ)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3))) {α : Type u} {s : Finset α}
    (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hcanon : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀) (W : κ₀ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ j ∈ t, ∃ i ∈ s,
          (spineFamily (spineRescaleUnit hθ T₀ hR) 𝕋 i).toConvexSpaceBody
            ≤ (W j).toConvexSpaceBody) ∧
        (spineCoverCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ) ≤ (t.card : ℝ))
    {ρ : NNReal} (hρ : ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ)) :
    s.Nonempty := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le (NNReal.rpow_pos hσ0) hρ.1
  obtain ⟨κ₀, t, W, -, hused, hlow⟩ := hcanon ρ hρ
  have hpos : (0 : ℝ) < (spineCoverCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ) := by
    have h1 := one_le_spineCoverCountLoss R
    have h2 : (0 : ℝ) < (ρ : ℝ) ^ (-2 - ζ) := Real.rpow_pos_of_pos (by exact_mod_cast hρ0) _
    nlinarith
  have htcard : 0 < t.card := by
    by_contra hc
    rw [Nat.eq_zero_of_not_pos hc] at hlow
    simp only [Nat.cast_zero] at hlow
    linarith
  obtain ⟨j, hj⟩ := Finset.card_pos.mp htcard
  obtain ⟨i, hi, -⟩ := hused j hj
  exact ⟨i, hi⟩

/-! ## The body→outer-tube transport of the canonical cover -/

/-- **A dilate grows with its ratio.**  Read through `Tube.dilate_carrier_eq_cthickening`: the
`a`-dilate is the `aδ`-neighbourhood of the centred segment of length `a`, and both grow with
`a`. -/
theorem dilate_carrier_subset_dilate_of_le {δ : NNReal} (T : Tube δ E) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (Kakeya.Tube.dilate T a).carrier ⊆ (Kakeya.Tube.dilate T b).carrier := by
  have hb : 0 < b := ha.trans_le hab
  have hb0 : b ≠ 0 := hb.ne'
  rw [_root_.Tube.dilate_carrier_eq_cthickening T ha,
    _root_.Tube.dilate_carrier_eq_cthickening T hb]
  have hδ : a * (δ : ℝ) ≤ b * (δ : ℝ) := mul_le_mul_of_nonneg_right hab δ.coe_nonneg
  have hseg : segment ℝ (T.center - (a / 2) • T.direction) (T.center + (a / 2) • T.direction)
      ⊆ segment ℝ (T.center - (b / 2) • T.direction) (T.center + (b / 2) • T.direction) := by
    refine Convex.segment_subset (convex_segment _ _) ?_ ?_
    · rw [segment_eq_image']
      refine ⟨(b - a) / (2 * b), ⟨div_nonneg (by linarith) (by positivity),
        (div_le_one (by positivity)).mpr (by linarith)⟩, ?_⟩
      match_scalars <;> field_simp <;> ring
    · rw [segment_eq_image']
      refine ⟨(b + a) / (2 * b), ⟨div_nonneg (by linarith) (by positivity),
        (div_le_one (by positivity)).mpr (by linarith)⟩, ?_⟩
      match_scalars <;> field_simp <;> ring
  exact (Metric.cthickening_subset_of_subset _ hseg).trans (Metric.cthickening_mono hδ _)

/-- **The dilation ratio at which the transport's fibres are counted**: `6 c²` for
`c = max (32 K) C_n`, where `32 K` is the chord-comparability ratio of
`Tube.subset_dilate_of_common_chord_at` at chord threshold `2/(5K)`, `C_n` is the
overlap-containment ratio `Kakeya.Tube.tubeOverlapCoreClose.C n`, and the `6 c²` is the ratio
`Kakeya.Tube.subset_dilate_rescale_of_subset_dilate` produces. -/
noncomputable abbrev outerTransportRatio (n : ℕ) (K : ℝ) : ℝ :=
  6 * (max (32 * K) (Kakeya.Tube.tubeOverlapCoreClose.C n)) ^ 2

theorem one_le_outerTransportRatio (n : ℕ) {K : ℝ} (hK : 1 ≤ K) :
    1 ≤ outerTransportRatio n K := by
  have hc1 : (1 : ℝ) ≤ max (32 * K) (Kakeya.Tube.tubeOverlapCoreClose.C n) :=
    le_trans (by linarith) (le_max_left _ _)
  unfold outerTransportRatio
  nlinarith

/-- **Transport of an essentially distinct all-used family from bodies to their outer tubes.**

Bodies `B i` (each carrying a chord of length `≥ 2/(5K)`) sit inside `σ`-tubes `O i`, and `W` is a
pairwise essentially distinct family of `ρ`-tubes (`σ ≤ ρ ≤ 1`) every member of which contains some
`B i`.  Then there is a pairwise essentially distinct family of `ρ`-tubes every member of which
contains some **`O i`** — the tubes `Tube.rescale (O i) ρ` — of cardinality at least
`|W| / C(n, outerTransportRatio n K)`.

Proof: pick for each `j` a body `B (f j) ≤ W j` and set `V j = Tube.rescale (O (f j)) ρ`, so
`O (f j) ≤ V j` (`Tube.rescale_le_rescale_of_radius_le`).  Take a maximal essentially distinct
subfamily `u` of `V` (`Kakeya.Tube.exists_maximal_essDistinct`).  For `j ∈ t` there is `k ∈ u` with
`V k ⊆ c · V j` (itself if `j ∈ u`, else `Kakeya.Tube.tubeOverlapCoreClose` on the heavy overlap),
and `W j ⊆ 32K · V j` by the common chord `B (f j)`; so `c · V j` is a set containing `O (f k)` and
contained in `c · V j`, whence `Kakeya.Tube.subset_dilate_rescale_of_subset_dilate` puts it — and
`W j` — inside `6c² · V k`.  The fibres of `j ↦ k` are essentially distinct `ρ`-tubes in one dilate
of a `ρ`-tube, counted by `Tube.essDistinctTubesInSelfDilate`. -/
theorem exists_edUsed_rescale_of_edUsed_body [Nontrivial E] {ρ σ : NNReal}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hσρ : σ ≤ ρ) {K : ℝ} (hK : 1 ≤ K)
    (B : ι → ConvexSpaceBody E) (O : ι → Tube σ E) (s : Finset ι)
    (hnd : ∀ i ∈ s, ∃ p ∈ (B i).carrier, ∃ q ∈ (B i).carrier, 2 / (5 * K) ≤ dist p q)
    (hBO : ∀ i ∈ s, B i ≤ (O i).toConvexSpaceBody)
    (t : Finset κ) (W : κ → Tube ρ E)
    (hED : (t : Set κ).Pairwise fun j k => IsEssentiallyDistinct (W j).carrier (W k).carrier)
    (hused : ∀ j ∈ t, ∃ i ∈ s, B i ≤ (W j).toConvexSpaceBody) :
    ∃ (u : Finset κ) (V : κ → Tube ρ E),
      ((u : Set κ).Pairwise fun j k => IsEssentiallyDistinct (V j).carrier (V k).carrier) ∧
      (∀ j ∈ u, ∃ i ∈ s, (O i).toConvexSpaceBody ≤ (V j).toConvexSpaceBody) ∧
      (t.card : ℝ) ≤ (Tube.essDistinctTubesInSelfDilate.C (Module.finrank ℝ E)
        (outerTransportRatio (Module.finrank ℝ E) K) : ℝ) * (u.card : ℝ) := by
  classical
  rcases t.eq_empty_or_nonempty with rfl | ⟨j₀, hj₀⟩
  · exact ⟨∅, W, by simp, by simp, by simp⟩
  obtain ⟨i₀, hi₀, -⟩ := hused j₀ hj₀
  haveI : Nonempty ι := ⟨i₀⟩
  choose! f hfs hfle using hused
  set V : κ → Tube ρ E := fun j => (O (f j)).rescale ρ with hV
  have hOV : ∀ j ∈ t, (O (f j)).toConvexSpaceBody ≤ (V j).toConvexSpaceBody := by
    intro j hj
    have h := Tube.rescale_le_rescale_of_radius_le (O (f j)) hσρ
    rwa [Tube.toConvexSpaceBody_rescale_self] at h
  have hBV : ∀ j ∈ t, B (f j) ≤ (V j).toConvexSpaceBody :=
    fun j hj => (hBO _ (hfs j hj)).trans (hOV j hj)
  set Cn : ℝ := Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) with hCn
  set c : ℝ := max (32 * K) Cn with hc
  have hCn1 : 1 ≤ Cn := le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C _)
  have hc1 : 1 ≤ c := le_trans (by linarith) (le_max_left _ _)
  have hD1 : 1 ≤ 6 * c ^ 2 := by nlinarith
  obtain ⟨u, hut, hEDV, hmax⟩ := Kakeya.Tube.exists_maximal_essDistinct t V
  -- every `W j` lies in the `6c²`-dilate of a retained `V k`
  have key : ∀ j ∈ t, ∃ k ∈ u,
      (W j).carrier ⊆ (Kakeya.Tube.dilate (V k) (6 * c ^ 2)).carrier := by
    intro j hj
    obtain ⟨k, hk, hVk⟩ : ∃ k ∈ u, (V k).carrier ⊆ (Kakeya.Tube.dilate (V j) c).carrier := by
      by_cases hju : j ∈ u
      · exact ⟨j, hju, Tube.subset_dilate (V j) hc1⟩
      · obtain ⟨k, hk, hnot⟩ := hmax j hj hju
        refine ⟨k, hk, ?_⟩
        have hhalf : (1 / 2 : ENNReal) * volume (V j).carrier
            < volume ((V j).carrier ∩ (V k).carrier) := by
          have h' : (1 / 2 : ENNReal) * max (volume (V k).carrier) (volume (V j).carrier)
              < volume ((V k).carrier ∩ (V j).carrier) := lt_of_not_ge hnot
          rw [Set.inter_comm] at h'
          calc (1 / 2 : ENNReal) * volume (V j).carrier
              ≤ (1 / 2 : ENNReal) * max (volume (V k).carrier) (volume (V j).carrier) := by
                gcongr; exact le_max_right _ _
            _ < _ := h'
        exact (Kakeya.Tube.tubeOverlapCoreClose hρ0 hρ1 (V j) (V k) hhalf).trans
          (dilate_carrier_subset_dilate_of_le (V j) (by linarith) (le_max_right _ _))
    refine ⟨k, hk, ?_⟩
    have hWj : (W j).carrier ⊆ (Kakeya.Tube.dilate (V j) c).carrier := by
      obtain ⟨p, hp, q, hq, hpq⟩ := hnd (f j) (hfs j hj)
      have h32 := Tube.subset_dilate_of_common_chord_at (by exact_mod_cast hρ1) hK (W j) (V j)
        (hfle j hj hp) (hfle j hj hq) (hBV j hj hp) (hBV j hj hq) hpq
      exact h32.trans (dilate_carrier_subset_dilate_of_le (V j) (by linarith) (le_max_left _ _))
    have hOk : (O (f k)).carrier ⊆ (Kakeya.Tube.dilate (V j) c).carrier :=
      fun x hx => hVk (hOV k (hut hk) hx)
    have hsand := Kakeya.Tube.subset_dilate_rescale_of_subset_dilate (V j) (O (f k))
      (c := c) (Λ := 6 * c ^ 2) hc1 (by nlinarith) le_rfl hOk subset_rfl
    exact hWj.trans hsand
  -- the fibres
  let A : κ → Finset κ := fun k =>
    t.filter (fun j => (W j).carrier ⊆ (Kakeya.Tube.dilate (V k) (6 * c ^ 2)).carrier)
  have hcover : t ⊆ u.biUnion A := by
    intro j hj
    obtain ⟨k, hk, hjk⟩ := key j hj
    exact Finset.mem_biUnion.mpr ⟨k, hk, Finset.mem_filter.mpr ⟨hj, hjk⟩⟩
  set Cb : NNReal :=
    Tube.essDistinctTubesInSelfDilate.C (Module.finrank ℝ E) (6 * c ^ 2) with hCb
  have hfib : ∀ k ∈ u, ((A k).card : ENNReal) ≤ (Cb : ENNReal) := by
    intro k _
    refine Tube.essDistinctTubesInSelfDilate hD1 hρ0 hρ1 (V k) (A k) W ?_ ?_
    · exact hED.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
    · intro j hj
      exact (Finset.mem_filter.mp hj).2
  have hENN : (t.card : ENNReal) ≤ (Cb : ENNReal) * (u.card : ENNReal) := by
    calc (t.card : ENNReal) ≤ ((u.biUnion A).card : ENNReal) := by
          exact_mod_cast Finset.card_le_card hcover
      _ ≤ (∑ k ∈ u, (A k).card : ENNReal) := by
          exact_mod_cast Finset.card_biUnion_le (t := A)
      _ ≤ ∑ _k ∈ u, (Cb : ENNReal) := Finset.sum_le_sum hfib
      _ = (Cb : ENNReal) * (u.card : ENNReal) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hreal : (t.card : ℝ) ≤ (Cb : ℝ) * (u.card : ℝ) := by
    have := (ENNReal.toReal_le_toReal (by simp) (by finiteness)).mpr hENN
    simpa using this
  exact ⟨u, V, hEDV, fun k hk => ⟨f k, hfs k (hut hk), hOV k (hut hk)⟩, hreal⟩

/-- **`exists_edUsed_rescale_of_edUsed_body`, with its witness exposed** (route (α)).  ADDITIVE: the existing theorem above is and is recovered from this one by
`exists_edUsed_rescale_of_edUsed_body_of_data`.

That is enough to *use* the family and not
enough to *say what it is*: a consumer that must then compare `V j` with something built from the
same `O (f j)` — the centred hand-back's `hnode` is exactly such a consumer — receives a tube it
only knows to be a container, and a containment constant would have to be invented to get back. The proof already names the witness (`V := fun j ↦ (O (f j)).rescale ρ`, and `f` from `choose!`), so
exposing `f` costs nothing and makes the downstream discharge a syntactic `exact`.

Same proof as the existing theorem, with `⟨u, V, …⟩` replaced by `⟨u, f, …⟩`. -/
theorem exists_edUsed_rescale_of_edUsed_body_data [Nontrivial E] [Nonempty ι] {ρ σ : NNReal}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hσρ : σ ≤ ρ) {K : ℝ} (hK : 1 ≤ K)
    (B : ι → ConvexSpaceBody E) (O : ι → Tube σ E) (s : Finset ι)
    (hnd : ∀ i ∈ s, ∃ p ∈ (B i).carrier, ∃ q ∈ (B i).carrier, 2 / (5 * K) ≤ dist p q)
    (hBO : ∀ i ∈ s, B i ≤ (O i).toConvexSpaceBody)
    (t : Finset κ) (W : κ → Tube ρ E)
    (hED : (t : Set κ).Pairwise fun j k => IsEssentiallyDistinct (W j).carrier (W k).carrier)
    (hused : ∀ j ∈ t, ∃ i ∈ s, B i ≤ (W j).toConvexSpaceBody) :
    ∃ (u : Finset κ) (f : κ → ι), u ⊆ t ∧ (∀ j ∈ u, f j ∈ s) ∧
      ((u : Set κ).Pairwise fun j k =>
        IsEssentiallyDistinct ((O (f j)).rescale ρ).carrier ((O (f k)).rescale ρ).carrier) ∧
      (t.card : ℝ) ≤ (Tube.essDistinctTubesInSelfDilate.C (Module.finrank ℝ E)
        (outerTransportRatio (Module.finrank ℝ E) K) : ℝ) * (u.card : ℝ) := by
  classical
  rcases t.eq_empty_or_nonempty with rfl | ⟨j₀, hj₀⟩
  · exact ⟨∅, fun _ => Classical.arbitrary ι, by simp, by simp, by simp, by simp⟩
  obtain ⟨i₀, hi₀, -⟩ := hused j₀ hj₀
  haveI : Nonempty ι := ⟨i₀⟩
  choose! f hfs hfle using hused
  set V : κ → Tube ρ E := fun j => (O (f j)).rescale ρ with hV
  have hOV : ∀ j ∈ t, (O (f j)).toConvexSpaceBody ≤ (V j).toConvexSpaceBody := by
    intro j hj
    have h := Tube.rescale_le_rescale_of_radius_le (O (f j)) hσρ
    rwa [Tube.toConvexSpaceBody_rescale_self] at h
  have hBV : ∀ j ∈ t, B (f j) ≤ (V j).toConvexSpaceBody :=
    fun j hj => (hBO _ (hfs j hj)).trans (hOV j hj)
  set Cn : ℝ := Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) with hCn
  set c : ℝ := max (32 * K) Cn with hc
  have hCn1 : 1 ≤ Cn := le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C _)
  have hc1 : 1 ≤ c := le_trans (by linarith) (le_max_left _ _)
  have hD1 : 1 ≤ 6 * c ^ 2 := by nlinarith
  obtain ⟨u, hut, hEDV, hmax⟩ := Kakeya.Tube.exists_maximal_essDistinct t V
  -- every `W j` lies in the `6c²`-dilate of a retained `V k`
  have key : ∀ j ∈ t, ∃ k ∈ u,
      (W j).carrier ⊆ (Kakeya.Tube.dilate (V k) (6 * c ^ 2)).carrier := by
    intro j hj
    obtain ⟨k, hk, hVk⟩ : ∃ k ∈ u, (V k).carrier ⊆ (Kakeya.Tube.dilate (V j) c).carrier := by
      by_cases hju : j ∈ u
      · exact ⟨j, hju, Tube.subset_dilate (V j) hc1⟩
      · obtain ⟨k, hk, hnot⟩ := hmax j hj hju
        refine ⟨k, hk, ?_⟩
        have hhalf : (1 / 2 : ENNReal) * volume (V j).carrier
            < volume ((V j).carrier ∩ (V k).carrier) := by
          have h' : (1 / 2 : ENNReal) * max (volume (V k).carrier) (volume (V j).carrier)
              < volume ((V k).carrier ∩ (V j).carrier) := lt_of_not_ge hnot
          rw [Set.inter_comm] at h'
          calc (1 / 2 : ENNReal) * volume (V j).carrier
              ≤ (1 / 2 : ENNReal) * max (volume (V k).carrier) (volume (V j).carrier) := by
                gcongr; exact le_max_right _ _
            _ < _ := h'
        exact (Kakeya.Tube.tubeOverlapCoreClose hρ0 hρ1 (V j) (V k) hhalf).trans
          (dilate_carrier_subset_dilate_of_le (V j) (by linarith) (le_max_right _ _))
    refine ⟨k, hk, ?_⟩
    have hWj : (W j).carrier ⊆ (Kakeya.Tube.dilate (V j) c).carrier := by
      obtain ⟨p, hp, q, hq, hpq⟩ := hnd (f j) (hfs j hj)
      have h32 := Tube.subset_dilate_of_common_chord_at (by exact_mod_cast hρ1) hK (W j) (V j)
        (hfle j hj hp) (hfle j hj hq) (hBV j hj hp) (hBV j hj hq) hpq
      exact h32.trans (dilate_carrier_subset_dilate_of_le (V j) (by linarith) (le_max_left _ _))
    have hOk : (O (f k)).carrier ⊆ (Kakeya.Tube.dilate (V j) c).carrier :=
      fun x hx => hVk (hOV k (hut hk) hx)
    have hsand := Kakeya.Tube.subset_dilate_rescale_of_subset_dilate (V j) (O (f k))
      (c := c) (Λ := 6 * c ^ 2) hc1 (by nlinarith) le_rfl hOk subset_rfl
    exact hWj.trans hsand
  -- the fibres
  let A : κ → Finset κ := fun k =>
    t.filter (fun j => (W j).carrier ⊆ (Kakeya.Tube.dilate (V k) (6 * c ^ 2)).carrier)
  have hcover : t ⊆ u.biUnion A := by
    intro j hj
    obtain ⟨k, hk, hjk⟩ := key j hj
    exact Finset.mem_biUnion.mpr ⟨k, hk, Finset.mem_filter.mpr ⟨hj, hjk⟩⟩
  set Cb : NNReal :=
    Tube.essDistinctTubesInSelfDilate.C (Module.finrank ℝ E) (6 * c ^ 2) with hCb
  have hfib : ∀ k ∈ u, ((A k).card : ENNReal) ≤ (Cb : ENNReal) := by
    intro k _
    refine Tube.essDistinctTubesInSelfDilate hD1 hρ0 hρ1 (V k) (A k) W ?_ ?_
    · exact hED.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
    · intro j hj
      exact (Finset.mem_filter.mp hj).2
  have hENN : (t.card : ENNReal) ≤ (Cb : ENNReal) * (u.card : ENNReal) := by
    calc (t.card : ENNReal) ≤ ((u.biUnion A).card : ENNReal) := by
          exact_mod_cast Finset.card_le_card hcover
      _ ≤ (∑ k ∈ u, (A k).card : ENNReal) := by
          exact_mod_cast Finset.card_biUnion_le (t := A)
      _ ≤ ∑ _k ∈ u, (Cb : ENNReal) := Finset.sum_le_sum hfib
      _ = (Cb : ENNReal) * (u.card : ENNReal) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hreal : (t.card : ℝ) ≤ (Cb : ℝ) * (u.card : ℝ) := by
    have := (ENNReal.toReal_le_toReal (by simp) (by finiteness)).mpr hENN
    simpa using this
  exact ⟨u, f, hut, fun k hk => hfs k (hut hk), hEDV, hreal⟩

/-- **The projection tie** (pattern): the existing
`Kakeya.ML2Reduction.exists_edUsed_rescale_of_edUsed_body` is the `_data` sibling with its witness
forgotten, so the two cannot drift. -/
theorem exists_edUsed_rescale_of_edUsed_body_of_data [Nontrivial E] {ρ σ : NNReal}
    (hσρ : σ ≤ ρ) (O : ι → Tube σ E) (s : Finset ι) {t u : Finset κ} {f : κ → ι}
    (hfs : ∀ j ∈ u, f j ∈ s)
    (hED : (u : Set κ).Pairwise fun j k =>
      IsEssentiallyDistinct ((O (f j)).rescale ρ).carrier ((O (f k)).rescale ρ).carrier)
    {c : ℝ} (hcard : (t.card : ℝ) ≤ c * (u.card : ℝ)) :
    ∃ (u' : Finset κ) (V : κ → Tube ρ E),
      ((u' : Set κ).Pairwise fun j k => IsEssentiallyDistinct (V j).carrier (V k).carrier) ∧
      (∀ j ∈ u', ∃ i ∈ s, (O i).toConvexSpaceBody ≤ (V j).toConvexSpaceBody) ∧
      (t.card : ℝ) ≤ c * (u'.card : ℝ) := by
  refine ⟨u, fun j => (O (f j)).rescale ρ, hED, fun j hj => ⟨f j, hfs j hj, ?_⟩, hcard⟩
  have h := Tube.rescale_le_rescale_of_radius_le (O (f j)) hσρ
  rwa [Tube.toConvexSpaceBody_rescale_self] at h

/-- **The loss of the body→outer-tube transport at the step-10 bodies**: the packing constant of
`Tube.essDistinctTubesInSelfDilate` at the ratio `outerTransportRatio 3 K`, `K = max 1 (8R/5)`
being the chord parameter the rescaling delivers (`Kakeya.ML2Reduction.spineCoverCountLoss`),
padded by `1` so that `1 ≤ Λ` is free.  It depends only on the ambient dimension and on `R`. -/
noncomputable abbrev spineOuterCountLoss (R : ℝ) : NNReal :=
  1 + Tube.essDistinctTubesInSelfDilate.C 3 (outerTransportRatio 3 (max 1 (8 * R / 5)))

theorem one_le_spineOuterCountLoss (R : ℝ) : (1 : ℝ) ≤ (spineOuterCountLoss R : ℝ) := by
  have h : (1 : NNReal) ≤ spineOuterCountLoss R := le_self_add
  exact_mod_cast h

/-- **`Lemma91At`'s count clause on the outer family, from the canonical cover on the rescaled
bodies.**  This is the `hcnt` binder of `Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer`
character for character, produced from `hcanon` — at each scale of the window, one essentially
distinct `ρ`-tube family every member of which contains a rescaled body, of cardinality at least
`spineOuterCountLoss R · ρ^{-2-ζ}` — by `Kakeya.ML2Reduction.exists_edUsed_rescale_of_edUsed_body`
at the chord `1/(4R)` of `Kakeya.ML2Reduction.exists_chord_spineFamily`. -/
theorem outerCanonicalCover_of_canonicalCover
    {σ : NNReal} {R ϖ ζ : ℝ} (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (hτσ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ)) (hσ0 : 0 < σ) (hϖ : 0 ≤ ϖ)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3))) {α : Type u} {s : Finset α}
    (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hsub : ∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier)
    (hcanon : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀) (W : κ₀ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ j ∈ t, ∃ i ∈ s,
          (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).toConvexSpaceBody
            ≤ (W j).toConvexSpaceBody) ∧
        (spineOuterCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ) ≤ (t.card : ℝ)) :
    ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (tρ : Set κ).Pairwise
          (fun j k ↦ _root_.IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
        (∀ j ∈ tρ, ∃ i ∈ s,
          (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toConvexSpaceBody
            ≤ (Tρ j).toConvexSpaceBody) ∧
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ) := by
  intro ρ hρ
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hσ1 : σ ≤ 1 := by
    have := hsit.out_le_quarter
    rw [← NNReal.coe_le_coe]
    push_cast
    linarith
  have hρ0 : 0 < ρ := lt_of_lt_of_le (NNReal.rpow_pos hσ0) hρ.1
  have hρ1 : ρ ≤ 1 := hρ.2.trans (NNReal.rpow_le_one hσ1 hϖ)
  have hσρ : σ ≤ ρ := by
    calc σ = σ ^ (1 : ℝ) := (NNReal.rpow_one σ).symm
      _ ≤ σ ^ (1 - ϖ) := NNReal.rpow_le_rpow_of_exponent_ge hσ0 hσ1 (by linarith)
      _ ≤ ρ := hρ.1
  obtain ⟨κ₀, t, W, hEDW, hused, hlow⟩ := hcanon ρ hρ
  have hK : (1 : ℝ) ≤ max 1 (8 * R / 5) := le_max_left _ _
  obtain ⟨u, V, hEDV, husedV, hcard⟩ := exists_edUsed_rescale_of_edUsed_body hρ0 hρ1 hσρ hK
    (fun i => (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).toConvexSpaceBody)
    (fun i => (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toTube) s
    (fun i hi => by
      obtain ⟨p, hp, q, hq, hpq⟩ :=
        exists_chord_spineFamily hsit.pos_ambient hsit.ambient_le_one hR T₀ 𝕋 hsub i hi
      exact ⟨p, hp, q, hq, (chordThreshold_le_rescaledChord hR).trans hpq⟩)
    (fun i hi => spineImage_le_outerShadedTube hfr hsit hR hτσ T₀ (𝕋 i) (hsub i hi))
    t W hEDW hused
  refine ⟨κ₀, u, V, hEDV, husedV, ?_⟩
  rw [hfr] at hcard
  have hC_le : (Tube.essDistinctTubesInSelfDilate.C 3
      (outerTransportRatio 3 (max 1 (8 * R / 5))) : ℝ) ≤ (spineOuterCountLoss R : ℝ) := by
    have h : Tube.essDistinctTubesInSelfDilate.C 3 (outerTransportRatio 3 (max 1 (8 * R / 5)))
        ≤ spineOuterCountLoss R := le_add_self
    exact_mod_cast h
  have hΛpos : (0 : ℝ) < (spineOuterCountLoss R : ℝ) :=
    lt_of_lt_of_le zero_lt_one (one_le_spineOuterCountLoss R)
  have hstep : (spineOuterCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ)
      ≤ (spineOuterCountLoss R : ℝ) * (u.card : ℝ) :=
    hlow.trans (hcard.trans (mul_le_mul_of_nonneg_right hC_le (Nat.cast_nonneg _)))
  exact le_of_mul_le_mul_left hstep hΛpos

/-! ## Step 10, with the count clause discharged -/

/-- **STEP 10, with the count clause replaced by GWZ's canonical-cover reading.**

Identical to `Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer` except that the `hcnt` binder
— an essentially distinct all-used `ρ`-tube family over the *outer* tubes — is replaced by
`hcanon`, the existence of one such family over the **rescaled bodies** of cardinality at least
`Λ ρ^{-2-ζ}`, `Λ = Kakeya.ML2Reduction.spineOuterCountLoss R`; the transport is
`Kakeya.ML2Reduction.outerCanonicalCover_of_canonicalCover`.  The extra numeric hypothesis `hϖ` is
free in the spine. -/
theorem multiplicity_le_of_lemma91At_outer_of_canonicalCover
    {β ϖ ζ ν ηd cst : ℝ} {σ : NNReal} {R : ℝ}
    (hL : Lemma91At.{u} β ϖ ζ ν ηd σ)
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*` (refined l.2831–2834).  Symbol-indexed
    --: the same text in this statement's own `ζ`, `ϖ`, `ηd`.
    -- The criterion's derivation needs the scale `< 1` (monotonicity of `s^{-x}` in `x`).
    -- MEASURED: available here, and strictly stronger — `hsit.out_le_quarter` gives
    -- `(σ : ℝ) ≤ 1/4` (`Kakeya/Tube/Rescale.lean:2627`), and this statement carries `hsit`.
    -- So `σ ≤ 1` is a citation, not an added binder.
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ)) (hσ0 : 0 < σ) (hϖ : 0 ≤ ϖ)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3))) {α : Type u} (s : Finset α)
    (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hsub : ∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier)
    (hloss : outerLoss R ≤ σ ^ (-cst))
    (hmax : Kakeya.maxDensity s (fun i ↦ (𝕋 i).toConvexSpaceBody)
      ≤ (σ : ENNReal) ^ (-(ηd - cst)))
    (hfull : σ ^ (ηd - cst) ≤ ShadedBody.fullness s (fun i ↦ (𝕋 i).toShadedBody))
    (hcen : ∀ i ∈ s, (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toTube.IsCentred)
    (huni : ∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (σ : ENNReal) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s
      (outerFamily hsit.pos_ambient T₀ hR σ 𝕋) (Tube.ssfGridLen σ) C))
    (hcanon : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀) (W : κ₀ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ j ∈ t, ∃ i ∈ s,
          (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).toConvexSpaceBody
            ≤ (W j).toConvexSpaceBody) ∧
        (spineOuterCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ) ≤ (t.card : ℝ)) :
    ShadedBody.multiplicity s (fun i ↦ (𝕋 i).toShadedBody)
      ≤ (σ : ENNReal) ^ ν * (s.card : ENNReal) ^ β :=
  multiplicity_le_of_lemma91At_outer hL hζ hsit hR hR1 hτσ hσ0 T₀ s 𝕋 hsub hloss hmax hfull hcen
    huni (outerCanonicalCover_of_canonicalCover hsit hR hτσ hσ0 hϖ T₀ 𝕋 hsub hcanon)

/-! ## The essential-distinctness half of the canonical-cover datum -/

/-- **`spineCoverCountLoss` is `Tube.count_of_canonicalCover_of_diam`'s constant at the chord length
the rescaling delivers**, `d = 1/(4R)`.  Recorded so that the constant used here is visibly the one
`Kakeya/Tube/CoverCountComparable.lean` already anticipated for the rescaled bodies. -/
theorem spineCoverCountLoss_eq {R : ℝ} (hR : 0 < R) :
    spineCoverCountLoss R = Tube.coverCountLossAt 3 (max 1 (2 / (5 * (1 / (4 * R))))) := by
  have : 2 / (5 * (1 / (4 * R))) = 8 * R / 5 := by field_simp; ring
  rw [spineCoverCountLoss, this]

/-- **The essential-distinctness clause of the canonical-cover datum, produced.**

`Kakeya.Tube.refineToEssDistinctLeaves` turns *any* finite family of `ρ`-tubes into a pairwise
essentially distinct subfamily at the cardinality loss `C_n · Δ_max`.  A subfamily inherits the
"used" clause verbatim, so the datum of
`Kakeya.ML2Reduction.rescaled_count_of_canonicalCover` needs no essential distinctness of its own:
what it needs is an all-used family together with a bound `Ced` on `C_n · Δ_max` and the
correspondingly inflated cardinality bound `Ced · c ≤ |t|`.

This is the second of the two halves of the push-down; the first is
`Kakeya.ML2Reduction.outerTube_used_of_used` below. -/
theorem canonicalCoverAt_of_used_of_maxDensity
    {R : ℝ} (hθ : 0 < θ) (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3))) {hR : 0 < R}
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {κ₀ : Type u} (t : Finset κ₀) (W : κ₀ → Tube ρ (EuclideanSpace ℝ (Fin 3)))
    {D : ENNReal} {Ced : NNReal} (hCed : 0 < Ced)
    (hD : Kakeya.maxDensity t (fun j => (W j).toConvexSpaceBody) ≤ D)
    (hedloss : Kakeya.Tube.refineToEssDistinctLeaves.C 3 * D ≤ (Ced : ENNReal))
    (hused : ∀ j ∈ t, ∃ i ∈ s,
      (spineFamily (spineRescaleUnit hθ T₀ hR) 𝕋 i).toConvexSpaceBody ≤ (W j).toConvexSpaceBody)
    {c : ℝ} (hlow : (Ced : ℝ) * c ≤ (t.card : ℝ)) :
    ∃ (κ₁ : Type u) (u : Finset κ₁) (V : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
      ((u : Set κ₁).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (V j).carrier (V k).carrier) ∧
      (∀ j ∈ u, ∃ i ∈ s,
        (spineFamily (spineRescaleUnit hθ T₀ hR) 𝕋 i).toConvexSpaceBody
          ≤ (V j).toConvexSpaceBody) ∧
      c ≤ (u.card : ℝ) := by
  classical
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  obtain ⟨u, hut, hED, hcard⟩ := Kakeya.Tube.refineToEssDistinctLeaves hρ0 hρ1 t W hD
  refine ⟨κ₀, u, W, hED, fun j hj => hused j (hut hj), ?_⟩
  rw [hfr] at hcard
  have hstep : (t.card : ENNReal) ≤ (Ced : ENNReal) * (u.card : ENNReal) :=
    hcard.trans (mul_le_mul_right' hedloss _)
  have hreal : (t.card : ℝ) ≤ (Ced : ℝ) * (u.card : ℝ) := by
    have := (ENNReal.toReal_le_toReal (by simp) (by finiteness)).mpr hstep
    simpa using this
  have hCedR : (0 : ℝ) < (Ced : ℝ) := by exact_mod_cast hCed
  nlinarith [hlow, hreal]

/-! ## What is still owed: the push-down of the canonical cover -/

/-- **The "used" half of the push-down.**  If every member of an upstairs `ρup`-tube family `W`
contains one of the tubes `𝕋 i`, then every one of the downstairs outer tubes contains the
corresponding rescaled body — so "all members used" transports across the rescaling for free, and
so does the cardinality (`Kakeya.ML2Reduction.exists_outerCover` re-indexes by the *same* `Finset`).

Essential distinctness does **not** transport, and that is the whole residue: `outerTube` fattens
`Ψ(W k)` by `≍ 4R` in every direction (`Kakeya.ML2Reduction.outerTube_spec` prices the fattening at
`(4R)^6` in volume), so upstairs essentially distinct tubes can push down onto outer tubes that
coincide. -/
theorem outerTube_used_of_used [Nontrivial E] {ρup ρ : NNReal} {R : ℝ}
    (hn : Module.finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ ρup ρ R 3) (hR : 0 < R)
    (hρσ : (ρup : ℝ) / (θ : ℝ) ≤ 4 * (ρ : ℝ))
    (T₀ : Tube θ E) {s : Finset ι} (𝕋 : ι → ShadedTube τ E)
    {t : Finset κ} (W : κ → Tube ρup E)
    (hsubW : ∀ k ∈ t, (W k).carrier ⊆ T₀.carrier)
    (hused : ∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier) :
    ∀ k ∈ t, ∃ i ∈ s,
      (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).toConvexSpaceBody
        ≤ (outerTube hsit.pos_ambient T₀ hR ρ (W k)).toConvexSpaceBody := by
  intro k hk
  obtain ⟨i, hi, hle⟩ := hused k hk
  refine ⟨i, hi, ?_⟩
  exact (Set.image_mono hle).trans
    (outerTube_spec hn hsit hR hρσ T₀ (W k) (hsubW k hk)).1

end Kakeya.ML2Reduction

end
