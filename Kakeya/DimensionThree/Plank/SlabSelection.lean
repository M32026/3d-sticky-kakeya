/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.AssignedSlabFamily
public import Kakeya.Mathlib.MeasureTheory.BoundedOverlap
public import Kakeya.DimensionThree.Plank.SlabwiseInputs

/-!
# Dominant slab regions: a joint slab/point refinement

Pruning the active family to a set of *good* slabs is unavoidable for Item 2 of GWZ Lemma 6.13,
because `ShadedBody.fullness` is an aggregate ratio and a slab whose assigned family carries almost
no mass cannot meet any fixed threshold.  But a class-wise deletion cannot carry either of the two
*two-sided* predicates the public statement needs: the only transports of
`Kakeya.IsTypicalPlankAngle` and of `ShadedBody.HasCConstantMultiplicity` across a deletion
(`Plank.isTypicalPlankAngle_of_fibreRetention`,
`Plank.hasCConstantMultiplicity_of_fibreRetention_real`) consume a *pointwise* fibre-retention
hypothesis, and a class-uniform pointwise retention cannot be extracted from an aggregate hypothesis
at all — the class realising the bound depends on the point.

This file resolves that by refining slabs and points *together*.  Each plank's shade is cut down to
the region where its own slab class is **dominant**, meaning that class already accounts for a
`Nov⁻¹`-fraction of the pointwise multiplicity:

`G_S = {x | #𝒫_{s'}(x) ≤ Nov · #𝒫_{𝒜_S}(x)}`,   `Ydom i = (Y' i) ⌞ G_{slabOf (repr i)}`.

Both conclusions then come out at the *same absolute* rate `Nov⁻¹`, with no power of `a`:

* pointwise retention (`Plank.dominantSlabShading_fibre_retention`) — every point of the retained
  union lies in the dominant region of its own class, which *exhibits* the retaining class rather
  than merely asserting one exists;
* aggregate mass retention (`Plank.dominantSlabShading_mass_retention`) — by integrating the
  defining inequality of `G_S` against
  `MeasureTheory.sum_measure_inter_eq_setLIntegral_card_filter`, with no multiplicity sup bound.

`Plank.exists_dominantGoodSlabRefinement` then bolts the good-slab prune onto the dominant
restriction in one step, at the combined absolute rate `(2 · Nov)⁻¹`.

`Nov` is an absolute pointwise slab-overlap constant, fixed before every geometric datum; nothing in
this file may depend on `a`, `b`, `θ`, `s'` or `Y'`.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {ι τ σ : Type*}

/-! ## The dominant region of a slab -/

/-- The **dominant region** of the slab index `S`: the points at which the assigned family of `S`
already accounts for a `Nov⁻¹`-fraction of the pointwise shading multiplicity. -/
def dominantSlabRegion (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (Nov : ℕ) (S : σ) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | ((Kakeya.shadeFibre s' Y' x).card : ENNReal)
        ≤ (Nov : ENNReal) *
            ((Kakeya.shadeFibre (assignedSlabFamily s' repr slabOf S) Y' x).card : ENNReal)}

/-- Each dominant region is measurable: both sides of its defining inequality are finite sums of
indicators of the measurable shades. -/
theorem measurableSet_dominantSlabRegion (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (Nov : ℕ) (S : σ) :
    MeasurableSet (dominantSlabRegion s' Y' repr slabOf Nov S) :=
  measurableSet_le (measurable_card_filter_mem s' fun i _ => (Y' i).measurableSet_shade)
    (measurable_const.mul
      (measurable_card_filter_mem _ fun i _ => (Y' i).measurableSet_shade))

/-- The **dominant shading**: each plank's shade cut down to the dominant region of its own assigned
slab.  The convex body is untouched, so this is a `ShadedBody.IsRefinement` on the nose. -/
def dominantSlabShading (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (Nov : ℕ) (i : ι) :
    ShadedBody (EuclideanSpace ℝ (Fin 3)) :=
  ShadedBody.restrictShade (Y' i) (dominantSlabRegion s' Y' repr slabOf Nov (slabOf (repr i)))
    (measurableSet_dominantSlabRegion s' Y' repr slabOf Nov (slabOf (repr i)))

/-! ## Carrier and shade identities -/

@[simp] theorem dominantSlabShading_toConvexSpaceBody (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (Nov : ℕ) (i : ι) :
    (dominantSlabShading s' Y' repr slabOf Nov i).toConvexSpaceBody
      = (Y' i).toConvexSpaceBody := by
  rfl

@[simp] theorem dominantSlabShading_shade (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (Nov : ℕ) (i : ι) :
    (dominantSlabShading s' Y' repr slabOf Nov i).shade
      = (Y' i).shade ∩ dominantSlabRegion s' Y' repr slabOf Nov (slabOf (repr i)) := by
  rfl

theorem dominantSlabShading_shade_subset (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (Nov : ℕ) (i : ι) :
    (dominantSlabShading s' Y' repr slabOf Nov i).shade ⊆ (Y' i).shade :=
  Set.inter_subset_left

/-! ## The assigned fibre is unchanged at a dominant point -/

/-- At a point of the dominant region of `S`, cutting to that region does not remove anything from
the `𝒜_S`-fibre: every `i ∈ 𝒜_S` is cut against exactly the `S`-region.  This is the analogue of
`Plank.shadeFibre_restrictShade` for the class-dependent restriction. -/
theorem shadeFibre_assignedSlabFamily_dominantSlabShading (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (Nov : ℕ) (S : σ)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ dominantSlabRegion s' Y' repr slabOf Nov S) :
    Kakeya.shadeFibre (assignedSlabFamily s' repr slabOf S)
        (dominantSlabShading s' Y' repr slabOf Nov) x
      = Kakeya.shadeFibre (assignedSlabFamily s' repr slabOf S) Y' x := by
  ext i
  simp only [Kakeya.mem_shadeFibre, dominantSlabShading_shade, Set.mem_inter_iff]
  refine and_congr_right fun hi => ?_
  rw [(mem_assignedSlabFamily.mp hi).2]
  exact and_iff_left hx

/-! ## Pointwise fibre retention at the absolute rate `Nov⁻¹` -/

/-- **Pointwise fibre retention.**  Every point of the retained union lies in the dominant region of
its own class, so that class *exhibits* the retention; no maximisation over classes and no covering
lemma is needed.

This is the `hkeep` / `hret` clause consumed by `Plank.isTypicalPlankAngle_of_fibreRetention` and by
`Plank.hasCConstantMultiplicity_of_fibreRetention_real`, and the rate is the absolute `Nov⁻¹`. -/
theorem dominantSlabShading_fibre_retention (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) {Nov : ℕ} (hNov : 1 ≤ Nov)
    {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ ⋃ i ∈ s', (dominantSlabShading s' Y' repr slabOf Nov i).shade) :
    ((Nov : ℝ))⁻¹ * ((Kakeya.shadeFibre s' Y' x).card : ℝ)
      ≤ ((Kakeya.shadeFibre s' (dominantSlabShading s' Y' repr slabOf Nov) x).card : ℝ) := by
  obtain ⟨i₀, -, hxi₀⟩ := Set.mem_iUnion₂.mp hx
  set S₀ := slabOf (repr i₀)
  have hxS₀ : x ∈ dominantSlabRegion s' Y' repr slabOf Nov S₀ := hxi₀.2
  have hdom : ((Kakeya.shadeFibre s' Y' x).card : ENNReal)
      ≤ Nov * ((Kakeya.shadeFibre (assignedSlabFamily s' repr slabOf S₀) Y' x).card : ENNReal) :=
    hxS₀
  have hnat : (Kakeya.shadeFibre s' Y' x).card
      ≤ Nov * (Kakeya.shadeFibre (assignedSlabFamily s' repr slabOf S₀) Y' x).card := by
    exact_mod_cast hdom
  have hsub : (Kakeya.shadeFibre (assignedSlabFamily s' repr slabOf S₀) Y' x).card
      ≤ (Kakeya.shadeFibre s' (dominantSlabShading s' Y' repr slabOf Nov) x).card := by
    rw [← shadeFibre_assignedSlabFamily_dominantSlabShading s' Y' repr slabOf Nov S₀ hxS₀]
    exact Finset.card_le_card
      (Finset.filter_subset_filter _ (assignedSlabFamily_subset s' repr slabOf S₀))
  have hNovpos : (0 : ℝ) < (Nov : ℝ) := by exact_mod_cast hNov
  rw [inv_mul_le_iff₀ hNovpos]
  exact_mod_cast hnat.trans (Nat.mul_le_mul_left Nov hsub)

/-! ## Aggregate mass retention at the absolute rate `Nov⁻¹` -/

open scoped Classical in
/-- The assigned-family fibre is the class-`S` part of the whole fibre. -/
theorem shadeFibre_assignedSlabFamily_eq_filter (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (S : σ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    Kakeya.shadeFibre (assignedSlabFamily s' repr slabOf S) Y' x
      = (Kakeya.shadeFibre s' Y' x).filter (fun i => slabOf (repr i) = S) := by
  ext i
  simp only [Kakeya.mem_shadeFibre, Plank.mem_assignedSlabFamily, Finset.mem_filter,
    and_assoc, and_comm]

open scoped Classical in
/-- The classes partition the fibre, so the fibre cardinality is the sum of the class
cardinalities. -/
theorem card_shadeFibre_eq_sum_assignedSlabFamily (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (𝒮 : Finset σ)
    (h𝒮 : ∀ i ∈ s', slabOf (repr i) ∈ 𝒮) (x : EuclideanSpace ℝ (Fin 3)) :
    (Kakeya.shadeFibre s' Y' x).card
      = ∑ S ∈ 𝒮, (Kakeya.shadeFibre (assignedSlabFamily s' repr slabOf S) Y' x).card := by
  simp only [shadeFibre_assignedSlabFamily_eq_filter]
  exact Finset.card_eq_sum_card_fiberwise fun i hi =>
    h𝒮 i ((Kakeya.mem_shadeFibre s' Y' x i).mp hi).1

open scoped Classical in
/-- **Every shaded point has a dominant class.**  The classes partition the fibre and, by the
pointwise overlap bound, at most `Nov` of them are active at `x`; so the largest class already holds
a `Nov⁻¹`-fraction of the fibre, which is exactly membership in its dominant region. -/
theorem exists_mem_dominantSlabRegion (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (𝒮 : Finset σ)
    (h𝒮 : ∀ i ∈ s', slabOf (repr i) ∈ 𝒮) {Nov : ℕ}
    (hov : ∀ x : EuclideanSpace ℝ (Fin 3),
      (𝒮.filter fun S =>
        x ∈ ⋃ i ∈ assignedSlabFamily s' repr slabOf S, (Y' i).shade).card ≤ Nov)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : (Kakeya.shadeFibre s' Y' x).Nonempty) :
    ∃ S ∈ 𝒮, x ∈ dominantSlabRegion s' Y' repr slabOf Nov S := by
  obtain ⟨i₀, hi₀⟩ := hx
  obtain ⟨hi₀s, hxi₀⟩ := (Kakeya.mem_shadeFibre s' Y' x i₀).mp hi₀
  set F : σ → ℕ := fun S => (Kakeya.shadeFibre (assignedSlabFamily s' repr slabOf S) Y' x).card
  set 𝒢 : Finset σ := 𝒮.filter (fun S => F S ≠ 0) with h𝒢
  have hi₀𝒢 : slabOf (repr i₀) ∈ 𝒢 :=
    Finset.mem_filter.mpr ⟨h𝒮 i₀ hi₀s, Finset.card_ne_zero_of_mem
      ((Kakeya.mem_shadeFibre _ Y' x i₀).mpr ⟨mem_assignedSlabFamily_self hi₀s, hxi₀⟩)⟩
  have hsub : 𝒢 ⊆ 𝒮.filter
      (fun S => x ∈ ⋃ i ∈ assignedSlabFamily s' repr slabOf S, (Y' i).shade) := by
    intro S hS
    obtain ⟨hS𝒮, hne⟩ := Finset.mem_filter.mp hS
    obtain ⟨i, hi⟩ := Finset.card_ne_zero.mp hne
    obtain ⟨hiA, hxi⟩ := (Kakeya.mem_shadeFibre _ Y' x i).mp hi
    exact Finset.mem_filter.mpr ⟨hS𝒮, Set.mem_iUnion₂.mpr ⟨i, hiA, hxi⟩⟩
  have h𝒢_card_le : 𝒢.card ≤ Nov := (Finset.card_le_card hsub).trans (hov x)
  obtain ⟨S₀, hS₀𝒢, hS₀max⟩ := Finset.exists_max_image 𝒢 F ⟨_, hi₀𝒢⟩
  refine ⟨S₀, (Finset.mem_filter.mp hS₀𝒢).1, ?_⟩
  have hle : (Kakeya.shadeFibre s' Y' x).card ≤ Nov * F S₀ := by
    calc (Kakeya.shadeFibre s' Y' x).card
        = ∑ S ∈ 𝒮, F S := card_shadeFibre_eq_sum_assignedSlabFamily s' Y' repr slabOf 𝒮 h𝒮 x
      _ = ∑ S ∈ 𝒢, F S := by rw [h𝒢, Finset.sum_filter_ne_zero]
      _ ≤ 𝒢.card * F S₀ := by
          simpa only [smul_eq_mul] using Finset.sum_le_card_nsmul 𝒢 F (F S₀) hS₀max
      _ ≤ Nov * F S₀ := Nat.mul_le_mul_right _ h𝒢_card_le
  change ((Kakeya.shadeFibre s' Y' x).card : ENNReal) ≤ _
  exact_mod_cast hle

open scoped Classical in
/-- The pointwise form of the mass retention, before integration. -/
theorem card_shadeFibre_le_sum_indicator_dominant (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (𝒮 : Finset σ)
    (h𝒮 : ∀ i ∈ s', slabOf (repr i) ∈ 𝒮) {Nov : ℕ} (hNov : 1 ≤ Nov)
    (hov : ∀ x : EuclideanSpace ℝ (Fin 3),
      (𝒮.filter fun S =>
        x ∈ ⋃ i ∈ assignedSlabFamily s' repr slabOf S, (Y' i).shade).card ≤ Nov)
    (x : EuclideanSpace ℝ (Fin 3)) :
    ((Nov : ENNReal))⁻¹ * ((Kakeya.shadeFibre s' Y' x).card : ENNReal)
      ≤ ∑ S ∈ 𝒮, (dominantSlabRegion s' Y' repr slabOf Nov S).indicator
          (fun _ => ((Kakeya.shadeFibre (assignedSlabFamily s' repr slabOf S) Y' x).card
            : ENNReal)) x := by
  rcases (Kakeya.shadeFibre s' Y' x).eq_empty_or_nonempty with hne | hne
  · simp [hne]
  obtain ⟨S₀, hS₀𝒮, hS₀⟩ := exists_mem_dominantSlabRegion s' Y' repr slabOf 𝒮 h𝒮 hov hne
  have hNovne : (Nov : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  calc (Nov : ENNReal)⁻¹ * ((Kakeya.shadeFibre s' Y' x).card : ENNReal)
      ≤ ((Kakeya.shadeFibre (assignedSlabFamily s' repr slabOf S₀) Y' x).card : ENNReal) :=
        (ENNReal.inv_mul_le_iff hNovne (ENNReal.natCast_ne_top Nov)).mpr hS₀
    _ = (dominantSlabRegion s' Y' repr slabOf Nov S₀).indicator
          (fun _ => ((Kakeya.shadeFibre (assignedSlabFamily s' repr slabOf S₀) Y' x).card
            : ENNReal)) x :=
      (Set.indicator_of_mem hS₀
        (fun _ => ((Kakeya.shadeFibre (assignedSlabFamily s' repr slabOf S₀) Y' x).card
          : ENNReal))).symm
    _ ≤ _ := Finset.single_le_sum
        (f := fun S => (dominantSlabRegion s' Y' repr slabOf Nov S).indicator
          (fun _ => ((Kakeya.shadeFibre (assignedSlabFamily s' repr slabOf S) Y' x).card
            : ENNReal)) x) (fun _ _ => bot_le) hS₀𝒮

/-! ### The two sides of the mass retention, as single integrals

The layer-cake rewrites are split off so that the retention proof itself is one `lintegral_mono`.
-/

/-- The total shading mass is the integral of the pointwise fibre count. -/
theorem sum_volume_shade_eq_lintegral_card_shadeFibre (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) :
    ∑ i ∈ s', volume (Y' i).shade
      = ∫⁻ x, ((Kakeya.shadeFibre s' Y' x).card : ENNReal) := by
  simpa only [Set.inter_univ, Measure.restrict_univ, Kakeya.shadeFibre] using
    (MeasureTheory.sum_measure_inter_eq_setLIntegral_card_filter (s := s')
      (A := fun i => (Y' i).shade) (hA := fun i _ => (Y' i).measurableSet_shade)
      (B := Set.univ) (μ := volume))

/-- The mass of the dominant shading, grouped by assigned slab and written as a sum of integrals of
indicators.  Each class contributes only over its own dominant region. -/
theorem sum_volume_dominantSlabShading_eq_sum_lintegral (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (𝒮 : Finset σ)
    (h𝒮 : ∀ i ∈ s', slabOf (repr i) ∈ 𝒮) (Nov : ℕ) :
    ∑ i ∈ s', volume (dominantSlabShading s' Y' repr slabOf Nov i).shade
      = ∑ S ∈ 𝒮, ∫⁻ x, (dominantSlabRegion s' Y' repr slabOf Nov S).indicator
          (fun _ => ((Kakeya.shadeFibre (assignedSlabFamily s' repr slabOf S) Y' x).card
            : ENNReal)) x := by
  rw [← sum_volume_assignedSlabFamily_eq s' (dominantSlabShading s' Y' repr slabOf Nov)
    repr slabOf 𝒮 h𝒮]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hcut : ∀ i ∈ assignedSlabFamily s' repr slabOf S,
      volume (dominantSlabShading s' Y' repr slabOf Nov i).shade
        = volume ((Y' i).shade ∩ dominantSlabRegion s' Y' repr slabOf Nov S) :=
    fun i hi => by rw [dominantSlabShading_shade, (mem_assignedSlabFamily.mp hi).2]
  rw [Finset.sum_congr rfl hcut,
    sum_measure_inter_eq_setLIntegral_card_filter (s := assignedSlabFamily s' repr slabOf S)
      (A := fun i => (Y' i).shade) (hA := fun i _ => (Y' i).measurableSet_shade),
    ← lintegral_indicator (measurableSet_dominantSlabRegion s' Y' repr slabOf Nov S)]
  rfl

/-- The finite sum over slabs commutes with the integral, for the indicator integrands above. -/
theorem sum_lintegral_indicator_dominant_eq_lintegral_sum (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (𝒮 : Finset σ) (Nov : ℕ) :
    ∑ S ∈ 𝒮, ∫⁻ x, (dominantSlabRegion s' Y' repr slabOf Nov S).indicator
        (fun _ => ((Kakeya.shadeFibre (assignedSlabFamily s' repr slabOf S) Y' x).card
          : ENNReal)) x
      = ∫⁻ x, ∑ S ∈ 𝒮, (dominantSlabRegion s' Y' repr slabOf Nov S).indicator
          (fun _ => ((Kakeya.shadeFibre (assignedSlabFamily s' repr slabOf S) Y' x).card
            : ENNReal)) x := by
  classical
  let f : σ → EuclideanSpace ℝ (Fin 3) → ℝ≥0∞ := fun S x =>
    (dominantSlabRegion s' Y' repr slabOf Nov S).indicator
      (fun _ => ((Kakeya.shadeFibre (assignedSlabFamily s' repr slabOf S) Y' x).card : ENNReal)) x
  have hmeas : ∀ S ∈ 𝒮, Measurable (f S) := fun S _ => Measurable.indicator
    (by simpa [Kakeya.shadeFibre] using
        measurable_card_filter_mem (assignedSlabFamily s' repr slabOf S)
          (fun i _ => (Y' i).measurableSet_shade))
    (measurableSet_dominantSlabRegion s' Y' repr slabOf Nov S)
  exact (lintegral_finsetSum 𝒮 hmeas).symm

open scoped Classical in
/-- **Aggregate mass retention.**  Integrating the defining inequality of the dominant regions
against `MeasureTheory.sum_measure_inter_eq_setLIntegral_card_filter`.  No multiplicity sup bound is
used, and the rate is again the absolute `Nov⁻¹`.

The pointwise overlap hypothesis `hov` is exactly what makes `Nov` usable here, and it is not
bookkeeping: the assigned families partition `s'`, so at each `x` the fibre splits as
`#𝒫_{s'}(x) = ∑_{S} #𝒫_{𝒜_S}(x)`, and the largest term is a `Nov⁻¹`-fraction of the total *only*
when at most `Nov` terms are nonzero.  Without `hov` the only available bound on the number
of active classes is `𝒮.card`, which is configuration-dependent, so `Nov` would stop being
absolute and the whole point of the construction would be lost.  `hov` is available at the call
site: the preassembly
returns the same bound for the *geometric* family `Plank.inSlabFamilyC`, and
`Plank.assignedSlabFamily_subset_inSlabFamilyC` carries it to the assigned family. -/
theorem dominantSlabShading_mass_retention (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (𝒮 : Finset σ)
    (h𝒮 : ∀ i ∈ s', slabOf (repr i) ∈ 𝒮) {Nov : ℕ} (hNov : 1 ≤ Nov)
    (hov : ∀ x : EuclideanSpace ℝ (Fin 3),
      (𝒮.filter fun S =>
        x ∈ ⋃ i ∈ assignedSlabFamily s' repr slabOf S, (Y' i).shade).card ≤ Nov) :
    ((Nov : ENNReal))⁻¹ * ∑ i ∈ s', volume (Y' i).shade
      ≤ ∑ i ∈ s', volume (dominantSlabShading s' Y' repr slabOf Nov i).shade := by
  have hmeasL : Measurable (fun x : EuclideanSpace ℝ (Fin 3) =>
      ((Kakeya.shadeFibre s' Y' x).card : ENNReal)) := by
    simpa [Kakeya.shadeFibre] using
      measurable_card_filter_mem s' (fun i _ => (Y' i).measurableSet_shade)
  rw [sum_volume_shade_eq_lintegral_card_shadeFibre,
    ← lintegral_const_mul ((Nov : ENNReal)⁻¹) hmeasL,
    sum_volume_dominantSlabShading_eq_sum_lintegral s' Y' repr slabOf 𝒮 h𝒮 Nov,
    sum_lintegral_indicator_dominant_eq_lintegral_sum s' Y' repr slabOf 𝒮 Nov]
  exact lintegral_mono
    (card_shadeFibre_le_sum_indicator_dominant s' Y' repr slabOf 𝒮 h𝒮 hNov hov)

/-! ## The joint dominant/good-slab refinement -/

/-- The dominant restriction does not touch the convex bodies, so it changes no sum of carrier
volumes.  This is what lets the good-slab threshold be read against the *original* carrier mass. -/
theorem dominantSlabShading_sum_volume_carrier (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (Nov : ℕ) (t : Finset ι) :
    ∑ i ∈ t, volume (dominantSlabShading s' Y' repr slabOf Nov i).carrier
      = ∑ i ∈ t, volume (Y' i).carrier := rfl

/-- Cancelling a positive finite natural cast on the left in `ℝ≥0∞`. -/
theorem ennreal_natCast_inv_mul_cancel {Nov : ℕ} (hNov : 1 ≤ Nov) (y : ENNReal) :
    ((Nov : ENNReal))⁻¹ * ((Nov : ENNReal) * y) = y := by
  have hne : (Nov : ENNReal) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.lt_of_lt_of_le (by decide : 0 < 1) hNov))
  have htop : (Nov : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top Nov
  rw [← mul_assoc, ENNReal.inv_mul_cancel hne htop, one_mul]

/-- The halving step of the joint ledger: `Nov⁻¹ · T ≤ 2 · R` gives `(2 · Nov)⁻¹ · T ≤ R`. -/
theorem le_of_natCast_inv_mul_le_two_mul {Nov : ℕ} {T R : ENNReal}
    (h : ((Nov : ENNReal))⁻¹ * T ≤ 2 * R) :
    ((2 * (Nov : ENNReal)))⁻¹ * T ≤ R := by
  calc ((2 * (Nov : ENNReal)))⁻¹ * T = (2⁻¹ : ENNReal) * ((Nov : ENNReal)⁻¹ * T) := by
        rw [ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl (ENNReal.natCast_ne_top 2)), mul_assoc]
    _ ≤ (2⁻¹ : ENNReal) * (2 * R) := mul_le_mul_right h (2⁻¹ : ENNReal)
    _ = R := ENNReal.inv_mul_cancel_left two_ne_zero (ENNReal.natCast_ne_top 2)

/-- Reassociating the `2 · Nov` prefactor of the joint threshold, so that
`Plank.ennreal_natCast_inv_mul_cancel` applies directly. -/
theorem two_mul_natCast_mul_comm (Nov : ℕ) (z : ENNReal) :
    2 * (Nov : ENNReal) * z = (Nov : ENNReal) * (2 * z) := by
  rw [mul_comm (2 : ENNReal) (Nov : ENNReal), mul_assoc]

open scoped Classical in
/-- **The joint slab/point refinement.**  The dominant restriction followed by a good-slab prune at
the aggregate threshold `τ`, computed for the *dominant* shading.

The whole point is the ledger.  The dominant restriction keeps a `Nov⁻¹`-fraction of the shading
mass; the slabs it then rejects carry at most `τ · totalCarrier`; and the hypothesis makes that at
most half of what was already retained.  So the combined coefficient is the **absolute**
`(2 · Nov)⁻¹` — no power of `a` is spent — while the pointwise retention survives at `Nov⁻¹`, which
is what lets the two-sided predicates be transported.  No further common-region restriction is
applied to `sGood`; doing so would destroy the slab-local fullness just established. -/
theorem exists_dominantGoodSlabRefinement (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (𝒮 : Finset σ)
    (h𝒮 : ∀ i ∈ s', slabOf (repr i) ∈ 𝒮) {Nov : ℕ} (hNov : 1 ≤ Nov)
    (hov : ∀ x : EuclideanSpace ℝ (Fin 3),
      (𝒮.filter fun S =>
        x ∈ ⋃ i ∈ assignedSlabFamily s' repr slabOf S, (Y' i).shade).card ≤ Nov)
    (τ : ℝ≥0)
    (htop : ∑ i ∈ s', volume (Y' i).shade ≠ ⊤)
    (hτ : 2 * (Nov : ENNReal) * ((τ : ENNReal) * ∑ i ∈ s', volume (Y' i).carrier)
      ≤ ∑ i ∈ s', volume (Y' i).shade) :
    ∃ 𝒮g ⊆ 𝒮,
      (∀ S ∈ 𝒮g,
        (τ : ENNReal) *
            ∑ i ∈ assignedSlabFamily s' repr slabOf S,
              volume (dominantSlabShading s' Y' repr slabOf Nov i).carrier
          ≤ ∑ i ∈ assignedSlabFamily s' repr slabOf S,
              volume (dominantSlabShading s' Y' repr slabOf Nov i).shade) ∧
      ((2 * (Nov : ENNReal)))⁻¹ * ∑ i ∈ s', volume (Y' i).shade
        ≤ ∑ i ∈ s'.filter (fun i => slabOf (repr i) ∈ 𝒮g),
            volume (dominantSlabShading s' Y' repr slabOf Nov i).shade := by
  classical
  set Ydom : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) :=
    dominantSlabShading s' Y' repr slabOf Nov
  -- (a) Aggregate mass retention at the absolute rate `Nov⁻¹`.
  have hmass : ((Nov : ENNReal))⁻¹ * ∑ i ∈ s', volume (Y' i).shade
      ≤ ∑ i ∈ s', volume (Ydom i).shade :=
    dominantSlabShading_mass_retention s' Y' repr slabOf 𝒮 h𝒮 hNov hov
  -- (b) The dominant shading mass is finite, as the shade is cut down from `Y'`.
  have htop_dom : ∑ i ∈ s', volume (Ydom i).shade ≠ ⊤ :=
    ne_top_of_le_ne_top htop (Finset.sum_le_sum fun i _ =>
      measure_mono (dominantSlabShading_shade_subset s' Y' repr slabOf Nov i))
  -- (c) The aggregate threshold, read against the (unchanged) dominant carrier mass.
  have hτ_dom : 2 * ((τ : ENNReal) * ∑ i ∈ s', volume (Ydom i).carrier)
      ≤ ∑ i ∈ s', volume (Ydom i).shade := by
    refine le_trans (le_of_eq ?_) (le_trans (mul_le_mul_right hτ ((Nov : ENNReal))⁻¹) hmass)
    rw [dominantSlabShading_sum_volume_carrier, two_mul_natCast_mul_comm,
      ennreal_natCast_inv_mul_cancel hNov]
  -- The existing good-slab prune, applied to the dominant shading.
  obtain ⟨𝒮g, hsubset, hcond, hprune⟩ :=
    exists_goodSlabPrune s' Ydom repr slabOf 𝒮 h𝒮 τ htop_dom hτ_dom
  exact ⟨𝒮g, hsubset, hcond,
    le_of_natCast_inv_mul_le_two_mul (hmass.trans hprune)⟩

/-! ## The quantitative refinement package -/

/-- The `ℝ≥0`-to-`ℝ≥0∞` cast of the joint coefficient.  Note this needs `1 ≤ Nov`: at `Nov = 0` the
left side is `0` while the right side is `⊤`. -/
theorem coe_two_mul_natCast_inv {Nov : ℕ} (hNov : 1 ≤ Nov) :
    (((2 * (Nov : ℝ≥0))⁻¹ : ℝ≥0) : ENNReal) = ((2 * (Nov : ENNReal)))⁻¹ := by
  rw [ENNReal.coe_inv (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (by omega)))]
  push_cast
  rfl

open scoped Classical in
/-- **The refinement package.**  The interface the final assembly should consume: the joint
dominant/good-slab refinement as a single `ShadedBody.IsCRefinement` at the absolute coefficient
`(2 · Nov)⁻¹`, rather than as a raw sum inequality. -/
theorem isCRefinement_dominantGoodSlabShading (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (repr : ι → τ) (slabOf : τ → σ) (𝒮g : Finset σ)
    {Nov : ℕ} (hNov : 1 ≤ Nov)
    (hmass : ((2 * (Nov : ENNReal)))⁻¹ * ∑ i ∈ s', volume (Y' i).shade
      ≤ ∑ i ∈ s'.filter (fun i => slabOf (repr i) ∈ 𝒮g),
          volume (dominantSlabShading s' Y' repr slabOf Nov i).shade) :
    ShadedBody.IsCRefinement (s'.filter (fun i => slabOf (repr i) ∈ 𝒮g))
      (dominantSlabShading s' Y' repr slabOf Nov) s' Y' ((2 * (Nov : ℝ≥0))⁻¹) := by
  refine ⟨⟨Finset.filter_subset _ s', fun i _ =>
    ⟨dominantSlabShading_toConvexSpaceBody .., dominantSlabShading_shade_subset ..⟩⟩, ?_⟩
  rwa [coe_two_mul_natCast_inv hNov]

end Plank

end
