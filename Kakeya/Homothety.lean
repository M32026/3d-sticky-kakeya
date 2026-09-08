/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Density
public import Kakeya.Frostman
public import Kakeya.KatzTao
public import Kakeya.Multiplicity
public import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Homothety images of convex bodies and shaded bodies

The affine changes of variables of the Kakeya argument are of the shape
`L(y) = ρ⁻¹ • (y - c)`, i.e. a homothety followed by a translation. The translation half of
this is already covered: `ConvexSpaceBody.translate`, `ShadedBody.translate`,
`IsEssentiallyDistinct.image_add_left`, `ShadedBody.multiplicity_translate_const`,
`ShadedBody.fullness_translate_const` and `Kakeya.maxDensity_translate` all exist. This file
supplies the missing homothety half, together with the missing image operation on
`ShadedBody`.

The only quantitative input is that a homothety of nonzero ratio `r` multiplies every volume
by the single constant `|r| ^ finrank ℝ E`
(`MeasureTheory.Measure.addHaar_image_homothety`). Everything below is a formal consequence of
that: `IsEssentiallyDistinct`, `ShadedBody.multiplicity` and `Kakeya.densityIn` are ratios of
volumes, and `ShadedBody.IsCRefinement` is an inequality between two volume sums scaled by the
same factor.

These statements are what `Kakeya.VeryNotSticky.plankPresentation` composes. They are the
blueprint subsection "Invariance under homothety" of `GWZAdapted/section2.tex`.
-/

@[expose] public section

open MeasureTheory Metric Set

section Homothety

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace Kakeya

omit [FiniteDimensional ℝ E] in
/-- A homothety of nonzero ratio is a measurable embedding: it is the composition of the
homeomorphism `y ↦ r • y` with a translation. This is what lets the shading of a
`ShadedBody` be pushed forward along it. -/
lemma measurableEmbedding_homothety (x : E) {r : ℝ} (hr : r ≠ 0) :
    MeasurableEmbedding (AffineMap.homothety x r) := by
  have h : (AffineMap.homothety x r : E → E) =
      ((x - r • x) + ·) ∘ (fun y : E => r • y) := by
    funext y
    simp only [AffineMap.homothety_apply, Function.comp_apply, vsub_eq_sub, vadd_eq_add,
      smul_sub]
    abel
  rw [h]
  exact (measurableEmbedding_addLeft (x - r • x)).comp
    (Homeomorph.smulOfNeZero r hr).measurableEmbedding

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The homothety of centre `x` and ratio `r⁻¹` undoes the homothety of centre `x` and ratio
`r`, at the level of images of sets. -/
lemma homothety_inv_image_homothety_image (x : E) {r : ℝ} (hr : r ≠ 0) (A : Set E) :
    AffineMap.homothety x r⁻¹ '' (AffineMap.homothety x r '' A) = A := by
  rw [← Set.image_comp]
  simp [AffineMap.homothety_apply, smul_smul, inv_mul_cancel₀ hr]

end Kakeya

/-- The image of a convex body under the homothety of centre `x` and ratio `r`, as a convex
body. This is `ConvexSpaceBody.affineImage` specialised to `AffineMap.homothety`. -/
def ConvexSpaceBody.homothety (K : ConvexSpaceBody E) (x : E) (r : ℝ) : ConvexSpaceBody E :=
  K.affineImage (AffineMap.homothety x r) (AffineMap.homothety_continuous x r)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp]
lemma ConvexSpaceBody.coe_homothety (K : ConvexSpaceBody E) (x : E) (r : ℝ) :
    SetLike.coe (K.homothety x r) = AffineMap.homothety x r '' K.carrier := rfl

/-- A homothety multiplies the volume of a convex body by `|r ^ finrank ℝ E|`. This is the
homothety analogue of `Kakeya.volume_translate`. -/
lemma ConvexSpaceBody.volume_homothety (K : ConvexSpaceBody E) (x : E) (r : ℝ) :
    volume (K.homothety x r).carrier
      = ENNReal.ofReal |r ^ Module.finrank ℝ E| * volume K.carrier :=
  MeasureTheory.Measure.addHaar_image_homothety (μ := (volume : Measure E)) x r K.carrier

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A homothety of nonzero ratio preserves and reflects inclusion of convex bodies. This is the
homothety analogue of `translate_le_translate_iff`. -/
lemma ConvexSpaceBody.homothety_le_homothety_iff {K L : ConvexSpaceBody E} (x : E) {r : ℝ}
    (hr : r ≠ 0) : K.homothety x r ≤ L.homothety x r ↔ K ≤ L := by
  rw [← SetLike.coe_subset_coe, ConvexSpaceBody.coe_homothety, ConvexSpaceBody.coe_homothety,
    Set.image_subset_image_iff (AffineMap.homothety_injective x hr)]
  exact (SetLike.coe_subset_coe (S := K) (T := L))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The homothety of ratio `r⁻¹` undoes the homothety of ratio `r` on convex bodies. This is the
homothety analogue of `ConvexSpaceBody.translate_neg_cancel`. -/
lemma ConvexSpaceBody.homothety_homothety_inv (K : ConvexSpaceBody E) (x : E) {r : ℝ}
    (hr : r ≠ 0) : (K.homothety x r).homothety x r⁻¹ = K :=
  ConvexSpaceBody.ext (Kakeya.homothety_inv_image_homothety_image x hr K.carrier)

namespace ShadedBody

/-- The image of a shaded body under a continuous affine self-map that is a measurable
embedding, pushing forward both the underlying convex body (via
`ConvexSpaceBody.affineImage`) and the shading. The measurable-embedding hypothesis is what
keeps the image of the shading measurable; compare `ShadedBody.translate`, which gets it from
`measurableEmbedding_addLeft`. -/
def affineImage (W : ShadedBody E) (f : E →ᵃ[ℝ] E) (hcont : Continuous f)
    (hemb : MeasurableEmbedding f) : ShadedBody E where
  toConvexSpaceBody := W.toConvexSpaceBody.affineImage f hcont
  shade := f '' W.shade
  measurableSet_shade := hemb.measurableSet_image' W.measurableSet_shade
  shade_subset := Set.image_mono W.shade_subset

omit [FiniteDimensional ℝ E] [BorelSpace E] in
@[simp]
lemma affineImage_shade (W : ShadedBody E) (f : E →ᵃ[ℝ] E) (hcont : Continuous f)
    (hemb : MeasurableEmbedding f) :
    (W.affineImage f hcont hemb).shade = f '' W.shade := rfl

/-- The image of a shaded body under the homothety of centre `x` and nonzero ratio `r`. -/
def homothety (W : ShadedBody E) (x : E) {r : ℝ} (hr : r ≠ 0) : ShadedBody E :=
  W.affineImage (AffineMap.homothety x r) (AffineMap.homothety_continuous x r)
    (Kakeya.measurableEmbedding_homothety x hr)

omit [FiniteDimensional ℝ E] in
@[simp]
lemma homothety_shade (W : ShadedBody E) (x : E) {r : ℝ} (hr : r ≠ 0) :
    (W.homothety x hr).shade = AffineMap.homothety x r '' W.shade := rfl

omit [FiniteDimensional ℝ E] in
@[simp]
lemma homothety_toConvexSpaceBody (W : ShadedBody E) (x : E) {r : ℝ} (hr : r ≠ 0) :
    (W.homothety x hr).toConvexSpaceBody = W.toConvexSpaceBody.homothety x r := rfl

end ShadedBody

/-- **`IsEssentiallyDistinct` is preserved by a homothety.**

Only the translation case was available (`IsEssentiallyDistinct.image_add_left`). A homothety
of nonzero ratio is injective and multiplies all three volumes occurring in the definition by
the same factor `|r| ^ finrank ℝ E`
(`MeasureTheory.Measure.addHaar_image_homothety`), so the inequality is unchanged. -/
lemma IsEssentiallyDistinct.image_homothety {U V : Set E} (x : E) {r : ℝ} (hr : r ≠ 0)
    (h : IsEssentiallyDistinct U V) :
    IsEssentiallyDistinct (AffineMap.homothety x r '' U) (AffineMap.homothety x r '' V) := by
  unfold IsEssentiallyDistinct at *
  have h_inj : Function.Injective (AffineMap.homothety x r) :=
    AffineMap.homothety_injective x hr
  rw [← Set.image_inter h_inj]
  rw [MeasureTheory.Measure.addHaar_image_homothety (μ := (volume : Measure E)) x r (U ∩ V),
    MeasureTheory.Measure.addHaar_image_homothety (μ := (volume : Measure E)) x r U,
    MeasureTheory.Measure.addHaar_image_homothety (μ := (volume : Measure E)) x r V]
  set c := ENNReal.ofReal |r ^ Module.finrank ℝ E| with hc
  calc
    c * volume (U ∩ V) ≤ c * ((1/2 : ENNReal) * max (volume U) (volume V)) := by
      gcongr
    _ = (1/2 : ENNReal) * (c * max (volume U) (volume V)) := by
      ring
    _ = (1/2 : ENNReal) * max (c * volume U) (c * volume V) := by rw [mul_max]

/-- `IsEssentiallyDistinct` for the homothety images of two convex bodies. -/
lemma IsEssentiallyDistinct.homothety_convexBody {K L : ConvexSpaceBody E} (x : E) {r : ℝ}
    (hr : r ≠ 0) (h : IsEssentiallyDistinct K.carrier L.carrier) :
    IsEssentiallyDistinct (K.homothety x r).carrier (L.homothety x r).carrier :=
  IsEssentiallyDistinct.image_homothety x hr h

namespace ShadedBody

variable {ι : Type*}

/-- A homothety multiplies the total shading volume of a finite family by
`|r ^ finrank ℝ E|`. -/
lemma sum_volume_shade_homothety (s : Finset ι) (V : ι → ShadedBody E) (x : E) {r : ℝ}
    (hr : r ≠ 0) :
    ∑ i ∈ s, volume ((V i).homothety x hr).shade
      = ENNReal.ofReal |r ^ Module.finrank ℝ E| * ∑ i ∈ s, volume (V i).shade := by
  calc
    ∑ i ∈ s, volume ((V i).homothety x hr).shade
        = ∑ i ∈ s, volume (AffineMap.homothety x r '' (V i).shade) := by
      simp [homothety_shade]
    _ = ∑ i ∈ s, (ENNReal.ofReal |r ^ Module.finrank ℝ E| * volume ((V i).shade)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [MeasureTheory.Measure.addHaar_image_homothety]
    _ = ENNReal.ofReal |r ^ Module.finrank ℝ E| * ∑ i ∈ s, volume (V i).shade := by
      rw [Finset.mul_sum]

/-- The inverse form of `ShadedBody.sum_volume_shade_homothety`. -/
lemma sum_volume_shade_homothety_inv (s : Finset ι) (V : ι → ShadedBody E) (x : E) {r : ℝ}
    (hr : r ≠ 0) :
    ∑ i ∈ s, volume ((V i).homothety x (inv_ne_zero hr)).shade
      = (ENNReal.ofReal |r ^ Module.finrank ℝ E|)⁻¹ * ∑ i ∈ s, volume (V i).shade := by
  have h := sum_volume_shade_homothety s V x (inv_ne_zero hr)
  set n := Module.finrank ℝ E with hn
  have hcalc : ENNReal.ofReal |(r⁻¹) ^ n| = (ENNReal.ofReal |r ^ n|)⁻¹ := by
    calc
      ENNReal.ofReal |(r⁻¹) ^ n| = ENNReal.ofReal (|r ^ n|⁻¹) := by
        rw [inv_pow, abs_inv]
      _ = (ENNReal.ofReal |r ^ n|)⁻¹ := by
        have hpos : 0 < |r ^ n| := abs_pos.mpr (pow_ne_zero n hr)
        rw [ENNReal.ofReal_inv_of_pos hpos]
  calc
    ∑ i ∈ s, volume ((V i).homothety x (inv_ne_zero hr)).shade
        = ENNReal.ofReal |(r⁻¹) ^ n| * ∑ i ∈ s, volume (V i).shade := h
    _ = (ENNReal.ofReal |r ^ n|)⁻¹ * ∑ i ∈ s, volume (V i).shade := by rw [hcalc]

omit [FiniteDimensional ℝ E] in
/-- The shaded union of a homothety image family is the homothety image of the shaded union. -/
lemma iUnionShade_homothety (s : Finset ι) (V : ι → ShadedBody E) (x : E) {r : ℝ}
    (hr : r ≠ 0) :
    (⋃ i ∈ s, ((V i).homothety x hr).shade)
      = AffineMap.homothety x r '' ⋃ i ∈ s, (V i).shade := by
  simp [homothety_shade, ← Set.image_iUnion₂]

/-- Fullness is invariant under a nonzero homothety applied to every shaded body. -/
lemma fullness_homothety (s : Finset ι) (V : ι → ShadedBody E) (x : E) {r : ℝ}
    (hr : r ≠ 0) :
    fullness s (fun i ↦ (V i).homothety x hr) = fullness s V := by
  rw [← ENNReal.coe_inj, coe_fullness, coe_fullness]
  unfold fullness'
  rw [sum_volume_shade_homothety s V x hr]
  have hcarrier :
      ∑ i ∈ s, volume ((V i).homothety x hr).carrier =
        ENNReal.ofReal |r ^ Module.finrank ℝ E| *
          ∑ i ∈ s, volume (V i).carrier := by
    calc
      ∑ i ∈ s, volume ((V i).homothety x hr).carrier =
          ∑ i ∈ s, ENNReal.ofReal |r ^ Module.finrank ℝ E| *
            volume (V i).carrier := by
              exact Finset.sum_congr rfl fun i _ ↦
                ConvexSpaceBody.volume_homothety (V i).toConvexSpaceBody x r
      _ = ENNReal.ofReal |r ^ Module.finrank ℝ E| *
          ∑ i ∈ s, volume (V i).carrier := by rw [Finset.mul_sum]
  rw [hcarrier]
  exact ENNReal.mul_div_mul_left _ _
    (ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr (pow_ne_zero _ hr)))
    ENNReal.ofReal_ne_top

/-- **Multiplicity is invariant under a homothety.**

The template is `ShadedBody.multiplicity_translate_const`. Both the numerator
`∑ |Y(V)|` and the denominator `|U(𝒱, Y)|` of `ShadedBody.multiplicity` are multiplied by the
same factor `|r| ^ finrank ℝ E`, so the ratio is unchanged. -/
lemma multiplicity_homothety (s : Finset ι) (V : ι → ShadedBody E) (x : E) {r : ℝ}
    (hr : r ≠ 0) :
    multiplicity s (fun i => (V i).homothety x hr) = multiplicity s V := by
  have hc0 : ENNReal.ofReal |r ^ Module.finrank ℝ E| ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr (pow_ne_zero _ hr))
  simp only [multiplicity_eq_div]
  rw [sum_volume_shade_homothety s V x hr, iUnionShade_homothety s V x hr,
    MeasureTheory.Measure.addHaar_image_homothety (μ := volume) x r _,
    ENNReal.mul_div_mul_left _ _ hc0 ENNReal.ofReal_ne_top]

omit [FiniteDimensional ℝ E] in
/-- **A refinement pulls back along a homothety.**

The unquantified half of `ShadedBody.IsCRefinement.comap_homothety`. -/
lemma IsRefinement.comap_homothety {s' s : Finset ι} {V' V : ι → ShadedBody E} (x : E)
    {r : ℝ} (hr : r ≠ 0)
    (h : IsRefinement s' V' s (fun i => (V i).homothety x hr)) :
    IsRefinement s' (fun i => (V' i).homothety x (inv_ne_zero hr)) s V := by
  refine ⟨h.1, fun i hi => ⟨?_, ?_⟩⟩
  · rw [homothety_toConvexSpaceBody, (h.2 i hi).1, homothety_toConvexSpaceBody,
      ConvexSpaceBody.homothety_homothety_inv _ _ hr]
  · exact (Set.image_mono (h.2 i hi).2).trans
      (Kakeya.homothety_inv_image_homothety_image x hr (V i).shade).le

/-- **A `c`-refinement pulls back along a homothety.**

If `(𝒱', Y')` is a `c`-refinement of the homothety image of `(𝒱, Y)`, then its image under the
inverse homothety is a `c`-refinement of `(𝒱, Y)` itself. This is the direction that
`Kakeya.VeryNotSticky.plankPresentation` needs: a refinement of the plank family has to be
transported back to the family of factoring bodies.

Note that `ShadedBody.IsRefinement` demands the carriers to be *equal*, not merely contained
in one another, which is why the conclusion is stated for the explicit inverse image
`(V' i).homothety x r⁻¹` — whose carrier is exactly that of `V i` — rather than for some
unspecified shading. -/
lemma IsCRefinement.comap_homothety {s' s : Finset ι} {V' V : ι → ShadedBody E} (x : E)
    {r : ℝ} (hr : r ≠ 0) {c : NNReal}
    (h : IsCRefinement s' V' s (fun i => (V i).homothety x hr) c) :
    IsCRefinement s' (fun i => (V' i).homothety x (inv_ne_zero hr)) s V c := by
  have hc₀ : ENNReal.ofReal |r ^ Module.finrank ℝ E| ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr (pow_ne_zero _ hr))
  refine ⟨IsRefinement.comap_homothety x hr h.1, ?_⟩
  have h2 := h.2
  rw [sum_volume_shade_homothety s V x hr] at h2
  rw [sum_volume_shade_homothety_inv s' V' x hr,
    ← ENNReal.mul_le_iff_le_inv hc₀ ENNReal.ofReal_ne_top, mul_left_comm]
  exact h2

end ShadedBody

namespace Kakeya

variable {ι : Type*}

/-- A homothety multiplies the total volume of a finite family of convex bodies by
`|r ^ finrank ℝ E|`. -/
lemma sum_volume_homothety (t : Finset ι) (W : ι → ConvexSpaceBody E) (x : E) (r : ℝ) :
    ∑ i ∈ t, volume ((W i).homothety x r).carrier
      = ENNReal.ofReal |r ^ Module.finrank ℝ E| * ∑ i ∈ t, volume (W i).carrier := by
  calc
    ∑ i ∈ t, volume ((W i).homothety x r).carrier
        = ∑ i ∈ t, (ENNReal.ofReal |r ^ Module.finrank ℝ E| * volume (W i).carrier) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ConvexSpaceBody.volume_homothety (W i) x r]
    _ = ENNReal.ofReal |r ^ Module.finrank ℝ E| * ∑ i ∈ t, volume (W i).carrier := by
      rw [Finset.mul_sum]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A homothety of nonzero ratio does not change which bodies of the family are contained in the
test body, so it leaves `Kakeya.familyIn` unchanged. -/
lemma familyIn_homothety (s : Finset ι) (W : ι → ConvexSpaceBody E) (K : ConvexSpaceBody E)
    (x : E) {r : ℝ} (hr : r ≠ 0) :
    familyIn s (fun i => (W i).homothety x r) (K.homothety x r) = familyIn s W K :=
  Finset.filter_congr fun _ _ => ConvexSpaceBody.homothety_le_homothety_iff x hr

/-- **`densityIn` is invariant under a homothety of the test body and of all bodies.**

The homothety multiplies the numerator and the denominator of `Kakeya.densityIn` by the same
factor, and it preserves the containment relation `W i ≤ K` used to cut down the sum. Compare
`Kakeya.densityIn_translate`. -/
lemma densityIn_homothety (s : Finset ι) (W : ι → ConvexSpaceBody E) (K : ConvexSpaceBody E)
    (x : E) {r : ℝ} (hr : r ≠ 0) :
    densityIn s (fun i => (W i).homothety x r) (K.homothety x r) = densityIn s W K := by
  have hc0 : ENNReal.ofReal |r ^ Module.finrank ℝ E| ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr (pow_ne_zero _ hr))
  have hfam := familyIn_homothety s W K x hr
  unfold familyIn at hfam
  unfold densityIn
  rw [hfam, sum_volume_homothety _ W x r, ConvexSpaceBody.volume_homothety K x r,
    ENNReal.mul_div_mul_left _ _ hc0 ENNReal.ofReal_ne_top]

/-- **`Δ_max` is invariant under a homothety.**

The template is `Kakeya.maxDensity_translate`: the homothety of nonzero ratio `r` is a
bijection of the convex bodies of `E`, so it permutes the test bodies over which the supremum
defining `Kakeya.maxDensity` is taken, and it leaves each `Kakeya.densityIn` unchanged by
`Kakeya.densityIn_homothety`.

This is what transfers the bound on `Δ_max(𝕎_B)` supplied by the biased factoring to the plank
family produced by `Kakeya.VeryNotSticky.plankPresentation`, i.e. what feeds the hypothesis
`hdens` of `Kakeya.VeryNotSticky.plankCard`. -/
lemma maxDensity_homothety (s : Finset ι) (W : ι → ConvexSpaceBody E) (x : E) {r : ℝ}
    (hr : r ≠ 0) :
    maxDensity s (fun i => (W i).homothety x r) = maxDensity s W := by
  apply le_antisymm
  · rw [maxDensity_le_iff]
    intro K
    have hK : K = (K.homothety x r⁻¹).homothety x r := by
      simpa using (ConvexSpaceBody.homothety_homothety_inv K x (inv_ne_zero hr)).symm
    rw [hK, densityIn_homothety s W (K.homothety x r⁻¹) x hr]
    exact le_maxDensity s W _
  · rw [maxDensity_le_iff]
    intro K
    rw [← densityIn_homothety s W K x hr]
    exact le_maxDensity s (fun i => (W i).homothety x r) _

end Kakeya

namespace ConvexSpaceBody

variable {ι : Type*}

/-- The Katz--Tao maximal-density condition is invariant under a common nonzero homothety. -/
lemma IsKatzTao.homothety {s : Finset ι} {W : ι → ConvexSpaceBody E} {C : ENNReal}
    (h : IsKatzTao s W C) (x : E) {r : ℝ} (hr : r ≠ 0) :
    IsKatzTao s (fun i => (W i).homothety x r) C := by
  rw [IsKatzTao_def, Kakeya.maxDensity_homothety s W x hr]
  exact h

/-- **The Frostman property is invariant under a homothety.**

A homothety of nonzero ratio `r` is an order isomorphism of the convex bodies of `E`
(`ConvexSpaceBody.homothety_le_homothety_iff`, with inverse
`ConvexSpaceBody.homothety_homothety_inv`), and it leaves `Kakeya.densityIn` unchanged
(`Kakeya.densityIn_homothety`). So the two families of inequalities defining
`ConvexSpaceBody.IsFrostmanIn` are in bijection and termwise identical. Compare
`ConvexSpaceBody.IsFrostmanIn.translate_iff`. -/
lemma IsFrostmanIn.homothety {s : Finset ι} {W : ι → ConvexSpaceBody E} {K : ConvexSpaceBody E}
    {C : ENNReal} (x : E) {r : ℝ} (hr : r ≠ 0) :
    IsFrostmanIn s (fun i => (W i).homothety x r) (K.homothety x r) C ↔ IsFrostmanIn s W K C := by
  constructor
  · intro h K' hK'
    have h' := h (K'.homothety x r) ((homothety_le_homothety_iff x hr).2 hK')
    rwa [Kakeya.densityIn_homothety s W K' x hr, Kakeya.densityIn_homothety s W K x hr] at h'
  · intro h K' hK'
    have hK'' : K' = (K'.homothety x r⁻¹).homothety x r := by
      simpa using (homothety_homothety_inv K' x (inv_ne_zero hr)).symm
    have hle : K'.homothety x r⁻¹ ≤ K := by
      have := (homothety_le_homothety_iff x (inv_ne_zero hr)).2 hK'
      rwa [homothety_homothety_inv K x hr] at this
    rw [hK'', Kakeya.densityIn_homothety s W _ x hr, Kakeya.densityIn_homothety s W K x hr]
    exact h _ hle

/-- **The Frostman constant is invariant under a homothety.**

Immediate from `ConvexSpaceBody.IsFrostmanIn.homothety`: the two sets of admissible constants
coincide, hence so do their infima. -/
theorem frostmanConstIn_homothety (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (K : ConvexSpaceBody E) (x : E) {r : ℝ} (hr : r ≠ 0) :
    frostmanConstIn s (fun i => (W i).homothety x r) (K.homothety x r) = frostmanConstIn s W K :=
  congrArg sInf (Set.ext fun _ => IsFrostmanIn.homothety x hr)

end ConvexSpaceBody

end Homothety
