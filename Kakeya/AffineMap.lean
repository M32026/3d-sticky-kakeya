/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Homothety
public import Kakeya.Frostman

/-!
# Invertible affine transport

`Kakeya.Homothety` treats the isotropic change of variables `y ↦ AffineMap.homothety x r y`.
Some of the arguments need a genuinely anisotropic change of variables, which stretches the
axes by different factors, so the homothety statements do not cover them.

This file supplies the general-affine versions for an affine equivalence `L : E ≃ᵃ[ℝ] E`. Its
single quantitative input is that `L` multiplies the volume of *every* set by the constant
`|det L.linear|`: the linear part scales by that determinant
(`MeasureTheory.Measure.addHaar_image_linearMap`) and the translation part is neutered by
add-invariance.

That factor cancels from `ShadedBody.multiplicity`, `ShadedBody.fullness`, and
`Kakeya.densityIn`. Thus these quantities, as well as `Kakeya.maxDensity` and
`IsEssentiallyDistinct`, are exactly invariant under affine equivalences.
-/

@[expose] public section

open MeasureTheory Metric Set

section AffineImage

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

namespace Kakeya

/-- An affine automorphism of `E` multiplies the volume of every set by `|det L.linear|`. This
is the general-affine analogue of `MeasureTheory.Measure.addHaar_image_homothety`: the linear
part of `L` scales by `|det L.linear|` (`addHaar_image_linearMap`) and the translation part is
neutered by add-invariance (`AffineMap.decomp` + `Set.image_comp`). -/
lemma volume_affineImage (L : E ≃ᵃ[ℝ] E) (s : Set E) :
    volume (L.toAffineMap '' s) =
      ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| * volume s := by
  let c : E := L.toAffineMap 0
  have hf : (L.toAffineMap : E → E) =
      (fun x : E => x + c) ∘ (fun x : E => L.toAffineMap.linear x) := by
    funext x
    dsimp
    simpa [c] using (congrFun (AffineMap.decomp (L.toAffineMap)) x)
  calc
    volume (L.toAffineMap '' s)
        = volume (((fun x : E => x + c) ∘
            (fun x : E => L.toAffineMap.linear x)) '' s) := by
          rw [hf]
    _ = volume ((fun x : E => x + c) '' (L.toAffineMap.linear '' s)) := by
          rw [Set.image_comp]
    _ = volume (L.toAffineMap.linear '' s) := by
          simp
    _ = ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| * volume s := by
          rw [AffineEquiv.linear_toAffineMap]
          exact MeasureTheory.Measure.addHaar_image_linearMap (μ := (volume : Measure E))
            (f := (L.linear : E →ₗ[ℝ] E)) s

end Kakeya

namespace ShadedBody

open Kakeya

/-- The total shading volume of an affine-image family is `|det L.linear|` times the original. -/
lemma sum_volume_shade_affineImage (t : Finset ι) (Y : ι → ShadedBody E)
    (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L) (hemb : MeasurableEmbedding L) :
    ∑ i ∈ t, volume ((Y i).affineImage L.toAffineMap hcont hemb).shade
      = ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| *
          ∑ i ∈ t, volume (Y i).shade := by
  calc
    ∑ i ∈ t, volume ((Y i).affineImage L.toAffineMap hcont hemb).shade
        = ∑ i ∈ t, volume (L.toAffineMap '' (Y i).shade) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ShadedBody.affineImage_shade]
    _ = ∑ i ∈ t, (ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| *
          volume (Y i).shade) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [volume_affineImage]
    _ = ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| *
          ∑ i ∈ t, volume (Y i).shade := by
          rw [Finset.mul_sum]

/-- The total carrier volume of an affine-image family is `|det L.linear|` times the original. -/
lemma sum_volume_carrier_affineImage (t : Finset ι) (Y : ι → ShadedBody E)
    (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L) (hemb : MeasurableEmbedding L) :
    ∑ i ∈ t, volume ((Y i).affineImage L.toAffineMap hcont hemb).carrier
      = ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| *
          ∑ i ∈ t, volume (Y i).carrier := by
  calc
    ∑ i ∈ t, volume ((Y i).affineImage L.toAffineMap hcont hemb).carrier
        = ∑ i ∈ t, volume (L.toAffineMap '' (Y i).carrier) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [ShadedBody.affineImage]
    _ = ∑ i ∈ t, (ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| *
          volume (Y i).carrier) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [volume_affineImage]
    _ = ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| *
          ∑ i ∈ t, volume (Y i).carrier := by
          rw [Finset.mul_sum]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The shaded union of an affine-image family is the affine image of the shaded union. -/
lemma iUnionShade_affineImage (t : Finset ι) (Y : ι → ShadedBody E)
    (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L) (hemb : MeasurableEmbedding L) :
    (⋃ i ∈ t, ((Y i).affineImage L.toAffineMap hcont hemb).shade) =
      L.toAffineMap '' ⋃ i ∈ t, (Y i).shade := by
  simp [ShadedBody.affineImage_shade, ← Set.image_iUnion₂]

/-- **Multiplicity is invariant under an invertible affine change of variables.**

An invertible affine self-map multiplies the volume of *every* set by the single factor
`|det L.linear|`, and images commute with unions, so the numerator `∑ |Y(V)|` and the
denominator `|U(𝒱, Y)|` of `ShadedBody.multiplicity` are scaled by that one factor and the
ratio is left *exactly* unchanged. No comparison constant is lost. The determinant is nonzero
because `L` is an equivalence, which is what keeps the common factor cancellable rather than
collapsing the ratio to `0/0`.

This is the general-affine strengthening of `ShadedBody.multiplicity_homothety`, which is the
special case `L = AffineMap.homothety x r`. It is stated because an anisotropic slab rescaling
stretches the axes by *different* factors, so the isotropic statement does not cover it.

`MeasureTheory.Measure.addHaar_image_linearMap` supplies the volume scaling for the linear
part of `L` and `MeasureTheory.measure_preimage_add` the translation part. -/
lemma multiplicity_affineImage (s : Finset ι) (V : ι → ShadedBody E) (L : E ≃ᵃ[ℝ] E)
    (hcont : Continuous L) (hemb : MeasurableEmbedding L) :
    multiplicity s (fun i => (V i).affineImage L.toAffineMap hcont hemb)
      = multiplicity s V := by
  have hdet_ne0 : LinearMap.det (L.linear : E →ₗ[ℝ] E) ≠ 0 :=
    (LinearEquiv.isUnit_det' L.linear).ne_zero
  have hc0 : ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr hdet_ne0)
  rw [ShadedBody.multiplicity_eq_div]
  rw [sum_volume_shade_affineImage s V L hcont hemb,
    iUnionShade_affineImage s V L hcont hemb, volume_affineImage]
  exact ENNReal.mul_div_mul_left _ _ hc0 ENNReal.ofReal_ne_top

/-- **Fullness is invariant under an invertible affine change of variables.**

The companion of `ShadedBody.multiplicity_affineImage`, and the general-affine strengthening
of `ShadedBody.fullness_translate_const`: both the numerator `∑ |Y(V)|` and the denominator
`∑ |V|` of `ShadedBody.fullness` are multiplied by `|det L.linear|`, so the ratio is
unchanged, exactly and not merely up to a factor `≈ 1`. -/
lemma fullness_affineImage (s : Finset ι) (V : ι → ShadedBody E) (L : E ≃ᵃ[ℝ] E)
    (hcont : Continuous L) (hemb : MeasurableEmbedding L) :
    fullness s (fun i => (V i).affineImage L.toAffineMap hcont hemb) = fullness s V := by
  have hdet_ne0 : LinearMap.det (L.linear : E →ₗ[ℝ] E) ≠ 0 :=
    (LinearEquiv.isUnit_det' L.linear).ne_zero
  have hc0 : ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr hdet_ne0)
  rw [← ENNReal.coe_inj, ShadedBody.coe_fullness, ShadedBody.coe_fullness]
  unfold ShadedBody.fullness'
  rw [sum_volume_shade_affineImage s V L hcont hemb,
    sum_volume_carrier_affineImage s V L hcont hemb]
  exact ENNReal.mul_div_mul_left _ _ hc0 ENNReal.ofReal_ne_top

end ShadedBody

namespace Kakeya

/-- An affine equivalence of a finite-dimensional real normed space is a measurable embedding:
it is a homeomorphism, via `AffineEquiv.toContinuousAffineEquiv`. This is what lets the shading
of a `ShadedBody` be pushed forward along it, and it is the general-affine replacement for
`Kakeya.measurableEmbedding_homothety`. -/
lemma measurableEmbedding_affineEquiv (L : E ≃ᵃ[ℝ] E) : MeasurableEmbedding L := by
  exact L.toContinuousAffineEquiv.toHomeomorph.measurableEmbedding

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The volume scaling factor `|det L.linear|` of an affine equivalence is nonzero in `[0, ∞]`.
This is the bookkeeping that keeps the common factor of `Kakeya.densityIn` cancellable rather
than collapsing the ratio to `0/0`. -/
lemma ofReal_abs_det_affineEquiv_ne_zero (L : E ≃ᵃ[ℝ] E) :
    ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| ≠ 0 := by
  have hdet_ne0 : LinearMap.det (L.linear : E →ₗ[ℝ] E) ≠ 0 :=
    (LinearEquiv.isUnit_det' L.linear).ne_zero
  exact ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr hdet_ne0)

end Kakeya

/-- An affine equivalence multiplies the volume of a convex body by `|det L.linear|`. This is
`Kakeya.volume_affineImage` read on `ConvexSpaceBody.affineImage`, and the general-affine
analogue of `ConvexSpaceBody.volume_homothety`. -/
lemma ConvexSpaceBody.volume_affineImage (K : ConvexSpaceBody E) (L : E ≃ᵃ[ℝ] E)
    (hcont : Continuous L) :
    volume (K.affineImage L.toAffineMap hcont).carrier
      = ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| * volume K.carrier := by
  change volume (L.toAffineMap '' K.carrier) =
    ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| * volume K.carrier
  exact Kakeya.volume_affineImage L K.carrier

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- An injective continuous affine map preserves and reflects inclusion of convex bodies. This
is the general-affine strengthening of `ConvexSpaceBody.homothety_le_homothety_iff`, and it is
what makes the containment condition `W i ≤ K` cutting down `Kakeya.densityIn` invariant. -/
lemma ConvexSpaceBody.affineImage_le_affineImage_iff {K K' : ConvexSpaceBody E}
    (f : E →ᵃ[ℝ] E) (hf : Continuous f) (hinj : Function.Injective f) :
    K.affineImage f hf ≤ K'.affineImage f hf ↔ K ≤ K' := by
  rw [← SetLike.coe_subset_coe, ConvexSpaceBody.coe_affineImage, ConvexSpaceBody.coe_affineImage,
    Set.image_subset_image_iff hinj]
  exact SetLike.coe_subset_coe (S := K) (T := K')

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The image under `L.symm` undoes the image under `L` on convex bodies. This is the
general-affine analogue of `ConvexSpaceBody.homothety_homothety_inv`, and it shows that every
test body of `Kakeya.maxDensity` is in the range of the transport. -/
lemma ConvexSpaceBody.affineImage_symm_affineImage (K : ConvexSpaceBody E) (L : E ≃ᵃ[ℝ] E)
    (hcont : Continuous L) (hcont' : Continuous L.symm) :
    (K.affineImage L.symm.toAffineMap hcont').affineImage L.toAffineMap hcont = K := by
  apply ConvexSpaceBody.ext
  change L.toAffineMap '' (L.symm.toAffineMap '' K.carrier) = K.carrier
  rw [← Set.image_comp]
  have hf : (L.toAffineMap ∘ L.symm.toAffineMap) = (fun x : E ↦ x) := by
    funext x
    simp
  rw [hf]
  simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The companion of `ConvexSpaceBody.affineImage_symm_affineImage`: the image along `L.symm`
undoes the image along `L`. Together the two say that `K ↦ L(K)` is a bijection of the convex
bodies of `E`, with inverse `K ↦ L⁻¹(K)`; that bijectivity — and not merely the order embedding
of `ConvexSpaceBody.affineImage_le_affineImage_iff` — is what
`ConvexSpaceBody.IsFrostmanIn.affineImage_iff` needs, since it quantifies over *all* test bodies
contained in the image. -/
lemma ConvexSpaceBody.affineImage_affineImage_symm (K : ConvexSpaceBody E) (L : E ≃ᵃ[ℝ] E)
    (hcont : Continuous L) (hcont' : Continuous L.symm) :
    (K.affineImage L.toAffineMap hcont).affineImage L.symm.toAffineMap hcont' = K := by
  apply ConvexSpaceBody.ext
  change L.symm.toAffineMap '' (L.toAffineMap '' K.carrier) = K.carrier
  rw [← Set.image_comp]
  have hf : (L.symm.toAffineMap ∘ L.toAffineMap) = (fun x : E ↦ x) := by
    funext x
    simp
  rw [hf]
  simp

/-- **`IsEssentiallyDistinct` is preserved by an affine equivalence.**

An affine equivalence is injective and multiplies all three volumes occurring in
`IsEssentiallyDistinct` by the same factor `|det L.linear|`
(`Kakeya.volume_affineImage`), so the inequality is unchanged.

This is the general-affine strengthening of `IsEssentiallyDistinct.image_homothety` and of
`Kakeya.isEssentiallyDistinct_translate` to an arbitrary finite-dimensional real
inner-product space. -/
theorem IsEssentiallyDistinct.image_affineEquiv (L : E ≃ᵃ[ℝ] E) {U V : Set E}
    (h : IsEssentiallyDistinct U V) :
    IsEssentiallyDistinct (L '' U) (L '' V) := by
  unfold IsEssentiallyDistinct at *
  have h_inj : Function.Injective (L : E → E) := L.injective
  rw [← Set.image_inter h_inj]
  rw [(show (L : E → E) = (L.toAffineMap : E → E) from
    (AffineEquiv.coe_toAffineMap (e := L)).symm)]
  rw [Kakeya.volume_affineImage L (U ∩ V), Kakeya.volume_affineImage L U,
    Kakeya.volume_affineImage L V]
  set c := ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)|
  calc
    c * volume (U ∩ V) ≤ c * ((1 / 2 : ENNReal) * max (volume U) (volume V)) := by
      gcongr
    _ = (1 / 2 : ENNReal) * (c * max (volume U) (volume V)) := by
      ring
    _ = (1 / 2 : ENNReal) * max (c * volume U) (c * volume V) := by
      rw [mul_max]

/-- `IsEssentiallyDistinct` for the affine images of two convex bodies. This is the
general-affine analogue of `IsEssentiallyDistinct.homothety_convexBody`. -/
lemma IsEssentiallyDistinct.affineImage_convexBody {K K' : ConvexSpaceBody E}
    (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L)
    (h : IsEssentiallyDistinct K.carrier K'.carrier) :
    IsEssentiallyDistinct (K.affineImage L.toAffineMap hcont).carrier
      (K'.affineImage L.toAffineMap hcont).carrier := by
  change IsEssentiallyDistinct (L.toAffineMap '' K.carrier) (L.toAffineMap '' K'.carrier)
  simpa using IsEssentiallyDistinct.image_affineEquiv L h

/-- **`IsEssentiallyDistinct` is also *reflected* by an affine equivalence.**

The iff strengthening of `IsEssentiallyDistinct.image_affineEquiv`: the reverse implication is
that lemma applied to `L.symm`, `L` being a bijection. Both directions are needed wherever the
property has to be transported back from a normalized picture to the original one. -/
lemma IsEssentiallyDistinct.image_affineEquiv_iff (L : E ≃ᵃ[ℝ] E) {U V : Set E} :
    IsEssentiallyDistinct (L '' U) (L '' V) ↔ IsEssentiallyDistinct U V := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.image_affineEquiv L⟩
  simpa [Set.image_image] using h.image_affineEquiv L.symm

/-- The convex-body twin of `IsEssentiallyDistinct.image_affineEquiv_iff`, and the iff
strengthening of `IsEssentiallyDistinct.affineImage_convexBody`. -/
lemma IsEssentiallyDistinct.affineImage_convexBody_iff {K K' : ConvexSpaceBody E}
    (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L) :
    IsEssentiallyDistinct (K.affineImage L.toAffineMap hcont).carrier
        (K'.affineImage L.toAffineMap hcont).carrier ↔
      IsEssentiallyDistinct K.carrier K'.carrier := by
  change IsEssentiallyDistinct (L.toAffineMap '' K.carrier) (L.toAffineMap '' K'.carrier) ↔ _
  simpa using IsEssentiallyDistinct.image_affineEquiv_iff L (U := K.carrier) (V := K'.carrier)

/-- `IsEssentiallyDistinct.image_affineEquiv_iff` phrased with the image taken along
`L.toAffineMap` rather than along the coercion of `L`, the shape in which the tube
normalization transport (`ShadedTube.normalizeInto`) consumes it. -/
lemma isEssentiallyDistinct_affineImage_iff {U V : Set E} (L : E ≃ᵃ[ℝ] E) :
    IsEssentiallyDistinct (L.toAffineMap '' U) (L.toAffineMap '' V) ↔
      IsEssentiallyDistinct U V := by
  simpa using IsEssentiallyDistinct.image_affineEquiv_iff L (U := U) (V := V)

namespace Kakeya

/-- An affine equivalence multiplies the total volume of a finite family of convex bodies by
`|det L.linear|`. This is the `ConvexSpaceBody` counterpart of
`ShadedBody.sum_volume_carrier_affineImage`, and the general-affine analogue of
`Kakeya.sum_volume_homothety`. It is the numerator half of `Kakeya.densityIn_affineImage`. -/
lemma sum_volume_affineImage (t : Finset ι) (W : ι → ConvexSpaceBody E) (L : E ≃ᵃ[ℝ] E)
    (hcont : Continuous L) :
    ∑ i ∈ t, volume ((W i).affineImage L.toAffineMap hcont).carrier
      = ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| *
          ∑ i ∈ t, volume (W i).carrier := by
  calc
    ∑ i ∈ t, volume ((W i).affineImage L.toAffineMap hcont).carrier
        = ∑ i ∈ t, volume (L.toAffineMap '' (W i).carrier) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simp
    _ = ∑ i ∈ t, (ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| *
          volume (W i).carrier) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [volume_affineImage]
    _ = ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| *
          ∑ i ∈ t, volume (W i).carrier := by
          rw [Finset.mul_sum]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- An affine equivalence does not change which bodies of the family are contained in the test
body, so it leaves `Kakeya.familyIn` unchanged. This is the general-affine analogue of
`Kakeya.familyIn_homothety`. -/
lemma familyIn_affineImage (s : Finset ι) (W : ι → ConvexSpaceBody E) (K : ConvexSpaceBody E)
    (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L) :
    familyIn s (fun i ↦ (W i).affineImage L.toAffineMap hcont)
        (K.affineImage L.toAffineMap hcont) = familyIn s W K := by
  have hinj : Function.Injective (L.toAffineMap : E → E) := by
    intro x y hxy
    exact L.injective hxy
  exact Finset.filter_congr (fun i hi ↦
    ConvexSpaceBody.affineImage_le_affineImage_iff L.toAffineMap hcont hinj)

/-- **`Δ(𝕎, K)` is invariant under an affine equivalence applied to the test body and to all
bodies of the family.**

The equivalence multiplies the numerator and the denominator of `Kakeya.densityIn` by the same
factor `|det L.linear|`, and it preserves the containment relation `W i ≤ K` used to cut down
the sum, so the ratio is left exactly unchanged. This is the general-affine strengthening of
`Kakeya.densityIn_homothety` and of `Kakeya.densityIn_translate`. -/
lemma densityIn_affineImage (s : Finset ι) (W : ι → ConvexSpaceBody E) (K : ConvexSpaceBody E)
    (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L) :
    densityIn s (fun i ↦ (W i).affineImage L.toAffineMap hcont)
        (K.affineImage L.toAffineMap hcont) = densityIn s W K := by
  have hc0 : ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| ≠ 0 :=
    ofReal_abs_det_affineEquiv_ne_zero L
  have hfam := familyIn_affineImage s W K L hcont
  unfold familyIn at hfam
  unfold densityIn
  rw [hfam, sum_volume_affineImage _ W L hcont, ConvexSpaceBody.volume_affineImage,
    ENNReal.mul_div_mul_left _ _ hc0 ENNReal.ofReal_ne_top]

/-- **`Δ_max(𝕎)` is invariant under an affine equivalence.**

An affine equivalence of nonzero determinant is a bijection of the convex bodies of `E`, so it
permutes the test bodies over which the supremum defining `Kakeya.maxDensity` is taken, and it
leaves each `Kakeya.densityIn` unchanged by `Kakeya.densityIn_affineImage`.

This is the general-affine strengthening of `Kakeya.maxDensity_homothety` and of
`Kakeya.maxDensity_translate`. -/
lemma maxDensity_affineImage (s : Finset ι) (W : ι → ConvexSpaceBody E) (L : E ≃ᵃ[ℝ] E)
    (hcont : Continuous L) :
    maxDensity s (fun i ↦ (W i).affineImage L.toAffineMap hcont) = maxDensity s W := by
  have hcont' : Continuous (L.symm : E → E) := L.symm.continuous_of_finiteDimensional
  apply le_antisymm
  · rw [maxDensity_le_iff]
    intro K
    have hK : K = (K.affineImage L.symm.toAffineMap hcont').affineImage L.toAffineMap hcont :=
      (ConvexSpaceBody.affineImage_symm_affineImage K L hcont hcont').symm
    rw [hK, densityIn_affineImage s W (K.affineImage L.symm.toAffineMap hcont') L hcont]
    exact le_maxDensity s W _
  · rw [maxDensity_le_iff]
    intro K
    rw [← densityIn_affineImage s W K L hcont]
    exact le_maxDensity s (fun i ↦ (W i).affineImage L.toAffineMap hcont) _

end Kakeya

namespace ConvexSpaceBody

/-- **The Frostman property is invariant under an invertible affine change of variables.**

The affine image is an order isomorphism of the convex bodies of `E`
(`ConvexSpaceBody.affineImage_le_affineImage_iff`, together with
`ConvexSpaceBody.affineImage_symm_affineImage` and
`ConvexSpaceBody.affineImage_affineImage_symm`), so the test bodies `K' ≤ K` quantified over in
`ConvexSpaceBody.IsFrostmanIn` are in bijection with those `≤ L(K)`, and the two inequalities
matched by that bijection are identical by `Kakeya.densityIn_affineImage`.

This is the general-affine analogue of `ConvexSpaceBody.IsFrostmanIn.translate_iff`. The
continuity of `L.symm`, needed for the bijection, is automatic in finite dimension, so it is not
a hypothesis. -/
lemma IsFrostmanIn.affineImage_iff {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} {C : ENNReal} (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L) :
    IsFrostmanIn s (fun i ↦ (W i).affineImage L.toAffineMap hcont)
        (K.affineImage L.toAffineMap hcont) C ↔ IsFrostmanIn s W K C := by
  have hcont' : Continuous (L.symm : E → E) := L.symm.continuous_of_finiteDimensional
  have hinj : Function.Injective (L.toAffineMap : E → E) := by simpa using L.injective
  have hinj' : Function.Injective (L.symm.toAffineMap : E → E) := by simpa using L.symm.injective
  constructor
  · intro h K' hK'
    have h' := h (K'.affineImage L.toAffineMap hcont)
      ((affineImage_le_affineImage_iff L.toAffineMap hcont hinj).2 hK')
    rwa [Kakeya.densityIn_affineImage s W K' L hcont,
      Kakeya.densityIn_affineImage s W K L hcont] at h'
  · intro h K' hK'
    rw [← affineImage_symm_affineImage K' L hcont hcont',
      Kakeya.densityIn_affineImage s W (K'.affineImage L.symm.toAffineMap hcont') L hcont,
      Kakeya.densityIn_affineImage s W K L hcont]
    refine h (K'.affineImage L.symm.toAffineMap hcont') ?_
    have hle := (affineImage_le_affineImage_iff L.symm.toAffineMap hcont' hinj').mpr hK'
    rwa [affineImage_affineImage_symm K L hcont hcont'] at hle

/-- `IsFrostmanIn` is transported along an affine equivalence; the one-directional form of
`ConvexSpaceBody.IsFrostmanIn.affineImage_iff`, shaped like
`ConvexSpaceBody.IsFrostmanIn.translate`. -/
lemma IsFrostmanIn.affineImage {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} {C : ENNReal} (h : IsFrostmanIn s W K C) (L : E ≃ᵃ[ℝ] E)
    (hcont : Continuous L) :
    IsFrostmanIn s (fun i ↦ (W i).affineImage L.toAffineMap hcont)
      (K.affineImage L.toAffineMap hcont) C :=
  (IsFrostmanIn.affineImage_iff L hcont).mpr h

/-- **The Frostman constant is invariant under an invertible affine change of variables.**

Immediate from `ConvexSpaceBody.IsFrostmanIn.affineImage_iff`: the two sets of admissible
constants coincide, hence so do their infima. Compare
`ConvexSpaceBody.frostmanConstIn_homothety`. -/
theorem frostmanConstIn_affineImage (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (K : ConvexSpaceBody E) (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L) :
    frostmanConstIn s (fun i ↦ (W i).affineImage L.toAffineMap hcont)
        (K.affineImage L.toAffineMap hcont) = frostmanConstIn s W K :=
  congrArg sInf (Set.ext fun _ => IsFrostmanIn.affineImage_iff L hcont)

end ConvexSpaceBody

end AffineImage
