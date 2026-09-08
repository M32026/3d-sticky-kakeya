/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.Rescale
public import Kakeya.DimensionThree.AffineTransport

/-!
# The spine rescaling of Main Lemma 2

Two rescalings occur in the proof of GWZ Main Lemma 2 (`blueprint/src/GWZAdapted/section9.tex`,
"Proof of Main Lemma~\ref{lemmain2}"):

* the *spine* rescaling, which fixes `T_θ ∈ 𝕋_θ` and replaces the family `𝕋_τ[T_θ]` of `τ`-tubes
  inside `T_θ` (and its shading) by its image `(𝕋̃, Ỹ)` under "the rescaling taking `T_θ` to a
  tube of thickness `1`", so that `𝕋̃` is a family of `τ/θ`-tubes at the scale `δ̃ = δ/θ`;
* the same operation one level down, rescaling the `b`-tube `T_b` to `B_1` and turning
  `𝕋̃[T_b]` into a family `𝕋'` of `δ' = δ̃/b`-tubes, so that GWZ Lemma 9.1 applies to it.

Both are the *same* map, `Kakeya.ML2Reduction.spineRescale`, at two different ambient scales, so
this file states the transport laws once, for a general ambient tube `T₀` of thickness `θ`.

## The map

`Kakeya.ML2Reduction.spineRescale hθ T₀` is the affine equivalence `Φ_{T₀}` of
`Tube.normalizationEquiv`: the identity along the axis of `T₀`, multiplication by `θ⁻¹`
transverse to it, fixing the initial core endpoint `T₀.x`.  It carries `T₀`, a tube of thickness
`θ`, to a body of thickness `1`.  `Kakeya.ML2Reduction.spineRescaleUnit hθ T₀ hR` is `Φ_{T₀}`
followed by the homothety of ratio `(4R)⁻¹` about `T₀.x` (`Tube.rescaleMap`); that is the
form needed for GWZ Lemma 9.1, whose tubes must lie in `B_1`.

## The transport laws

Every quantity of the argument that is a *ratio* of volumes is left exactly unchanged, because an
affine equivalence multiplies every volume by the single nonzero finite constant `|det|`.  That is
the content of `Kakeya/AffineMap.lean`; the lemmas below are its ML2-shaped readings, one law per
declaration:

* `spineFamily_multiplicity` — `μ(𝕋̃, Ỹ) = μ(𝕋, Y)`;
* `spineFamily_fullness` — `λ(𝕋̃, Ỹ) = λ(𝕋, Y)`;
* `spineFamily_densityIn`, `spineFamily_maxDensity` — `Δ(·, K)` and `Δ_max`;
* `spineFamily_frostmanConstIn` — `C_F(·, K)`;
* `spineImage_isEssentiallyDistinct_iff` — essential distinctness, in both directions;
* `spineFamily_card_image`, `spineFamily_injOn` — `|𝕋̃| = |𝕋|`;
* `spineRescale_distortion` and `exists_outerTube` — thickness/radius: the image of a `τ`-tube
  inside `T₀` is caught between the `C⁻¹ (τ/θ)`- and `C (τ/θ)`-neighbourhoods of its image core,
  and (after the `(4R)⁻¹` homothety) is contained in an honest `σ`-tube inside `B_1`;
* `spineFamily_cover`, `exists_outerCover` — the `ρ`-tube covering counts: a cover of `𝕋` by
  parents indexed by `t` transports to a cover of `𝕋̃` indexed by the *same* `t`, and back.

## The scale conversion

`δ̃ ≤ δ^{ε₂}` is the standing separation of the argument.  The three lemmas
`spineFamily_multiplicity_le`, `spineFamily_maxDensity_le` and `spineFamily_le_fullness` fuse a
transport law with that conversion, and are exactly the equivalences GWZ asserts between
`multTildeTLem2` and `multTTauInsideTThetaLem2`, and the transported bounds
`upperBdDeltaMaxTildeTT` and the fullness hypothesis of Lemma 9.1.

## What is *not* here

The converse of `exists_outerCover` — turning a cover of `𝕋̃` by `σ`-tubes into a cover of `𝕋` by
`ρ`-tubes — is **not** proved here and is not stated.  It needs a covering of `Φ⁻¹(V)` by tubes for
a `σ`-tube `V`, i.e. the inverse-image tube-covering estimate; `Kakeya.ML2Reduction.spineFamily_cover_symm`
below gives the transport at the level of convex bodies, which is all that holds without it.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace Kakeya.ML2Reduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι κ : Type*} {θ τ σ : NNReal}

/-! ## The rescaling map -/

/-- **The spine rescaling** `Φ_{T₀}`: the affine equivalence carrying the ambient `θ`-tube `T₀` to
a body of thickness `1`, GWZ's "rescaling taking `T_θ` to a tube of thickness 1".

It is `Tube.normalizationEquiv`, the identity along the axis of `T₀` and multiplication by
`θ⁻¹` on its orthogonal complement, fixing `T₀.x`. -/
noncomputable def spineRescale (hθ : 0 < θ) (T₀ : Tube θ E) : E ≃ᵃ[ℝ] E :=
  Tube.normalizationEquiv hθ T₀

@[simp]
theorem spineRescale_apply (hθ : 0 < θ) (T₀ : Tube θ E) (z : E) :
    spineRescale hθ T₀ z = T₀.normalization z :=
  Tube.normalizationEquiv_apply hθ T₀ z

theorem spineRescale_coe (hθ : 0 < θ) (T₀ : Tube θ E) :
    ⇑(spineRescale hθ T₀) = ⇑T₀.normalization :=
  Tube.normalizationEquiv_coe hθ T₀

theorem spineRescale_toAffineMap (hθ : 0 < θ) (T₀ : Tube θ E) :
    (spineRescale hθ T₀).toAffineMap = T₀.normalization :=
  AffineMap.ext (Tube.normalizationEquiv_apply hθ T₀)

@[simp]
theorem spineRescale_apply_x (hθ : 0 < θ) (T₀ : Tube θ E) :
    spineRescale hθ T₀ T₀.x = T₀.x := by
  rw [spineRescale_apply, Tube.normalization_apply_x]

/-- **The unit-ball form of the spine rescaling** `Ψ_{T₀,R}`: `Φ_{T₀}` followed by the homothety
`z ↦ (z - T₀.x)/(4R)`, i.e. `Tube.rescaleMap`, as an affine equivalence.

This is the map GWZ needs for the second rescaling, "rescale `T_b` to `B_1`": Lemma 9.1 asks for a
family of tubes *in the unit ball*, which `spineRescale` alone does not deliver. -/
noncomputable def spineRescaleUnit (hθ : 0 < θ) (T₀ : Tube θ E) {R : ℝ} (hR : 0 < R) :
    E ≃ᵃ[ℝ] E :=
  (Tube.exists_rescaleEquiv hθ hR T₀).choose

theorem spineRescaleUnit_toAffineMap (hθ : 0 < θ) (T₀ : Tube θ E) {R : ℝ} (hR : 0 < R) :
    (spineRescaleUnit hθ T₀ hR).toAffineMap = T₀.rescaleMap R :=
  (Tube.exists_rescaleEquiv hθ hR T₀).choose_spec

@[simp]
theorem spineRescaleUnit_apply (hθ : 0 < θ) (T₀ : Tube θ E) {R : ℝ} (hR : 0 < R) (z : E) :
    spineRescaleUnit hθ T₀ hR z = T₀.rescaleMap R z := by
  conv_rhs => rw [← spineRescaleUnit_toAffineMap hθ T₀ hR]
  rfl

theorem spineRescaleUnit_coe (hθ : 0 < θ) (T₀ : Tube θ E) {R : ℝ} (hR : 0 < R) :
    ⇑(spineRescaleUnit hθ T₀ hR) = ⇑(T₀.rescaleMap R) :=
  funext fun z => spineRescaleUnit_apply hθ T₀ hR z

/-- `Ψ_{T₀,R}` is injective: it is the underlying map of an affine equivalence. -/
theorem rescaleMap_injective (hθ : 0 < θ) (T₀ : Tube θ E) {R : ℝ} (hR : 0 < R) :
    Function.Injective (T₀.rescaleMap R) := by
  rw [← spineRescaleUnit_coe hθ T₀ hR]
  exact (spineRescaleUnit hθ T₀ hR).injective

/-- The two core endpoints of a tube have distinct images under `Ψ_{T₀,R}`.  This is the
side condition of `Tube.centredExtension`, and it never has to be assumed: it follows from
`dist T.x T.y = 1` and injectivity. -/
theorem rescaleMap_x_ne_rescaleMap_y (hθ : 0 < θ) (T₀ : Tube θ E) {R : ℝ} (hR : 0 < R)
    (T : Tube τ E) : T₀.rescaleMap R T.x ≠ T₀.rescaleMap R T.y := by
  intro h
  have hxy : T.x = T.y := rescaleMap_injective hθ T₀ hR h
  have : dist T.x T.y = 1 := T.dist_eq_one
  rw [hxy, dist_self] at this
  exact absurd this (by norm_num)


/-! ## The action on a sub-family and its shadings -/

/-- **The image of a shaded tube** under an affine change of variables, as a shaded body.

The result is a `ShadedBody` and not a `ShadedTube`: `Φ_{T₀}` does not preserve the class of
tubes (`Tube.normalization_distortion` and the note before it), only the class of bodies
caught between two neighbourhoods of a segment. -/
noncomputable def spineImage (A : E ≃ᵃ[ℝ] E) (S : ShadedTube τ E) : ShadedBody E :=
  S.toShadedBody.mapAffine A

@[simp]
theorem spineImage_carrier (A : E ≃ᵃ[ℝ] E) (S : ShadedTube τ E) :
    (spineImage A S).carrier = A '' S.carrier := rfl

@[simp]
theorem spineImage_shade (A : E ≃ᵃ[ℝ] E) (S : ShadedTube τ E) :
    (spineImage A S).shade = A '' S.shade := rfl

@[simp]
theorem spineImage_toConvexSpaceBody (A : E ≃ᵃ[ℝ] E) (S : ShadedTube τ E) :
    (spineImage A S).toConvexSpaceBody = S.toConvexSpaceBody.mapAffine A := rfl

/-- **The image of a whole shaded family** `(𝕋, Y) ↦ (𝕋̃, Ỹ)`.  The index set is unchanged. -/
noncomputable def spineFamily (A : E ≃ᵃ[ℝ] E) (𝕋 : ι → ShadedTube τ E) : ι → ShadedBody E :=
  fun i => spineImage A (𝕋 i)

@[simp]
theorem spineFamily_apply (A : E ≃ᵃ[ℝ] E) (𝕋 : ι → ShadedTube τ E) (i : ι) :
    spineFamily A 𝕋 i = spineImage A (𝕋 i) := rfl

theorem spineFamily_eq_mapAffine (A : E ≃ᵃ[ℝ] E) (𝕋 : ι → ShadedTube τ E) :
    spineFamily A 𝕋 = fun i => (𝕋 i).toShadedBody.mapAffine A := rfl

/-! ## The transport laws

Each law is a separate declaration.  Their common source is that an affine equivalence multiplies
every volume by one nonzero finite factor, so every ratio of volumes is left exactly unchanged;
no comparison constant is lost anywhere below. -/

/-- **(i) Multiplicity is transported exactly**: `μ(𝕋̃, Ỹ) = μ(𝕋, Y)`. -/
theorem spineFamily_multiplicity (A : E ≃ᵃ[ℝ] E) (s : Finset ι) (𝕋 : ι → ShadedTube τ E) :
    ShadedBody.multiplicity s (spineFamily A 𝕋)
      = ShadedBody.multiplicity s (fun i => (𝕋 i).toShadedBody) :=
  ShadedBody.multiplicity_mapAffine s (fun i => (𝕋 i).toShadedBody) A

/-- **(ii) Fullness is transported exactly**: `λ(𝕋̃, Ỹ) = λ(𝕋, Y)`. -/
theorem spineFamily_fullness (A : E ≃ᵃ[ℝ] E) (s : Finset ι) (𝕋 : ι → ShadedTube τ E) :
    ShadedBody.fullness s (spineFamily A 𝕋)
      = ShadedBody.fullness s (fun i => (𝕋 i).toShadedBody) :=
  ShadedBody.fullness_affineImage s (fun i => (𝕋 i).toShadedBody) A
    A.continuous_of_finiteDimensional (Kakeya.measurableEmbedding_affineEquiv A)

/-- **(iii) Density inside a test body is transported**: `Δ(𝕋̃, Φ K) = Δ(𝕋, K)` for every convex
body `K`, not only for `K ⊆ T₀`. -/
theorem spineFamily_densityIn (A : E ≃ᵃ[ℝ] E) (s : Finset ι) (𝕋 : ι → ShadedTube τ E)
    (K : ConvexSpaceBody E) :
    Kakeya.densityIn s (fun i => (spineFamily A 𝕋 i).toConvexSpaceBody) (K.mapAffine A)
      = Kakeya.densityIn s (fun i => (𝕋 i).toConvexSpaceBody) K :=
  Kakeya.densityIn_mapAffine s (fun i => (𝕋 i).toConvexSpaceBody) K A

/-- **(iv) `Δ_max` is transported exactly**: `Δ_max(𝕋̃) = Δ_max(𝕋)`. -/
theorem spineFamily_maxDensity (A : E ≃ᵃ[ℝ] E) (s : Finset ι) (𝕋 : ι → ShadedTube τ E) :
    Kakeya.maxDensity s (fun i => (spineFamily A 𝕋 i).toConvexSpaceBody)
      = Kakeya.maxDensity s (fun i => (𝕋 i).toConvexSpaceBody) :=
  Kakeya.maxDensity_mapAffine s (fun i => (𝕋 i).toConvexSpaceBody) A

/-- **(iv') `Δ_max` of an arbitrary family of convex bodies is transported exactly.**

The form in which the `ρ`-tube layer of the argument reads (iv): the parents `𝕋_ρ` are tubes, not
shaded tubes, and GWZ's lower bound `Δ_max(𝕋̃_ρ) ≥ ρ^{-η_j}` (`tildeDeltaLargeDeltamax`) is a
statement about them. -/
theorem mapAffine_maxDensity (A : E ≃ᵃ[ℝ] E) (t : Finset κ) (W : κ → ConvexSpaceBody E) :
    Kakeya.maxDensity t (fun k => (W k).mapAffine A) = Kakeya.maxDensity t W :=
  Kakeya.maxDensity_mapAffine t W A

/-- **(v) The Frostman constant is transported**: `C_F(𝕋̃, Φ K) = C_F(𝕋, K)`. -/
theorem spineFamily_frostmanConstIn (A : E ≃ᵃ[ℝ] E) (s : Finset ι) (𝕋 : ι → ShadedTube τ E)
    (K : ConvexSpaceBody E) :
    ConvexSpaceBody.frostmanConstIn s (fun i => (spineFamily A 𝕋 i).toConvexSpaceBody)
        (K.mapAffine A)
      = ConvexSpaceBody.frostmanConstIn s (fun i => (𝕋 i).toConvexSpaceBody) K :=
  ConvexSpaceBody.frostmanConstIn_affineImage s (fun i => (𝕋 i).toConvexSpaceBody) K A
    A.continuous_of_finiteDimensional

/-- **(vi) Essential distinctness is preserved and reflected.** -/
theorem spineImage_isEssentiallyDistinct_iff (A : E ≃ᵃ[ℝ] E) (S S' : ShadedTube τ E) :
    IsEssentiallyDistinct (spineImage A S).carrier (spineImage A S').carrier
      ↔ IsEssentiallyDistinct S.carrier S'.carrier :=
  IsEssentiallyDistinct.image_affineEquiv_iff A

/-- **(vi') Essential distinctness of transported convex bodies.** -/
theorem mapAffine_isEssentiallyDistinct_iff (A : E ≃ᵃ[ℝ] E) (K K' : ConvexSpaceBody E) :
    IsEssentiallyDistinct (K.mapAffine A).carrier (K'.mapAffine A).carrier
      ↔ IsEssentiallyDistinct K.carrier K'.carrier :=
  IsEssentiallyDistinct.image_affineEquiv_iff A

/-! ## Cardinality: `|𝕋̃| = |𝕋|` -/

/-- Transport of convex bodies along an affine equivalence is injective. -/
theorem mapAffine_injective (A : E ≃ᵃ[ℝ] E) :
    Function.Injective (fun K : ConvexSpaceBody E => K.mapAffine A) := by
  intro K L h
  have := congrArg (fun M : ConvexSpaceBody E => M.mapAffine A.symm) h
  simpa [ConvexSpaceBody.mapAffine_symm_mapAffine] using this

/-- **(vii) Nothing is collapsed and nothing is created**: the transported family is indexed
injectively exactly when the original one is. -/
theorem spineFamily_injOn_iff (A : E ≃ᵃ[ℝ] E) (s : Finset ι) (𝕋 : ι → ShadedTube τ E) :
    Set.InjOn (fun i => (spineFamily A 𝕋 i).toConvexSpaceBody) s
      ↔ Set.InjOn (fun i => (𝕋 i).toConvexSpaceBody) s := by
  constructor
  · intro h i hi j hj hij
    exact h hi hj (by simpa [spineImage_toConvexSpaceBody] using congrArg (fun K : ConvexSpaceBody E => K.mapAffine A) hij)
  · intro h i hi j hj hij
    exact h hi hj (mapAffine_injective A hij)

/-- **(vii') `|𝕋̃| = |𝕋|`**: the number of distinct bodies of the transported family equals the
number of distinct bodies of the original one.  (The index `Finset` itself is literally
unchanged, so the cardinality reading `|𝕋| = s.card` is preserved on the nose.) -/
theorem spineFamily_card_image [DecidableEq (ConvexSpaceBody E)] (A : E ≃ᵃ[ℝ] E) (s : Finset ι)
    (𝕋 : ι → ShadedTube τ E) :
    (s.image fun i => (spineFamily A 𝕋 i).toConvexSpaceBody).card
      = (s.image fun i => (𝕋 i).toConvexSpaceBody).card := by
  have hcomp : (fun i => (spineFamily A 𝕋 i).toConvexSpaceBody)
      = (fun K : ConvexSpaceBody E => K.mapAffine A) ∘ (fun i => (𝕋 i).toConvexSpaceBody) := rfl
  rw [hcomp, ← Finset.image_image]
  exact Finset.card_image_of_injective _ (mapAffine_injective A)

/-! ## The `ρ`-tube covering counts

A cover of `𝕋` by parents indexed by a finite set `t` is carried to a cover of `𝕋̃` indexed by the
*same* `t`, and back; so the *count* `|𝕋_ρ|` is transported on the nose.  What changes is only the
*shape* of the parents: the image of a `ρ`-tube is a body, and turning it back into an honest tube
is `exists_outerTube` below. -/

/-- Containment in a parent is preserved by the transport. -/
theorem spineImage_le_mapAffine (A : E ≃ᵃ[ℝ] E) {S : ShadedTube τ E} {W : ConvexSpaceBody E}
    (h : S.toConvexSpaceBody ≤ W) : (spineImage A S).toConvexSpaceBody ≤ W.mapAffine A :=
  (ConvexSpaceBody.mapAffine_le_mapAffine_iff A).mpr h

/-- **A cover pushes forward, with the same index set.** -/
theorem spineFamily_cover (A : E ≃ᵃ[ℝ] E) {s : Finset ι} {𝕋 : ι → ShadedTube τ E}
    {t : Finset κ} {W : κ → ConvexSpaceBody E}
    (hcov : ∀ i ∈ s, ∃ k ∈ t, (𝕋 i).toConvexSpaceBody ≤ W k) :
    ∀ i ∈ s, ∃ k ∈ t, (spineFamily A 𝕋 i).toConvexSpaceBody ≤ (W k).mapAffine A := by
  intro i hi
  obtain ⟨k, hk, hle⟩ := hcov i hi
  exact ⟨k, hk, spineImage_le_mapAffine A hle⟩

/-- **A cover pulls back, with the same index set.**

This is the transport of the counting hypothesis `|𝕋_ρ| ≥ ρ^{-2-ζ}` at the level of convex
bodies: a cover of `𝕋̃` by `(W k)_{k ∈ t}` is a cover of `𝕋` by `(Φ⁻¹ W k)_{k ∈ t}`, of the same
cardinality, with the same essential-distinctness pattern
(`mapAffine_isEssentiallyDistinct_iff`). -/
theorem spineFamily_cover_symm (A : E ≃ᵃ[ℝ] E) {s : Finset ι} {𝕋 : ι → ShadedTube τ E}
    {t : Finset κ} {W : κ → ConvexSpaceBody E}
    (hcov : ∀ i ∈ s, ∃ k ∈ t, (spineFamily A 𝕋 i).toConvexSpaceBody ≤ W k) :
    ∀ i ∈ s, ∃ k ∈ t, (𝕋 i).toConvexSpaceBody ≤ (W k).mapAffine A.symm := by
  intro i hi
  obtain ⟨k, hk, hle⟩ := hcov i hi
  refine ⟨k, hk, ?_⟩
  have := (ConvexSpaceBody.mapAffine_le_mapAffine_iff (K := (spineFamily A 𝕋 i).toConvexSpaceBody)
    (L := W k) A.symm).mpr hle
  rwa [spineFamily_apply, spineImage_toConvexSpaceBody,
    ConvexSpaceBody.mapAffine_symm_mapAffine] at this

/-- **The pairwise essential-distinctness pattern of a cover is transported.** -/
theorem mapAffine_pairwise_isEssentiallyDistinct_iff (A : E ≃ᵃ[ℝ] E) (t : Finset κ)
    (W : κ → ConvexSpaceBody E) :
    (t : Set κ).Pairwise
        (fun j k => IsEssentiallyDistinct ((W j).mapAffine A).carrier ((W k).mapAffine A).carrier)
      ↔ (t : Set κ).Pairwise (fun j k => IsEssentiallyDistinct (W j).carrier (W k).carrier) := by
  constructor
  · intro h j hj k hk hjk
    exact (mapAffine_isEssentiallyDistinct_iff A (W j) (W k)).mp (h hj hk hjk)
  · intro h j hj k hk hjk
    exact (mapAffine_isEssentiallyDistinct_iff A (W j) (W k)).mpr (h hj hk hjk)

/-! ## Thickness and radius

`Φ_{T₀}` does not carry tubes to tubes, but it carries a `τ`-tube inside `T₀` to a body caught
between the `C⁻¹ (τ/θ)`- and `C (τ/θ)`-neighbourhoods of a segment of length between `7/8` and
`C`, with `C = C_N(n)` the dimensional distortion constant.  This is GWZ's "`𝕋̃` is a family of
`τ/θ`-tubes", and it is `Tube.normalization_distortion`, restated here in the vocabulary of
`spineRescale`. -/

/-- **(viii) The distortion package of the spine rescaling.** -/
theorem spineRescale_distortion (hθ : 0 < θ) (hτθ : τ ≤ θ) (hθ1 : θ ≤ 1) (T₀ : Tube θ E)
    (T : Tube τ E) (hT : T.carrier ⊆ T₀.carrier) :
    Tube.IsNormalizationDistortion T₀ T :=
  Tube.normalization_distortion hθ hτθ hθ1 T₀ T hT

/-- **(viii.a) The image core has length between `1` and `C_N(n)`.** -/
theorem one_le_dist_spineRescale (hθ : 0 < θ) (hτθ : τ ≤ θ) (hθ1 : θ ≤ 1) (T₀ : Tube θ E)
    (T : Tube τ E) (hT : T.carrier ⊆ T₀.carrier) :
    1 ≤ dist (spineRescale hθ T₀ T.x) (spineRescale hθ T₀ T.y) := by
  simpa using (spineRescale_distortion hθ hτθ hθ1 T₀ T hT).one_le_dist

/-- **(viii.b)** -/
theorem dist_spineRescale_le (hθ : 0 < θ) (hτθ : τ ≤ θ) (hθ1 : θ ≤ 1) (T₀ : Tube θ E)
    (T : Tube τ E) (hT : T.carrier ⊆ T₀.carrier) :
    dist (spineRescale hθ T₀ T.x) (spineRescale hθ T₀ T.y)
      ≤ (Tube.normalization.C (Module.finrank ℝ E) : ℝ) := by
  simpa using (spineRescale_distortion hθ hτθ hθ1 T₀ T hT).dist_le_C

/-- **(viii.c) The image is thin**: it lies in the `C_N (τ/θ)`-neighbourhood of the image core.
This is the upper half of "`𝕋̃` is a family of `τ/θ`-tubes". -/
theorem spineRescale_image_subset_cthickening (hθ : 0 < θ) (hτθ : τ ≤ θ) (hθ1 : θ ≤ 1)
    (T₀ : Tube θ E) (T : Tube τ E) (hT : T.carrier ⊆ T₀.carrier) :
    spineRescale hθ T₀ '' T.carrier ⊆
      cthickening ((Tube.normalization.C (Module.finrank ℝ E) : ℝ) * ((τ : ℝ) / (θ : ℝ)))
        (segment ℝ (spineRescale hθ T₀ T.x) (spineRescale hθ T₀ T.y)) := by
  simpa [spineRescale_coe] using
    (spineRescale_distortion hθ hτθ hθ1 T₀ T hT).image_subset_cthickening

/-- **(viii.d) The image is thick**: it contains the `C_N⁻¹ (τ/θ)`-neighbourhood of a sub-segment
of the image core of length at least `7/8`.  This is the lower half of "`𝕋̃` is a family of
`τ/θ`-tubes"; unit length is false here, see `Tube.IsNormalizationDistortion`. -/
theorem spineRescale_exists_subsegment (hθ : 0 < θ) (hτθ : τ ≤ θ) (hθ1 : θ ≤ 1)
    (T₀ : Tube θ E) (T : Tube τ E) (hT : T.carrier ⊆ T₀.carrier) :
    ∃ a ∈ segment ℝ (spineRescale hθ T₀ T.x) (spineRescale hθ T₀ T.y),
      ∃ b ∈ segment ℝ (spineRescale hθ T₀ T.x) (spineRescale hθ T₀ T.y),
        (7 / 8 : ℝ) ≤ dist a b ∧
        cthickening ((Tube.normalization.C (Module.finrank ℝ E) : ℝ)⁻¹ * ((τ : ℝ) / (θ : ℝ)))
          (segment ℝ a b) ⊆ spineRescale hθ T₀ '' T.carrier := by
  simpa [spineRescale_coe] using
    (spineRescale_distortion hθ hτθ hθ1 T₀ T hT).exists_subsegment

/-- **(viii.e) The image of the ambient tube is bounded**: `Φ_{T₀}(T₀) ⊆ B̄(T₀.x, C_N(n))`. -/
theorem spineRescale_image_ambient_subset_closedBall (hθ : 0 < θ) (hθ1 : θ ≤ 1) (T₀ : Tube θ E) :
    spineRescale hθ T₀ '' T₀.carrier
      ⊆ closedBall T₀.x (Tube.normalization.C (Module.finrank ℝ E) : ℝ) := by
  simpa [spineRescale_coe] using Tube.normalization_image_ambient_subset_closedBall hθ hθ1 T₀

/-! ## Honest tubes downstairs: the outer tube of a rescaled tube

For the second rescaling — `T_b ↦ B_1`, feeding GWZ Lemma 9.1 — the images have to be honest
`Kakeya.Tube`s inside the unit ball, not merely thin bodies.  That is what the unit form
`spineRescaleUnit` and `Tube.rescale_outer_tube` deliver, at the cost of a bounded volume
loss `(4R)^6`.  The two side conditions of that lemma, the ball containment of the image and the
nondegeneracy of the image core, are discharged here rather than assumed. -/

variable [Nontrivial E]

/-- The image of a tube contained in the ambient tube stays in `B̄(T₀.x, R)`, for any admissible
ambient radius `R`.  This is the hypothesis `hball` of `Tube.rescale_outer_tube`, which
therefore never has to be supplied by a caller. -/
theorem normalization_image_subset_closedBall_of_subset {R : ℝ}
    (hn : Module.finrank ℝ E = 3) (hsit : Tube.IsRescalingSituation θ τ σ R 3)
    (T₀ : Tube θ E) (T : Tube τ E) (hT : T.carrier ⊆ T₀.carrier) :
    T₀.normalization '' T.carrier ⊆ closedBall T₀.x R := by
  have hC : T₀.normalization '' T₀.carrier
      ⊆ closedBall T₀.x (Tube.normalization.C (Module.finrank ℝ E) : ℝ) :=
    Tube.normalization_image_ambient_subset_closedBall hsit.pos_ambient hsit.ambient_le_one T₀
  have hCR : (Tube.normalization.C (Module.finrank ℝ E) : ℝ) ≤ R := by
    rw [hn]; exact hsit.normalizationConst_le_radius
  exact ((Set.image_mono hT).trans hC).trans (closedBall_subset_closedBall hCR)

/-- **The outer tube attached to a rescaled tube**: the centred unit extension of the image core,
at radius `σ`.  It is total — the nondegeneracy side condition of `Tube.centredExtension`
is automatic (`rescaleMap_x_ne_rescaleMap_y`) — so a whole family of parents can be pushed forward
at once (`exists_outerCover`). -/
noncomputable def outerTube (hθ : 0 < θ) (T₀ : Tube θ E) {R : ℝ} (hR : 0 < R) (σ : NNReal)
    (T : Tube τ E) : Tube σ E :=
  Tube.centredExtension σ (rescaleMap_x_ne_rescaleMap_y hθ T₀ hR T)

/-- **(ix) The outer tube.**  In a rescaling situation, the image of a `τ`-tube `T ⊆ T₀` under the
unit form of the spine rescaling is contained in the honest `σ`-tube `outerTube`, which lies
inside `B_1` and has volume at most `(4R)^6` times the volume of the image.

Together with `spineRescale_exists_subsegment` this is the precise content of "`𝕋̃` is a family of
`τ/θ`-tubes": `σ` may be taken `≍ τ/θ`, since `IsRescalingSituation` asks `σ ≤ τ/θ` and the extra
hypothesis here asks `τ/θ ≤ 4σ`. -/
theorem outerTube_spec {R : ℝ} (hn : Module.finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (hρσ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ))
    (T₀ : Tube θ E) (T : Tube τ E) (hT : T.carrier ⊆ T₀.carrier) :
    spineRescaleUnit hsit.pos_ambient T₀ hR '' T.carrier
        ⊆ (outerTube hsit.pos_ambient T₀ hR σ T).carrier ∧
      (outerTube hsit.pos_ambient T₀ hR σ T).carrier ⊆ closedBall (0 : E) 1 ∧
      volume (outerTube hsit.pos_ambient T₀ hR σ T).carrier
        ≤ ENNReal.ofReal ((4 * R) ^ 6)
          * volume (spineRescaleUnit hsit.pos_ambient T₀ hR '' T.carrier) := by
  have hxy : T₀.rescaleMap R T.x ≠ T₀.rescaleMap R T.y :=
    rescaleMap_x_ne_rescaleMap_y hsit.pos_ambient T₀ hR T
  have hdist : Tube.IsNormalizationDistortion T₀ T :=
    Tube.normalization_distortion hsit.pos_ambient hsit.inner_le_ambient hsit.ambient_le_one
      T₀ T hT
  have hball : T₀.normalization '' T.carrier ⊆ closedBall T₀.x R :=
    normalization_image_subset_closedBall_of_subset hn hsit T₀ T hT
  obtain ⟨hsub, hpos, hvol⟩ :=
    Tube.rescale_outer_tube hsit hn hR hρσ T₀ T hdist hball hxy
  refine ⟨?_, hpos, ?_⟩
  · simpa [outerTube, spineRescaleUnit_coe hsit.pos_ambient T₀ hR] using hsub
  · simpa [outerTube, spineRescaleUnit_coe hsit.pos_ambient T₀ hR] using hvol

/-- The existential reading of `outerTube_spec`. -/
theorem exists_outerTube {R : ℝ} (hn : Module.finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (hρσ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ))
    (T₀ : Tube θ E) (T : Tube τ E) (hT : T.carrier ⊆ T₀.carrier) :
    ∃ V : Tube σ E,
      spineRescaleUnit hsit.pos_ambient T₀ hR '' T.carrier ⊆ V.carrier ∧
        V.carrier ⊆ closedBall (0 : E) 1 ∧
        volume V.carrier ≤ ENNReal.ofReal ((4 * R) ^ 6)
          * volume (spineRescaleUnit hsit.pos_ambient T₀ hR '' T.carrier) :=
  ⟨outerTube hsit.pos_ambient T₀ hR σ T, outerTube_spec hn hsit hR hρσ T₀ T hT⟩

/-- **(x) The `ρ`-tube covering count, transported to honest tubes.**

A cover of the family `𝕋` by `ρ`-tubes `(W_k)_{k ∈ t}` inside the ambient tube `T₀` becomes, under
the unit form of the spine rescaling, a cover of the transported family by honest `σ`-tubes inside
`B_1` indexed by the **same** finite set `t`.  Hence `|𝕋̃_σ| ≤ |𝕋_ρ|` on the nose — the parents are
neither merged nor split.

The converse — every cover downstairs comes from a cover upstairs, which is what a *lower* bound
on `|𝕋̃_σ|` needs — is not available at this level of generality; see the module docstring. -/
theorem exists_outerCover {ρ : NNReal} {R : ℝ} (hn : Module.finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ ρ σ R 3) (hR : 0 < R)
    (hρσ : (ρ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ))
    (T₀ : Tube θ E) {s : Finset ι} (𝕋 : ι → ShadedTube τ E)
    {t : Finset κ} (W : κ → Tube ρ E)
    (hsub : ∀ k ∈ t, (W k).carrier ⊆ T₀.carrier)
    (hcov : ∀ i ∈ s, ∃ k ∈ t, (𝕋 i).carrier ⊆ (W k).carrier) :
    ∃ V : κ → Tube σ E,
      (∀ k ∈ t, (V k).carrier ⊆ closedBall (0 : E) 1) ∧
        ∀ i ∈ s, ∃ k ∈ t,
          (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).carrier ⊆ (V k).carrier := by
  refine ⟨fun k => outerTube hsit.pos_ambient T₀ hR σ (W k), ?_, ?_⟩
  · intro k hk
    exact (outerTube_spec hn hsit hR hρσ T₀ (W k) (hsub k hk)).2.1
  · intro i hi
    obtain ⟨k, hk, hle⟩ := hcov i hi
    refine ⟨k, hk, ?_⟩
    have himg := (outerTube_spec hn hsit hR hρσ T₀ (W k) (hsub k hk)).1
    have hmono : spineRescaleUnit hsit.pos_ambient T₀ hR '' (𝕋 i).carrier
        ⊆ spineRescaleUnit hsit.pos_ambient T₀ hR '' (W k).carrier := Set.image_mono hle
    have : (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).carrier
        = spineRescaleUnit hsit.pos_ambient T₀ hR '' (𝕋 i).carrier := rfl
    rw [this]
    exact hmono.trans himg

/-! ## The scale conversion `δ̃ ≤ δ^{ε₂}`

GWZ's standing separation between the outer scale `δ` and the rescaled scale `δ̃ = δ/θ` is
`δ̃ ≤ δ^{ε₂}`.  Reading a conclusion stated at the rescaled scale as one at the outer scale, and a
hypothesis at the outer scale as one at the rescaled scale, is the following pair of numeric
facts; fusing them with the transport laws above gives the three statements the proof of Main
Lemma 2 actually quotes. -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **A power of `δ̃` is a power of `δ`, downwards**: if `δ̃ ≤ δ^{ε}` with `ε > 0` and `x ≥ 0`,
then `δ̃^{x/ε} ≤ δ^{x}`. -/
theorem rpow_div_le_rpow_of_sep {ε : ℝ} (hε : 0 < ε) {δ δt : NNReal} (hsep : δt ≤ δ ^ ε)
    {x : ℝ} (hx : 0 ≤ x) : δt ^ (x / ε) ≤ δ ^ x := by
  have hxε : 0 ≤ x / ε := div_nonneg hx hε.le
  calc δt ^ (x / ε) ≤ (δ ^ ε) ^ (x / ε) := NNReal.rpow_le_rpow hsep hxε
    _ = δ ^ (ε * (x / ε)) := (NNReal.rpow_mul δ ε (x / ε)).symm
    _ = δ ^ x := by rw [mul_div_cancel₀ x (ne_of_gt hε)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- The `ENNReal` form of `rpow_div_le_rpow_of_sep`. -/
theorem coe_rpow_div_le_rpow_of_sep {ε : ℝ} (hε : 0 < ε) {δ δt : NNReal} (hsep : δt ≤ δ ^ ε)
    {x : ℝ} (hx : 0 ≤ x) : (δt : ENNReal) ^ (x / ε) ≤ (δ : ENNReal) ^ x := by
  have h1 : ((δt ^ (x / ε) : NNReal) : ENNReal) ≤ ((δ ^ x : NNReal) : ENNReal) :=
    ENNReal.coe_le_coe.mpr (rpow_div_le_rpow_of_sep hε hsep hx)
  rwa [ENNReal.coe_rpow_of_nonneg _ (div_nonneg hx hε.le), ENNReal.coe_rpow_of_nonneg _ hx] at h1

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **A negative power of `δ` is a negative power of `δ̃`, upwards**: if `δ̃ ≤ δ^{ε}` with `ε > 0`
and `x ≥ 0`, then `δ^{-x} ≤ δ̃^{-(x/ε)}`.  This is the direction that converts the outer bound
`Δ_max(𝕋) ≤ δ^{-η_{j-1}}` into GWZ's `upperBdDeltaMaxTildeTT`. -/
theorem rpow_neg_le_coe_rpow_neg_div_of_sep {ε : ℝ} (hε : 0 < ε) {δ δt : NNReal}
    (hsep : δt ≤ δ ^ ε) {x : ℝ} (hx : 0 ≤ x) :
    (δ : ENNReal) ^ (-x) ≤ (δt : ENNReal) ^ (-(x / ε)) := by
  rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
  exact ENNReal.inv_le_inv.mpr (coe_rpow_div_le_rpow_of_sep hε hsep hx)

/-! ## The three statements Main Lemma 2 quotes -/

/-- **The goal transport** (GWZ: proving `multTildeTLem2` is equivalent to proving
`multTTauInsideTThetaLem2`).

If `δ̃ ≤ δ^{ε₂}` and the rescaled family obeys `μ(𝕋̃, Ỹ) ≤ δ̃^{e/ε₂} |𝕋̃|^β`, then the original
family obeys `μ(𝕋_τ[T_θ], Y) ≤ δ^{e} |𝕋_τ[T_θ]|^β`.  Multiplicity and the index set are carried
across unchanged (`spineFamily_multiplicity`); only the exponent is converted. -/
theorem spineFamily_multiplicity_le {ε e β : ℝ} (hε : 0 < ε) (he : 0 ≤ e)
    {δ δt : NNReal} (hsep : δt ≤ δ ^ ε)
    (A : E ≃ᵃ[ℝ] E) (s : Finset ι) (𝕋 : ι → ShadedTube τ E) (N : ENNReal)
    (h : ShadedBody.multiplicity s (spineFamily A 𝕋) ≤ (δt : ENNReal) ^ (e / ε) * N ^ β) :
    ShadedBody.multiplicity s (fun i => (𝕋 i).toShadedBody) ≤ (δ : ENNReal) ^ e * N ^ β := by
  rw [← spineFamily_multiplicity A s 𝕋]
  refine h.trans (mul_le_mul' (coe_rpow_div_le_rpow_of_sep hε hsep he) le_rfl)

/-- **The transported `Δ_max` bound** (GWZ `upperBdDeltaMaxTildeTT`).

`Δ_max(𝕋) ≤ δ^{-η}` and `δ̃ ≤ δ^{ε₂}` give `Δ_max(𝕋̃) ≤ δ̃^{-η/ε₂}`. -/
theorem spineFamily_maxDensity_le {ε η : ℝ} (hε : 0 < ε) (hη : 0 ≤ η)
    {δ δt : NNReal} (hsep : δt ≤ δ ^ ε)
    (A : E ≃ᵃ[ℝ] E) (s : Finset ι) (𝕋 : ι → ShadedTube τ E)
    (h : Kakeya.maxDensity s (fun i => (𝕋 i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η)) :
    Kakeya.maxDensity s (fun i => (spineFamily A 𝕋 i).toConvexSpaceBody)
      ≤ (δt : ENNReal) ^ (-(η / ε)) := by
  rw [spineFamily_maxDensity A s 𝕋]
  exact h.trans (rpow_neg_le_coe_rpow_neg_div_of_sep hε hsep hη)

/-- **The transported fullness bound.**

`λ(𝕋, Y) ≥ δ^{η}` and `δ̃ ≤ δ^{ε₂}` give `λ(𝕋̃, Ỹ) ≥ δ̃^{η/ε₂}`, which is the shading hypothesis
GWZ Lemma 9.1 asks of the rescaled family. -/
theorem spineFamily_le_fullness {ε η : ℝ} (hε : 0 < ε) (hη : 0 ≤ η)
    {δ δt : NNReal} (hsep : δt ≤ δ ^ ε)
    (A : E ≃ᵃ[ℝ] E) (s : Finset ι) (𝕋 : ι → ShadedTube τ E)
    (h : δ ^ η ≤ ShadedBody.fullness s (fun i => (𝕋 i).toShadedBody)) :
    δt ^ (η / ε) ≤ ShadedBody.fullness s (spineFamily A 𝕋) := by
  rw [spineFamily_fullness A s 𝕋]
  exact (rpow_div_le_rpow_of_sep hε hsep hη).trans h

omit [Nontrivial E] in
/-- **The transported `Δ_max` lower bound** (GWZ `tildeDeltaLargeDeltamax`).

A lower bound for the maximal density of a family of parents is carried across the rescaling
unchanged; only the scale at which it is read changes. -/
theorem le_mapAffine_maxDensity (A : E ≃ᵃ[ℝ] E) (t : Finset κ) (W : κ → ConvexSpaceBody E)
    {c : ENNReal} (h : c ≤ Kakeya.maxDensity t W) :
    c ≤ Kakeya.maxDensity t (fun k => (W k).mapAffine A) := by
  rwa [mapAffine_maxDensity A t W]

end Kakeya.ML2Reduction
